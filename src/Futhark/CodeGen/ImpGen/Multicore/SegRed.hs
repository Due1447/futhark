module Futhark.CodeGen.ImpGen.Multicore.SegRed
  ( compileSegRed,
    compileSegRed',
  )
where

import Control.Monad
import qualified Futhark.CodeGen.ImpCode.Multicore as Imp
import Futhark.CodeGen.ImpGen
import Futhark.CodeGen.ImpGen.Multicore.Base
import Futhark.IR.MCMem
import Futhark.Util (chunks)
import Prelude hiding (quot, rem)
import Futhark.MonadFreshNames

type DoSegBody = (([(SubExp, [Imp.TExp Int64])] -> MulticoreGen ()) -> MulticoreGen ())

-- | Generate code for a SegRed construct
compileSegRed ::
  Pat MCMem ->
  SegSpace ->
  [SegBinOp MCMem] ->
  KernelBody MCMem ->
  TV Int32 ->
  MulticoreGen Imp.Code
compileSegRed pat space reds kbody nsubtasks =
  compileSegRed' pat space reds nsubtasks $ \red_cont ->
    compileStms mempty (kernelBodyStms kbody) $ do
      let (red_res, map_res) = splitAt (segBinOpResults reds) $ kernelBodyResult kbody

      sComment "save map-out results" $ do
        let map_arrs = drop (segBinOpResults reds) $ patElems pat
        zipWithM_ (compileThreadResult space) map_arrs map_res

      red_cont $ zip (map kernelResultSubExp red_res) $ repeat []

-- | Like 'compileSegRed', but where the body is a monadic action.
compileSegRed' ::
  Pat MCMem ->
  SegSpace ->
  [SegBinOp MCMem] ->
  TV Int32 ->
  DoSegBody ->
  MulticoreGen Imp.Code
compileSegRed' pat space reds nsubtasks kbody
  | [_] <- unSegSpace space =
    nonsegmentedReduction pat space reds nsubtasks kbody
  | otherwise =
    segmentedReduction pat space reds kbody

-- | A SegBinOp with auxiliary information.
data SegBinOpSlug = SegBinOpSlug
  { slugOp :: SegBinOp MCMem,
    -- | The array in which we write the intermediate results, indexed
    -- by the flat/physical thread ID.
    slugResArrs :: [VName]
  }

slugBody :: SegBinOpSlug -> Body MCMem
slugBody = lambdaBody . segBinOpLambda . slugOp

slugParams :: SegBinOpSlug -> [LParam MCMem]
slugParams = lambdaParams . segBinOpLambda . slugOp

slugNeutral :: SegBinOpSlug -> [SubExp]
slugNeutral = segBinOpNeutral . slugOp

slugShape :: SegBinOpSlug -> Shape
slugShape = segBinOpShape . slugOp

accParams, nextParams :: SegBinOpSlug -> [LParam MCMem]
accParams slug = take (length (slugNeutral slug)) $ slugParams slug
nextParams slug = drop (length (slugNeutral slug)) $ slugParams slug

nonsegmentedReduction ::
  Pat MCMem ->
  SegSpace ->
  [SegBinOp MCMem] ->
  TV Int32 ->
  DoSegBody ->
  MulticoreGen Imp.Code
nonsegmentedReduction pat space reds nsubtasks kbody = collect $ do
  thread_res_arrs <- groupResultArrays "reduce_stage_1_tid_res_arr" (tvSize nsubtasks) reds
  let slugs1 = zipWith SegBinOpSlug reds thread_res_arrs
      nsubtasks' = tvExp nsubtasks

  -- Are all the operators commutative?
  let comm = all ((==Commutative) . segBinOpComm) reds

  let dims = map (shapeDims . slugShape) slugs1
  let isScalar x = case x of MemPrim _ -> True; _ -> False
   -- Are we only working on scalar arrays?
  let scalars = all (all (isScalar . paramDec) . slugParams) slugs1 && all (==[]) dims
   -- Are we only working on arrays of arrays?
  let arrays = all (/=[]) dims
  
  -- TODO(pema): Extract into one function, refactor
  let path
       | comm && scalars = reductionStage1CommScalar
       | arrays          = reductionStage1Array
       | scalars         = reductionStage1NonCommScalar
       | otherwise       = reductionStage1
  path space slugs1 kbody

  reds2 <- renameSegBinOp reds
  let slugs2 = zipWith SegBinOpSlug reds2 thread_res_arrs
  reductionStage2 pat space nsubtasks' slugs2

-- Pure sequential C codegen
reductionStage1 ::
  SegSpace ->
  [SegBinOpSlug] ->
  DoSegBody ->
  MulticoreGen ()
reductionStage1 space slugs kbody = do
  let (is, ns) = unzip $ unSegSpace space
      ns' = map toInt64Exp ns
  -- Create local accumulator variables in which we carry out the
  -- sequential reduction of this function.  If we are dealing with
  -- vectorised operators, then this implies a private allocation.  If
  -- the original operand type of the reduction is a memory block,
  -- then our hands are unfortunately tied, and we have to use exactly
  -- that memory.  This is likely to be slow.

  fbody <- collect $ do
    dPrim_ (segFlat space) int64
    sOp $ Imp.GetTaskId (segFlat space)

    slug_local_accs <- do
      dScope Nothing $ scopeOfLParams $ concatMap slugParams slugs

      forM slugs $ \slug -> do
        let shape = segBinOpShape $ slugOp slug

        forM (zip (accParams slug) (slugNeutral slug)) $ \(p, ne) -> do
          -- Declare accumulator variable.
          acc <-
            case paramType p of
              Prim pt
                | shape == mempty ->
                  tvVar <$> dPrim "local_acc" pt
                | otherwise ->
                  sAllocArray "local_acc" pt shape DefaultSpace
              _ ->
                pure $ paramName p

          -- Now neutral-initialise the accumulator.
          sLoopNest (slugShape slug) $ \vec_is ->
            copyDWIMFix acc vec_is ne []

          pure acc

    generateChunkLoop "SegRed" False $ \i -> do
      zipWithM_ dPrimV_ is $ unflattenIndex ns' i
      kbody $ \all_red_res -> do
        let all_red_res' = segBinOpChunks (map slugOp slugs) all_red_res
        forM_ (zip3 all_red_res' slugs slug_local_accs) $ \(red_res, slug, local_accs) ->
          sLoopNest (slugShape slug) $ \vec_is -> do
            let lamtypes = lambdaReturnType $ segBinOpLambda $ slugOp slug
            -- Load accum params
            sComment "Load accum params" $
              forM_ (zip3 (accParams slug) local_accs lamtypes) $
                \(p, local_acc, t) ->
                  when (primType t) $
                    copyDWIMFix (paramName p) [] (Var local_acc) vec_is

            sComment "Load next params" $
              forM_ (zip (nextParams slug) red_res) $ \(p, (res, res_is)) ->
                copyDWIMFix (paramName p) [] res (res_is ++ vec_is)

            sComment "SegRed body" $
              compileStms mempty (bodyStms $ slugBody slug) $
                forM_ (zip local_accs $ map resSubExp $ bodyResult $ slugBody slug) $
                  \(local_acc, se) ->
                    copyDWIMFix local_acc vec_is se []

    forM_ (zip slugs slug_local_accs) $ \(slug, local_accs) ->
      forM (zip (slugResArrs slug) local_accs) $ \(acc, local_acc) ->
        copyDWIMFix acc [Imp.le64 $ segFlat space] (Var local_acc) []

  free_params <- freeParams fbody
  emit $ Imp.Op $ Imp.ParLoop "segred_stage_1" fbody free_params

-- Codegen for noncommutative scalar reduction
reductionStage1NonCommScalar ::
  SegSpace ->
  [SegBinOpSlug] ->
  DoSegBody ->
  MulticoreGen ()
reductionStage1NonCommScalar space slugs kbody = do
  let (is, ns) = unzip $ unSegSpace space
      ns' = map toInt64Exp ns
  -- Create local accumulator variables in which we carry out the
  -- sequential reduction of this function.  If we are dealing with
  -- vectorised operators, then this implies a private allocation.  If
  -- the original operand type of the reduction is a memory block,
  -- then our hands are unfortunately tied, and we have to use exactly
  -- that memory.  This is likely to be slow.

  fbody <- collect $ do
    dPrim_ (segFlat space) int64
    sOp $ Imp.GetTaskId (segFlat space)

    (slug_local_accs_pairs, prebody) <- collect' $ everythingUniform $ do
      dScope Nothing $ scopeOfLParams $ concatMap slugParams slugs

      forM slugs $ \slug -> do
        let shape = segBinOpShape $ slugOp slug

        forM (zip (accParams slug) (slugNeutral slug)) $ \(p, ne) -> do
          -- Declare accumulator variable.
          acc <-
            let typ = paramType p in
            case typ of
              Prim pt
                | shape == mempty -> do
                  name <- tvVar <$> dPrim "local_acc" pt
                  pure (name, typ)
                | otherwise -> do
                  name <- sAllocArray "local_acc" pt shape DefaultSpace
                  pure (name, typ)
              _ ->
                pure (paramName p, typ)

          -- Now neutral-initialise the accumulator.
          sLoopNest (slugShape slug) $ \vec_is ->
            copyDWIMFix (fst acc) vec_is ne []

          pure acc

    let slug_local_accs = map (map fst) slug_local_accs_pairs
    retvals <- fmap concat $ mapM (uncurry toParam) . concat $ slug_local_accs_pairs

    -- Declare result vars
    forM_ retvals $ \local_accs ->
      case local_accs of
        Imp.ScalarParam name pt -> dPrim_ name pt
        _ -> undefined

    inISPC retvals $ do
      emit prebody
      generateChunkLoop "SegRed" True $ \i -> do
        zipWithM_ dPrimV_ is $ unflattenIndex ns' i
        kbody $ \all_red_res -> do
          let all_red_res' = segBinOpChunks (map slugOp slugs) all_red_res
          forM_ (zip3 all_red_res' slugs slug_local_accs) $ \(red_res, slug, local_accs) ->
            sLoopNest (slugShape slug) $ \vec_is -> do
              let lamtypes = lambdaReturnType $ segBinOpLambda $ slugOp slug
              -- Load accum params
              everythingUniform $
                generateUniformizeLoop $ \uni -> do
                  sComment "Load accum params" $
                    forM_ (zip3 (accParams slug) local_accs lamtypes) $
                      \(p, local_acc, t) ->
                        when (primType t) $ do
                          copyDWIMFix (paramName p) [] (Var local_acc) vec_is

                  sComment "Load next params" $
                    forM_ (zip (nextParams slug) red_res) $ \(p, (res, res_is)) -> do
                      extractVectorLane uni $ collect $
                        copyDWIMFix (paramName p) [] res (res_is ++ vec_is)

                  sComment "SegRed body" $
                    compileStms mempty (bodyStms $ slugBody slug) $
                      forM_ (zip local_accs $ map resSubExp $ bodyResult $ slugBody slug) $
                        \(local_acc, se) ->
                          copyDWIMFix local_acc vec_is se []

    forM_ (zip slugs slug_local_accs) $ \(slug, local_accs) ->
      forM (zip (slugResArrs slug) local_accs) $ \(acc, local_acc) ->
        copyDWIMFix acc [Imp.le64 $ segFlat space] (Var local_acc) []

  free_params <- freeParams fbody
  emit $ Imp.Op $ Imp.ParLoop "segred_stage_1" fbody free_params

-- Codegen for a commutative reduction on scalar arrays
reductionStage1CommScalar ::
  SegSpace ->
  [SegBinOpSlug] ->
  DoSegBody ->
  MulticoreGen ()
reductionStage1CommScalar space slugs kbody = do
  let (is, ns) = unzip $ unSegSpace space
      ns' = map toInt64Exp ns
  -- Create local accumulator variables in which we carry out the
  -- sequential reduction of this function.  If we are dealing with
  -- vectorised operators, then this implies a private allocation.  If
  -- the original operand type of the reduction is a memory block,
  -- then our hands are unfortunately tied, and we have to use exactly
  -- that memory.  This is likely to be slow.

  fbody <- collect $ do
    dPrim_ (segFlat space) int64
    sOp $ Imp.GetTaskId (segFlat space)

    prebody1 <- collect $ dScope Nothing $ scopeOfLParams $ concatMap slugParams slugs
    let genAccs =
          collect' $ do
            forM slugs $ \slug -> do
              let shape = segBinOpShape $ slugOp slug

              forM (zip (accParams slug) (slugNeutral slug)) $ \(p, ne) -> do
                -- Declare accumulator variable.
                acc <-
                  let typ = paramType p in
                  case typ of
                    Prim pt
                      | shape == mempty -> do
                        name <- tvVar <$> dPrim "local_acc" pt
                        pure (name, typ)
                      | otherwise -> do
                        name <- sAllocArray "local_acc" pt shape DefaultSpace
                        pure (name, typ)
                    _ ->
                      pure (paramName p, typ)

                -- Now neutral-initialise the accumulator.
                sLoopNest (slugShape slug) $ \vec_is ->
                  copyDWIMFix (fst acc) vec_is ne []

                pure acc

    (slug_local_accs_pairs, prebody2) <- genAccs
    (slug_local_accs_pairs_uni, prebody3) <- genAccs
    let prebody = prebody1 Imp.:>>: prebody2 Imp.:>>: prebody3

    -- This is a list of lists because we can have multiple fused reduction (multiple binops), and each reduction can return multiple values
    let slug_local_accs = map (map fst) slug_local_accs_pairs
    let slug_local_accs_uni = map (map fst) slug_local_accs_pairs_uni
    retvals <- fmap concat $ mapM (uncurry toParam) . concat $ slug_local_accs_pairs_uni

    postbody <- collect $ generateUniformizeLoop $ \i -> do
      zipWithM_ dPrimV_ is $ unflattenIndex ns' i
      forM_ (zip3 slugs slug_local_accs slug_local_accs_uni) $ \(slug, local_accs, local_accs_uni) ->
        sLoopNest (slugShape slug) $ \vec_is -> do
          let lamtypes = lambdaReturnType $ segBinOpLambda $ slugOp slug
          -- Load accum params
          sComment "Load accum params" $
            forM_ (zip3 (accParams slug) local_accs_uni lamtypes) $
              \(p, local_acc, t) ->
                when (primType t) $ do
                  copyDWIMFix (paramName p) [] (Var local_acc) vec_is
                  uniformizeVar (paramName p) (untyped i)

          sComment "Load next params" $ -- TODO(pema): red_res missing, problem?
            forM_ (zip (nextParams slug) local_accs) $ \(p, local_acc) -> do
              copyDWIMFix (paramName p) [] (Var local_acc) vec_is
              uniformizeVar (paramName p) (untyped i)

          sComment "SegRed body" $
            compileStms mempty (bodyStms $ slugBody slug) $
              forM_ (zip local_accs_uni $ map resSubExp $ bodyResult $ slugBody slug) $
                \(local_acc, se) ->
                  copyDWIMFix local_acc vec_is se []

    -- Declare result vars
    forM_ retvals $ \local_accs ->
      case local_accs of
        Imp.ScalarParam name pt -> dPrim_ name pt
        _ -> undefined
    -- TODO(pema): Arrays and such are already allocated above, move
    -- the prebody out of and pass it in?

    inISPC retvals $ do
      emit prebody
      generateChunkLoop "SegRed" True $ \i -> do
        zipWithM_ dPrimV_ is $ unflattenIndex ns' i
        kbody $ \all_red_res -> do
          let all_red_res' = segBinOpChunks (map slugOp slugs) all_red_res
          forM_ (zip3 all_red_res' slugs slug_local_accs) $ \(red_res, slug, local_accs) ->
            sLoopNest (slugShape slug) $ \vec_is -> do
              let lamtypes = lambdaReturnType $ segBinOpLambda $ slugOp slug
              -- Load accum params
              sComment "Load accum params" $
                forM_ (zip3 (accParams slug) local_accs lamtypes) $
                  \(p, local_acc, t) ->
                    when (primType t) $
                      copyDWIMFix (paramName p) [] (Var local_acc) vec_is

              sComment "Load next params" $
                forM_ (zip (nextParams slug) red_res) $ \(p, (res, res_is)) ->
                  copyDWIMFix (paramName p) [] res (res_is ++ vec_is)

              sComment "SegRed body" $
                compileStms mempty (bodyStms $ slugBody slug) $
                  forM_ (zip local_accs $ map resSubExp $ bodyResult $ slugBody slug) $
                    \(local_acc, se) ->
                      copyDWIMFix local_acc vec_is se []
      emit postbody

    -- Read back results
    forM_ (zip slugs slug_local_accs_uni) $ \(slug, local_accs) ->
      forM (zip (slugResArrs slug) local_accs) $ \(acc, local_acc) ->
        copyDWIMFix acc [Imp.le64 $ segFlat space] (Var local_acc) []

  free_params <- freeParams fbody
  emit $ Imp.Op $ Imp.ParLoop "segred_stage_1" fbody free_params

sForISPC' :: VName -> Imp.Exp -> ImpM rep r Imp.Multicore () -> ImpM rep r Imp.Multicore ()
sForISPC' i bound body = do
  let it = case primExpType bound of
        IntType bound_t -> bound_t
        t -> error $ "sFor': bound " ++ pretty bound ++ " is of type " ++ pretty t
  addLoopVar i it
  body' <- collect body
  emit $ Imp.Op $ Imp.ForEach i bound body'

sForISPC :: String -> Imp.TExp t -> (Imp.TExp t -> ImpM rep r Imp.Multicore ()) -> ImpM rep r Imp.Multicore ()
sForISPC i bound body = do
  i' <- newVName i
  sForISPC' i' (untyped bound) $
    body $ TPrimExp $ Imp.var i' $ primExpType $ untyped bound

-- Like sLoopNest, but puts a foreach at the innermost layer
sLoopNestISPC ::
  Shape ->
  ([Imp.TExp Int64] -> ImpM rep r Imp.Multicore ()) ->
  ImpM rep r Imp.Multicore ()
sLoopNestISPC = sLoopNest' [] . shapeDims
  where
    sLoopNest' is [] f = f $ reverse is
    sLoopNest' is [d] f =
      sForISPC "nest_i" (toInt64Exp d) $ \i -> sLoopNest' (i : is) [] f
    sLoopNest' is (d : ds) f =
      sFor "nest_i" (toInt64Exp d) $ \i -> sLoopNest' (i : is) ds f

-- Codegen for a reduction on arrays, where the body is a perfect nesteed map.
reductionStage1Array ::
  SegSpace ->
  [SegBinOpSlug] ->
  DoSegBody ->
  MulticoreGen ()
reductionStage1Array space slugs kbody = do
  let (is, ns) = unzip $ unSegSpace space
      ns' = map toInt64Exp ns
  -- Create local accumulator variables in which we carry out the
  -- sequential reduction of this function.  If we are dealing with
  -- vectorised operators, then this implies a private allocation.  If
  -- the original operand type of the reduction is a memory block,
  -- then our hands are unfortunately tied, and we have to use exactly
  -- that memory.  This is likely to be slow.

  fbody <- collect $ do
    dPrim_ (segFlat space) int64
    sOp $ Imp.GetTaskId (segFlat space)

    prebody1 <- collect $ dScope Nothing $ scopeOfLParams $ concatMap slugParams slugs
    let genAccs =
          collect' $ do
            forM slugs $ \slug -> do
              let shape = segBinOpShape $ slugOp slug

              forM (zip (accParams slug) (slugNeutral slug)) $ \(p, ne) -> do
                -- Declare accumulator variable.
                acc <-
                  let typ = paramType p in
                  case typ of
                    Prim pt
                      | shape == mempty -> do
                        name <- tvVar <$> dPrim "local_acc" pt
                        pure (name, typ)
                      | otherwise -> do
                        name <- sAllocArray "local_acc" pt shape DefaultSpace
                        pure (name, typ)
                    _ ->
                      pure (paramName p, typ)

                -- Now neutral-initialise the accumulator.
                sLoopNest (slugShape slug) $ \vec_is ->
                  copyDWIMFix (fst acc) vec_is ne []

                pure acc

    (slug_local_accs_pairs, prebody2) <- genAccs
    let prebody = prebody1 Imp.:>>: prebody2

    let slug_local_accs = map (map fst) slug_local_accs_pairs

    inISPC [] $ do
      emit prebody
      generateChunkLoop "SegRed" False $ \i -> do
        zipWithM_ dPrimV_ is $ unflattenIndex ns' i
        kbody $ \all_red_res -> do
          let all_red_res' = segBinOpChunks (map slugOp slugs) all_red_res
          forM_ (zip3 all_red_res' slugs slug_local_accs) $ \(red_res, slug, local_accs) ->
            sLoopNestISPC (slugShape slug) $ \vec_is -> do
              let lamtypes = lambdaReturnType $ segBinOpLambda $ slugOp slug
              -- Load accum params
              sComment "Load accum params" $
                forM_ (zip3 (accParams slug) local_accs lamtypes) $
                  \(p, local_acc, t) ->
                    when (primType t) $
                      copyDWIMFix (paramName p) [] (Var local_acc) vec_is

              sComment "Load next params" $
                forM_ (zip (nextParams slug) red_res) $ \(p, (res, res_is)) ->
                  copyDWIMFix (paramName p) [] res (res_is ++ vec_is)

              sComment "SegRed body" $
                compileStms mempty (bodyStms $ slugBody slug) $
                  forM_ (zip local_accs $ map resSubExp $ bodyResult $ slugBody slug) $
                    \(local_acc, se) ->
                      copyDWIMFix local_acc vec_is se []

    -- Read back results
    forM_ (zip slugs slug_local_accs) $ \(slug, local_accs) ->
      forM (zip (slugResArrs slug) local_accs) $ \(acc, local_acc) ->
        copyDWIMFix acc [Imp.le64 $ segFlat space] (Var local_acc) []

  free_params <- freeParams fbody
  emit $ Imp.Op $ Imp.ParLoop "segred_stage_1" fbody free_params

reductionStage2 ::
  Pat MCMem ->
  SegSpace ->
  Imp.TExp Int32 ->
  [SegBinOpSlug] ->
  MulticoreGen ()
reductionStage2 pat space nsubtasks slugs = do
  let per_red_pes = segBinOpChunks (map slugOp slugs) $ patElems pat
      phys_id = Imp.le64 (segFlat space)
  sComment "neutral-initialise the output" $
    forM_ (zip (map slugOp slugs) per_red_pes) $ \(red, red_res) ->
      forM_ (zip red_res $ segBinOpNeutral red) $ \(pe, ne) ->
        sLoopNest (segBinOpShape red) $ \vec_is ->
          copyDWIMFix (patElemName pe) vec_is ne []

  dScope Nothing $ scopeOfLParams $ concatMap slugParams slugs

  sFor "i" nsubtasks $ \i' -> do
    mkTV (segFlat space) int64 <-- i'
    sComment "Apply main thread reduction" $
      forM_ (zip slugs per_red_pes) $ \(slug, red_res) ->
        sLoopNest (slugShape slug) $ \vec_is -> do
          sComment "load acc params" $
            forM_ (zip (accParams slug) red_res) $ \(p, pe) ->
              copyDWIMFix (paramName p) [] (Var $ patElemName pe) vec_is
          sComment "load next params" $
            forM_ (zip (nextParams slug) (slugResArrs slug)) $ \(p, acc) ->
              copyDWIMFix (paramName p) [] (Var acc) (phys_id : vec_is)
          sComment "red body" $
            compileStms mempty (bodyStms $ slugBody slug) $
              forM_ (zip red_res $ map resSubExp $ bodyResult $ slugBody slug) $
                \(pe, se') -> copyDWIMFix (patElemName pe) vec_is se' []

-- Each thread reduces over the number of segments
-- each of which is done sequentially
-- Maybe we should select the work of the inner loop
-- based on n_segments and dimensions etc.
segmentedReduction ::
  Pat MCMem ->
  SegSpace ->
  [SegBinOp MCMem] ->
  DoSegBody ->
  MulticoreGen Imp.Code
segmentedReduction pat space reds kbody =
  collect $ do
    body <- compileSegRedBody pat space reds kbody
    free_params <- freeParams body
    emit $ Imp.Op $ Imp.ParLoop "segmented_segred" body free_params

compileSegRedBody ::
  Pat MCMem ->
  SegSpace ->
  [SegBinOp MCMem] ->
  DoSegBody ->
  MulticoreGen Imp.Code
compileSegRedBody pat space reds kbody = do
  let (is, ns) = unzip $ unSegSpace space
      ns_64 = map toInt64Exp ns
      inner_bound = last ns_64
  dPrim_ (segFlat space) int64
  sOp $ Imp.GetTaskId (segFlat space)

  let per_red_pes = segBinOpChunks reds $ patElems pat
  -- Perform sequential reduce on inner most dimension
  collect . generateChunkLoop "SegRed" False $ \n_segments -> do
    flat_idx <- dPrimVE "flat_idx" $ n_segments * inner_bound
    zipWithM_ dPrimV_ is $ unflattenIndex ns_64 flat_idx
    sComment "neutral-initialise the accumulators" $
      forM_ (zip per_red_pes reds) $ \(pes, red) ->
        forM_ (zip pes (segBinOpNeutral red)) $ \(pe, ne) ->
          sLoopNest (segBinOpShape red) $ \vec_is ->
            copyDWIMFix (patElemName pe) (map Imp.le64 (init is) ++ vec_is) ne []

    sComment "main body" $ do
      dScope Nothing $ scopeOfLParams $ concatMap (lambdaParams . segBinOpLambda) reds
      sFor "i" inner_bound $ \i -> do
        zipWithM_
          (<--)
          (map (`mkTV` int64) $ init is)
          (unflattenIndex (init ns_64) (sExt64 n_segments))
        dPrimV_ (last is) i
        kbody $ \all_red_res -> do
          let red_res' = chunks (map (length . segBinOpNeutral) reds) all_red_res
          forM_ (zip3 per_red_pes reds red_res') $ \(pes, red, res') ->
            sLoopNest (segBinOpShape red) $ \vec_is -> do
              sComment "load accum" $ do
                let acc_params = take (length (segBinOpNeutral red)) $ (lambdaParams . segBinOpLambda) red
                forM_ (zip acc_params pes) $ \(p, pe) ->
                  copyDWIMFix (paramName p) [] (Var $ patElemName pe) (map Imp.le64 (init is) ++ vec_is)

              sComment "load new val" $ do
                let next_params = drop (length (segBinOpNeutral red)) $ (lambdaParams . segBinOpLambda) red
                forM_ (zip next_params res') $ \(p, (res, res_is)) ->
                  copyDWIMFix (paramName p) [] res (res_is ++ vec_is)

              sComment "apply reduction" $ do
                let lbody = (lambdaBody . segBinOpLambda) red
                compileStms mempty (bodyStms lbody) $
                  sComment "write back to res" $
                    forM_ (zip pes $ map resSubExp $ bodyResult lbody) $
                      \(pe, se') -> copyDWIMFix (patElemName pe) (map Imp.le64 (init is) ++ vec_is) se' []
