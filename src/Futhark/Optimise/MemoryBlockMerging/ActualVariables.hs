{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
-- | Find the actual variables that need updating when a variable attribute
-- needs updating.  This is different than variable aliasing: Variable aliasing
-- is a theoretical concept, while this module has the practical purpose of
-- finding any extra variables that also need a change when a variable has a
-- change of memory block.
module Futhark.Optimise.MemoryBlockMerging.ActualVariables
  ( findActualVariables
  ) where

import qualified Data.Set as S
import qualified Data.Map.Strict as M
import qualified Data.List as L
import Data.Maybe (fromMaybe, mapMaybe, catMaybes)
import Control.Monad
import Control.Monad.RWS

import Futhark.Representation.AST
import Futhark.Representation.ExplicitMemory (
  ExplicitMemorish, ExplicitMemory, InKernel)
import qualified Futhark.Representation.ExplicitMemory as ExpMem
import Futhark.Representation.Kernels.Kernel

import Futhark.Optimise.MemoryBlockMerging.Miscellaneous
import Futhark.Optimise.MemoryBlockMerging.Types
import Futhark.Optimise.MemoryBlockMerging.AllExpVars


data Context = Context
  { ctxVarToMem :: VarMemMappings MemorySrc
  , ctxFirstUses :: FirstUses
  }
  deriving (Show)

newtype FindM lore a = FindM { unFindM :: RWS Context () ActualVariables a }
  deriving (Monad, Functor, Applicative,
            MonadReader Context,
            MonadState ActualVariables)

type LoreConstraints lore = (ExplicitMemorish lore,
                             FullWalk lore,
                             LookInKernelExp lore)

coerce :: (ExplicitMemorish flore, ExplicitMemorish tlore) =>
          FindM flore a -> FindM tlore a
coerce = FindM . unFindM

recordActuals :: VName -> Names -> FindM lore ()
recordActuals stmt_var more_actuals = do
  -- If S.empty has already been recorded, keep it at that.  This is because the
  -- ActualVariables system is currently also used for disabling memory block
  -- optimisations -- if a variables resolves to the empty set, don't touch it.
  -- This keeps some edge cases simple.  FIXME at some point.
  current_actuals <- M.lookup stmt_var <$> get
  case S.null <$> current_actuals of
    Just True -> return ()
    _ -> modify (insertOrUpdateMany stmt_var more_actuals)

findActualVariables :: LoreConstraints lore =>
                       VarMemMappings MemorySrc -> FirstUses ->
                       FunDef lore -> ActualVariables
findActualVariables var_mem_mappings first_uses fundef =
  let context = Context var_mem_mappings first_uses
      m = unFindM $ lookInBody $ funDefBody fundef
      actual_variables = fst $ execRWS m context M.empty
  in actual_variables

lookInBody :: LoreConstraints lore =>
              Body lore -> FindM lore ()
lookInBody (Body _ bnds _res) =
  mapM_ lookInStm bnds

lookInKernelBody :: LoreConstraints lore =>
                    KernelBody lore -> FindM lore ()
lookInKernelBody (KernelBody _ bnds _res) =
  mapM_ lookInStm bnds

lookInStm :: LoreConstraints lore =>
             Stm lore -> FindM lore ()
lookInStm stm@(Let (Pattern patctxelems patvalelems) _ e) = do
  forM_ patvalelems $ \(PatElem var bindage _) ->
    case bindage of
      BindInPlace _ orig _ -> do
        -- Record that when coalescing an in-place update statement, also look
        -- at the original array.
        let actuals = S.fromList [var, orig]
        recordActuals var actuals
      _ -> return ()

  -- Special handling of loops, ifs, etc.
  case e of
    DoLoop _mergectxparams mergevalparams _loopform body -> do
      let body_vars0 = mapMaybe (fromVar . snd) mergevalparams
          body_vars1 = map (paramName . fst) mergevalparams
          body_vars2 = S.toList $ findAllExpVars e
          body_vars = body_vars0 ++ body_vars1 ++ body_vars2
      forM_ patvalelems $ \(PatElem var _ membound) -> do
        case membound of
          ExpMem.ArrayMem _ _ _ mem _ -> do
            -- If mem is existential, we need to find the return memory that it
            -- refers to.  We cannot just look at its memory aliases, since it
            -- likely aliases both the initial memory and the final memory.

            let zipped = zip patctxelems (bodyResult body)
                mem_search = case L.find ((== mem) . patElemName . fst) zipped of
                  Just (_, Var res_mem) -> res_mem
                  _ -> mem
            -- Find the ones using the same memory as the result of the loop
            -- expression.
            body_vars' <- filterM (lookupGivesMem mem_search) body_vars
            -- Not only the result variable needs to change its memory block in case
            -- of a future coalescing with it; also the variables extracted above.
            -- FIXME: This is probably an okay way to do it?  What if the memory is
            -- used, but with a different index function?  Can that happen?
            let actuals = var : body_vars'
            forM_ actuals $ \a -> recordActuals a (S.fromList actuals)
            -- Some of these can be changed later on to have an actual variable
            -- set of S.empty, e.g. if one of the variables using the memory is
            -- a rearrange operation.  This is fine, and will occur in the walk
            -- later on.

            -- If you extend this loop handling, make sure not to target existential
            -- memory blocks.  We want those to stay.
          _ -> return ()

        -- It seems wrong to change the memory of merge variables, so we disable
        -- it.  If we were to accept it, we would need to record what other
        -- variables to change as well.  Seems hard.
        recordActuals var S.empty

    If _se body_then body_else _types ->
      -- We don't want to coalesce the existiential memory block of the if.
      -- However, if a branch result has a memory block that is firstly used
      -- inside the branch, it is okay to coalesce that in a future statement.
      forM_ (zip3 patvalelems (bodyResult body_then) (bodyResult body_else))
        $ \(PatElem var _ membound, res_then, res_else) -> do
        let body_vars = S.toList $ findAllExpVars e
        case membound of
          ExpMem.ArrayMem _ _ _ mem _ ->
            if mem `L.elem` map patElemName patctxelems
              then
              -- If the memory block is existential, we say that the If result
              -- refers to all results in the If.
              recordActuals var
              $ S.fromList (var : catMaybes [fromVar res_then, fromVar res_else])

              else do
              -- If the memory block is not existential, we need to find all the
              -- variables in any sub-bodies using the same memory block (like
              -- with loops).
              body_vars' <- filterM (lookupGivesMem mem) body_vars

              first_uses <- asks ctxFirstUses
              case filter ((mem `S.member`) . (`lookupEmptyable` first_uses)) body_vars' of
                [] ->
                  -- Not just the result variable needs to change its memory
                  -- block in case of a future coalescing with it; also the
                  -- variables extracted above.  FIXME: This is probably an okay
                  -- way to do it?  What if the memory is used, but with a
                  -- different index function?  Can that happen?
                  recordActuals var $ S.fromList (var : body_vars')
                _ ->
                  -- If we come across a non-existential If which can be said to
                  -- create a new array *and* which has one or more bodies which
                  -- can also be said to create a new array *in the same memory*
                  -- (i.e. has first memory uses), then we disable it.  This is
                  -- not at all an impossible case to handle, but such a loop is
                  -- weird, since it would make more sense if it had existential
                  -- memory, so maybe something needs to be done somewhere else
                  -- in the compiler?  If this is naively enabled, we can get an
                  -- error because the sub-body results are first uses while the
                  -- main result is not.  This can be "fixed" by stating that
                  -- the If as a whole is also a first use of the memory, but
                  -- this seems too conservative.
                  forM_ (var : body_vars') $ \v -> recordActuals v S.empty

          _ -> return ()

    BasicOp (Index _ orig _) -> do
      let ielem = head patvalelems -- Should be okay.
          var = patElemName ielem
      case patElemAttr ielem of
        ExpMem.ArrayMem{} -> do
          -- Disable merging for index expressions that return arrays.  Maybe
          -- too restrictive.
          recordActuals var S.empty
          -- Make sure the source also updates the memory of the index when
          -- updated.  The array might be an aliasing operation, in which case
          -- we try to find the original array.
          orig' <- fromMaybe orig <$> aliasOpRoot orig
          recordActuals orig' $ S.fromList [orig', var]
        _ -> return ()

    -- Support reusing the memory of reshape operations by recording the origin
    -- array that is being reshaped.
    BasicOp (Reshape _ shapechange_var orig) ->
      forM_ (map patElemName patvalelems) $ \var -> do
        mem_orig <- M.lookup orig <$> asks ctxVarToMem
        case (shapechange_var, mem_orig) of
          ([_], Just (MemorySrc _ _ (Shape [_]))) ->
            recordActuals var $ S.fromList [var, orig]
            -- Works, but only in limited cases where the reshape is not even
            -- that useful to begin with.
          _ ->
            recordActuals var S.empty
            -- FIXME: The problem with these more complex cases is that a slice
            -- is relative to the shape of the reshaped array, and not the
            -- original array.  Disabled for now.
        recordActuals orig $ S.fromList [orig, var]

    -- For the other aliasing operations, disable their use for now.  If the
    -- source has a change of memory block, make sure to change this as well.
    BasicOp (Rearrange _ _ orig) ->
      aliasOpHandle patvalelems orig

    BasicOp (Split _ _ _ orig) ->
      aliasOpHandle patvalelems orig

    BasicOp (Rotate _ _ orig) ->
      aliasOpHandle patvalelems orig

    BasicOp (Opaque (Var orig)) ->
      aliasOpHandle patvalelems orig

    _ -> forM_ patvalelems $ \(PatElem var _ membound) -> do
      let body_vars = S.toList $ findAllExpVars e
      case membound of
        ExpMem.ArrayMem _ _ _ mem _ -> do
          body_vars' <- filterM (lookupGivesMem mem) body_vars
          recordActuals var $ S.fromList (var : body_vars')
        _ -> return ()

  lookInKernelExp stm

  fullWalkExpM walker walker_kernel e
  where walker = identityWalker
          { walkOnBody = lookInBody }
        walker_kernel = identityKernelWalker
          { walkOnKernelBody = coerce . lookInBody
          , walkOnKernelKernelBody = coerce . lookInKernelBody
          , walkOnKernelLambda = coerce . lookInBody . lambdaBody
          }

-- If we have a rotate or similar, we want to find the original array and
-- associate *that* with this aliasing array, so that changes to the original
-- array will affect this one as well.
aliasOpHandle :: [PatElem lore] -> VName -> FindM lore ()
aliasOpHandle patvalelems orig =
  forM_ (map patElemName patvalelems) $ \var -> do
    recordActuals var S.empty
    orig' <- fromJust "at some point there will have been a proper statement"
             <$> aliasOpRoot orig
    recordActuals orig' $ S.fromList [orig', var]

aliasOpRoot :: VName -> FindM lore (Maybe VName)
aliasOpRoot orig = do
  current_actuals <- get
  case S.null <$> M.lookup orig current_actuals of
    -- If the original array is itself an aliasing operation, find the *actual*
    -- original array.
    Just True -> case M.keys (M.filter (orig `S.member`) current_actuals) of
      [orig'] -> return $ Just orig'
      _ -> return Nothing
    -- Else, just return orig.
    _ -> return $ Just orig

lookupGivesMem :: VName -> VName -> FindM lore Bool
lookupGivesMem mem v = do
  m <- M.lookup v <$> asks ctxVarToMem
  return (Just mem == (memSrcName <$> m))

class LookInKernelExp lore where
  lookInKernelExp :: Stm lore -> FindM lore ()

instance LookInKernelExp ExplicitMemory where
  lookInKernelExp (Let (Pattern _ patvalelems) _ e) = case e of
    Op (ExpMem.Inner (Kernel _ _ _ _ (KernelBody _ _ ress))) ->
      zipWithM_ (\(PatElem var _ _) res -> case res of
                    WriteReturn _ arr _ _ ->
                      recordActuals arr $ S.singleton var
                    _ -> return ()
                ) patvalelems ress
    _ -> return ()

instance LookInKernelExp InKernel where
  lookInKernelExp (Let _ _ e) = case e of
    Op (ExpMem.Inner ke) -> case ke of
      ExpMem.GroupReduce _ _ input -> do
        let arrs = map snd input
        extendActualVarsInKernel e arrs
      ExpMem.GroupScan _ _ input -> do
        let arrs = map snd input
        extendActualVarsInKernel e arrs
      ExpMem.GroupStream _ _ _ _ arrs ->
        extendActualVarsInKernel e arrs
      _ -> return ()
    _ -> return ()

extendActualVarsInKernel :: Exp InKernel -> [VName] -> FindM InKernel ()
extendActualVarsInKernel e arrs = forM_ arrs $ \var -> do
  mem0 <- M.lookup var <$> asks ctxVarToMem

  -- The array might be an aliasing operation, in which case we try to find the
  -- original array.
  var' <- fromMaybe var <$> aliasOpRoot var
  case mem0 of
    Just mem -> do
      let body_vars = S.toList $ findAllExpVars e
      body_vars' <- filterM (lookupGivesMem $ memSrcName mem) body_vars
      let actuals = S.fromList (var' : body_vars')

      body_vars_mems <- mapM (\v -> M.lookup v <$> asks ctxVarToMem) body_vars
      let debug = do
            putStrLn $ replicate 70 '~'
            putStrLn "extendActualVarsInKernel:"
            putStrLn $ pretty var
            putStrLn $ pretty var'
            putStrLn $ prettySet (S.fromList body_vars)
            print body_vars_mems
            putStrLn $ prettySet (S.fromList body_vars')
            putStrLn $ replicate 70 '~'
      withDebug debug $ recordActuals var' actuals
    Nothing -> return ()
