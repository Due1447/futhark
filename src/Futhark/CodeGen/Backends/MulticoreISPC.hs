{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

-- | C code generator.  This module can convert a correct ImpCode
-- program to an equivalent ISPC program.
module Futhark.CodeGen.Backends.MulticoreISPC
  ( compileProg,
    GC.CParts (..),
    GC.asLibrary,
    GC.asExecutable,
    GC.asServer,
    operations,
  )
where

import Control.Monad
import qualified Data.Text as T
import Futhark.CodeGen.ImpCode.Multicore
import qualified Futhark.CodeGen.ImpGen.Multicore as ImpGen
import Futhark.IR.MCMem (MCMem, Prog)
import Futhark.MonadFreshNames
import qualified Language.C.Quote.ISPC as C
import qualified Language.C.Syntax as C
import qualified Futhark.CodeGen.Backends.GenericC as GC
import qualified Futhark.CodeGen.Backends.MulticoreC as MC
import qualified Futhark.CodeGen.ImpCode as Imp
import Futhark.CodeGen.RTS.C (errorsH, ispcUtilH, uniformH)
import Futhark.CodeGen.Backends.SimpleRep (toStorage, primStorageType, cScalarDefs, funName, defaultMemBlockType)
import Data.Maybe
import Data.Loc (noLoc)
import qualified Data.DList as DL
import NeatInterpolation (untrimming)
import Futhark.Util.Pretty (prettyText)

type ISPCState = (DL.DList C.Definition)
type ISPCCompilerM a = GC.CompilerM Multicore ISPCState a

makeFunctionBinding :: (Name, Function Multicore) -> ISPCCompilerM ()
makeFunctionBinding (fname, Function _ outputs inputs _ _ _) = do
  outparams <- mapM compileOutput outputs
  inparams <- mapM compileInput inputs
  let def = [C.cedecl|extern "C" unmasked uniform int $id:(funName fname)(uniform struct futhark_context * uniform ctx,
                      $params:outparams, $params:inparams);|]
  --GC.modifyUserState (\s -> DL.singleton def <> s)
  -- TODO(pema, K, obp): This is just a proof concept for how one could generate bindings from ImpCode functions.
  -- You can comment out the line above this to see how it works. It's sort of copy pasta'd from compileFun.
  -- For each function, we need to:
  --   1. Generate a new C function which doesn't pass structs by value.
  --   2. Generate a binding for that new C function in ISPC.
  --   3. Make sure the names match.
  pure ()
  where
    compileInput (ScalarParam name bt) = do
      let ctp = GC.primTypeToCType bt
      pure [C.cparam|$ty:ctp $id:name|]
    compileInput (MemParam name space) = do
      ty <- GC.memToCType name space
      pure [C.cparam|$ty:ty $id:name|]

    compileOutput (ScalarParam name bt) = do
      let ctp = GC.primTypeToCType bt
      p_name <- newVName $ "out_" ++ baseString name
      pure [C.cparam|$ty:ctp *$id:p_name|]
    compileOutput (MemParam name space) = do
      ty <- GC.memToCType name space
      p_name <- newVName $ baseString name ++ "_p"
      pure [C.cparam|$ty:ty *$id:p_name|]

-- | Compile the program to C and ISPC code using multicore operations.
compileProg ::
  MonadFreshNames m => T.Text -> T.Text -> Prog MCMem -> m (ImpGen.Warnings, (GC.CParts, T.Text))
compileProg header version prog = do
  (ws, defs) <- ImpGen.compileProg prog
  let Functions funs = defFuns defs

  (ws', (cparts, endstate)) <-
    traverse
      (GC.compileProg'
        "ispc_multicore"
        version
        operations
        (MC.generateContext >> mapM_ makeFunctionBinding funs)
        header
        [DefaultSpace]
        MC.cliOptions
      ) (ws, defs)

  let ispc_decls = T.unlines $ map prettyText $ DL.toList $ GC.compUserState endstate
  let ispcdefs =
        [untrimming|
#define bool uint8 // This is a workaround around an ISPC bug, stdbool doesn't get included
typedef int64 int64_t;
typedef int32 int32_t;
typedef int16 int16_t;
typedef int8 int8_t;
typedef int8 char;
typedef unsigned int64 uint64_t;
typedef unsigned int32 uint32_t;
typedef unsigned int16 uint16_t;
typedef unsigned int8 uint8_t;

$errorsH

#define INFINITY (floatbits((uniform int)0x7f800000))
#define NAN (floatbits((uniform int)0x7fc00000))
#define fabs(x) abs(x)
#define FUTHARK_F64_ENABLED
$cScalarDefs

$uniformH

$ispcUtilH

#ifndef __ISPC_STRUCT_memblock__
#define __ISPC_STRUCT_memblock__
struct memblock {
    int32_t * references;
    uint8_t * mem;
    int64_t size;
    const int8_t * desc;
};
#endif

$ispc_decls|]

  pure (ws', (cparts, ispcdefs))

operations :: GC.Operations Multicore ISPCState
operations =
  MC.operations
    { GC.opsCompiler = compileOp
    }

ispcDecl :: C.Definition  -> ISPCCompilerM ()
ispcDecl def =
  GC.modifyUserState (\s -> s <> DL.singleton def)

ispcDef :: MC.DefSpecifier ISPCState
ispcDef s f = do
  s' <- MC.multicoreName s
  ispcDecl =<< f s'
  pure s'

sharedDef :: MC.DefSpecifier ISPCState
sharedDef s f = do
  s' <- MC.multicoreName s
  ispcDecl =<< f s'
  -- Workaround for https://github.com/ispc/ispc/issues/2277
  dummy <- newVName "dummy_struct_usage"
  ispcDecl [C.cedecl|export void $id:dummy(uniform struct $id:s' * uniform a) { (void)a; }|]
  pure s'

makeStringLiteral :: String -> ISPCCompilerM Name
makeStringLiteral str = do
  name <- MC.multicoreDef "strlit_shim" $ \s ->
    pure [C.cedecl|char* $id:s() { return $string:str; }|]
  ispcDecl
    [C.cedecl|extern "C" unmasked uniform char* uniform $id:name();|]
  pure name

allocMemISPC :: (C.ToExp a, C.ToExp b) => a -> b -> Space -> C.Stm -> ISPCCompilerM ()
allocMemISPC mem size space on_failure = GC.allocMem' mem size space on_failure stmt
  where
    stmt space' mem' size' mem_s' on_failure' = do
      strlit <- makeStringLiteral mem_s'
      pure
        [C.cstm|if ($id:(GC.fatMemAlloc space')(ctx, &$exp:mem', $exp:size',
                  $id:strlit())) {
                  $stm:on_failure'
        }|]

setMemISPC :: (C.ToExp a, C.ToExp b) => a -> b -> Space -> ISPCCompilerM ()
setMemISPC dest src space = GC.setMem' dest src space stmt
  where
    stmt space' dest' src' src_s' = do
      strlit <- makeStringLiteral src_s'
      pure
        [C.cstm|if ($id:(GC.fatMemSet space')(ctx, &$exp:dest', &$exp:src',
          $id:strlit()) != 0) {
          err = 1;
        }|]

unRefMemISPC :: C.ToExp a => a -> Space -> ISPCCompilerM ()
unRefMemISPC mem space = GC.unRefMem' mem space cstm
  where
    cstm s m m_s = do
      strlit <- makeStringLiteral m_s
      pure
        [C.cstm|if ($id:(GC.fatMemUnRef s)(ctx, &$exp:m, $id:strlit()) != 0) {
          err = 1;
        }|]

freeAllocatedMemISPC :: ISPCCompilerM [C.BlockItem]
freeAllocatedMemISPC = GC.freeAllocatedMem' unRefMemISPC

-- Handle printing an error message in ISPC
errorInISPC :: ErrorMsg Exp -> String -> ISPCCompilerM ()
errorInISPC msg stacktrace = do
  -- Get format sting
  (formatstr, formatargs) <- GC.errorMsgString msg
  let formatstr' = "Error: " <> formatstr <> "\n\nBacktrace:\n%s"
  -- Get args types and names for shim
  let arg_types = errorMsgArgTypes msg
  arg_names <- mapM (newVName . const "arg") arg_types
  let params = zipWith (\ty name -> [C.cparam|$ty:(GC.primTypeToCType ty) $id:name|]) arg_types arg_names
  let params_uni = zipWith (\ty name -> [C.cparam|uniform $ty:(GC.primTypeToCType ty) $id:name|]) arg_types arg_names
  -- Make shim
  let formatargs' = mapArgNames msg formatargs arg_names
  shim <- MC.multicoreDef "assert_shim" $ \s -> do
    pure
      [C.cedecl|void $id:s(struct futhark_context* ctx, $params:params) {
        ctx->error = msgprintf($string:formatstr', $args:formatargs', $string:stacktrace);
      }|]
  ispcDecl
    [C.cedecl|extern "C" unmasked void $id:shim(uniform struct futhark_context* uniform, $params:params_uni);|]
  -- Call the shim
  args <- getErrorValExps msg
  uni <- newVName "uni"
  let args' = map (\x -> [C.cexp|extract($exp:x, $id:uni)|]) args
  GC.items
    [C.citems|
      foreach_active($id:uni) {
        $id:shim(ctx, $args:args');
        err = FUTHARK_PROGRAM_ERROR;
      }|]
  where
    getErrorVal (ErrorString _) = Nothing
    getErrorVal (ErrorVal _ v) = Just v

    getErrorValExps (ErrorMsg m) = mapM GC.compileExp $ mapMaybe getErrorVal m

    mapArgNames' (x:xs) (y:ys) (t:ts)
      | isJust $ getErrorVal x = [C.cexp|$id:t|] : mapArgNames' xs ys ts
      | otherwise = y : mapArgNames' xs ys (t:ts)
    mapArgNames' _ ys [] = ys
    mapArgNames' _ _ _ = []

    mapArgNames (ErrorMsg parts) = mapArgNames' parts

isConstExp :: PrimExp VName -> Bool
isConstExp = isSimple . constFoldPrimExp
  where isSimple (ValueExp _) = True
        isSimple _ = False

-- TODO(pema): Deduplicate some of the C code in the generic C generator
-- Compile a block of code with ISPC specific semantics, falling back
-- to generic C when this semantics is not needed.
compileCodeISPC :: Imp.Variability -> MCCode -> ISPCCompilerM ()
compileCodeISPC vari (Comment s code) = do
  xs <- GC.collect $ compileCodeISPC vari code
  let comment = "// " ++ s
  GC.stm
    [C.cstm|$comment:comment
              { $items:xs }
             |]
compileCodeISPC vari (DeclareScalar name vol t) = do
  let ct = GC.primTypeToCType t
  GC.decl [C.cdecl|$tyquals:(GC.volQuals vol) $tyquals:(GC.variQuals vari) $ty:ct $id:name;|]
compileCodeISPC _ (DeclareArray name DefaultSpace t vs) = do
  name_realtype <- newVName $ baseString name ++ "_realtype"
  let ct = GC.primTypeToCType t
  case vs of
    ArrayValues vs' -> do
      let vs'' = [[C.cinit|$exp:v|] | v <- vs']
      GC.earlyDecl [C.cedecl|static $ty:ct $id:name_realtype[$int:(length vs')] = {$inits:vs''};|]
    ArrayZeros n ->
      GC.earlyDecl [C.cedecl|static $ty:ct $id:name_realtype[$int:n];|]
  -- Fake a memory block.
  GC.contextField
    (C.toIdent name noLoc)
    [C.cty|struct memblock|]
    $ Just [C.cexp|(struct memblock){NULL, (char*)$id:name_realtype, 0}|]
  -- Make an exported C shim to access it
  shim <- MC.multicoreDef "get_static_array_shim" $ \f ->
    pure [C.cedecl|struct memblock* $id:f(struct futhark_context* ctx) { return &ctx->$id:name; }|]
  ispcDecl [C.cedecl|extern "C" unmasked uniform struct memblock * uniform
                        $id:shim(uniform struct futhark_context* uniform ctx);|]
  -- Call it
  GC.item [C.citem|uniform struct memblock $id:name = *$id:shim(ctx);|]
compileCodeISPC vari (c1 :>>: c2) = go (GC.linearCode (c1 :>>: c2))
  where
    go (DeclareScalar name vol t : SetScalar dest e : code)
      | name == dest = do
        let ct = GC.primTypeToCType t
        e' <- GC.compileExp e
        GC.item [C.citem|$tyquals:(GC.volQuals vol) $tyquals:(GC.variQuals vari)  $ty:ct $id:name = $exp:e';|]
        go code
    go (x : xs) = compileCodeISPC vari x >> go xs
    go [] = pure ()
compileCodeISPC _ (Allocate name (Count (TPrimExp e)) space) = do
  size <- GC.compileExp e
  cached <- GC.cacheMem name
  case cached of
    Just cur_size ->
      GC.stm -- TODO(pema): Handle errors here
        [C.cstm|if ($exp:cur_size < $exp:size) {
                  lexical_realloc_ispc(&$exp:name, &$exp:cur_size, $exp:size);
                }|]
    _ ->
      allocMemISPC name size space [C.cstm|{err = 1;}|]
compileCodeISPC _ (SetMem dest src space) =
  setMemISPC dest src space
compileCodeISPC vari code@(Write dest (Count idx) elemtype DefaultSpace vol elemexp)
  | isConstExp (untyped idx) = do
    dest' <- GC.rawMem dest
    idxexp <- GC.compileExp (untyped idx)
    tmp <- newVName "tmp_idx"
    -- Disambiguate the variability of the constant index
    GC.decl [C.cdecl|$tyquals:(GC.variQuals vari) typename int64_t $id:tmp = $exp:idxexp;|]
    let deref =
          GC.derefPointer
            dest'
            [C.cexp|$id:tmp|]
            [C.cty|$tyquals:(GC.volQuals vol) $ty:(primStorageType elemtype)*|]
    elemexp' <- toStorage elemtype <$> GC.compileExp elemexp
    GC.stm [C.cstm|$exp:deref = $exp:elemexp';|]
  | otherwise = GC.compileCode code
compileCodeISPC _ (Free name space) = do
  cached <- isJust <$> GC.cacheMem name
  unless cached $ unRefMemISPC name space
compileCodeISPC vari (For i bound body) = do
  let i' = C.toIdent i
      t = GC.primTypeToCType $ primExpType bound
  bound' <- GC.compileExp bound
  body' <- GC.collect $ compileCodeISPC vari body
  GC.stm -- TODO(pema): This is unsafe is the bound is varying
    [C.cstm|for (uniform $ty:t $id:i' = 0; $id:i' < $exp:bound'; $id:i'++) {
            $items:body'
          }|]
compileCodeISPC vari (While cond body) = do
  cond' <- GC.compileExp $ untyped cond
  body' <- GC.collect $ compileCodeISPC vari body
  GC.stm
    [C.cstm|while ($exp:cond') {
            $items:body'
          }|]
compileCodeISPC vari (If cond tbranch fbranch) = do
  cond' <- GC.compileExp $ untyped cond
  tbranch' <- GC.collect $ compileCodeISPC vari tbranch
  fbranch' <- GC.collect $ compileCodeISPC vari fbranch
  GC.stm $ case (tbranch', fbranch') of
    (_, []) ->
      [C.cstm|if ($exp:cond') { $items:tbranch' }|]
    ([], _) ->
      [C.cstm|if (!($exp:cond')) { $items:fbranch' }|]
    _ ->
      [C.cstm|if ($exp:cond') { $items:tbranch' } else { $items:fbranch' }|]
compileCodeISPC _ (Assert e msg (loc, locs)) = do
  e' <- GC.compileExp e
  err <- GC.collect $ errorInISPC msg stacktrace
  GC.stm [C.cstm|if (!$exp:e') { $items:err }|]
  where
    stacktrace = prettyStacktrace 0 $ map locStr $ loc : locs
compileCodeISPC _ code =
  GC.compileCode code

compileGetStructVals ::
  Name ->
  [VName] ->
  [(C.Type, MC.ValueType)] ->
  [C.BlockItem]
compileGetStructVals struct a b = concat $ zipWith field a b
  where
    struct' = struct <> "_"
    field name (ty, MC.Prim) =
      [C.citems|$ty:ty $id:name = $id:struct'->$id:(closureFreeStructField name);|]
    field name (_, MC.MemBlock) =
      [C.citems|uniform struct memblock* uniform $id:(pretty name <> "_") = $id:(struct')->$id:(closureFreeStructField name);
                uniform struct memblock $id:name = *$id:(pretty name <> "_");|]
    field name (_, MC.RawMem) =
      [C.citems|uniform unsigned char * uniform $id:name = $id:struct'->$id:(closureFreeStructField name);|]


closureFreeStructField :: VName -> Name
closureFreeStructField v =
  nameFromString "free_" <> nameFromString (pretty v)

compileFreeStructFields :: [VName] -> [(C.Type, MC.ValueType)] -> [C.FieldGroup]
compileFreeStructFields = zipWith field
  where
    field name (ty, MC.Prim) =
      [C.csdecl|$ty:ty $id:(closureFreeStructField name);|]
    field name (_, MC.MemBlock) =
      [C.csdecl|struct memblock* $id:(closureFreeStructField name);|]
    field name (_, MC.RawMem) =
      [C.csdecl|$ty:defaultMemBlockType $id:(closureFreeStructField name);|]

compileSetStructValues ::
  C.ToIdent a =>
  a ->
  [VName] ->
  [(C.Type, MC.ValueType)] ->
  [C.Stm]
compileSetStructValues struct = zipWith field
  where
    field name (_, MC.Prim) =
      [C.cstm|$id:struct.$id:(closureFreeStructField name)=$id:name;|]
    field name (_, MC.MemBlock) =
      [C.cstm|$id:struct.$id:(closureFreeStructField name)=& $id:name;|]
    field name (_, MC.RawMem) =
      [C.cstm|$id:struct.$id:(closureFreeStructField name)=$id:name;|]

prepareTaskStruct ::
  MC.DefSpecifier s ->
  String ->
  [VName] ->
  [(C.Type, MC.ValueType)] ->
  GC.CompilerM Multicore s Name
prepareTaskStruct def name free_args free_ctypes = do
  let makeStruct s = pure
        [C.cedecl|struct $id:s {
                       struct futhark_context *ctx;
                       $sdecls:(compileFreeStructFields free_args free_ctypes)
                     };|]
  fstruct <- def name makeStruct
  let fstruct' =  fstruct <> "_"
  GC.decl [C.cdecl|struct $id:fstruct $id:fstruct';|]
  GC.stm [C.cstm|$id:fstruct'.ctx = ctx;|]
  GC.stms [C.cstms|$stms:(compileSetStructValues fstruct' free_args free_ctypes)|]
  pure fstruct

-- Generate a segop function for top_level and potentially nested SegOp code
compileOp :: GC.OpCompiler Multicore ISPCState
compileOp (SegOp name params seq_task par_task retvals (SchedulerInfo e sched)) = do
  let (ParallelTask seq_code) = seq_task
  free_ctypes <- mapM MC.paramToCType params
  retval_ctypes <- mapM MC.paramToCType retvals
  let free_args = map paramName params
      retval_args = map paramName retvals
      free = zip free_args free_ctypes
      retval = zip retval_args retval_ctypes

  e' <- GC.compileExp e

  let lexical = lexicalMemoryUsageMC $ Function Nothing [] params seq_code [] []

  fstruct <-
    MC.prepareTaskStruct sharedDef "task" free_args free_ctypes retval_args retval_ctypes

  fpar_task <- MC.generateParLoopFn lexical (name ++ "_task") seq_code fstruct free retval
  MC.addTimingFields fpar_task

  let ftask_name = fstruct <> "_task"

  toC <- GC.collect $ do
    GC.decl [C.cdecl|struct scheduler_segop $id:ftask_name;|]
    GC.stm [C.cstm|$id:ftask_name.args = args;|]
    GC.stm [C.cstm|$id:ftask_name.top_level_fn = $id:fpar_task;|]
    GC.stm [C.cstm|$id:ftask_name.name = $string:(nameToString fpar_task);|]
    GC.stm [C.cstm|$id:ftask_name.iterations = iterations;|]
    -- Create the timing fields for the task
    GC.stm [C.cstm|$id:ftask_name.task_time = &ctx->$id:(MC.functionTiming fpar_task);|]
    GC.stm [C.cstm|$id:ftask_name.task_iter = &ctx->$id:(MC.functionIterations fpar_task);|]

    case sched of
        Dynamic -> GC.stm [C.cstm|$id:ftask_name.sched = DYNAMIC;|]
        Static -> GC.stm [C.cstm|$id:ftask_name.sched = STATIC;|]

    -- Generate the nested segop function if available
    fnpar_task <- case par_task of
        Just (ParallelTask nested_code) -> do
            let lexical_nested = lexicalMemoryUsageMC $ Function Nothing [] params nested_code [] []
            fnpar_task <- MC.generateParLoopFn lexical_nested (name ++ "_nested_task") nested_code fstruct free retval
            GC.stm [C.cstm|$id:ftask_name.nested_fn = $id:fnpar_task;|]
            pure $ zip [fnpar_task] [True]
        Nothing -> do
            GC.stm [C.cstm|$id:ftask_name.nested_fn=NULL;|]
            pure mempty

    GC.stm [C.cstm|return scheduler_prepare_task(&ctx->scheduler, &$id:ftask_name);|]

    -- Add profile fields for -P option
    mapM_ GC.profileReport $ MC.multiCoreReport $ (fpar_task, True) : fnpar_task

  schedn <- MC.multicoreDef "schedule_shim" $ \s ->
    pure [C.cedecl|int $id:s(struct futhark_context* ctx, void* args, typename int64_t iterations) {
        $items:toC
    }|]

  ispcDecl [C.cedecl|extern "C" unmasked uniform int $id:schedn 
                        (struct futhark_context uniform * uniform ctx, 
                        struct $id:fstruct uniform * uniform args, 
                        uniform int iterations);|]

  aos_name <- newVName "aos"
  GC.stm [C.cstm|$escstm:("#if ISPC")|]
  GC.items [C.citems|
    #if ISPC
    uniform struct $id:fstruct $id:aos_name[programCount];
    $id:aos_name[programIndex] = $id:(fstruct <> "_");
    foreach_active (i) {
      if (err == 0) {
        err = $id:schedn(ctx, &$id:aos_name[i], extract($exp:e', i));
      }
    }|]
  -- TODO(pema): We can't do much else here^^ than set the error code and hope for the best
  GC.stm [C.cstm|$escstm:("#else")|]
  GC.items [C.citems|
    err = $id:schedn(ctx, &$id:(fstruct <> "_"), $exp:e');
    if (err != 0) {
      goto cleanup;
    }|]
  GC.stm [C.cstm|$escstm:("#endif")|]

compileOp (ISPCKernel body free) = do
  free_ctypes <- mapM MC.paramToCType free
  let free_args = map paramName free

  let lexical = lexicalMemoryUsageMC $ Function Nothing [] free body [] []
  -- Generate ISPC kernel
  fstruct <- prepareTaskStruct sharedDef "param_struct" free_args free_ctypes
  let fstruct' = fstruct <> "_"

  ispcShim <- ispcDef "loop_ispc" $ \s -> do
    mainBody <- GC.inNewFunction $ GC.cachingMemory lexical $ \decl_cached free_cached ->
      GC.collect $ do
        GC.items $ compileGetStructVals fstruct free_args free_ctypes
        GC.decl [C.cdecl|uniform int err = 0;|]
        body' <- GC.collect $ compileCodeISPC Imp.Varying body
        mapM_ GC.item decl_cached
        mapM_ GC.item =<< GC.declAllocatedMem
        mapM_ GC.item body'
        free_mem <- freeAllocatedMemISPC

        GC.stm [C.cstm|cleanup: {$stms:free_cached $items:free_mem}|]
        GC.stm [C.cstm|return err;|]

    pure
      [C.cedecl|
        export static uniform int $id:s(struct futhark_context uniform * uniform ctx,
                                 uniform typename int64_t start,
                                 uniform typename int64_t end,
                                 struct $id:fstruct uniform * uniform $id:fstruct' ) {
          $items:mainBody
        }|]

  -- Generate C code to call into ISPC kernel
  GC.items [C.citems|
    err = $id:ispcShim(ctx, start, end, & $id:fstruct');
    if (err != 0) {
      goto cleanup;
    }|]

compileOp (ForEach i bound body) = do
  bound' <- GC.compileExp bound
  body' <- GC.collect $ compileCodeISPC Imp.Varying body
  GC.stm [C.cstm|
    foreach ($id:i = 0 ... extract($exp:bound', 0)) {
      $items:body'
    }|]

compileOp (ForEachActive name body) = do
  body' <- GC.collect $ compileCodeISPC Imp.Uniform body
  GC.stm [C.cstm|
    foreach_active ($id:name) {
      $items:body'
    }|]

compileOp (ExtractLane dest tar lane) = do
  tar' <- GC.compileExp tar
  lane' <- GC.compileExp lane
  GC.stm [C.cstm|$id:dest = extract($exp:tar', $exp:lane');|]

compileOp (VariabilityBlock vari code) = do
  compileCodeISPC vari code

compileOp op = MC.compileOp op
