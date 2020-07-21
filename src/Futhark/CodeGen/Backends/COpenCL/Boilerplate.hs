{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
module Futhark.CodeGen.Backends.COpenCL.Boilerplate
  ( generateBoilerplate
  , profilingEvent
  , copyDevToDev, copyDevToHost, copyHostToDev, copyScalarToDev, copyScalarFromDev

  , commonOptions
  , failureSwitch
  , costCentreReport
  , kernelRuntime
  , kernelRuns
  ) where

import Control.Monad.State
import Data.FileEmbed
import qualified Data.Map as M
import qualified Language.C.Syntax as C
import qualified Language.C.Quote.OpenCL as C

import Futhark.CodeGen.ImpCode.OpenCL
import qualified Futhark.CodeGen.Backends.GenericC as GC
import Futhark.CodeGen.Backends.GenericC.Options
import Futhark.CodeGen.OpenCL.Heuristics
import Futhark.Util (chunk, zEncodeString)

errorMsgNumArgs :: ErrorMsg a -> Int
errorMsgNumArgs = length . errorMsgArgTypes

failureSwitch :: [FailureMsg] -> C.Stm
failureSwitch failures =
  let printfEscape = let escapeChar '%' = "%%"
                         escapeChar c = [c]
                     in concatMap escapeChar
      onPart (ErrorString s) = printfEscape s
      onPart ErrorInt32{} = "%d"
      onFailure i (FailureMsg emsg@(ErrorMsg parts) backtrace) =
         let msg = concatMap onPart parts ++ "\n" ++ printfEscape backtrace
             msgargs = [ [C.cexp|args[$int:j]|] | j <- [0..errorMsgNumArgs emsg-1] ]
         in [C.cstm|case $int:i: {ctx->error = msgprintf($string:msg, $args:msgargs); break;}|]
      failure_cases =
        zipWith onFailure [(0::Int)..] failures
  in [C.cstm|switch (failure_idx) { $stms:failure_cases }|]

copyDevToDev, copyDevToHost, copyHostToDev, copyScalarToDev, copyScalarFromDev :: Name
copyDevToDev = "copy_dev_to_dev"
copyDevToHost = "copy_dev_to_host"
copyHostToDev = "copy_host_to_dev"
copyScalarToDev = "copy_scalar_to_dev"
copyScalarFromDev = "copy_scalar_from_dev"

profilingEvent :: Name -> C.Exp
profilingEvent name =
  [C.cexp|(ctx->profiling_paused || !ctx->profiling) ? NULL
          : opencl_get_event(&ctx->opencl,
                             &ctx->$id:(kernelRuns name),
                             &ctx->$id:(kernelRuntime name))|]

-- | Called after most code has been generated to generate the bulk of
-- the boilerplate.
generateBoilerplate :: String -> String -> [Name]
                    -> M.Map KernelName KernelSafety
                    -> [PrimType]
                    -> M.Map Name SizeClass
                    -> [FailureMsg]
                    -> GC.CompilerM OpenCL () ()
generateBoilerplate opencl_code opencl_prelude cost_centres kernels types sizes failures = do
  final_inits <- GC.contextFinalInits

  let (ctx_opencl_fields, ctx_opencl_inits, top_decls, later_top_decls) =
        openClDecls cost_centres kernels opencl_code opencl_prelude

  mapM_ GC.earlyDecl top_decls

  let size_name_inits = map (\k -> [C.cinit|$string:(pretty k)|]) $ M.keys sizes
      size_var_inits = map (\k -> [C.cinit|$string:(zEncodeString (pretty k))|]) $ M.keys sizes
      size_class_inits = map (\c -> [C.cinit|$string:(pretty c)|]) $ M.elems sizes
      num_sizes = M.size sizes

  GC.earlyDecl [C.cedecl|static const char *size_names[] = { $inits:size_name_inits };|]
  GC.earlyDecl [C.cedecl|static const char *size_vars[] = { $inits:size_var_inits };|]
  GC.earlyDecl [C.cedecl|static const char *size_classes[] = { $inits:size_class_inits };|]

  GC.publicDef_ "get_num_sizes" GC.InitDecl $ \s ->
    ([C.cedecl|int $id:s(void);|],
     [C.cedecl|int $id:s(void) {
                return $int:num_sizes;
              }|])

  GC.publicDef_ "get_size_name" GC.InitDecl $ \s ->
    ([C.cedecl|const char* $id:s(int);|],
     [C.cedecl|const char* $id:s(int i) {
                return size_names[i];
              }|])

  GC.publicDef_ "get_size_class" GC.InitDecl $ \s ->
    ([C.cedecl|const char* $id:s(int);|],
     [C.cedecl|const char* $id:s(int i) {
                return size_classes[i];
              }|])

  let size_decls = map (\k -> [C.csdecl|size_t $id:k;|]) $ M.keys sizes
  GC.earlyDecl [C.cedecl|struct sizes { $sdecls:size_decls };|]
  cfg <- GC.publicDef "context_config" GC.InitDecl $ \s ->
    ([C.cedecl|struct $id:s;|],
     [C.cedecl|struct $id:s { struct opencl_config opencl;
                              size_t sizes[$int:num_sizes];
                              int num_build_opts;
                              const char **build_opts;
                            };|])

  let size_value_inits = zipWith sizeInit [0..M.size sizes-1] (M.elems sizes)
      sizeInit i size = [C.cstm|cfg->sizes[$int:i] = $int:val;|]
         where val = case size of SizeBespoke _ x -> x
                                  _               -> 0
  GC.publicDef_ "context_config_new" GC.InitDecl $ \s ->
    ([C.cedecl|struct $id:cfg* $id:s(void);|],
     [C.cedecl|struct $id:cfg* $id:s(void) {
                         struct $id:cfg *cfg = (struct $id:cfg*) malloc(sizeof(struct $id:cfg));
                         if (cfg == NULL) {
                           return NULL;
                         }

                         cfg->num_build_opts = 0;
                         cfg->build_opts = (const char**) malloc(sizeof(const char*));
                         cfg->build_opts[0] = NULL;
                         $stms:size_value_inits
                         opencl_config_init(&cfg->opencl, $int:num_sizes,
                                            size_names, size_vars,
                                            cfg->sizes, size_classes);
                         return cfg;
                       }|])

  GC.publicDef_ "context_config_free" GC.InitDecl $ \s ->
    ([C.cedecl|void $id:s(struct $id:cfg* cfg);|],
     [C.cedecl|void $id:s(struct $id:cfg* cfg) {
                         free(cfg->build_opts);
                         free(cfg);
                       }|])

  GC.publicDef_ "context_config_add_build_option" GC.InitDecl $ \s ->
    ([C.cedecl|void $id:s(struct $id:cfg* cfg, const char *opt);|],
     [C.cedecl|void $id:s(struct $id:cfg* cfg, const char *opt) {
                         cfg->build_opts[cfg->num_build_opts] = opt;
                         cfg->num_build_opts++;
                         cfg->build_opts = (const char**) realloc(cfg->build_opts, (cfg->num_build_opts+1) * sizeof(const char*));
                         cfg->build_opts[cfg->num_build_opts] = NULL;
                       }|])

  GC.publicDef_ "context_config_set_debugging" GC.InitDecl $ \s ->
    ([C.cedecl|void $id:s(struct $id:cfg* cfg, int flag);|],
     [C.cedecl|void $id:s(struct $id:cfg* cfg, int flag) {
                         cfg->opencl.profiling = cfg->opencl.logging = cfg->opencl.debugging = flag;
                       }|])

  GC.publicDef_ "context_config_set_profiling" GC.InitDecl $ \s ->
    ([C.cedecl|void $id:s(struct $id:cfg* cfg, int flag);|],
     [C.cedecl|void $id:s(struct $id:cfg* cfg, int flag) {
                         cfg->opencl.profiling = flag;
                       }|])

  GC.publicDef_ "context_config_set_logging" GC.InitDecl $ \s ->
    ([C.cedecl|void $id:s(struct $id:cfg* cfg, int flag);|],
     [C.cedecl|void $id:s(struct $id:cfg* cfg, int flag) {
                         cfg->opencl.logging = flag;
                       }|])

  GC.publicDef_ "context_config_set_device" GC.InitDecl $ \s ->
    ([C.cedecl|void $id:s(struct $id:cfg* cfg, const char *s);|],
     [C.cedecl|void $id:s(struct $id:cfg* cfg, const char *s) {
                         set_preferred_device(&cfg->opencl, s);
                       }|])

  GC.publicDef_ "context_config_set_platform" GC.InitDecl $ \s ->
    ([C.cedecl|void $id:s(struct $id:cfg* cfg, const char *s);|],
     [C.cedecl|void $id:s(struct $id:cfg* cfg, const char *s) {
                         set_preferred_platform(&cfg->opencl, s);
                       }|])

  GC.publicDef_ "context_config_select_device_interactively" GC.InitDecl $ \s ->
    ([C.cedecl|void $id:s(struct $id:cfg* cfg);|],
     [C.cedecl|void $id:s(struct $id:cfg* cfg) {
                         select_device_interactively(&cfg->opencl);
                       }|])

  GC.publicDef_ "context_config_dump_program_to" GC.InitDecl $ \s ->
    ([C.cedecl|void $id:s(struct $id:cfg* cfg, const char *path);|],
     [C.cedecl|void $id:s(struct $id:cfg* cfg, const char *path) {
                         cfg->opencl.dump_program_to = path;
                       }|])

  GC.publicDef_ "context_config_load_program_from" GC.InitDecl $ \s ->
    ([C.cedecl|void $id:s(struct $id:cfg* cfg, const char *path);|],
     [C.cedecl|void $id:s(struct $id:cfg* cfg, const char *path) {
                         cfg->opencl.load_program_from = path;
                       }|])


  GC.publicDef_ "context_config_dump_binary_to" GC.InitDecl $ \s ->
    ([C.cedecl|void $id:s(struct $id:cfg* cfg, const char *path);|],
     [C.cedecl|void $id:s(struct $id:cfg* cfg, const char *path) {
                         cfg->opencl.dump_binary_to = path;
                       }|])

  GC.publicDef_ "context_config_load_binary_from" GC.InitDecl $ \s ->
    ([C.cedecl|void $id:s(struct $id:cfg* cfg, const char *path);|],
     [C.cedecl|void $id:s(struct $id:cfg* cfg, const char *path) {
                         cfg->opencl.load_binary_from = path;
                       }|])

  GC.publicDef_ "context_config_set_default_group_size" GC.InitDecl $ \s ->
    ([C.cedecl|void $id:s(struct $id:cfg* cfg, int size);|],
     [C.cedecl|void $id:s(struct $id:cfg* cfg, int size) {
                         cfg->opencl.default_group_size = size;
                         cfg->opencl.default_group_size_changed = 1;
                       }|])

  GC.publicDef_ "context_config_set_default_num_groups" GC.InitDecl $ \s ->
    ([C.cedecl|void $id:s(struct $id:cfg* cfg, int num);|],
     [C.cedecl|void $id:s(struct $id:cfg* cfg, int num) {
                         cfg->opencl.default_num_groups = num;
                       }|])

  GC.publicDef_ "context_config_set_default_tile_size" GC.InitDecl $ \s ->
    ([C.cedecl|void $id:s(struct $id:cfg* cfg, int num);|],
     [C.cedecl|void $id:s(struct $id:cfg* cfg, int size) {
                         cfg->opencl.default_tile_size = size;
                         cfg->opencl.default_tile_size_changed = 1;
                       }|])

  GC.publicDef_ "context_config_set_default_threshold" GC.InitDecl $ \s ->
    ([C.cedecl|void $id:s(struct $id:cfg* cfg, int num);|],
     [C.cedecl|void $id:s(struct $id:cfg* cfg, int size) {
                         cfg->opencl.default_threshold = size;
                       }|])

  GC.publicDef_ "context_config_set_size" GC.InitDecl $ \s ->
    ([C.cedecl|int $id:s(struct $id:cfg* cfg, const char *size_name, size_t size_value);|],
     [C.cedecl|int $id:s(struct $id:cfg* cfg, const char *size_name, size_t size_value) {

                         for (int i = 0; i < $int:num_sizes; i++) {
                           if (strcmp(size_name, size_names[i]) == 0) {
                             cfg->sizes[i] = size_value;
                             return 0;
                           }
                         }

                         if (strcmp(size_name, "default_group_size") == 0) {
                           cfg->opencl.default_group_size = size_value;
                           return 0;
                         }

                         if (strcmp(size_name, "default_num_groups") == 0) {
                           cfg->opencl.default_num_groups = size_value;
                           return 0;
                         }

                         if (strcmp(size_name, "default_threshold") == 0) {
                           cfg->opencl.default_threshold = size_value;
                           return 0;
                         }

                         if (strcmp(size_name, "default_tile_size") == 0) {
                           cfg->opencl.default_tile_size = size_value;
                           return 0;
                         }

                         return 1;
                       }|])

  (fields, init_fields) <- GC.contextContents
  ctx <- GC.publicDef "context" GC.InitDecl $ \s ->
    ([C.cedecl|struct $id:s;|],
     [C.cedecl|struct $id:s {
                         int detail_memory;
                         int debugging;
                         int profiling;
                         int profiling_paused;
                         int logging;
                         typename lock_t lock;
                         char *error;
                         $sdecls:fields
                         $sdecls:ctx_opencl_fields
                         typename cl_mem global_failure;
                         typename cl_mem global_failure_args;
                         struct opencl_context opencl;
                         struct sizes sizes;
                         // True if a potentially failing kernel has been enqueued.
                         typename cl_int failure_is_an_option;
                       };|])

  mapM_ GC.earlyDecl later_top_decls

  GC.earlyDecl [C.cedecl|static void init_context_early(struct $id:cfg *cfg, struct $id:ctx* ctx) {
                     ctx->opencl.cfg = cfg->opencl;
                     ctx->detail_memory = cfg->opencl.debugging;
                     ctx->debugging = cfg->opencl.debugging;
                     ctx->profiling = cfg->opencl.profiling;
                     ctx->profiling_paused = 0;
                     ctx->logging = cfg->opencl.logging;
                     ctx->error = NULL;
                     ctx->opencl.profiling_records_capacity = 200;
                     ctx->opencl.profiling_records_used = 0;
                     ctx->opencl.profiling_records =
                       malloc(ctx->opencl.profiling_records_capacity *
                              sizeof(struct profiling_record));
                     create_lock(&ctx->lock);

                     ctx->failure_is_an_option = 0;
                     $stms:init_fields
                     $stms:ctx_opencl_inits
  }|]

  let set_sizes = zipWith (\i k -> [C.cstm|ctx->sizes.$id:k = cfg->sizes[$int:i];|])
                          [(0::Int)..] $ M.keys sizes
      max_failure_args =
        foldl max 0 $ map (errorMsgNumArgs . failureError) failures

  GC.earlyDecl [C.cedecl|static int init_context_late(struct $id:cfg *cfg, struct $id:ctx* ctx, typename cl_program prog) {
                     typename cl_int error;

                     typename cl_int no_error = -1;
                     ctx->global_failure =
                       clCreateBuffer(ctx->opencl.ctx,
                                      CL_MEM_READ_WRITE | CL_MEM_COPY_HOST_PTR,
                                      sizeof(cl_int), &no_error, &error);
                     OPENCL_SUCCEED_OR_RETURN(error);

                     // The +1 is to avoid zero-byte allocations.
                     ctx->global_failure_args =
                       clCreateBuffer(ctx->opencl.ctx,
                                      CL_MEM_READ_WRITE,
                                      sizeof(cl_int)*($int:max_failure_args+1), NULL, &error);
                     OPENCL_SUCCEED_OR_RETURN(error);

                     // Load all the kernels.
                     $stms:(map loadKernel (M.toList kernels))

                     $stms:final_inits
                     $stms:set_sizes

                     init_constants(ctx);
                     // Clear the free list of any deallocations that occurred while initialising constants.
                     OPENCL_SUCCEED_OR_RETURN(opencl_free_all(&ctx->opencl));

                     // The program will be properly freed after all the kernels have also been freed.
                     OPENCL_SUCCEED_OR_RETURN(clReleaseProgram(prog));

                     return futhark_context_sync(ctx);
  }|]

  let set_required_types = [ [C.cstm|required_types |= OPENCL_F64; |]
                           | FloatType Float64 `elem` types ]

  GC.publicDef_ "context_new" GC.InitDecl $ \s ->
    ([C.cedecl|struct $id:ctx* $id:s(struct $id:cfg* cfg);|],
     [C.cedecl|struct $id:ctx* $id:s(struct $id:cfg* cfg) {
                          struct $id:ctx* ctx = (struct $id:ctx*) malloc(sizeof(struct $id:ctx));
                          if (ctx == NULL) {
                            return NULL;
                          }

                          int required_types = 0;
                          $stms:set_required_types

                          init_context_early(cfg, ctx);
                          typename cl_program prog = setup_opencl(&ctx->opencl, opencl_program, required_types, cfg->build_opts);
                          init_context_late(cfg, ctx, prog);
                          return ctx;
                       }|])

  GC.publicDef_ "context_new_with_command_queue" GC.InitDecl $ \s ->
    ([C.cedecl|struct $id:ctx* $id:s(struct $id:cfg* cfg, typename cl_command_queue queue);|],
     [C.cedecl|struct $id:ctx* $id:s(struct $id:cfg* cfg, typename cl_command_queue queue) {
                          struct $id:ctx* ctx = (struct $id:ctx*) malloc(sizeof(struct $id:ctx));
                          if (ctx == NULL) {
                            return NULL;
                          }

                          int required_types = 0;
                          $stms:set_required_types

                          init_context_early(cfg, ctx);
                          typename cl_program prog = setup_opencl_with_command_queue(&ctx->opencl, queue, opencl_program, required_types, cfg->build_opts);
                          init_context_late(cfg, ctx, prog);
                          return ctx;
                       }|])

  GC.publicDef_ "context_free" GC.InitDecl $ \s ->
    ([C.cedecl|void $id:s(struct $id:ctx* ctx);|],
     [C.cedecl|void $id:s(struct $id:ctx* ctx) {
                                 free_constants(ctx);
                                 free_lock(&ctx->lock);
                                 $stms:(map releaseKernel (M.toList kernels))
                                 teardown_opencl(&ctx->opencl);
                                 free(ctx);
                               }|])

  GC.publicDef_ "context_sync" GC.MiscDecl $ \s ->
    ([C.cedecl|int $id:s(struct $id:ctx* ctx);|],
     [C.cedecl|int $id:s(struct $id:ctx* ctx) {
                 // Check for any delayed error.
                 typename cl_int failure_idx = -1;
                 if (ctx->failure_is_an_option) {
                   OPENCL_SUCCEED_OR_RETURN(
                     clEnqueueReadBuffer(ctx->opencl.queue,
                                         ctx->global_failure,
                                         CL_FALSE,
                                         0, sizeof(typename cl_int), &failure_idx,
                                         0, NULL, $exp:(profilingEvent copyScalarFromDev)));
                   ctx->failure_is_an_option = 0;
                 }

                 OPENCL_SUCCEED_OR_RETURN(clFinish(ctx->opencl.queue));

                 if (failure_idx >= 0) {
                   // We have to clear global_failure so that the next entry point
                   // is not considered a failure from the start.
                   typename cl_int no_failure = -1;
                   OPENCL_SUCCEED_OR_RETURN(
                    clEnqueueWriteBuffer(ctx->opencl.queue, ctx->global_failure, CL_TRUE,
                                         0, sizeof(cl_int), &no_failure,
                                         0, NULL, NULL));

                   typename cl_int args[$int:max_failure_args+1];
                   OPENCL_SUCCEED_OR_RETURN(
                     clEnqueueReadBuffer(ctx->opencl.queue,
                                         ctx->global_failure_args,
                                         CL_TRUE,
                                         0, sizeof(args), &args,
                                         0, NULL, $exp:(profilingEvent copyDevToHost)));

                   $stm:(failureSwitch failures)

                   return 1;
                 }
                 return 0;
               }|])

  GC.publicDef_ "context_clear_caches" GC.MiscDecl $ \s ->
    ([C.cedecl|int $id:s(struct $id:ctx* ctx);|],
     [C.cedecl|int $id:s(struct $id:ctx* ctx) {
                         ctx->error = OPENCL_SUCCEED_NONFATAL(opencl_free_all(&ctx->opencl));
                         return ctx->error != NULL;
                       }|])

  GC.publicDef_ "context_get_command_queue" GC.InitDecl $ \s ->
    ([C.cedecl|typename cl_command_queue $id:s(struct $id:ctx* ctx);|],
     [C.cedecl|typename cl_command_queue $id:s(struct $id:ctx* ctx) {
                 return ctx->opencl.queue;
               }|])

  GC.profileReport [C.citem|OPENCL_SUCCEED_FATAL(opencl_tally_profiling_records(&ctx->opencl));|]
  mapM_ GC.profileReport $ costCentreReport $
    cost_centres ++ M.keys kernels

openClDecls :: [Name] -> M.Map KernelName KernelSafety -> String -> String
            -> ([C.FieldGroup], [C.Stm], [C.Definition], [C.Definition])
openClDecls cost_centres kernels opencl_program opencl_prelude =
  (ctx_fields, ctx_inits, openCL_boilerplate, openCL_load)
  where opencl_program_fragments =
          -- Some C compilers limit the size of literal strings, so
          -- chunk the entire program into small bits here, and
          -- concatenate it again at runtime.
          [ [C.cinit|$string:s|] | s <- chunk 2000 (opencl_prelude++opencl_program) ]

        ctx_fields =
          [ [C.csdecl|int total_runs;|],
            [C.csdecl|long int total_runtime;|] ] ++
          [ [C.csdecl|typename cl_kernel $id:name;|]
          | name <- M.keys kernels ] ++
          concat
          [ [ [C.csdecl|typename int64_t $id:(kernelRuntime name);|]
            , [C.csdecl|int $id:(kernelRuns name);|]
            ]
          | name <- cost_centres ++ M.keys kernels ]

        ctx_inits =
          [ [C.cstm|ctx->total_runs = 0;|],
            [C.cstm|ctx->total_runtime = 0;|] ] ++
          concat
          [ [ [C.cstm|ctx->$id:(kernelRuntime name) = 0;|]
            , [C.cstm|ctx->$id:(kernelRuns name) = 0;|]
            ]
          | name <- cost_centres ++ M.keys kernels ]

        openCL_load = [
          [C.cedecl|
void post_opencl_setup(struct opencl_context *ctx, struct opencl_device_option *option) {
  $stms:(map sizeHeuristicsCode sizeHeuristicsTable)
}|]]

        free_list_h = $(embedStringFile "rts/c/free_list.h")
        openCL_h = $(embedStringFile "rts/c/opencl.h")

        program_fragments = opencl_program_fragments ++ [[C.cinit|NULL|]]
        openCL_boilerplate = [C.cunit|
          $esc:("typedef cl_mem fl_mem_t;")
          $esc:free_list_h
          $esc:openCL_h
          static const char *opencl_program[] = {$inits:program_fragments};|]

loadKernel :: (KernelName, KernelSafety) -> C.Stm
loadKernel (name, safety) = [C.cstm|{
  ctx->$id:name = clCreateKernel(prog, $string:(pretty (C.toIdent name mempty)), &error);
  OPENCL_SUCCEED_FATAL(error);
  $items:set_args
  if (ctx->debugging) {
    fprintf(stderr, "Created kernel %s.\n", $string:(pretty name));
  }
  }|]
  where set_global_failure =
          [C.citem|OPENCL_SUCCEED_FATAL(
                     clSetKernelArg(ctx->$id:name, 0, sizeof(typename cl_mem),
                                    &ctx->global_failure));|]
        set_global_failure_args =
          [C.citem|OPENCL_SUCCEED_FATAL(
                     clSetKernelArg(ctx->$id:name, 2, sizeof(typename cl_mem),
                                    &ctx->global_failure_args));|]
        set_args = case safety of
                     SafetyNone -> []
                     SafetyCheap -> [set_global_failure]
                     SafetyFull -> [set_global_failure, set_global_failure_args]

releaseKernel :: (KernelName, KernelSafety) -> C.Stm
releaseKernel (name, _) = [C.cstm|OPENCL_SUCCEED_FATAL(clReleaseKernel(ctx->$id:name));|]

kernelRuntime :: KernelName -> Name
kernelRuntime = (<>"_total_runtime")

kernelRuns :: KernelName -> Name
kernelRuns = (<>"_runs")

costCentreReport :: [Name] -> [C.BlockItem]
costCentreReport names = report_kernels ++ [report_total]
  where longest_name = foldl max 0 $ map (length . pretty) names
        report_kernels = concatMap reportKernel names
        format_string name =
          let padding = replicate (longest_name - length name) ' '
          in unwords [name ++ padding,
                      "ran %5d times; avg: %8ldus; total: %8ldus\n"]
        reportKernel name =
          let runs = kernelRuns name
              total_runtime = kernelRuntime name
          in [[C.citem|
               str_builder(&builder,
                           $string:(format_string (pretty name)),
                           ctx->$id:runs,
                           (long int) ctx->$id:total_runtime / (ctx->$id:runs != 0 ? ctx->$id:runs : 1),
                           (long int) ctx->$id:total_runtime);
              |],
              [C.citem|ctx->total_runtime += ctx->$id:total_runtime;|],
              [C.citem|ctx->total_runs += ctx->$id:runs;|]]

        report_total = [C.citem|
                          str_builder(&builder, "%d operations with cumulative runtime: %6ldus\n",
                                      ctx->total_runs, ctx->total_runtime);
                        |]

sizeHeuristicsCode :: SizeHeuristic -> C.Stm
sizeHeuristicsCode (SizeHeuristic platform_name device_type which what) =
  [C.cstm|
   if ($exp:which' == 0 &&
       strstr(option->platform_name, $string:platform_name) != NULL &&
       (option->device_type & $exp:(clDeviceType device_type)) == $exp:(clDeviceType device_type)) {
     $items:get_size
   }|]
  where clDeviceType DeviceGPU = [C.cexp|CL_DEVICE_TYPE_GPU|]
        clDeviceType DeviceCPU = [C.cexp|CL_DEVICE_TYPE_CPU|]

        which' = case which of
                   LockstepWidth -> [C.cexp|ctx->lockstep_width|]
                   NumGroups -> [C.cexp|ctx->cfg.default_num_groups|]
                   GroupSize -> [C.cexp|ctx->cfg.default_group_size|]
                   TileSize -> [C.cexp|ctx->cfg.default_tile_size|]
                   Threshold -> [C.cexp|ctx->cfg.default_threshold|]

        get_size =
          let (e, m) = runState (GC.compilePrimExp onLeaf what) mempty
          in concat (M.elems m) ++ [[C.citem|$exp:which' = $exp:e;|]]

        onLeaf (DeviceInfo s) = do
          let s' = "CL_DEVICE_" ++ s
              v = s ++ "_val"
          m <- get
          case M.lookup s m of
            Nothing ->
              -- Cheating with the type here; works for the infos we
              -- currently use, but should be made more size-aware in
              -- the future.
              modify $ M.insert s'
              [C.citems|size_t $id:v;
                        clGetDeviceInfo(ctx->device, $id:s',
                                        sizeof($id:v), &$id:v,
                                        NULL);|]
            Just _ -> return ()

          return [C.cexp|$id:v|]

-- Options that are common to multiple GPU-like backends.
commonOptions :: [Option]
commonOptions =
   [ Option { optionLongName = "device"
            , optionShortName = Just 'd'
            , optionArgument = RequiredArgument "NAME"
            , optionAction = [C.cstm|futhark_context_config_set_device(cfg, optarg);|]
            }
   , Option { optionLongName = "default-group-size"
            , optionShortName = Nothing
            , optionArgument = RequiredArgument "INT"
            , optionAction = [C.cstm|futhark_context_config_set_default_group_size(cfg, atoi(optarg));|]
            }
   , Option { optionLongName = "default-num-groups"
            , optionShortName = Nothing
            , optionArgument = RequiredArgument "INT"
            , optionAction = [C.cstm|futhark_context_config_set_default_num_groups(cfg, atoi(optarg));|]
            }
   , Option { optionLongName = "default-tile-size"
            , optionShortName = Nothing
            , optionArgument = RequiredArgument "INT"
            , optionAction = [C.cstm|futhark_context_config_set_default_tile_size(cfg, atoi(optarg));|]
            }
   , Option { optionLongName = "default-threshold"
            , optionShortName = Nothing
            , optionArgument = RequiredArgument "INT"
            , optionAction = [C.cstm|futhark_context_config_set_default_threshold(cfg, atoi(optarg));|]
            }
   , Option { optionLongName = "print-sizes"
            , optionShortName = Nothing
            , optionArgument = NoArgument
            , optionAction = [C.cstm|{
                int n = futhark_get_num_sizes();
                for (int i = 0; i < n; i++) {
                  printf("%s (%s)\n", futhark_get_size_name(i),
                                      futhark_get_size_class(i));
                }
                exit(0);
              }|]
            }
   , Option { optionLongName = "size"
            , optionShortName = Nothing
            , optionArgument = RequiredArgument "NAME=INT"
            , optionAction = [C.cstm|{
                char *name = optarg;
                char *equals = strstr(optarg, "=");
                char *value_str = equals != NULL ? equals+1 : optarg;
                int value = atoi(value_str);
                if (equals != NULL) {
                  *equals = 0;
                  if (futhark_context_config_set_size(cfg, name, value) != 0) {
                    futhark_panic(1, "Unknown size: %s\n", name);
                  }
                } else {
                  futhark_panic(1, "Invalid argument for size option: %s\n", optarg);
                }}|]
            }
   , Option { optionLongName = "tuning"
            , optionShortName = Nothing
            , optionArgument = RequiredArgument "FILE"
            , optionAction = [C.cstm|{
                char *ret = load_tuning_file(optarg, cfg, (int(*)(void*, const char*, size_t))
                                                          futhark_context_config_set_size);
                if (ret != NULL) {
                  futhark_panic(1, "When loading tuning from '%s': %s\n", optarg, ret);
                }}|]
            }
   ]
