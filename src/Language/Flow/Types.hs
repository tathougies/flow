module Language.Flow.Types where

    import Language.Flow.Execution.Types

    import qualified Data.Map as M

    data FlowCompileOptions = Options {
                             builtinModules :: M.Map ModuleName Module,
                             builtinTypes :: M.Map GTypeName (GConstr -> [GMachineAddress] -> GenericGData)
                           }