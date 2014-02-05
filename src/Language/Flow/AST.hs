{-# LANGUAGE GeneralizedNewtypeDeriving, OverloadedStrings #-}
module Language.Flow.AST
    ( Program(..),
      Expression(..),
      Literal(..),
      Binding(..),
      TypeAssertion(..),
      Pattern(..),
      Type(..),
      TyConName(..),
      VariableName(..),
      TypeName(..),
      Region(..),
      VarID(..),

      getUniversalImports,
      addUniversalImport,

      exprRegion,
      prettyPrintAST,

      intType, stringType, doubleType, fnType
    ) where

import qualified Data.Text as T
import Data.String
import Data.Int
import Data.IORef

import Language.Flow.Execution.Types hiding (Ap)

import System.IO.Unsafe

import Text.Parsec (SourcePos)
import Text.PrettyPrint.HughesPJ

newtype TyConName = TyConName { unTyConName :: T.Text }
    deriving (Show, Eq, Ord, IsString)

data Pattern =
    VariablePattern Region VariableName | -- Constructor arguments
    ConstrPattern Region TypeName [Pattern] | -- Unpacking a constructor
    PlaceholderPattern Region | -- always matches

    -- Internal use only
    VarIDPattern Region VarID
    deriving (Show)

data Type = TypeVariable VariableName |
            TypeConstructor TyConName [Type]
            deriving (Eq, Ord)

data Literal = IntLiteral Int64 |
               StringLiteral String |
               DoubleLiteral Double
               deriving (Show)

data Region = Region SourcePos SourcePos |
              EmptyRegion
              deriving (Show, Eq, Ord)

data TypeAssertion = TypeAssertion VariableName Type |
                     TypeAssertionId VarID Type
                   deriving (Show)
data Binding = Binding Region Pattern Expression
             deriving (Show)


-- | As stated in the documentation, there are three types of flow expressions: literals,
-- | function application, and let-in blocks
data Expression =
    Identifier Region VariableName |
    Literal Region Literal |
    Ap Region Expression Expression | -- Simple function application
    LetIn Region [TypeAssertion] [Binding] Expression |
    TypeAssertionE Region Expression Type |
    Block Region [Expression] |
    Lambda Region [Pattern] Expression |
    Case Region Expression [(Pattern, Expression)] |

    -- Internal use only
    LocationRef Region GMachineAddress |
    VariableRef Region VarID |
    SimpleLet Region (VarID, Expression) Expression -- Non recursive let, only used internally
    deriving Show

-- | A data type used to represent a complete Flow progra
data Program = Program {
      flowProgramImports :: [(ModuleName, ModuleName)],
      flowGlobalImports :: [ModuleName],
      flowProgramBody :: Expression
    }

instance Show Type where
    show (TypeVariable var) = T.unpack . unVariableName $ var
    show (TypeConstructor "(->)" [x, y]) = concat [case x of
                                                     TypeConstructor "(->)" -> concat ["(", show x, ")"]
                                                     _ -> show x,
                                                   " -> ",
                                                   case y of
                                                     TypeConstructor "(->)" _ -> show y
                                                     _ -> show y]
    show (TypeConstructor con args)

intTyName, stringTyName, doubleTyName, arrowTyName :: TyConName
intTyName = "Integer"
stringTyName = "String"
doubleTyName = "Double"
arrowTyName = "(->)"

intType, stringType, doubleType :: Type
intType = TypeConstructor intTyName []
stringType = TypeConstructor stringTyName []
doubleType = TypeConstructor doubleTyName []

-- | `fnType a b` Constructs the type `a -> b`
fnType :: Type -> Type -> Type
fnType a b = TypeConstructor arrowTyName [a, b]

{-# NOINLINE universalImportsVar #-}
universalImportsVar :: IORef [(ModuleName, ModuleName)]
universalImportsVar = unsafePerformIO $ newIORef [(fromString "HeadWater", fromString "HeadWater")]

getUniversalImports :: IO [(ModuleName, ModuleName)]
getUniversalImports = readIORef universalImportsVar

addUniversalImport :: ModuleName -> IO ()
addUniversalImport modName =
  modifyIORef universalImportsVar (\universalImports -> (modName, modName):universalImports)

exprRegion :: Expression -> Region
exprRegion (Identifier x _) = x
exprRegion (Literal x _) = x
exprRegion (Ap x _ _) = x
exprRegion (LetIn x _ _ _) = x
exprRegion (SimpleLet x _ _) = x
exprRegion (TypeAssertionE x _ _) = x
exprRegion (Block x _) = x
exprRegion (Lambda x _ _) = x
exprRegion (LocationRef x _) = x
exprRegion (VariableRef x _) = x

prettyPrintAST :: Expression -> String
prettyPrintAST e = render $ prettyPrintAST' e
    where
      prettyPrintAST' (VariableRef _ (VarID vId)) = text $ "V#" ++ show vId
      prettyPrintAST' (LocationRef _ (GMachineAddress addr)) = text $ "@" ++ show addr
      prettyPrintAST' (Identifier _ (VariableName v)) = text $ T.unpack v
      prettyPrintAST' (Literal _ (IntLiteral i)) = text $ "I" ++ show i
      prettyPrintAST' (Literal _ (StringLiteral s)) = text $ "'" ++ show s ++ "'"
      prettyPrintAST' (Literal _ (DoubleLiteral d)) = text $ show d
      prettyPrintAST' (Ap _ e1 e2@(Ap _ _ _)) = prettyPrintAST' e1 <+> (parens $ prettyPrintAST' e2)
      prettyPrintAST' (Ap _ e1 e2) = prettyPrintAST' e1 <+> prettyPrintAST' e2
      prettyPrintAST' (LetIn _ assertions bindings expression) =
          let assertionsDoc = vcat $ punctuate semi $ map prettyPrintAssertion assertions
              bindingsDoc = vcat $ punctuate semi $ map prettyPrintBinding bindings
          in text "let" <+> braces (nest 4 $ assertionsDoc $+$ bindingsDoc) <+> text "in" <+>
             nest 4 (prettyPrintAST' expression)
      prettyPrintAST' (SimpleLet r (var, binding) expr) = prettyPrintAST' (LetIn r [] [Binding r (VarIDPattern r var) binding] expr)
      prettyPrintAST' (TypeAssertionE _ e t) = parens $ prettyPrintAST' e <+> text "::" <+> prettyPrintType t
      prettyPrintAST' (Block _ es) = braces $ nest 4 $ vcat $ punctuate semi $ map prettyPrintAST' es
      prettyPrintAST' (Lambda _ pats e) = parens $ text "\\" <> (hcat $ map prettyPrintPattern pats) <+> text "->" <+> prettyPrintAST' e
      prettyPrintAST' (Case _ e patsAndExprs) = text "case" <+> prettyPrintAST' e <+> text "of" <+> (braces $ nest 4 $ vcat $ map prettyPrintPatAndExpr patsAndExprs)

      prettyPrintPatAndExpr (pat, expr) = prettyPrintPattern pat <+> text "->" <+> prettyPrintAST' expr

      prettyPrintPattern (VariablePattern _ (VariableName v)) = text $ T.unpack v
      prettyPrintPattern (VarIDPattern _ (VarID v)) = text $ "V#" ++ show v
      prettyPrintPattern (ConstrPattern _ (TypeName t) pats) = parens $ (text $ T.unpack t) <+> (hsep $ map prettyPrintPattern pats)
      prettyPrintPattern (PlaceholderPattern _) = text "_"

      prettyPrintType (TypeConstructor name [a, b])
          | name == arrowTyName = prettyPrintType a <+> text "->" <+> prettyPrintType b
      prettyPrintType (TypeConstructor (TyConName name) args) = (text . T.unpack $name) <+> (hsep $ map prettyPrintType args)
      prettyPrintType (TypeVariable (VariableName v)) = text $ T.unpack v

      prettyPrintBinding (Binding _ pat expr) = prettyPrintPattern pat <+> equals <+> prettyPrintAST' expr

      prettyPrintAssertion (TypeAssertion (VariableName v) t) = (text $ T.unpack v) <+> text "::" <+> prettyPrintType t
      prettyPrintAssertion (TypeAssertionId (VarID v) t) = (text $ "V#" ++ show v) <+> text "::" <+> prettyPrintType t