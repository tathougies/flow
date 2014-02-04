{-# LANGUAGE GeneralizedNewtypeDeriving, BangPatterns, ExistentialQuantification, RankNTypes, DeriveDataTypeable, RecordWildCards, MultiParamTypeClasses #-}
module Language.Flow.Execution.Types where

import qualified Data.IntSet as IntSet
import Data.Map as M
import Data.Array.IO
import Data.Array as A
import Data.Word
import Data.Either
import Data.Int
import qualified Data.List as L
import Data.Text hiding (length)
import Data.String
import Data.Binary
import Data.Binary.Put
import Data.Dynamic
import Data.IORef

import Control.Applicative
import Control.Monad
import qualified Control.Monad.State as S
import Control.Monad.Reader
import Control.Monad.Trans
import Control.Exception

import System.IO.Unsafe

import Unsafe.Coerce

newtype GMachineAddress = GMachineAddress Int
    deriving (Ord, Eq, Enum, Show, Read, Num, Ix, Integral, Real, Binary)
newtype StackOffset = StackOffset Int
    deriving (Ord, Eq, Enum, Show, Read, Num, Ix, Integral, Real, Binary)
newtype VarID = VarID Int
    deriving (Ord, Eq, Show, Read, Num, Integral, Real, Enum)
newtype SCName = SCName Int
    deriving (Ord, Eq, Show, Read, Num, Integral, Real, Enum)
newtype VariableName = VariableName Text
    deriving (Ord, Eq, Show, Read, IsString, Binary)
newtype TypeName = TypeName Text
    deriving (Ord, Eq, Show, Read, IsString, Binary)
newtype ModuleName = ModuleName Text
    deriving (Ord, Eq, Show, Read, IsString, Binary)

type Label = Int
type GMachineStack = [GMachineAddress]
newtype GCodeBuiltin = GCodeBuiltin ([GMachineAddress] -> GMachine (Maybe GenericGData))
type GCodeSequence = [GCode]
type GTypeName = Text
type GFieldName = Text
type GConstr = Text -- type of constructor names
type GConstrArgs = Array Int GMachineAddress

data GMachineError = GMachineError GMachineState String
                     deriving Typeable

data GMachine a =
    GMachine { runGMachine :: GMachineState -> IO (Either GMachineError (GMachineState, a)) }

data GCodeProgram =
    GCodeProgram {
      initCode :: GCodeSequence,
      initialData :: [(GMachineAddress, GenericGData)],
      progModules :: M.Map ModuleName Module,
      progTypes :: Map GTypeName (GConstr -> [GMachineAddress] -> GenericGData)
    }

data GMachineContext = GMachineContext {
      gmcModules :: Map ModuleName Module,
      gmcTypes :: Map GTypeName (GConstr -> [GMachineAddress] -> GenericGData)
    }

data GMachineState = GMachineState {
      gmachineStack :: GMachineStack,
      gmachineGraph :: IOArray GMachineAddress GenericGData,
      gmachineCode :: GCodeSequence,
      gmachineDump :: [(GMachineStack, GCodeSequence)],
      gmachineInitData :: [(GMachineAddress, GenericGData)],
      gmachineFreeCells :: IntSet.IntSet,
      gmachineIndent :: Int,
      gmachineDebug :: Bool,
      gmachineUserState :: Dynamic,
      gmachineContext :: GMachineContext
    }

data GMachineFrozenState = GMachineFrozenState {
      gmachineFrozenStack :: GMachineStack,
      gmachineFrozenGraph :: Array GMachineAddress GenericGData,
      gmachineFrozenCode :: GCodeSequence,
      gmachineFrozenDump :: [(GMachineStack, GCodeSequence)],
      gmachineFrozenInitData :: [GMachineAddress],
      gmachineFrozenFreeCells :: IntSet.IntSet,
      gmachineFrozenDebug :: Bool
    }

instance Monad GMachine where
    return x = GMachine (\st -> return $ Right (st, x))
    a >>= b = GMachine (\st -> do
                          aRet <- runGMachine a st
                          case aRet of
                            Left e -> return $ Left e
                            Right (newState, retVal) ->
                                runGMachine (b retVal) newState)

instance S.MonadState GMachineState GMachine where
    get = GMachine (\st -> return $ Right (st, st))
    put x = GMachine (\_ -> return $ Right (x, ()))

instance Applicative GMachine where
    pure = return
    f <*> x = do
      f' <- f
      x' <- x
      return (f' x')

instance Functor GMachine where
    fmap f x = do
      x' <- x
      return (f x')

instance MonadIO GMachine where
    liftIO f = GMachine (\st -> do
                           ret <- f
                           return $ Right (st, ret))

instance Read GMachineFrozenState where -- necessary so that MapOperation is Read'able
    readsPrec = error "Can't read GMachineFrozenState"

instance GBinary GMachineAddress where
    gput = lift . put
    gget = lift get

instance (GBinary a, GBinary b) => GBinary (a, b) where
    gput (a, b) = gput a >> gput b
    gget = (,) <$> gget <*> gget

instance GBinary a => GBinary [a] where
    gput a = (lift . put . length $ a) >> mapM_ gput a
    gget = do
      l <- lift (get :: Get Int)
      replicateM l gget

instance (Ix i, GBinary i, GBinary b) => GBinary (Array i b) where
    gput a = do
      gput (bounds a)
      gput (A.assocs a)

    gget = do
      bounds <- gget
      assocs <- gget
      return (array bounds assocs)

instance GBinary GMachineFrozenState where
    gput GMachineFrozenState {..} = do
      lift (put gmachineFrozenStack)
      gput gmachineFrozenGraph
      lift (put gmachineFrozenCode)
      lift (put gmachineFrozenDump)
      lift (put gmachineFrozenInitData)
      lift (put gmachineFrozenFreeCells)
      lift (put gmachineFrozenDebug)

    gget = GMachineFrozenState <$>
           lift get <*> gget <*>
           lift get <*> lift get <*> lift get <*>
           lift get <*> lift get

data Module = Module {
            flowModuleName :: ModuleName,
            flowModuleMembers :: M.Map VariableName GenericGData
    }

-- | G-Machine instructions as found in Simon Peyton-Jones's book w/ some modifications
data GCode =
    -- State transitions (control)
    Eval |
    Unwind |
    Return |
    Jump {-# UNPACK #-} !Label |
    JFalse {-# UNPACK #-} !Label |

    -- Data examination
    Examine Text {-# UNPACK #-} !Int {-# UNPACK #-} !Label |

    -- Data manipulation
    Push {-# UNPACK #-} !StackOffset |
    PushInt {-# UNPACK #-} !Int64 |
    PushString !Text |
    PushDouble {-# UNPACK #-} !Double |
    PushLocation {-# UNPACK #-} !GMachineAddress |
    Pop {-# UNPACK #-} !StackOffset |
    Slide {-# UNPACK #-} !StackOffset |
    Update {-# UNPACK #-} !StackOffset |
    Alloc {-# UNPACK #-} !Int |
    MkAp |

    -- Internal codes
    CallBuiltin |
    ProgramDone
    deriving (Show, Eq)

instance Binary GCode where
    put Eval = put (0 :: Int8)
    put Unwind = put (1 :: Int8)
    put Return = put (2 :: Int8)
    put (Jump l) = do
                 put (3 :: Int8)
                 put l
    put (JFalse l) = do
                 put (4 :: Int8)
                 put l
    put (Examine constr arity offset) = do
                 put (5 :: Int8)
                 put constr
                 put arity
                 put offset
    put (Push stackOfs) = do
                 put (6 :: Int8)
                 put stackOfs
    put (PushInt i) = do
                 put (7 :: Int8)
                 put i
    put (PushString s) = do
                 put (8 :: Int8)
                 put s
    put (PushDouble d) = do
                 put (9 :: Int8)
                 put d
    put (PushLocation l) = do
                 put (10 :: Int8)
                 put l
    put (Pop stackOfs) = do
                 put (11 :: Int8)
                 put stackOfs
    put (Slide stackOfs) = do
                 put (12 :: Int8)
                 put stackOfs
    put (Update stackOfs) = do
                 put (13 :: Int8)
                 put stackOfs
    put (Alloc count) = do
                 put (14 :: Int8)
                 put count
    put MkAp = put (15 :: Int8)
    put CallBuiltin = put (16 :: Int8)
    put ProgramDone = put (17 :: Int8)

    get = do
      tag <- (get :: Get Int8)
      case tag of
        0 -> return Eval
        1 -> return Unwind
        2 -> return Return
        3 -> doJump
        4 -> doJFalse
        5 -> doExamine
        6 -> doPush
        7 -> doPushInt
        8 -> doPushString
        9 -> doPushDouble
        10 -> doPushLocation
        11 -> doPop
        12 -> doSlide
        13 -> doUpdate
        14 -> doAlloc
        15 -> return MkAp
        16 -> return CallBuiltin
        17 -> return ProgramDone

     where
       doJump = liftM Jump get
       doJFalse = liftM JFalse get
       doExamine = liftM3 Examine get get get
       doPush = liftM Push get
       doPushInt = liftM PushInt get
       doPushString = liftM PushString get
       doPushDouble = liftM PushDouble get
       doPushLocation = liftM PushLocation get
       doPop = liftM Pop get
       doSlide = liftM Slide get
       doUpdate = liftM Update get
       doAlloc = liftM Alloc get

-- Data

data GenericGData = forall a. GData a => G a |
                    Hole

mkGeneric :: GData a => a -> GenericGData
mkGeneric = G

withGenericData :: (forall a. GData a => a -> b) -> GenericGData -> b
withGenericData f Hole = error "withGenericData: Hole"
withGenericData f (G x) = f x

usingGenericData = flip withGenericData

type GPut = ReaderT GMachineContext PutM ()
type GGet = ReaderT GMachineContext Get

-- | A generic class for all things that can be serialized or unserialized given a GMachineContext
class GBinary a where
    gput :: a -> GPut
    gget :: GGet a

-- | A generic class for things that can be shown given a GMachineState
class GShow a where
    gshow :: a -> GMachine String

instance GShow a => GShow [a] where
    gshow [] = return "[]"
    gshow xs = do
      body <- L.intercalate ", " <$> mapM gshow xs
      return (L.concat ["[", body, "]"])

gshow' :: GShow a => GMachineState -> a -> IO (GMachineState, String)
gshow' st x = do
  a <- runGMachine (gshow x) st
  case a of
    Left error -> throwIO error
    Right (st, s) -> return (st, s)

-- | A generic class for all data types that can be put into the G-Machine graph
-- it contains functions that are necessary for the type checker, the constructor
-- matching system, and the garbage collector
class (GShow a) => GData a where
    -- | Returns the type name of the this data. This function may be strict in its first argument
    typeName :: a -> GTypeName

    -- | Returns the name of the constructor used to constract this data type
    constr :: a -> GConstr

    -- | The arguments used to construct this data point. This should also be all things
    -- referenced by this data point.
    constrArgs :: a -> GConstrArgs

    -- | For performance reasons. Do not overwrite in your own code!
    isBuiltin :: a -> Bool
    isBuiltin _ = False

    -- | Access the field specified (by default spits out an error message)
    getField :: GFieldName -> a -> GMachine GenericGData
    getField f x = throwError $ "Cannot get field " ++ show f ++ " from object of type " ++ unpack (typeName x)

    -- | Determine if this type supports a generic operation
    supportsGeneric :: a -> String -> Bool
    supportsGeneric _ _ = False

    -- | Run a generic operation on this type
    runGeneric :: a -> String -> [GenericGData] -> GMachine (Maybe GenericGData)
    runGeneric a gen = error $ "Generic " ++ gen ++ " not supported by " ++ (unpack $ typeName a)

instance Show GenericGData where
    show Hole = "Hole"
    show x = "GenericGData"

instance GShow GenericGData where
    gshow Hole = pure "Hole"
    gshow x = withGenericData gshow x

instance Binary Text where
    put = put . unpack
    get = liftM pack get

-- TODO get rid of this
instance GBinary GenericGData where
    gput Hole = lift (put (-1 :: Int8))
    gput x
     | isInteger x = lift $ do
           put (1 :: Int8)
           put (asInteger x)
     | isString x = lift $ do
           put (2 :: Int8)
           put (asString x)
     | isDouble x = lift $ do
           put (3 :: Int8)
           put (asDouble x)
     | withGenericData isBuiltin x = lift $
           case withGenericData asBuiltin x of
             Ap a b -> do
               put (4 :: Int8)
               put a
               put b
             Fun arity code -> do
               put (5 :: Int8)
               put arity
               put code
             BuiltinFun _ modName symName _ -> do
               put (6 :: Int8)
               put modName
               put symName
     | otherwise = lift $ do
           put (0 :: Int8)
           put (withGenericData typeName x)
           put (withGenericData constr x)
           put (A.elems $ withGenericData constrArgs x)

    gget = do
      tag <- lift (get :: Get Int8)
      case tag of
        -1 -> return Hole
        1 {- IntConstant -} -> liftM (mkGeneric . IntConstant) (lift get)
        2 {- StringConstant -} -> liftM (mkGeneric . StringConstant) (lift get)
        3 {- DoubleConstant -} -> liftM (mkGeneric . DoubleConstant) (lift get)
        4 {- BuiltinData Ap -} -> lift $ do
                               a <- get
                               b <- get
                               return $ mkGeneric $ Ap a b
        5 {- BuiltinData Fun -} -> lift $ do
                               arity <- get
                               code <- get
                               return $ mkGeneric $ Fun arity code
        6 {- BuiltinData BuiltinFun -} -> do
                               modName <- lift get
                               symName <- lift get
                               allBuiltinModules <- gmcModules <$> ask
                               case M.lookup modName allBuiltinModules of
                                 Nothing -> error $ "Could not find builtin module " ++ show modName
                                 Just Module { flowModuleMembers = mod } ->
                                     case M.lookup symName mod of
                                       Nothing -> error $ "Could not find " ++ show symName ++ " in " ++ show modName
                                       Just sym -> return sym
        0 -> do
            typeName <- lift (get :: Get GTypeName)
            constrFuncs <- gmcTypes <$> ask
            case M.lookup typeName constrFuncs of
              Nothing -> fail $ "Could not find constructor function for type " ++ show typeName
              Just constrFunc -> do
                               constrName <- lift (get :: Get GConstr)
                               constrArgs <- lift (get :: Get [GMachineAddress])
                               return $ constrFunc constrName constrArgs

-- Data types

checkCoerce :: GTypeName -> GenericGData -> b
checkCoerce name x = if checkType name x then withGenericData unsafeCoerce x else error "checkCoerce failed"

checkType :: GTypeName -> GenericGData -> Bool
checkType name = withGenericData (\gData -> typeName gData == name)

newtype IntConstant = IntConstant Int64
    deriving (Ord, Eq, Enum, Num, Real, Integral, Read)

isInteger :: GenericGData -> Bool
isInteger = checkType (typeName (undefined :: IntConstant))

asInteger :: GenericGData -> Int64
asInteger = checkCoerce (typeName (undefined :: IntConstant))

instance GShow IntConstant where
    gshow (IntConstant i) = pure (show i)

instance GData IntConstant where
    typeName _ = fromString "Integer"
    constr x = fromString $ "I" ++ show (fromIntegral x :: Integer)
    constrArgs _ = array (0,-1) []

newtype StringConstant = StringConstant Text
    deriving (Ord, Eq, IsString, Show, Read)

isString :: GenericGData -> Bool
isString = checkType (typeName (undefined :: StringConstant))

asString :: GenericGData -> Text
asString = checkCoerce (typeName (undefined :: StringConstant))

instance GShow StringConstant where
    gshow (StringConstant s) = pure (show s)

instance GData StringConstant where
    typeName _ = fromString "String"
    constr (StringConstant x) = fromString $ show x
    constrArgs _ = array (0,-1) []

newtype DoubleConstant = DoubleConstant Double
    deriving (Show, Read, Ord, Eq, Real, Num, Fractional)

isDouble :: GenericGData -> Bool
isDouble = checkType (typeName (undefined :: DoubleConstant))

asDouble :: GenericGData -> Double
asDouble = checkCoerce (typeName (undefined :: DoubleConstant))

instance GShow DoubleConstant where
    gshow (DoubleConstant d) = pure (show d)

instance GData DoubleConstant where
    typeName _ = fromString "Double"
    constr x = fromString $ show x
    constrArgs _ = array (0,-1) []

data BuiltinData = Ap {-# UNPACK #-} !GMachineAddress {-# UNPACK #-} !GMachineAddress |
                   Fun {-# UNPACK #-} !Int GCodeSequence |
                   BuiltinFun {-# UNPACK #-} !Int !ModuleName !VariableName GCodeBuiltin

asBuiltin :: GData a => a -> BuiltinData
asBuiltin dat = if isBuiltin dat then unsafeCoerce dat else
                    error $ "Cannot coerce builtin data"

instance GShow BuiltinData where
    gshow a = pure (show a)

instance GData BuiltinData where
    typeName _ = fromString "BuiltinData"
    constr _ = error "Attempt to examine constructor of builtin data"
    constrArgs (Ap a1 a2) = listArray (0, 1) [a1, a2]
    constrArgs _ = array (0,-1) []
    isBuiltin _ = True

instance Show BuiltinData where
    show (Ap a b) = "Ap (" ++ show a ++ ") (" ++ show b ++ ")"
    show (Fun i s) = "Fun " ++ show i ++ " " ++ show s
    show (BuiltinFun i modName symbolName _) = "BuiltinFun " ++ show i ++ " (" ++ show symbolName ++ " from " ++ show modName ++ ")"

instance Show GMachineError where
    show (GMachineError _ e) = e

instance Exception GMachineError

todo :: MonadIO m => String -> m ()
todo = liftIO . putStrLn . ("TODO: " ++)

-- | Throw an error from within the GMachine monad
throwError :: String -> GMachine a
throwError errorMsg = GMachine (\st ->
                                  return $ Left $ GMachineError st errorMsg)

-- | Rethrow an error from within the GMachine monad
throwError' :: GMachineError -> GMachine a
throwError' e = GMachine (\st -> return $ Left e)