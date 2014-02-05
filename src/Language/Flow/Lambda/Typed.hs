module Language.Flow.Lambda.Typed where
    import qualified Language.Flow.AST as L

    import Control.Monad.Error
    import Control.Monad.Error.Class

    import qualified Data.Set as S
    import qualified Data.Text as T
    import qualified Data.Map as M
    import Data.Maybe
    import Data.Monoid
    import Data.Foldable hiding (concat, foldr, foldl)
    import Data.List

    data TypeSubstitution = TypeSubstitution {
                                    runSubst  :: L.VariableName -> L.Type,
                                    varsSubst :: S.Set L.VariableName
                                  }
    type TyCheckM = Either TyCheckError

    data TyScheme = Scheme [L.VariableName] L.Type
                  deriving (Show, Ord, Eq)

    data TyCheckError = CantConstructInfiniteType L.Region L.VariableName L.Type |
                        CouldNotMatchTypes L.Region L.Type L.Type |
                        UnknownError String
         deriving (Show)

    newtype NameSupply = NameSupply { unNS :: [Int] }

    newtype TypeEnv = TypeEnv { unTypeEnv :: M.Map L.VariableName TyScheme }
        deriving (Show, Eq, Ord)

    instance Error TyCheckError where
        strMsg s = UnknownError s

    instance Show TypeSubstitution where
        show ts = concat ["TypeSubstitution {",
                          intercalate ", " (map (\n -> concat [T.unpack . L.unVariableName $ n,
                                                              " -> ",
                                                              show (runSubst ts n)])
                                           (S.toList . varsSubst $ ts)),
                          "}"]

    instance Monoid TypeSubstitution where
        mempty = TypeSubstitution { runSubst = \n -> L.TypeVariable n,
                                    varsSubst = S.empty }
        mappend = (<.>)

    throwWithRegion :: L.Region -> TyCheckError -> TyCheckM a
    throwWithRegion r (CantConstructInfiniteType _ v t) = throwError (CantConstructInfiniteType r v t)
    throwWithRegion r (CouldNotMatchTypes _ t1 t2) = throwError (CouldNotMatchTypes r t1 t2)
    throwWithRegion _ x = throwError x

    nameSequence :: NameSupply
    nameSequence = NameSupply [0, 10..]

    nextName :: NameSupply -> (NameSupply, L.VariableName)
    nextName ns = (NameSupply . tail . unNS $ ns, L.VariableName . T.pack . ("x" ++ ) . show . head . unNS $ ns)

    names :: NameSupply -> [L.VariableName]
    names ns = let (ns', n) = nextName ns
               in n:names ns'

    split :: NameSupply -> (NameSupply, NameSupply)
    split ns = (ns, NameSupply (map (+1) (unNS ns)))

    insertTypeScheme :: L.VariableName -> TyScheme -> TypeEnv -> TypeEnv
    insertTypeScheme var scheme env = TypeEnv (M.insert var scheme (unTypeEnv env))

    -- | TypeSubstitution composition
    (<.>) :: TypeSubstitution -> TypeSubstitution -> TypeSubstitution
    phi <.> psi = TypeSubstitution { runSubst = \tvn -> tySub phi (runSubst psi tvn), varsSubst = varsSubst phi `S.union` varsSubst psi }

    tsVarSubst :: L.VariableName -> L.Type -> TypeSubstitution
    tsVarSubst varName subst = TypeSubstitution {
                                    runSubst = \candidate ->
                                               if varName == candidate
                                               then subst
                                               else L.TypeVariable candidate,
                                    varsSubst = S.singleton varName }

    tsExclude :: TypeSubstitution -> [L.VariableName] -> TypeSubstitution
    tsExclude phi scvs =
        let scvsS = S.fromList scvs
        in TypeSubstitution {
                 runSubst = \candidate -> if candidate `S.member` scvsS
                                          then L.TypeVariable candidate
                                          else runSubst phi candidate,
                 varsSubst = varsSubst phi S.\\ scvsS }

    tsAssocs :: [(L.VariableName, L.Type)] -> TypeSubstitution
    tsAssocs assocs = let assocsMap = M.fromList assocs
                      in TypeSubstitution {
                                    varsSubst = M.keysSet assocsMap,
                                    runSubst = \candidate ->
                                               case M.lookup candidate assocsMap of
                                                 Just t -> t
                                                 Nothing -> L.TypeVariable candidate }

    tyVarsIn :: L.Type -> S.Set L.VariableName
    tyVarsIn (L.TypeVariable v) = S.singleton v
    tyVarsIn (L.TypeConstructor _ args) = mconcat . map tyVarsIn $ args

    tySub :: TypeSubstitution -> L.Type -> L.Type
    tySub phi (L.TypeVariable v) = runSubst phi v
    tySub phi (L.TypeConstructor c args) = L.TypeConstructor c (map (tySub phi) args)

    tyExtend :: TypeSubstitution -> L.VariableName -> L.Type -> TyCheckM TypeSubstitution
    tyExtend phi tvn (L.TypeVariable tvn')
        | tvn == tvn' = return phi
    tyExtend phi tvn ty
        | tvn `S.member` (tyVarsIn ty) = throwError (CantConstructInfiniteType L.EmptyRegion tvn ty)
        | otherwise = return (tsVarSubst tvn ty <.> phi)

    -- | Main unification algorithm
    tyUnify :: TypeSubstitution -> L.Type -> L.Type -> TyCheckM TypeSubstitution
    tyUnify phi (L.TypeVariable tvn) t
        | phitvn == L.TypeVariable tvn = tyExtend phi tvn phit
        | otherwise                    = tyUnify phi phitvn phit
        where phitvn = runSubst phi tvn
              phit   = tySub phi t
    tyUnify phi tc@(L.TypeConstructor _ _) tv@(L.TypeVariable _) = tyUnify phi tv tc
    tyUnify phi t1@(L.TypeConstructor tcn ts) t2@(L.TypeConstructor tcn' ts')
        | tcn == tcn' = foldrM (\(t1, t2) phi -> tyUnify phi t1 t2) phi (ts `zip` ts')
        | otherwise          = throwError (CouldNotMatchTypes L.EmptyRegion t1 t2)

    tySchemeUnknowns :: TyScheme -> S.Set L.VariableName
    tySchemeUnknowns (Scheme sns t) = tyVarsIn t S.\\ S.fromList sns

    tySubScheme :: TypeSubstitution -> TyScheme -> TyScheme
    tySubScheme phi (Scheme scvs t) = Scheme scvs (tySub (tsExclude phi scvs) t)

    tyEnvUnknowns :: TypeEnv -> S.Set L.VariableName
    tyEnvUnknowns (TypeEnv env) = S.unions (map tySchemeUnknowns (M.elems env))

    tySubEnv :: TypeSubstitution -> TypeEnv -> TypeEnv
    tySubEnv phi gamma = TypeEnv (M.map (tySubScheme phi) (unTypeEnv gamma))

    typeCheckS :: TypeEnv -> NameSupply -> [L.Expression] -> TyCheckM (TypeSubstitution, [L.Type])
    typeCheckS env ns [] = return (mempty, [])
    typeCheckS env ns (e:es) = do
      (phi, t) <- typeCheck env ns e
      let env' = tySubEnv phi env
      (psi, ts) <- typeCheckS env' ns es
      return (psi <.> phi, (tySub psi t):ts)

    vid2Name vid = L.VariableName . T.pack . concat $ ["v", show vid]

    -- | The type checker
    typeCheck :: TypeEnv -> NameSupply -> L.Expression -> TyCheckM (TypeSubstitution, L.Type)
    typeCheck env ns (L.Literal r l) = case l of
                                         L.IntLiteral _ -> return (mempty, L.intType)
                                         L.StringLiteral _ -> return (mempty, L.stringType)
                                         L.DoubleLiteral _ -> return (mempty, L.doubleType)
    typeCheck env ns (L.Identifier r v) = let Just scheme@(Scheme scvs t) = M.lookup v (unTypeEnv env)
                                              newinstance = tySub phi t
                                              phi = tsAssocs (scvs `zip` (map L.TypeVariable (names ns)))
                                          in return (mempty, newinstance)
    typeCheck env ns (L.VariableRef r v) = typeCheck env ns (L.Identifier r (vid2Name v))
    typeCheck env ns (L.Ap r e1 e2) = do
                                    let (ns', tvn) = nextName ns
                                    (phi, [t1, t2]) <- typeCheckS env ns' [e1, e2]
                                    phi <- tyUnify phi t1  (L.fnType t2 (L.TypeVariable tvn))
                                           `catchError` (throwWithRegion r)
                                    return (phi, runSubst phi tvn)
    typeCheck env ns (L.Lambda rl [L.PlaceholderPattern rp] e) = typeCheck env ns e
    typeCheck env ns (L.Lambda rl [L.VariablePattern rp name] e) = do
                                    let env' = insertTypeScheme name (Scheme [] (L.TypeVariable n)) env
                                        (ns', n) = nextName ns
                                    (phi, t) <- typeCheck env' ns' e
                                    return (phi, L.fnType (runSubst phi n) t)
    typeCheck env ns (L.Lambda rl [L.VarIDPattern rp vid] e) = do
                                    let env' = insertTypeScheme (vid2Name vid) (Scheme [] (L.TypeVariable n)) env
                                        (ns', n) = nextName ns
                                    (phi, t) <- typeCheck env' ns' e
                                    return (phi, L.fnType (runSubst phi n) t)
    typeCheck env ns (L.SimpleLet rl (v,b) expr) = do
                                    (phi, t) <- typeCheck env ns b
                                    let (ns', ns'') = split ns
                                        env' = tySubEnv phi env
                                        env'' = insertTypeScheme (vid2Name v) scheme env'

                                        unknowns = tyEnvUnknowns env'
                                        scheme = let al = (S.toList scvs) `zip` (map L.TypeVariable (names ns'))
                                                     scvs = tyVarsIn t `S.union` unknowns
                                                     t' = tySub (tsAssocs al) t
                                                 in Scheme (names ns') t'
                                    (phi', t) <- typeCheck env'' ns'' expr
                                    return (phi' <.> phi, t)
    typeCheck env ns (L.LetIn rl _ bindings expr) = do
                                    let bindings' = map (\(L.Binding _ (L.VarIDPattern _ v) e) -> (vid2Name v, e)) bindings
                                        bindingVars = map fst bindings'
                                        bindingExprs = map snd bindings'

                                        (ns0, ns') = split ns
                                        (ns1, ns2) = split ns'
                                        nbvs = bindingVars `zip` (map newBVar (names ns2))

                                        newBVar tvn = Scheme [] (L.TypeVariable tvn)

                                        env' = foldr (uncurry insertTypeScheme) env nbvs
                                    (phi, ts) <- typeCheckS env' ns1 bindingExprs

                                    let ts' = map oldBVar . M.elems . unTypeEnv $ nbvs'
                                        nbvs' = tySubEnv phi (TypeEnv . M.fromList $ nbvs)
                                        env'' = tySubEnv phi env

                                        oldBVar :: TyScheme -> L.Type
                                        oldBVar (Scheme [] t) = t

                                    phi <- foldrM (\(t1, t2) phi -> tyUnify phi t1 t2 `catchError` (throwWithRegion rl)) phi (ts `zip` ts')
                                    let ts = map oldBVar . M.elems . unTypeEnv $ nbvs''
                                        nbvs'' = tySubEnv phi nbvs'
                                        env'' = tySubEnv phi env'
                                        (ns0', ns0'') = split ns0
                                        env''' = foldr (uncurry insertTypeScheme) env'' (bindingVars `zip` schemes)
                                        unknowns = tyEnvUnknowns env''
                                        schemes = map genbar ts

                                        genbar t = let al = (S.toList scvs) `zip` (map L.TypeVariable . names $ ns0')
                                                       scvs = tyVarsIn t `S.union` unknowns
                                                       t' = tySub (tsAssocs al) t
                                                   in Scheme (names ns0') t'

                                    (phi', t) <- typeCheck env''' ns0'' expr
                                    return (phi' <.> phi, t)
--    typeCheck env ns (L.Let