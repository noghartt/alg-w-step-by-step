module Main (main) where

import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified Text.PrettyPrint as PP

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

type Subst = Map.Map String Type

data Exp
  = EVar String
  | ELit Lit
  | EApp Exp Exp
  | EAbs String Exp
  | ELet String Exp Exp
  deriving (Eq, Ord)

data Lit = LInt Integer | LBool Bool
  deriving (Eq, Ord)

data Type
  = TVar String
  | TInt
  | TBool
  | TFun Type Type
  deriving (Eq, Ord)

data Scheme = Scheme [String] Type

class Types a where
  ftv   :: a -> Set.Set String
  apply :: Subst -> a -> a

instance Types Type where
  ftv (TVar n)         = Set.singleton n
  ftv TInt             = Set.empty
  ftv TBool            = Set.empty
  ftv (TFun t1 t2)     = ftv t1 `Set.union` ftv t2
  apply s (TVar n)     =
    case Map.lookup n s of
      Just t  -> t
      Nothing -> TVar n
  apply s (TFun t1 t2) = TFun (apply s t1) (apply s t2)
  apply _ t            = t

instance Types Scheme where
  ftv (Scheme vars t)     = (ftv t) `Set.difference` (Set.fromList vars)
  apply s (Scheme vars t) = Scheme vars (apply (foldr Map.delete s vars) t)

instance Types a => Types [a] where
  apply s = map (apply s)
  ftv l   = foldr Set.union (Set.empty) (map ftv l)

nullSubst :: Subst
nullSubst = Map.empty

composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = (Map.map (apply s1) s2) `Map.union` s1

newtype TypeEnv = TypeEnv (Map.Map String Scheme)

remove :: TypeEnv -> String -> TypeEnv
remove (TypeEnv env) var = TypeEnv (Map.delete var env)

instance Types TypeEnv where
  ftv (TypeEnv env)     = ftv (Map.elems env)
  apply s (TypeEnv env) = TypeEnv (Map.map (apply s) env)

generalize :: TypeEnv -> Type -> Scheme
generalize env t = Scheme vars t
  where vars = Set.toList (ftv t `Set.difference` ftv env)

type TIState = Int
type TI a    = ExceptT String (State TIState) a

runTI :: TI a -> (Either String a, TIState)
runTI t = runState (runExceptT t) initTIState
  where
    initTIState = 0

newTyVar :: TI Type
newTyVar = do
  s <- get
  put (s + 1)
  pure $ TVar (reverse (toTyVar s))
  where
    toTyVar c | c < 26    = [toEnum (97 + c)]
              | otherwise =
                let (n, r) = c `divMod` 26
                in (toEnum (97 + r) : toTyVar (n - 1))

instantiate :: Scheme -> TI Type
instantiate (Scheme vars t) = do
  nvars <- mapM (\_ -> newTyVar) vars
  let s = Map.fromList (zip vars nvars)
  pure $ apply s t

mgu :: Type -> Type -> TI Subst
mgu (TFun l r) (TFun l' r') = do
  s1 <- mgu l l'
  s2 <- mgu (apply s1 r) (apply s1 r')
  pure $ s1 `composeSubst` s2
mgu (TVar u) t = varBind u t
mgu t (TVar u) = varBind u t
mgu TInt TInt  = pure nullSubst
mgu TBool TBool = pure nullSubst
mgu t1 t2       = throwError  $ "types do not unify: " ++ show t1 ++ " vs. " ++ show t2

varBind :: String -> Type -> TI Subst
varBind u t
  | t == TVar u          = pure nullSubst
  | u `Set.member` ftv t =
    throwError $ "occurs check fails: " ++ u ++ " vs " ++ show t
  | otherwise = pure $ Map.singleton u t

tiLit :: TypeEnv -> Lit -> TI (Subst, Type)
tiLit _ (LInt _)  = pure (nullSubst, TInt)
tiLit _ (LBool _) = pure (nullSubst, TBool)

ti :: TypeEnv -> Exp -> TI (Subst, Type)
ti (TypeEnv env) (EVar n) =
  case Map.lookup n env of
    Nothing -> throwError $ "unbound variable: " ++ n
    Just sigma -> do
      t <- instantiate sigma
      pure (nullSubst, t)
ti env (ELit l) = tiLit env l
ti env (EAbs n e) = do
  tv <- newTyVar
  let TypeEnv env'  = remove env n
  let env'' = TypeEnv $ env' `Map.union` (Map.singleton n (Scheme [] tv))
  (s1, t1) <- ti env'' e
  pure (s1, TFun (apply s1 tv) t1)
ti env (EApp e1 e2) = do
  tv <- newTyVar
  (s1, t1) <- ti env e1
  (s2, t2) <- ti (apply s1 env) e2
  s3 <- mgu (apply s2 t1) (TFun t2 tv)
  pure (s3 `composeSubst` s2 `composeSubst` s1, apply s3 tv)
ti env (ELet x e1 e2) = do
  (s1, t1) <- ti env e1
  let TypeEnv env' = remove env x
  let t' = generalize (apply s1 env) t1
  let env'' = TypeEnv (Map.insert x t' env')
  (s2, t2) <- ti (apply s1 env'') e2
  pure (s1 `composeSubst` s2, t2)

typeInference :: Map.Map String Scheme -> Exp -> TI Type
typeInference env e = do
  (s, t) <- ti (TypeEnv env) e
  pure $ apply s t

instance Show Type where
  showsPrec _ x = shows (prType x)

prType :: Type -> PP.Doc
prType (TVar n)   = PP.text n
prType TInt       = PP.text "Int"
prType TBool      = PP.text "Bool"
prType (TFun t s) = prParenType t PP.<+> PP.text "->" PP.<+> prType s

prParenType :: Type -> PP.Doc
prParenType t = case t of
  TFun _ _ -> PP.parens (prType t)
  _        -> prType t

instance Show Exp where
  showsPrec _ x = shows (prExp x)
    where
      prExp (EVar name)     = PP.text name
      prExp (ELit lit)      = prLit lit
      prExp (ELet x b body) = PP.text "let" PP.<+> 
                              PP.text x PP.<+> PP.text "=" PP.<+>
                              prExp b PP.<+> PP.text "in" PP.$$
                              PP.nest 2 (prExp body)
      prExp (EApp e1 e2)    = prExp e1 PP.<+> prParensExp e2
      prExp (EAbs n e)      = PP.char '\\' PP.<> PP.text n PP.<+>
                              PP.text "->" PP.<+> prExp e
      prParensExp t = case t of
        ELet _ _ _ -> PP.parens (prExp t)
        EApp _ _   -> PP.parens (prExp t)
        EAbs _ _   -> PP.parens (prExp t)
        _          -> prExp t

instance Show Lit where
  showsPrec _ x = shows (prLit x)

prLit :: Lit -> PP.Doc
prLit (LInt i)  = PP.integer i
prLit (LBool b) = if b then PP.text "True" else PP.text "False"

instance Show Scheme where
  showsPrec _ x = shows (prScheme x)

prScheme :: Scheme -> PP.Doc
prScheme (Scheme vars t) = PP.text "All" PP.<+> 
  PP.hcat (PP.punctuate PP.comma (map PP.text vars))
  PP.<> PP.text "." PP.<+> prType t

e0  =  ELet "id" (EAbs "x" (EVar "x"))
        (EVar "id")
e1  =  ELet "id" (EAbs "x" (EVar "x"))
        (EApp (EVar "id") (EVar "id"))
e2  =  ELet "id" (EAbs "x" (ELet "y" (EVar "x") (EVar "y")))
        (EApp (EVar "id") (EVar "id"))
e3  =  ELet "id" (EAbs "x" (ELet "y" (EVar "x") (EVar "y")))
        (EApp (EApp (EVar "id") (EVar "id")) (ELit (LInt 2)))
e4  =  ELet "id" (EAbs "x" (EApp (EVar "x") (EVar "x")))
        (EVar "id")
e5  =  EAbs "m" (ELet "y" (EVar "m")
                 (ELet "x" (EApp (EVar "y") (ELit (LBool True)))
                       (EVar "x")))
test :: Exp -> IO ()
test e =
  let (res, _) = runTI (typeInference Map.empty e)
  in case res of
    Left err -> putStrLn $ show e ++ "\nerror: " ++ err
    Right t  -> putStrLn $ show e ++ " :: " ++ show t

main :: IO ()
main = mapM_ test [e5]