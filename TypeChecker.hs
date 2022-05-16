{-# LANGUAGE FlexibleContexts #-}

module TypeChecker where

import AbsLintte
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as Map
import System.IO
import Data.List
import System.Exit

type Loc = Int
type Name = Ident
type Env = Map.Map Name TType
type InterpreterT = ReaderT Env (ExceptT String IO)

throwError' :: MonadError String m => BNFC'Position -> String -> m v
throwError' (Just (a, b)) msg = do
    throwError $ "Line " ++ show a ++ " col " ++ show b ++ ": " ++ msg

refineProgram :: Program' BNFC'Position -> InterpreterT ()
refineProgram (IProgram p funDefs) = do
    let helper funDefs = do
        case funDefs of
            [] -> do
                res <- asks (Map.lookup (Ident "main"))
                case res of
                    Just (TFun [] TInt) -> return ()
                    Nothing -> throwError' p "No main function."
                    _ -> throwError' p "Invalid signature of main function."
            (funDef:xs) -> do
                let ~(IFunDef _ _ ident _ _) = funDef
                funT <- refineFunDef funDef
                local (Map.insert ident funT) (helper xs)
    helper funDefs

argToType :: Arg' a -> TType
argToType x = case x of
  ArgRef _ type_ _ -> (refineType type_)
  ArgVal _ type_ _ -> (refineType type_)

argToIdent :: Arg' a -> Ident
argToIdent x = case x of
  ArgRef _ _ ident -> ident
  ArgVal _ _ ident -> ident

refineStmt :: Stmt' BNFC'Position -> InterpreterT ()
refineStmt stmt = refineStmts [stmt]

assignVar :: BNFC'Position -> Ident -> TType -> InterpreterT ()
assignVar p ident typ = do
    varT <- asks (Map.lookup ident)
    case varT of
        Just varT' -> when (varT' /= typ) (throwError' p "Wrong type in variable assignment.")
        Nothing -> throwError' p "Undeclared variable assignment."

refineStmts :: [Stmt' BNFC'Position] -> InterpreterT ()
refineStmts stmts =
    case stmts of
        [] -> return ()
        (x:xs) -> case x of
            Empty _ -> refineStmts xs
            BStmt _ block -> do
                refineBlock block
                refineStmts xs
            Decl p type_ items -> do
                let identList = map identOfItem items
                when (not (listUnique identList)) (throwError' p "Variables names in declaration not unique.")
                let helper items = do
                    case items of
                        [] -> refineStmts xs
                        (item:xs) -> do
                            (ident, val) <- refineItem item
                            let uscIdent = Ident ("_" ++ (identToStr ident))
                            isDeclInBlock <- asks (Map.member uscIdent)
                            when (isDeclInBlock) (throwError' p ("Variable " ++ (identToStr ident) ++ " already declaraed in block."))
                            let defval = refineType type_
                            let val' = case val of
                                    Nothing -> defval
                                    Just val'' -> val''
                            case defval == val' of
                                False -> throwError' p "Wrong type in declaration."
                                True -> do
                                    local (Map.insert ident val' . Map.insert uscIdent val') (helper xs)
                helper items
            DeclF _ fundef -> do
                let ~(IFunDef _ _ ident _ _) = fundef
                funT <- refineFunDef fundef
                local (Map.insert ident funT) (refineStmts xs)
            Ass p ident expr -> do
                exprT <- refineExpr expr
                assignVar p ident exprT
                refineStmts xs
            Incr p ident -> do
                assignVar p ident TInt
                refineStmts xs
            Decr p ident -> do
                assignVar p ident TInt
                refineStmts xs
            Ret p expr -> do
                refExpr <- refineExpr expr
                (Just funT) <- asks (Map.lookup $ Ident "~funt")
                when (funT /= refExpr) (throwError' p "Wrong type returned.")
                refineStmts xs
            VRet p -> do
                (Just funT) <- asks (Map.lookup $ Ident "~funt")
                when (funT /= TVoid) (throwError' p "Wrong type returned.")
                refineStmts xs
            Cond p expr stmt -> do
                refineBool p expr
                refineStmt stmt
                refineStmts xs
            CondElse p expr stmt1 stmt2 -> do
                refineBool p expr
                refineStmt stmt1
                refineStmt stmt2
                refineStmts xs
            While p expr stmt -> do
                refineBool p expr
                local (Map.insert (Ident "~inloop") TVoid) (refineStmt stmt)
                refineStmts xs
            SExp _ expr -> refineExpr expr >> refineStmts xs
            Break p -> do
                notInLoop <- asks (Map.notMember (Ident "~inloop"))
                when (notInLoop) (throwError' p "Break outside of loop.")
            Continue p -> do
                notInLoop <- asks (Map.notMember (Ident "~inloop"))
                when (notInLoop) (throwError' p "Continue outside of loop.")
            Print p expr -> do
                refExpr <- refineExpr expr
                case refExpr of
                    TInt -> return ()
                    TBool -> return ()
                    TString -> return ()
                    _ -> throwError' p "Print on non-literal."
                refineStmts xs

identNotStartsWithUscore ident _ = not (isPrefixOf "_" (identToStr ident))

refineBlock :: Block' BNFC'Position -> InterpreterT ()
refineBlock (IBlock _ l) = local (Map.filterWithKey identNotStartsWithUscore) (refineStmts l)

listUnique :: (Eq a) => [a] -> Bool
listUnique [] = True
listUnique (x:xs) = x `notElem` xs && listUnique xs

refineFunDef :: FunDef' BNFC'Position -> InterpreterT (TType)
refineFunDef (IFunDef p type_ ident args block) = do
    let identList = map argToIdent args
    when (not (listUnique identList)) (throwError' p "Arguments not unique.")
    let funT = TFun (map argToType args) (refineType type_)
    let (TFun _ retT) = funT
    let argIterHelper remargs =
            case remargs of
                [] -> local ((Map.insert (Ident "~funt") retT) . (Map.insert ident funT)) (refineBlock block)
                (x:xs) -> do
                    let ident = argToIdent x
                    let argT = argToType x
                    local (Map.insert ident argT) (argIterHelper xs)
    argIterHelper args
    return (funT)

refineItem :: Item' BNFC'Position -> InterpreterT (Ident, Maybe TType)
refineItem x = case x of
  NoInit _ ident -> return (ident, Nothing)
  Init _ ident expr -> do
    refExpr <- refineExpr expr
    return (ident, Just refExpr)

identOfItem :: Item' BNFC'Position -> Ident
identOfItem x = case x of
  NoInit _ ident -> ident
  Init _ ident expr -> ident

identToStr :: Ident -> String
identToStr (Ident s) = s

refineType :: Type' a -> TType
refineType x = case x of
  Int _ -> TInt
  Str _ -> TString
  Bool _ -> TBool
  Void _ -> TVoid
  Lambda _ type_ types -> TFun (map refineType types) (refineType type_)

data Lit = LInt Integer
    | LBool Bool
    | LString String
    | LFun [Arg] Block Env Type
    | LVoid
    | LLambda
    | WasContinue
    | WasBreak
  deriving (Eq, Show)

data TType = TInt
    | TBool
    | TString
    | TVoid
    | TFun [TType] TType
    deriving (Eq, Show)

refineInt :: BNFC'Position -> Expr' BNFC'Position -> InterpreterT ()
refineInt p x = do
    x' <- refineExpr x
    case x' of
        TInt -> return ()
        _ -> throwError' p "Non-integer in integer expression."

refineBool :: BNFC'Position -> Expr' BNFC'Position -> InterpreterT ()
refineBool p x = do
    x' <- refineExpr x
    case x' of
        TBool -> return ()
        _ -> throwError' p "Non-boolean in boolean expression."

refineExpr :: Expr' BNFC'Position -> InterpreterT (TType)
refineExpr x = case x of
  EVar p ident -> do
    res <- asks (Map.lookup ident)
    case res of
        Just res' -> return res'
        Nothing -> throwError' p $ "Undeclared variable " ++ (identToStr ident) ++ "."
  ELitInt _ integer -> return $ TInt
  ELitTrue _ -> return $ TBool
  ELitFalse _ -> return $ TBool
  EApp p ident exprs -> do
    fun <- refineExpr (EVar p ident)
    case fun of
        (TFun args retType) -> do
            exprTypes <- mapM refineExpr exprs
            when (length args /= length exprTypes) (throwError' p "Wrong argument amount.")
            when (args /= exprTypes) (throwError' p "Wrong argument type.")
            return $ retType
        _ -> throwError' p "Application on non-function variable."
  ELambda _ type_ args block -> do
    return $ TFun (map argToType args) (refineType type_)
  ELbApp p expr exprs -> do
    refExpr <- refineExpr expr
    case refExpr of
        (TFun args retType) -> do
            exprTypes <- mapM refineExpr exprs
            when (length args /= length exprTypes) (throwError' p "Wrong argument amount.")
            when (args /= exprTypes) (throwError' p "Wrong argument type.")
            return $ retType
        _ -> throwError' p "Application on non-lambda expression, or lambda uninitialized."
  EString _ string -> return $ TString
  Neg p expr -> do
    arg <- refineInt p expr
    return $ TInt
  Not p expr -> do
    arg <- refineBool p expr
    return $ TBool
  EMul p expr1 mulop expr2 -> do
    lhs <- refineInt p expr1
    rhs <- refineInt p expr2
    return $ TInt
  EAdd p expr1 addop expr2 -> do
    lhs <- refineInt p expr1
    rhs <- refineInt p expr2
    return $ TInt
  ERel p expr1 relop expr2 -> do
    lhs <- refineInt p expr1
    rhs <- refineInt p expr2
    return $ TBool
  EAnd p expr1 expr2 -> do
    lhs <- refineBool p expr1
    rhs <- refineBool p expr2
    return $ TBool
  EOr p expr1 expr2 -> do
    lhs <- refineBool p expr1
    rhs <- refineBool p expr2
    return $ TBool

typeCheck :: Program' BNFC'Position -> IO ()
typeCheck x = do
    runRes <- runExceptT (runReaderT (refineProgram x) Map.empty >> return ())
    case runRes of
        Left err -> die ("Typechecker error: " ++ err)
        Right out -> return out
