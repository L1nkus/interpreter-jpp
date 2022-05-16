{-# LANGUAGE FlexibleContexts #-}

module Interpreter where

import AbsLintte
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as Map
import System.IO
-- import Debug.Trace
-- debug = flip trace

type Loc = Int
type Name = Ident
type Env = Map.Map Name Loc
type Store = Map.Map Loc Lit
type InterpreterT = StateT Store (ReaderT Env (ExceptT String IO))

nwloc :: InterpreterT Loc
nwloc = do
    m <- get
    return $ if Map.null m then 0 else (fst (Map.findMax m)) + 1

throwError' :: MonadError String m => BNFC'Position -> String -> m v
throwError' (Just (a, b)) msg = do
    throwError $ "Line " ++ show a ++ " col " ++ show b ++ ": " ++ msg

refineProgram :: Program' BNFC'Position -> InterpreterT ()
refineProgram (IProgram p funDefs) = do
    let helper funDefs = do
        case funDefs of
            [] -> do
                mbloc <- asks (Map.lookup (Ident "main"))
                case mbloc of
                    Just loc -> do
                        res <- gets (\x -> Map.lookup loc x)
                        case res of
                            Just (LFun [] block env (Int a)) -> do
                                mainRet <- local (const env) (refineBlock block)
                                case mainRet of
                                    Just (LInt 0) -> return ()
                                    Just (LInt x) -> throwError' p "Main returned non-zero exit code."
                                    Just WasBreak -> throwError' p "Break not inside while block."
                                    Just WasContinue -> throwError' p "Continue not inside while block."
                                    Nothing -> throwError' p "Main did not return."
                                    _ -> throwError' p "Main returned wrong type."
                            _ -> throwError' p "Invalid signature of main function."
                    Nothing -> throwError' p "No main function."
            (funDef:xs) -> do
                loc <- nwloc
                let ~(IFunDef _ _ ident _ _) = funDef
                local (Map.insert ident loc) (refineFunDef funDef loc >> helper xs)
    helper funDefs

refineArg :: Arg' BNFC'Position -> (Type, Ident, Bool)
refineArg x = case x of
  ArgRef _ type_ ident -> (type_, ident, True)
  ArgVal _ type_ ident -> (type_, ident, False)

argToType :: Arg' a -> Type' a
argToType x = case x of
  ArgRef _ type_ _ -> type_
  ArgVal _ type_ _ -> type_

refineStmt :: Stmt' BNFC'Position -> InterpreterT (Maybe Lit)
refineStmt stmt = refineStmts [stmt]

assignVar :: BNFC'Position -> Ident -> Expr -> InterpreterT ()
assignVar p ident expr = do
    refExpr <- refineExpr expr
    mbloc <- asks (Map.lookup ident)
    case mbloc of
        Just loc -> do
            modify (Map.insert loc refExpr)
        Nothing -> throwError' p "Undeclared variable assignment."

typeEqVal :: Type' a -> Lit -> Bool
typeEqVal type_ val = True -- Left to typechecker now.
-- typeEqVal type_ val = let defval = refineType type_
--         in case val of
--             LFun _ _ _ _ ->
--                 case defval of
--                     LLambda -> True
--                     _ -> False
--             _ -> case (val, defval) of
--                 (LInt a, LInt b) -> True
--                 (LBool a, LBool b) -> True
--                 (LString a, LString b) -> True
--                 (LVoid, LVoid) -> True
--                 _ -> False

refineStmts :: [Stmt' BNFC'Position] -> InterpreterT (Maybe Lit)
refineStmts stmts =
    case stmts of
        [] -> return Nothing
        (x:xs) -> case x of
            Empty _ -> refineStmts xs
            BStmt _ block -> do
                blockres <- refineBlock block
                case blockres of
                    Just justres -> return blockres
                    Nothing -> refineStmts xs
            Decl p type_ items -> do
                let identList = map identOfItem items
                when (not (listUnique identList)) (throwError' p "Variables names in declaration not unique.")
                let helper items = do
                    case items of
                        [] -> refineStmts xs
                        (item:xs) -> do
                            (ident, val) <- refineItem item
                            let defval = refineType type_
                            let val' = case val of
                                    Nothing -> defval
                                    Just val'' -> val''
                            case typeEqVal type_ val' of
                                False -> throwError' p "Wrong type in declaration."
                                True -> do
                                    loc <- nwloc
                                    modify (Map.insert loc val')
                                    local (Map.insert ident loc) (helper xs)
                helper items
            DeclF _ fundef -> do
                loc <- nwloc
                let ~(IFunDef _ _ ident _ _) = fundef
                local (Map.insert ident loc) (refineFunDef fundef loc >> refineStmts xs)
            Ass p ident expr -> do
                assignVar p ident expr
                refineStmts xs
            Incr p ident -> do
                crval <- refineInt p (EVar p ident)
                assignVar p ident (ELitInt p (crval + 1))
                refineStmts xs
            Decr p ident -> do
                crval <- refineInt p (EVar p ident)
                assignVar p ident (ELitInt p (crval - 1))
                refineStmts xs
            Ret _ expr -> do
                refExpr <- refineExpr expr
                return (Just refExpr)
            VRet _ -> return (Just LVoid)
            Cond p expr stmt -> do
                refExpr <- refineBool p expr
                condRes <- if refExpr then refineStmt stmt else return (Nothing)
                case condRes of
                    Just justres -> return condRes
                    Nothing -> refineStmts xs
            CondElse p expr stmt1 stmt2 -> do
                refExpr <- refineBool p expr
                condRes <- refineStmt $ if refExpr then stmt1 else stmt2
                case condRes of
                    Just justres -> return condRes
                    Nothing -> refineStmts xs
            While p expr stmt -> do
                refExpr <- refineBool p expr
                if refExpr then do
                    iterRes <- refineStmt stmt
                    case iterRes of
                        Just WasBreak -> refineStmts xs
                        Just WasContinue -> refineStmts (x:xs)
                        Just justres -> return iterRes
                        Nothing -> refineStmts (x:xs)
                else
                    refineStmts xs
            SExp _ expr -> refineExpr expr >> refineStmts xs
            Break _ -> return (Just WasBreak)
            Continue _ -> return (Just WasContinue)
            Print _ expr -> do
                refExpr <- refineExpr expr
                liftIO $ putStrLn $ case refExpr of
                    LInt x -> show x
                    LBool x -> show x
                    LString x -> x
                refineStmts xs

refineBlock :: Block' BNFC'Position -> InterpreterT (Maybe Lit)
refineBlock (IBlock _ l) = refineStmts l

listUnique :: (Eq a) => [a] -> Bool
listUnique [] = True
listUnique (x:xs) = x `notElem` xs && listUnique xs

refineFunDef :: FunDef' BNFC'Position -> Loc -> InterpreterT ()
refineFunDef (IFunDef p type_ ident args block) loc = do
    env <- ask
    let identList = map (\x -> let ~(_, ident, _) = refineArg x in ident) args
    when (not (listUnique identList)) (throwError' p "Arguments not unique.")
    modify (Map.insert loc (LFun args block env type_))
    return ()

refineItem :: Item' BNFC'Position -> InterpreterT (Ident, Maybe Lit)
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

refineType :: Type' a -> Lit
refineType x = case x of
  Int _ -> LInt 0
  Str _ -> LString ""
  Bool _ -> LBool False
  Void _ -> LVoid
  Lambda _ _ _ -> LLambda

data Lit = LInt Integer
    | LBool Bool
    | LString String
    | LFun [Arg] Block Env Type
    | LVoid
    | LLambda
    | WasContinue
    | WasBreak
  deriving (Eq, Show)

refineInt :: BNFC'Position -> Expr' BNFC'Position -> InterpreterT Integer
refineInt p x = do
    x' <- refineExpr x
    case x' of
        LInt x'' -> return x''
        _ -> throwError' p "Non-integer in integer expression."

refineBool :: BNFC'Position -> Expr' BNFC'Position -> InterpreterT Bool
refineBool p x = do
    x' <- refineExpr x
    case x' of
        LBool x'' -> return x''
        _ -> throwError' p "Non-boolean in boolean expression."

callFun p remargs remExprs block env retType = do
    curenv <- ask
    let argIterHelper remargs remExprs =
            case (remargs, remExprs) of
                ([], []) -> do
                    res <- refineBlock block
                    case res of
                        Just WasBreak -> throwError' p "Break not inside while block."
                        Just WasContinue -> throwError' p "Continue not inside while block."
                        Just res' ->
                            case typeEqVal retType res' of
                                    False -> throwError' p "Wrong returned argument type."
                                    True -> return (res)
                        Nothing -> throwError' p "Function did not return."
                ((arg:argxs), (expr:exprxs)) -> do
                    let (type_, ident, isref) = refineArg arg
                    refExpr <- local (const curenv) (refineExpr expr)
                    let defval = refineType type_
                    case typeEqVal type_ refExpr of
                        False -> throwError' p "Wrong argument type."
                        True -> do
                            if isref then do
                                case expr of
                                    EVar _ varIdent -> do
                                        let locres = Map.lookup varIdent curenv
                                        case locres of
                                            Just loc -> do
                                                local (Map.insert ident loc) (argIterHelper argxs exprxs)
                                            _ -> throwError' p "Undeclared variable passed as argument by reference."
                                    _ -> throwError' p "Wrong argument type."
                            else do
                                loc <- nwloc
                                modify (Map.insert loc refExpr)
                                local (Map.insert ident loc) (argIterHelper argxs exprxs)
                _ -> throwError' p "Wrong amount of arguments."
    local (const env) (argIterHelper remargs remExprs)

refineExpr :: Expr' BNFC'Position -> InterpreterT Lit
refineExpr x = case x of
  EVar p ident -> do
    mbloc <- asks (Map.lookup ident)
    case mbloc of
        Just loc -> do
            res <- gets (\x -> Map.lookup loc x)
            case res of
                Just res' -> return res'
                Nothing -> throwError' p "This shouldn't happen."
        Nothing -> throwError' p $ "Undeclared variable " ++ (identToStr ident) ++ "."
  ELitInt _ integer -> return $ LInt integer
  ELitTrue _ -> return $ LBool True
  ELitFalse _ -> return $ LBool False
  EApp p ident exprs -> do
    fun <- refineExpr (EVar p ident)
    case fun of
        (LFun _args _block _env _type) -> do
            res <- callFun p _args exprs _block _env _type
            case res of
                Just val -> return (val)
                Nothing -> return (LVoid)
        _ -> throwError' p "Application on non-function variable."
  ELambda _ type_ args block -> do
    env <- ask
    return $ LFun args block env type_
  ELbApp p expr args -> do
    refExpr <- refineExpr expr
    case refExpr of
        LFun funArgs block env type_ -> do
            res <- callFun p funArgs args block env type_
            case res of
                Just val -> return (val)
                Nothing -> return (LVoid)
        _ -> throwError' p "Application on non-lambda expression, or lambda uninitialized."
  EString _ string -> return $ LString string
  Neg p expr -> do
    arg <- refineInt p expr
    return $ LInt (-arg)
  Not p expr -> do
    arg <- refineBool p expr
    return $ LBool (not arg)
  EMul p expr1 mulop expr2 -> do
    lhs <- refineInt p expr1
    rhs <- refineInt p expr2
    op <- refineMulOp mulop
    case mulop of
        Div _ -> when (rhs == 0) (throwError' p "Division by zero.")
        _ -> return ()
    return $ LInt (op lhs rhs)
  EAdd p expr1 addop expr2 -> do
    lhs <- refineInt p expr1
    rhs <- refineInt p expr2
    op <- refineAddOp addop
    return $ LInt (op lhs rhs)
  ERel p expr1 relop expr2 -> do
    lhs <- refineInt p expr1
    rhs <- refineInt p expr2
    op <- refineOrdOp relop
    return $ LBool (op lhs rhs)
  EAnd p expr1 expr2 -> do
    lhs <- refineBool p expr1
    rhs <- refineBool p expr2
    return $ LBool (lhs && rhs)
  EOr p expr1 expr2 -> do
    lhs <- refineBool p expr1
    rhs <- refineBool p expr2
    return $ LBool (lhs || rhs)

refineAddOp :: Show a => AddOp' a -> InterpreterT (Integer -> Integer -> Integer)
refineAddOp x = case x of
  Plus _ -> return (+)
  Minus _ -> return (-)

refineMulOp :: Show a => MulOp' a -> InterpreterT (Integer -> Integer -> Integer)
refineMulOp x = case x of
  Times _ -> return (*)
  Div _ -> return div
  Mod _ -> return mod

refineOrdOp :: (Show a, Ord b) => RelOp' a -> InterpreterT (b -> b -> Bool)
refineOrdOp x = case x of
  LTH _ -> return (<)
  LE _ -> return (<=)
  GTH _ -> return (>)
  GE _ -> return (>=)
  EQU _ -> return (==)
  NE _ -> return (/=)

interpret :: Program' BNFC'Position -> IO ()
interpret x = do
    runRes <- runExceptT (runReaderT (execStateT (refineProgram x) Map.empty) Map.empty >> return ())
    case runRes of
        Left err -> hPutStrLn stderr ("Error: " ++ err)
        Right out -> return out
