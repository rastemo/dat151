module TypeChecker where

import Control.Monad

import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.List as List

-------
import CPP.Lex
import CPP.Par
------

import CPP.Abs
import CPP.Print
import CPP.ErrM

--------------------------------------------------------------------------------

-- * types, data

-- | Function table and list of Contexts
type Env = (Sig,[Context])
-- | Function table
type Sig = Map Id ([Type],Type)
-- | Variable table
type Context = Map Id Type

testSig :: Sig
testSig = Map.fromList [(Id "main",([],Type_int)),(Id "test",([Type_int,Type_int],Type_void))]
testCxt1 :: Context
testCxt1 = Map.fromList [(Id "x",Type_int),(Id "y",Type_int)]
testCxt2 :: Context
testCxt2 = Map.fromList [(Id "x",Type_bool),(Id "z",Type_double)]
testEnv :: Env
testEnv = (testSig,[testCxt1,testCxt2])

lookupVar :: Env -> Id -> Err Type
lookupVar (_,cs) id = getType cs
  where getType []     = fail $ "variable " ++ printTree id ++ " not in scope"
        getType (c:cs) = do
          case Map.lookup id c of
            Just typ -> return typ
            Nothing -> getType cs

lookupFun :: Env -> Id -> Err ([Type],Type)
lookupFun (sig,_) id = do
  case Map.lookup id sig of
    Just fun -> return fun
    Nothing -> fail $ "function " ++ printTree id ++ " not defined"

updateVar :: Env -> Id -> Type -> Err Env
updateVar = undefined

--updateFun :: Env -> Id -> ([Type],Type)
--updateFun = undefined

newBlock :: Env -> Env
newBlock (sig,cs) = (sig,Map.fromList [] : cs)

--emptyEnv :: Env
--emptyEnv = undefined

-------------------------------------------------------------------------------

-- | Predefined functions
preDef :: [(Id,([Type],Type))]
preDef = [(Id "printInt",    ([Type_int],Type_void)),
          (Id "printDouble", ([Type_double],Type_void)),
          (Id "readInt",     ([],Type_int)),
          (Id "readDouble",  ([],Type_double))]

------------------------------------------------------------------------------
        
-- | Type checks program
typecheck :: Program -> Err ()
typecheck p = do
  -- check function definitions
  sig <- checkDefs' p
  let (PDefs ds) = p
  checkDefs (sig, []) ds 
  return ()

-- data Def = DFun Type Id [Arg] [Stm]
-- data Arg = ADecl Type Id


inferExp :: Env -> Exp -> Err Type
inferExp env exp = case exp of

  ETrue     -> return Type_bool
  EFalse    -> return Type_bool
  EInt _    -> return Type_int
  EDouble _ -> return Type_double
  EId id    -> lookupVar env id
  EApp id es ->
    do (typs,typ) <- lookupFun env id
       args <- sequence $ map (inferExp env) es
       unless (typs == args)
         $ fail $ "types of " ++
           List.intercalate ", " (map printTree args) ++
           " expected for function " ++ (printTree id) ++ 
           "but found " ++ List.intercalate ", " (map printTree typs)
       return typ
  EPostIncr id -> incdec id
  EPostDecr id -> incdec id
  EPreIncr id -> incdec id
  EPreDecr id -> incdec id
  ETimes e1 e2 -> inferBin [Type_int,Type_double] env e1 e2
  EDiv   e1 e2 -> inferBin [Type_int,Type_double] env e1 e2
  EPlus  e1 e2 -> inferBin [Type_int,Type_double] env e1 e2
  EMinus e1 e2 -> inferBin [Type_int,Type_double] env e1 e2
  ELt    e1 e2 -> inferBin [Type_bool] env e1 e2
  EGt    e1 e2 -> inferBin [Type_bool] env e1 e2
  ELtEq  e1 e2 -> inferBin [Type_bool] env e1 e2
  EGtEq  e1 e2 -> inferBin [Type_bool] env e1 e2
  EAnd   e1 e2 -> inferBin [Type_bool] env e1 e2
  EOr    e1 e2 -> inferBin [Type_bool] env e1 e2
  EEq    e1 e2 -> inferBin [Type_int,Type_double,Type_bool] env e1 e2
  ENEq   e1 e2 -> inferBin [Type_int,Type_double,Type_bool] env e1 e2
  EAss id exp -> do
    typ <- lookupVar env id
    checkExp env typ exp
    return typ
  
  where incdec id =
          do typ <- lookupVar env id
             unless (typ /= Type_int || typ /= Type_double)
               $ fail $ "type of int or double expected but found" ++ printTree typ
             return typ

inferBin :: [Type] -> Env -> Exp -> Exp -> Err Type
inferBin typs env e1 e2 = do
  typ <- inferExp env e1
  unless (elem typ typs) $ fail $ "wrong type of expression " ++ printTree e1
  checkExp env typ e2
  return typ  
  

checkExp :: Env -> Type -> Exp -> Err ()
checkExp env typ exp = do
  typ' <- inferExp env exp
  unless (typ' == typ) $ fail $ "type of " ++ printTree exp ++
                                " expected " ++ printTree typ ++
                                " but found " ++ printTree typ'

checkDefs :: Env -> [Def] -> Err ()
checkDefs env []     = return ()
checkDefs env (d:ds) =
  do checkDef env d
     checkDefs env ds

checkDef :: Env -> Def -> Err ()
checkDef env (DFun typ id args stms) = do
  env' <- checkArgs env args  
  checkStms env' typ stms
  return ()

checkStms :: Env -> Type -> [Stm] -> Err Env
checkStms env typ stms = case stms of
  [] -> return env
  x : xs -> do
    env' <- checkStm env typ x
    checkStms env' typ xs

checkStm :: Env -> Type -> Stm -> Err Env
checkStm env val stm = case stm of
  SExp exp -> do
    inferExp env exp
    return env
  SDecls typ ids -> chain env ids
    where chain env [] = return env
          chain env (id:ids) = updateVar env id typ >>= (`chain` ids)
  SInit typ id exp -> do checkExp env typ exp
                         updateVar env id typ
  SReturn exp -> do
    checkExp env val exp
    return env
  SWhile exp stm -> do
    checkExp env Type_bool exp
    checkStm env val stm
    return env
  SBlock stms -> do
    checkStms (newBlock env) val stms
    return env
  SIfElse exp stm stm' -> do
    checkExp env Type_bool exp
    checkStm env val stm
    checkStm env val stm'
    return env

checkArgs :: Env -> [Arg] -> Err Env
checkArgs = undefined

checkDefs' :: Program -> Err Sig
checkDefs' p = do
  -- add function definitions to Sig
  let ds = addDefs p ++ preDef
      s  = Map.fromList $ ds
  -- check for duplicate function id:s
  let names = map fst ds
      dup = names List.\\ List.nub names
  unless (length dup == 0) $ fail $
    "the following functions are defined several times: " ++
    List.intercalate ", " (map printTree dup)
  return s

addDefs :: Program -> [(Id,([Type],Type))]
addDefs (PDefs ds) = map getDefType ds
  where getDefType (DFun t id as _) = (id, (map getArgType as,t))
        getArgType (ADecl t id)     =  t

checkMain :: Sig -> Err ()
checkMain sig = do
  case Map.lookup (Id "main") sig of
    Just (args,t) -> do
      unless (t == Type_int) $ fail "function main does not return int"
      unless (null args) $ fail "function main does not take argmuments"
    Nothing -> fail "no function main found"

--------------------------------------------------------------------------------




