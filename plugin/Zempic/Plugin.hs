-- Copyright 2026 Keith Adler. Licensed under the Apache License, Version 2.0.
--
-- A GHC Core plugin for leanzempic (SPIKE).
--
-- Reads the s-expression file that Lean writes in `mode core` and replaces the right-hand side of
-- each stub binding with Core built directly from it. No Haskell is parsed, typechecked or
-- desugared for the function bodies. Core Lint (-dcore-lint) checks the result.
module Zempic.Plugin (plugin) where

import Control.Monad (foldM)
import Data.Char (isSpace)
import Data.List (sortOn)
import qualified Data.Map.Strict as M
import GHC.Core.TyCo.Rep (scaledThing)
import GHC.Plugins
import GHC.Platform (Platform)

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install, pluginRecompile = purePlugin }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install [file] todos = return (CoreDoPluginPass "zempic-inject" (inject file) : todos)
install _ _ = error "zempic plugin: expected -fplugin-opt=Zempic.Plugin:FILE.zc"

-- * S-expressions

data SExp = Atom String | List [SExp] deriving Show

parseSExps :: String -> [SExp]
parseSExps s = case go (dropWhile isSpace s) of (xs, _) -> xs
  where
    go [] = ([], [])
    go (')' : rest) = ([], rest)
    go ('(' : rest) =
      let (inner, rest') = go (dropWhile isSpace rest)
          (more, rest'') = go (dropWhile isSpace rest')
      in (List inner : more, rest'')
    go str =
      let (a, rest) = break (\c -> isSpace c || c == '(' || c == ')') str
          (more, rest') = go (dropWhile isSpace rest)
      in (Atom a : more, rest')

-- * Building Core

data Env = Env
  { envVars :: M.Map String Id     -- local variables
  , envFns :: M.Map String Id      -- functions of the module being compiled
  , envPrims :: M.Map String Id    -- runtime primitives, looked up by name
  , envPlatform :: Platform
  }

local :: String -> Type -> CoreM Id
local name ty = mkSysLocalM (fsLit name) manyDataConTy ty

callee :: Env -> String -> CoreM Id
callee env f = case M.lookup f (envFns env) of
  Just i -> return i
  Nothing -> maybe (error ("zempic plugin: unknown function " ++ f)) return (M.lookup f (envPrims env))

atomVar :: Env -> SExp -> CoreExpr
atomVar env (Atom x) = maybe (error ("zempic plugin: unbound " ++ x)) Var (M.lookup x (envVars env))
atomVar _ e = error ("zempic plugin: expected a variable, got " ++ show e)

buildValue :: Env -> SExp -> CoreM CoreExpr
buildValue env v = case v of
  List [Atom "lit", Atom n] -> return (mkWordExpr (envPlatform env) (read n))
  List [Atom "var", x] -> return (atomVar env x)
  List (Atom "call" : Atom f : args) -> do
    fid <- callee env f
    return (mkCoreApps (Var fid) (map (atomVar env) args))
  _ -> error ("zempic plugin: value " ++ show v)

buildCode :: Env -> SExp -> CoreM CoreExpr
buildCode env c = case c of
  List [Atom "ret", x] -> return (atomVar env x)
  List [Atom "let", Atom x, v, k] -> do
    rhs <- buildValue env v
    b <- local x (exprType rhs)
    body <- buildCode env { envVars = M.insert x b (envVars env) } k
    -- A strict let is a case that binds the evaluated value: Lean evaluates eagerly.
    return (Case rhs b (exprType body) [Alt DEFAULT [] body])
  List (Atom "case" : Atom x : alts) -> do
    let scrut = atomVar env (Atom x)
    w <- local "w" boolTy
    built <- mapM (buildAlt env) alts
    let ty = case built of
          ((_, e) : _) -> exprType e
          [] -> error "zempic plugin: case without alternatives"
    -- Core wants DEFAULT first, then constructors in tag order (False before True).
    let rank (DEFAULT, _) = 0 :: Int
        rank (DataAlt dc, _) = if dc == falseDataCon then 1 else 2
        rank _ = 3
    return (Case scrut w ty [Alt con [] e | (con, e) <- sortOn rank built])
  _ -> error ("zempic plugin: code " ++ show c)

buildAlt :: Env -> SExp -> CoreM (AltCon, CoreExpr)
buildAlt env (List [Atom con, k]) = do
  e <- buildCode env k
  return (case con of
    "True" -> DataAlt trueDataCon
    "False" -> DataAlt falseDataCon
    _ -> DEFAULT, e)
buildAlt _ a = error ("zempic plugin: alternative " ++ show a)

-- | @(fn name (params) code)@ against the stub binder's type.
buildFn :: Env -> Id -> [SExp] -> SExp -> CoreM CoreExpr
buildFn env stub params code = do
  let (argTys, _) = splitFunTys (idType stub)
  ps <- sequence [ local x (scaledThing t) | (Atom x, t) <- zip params argTys ]
  let env' = env { envVars = M.fromList (zip [x | Atom x <- params] ps) }
  body <- buildCode env' code
  return (mkCoreLams ps body)

inject :: FilePath -> ModGuts -> CoreM ModGuts
inject file guts = do
  text <- liftIO (readFile file)
  hsc <- getHscEnv
  let allDefs = [ (name, params, code) | List [Atom "fn", Atom name, List params, code] <- parseSExps text ]
      flat = concatMap flattenBind (mg_binds guts)
      stubs = M.fromList [ (occNameString (nameOccName (idName b)), b) | (b, _) <- flat ]
      -- Only the module that holds the stubs is touched; the plugin sees every module of a build.
      defs = [ d | d@(name, _, _) <- allDefs, M.member name stubs ]
  if null defs then return guts else injectDefs hsc guts defs flat stubs

injectDefs :: HscEnv -> ModGuts -> [(String, [SExp], SExp)] -> [(Id, CoreExpr)] -> M.Map String Id -> CoreM ModGuts
injectDefs hsc guts defs flat stubs = do
  let
      -- p_NAME = NAME in the stub: the right-hand side is the imported primitive's Id.
      prims = M.fromList [ (drop 2 n, v) | (b, Var v) <- flat
                         , let n = occNameString (nameOccName (idName b)), take 2 n == "p_" ]
      env0 = Env M.empty (M.fromList [ (n, b) | (n, _, _) <- defs, Just b <- [M.lookup n stubs] ])
                 prims (targetPlatform (hsc_dflags hsc))
  built <- foldM
    (\acc (name, params, code) -> case M.lookup name stubs of
        Nothing -> error ("zempic plugin: no stub for " ++ name)
        Just b -> do
          rhs <- buildFn env0 b params code
          return (acc ++ [(b, rhs)]))
    [] defs
  let replaced = M.fromList [ (b, ()) | (b, _) <- built ]
      untouched = [ bind | bind <- mg_binds guts, not (any (`M.member` replaced) (bindersOf bind)) ]
  putMsgS ("zempic plugin: injected Core for " ++ unwords [ occNameString (nameOccName (idName b)) | (b, _) <- built ])
  return guts { mg_binds = Rec built : untouched }

flattenBind :: CoreBind -> [(Id, CoreExpr)]
flattenBind (NonRec b e) = [(b, e)]
flattenBind (Rec ps) = ps
