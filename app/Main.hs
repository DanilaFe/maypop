module Main where

import System.Environment
import Language.Maypop.Syntax
import Language.Maypop.Eval
import Language.Maypop.Modules
import Language.Maypop.LoadingImpl
import qualified Data.Map as Map
import Data.Maybe

moduleFunctions :: Module -> [Function]
moduleFunctions m = catMaybes $ map (asFunction . dContent) $ Map.elems $ mDefinitions m

printFunction :: Function -> IO ()
printFunction f = mapM_ (putStrLn . ("  "++)) $
    [ "Function name: " ++ fName f
    , "Function type: " ++ pretty (fFullType f)
    , ""
    ]

runMain :: Module -> IO ()
runMain m = case Map.lookup "main" (mDefinitions m) of
    Just Definition{dContent = FunDef f} -> putStrLn $ pretty $ eval (fBody f)
    Just Definition{dContent = FixDef f} -> putStrLn $ pretty $ eval (fBody (fxFun f))
    Nothing -> putStrLn "No main function!"

main :: IO ()
main = do
    file <- head <$> getArgs
    mm <- defaultLoadFile file
    case mm of
        Left e -> error $ "Error while checking the file: " ++ show e
        Right m -> do
            putStrLn $ "Successfully read module " ++ show (mName m)
            putStrLn "Functions: "
            mapM_ printFunction (moduleFunctions m)
            runMain m
    return ()
