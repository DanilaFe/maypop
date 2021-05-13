module Main where

import System.Environment
import Language.Maypop.Syntax
import Language.Maypop.Modules
import Language.Maypop.LoadingImpl
import qualified Data.Map as Map
import Data.Either

moduleFunctions :: Module -> [Function]
moduleFunctions m = rights $ map dContent $ Map.elems $ mDefinitions m

printFunction :: Function -> IO ()
printFunction f = mapM_ (putStrLn . ("  "++)) $
    [ "Function name: " ++ fName f
    , "Function type: " ++ show (fType f)
    , ""
    ]

main :: IO ()
main = do
    file <- head <$> getArgs
    mm <- defaultLoadFile file
    case mm of
        Left e -> putStrLn $ "Error while checking the file: " ++ show e
        Right m -> do
            putStrLn $ "Successfully read module " ++ show (mName m)
            putStrLn $ "Functions: "
            mapM_ printFunction (moduleFunctions m)
    return ()
