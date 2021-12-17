import Control.Monad;
import System.Exit;
import System.Directory;
import System.Environment;
import System.IO;
import Data.List;
import Data.List.Split;

main :: IO ();
main = getArgs >>= \a ->
  if a == []
    then edFunction a
    else doesFileExist (a !! 0) >>= \fileExists ->
      if fileExists
        then readFile (a !! 0) >>= edFunction . lines
        else writeFile (a !! 0) "" >> main;

parseNums :: String -> [String] -> [Int];
parseNums n b = haveFun $ map san $ splitOn "," n
  where
  haveFun ["",""] = [1,length b]
  haveFun ["",c] = [1,read c]
  haveFun [a,""] = [read a,length b]
  haveFun j = map read j
  san = filter (`elem` ['0'..'9']);

genRange :: [Int] -> [Int];
genRange [a,b] = [a..b];

insertAt :: Int -> [a] -> [a] -> [a];
insertAt n x xs = take g xs ++ x ++ drop g xs
  where g = n - 1;

edPrintLine :: Int -> [String] -> IO [String];
edPrintLine n buf = (putStrLn $ buf !! (n - 1)) >> return buf;

edInsert :: Int -> [String] -> IO [String];
edInsert n buf = isEOF >>= \ a ->
  if a
    then return buf
    else getLine >>= \ x -> edInsert (n + 1) $ insertAt n [x] buf;

edWrite :: [String] -> String -> IO [String];
edWrite buf fn = writeFile fn conkd >> return buf
  where conkd = foldr (++) [] $ intersperse "\n" buf;

edDel :: Int -> [String] -> IO [String];
edDel n buf = return $ take (n - 1) buf ++ drop n buf;

edFunction :: [String] -> IO ();
edFunction buf = getLine >>= detFun >>= edFunction
  where
  detFun cmd
    | length cmd == 0 = err
    | last cmd == 'p' = mapM_ (flip edPrintLine buf) k >> return buf
    | last cmd == 'n' = mapM_ (\m -> putStr (show m ++ "\t") >>
      edPrintLine m buf) k >> return buf
    | cmd == "i" = edInsert 1 buf
    | last cmd == 'p' = edPrintLine n buf
    | last cmd == 'i' = edInsert n buf
    | last cmd == 'a' = edInsert (n + 1) buf
    | head cmd == 'w' = edWrite buf $ unwords $ drop 1 $ words cmd
    | last cmd == 'd' = edDel n buf
    | last cmd == 'q' = exitSuccess
    | last cmd == 'c' = edDel n buf >>= edInsert n
    | otherwise = err
    where
    n = read $ init cmd
    k = genRange $ parseNums cmd buf
  err = putStrLn "?" >> return buf;
