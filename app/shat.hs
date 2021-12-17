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

-- | @parseNums n b@ is an 'Int'-based list of the line numbers which
-- are specified by the the ed(1)-compliant @n@.
parseNums :: String
          -- ^ The ed(1)-compliant range of line numbers
          -> [String]
          -- ^ The current text buffer
          -> [Int];
parseNums n b = haveFun $ map san $ splitOn "," n
  where
  haveFun ["",""] = [1,length b]
  haveFun ["",c] = [1,read c]
  haveFun [a,""] = [read a,length b]
  haveFun j = map read j
  san = filter (`elem` ['0'..'9']);

-- | If @k@ is a 2-list, then @genRange k == [k !! 0..k!! 1]@.
--
-- If @k@ is a 1-list, then @genRange == id@.
genRange :: [Int] -> [Int];
genRange [a,b] = [a..b];

-- | @insertAt n i xs@ is a version of @xs@ which is modified such that
-- the elements of @i@ immediately precede the @n@th element of @xs@,
-- where lists are 1-indexed.
insertAt :: Int
         -- ^ The index
         -> [a]
         -- ^ The list which is inserted into the other list
         -> [a]
         -- ^ The list into which the other list is inserted
         -> [a];
insertAt n x xs = take g xs ++ x ++ drop g xs
  where g = n - 1;

-- | @edPrintLine n buffer@ prints the @n@th line of the @buffer@,
-- returning @buffer@.
--
-- Lines are 1-indexed.
edPrintLine :: Int
            -- ^ The index of the line which is written to the
            -- standard output
            -> [String]
            -- ^ The buffer
            -> IO [String];
edPrintLine n buf = (putStrLn $ buf !! (n - 1)) >> return buf;

-- | @edInsert n buffer@ inserts some lines which are read from the
-- standard input immediately before the @n@th line of @buffer@,
-- returning the resulting buffer.
--
-- Lines are 1-indexed.
edInsert n buf = isEOF >>= \ a ->
  if a
    then return buf
    else getLine >>= \ x -> edInsert (n + 1) $ insertAt n [x] buf;

-- | @edWrite buffer finename@ writes the @buffer@ to the file whose
-- path is @finename@.  The name of the fille need not be fine.
edWrite :: [String]
        -- ^ The buffer
        -> String
        -- ^ The file path
        -> IO [String];
edWrite buf fn = writeFile fn conkd >> return buf
  where conkd = foldr (++) [] $ intersperse "\n" buf;

-- | @edDel n buffer@ is a @buffer@ which lacks line @n@, where lines
-- are 1-indexed.
edDel :: Int
      -- ^ The index of the line which is removed
      -> [String]
      -- ^ The buffer from which a line is removed
      -> IO [String];
edDel n buf = return $ take (n - 1) buf ++ drop n buf;

-- | @edFunction@ is the "meat and potatoes" of @shat@.
--
-- @edFunction buffer@ reads a command from the standard input and
-- operates on the @buffer@.
edFunction :: [String]
           -- ^ The buffer
           -> IO ();
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
