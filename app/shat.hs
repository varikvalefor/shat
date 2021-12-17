import Control.Monad;
import System.Exit;
import System.Directory;
import System.Environment;
import System.IO;
import Data.List;
import Text.Read;
import Data.Maybe;
import Data.List.Split;

-- | The main 'EdData' variable contains the buffer and the current line
-- of the program.
data EdData = EdData {
  -- | Where @k@ is the "main" 'EdData' variable of the program,
  -- @currentLine k@ is the current line.
  currentLine :: Int,
  -- | Where @k@ is the "main" 'EdData' variable of the program,
  -- @stk k@ is the text buffer.
  --
  -- "@stk@" is derived from "beef", which is derived from "buffer".
  stk :: [String]
};

main :: IO ();
main = getArgs >>= \a ->
  if a == []
    then edFunction $ wBuf []
    else readFile (a !! 0) >>= edFunction . wBuf . lines
  where wBuf beefer = EdData {currentLine = 1, stk = beefer};

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
genRange [a] = [a];

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

-- | @edPrintLine n eddy@ prints the @n@th line of the buffer of @eddy@,
-- returning the resulting @eddy@.
--
-- Lines are 1-indexed.
edPrintLine :: Int
            -- ^ The index of the line which is written to the
            -- standard output
            -> EdData
            -- ^ The program's main text thing
            -> IO EdData;
edPrintLine n e = (putStrLn $ stk e !! (n - 1)) >> return e;

-- | @edInsert n eddy@ inserts some lines which are read from the
-- standard input immediately before the @n@th line of the buffer of
-- @eddy@, returning the resulting @eddy@.
--
-- Lines are 1-indexed.
edInsert :: Int
         -- ^ The index of the line which follows the inserted stuff
         -> EdData
         -> IO EdData;
edInsert n e =
  isEOF >>= \ a -> if a
    then return e
    else getLine >>= \ x ->
      if x == "."
        then return e
        else edInsert (n + 1) $ e {stk = insertAt n [x] (stk e)};

-- | @edWrite ed finename@ writes the buffer of @ed@ to the file whose
-- path is @finename@.  The name of the file need not be fine.
edWrite :: EdData
        -- ^ The buffer
        -> String
        -- ^ The file path
        -> IO EdData;
edWrite e fn = writeFile fn ((++ "\n") $ unlines $ stk e) >> return e;

-- | @edDel n dt@ is a @dt@ whose buffer lacks line @n@, where lines
-- are 1-indexed.
edDel :: Int
      -- ^ The index of the line which is removed
      -> EdData
      -- ^ The buffer from which a line is removed
      -> IO EdData;
edDel n e = return e {stk = take (n - 1) (stk e) ++ drop n (stk e)};

-- | @edFunction@ is the "meat and potatoes" of @shat@.
--
-- @edFunction ed@ reads a command from the standard input and
-- operates on the @ed@.
edFunction :: EdData
           -- ^ The buffer
           -> IO ();
edFunction eddy = getLine >>= detFun >>= edFunction
  where
  detFun cmd
    | cmd == [] = err
    | last cmd == 'p' = mapM_ (`edPrintLine` m) k >> return eddy
    | last cmd == 'n' = mapM_ (\m -> putStr (show m ++ "\t") >>
      edPrintLine m eddy) k >> return eddy
    | last cmd == 'p' = edPrintLine n eddy
    | last cmd == 'i' = edInsert n eddy
    | last cmd == 'a' = edInsert (n + 1) eddy
    | head cmd == 'w' = edWrite (eddy) $ drop 2 cmd
    | last cmd == 'd' = edDel n eddy
    | last cmd == 'q' = exitSuccess
    | last cmd == 'c' = edDel n eddy >>= edInsert n
    | isJust $ (readMaybe cmd :: Maybe Int) =
      return eddy {currentLine = read cmd}
    | otherwise = err
    where
    -- \| @n@ is the number of the line to which monargumental
    -- commands are applied.
    n | not $ head cmd `elem` ['a'..'z'] = read $ init cmd :: Int
        -- \^ Parsing commands as numbers is a pretty stupid
        -- idea.  As such, commands are not parsed as numbers.
      | otherwise = currentLine eddy
    -- \| @n@ is the range of line numbers to which variadic commands
    -- -- are applied.
    k = genRange $ parseNums cmd $ stk eddy
  err = putStrLn "?" >> return eddy;
