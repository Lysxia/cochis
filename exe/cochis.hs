import Control.Monad.Fail
import Data.Foldable
import Prelude hiding (fail)

import Cochis
import Cochis.Parser
import Cochis.Printer
import Cochis.Utils

main = do
  s <- readFile "examples/basic.hs"
  xs <- unwrap (parseMod s)
  putStrLn (printMod xs)
  for_ xs $ \(name, e) -> do
    putStrLn (prettyPrint name)
    case typeCheck0 e of
      Left e -> print e
      Right t -> putStrLn (prettyPrint (runFreshM (toType t)))

unwrap :: (Show e, MonadFail m) => Either e a -> m a
unwrap (Left e) = fail (show e)
unwrap (Right a) = return a
