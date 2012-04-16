-- Trie, in a kind of 'python eye for the haskell guy' way
module Trie where

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe

data Trie a = Trie { children :: Map a (Trie a)
                   , present  :: Bool }

empty :: Ord a => Trie a
empty = Trie { children = M.empty, present = False }

only :: Ord a => [a] -> Trie a
only word = insert word empty

insert :: Ord a => [a] -> Trie a -> Trie a
insert []          trie = trie { present = True }
insert (char:rest) trie =
    case M.lookup char (children trie) of
        Nothing -> trie { children = M.insert char (only rest) (children trie) }
        Just child -> trie { children = M.insert char (insert rest child) (children trie) }

find :: Ord a => [a] -> Trie a -> Bool
find []          trie = present trie
find (char:rest) trie = fromMaybe False $ do
  child <- M.lookup char (children trie)
  return (find rest child)

complete :: Ord a => [a] -> Trie a -> [[a]]
complete []          trie =
    let here  = if present trie then [[]] else []
        there = do
            (char, child) <- M.toList (children trie)
            item <- complete [] child
            return (char:item)
    in here ++ there
complete (char:rest) trie = do
    child <- maybeToList (M.lookup char (children trie))
    item <- complete rest child
    return (char:item)
