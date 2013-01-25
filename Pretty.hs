module Pretty where

class Pretty a where
    pretty :: a -> String
