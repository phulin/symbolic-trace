{-# LANGUAGE FlexibleContexts #-}
module AppList(AppList, mkAppList, singleAppList, unAppList, (+:), suffix) where

newtype AppList a = MkAppList [a]
    deriving (Eq, Ord)

instance Show a => Show (AppList a) where
    show (MkAppList l) = "AppList " ++ show (reverse l)

(+:) :: AppList a -> a -> AppList a
MkAppList l +: x = MkAppList (x : l)
infixr 5 +:

mkAppList :: AppList a
mkAppList = MkAppList []

singleAppList :: a -> AppList a
singleAppList x = MkAppList [x]

unAppList :: AppList a -> [a]
unAppList (MkAppList l) = reverse l

suffix :: Int -> AppList a -> [a]
suffix n (MkAppList l) = reverse $ take n l
