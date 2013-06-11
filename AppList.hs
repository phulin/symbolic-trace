module AppList(AppList, mkAppList, unAppList, (+:)) where

newtype AppList a = MkAppList [a]

(+:) :: AppList a -> a -> AppList a
MkAppList l +: x = MkAppList (x : l)

mkAppList :: AppList a
mkAppList = MkAppList []

unAppList :: AppList a -> [a]
unAppList (MkAppList l) = reverse l
