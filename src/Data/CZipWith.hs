{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}

-- | A typeclass for an operation resembling 'zipWith' for types that are
-- parameterized over a constructor, plus template-haskell magic to
-- automatically derive instances.
--
-- @
-- zipWith  ::                          (g   -> h   -> i  ) -> [g] -> [h] -> [i]
-- cZipWith :: CZipWith k => (forall a . g a -> h a -> i a) -> k g -> k h -> k i
-- @
--
-- Types of the corresponding kind occur for example when handling program
-- configuration: When we define our an example configuration type like
--
-- @
-- data MyConfig f = MyConfig
--   { flag_foo       :: f Bool
--   , flag_bar       :: f Bool
--   , flag_someLimit :: f Int
--   }
-- @
--
-- then
--
-- * @MyConfig Maybe@ can be used as the result-type of parsing the
--   commandline or a configuration file; it includes the option that some
--   field was not specified;
-- * @MyConfig Identity@ can be used to represent both the default
--   configuration and the actual configuration derived from
--   defaults and the user input;
-- * @MyConfig (Const Text)@ type to represent documentation for our config,
--   to be displayed to the user.
--
-- This has the advantage that our configuration is defined in one place only,
-- so that changes are easy to make and we do not ever run into any internal
-- desynchonization of different datatypes. And once we obtained the final
-- config @:: MyConfig Identity@, we don't have to think about @Nothing@ cases
-- anymore.
--
-- The @'CZipWith'@ helps with this use-case, more specifically the merging of
-- input and default config: we can express the merging of user/default config
-- @:: MyConfig Maybe -> MyConfig Identity -> MyConfig Identity@ in terms of
-- @'cZipWith'@ (and get the implementation for free via 'deriveCZipWith').
--
-- As an example for such usage, the
-- <https://github.com/lspitzner/brittany brittany> package uses this approach
-- together with using automatically-derived Semigroup-instances that allow
-- merging of config values (for example when commandline args do not override,
-- but are added to those settings read from config file). See
-- <https://github.com/lspitzner/brittany/blob/master/src/Language/Haskell/Brittany/Config/Types.hs the module containing the config type>.
module Data.CZipWith
  ( CZipWith(..)
  , deriveCZipWith
  )
where



import Language.Haskell.TH.Lib
import Language.Haskell.TH.Syntax



-- | laws:
--
-- * @'cZipWith' (\\x _ -> x) g _ = g@
-- * @'cZipWith' (\\_ y -> y) _ h = h@
--
-- This class is morally related to the <https://hackage.haskell.org/package/distributive-0.5.2/docs/Data-Distributive.html#t:Distributive Distributive> class from the
-- <https://hackage.haskell.org/package/distributive distributive> package,
-- even when its method might not look similar to
-- those from @'Distributive'@. From the corresponding docs:
--
-- > To be distributable a container will need to have a way to consistently
-- > zip a potentially infinite number of copies of itself. This effectively
-- > means that the holes in all values of that type, must have the same
-- > cardinality, fixed sized vectors, infinite streams, functions, etc.
-- > and no extra information to try to merge together.
--
-- Especially "all values of that type must have the same cardinality" is
-- true for instances of CZipWith, the only difference being that the "holes"
-- are instantiations of the @f :: * -> *@ to some type, where they are simply
-- @a :: *@ for @'Distributive'@.
--
-- For many @'Distributive'@ instances there are corresponding datatypes that
-- are instances of @'CZipWith'@ (although they do not seem particularly
-- useful..), for example:
--
-- @
-- newtype CUnit a f = CUnit (f a)                -- corresponding to 'Identity'
-- data CPair a b f = CPair (f a) (f b)           -- corresponding to 'data MonoPair a = MonoPair a a'
--                                                -- (the trivial fixed-size vector example :)
-- data CStream a f = CStream (f a) (CStream a f) -- corresponding to an infinite stream
-- @
class CZipWith (k :: (* -> *) -> *) where
  -- | zipWith on constructors instead of values.
  cZipWith :: (forall a . g a -> h a -> i a) -> k g -> k h -> k i


(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip fmap

-- | Derives a 'CZipWith' instance for a datatype of kind @(* -> *) -> *@.
--
-- Requires that for this datatype (we shall call its argument @f :: * -> *@ here)
--
-- * there is exactly one constructor;
-- * all fields in the one constructor are either of the form @f x@ for some
--   @x@ or of the form @X f@ for some type @X@ where there is an
--   @instance CZipWith X@.
--
-- For example, the following would be valid usage:
--
-- @
-- data A f = A
--   { a_str  :: f String
--   , a_bool :: f Bool
--   }
--
-- data B f = B
--   { b_int   :: f Int
--   , b_float :: f Float
--   , b_a     :: A f
--   }
--
-- deriveCZipWith ''A
-- deriveCZipWith ''B
-- @
--
-- This produces the following instances:
--
-- @
-- instance CZipWith A where
--   cZipWith f (A x1 x2) (A y1 y2) = A (f x1 y1) (f x2 y2)
--
-- instance CZipWith B where
--   cZipWith f (B x1 x2 x3) (B y1 y2 y3)
--     = B (f x1 y1) (f x2 y2) (cZipWith f x3 y3)
-- @
deriveCZipWith :: Name -> DecsQ
deriveCZipWith name = do
  info <- reify name
  case info of
#if MIN_VERSION_template_haskell(2,11,0)
    TyConI (DataD _ _ [tyvarbnd] _ [con] []) -> do
#else
    TyConI (DataD _ _ [tyvarbnd] [con] []) -> do
#endif
      let (cons, elemTys) = case con of
            NormalC c tys -> (c, tys <&> \(_, t) -> t)
            RecC    c tys -> (c, tys <&> \(_, _, t) -> t)
            _ ->
              error
                $  "Deriving requires non-GADT, non-infix data type/record!"
                ++ " (Found: "
                ++ show con
                ++ ")"
      let tyvar = case tyvarbnd of
            PlainTV n    -> n
            KindedTV n _ -> n
      let fQ       = mkName "f"
      let indexTys = zip [1 ..] elemTys
      let indexTysVars = indexTys <&> \(i :: Int, ty) ->
            (ty, mkName $ "x" ++ show i, mkName $ "y" ++ show i)
      let dPat1     = conP cons $ indexTysVars <&> \(_, x, _) -> varP x
      let dPat2     = conP cons $ indexTysVars <&> \(_, _, x) -> varP x
      let pats      = [varP fQ, dPat1, dPat2]
      let
        params = indexTysVars <&> \(ty, x, y) -> case ty of
          AppT (VarT a1) _ | a1 == tyvar -> [|$(varE fQ) $(varE x) $(varE y)|]
          AppT ConT{} (VarT a2) | a2 == tyvar ->
            [|cZipWith $(varE fQ) $(varE x) $(varE y)|]
          _ ->
            error
              $ "All constructor arguments must have either type k a for some a or C k for some C (with instance CZip C)!"
              ++ " (Found: "
              ++ show ty
              ++ ")"
      let body = normalB $ appsE $ conE cons : params
      let funQ = funD 'cZipWith [clause pats body []]
      sequence [instanceD (cxt []) [t|CZipWith $(conT name)|] [funQ]]
    TyConI (DataD{}) ->
      error
        $  "datatype must have kind (* -> *) -> *!"
        ++ " (Found: "
        ++ show info
        ++ ")"
    _ ->
      error
        $  "name does not refer to a datatype!"
        ++ " (Found: "
        ++ show info
        ++ ")"

