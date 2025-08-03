module Optically where

import Data.Function ((&))
import Data.Functor.Compose (Compose (..))
import Data.Functor.Const (Const (..))
import Data.Functor.Day (Day (..))
import Data.Functor.Day qualified as Day
import Data.Functor.Identity (Identity (..))
import Data.Functor.Product (Product (..))
import Data.Functor.Sum (Sum (..))
import Data.Kind
import Data.Proxy (Proxy (..))
import Data.Void (absurd)

--- Cat, ProCat, etc {{{

type f ~> g = forall i. f i -> g i

newtype f :~> g = Nt {(*$) :: f ~> g}

(*&) :: f i -> (f :~> g) -> g i
(*&) x f = f *$ x
{-# INLINE (*&) #-}

infixr 8 *&

type (:->) :: forall j. j -> j -> Type
type family (:->) @j where
  (:->) @Type = (->)
  (:->) @(j -> Type) = (:~>)

class Vacuous t

instance Vacuous t

class Cat k where
  identity :: k x x
  (<<<) :: k a b -> k x a -> k x b

instance Cat (->) where
  identity = id
  (<<<) = (.)

instance Cat (:~>) where
  identity = Nt identity
  Nt l <<< Nt r = Nt (l <<< r)

type ProCat :: forall j. (j -> j -> j -> j -> Type) -> Constraint
class ProCat k where
  type ProObj k :: j -> Constraint
  type ProObj k = Vacuous
  proidentity :: (ProObj k a, ProObj k b) => k a b a b
  (<<<<) :: k a b s t -> k x y a b -> k x y s t

--- }}}

---

type Viewer :: forall obj. obj -> obj -> obj -> obj -> Type
newtype Viewer a b s t = Viewer {runViewer :: s :-> a}

type Like :: forall obj. obj -> obj -> obj -> obj -> Type
data Like a b s t = Like !(s :-> a) !(b :-> t)

data Tensored tensor proarr a b s t
  = forall e. Tensored !(proarr (tensor e a) (tensor e b) s t)

type data Direction = RTL | LTR

type ReverseDirection :: Direction -> Direction
type family ReverseDirection dir where
  ReverseDirection RTL = LTR
  ReverseDirection LTR = RTL

data Glass dir proarr a b s t where
  Window :: !(proarr a b s t) -> Glass RTL proarr a b s t
  Mirror :: !(proarr t s b a) -> Glass LTR proarr a b s t

class Reversible input output | input -> output, output -> input where
  reversed :: input a b s t -> output t s b a

instance Reversible Like Like where
  reversed (Like sa bt) = Like bt sa
  {-# INLINE reversed #-}

instance (m ~ ReverseDirection w, ReverseDirection m ~ w) => Reversible (Glass m k) (Glass w k) where
  reversed (Window k) = Mirror k
  reversed (Mirror k) = Window k
  {-# INLINE reversed #-}

---

type Super ::
  forall i j.
  (i -> j -> Constraint) ->
  (i -> j -> Constraint)
type family Super c k p

type Optical p a b s t = p a b -> p s t

type Optically ::
  forall i.
  (i -> i -> i -> i -> Type) ->
  (i -> i -> Type) ->
  Constraint
class (Super Optically proarr p) => Optically proarr p where
  optically :: proarr a b s t -> Optical p a b s t

---

data Walk container index = (Traversable container) => Walk {getWalk :: container index}

deriving stock instance Functor (Walk container)

deriving stock instance Foldable (Walk container)

deriving stock instance Traversable (Walk container)

--- Shapes {{{

type TupleShaped = Tensored (,) Like

type EitherShaped = Tensored Either Like

type DomShaped = Tensored (->) Like

type WalkShaped = Tensored Walk Like

type DayShaped = Tensored Day Like

type ProductShaped = Tensored Product Like

--- }}}

--- Optic likes {{{

type IsoLike = Glass RTL Like

type OsiLike = Glass LTR Like

type ViewLike = Glass RTL Viewer

type ReviewLike = Glass LTR Viewer

type LensLike = Glass RTL TupleShaped

type ColensLike = Glass LTR TupleShaped

type PrismLike = Glass RTL EitherShaped

type CoprismLike = Glass LTR EitherShaped

type GrateLike = Glass RTL DomShaped

type CograteLike = Glass LTR DomShaped

type TraversalLike = Glass RTL WalkShaped

type CotraversalLike = Glass LTR WalkShaped

type SummerLike = Glass RTL DayShaped

type CosummerLike = Glass LTR DayShaped

type Lens1Like = Glass RTL ProductShaped

type Colens1Like = Glass LTR ProductShaped

--- }}}

--- Super instances {{{

type instance Super (Optically @j) Viewer p = ()

type instance Super (Optically @j) Like p = ()

type instance Super (Optically @j) IsoLike p = ()

type instance Super (Optically @j) OsiLike p = ()

type instance Super (Optically @Type) LensLike p = Optically IsoLike p

type instance Super (Optically @Type) ColensLike p = Optically OsiLike p

type instance Super (Optically @Type) PrismLike p = Optically IsoLike p

type instance Super (Optically @Type) CoprismLike p = Optically OsiLike p

type instance Super (Optically @Type) GrateLike p = Optically IsoLike p

type instance Super (Optically @Type) CograteLike p = Optically OsiLike p

type instance Super (Optically @Type) TraversalLike p = (Optically LensLike p, Optically PrismLike p)

type instance Super (Optically @Type) CotraversalLike p = (Optically ColensLike p, Optically CoprismLike p)

type instance Super (Optically @Type) ViewLike p = (Optically CoprismLike p, Optically LensLike p)

type instance Super (Optically @(j -> Type)) ViewLike p = Optically IsoLike p

type instance Super (Optically @Type) ReviewLike p = (Optically PrismLike p, Optically ColensLike p)

type instance Super (Optically @(j -> Type)) ReviewLike p = Optically OsiLike p

type instance Super (Optically @(Type -> Type)) SummerLike p = Optically IsoLike p

type instance Super (Optically @(Type -> Type)) CosummerLike p = Optically OsiLike p

type instance Super (Optically @(j -> Type)) Lens1Like p = Optically IsoLike p

--- }}}

---

type EachHas ::
  (a -> b -> Constraint) ->
  ([a] -> b -> Constraint)
type family EachHas c ks p where
  EachHas c '[] p = ()
  EachHas c (k ': ks) p = (c k p, EachHas c ks p)

type Optics proarrs a b s t = forall p. (EachHas Optically proarrs p) => Optical p a b s t

type Optic proarr a b s t = forall p. (Optically proarr p) => Optical p a b s t

---

type Iso a b s t = Optic IsoLike a b s t

type Osi a b s t = Optic OsiLike a b s t

type View a b s t = Optic ViewLike a b s t

type Review a b s t = Optic ReviewLike a b s t

type Lens a b s t = Optic LensLike a b s t

type Colens a b s t = Optic ColensLike a b s t

type Lens1 a b s t = Optic Lens1Like a b s t

type Colens1 a b s t = Optic Colens1Like a b s t

type Prism a b s t = Optic PrismLike a b s t

type Coprism a b s t = Optic CoprismLike a b s t

type Grate a b s t = Optic GrateLike a b s t

type Cograte a b s t = Optic CograteLike a b s t

type AffineTraversal a b s t = Optics '[LensLike, PrismLike] a b s t

type Traversal a b s t = Optic TraversalLike a b s t

type Cotraversal a b s t = Optic CotraversalLike a b s t

type Summer a b s t = Optic SummerLike a b s t

type Cosummer a b s t = Optic CosummerLike a b s t

--- Simple {{{

type Iso' a s = Iso a a s s

type Osi' a s = Osi a a s s

type View' a s = View a a s s

type Review' a s = Review a a s s

type Lens' a s = Lens a a s s

type Colens' a s = Colens a a s s

type Lens1' a s = Lens1 a a s s

type Colens1' a s = Colens1 a a s s

type Prism' a s = Prism a a s s

type Coprism' a s = Coprism a a s s

type Grate' a s = Grate a a s s

type Cograte' a s = Cograte a a s s

type Traversal' a s = Traversal a a s s

type Cotraversal' a s = Cotraversal a a s s

type Summer' a s = Summer a a s s

type Cosummer' a s = Cosummer a a s s

type AffineTraversal' a s = AffineTraversal a a s s

--- }}}

--- ProCat instances {{{

instance (Cat ((:->) @k)) => ProCat @k Like where
  proidentity = Like identity identity
  {-# INLINE proidentity #-}

  (<<<<) (Like sa bt) (Like ax yb) = Like (ax <<< sa) (bt <<< yb)
  {-# INLINE (<<<<) #-}

instance (Cat ((:->) @k)) => ProCat @k IsoLike where
  proidentity = Window proidentity
  {-# INLINE proidentity #-}

  Window abst <<<< Window xyab = Window (abst <<<< xyab)
  {-# INLINE (<<<<) #-}

instance (Cat ((:->) @k)) => ProCat @k OsiLike where
  proidentity = Mirror proidentity
  {-# INLINE proidentity #-}

  Mirror tsba <<<< Mirror bayx = Mirror (bayx <<<< tsba)
  {-# INLINE (<<<<) #-}

instance (Cat ((:->) @k)) => ProCat @k Viewer where
  proidentity = Viewer identity
  {-# INLINE proidentity #-}

  Viewer sa <<<< Viewer ar = Viewer (ar <<< sa)
  {-# INLINE (<<<<) #-}

instance (Cat ((:->) @k)) => ProCat @k ViewLike where
  proidentity = Window (Viewer identity)
  {-# INLINE proidentity #-}

  Window (Viewer sa) <<<< Window (Viewer ar) =
    Window (Viewer (ar <<< sa))
  {-# INLINE (<<<<) #-}

instance (Cat ((:->) @k)) => ProCat @k ReviewLike where
  proidentity = Mirror (Viewer identity)
  {-# INLINE proidentity #-}

  Mirror (Viewer ar) <<<< Mirror (Viewer sa) =
    Mirror (Viewer (ar <<< sa))
  {-# INLINE (<<<<) #-}

instance ProCat LensLike where
  proidentity = Window (Tensored (Like ((),) snd))
  {-# INLINE proidentity #-}

  Window (Tensored (Like sea ebt)) <<<< Window (Tensored (Like afx fyb)) =
    Window . Tensored $ Like (assocl . fmap afx . sea) (ebt . fmap fyb . assocr)
    where
      assocl (e, (f, x)) = ((e, f), x)
      assocr ((e, f), x) = (e, (f, x))
  {-# INLINE (<<<<) #-}

instance ProCat ColensLike where
  proidentity = reversed proidentity
  {-# INLINE proidentity #-}

  l <<<< r = reversed $ reversed r <<<< reversed l
  {-# INLINE (<<<<) #-}

instance ProCat PrismLike where
  proidentity = Window (Tensored (Like Right (either absurd id)))
  {-# INLINE proidentity #-}

  Window (Tensored (Like sea ebt)) <<<< Window (Tensored (Like afx fyb)) =
    Window . Tensored $
      Like
        (assocl . fmap afx . sea)
        (ebt . fmap fyb . assocr)
    where
      assocl = either (Left . Left) (either (Left . Right) Right)
      assocr = either (fmap Left) (Right . Right)
  {-# INLINE (<<<<) #-}

instance ProCat CoprismLike where
  proidentity = reversed proidentity
  {-# INLINE proidentity #-}

  l <<<< r = reversed $ reversed r <<<< reversed l
  {-# INLINE (<<<<) #-}

instance ProCat GrateLike where
  proidentity = Window (Tensored (Like const ($ ())))
  {-# INLINE proidentity #-}

  Window (Tensored (Like sea ebt)) <<<< Window (Tensored (Like afx fyb)) =
    Window . Tensored $
      Like
        ((\ea (e, f) -> afx (ea e) f) . sea)
        (\efy -> ebt \e -> fyb \f -> efy (e, f))
  {-# INLINE (<<<<) #-}

instance ProCat CograteLike where
  proidentity = reversed proidentity
  {-# INLINE proidentity #-}

  l <<<< r = reversed $ reversed r <<<< reversed l
  {-# INLINE (<<<<) #-}

instance ProCat TraversalLike where
  proidentity = Window (Tensored (Like (Walk . Identity) (runIdentity . getWalk)))
  {-# INLINE proidentity #-}

  Window (Tensored (Like sea ebt)) <<<< Window (Tensored (Like afx fyb)) =
    Window . Tensored $
      Like
        (Walk . Compose . fmap afx . sea)
        (ebt . fmap fyb . getCompose . getWalk)
  {-# INLINE (<<<<) #-}

instance ProCat CotraversalLike where
  proidentity = reversed proidentity
  {-# INLINE proidentity #-}

  l <<<< r = reversed $ reversed r <<<< reversed l
  {-# INLINE (<<<<) #-}

instance ProCat SummerLike where
  type ProObj SummerLike = Functor
  proidentity =
    Window . Tensored $
      Like
        (Nt \a -> Day (Identity ()) a (const id))
        (Nt \(Day (Identity unit) g h) -> h unit <$> g)
  {-# INLINE proidentity #-}

  Window (Tensored (Like sea ebt)) <<<< Window (Tensored (Like afx fyb)) =
    Window . Tensored $
      Like
        (Nt Day.assoc <<< Nt (Day.trans2 (afx *$)) <<< sea)
        (ebt <<< Nt (Day.trans2 (fyb *$)) <<< Nt Day.disassoc)
  {-# INLINE (<<<<) #-}

instance ProCat CosummerLike where
  type ProObj CosummerLike = Functor
  proidentity = reversed proidentity
  {-# INLINE proidentity #-}

  l <<<< r = reversed $ reversed r <<<< reversed l
  {-# INLINE (<<<<) #-}

instance ProCat Lens1Like where
  proidentity = Window (Tensored (Like (Nt (Pair Proxy)) (Nt \(Pair Proxy t) -> t)))
  {-# INLINE proidentity #-}

  Window (Tensored (Like sea ebt)) <<<< Window (Tensored (Like afx fyb)) =
    Window . Tensored $
      Like
        (assocl <<< mapProduct afx <<< sea)
        (ebt <<< mapProduct fyb <<< assocr)
    where
      mapProduct :: (x :~> y) -> (Product e x :~> Product e y)
      mapProduct g = Nt \(Pair e x) -> Pair e (g *$ x)
      assocl = Nt \(Pair e (Pair f x)) -> Pair (Pair e f) x
      assocr = Nt \(Pair (Pair e f) x) -> Pair e (Pair f x)
  {-# INLINE (<<<<) #-}

instance ProCat Colens1Like where
  proidentity = reversed proidentity
  {-# INLINE proidentity #-}

  l <<<< r = reversed $ reversed r <<<< reversed l
  {-# INLINE (<<<<) #-}

--- }}}

instance (Cat ((:->) @j)) => Optically @j IsoLike (ViewLike x y) where
  optically (Window (Like sa _bt)) (Window (Viewer ar)) =
    Window (Viewer (ar <<< sa))
  {-# INLINE optically #-}

instance (Cat ((:->) @j)) => Optically @j OsiLike (ViewLike x y) where
  optically (Mirror (Like _bt sa)) (Window (Viewer ar)) =
    Window (Viewer (ar <<< sa))
  {-# INLINE optically #-}

instance Optically LensLike (ViewLike x y) where
  optically (Window (Tensored (Like sea _ebt))) (Window (Viewer ar)) =
    Window (Viewer (ar <<< snd <<< sea))
  {-# INLINE optically #-}

instance Optically CoprismLike (ViewLike x y) where
  optically (Mirror (Tensored (Like _bet esa))) (Window (Viewer ax)) =
    Window (Viewer (ax . esa . Right))
  {-# INLINE optically #-}

instance (Cat ((:->) @j)) => Optically @j IsoLike (ReviewLike x y) where
  optically (Window (Like _sa bt)) (Mirror (Viewer ar)) =
    Mirror (Viewer (bt <<< ar))
  {-# INLINE optically #-}

instance (Cat ((:->) @j)) => Optically @j OsiLike (ReviewLike x y) where
  optically (Mirror (Like bt _sa)) (Mirror (Viewer ar)) =
    Mirror (Viewer (bt <<< ar))
  {-# INLINE optically #-}

instance Optically ColensLike (ReviewLike x y) where
  optically (Mirror (Tensored (Like sea _ebt))) (Mirror (Viewer ar)) =
    Mirror (Viewer (snd . sea . ar))
  {-# INLINE optically #-}

instance Optically PrismLike (ReviewLike x y) where
  optically (Window (Tensored (Like _sea ebt))) (Mirror (Viewer yb)) =
    Mirror (Viewer (ebt . Right . yb))
  {-# INLINE optically #-}

instance Optically IsoLike (LensLike x y) where
  optically (Window (Like sa bt)) (Window (Tensored (Like aex eyb))) =
    Window (Tensored (Like (aex . sa) (bt . eyb)))
  {-# INLINE optically #-}

instance Optically OsiLike (ColensLike x y) where
  optically (Mirror (Like bt sa)) (Mirror (Tensored (Like yeb eax))) =
    Mirror (Tensored (Like (fmap bt . yeb) (eax . fmap sa)))
  {-# INLINE optically #-}

instance Optically IsoLike (PrismLike x y) where
  optically (Window (Like sa bt)) (Window (Tensored (Like aex eyb))) =
    Window (Tensored (Like (aex . sa) (bt . eyb)))
  {-# INLINE optically #-}

instance Optically OsiLike (CoprismLike x y) where
  optically (Mirror (Like bt sa)) (Mirror (Tensored (Like yeb eax))) =
    Mirror (Tensored (Like (fmap bt . yeb) (eax . fmap sa)))
  {-# INLINE optically #-}

instance Optically IsoLike (GrateLike x y) where
  optically (Window (Like sa bt)) (Window (Tensored (Like aex eyb))) =
    Window (Tensored (Like (aex . sa) (bt . eyb)))
  {-# INLINE optically #-}

instance Optically OsiLike (CograteLike x y) where
  optically (Mirror (Like bt sa)) (Mirror (Tensored (Like yeb eax))) =
    Mirror (Tensored (Like (fmap bt . yeb) (eax . fmap sa)))
  {-# INLINE optically #-}

instance Optically IsoLike (TraversalLike x y) where
  optically (Window (Like sa bt)) (Window (Tensored (Like sea ebt))) =
    Window . Tensored $ Like (sea . sa) (bt . ebt)
  {-# INLINE optically #-}

instance Optically OsiLike (TraversalLike x y) where
  optically (Mirror (Like bt sa)) (Window (Tensored (Like sea ebt))) =
    Window . Tensored $ Like (sea . sa) (bt . ebt)
  {-# INLINE optically #-}

instance Optically LensLike (TraversalLike x y) where
  optically (Window (Tensored (Like sea ebt))) (Window (Tensored (Like ayx fyb))) =
    Window . Tensored $
      Like
        (\s -> Walk (Pair (Const s) (ayx (snd (sea s)))))
        (ebt . \(Walk (Pair (Const s) ey)) -> (fst (sea s), fyb ey))
  {-# INLINE optically #-}

instance Optically PrismLike (TraversalLike x y) where
  optically (Window (Tensored (Like sea ebt))) (Window (Tensored (Like ayx fyb))) =
    Window . Tensored $
      Like
        (Walk . either (InL . Const) (InR . ayx) . sea)
        (ebt . onSum (Left . getConst) (Right . fyb) . getWalk)
    where
      onSum f _ (InL x) = f x
      onSum _ g (InR x) = g x
  {-# INLINE optically #-}

instance Optically IsoLike (CotraversalLike x y) where
  optically (Window (Like sa bt)) (Mirror (Tensored (Like eyb aex))) =
    Mirror (Tensored (Like (fmap bt . eyb) (aex . fmap sa)))
  {-# INLINE optically #-}

instance Optically OsiLike (CotraversalLike x y) where
  optically (Mirror (Like bt sa)) (Mirror (Tensored (Like yeb eax))) =
    Mirror (Tensored (Like (fmap bt . yeb) (eax . fmap sa)))
  {-# INLINE optically #-}

instance Optically ColensLike (CotraversalLike x y) where
  optically (Mirror (Tensored (Like bet esa))) (Mirror (Tensored (Like yfb fax))) =
    Mirror . Tensored $
      Like
        (Walk . Compose . fmap bet . yfb)
        (fax . fmap esa . getCompose . getWalk)
  {-# INLINE optically #-}

instance Optically CoprismLike (CotraversalLike x y) where
  optically (Mirror (Tensored (Like bet esa))) (Mirror (Tensored (Like yfb fax))) =
    Mirror . Tensored $
      Like
        (Walk . Compose . fmap bet . yfb)
        (fax . fmap esa . getCompose . getWalk)
  {-# INLINE optically #-}

instance Optically IsoLike (SummerLike x y) where
  optically (Window l) (Window (Tensored r)) = Window (Tensored (l <<<< r))
  {-# INLINE optically #-}

instance Optically OsiLike (CosummerLike x y) where
  optically (Mirror (Like bt sa)) (Mirror (Tensored (Like yeb eax))) =
    Mirror (Tensored (Like (Nt (Day.trans2 (bt *$)) <<< yeb) (eax <<< Nt (Day.trans2 (sa *$)))))
  {-# INLINE optically #-}

instance Optically IsoLike (Lens1Like x y) where
  optically (Window (Like sa bt)) (Window (Tensored (Like aex eyb))) =
    Window (Tensored (Like (aex <<< sa) (bt <<< eyb)))
  {-# INLINE optically #-}

--- Hom functors {{{

instance (Cat ((:->) @j)) => Optically @j Like (Like x y) where
  optically = (<<<<)
  {-# INLINE optically #-}

instance (Cat ((:->) @j)) => Optically @j Viewer (Viewer r x) where
  optically = (<<<<)
  {-# INLINE optically #-}

instance (Cat ((:->) @j)) => Optically @j IsoLike (IsoLike x y) where
  optically = (<<<<)
  {-# INLINE optically #-}

instance (Cat ((:->) @j)) => Optically @j OsiLike (OsiLike x y) where
  optically = (<<<<)
  {-# INLINE optically #-}

instance Optically @Type ViewLike (ViewLike x y) where
  optically = (<<<<)
  {-# INLINE optically #-}

instance (Cat ((:->) @(j -> Type))) => Optically @(j -> Type) ViewLike (ViewLike x y) where
  optically = (<<<<)
  {-# INLINE optically #-}

instance Optically @Type ReviewLike (ReviewLike x y) where
  optically = (<<<<)
  {-# INLINE optically #-}

instance (Cat ((:->) @(j -> Type))) => Optically @(j -> Type) ReviewLike (ReviewLike x y) where
  optically = (<<<<)
  {-# INLINE optically #-}

instance Optically LensLike (LensLike x y) where
  optically = (<<<<)
  {-# INLINE optically #-}

instance Optically ColensLike (ColensLike x y) where
  optically = (<<<<)
  {-# INLINE optically #-}

instance Optically PrismLike (PrismLike x y) where
  optically = (<<<<)
  {-# INLINE optically #-}

instance Optically CoprismLike (CoprismLike x y) where
  optically = (<<<<)
  {-# INLINE optically #-}

instance Optically GrateLike (GrateLike x y) where
  optically = (<<<<)
  {-# INLINE optically #-}

instance Optically CograteLike (CograteLike x y) where
  optically = (<<<<)
  {-# INLINE optically #-}

instance Optically TraversalLike (TraversalLike x y) where
  optically = (<<<<)
  {-# INLINE optically #-}

instance Optically CotraversalLike (CotraversalLike x y) where
  optically = (<<<<)
  {-# INLINE optically #-}

instance Optically SummerLike (SummerLike x y) where
  optically = (<<<<)
  {-# INLINE optically #-}

instance Optically CosummerLike (CosummerLike x y) where
  optically = (<<<<)
  {-# INLINE optically #-}

instance Optically Lens1Like (Lens1Like x y) where
  optically = (<<<<)
  {-# INLINE optically #-}

--- }}}

newtype Re p a b s t = Re {getRe :: p t s -> p b a}

instance
  ( Reversible m w,
    Optically w p,
    Super Optically m (Re p x y)
  ) =>
  Optically m (Re p x y)
  where
  optically d (Re q) = Re (q <<< optically (reversed d))
  {-# INLINE optically #-}

re :: Optical (Re p a b) a b s t -> Optical p t s b a
re o = getRe (o (Re id))
{-# INLINE re #-}

--- Constructors {{{

windowAppLike ::
  (s :-> o e a) ->
  (o e b :-> t) ->
  Optic (Glass RTL (Tensored o Like)) a b s t
windowAppLike sea ebt = optically (Window (Tensored (Like sea ebt)))
{-# INLINE windowAppLike #-}

mirrorAppLike ::
  (b :-> o e t) ->
  (o e s :-> a) ->
  Optic (Glass LTR (Tensored o Like)) a b s t
mirrorAppLike bet esa = optically (Mirror (Tensored (Like bet esa)))
{-# INLINE mirrorAppLike #-}

view :: (s :-> a) -> View a b s t
view sa = optically (Window (Viewer sa))
{-# INLINE view #-}

review :: (b :-> t) -> Review a b s t
review bt = optically (Mirror (Viewer bt))
{-# INLINE review #-}

iso :: (s :-> a) -> (b :-> t) -> Iso a b s t
iso sa bt = optically (Window (Like sa bt))
{-# INLINE iso #-}

lens :: (s :-> (e, a)) -> ((e, b) :-> t) -> Lens a b s t
lens = windowAppLike
{-# INLINE lens #-}

colens :: (b :-> (e, t)) -> ((e, s) :-> a) -> Colens a b s t
colens = mirrorAppLike
{-# INLINE colens #-}

prism :: (s :-> Either e a) -> (Either e b :-> t) -> Prism a b s t
prism = windowAppLike
{-# INLINE prism #-}

coprism :: (b :-> Either e t) -> (Either e s :-> a) -> Coprism a b s t
coprism = mirrorAppLike
{-# INLINE coprism #-}

grate :: (s :-> (e -> a)) -> ((e -> b) :-> t) -> Grate a b s t
grate = windowAppLike
{-# INLINE grate #-}

cograte :: (b :-> (e -> t)) -> ((e -> s) :-> a) -> Cograte a b s t
cograte = mirrorAppLike
{-# INLINE cograte #-}

traversal :: (Traversable e) => (s :-> e a) -> (e b :-> t) -> Traversal a b s t
traversal sea ebt = windowAppLike (Walk . sea) (ebt . getWalk)
{-# INLINE traversal #-}

summer :: (s :-> Day e a) -> (Day e b :-> t) -> Summer a b s t
summer = windowAppLike
{-# INLINE summer #-}

cosummer :: (b :-> Day e t) -> (Day e s :-> a) -> Cosummer a b s t
cosummer = mirrorAppLike
{-# INLINE cosummer #-}

lens1 :: (s :-> Product e a) -> (Product e b :-> t) -> Lens1 a b s t
lens1 = windowAppLike
{-# INLINE lens1 #-}

--- }}}

instance Optically IsoLike (->) where
  optically (Window (Like sa bt)) ab = bt <<< ab <<< sa
  {-# INLINE optically #-}

instance Optically OsiLike (->) where
  optically (Mirror (Like bt sa)) ab = bt <<< ab <<< sa
  {-# INLINE optically #-}

instance
  ( forall t. Functor (o t),
    Optically (Glass RTL k) (->),
    Super Optically (Glass RTL (Tensored o k)) (->)
  ) =>
  Optically (Glass RTL (Tensored o k)) (->)
  where
  optically (Window (Tensored k)) = optically (Window k) . fmap
  {-# INLINE optically #-}

(%~) :: Optical (:->) a b s t -> (a :-> b) -> s :-> t
(%~) = identity
{-# INLINE (%~) #-}

instance Optically IsoLike (:~>) where
  optically (Window (Like sa bt)) ab = bt <<< ab <<< sa
  {-# INLINE optically #-}

instance Optically OsiLike (:~>) where
  optically (Mirror (Like bt sa)) ab = bt <<< ab <<< sa
  {-# INLINE optically #-}

instance Optically SummerLike (:~>) where
  optically (Window (Tensored k)) (Nt ab) =
    optically (Window k) (Nt (Day.trans2 ab))
  {-# INLINE optically #-}

instance Optically Lens1Like (:~>) where
  optically (Window (Tensored k)) (Nt ab) =
    optically (Window k) (Nt \(Pair e a) -> Pair e (ab a))
  {-# INLINE optically #-}

(*%~) :: Optical (:~>) a b s t -> (a ~> b) -> (s ~> t)
(*%~) o ab s = o (Nt ab) *$ s
{-# INLINE (*%~) #-}

newtype Star f i o = Star {runStar :: i -> f o}

instance (Functor f) => Optically IsoLike (Star f) where
  optically (Window (Like sa bt)) (Star afb) =
    Star (fmap bt . afb . sa)
  {-# INLINE optically #-}

instance (Functor f) => Optically OsiLike (Star f) where
  optically (Mirror (Like bt sa)) (Star afb) =
    Star (fmap bt . afb . sa)
  {-# INLINE optically #-}

instance
  ( forall t. Traversable (o t),
    Applicative f,
    Optically (Glass RTL k) (Star f),
    Super Optically (Glass RTL (Tensored o k)) (Star f)
  ) =>
  Optically (Glass RTL (Tensored o k)) (Star f)
  where
  optically (Window (Tensored k)) =
    optically (Window k) . (Star . traverse . runStar)
  {-# INLINE optically #-}

traverseOf :: Optical (Star f) a b s t -> (a :-> f b) -> s :-> f t
traverseOf o = runStar . o . Star
{-# INLINE traverseOf #-}

---

instance (Cat ((:->) @j)) => Optically IsoLike (Viewer @j x y) where
  optically (Window (Like sa _)) (Viewer ar) =
    Viewer (ar <<< sa)
  {-# INLINE optically #-}

instance (Cat ((:->) @j)) => Optically OsiLike (Viewer @j x y) where
  optically (Mirror (Like _bt sa)) (Viewer ar) =
    Viewer (ar <<< sa)
  {-# INLINE optically #-}

instance (Cat ((:->) @j)) => Optically ViewLike (Viewer @(j -> Type) x y) where
  optically (Window (Viewer sa)) (Viewer ar) =
    Viewer (ar <<< sa)
  {-# INLINE optically #-}

instance Optically LensLike (Viewer x y) where
  optically (Window (Tensored l)) (Viewer ar) =
    optically (Window l) (Viewer (ar <<< snd))
  {-# INLINE optically #-}

instance (Monoid x) => Optically PrismLike (Viewer x y) where
  optically (Window (Tensored l)) (Viewer ar) =
    optically (Window l) (Viewer (either mempty ar))
  {-# INLINE optically #-}

instance Optically CoprismLike (Viewer x y) where
  optically (Mirror (Tensored l)) =
    optically (Viewer Right) . optically (Window (reversed l))
  {-# INLINE optically #-}

instance (Monoid x) => Optically TraversalLike (Viewer x y) where
  optically (Window (Tensored l)) (Viewer ar) =
    optically (Window l) (Viewer (foldMap ar))
  {-# INLINE optically #-}

instance Optically Lens1Like (Viewer x y) where
  optically (Window (Tensored l)) (Viewer ar) =
    optically (Window l) (Viewer (ar <<< Nt \(Pair _ r) -> r))
  {-# INLINE optically #-}

(^.) :: s -> Optical (Viewer a b) a b s t -> a
(^.) s o = runViewer (o (Viewer id)) s
{-# INLINE (^.) #-}

(#) :: Optical (Re (Viewer t s) a b) a b s t -> b -> t
(#) o b = (^.) b (re o)
{-# INLINE (#) #-}

(*^.) :: s i -> Optical (Viewer a b) a b s t -> a i
(*^.) s o = runViewer (o (Viewer identity)) *$ s
{-# INLINE (*^.) #-}

---

asLens :: Optical (LensLike a b) a b s t -> Lens a b s t
asLens o = optically $ o (Window . Tensored $ Like ((),) snd)
{-# INLINE asLens #-}

asPrism :: Optical (PrismLike a b) a b s t -> Prism a b s t
asPrism o =
  optically . o . Window . Tensored $
    Like Right (either absurd id)
{-# INLINE asPrism #-}

asGrate :: Optical (GrateLike a b) a b s t -> Grate a b s t
asGrate o =
  optically . o . Window . Tensored $
    Like const ($ ())
{-# INLINE asGrate #-}

asTraversal :: Optical (TraversalLike a b) a b s t -> Traversal a b s t
asTraversal o =
  optically . o . Window . Tensored $
    Like
      (Walk . Identity)
      (runIdentity . getWalk)
{-# INLINE asTraversal #-}

asView :: (Cat ((:->) @k)) => Optical (ViewLike (a :: k) b) a b s t -> View a b s t
asView o = optically . o . Window . Viewer $ identity
{-# INLINE asView #-}

---

swapTuple :: Iso (x, a) (x, b) (a, x) (b, x)
swapTuple =
  iso
    (\(x, a) -> (a, x))
    (\(b, x) -> (x, b))
{-# INLINE swapTuple #-}

_2 :: Lens a b (x, a) (x, b)
_2 = lens identity identity
{-# INLINE _2 #-}

_1 :: Lens a b (a, x) (b, x)
_1 = swapTuple . _2
{-# INLINE _1 #-}

swapEither :: Iso (Either x a) (Either x b) (Either a x) (Either b x)
swapEither =
  iso
    (\case Left a -> Right a; Right x -> Left x)
    (\case Left b -> Right b; Right x -> Left x)
{-# INLINE swapEither #-}

_Right :: Prism a b (Either x a) (Either x b)
_Right = prism identity identity
{-# INLINE _Right #-}

_Left :: Prism a b (Either a x) (Either b x)
_Left = swapEither . _Right
{-# INLINE _Left #-}

_dom :: Grate a b (x -> a) (x -> b)
_dom = grate identity identity
{-# INLINE _dom #-}

_traverse :: (Traversable f) => Traversal a b (f a) (f b)
_traverse = traversal identity identity
{-# INLINE _traverse #-}

swapDay :: Iso (Day e a) (Day e b) (Day a e) (Day b e)
swapDay = iso (Nt Day.swapped) (Nt Day.swapped)
{-# INLINE swapDay #-}

_pm :: Summer a b (Day e a) (Day e b)
_pm = summer identity identity
{-# INLINE _pm #-}

_am :: Summer a b (Day a e) (Day b e)
_am = swapDay . _pm
{-# INLINE _am #-}

swapProduct :: Iso (Product e a) (Product e b) (Product a e) (Product b e)
swapProduct =
  iso
    (Nt \(Pair e a) -> Pair a e)
    (Nt \(Pair b e) -> Pair e b)
{-# INLINE swapProduct #-}

__2 :: Lens1 a b (Product e a) (Product e b)
__2 = lens1 identity identity
{-# INLINE __2 #-}

__1 :: Lens1 a b (Product a e) (Product b e)
__1 = swapProduct . __2
{-# INLINE __1 #-}

---

bothTuple :: Traversal a b (a, a) (b, b)
bothTuple =
  traversal
    (\(l, r) -> Identity l `Pair` Identity r)
    (\(Identity l `Pair` Identity r) -> (l, r))
{-# INLINE bothTuple #-}

isoBothEither :: Iso (Bool, a) (Bool, b) (Either a a) (Either b b)
isoBothEither =
  iso
    (\case Left a -> (True, a); Right b -> (False, b))
    (\case (True, a) -> Left a; (False, b) -> Right b)
{-# INLINE isoBothEither #-}

bothEither :: Lens a b (Either a a) (Either b b)
bothEither = isoBothEither . _2
{-# INLINE bothEither #-}

_2_Right :: AffineTraversal a b (x, Either y a) (x, Either y b)
_2_Right = _2 . _Right
{-# INLINE _2_Right #-}

_2view :: View a b (x, a) (x, b)
_2view = _2
{-# INLINE _2view #-}

_2traversal :: Traversal a b (x, a) (x, b)
_2traversal = _2
{-# INLINE _2traversal #-}

-- $> main

main :: IO ()
main = do
  let eg0 = (True, 42) :: (Bool, Int)
  print $ eg0 & _2 %~ show
  print $ eg0 ^. _2

  let eg1 = Right 42 :: Either Bool Int
  print $ eg1 & _Right %~ show
  print $ (eg1 & _Right %~ show) ^. _Right

  let eg2 = show :: Int -> String
  print $ (eg2 & _dom %~ (<> "!!")) 42

  let eg3 = (\i -> (True, Right (show @Int i))) :: Int -> (Bool, Either () String)
  print $ (eg3 & (_dom . _2 . _Right) %~ (<> "!!!")) 42

  print $ (_Right # 42 :: Either Bool Int)

  -- print $ (_2 # 42 :: (String, Int)) -- is this even possible

  print $ (0, 1) & bothTuple %~ show @Int

  _ <- ((3, 2), (0, 1)) & traverseOf (bothTuple . bothTuple) (print @Int)

  let eg4 = Day (Just 1) (Right 2) (+) :: Day Maybe (Either Bool) Int
  print $ Day.dap (eg4 & _pm *%~ either (const Nothing) Just)

  let eg5 = Pair (Just 1) (Right 2) :: Product Maybe (Either Bool) Int
  print $ eg5 *^. __2
  print $ eg5 & __2 *%~ either (const Nothing) Just

  mempty
