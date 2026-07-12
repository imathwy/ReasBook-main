import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
variable [∀ {i j : OrderDual I} (f : i ⟶ j), IsAffineHom (D.map f)]

-- Semantic recall: `lean_leansearch` found the canonical residue-field owner
-- `Scheme.residueField`, the induced map `Scheme.Hom.residueFieldMap`, and the
-- affine-transition limit API from `Mathlib.AlgebraicGeometry.AffineTransitionLimit`; local
-- Chapter 32 precedent represents a limit scheme by a cone `c : Cone D` with `hc : IsLimit c`.

/-- The stagewise image of a point of a limit cone. -/
abbrev limitPointImage (s : c.pt) (i : OrderDual I) : D.obj i :=
  (c.π.app i) s

/-- A point of a limit cone is compatible with all transition morphisms. -/
theorem limitPointImage_compatible (s : c.pt) {i j : OrderDual I} (f : i ⟶ j) :
    (D.map f) (limitPointImage D c s i) = limitPointImage D c s j := sorry

/-- The reduced induced scheme structure on the closure of a point. -/
structure ReducedPointClosure (X : Scheme.{u}) (x : X) where
  /-- The scheme carrying the reduced induced structure on the closure. -/
  carrier : Scheme.{u}
  /-- The closed immersion into the ambient scheme. -/
  ι : carrier ⟶ X
  /-- The inclusion is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion ι
  /-- The model is reduced. -/
  isReduced : IsReduced carrier
  /-- The underlying image of the model is exactly the topological closure of the point. -/
  range_eq_closure :
    Set.range ι.base = closure ({x} : Set X)

/-- A reduced point closure is used as its underlying scheme. -/
instance ReducedPointClosure.instCoeSort (X : Scheme.{u}) (x : X) :
    CoeSort (ReducedPointClosure X x) (Type u) where
  coe Z := Z.carrier

/-- The inclusion map of a reduced point closure. -/
abbrev ReducedPointClosure.inclusion {X : Scheme.{u}} {x : X}
    (Z : ReducedPointClosure X x) : Z.carrier ⟶ X :=
  Z.ι

/-- The reduced point closure has underlying image equal to the singleton closure. -/
theorem ReducedPointClosure.range_inclusion {X : Scheme.{u}} {x : X}
    (Z : ReducedPointClosure X x) :
    Set.range Z.inclusion.base = closure ({x} : Set X) := sorry

/-- Lemma 32.4.4 (1): for a directed inverse system of schemes with affine transition morphisms,
if `S = lim_i S_i` and `s ∈ S` has images `s_i ∈ S_i`, then the residue field `κ(s)` is the
filtered colimit of the residue fields `κ(s_i)`.  The diagram and cocone are supplied explicitly,
with object and vertex identifications recording that they are the stagewise residue fields and
`κ(s)`. -/
@[stacks 0CUG]
def isColimit_limitPointResidueFieldCocone
    (s : c.pt) (hlim : IsLimit c) (K : (OrderDual I)ᵒᵖ ⥤ CommRingCat.{u})
    (t : Cocone K)
    (hK_obj : ∀ i : (OrderDual I)ᵒᵖ,
      K.obj i = (D.obj i.unop).residueField (limitPointImage D c s i.unop))
    (hK_map : ∀ {i j : (OrderDual I)ᵒᵖ} (f : i ⟶ j),
      K.map f =
        eqToHom (hK_obj i) ≫
          (Scheme.residueFieldCongr (limitPointImage_compatible D c s f.unop)).inv ≫
            Scheme.Hom.residueFieldMap (D.map f.unop) (limitPointImage D c s j.unop) ≫
              eqToHom (hK_obj j).symm)
    (ht_pt : t.pt = c.pt.residueField s)
    (ht_map : ∀ i : (OrderDual I)ᵒᵖ,
      t.ι.app i =
        eqToHom (hK_obj i) ≫
          Scheme.Hom.residueFieldMap (c.π.app i.unop) s ≫
            eqToHom ht_pt.symm) :
    IsColimit t := sorry

/-- The residue-field cocone colimit witness satisfies the canonical factorization property. -/
@[stacks 0CUG]
theorem isColimit_limitPointResidueFieldCocone_fac
    (s : c.pt) (hlim : IsLimit c) (K : (OrderDual I)ᵒᵖ ⥤ CommRingCat.{u})
    (t : Cocone K)
    (hK_obj : ∀ i : (OrderDual I)ᵒᵖ,
      K.obj i = (D.obj i.unop).residueField (limitPointImage D c s i.unop))
    (hK_map : ∀ {i j : (OrderDual I)ᵒᵖ} (f : i ⟶ j),
      K.map f =
        eqToHom (hK_obj i) ≫
          (Scheme.residueFieldCongr (limitPointImage_compatible D c s f.unop)).inv ≫
            Scheme.Hom.residueFieldMap (D.map f.unop) (limitPointImage D c s j.unop) ≫
              eqToHom (hK_obj j).symm)
    (ht_pt : t.pt = c.pt.residueField s)
    (ht_map : ∀ i : (OrderDual I)ᵒᵖ,
      t.ι.app i =
        eqToHom (hK_obj i) ≫
          Scheme.Hom.residueFieldMap (c.π.app i.unop) s ≫
            eqToHom ht_pt.symm)
    (w : Cocone K) (i : (OrderDual I)ᵒᵖ) :
    t.ι.app i ≫
        (isColimit_limitPointResidueFieldCocone D c s hlim K t hK_obj hK_map ht_pt ht_map).desc w =
      w.ι.app i := sorry

/-- Lemma 32.4.4 (2): for a directed inverse system of schemes with affine transition morphisms,
if `S = lim_i S_i` and `s ∈ S` has images `s_i ∈ S_i`, then the closure of `{s}` is the inverse
limit of the closures of `{s_i}` as underlying sets.  The set-valued diagram and cone are supplied
explicitly, with object and vertex identifications recording the singleton closures. -/
@[stacks 0CUG]
def isLimit_limitPointClosureSetCone
    (s : c.pt) (hlim : IsLimit c) (Z : OrderDual I ⥤ Type u) (t : Cone Z)
    (hZ_obj : ∀ i : OrderDual I,
      Z.obj i = closure ({limitPointImage D c s i} : Set (D.obj i)))
    (hZ_map : ∀ {i j : OrderDual I} (f : i ⟶ j) (x : Z.obj i),
      ((cast (hZ_obj j) ((Z.map f) x) :
        closure ({limitPointImage D c s j} : Set (D.obj j))) : D.obj j) =
        (D.map f)
          (((cast (hZ_obj i) x :
            closure ({limitPointImage D c s i} : Set (D.obj i))) : D.obj i)))
    (ht_pt : t.pt = closure ({s} : Set c.pt))
    (ht_map : ∀ (i : OrderDual I) (x : t.pt),
      ((cast (hZ_obj i) ((t.π.app i) x) :
        closure ({limitPointImage D c s i} : Set (D.obj i))) : D.obj i) =
        (c.π.app i) (((cast ht_pt x : closure ({s} : Set c.pt)) : c.pt))) :
    IsLimit t := sorry

/-- The point-closure set cone limit witness satisfies the canonical factorization property. -/
@[stacks 0CUG]
theorem isLimit_limitPointClosureSetCone_fac
    (s : c.pt) (hlim : IsLimit c) (Z : OrderDual I ⥤ Type u) (t : Cone Z)
    (hZ_obj : ∀ i : OrderDual I,
      Z.obj i = closure ({limitPointImage D c s i} : Set (D.obj i)))
    (hZ_map : ∀ {i j : OrderDual I} (f : i ⟶ j) (x : Z.obj i),
      ((cast (hZ_obj j) ((Z.map f) x) :
        closure ({limitPointImage D c s j} : Set (D.obj j))) : D.obj j) =
        (D.map f)
          (((cast (hZ_obj i) x :
            closure ({limitPointImage D c s i} : Set (D.obj i))) : D.obj i)))
    (ht_pt : t.pt = closure ({s} : Set c.pt))
    (ht_map : ∀ (i : OrderDual I) (x : t.pt),
      ((cast (hZ_obj i) ((t.π.app i) x) :
        closure ({limitPointImage D c s i} : Set (D.obj i))) : D.obj i) =
        (c.π.app i) (((cast ht_pt x : closure ({s} : Set c.pt)) : c.pt)))
    (w : Cone Z) (i : OrderDual I) :
    (isLimit_limitPointClosureSetCone D c s hlim Z t hZ_obj hZ_map ht_pt ht_map).lift w ≫
        t.π.app i =
      w.π.app i := sorry

/-- Lemma 32.4.4 (3): for a directed inverse system of schemes with affine transition morphisms,
if `S = lim_i S_i` and `s ∈ S` has images `s_i ∈ S_i`, then the reduced induced scheme structure
on `closure {s}` is the inverse limit of the reduced induced scheme structures on
`closure {s_i}`.  The reduced closed models are explicit parameters, so the concrete reduced
induced structures are not hidden behind an existential choice. -/
@[stacks 0CUG]
def isLimit_reducedPointClosureCone
    (s : c.pt) (hlim : IsLimit c) (Zstage : ∀ i : OrderDual I,
      ReducedPointClosure (D.obj i) (limitPointImage D c s i))
    (Zlimit : ReducedPointClosure c.pt s)
    (E : OrderDual I ⥤ Scheme.{u}) (t : Cone E)
    (hE_obj : ∀ i : OrderDual I, E.obj i = (Zstage i).carrier)
    (hE_map : ∀ {i j : OrderDual I} (f : i ⟶ j),
      E.map f ≫ eqToHom (hE_obj j) ≫ (Zstage j).inclusion =
        eqToHom (hE_obj i) ≫ (Zstage i).inclusion ≫ D.map f)
    (ht_pt : t.pt = Zlimit.carrier)
    (hπ_fac : ∀ i : OrderDual I,
      t.π.app i ≫ eqToHom (hE_obj i) ≫ (Zstage i).inclusion =
        eqToHom ht_pt ≫ Zlimit.inclusion ≫ c.π.app i) :
    IsLimit t := sorry

/-- The reduced point-closure cone limit witness satisfies the canonical factorization property. -/
@[stacks 0CUG]
theorem isLimit_reducedPointClosureCone_fac
    (s : c.pt) (hlim : IsLimit c) (Zstage : ∀ i : OrderDual I,
      ReducedPointClosure (D.obj i) (limitPointImage D c s i))
    (Zlimit : ReducedPointClosure c.pt s)
    (E : OrderDual I ⥤ Scheme.{u}) (t : Cone E)
    (hE_obj : ∀ i : OrderDual I, E.obj i = (Zstage i).carrier)
    (hE_map : ∀ {i j : OrderDual I} (f : i ⟶ j),
      E.map f ≫ eqToHom (hE_obj j) ≫ (Zstage j).inclusion =
        eqToHom (hE_obj i) ≫ (Zstage i).inclusion ≫ D.map f)
    (ht_pt : t.pt = Zlimit.carrier)
    (hπ_fac : ∀ i : OrderDual I,
      t.π.app i ≫ eqToHom (hE_obj i) ≫ (Zstage i).inclusion =
        eqToHom ht_pt ≫ Zlimit.inclusion ≫ c.π.app i)
    (w : Cone E) (i : OrderDual I) :
    (isLimit_reducedPointClosureCone D c s hlim Zstage Zlimit E t hE_obj hE_map ht_pt hπ_fac).lift w ≫
        t.π.app i =
      w.π.app i := sorry

end

end AlgebraicGeometry
