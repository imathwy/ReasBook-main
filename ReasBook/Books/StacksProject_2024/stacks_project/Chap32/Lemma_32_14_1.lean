import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical closed-subscheme owner
-- `Scheme.IdealSheafData`, base change via `pullback.snd`, plus the morphism property
-- `LocallyOfFinitePresentation`; nearby Chapter 31 files use `IdealSheafData.comap` for
-- fibre restrictions of closed subschemes.

/-- A closed subscheme of `Y` avoids the fibre of `p : Y ⟶ B` over the point `b`. -/
def ClosedSubschemeAvoidsFiber {Y B : Scheme.{u}} (p : Y ⟶ B)
    (Z : Y.IdealSheafData) (b : B) : Prop :=
  IsEmpty ((Z.comap (Scheme.Hom.fiberι p b)).subscheme)

/-- Witnesses for approximating a closed subscheme over an affine neighbourhood by a
locally-finitely-presented affine `S`-scheme. -/
structure ClosedSubschemeAvoidingFiberApproximation
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (t : T)
    (Z : (pullback f g).IdealSheafData) where
  /-- The affine open neighbourhood of `t`. -/
  V : T.Opens
  /-- The point `t` lies in the chosen open neighbourhood. -/
  hVt : t ∈ (V : Set T)
  /-- The chosen open neighbourhood is affine. -/
  isAffineV : IsAffine V.toScheme
  /-- The approximating scheme over `S`. -/
  T' : Scheme.{u}
  /-- The structure morphism `T' ⟶ S`. -/
  b : T' ⟶ S
  /-- The morphism `T' ⟶ S` is locally of finite presentation. -/
  lfp_b : LocallyOfFinitePresentation b
  /-- The approximating scheme `T'` is affine. -/
  isAffineT' : IsAffine T'
  /-- The comparison map from the neighbourhood to `T'`. -/
  a : V.toScheme ⟶ T'
  /-- The comparison map is compatible with the maps to `S`. -/
  comm : CommSq a V.ι b g
  /-- The closed subscheme over the approximating base. -/
  Z' : (pullback f b).IdealSheafData
  /-- The approximating closed subscheme avoids the fibre over `a(t)`. -/
  avoidsFiber : ClosedSubschemeAvoidsFiber (pullback.snd f b) Z' (a ⟨t, hVt⟩)
  /-- The projection from `X ×_S V` to `X ×_S T`. -/
  toXT : pullback f (V.ι ≫ g) ⟶ pullback f g
  /-- The projection from `X ×_S V` to `X ×_S T'`. -/
  toXT' : pullback f (V.ι ≫ g) ⟶ pullback f b
  /-- The first projection of `toXT` is the first projection from `X ×_S V`. -/
  toXT_fst : toXT ≫ pullback.fst f g = pullback.fst f (V.ι ≫ g)
  /-- The second projection of `toXT` is induced by `V ⟶ T`. -/
  toXT_snd : toXT ≫ pullback.snd f g = pullback.snd f (V.ι ≫ g) ≫ V.ι
  /-- The first projection of `toXT'` is the first projection from `X ×_S V`. -/
  toXT'_fst : toXT' ≫ pullback.fst f b = pullback.fst f (V.ι ≫ g)
  /-- The second projection of `toXT'` is induced by `V ⟶ T'`. -/
  toXT'_snd : toXT' ≫ pullback.snd f b = pullback.snd f (V.ι ≫ g) ≫ a
  /-- The restriction of `Z` to `X ×_S V` is contained in the inverse image of `Z'`. -/
  closedSubscheme_le : Z'.comap toXT' ≤ Z.comap toXT

/-- Lemma 32.14.1: for a quasi-compact morphism `f : X ⟶ S`, a morphism
`g : T ⟶ S`, a point `t : T`, with a closed subscheme `Z ⊆ X_T` disjoint from the
fibre `X_t`, there is an affine open neighbourhood `V` of `t`, an affine scheme `T'`
locally of finite presentation over `S`, a commutative square `V ⟶ T'` over `T ⟶ S`,
plus a closed subscheme `Z' ⊆ X_{T'}` disjoint from the fibre over `a(t)`, such that
`Z ∩ X_V` maps into `Z'` under the induced map `X_V ⟶ X_{T'}`. The two maps from
`X_V = X ×_S V` to `X_T`, respectively `X_{T'}`, are recorded by their pullback projection
identities; the final inequality says exactly that the restriction of `Z` to `X_V`
is contained in the inverse image of `Z'`. -/
@[stacks 05BD]
theorem exists_affine_neighborhood_lfp_approximation_closedSubscheme_avoids_fiber
    {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] (g : T ⟶ S)
    (t : T) (Z : (pullback f g).IdealSheafData)
    (hZt : ClosedSubschemeAvoidsFiber (pullback.snd f g) Z t) :
    Nonempty (ClosedSubschemeAvoidingFiberApproximation f g t Z) := sorry

end AlgebraicGeometry
