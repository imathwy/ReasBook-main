import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the canonical rational-map owner
-- `Scheme.RationalMap`, and local Chapter 29 precedent uses `genericPoints.ofComponent` for the
-- generic point of an irreducible component. The source tuple
-- `(y_i, φ_i : 𝒪_{Y,y_i} → 𝒪_{X,x_i})` is therefore packaged canonically by a morphism
-- `Spec 𝒪_{X,x_i} ⟶ Y` over `S`, indexed by irreducible components of `X`.

variable {S X Y : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S)

/-- Componentwise generic-point stalk data for rational maps from `X` to `Y` over `S`. For each
irreducible component `Z` of `X`, this is a morphism `Spec 𝒪_{X,ξ_Z} ⟶ Y` over `S`, where `ξ_Z`
is the generic point of `Z`. -/
abbrev ComponentStalkMaps :=
  ∀ Z : irreducibleComponents X,
    { g : Spec (X.presheaf.stalk (genericPoints.ofComponent Z)) ⟶ Y //
        g ≫ fY = X.fromSpecStalk (genericPoints.ofComponent Z) ≫ fX }

/-- Unfold `ComponentStalkMaps fX fY` as the family of `S`-morphisms from the generic-point
stalk spectra of the irreducible components of `X` to `Y`. -/
theorem componentStalkMaps_def :
    ComponentStalkMaps fX fY =
      ∀ Z : irreducibleComponents X,
        { g : Spec (X.presheaf.stalk (genericPoints.ofComponent Z)) ⟶ Y //
            g ≫ fY = X.fromSpecStalk (genericPoints.ofComponent Z) ≫ fX } :=
  rfl

namespace PartialMap

/-- A partial map from `X` to `Y` induces the prescribed componentwise generic-point stalk data
over `S` if it is an `S`-morphism and its restriction to each generic point agrees with the given
map from the corresponding local spectrum. -/
def HasComponentStalkMaps (p : X.PartialMap Y) (d : ComponentStalkMaps fX fY) : Prop :=
  p.hom ≫ fY = p.domain.ι ≫ fX ∧
    ∀ Z : irreducibleComponents X,
      ∃ hxZ : (genericPoints.ofComponent Z : X) ∈ p.domain,
        p.fromSpecStalkOfMem hxZ = (d Z).1

/-- Unfold `p.HasComponentStalkMaps fX fY d` into the over-`S` condition on `p` together with the
generic-point restriction equalities on every irreducible component of `X`. -/
theorem hasComponentStalkMaps_iff (p : X.PartialMap Y) (d : ComponentStalkMaps fX fY) :
    p.HasComponentStalkMaps fX fY d ↔
      p.hom ≫ fY = p.domain.ι ≫ fX ∧
        ∀ Z : irreducibleComponents X,
          ∃ hxZ : (genericPoints.ofComponent Z : X) ∈ p.domain,
            p.fromSpecStalkOfMem hxZ = (d Z).1 :=
  Iff.rfl

end PartialMap

namespace RationalMap

/-- A rational map from `X` to `Y` induces the prescribed componentwise generic-point stalk data
over `S` if it admits a representative partial map over `S` with those generic-point
restrictions. -/
def HasComponentStalkMaps (φ : X ⤏ Y) (d : ComponentStalkMaps fX fY) : Prop :=
  ∃ p : X.PartialMap Y, p.HasComponentStalkMaps fX fY d ∧ p.toRationalMap = φ

/-- Unfold `φ.HasComponentStalkMaps fX fY d` as the existence of a representative partial map over
`S` whose restrictions to the generic points of the irreducible components of `X` match `d`. -/
theorem hasComponentStalkMaps_iff (φ : X ⤏ Y) (d : ComponentStalkMaps fX fY) :
    φ.HasComponentStalkMaps fX fY d ↔
      ∃ p : X.PartialMap Y, p.HasComponentStalkMaps fX fY d ∧ p.toRationalMap = φ :=
  Iff.rfl

/-- Lemma 29.49.2 (1): let `S` be a scheme, let `X` and `Y` be schemes over `S`, and assume that
`X` has finitely many irreducible components. If `Y ⟶ S` is locally of finite type, then the
componentwise generic-point stalk data determines an `S`-rational map from `X` to `Y` uniquely. -/
@[stacks 0BX8]
theorem eq_of_hasComponentStalkMaps_of_locallyOfFiniteType
    [Finite (irreducibleComponents X)] [LocallyOfFiniteType fY]
    {φ ψ : X ⤏ Y} {d : ComponentStalkMaps fX fY}
    (hφ : φ.HasComponentStalkMaps fX fY d)
    (hψ : ψ.HasComponentStalkMaps fX fY d) :
    φ = ψ := sorry

/-- Lemma 29.49.2 (2): let `S` be a scheme, let `X` and `Y` be schemes over `S`, and assume that
`X` has finitely many irreducible components. If `Y ⟶ S` is locally of finite presentation, then
for every componentwise generic-point stalk datum there exists a unique `S`-rational map from `X`
to `Y` inducing it. -/
@[stacks 0BX8]
theorem existsUnique_rationalMap_hasComponentStalkMaps_of_locallyOfFinitePresentation
    [Finite (irreducibleComponents X)] [LocallyOfFinitePresentation fY]
    (d : ComponentStalkMaps fX fY) :
    ∃! φ : X ⤏ Y, φ.HasComponentStalkMaps fX fY d := sorry

/-- Lemma 29.49.2 (3): let `S` be a scheme, let `X` and `Y` be schemes over `S`, and assume that
`X` has finitely many irreducible components. If `Y ⟶ S` is locally of finite type and `X` is
reduced, then for every componentwise generic-point stalk datum there exists a unique
`S`-rational map from `X` to `Y` inducing it. -/
@[stacks 0BX8]
theorem existsUnique_rationalMap_hasComponentStalkMaps_of_locallyOfFiniteType_of_isReduced
    [Finite (irreducibleComponents X)] [LocallyOfFiniteType fY] [IsReduced X]
    (d : ComponentStalkMaps fX fY) :
    ∃! φ : X ⤏ Y, φ.HasComponentStalkMaps fX fY d := sorry

end RationalMap

end AlgebraicGeometry.Scheme
