import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import StacksProject_2024.Chap28.Proposition_28_26_13

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme

/- Semantic recall: `lean_leansearch` surfaced the canonical owners `Scheme.IsQuasiAffine`,
`IsAffineOpen`, and `Proj`. The phrase "isomorphic to a locally closed subscheme" is represented
by the canonical scheme-theoretic immersion owner `IsImmersion`. The local Chapter 28 owner for
ample invertible sheaves is `Scheme.Modules.IsAmple`, but importing that owner currently pulls
out-of-scope Chapter 17 dependency failures in item-file checking. -/

/-- Lemma 28.29.5 (1): if `X` is quasi-affine, then every finite subset of `X` is contained
in an affine open subset of `X`. -/
@[stacks 01ZY]
theorem exists_affineOpen_containing_finiteSet_of_isQuasiAffine
    {X : Scheme.{u}} (hX : X.IsQuasiAffine) (E : Set X) (hE : E.Finite) :
    ∃ U : X.Opens, IsAffineOpen U ∧ E ⊆ (U : Set X) := sorry

/-- Lemma 28.29.5 (2): if `X` is isomorphic to a locally closed subscheme of an affine
scheme, then every finite subset of `X` is contained in an affine open subset of `X`. -/
@[stacks 01ZY]
theorem exists_affineOpen_containing_finiteSet_of_exists_isImmersion_to_isAffine
    {X : Scheme.{u}}
    (hX : ∃ (Y : Scheme.{u}) (hY : IsAffine Y) (i : X ⟶ Y), IsImmersion i)
    (E : Set X) (hE : E.Finite) :
    ∃ U : X.Opens, IsAffineOpen U ∧ E ⊆ (U : Set X) := sorry

/- Lemma 28.29.5, ample invertible-sheaf clause: if `X` has an ample invertible sheaf, then every finite subset of
`X` is contained in an affine open subset of `X`. This clause is intentionally kept as a
source-facing recall block until the local `Scheme.Modules.IsAmple` import is dependency-closed
for item-file checking. -/
#check List.TFAE

/-- Lemma 28.29.5 (3): if `X` is isomorphic to a locally closed subscheme of `Proj(S)` for
some graded ring `S`, then every finite subset of `X` is contained in an affine open subset
of `X`. -/
@[stacks 01ZY]
theorem exists_affineOpen_containing_finiteSet_of_exists_isImmersion_to_Proj
    {X : Scheme.{u}}
    (hX : ∃ (A : Type u) (σ : Type v) (_ : CommRing A) (_ : SetLike σ A)
        (_ : AddSubgroupClass σ A) (𝒜 : ℕ → σ) (_ : GradedRing 𝒜)
        (i : X ⟶ Proj 𝒜), IsImmersion i)
    (E : Set X) (hE : E.Finite) :
    ∃ U : X.Opens, IsAffineOpen U ∧ E ⊆ (U : Set X) := sorry

end AlgebraicGeometry.Scheme
