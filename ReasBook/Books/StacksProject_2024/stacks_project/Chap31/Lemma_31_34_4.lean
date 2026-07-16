import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` did not find a canonical common-refinement theorem for
-- admissible blowups; nearby Chapter 31 precedent uses `IsAdmissibleBlowup` as the owner.

/-- A factor map from a common refinement through a given admissible blowup, together with the
source condition that this factor map is admissible over the inverse-image open. -/
structure IsAdmissibleBlowupCommonRefinementFactor
    {X X' Xi : Scheme.{u}} (U : X.Opens)
    (bi : Xi ⟶ X) (b : X' ⟶ X) (c : X' ⟶ Xi) : Prop where
  commutes : c ≫ bi = b
  isAdmissible : IsAdmissibleBlowup ((TopologicalSpace.Opens.map bi.base).obj U) c

/-- Lemma 31.34.4: if `X` is quasi-compact and quasi-separated, `U ⊆ X` is a quasi-compact
open subscheme, and `bᵢ : Xᵢ ⟶ X` is a finite family of `U`-admissible blowups, then there is a
`U`-admissible blowup `b : X' ⟶ X` which factors through every `bᵢ`, and each factor map
`X' ⟶ Xᵢ` is admissible over the inverse-image open of `U` in `Xᵢ`. -/
@[stacks 080N]
theorem exists_isAdmissibleBlowup_common_refinement
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : IsCompact (U : Set X))
    {n : ℕ} (Xi : Fin n → Scheme.{u}) (bi : ∀ i : Fin n, Xi i ⟶ X)
    (hbi : ∀ i : Fin n, IsAdmissibleBlowup U (bi i)) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X),
      IsAdmissibleBlowup U b ∧
        ∀ i : Fin n,
          ∃ c : X' ⟶ Xi i,
            IsAdmissibleBlowupCommonRefinementFactor U (bi i) b c := sorry

end AlgebraicGeometry
