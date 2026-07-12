import Mathlib
import StacksProject_2024.Chap31.Definition_31_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

namespace AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` surfaced `Scheme.Hom.preimage_sup` and related open-preimage
-- API; nearby Chapter 31 files use `IsAdmissibleBlowup` as the owner for admissible blowups.

/-- A pair of open subschemes of the source of `b` that are disjoint, cover the source, and
contain the inverse images of the two prescribed opens. -/
structure DisjointOpenCoverContainsPreimages
    {X X' : Scheme.{u}} (b : X' ⟶ X) (U V : X.Opens) (X₁ X₂ : X'.Opens) : Prop where
  /-- The two opens are disjoint. -/
  disjoint : Disjoint (X₁ : Set X') (X₂ : Set X')
  /-- The two opens cover the source scheme. -/
  sup_eq_top : X₁ ⊔ X₂ = ⊤
  /-- The inverse image of the first prescribed open lies in the first open. -/
  preimage_left_le : (b ⁻¹ᵁ U) ≤ X₁
  /-- The inverse image of the second prescribed open lies in the second open. -/
  preimage_right_le : (b ⁻¹ᵁ V) ≤ X₂

/-- Lemma 31.34.5: if `X` is quasi-compact and quasi-separated and `U, V ⊆ X` are disjoint
quasi-compact open subschemes, then there is a `(U ∪ V)`-admissible blowup `b : X' ⟶ X` such
that `X'` is the disjoint union of two open subschemes `X₁` and `X₂`, with `b⁻¹(U) ⊆ X₁` and
`b⁻¹(V) ⊆ X₂`. -/
@[stacks 080P]
theorem exists_isAdmissibleBlowup_disjointOpenCover_of_disjoint_qc_opens
    {X : Scheme.{u}} [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    (U V : X.Opens) (hU : QuasiCompact U.ι) (hV : QuasiCompact V.ι)
    (hUV : Disjoint (U : Set X) (V : Set X)) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X),
      IsAdmissibleBlowup (U ⊔ V) b ∧
        ∃ X₁ X₂ : X'.Opens,
          DisjointOpenCoverContainsPreimages b U V X₁ X₂ := sorry

end AlgebraicGeometry
