import Mathlib
import StacksProject_2024.Chap29.Definition_29_49_1
import StacksProject_2024.Chap29.Lemma_29_49_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped AlgebraicGeometry

namespace AlgebraicGeometry
namespace Scheme.RationalMap

-- Semantic recall: `lean_leansearch` surfaced the canonical morphism-side predicate
-- `AlgebraicGeometry.IsDominant`, while nearby Chap29 files verified that rational maps are
-- represented through `Scheme.PartialMap.toRationalMap`, `Scheme.RationalMap.exists_rep`,
-- and, under the usual reduced/separated hypotheses, `φ.toPartialMap.hom`.

variable {X Y : Scheme}

/-- Definition 29.49.10: in the source this is stated for irreducible schemes `X` and `Y`; the
underlying owner is the representative-existence predicate saying that a rational map from `X` to
`Y` is dominant when it admits a representative `f : U ⟶ Y` that is a dominant morphism of
schemes. -/
def IsDominant (φ : X ⤏ Y) : Prop :=
  ∃ p : X.PartialMap Y, p.toRationalMap = φ ∧ AlgebraicGeometry.IsDominant p.hom

/-- A representative of a dominant rational map is dominant, and conversely. -/
theorem isDominant_iff_of_toRationalMap (φ : X ⤏ Y) (p : X.PartialMap Y)
    (hp : Scheme.PartialMap.toRationalMap p = φ) :
    φ.IsDominant ↔ AlgebraicGeometry.IsDominant p.hom := sorry

/-- A rational map is dominant exactly when some representative is a dominant morphism. -/
theorem isDominant_iff_exists_partialMap (φ : X ⤏ Y) :
    φ.IsDominant ↔
      ∃ p : X.PartialMap Y, p.toRationalMap = φ ∧ AlgebraicGeometry.IsDominant p.hom :=
  Iff.rfl

/-- If `X` is reduced and `Y` is separated, dominance of a rational map is equivalent to
dominance of its canonical representative on the domain of definition. -/
theorem isDominant_iff_isDominant_toPartialMap_hom [IsReduced X] [Y.IsSeparated] (φ : X ⤏ Y) :
    φ.IsDominant ↔ AlgebraicGeometry.IsDominant φ.toPartialMap.hom := by
  simpa using
    (isDominant_iff_of_toRationalMap
      φ
      (⟨φ.domain, φ.dense_domain, φ.toPartialMap.hom⟩ : X.PartialMap Y)
      (toRationalMap_toPartialMap φ))

end Scheme.RationalMap
end AlgebraicGeometry
