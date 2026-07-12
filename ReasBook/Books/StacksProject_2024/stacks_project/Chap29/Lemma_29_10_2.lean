import StacksProject_2024.Chap29.Definition_29_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

-- Semantic recall: `UniversallyInjective` is the canonical core owner in mathlib, while
-- `Radicial` from `Definition_29_10_1` is the chapter-local source-facing owner for the
-- injective-on-points and purely inseparable residue-field condition.

section

variable {X S : Scheme.{u}}

namespace Scheme.Hom

/-- A morphism of schemes is injective on field-valued points if every map `Spec K ⟶ X` is
determined by its composite with the morphism. This is the source-facing clause `(1)` in
Lemma 29.10.2. -/
def InjectiveOnFieldValuedPoints (f : X ⟶ S) : Prop :=
  ∀ (K : Type v) [Field K], Function.Injective (fun x : Spec (.of K) ⟶ X ↦ x ≫ f)

end Scheme.Hom

/-- Lemma 29.10.2 (1) ↔ (2): a morphism of schemes is universally injective exactly when, for
every field `K`, precomposition with `f` induces an injective map on `K`-valued points
`Spec K ⟶ X`. -/
@[stacks 01L3]
theorem universallyInjective_iff_injective_on_fieldValuedPoints (f : X ⟶ S) :
    UniversallyInjective f ↔ f.InjectiveOnFieldValuedPoints := by
  sorry

/-- Lemma 29.10.2 (2) ↔ (3): a morphism of schemes is universally injective exactly when it is
injective on points and induces a purely inseparable extension on each residue field. -/
@[stacks 01L3]
theorem universallyInjective_iff_radicial (f : X ⟶ S) :
    UniversallyInjective f ↔ Radicial f :=
  (radicial_iff_universallyInjective f).symm

/-- Lemma 29.10.2 (2) ↔ (4): a morphism of schemes is universally injective exactly when its
diagonal morphism is surjective. -/
@[stacks 01L3]
theorem universallyInjective_iff_surjective_diagonal (f : X ⟶ S) :
    UniversallyInjective f ↔ Surjective (CategoryTheory.Limits.pullback.diagonal f) :=
  UniversallyInjective.iff_diagonal

end

end

end AlgebraicGeometry
