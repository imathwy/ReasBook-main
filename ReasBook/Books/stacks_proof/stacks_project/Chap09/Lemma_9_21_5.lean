import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open IntermediateField

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable [Algebra.IsSeparable K L]

/-
Domain-style sampling for Lemma 9.21.5:
- primary domain: Galois and normal closure theory for separable field extensions;
- sampled owner declarations:
  `IntermediateField.normalClosure`,
  `IntermediateField.normalClosure_le_iff`,
  `IntermediateField.le_separableClosure_iff`,
  `Algebra.IsAlgebraic.isNormalClosure_normalClosure`;
- best owner abstraction: the canonical intermediate field `normalClosure K L (AlgebraicClosure L)`.

Source/core/bridge triage:
- `source-facing`: the normal closure of the separable extension `L/K` inside
  `AlgebraicClosure L`;
- `core/canonical`: the owner-level construction `normalClosure K L (AlgebraicClosure L)`;
- `bridge/view`: the proof that this owner is Galois over `K`, assembled from the canonical
  normality and separability APIs.

Primitive data are only the tower `K → L → AlgebraicClosure L` together with the separability of
`L/K`. The Galois property is entirely derived API, so this file should use the canonical owner
directly rather than introducing any parallel local closure object or comparison wrapper.
-/

/-- Helper for Lemma 9.21.5: the field range of a `K`-embedding of `L` into `AlgebraicClosure L`
lies in the separable closure over `K`. -/
lemma field_range_le_separable_closure_of_embedding
    (f : L →ₐ[K] AlgebraicClosure L) :
    f.fieldRange ≤ separableClosure K (AlgebraicClosure L) := by
  -- Transport separability of `L/K` across the canonical equivalence onto the embedding range.
  refine (le_separableClosure_iff K (AlgebraicClosure L) f.fieldRange).2 ?_
  exact AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField f)

/-- Helper for Lemma 9.21.5: the canonical normal closure inside `AlgebraicClosure L` is
contained in the separable closure over `K`. -/
lemma normal_closure_le_separable_closure :
    normalClosure K L (AlgebraicClosure L) ≤ separableClosure K (AlgebraicClosure L) := by
  -- Control the normal closure through the defining condition on the ranges of embeddings.
  exact normalClosure_le_iff.2 field_range_le_separable_closure_of_embedding

/-- Lemma 9.21.5: for a separable extension `L/K` (in particular for a finite separable one),
the normal closure of `L/K`, taken inside `AlgebraicClosure L`, is Galois over `K`. -/
@[stacks 0EXM]
theorem isGalois_normalClosure_of_separable :
    IsGalois K (normalClosure K L (AlgebraicClosure L)) := by
  -- Decompose the Galois condition into separability and normality of the canonical owner.
  rw [isGalois_iff]
  constructor
  · rw [← le_separableClosure_iff]
    -- The normal closure is separable because every embedding range lands in the separable closure.
    exact normal_closure_le_separable_closure (K := K) (L := L)
  · -- Route correction: close normality through the owner-level `normalClosure.normal` instance.
    infer_instance
