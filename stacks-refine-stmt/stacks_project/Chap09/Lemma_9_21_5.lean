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

/-- Lemma 9.21.5: for a separable extension `L/K` (in particular for a finite separable one),
the normal closure of `L/K`, taken inside `AlgebraicClosure L`, is Galois over `K`. -/
theorem isGalois_normalClosure_of_separable :
    IsGalois K (normalClosure K L (AlgebraicClosure L)) := by
  rw [isGalois_iff]
  constructor
  · rw [← le_separableClosure_iff]
    exact normalClosure_le_iff.2 fun f ↦ by
      letI : Algebra.IsSeparable K f.fieldRange :=
        AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField f)
      exact le_separableClosure K (AlgebraicClosure L) f.fieldRange
  · let hnormalClosure : IsNormalClosure K L (normalClosure K L (AlgebraicClosure L)) :=
      Algebra.IsAlgebraic.isNormalClosure_normalClosure
        (fun x ↦ IsAlgClosed.splits ((minpoly K x).map (algebraMap K (AlgebraicClosure L))))
    letI : IsNormalClosure K L (normalClosure K L (AlgebraicClosure L)) := hnormalClosure
    infer_instance
