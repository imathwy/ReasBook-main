import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_42_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_158_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open IsLocalRing

universe u v

noncomputable section

variable (k : Type u) (R : Type v)
  [Field k] [CommRing R] [Algebra k R] [IsLocalRing R]

/- Domain-style sampling for Lemma 10.140.4:
- primary domain: the conormal map for the residue-field quotient of a local `k`-algebra and its
  split-injectivity via formal smoothness of the residue-field extension;
- sampled owner declarations:
  `KaehlerDifferential.kerCotangentToTensor`,
  `FormallySmooth.liftOfSurjective`,
  `retractionKerCotangentToTensorEquivSection`,
  `Algebra.formallySmooth_of_isSeparableOver`;
- best owner abstraction: the canonical conormal map
  `KaehlerDifferential.kerCotangentToTensor k R (ResidueField R)`;
- primitive data: the surjective algebra map `R → ResidueField R` and the source-facing
  separability hypothesis on `ResidueField R / k`;
- derived API: the split retraction of the conormal map coming from formal smoothness, and the
  resulting injectivity.

Source/core/bridge triage:
- `source-facing`: the injectivity statement for the cotangent-space map of a local `k`-algebra;
- `core/canonical`: `KaehlerDifferential.kerCotangentToTensor` together with the formal-smooth
  lifting owner `FormallySmooth.liftOfSurjective`;
- `bridge/view`: the identification of `ker (R → ResidueField R)` with the maximal ideal
  via `IsLocalRing.ker_residue`, which explains the cotangent-space reading but is not a second
  owner. -/

-- Proof sketch: `ResidueField R / k` is formally smooth by the chapter field-extension owner
-- `Algebra.formallySmooth_of_isSeparableOver`. Lift the identity map of `ResidueField R` across
-- the square-zero surjection `(R ⧸ m²) → ResidueField R`, obtained as the canonical
-- `kerSquareLift` of `R → ResidueField R`. The resulting section is converted by
-- `retractionKerCotangentToTensorEquivSection` into a retraction of
-- `KaehlerDifferential.kerCotangentToTensor k R (ResidueField R)`, so the conormal map is
-- injective.
/-- Lemma 10.140.4: if `R` is a local `k`-algebra whose residue field is separable over `k` in the
Stacks Project sense, then the differential induces an
injective map from the cotangent space `m/m²` to the residue-field base change of `Ω[R⁄k]`;
equivalently, the canonical conormal map for `R → ResidueField R` is injective. -/
theorem residueCotangentToKaehler_injective_of_isSeparableOver
    [Algebra.IsSeparableOver k (ResidueField R)] :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor k R (ResidueField R)) := by
  have hresidueSurj : Function.Surjective (IsLocalRing.residue R) := residue_surjective
  have hsurj : Function.Surjective (algebraMap R (ResidueField R)) := by
    simpa [ResidueField.algebraMap_eq] using hresidueSurj
  have hsurjLift :
      Function.Surjective (IsScalarTower.toAlgHom k R (ResidueField R)).kerSquareLift := by
    exact Ideal.Quotient.lift_surjective_of_surjective _ _ hsurj
  have hsqz :
      RingHom.ker (IsScalarTower.toAlgHom k R (ResidueField R)).kerSquareLift.toRingHom ^ 2 = ⊥ := by
    rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  let σ : ResidueField R →ₐ[k] R ⧸ RingHom.ker (algebraMap R (ResidueField R)) ^ 2 :=
    Algebra.FormallySmooth.liftOfSurjective
      (AlgHom.id k (ResidueField R))
      (IsScalarTower.toAlgHom k R (ResidueField R)).kerSquareLift
      hsurjLift
      ⟨2, hsqz⟩
  have hσ :
      (IsScalarTower.toAlgHom k R (ResidueField R)).kerSquareLift.comp σ =
        AlgHom.id k (ResidueField R) := by
    simpa [σ] using
      (Algebra.FormallySmooth.comp_liftOfSurjective
        (AlgHom.id k (ResidueField R))
        (IsScalarTower.toAlgHom k R (ResidueField R)).kerSquareLift
        hsurjLift
        ⟨2, hsqz⟩ : _)
  obtain ⟨l, hl⟩ := ((retractionKerCotangentToTensorEquivSection hsurj).symm ⟨σ, hσ⟩)
  exact LinearMap.injective_of_comp_eq_id _ _ hl

end
