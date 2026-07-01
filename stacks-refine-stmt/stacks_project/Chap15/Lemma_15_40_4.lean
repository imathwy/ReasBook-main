import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap10.Lemma_10_131_9
import stacks_project.Chap15.Definition_15_37_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Algebra
open IsLocalRing
open KaehlerDifferential
open scoped TensorProduct

universe u v

namespace Algebra

noncomputable section

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [IsLocalRing B]

/- Domain-style sampling for Lemma 15.40.4:
- primary domain: the residue-field Jacobi-Zariski exact sequence for the local tower
  `A → B → κ(B)`, with the middle cotangent term written source-faithfully as
  `maximalIdeal B / (maximalIdeal B)^2`.
- sampled owner declarations:
  `KaehlerDifferential.kerCotangentToTensor`,
  `KaehlerDifferential.mapBaseChange`,
  `kaehlerDifferential_exact_cotangent_tensor_of_surjective`,
  `surjective_algebra_h1Cotangent_equiv_cotangent`,
  `ModuleCat.shortComplexOfCompEqZero`.
- best owner abstraction: the source-facing sequence should keep the cotangent-space term
  `(maximalIdeal B).Cotangent`; the public owner is the source-facing short complex
  `residueFieldCotangentSequence`, whose left map is the canonical conormal map
  `residueFieldCotangentToTensor`, built from `kerCotangentToTensor`, and whose right map is the
  canonical owner `KaehlerDifferential.mapBaseChange A B (ResidueField B)`. Since all three terms
  already carry their canonical `ResidueField B`-module structures, the sequence should live in
  `ShortComplex (ModuleCat (ResidueField B))`.
- primitive data: the algebra map `A → B` and the residue-field quotient `B → κ(B)`.
- derived API: the source-facing residue-field conormal map and the resulting
  exactness bridge theorem. The stronger local-hom/Noetherian and adic formal-smoothness
  hypotheses belong only to the injectivity theorem and the short-exact upgrade below.
- derived proof input: the bridge equivalence
  `H1Cotangent B κ(B) ≃ (maximalIdeal B).Cotangent` used in the injectivity theorem.

Source/core/bridge triage:
- `source-facing`: Lemma `15.40.4`, namely the exact sequence
  `0 → m_B / m_B² → κ(B) ⊗[B] Ω[B⁄A] → Ω[κ(B)⁄A] → 0`.
- `core/canonical`: `kerCotangentToTensor`, `KaehlerDifferential.mapBaseChange`, and
  `ModuleCat.shortComplexOfCompEqZero`.
- `bridge/view`: the kernel-identified exactness theorem
  `kaehlerDifferential_exact_cotangent_tensor_of_surjective` and the transport of the conormal
  owner from `ker (B → κ(B))` to `maximalIdeal B`, together with the quotient-linear upgrade of
  the left map from `B`-linearity to `ResidueField B`-linearity.
-/

/- The source-facing residue-field conormal exactness statement is already the kernel-identified
bridge `kaehlerDifferential_exact_cotangent_tensor_of_surjective`. -/
recall kaehlerDifferential_exact_cotangent_tensor_of_surjective

private theorem ker_algebraMap_residueField :
    RingHom.ker (algebraMap B (ResidueField B)) = maximalIdeal B := by
  simpa [ResidueField.algebraMap_eq] using
    (ker_residue : RingHom.ker (IsLocalRing.residue B) = maximalIdeal B)

private theorem algebraMap_residueField_surjective :
    Function.Surjective (algebraMap B (ResidueField B)) := by
  simpa [ResidueField.algebraMap_eq] using
    (residue_surjective : Function.Surjective (IsLocalRing.residue B))

private noncomputable def residueFieldKerCotangentEquiv :
    (maximalIdeal B).Cotangent ≃ₗ[B]
      (RingHom.ker (algebraMap B (ResidueField B))).Cotangent :=
  Ideal.Cotangent.equivOfEq
    (maximalIdeal B)
    (RingHom.ker (algebraMap B (ResidueField B)))
    ker_algebraMap_residueField.symm

variable (A B)

private noncomputable def residueFieldCotangentToTensorOverB :
    (maximalIdeal B).Cotangent →ₗ[B] ResidueField B ⊗[B] Ω[B⁄A] :=
  (kerCotangentToTensor A B (ResidueField B)).comp
    residueFieldKerCotangentEquiv.toLinearMap

noncomputable def residueFieldCotangentToTensor :
    (maximalIdeal B).Cotangent →ₗ[ResidueField B] ResidueField B ⊗[B] Ω[B⁄A] where
  toFun := residueFieldCotangentToTensorOverB A B
  map_add' := (residueFieldCotangentToTensorOverB A B).map_add
  map_smul' c x := by
    refine Quotient.inductionOn c ?_
    intro b
    change residueFieldCotangentToTensorOverB A B (b • x) = b • residueFieldCotangentToTensorOverB A B x
    exact (residueFieldCotangentToTensorOverB A B).map_smul b x

theorem residueFieldCotangentToTensor_exact :
    Function.Exact
      (residueFieldCotangentToTensor A B)
      (mapBaseChange A B (ResidueField B)) := by
  exact
    (kaehlerDifferential_exact_cotangent_tensor_of_surjective
      (maximalIdeal B)
      ker_algebraMap_residueField
      algebraMap_residueField_surjective).1

theorem residueFieldCotangentSequence_comp_eq_zero :
    (mapBaseChange A B (ResidueField B)).comp (residueFieldCotangentToTensor A B) =
      0 := by
  ext x
  simpa [Function.comp] using congrFun (residueFieldCotangentToTensor_exact A B).comp_eq_zero x

/-- The residue-field cotangent sequence
`(maximalIdeal B).Cotangent ⟶ ResidueField B ⊗[B] Ω[B⁄A] ⟶ Ω[ResidueField B⁄A]`
viewed in the canonical owner `ShortComplex (ModuleCat (ResidueField B))`. -/
noncomputable abbrev residueFieldCotangentSequence :
    ShortComplex (ModuleCat (ResidueField B)) :=
  ModuleCat.shortComplexOfCompEqZero
    (residueFieldCotangentToTensor A B)
    (mapBaseChange A B (ResidueField B))
    (residueFieldCotangentSequence_comp_eq_zero A B)

variable {A B}

section

variable [IsLocalRing A] [IsLocalHom (algebraMap A B)]
variable [IsNoetherianRing A] [IsNoetherianRing B]

-- Proof sketch: identify the residue-field Jacobi-Zariski connecting term
-- `H₁(L_{κ(B)/B})` with `maximalIdeal B / (maximalIdeal B)^2` via the canonical surjective bridge
-- `surjective_algebra_h1Cotangent_equiv_cotangent`. The formal-smoothness hypothesis kills the
-- preceding homology term, so the source-facing conormal map becomes injective.
/-- Lemma 15.40.4: let `A → B` be a local homomorphism of Noetherian local rings. If
`A → B` is formally smooth for the `maximalIdeal B`-adic topology, then the leftmost map
`maximalIdeal B / (maximalIdeal B)^2 → κ(B) ⊗[B] Ω[B⁄A]`
in the residue-field cotangent sequence is injective. Combined with the kernel-identified
exactness bridge from Lemma `10.131.9`, this gives the source-facing exact sequence
`0 → maximalIdeal B / (maximalIdeal B)^2 → κ(B) ⊗[B] Ω[B⁄A] → Ω[κ(B)⁄A] → 0`. -/
theorem residueFieldCotangentToTensor_injective_of_formallySmooth_for_maximalIdeal_adic
    (hfs : RingHom.formally_smooth_for_adic (algebraMap A B) (maximalIdeal B)) :
    Function.Injective (residueFieldCotangentToTensor A B) := sorry

/-- Lemma 15.40.4: under maximal-ideal-adic formal smoothness, the residue-field cotangent
sequence
`0 → maximalIdeal B / (maximalIdeal B)^2 →
  κ(B) ⊗[B] Ω[B⁄A] → Ω[κ(B)⁄A] → 0`
is short exact. -/
theorem residueFieldCotangent_shortExact_of_formallySmooth_for_maximalIdeal_adic
    (hfs : RingHom.formally_smooth_for_adic (algebraMap A B) (maximalIdeal B)) :
    (residueFieldCotangentSequence A B).ShortExact := by
  refine ModuleCat.shortComplex_shortExact (residueFieldCotangentSequence A B) ?_ ?_ ?_
  · change Function.Exact (residueFieldCotangentToTensor A B) (mapBaseChange A B (ResidueField B))
    exact residueFieldCotangentToTensor_exact A B
  · change Function.Injective (residueFieldCotangentToTensor A B)
    exact residueFieldCotangentToTensor_injective_of_formallySmooth_for_maximalIdeal_adic hfs
  · change Function.Surjective (mapBaseChange A B (ResidueField B))
    exact mapBaseChange_surjective A B (ResidueField B) algebraMap_residueField_surjective

end

end

end

end Algebra
