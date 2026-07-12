import Mathlib
import StacksProject_2024.Chap10.Definition_10_160_1
import StacksProject_2024.Chap15.Lemma_15_41_7
import StacksProject_2024.Chap15.Theorem_15_49_3_Andr

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open AdicCompletion
open IsLocalRing
open scoped TensorProduct

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [IsNoetherianRing A] [IsCompleteLocalRing A]
variable [IsLocalRing B] [IsNoetherianRing B]
variable [IsLocalHom (algebraMap A B)]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal A) B
local notation "𝔪ClosedFiber" => Ideal.map (algebraMap B ClosedFiber) (maximalIdeal B)

/- Domain-style sampling for Proposition 15.49.2:
- primary domain: regular local morphisms from a Noetherian complete local source to a Noetherian
  local target, their special fibers, and adic formal smoothness;
- sampled owner declarations:
  `RingHom.IsRegularRingMap`,
  `flat_geometricallyRegularSpecialFiber_formallySmooth_tfae`,
  `RingHom.IsRegularRingMap.of_comp_of_faithfullyFlat`,
  `regularRingMap_specialFiber_formallySmooth_tfae_of_regular_completion`;
- best owner abstraction: the four-way equivalence is already canonically owned by
  `regularRingMap_specialFiber_formallySmooth_tfae_of_regular_completion`; in the complete-local
  case, this proposition is the specialization where the completion map
  `A → ACompletion` is regular;
- primitive data: the local map `A → B`, the complete-local owner on `A`, the local Noetherian
  target `B`, the special fiber `ClosedFiber`, and the adic ideal `𝔪ClosedFiber`;
- derived API: the regularity of `A → ACompletion`, obtained from the completion equivalence and
  faithfully-flat descent, and then the specialized `List.TFAE` conclusion.

Source/core/bridge triage:
- `source-facing`: Proposition 15.49.2 itself, the complete-local form of the four-way
  equivalence;
- `core/canonical`: `regularRingMap_specialFiber_formallySmooth_tfae_of_regular_completion`;
- `bridge/view`: the regularity of `A → ACompletion`, deduced from the equivalence
  `ofAlgEquiv (maximalIdeal A) : A ≃ₐ[A] ACompletion`.
-/
-- Proof sketch: apply the canonical theorem
-- `regularRingMap_specialFiber_formallySmooth_tfae_of_regular_completion`. Since `A` is already
-- complete for the `maximalIdeal A`-adic topology, the completion map `A → ACompletion` admits an
-- inverse ring map `ACompletion → A` from `ofAlgEquiv (maximalIdeal A)`. The composition is the
-- identity on `A`, hence regular; the inverse is bijective, therefore faithfully flat, so Lemma
-- `15.41.7` descends regularity to `A → ACompletion`.
/-- Proposition 15.49.2: for a local homomorphism `A → B` of Noetherian local rings with `A`
complete local, the following are equivalent: `A → B` is regular; `A → B` is flat and the special
fiber
`ClosedFiber = Ideal.Fiber (maximalIdeal A) B`, equivalently `ResidueField A ⊗[A] B`, is
geometrically regular over `ResidueField A`; `A → B` is flat and
`ResidueField A → ClosedFiber` is formally smooth for the `𝔪ClosedFiber`-adic topology; and
`A → B` is formally smooth for the `maximalIdeal B`-adic topology. -/
theorem regularMap_specialFiber_characterizations_tfae :
    List.TFAE [
      (algebraMap A B).IsRegularRingMap,
      (algebraMap A B).Flat ∧ Algebra.IsGeometricallyRegular (ResidueField A) ClosedFiber,
      (algebraMap A B).Flat ∧
        RingHom.formally_smooth_for_adic (algebraMap (ResidueField A) ClosedFiber) 𝔪ClosedFiber,
      (algebraMap A B).formally_smooth_for_adic (maximalIdeal B)
    ] := by
  let g : ACompletion →+* A := (ofAlgEquiv (maximalIdeal A)).symm.toRingHom
  have hcomp : (g.comp (algebraMap A ACompletion)).IsRegularRingMap := by
    have hg : g.comp (algebraMap A ACompletion) = RingHom.id A := by
      ext x
      change (ofAlgEquiv (maximalIdeal A)).symm (of (maximalIdeal A) A x) = x
      simpa using ofAlgEquiv_symm_of (maximalIdeal A) x
    rw [hg]
    infer_instance
  have hACompletion : (algebraMap A ACompletion).IsRegularRingMap :=
    RingHom.IsRegularRingMap.of_comp_of_faithfullyFlat hcomp
      (RingHom.FaithfullyFlat.of_bijective (ofAlgEquiv (maximalIdeal A)).symm.bijective)
  exact regularRingMap_specialFiber_formallySmooth_tfae_of_regular_completion hACompletion

end
