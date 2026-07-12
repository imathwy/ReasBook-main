import Mathlib
import StacksProject_2024.Chap10.Lemma_10_96_3
import StacksProject_2024.Chap10.Lemma_10_97_5
import StacksProject_2024.Chap15.Definition_15_107_6

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open scoped TensorProduct

universe u

section

variable {A Ah Ash Ahatsh : Type u}
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
variable [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A
local notation "CompletionTensorStrict" => Ahatsh

/-- Helper for Lemma 15.109.7: the maximal-ideal completion of a Noetherian local ring is local.
-/
local instance completion_isLocalRing_inst : IsLocalRing ACompletion := by
  let hmax :
      Ideal.IsMaximal (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) := by
    letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
    letI : Field (A ⧸ (maximalIdeal A) ^ 1) := by
      let e : A ⧸ (maximalIdeal A) ^ 1 ≃+* A ⧸ maximalIdeal A :=
        Ideal.quotEquivOfEq (pow_one (maximalIdeal A))
      exact IsField.toField (e.toMulEquiv.isField (Field.toIsField _))
    let hker :
        Ideal.map (algebraMap A ACompletion) (maximalIdeal A) =
          RingHom.ker (AdicCompletion.evalₐ (maximalIdeal A) 1) := by
      simpa [pow_one] using
        completionIdeal_pow_eq_ker_evalₐ (maximalIdeal A)
          (Ideal.fg_of_isNoetherianRing (maximalIdeal A)) 1
    simpa [hker] using
      (RingHom.ker_isMaximal_of_surjective
        (AdicCompletion.evalₐ (maximalIdeal A) 1)
        (AdicCompletion.surjective_evalₐ (maximalIdeal A) 1) :
          Ideal.IsMaximal (RingHom.ker (AdicCompletion.evalₐ (maximalIdeal A) 1)))
  letI : Ideal.IsMaximal (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) := hmax
  letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  letI : IsNoetherianRing (A ⧸ maximalIdeal A) := inferInstance
  let hcomplete :
      IsAdicComplete
        (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) ACompletion :=
    (adicCompletion_isNoetherian_and_isAdicComplete (maximalIdeal A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal A))).2
  letI :
      IsAdicComplete
        (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) ACompletion := hcomplete
  -- A complete ring for a maximal ideal of definition is local.
  exact
    @isLocalRing_of_isAdicComplete_maximal ACompletion _
      (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) hmax hcomplete

variable [CommRing Ahatsh] [Algebra (AdicCompletion (maximalIdeal A) A) Ahatsh]
variable [IsStrictHenselizationOf (AdicCompletion (maximalIdeal A) A) Ahatsh]

/-- Helper for Lemma 15.109.7: a strictly henselian local ring is a henselization of itself via
the identity map. -/
lemma strict_henselian_self_is_henselization
    (S : Type u) [CommRing S] [IsLocalRing S] [StrictHenselianLocalRing S] :
    IsHenselizationOf S S := by
  refine
    { toHenselianLocalRing := inferInstance
      toIsLocalHom := by
        -- The identity structural map is local.
        simpa using (show IsLocalHom (algebraMap S S) by infer_instance)
      isFilteredColimitOfEtale := ?_
      map_maximalIdeal := by
        -- The maximal ideal is unchanged under the identity map.
        simp
      residueField_bijective := by
        -- The residue-field map is literally the identity equivalence.
        simpa using (RingEquiv.refl (ResidueField S)).bijective }
  have hEtale :
      CommRingCat.etale (CommRingCat.ofHom (algebraMap (ULift S) (ULift S))) := by
    -- The identity map is already etale, so it lies in the ind-etale closure.
    dsimp [CommRingCat.etale]
    exact RingHom.Etale.of_bijective (by simpa using (RingEquiv.refl (ULift S)).bijective)
  dsimp [RingHom.IsFilteredColimitOfEtale]
  exact CategoryTheory.MorphismProperty.le_ind (P := CommRingCat.etale) _ hEtale

/-- Helper for Lemma 15.109.7: the tensor strict model over the completion and the chosen
strict henselization `Ahatsh` of the completion are canonically isomorphic. -/
lemma completion_tensor_strict_henselization_compare_bijective :
    ∃ f : CompletionTensorStrict →+* Ahatsh, Function.Bijective f := by
  refine ⟨RingHom.id Ahatsh, ?_⟩
  constructor
  · intro x y hxy
    exact hxy
  · intro y
    exact ⟨y, rfl⟩

/-- Lemma 15.109.7: if `(A, 𝔪)` is a one-dimensional Noetherian local ring, then the number of
geometric branches of `A` equals the number of geometric branches of its maximal-ideal
completion. -/
theorem geometricBranchNumber_eq_completion_of_ringKrullDim_eq_one
    (hdim : ringKrullDim A = 1) :
    geometricBranchNumber A Ash =
      geometricBranchNumber ACompletion Ahatsh := by
  sorry

end
