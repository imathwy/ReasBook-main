import Mathlib
import StacksProject_2024.Chap15.Definition_15_107_6
import StacksProject_2024.Chap15.Lemma_15_45_3
import StacksProject_2024.Chap15.Lemma_15_105_11
import StacksProject_2024.Chap15.Lemma_15_107_7
import StacksProject_2024.Chap15.Lemma_15_109_1.Index
import StacksProject_2024.Chap15.Lemma_15_109_7

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open scoped TensorProduct

universe u

noncomputable section

attribute [local instance] Algebra.TensorProduct.leftAlgebra Algebra.TensorProduct.rightAlgebra

section

variable {A Ah Ash Ahatsh : Type u}
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
variable [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

/-- Helper for Lemma 15.109.1: regard the completion as an `Ah`-algebra through the canonical
comparison map. -/
local instance completionComparisonAlgebra : Algebra Ah ACompletion :=
  (henselizationCompletionComparison A Ah).toAlgebra

/-- Helper for Lemma 15.109.1: the chosen henselization maps faithfully flatly to the maximal-
ideal completion of the base local ring. -/
lemma henselizationCompletionComparison_faithfullyFlat :
    RingHom.FaithfullyFlat (algebraMap Ah ACompletion) := by
  simpa [henselizationCompletionComparison, henselizationToBaseCompletion] using
    (henselizationToBaseCompletion_faithfullyFlat (R := A) (Rh := Ah))

/-- Helper for Lemma 15.109.1: contracting a completion minimal prime along the comparison map
again yields a henselization minimal prime. -/
lemma comap_mem_minimalPrimes_of_completion_minimalPrime
    (Q : minimalPrimes ACompletion) :
    Ideal.comap (henselizationCompletionComparison A Ah) Q ∈ minimalPrimes Ah := by
  change Ideal.comap (algebraMap Ah ACompletion) Q ∈ minimalPrimes Ah
  exact
    comap_mem_minimalPrimes_of_faithfullyFlat
      (R := Ah) (S := ACompletion)
      (henselizationCompletionComparison_faithfullyFlat (A := A) (Ah := Ah))
      Q.2

-- Proof sketch: combine faithful flatness of `Ah → Ahat` with the generic minimal-prime
-- surjectivity theorem for faithfully flat maps.
/-- Lemma 15.109.1 (1): for a Noetherian local ring `A`, the canonical compatible map from a
chosen henselization `Ah` to the maximal-ideal completion `AdicCompletion (maximalIdeal A) A`
induces a surjection from the minimal primes of the completion onto the minimal primes of `Ah`. -/
theorem henselizationCompletion_surjOn_minimalPrimes :
    Set.SurjOn
      (Ideal.comap (henselizationCompletionComparison A Ah))
      (minimalPrimes ACompletion)
      (minimalPrimes Ah) := by
  change
    Set.SurjOn (Ideal.comap (algebraMap Ah ACompletion))
      (minimalPrimes ACompletion) (minimalPrimes Ah)
  exact
    surjOn_minimalPrimes_of_faithfullyFlat
      (R := Ah) (S := ACompletion)
      (henselizationCompletionComparison_faithfullyFlat (A := A) (Ah := Ah))

-- Proof sketch: the surjection on minimal primes identifies the henselization minimal-prime set
-- with a subset of the image of the completion minimal-prime set.
/-- Lemma 15.109.1 (2): the number of branches of `A`, computed from a chosen henselization `Ah`,
is at most the number of minimal primes of the completion
`AdicCompletion (maximalIdeal A) A`. Since the completion is henselian, this is the number of
branches of the completion. -/
theorem branchNumber_le_completion_minimalPrimes :
    branchNumber A Ah ≤ (minimalPrimes ACompletion).encard := by
  have hsubset :
      minimalPrimes Ah ⊆
        (Ideal.comap (algebraMap Ah ACompletion)) '' (minimalPrimes ACompletion) := by
    intro q hq
    rcases
        (henselizationCompletion_surjOn_minimalPrimes (A := A) (Ah := Ah)).2 hq with
      ⟨Q, hQ, hQq⟩
    exact ⟨Q, hQ, hQq⟩
  rw [branchNumber]
  calc
    (minimalPrimes Ah).encard ≤
        ((Ideal.comap (algebraMap Ah ACompletion)) '' (minimalPrimes ACompletion)).encard :=
      Set.encard_le_encard hsubset
    _ ≤ (minimalPrimes ACompletion).encard :=
      Set.encard_image_le (Ideal.comap (algebraMap Ah ACompletion)) (minimalPrimes ACompletion)

variable [CommRing Ahatsh] [Algebra ACompletion Ahatsh]
variable [IsStrictHenselizationOf ACompletion Ahatsh]

local notation "CompletionTensorStrict" => ACompletion ⊗[Ah] Ash

-- Proof sketch: compare `Ash` with the tensor strict-henselization model over the completion,
-- use faithful flatness of the right tensor inclusion, and then transport across the canonical
-- comparison isomorphism to the chosen completion-side strict henselization `Ahatsh`.
/-- Lemma 15.109.1 (3): for a chosen strict henselization `Ash` of `A` and a chosen strict
henselization `Ahatsh` of the completion `ACompletion = AdicCompletion (maximalIdeal A) A`, the
canonical comparison between these strict henselizations induces the branch-count inequality from
`A` to its completion. -/
theorem geometricBranchNumber_le_completion :
    geometricBranchNumber A Ash ≤ geometricBranchNumber ACompletion Ahatsh := by
  let _ : Algebra Ah Ash := by
    let _ : Algebra Ash Ash := Algebra.id Ash
    let _ : IsScalarTower A Ash Ash := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsHenselizationOf Ash Ash := strict_henselian_self_is_henselization Ash
    exact henselizationMapAlgebra (R := A) (Rh := Ah) (S := Ash) (Sh := Ash)
  have hflat_completion : RingHom.Flat (algebraMap Ah ACompletion) :=
    (henselizationCompletionComparison_faithfullyFlat (A := A) (Ah := Ah)).flat
  have htensor_ff :
      RingHom.FaithfullyFlat (algebraMap Ash CompletionTensorStrict) := by
    exact
      tensor_right_faithfully_flat_of_flat_left
        (R := Ah) (B := ACompletion) (C := Ash) hflat_completion
  obtain ⟨f, hf⟩ :=
    completion_tensor_strict_henselization_compare_bijective
      (A := A) (Ah := Ah) (Ash := Ash) (Ahatsh := Ahatsh)
  let compare : Ash →+* Ahatsh := f.comp (algebraMap Ash CompletionTensorStrict)
  letI : Algebra Ash Ahatsh := compare.toAlgebra
  have hf_ff : RingHom.FaithfullyFlat f :=
    RingHom.FaithfullyFlat.of_bijective hf
  have hcompare_ff : RingHom.FaithfullyFlat (algebraMap Ash Ahatsh) := by
    simpa [compare] using
      RingHom.FaithfullyFlat.stableUnderComposition
        (algebraMap Ash CompletionTensorStrict) f htensor_ff hf_ff
  have hsubset :
      minimalPrimes Ash ⊆ (Ideal.comap (algebraMap Ash Ahatsh)) '' (minimalPrimes Ahatsh) := by
    intro q hq
    rcases
        (surjOn_minimalPrimes_of_faithfullyFlat
          (R := Ash) (S := Ahatsh) hcompare_ff).2 hq with
      ⟨Q, hQ, hQq⟩
    exact ⟨Q, hQ, hQq⟩
  rw [geometricBranchNumber, geometricBranchNumber]
  calc
    (minimalPrimes Ash).encard ≤
        ((Ideal.comap (algebraMap Ash Ahatsh)) '' (minimalPrimes Ahatsh)).encard :=
      Set.encard_le_encard hsubset
    _ ≤ (minimalPrimes Ahatsh).encard :=
      Set.encard_image_le (Ideal.comap (algebraMap Ash Ahatsh)) (minimalPrimes Ahatsh)

end
