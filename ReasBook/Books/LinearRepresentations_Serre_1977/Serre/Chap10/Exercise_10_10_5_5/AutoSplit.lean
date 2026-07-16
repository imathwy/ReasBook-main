import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap01.Definition_1_1_2_1
import LinearRepresentations_Serre_1977.Serre.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Serre.Chap02.Proposition_2_2_4_1
import LinearRepresentations_Serre_1977.Serre.Chap08.Theorem_8_8_5_2
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_2_1
import LinearRepresentations_Serre_1977.Serre.Chap09.Theorem_9_9_2_1
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_4
import LinearRepresentations_Serre_1977.Serre.Chap10.Lemma_10_10_3_3
import LinearRepresentations_Serre_1977.Serre.Chap11.Theorem_11_11_2_1
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_1

noncomputable section
universe u
open scoped Representation SubgroupInduction
namespace Representation
section
variable {G : Type} [Group G] [Finite G]
namespace Subgroup

/-- Helper for Exercise 10-10.5-5: the order of a `p`-regular element divides the prime-to-`p`
part of `|G|`. -/
theorem orderOf_dvd_ordCompl_card_of_isPRegular_local
    (p : Nat.Primes) {s : G} (hs : IsPRegular (p : ℕ) s) :
    orderOf s ∣ ordCompl[(p : ℕ)] (Nat.card G) := by
  letI : Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩
  -- A `p`-regular element has order prime to `p`, so its order survives inside the prime-to-`p`
  -- factor of `|G|`.
  have hs_not_dvd : ¬ (p : ℕ) ∣ orderOf s := by
    exact (isPRegular_iff_not_dvd_orderOf (p := (p : ℕ)) s).1 hs
  exact Nat.dvd_ordCompl_of_dvd_not_dvd (orderOf_dvd_natCard s) hs_not_dvd
end Subgroup
end
end Representation
end
