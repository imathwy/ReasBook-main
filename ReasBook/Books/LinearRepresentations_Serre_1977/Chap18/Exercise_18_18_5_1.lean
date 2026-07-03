import Mathlib
import LinearRepresentations_Serre_1977.Chap08.Exercise_8_8_2_3
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace Representation

section

open CategoryTheory
open Equiv

local notation "S3" => Equiv.Perm (Fin 3)
local notation "S4" => Equiv.Perm (Fin 4)
local notation "A3" => alternatingGroup (Fin 3)
local notation "A4" => alternatingGroup (Fin 4)
local notation "V4" => alternatingGroup.kleinFour (Fin 4)
local notation "V4InS4" => Subgroup.map (Subgroup.subtype A4) V4

variable {p : ℕ}
variable {k : Type} [Field k] [IsAlgClosed k] [CharP k p]
variable {K : Type} [Field K] [CharZero K]

/-- Helper for Exercise 18-18.5-1: the double-transposition Klein four subgroup is normal in
`S₄`, so quotient notation by `V4InS4` is available throughout this file. -/
local instance : (V4InS4).Normal := _root_.s4DoubleTranspositionKleinFour_normal

/- Domain-style sampling:
* `FDRep.modularCharacterOnPRegularConjClass` is the canonical Brauer-character owner on
  `PRegularConjClass S4 p`, evaluated through `PrimeToPRoot.toFieldLift`.
* `FDRep.ordinaryCharacterOnPRegularConjClass` is the canonical restricted ordinary-character owner
  on the same quotient.
* `simple_modularCharacter_exists_restricted_ordinary_character` is the upstream existence theorem
  in this domain.
* `s4_hasSemidirectDecomposition` is the upstream chapter-level owner of the canonical
  `S₄ = V₄ ⋊ S₃` subgroup decomposition, and `IsPSolvable.of_equiv` is the owner-level bridge for
  transporting `p`-solvability across the induced quotient equivalence.
* Primitive data: a simple `FDRep k S4`, together with the canonical subgroup data `V₄ ≤ S₄`
  and `A₃ ≤ S₃` used to discharge the `p`-solvability hypothesis upstream.
* Derived API: the Brauer class function on `PRegularConjClass S4 p`, the induced
  `p`-solvability of `S₄`, and the existence of an ordinary lift with the same restricted class
  function.

Layer triage:
* source-facing: the existence of an ordinary irreducible representation whose restricted ordinary
  character agrees with the Brauer character of a simple `k[S4]`-module.
* core/canonical: class functions on `PRegularConjClass S4 p`.
* bridge/view: `PrimeToPRoot.toFieldLift`, the canonical quotient equivalence induced by the
  `S₄ = V₄ ⋊ S₃` decomposition, and `IsPSolvable.of_equiv`.
-/

-- Proof sketch: `A₃ ≤ S₃` gives a height-two `p`-solvable series for `S₃`, and the canonical
-- Klein-four subgroup `V₄ ≤ S₄` together with `s4_hasSemidirectDecomposition` identifies
-- `S₄ / V₄ ≃ S₃`, yielding the corresponding `p`-solvable series for `S₄`.
/-- Helper for Exercise 18-18.5-1: the symmetric group `S₃` is `p`-solvable for every prime `p`,
using the normal series `A₃ ◁ S₃`. -/
theorem symmetricGroup_three_isPSolvable (hp : Nat.Prime p) : IsPSolvable p S3 := by
  -- Compute the subgroup and quotient orders in the series `A₃ ◁ S₃`.
  have hA3 : Nat.card A3 = 3 := by
    rw [nat_card_alternatingGroup]
    norm_num
  have hQ : Nat.card (S3 ⧸ A3) = 2 := by
    have h : 6 = Nat.card (S3 ⧸ A3) * 3 := by
      simpa [hA3] using Subgroup.card_eq_card_quotient_mul_card_subgroup A3
    omega
  have hprime3 : Nat.Prime 3 := by decide
  have hprime2 : Nat.Prime 2 := by decide
  -- The kernel term has order `3`, so it is either a `p`-group or a `p'`-group.
  refine ⟨2, ?_⟩
  refine ⟨A3, alternatingGroup.normal, ?_, ?_⟩
  · by_cases hp3 : p = 3
    · right
      have hA3p : Nat.card A3 = p ^ 1 := by
        simpa [hp3] using hA3
      exact IsPGroup.of_card hA3p
    · left
      refine hp.coprime_iff_not_dvd.mpr ?_
      intro hdiv
      rw [hA3] at hdiv
      rcases (Nat.dvd_prime hprime3).mp hdiv with h1 | h3
      · exact hp.ne_one h1
      · exact hp3 h3
  -- The quotient has order `2`, so the same dichotomy closes the final step.
  · refine ⟨⊤, inferInstance, ?_, QuotientGroup.subsingleton_quotient_top⟩
    by_cases hp2 : p = 2
    · right
      have htop : Nat.card (⊤ : Subgroup (S3 ⧸ A3)) = 2 := by
        simp [hQ]
      have htop_p : Nat.card (⊤ : Subgroup (S3 ⧸ A3)) = p ^ 1 := by
        simpa [hp2] using htop
      exact IsPGroup.of_card htop_p
    · left
      refine hp.coprime_iff_not_dvd.mpr ?_
      intro hdiv
      have hdiv' : p ∣ 2 := by
        simpa [hQ] using hdiv
      rcases (Nat.dvd_prime hprime2).mp hdiv' with h1 | h2
      · exact hp.ne_one h1
      · exact hp2 h2

/-- Helper for Exercise 18-18.5-1: the normal Klein four subgroup of double transpositions in
`S₄` has cardinality `4`. -/
lemma symmetricGroup_four_kleinFour_card : Nat.card V4InS4 = 4 := by
  -- Compare the embedded subgroup in `S₄` with the standard Klein four subgroup inside `A₄`.
  have hcard_map : Nat.card V4InS4 = Nat.card V4 := by
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective V4
        (Subgroup.subtype A4) (Subgroup.subtype_injective _)).toEquiv.symm
  have hFin4 : Nat.card (Fin 4) = 4 := by
    simp
  rw [hcard_map]
  simpa using alternatingGroup.kleinFour_card_of_card_eq_four hFin4

/-- Helper for Exercise 18-18.5-1: the quotient `S₄ / V₄` is `p`-solvable because the canonical
semidirect-product decomposition identifies it with `S₃`. -/
theorem symmetricGroup_four_quotient_isPSolvable (hp : Nat.Prime p) :
    IsPSolvable p (S4 ⧸ V4InS4) := by
  -- Route correction: the quotient is not analyzed by ad hoc generators; we transport the already
  -- proved `p`-solvability of `S₃` through the chapter-level semidirect decomposition.
  obtain ⟨H, e, hcomp⟩ := s4_hasSemidirectDecomposition
  let hHV : H.IsComplement' V4InS4 := hcomp.symm
  exact
    IsPSolvable.of_equiv
      (e.symm.trans hHV.QuotientMulEquiv.symm)
      (symmetricGroup_three_isPSolvable hp)

/-- Helper for Exercise 18-18.5-1: the symmetric group `S₄` is `p`-solvable for every prime `p`,
using the normal Klein four subgroup and the quotient `S₄ / V₄ ≃ S₃`. -/
theorem symmetricGroup_four_isPSolvable (hp : Nat.Prime p) : IsPSolvable p S4 := by
  -- The source-faithful skeleton is `V₄ ◁ S₄` with quotient identified with `S₃`.
  have hV4 : Nat.card V4InS4 = 4 := symmetricGroup_four_kleinFour_card
  have hquot : IsPSolvable p (S4 ⧸ V4InS4) := symmetricGroup_four_quotient_isPSolvable hp
  have hprime2 : Nat.Prime 2 := by decide
  rcases hquot with ⟨h, hquot⟩
  refine ⟨h + 1, ?_⟩
  refine ⟨V4InS4, inferInstance, ?_, hquot⟩
  -- The kernel has order `4 = 2²`, so only the split `p = 2` versus `p ≠ 2` remains.
  by_cases hp2 : p = 2
  · right
    have hV4p : Nat.card V4InS4 = p ^ 2 := by
      simpa [hp2] using hV4
    exact IsPGroup.of_card hV4p
  · left
    refine hp.coprime_iff_not_dvd.mpr ?_
    intro hdiv
    rw [hV4] at hdiv
    have hpow : p ∣ 2 ^ 2 := by
      simpa [pow_two] using hdiv
    have hdiv2 : p ∣ 2 := hp.dvd_of_dvd_pow hpow
    rcases (Nat.dvd_prime hprime2).mp hdiv2 with h1 | h2
    · exact hp.ne_one h1
    · exact hp2 h2

-- Proof sketch: the primitive source input is a simple `k[S₄]`-module, not an arbitrary class
-- function plus a witness that it comes from one. The conclusion is stated directly on the
-- canonical Brauer/ordinary character owners on `PRegularConjClass S4 p`, and the only extra
-- group-theoretic input is the canonical `p`-solvability of `S₄` recovered above from the
-- chapter-level decomposition `S₄ = V₄ ⋊ S₃`.
/-- Exercise 18-18.5-1: for the symmetric group `S₄` and a prime characteristic `p`, the Brauer
character of every simple finite-dimensional `k[S₄]`-module is the restriction to the `p`-regular
locus of the ordinary character of some simple finite-dimensional `K[S₄]`-module. In the source,
the interesting cases are `p = 2` and `p = 3`. -/
theorem symmetricGroup_four_simple_modularCharacter_exists_restricted_ordinary_character
    (hp : Nat.Prime p)
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (S : FDRep k S4) (hS : Simple S) :
    ∃ X : FDRep K S4,
      Simple X ∧
        FDRep.modularCharacterOnPRegularConjClass S (PrimeToPRoot.toFieldLift lift) =
          FDRep.ordinaryCharacterOnPRegularConjClass p X := by
  obtain ⟨X, hX, hχ⟩ :=
    simple_modularCharacter_exists_restricted_ordinary_character
      lift S hp (symmetricGroup_four_isPSolvable hp) hlift hS
  exact ⟨X, hX, hχ⟩

end

end Representation
