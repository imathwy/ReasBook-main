import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap15.Situation_15_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits CommRingCat CategoryTheory.Limits.Types

universe u

section

variable {B A A' : Type u}
variable [CommRing B] [CommRing A] [CommRing A']

/- Domain-style sampling for 15.6.3:
- primary domain: integrality of commutative-ring maps and its stability under base change;
- sampled owner declarations:
  `RingHom.IsIntegral`,
  `RingHom.isIntegral_isStableUnderBaseChange`,
  `SurjectiveRingPullbackSituation`,
  `SurjectiveRingPullbackSituation.bprimeToAprime`;
- best owner abstraction: the mathematical property is owned by `RingHom.IsIntegral`, and the
  base-change theorem is the canonical owner declaration
  `RingHom.isIntegral_isStableUnderBaseChange`; the chapter pullback situation is only a
  source-facing bridge packaging the specific fibre-product square from Situation `15.6.1`;
- primitive data at the core layer: a ring map and the proposition that it is integral;
- derived bridge API in this file: for `S : SurjectiveRingPullbackSituation B A A'`, the map
  `S.bprimeToAprime` is derived from the pullback owner data and inherits integrality from the core
  base-change theorem.

Source/core/bridge triage:
- `source-facing`: the chapter specialization to Situation `15.6.1`;
- `core/canonical`: `RingHom.IsIntegral` and `RingHom.isIntegral_isStableUnderBaseChange`;
- `bridge/view`: `SurjectiveRingPullbackSituation` and the specialized theorem below. -/

/- Lemma 15.6.3 is a chapter-level pullback instance of the canonical base-change theorem
`RingHom.isIntegral_isStableUnderBaseChange`. -/
recall RingHom.isIntegral_isStableUnderBaseChange

/-- Helper for Lemma 15.6.3: a compatible pair `(b, a')` in the fiber product gives an element of
`A'` that is integral over the pullback projection `B' → A'`. -/
lemma bprimeToAprime_isIntegralElem_of_compatible_pair
    (S : SurjectiveRingPullbackSituation B A A') (b : B) (a' : A')
    (h : S.fromAprime a' = S.toA b) :
    S.bprimeToAprime.IsIntegralElem a' := by
  -- View the pullback square on underlying types so the universal property produces the pair.
  have hpb := CategoryTheory.Functor.map_isPullback (F := forget CommRingCat) S.isPullback
  obtain ⟨x, -, hx⟩ := Types.exists_of_isPullback hpb b a' h.symm
  -- The element `a'` lies in the image of `B' → A'`, hence is integral by the linear polynomial.
  rw [← hx]
  exact RingHom.isIntegralElem_map S.bprimeToAprime

/-- Helper for Lemma 15.6.3: every element of `ker(A' → A)` is integral over the pullback
projection `B' → A'`. -/
lemma bprimeToAprime_isIntegralElem_of_mem_ker_fromAprime
    (S : SurjectiveRingPullbackSituation B A A') (k : A')
    (hk : S.fromAprime k = 0) :
    S.bprimeToAprime.IsIntegralElem k := by
  -- The kernel element is represented by the compatible pair `(0, k)`.
  have hzero : S.fromAprime k = S.toA 0 := by
    simpa using hk
  simpa using bprimeToAprime_isIntegralElem_of_compatible_pair S 0 k hzero

/-- Helper for Lemma 15.6.3: if `S.fromAprime x` satisfies a monic polynomial over `B`, then `x`
is integral over the pullback projection `B' → A'`. -/
lemma bprimeToAprime_isIntegralElem_of_integral_image
    (S : SurjectiveRingPullbackSituation B A A') (x : A') (p : Polynomial B)
    (hp : p.Monic) (hpx : Polynomial.eval₂ S.toA (S.fromAprime x) p = 0) :
    S.bprimeToAprime.IsIntegralElem x := by
  by_cases hA : Subsingleton A
  · -- If `A` is trivial, every element of `A'` lands in the kernel and the kernel helper closes.
    have hxker : S.fromAprime x = 0 := Subsingleton.elim _ _
    exact bprimeToAprime_isIntegralElem_of_mem_ker_fromAprime S x hxker
  · let _ : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
    -- Lift the mapped witness polynomial along the surjection `A' → A`.
    have hp_lifts : Polynomial.map S.toA p ∈ Polynomial.lifts S.fromAprime := by
      rw [Polynomial.mem_lifts]
      exact Polynomial.map_surjective S.fromAprime S.fromAprime_surjective _
    have hp_map_monic : (Polynomial.map S.toA p).Monic := by
      simpa using hp.map S.toA
    obtain ⟨q, hqmap, _, hqmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      (f := S.fromAprime) (p := Polynomial.map S.toA p) hp_lifts hp_map_monic
    -- Evaluating the lifted polynomial at `x` lands in the kernel of `A' → A`.
    have hqeval_mem_ker : S.fromAprime (Polynomial.eval x q) = 0 := by
      rw [← Polynomial.eval_map_apply, hqmap]
      simpa [Polynomial.eval₂_eq_eval_map] using hpx
    have hqeval_integral :
        S.bprimeToAprime.IsIntegralElem (Polynomial.eval x q) :=
      bprimeToAprime_isIntegralElem_of_mem_ker_fromAprime S (Polynomial.eval x q) hqeval_mem_ker
    have hcoeff_integral : ∀ i, S.bprimeToAprime.IsIntegralElem (q.coeff i) := by
      intro i
      have hcoeff_eq : S.fromAprime (q.coeff i) = S.toA (p.coeff i) := by
        simpa [Polynomial.coeff_map] using congrArg (fun r : Polynomial A ↦ r.coeff i) hqmap
      exact bprimeToAprime_isIntegralElem_of_compatible_pair S (p.coeff i) (q.coeff i) hcoeff_eq
    -- Switch to the algebra form of integrality and use the lifted monic polynomial criterion.
    let _ : Algebra (↑S.Bprime) A' := (show ↑S.Bprime →+* A' from S.bprimeToAprime).toAlgebra
    change IsIntegral (↑S.Bprime) x
    have hq_ne_one : q ≠ 1 := by
      intro hq1
      rw [hq1] at hqeval_mem_ker
      simp at hqeval_mem_ker
    have hq_natDegree_ne_zero : q.natDegree ≠ 0 := by
      exact Nat.ne_of_gt ((hqmonic.natDegree_pos).2 hq_ne_one)
    refine IsIntegral.of_aeval_monic_of_isIntegral_coeff hqmonic hq_natDegree_ne_zero ?_ ?_
    · simpa [IsIntegral] using hqeval_integral
    · intro i
      simpa [IsIntegral] using hcoeff_integral i

/-- Lemma 15.6.3: specialized bridge from Situation `15.6.1` to the canonical base-change owner.
If `B → A` is integral in a surjective ring pullback situation, then the induced projection
`B' = B ×_A A' → A'` is integral. -/
-- Route correction: the tensor-product base-change theorem recalled above does not apply directly
-- to this fiber-product ring, so we follow the source pullback argument on integral elements.
theorem isIntegral_pullback_projection_of_surjective_of_isIntegral
    (S : SurjectiveRingPullbackSituation B A A') (hBA : S.toA.IsIntegral) :
    S.bprimeToAprime.IsIntegral := by
  intro x
  -- Start from an integral polynomial for the image of `x` in `A`.
  obtain ⟨p, hp, hpx⟩ := hBA (S.fromAprime x)
  -- The lifted-polynomial helper converts that witness back to integrality over `B' → A'`.
  exact bprimeToAprime_isIntegralElem_of_integral_image S x p hp hpx

end
