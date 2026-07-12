import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open HomogeneousIdeal

universe u v w

section

variable {S : Type u} [CommRing S]
variable {σ : Type v} [SetLike σ S] [AddSubgroupClass σ S]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable (s : Set S)

/- Domain triage:
* source-facing: a set of positive-degree homogeneous generators.
* core/canonical owners: `HomogeneousIdeal.irrelevant`, `HomogeneousIdeal.irrelevant_eq_span`,
  and `HomogeneousIdeal.toIdeal_irrelevant_le`.
* bridge/view: the inclusion `𝒜₊.toIdeal ≤ Ideal.span s` used by the `Proj` API, and the indexed
  family presentation via `Set.range`.

Primitive data are the set `s : Set S` and the positive-degree homogeneous membership condition on
its elements. The family presentation `f : ι → S` is derived API through `Set.range f` and should
not be the owner-level public input.

Relevant owner declarations sampled for this refinement:
* `HomogeneousIdeal.irrelevant`
* `HomogeneousIdeal.irrelevant_eq_span`
* `HomogeneousIdeal.toIdeal_irrelevant_le`
* `Ideal.homogeneous_span`
-/

/-- A set of positive-degree homogeneous elements always spans an ideal inside the irrelevant
ideal. -/
lemma span_le_irrelevant_of_pos_homogeneous
    (hs_deg : ∀ ⦃x⦄, x ∈ s → ∃ n > 0, x ∈ 𝒜 n) :
    Ideal.span s ≤ 𝒜₊.toIdeal := by
  refine Ideal.span_le.2 ?_
  intro x hx
  rcases hs_deg hx with ⟨n, hn, hx_n⟩
  exact mem_irrelevant_of_mem 𝒜 hn hx_n

/-- Library-facing bridge form of Lemma 10.58.1: `Proj`-style arguments naturally use the
inclusion `𝒜₊.toIdeal ≤ Ideal.span s`. -/
theorem homogeneous_adjoin_eq_top_iff_irrelevant_le_span
    (hs_deg : ∀ ⦃x⦄, x ∈ s → ∃ n > 0, x ∈ 𝒜 n) :
    Algebra.adjoin (𝒜 0) s = ⊤ ↔ 𝒜₊.toIdeal ≤ Ideal.span s := by
  classical
  let B : Subalgebra (𝒜 0) S := Algebra.adjoin (𝒜 0) s
  constructor
  · intro hs_top
    rw [HomogeneousIdeal.toIdeal_irrelevant_le]
    intro n hn x hx
    have hspan_all :
        ∀ ⦃y : S⦄, y ∈ Algebra.adjoin (𝒜 0) s →
          y - GradedRing.projZeroRingHom 𝒜 y ∈ Ideal.span s := by
      intro y hy
      induction hy using Algebra.adjoin_induction with
      | mem y hy =>
          rcases hs_deg hy with ⟨m, hm, hym⟩
          have hy_zero : GradedRing.projZeroRingHom 𝒜 y = 0 := by
            rw [GradedRing.projZeroRingHom_apply, DirectSum.decompose_of_mem_ne 𝒜 hym hm.ne']
          simpa [hy_zero] using (Ideal.subset_span hy : y ∈ Ideal.span s)
      | algebraMap r =>
          have hr_proj :
              GradedRing.projZeroRingHom 𝒜 (algebraMap (𝒜 0) S r) = algebraMap (𝒜 0) S r := by
            change GradedRing.projZeroRingHom 𝒜 (r : S) = (r : S)
            exact congrArg ((↑) : 𝒜 0 → S) (GradedRing.projZeroRingHom'_apply_coe 𝒜 r)
          rw [hr_proj, sub_self]
          exact Ideal.zero_mem (Ideal.span s)
      | add a b ha hb ha_span hb_span =>
          simpa [map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            Ideal.add_mem (Ideal.span s) ha_span hb_span
      | mul a b ha hb ha_span hb_span =>
          have hmul_left :
              a * (b - GradedRing.projZeroRingHom 𝒜 b) ∈ Ideal.span s :=
            Ideal.mul_mem_left (Ideal.span s) a hb_span
          have hmul_right :
              (a - GradedRing.projZeroRingHom 𝒜 a) * GradedRing.projZeroRingHom 𝒜 b ∈
                Ideal.span s :=
            Ideal.mul_mem_right (GradedRing.projZeroRingHom 𝒜 b) (Ideal.span s) ha_span
          simpa [map_mul, sub_eq_add_neg, left_distrib, right_distrib, mul_add, add_mul,
            add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
            Ideal.add_mem (Ideal.span s) hmul_left hmul_right
    have hx_adjoin : x ∈ Algebra.adjoin (𝒜 0) s := by
      rw [hs_top]
      exact trivial
    have hx_span : x - GradedRing.projZeroRingHom 𝒜 x ∈ Ideal.span s := hspan_all hx_adjoin
    have hx_zero : GradedRing.projZeroRingHom 𝒜 x = 0 := by
      rw [GradedRing.projZeroRingHom_apply]
      exact DirectSum.decompose_of_mem_ne 𝒜 hx (Nat.ne_of_gt hn)
    simpa [hx_zero] using hx_span
  · intro hirr
    have hhom : ∀ n : ℕ, ∀ x : S, x ∈ 𝒜 n → x ∈ B := by
      intro n
      refine Nat.strong_induction_on n ?_
      intro n ih x hx
      cases n with
      | zero =>
          exact B.algebraMap_mem ⟨x, hx⟩
      | succ n =>
          have hx_span : x ∈ Ideal.span s :=
            hirr (mem_irrelevant_of_mem 𝒜 (Nat.succ_pos _) hx)
          rw [Ideal.span, Finsupp.span_eq_range_linearCombination] at hx_span
          rw [LinearMap.mem_range] at hx_span
          obtain ⟨l, rfl⟩ := hx_span
          have hproj :
              GradedRing.proj 𝒜 (n + 1)
                  (Finsupp.linearCombination S (fun z : s ↦ (z : S)) l) =
                Finsupp.linearCombination S (fun z : s ↦ (z : S)) l := by
            rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 hx]
          rw [← hproj, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
          refine B.sum_mem ?_
          intro z hz
          rcases hs_deg z.2 with ⟨d, hd, hzd⟩
          by_cases hdn : d ≤ n + 1
          · rw [smul_eq_mul, GradedRing.proj_apply,
              DirectSum.coe_decompose_mul_of_right_mem_of_le 𝒜 hzd hdn]
            exact B.mul_mem
              (ih (n + 1 - d) (Nat.sub_lt (Nat.succ_pos _) hd) _
                (DirectSum.decompose 𝒜 (l z) (n + 1 - d)).2)
              (Algebra.subset_adjoin z.2)
          · rw [smul_eq_mul, GradedRing.proj_apply,
              DirectSum.coe_decompose_mul_of_right_mem_of_not_le 𝒜 hzd hdn]
            exact B.zero_mem
    change B = ⊤
    rw [← top_le_iff]
    intro x hx
    rw [← DirectSum.sum_support_decompose 𝒜 x]
    exact B.sum_mem fun i hi ↦ hhom i _ (DirectSum.decompose 𝒜 x i).2

/-- Lemma 10.58.1 (Stacks, Tag `07Z4`): a set of positive-degree homogeneous elements generates
the graded ring as an algebra over its degree-zero part if and only if it generates the irrelevant
ideal as an ideal. -/
-- Proof sketch: for the forward implication, every element of the irrelevant ideal is a polynomial
-- in the chosen generators with vanishing constant term, so it lies in the ideal they generate.
-- For the reverse implication, argue by induction on degree for homogeneous elements: write a
-- positive-degree homogeneous element as an ideal combination of the generators and recursively
-- expand the lower-degree coefficients as polynomials over `𝒜 0`.
@[stacks 07Z4]
theorem homogeneous_adjoin_eq_top_iff_span_eq_irrelevant
    (hs_deg : ∀ ⦃x⦄, x ∈ s → ∃ n > 0, x ∈ 𝒜 n) :
    Algebra.adjoin (𝒜 0) s = ⊤ ↔ Ideal.span s = 𝒜₊.toIdeal := by
  constructor
  · intro hs_top
    exact le_antisymm
      (span_le_irrelevant_of_pos_homogeneous 𝒜 s hs_deg)
      ((homogeneous_adjoin_eq_top_iff_irrelevant_le_span 𝒜 s hs_deg).1 hs_top)
  · intro hspan
    exact (homogeneous_adjoin_eq_top_iff_irrelevant_le_span 𝒜 s hs_deg).2 hspan.symm.le

end
