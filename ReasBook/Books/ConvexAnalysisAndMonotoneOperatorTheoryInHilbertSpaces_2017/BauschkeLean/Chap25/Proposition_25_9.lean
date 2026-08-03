import BauschkeLean.Chap06.Proposition_6_45
import BauschkeLean.Chap06.Proposition_6_47
import BauschkeLean.Chap20.Example_20_26
import BauschkeLean.Chap20.Proposition_20_22
import BauschkeLean.Chap25.Corollary_25_5
import BauschkeLean.Chap25.Proposition_25_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise SetValuedOperator
open Set

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Source/core/bridge triage:
-- `source-facing`: Proposition 25.9 is the chapter implication from maximal monotonicity to local
--   maximal monotonicity.
-- `core/canonical`: the owner abstractions are `Maximal IsMonotone A`,
--   `A.IsLocallyMaximallyMonotone`, and the bounded closed convex criterion from
--   `Proposition_25_8.lean`.
-- `bridge/view`: the proof localizes on the codomain by passing to `A⁻¹ + N[C]`, so the normal
--   cone and inverse-operator APIs remain proof-local rather than becoming a second public owner.

omit [CompleteSpace H] in
private theorem normalCone_dom_eq {C : Set H} :
    SetValuedOperator.dom (N[C] : SetValuedOperator H H) = C := by
  ext x
  by_cases hx : x ∈ C
  · constructor
    · intro _
      exact hx
    · intro _
      change (N[C] x).Nonempty
      refine ⟨0, ?_⟩
      simp [Set.normalCone_of_mem hx]
  · constructor
    · intro hxdom
      change (N[C] x).Nonempty at hxdom
      rw [Set.normalCone_of_not_mem hx] at hxdom
      simp at hxdom
    · intro hxC
      exact (hx hxC).elim

/-- Proposition 25.9: every maximally monotone set-valued operator is locally maximally monotone. -/
theorem Maximal.isLocallyMaximallyMonotone
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) :
    A.IsLocallyMaximallyMonotone := by
  rw [isLocallyMaximallyMonotone_iff_forall_bounded_closed_convex (Maximal.isMonotone hA)]
  intro C _ hC_closed hC_convex hC_range x u huInt hxu
  rcases hC_range with ⟨w, hwInt, hwRange⟩
  have hC_nonempty : C.Nonempty := ⟨u, interior_subset huInt⟩
  let Ainv : H → Set H := A⁻¹
  let NC : H → Set H := N[C]
  have hAinv : Maximal IsMonotone Ainv := by
    simpa [Ainv] using (Maximal.inverse hA)
  have hNC : Maximal IsMonotone NC :=
    Set.normalCone_isMaximallyMonotone hC_nonempty hC_closed hC_convex
  have hsum : Maximal IsMonotone (Ainv + NC) := by
    apply Maximal.add_of_sumRegularity hAinv hNC
    right
    left
    refine ⟨w, ?_⟩
    rw [Set.mem_inter_iff]
    refine ⟨?_, ?_⟩
    · rw [show Ainv = A⁻¹ by rfl, SetValuedOperator.mem_dom_iff]
      rcases (SetValuedOperator.mem_range_iff A w).1 hwRange with ⟨y, hy⟩
      exact ⟨y, (SetValuedOperator.mem_inverse_iff A w y).2 hy⟩
    · simpa [NC, normalCone_dom_eq] using hwInt
  have huC : u ∈ C := interior_subset huInt
  have hNu :
      N[C] u = ({0} : Set H) :=
    (Set.mem_interior_iff_normalCone_eq_singleton_zero_of_convex
      hC_convex ⟨u, huInt⟩ huC).1 huInt
  have hNCu : NC u = ({0} : Set H) := by
    simpa [NC] using hNu
  have hx_not_mem : x ∉ (Ainv + NC) u := by
    intro hx
    rcases Set.mem_add.mp hx with ⟨a, ha, b, hb, hab⟩
    have hb_zero : b = 0 := by
      have : b ∈ ({0} : Set H) := by simpa [hNCu] using hb
      simpa using this
    have ha' : a = x := by
      calc
        a = a + 0 := by simp
        _ = x := by simpa [hb_zero] using hab
    have hxAinv : x ∈ A⁻¹ u := by simpa [ha'] using ha
    exact hxu <| (SetValuedOperator.mem_inverse_iff A u x).1 hxAinv
  have hwitness :
      ∃ z q : H,
        q ∈ (Ainv + NC) z ∧ ⟪u - z, x - q⟫_ℝ < 0 := by
    by_contra hNo
    apply hx_not_mem
    refine (Maximal.mem_iff hsum u x).2 ?_
    intro z q hq
    by_contra hlt
    exact hNo ⟨z, q, hq, lt_of_not_ge hlt⟩
  rcases hwitness with ⟨z, q, hq, hpair_neg⟩
  rcases Set.mem_add.mp hq with ⟨a, haAinv, b, hbN, hqeq⟩
  have haAinv' : a ∈ A⁻¹ z := by
    simpa [Ainv] using haAinv
  have hbN' : b ∈ N[C] z := by
    simpa [NC] using hbN
  have hzC : z ∈ C := by
    by_contra hzC
    rw [Set.normalCone_of_not_mem hzC] at hbN'
    simp at hbN'
  have hzA : z ∈ A a := (SetValuedOperator.mem_inverse_iff A z a).1 haAinv'
  have hb_nonpos : ⟪u - z, b⟫_ℝ ≤ 0 := by
    rw [Set.normalCone_of_mem hzC] at hbN'
    exact (innerSupremumOn_sub_singleton_le_zero_iff).1 hbN' u huC
  have hsplit :
      ⟪u - z, x - q⟫_ℝ = ⟪u - z, x - a⟫_ℝ - ⟪u - z, b⟫_ℝ := by
    have hxaqb : x - q = (x - a) - b := by
      rw [← hqeq]
      abel_nf
    rw [hxaqb, inner_sub_right]
  have hpair_aux : ⟪u - z, x - a⟫_ℝ < 0 := by
    have hle : ⟪u - z, x - a⟫_ℝ ≤ ⟪u - z, x - q⟫_ℝ := by
      rw [hsplit]
      linarith
    exact lt_of_le_of_lt hle hpair_neg
  refine ⟨a, z, hzC, hzA, ?_⟩
  simpa [real_inner_comm] using hpair_aux

end SetValuedOperator
