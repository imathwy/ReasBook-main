import BauschkeLean.Chap21.Corollary_21_14
import BauschkeLean.Chap25.Proposition_25_21

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open scoped InnerProductSpace Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Theorem 25.23 records the Brézis--Haraux closure/interior formulas under the
  chapter's common Fitzpatrick-domain hypothesis on `range A × range B`.
- `core/canonical`: the Fitzpatrick owner is `F[_]`, and the range-side closure/interior owner is
  `A.sndImageDomFitzpatrick` from Chapter 21.
- `bridge/view`: the source hypothesis below is kept as a named proposition because Chapter 25 uses
  it directly, while the actual range identities are routed through the Chapter 21 projection API.

Primitive data: the operators `A`, `B`, monotonicity of each, maximal monotonicity of `A + B`,
and the common Fitzpatrick-domain hypothesis on `A.range × B.range`.
Derived API: the closure and interior identities for `(A + B).range`. -/

/-- The Chapter 25 common Fitzpatrick-domain hypothesis on `A.range × B.range`: every
`u ∈ range A` and `v ∈ range B` admit a common first coordinate `x` such that `(x, u) ∈ dom F_A`
and `(x, v) ∈ dom F_B`. -/
def FitzpatrickDomainCondition (A B : SetValuedOperator H H) : Prop :=
  ∀ u ∈ A.range, ∀ v ∈ B.range, ∃ x : H,
    (x, u) ∈ ERealFunction.dom (F[A]) ∧ (x, v) ∈ ERealFunction.dom (F[B])

omit [CompleteSpace H] in
/-- Helper for Theorem 25.23: two Fitzpatrick-domain witnesses over the same first coordinate
combine into a Fitzpatrick-domain witness for the sum operator. -/
private theorem memDomFitzpatrickAddOfSplit
    {A B : SetValuedOperator H H} (hA : A.IsMonotone) (hB : B.IsMonotone)
    {x u v : H} (hu : (x, u) ∈ ERealFunction.dom (F[A]))
    (hv : (x, v) ∈ ERealFunction.dom (F[B])) :
    (x, u + v) ∈ ERealFunction.dom (F[(A + B)]) := by
  -- Turn Fitzpatrick-domain membership into finiteness of the two summand values.
  rw [ERealFunction.mem_dom_iff]
  have hAu_top : F[A] (x, u) ≠ ⊤ := (ERealFunction.mem_dom_iff_ne_top _ _).1 hu
  have hBv_top : F[B] (x, v) ≠ ⊤ := (ERealFunction.mem_dom_iff_ne_top _ _).1 hv
  have hsum_lt_top : F[A] (x, u) + F[B] (x, v) < ⊤ := by
    exact lt_top_iff_ne_top.mpr (EReal.add_ne_top hAu_top hBv_top)
  have hle_inf :
      F[(A + B)] (x, u + v) ≤
        (((fun z : H ↦ F[A] (x, z)) □ (fun z : H ↦ F[B] (x, z))) (u + v)) :=
    SetValuedOperator.fitzpatrickFunction_add_le_infimalConvolution_fibers
      (A := A) (B := B) hA hB x (u + v)
  have hle_sum : F[(A + B)] (x, u + v) ≤ F[A] (x, u) + F[B] (x, v) := by
    -- Evaluate the infimal convolution at the concrete split `u`.
    rw [ERealFunction.infimalConvolution_apply] at hle_inf
    exact le_trans hle_inf <| by
      simpa using iInf_le (fun z : H ↦ F[A] (x, z) + F[B] (x, (u + v) - z)) u
  -- A finite upper bound proves that the Fitzpatrick value of `A + B` is still below `⊤`.
  exact lt_of_le_of_lt hle_sum hsum_lt_top

/-- Helper for Theorem 25.23: the common Fitzpatrick-domain hypothesis sends every element of
`A.range + B.range` into `(A + B).sndImageDomFitzpatrick`. -/
private theorem rangeSum_subset_sndImageDomFitzpatrickAddOfFitzpatrickDomainCondition
    {A B : SetValuedOperator H H} (hA : A.IsMonotone) (hB : B.IsMonotone)
    (hfitz : FitzpatrickDomainCondition A B) :
    A.range + B.range ⊆ (A + B).sndImageDomFitzpatrick := by
  intro w hw
  rcases Set.mem_add.mp hw with ⟨u, huA, v, hvB, rfl⟩
  rcases hfitz u huA v hvB with ⟨x, hxu, hxv⟩
  have hdom : (x, u + v) ∈ ERealFunction.dom (F[(A + B)]) :=
    memDomFitzpatrickAddOfSplit (A := A) (B := B) hA hB hxu hxv
  -- Package the sum witness as a second-coordinate image point of `dom (F[A + B])`.
  exact ⟨(x, u + v), hdom, rfl⟩

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 25.23: every point of `(A + B).range` splits into a sum of one point from
`A.range` and one point from `B.range`. -/
private theorem rangeAdd_subset_rangeSum
    {A B : SetValuedOperator H H} :
    (A + B).range ⊆ A.range + B.range := by
  intro w hw
  rcases (SetValuedOperator.mem_range_iff (A := A + B) (y := w)).1 hw with ⟨x, hx⟩
  rcases Set.mem_add.mp hx with ⟨u, hu, v, hv, rfl⟩
  -- Repackage the two split values as witnesses for membership in `A.range + B.range`.
  exact Set.mem_add.2 ⟨u,
    (SetValuedOperator.mem_range_iff (A := A) (y := u)).2 ⟨x, hu⟩,
    v,
    (SetValuedOperator.mem_range_iff (A := B) (y := v)).2 ⟨x, hv⟩,
    rfl⟩

/-- Theorem 25.23 (1): let `A` and `B` be monotone operators on a real Hilbert space such that
`A + B` is maximally monotone. Suppose that for every `u ∈ ran A` and `v ∈ ran B`, there exists
`x` such that `(x, u) ∈ dom F_A` and `(x, v) ∈ dom F_B`, formalized by
`FitzpatrickDomainCondition A B`. Then
`closure (ran (A + B)) = closure (ran A + ran B)`, formalized as
`closure (A + B).range = closure (A.range + B.range)`. -/
theorem closure_range_add_eq_closure_range_sum_of_fitzpatrick_domain_condition
    {A B : SetValuedOperator H H} (hA : A.IsMonotone) (hB : B.IsMonotone)
    (hAB_max : Maximal IsMonotone (A + B)) (hfitz : FitzpatrickDomainCondition A B) :
    closure (A + B).range = closure (A.range + B.range) := by
  -- The source proof compares both sides through the Chapter 21 projection
  -- `(A + B).sndImageDomFitzpatrick`.
  refine Set.Subset.antisymm ?_ ?_
  · -- The reverse inclusion is always true because a value of `A + B` splits into two range points.
    exact closure_mono (rangeAdd_subset_rangeSum (A := A) (B := B))
  · -- The Fitzpatrick-domain hypothesis puts `A.range + B.range` inside the Chapter 21 projection.
    calc
      closure (A.range + B.range) ⊆ closure ((A + B).sndImageDomFitzpatrick) := by
        exact closure_mono
          (rangeSum_subset_sndImageDomFitzpatrickAddOfFitzpatrickDomainCondition
            (A := A) (B := B) hA hB hfitz)
      _ = closure (A + B).range := by
        symm
        exact closure_range_eq_closure_snd_image_dom_fitzpatrick_of_maximal
          (A := A + B) hAB_max

/-- Theorem 25.23 (2): let `A` and `B` be monotone operators on a real Hilbert space such that
`A + B` is maximally monotone. Suppose that for every `u ∈ ran A` and `v ∈ ran B`, there exists
`x` such that `(x, u) ∈ dom F_A` and `(x, v) ∈ dom F_B`, formalized by
`FitzpatrickDomainCondition A B`. Then
`interior (ran (A + B)) = interior (ran A + ran B)`, formalized as
`interior (A + B).range = interior (A.range + B.range)`. -/
theorem interior_range_add_eq_interior_range_sum_of_fitzpatrick_domain_condition
    {A B : SetValuedOperator H H} (hA : A.IsMonotone) (hB : B.IsMonotone)
    (hAB_max : Maximal IsMonotone (A + B)) (hfitz : FitzpatrickDomainCondition A B) :
    interior (A + B).range = interior (A.range + B.range) := by
  -- The same two subset lemmas as in the closure theorem pass through interiors by monotonicity.
  refine Set.Subset.antisymm ?_ ?_
  · -- The always-true range inclusion yields the forward interior inclusion.
    exact interior_mono (rangeAdd_subset_rangeSum (A := A) (B := B))
  · -- The Fitzpatrick-domain hypothesis supplies the reverse inclusion through Chapter 21.
    calc
      interior (A.range + B.range) ⊆ interior ((A + B).sndImageDomFitzpatrick) := by
        exact interior_mono
          (rangeSum_subset_sndImageDomFitzpatrickAddOfFitzpatrickDomainCondition
            (A := A) (B := B) hA hB hfitz)
      _ = interior (A + B).range := by
        symm
        exact interior_range_eq_interior_snd_image_dom_fitzpatrick_of_maximal
          (A := A + B) hAB_max

end SetValuedOperator
