import BauschkeLean.Chap25.Definition_25_10
import BauschkeLean.Chap20.Proposition_20_56
import BauschkeLean.Chap25.Proposition_25_21

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open scoped InnerProductSpace Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 25.22: a concrete value `u ∈ A x` gives a Fitzpatrick-domain witness
at `(x, u)`. -/
private theorem memDomFitzpatrickOfMemValue
    {A : SetValuedOperator H H} (hA_mono : A.IsMonotone) {x u : H} (hu : u ∈ A x) :
    (x, u) ∈ ERealFunction.dom (F[A]) := by
  -- Rewrite the Fitzpatrick value on the graph to the finite pairing value.
  rw [ERealFunction.mem_dom_iff_ne_top]
  rw [SetValuedOperator.fitzpatrickFunction_eq_inner_of_mem_graph (A := A) hA_mono]
  · exact EReal.coe_ne_top _
  · simpa [SetValuedOperator.mem_graph] using hu

/-- Helper for Proposition 25.22: a point in `dom (A + B)` lies in both `dom A` and `dom B`. -/
private theorem mem_dom_inter_of_mem_dom_add
    {A B : SetValuedOperator H H} {x : H} (hx : x ∈ (A + B).dom) :
    x ∈ A.dom ∩ B.dom := by
  -- Expand the domain witness of `A + B` into witnesses for both summands.
  rcases (SetValuedOperator.mem_dom_iff (A := A + B) (x := x)).1 hx with ⟨w, hw⟩
  rcases Set.mem_add.mp hw with ⟨u, hu, v, hv, _⟩
  -- Repackage those witnesses as membership in the two domains.
  rw [Set.mem_inter_iff]
  exact ⟨
    (SetValuedOperator.mem_dom_iff (A := A) (x := x)).2 ⟨u, hu⟩,
    (SetValuedOperator.mem_dom_iff (A := B) (x := x)).2 ⟨v, hv⟩
  ⟩

/-- Helper for Proposition 25.22: every point in `(A + B).range` splits into a sum of one point
from `A.range` and one point from `B.range`. -/
private theorem exists_rangeDecomposition_of_mem_range_add
    {A B : SetValuedOperator H H} {w : H} (hw : w ∈ (A + B).range) :
    ∃ u ∈ A.range, ∃ v ∈ B.range, w = u + v := by
  -- Open the range witness at some base point and split the value in `(A + B) x`.
  rcases (SetValuedOperator.mem_range_iff (A := A + B) (y := w)).1 hw with ⟨x, hx⟩
  rcases Set.mem_add.mp hx with ⟨u, hu, v, hv, huv⟩
  -- Each split value belongs to the corresponding range by construction.
  refine ⟨u, (SetValuedOperator.mem_range_iff (A := A) (y := u)).2 ⟨x, hu⟩,
    v, (SetValuedOperator.mem_range_iff (A := B) (y := v)).2 ⟨x, hv⟩, huv.symm⟩

/-- Helper for Proposition 25.22: if `(x, u)` and `(x, v)` lie in the Fitzpatrick domains of `A`
and `B`, then `(x, u + v)` lies in the Fitzpatrick domain of `A + B`. -/
private theorem memDomFitzpatrickAddOfSplit
    {A B : SetValuedOperator H H} (hA_mono : A.IsMonotone) (hB_mono : B.IsMonotone)
    {x u v : H} (hu : (x, u) ∈ ERealFunction.dom (F[A]))
    (hv : (x, v) ∈ ERealFunction.dom (F[B])) :
    (x, u + v) ∈ ERealFunction.dom (F[(A + B)]) := by
  -- It suffices to show that the Fitzpatrick value of `A + B` is finite above.
  rw [ERealFunction.mem_dom_iff]
  have hAu_top : F[A] (x, u) ≠ ⊤ := (ERealFunction.mem_dom_iff_ne_top _ _).1 hu
  have hBv_top : F[B] (x, v) ≠ ⊤ := (ERealFunction.mem_dom_iff_ne_top _ _).1 hv
  have hsum_lt_top : F[A] (x, u) + F[B] (x, v) < ⊤ := by
    exact lt_top_iff_ne_top.mpr (EReal.add_ne_top hAu_top hBv_top)
  have hle_inf :
      F[(A + B)] (x, u + v) ≤
        (((fun z : H ↦ F[A] (x, z)) □ (fun z : H ↦ F[B] (x, z))) (u + v)) :=
    SetValuedOperator.fitzpatrickFunction_add_le_infimalConvolution_fibers
      (A := A) (B := B) hA_mono hB_mono x (u + v)
  have hle_sum : F[(A + B)] (x, u + v) ≤ F[A] (x, u) + F[B] (x, v) := by
    -- Evaluate the infimal convolution at the chosen split `u`.
    rw [ERealFunction.infimalConvolution_apply] at hle_inf
    exact le_trans hle_inf <| by
      simpa using iInf_le (fun z : H ↦ F[A] (x, z) + F[B] (x, (u + v) - z)) u
  exact lt_of_le_of_lt hle_sum hsum_lt_top

/-- Proposition 25.22 (1): if `A` and `B` are monotone and
`(dom A ∩ dom B) × H ⊆ dom F_B`, then `A + B` is `3*` monotone. -/
theorem isThreeStarMonotone_add_of_dom_inter_prod_univ_subset_dom_fitzpatrick
    {A B : SetValuedOperator H H} (hA_mono : A.IsMonotone) (hB_mono : B.IsMonotone)
    (hdom : (A.dom ∩ B.dom) ×ˢ (Set.univ : Set H) ⊆ ERealFunction.dom (F[B])) :
    (A + B).IsThreeStarMonotone := by
  -- Unfold `3*` monotonicity into the Fitzpatrick-domain inclusion to prove.
  rw [SetValuedOperator.isThreeStarMonotone_iff]
  rintro ⟨x, w⟩ ⟨hx_dom, _⟩
  have hxAB : x ∈ A.dom ∩ B.dom :=
    mem_dom_inter_of_mem_dom_add (A := A) (B := B) hx_dom
  rcases (SetValuedOperator.mem_dom_iff (A := A) (x := x)).1 hxAB.1 with ⟨u, hu⟩
  have hAu : (x, u) ∈ ERealFunction.dom (F[A]) :=
    memDomFitzpatrickOfMemValue (A := A) hA_mono hu
  have hBw : (x, w - u) ∈ ERealFunction.dom (F[B]) := by
    -- Clause (i) provides the needed `B`-side domain witness for every second coordinate.
    exact hdom ⟨hxAB, by simp⟩
  have hsplit :
      (x, u + (w - u)) ∈ ERealFunction.dom (F[(A + B)]) :=
    memDomFitzpatrickAddOfSplit (A := A) (B := B) hA_mono hB_mono hAu hBw
  -- Normalize the chosen split back to the original second coordinate `w`.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsplit

/-- Proposition 25.22 (2): if `A` and `B` are monotone and both are `3*` monotone, then
`A + B` is `3*` monotone. -/
theorem isThreeStarMonotone_add_of_isThreeStarMonotone
    {A B : SetValuedOperator H H} (hA_mono : A.IsMonotone) (hB_mono : B.IsMonotone)
    (hA_threeStar : A.IsThreeStarMonotone) (hB_threeStar : B.IsThreeStarMonotone) :
    (A + B).IsThreeStarMonotone := by
  -- Unfold `3*` monotonicity and reduce to an arbitrary point in `dom (A + B) × range (A + B)`.
  rw [SetValuedOperator.isThreeStarMonotone_iff]
  rintro ⟨x, w⟩ ⟨hx_dom, hw_range⟩
  have hxAB : x ∈ A.dom ∩ B.dom :=
    mem_dom_inter_of_mem_dom_add (A := A) (B := B) hx_dom
  rcases exists_rangeDecomposition_of_mem_range_add (A := A) (B := B) hw_range with
    ⟨u, hu_range, v, hv_range, hw_eq⟩
  have hAu : (x, u) ∈ ERealFunction.dom (F[A]) :=
    hA_threeStar.subset_dom_fitzpatrickFunction ⟨hxAB.1, hu_range⟩
  have hBv : (x, v) ∈ ERealFunction.dom (F[B]) :=
    hB_threeStar.subset_dom_fitzpatrickFunction ⟨hxAB.2, hv_range⟩
  have hsplit :
      (x, u + v) ∈ ERealFunction.dom (F[(A + B)]) :=
    memDomFitzpatrickAddOfSplit (A := A) (B := B) hA_mono hB_mono hAu hBv
  -- Substitute the range decomposition of `w` into the final Fitzpatrick-domain witness.
  simpa [hw_eq.symm] using hsplit

end SetValuedOperator
