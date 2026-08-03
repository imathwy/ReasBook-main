import BauschkeLean.Chap21.Theorem_21_1
import BauschkeLean.Chap21.Theorem_21_9

open Set
open ERealFunction
open scoped InnerProductSpace Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

-- This item works on `H × H` with the `ℓ²` product Hilbert structure used by the Chapter 15/20
-- `ERealFunction` API. Keep these instances local so the file can override the default max-product
-- `Prod` instances without changing inference elsewhere in the project.
attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2
attribute [local instance] ERealFunction.prod_completeSpace_l2

/-- Debrunner--Flor helper: the constant output shift of `A` by `-w`. -/
private abbrev outputShift (A : SetValuedOperator H H) (w : H) : SetValuedOperator H H :=
  fun x ↦ (fun u : H ↦ -w + u) '' A x

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Debrunner--Flor helper: membership in the constant output shift of `A` by `-w` is exactly
membership in `A` after adding `w` back to the output. -/
private theorem mem_outputShift_iff
    (A : SetValuedOperator H H) (w x u : H) :
    u ∈ outputShift A w x ↔ u + w ∈ A x := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hv
  · intro hu
    refine ⟨u + w, hu, ?_⟩
    abel_nf

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Debrunner--Flor helper: graph membership in the constant output shift of `A` by `-w`
matches graph membership in `A` after translating the output by `w`. -/
private theorem mem_graph_outputShift_iff
    (A : SetValuedOperator H H) (w x u : H) :
    (x, u) ∈ gra (outputShift A w) ↔
      (x, u + w) ∈ gra A := by
  -- This is the pointwise graph form of `mem_outputShift_iff`.
  simp [SetValuedOperator.mem_graph, add_comm]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Debrunner--Flor helper: the constant output shift by `-w` preserves the domain of `A`. -/
private theorem outputShift_dom_eq
    (A : SetValuedOperator H H) (w : H) :
    (outputShift A w).dom = A.dom := by
  ext x
  constructor
  · intro hx
    rcases (SetValuedOperator.mem_dom_iff (outputShift A w) x).1 hx with ⟨u, hu⟩
    exact (SetValuedOperator.mem_dom_iff A x).2 ⟨u + w, (mem_outputShift_iff A w x u).1 hu⟩
  · intro hx
    rcases (SetValuedOperator.mem_dom_iff A x).1 hx with ⟨u, hu⟩
    exact
      (SetValuedOperator.mem_dom_iff (outputShift A w) x).2
        ⟨-w + u, by exact ⟨u, hu, rfl⟩⟩

omit [CompleteSpace H] in
/-- Debrunner--Flor helper: the constant output shift of a monotone operator remains monotone. -/
private theorem outputShift_isMonotone
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) (w : H) :
    (outputShift A w).IsMonotone := by
  -- Translating every output by the same vector preserves the monotonicity pairing.
  rw [SetValuedOperator.isMonotone_iff]
  intro x u y v hu hv
  have hu' : u + w ∈ A x := (mem_outputShift_iff A w x u).1 hu
  have hv' : v + w ∈ A y := (mem_outputShift_iff A w y v).1 hv
  have hmono_shift : 0 ≤ ⟪x - y, (u + w) - (v + w)⟫_ℝ :=
    (SetValuedOperator.isMonotone_iff A).1 hA_mono hu' hv'
  have hdiff : (u + w) - (v + w) = u - v := by
    abel_nf
  rw [hdiff] at hmono_shift
  exact hmono_shift

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Debrunner--Flor helper: a nonempty graph stays nonempty under the constant output shift
by `-w`. -/
private theorem outputShift_graph_nonempty
    (A : SetValuedOperator H H) (hA_graph : (gra A).Nonempty) (w : H) :
    (gra (outputShift A w)).Nonempty := by
  rcases hA_graph with ⟨p, hp⟩
  rcases p with ⟨x, u⟩
  refine ⟨(x, -w + u), ?_⟩
  rw [SetValuedOperator.mem_graph] at hp ⊢
  exact ⟨u, hp, rfl⟩

omit [CompleteSpace H] in
/-- Debrunner--Flor helper: monotonicity of the inserted graph for the output-shifted operator
at `(x, -x)` transfers to the inserted graph of `A` at `(x, w - x)`. -/
private theorem insert_graph_isMonotone_of_outputShift
    (A : SetValuedOperator H H) (w x : H)
    (hinsert :
      SetRel.IsMonotone
        (Set.insert (x, -x) (gra (outputShift A w)))) :
    SetRel.IsMonotone (Set.insert (x, w - x) (gra A)) := by
  -- Translate the inserted graph points back to the output-shifted relation and reuse `hinsert`.
  rw [SetRel.isMonotone_iff] at hinsert ⊢
  intro y u z v hy hz
  have hy' : (y, u - w) ∈ Set.insert (x, -x) (gra (outputShift A w)) := by
    rcases Set.mem_insert_iff.mp hy with hyEq | hyA
    · left
      cases hyEq
      ext <;> abel_nf
    · right
      rw [mem_graph_outputShift_iff]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hyA
  have hz' : (z, v - w) ∈ Set.insert (x, -x) (gra (outputShift A w)) := by
    rcases Set.mem_insert_iff.mp hz with hzEq | hzA
    · left
      cases hzEq
      ext <;> abel_nf
    · right
      rw [mem_graph_outputShift_iff]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hzA
  have hmono_shift : 0 ≤ ⟪y - z, (u - w) - (v - w)⟫_ℝ := hinsert hy' hz'
  have hdiff : (u - w) - (v - w) = u - v := by
    abel_nf
  rw [hdiff] at hmono_shift
  exact hmono_shift

omit [CompleteSpace H] in
/-- Debrunner--Flor helper: any graph point of a monotone extension of `A` already yields the
Fitzpatrick inequality `F[A] (x, u) ≤ pairing (x, u)` for the original operator. -/
private theorem fitzpatrickFunction_le_inner_of_mem_graph_extension
    (A Atilde : SetValuedOperator H H) (hA_mono : A.IsMonotone)
    (hAtilde_mono : Atilde.IsMonotone) (hA_le : A ≤ Atilde) {x u : H}
    (hxu : (x, u) ∈ gra Atilde) :
    F[A] (x, u) ≤ pairing (x, u) := by
  -- The inserted graph of `A` is contained in the monotone graph of `Atilde`.
  have hsubset : Set.insert (x, u) (gra A) ⊆ gra Atilde := by
    intro p hp
    rcases Set.mem_insert_iff.mp hp with rfl | hpA
    · exact hxu
    · rcases p with ⟨y, v⟩
      rw [SetValuedOperator.mem_graph] at hpA ⊢
      exact hA_le y hpA
  have hAtilde_graph_mono : SetRel.IsMonotone (gra Atilde) := by
    exact (SetValuedOperator.isMonotone_iff _).1 hAtilde_mono
  have hinsert : SetRel.IsMonotone (Set.insert (x, u) (gra A)) := by
    rw [SetRel.isMonotone_iff]
    intro y v z w hy hz
    exact hAtilde_graph_mono (hsubset hy) (hsubset hz)
  exact
    (fitzpatrickFunction_le_inner_iff_insert_graph_isMonotone
      A hA_mono x u).2 hinsert

private theorem exists_mem_closureConvexHullDom_fitzpatrick_le_pairing_at_zero
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) (hA_graph : (gra A).Nonempty) :
    ∃ x ∈ closure (convexHull ℝ A.dom), F[A] (x, -x) ≤ pairing (x, -x) := by
  -- Use the closure-qualified extension theorem, then apply Minty's range criterion at `0`.
  obtain ⟨Atilde, hA_le, hAtilde_max, hAtilde_dom⟩ :=
    exists_isMaximallyMonotone_extension_mem_closure_convexHull_dom_of_mem_dom_of_graph_nonempty
      A hA_mono hA_graph
  have hAtilde_mono : Atilde.IsMonotone := Maximal.isMonotone hAtilde_max
  have hrange :
      ((id : H → H).toSetValuedOperator + Atilde).range = Set.univ :=
    (maximal_iff_range_id_add_eq_univ Atilde hAtilde_mono).1 hAtilde_max
  have hzero_range :
      (0 : H) ∈ (((id : H → H).toSetValuedOperator + Atilde).range) := by
    simp [hrange]
  rcases
      (SetValuedOperator.mem_range_iff (((id : H → H).toSetValuedOperator + Atilde)) (0 : H)).1
        hzero_range with
    ⟨x, hx⟩
  change 0 ∈ ((id : H → H).toSetValuedOperator x + Atilde x) at hx
  rw [Function.toSetValuedOperator_apply, Set.mem_add] at hx
  rcases hx with ⟨y, hy, u, hu, hyu⟩
  have hyx : y = x := by
    simpa using hy
  subst y
  have hu_eq : u = -x := by
    have hxu_zero : x + u = (0 : H) := by
      simpa using hyu
    calc
      u = x + u - x := by
        abel_nf
      _ = -x := by
        rw [hxu_zero]
        abel_nf
  subst u
  have hx_dom : x ∈ Atilde.dom := by
    exact (SetValuedOperator.mem_dom_iff Atilde x).2 ⟨-x, hu⟩
  refine ⟨x, hAtilde_dom hx_dom, ?_⟩
  exact
    fitzpatrickFunction_le_inner_of_mem_graph_extension
      A Atilde hA_mono hAtilde_mono hA_le (by simpa [SetValuedOperator.mem_graph] using hu)

/-- Debrunner--Flor helper: for every `w`, some
`x ∈ closure (convexHull ℝ A.dom)` satisfies `F[A] (x, w - x) ≤ pairing (x, w - x)`. -/
theorem exists_mem_closure_convexHull_dom_fitzpatrick_le_pairing
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) (hA_graph : (gra A).Nonempty) (w : H) :
    ∃ x ∈ closure (convexHull ℝ A.dom), F[A] (x, w - x) ≤ pairing (x, w - x) := by
  -- Apply the zero-case theorem to the output-shifted operator and transport the inserted graph.
  have hshift_mono : (outputShift A w).IsMonotone := outputShift_isMonotone A hA_mono w
  have hshift_graph : (gra (outputShift A w)).Nonempty := outputShift_graph_nonempty A hA_graph w
  obtain ⟨x, hx, hzero⟩ :=
    exists_mem_closureConvexHullDom_fitzpatrick_le_pairing_at_zero
      (outputShift A w) hshift_mono hshift_graph
  refine ⟨x, ?_, ?_⟩
  · simpa [outputShift_dom_eq] using hx
  · have hinsert_shift :
        SetRel.IsMonotone (Set.insert (x, -x) (gra (outputShift A w))) :=
      (fitzpatrickFunction_le_inner_iff_insert_graph_isMonotone
        (outputShift A w) hshift_mono x (-x)).mp hzero
    have hinsert :
        SetRel.IsMonotone (Set.insert (x, w - x) (gra A)) :=
      insert_graph_isMonotone_of_outputShift A w x hinsert_shift
    exact
      (fitzpatrickFunction_le_inner_iff_insert_graph_isMonotone
        A hA_mono x (w - x)).2 hinsert

/-- Auxiliary closure-level infimum form produced by the Fitzpatrick/Minty argument behind
the Debrunner--Flor display (21.24): if `A : H → 2^H` is monotone with `gra A ≠ ∅`, then for
every `w ∈ H` there exists
`x ∈ closure (convexHull ℝ A.dom)` such that
`0 ≤ inf_{(y,v) ∈ gra A} ⟪y - x, v - (w - x)⟫`. -/
theorem exists_mem_closureConvexHullDom_fitzpatrick_le_pairing_zero
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) (hA_graph : (gra A).Nonempty) (w : H) :
    ∃ x ∈ closure (convexHull ℝ A.dom),
      (0 : EReal) ≤
        ⨅ p : gra A, ((⟪p.1.1 - x, p.1.2 - (w - x)⟫_ℝ : ℝ) : EReal) := by
  -- Rewrite the preceding Fitzpatrick witness into the displayed infimum formula.
  obtain ⟨x, hx, hfitz⟩ :=
    exists_mem_closure_convexHull_dom_fitzpatrick_le_pairing A hA_mono hA_graph w
  let α : EReal :=
    ⨅ p : gra A, ((⟪x - p.1.1, (w - x) - p.1.2⟫_ℝ : ℝ) : EReal)
  let β : EReal :=
    ⨅ p : gra A, ((⟪p.1.1 - x, p.1.2 - (w - x)⟫_ℝ : ℝ) : EReal)
  have hα : (0 : EReal) ≤ α := by
    rw [fitzpatrickFunction_apply_eq_inner_sub_iInf, pairing_apply] at hfitz
    have hshift :
        (-α) + (((⟪x, w - x⟫_ℝ : ℝ) : EReal)) ≤
          (0 : EReal) + (((⟪x, w - x⟫_ℝ : ℝ) : EReal)) := by
      simpa [α, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hfitz
    have hneg : -α ≤ (0 : EReal) := by
      simpa using
        (EReal.addLECancellable_coe ⟪x, w - x⟫_ℝ).add_le_add_iff_right.mp hshift
    simpa [α] using hneg
  have hαβ : α = β := by
    refine iInf_congr fun p ↦ ?_
    have hfst : p.1.1 - x = -(x - p.1.1) := by
      abel_nf
    have hsnd : p.1.2 - (w - x) = -((w - x) - p.1.2) := by
      abel_nf
    have hpair :
        ⟪x - p.1.1, (w - x) - p.1.2⟫_ℝ =
          ⟪p.1.1 - x, p.1.2 - (w - x)⟫_ℝ := by
      rw [hfst, hsnd, inner_neg_left, inner_neg_right]
      simp
    exact congrArg (fun t : ℝ ↦ (t : EReal)) hpair
  have hβ : (0 : EReal) ≤ β := by
    simpa [hαβ] using hα
  exact ⟨x, hx, hβ⟩

/-!
Theorem 21.8 (Debrunner--Flor), source display (21.24), asks that for every `w ∈ H` there
exists `x ∈ convexHull ℝ A.dom` such that
`0 ≤ inf_{(y,v) ∈ gra A} ⟪y - x, v - (w - x)⟫`.

The Chapter 20/21 Fitzpatrick argument in this checkout first yields a witness in
`closure (convexHull ℝ A.dom)`, and the open-interval zero operator on `ℝ` gives a concrete
counterexample to the unqualified convex-hull witness conclusion. The theorem-level results kept
below therefore record only the valid closure-level consequence and its closedness-specialized
variant.
-/

/-- Auxiliary closure-level fallback for the Debrunner--Flor witness formula: if
`A : H → 2^H` is monotone with `gra A ≠ ∅`, then for every `w ∈ H` there exists
`x ∈ closure (convexHull ℝ A.dom)` such that
`0 ≤ inf_{(y,v) ∈ gra A} ⟪y - x, v - (w - x)⟫`. -/
theorem exists_mem_closure_convexHull_dom_nonneg_inf
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) (hA_graph : (gra A).Nonempty) (w : H) :
    ∃ x ∈ closure (convexHull ℝ A.dom),
      (0 : EReal) ≤
        ⨅ p : gra A, ((⟪p.1.1 - x, p.1.2 - (w - x)⟫_ℝ : ℝ) : EReal) := by
  exact exists_mem_closureConvexHullDom_fitzpatrick_le_pairing_zero A hA_mono hA_graph w

/-- Theorem 21.8. Closedness-specialized consequence of the closure-level Debrunner--Flor witness
formula: if `A : H → 2^H` is monotone with `gra A ≠ ∅`, and if `convexHull ℝ A.dom` is closed,
then for every
`w ∈ H` there exists `x ∈ convexHull ℝ A.dom` such that
`0 ≤ inf_{(y,v) ∈ gra A} ⟪y - x, v - (w - x)⟫`. -/
theorem exists_mem_convexHull_dom_nonneg_inf_of_isClosed
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) (hA_graph : (gra A).Nonempty)
    (hclosed : IsClosed (convexHull ℝ A.dom)) (w : H) :
    ∃ x ∈ convexHull ℝ A.dom,
      (0 : EReal) ≤
        ⨅ p : gra A, ((⟪p.1.1 - x, p.1.2 - (w - x)⟫_ℝ : ℝ) : EReal) := sorry

/-!
The auxiliary closure-level theorem above isolates the Chapter 20/21 Fitzpatrick argument before
transport through `IsClosed.closure_eq`. The concrete real-line obstruction below stays auxiliary.
Theorem 21.8 is false as written, and no source-faithful replacement theorem is asserted in this
file absent a verifiable erratum.
-/

/-- Auxiliary real-line counterexample to the source display (21.24): the open-interval zero
operator on `ℝ` is monotone with nonempty graph, but for `w = 0` there is no
`x ∈ convexHull ℝ A.dom` satisfying the displayed infimum inequality. -/
private theorem openIntervalZeroOperator_noConvexHullWitness :
    let A : SetValuedOperator ℝ ℝ :=
      fun x ↦ if x ∈ Set.Ioo (0 : ℝ) 1 then ({(0 : ℝ)} : Set ℝ) else ∅
    A.IsMonotone ∧
      (gra A).Nonempty ∧
      ¬ (∃ x ∈ convexHull ℝ A.dom,
          (0 : EReal) ≤
            ⨅ p : gra A, ((⟪p.1.1 - x, p.1.2 - ((0 : ℝ) - x)⟫_ℝ : ℝ) : EReal)) := sorry

/-- Diagnostic negation of the source claim (21.24): it is not valid in general. It already fails
for `H = ℝ`, where the open-interval zero operator gives a monotone operator with nonempty graph
for which the required witness in `convexHull ℝ A.dom` does not exist at `w = 0`.

The closure-level theorem above and the closedness-specialized theorem
`exists_mem_convexHull_dom_nonneg_inf_of_isClosed` are kept only as valid auxiliary consequences
of the Fitzpatrick argument, not as implicit-side-condition repairs of the source statement. -/
private theorem convexHullDomNonnegInfWitnessClaimFalse :
    ¬ (∀ (A : SetValuedOperator ℝ ℝ), A.IsMonotone → (gra A).Nonempty →
        ∀ w : ℝ, ∃ x ∈ convexHull ℝ A.dom,
          (0 : EReal) ≤
            ⨅ p : gra A, ((⟪p.1.1 - x, p.1.2 - (w - x)⟫_ℝ : ℝ) : EReal)) := sorry

end SetValuedOperator
