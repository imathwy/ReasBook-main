module

public import Topology_Munkres_2000.Book.Example_71_1.Earring
public import Topology_Munkres_2000.Book.Definition_71_4.WedgeOfCircles
public import Mathlib.Analysis.Normed.Affine.AddTorsor

public section

namespace InfiniteEarring

/-- Helper for Example 71.1: the point opposite the origin on the `n`th circle
belongs to the carrier of the infinite earring. -/
lemma outerPoint_mem_carrier (n : ℕ+) :
    WithLp.toLp 2 ![2 * (n : ℝ)⁻¹, 0] ∈ carrier := by
  -- Route correction: the imported geometric definitions are reducible here,
  -- so the defining sphere equation can be checked through its bridge lemma.
  rw [mem_carrier_iff]
  refine ⟨n, ?_⟩
  rw [mem_circle_iff, EuclideanSpace.dist_eq]
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast n.property
  have hinvpos : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hnpos
  simp only [Fin.sum_univ_two, Real.dist_eq, center_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, sub_zero, sq_abs]
  rw [show 2 * (n : ℝ)⁻¹ - (n : ℝ)⁻¹ = (n : ℝ)⁻¹ by ring]
  norm_num

/-- Helper for Example 71.1: the point opposite the origin on the `n`th
component circle. -/
noncomputable def outerPoint (n : ℕ+) : Space :=
  ⟨WithLp.toLp 2 ![2 * (n : ℝ)⁻¹, 0], outerPoint_mem_carrier n⟩

/-- Helper for Example 71.1: distinct ambient component circles meet only at
the origin. -/
lemma circle_inter_circle (m n : ℕ+) (hmn : m ≠ n) :
    circle m ∩ circle n = {(0 : Plane)} := by
  -- Route correction: expand each sphere equation once, then compare the two
  -- resulting quadratic equations to force both coordinates to vanish.
  ext x
  constructor
  · intro hx
    have hm := hx.1
    have hn := hx.2
    rw [mem_circle_iff] at hm hn
    have hm_sq := congrArg (fun z : ℝ ↦ z ^ 2) hm
    have hn_sq := congrArg (fun z : ℝ ↦ z ^ 2) hn
    rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two] at hm_sq hn_sq
    have hm_quad : (x 0 - (m : ℝ)⁻¹) ^ 2 + (x 1) ^ 2 = ((m : ℝ)⁻¹) ^ 2 := by
      simpa [center_apply, Real.dist_eq] using hm_sq
    have hn_quad : (x 0 - (n : ℝ)⁻¹) ^ 2 + (x 1) ^ 2 = ((n : ℝ)⁻¹) ^ 2 := by
      simpa [center_apply, Real.dist_eq] using hn_sq
    have hmpos : 0 < (m : ℝ) := by
      exact_mod_cast m.property
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast n.property
    have hinv_ne : (m : ℝ)⁻¹ ≠ (n : ℝ)⁻¹ := by
      intro h
      apply hmn
      apply PNat.eq
      exact_mod_cast inv_injective h
    have hfactor : ((m : ℝ)⁻¹ - (n : ℝ)⁻¹) * x 0 = 0 := by
      nlinarith [hm_quad, hn_quad]
    have hx0 : x 0 = 0 := by
      rcases mul_eq_zero.mp hfactor with hradius | hxzero
      · exact False.elim (hinv_ne (sub_eq_zero.mp hradius))
      · exact hxzero
    have hm_zero := hm_quad
    rw [hx0] at hm_zero
    have hx1_sq : (x 1) ^ 2 = 0 := by
      nlinarith [hm_zero]
    have hx1 : x 1 = 0 := sq_eq_zero_iff.mp hx1_sq
    rw [Set.mem_singleton_iff]
    ext i
    fin_cases i
    · simp [hx0]
    · simp [hx1]
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    constructor
    · rw [mem_circle_iff, EuclideanSpace.dist_eq]
      simp [center_apply, Fin.sum_univ_two]
    · rw [mem_circle_iff, EuclideanSpace.dist_eq]
      simp [center_apply, Fin.sum_univ_two]

/-- Helper for Example 71.1: the strictly positive horizontal axis meets the
`n`th component exactly at its outer point. -/
lemma positiveAxis_inter_component (n : ℕ+) :
    {x : Space | 0 < (x : Plane) 0 ∧ (x : Plane) 1 = 0} ∩ component n =
      {outerPoint n} := by
  -- Route correction: reduce component membership to the ambient quadratic;
  -- strict positivity discards the origin root and selects the outer point.
  ext x
  constructor
  · intro hx
    have hcircle := (mem_component_iff x n).mp hx.2
    rw [mem_circle_iff] at hcircle
    have hcircle_sq := congrArg (fun z : ℝ ↦ z ^ 2) hcircle
    rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two] at hcircle_sq
    have hcircle_quad :
        ((x : Plane) 0 - (n : ℝ)⁻¹) ^ 2 + ((x : Plane) 1) ^ 2 = ((n : ℝ)⁻¹) ^ 2 := by
      simpa [center_apply, Real.dist_eq, hx.1.2] using hcircle_sq
    have hfactor : (x : Plane) 0 * ((x : Plane) 0 - 2 * (n : ℝ)⁻¹) = 0 := by
      nlinarith [hcircle_quad, hx.1.2]
    have hx0 : (x : Plane) 0 = 2 * (n : ℝ)⁻¹ := by
      rcases mul_eq_zero.mp hfactor with hxzero | houter
      · exact False.elim (ne_of_gt hx.1.1 hxzero)
      · linarith
    rw [Set.mem_singleton_iff]
    apply Subtype.ext
    ext i
    fin_cases i
    · simpa [outerPoint] using hx0
    · simpa [outerPoint] using hx.1.2
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    constructor
    · constructor
      · have hnpos : 0 < (n : ℝ) := by
          exact_mod_cast n.property
        have hinvpos : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hnpos
        exact mul_pos (by norm_num) hinvpos
      · simp [outerPoint]
    · rw [mem_component_iff, mem_circle_iff, EuclideanSpace.dist_eq]
      have hnpos : 0 < (n : ℝ) := by
        exact_mod_cast n.property
      have hinvpos : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hnpos
      simp only [outerPoint, Fin.sum_univ_two, Real.dist_eq, center_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero, sq_abs]
      rw [show 2 * (n : ℝ)⁻¹ - (n : ℝ)⁻¹ = (n : ℝ)⁻¹ by ring]
      norm_num

/-- Helper for Example 71.1: the unit sphere in the Euclidean plane is
homeomorphic to the complex unit circle. -/
lemma unitPlane_mem_iff (x : Plane) :
    x ∈ Metric.sphere 0 1 ↔
      Complex.orthonormalBasisOneI.repr.symm x ∈ Submonoid.unitSphere ℂ := by
  -- The orthonormal coordinate equivalence preserves the norm exactly.
  rw [Metric.mem_sphere, dist_zero_right, Submonoid.unitSphere]
  change ‖x‖ = 1 ↔ dist (Complex.orthonormalBasisOneI.repr.symm x) 0 = 1
  rw [dist_zero_right, Complex.orthonormalBasisOneI.repr.symm.norm_map]

/-- Helper for Example 71.1: every ambient component circle is homeomorphic
to the standard complex circle. -/
lemma circleHomeomorphCircle (n : ℕ+) : Nonempty (circle n ≃ₜ Circle) := by
  -- Route correction: normalize the circle by the canonical affine dilation,
  -- then identify the Euclidean unit sphere with the complex unit circle.
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast n.property
  have hradius : (n : ℝ)⁻¹ ≠ 0 := (inv_pos.mpr hnpos).ne'
  let dilation : Plane ≃ₜ Plane :=
    (DilationEquiv.smulTorsor (center n) hradius).toHomeomorph
  have hdilation (x : Plane) :
      x ∈ Metric.sphere 0 1 ↔ dilation x ∈ circle n := by
    rw [mem_circle_iff, Metric.mem_sphere]
    simp only [dilation, DilationEquiv.coe_toHomeomorph,
      DilationEquiv.smulTorsor_apply, vadd_eq_add]
    rw [dist_add_self_left, norm_smul, dist_zero_right]
    have hnorm : ‖(n : ℝ)⁻¹‖ = (n : ℝ)⁻¹ := abs_of_pos (inv_pos.mpr hnpos)
    rw [hnorm]
    constructor
    · intro hx
      rw [hx, mul_one]
    · intro hx
      exact mul_left_cancel₀ hradius (by simpa using hx)
  let sphereCircle : Metric.sphere (0 : Plane) 1 ≃ₜ Circle :=
    Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.subtype unitPlane_mem_iff
  exact ⟨(dilation.subtype hdilation).symm.trans sphereCircle⟩

/-- Helper for Example 71.1: the outer points converge to the common origin. -/
lemma outerPoint_tendsto_origin :
    Filter.Tendsto (fun k : ℕ ↦ outerPoint (Nat.succPNat k)) Filter.atTop (nhds origin) := by
  -- In ambient coordinates the distance is `2 / (k + 1)`, which tends to zero.
  rw [tendsto_subtype_rng, origin_coe, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  refine ⟨N, fun k hk ↦ ?_⟩
  rw [EuclideanSpace.dist_eq]
  simp [outerPoint, Fin.sum_univ_two]
  have hkpos : 0 < (k + 1 : ℝ) := by
    positivity
  have hkbound : 2 / ε < (k + 1 : ℝ) := by
    calc
      2 / ε < N := hN
      _ ≤ k := by exact_mod_cast hk
      _ < k + 1 := by norm_num
  have hdiv : 2 / (k + 1 : ℝ) < ε := (div_lt_iff₀ hkpos).mpr (by
    nlinarith [(div_lt_iff₀ hε).mp hkbound])
  simpa [div_eq_mul_inv, abs_of_pos hkpos, Real.sqrt_sq_eq_abs] using hdiv

/-- Helper for Example 71.1: the positive-integer-indexed component circles of the
infinite earring are all distinct, so they form a countably infinite collection. -/
theorem component_injective : Function.Injective component := by
  -- The outer point of one circle cannot lie on any distinct circle.
  intro m n hcomponent
  by_contra hmn
  have hm_outer : outerPoint m ∈ component m :=
    (positiveAxis_inter_component m).symm.subset rfl |>.2
  have hn_outer : outerPoint m ∈ component n := hcomponent ▸ hm_outer
  have hinter : (outerPoint m : Plane) ∈ circle m ∩ circle n := by
    exact ⟨(mem_component_iff _ _).mp hm_outer, (mem_component_iff _ _).mp hn_outer⟩
  have hzero : (outerPoint m : Plane) = 0 :=
    Set.mem_singleton_iff.mp ((circle_inter_circle m n hmn).subset hinter)
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast m.property
  have hcoord := congrArg (fun x : Plane ↦ x 0) hzero
  simp [outerPoint] at hcoord

/-- Helper for Example 71.1: two distinct component circles of the infinite earring
intersect exactly at their common origin. -/
theorem component_inter_component (m n : ℕ+) (hmn : m ≠ n) :
    component m ∩ component n = {origin} := by
  -- Pull the ambient singleton intersection back to the earring subtype.
  ext x
  constructor
  · intro hx
    have hambient : (x : Plane) ∈ circle m ∩ circle n := by
      exact ⟨(mem_component_iff _ _).mp hx.1, (mem_component_iff _ _).mp hx.2⟩
    have hzero : (x : Plane) = 0 :=
      Set.mem_singleton_iff.mp ((circle_inter_circle m n hmn).subset hambient)
    simp only [Set.mem_singleton_iff]
    apply Subtype.ext
    simpa [origin_coe] using hzero
  · intro hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    have hambient : (origin : Plane) ∈ circle m ∩ circle n := by
      rw [origin_coe, circle_inter_circle m n hmn]
      rfl
    exact ⟨(mem_component_iff _ _).mpr hambient.1,
      (mem_component_iff _ _).mpr hambient.2⟩

/-- Helper for Example 71.1: every component of the infinite earring is topologically
a circle. -/
theorem componentHomeomorphicCircle (n : ℕ+) : Nonempty (component n ≃ₜ Circle) := by
  -- The subtype embedding identifies the component with its ambient circle.
  have hsubset : circle n ⊆ Set.range (Subtype.val : Space → Plane) := by
    intro x hx
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [mem_carrier_iff]
    exact ⟨n, hx⟩
  have hcomponent : component n = Subtype.val ⁻¹' circle n := by
    ext x
    exact mem_component_iff x n
  let componentCircle : component n ≃ₜ circle n :=
    (Homeomorph.setCongr hcomponent).trans
      (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hsubset)
  exact ⟨componentCircle.trans (Classical.choice (circleHomeomorphCircle n))⟩

/-- Example 71.1: The subspace topology on the infinite earring is not
coherent with its component circles; hence it is not their coherence-based wedge. -/
theorem notCoherent :
    ¬ Topology.IsCoherentWith (Set.range component) := by
  -- Componentwise the positive axis is a singleton, but globally it omits its
  -- sequential limit at the origin.
  intro hcoherent
  let positiveAxis : Set Space :=
    {x | 0 < (x : Plane) 0 ∧ (x : Plane) 1 = 0}
  have hclosed : IsClosed positiveAxis := (hcoherent.isClosed_iff).mpr (by
    intro s hs
    rcases hs with ⟨n, rfl⟩
    have houter : outerPoint n ∈ positiveAxis ∩ component n :=
      (positiveAxis_inter_component n).symm.subset rfl
    have hpreimage : Subtype.val ⁻¹' positiveAxis =
        ({⟨outerPoint n, houter.2⟩} : Set (component n)) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hx
        apply Subtype.ext
        have hinter : (x : Space) ∈ positiveAxis ∩ component n := ⟨hx, x.property⟩
        exact Set.mem_singleton_iff.mp
          ((Set.ext_iff.mp (positiveAxis_inter_component n) _).mp hinter)
      · intro hx
        subst x
        exact houter.1
    rw [hpreimage]
    exact isClosed_singleton)
  have hseq_mem : ∀ k : ℕ, outerPoint (Nat.succPNat k) ∈ positiveAxis := by
    intro k
    exact ((positiveAxis_inter_component (Nat.succPNat k)).symm.subset rfl).1
  have horigin_not_mem : origin ∉ positiveAxis := by
    intro h
    simpa [positiveAxis, origin_coe] using h.1
  exact horigin_not_mem (hclosed.isSeqClosed hseq_mem outerPoint_tendsto_origin)

/-- The infinite earring is not a wedge of its component circles. -/
theorem not_isWedgeOfCircles :
    ¬ Topology.IsWedgeOfCircles component origin :=
  fun h ↦ notCoherent h.isCoherentWith

end InfiniteEarring
