module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Geometry.Polygon.Basic
public import Mathlib.GroupTheory.Perm.Fin

public section

open Set
open Filter
open scoped Pointwise Topology

/-- An explicitly presented polygon whose vertices occur counterclockwise on a circle. -/
structure CyclicPolygon (n : ℕ) where
  /-- The polygon has at least three vertices. -/
  three_le : 3 ≤ n
  /-- The center of the circle containing the vertices. -/
  center : EuclideanSpace ℝ (Fin 2)
  /-- The radius of the circle containing the vertices. -/
  radius : ℝ
  /-- The radius is positive. -/
  radius_pos : 0 < radius
  /-- A lifted sequence of arguments, including its closing endpoint. -/
  angles : Fin (n + 1) → ℝ
  /-- The lifted arguments are strictly increasing. -/
  angles_strictMono : StrictMono angles
  /-- The final argument closes the circle after one full turn. -/
  angles_last : angles (Fin.last n) = angles 0 + 2 * Real.pi

namespace CyclicPolygon

noncomputable section

variable {n : ℕ}

/-- The vertex determined by an entry of the lifted angle sequence. -/
@[expose]
def vertex (poly : CyclicPolygon n) (i : Fin (n + 1)) : EuclideanSpace ℝ (Fin 2) :=
  poly.center + poly.radius • WithLp.toLp 2 ![Real.cos (poly.angles i), Real.sin (poly.angles i)]

/-- The closing vertex agrees with the initial vertex. -/
theorem vertexLast (poly : CyclicPolygon n) :
    poly.vertex (Fin.last n) = poly.vertex 0 := by
  -- The lifted endpoint differs from the initial angle by one full period.
  ext i
  fin_cases i
  · simp only [vertex, PiLp.add_apply, smul_eq_mul, PiLp.smul_apply,
      poly.angles_last, Real.cos_add_two_pi, Real.sin_add_two_pi]
  ·
    simp only [vertex, PiLp.add_apply, smul_eq_mul, PiLp.smul_apply,
      poly.angles_last, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- The cyclic polygon obtained from the first `n` vertices of the lifted presentation. -/
def toPolygon (poly : CyclicPolygon n) : Polygon (EuclideanSpace ℝ (Fin 2)) n :=
  ⟨fun i ↦ poly.vertex i.castSucc⟩

/-- The vertices of the associated mathlib polygon are the first lifted vertices. -/
theorem toPolygon_vertices (poly : CyclicPolygon n) (i : Fin n) :
    poly.toPolygon.vertices i = poly.vertex i.castSucc := by
  unfold toPolygon
  rfl

/-- Helper for Definition 74.1: the lifted successor represents the cyclic successor vertex. -/
theorem vertex_succ_eq_rotated (poly : CyclicPolygon n) (i : Fin n) :
    poly.vertex i.succ = poly.toPolygon.vertices (finRotate n i) := by
  -- Split at the final index, where the lifted endpoint closes the cycle.
  have hzero_three : 0 < 3 := by
    norm_num
  have hn : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le hzero_three poly.three_le)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [toPolygon_vertices]
  by_cases hi : i = Fin.last m
  · subst i
    rw [finRotate_last]
    exact poly.vertexLast
  · have hi_val : i.val < m := by
      exact Fin.val_lt_last hi
    rw [finRotate_of_lt hi_val]
    rfl

/-- The signed area form on the oriented Euclidean plane. -/
def signedArea (u v : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  u 0 * v 1 - u 1 * v 0

/-- Helper for Definition 74.1: the standard point of argument `θ` on the unit circle. -/
def unitCirclePoint (θ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![Real.cos θ, Real.sin θ]

/-- Helper for Definition 74.1: a cyclic vertex is a translated, scaled unit-circle point. -/
theorem vertex_eq_center_add_unitCirclePoint (poly : CyclicPolygon n) (i : Fin (n + 1)) :
    poly.vertex i = poly.center + poly.radius • unitCirclePoint (poly.angles i) := by
  -- This exposes only the stable circle-point interface of the vertex construction.
  unfold vertex unitCirclePoint
  rfl

/-- Helper for Definition 74.1: the signed area of three unit-circle points factors into
three half-angle sines. -/
theorem signedArea_unitCircle_sub (a b c : ℝ) :
    signedArea (unitCirclePoint b - unitCirclePoint a)
        (unitCirclePoint c - unitCirclePoint a) =
      4 * Real.sin ((b - a) / 2) * Real.sin ((c - a) / 2) *
        Real.sin ((c - b) / 2) := by
  -- Difference-to-product identities isolate the three positive half-angle factors.
  unfold signedArea unitCirclePoint
  simp only [PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Real.cos_sub_cos, Real.sin_sub_sin, Real.sin_sub_sin, Real.cos_sub_cos]
  have harg : (c - b) / 2 = (c + a) / 2 - (b + a) / 2 := by
    ring
  rw [harg, Real.sin_sub]
  ring

/-- Helper for Definition 74.1: translation and scaling multiply the circle determinant by
the square of the radius. -/
theorem signedArea_circle_sub (o : EuclideanSpace ℝ (Fin 2)) (r a b c : ℝ) :
    signedArea
        ((o + r • unitCirclePoint b) - (o + r • unitCirclePoint a))
        ((o + r • unitCirclePoint c) - (o + r • unitCirclePoint a)) =
      r ^ 2 * signedArea (unitCirclePoint b - unitCirclePoint a)
        (unitCirclePoint c - unitCirclePoint a) := by
  -- The common center cancels, and bilinearity contributes one radius from each vector.
  unfold signedArea unitCirclePoint
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Helper for Definition 74.1: the lift of vertex `j` lying after the start of edge `i`. -/
def liftedAngle (poly : CyclicPolygon n) (i j : Fin n) : ℝ :=
  if i < j then poly.angles j.castSucc else poly.angles j.castSucc + 2 * Real.pi

/-- Helper for Definition 74.1: replacing an angle by its cyclic lift does not change its
circle point. -/
theorem vertex_eq_circle_liftedAngle (poly : CyclicPolygon n) (i j : Fin n) :
    poly.vertex j.castSucc =
      poly.center + poly.radius • unitCirclePoint (poly.liftedAngle i j) := by
  -- In the wrapped case, sine and cosine are unchanged by addition of `2π`.
  unfold vertex liftedAngle unitCirclePoint
  by_cases hij : i < j
  · simp only [if_pos hij]
  · simp only [if_neg hij, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- Helper for Definition 74.1: a non-endpoint cyclic lift lies strictly between the lifted
end of its edge and the next copy of the edge's initial angle. -/
theorem angles_succ_lt_liftedAngle_lt (poly : CyclicPolygon n) (i j : Fin n)
    (hji : j ≠ i) (hjrot : j ≠ finRotate n i) :
    poly.angles i.succ < poly.liftedAngle i j ∧
      poly.liftedAngle i j < poly.angles i.castSucc + 2 * Real.pi := by
  -- Work in `Fin (m + 1)` so the wrapped and nonwrapped successors are explicit.
  have hzero_three : 0 < 3 := by
    norm_num
  have hn : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le hzero_three poly.three_le)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  unfold liftedAngle
  by_cases hij : i < j
  · rw [if_pos hij]
    have hi_last : i ≠ Fin.last m := by
      intro hi
      subst i
      exact (not_lt_of_ge j.le_last) hij
    have hisucc_le : i.succ ≤ j.castSucc := Fin.succ_le_castSucc_iff.mpr hij
    have hisucc_ne : i.succ ≠ j.castSucc := by
      intro heq
      apply hjrot
      rw [finRotate_of_lt (Fin.val_lt_last hi_last)]
      exact Fin.ext (congrArg Fin.val heq).symm
    have hisucc_lt : i.succ < j.castSucc := lt_of_le_of_ne hisucc_le hisucc_ne
    constructor
    · exact poly.angles_strictMono hisucc_lt
    · calc
        poly.angles j.castSucc < poly.angles (Fin.last (m + 1)) :=
          poly.angles_strictMono j.castSucc_lt_last
        _ = poly.angles 0 + 2 * Real.pi := poly.angles_last
        _ ≤ poly.angles i.castSucc + 2 * Real.pi :=
          by simpa [add_comm] using
            add_le_add_right (poly.angles_strictMono.monotone (Fin.zero_le i.castSucc))
              (2 * Real.pi)
  · rw [if_neg hij]
    have hji_le : j ≤ i := Fin.not_lt.mp hij
    have hji_lt : j < i := lt_of_le_of_ne hji_le hji
    constructor
    · by_cases hi : i = Fin.last m
      · subst i
        rw [Fin.succ_last, poly.angles_last]
        have hjzero : j ≠ 0 := by
          intro hj
          subst j
          apply hjrot
          rw [finRotate_last]
        have hjpos : (0 : Fin (m + 1)) < j := Fin.pos_iff_ne_zero.mpr hjzero
        simpa [add_comm] using add_lt_add_right
          (poly.angles_strictMono (Fin.castSucc_lt_castSucc_iff.mpr hjpos))
            (2 * Real.pi)
      · calc
          poly.angles i.succ < poly.angles (Fin.last (m + 1)) :=
            poly.angles_strictMono
              (Fin.lt_last_iff_ne_last.mpr ((Fin.succ_ne_last_iff i).mpr hi))
          _ = poly.angles 0 + 2 * Real.pi := poly.angles_last
          _ ≤ poly.angles j.castSucc + 2 * Real.pi :=
            by simpa [add_comm] using
              add_le_add_right (poly.angles_strictMono.monotone (Fin.zero_le j.castSucc))
                (2 * Real.pi)
    · simpa [add_comm] using add_lt_add_right (poly.angles_strictMono
        (Fin.castSucc_lt_castSucc_iff.mpr hji_lt)) (2 * Real.pi)

/-- Helper for Definition 74.1: the determinant of a cyclic edge and a vertex has the
half-angle factorization associated to the cyclic lift. -/
theorem signedArea_edge_vertex_eq (poly : CyclicPolygon n) (i j : Fin n) :
    signedArea
        (poly.toPolygon.vertices (finRotate n i) - poly.toPolygon.vertices i)
        (poly.toPolygon.vertices j - poly.toPolygon.vertices i) =
      poly.radius ^ 2 *
        (4 * Real.sin ((poly.angles i.succ - poly.angles i.castSucc) / 2) *
          Real.sin ((poly.liftedAngle i j - poly.angles i.castSucc) / 2) *
          Real.sin ((poly.liftedAngle i j - poly.angles i.succ) / 2)) := by
  -- Normalize the three vertices to one translated and scaled unit-circle computation.
  rw [← poly.vertex_succ_eq_rotated i, toPolygon_vertices, toPolygon_vertices]
  rw [poly.vertex_eq_circle_liftedAngle i j]
  rw [poly.vertex_eq_center_add_unitCirclePoint i.succ,
    poly.vertex_eq_center_add_unitCirclePoint i.castSucc]
  rw [signedArea_circle_sub, signedArea_unitCircle_sub]

/-- Helper for Definition 74.1: every vertex is on the inward side of every cyclic edge,
with equality exactly at that edge's endpoints. -/
theorem signedArea_edge_vertex_nonneg_and_eq_zero (poly : CyclicPolygon n) (i j : Fin n) :
    0 ≤ signedArea
        (poly.toPolygon.vertices (finRotate n i) - poly.toPolygon.vertices i)
        (poly.toPolygon.vertices j - poly.toPolygon.vertices i) ∧
      (signedArea
          (poly.toPolygon.vertices (finRotate n i) - poly.toPolygon.vertices i)
          (poly.toPolygon.vertices j - poly.toPolygon.vertices i) = 0 ↔
        j = i ∨ j = finRotate n i) := by
  -- Endpoints give a zero determinant; every other cyclic lift gives three positive sines.
  by_cases hji : j = i
  · subst j
    constructor
    · unfold signedArea
      simp
    · constructor
      · intro _
        exact Or.inl rfl
      · intro _
        unfold signedArea
        simp
  by_cases hjrot : j = finRotate n i
  · subst j
    constructor
    · have hself : signedArea
          (poly.toPolygon.vertices (finRotate n i) - poly.toPolygon.vertices i)
          (poly.toPolygon.vertices (finRotate n i) - poly.toPolygon.vertices i) = 0 := by
        unfold signedArea
        ring
      rw [hself]
    · constructor
      · intro _
        exact Or.inr rfl
      · intro _
        unfold signedArea
        ring
  have hab : poly.angles i.castSucc < poly.angles i.succ :=
    poly.angles_strictMono i.castSucc_lt_succ
  have hbc := poly.angles_succ_lt_liftedAngle_lt i j hji hjrot
  have hsab : 0 < Real.sin ((poly.angles i.succ - poly.angles i.castSucc) / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · have hlast : poly.angles i.succ ≤ poly.angles (Fin.last n) :=
        poly.angles_strictMono.monotone (Fin.le_last _)
      have hzero : poly.angles 0 ≤ poly.angles i.castSucc :=
        poly.angles_strictMono.monotone (Fin.zero_le _)
      rw [poly.angles_last] at hlast
      linarith [Real.pi_pos]
  have hsac : 0 < Real.sin ((poly.liftedAngle i j - poly.angles i.castSucc) / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
  have hsbc : 0 < Real.sin ((poly.liftedAngle i j - poly.angles i.succ) / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
  have harea : 0 < signedArea
      (poly.toPolygon.vertices (finRotate n i) - poly.toPolygon.vertices i)
      (poly.toPolygon.vertices j - poly.toPolygon.vertices i) := by
    rw [poly.signedArea_edge_vertex_eq i j]
    have hfour : (0 : ℝ) < 4 := by
      norm_num
    exact mul_pos (sq_pos_of_pos poly.radius_pos)
      (mul_pos (mul_pos (mul_pos hfour hsab) hsac) hsbc)
  exact ⟨harea.le, ⟨fun hz ↦ False.elim (harea.ne' hz), fun hj ↦ (hj.elim hji hjrot).elim⟩⟩

/-- Reversing a based directed segment negates its signed-area test. -/
theorem signedArea_sub_swap (a b x : EuclideanSpace ℝ (Fin 2)) :
    signedArea (a - b) (x - b) = -signedArea (b - a) (x - a) := by
  -- Expand the two coordinates and verify the affine determinant identity.
  unfold signedArea
  simp only [PiLp.sub_apply]
  ring

/-- Helper for Definition 74.1: signed area is linear in its second argument. -/
theorem signedArea_isLinearMap_right (u : EuclideanSpace ℝ (Fin 2)) :
    IsLinearMap ℝ (fun v ↦ signedArea u v) := by
  -- Both determinant coordinates distribute over addition and real scalar multiplication.
  constructor
  · intro x y
    unfold signedArea
    simp only [PiLp.add_apply]
    ring
  · intro r x
    unfold signedArea
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring

/-- Helper for Definition 74.1: signed area with a fixed first vector as a linear map. -/
def signedAreaRightLinearMap (u : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ :=
  IsLinearMap.mk' (fun v ↦ signedArea u v) (signedArea_isLinearMap_right u)

/-- Helper for Definition 74.1: the continuous linear signed-area functional. -/
noncomputable def signedAreaRightCLM (u : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (signedAreaRightLinearMap u)

/-- Helper for Definition 74.1: evaluation of the continuous signed-area functional. -/
theorem signedAreaRightCLM_apply (u v : EuclideanSpace ℝ (Fin 2)) :
    signedAreaRightCLM u v = signedArea u v := by
  -- Both bundled maps have the same underlying signed-area function.
  unfold signedAreaRightCLM signedAreaRightLinearMap
  rfl

/-- Helper for Definition 74.1: the underlying linear map of the continuous signed-area
functional has the expected evaluation. -/
theorem signedAreaRightCLM_toLinearMap_apply (u v : EuclideanSpace ℝ (Fin 2)) :
    (signedAreaRightCLM u).toLinearMap v = signedArea u v := by
  -- This is the linear-map spelling of `signedAreaRightCLM_apply`.
  rfl

/-- Helper for Definition 74.1: signed area distributes over subtraction in its second
argument. -/
theorem signedArea_sub_right (u x p : EuclideanSpace ℝ (Fin 2)) :
    signedArea u (x - p) = signedArea u x - signedArea u p := by
  -- This is linearity of the determinant written in based-point form.
  unfold signedArea
  simp only [PiLp.sub_apply]
  ring

/-- Helper for Definition 74.1: a nonzero first vector gives a surjective signed-area
functional. -/
theorem signedAreaRightCLM_surjective {u : EuclideanSpace ℝ (Fin 2)} (hu : u ≠ 0) :
    Function.Surjective (signedAreaRightCLM u) := by
  -- A nonzero linear functional onto the one-dimensional scalar field is surjective.
  apply surjective_of_nonzero_of_finrank_eq_one (K := ℝ) (A := ℝ)
  · simp
  · apply DFunLike.ne_iff.mpr
    by_cases hu0 : u 0 = 0
    · have hu1 : u 1 ≠ 0 := by
        intro hu1
        apply hu
        ext k
        fin_cases k
        · exact hu0
        · exact hu1
      refine ⟨unitCirclePoint 0, ?_⟩
      rw [LinearMap.zero_apply]
      rw [signedAreaRightCLM_toLinearMap_apply]
      unfold signedArea unitCirclePoint
      simp only [Real.cos_zero, Real.sin_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
        mul_zero, mul_one, zero_sub]
      exact neg_ne_zero.mpr hu1
    · refine ⟨unitCirclePoint (Real.pi / 2), ?_⟩
      rw [LinearMap.zero_apply]
      rw [signedAreaRightCLM_toLinearMap_apply]
      unfold signedArea unitCirclePoint
      simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, mul_one, mul_zero, sub_zero]
      exact hu0

/-- Helper for Definition 74.1: the interior of a genuine signed-area half-space is given by
the corresponding strict inequality. -/
theorem interior_signedArea_sub_nonneg {u : EuclideanSpace ℝ (Fin 2)} (hu : u ≠ 0)
    (p : EuclideanSpace ℝ (Fin 2)) :
    _root_.interior {x | 0 ≤ signedArea u (x - p)} =
      {x | 0 < signedArea u (x - p)} := by
  -- Rewrite as a preimage of `Ici` under a surjective continuous linear functional.
  have hclosed : {x | 0 ≤ signedArea u (x - p)} =
      signedAreaRightCLM u ⁻¹' Set.Ici (signedArea u p) := by
    ext x
    simp only [mem_setOf_eq, mem_preimage, mem_Ici, signedAreaRightCLM_apply,
      signedArea_sub_right, sub_nonneg]
  have hopen : {x | 0 < signedArea u (x - p)} =
      signedAreaRightCLM u ⁻¹' Set.Ioi (signedArea u p) := by
    ext x
    simp only [mem_setOf_eq, mem_preimage, mem_Ioi, signedAreaRightCLM_apply,
      signedArea_sub_right, sub_pos]
  rw [hclosed, (signedAreaRightCLM u).interior_preimage
    (signedAreaRightCLM_surjective hu), interior_Ici, ← hopen]

/-- Helper for Definition 74.1: a nonnegative affine signed-area half-space is convex. -/
theorem convex_signedArea_sub_nonneg (u p : EuclideanSpace ℝ (Fin 2)) :
    Convex ℝ {x | 0 ≤ signedArea u (x - p)} := by
  -- Linearity rewrites the based determinant inequality as an ordinary linear half-space.
  have hset : {x | 0 ≤ signedArea u (x - p)} = {x | signedArea u p ≤ signedArea u x} := by
    ext x
    unfold signedArea
    simp only [mem_setOf_eq, PiLp.sub_apply]
    constructor
    · intro h
      linarith
    · intro h
      linarith
  rw [hset]
  exact convex_halfSpace_ge (signedArea_isLinearMap_right u) _

/-- Helper for Definition 74.1: two vectors with nonzero determinant give the signed-area
coordinate decomposition of every planar vector. -/
theorem eq_signedArea_coordinates {a b : EuclideanSpace ℝ (Fin 2)}
    (hab : signedArea a b ≠ 0) (d : EuclideanSpace ℝ (Fin 2)) :
    d = (-signedArea b d / signedArea a b) • a +
      (signedArea a d / signedArea a b) • b := by
  -- Check the two coordinates after clearing the nonzero determinant denominator.
  ext k
  fin_cases k
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp [hab]
    unfold signedArea
    simp
    ring
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp [hab]
    unfold signedArea
    simp
    ring

/-- Helper for Definition 74.1: cyclic rotation on at least two indices has no fixed point. -/
theorem finRotate_ne_self_of_two_le {m : ℕ} (hm : 2 ≤ m) (i : Fin m) :
    finRotate m i ≠ i := by
  -- Every index lies in the full support of the cyclic rotation.
  have hi : i ∈ (finRotate m).support := by
    rw [support_finRotate_of_le hm]
    exact Finset.mem_univ i
  exact Equiv.Perm.mem_support.mp hi

/-- Helper for Definition 74.1: on at least three indices, the predecessor and successor of
an index are distinct. -/
theorem finRotate_symm_ne_finRotate_of_three_le {m : ℕ} (hm : 3 ≤ m) (i : Fin m) :
    (finRotate m).symm i ≠ finRotate m i := by
  -- A coincidence would make the square of the full cycle fix an index, contradicting its order.
  have htwo_three : 2 ≤ 3 := by
    norm_num
  have hm_two : 2 ≤ m := hm.trans' htwo_three
  have hcycle := isCycle_finRotate_of_le hm_two
  have horder : orderOf (finRotate m) = m := by
    rw [hcycle.orderOf, support_finRotate_of_le hm_two, Finset.card_univ,
      Fintype.card_fin]
  have hsupp : ((finRotate m) ^ 2).support = (finRotate m).support := by
    apply hcycle.support_pow_of_pos_of_lt_orderOf
    · norm_num
    · rwa [horder]
  have hi : i ∈ ((finRotate m) ^ 2).support := by
    rw [hsupp, support_finRotate_of_le hm_two]
    exact Finset.mem_univ i
  intro h
  have hfix : ((finRotate m) ^ 2) i = i := by
    rw [pow_two, Equiv.Perm.mul_apply, ← h, (finRotate m).apply_symm_apply]
  exact (Equiv.Perm.mem_support.mp hi) hfix

/-- The inward closed half-plane supported by the `i`th directed edge. -/
def supportingHalfspace (poly : CyclicPolygon n) (i : Fin n) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {x |
    0 ≤ signedArea
      (poly.toPolygon.vertices (finRotate n i) - poly.toPolygon.vertices i)
      (x - poly.toPolygon.vertices i)}

/-- Membership in a supporting half-plane is expressed by nonnegative signed area. -/
theorem mem_supportingHalfspace_iff (poly : CyclicPolygon n) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ poly.supportingHalfspace i ↔
      0 ≤ signedArea
        (poly.toPolygon.vertices (finRotate n i) - poly.toPolygon.vertices i)
        (x - poly.toPolygon.vertices i) := by rfl

/-- The polygonal region determined by the inward supporting half-planes. -/
def region (poly : CyclicPolygon n) : Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋂ i, poly.supportingHalfspace i

/-- The source-defined region is the intersection of its supporting half-planes. -/
theorem region_eq_iInter_supportingHalfspace (poly : CyclicPolygon n) :
    poly.region = ⋂ i, poly.supportingHalfspace i := by
  unfold region
  rfl

/-- Helper for Definition 74.1: a finite, strictly oriented planar cycle is the intersection
of the inward half-spaces of its cyclic edges. -/
theorem convexHull_eq_iInter_orientedEdges {m : ℕ}
    (v : Fin m → EuclideanSpace ℝ (Fin 2)) (hm : 3 ≤ m)
    (harea : ∀ i j, 0 ≤ signedArea (v (finRotate m i) - v i) (v j - v i))
    (hzero : ∀ i j,
      signedArea (v (finRotate m i) - v i) (v j - v i) = 0 ↔
        j = i ∨ j = finRotate m i) :
    convexHull ℝ (Set.range v) =
      ⋂ i, {x | 0 ≤ signedArea (v (finRotate m i) - v i) (x - v i)} := by
  -- Vertex containment and convexity give the easy inclusion into all inward half-spaces.
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro _ ⟨j, rfl⟩
      rw [mem_iInter]
      exact fun i ↦ harea i j
    · exact convex_iInter fun i ↦ convex_signedArea_sub_nonneg _ _
  · intro x hx
    -- Separate an alleged exterior point, then maximize the separator on the finite vertices.
    by_contra hxc
    have hclosed : IsClosed (convexHull ℝ (Set.range v)) :=
      (Set.finite_range v).isClosed_convexHull ℝ
    obtain ⟨f, u, hfv, hux⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ (Set.range v)) hclosed hxc
    classical
    have huniv : (Finset.univ : Finset (Fin m)).Nonempty := by
      have hzero_three : 0 < 3 := by
        norm_num
      have hm_pos : 0 < m := lt_of_lt_of_le hzero_three hm
      let i0 : Fin m := ⟨0, hm_pos⟩
      exact ⟨i0, Finset.mem_univ i0⟩
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun k ↦ f (v k)) huniv
    let prev : Fin m := (finRotate m).symm i
    let a := v (finRotate m i) - v i
    let b := v prev - v i
    let d := x - v i
    have hm_two : 2 ≤ m := by
      omega
    have hnext_ne : finRotate m i ≠ i := finRotate_ne_self_of_two_le hm_two i
    have hprev_ne : prev ≠ i := by
      intro hprev
      apply hnext_ne
      have happly := congrArg (finRotate m) hprev
      simpa only [prev, (finRotate m).apply_symm_apply] using happly.symm
    have hprev_next : prev ≠ finRotate m i :=
      finRotate_symm_ne_finRotate_of_three_le hm i
    have hdet_ne : signedArea a b ≠ 0 := by
      intro hab
      have hab' : signedArea (v (finRotate m i) - v i) (v prev - v i) = 0 := by
        simpa [a, b] using hab
      have hendpoints := (hzero i prev).mp hab'
      exact hendpoints.elim hprev_ne hprev_next
    have hdet_nonneg : 0 ≤ signedArea a b := by
      simpa [a, b] using harea i prev
    have hdet_pos : 0 < signedArea a b := lt_of_le_of_ne hdet_nonneg hdet_ne.symm
    have hxi : 0 ≤ signedArea a d := by
      exact mem_iInter.mp hx i
    have hxprev : 0 ≤ signedArea (v i - v prev) (x - v prev) := by
      have hp := mem_iInter.mp hx prev
      simpa only [mem_setOf_eq, prev, (finRotate m).apply_symm_apply] using hp
    have hbd : 0 ≤ -signedArea b d := by
      rw [← signedArea_sub_swap (v i) (v prev) x]
      exact hxprev
    have halpha : 0 ≤ -signedArea b d / signedArea a b :=
      div_nonneg hbd hdet_pos.le
    have hbeta : 0 ≤ signedArea a d / signedArea a b :=
      div_nonneg hxi hdet_pos.le
    have hfa : f a ≤ 0 := by
      dsimp [a]
      rw [f.map_sub]
      exact sub_nonpos.mpr (hi _ (Finset.mem_univ _))
    have hfb : f b ≤ 0 := by
      dsimp [b]
      rw [f.map_sub]
      exact sub_nonpos.mpr (hi _ (Finset.mem_univ _))
    have hfd_nonpos : f d ≤ 0 := by
      rw [eq_signedArea_coordinates hdet_ne d, f.map_add, f.map_smul, f.map_smul]
      simp only [smul_eq_mul]
      exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos halpha hfa)
        (mul_nonpos_of_nonneg_of_nonpos hbeta hfb)
    have hfd_pos : 0 < f d := by
      have hvi : v i ∈ convexHull ℝ (Set.range v) :=
        subset_convexHull ℝ (Set.range v) ⟨i, rfl⟩
      have hfvi := hfv (v i) hvi
      dsimp [d]
      rw [f.map_sub]
      linarith
    exact (not_lt_of_ge hfd_nonpos) hfd_pos

/-- The supporting-half-plane region is also the convex hull of the cyclic vertices. -/
theorem region_eq_convexHull (poly : CyclicPolygon n) :
    poly.region = convexHull ℝ (Set.range poly.toPolygon.vertices) := by
  -- Apply the generic oriented-cycle theorem using the circle determinant invariant.
  rw [poly.region_eq_iInter_supportingHalfspace]
  symm
  have horiented := convexHull_eq_iInter_orientedEdges poly.toPolygon.vertices poly.three_le
    (fun i j ↦ (poly.signedArea_edge_vertex_nonneg_and_eq_zero i j).1)
    (fun i j ↦ (poly.signedArea_edge_vertex_nonneg_and_eq_zero i j).2)
  simpa only [supportingHalfspace] using horiented

/-- The `i`th closed edge of the cyclic polygon. -/
abbrev edgeSet (poly : CyclicPolygon n) (i : Fin n) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  poly.toPolygon.edgeSet ℝ i

/-- The owner-local edge set is the corresponding mathlib polygon edge. -/
theorem edgeSet_def (poly : CyclicPolygon n) (i : Fin n) :
    poly.edgeSet i = poly.toPolygon.edgeSet ℝ i := rfl

/-- The union of all cyclic edges of the polygon. -/
abbrev boundary (poly : CyclicPolygon n) : Set (EuclideanSpace ℝ (Fin 2)) :=
  poly.toPolygon.boundary ℝ

/-- The boundary is the union of the cyclic edge sets. -/
theorem boundary_def (poly : CyclicPolygon n) :
    poly.boundary = ⋃ i, poly.edgeSet i := rfl

/-- The source-defined interior, obtained by removing the boundary from the region. -/
def interior (poly : CyclicPolygon n) : Set (EuclideanSpace ℝ (Fin 2)) :=
  poly.region \ poly.boundary

/-- The source-defined interior is the region minus its boundary. -/
theorem interior_def (poly : CyclicPolygon n) :
    poly.interior = poly.region \ poly.boundary := by
  unfold interior
  rfl

/-- Every cyclic vertex belongs to the filled region. -/
theorem vertex_mem_region (poly : CyclicPolygon n) (i : Fin n) :
    poly.toPolygon.vertices i ∈ poly.region := by
  -- A generating vertex belongs to the convex hull presentation of the region.
  rw [poly.region_eq_convexHull]
  exact subset_convexHull ℝ (Set.range poly.toPolygon.vertices) ⟨i, rfl⟩

/-- The `i`th vertex regarded as a point of the filled polygonal region. -/
def vertexPoint (poly : CyclicPolygon n) (i : Fin n) : poly.region :=
  ⟨poly.toPolygon.vertices i, poly.vertex_mem_region i⟩

/-- Helper for Proposition 76.2: viewing a cyclic vertex in the filled region
preserves its ambient point. -/
theorem vertexPoint_coe (poly : CyclicPolygon n) (i : Fin n) :
    (poly.vertexPoint i : EuclideanSpace ℝ (Fin 2)) =
      poly.toPolygon.vertices i := by
  -- The region subtype stores only the vertex-membership proof.
  rfl

/-- Every cyclic edge is contained in the filled region. -/
theorem edgeSet_subset_region (poly : CyclicPolygon n) (i : Fin n) :
    poly.edgeSet i ⊆ poly.region := by
  -- Each edge is the segment between two generators of the region's convex hull.
  rw [poly.region_eq_convexHull, edgeSet_def]
  unfold Polygon.edgeSet
  rw [affineSegment_eq_segment]
  apply segment_subset_convexHull
  · exact ⟨i, rfl⟩
  · exact ⟨finRotate n i, rfl⟩

/-- Helper for Definition 74.1: inside the region, equality in one supporting inequality
characterizes the corresponding closed edge. -/
theorem mem_edgeSet_iff_mem_region_and_signedArea_eq_zero (poly : CyclicPolygon n) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ poly.edgeSet i ↔
      x ∈ poly.region ∧
        signedArea
          (poly.toPolygon.vertices (finRotate n i) - poly.toPolygon.vertices i)
          (x - poly.toPolygon.vertices i) = 0 := by
  -- Points of the segment satisfy its supporting-line equation.
  constructor
  · intro hx
    refine ⟨poly.edgeSet_subset_region i hx, ?_⟩
    rw [edgeSet_def] at hx
    unfold Polygon.edgeSet at hx
    rw [affineSegment_eq_segment, segment_eq_image_lineMap] at hx
    obtain ⟨t, _, rfl⟩ := hx
    rw [AffineMap.lineMap_apply_module']
    unfold signedArea
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  · rintro ⟨hxregion, hxzero⟩
    -- Decompose the based point in the edge/predecessor basis; the zero determinant removes
    -- the predecessor coordinate, while adjacent half-spaces bound the edge parameter.
    classical
    let prev : Fin n := (finRotate n).symm i
    let next : Fin n := finRotate n i
    let a := poly.toPolygon.vertices next - poly.toPolygon.vertices i
    let b := poly.toPolygon.vertices prev - poly.toPolygon.vertices i
    let d := x - poly.toPolygon.vertices i
    let α := -signedArea b d / signedArea a b
    have htwo_three : 2 ≤ 3 := by
      norm_num
    have hn_two : 2 ≤ n := poly.three_le.trans' htwo_three
    have hnext_ne : next ≠ i := finRotate_ne_self_of_two_le hn_two i
    have hprev_ne : prev ≠ i := by
      intro hprev
      apply hnext_ne
      have happly := congrArg (finRotate n) hprev
      simpa only [prev, next, (finRotate n).apply_symm_apply] using happly.symm
    have hprev_next : prev ≠ next :=
      finRotate_symm_ne_finRotate_of_three_le poly.three_le i
    have hdet_ne : signedArea a b ≠ 0 := by
      intro hdet
      have hdet' : signedArea
          (poly.toPolygon.vertices (finRotate n i) - poly.toPolygon.vertices i)
          (poly.toPolygon.vertices prev - poly.toPolygon.vertices i) = 0 := by
        simpa [a, b, next] using hdet
      have hendpoints :=
        (poly.signedArea_edge_vertex_nonneg_and_eq_zero i prev).2.mp hdet'
      exact hendpoints.elim hprev_ne hprev_next
    have hdet_nonneg : 0 ≤ signedArea a b := by
      simpa [a, b, next] using
        (poly.signedArea_edge_vertex_nonneg_and_eq_zero i prev).1
    have hdet_pos : 0 < signedArea a b := lt_of_le_of_ne hdet_nonneg hdet_ne.symm
    have hxhalf : ∀ k, x ∈ poly.supportingHalfspace k := by
      rw [poly.region_eq_iInter_supportingHalfspace] at hxregion
      exact mem_iInter.mp hxregion
    have hxprev : 0 ≤ signedArea
        (poly.toPolygon.vertices i - poly.toPolygon.vertices prev)
        (x - poly.toPolygon.vertices prev) := by
      have hp := (poly.mem_supportingHalfspace_iff prev x).mp (hxhalf prev)
      simpa only [prev, (finRotate n).apply_symm_apply] using hp
    have hbd : 0 ≤ -signedArea b d := by
      rw [← signedArea_sub_swap (poly.toPolygon.vertices i)
        (poly.toPolygon.vertices prev) x]
      exact hxprev
    have halpha_nonneg : 0 ≤ α := by
      exact div_nonneg hbd hdet_pos.le
    have hd : d = α • a := by
      calc
        d = (-signedArea b d / signedArea a b) • a +
            (signedArea a d / signedArea a b) • b :=
          eq_signedArea_coordinates hdet_ne d
        _ = α • a := by
          have hxad : signedArea a d = 0 := by
            simpa [a, d, next] using hxzero
          rw [hxad, zero_div, zero_smul, add_zero]
    have hxline : x = α • a + poly.toPolygon.vertices i := by
      have hd' : x - poly.toPolygon.vertices i = α • a := by
        simpa [d] using hd
      exact sub_eq_iff_eq_add.mp hd'
    let c := poly.toPolygon.vertices (finRotate n next) - poly.toPolygon.vertices next
    have hi_next : i ≠ next := hnext_ne.symm
    have hi_nextnext : i ≠ finRotate n next := by
      have h := finRotate_symm_ne_finRotate_of_three_le poly.three_le next
      simpa only [next, (finRotate n).symm_apply_apply] using h
    have hc_ne : signedArea c (poly.toPolygon.vertices i - poly.toPolygon.vertices next) ≠ 0 := by
      intro hc
      have hc' : signedArea
          (poly.toPolygon.vertices (finRotate n next) - poly.toPolygon.vertices next)
          (poly.toPolygon.vertices i - poly.toPolygon.vertices next) = 0 := by
        simpa [c] using hc
      have hendpoints :=
        (poly.signedArea_edge_vertex_nonneg_and_eq_zero next i).2.mp hc'
      exact hendpoints.elim hi_next hi_nextnext
    have hc_nonneg : 0 ≤ signedArea c
        (poly.toPolygon.vertices i - poly.toPolygon.vertices next) := by
      simpa [c] using (poly.signedArea_edge_vertex_nonneg_and_eq_zero next i).1
    have hc_pos : 0 < signedArea c
        (poly.toPolygon.vertices i - poly.toPolygon.vertices next) :=
      lt_of_le_of_ne hc_nonneg hc_ne.symm
    have hxnext : 0 ≤ signedArea c (x - poly.toPolygon.vertices next) := by
      have h := (poly.mem_supportingHalfspace_iff next x).mp (hxhalf next)
      simpa [c] using h
    have hxnext_eq : signedArea c (x - poly.toPolygon.vertices next) =
        (1 - α) * signedArea c
          (poly.toPolygon.vertices i - poly.toPolygon.vertices next) := by
      rw [hxline]
      unfold signedArea
      simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      dsimp [a, next]
      ring
    have halpha_one : α ≤ 1 := by
      rw [hxnext_eq] at hxnext
      exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hc_pos).mp hxnext)
    rw [edgeSet_def]
    unfold Polygon.edgeSet
    rw [affineSegment_eq_segment, segment_eq_image_lineMap]
    refine ⟨α, ⟨halpha_nonneg, halpha_one⟩, ?_⟩
    rw [AffineMap.lineMap_apply_module']
    simpa [a, next] using hxline.symm

/-- Helper for Definition 74.1: every directed cyclic edge has a nonzero direction vector. -/
theorem cyclicEdgeVector_ne_zero (poly : CyclicPolygon n) (i : Fin n) :
    poly.toPolygon.vertices (finRotate n i) - poly.toPolygon.vertices i ≠ 0 := by
  -- A zero edge vector would make its determinant with a third cyclic vertex vanish.
  let prev : Fin n := (finRotate n).symm i
  have htwo_three : 2 ≤ 3 := by
    norm_num
  have hn_two : 2 ≤ n := poly.three_le.trans' htwo_three
  have hnext_ne : finRotate n i ≠ i := finRotate_ne_self_of_two_le hn_two i
  have hprev_ne : prev ≠ i := by
    intro hprev
    apply hnext_ne
    have happly := congrArg (finRotate n) hprev
    simpa only [prev, (finRotate n).apply_symm_apply] using happly.symm
  have hprev_next : prev ≠ finRotate n i :=
    finRotate_symm_ne_finRotate_of_three_le poly.three_le i
  intro hedge
  have hzero : signedArea
      (poly.toPolygon.vertices (finRotate n i) - poly.toPolygon.vertices i)
      (poly.toPolygon.vertices prev - poly.toPolygon.vertices i) = 0 := by
    rw [hedge]
    unfold signedArea
    simp
  have hendpoints :=
    (poly.signedArea_edge_vertex_nonneg_and_eq_zero i prev).2.mp hzero
  exact hendpoints.elim hprev_ne hprev_next

/-- Helper for Definition 74.1: the source edge union is the topological frontier of the
filled polygonal region. -/
theorem boundary_eq_frontier (poly : CyclicPolygon n) :
    poly.boundary = frontier poly.region := by
  -- The convex-hull presentation makes the region closed.
  have hclosed : IsClosed poly.region := by
    rw [poly.region_eq_convexHull]
    exact (Set.finite_range poly.toPolygon.vertices).isClosed_convexHull ℝ
  apply Set.Subset.antisymm
  · intro x hxboundary
    rw [poly.boundary_def] at hxboundary
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxboundary
    have hactive :=
      (poly.mem_edgeSet_iff_mem_region_and_signedArea_eq_zero i x).mp hxi
    refine ⟨?_, ?_⟩
    · rw [hclosed.closure_eq]
      exact hactive.1
    · intro hxinterior
      have hregion_subset : poly.region ⊆ poly.supportingHalfspace i := by
        rw [poly.region_eq_iInter_supportingHalfspace]
        exact iInter_subset _ i
      have hhalfInterior := interior_mono hregion_subset hxinterior
      rw [supportingHalfspace,
        interior_signedArea_sub_nonneg (poly.cyclicEdgeVector_ne_zero i)
          (poly.toPolygon.vertices i)] at hhalfInterior
      exact (ne_of_gt hhalfInterior) hactive.2
  · intro x hxfrontier
    have hxregion : x ∈ poly.region := by
      rw [← hclosed.closure_eq]
      exact hxfrontier.1
    have hxhalf : ∀ i, x ∈ poly.supportingHalfspace i := by
      have hxall : x ∈ ⋂ i, poly.supportingHalfspace i := by
        rw [← poly.region_eq_iInter_supportingHalfspace]
        exact hxregion
      exact mem_iInter.mp hxall
    by_contra hxboundary
    apply hxfrontier.2
    rw [poly.region_eq_iInter_supportingHalfspace, interior_iInter_of_finite]
    apply mem_iInter.mpr
    intro i
    rw [supportingHalfspace,
      interior_signedArea_sub_nonneg (poly.cyclicEdgeVector_ne_zero i)
        (poly.toPolygon.vertices i)]
    have hnonneg := (poly.mem_supportingHalfspace_iff i x).mp
      (hxhalf i)
    have hne : signedArea
        (poly.toPolygon.vertices (finRotate n i) - poly.toPolygon.vertices i)
        (x - poly.toPolygon.vertices i) ≠ 0 := by
      intro hzero
      apply hxboundary
      rw [poly.boundary_def]
      apply mem_iUnion.mpr
      exact ⟨i, (poly.mem_edgeSet_iff_mem_region_and_signedArea_eq_zero i x).mpr
        ⟨hxregion, hzero⟩⟩
    exact lt_of_le_of_ne hnonneg hne.symm

/-- Helper for Definition 74.1: frontier membership transports across translation in a
topological real vector space. -/
theorem mem_frontier_vadd_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} (a x : E) :
    x ∈ frontier (a +ᵥ C) ↔ -a + x ∈ frontier C := by
  -- Translate both the closure and interior in the definition of the frontier.
  simp only [frontier, Set.mem_sdiff, closure_vadd, interior_vadd,
    mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]

/-- Helper for Definition 74.1: every noncentral point of a bounded convex set lies on a
unique radial segment from an interior base point to the frontier. -/
theorem existsUnique_frontier_endpoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} (hconv : Convex ℝ C) (hbound : Bornology.IsBounded C)
    {p x : E} (hp : p ∈ _root_.interior C) (hx : x ∈ C) (hxp : x ≠ p) :
    ∃! q, q ∈ frontier C ∧ x ∈ segment ℝ p q := by
  -- Translate the base point to zero and normalize the direction by the Minkowski gauge.
  let S : Set E := -p +ᵥ C
  let v : E := x - p
  let g : ℝ := gauge S v
  have hconvS : Convex ℝ S := by
    simpa [S] using hconv.vadd (-p)
  have hboundS : Bornology.IsVonNBounded ℝ S := by
    simpa [S] using (NormedSpace.isVonNBounded_of_isBounded ℝ hbound).vadd (-p)
  have h0interior : (0 : E) ∈ _root_.interior S := by
    simpa [S, interior_vadd, mem_vadd_set_iff_neg_vadd_mem]
      using hp
  have hSnhds : S ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.mp h0interior
  have hvS : v ∈ S := by
    simpa [S, v, mem_vadd_set_iff_neg_vadd_mem] using hx
  have hvne : v ≠ 0 := sub_ne_zero.mpr hxp
  have hgpos : 0 < g := by
    exact (gauge_pos (absorbent_nhds_zero hSnhds) hboundS).2 hvne
  have hgle : g ≤ 1 := gauge_le_one_of_mem hvS
  let q0 : E := g⁻¹ • v
  let q : E := q0 + p
  have hq0gauge : gauge S q0 = 1 := by
    dsimp [q0]
    rw [gauge_smul_of_nonneg (inv_nonneg.mpr hgpos.le), smul_eq_mul,
      inv_mul_cancel₀ hgpos.ne']
  have hq0frontier : q0 ∈ frontier S :=
    (gauge_eq_one_iff_mem_frontier hconvS hSnhds).mp hq0gauge
  have hqfrontier : q ∈ frontier C := by
    have htranslated := (mem_frontier_vadd_iff (-p) q0).mp hq0frontier
    simpa [q, add_comm, add_left_comm, add_assoc] using htranslated
  have hxsegment : x ∈ segment ℝ p q := by
    rw [segment_eq_image_lineMap]
    refine ⟨g, ⟨hgpos.le, hgle⟩, ?_⟩
    rw [AffineMap.lineMap_apply_module']
    simp only [q, q0, v, add_sub_cancel_right, smul_smul]
    rw [mul_inv_cancel₀ hgpos.ne', one_smul, sub_add_cancel]
  refine ⟨q, ⟨hqfrontier, hxsegment⟩, ?_⟩
  intro y hy
  -- A second endpoint has gauge one; the segment parameter is therefore exactly `g`.
  have hy0frontier : y - p ∈ frontier S := by
    apply (mem_frontier_vadd_iff (-p) (y - p)).mpr
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hy.1
  have hy0gauge : gauge S (y - p) = 1 :=
    (gauge_eq_one_iff_mem_frontier hconvS hSnhds).mpr hy0frontier
  rw [segment_eq_image_lineMap] at hy
  obtain ⟨t, ht, hline⟩ := hy.2
  have htne : t ≠ 0 := by
    intro htzero
    apply hxp
    rw [htzero, AffineMap.lineMap_apply_zero] at hline
    exact hline.symm
  have htpos : 0 < t := lt_of_le_of_ne ht.1 htne.symm
  have hv_eq : v = t • (y - p) := by
    rw [AffineMap.lineMap_apply_module'] at hline
    dsimp [v]
    exact sub_eq_iff_eq_add.mpr hline.symm
  have hgt : g = t := by
    dsimp [g]
    rw [hv_eq, gauge_smul_of_nonneg htpos.le, smul_eq_mul, hy0gauge, mul_one]
  dsimp [q, q0]
  rw [hgt, hv_eq, inv_smul_smul₀ htne, sub_add_cancel]

/-- Helper for Definition 74.1: the filled cyclic polygonal region is convex. -/
theorem convex_region (poly : CyclicPolygon n) : Convex ℝ poly.region := by
  -- Use the convex-hull presentation of the region.
  rw [poly.region_eq_convexHull]
  exact convex_convexHull ℝ (Set.range poly.toPolygon.vertices)

/-- Helper for Definition 74.1: the filled cyclic polygonal region is bounded. -/
theorem isBounded_region (poly : CyclicPolygon n) : Bornology.IsBounded poly.region := by
  -- A convex hull of finitely many vertices is compact, hence bounded.
  rw [poly.region_eq_convexHull]
  exact ((Set.finite_range poly.toPolygon.vertices).isCompact_convexHull ℝ).isBounded

/-- Helper for Definition 74.1: the source-defined interior agrees with the topological
interior of the filled region. -/
theorem interior_eq_topologicalInterior (poly : CyclicPolygon n) :
    poly.interior = _root_.interior poly.region := by
  -- Replace the source boundary by the frontier and use the standard frontier identity.
  rw [poly.interior_def, poly.boundary_eq_frontier, self_sdiff_frontier]

/-- Helper for Definition 74.1: every boundary point belongs to the filled region. -/
theorem boundary_subset_region (poly : CyclicPolygon n) : poly.boundary ⊆ poly.region := by
  -- Each boundary point lies on one of the cyclic edges.
  rw [poly.boundary_def]
  exact iUnion_subset fun i ↦ poly.edgeSet_subset_region i

/-- Radial segments from an interior point cover the polygonal region. -/
theorem region_eq_iUnion_segments (poly : CyclicPolygon n)
    {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ poly.interior) :
    poly.region = ⋃ q ∈ poly.boundary, segment ℝ p q := by
  -- Convert the source interior to the topological interior used by the gauge theorem.
  have hpTop : p ∈ _root_.interior poly.region := by
    rw [← poly.interior_eq_topologicalInterior]
    exact hp
  have hpRegion : p ∈ poly.region := interior_subset hpTop
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hxp : x = p
    · subst x
      have hzero_three : 0 < 3 := by
        norm_num
      have hn : 0 < n := lt_of_lt_of_le hzero_three poly.three_le
      let i : Fin n := ⟨0, hn⟩
      let q := poly.toPolygon.vertices i
      have hqBoundary : q ∈ poly.boundary := by
        rw [poly.boundary_def]
        apply mem_iUnion.mpr
        refine ⟨i, ?_⟩
        rw [edgeSet_def]
        unfold Polygon.edgeSet
        exact left_mem_affineSegment ℝ _ _
      apply mem_iUnion.mpr
      refine ⟨q, ?_⟩
      apply mem_iUnion.mpr
      exact ⟨hqBoundary, left_mem_segment ℝ p q⟩
    · obtain ⟨q, hq, _⟩ := existsUnique_frontier_endpoint poly.convex_region
        poly.isBounded_region hpTop hx hxp
      apply mem_iUnion.mpr
      refine ⟨q, ?_⟩
      apply mem_iUnion.mpr
      rw [poly.boundary_eq_frontier]
      exact ⟨hq.1, hq.2⟩
  · intro x hx
    obtain ⟨q, hx⟩ := mem_iUnion.mp hx
    obtain ⟨hq, hxsegment⟩ := mem_iUnion.mp hx
    exact poly.convex_region.segment_subset hpRegion (poly.boundary_subset_region hq) hxsegment

/-- Radial segments to distinct boundary points meet only at the interior point. -/
theorem segment_inter_segment (poly : CyclicPolygon n)
    {p q r : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ poly.interior)
    (hq : q ∈ poly.boundary) (hr : r ∈ poly.boundary) (hqr : q ≠ r) :
    segment ℝ p q ∩ segment ℝ p r = {p} := by
  -- Convert all source-facing memberships to the convex/frontier interface.
  have hpTop : p ∈ _root_.interior poly.region := by
    rw [← poly.interior_eq_topologicalInterior]
    exact hp
  have hpRegion : p ∈ poly.region := interior_subset hpTop
  have hqRegion : q ∈ poly.region := poly.boundary_subset_region hq
  have hrRegion : r ∈ poly.region := poly.boundary_subset_region hr
  have hqFrontier : q ∈ frontier poly.region := by
    rw [← poly.boundary_eq_frontier]
    exact hq
  have hrFrontier : r ∈ frontier poly.region := by
    rw [← poly.boundary_eq_frontier]
    exact hr
  apply Set.Subset.antisymm
  · intro z hz
    rw [mem_inter_iff] at hz
    by_cases hzp : z = p
    · subst z
      exact mem_singleton p
    · have hzRegion : z ∈ poly.region :=
        poly.convex_region.segment_subset hpRegion hqRegion hz.1
      obtain ⟨s, _, hsUnique⟩ := existsUnique_frontier_endpoint poly.convex_region
        poly.isBounded_region hpTop hzRegion hzp
      have hqs : q = s := hsUnique q ⟨hqFrontier, hz.1⟩
      have hrs : r = s := hsUnique r ⟨hrFrontier, hz.2⟩
      exact False.elim (hqr (hqs.trans hrs.symm))
  · intro z hz
    rw [mem_singleton_iff] at hz
    subst z
    exact ⟨left_mem_segment ℝ p q, left_mem_segment ℝ p r⟩


end

end CyclicPolygon
