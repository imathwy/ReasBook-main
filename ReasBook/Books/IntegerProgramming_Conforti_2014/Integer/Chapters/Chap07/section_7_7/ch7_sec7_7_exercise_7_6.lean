import Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_7
import Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2

open scoped Matrix

section Exercise76

/-- The concrete binary set
`S = {(1,1,0), (1,0,0), (0,1,0), (1,0,1), (0,1,1)} ⊆ {0,1}^3`
used for Exercise 7.6, with zero-based coordinates on `Fin 3`. -/
def exercise_7_6_binary_example_set : Set (Fin 3 → ℝ) :=
  { ![(1 : ℝ), 1, 0],
    ![(1 : ℝ), 0, 0],
    ![(0 : ℝ), 1, 0],
    ![(1 : ℝ), 0, 1],
    ![(0 : ℝ), 1, 1] }

/-- Membership in `exercise_7_6_binary_example_set` means being one of the five explicit binary
points used in the example. -/
theorem mem_exercise_7_6_binary_example_set_iff
    (x : Fin 3 → ℝ) :
    x ∈ exercise_7_6_binary_example_set ↔
      x = ![(1 : ℝ), 1, 0] ∨
        x = ![(1 : ℝ), 0, 0] ∨
        x = ![(0 : ℝ), 1, 0] ∨
        x = ![(1 : ℝ), 0, 1] ∨
        x = ![(0 : ℝ), 1, 1] := by
  simp [exercise_7_6_binary_example_set]

/-- The polytope `conv(S)` attached to the explicit Exercise 7.6 example. -/
def exercise_7_6_polytope : Set (Fin 3 → ℝ) :=
  convexHull ℝ exercise_7_6_binary_example_set

/-- Expanding `exercise_7_6_polytope` recovers the convex hull of the five-point example set. -/
theorem exercise_7_6_polytope_eq_convexHull :
    exercise_7_6_polytope = convexHull ℝ exercise_7_6_binary_example_set := rfl

/-- The zero-tail slice `conv(S) ∩ {x | x₃ = 0}` from Exercise 7.6, encoded on `Fin 3` by the
zero-based coordinate condition `x 2 = 0`. -/
def exercise_7_6_zero_tail_slice : Set (Fin 3 → ℝ) :=
  exercise_7_6_polytope ∩ {x : Fin 3 → ℝ | x 2 = 0}

/-- Membership in `exercise_7_6_zero_tail_slice` means belonging to `conv(S)` and satisfying the
slice equation `x₃ = 0`. -/
theorem mem_exercise_7_6_zero_tail_slice_iff
    (x : Fin 3 → ℝ) :
    x ∈ exercise_7_6_zero_tail_slice ↔
      x ∈ exercise_7_6_polytope ∧ x 2 = 0 := Iff.rfl

/-- The base coefficient vector `(1,1,0)` defining the slice inequality `x₁ + x₂ ≤ 2`. -/
def exercise_7_6_base_coeffs : Fin 3 → ℝ :=
  ![(1 : ℝ), 1, 0]

/-- The base coefficient vector of the Exercise 7.6 example is exactly `(1,1,0)`. -/
theorem exercise_7_6_base_coeffs_eq :
    exercise_7_6_base_coeffs = ![(1 : ℝ), 1, 0] := rfl

/-- The lifted coefficient vector `(1,1,1)` defining the lifted inequality `x₁ + x₂ + x₃ ≤ 2`.
-/
def exercise_7_6_lifted_coeffs : Fin 3 → ℝ :=
  ![(1 : ℝ), 1, 1]

/-- The lifted coefficient vector of the Exercise 7.6 example is exactly `(1,1,1)`. -/
theorem exercise_7_6_lifted_coeffs_eq :
    exercise_7_6_lifted_coeffs = ![(1 : ℝ), 1, 1] := rfl

/-- The face of the slice cut out by the base inequality `x₁ + x₂ ≤ 2`. -/
def exercise_7_6_base_face : Set (Fin 3 → ℝ) :=
  {x | x ∈ exercise_7_6_zero_tail_slice ∧ exercise_7_6_base_coeffs ⬝ᵥ x = 2}

/-- Membership in `exercise_7_6_base_face` means belonging to the zero-tail slice and meeting the
base inequality at equality. -/
theorem mem_exercise_7_6_base_face_iff
    (x : Fin 3 → ℝ) :
    x ∈ exercise_7_6_base_face ↔
      x ∈ exercise_7_6_zero_tail_slice ∧ exercise_7_6_base_coeffs ⬝ᵥ x = 2 := Iff.rfl

/-- The face of `conv(S)` cut out by the lifted inequality `x₁ + x₂ + x₃ ≤ 2`. -/
def exercise_7_6_lifted_face : Set (Fin 3 → ℝ) :=
  {x | x ∈ exercise_7_6_polytope ∧ exercise_7_6_lifted_coeffs ⬝ᵥ x = 2}

/-- Membership in `exercise_7_6_lifted_face` means belonging to `conv(S)` and meeting the lifted
inequality at equality. -/
theorem mem_exercise_7_6_lifted_face_iff
    (x : Fin 3 → ℝ) :
    x ∈ exercise_7_6_lifted_face ↔
      x ∈ exercise_7_6_polytope ∧ exercise_7_6_lifted_coeffs ⬝ᵥ x = 2 := Iff.rfl

/-- Helper for Exercise 7.6: every listed example vertex belongs to the polytope `conv(S)`. -/
theorem mem_exercise_7_6_polytope_of_mem_example_set
    {x : Fin 3 → ℝ}
    (hx : x ∈ exercise_7_6_binary_example_set) :
    x ∈ exercise_7_6_polytope := by
  -- The example vertices are the generators of the convex hull defining the polytope.
  rw [exercise_7_6_polytope_eq_convexHull]
  exact subset_convexHull ℝ exercise_7_6_binary_example_set hx

/-- Helper for Exercise 7.6: the explicit polytope is contained in the ambient unit box. -/
theorem exercise_7_6_polytope_subset_unit_box :
    exercise_7_6_polytope ⊆ Set.univ.pi (fun _ : Fin 3 ↦ Set.Icc (0 : ℝ) 1) := by
  -- Convexity of the unit box lifts the vertexwise `0/1` bounds to the whole convex hull.
  rw [exercise_7_6_polytope_eq_convexHull]
  refine convexHull_min ?_ ?_
  · intro x hx
    rcases (mem_exercise_7_6_binary_example_set_iff x).1 hx with
      rfl | rfl | rfl | rfl | rfl
    all_goals
      rw [Set.mem_pi]
      intro i hi
      fin_cases i <;> norm_num
  · exact convex_pi fun _ _ ↦ convex_Icc (0 : ℝ) 1

/-- Helper for Exercise 7.6: every coordinate of a point in the polytope lies in `[0, 1]`. -/
theorem exercise_7_6_polytope_coord_mem_Icc
    {x : Fin 3 → ℝ}
    (hx : x ∈ exercise_7_6_polytope)
    (i : Fin 3) :
    x i ∈ Set.Icc (0 : ℝ) 1 := by
  -- Read the coordinatewise box bound from `exercise_7_6_polytope_subset_unit_box`.
  have hxBox := exercise_7_6_polytope_subset_unit_box hx
  simpa [Set.mem_pi] using hxBox i (by simp)

/-- Helper for Exercise 7.6: the lifted inequality `x₁ + x₂ + x₃ ≤ 2` is valid on the whole
example polytope. -/
theorem exercise_7_6_valid_lifted_inequality :
    is_valid_inequality exercise_7_6_polytope exercise_7_6_lifted_coeffs 2 := by
  let halfspace : Set (Fin 3 → ℝ) :=
    {x | exercise_7_6_lifted_coeffs ⬝ᵥ x ≤ 2}
  have hvertices : exercise_7_6_binary_example_set ⊆ halfspace := by
    -- Each of the five listed vertices satisfies the lifted inequality directly.
    intro x hx
    rcases (mem_exercise_7_6_binary_example_set_iff x).1 hx with
      rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [halfspace, exercise_7_6_lifted_coeffs_eq, dotProduct, Fin.sum_univ_three]
    all_goals
      norm_num
  have hhalfspace_convex : Convex ℝ halfspace := by
    -- The inequality halfspace is the linear preimage of the interval `(-∞, 2]`.
    let f : Module.Dual ℝ (Fin 3 → ℝ) :=
      ∑ i, exercise_7_6_lifted_coeffs i • LinearMap.proj i
    have hpreimage :
        halfspace = f ⁻¹' Set.Iic (2 : ℝ) := by
      ext x
      simp [halfspace, f, exercise_7_6_lifted_coeffs_eq, dotProduct]
    rw [hpreimage]
    exact (convex_Iic (2 : ℝ)).linear_preimage f
  have hsubset : exercise_7_6_polytope ⊆ halfspace := by
    -- Vertexwise validity extends from the generators to the entire convex hull.
    rw [exercise_7_6_polytope_eq_convexHull]
    exact convexHull_min hvertices hhalfspace_convex
  -- Unpack the halfspace inclusion back into inequality validity.
  intro x hx
  exact hsubset hx

/-- Helper for Exercise 7.6: the base face is the canonical equality face on the zero-tail slice.
-/
theorem exercise_7_6_base_face_eq_face_set :
    exercise_7_6_base_face = face_set exercise_7_6_zero_tail_slice exercise_7_6_base_coeffs 2 := by
  -- Both sets are defined by the same slice-membership and equality conditions.
  ext x
  rw [mem_exercise_7_6_base_face_iff, mem_face_set_iff]

/-- Helper for Exercise 7.6: the lifted face is the canonical equality face on the whole polytope.
-/
theorem exercise_7_6_lifted_face_eq_face_set :
    exercise_7_6_lifted_face = face_set exercise_7_6_polytope exercise_7_6_lifted_coeffs 2 := by
  -- Both sets are defined by the same polytope-membership and equality conditions.
  ext x
  rw [mem_exercise_7_6_lifted_face_iff, mem_face_set_iff]

/-- Helper for Exercise 7.6: restricting the lifted inequality to the zero-tail slice gives the
base inequality `x₁ + x₂ ≤ 2`. -/
theorem exercise_7_6_valid_base_inequality_on_slice :
    is_valid_inequality exercise_7_6_zero_tail_slice exercise_7_6_base_coeffs 2 := by
  intro x hx
  rcases (mem_exercise_7_6_zero_tail_slice_iff x).1 hx with ⟨hxPolytope, hx2⟩
  -- On the slice, the lifted inequality specializes by the equation `x 2 = 0`.
  have hLift := exercise_7_6_valid_lifted_inequality hxPolytope
  simpa [exercise_7_6_base_coeffs_eq, exercise_7_6_lifted_coeffs_eq, dotProduct,
    Fin.sum_univ_three, hx2] using hLift

/-- Helper for Exercise 7.6: the base equality face on the slice is exactly the singleton
`{(1,1,0)}`. -/
theorem exercise_7_6_base_face_eq_singleton :
    exercise_7_6_base_face = ({![(1 : ℝ), 1, 0]} : Set (Fin 3 → ℝ)) := by
  ext x
  constructor
  · intro hx
    rcases (mem_exercise_7_6_base_face_iff x).1 hx with ⟨hxSlice, hxEq⟩
    rcases (mem_exercise_7_6_zero_tail_slice_iff x).1 hxSlice with ⟨hxPolytope, hx2⟩
    have hx0Mem := exercise_7_6_polytope_coord_mem_Icc hxPolytope 0
    have hx1Mem := exercise_7_6_polytope_coord_mem_Icc hxPolytope 1
    have hsum : x 0 + x 1 = 2 := by
      simpa [exercise_7_6_base_coeffs_eq, dotProduct, Fin.sum_univ_three, hx2] using hxEq
    have hx0 : x 0 = 1 := by
      have hx1le : x 1 ≤ 1 := hx1Mem.2
      have hx0le : x 0 ≤ 1 := hx0Mem.2
      have hx0ge : 1 ≤ x 0 := by
        linarith
      linarith
    have hx1 : x 1 = 1 := by
      have hx0le : x 0 ≤ 1 := hx0Mem.2
      have hx1le : x 1 ≤ 1 := hx1Mem.2
      have hx1ge : 1 ≤ x 1 := by
        linarith
      linarith
    -- The box bounds and the equality force the unique slice point `(1,1,0)`.
    have hxPoint : x = ![(1 : ℝ), 1, 0] := by
      ext i
      fin_cases i <;> simp [hx0, hx1, hx2]
    simpa [Set.mem_singleton_iff] using hxPoint
  · rintro rfl
    -- The unique tight slice vertex is one of the original generators, hence belongs to the face.
    let p : Fin 3 → ℝ := ![(1 : ℝ), 1, 0]
    have hPolytope : p ∈ exercise_7_6_polytope := by
      exact mem_exercise_7_6_polytope_of_mem_example_set (by
        simp [p, exercise_7_6_binary_example_set])
    have hp2 : p 2 = 0 := by
      simp [p]
    have hp0 : p 0 = 1 := by
      simp [p]
    have hp1 : p 1 = 1 := by
      simp [p]
    refine (mem_exercise_7_6_base_face_iff p).2 ?_
    refine ⟨(mem_exercise_7_6_zero_tail_slice_iff p).2 ?_, ?_⟩
    · exact ⟨hPolytope, hp2⟩
    · calc
        exercise_7_6_base_coeffs ⬝ᵥ p = p 0 + p 1 + 0 * p 2 := by
          simp [exercise_7_6_base_coeffs_eq, dotProduct, Fin.sum_univ_three]
      _ = 2 := by
          norm_num [hp0, hp1, hp2]

/-- Helper for Exercise 7.6: the four vertices `(1,0,0)`, `(1,1,0)`, `(1,0,1)`, and `(0,1,0)`
are affinely independent in `ℝ^3`. -/
theorem exercise_7_6_polytope_affineIndependentFamily :
    AffineIndependent ℝ
      ![(![(1 : ℝ), 0, 0] : Fin 3 → ℝ),
        ![(1 : ℝ), 1, 0],
        ![(1 : ℝ), 0, 1],
        ![(0 : ℝ), 1, 0]] := by
  rw [affineIndependent_iff_linearIndependent_tail_sub]
  let e1 : Fin 3 → ℝ := Pi.single 1 1
  let e2 : Fin 3 → ℝ := Pi.single 2 1
  let v : Fin 3 → ℝ := -Pi.single 0 1 + Pi.single 1 1
  have htail :
      (fun i : Fin 3 ↦
        ![(![(1 : ℝ), 0, 0] : Fin 3 → ℝ),
          ![(1 : ℝ), 1, 0],
          ![(1 : ℝ), 0, 1],
          ![(0 : ℝ), 1, 0]] i.succ -
          ![(![(1 : ℝ), 0, 0] : Fin 3 → ℝ),
            ![(1 : ℝ), 1, 0],
            ![(1 : ℝ), 0, 1],
            ![(0 : ℝ), 1, 0]] 0) = ![e1, e2, v] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e1, e2, v]
  rw [htail]
  have hpair : LinearIndependent ℝ ![e2, v] := by
    have he2_ne : e2 ≠ 0 := by
      intro hzero
      have hcoord := congrArg (fun x : Fin 3 → ℝ ↦ x 2) hzero
      simp [e2] at hcoord
    apply (LinearIndependent.pair_iff' he2_ne).2
    intro a ha
    have hcoord := congrArg (fun x : Fin 3 → ℝ ↦ x 0) ha
    simp [e2, v] at hcoord
  have he1_not_mem : e1 ∉ Submodule.span ℝ (Set.range ![e2, v]) := by
    intro he1_mem
    have he1_mem' : e1 ∈ Submodule.span ℝ ({v, e2} : Set (Fin 3 → ℝ)) := by
      simpa using he1_mem
    rcases (Submodule.mem_span_pair).1 he1_mem' with ⟨a, b, hab⟩
    have hcoord0 := congrArg (fun x : Fin 3 → ℝ ↦ x 0) hab
    have hcoord1 := congrArg (fun x : Fin 3 → ℝ ↦ x 1) hab
    have hcoord2 := congrArg (fun x : Fin 3 → ℝ ↦ x 2) hab
    simp [e1, e2, v] at hcoord0 hcoord1 hcoord2
    linarith
  have hlin : LinearIndependent ℝ (Fin.cons e1 ![e2, v] : Fin 3 → Fin 3 → ℝ) :=
    hpair.finCons he1_not_mem
  exact hlin

/-- Helper for Exercise 7.6: the three slice vertices `(1,0,0)`, `(1,1,0)`, and `(0,1,0)` are
affinely independent. -/
theorem exercise_7_6_zero_tail_slice_affineIndependentFamily :
    AffineIndependent ℝ
      ![(![(1 : ℝ), 0, 0] : Fin 3 → ℝ),
        ![(1 : ℝ), 1, 0],
        ![(0 : ℝ), 1, 0]] := by
  rw [affineIndependent_iff_linearIndependent_tail_sub]
  let e1 : Fin 3 → ℝ := Pi.single 1 1
  let v : Fin 3 → ℝ := -Pi.single 0 1 + Pi.single 1 1
  have htail :
      (fun i : Fin 2 ↦
        ![(![(1 : ℝ), 0, 0] : Fin 3 → ℝ),
          ![(1 : ℝ), 1, 0],
          ![(0 : ℝ), 1, 0]] i.succ -
          ![(![(1 : ℝ), 0, 0] : Fin 3 → ℝ),
            ![(1 : ℝ), 1, 0],
            ![(0 : ℝ), 1, 0]] 0) = ![e1, v] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e1, v]
  rw [htail]
  have he1_ne : e1 ≠ 0 := by
    intro hzero
    have hcoord := congrArg (fun x : Fin 3 → ℝ ↦ x 1) hzero
    simp [e1] at hcoord
  apply (LinearIndependent.pair_iff' he1_ne).2
  intro a ha
  have hcoord := congrArg (fun x : Fin 3 → ℝ ↦ x 0) ha
  -- The first coordinate isolates the scalar coefficient.
  simp [e1, v] at hcoord

/-- Helper for Exercise 7.6: the three lifted-face vertices `(1,1,0)`, `(1,0,1)`, and `(0,1,1)`
are affinely independent. -/
theorem exercise_7_6_lifted_face_affineIndependentFamily :
    AffineIndependent ℝ
      ![(![(1 : ℝ), 1, 0] : Fin 3 → ℝ),
        ![(1 : ℝ), 0, 1],
        ![(0 : ℝ), 1, 1]] := by
  rw [affineIndependent_iff_linearIndependent_tail_sub]
  let v1 : Fin 3 → ℝ := ![(0 : ℝ), -1, 1]
  let v2 : Fin 3 → ℝ := ![(-1 : ℝ), 0, 1]
  have htail :
      (fun i : Fin 2 ↦
        ![(![(1 : ℝ), 1, 0] : Fin 3 → ℝ),
          ![(1 : ℝ), 0, 1],
          ![(0 : ℝ), 1, 1]] i.succ -
          ![(![(1 : ℝ), 1, 0] : Fin 3 → ℝ),
            ![(1 : ℝ), 0, 1],
            ![(0 : ℝ), 1, 1]] 0) = ![v1, v2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [v1, v2]
  rw [htail]
  have hv1_ne : v1 ≠ 0 := by
    intro hv1_zero
    have hcoord := congrArg (fun x : Fin 3 → ℝ ↦ x 2) hv1_zero
    simp [v1] at hcoord
  apply (LinearIndependent.pair_iff' hv1_ne).2
  intro a ha
  have hcoord := congrArg (fun x : Fin 3 → ℝ ↦ x 0) ha
  -- The first coordinate again forces the scalar coefficient to vanish.
  simp [v1, v2] at hcoord

/-- Helper for Exercise 7.6: four affinely independent points in `ℝ^3` already span the ambient
affine space. -/
private theorem affineSpan_eq_top_of_affineIndependentFamily
    {P : Set (Fin 3 → ℝ)} {p : Fin 4 → Fin 3 → ℝ}
    (hp : AffineIndependent ℝ p)
    (hp_range : Set.range p ⊆ P) :
    affineSpan ℝ P = ⊤ := by
  have hp_top : affineSpan ℝ (Set.range p) = ⊤ := by
    -- A `Fin 4`-indexed affinely independent family in `ℝ^3` already has maximal affine span.
    exact
      (hp.affineSpan_eq_top_iff_card_eq_finrank_add_one).2
        (by simp [Module.finrank_fintype_fun_eq_card])
  apply top_unique
  have hle : affineSpan ℝ (Set.range p) ≤ affineSpan ℝ P :=
    affineSpan_mono ℝ hp_range
  simpa [hp_top] using hle

/-- Helper for Exercise 7.6: a zero-tail convex combination of the five example vertices cannot
use the two vertices with third coordinate `1`. -/
private theorem exercise_7_6_zero_tail_weights_vanish
    {w : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ}
    (hw_nonneg :
      ∀ y ∈ ({![(1 : ℝ), 1, 0], ![(1 : ℝ), 0, 0], ![(0 : ℝ), 1, 0], ![(1 : ℝ), 0, 1],
        ![(0 : ℝ), 1, 1]} : Finset (Fin 3 → ℝ)),
        0 ≤ w y)
    (hw_eq :
      ∑ y ∈ ({![(1 : ℝ), 1, 0], ![(1 : ℝ), 0, 0], ![(0 : ℝ), 1, 0], ![(1 : ℝ), 0, 1],
        ![(0 : ℝ), 1, 1]} : Finset (Fin 3 → ℝ)),
        w y • y = x)
    (hx2 : x 2 = 0) :
    w ![(1 : ℝ), 0, 1] = 0 ∧ w ![(0 : ℝ), 1, 1] = 0 := by
  -- Reading the third coordinate leaves only the two lifted vertices.
  have hcoord := congrArg (fun z : Fin 3 → ℝ ↦ z 2) hw_eq
  have hw101_nonneg : 0 ≤ w ![(1 : ℝ), 0, 1] := by
    exact hw_nonneg ![(1 : ℝ), 0, 1] (by simp)
  have hw011_nonneg : 0 ≤ w ![(0 : ℝ), 1, 1] := by
    exact hw_nonneg ![(0 : ℝ), 1, 1] (by simp)
  simp [hx2] at hcoord
  have hw101_zero : w ![(1 : ℝ), 0, 1] = 0 := by
    linarith
  have hw011_zero : w ![(0 : ℝ), 1, 1] = 0 := by
    linarith
  exact ⟨hw101_zero, hw011_zero⟩

/-- Helper for Exercise 7.6: a convex combination of the five example vertices that is tight for
`x₁ + x₂ + x₃ = 2` cannot use the two slack vertices `(1,0,0)` and `(0,1,0)`. -/
private theorem exercise_7_6_lifted_slack_weights_vanish
    {w : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ}
    (hw_nonneg :
      ∀ y ∈ ({![(1 : ℝ), 1, 0], ![(1 : ℝ), 0, 0], ![(0 : ℝ), 1, 0], ![(1 : ℝ), 0, 1],
        ![(0 : ℝ), 1, 1]} : Finset (Fin 3 → ℝ)),
        0 ≤ w y)
    (hw_sum :
      ∑ y ∈ ({![(1 : ℝ), 1, 0], ![(1 : ℝ), 0, 0], ![(0 : ℝ), 1, 0], ![(1 : ℝ), 0, 1],
        ![(0 : ℝ), 1, 1]} : Finset (Fin 3 → ℝ)),
        w y = 1)
    (hw_eq :
      ∑ y ∈ ({![(1 : ℝ), 1, 0], ![(1 : ℝ), 0, 0], ![(0 : ℝ), 1, 0], ![(1 : ℝ), 0, 1],
        ![(0 : ℝ), 1, 1]} : Finset (Fin 3 → ℝ)),
        w y • y = x)
    (hx_tight : x 0 + x 1 + x 2 = 2) :
    w ![(1 : ℝ), 0, 0] = 0 ∧ w ![(0 : ℝ), 1, 0] = 0 := by
  -- Summing all three coordinates distinguishes the tight and slack vertices.
  have hcoord := congrArg (fun z : Fin 3 → ℝ ↦ z 0 + z 1 + z 2) hw_eq
  have hw100_nonneg : 0 ≤ w ![(1 : ℝ), 0, 0] := by
    exact hw_nonneg ![(1 : ℝ), 0, 0] (by simp)
  have hw010_nonneg : 0 ≤ w ![(0 : ℝ), 1, 0] := by
    exact hw_nonneg ![(0 : ℝ), 1, 0] (by simp)
  simp [hx_tight] at hcoord hw_sum
  have hslack : w ![(1 : ℝ), 0, 0] + w ![(0 : ℝ), 1, 0] = 0 := by
    linarith
  have hw100_zero : w ![(1 : ℝ), 0, 0] = 0 := by
    linarith
  have hw010_zero : w ![(0 : ℝ), 1, 0] = 0 := by
    linarith
  exact ⟨hw100_zero, hw010_zero⟩

/-- Helper for Exercise 7.6: the zero-tail slice is exactly the convex hull of the three example
vertices whose third coordinate is `0`. -/
theorem exercise_7_6_zero_tail_slice_eq_convexHull_baseVertices :
    exercise_7_6_zero_tail_slice =
      convexHull ℝ ({![(1 : ℝ), 1, 0], ![(1 : ℝ), 0, 0], ![(0 : ℝ), 1, 0]} :
        Set (Fin 3 → ℝ)) := by
  classical
  let baseVertices : Finset (Fin 3 → ℝ) :=
    {![(1 : ℝ), 1, 0], ![(1 : ℝ), 0, 0], ![(0 : ℝ), 1, 0]}
  suffices hbase :
      exercise_7_6_zero_tail_slice = convexHull ℝ ((baseVertices : Set (Fin 3 → ℝ))) by
    simpa [baseVertices] using hbase
  -- Route correction: identify the slice by explicit barycentric elimination on the five vertices
  -- instead of transporting through abstract level-set dimension lemmas.
  ext x
  constructor
  · intro hx
    rcases (mem_exercise_7_6_zero_tail_slice_iff x).1 hx with ⟨hxPolytope, hx2⟩
    have hxPolytope' :
        x ∈ convexHull ℝ
          (({![(1 : ℝ), 1, 0], ![(1 : ℝ), 0, 0], ![(0 : ℝ), 1, 0], ![(1 : ℝ), 0, 1],
            ![(0 : ℝ), 1, 1]} : Finset (Fin 3 → ℝ)) : Set (Fin 3 → ℝ)) := by
      simpa [exercise_7_6_polytope_eq_convexHull, exercise_7_6_binary_example_set] using hxPolytope
    rcases (Finset.mem_convexHull').1 hxPolytope' with ⟨w, hw_nonneg, hw_sum, hw_eq⟩
    have hw_vanish := exercise_7_6_zero_tail_weights_vanish hw_nonneg hw_eq hx2
    -- Removing the vanished weights leaves a convex combination on the three slice vertices.
    refine (Finset.mem_convexHull').2 ?_
    refine ⟨w, ?_, ?_, ?_⟩
    · intro y hy
      have hy_large :
          y ∈ ({![(1 : ℝ), 1, 0], ![(1 : ℝ), 0, 0], ![(0 : ℝ), 1, 0], ![(1 : ℝ), 0, 1],
            ![(0 : ℝ), 1, 1]} : Finset (Fin 3 → ℝ)) := by
        rcases (by simpa [baseVertices] using hy :
          y = ![(1 : ℝ), 1, 0] ∨ y = ![(1 : ℝ), 0, 0] ∨ y = ![(0 : ℝ), 1, 0]) with
          rfl | rfl | rfl
        all_goals
          simp
      exact hw_nonneg y hy_large
    · simpa [baseVertices, hw_vanish.1, hw_vanish.2] using hw_sum
    · simpa [baseVertices, hw_vanish.1, hw_vanish.2] using hw_eq
  · intro hx
    have hbase_subset :
        (({![(1 : ℝ), 1, 0], ![(1 : ℝ), 0, 0], ![(0 : ℝ), 1, 0]} :
          Finset (Fin 3 → ℝ)) : Set (Fin 3 → ℝ)) ⊆ exercise_7_6_binary_example_set := by
      intro y hy
      rcases (by simpa using hy :
        y = ![(1 : ℝ), 1, 0] ∨ y = ![(1 : ℝ), 0, 0] ∨ y = ![(0 : ℝ), 1, 0]) with
        rfl | rfl | rfl
      all_goals
        simp [exercise_7_6_binary_example_set]
    have hxPolytope : x ∈ exercise_7_6_polytope := by
      rw [exercise_7_6_polytope_eq_convexHull]
      exact convexHull_mono hbase_subset hx
    rcases (Finset.mem_convexHull').1 hx with ⟨w, hw_nonneg, hw_sum, hw_eq⟩
    -- Every base vertex already has third coordinate zero, so the convex hull stays in the slice.
    have hx2 : x 2 = 0 := by
      have hcoord := congrArg (fun z : Fin 3 → ℝ ↦ z 2) hw_eq
      simpa [baseVertices] using hcoord.symm
    exact (mem_exercise_7_6_zero_tail_slice_iff x).2 ⟨hxPolytope, hx2⟩

/-- Helper for Exercise 7.6: the slice has affine dimension `2` because it is the convex hull of
an affinely independent triangle. -/
theorem exercise_7_6_zero_tail_slice_finrank_direction_affineSpan :
    Module.finrank ℝ (affineSpan ℝ exercise_7_6_zero_tail_slice).direction = 2 := by
  let p : Fin 3 → Fin 3 → ℝ :=
    ![(![(1 : ℝ), 0, 0] : Fin 3 → ℝ), ![(1 : ℝ), 1, 0], ![(0 : ℝ), 1, 0]]
  have hp_affineIndependent : AffineIndependent ℝ p := by
    simpa [p] using exercise_7_6_zero_tail_slice_affineIndependentFamily
  have hset :
      ({![(1 : ℝ), 1, 0], ![(1 : ℝ), 0, 0], ![(0 : ℝ), 1, 0]} : Set (Fin 3 → ℝ)) =
        Set.range p := by
    ext x
    constructor <;> intro hx <;> simpa [p, or_assoc, or_left_comm, or_comm] using hx
  -- Route correction: compute the slice dimension from its exact triangle model.
  rw [exercise_7_6_zero_tail_slice_eq_convexHull_baseVertices, affineSpan_convexHull,
    direction_affineSpan]
  have hcard :
      Module.finrank ℝ
          (vectorSpan ℝ ({![(1 : ℝ), 1, 0], ![(1 : ℝ), 0, 0], ![(0 : ℝ), 1, 0]} :
            Set (Fin 3 → ℝ))) +
        1 = 3 := by
    rw [hset]
    simpa using
      (AffineIndependent.finrank_vectorSpan_add_one (k := ℝ) (p := p) hp_affineIndependent)
  omega

/-- Helper for Exercise 7.6: the lifted equality face is exactly the convex hull of the three
vertices that satisfy `x₁ + x₂ + x₃ = 2`. -/
theorem exercise_7_6_lifted_face_eq_convexHull_tightVertices :
    exercise_7_6_lifted_face =
      convexHull ℝ ({![(1 : ℝ), 1, 0], ![(1 : ℝ), 0, 1], ![(0 : ℝ), 1, 1]} :
        Set (Fin 3 → ℝ)) := by
  classical
  let tightVertices : Finset (Fin 3 → ℝ) :=
    {![(1 : ℝ), 1, 0], ![(1 : ℝ), 0, 1], ![(0 : ℝ), 1, 1]}
  suffices htight :
      exercise_7_6_lifted_face = convexHull ℝ ((tightVertices : Set (Fin 3 → ℝ))) by
    simpa [tightVertices] using htight
  -- Route correction: work directly with the five explicit vertices and eliminate the two slack
  -- barycentric coefficients using the tight equality `x₁ + x₂ + x₃ = 2`.
  ext x
  constructor
  · intro hx
    rcases (mem_exercise_7_6_lifted_face_iff x).1 hx with ⟨hxPolytope, hxEq⟩
    have hxPolytope' :
        x ∈ convexHull ℝ
          (({![(1 : ℝ), 1, 0], ![(1 : ℝ), 0, 0], ![(0 : ℝ), 1, 0], ![(1 : ℝ), 0, 1],
            ![(0 : ℝ), 1, 1]} : Finset (Fin 3 → ℝ)) : Set (Fin 3 → ℝ)) := by
      simpa [exercise_7_6_polytope_eq_convexHull, exercise_7_6_binary_example_set] using hxPolytope
    have hx_tight : x 0 + x 1 + x 2 = 2 := by
      simpa [exercise_7_6_lifted_coeffs_eq, dotProduct, Fin.sum_univ_three, add_assoc,
        add_left_comm, add_comm] using hxEq
    rcases (Finset.mem_convexHull').1 hxPolytope' with ⟨w, hw_nonneg, hw_sum, hw_eq⟩
    have hw_vanish := exercise_7_6_lifted_slack_weights_vanish hw_nonneg hw_sum hw_eq hx_tight
    -- The tight face is the convex hull of the three vertices that meet the lifted equality.
    refine (Finset.mem_convexHull').2 ?_
    refine ⟨w, ?_, ?_, ?_⟩
    · intro y hy
      have hy_large :
          y ∈ ({![(1 : ℝ), 1, 0], ![(1 : ℝ), 0, 0], ![(0 : ℝ), 1, 0], ![(1 : ℝ), 0, 1],
            ![(0 : ℝ), 1, 1]} : Finset (Fin 3 → ℝ)) := by
        rcases (by simpa [tightVertices] using hy :
          y = ![(1 : ℝ), 1, 0] ∨ y = ![(1 : ℝ), 0, 1] ∨ y = ![(0 : ℝ), 1, 1]) with
          rfl | rfl | rfl
        all_goals
          simp
      exact hw_nonneg y hy_large
    · simpa [tightVertices, hw_vanish.1, hw_vanish.2] using hw_sum
    · simpa [tightVertices, hw_vanish.1, hw_vanish.2] using hw_eq
  · intro hx
    have htight_subset :
        (({![(1 : ℝ), 1, 0], ![(1 : ℝ), 0, 1], ![(0 : ℝ), 1, 1]} :
          Finset (Fin 3 → ℝ)) : Set (Fin 3 → ℝ)) ⊆ exercise_7_6_binary_example_set := by
      intro y hy
      rcases (by simpa using hy :
        y = ![(1 : ℝ), 1, 0] ∨ y = ![(1 : ℝ), 0, 1] ∨ y = ![(0 : ℝ), 1, 1]) with
        rfl | rfl | rfl
      all_goals
        simp [exercise_7_6_binary_example_set]
    have hxPolytope : x ∈ exercise_7_6_polytope := by
      rw [exercise_7_6_polytope_eq_convexHull]
      exact convexHull_mono htight_subset hx
    rcases (Finset.mem_convexHull').1 hx with ⟨w, hw_nonneg, hw_sum, hw_eq⟩
    -- The lifted coefficient vector is constant with value `2` on each tight vertex.
    have hx_tight : x 0 + x 1 + x 2 = 2 := by
      have hcoord := congrArg (fun z : Fin 3 → ℝ ↦ z 0 + z 1 + z 2) hw_eq
      simp [tightVertices, add_assoc] at hcoord hw_sum
      linarith
    have hxEq : exercise_7_6_lifted_coeffs ⬝ᵥ x = 2 := by
      calc
        exercise_7_6_lifted_coeffs ⬝ᵥ x = x 0 + x 1 + x 2 := by
          simp [exercise_7_6_lifted_coeffs_eq, dotProduct, Fin.sum_univ_three]
        _ = 2 := hx_tight
    exact (mem_exercise_7_6_lifted_face_iff x).2 ⟨hxPolytope, hxEq⟩

/-- Helper for Exercise 7.6: the ambient polytope has affine dimension `3`. -/
theorem exercise_7_6_polytope_finrank_direction_affineSpan :
    Module.finrank ℝ (affineSpan ℝ exercise_7_6_polytope).direction = 3 := by
  let p0 : Fin 3 → ℝ := ![(1 : ℝ), 1, 0]
  let p1 : Fin 3 → ℝ := ![(1 : ℝ), 0, 0]
  let p2 : Fin 3 → ℝ := ![(0 : ℝ), 1, 0]
  let p3 : Fin 3 → ℝ := ![(1 : ℝ), 0, 1]
  have hp0 : p0 ∈ exercise_7_6_polytope := by
    exact mem_exercise_7_6_polytope_of_mem_example_set (by
      simp [p0, exercise_7_6_binary_example_set])
  have hp1 : p1 ∈ exercise_7_6_polytope := by
    exact mem_exercise_7_6_polytope_of_mem_example_set (by
      simp [p1, exercise_7_6_binary_example_set])
  have hp2 : p2 ∈ exercise_7_6_polytope := by
    exact mem_exercise_7_6_polytope_of_mem_example_set (by
      simp [p2, exercise_7_6_binary_example_set])
  have hp3 : p3 ∈ exercise_7_6_polytope := by
    exact mem_exercise_7_6_polytope_of_mem_example_set (by
      simp [p3, exercise_7_6_binary_example_set])
  let p : Fin 4 → Fin 3 → ℝ := ![p1, p0, p3, p2]
  have hp_affineIndependent : AffineIndependent ℝ p := by
    simpa [p, p0, p1, p2, p3] using exercise_7_6_polytope_affineIndependentFamily
  have hp_range : Set.range p ⊆ exercise_7_6_polytope := by
    intro x hx
    rcases hx with ⟨i, rfl⟩
    fin_cases i
    · simpa [p] using hp1
    · simpa [p] using hp0
    · simpa [p] using hp3
    · simpa [p] using hp2
  have htop : affineSpan ℝ exercise_7_6_polytope = ⊤ :=
    affineSpan_eq_top_of_affineIndependentFamily hp_affineIndependent hp_range
  rw [htop, AffineSubspace.direction_top, finrank_top]
  simp [Module.finrank_fintype_fun_eq_card]

/-- Helper for Exercise 7.6: the lifted equality face has affine dimension `2`. -/
theorem exercise_7_6_lifted_face_finrank_direction_affineSpan :
    Module.finrank ℝ (affineSpan ℝ exercise_7_6_lifted_face).direction = 2 := by
  let p : Fin 3 → Fin 3 → ℝ :=
    ![(![(1 : ℝ), 1, 0] : Fin 3 → ℝ), ![(1 : ℝ), 0, 1], ![(0 : ℝ), 1, 1]]
  have hp_affineIndependent : AffineIndependent ℝ p := by
    simpa [p] using exercise_7_6_lifted_face_affineIndependentFamily
  have hset :
      ({![(1 : ℝ), 1, 0], ![(1 : ℝ), 0, 1], ![(0 : ℝ), 1, 1]} : Set (Fin 3 → ℝ)) =
        Set.range p := by
    ext x
    constructor <;> intro hx <;> simpa [p, or_assoc, or_left_comm, or_comm] using hx
  -- Route correction: compute the face dimension from its exact triangle model.
  rw [exercise_7_6_lifted_face_eq_convexHull_tightVertices, affineSpan_convexHull,
    direction_affineSpan]
  have hcard :
      Module.finrank ℝ
          (vectorSpan ℝ ({![(1 : ℝ), 1, 0], ![(1 : ℝ), 0, 1], ![(0 : ℝ), 1, 1]} :
            Set (Fin 3 → ℝ))) +
        1 = 3 := by
    rw [hset]
    simpa using
      (AffineIndependent.finrank_vectorSpan_add_one (k := ℝ) (p := p) hp_affineIndependent)
  omega

/-- Helper for Exercise 7.6: for the explicit binary set
`S = {(1,1,0), (1,0,0), (0,1,0), (1,0,1), (0,1,1)} ⊆ {0,1}^3`, the slice
`conv(S) ∩ {x | x₃ = 0}` has dimension `2`; here `p = 2` and the source condition
`x_k = 0` for `k = p + 1, ..., n` is the single zero-based equation `x 2 = 0`. -/
theorem exercise_7_6_binary_example_slice_has_dimension_two :
    exercise_7_6_binary_example_set ⊆ {x : Fin 3 → ℝ | ∀ i, x i = 0 ∨ x i = 1} ∧
      Module.finrank ℝ (affineSpan ℝ exercise_7_6_zero_tail_slice).direction = 2 := by
  constructor
  · intro x hx i
    -- The five listed generators are visibly binary.
    rcases (mem_exercise_7_6_binary_example_set_iff x).1 hx with
      rfl | rfl | rfl | rfl | rfl
    all_goals
      fin_cases i <;> simp
  · -- The slice dimension now comes from its exact triangle description.
    exact exercise_7_6_zero_tail_slice_finrank_direction_affineSpan

/-- Helper for Exercise 7.6: in the same example, the base inequality `x₁ + x₂ ≤ 2` on the slice
`conv(S) ∩ {x | x₃ = 0}` defines the face `exercise_7_6_base_face`, and that face has dimension
`0 = p - 2`. -/
theorem exercise_7_6_base_inequality_defines_zero_dimensional_face :
    IsExposed ℝ exercise_7_6_zero_tail_slice exercise_7_6_base_face ∧
      Module.finrank ℝ (affineSpan ℝ exercise_7_6_base_face).direction = 0 := by
  constructor
  · -- The base face is the equality face of a valid inequality on the slice.
    rw [exercise_7_6_base_face_eq_face_set]
    exact isExposed_face_set_of_valid_inequality exercise_7_6_valid_base_inequality_on_slice
  · -- Once the base face is identified as a singleton, its direction is trivial.
    rw [exercise_7_6_base_face_eq_singleton, direction_affineSpan, vectorSpan_singleton,
      finrank_bot]

/-- Exercise 7.6 (3). For this same set `S`, lifting the base inequality `x₁ + x₂ ≤ 2` to
`x₁ + x₂ + x₃ ≤ 2` yields the face `exercise_7_6_lifted_face`, and that lifted face is a facet of
`conv(S)`. This gives the requested example where a lifting becomes facet-defining even though the
original face in the `x₃ = 0` slice has dimension `p - 2`. -/
theorem exercise_7_6_lifted_inequality_defines_facet :
    IsFacetOf exercise_7_6_polytope exercise_7_6_lifted_face := by
  let p0 : Fin 3 → ℝ := ![(1 : ℝ), 1, 0]
  have hp0_0 : p0 0 = 1 := by
    simp [p0]
  have hp0_1 : p0 1 = 1 := by
    simp [p0]
  have hp0_2 : p0 2 = 0 := by
    simp [p0]
  have hp0_polytope : p0 ∈ exercise_7_6_polytope := by
    exact mem_exercise_7_6_polytope_of_mem_example_set (by
      simp [p0, exercise_7_6_binary_example_set])
  have hp0_tight : exercise_7_6_lifted_coeffs ⬝ᵥ p0 = 2 := by
    calc
      exercise_7_6_lifted_coeffs ⬝ᵥ p0 = p0 0 + p0 1 + p0 2 := by
        simp [exercise_7_6_lifted_coeffs_eq, dotProduct, Fin.sum_univ_three]
      _ = 2 := by
        norm_num [hp0_0, hp0_1, hp0_2]
  have hp0 : p0 ∈ exercise_7_6_lifted_face := by
    -- The vertex `(1,1,0)` is one of the generators and is tight for the lifted inequality.
    refine (mem_exercise_7_6_lifted_face_iff p0).2 ?_
    exact ⟨hp0_polytope, hp0_tight⟩
  rw [isFacetOf_iff]
  refine ⟨⟨p0, hp0⟩, ?_, ?_⟩
  · -- The lifted face is the equality face of the globally valid lifted inequality.
    rw [exercise_7_6_lifted_face_eq_face_set]
    exact isExposed_face_set_of_valid_inequality exercise_7_6_valid_lifted_inequality
  · -- The explicit dimension counts give the codimension-one facet equation.
    norm_num [exercise_7_6_lifted_face_finrank_direction_affineSpan,
      exercise_7_6_polytope_finrank_direction_affineSpan]

end Exercise76
