/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

noncomputable section
open scoped Pointwise Topology

section Chap02
section Section06

/-- Text 6.1: The Euclidean distance between two points `x` and `y` in `R^n` is defined by
`d(x, y) = |x - y| = sqrt (inner (x - y) (x - y))`. -/
def euclideanDist (n : Nat) (x y : EuclideanSpace Real (Fin n)) : Real :=
  dist x y

/-- The norm of the difference on a product space is convex on all of `R^{2n}`. -/
lemma convexOn_univ_norm_comp_sub (n : Nat) :
    ConvexOn Real Set.univ
      (fun p : (EuclideanSpace Real (Fin n)) × (EuclideanSpace Real (Fin n)) => ‖p.1 - p.2‖) := by
  let g :
      (EuclideanSpace Real (Fin n)) × (EuclideanSpace Real (Fin n)) →ₗ[Real]
        (EuclideanSpace Real (Fin n)) :=
    LinearMap.fst Real (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) -
      LinearMap.snd Real (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n))
  simpa [g] using
    (convexOn_univ_norm :
      ConvexOn Real Set.univ (norm : (EuclideanSpace Real (Fin n)) → Real)).comp_linearMap g

/-- Text 6.2: The function `d`, the Euclidean metric, is convex as a function on `R^{2n}`. -/
theorem euclideanDist_convex (n : Nat) :
    ConvexOn Real Set.univ
      (fun p : (EuclideanSpace Real (Fin n)) × (EuclideanSpace Real (Fin n)) =>
        dist p.1 p.2) := by
  simpa [dist_eq_norm] using (convexOn_univ_norm_comp_sub n)

/-- Text 6.3: Throughout this section, the Euclidean unit ball in `R^n` is
`B = {x | ‖x‖ ≤ 1} = {x | dist x 0 ≤ 1}`. -/
def euclideanUnitBall (n : Nat) : Set (EuclideanSpace Real (Fin n)) :=
  {x | ‖x‖ ≤ (1 : Real)}

theorem euclideanUnitBall_eq_dist (n : Nat) :
    euclideanUnitBall n = {x | dist x 0 ≤ (1 : Real)} := by
  ext x; simp [euclideanUnitBall, dist_eq_norm]

/-- Text 6.4: The Euclidean unit ball `B` is a closed convex set. -/
theorem euclideanUnitBall_closed_convex (n : Nat) :
    IsClosed (euclideanUnitBall n) ∧ Convex Real (euclideanUnitBall n) := by
  have hball :
      euclideanUnitBall n =
        Metric.closedBall (0 : EuclideanSpace Real (Fin n)) (1 : Real) := by
    simpa [Metric.closedBall] using (euclideanUnitBall_eq_dist n)
  constructor
  · simpa [hball] using
      (Metric.isClosed_closedBall
        (x := (0 : EuclideanSpace Real (Fin n))) (ε := (1 : Real)))
  · simpa [hball] using
      (convex_closedBall (a := (0 : EuclideanSpace Real (Fin n))) (r := (1 : Real)))

/-- Text 6.5: For any `a ∈ R^n`, the ball with radius `ε > 0` and center `a` is
`{x | d(x, a) ≤ ε} = {a + y | |y| ≤ ε} = a + ε B`. The closed ball centered at `a` is a
translate of the radius-`ε` norm ball. -/
lemma euclidean_closedBall_eq_translate_left (n : Nat) (a : EuclideanSpace Real (Fin n))
    (ε : Real) :
    {x | dist x a ≤ ε} = Set.image (fun y => a + y) {y | ‖y‖ ≤ ε} := by
  ext x; constructor
  · intro hx
    refine ⟨x - a, ?_, ?_⟩
    · simpa [dist_eq_norm] using hx
    · simp
  · rintro ⟨y, hy, rfl⟩
    have hsub : (a + y) - a = y := by
      simp
    calc
      dist (a + y) a = ‖y‖ := by
        simp [dist_eq_norm, hsub]
      _ ≤ ε := hy

/-- Scaling the unit ball by `ε ≥ 0` gives the radius-`ε` norm ball. -/
lemma euclidean_normBall_eq_smul_unitBall (n : Nat) (ε : Real) (hε : 0 ≤ ε) :
    {y | ‖y‖ ≤ ε} = ε • euclideanUnitBall n := by
  have hunit :
      euclideanUnitBall n =
        Metric.closedBall (0 : EuclideanSpace Real (Fin n)) (1 : Real) := by
    simpa [Metric.closedBall] using (euclideanUnitBall_eq_dist n)
  calc
    {y | ‖y‖ ≤ ε}
        = Metric.closedBall (0 : EuclideanSpace Real (Fin n)) ε := by
            ext y; simp [Metric.closedBall, dist_eq_norm]
    _ = ε • Metric.closedBall (0 : EuclideanSpace Real (Fin n)) (1 : Real) := by
            symm
            simpa using
              (smul_unitClosedBall_of_nonneg (E := EuclideanSpace Real (Fin n)) (r := ε) hε)
    _ = ε • euclideanUnitBall n := by
            simp [hunit]

/-- Translating the ε-scaled unit ball equals scaling after translating. -/
lemma image_translate_smul_unitBall (n : Nat) (a : EuclideanSpace Real (Fin n)) (ε : Real) :
    Set.image (fun y => a + y) (ε • euclideanUnitBall n) =
      Set.image (fun y => a + ε • y) (euclideanUnitBall n) := by
  ext z; constructor
  · rintro ⟨y, ⟨y', hy', rfl⟩, rfl⟩
    exact ⟨y', hy', rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨ε • y, ⟨y, hy, rfl⟩, rfl⟩

theorem euclidean_closedBall_eq_translate (n : Nat) (a : EuclideanSpace Real (Fin n)) (ε : Real)
    (hε : 0 < ε) :
    {x | dist x a ≤ ε} = Set.image (fun y => a + y) {y | ‖y‖ ≤ ε} ∧
      Set.image (fun y => a + y) {y | ‖y‖ ≤ ε} =
        Set.image (fun y => a + ε • y) (euclideanUnitBall n) := by
  constructor
  · exact euclidean_closedBall_eq_translate_left n a ε
  · have hball : {y | ‖y‖ ≤ ε} = ε • euclideanUnitBall n :=
      euclidean_normBall_eq_smul_unitBall n ε (le_of_lt hε)
    calc
      Set.image (fun y => a + y) {y | ‖y‖ ≤ ε} =
          Set.image (fun y => a + y) (ε • euclideanUnitBall n) := by
            simp [hball]
      _ = Set.image (fun y => a + ε • y) (euclideanUnitBall n) := by
            simpa using (image_translate_smul_unitBall n a ε)

/-- Text 6.6: For any set `C` in `R^n`, the set of points `x` whose distance from `C`
does not exceed `ε` is
`{x | ∃ y ∈ C, d(x, y) ≤ ε} = ⋃ {y + ε B | y ∈ C} = C + ε B`. -/
theorem euclidean_neighborhood_eq_iUnion_translate (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) (ε : Real) (hε : 0 ≤ ε) :
    {x | ∃ y ∈ C, dist x y ≤ ε} =
        ⋃ y ∈ C, (fun z => y + z) '' (ε • euclideanUnitBall n) ∧
      (⋃ y ∈ C, (fun z => y + z) '' (ε • euclideanUnitBall n)) =
        C + ε • euclideanUnitBall n := by
  classical
  have hball : {z | ‖z‖ ≤ ε} = ε • euclideanUnitBall n :=
    euclidean_normBall_eq_smul_unitBall n ε hε
  constructor
  · ext x; constructor
    · rintro ⟨y, hyC, hdist⟩
      refine (Set.mem_iUnion₂).2 ?_
      refine ⟨y, hyC, ?_⟩
      have hx : x ∈ {x | dist x y ≤ ε} := hdist
      simpa [euclidean_closedBall_eq_translate_left, hball] using hx
    · intro hx
      rcases (Set.mem_iUnion₂).1 hx with ⟨y, hyC, hx⟩
      have hx' : x ∈ {x | dist x y ≤ ε} := by
        have hx'' :
            x ∈ Set.image (fun z => y + z) {z | ‖z‖ ≤ ε} := by
          simpa [hball] using hx
        simpa [euclidean_closedBall_eq_translate_left] using hx''
      exact ⟨y, hyC, hx'⟩
  · ext x; constructor
    · intro hx
      rcases (Set.mem_iUnion₂).1 hx with ⟨y, hyC, hx⟩
      rcases hx with ⟨z, hz, rfl⟩
      exact Set.mem_add.mpr ⟨y, hyC, z, hz, rfl⟩
    · intro hx
      rcases Set.mem_add.mp hx with ⟨y, hyC, z, hz, rfl⟩
      refine (Set.mem_iUnion₂).2 ?_
      exact ⟨y, hyC, ⟨z, hz, rfl⟩⟩

/-- Text 6.7: The closure `cl C` of `C` can be expressed by
`cl C = ⋂ { C + ε B | ε > 0 }`. -/
theorem euclidean_closure_eq_iInter_thickening (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) :
    closure C = ⋂ ε : {ε : Real // 0 < ε}, C + ε.1 • euclideanUnitBall n := by
  classical
  have hneigh (ε : Real) (hε : 0 ≤ ε) :
      {x | ∃ y ∈ C, dist x y ≤ ε} = C + ε • euclideanUnitBall n :=
    (euclidean_neighborhood_eq_iUnion_translate n C ε hε).1.trans
      (euclidean_neighborhood_eq_iUnion_translate n C ε hε).2
  ext x; constructor
  · intro hx
    refine Set.mem_iInter.mpr ?_
    intro ε
    have hx' := (Metric.mem_closure_iff).1 hx ε.1 ε.2
    rcases hx' with ⟨y, hyC, hdist⟩
    have hx'' : x ∈ {x | ∃ y ∈ C, dist x y ≤ ε.1} :=
      ⟨y, hyC, le_of_lt hdist⟩
    simpa [hneigh ε.1 (le_of_lt ε.2)] using hx''
  · intro hx
    refine (Metric.mem_closure_iff).2 ?_
    intro ε εpos
    have hx' : x ∈ C + (ε / 2) • euclideanUnitBall n := by
      exact (Set.mem_iInter.mp hx) ⟨ε / 2, by linarith⟩
    have hx'' : x ∈ {x | ∃ y ∈ C, dist x y ≤ ε / 2} := by
      simpa [hneigh (ε / 2) (by linarith)] using hx'
    rcases hx'' with ⟨y, hyC, hdist⟩
    refine ⟨y, hyC, ?_⟩
    exact lt_of_le_of_lt hdist (by linarith)

/-- Text 6.7: The interior `int C` of `C` can be expressed by
`int C = { x | ∃ ε > 0, x + ε B ⊆ C }`. -/
theorem euclidean_interior_eq_setOf_exists_thickening (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) :
    interior C =
      {x | ∃ ε : ℝ, 0 < ε ∧ (fun y => x + y) '' (ε • euclideanUnitBall n) ⊆ C} := by
  ext x; constructor
  · intro hx
    have hx' : C ∈ 𝓝 x := (mem_interior_iff_mem_nhds).1 hx
    rcases (Metric.mem_nhds_iff).1 hx' with ⟨ε, hε, hball⟩
    have hε2 : 0 < ε / 2 := by linarith
    have hclosed : Metric.closedBall x (ε / 2) ⊆ C := by
      have hsub : Metric.closedBall x (ε / 2) ⊆ Metric.ball x ε := by
        exact Metric.closedBall_subset_ball (by linarith)
      exact hsub.trans hball
    have hball_eq :
        (fun y => x + y) '' ((ε / 2) • euclideanUnitBall n) =
          Metric.closedBall x (ε / 2) := by
      have hnorm :
          {y | ‖y‖ ≤ ε / 2} = (ε / 2) • euclideanUnitBall n :=
        euclidean_normBall_eq_smul_unitBall n (ε / 2) (by linarith)
      have hclosed :
          Set.image (fun y => x + y) {y | ‖y‖ ≤ ε / 2} =
            Metric.closedBall x (ε / 2) := by
        simpa [Metric.closedBall] using
          (euclidean_closedBall_eq_translate_left n x (ε / 2)).symm
      calc
        (fun y => x + y) '' ((ε / 2) • euclideanUnitBall n) =
            (fun y => x + y) '' {y | ‖y‖ ≤ ε / 2} := by
              simp [hnorm]
        _ = Metric.closedBall x (ε / 2) := hclosed
    refine ⟨ε / 2, hε2, ?_⟩
    intro y hy
    have hy' : y ∈ Metric.closedBall x (ε / 2) := by
      simpa [hball_eq] using hy
    exact hclosed hy'
  · rintro ⟨ε, hε, hsubset⟩
    have hball_eq :
        (fun y => x + y) '' (ε • euclideanUnitBall n) = Metric.closedBall x ε := by
      have hnorm :
          {y | ‖y‖ ≤ ε} = ε • euclideanUnitBall n :=
        euclidean_normBall_eq_smul_unitBall n ε (le_of_lt hε)
      have hclosed :
          Set.image (fun y => x + y) {y | ‖y‖ ≤ ε} = Metric.closedBall x ε := by
        simpa [Metric.closedBall] using
          (euclidean_closedBall_eq_translate_left n x ε).symm
      calc
        (fun y => x + y) '' (ε • euclideanUnitBall n) =
            (fun y => x + y) '' {y | ‖y‖ ≤ ε} := by
              simp [hnorm]
        _ = Metric.closedBall x ε := hclosed
    have hclosed : Metric.closedBall x ε ⊆ C := by
      intro y hy
      have hy' : y ∈ (fun y => x + y) '' (ε • euclideanUnitBall n) := by
        simpa [hball_eq] using hy
      exact hsubset hy'
    have hball : Metric.ball x ε ⊆ C :=
      (Metric.ball_subset_closedBall.trans hclosed)
    exact (mem_interior_iff_mem_nhds).2 (Metric.mem_nhds_iff.2 ⟨ε, hε, hball⟩)

/-- Text 6.8: The relative interior `ri C` of a convex set `C` in `R^n` is the interior of `C`
in its affine hull `aff C`. Equivalently,
`ri C = { x ∈ aff C | ∃ ε > 0, (x + ε B) ∩ aff C ⊆ C }`. -/
def euclideanRelativeInterior (n : Nat) (C : Set (EuclideanSpace Real (Fin n))) :
    Set (EuclideanSpace Real (Fin n)) :=
  {x |
    x ∈ (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) ∧
      ∃ ε : ℝ, 0 < ε ∧
        ((fun y => x + y) '' (ε • euclideanUnitBall n)) ∩
            (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) ⊆ C}

/-- Text 6.9: Needless to say, `ri C ⊂ C ⊂ cl C`. -/
theorem euclideanRelativeInterior_subset_closure (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) :
    euclideanRelativeInterior n C ⊆ C ∧ C ⊆ closure C := by
  constructor
  · intro x hx
    rcases hx with ⟨hx_aff, ε, hε, hxsub⟩
    have hxball : x ∈ (fun y => x + y) '' (ε • euclideanUnitBall n) := by
      refine ⟨0, ?_, by simp⟩
      refine ⟨0, ?_, by simp⟩
      simp [euclideanUnitBall]
    have hx' :
        x ∈ ((fun y => x + y) '' (ε • euclideanUnitBall n)) ∩
            (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) :=
      ⟨hxball, hx_aff⟩
    exact hxsub hx'
  · exact subset_closure

/-- Text 6.10: The relative boundary of `C` is the set difference `(cl C) \ (ri C)`. -/
def euclideanRelativeBoundary (n : Nat) (C : Set (EuclideanSpace Real (Fin n))) :
    Set (EuclideanSpace Real (Fin n)) :=
  closure C \ euclideanRelativeInterior n C

/-- Text 6.11: Naturally, `C` is said to be relatively open if `ri C = C`. -/
def euclideanRelativelyOpen (n : Nat) (C : Set (EuclideanSpace Real (Fin n))) : Prop :=
  euclideanRelativeInterior n C = C

/-- Text 6.12: For an `n`-dimensional convex set, `aff C = R^n` by definition, so `ri C = int C`. -/
theorem euclideanRelativeInterior_eq_interior_of_affineSpan_eq_univ (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n)))
    (hC : (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) = Set.univ) :
    euclideanRelativeInterior n C = interior C := by
  ext x; constructor
  · intro hx
    rcases hx with ⟨hx_aff, ε, hε, hxsub⟩
    have hxsub' :
        (fun y => x + y) '' (ε • euclideanUnitBall n) ⊆ C := by
      intro y hy
      have hy' : y ∈ (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) := by
        simp [hC]
      exact hxsub ⟨hy, hy'⟩
    have hx' :
        x ∈ {x | ∃ ε : ℝ, 0 < ε ∧ (fun y => x + y) '' (ε • euclideanUnitBall n) ⊆ C} :=
      ⟨ε, hε, hxsub'⟩
    simpa [euclidean_interior_eq_setOf_exists_thickening] using hx'
  · intro hx
    have hx' :
        x ∈ {x | ∃ ε : ℝ, 0 < ε ∧ (fun y => x + y) '' (ε • euclideanUnitBall n) ⊆ C} := by
      simpa [euclidean_interior_eq_setOf_exists_thickening] using hx
    rcases hx' with ⟨ε, hε, hxsub⟩
    have hx_aff : x ∈ (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) := by
      simp [hC]
    refine ⟨hx_aff, ε, hε, ?_⟩
    intro y hy
    exact hxsub hy.1

/-- The relative interior of an affine subspace is the subspace itself. -/
lemma euclideanRelativeInterior_affineSubspace_eq (n : Nat)
    (s : AffineSubspace Real (EuclideanSpace Real (Fin n))) :
    euclideanRelativeInterior n (s : Set (EuclideanSpace Real (Fin n))) = s := by
  ext x; constructor
  · intro hx
    rcases (by
      simpa [euclideanRelativeInterior, AffineSubspace.affineSpan_coe] using hx) with
      ⟨hxmem, -⟩
    exact hxmem
  · intro hx
    have hx' :
        x ∈ (s : Set (EuclideanSpace Real (Fin n))) ∧
          ∃ ε : ℝ, 0 < ε ∧
            ((fun y => x + y) '' (ε • euclideanUnitBall n)) ∩
                (s : Set (EuclideanSpace Real (Fin n))) ⊆ s := by
      refine ⟨hx, ?_⟩
      refine ⟨(1 : Real), by norm_num, ?_⟩
      intro y hy
      exact hy.2
    simpa [euclideanRelativeInterior, AffineSubspace.affineSpan_coe] using hx'

/-- Every affine subspace of Euclidean space is closed. -/
lemma affineSubspace_isClosed (n : Nat)
    (s : AffineSubspace Real (EuclideanSpace Real (Fin n))) :
    IsClosed (s : Set (EuclideanSpace Real (Fin n))) := by
  haveI : FiniteDimensional Real s.direction := by infer_instance
  simpa using (AffineSubspace.closed_of_finiteDimensional (s := s))

/-- Text 6.13: An affine set is relatively open by definition. Every affine set is at the same
time closed. -/
theorem affineSubspace_relativelyOpen_closed (n : Nat)
    (s : AffineSubspace Real (EuclideanSpace Real (Fin n))) :
    euclideanRelativelyOpen n (s : Set (EuclideanSpace Real (Fin n))) ∧
      IsClosed (s : Set (EuclideanSpace Real (Fin n))) := by
  constructor
  · simpa [euclideanRelativelyOpen] using
      (euclideanRelativeInterior_affineSubspace_eq n s)
  · simpa using (affineSubspace_isClosed n s)

/-- Text 6.14: Observe that `cl C ⊆ cl (aff C) = aff C` for any `C`. -/
theorem euclidean_closure_subset_closure_affineSpan (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) :
    closure C ⊆ closure (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) ∧
      closure (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) =
        (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) := by
  constructor
  · exact closure_mono (subset_affineSpan (k := Real) (s := C))
  · have hclosed :
        IsClosed (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) :=
      affineSubspace_isClosed n (affineSpan Real C)
    simpa using hclosed.closure_eq

/-- The translated scaled unit ball is the metric closed ball. -/
lemma translate_smul_unitBall_eq_closedBall (n : Nat) (a : EuclideanSpace Real (Fin n)) (ε : Real)
    (hε : 0 < ε) :
    (fun y => a + y) '' (ε • euclideanUnitBall n) = Metric.closedBall a ε := by
  rcases euclidean_closedBall_eq_translate n a ε hε with ⟨h1, h2⟩
  have h12 :
      Metric.closedBall a ε = (fun y => a + ε • y) '' euclideanUnitBall n := by
    simpa [Metric.closedBall] using (h1.trans h2)
  have himage :
      (fun y => a + y) '' (ε • euclideanUnitBall n) =
        (fun y => a + ε • y) '' euclideanUnitBall n := by
    ext z; constructor
    · rintro ⟨y, ⟨y', hy', rfl⟩, rfl⟩
      exact ⟨y', hy', rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨ε • y, ⟨y, hy, rfl⟩, rfl⟩
  simpa [himage] using h12.symm

/-- Text 6.15: Closures and relative interiors are preserved under translations and, more
generally, under any one-to-one affine transformation of `R^n` onto itself. Such maps preserve
affine hulls and are continuous in both directions. -/
theorem closure_image_affineEquiv (n : Nat) (C : Set (EuclideanSpace Real (Fin n)))
    (e : EuclideanSpace Real (Fin n) ≃ᵃ[Real] EuclideanSpace Real (Fin n)) :
    closure (e '' C) = e '' closure C := by
  simpa using
    (Homeomorph.image_closure (e.toHomeomorphOfFiniteDimensional) C).symm

/-- Affine equivalences send affine spans to affine spans of the images. -/
lemma affineSpan_image_affineEquiv (n : Nat) (C : Set (EuclideanSpace Real (Fin n)))
    (e : EuclideanSpace Real (Fin n) ≃ᵃ[Real] EuclideanSpace Real (Fin n)) :
    e '' (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) =
      (affineSpan Real (e '' C) : Set (EuclideanSpace Real (Fin n))) := by
  have h :=
    (AffineSubspace.map_span (k := Real) (f := e.toAffineMap) (s := C) :
      (affineSpan Real C).map e.toAffineMap = affineSpan Real (e '' C))
  ext y; constructor
  · intro hy
    have hy' : y ∈ ((affineSpan Real C).map e.toAffineMap : Set _) := by
      simpa [AffineSubspace.coe_map] using hy
    simpa [h] using hy'
  · intro hy
    have hy' : y ∈ ((affineSpan Real C).map e.toAffineMap : Set _) := by
      simpa [h] using hy
    simpa [AffineSubspace.coe_map] using hy'

/-- The inverse affine equivalence cancels the direct image of a set. -/
lemma affineEquiv_symm_image_image (n : Nat) (C : Set (EuclideanSpace Real (Fin n)))
    (e : EuclideanSpace Real (Fin n) ≃ᵃ[Real] EuclideanSpace Real (Fin n)) :
    e.symm '' (e '' C) = C := by
  ext z; constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    simpa using hx
  · intro hz
    refine ⟨e z, ?_, by simp⟩
    exact ⟨z, hz, rfl⟩

/-- An affine equivalence sends relative interior into relative interior. -/
lemma ri_image_affineEquiv_subset (n : Nat) (C : Set (EuclideanSpace Real (Fin n)))
    (e : EuclideanSpace Real (Fin n) ≃ᵃ[Real] EuclideanSpace Real (Fin n)) :
    e '' euclideanRelativeInterior n C ⊆ euclideanRelativeInterior n (e '' C) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  rcases hx with ⟨hx_aff, ε, hε, hx_subset⟩
  refine ⟨?_, ?_⟩
  · have hx' : e x ∈ e '' (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) :=
      ⟨x, hx_aff, rfl⟩
    simpa [affineSpan_image_affineEquiv (n := n) (C := C) (e := e)] using hx'
  · have hcont :
        Continuous (e.symm :
          EuclideanSpace Real (Fin n) → EuclideanSpace Real (Fin n)) :=
      (AffineEquiv.continuous_of_finiteDimensional (f := e.symm))
    have hopen : IsOpen (e.symm ⁻¹' Metric.ball x ε) :=
      (Metric.isOpen_ball.preimage hcont)
    have hxball : e x ∈ e.symm ⁻¹' Metric.ball x ε := by
      change e.symm (e x) ∈ Metric.ball x ε
      simpa using
        (Metric.mem_ball_self (x := (x : EuclideanSpace Real (Fin n))) hε)
    rcases (Metric.isOpen_iff.mp hopen) (e x) hxball with ⟨δ, hδpos, hballδ⟩
    refine ⟨δ / 2, by linarith, ?_⟩
    intro y hy
    rcases hy with ⟨hyball, hyspan⟩
    have hyspan' : y ∈ e '' (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) := by
      simpa [← affineSpan_image_affineEquiv (n := n) (C := C) (e := e)] using hyspan
    rcases hyspan' with ⟨z, hz, rfl⟩
    have hball_eq :
        (fun y => e x + y) '' ((δ / 2) • euclideanUnitBall n) =
          Metric.closedBall (e x) (δ / 2) := by
      simpa using
        (translate_smul_unitBall_eq_closedBall n (e x) (δ / 2) (by linarith))
    have hyball_closed : e z ∈ Metric.closedBall (e x) (δ / 2) := by
      simpa [hball_eq] using hyball
    have hyball_ball : e z ∈ Metric.ball (e x) δ := by
      have hsubset : Metric.closedBall (e x) (δ / 2) ⊆ Metric.ball (e x) δ := by
        exact Metric.closedBall_subset_ball (by linarith)
      exact hsubset hyball_closed
    have hyball_pre : e z ∈ e.symm ⁻¹' Metric.ball x ε := hballδ hyball_ball
    have hzball : z ∈ Metric.ball x ε := by
      simpa using hyball_pre
    have hzclosed : z ∈ Metric.closedBall x ε :=
      (Metric.ball_subset_closedBall) hzball
    have hball_eq_x :
        (fun y => x + y) '' (ε • euclideanUnitBall n) = Metric.closedBall x ε :=
      translate_smul_unitBall_eq_closedBall n x ε hε
    have hzball' : z ∈ (fun y => x + y) '' (ε • euclideanUnitBall n) := by
      simpa [hball_eq_x] using hzclosed
    have hzC : z ∈ C := hx_subset ⟨hzball', hz⟩
    exact ⟨z, hzC, rfl⟩

/-- Text 6.15: Relative interiors are preserved under one-to-one affine transformations of `R^n`
onto itself (hence in particular under translations). -/
theorem euclideanRelativeInterior_image_affineEquiv (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n)))
    (e : EuclideanSpace Real (Fin n) ≃ᵃ[Real] EuclideanSpace Real (Fin n)) :
    euclideanRelativeInterior n (e '' C) = e '' euclideanRelativeInterior n C := by
  apply subset_antisymm
  · intro y hy
    have hsubset :=
      ri_image_affineEquiv_subset (n := n) (C := e '' C) (e := e.symm)
    have hy' : e.symm y ∈ euclideanRelativeInterior n (e.symm '' (e '' C)) :=
      hsubset ⟨y, hy, rfl⟩
    have hy'' : e.symm y ∈ euclideanRelativeInterior n C := by
      simpa [affineEquiv_symm_image_image (n := n) (C := C) (e := e)] using hy'
    exact ⟨e.symm y, hy'', by simp⟩
  · exact ri_image_affineEquiv_subset (n := n) (C := C) (e := e)

/-- The coordinate subspace where coordinates `m, ..., n-1` vanish. -/
def coordinateSubspace (n m : Nat) : Set (EuclideanSpace Real (Fin n)) :=
  {x | ∀ i : Fin n, m ≤ (i : Nat) → x i = 0}

/-- Evaluate `LinearEquiv.piCongrLeft` on a constant codomain. -/
@[simp] lemma piCongrLeft_apply_const {ι ι' : Type*} (e : ι' ≃ ι) (f : ι' → ℝ) (i : ι) :
    (LinearEquiv.piCongrLeft (R := ℝ) (φ := fun _ : ι => ℝ) e f) i = f (e.symm i) := by
  simp [LinearEquiv.piCongrLeft]

/-- Evaluate the inverse of `LinearEquiv.piCongrLeft` on a constant codomain. -/
@[simp] lemma piCongrLeft_symm_apply_const {ι ι' : Type*} (e : ι' ≃ ι) (f : ι → ℝ) (i : ι') :
    ((LinearEquiv.piCongrLeft (R := ℝ) (φ := fun _ : ι => ℝ) e).symm f) i = f (e i) := by
  simp [LinearEquiv.piCongrLeft]

/-- Text 6.16: For example, if `C` is an `m`-dimensional convex set in `R^n`, there exists by
Corollary 1.6.1 a one-to-one affine transformation `T` of `R^n` onto itself which carries
`aff C` onto the subspace
`L = { x = (xi_1, ..., xi_n) | xi_{m+1} = 0, ..., xi_n = 0 }`. This `L` can be regarded as a
copy of `R^m`. -/
theorem exists_affineEquiv_affineSpan_eq_coordinateSubspace (n m : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) (hCnonempty : C.Nonempty)
    (hCdim : Module.finrank Real (affineSpan Real C).direction = m) :
    ∃ T : EuclideanSpace Real (Fin n) ≃ᵃ[Real] EuclideanSpace Real (Fin n),
      T '' (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) =
        coordinateSubspace n m := by
  classical
  let V := EuclideanSpace Real (Fin n)
  let S : AffineSubspace Real V := affineSpan Real C
  let W : Submodule Real V := S.direction
  obtain ⟨p, hpC⟩ := hCnonempty
  have hpS : p ∈ (S : Set V) := subset_affineSpan (k := Real) (s := C) hpC
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
  have hWdim : Module.finrank Real W = m := by
    simpa [W, S] using hCdim
  have hsum :
      Module.finrank Real W + Module.finrank Real W' = n := by
    have hsum' :
        Module.finrank Real W + Module.finrank Real W' =
          Module.finrank Real V := by
      simpa using
        (Submodule.finrank_add_eq_of_isCompl (K := Real) (V := V) (U := W) (W := W') hW')
    simpa [V, finrank_euclideanSpace_fin] using hsum'
  have hsum' : m + Module.finrank Real W' = n := by
    calc
      m + Module.finrank Real W' = Module.finrank Real W + Module.finrank Real W' := by
        simp [hWdim]
      _ = n := hsum
  have hmn : m ≤ n := by
    exact Nat.le.intro hsum'
  have hW'fin : Module.finrank Real W' = n - m := by
    apply Nat.add_left_cancel
    calc
      m + Module.finrank Real W' = n := hsum'
      _ = m + (n - m) := (Nat.add_sub_of_le hmn).symm
  have eW : W ≃ₗ[Real] EuclideanSpace Real (Fin m) :=
    LinearEquiv.ofFinrankEq _ _ (by
      calc
        Module.finrank Real W = m := hWdim
        _ = Module.finrank Real (EuclideanSpace Real (Fin m)) := by
          simp)
  have eW' : W' ≃ₗ[Real] EuclideanSpace Real (Fin (n - m)) :=
    LinearEquiv.ofFinrankEq _ _ (by
      calc
        Module.finrank Real W' = n - m := hW'fin
        _ = Module.finrank Real (EuclideanSpace Real (Fin (n - m))) := by
          simp)
  let e_split : V ≃ₗ[Real] W × W' :=
    (Submodule.prodEquivOfIsCompl W W' hW').symm
  let e_prod := LinearEquiv.prodCongr eW eW'
  let e_m : EuclideanSpace Real (Fin m) ≃ₗ[Real] (Fin m → ℝ) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)).toLinearEquiv
  let e_p : EuclideanSpace Real (Fin (n - m)) ≃ₗ[Real] (Fin (n - m) → ℝ) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (n - m))).toLinearEquiv
  let e_n : EuclideanSpace Real (Fin n) ≃ₗ[Real] (Fin n → ℝ) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).toLinearEquiv
  have hmln : m + (n - m) = n := Nat.add_sub_of_le hmn
  let e_sum :
      ((Fin m → ℝ) × (Fin (n - m) → ℝ)) ≃ₗ[Real] (Fin m ⊕ Fin (n - m) → ℝ) :=
    (LinearEquiv.sumArrowLequivProdArrow (Fin m) (Fin (n - m)) ℝ ℝ).symm
  let e_reindex :
      (Fin m ⊕ Fin (n - m) → ℝ) ≃ₗ[Real] (Fin (m + (n - m)) → ℝ) :=
    LinearEquiv.piCongrLeft (R := ℝ) (φ := fun _ => ℝ) finSumFinEquiv
  let e_reindex' :
      (Fin (m + (n - m)) → ℝ) ≃ₗ[Real] (Fin n → ℝ) :=
    LinearEquiv.piCongrLeft (R := ℝ) (φ := fun _ => ℝ) (finCongr hmln)
  let e_append_fun' :
      ((Fin m → ℝ) × (Fin (n - m) → ℝ)) ≃ₗ[Real] (Fin n → ℝ) :=
    LinearEquiv.trans e_sum (LinearEquiv.trans e_reindex e_reindex')
  let e_append :
      (EuclideanSpace Real (Fin m) × EuclideanSpace Real (Fin (n - m)))
        ≃ₗ[Real] V := by
    exact (LinearEquiv.trans (LinearEquiv.prodCongr e_m e_p) e_append_fun').trans e_n.symm
  let A : V ≃ₗ[Real] V :=
    LinearEquiv.trans e_split (LinearEquiv.trans e_prod e_append)
  let T : V ≃ᵃ[Real] V := AffineEquiv.ofLinearEquiv A p 0
  refine ⟨T, ?_⟩
  have hTimage :
      T '' (S : Set V) = A '' (W : Set V) := by
    ext z; constructor
    · rintro ⟨x, hxS, rfl⟩
      refine ⟨x -ᵥ p, ?_, ?_⟩
      · exact (AffineSubspace.vsub_right_mem_direction_iff_mem (s := S) hpS x).2 hxS
      · simp [T, AffineEquiv.ofLinearEquiv_apply]
    · rintro ⟨v, hvW, rfl⟩
      refine ⟨v +ᵥ p, ?_, ?_⟩
      · exact AffineSubspace.vadd_mem_of_mem_direction hvW hpS
      · simp [T, AffineEquiv.ofLinearEquiv_apply]
  have hAimage :
      A '' (W : Set V) = coordinateSubspace n m := by
    ext z; constructor
    · rintro ⟨v, hvW, rfl⟩
      have hv' : e_split v = (⟨v, hvW⟩, 0) := by
        simpa [e_split] using
          (Submodule.prodEquivOfIsCompl_symm_apply_left (p := W) (q := W') hW' ⟨v, hvW⟩)
      let g : Fin n → ℝ :=
        (LinearEquiv.piCongrLeft (R := ℝ) (φ := fun _ : Fin n => ℝ) (finCongr hmln))
          ((LinearEquiv.piCongrLeft (R := ℝ) (φ := fun _ : Fin (m + (n - m)) => ℝ) finSumFinEquiv)
            ((LinearEquiv.sumArrowLequivProdArrow (Fin m) (Fin (n - m)) ℝ ℝ).symm
              (e_m (eW ⟨v, hvW⟩), 0)))
      -- show the coordinates past m vanish
      have hg : ∀ i : Fin n, m ≤ (i : Nat) → g i = 0 := by
        intro i hi
        have hi' : m ≤ ((finCongr hmln).symm i : Nat) := by
          simpa using hi
        have hj_lt : (i : Nat) - m < n - m := by
          exact Nat.sub_lt_sub_right (a := (i : Nat)) (b := n) (c := m) hi i.is_lt
        let j : Fin (n - m) := ⟨(i : Nat) - m, hj_lt⟩
        have hij : (finCongr hmln).symm i = Fin.natAdd m j := by
          ext
          simp [Fin.natAdd, j, Nat.add_sub_of_le hi]
        dsimp [g]
        rw [piCongrLeft_apply_const, piCongrLeft_apply_const, hij]
        simp
      intro i hi
      have hg' : g i = 0 := hg i hi
      have hfun : e_n (A v) = g := by
        have hA : A v = e_n.symm g := by
          simp [A, e_split, e_prod, e_append, e_append_fun', e_sum, e_reindex, e_reindex', hv', g]
          rfl
        simp [hA]
      have hAv : (A v).ofLp i = g i := by
        simpa [e_n, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using
          congrArg (fun f => f i) hfun
      simpa [hAv] using hg'
    · intro hz
      refine ⟨A.symm z, ?_, by simp⟩
      have hz' : ∀ i : Fin n, m ≤ (i : Nat) → (e_n z) i = 0 := by
        simpa [coordinateSubspace, e_n, EuclideanSpace.equiv,
          PiLp.coe_continuousLinearEquiv] using hz
      have hzero : (e_append_fun'.symm (e_n z)).2 = 0 := by
        ext j
        have hj : m ≤ ((finCongr hmln) (Fin.natAdd m j) : Nat) := by
          simp [Fin.natAdd]
        have hzj : (e_n z) ((finCongr hmln) (Fin.natAdd m j)) = 0 := hz' _ hj
        simpa [e_append_fun', e_sum, e_reindex, e_reindex', LinearEquiv.symm_trans_apply, hzj]
      have hsplit : (e_split (A.symm z)).2 = 0 := by
        simpa [A, e_split, e_prod, e_append, LinearEquiv.symm_trans_apply, LinearEquiv.trans_apply,
          LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply] using hzero
      exact
        (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero (p := W) (q := W') hW').1 hsplit
  exact hTimage.trans hAimage

/-- A half-radius translated ball around `y` stays inside the translated ball around `x`
when `y` is within the half-radius ball around `x`. -/
lemma translate_smul_unitBall_subset_translate_smul_unitBall (n : Nat)
    {x y : EuclideanSpace Real (Fin n)} {ε : Real} (hε : 0 < ε)
    (hy : y ∈ (fun v => x + v) '' ((ε / 2) • euclideanUnitBall n)) :
    (fun v => y + v) '' ((ε / 2) • euclideanUnitBall n) ⊆
      (fun v => x + v) '' (ε • euclideanUnitBall n) := by
  have hε2 : 0 < ε / 2 := by linarith [hε]
  have hball_x :
      (fun v => x + v) '' ((ε / 2) • euclideanUnitBall n) =
        Metric.closedBall x (ε / 2) := by
    simpa using (translate_smul_unitBall_eq_closedBall n x (ε / 2) hε2)
  have hball_y :
      (fun v => y + v) '' ((ε / 2) • euclideanUnitBall n) =
        Metric.closedBall y (ε / 2) := by
    simpa using (translate_smul_unitBall_eq_closedBall n y (ε / 2) hε2)
  have hball_x_big :
      (fun v => x + v) '' (ε • euclideanUnitBall n) =
        Metric.closedBall x ε := by
    simpa using (translate_smul_unitBall_eq_closedBall n x ε hε)
  have hy' : y ∈ Metric.closedBall x (ε / 2) := by
    simpa [hball_x] using hy
  have hy_dist : dist y x ≤ ε / 2 := (Metric.mem_closedBall.1 hy')
  have hsubset : Metric.closedBall y (ε / 2) ⊆ Metric.closedBall x ε := by
    refine Metric.closedBall_subset_closedBall' ?_
    have hsum : ε / 2 + dist y x ≤ ε / 2 + ε / 2 := by
      simpa [add_comm] using (add_le_add_left hy_dist (ε / 2))
    calc
      ε / 2 + dist y x ≤ ε / 2 + ε / 2 := hsum
      _ = ε := by ring
  intro z hz
  have hz' : z ∈ Metric.closedBall y (ε / 2) := by
    simpa [hball_y] using hz
  have hz'' : z ∈ Metric.closedBall x ε := hsubset hz'
  simpa [hball_x_big] using hz''

/-- A half-radius relative ball around a relative interior point is still in the relative
interior. -/
lemma small_ball_subset_relativeInterior (n : Nat)
    {C : Set (EuclideanSpace Real (Fin n))} {x : EuclideanSpace Real (Fin n)}
    (hx : x ∈ euclideanRelativeInterior n C) :
    ∃ ε : ℝ, 0 < ε ∧
      ((fun y => x + y) '' ((ε / 2) • euclideanUnitBall n)) ∩
          (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) ⊆
        euclideanRelativeInterior n C := by
  rcases hx with ⟨-, ε, hε, hxsub⟩
  refine ⟨ε, hε, ?_⟩
  intro y hy
  rcases hy with ⟨hy_ball, hy_aff⟩
  have hε2 : 0 < ε / 2 := by linarith [hε]
  have hsubset :
      (fun v => y + v) '' ((ε / 2) • euclideanUnitBall n) ⊆
        (fun v => x + v) '' (ε • euclideanUnitBall n) :=
    translate_smul_unitBall_subset_translate_smul_unitBall (n := n) (x := x) (y := y)
      (ε := ε) hε hy_ball
  refine ⟨hy_aff, ε / 2, hε2, ?_⟩
  intro z hz
  rcases hz with ⟨hz_ball, hz_aff⟩
  have hz' : z ∈ (fun v => x + v) '' (ε • euclideanUnitBall n) :=
    hsubset hz_ball
  have hz'' :
      z ∈ ((fun v => x + v) '' (ε • euclideanUnitBall n)) ∩
          (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) :=
    ⟨hz', hz_aff⟩
  exact hxsub hz''

/-- Text 6.17: For any set `C` in `R^n`, convex or not, the laws
`cl (cl C) = cl C` and `ri (ri C) = ri C` are valid. -/
theorem euclidean_closure_closure_eq_and_relativeInterior_relativeInterior_eq (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) :
    closure (closure C) = closure C ∧
      euclideanRelativeInterior n (euclideanRelativeInterior n C) =
        euclideanRelativeInterior n C := by
  constructor
  · simp
  · apply subset_antisymm
    · exact (euclideanRelativeInterior_subset_closure n (euclideanRelativeInterior n C)).1
    · intro x hx
      have hx_aff :
          x ∈ (affineSpan Real (euclideanRelativeInterior n C) :
            Set (EuclideanSpace Real (Fin n))) :=
        subset_affineSpan (k := Real) (s := euclideanRelativeInterior n C) hx
      rcases small_ball_subset_relativeInterior (n := n) (C := C) (x := x) hx with
        ⟨ε, hε, hsubset⟩
      have hε2 : 0 < ε / 2 := by linarith [hε]
      have hri_subset : euclideanRelativeInterior n C ⊆ C :=
        (euclideanRelativeInterior_subset_closure n C).1
      have hspan :
          (affineSpan Real (euclideanRelativeInterior n C) :
            Set (EuclideanSpace Real (Fin n))) ⊆
            (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) := by
        intro y hy
        exact (affineSpan_mono (k := Real) hri_subset) hy
      refine ⟨hx_aff, ε / 2, hε2, ?_⟩
      intro y hy
      rcases hy with ⟨hy_ball, hy_aff⟩
      have hy_affC :
          y ∈ (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) :=
        hspan hy_aff
      have hy' :
          y ∈ ((fun z => x + z) '' ((ε / 2) • euclideanUnitBall n)) ∩
              (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) :=
        ⟨hy_ball, hy_affC⟩
      exact hsubset hy'

/-- Auxiliary: the direct-sum set `C1 ⊕ C2` in `R^{m+p}`, built via `Fin.appendIsometry`. -/
def directSumSetEuclidean (m p : Nat)
    (C1 : Set (EuclideanSpace Real (Fin m))) (C2 : Set (EuclideanSpace Real (Fin p))) :
    Set (EuclideanSpace Real (Fin (m + p))) :=
  (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m + p))).symm ''
    ((Fin.appendIsometry m p) '' Set.prod
      ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) '' C1)
      ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)) '' C2))

/-- Express the direct-sum set as the image of the product under the append map. -/
lemma directSumSetEuclidean_eq_image_append (m p : Nat)
    (C1 : Set (EuclideanSpace Real (Fin m))) (C2 : Set (EuclideanSpace Real (Fin p))) :
    let append :
        EuclideanSpace Real (Fin m) → EuclideanSpace Real (Fin p) →
          EuclideanSpace Real (Fin (m + p)) :=
      fun x y =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m + p))).symm
          ((Fin.appendIsometry m p)
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) x,
             (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)) y))
    directSumSetEuclidean m p C1 C2 = (fun xy => append xy.1 xy.2) '' Set.prod C1 C2 := by
  classical
  intro append
  ext z; constructor
  · intro hz
    rcases hz with ⟨w, hw, rfl⟩
    rcases hw with ⟨⟨u, v⟩, huv, rfl⟩
    rcases huv with ⟨hu, hv⟩
    rcases hu with ⟨x, hx, rfl⟩
    rcases hv with ⟨y, hy, rfl⟩
    refine ⟨(x, y), ?_, rfl⟩
    exact ⟨hx, hy⟩
  · rintro ⟨⟨x, y⟩, hxy, rfl⟩
    rcases hxy with ⟨hx, hy⟩
    refine ⟨(Fin.appendIsometry m p)
        ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) x,
         (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)) y), ?_, rfl⟩
    refine ⟨((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) x,
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)) y), ?_, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩

/-- The append map on Euclidean spaces is a homeomorphism. -/
noncomputable def appendHomeomorph (m p : Nat) :
    (EuclideanSpace Real (Fin m) × EuclideanSpace Real (Fin p)) ≃ₜ
      EuclideanSpace Real (Fin (m + p)) :=
  (Homeomorph.prodCongr
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)).toHomeomorph
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)).toHomeomorph
    ).trans
    ((Fin.appendIsometry m p).toHomeomorph.trans
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m + p))).symm.toHomeomorph)

/-- The append map on Euclidean spaces is an affine equivalence. -/
noncomputable def appendAffineEquiv (m p : Nat) :
    (EuclideanSpace Real (Fin m) × EuclideanSpace Real (Fin p)) ≃ᵃ[Real]
      EuclideanSpace Real (Fin (m + p)) :=
by
  let e_m : EuclideanSpace Real (Fin m) ≃ᵃ[Real] (Fin m → ℝ) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)).toLinearEquiv.toAffineEquiv
  let e_p : EuclideanSpace Real (Fin p) ≃ᵃ[Real] (Fin p → ℝ) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)).toLinearEquiv.toAffineEquiv
  let e_mp : EuclideanSpace Real (Fin (m + p)) ≃ᵃ[Real] (Fin (m + p) → ℝ) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m + p))).toLinearEquiv.toAffineEquiv
  let e_prod : (EuclideanSpace Real (Fin m) × EuclideanSpace Real (Fin p)) ≃ᵃ[Real]
      (Fin m → ℝ) × (Fin p → ℝ) := AffineEquiv.prodCongr e_m e_p
  let e_append : (Fin m → ℝ) × (Fin p → ℝ) ≃ᵃ[Real] (Fin (m + p) → ℝ) :=
    (Fin.appendIsometry m p).toRealAffineIsometryEquiv.toAffineEquiv
  exact (e_prod.trans e_append).trans e_mp.symm

/-- The append affine equivalence acts as the explicit append map on coordinates. -/
lemma appendAffineEquiv_apply (m p : Nat) (x : EuclideanSpace Real (Fin m))
    (y : EuclideanSpace Real (Fin p)) :
    appendAffineEquiv m p (x, y) =
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m + p))).symm
        ((Fin.appendIsometry m p)
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) x,
           (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)) y)) := by
  rfl

/-- Express the direct-sum set as the image of the product under `appendAffineEquiv`. -/
lemma directSumSetEuclidean_eq_image_appendAffineEquiv (m p : Nat)
    (C1 : Set (EuclideanSpace Real (Fin m))) (C2 : Set (EuclideanSpace Real (Fin p))) :
    directSumSetEuclidean m p C1 C2 = (appendAffineEquiv m p) '' Set.prod C1 C2 := by
  classical
  ext z; constructor
  · intro hz
    have hz' :
        z ∈ (fun xy =>
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m + p))).symm
            ((Fin.appendIsometry m p)
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) xy.1,
               (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)) xy.2))) '' Set.prod C1 C2 := by
      simpa [directSumSetEuclidean_eq_image_append] using hz
    rcases hz' with ⟨xy, hxy, rfl⟩
    refine ⟨xy, hxy, ?_⟩
    rcases xy with ⟨x, y⟩
    simp [appendAffineEquiv_apply]
  · intro hz
    rcases hz with ⟨xy, hxy, rfl⟩
    rcases xy with ⟨x, y⟩
    have hz' :
        appendAffineEquiv m p (x, y) ∈
          (fun xy =>
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m + p))).symm
              ((Fin.appendIsometry m p)
                ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) xy.1,
                 (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)) xy.2))) '' Set.prod C1 C2 := by
      refine ⟨(x, y), hxy, ?_⟩
      simp [appendAffineEquiv_apply]
    simpa [directSumSetEuclidean_eq_image_append] using hz'

/-- The affine span of a product is the product of affine spans. -/
lemma affineSpan_prod_eq (m p : Nat)
    (C1 : Set (EuclideanSpace Real (Fin m))) (C2 : Set (EuclideanSpace Real (Fin p))) :
    (affineSpan Real (Set.prod C1 C2) :
        Set ((EuclideanSpace Real (Fin m)) × (EuclideanSpace Real (Fin p)))) =
      Set.prod (affineSpan Real C1 : Set (EuclideanSpace Real (Fin m)))
        (affineSpan Real C2 : Set (EuclideanSpace Real (Fin p))) := by
  classical
  ext z; constructor
  · intro hz
    have hz1 : z.1 ∈ (affineSpan Real C1 : Set (EuclideanSpace Real (Fin m))) := by
      have hmap :
          (affineSpan Real (Set.prod C1 C2)).map
              (AffineMap.fst :
                (EuclideanSpace Real (Fin m) × EuclideanSpace Real (Fin p)) →ᵃ[Real]
                  EuclideanSpace Real (Fin m)) =
            affineSpan Real (Prod.fst '' Set.prod C1 C2) := by
        simpa using
          (AffineSubspace.map_span (k := Real)
            (f := (AffineMap.fst :
              (EuclideanSpace Real (Fin m) × EuclideanSpace Real (Fin p)) →ᵃ[Real]
                EuclideanSpace Real (Fin m)))
            (s := Set.prod C1 C2))
      have hz1' :
          z.1 ∈
              ((affineSpan Real (Set.prod C1 C2)).map
                  (AffineMap.fst :
                    (EuclideanSpace Real (Fin m) × EuclideanSpace Real (Fin p)) →ᵃ[Real]
                      EuclideanSpace Real (Fin m)) : Set _) := by
        exact ⟨z, hz, rfl⟩
      have hz1'' : z.1 ∈ affineSpan Real (Prod.fst '' Set.prod C1 C2) := by
        simpa [hmap] using hz1'
      have himage : Prod.fst '' Set.prod C1 C2 ⊆ C1 := by
        intro x hx
        rcases hx with ⟨⟨x', y'⟩, ⟨hx', hy'⟩, rfl⟩
        exact hx'
      exact (affineSpan_mono (k := Real) himage) hz1''
    have hz2 : z.2 ∈ (affineSpan Real C2 : Set (EuclideanSpace Real (Fin p))) := by
      have hmap :
          (affineSpan Real (Set.prod C1 C2)).map
              (AffineMap.snd :
                (EuclideanSpace Real (Fin m) × EuclideanSpace Real (Fin p)) →ᵃ[Real]
                  EuclideanSpace Real (Fin p)) =
            affineSpan Real (Prod.snd '' Set.prod C1 C2) := by
        simpa using
          (AffineSubspace.map_span (k := Real)
            (f := (AffineMap.snd :
              (EuclideanSpace Real (Fin m) × EuclideanSpace Real (Fin p)) →ᵃ[Real]
                EuclideanSpace Real (Fin p)))
            (s := Set.prod C1 C2))
      have hz2' :
          z.2 ∈
              ((affineSpan Real (Set.prod C1 C2)).map
                  (AffineMap.snd :
                    (EuclideanSpace Real (Fin m) × EuclideanSpace Real (Fin p)) →ᵃ[Real]
                      EuclideanSpace Real (Fin p)) : Set _) := by
        exact ⟨z, hz, rfl⟩
      have hz2'' : z.2 ∈ affineSpan Real (Prod.snd '' Set.prod C1 C2) := by
        simpa [hmap] using hz2'
      have himage : Prod.snd '' Set.prod C1 C2 ⊆ C2 := by
        intro y hy
        rcases hy with ⟨⟨x', y'⟩, ⟨hx', hy'⟩, rfl⟩
        exact hy'
      exact (affineSpan_mono (k := Real) himage) hz2''
    exact ⟨hz1, hz2⟩
  · rintro ⟨hz1, hz2⟩
    set s : Set ((EuclideanSpace Real (Fin m)) × (EuclideanSpace Real (Fin p))) :=
      Set.prod C1 C2
    have hprod :
        ∀ x, x ∈ affineSpan Real C1 →
          ∀ y, y ∈ affineSpan Real C2 → (x, y) ∈ affineSpan Real s := by
      intro x hx
      refine affineSpan_induction (k := Real) (s := C1) (x := x)
        (p := fun x => ∀ y, y ∈ affineSpan Real C2 → (x, y) ∈ affineSpan Real s) hx ?mem ?smul
      · intro x hxC1 y hy
        refine affineSpan_induction (k := Real) (s := C2) (x := y)
          (p := fun y => (x, y) ∈ affineSpan Real s) hy ?mem2 ?smul2
        · intro y hyC2
          exact subset_affineSpan (k := Real) (s := s) ⟨hxC1, hyC2⟩
        · intro c u v w hu hv hw
          have hmem :
              c • ((x, u) -ᵥ (x, v)) +ᵥ (x, w) ∈ affineSpan Real s :=
            AffineSubspace.smul_vsub_vadd_mem (affineSpan Real s) c hu hv hw
          have h_eq :
              c • ((x, u) -ᵥ (x, v)) +ᵥ (x, w) = (x, c • (u -ᵥ v) +ᵥ w) := by
            ext <;>
              simp [vsub_eq_sub, vadd_eq_add, add_comm]
          simpa [h_eq] using hmem
      · intro c u v w hu hv hw y hy
        have hu' : (u, y) ∈ affineSpan Real s := hu y hy
        have hv' : (v, y) ∈ affineSpan Real s := hv y hy
        have hw' : (w, y) ∈ affineSpan Real s := hw y hy
        have hmem :
            c • ((u, y) -ᵥ (v, y)) +ᵥ (w, y) ∈ affineSpan Real s :=
          AffineSubspace.smul_vsub_vadd_mem (affineSpan Real s) c hu' hv' hw'
        have h_eq :
            c • ((u, y) -ᵥ (v, y)) +ᵥ (w, y) = (c • (u -ᵥ v) +ᵥ w, y) := by
          ext <;>
            simp [vsub_eq_sub, vadd_eq_add, add_comm]
        simpa [h_eq] using hmem
    exact hprod z.1 hz1 z.2 hz2

/-- The affine span of the direct-sum set factors as the direct sum of affine spans. -/
lemma affineSpan_directSumSetEuclidean_eq (m p : Nat)
    (C1 : Set (EuclideanSpace Real (Fin m))) (C2 : Set (EuclideanSpace Real (Fin p))) :
    (affineSpan Real (directSumSetEuclidean m p C1 C2) :
        Set (EuclideanSpace Real (Fin (m + p)))) =
      directSumSetEuclidean m p (affineSpan Real C1 : Set (EuclideanSpace Real (Fin m)))
        (affineSpan Real C2 : Set (EuclideanSpace Real (Fin p))) := by
  classical
  have hmap :
      (affineSpan Real ((appendAffineEquiv m p) '' Set.prod C1 C2) :
          Set (EuclideanSpace Real (Fin (m + p)))) =
        (appendAffineEquiv m p) '' (affineSpan Real (Set.prod C1 C2) : Set _) := by
    have h :=
      (AffineSubspace.map_span (k := Real)
        (f := (appendAffineEquiv m p).toAffineMap) (s := Set.prod C1 C2)).symm
    have h' :=
      congrArg
        (fun s : AffineSubspace Real (EuclideanSpace Real (Fin (m + p))) =>
          (s : Set (EuclideanSpace Real (Fin (m + p))))) h
    simpa [AffineSubspace.coe_map] using h'
  calc
    (affineSpan Real (directSumSetEuclidean m p C1 C2) :
        Set (EuclideanSpace Real (Fin (m + p)))) =
        (affineSpan Real ((appendAffineEquiv m p) '' Set.prod C1 C2) :
          Set (EuclideanSpace Real (Fin (m + p)))) := by
        simp [directSumSetEuclidean_eq_image_appendAffineEquiv]
    _ = (appendAffineEquiv m p) '' (affineSpan Real (Set.prod C1 C2) : Set _) := hmap
    _ =
        (appendAffineEquiv m p) '' Set.prod (affineSpan Real C1 : Set _)
          (affineSpan Real C2 : Set _) := by
        simpa using
          congrArg (fun s => (appendAffineEquiv m p) '' s) (affineSpan_prod_eq m p C1 C2)
    _ =
        directSumSetEuclidean m p (affineSpan Real C1 : Set _) (affineSpan Real C2 : Set _) := by
        symm
        simpa using
          (directSumSetEuclidean_eq_image_appendAffineEquiv m p
            (affineSpan Real C1 : Set _) (affineSpan Real C2 : Set _))

/-- The closure of the direct-sum set factors as the direct sum of closures. -/
lemma closure_directSumSetEuclidean_eq (m p : Nat)
    (C1 : Set (EuclideanSpace Real (Fin m))) (C2 : Set (EuclideanSpace Real (Fin p))) :
    closure (directSumSetEuclidean m p C1 C2) =
      directSumSetEuclidean m p (closure C1) (closure C2) := by
  classical
  have h1 :
      closure (directSumSetEuclidean m p C1 C2) =
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m + p))).symm ''
          closure ((Fin.appendIsometry m p) '' Set.prod
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) '' C1)
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)) '' C2)) := by
    simpa [directSumSetEuclidean] using
      (Homeomorph.image_closure
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m + p))).symm.toHomeomorph
        ((Fin.appendIsometry m p) '' Set.prod
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) '' C1)
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)) '' C2))).symm
  have h2 :
      closure ((Fin.appendIsometry m p) '' Set.prod
        ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) '' C1)
        ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)) '' C2)) =
        (Fin.appendIsometry m p) '' closure (Set.prod
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) '' C1)
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)) '' C2)) := by
    simpa using
      (Homeomorph.image_closure (Fin.appendIsometry m p).toHomeomorph
        (Set.prod
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) '' C1)
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)) '' C2))).symm
  have hprod :
      closure (Set.prod
        ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) '' C1)
        ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)) '' C2)) =
        Set.prod (closure ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) '' C1))
          (closure ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)) '' C2)) := by
    simpa using
      (closure_prod_eq
        (s := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) '' C1)
        (t := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)) '' C2))
  have hclC1 :
      closure ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) '' C1) =
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) '' closure C1 := by
    simpa using
      (Homeomorph.image_closure
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)).toHomeomorph C1).symm
  have hclC2 :
      closure ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)) '' C2) =
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)) '' closure C2 := by
    simpa using
      (Homeomorph.image_closure
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)).toHomeomorph C2).symm
  calc
    closure (directSumSetEuclidean m p C1 C2) =
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m + p))).symm ''
          closure ((Fin.appendIsometry m p) '' Set.prod
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) '' C1)
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)) '' C2)) := h1
    _ =
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m + p))).symm ''
          ((Fin.appendIsometry m p) '' closure (Set.prod
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) '' C1)
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)) '' C2))) := by
          simp [h2]
    _ =
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m + p))).symm ''
          ((Fin.appendIsometry m p) '' Set.prod
            (closure ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) '' C1))
            (closure ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)) '' C2))) := by
          simp [hprod]
    _ =
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m + p))).symm ''
          ((Fin.appendIsometry m p) '' Set.prod
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) '' closure C1)
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)) '' closure C2)) := by
          simp [hclC1, hclC2]
    _ = directSumSetEuclidean m p (closure C1) (closure C2) := by
          rfl

/-- Forward inclusion for the relative interior of a direct sum. -/
lemma euclideanRelativeInterior_directSumSetEuclidean_subset (m p : Nat)
    (C1 : Set (EuclideanSpace Real (Fin m))) (C2 : Set (EuclideanSpace Real (Fin p))) :
    euclideanRelativeInterior (m + p) (directSumSetEuclidean m p C1 C2) ⊆
      directSumSetEuclidean m p (euclideanRelativeInterior m C1)
        (euclideanRelativeInterior p C2) := by
  intro z hz
  rcases hz with ⟨hz_aff, ε, hε, hz_subset⟩
  have hz_subset' :
      Metric.closedBall z ε ∩
          (affineSpan Real (directSumSetEuclidean m p C1 C2) :
            Set (EuclideanSpace Real (Fin (m + p)))) ⊆
        directSumSetEuclidean m p C1 C2 := by
    have hball :
        (fun y => z + y) '' (ε • euclideanUnitBall (m + p)) =
          Metric.closedBall z ε := by
      simpa using
        (translate_smul_unitBall_eq_closedBall (n := m + p) (a := z) (ε := ε) hε)
    simpa [hball] using hz_subset
  have hz_aff' :
      z ∈ directSumSetEuclidean m p (affineSpan Real C1) (affineSpan Real C2) := by
    have hz_aff' := hz_aff
    rw [affineSpan_directSumSetEuclidean_eq (m := m) (p := p) (C1 := C1) (C2 := C2)] at hz_aff'
    exact hz_aff'
  have hz_aff'' := hz_aff'
  rw [directSumSetEuclidean_eq_image_appendAffineEquiv] at hz_aff''
  rcases hz_aff'' with ⟨⟨x, y⟩, hxy, rfl⟩
  rcases hxy with ⟨hx_aff, hy_aff⟩
  have hx_ri : x ∈ euclideanRelativeInterior m C1 := by
    let g : EuclideanSpace Real (Fin m) → EuclideanSpace Real (Fin (m + p)) :=
      fun u => appendAffineEquiv m p (u, y)
    have hcont_append :
        Continuous (appendAffineEquiv m p :
          (EuclideanSpace Real (Fin m) × EuclideanSpace Real (Fin p)) →
            EuclideanSpace Real (Fin (m + p))) :=
      (AffineEquiv.continuous_of_finiteDimensional (f := appendAffineEquiv m p))
    have hcont_g : Continuous g := by
      have hcont_pair : Continuous (fun u : EuclideanSpace Real (Fin m) => (u, y)) :=
        continuous_id.prodMk continuous_const
      simpa [g] using hcont_append.comp hcont_pair
    have hopen :
        IsOpen (g ⁻¹' Metric.ball (appendAffineEquiv m p (x, y)) ε) :=
      Metric.isOpen_ball.preimage hcont_g
    have hxball :
        x ∈ g ⁻¹' Metric.ball (appendAffineEquiv m p (x, y)) ε := by
      change g x ∈ Metric.ball (appendAffineEquiv m p (x, y)) ε
      simpa [g] using
        (Metric.mem_ball_self (x := appendAffineEquiv m p (x, y)) hε)
    rcases (Metric.isOpen_iff.mp hopen) x hxball with ⟨δ, hδpos, hballδ⟩
    have hδpos2 : 0 < δ / 2 := by linarith [hδpos]
    have hsubset_ball :
        Metric.closedBall x (δ / 2) ⊆ g ⁻¹' Metric.ball (appendAffineEquiv m p (x, y)) ε := by
      intro u hu
      have hu' : u ∈ Metric.ball x δ := by
        have hsub : Metric.closedBall x (δ / 2) ⊆ Metric.ball x δ :=
          Metric.closedBall_subset_ball (by linarith [hδpos])
        exact hsub hu
      exact hballδ hu'
    refine ⟨hx_aff, δ / 2, hδpos2, ?_⟩
    intro u hu
    rcases hu with ⟨hu_ball, hu_aff⟩
    have hu_ball' : u ∈ Metric.closedBall x (δ / 2) := by
      have hball_x :
          (fun v => x + v) '' ((δ / 2) • euclideanUnitBall m) =
            Metric.closedBall x (δ / 2) := by
        simpa using
          (translate_smul_unitBall_eq_closedBall (n := m) (a := x) (ε := δ / 2) hδpos2)
      simpa [hball_x] using hu_ball
    have hu_ball'' :
        g u ∈ Metric.ball (appendAffineEquiv m p (x, y)) ε := hsubset_ball hu_ball'
    have hu_ball_closed :
        g u ∈ Metric.closedBall (appendAffineEquiv m p (x, y)) ε :=
      Metric.ball_subset_closedBall hu_ball''
    have hu_aff' :
        g u ∈
          (affineSpan Real (directSumSetEuclidean m p C1 C2) :
            Set (EuclideanSpace Real (Fin (m + p)))) := by
      have hpair :
          g u ∈ directSumSetEuclidean m p (affineSpan Real C1 : Set _)
            (affineSpan Real C2 : Set _) := by
        have : g u ∈ (appendAffineEquiv m p) '' Set.prod
            (affineSpan Real C1 : Set _) (affineSpan Real C2 : Set _) := by
          refine ⟨(u, y), ?_, by simp [g]⟩
          exact ⟨hu_aff, hy_aff⟩
        simpa [directSumSetEuclidean_eq_image_appendAffineEquiv] using this
      have hpair' := hpair
      rw [← affineSpan_directSumSetEuclidean_eq (m := m) (p := p) (C1 := C1) (C2 := C2)] at hpair'
      exact hpair'
    have hu_in : g u ∈ directSumSetEuclidean m p C1 C2 :=
      hz_subset' ⟨hu_ball_closed, hu_aff'⟩
    have hu_in' := hu_in
    rw [directSumSetEuclidean_eq_image_appendAffineEquiv] at hu_in'
    rcases hu_in' with ⟨⟨u', v'⟩, ⟨hu'C1, hv'C2⟩, hEq⟩
    have hpair : (u', v') = (u, y) := (appendAffineEquiv m p).injective hEq
    have huC1 : u ∈ C1 := by
      cases hpair
      simpa using hu'C1
    exact huC1
  have hy_ri : y ∈ euclideanRelativeInterior p C2 := by
    let g : EuclideanSpace Real (Fin p) → EuclideanSpace Real (Fin (m + p)) :=
      fun v => appendAffineEquiv m p (x, v)
    have hcont_append :
        Continuous (appendAffineEquiv m p :
          (EuclideanSpace Real (Fin m) × EuclideanSpace Real (Fin p)) →
            EuclideanSpace Real (Fin (m + p))) :=
      (AffineEquiv.continuous_of_finiteDimensional (f := appendAffineEquiv m p))
    have hcont_g : Continuous g := by
      have hcont_pair : Continuous (fun v : EuclideanSpace Real (Fin p) => (x, v)) :=
        continuous_const.prodMk continuous_id
      simpa [g] using hcont_append.comp hcont_pair
    have hopen :
        IsOpen (g ⁻¹' Metric.ball (appendAffineEquiv m p (x, y)) ε) :=
      Metric.isOpen_ball.preimage hcont_g
    have hyball :
        y ∈ g ⁻¹' Metric.ball (appendAffineEquiv m p (x, y)) ε := by
      change g y ∈ Metric.ball (appendAffineEquiv m p (x, y)) ε
      simpa [g] using
        (Metric.mem_ball_self (x := appendAffineEquiv m p (x, y)) hε)
    rcases (Metric.isOpen_iff.mp hopen) y hyball with ⟨δ, hδpos, hballδ⟩
    have hδpos2 : 0 < δ / 2 := by linarith [hδpos]
    have hsubset_ball :
        Metric.closedBall y (δ / 2) ⊆ g ⁻¹' Metric.ball (appendAffineEquiv m p (x, y)) ε := by
      intro v hv
      have hv' : v ∈ Metric.ball y δ := by
        have hsub : Metric.closedBall y (δ / 2) ⊆ Metric.ball y δ :=
          Metric.closedBall_subset_ball (by linarith [hδpos])
        exact hsub hv
      exact hballδ hv'
    refine ⟨hy_aff, δ / 2, hδpos2, ?_⟩
    intro v hv
    rcases hv with ⟨hv_ball, hv_aff⟩
    have hv_ball' : v ∈ Metric.closedBall y (δ / 2) := by
      have hball_y :
          (fun v' => y + v') '' ((δ / 2) • euclideanUnitBall p) =
            Metric.closedBall y (δ / 2) := by
        simpa using
          (translate_smul_unitBall_eq_closedBall (n := p) (a := y) (ε := δ / 2) hδpos2)
      simpa [hball_y] using hv_ball
    have hv_ball'' :
        g v ∈ Metric.ball (appendAffineEquiv m p (x, y)) ε := hsubset_ball hv_ball'
    have hv_ball_closed :
        g v ∈ Metric.closedBall (appendAffineEquiv m p (x, y)) ε :=
      Metric.ball_subset_closedBall hv_ball''
    have hv_aff' :
        g v ∈
          (affineSpan Real (directSumSetEuclidean m p C1 C2) :
            Set (EuclideanSpace Real (Fin (m + p)))) := by
      have hpair :
          g v ∈ directSumSetEuclidean m p (affineSpan Real C1 : Set _)
            (affineSpan Real C2 : Set _) := by
        have : g v ∈ (appendAffineEquiv m p) '' Set.prod
            (affineSpan Real C1 : Set _) (affineSpan Real C2 : Set _) := by
          refine ⟨(x, v), ?_, by simp [g]⟩
          exact ⟨hx_aff, hv_aff⟩
        simpa [directSumSetEuclidean_eq_image_appendAffineEquiv] using this
      have hpair' := hpair
      rw [← affineSpan_directSumSetEuclidean_eq (m := m) (p := p) (C1 := C1) (C2 := C2)] at hpair'
      exact hpair'
    have hv_in : g v ∈ directSumSetEuclidean m p C1 C2 :=
      hz_subset' ⟨hv_ball_closed, hv_aff'⟩
    have hv_in' := hv_in
    rw [directSumSetEuclidean_eq_image_appendAffineEquiv] at hv_in'
    rcases hv_in' with ⟨⟨u', v'⟩, ⟨hu'C1, hv'C2⟩, hEq⟩
    have hpair : (u', v') = (x, v) := (appendAffineEquiv m p).injective hEq
    have hvC2 : v ∈ C2 := by
      cases hpair
      simpa using hv'C2
    exact hvC2
  have hz' :
      appendAffineEquiv m p (x, y) ∈
        (appendAffineEquiv m p) '' Set.prod (euclideanRelativeInterior m C1)
          (euclideanRelativeInterior p C2) := by
    exact ⟨(x, y), ⟨hx_ri, hy_ri⟩, rfl⟩
  simpa [directSumSetEuclidean_eq_image_appendAffineEquiv] using hz'


end Section06
end Chap02
