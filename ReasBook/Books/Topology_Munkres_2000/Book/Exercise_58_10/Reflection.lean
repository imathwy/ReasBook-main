module

public import Topology_Munkres_2000.Book.Definition_57_2.Antipodal

noncomputable section

public section

namespace StandardSphere

/-- Reflection in the last coordinate hyperplane of `ℝⁿ⁺¹`. -/
def reflectionFunction (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Function.update (fun i ↦ x i) (Fin.last n) (-x (Fin.last n)))

/-- Reflection in the last coordinate preserves the Euclidean norm. -/
theorem norm_reflectionFunction (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖reflectionFunction n x‖ = ‖x‖ := by
  -- Squaring reduces norm preservation to coordinatewise preservation of squares.
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [reflectionFunction, WithLp.ofLp_toLp]
  classical
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i = Fin.last n
  · subst i
    simp
  · simp [h]

/-- Reflection in the last coordinate is continuous. -/
theorem continuous_reflectionFunction (n : ℕ) : Continuous (reflectionFunction n) := by
  -- Coordinate update and negation are continuous in the Euclidean product topology.
  unfold reflectionFunction
  fun_prop

/-- Reflection in the last coordinate preserves membership in the standard sphere. -/
theorem reflectionFunction_mem (n : ℕ) (x : StandardSphere n) :
    reflectionFunction n x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  -- Norm preservation carries unit vectors to unit vectors.
  rw [mem_sphere_zero_iff_norm, norm_reflectionFunction]
  exact mem_sphere_zero_iff_norm.mp x.property

/-- Reflection in the last coordinate restricts to a self-map of the standard sphere. -/
def reflection (n : ℕ) : C(StandardSphere n, StandardSphere n) :=
  ⟨fun x ↦ ⟨reflectionFunction n x, reflectionFunction_mem n x⟩,
    ((continuous_reflectionFunction n).comp continuous_subtype_val).subtype_mk _⟩

/-- Reflection negates the last coordinate and fixes every other coordinate. -/
theorem reflection_apply (n : ℕ) (x : StandardSphere n) (i : Fin (n + 1)) :
    (reflection n x : EuclideanSpace ℝ (Fin (n + 1))) i =
      if i = Fin.last n then -(x : EuclideanSpace ℝ (Fin (n + 1))) i
      else (x : EuclideanSpace ℝ (Fin (n + 1))) i := by
  -- Evaluate the updated coordinate function at the chosen index.
  split_ifs with h
  · subst i
    simp [reflection, reflectionFunction]
  · simp [reflection, reflectionFunction, h]

/-- Helper for Exercise 58.10: swapping a chosen coordinate with the last coordinate is a
linear isometry of the ambient Euclidean space. -/
def coordinateSwapLinearIsometry (n : ℕ) (i : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i (Fin.last n))

/-- Helper for Exercise 58.10: a coordinate swap preserves membership in the unit sphere. -/
theorem coordinateSwapLinearIsometry_mem (n : ℕ) (i : Fin (n + 1))
    (x : StandardSphere n) : coordinateSwapLinearIsometry n i x ∈ StandardSphere n := by
  -- The ambient linear isometry preserves the unit norm.
  rw [mem_sphere_zero_iff_norm, (coordinateSwapLinearIsometry n i).norm_map]
  exact mem_sphere_zero_iff_norm.mp x.property

/-- Helper for Exercise 58.10: swap a chosen sphere coordinate with the last coordinate. -/
def coordinateSwap (n : ℕ) (i : Fin (n + 1)) : C(StandardSphere n, StandardSphere n) :=
  ⟨fun x ↦ ⟨coordinateSwapLinearIsometry n i x, coordinateSwapLinearIsometry_mem n i x⟩,
    ((coordinateSwapLinearIsometry n i).continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- Helper for Exercise 58.10: evaluate a coordinate swap at one coordinate. -/
theorem coordinateSwap_apply (n : ℕ) (i j : Fin (n + 1)) (x : StandardSphere n) :
    (coordinateSwap n i x : EuclideanSpace ℝ (Fin (n + 1))) j =
      (x : EuclideanSpace ℝ (Fin (n + 1))) (Equiv.swap i (Fin.last n) j) := by
  -- The `PiLp` coordinate permutation acts by precomposition with the inverse swap.
  rfl

/-- Helper for Exercise 58.10: swapping the same two sphere coordinates twice is the identity. -/
theorem coordinateSwap_comp_self (n : ℕ) (i : Fin (n + 1)) :
    (coordinateSwap n i).comp (coordinateSwap n i) =
      ContinuousMap.id (StandardSphere n) := by
  -- The underlying transposition is an involution at every coordinate.
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply PiLp.ext
  intro j
  simp only [ContinuousMap.comp_apply, coordinateSwap_apply, Equiv.swap_apply_self]
  rfl

/-- Helper for Exercise 58.10: reflection in any coordinate hyperplane, obtained by conjugating
the distinguished last-coordinate reflection by a coordinate swap. -/
def coordinateReflection (n : ℕ) (i : Fin (n + 1)) :
    C(StandardSphere n, StandardSphere n) :=
  (coordinateSwap n i).comp ((reflection n).comp (coordinateSwap n i))

/-- Helper for Exercise 58.10: expose a coordinate reflection as its conjugation composite. -/
theorem coordinateReflection_def (n : ℕ) (i : Fin (n + 1)) :
    coordinateReflection n i =
      (coordinateSwap n i).comp ((reflection n).comp (coordinateSwap n i)) := by
  -- This is the stable downstream rewrite for the opaque construction.
  rfl

/-- Helper for Exercise 58.10: a coordinate reflection negates exactly its chosen coordinate. -/
theorem coordinateReflection_apply (n : ℕ) (i j : Fin (n + 1)) (x : StandardSphere n) :
    (coordinateReflection n i x : EuclideanSpace ℝ (Fin (n + 1))) j =
      if j = i then -(x : EuclideanSpace ℝ (Fin (n + 1))) j
      else (x : EuclideanSpace ℝ (Fin (n + 1))) j := by
  -- Evaluate the conjugation; the swap sends the chosen coordinate to the last one and back.
  simp only [coordinateReflection, ContinuousMap.comp_apply, coordinateSwap_apply,
    reflection_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right,
    Equiv.swap_apply_self]

/-- Helper for Exercise 58.10: compose reflections in the coordinates listed from left to right. -/
def coordinateReflections (n : ℕ) :
    List (Fin (n + 1)) → C(StandardSphere n, StandardSphere n)
  | [] => ContinuousMap.id (StandardSphere n)
  | i :: indices => (coordinateReflection n i).comp (coordinateReflections n indices)

/-- Helper for Exercise 58.10: the empty coordinate-reflection composite is the identity. -/
theorem coordinateReflections_nil (n : ℕ) :
    coordinateReflections n [] = ContinuousMap.id (StandardSphere n) := by
  -- Expose the base computation rule without unfolding the recursive definition downstream.
  rfl

/-- Helper for Exercise 58.10: adjoining a coordinate prepends its reflection to the composite. -/
theorem coordinateReflections_cons (n : ℕ) (i : Fin (n + 1))
    (indices : List (Fin (n + 1))) :
    coordinateReflections n (i :: indices) =
      (coordinateReflection n i).comp (coordinateReflections n indices) := by
  -- Expose the recursive computation rule without unfolding the construction downstream.
  rfl

/-- Helper for Exercise 58.10: a duplicate-free list of coordinate reflections negates exactly
the coordinates occurring in the list. -/
theorem coordinateReflections_apply (n : ℕ) (indices : List (Fin (n + 1)))
    (hindices : indices.Nodup) (x : StandardSphere n) (j : Fin (n + 1)) :
    (coordinateReflections n indices x : EuclideanSpace ℝ (Fin (n + 1))) j =
      if j ∈ indices then -(x : EuclideanSpace ℝ (Fin (n + 1))) j
      else (x : EuclideanSpace ℝ (Fin (n + 1))) j := by
  -- Induct through the list, using duplicate-freeness to ensure that each coordinate flips once.
  induction indices with
  | nil =>
      simp [coordinateReflections]
  | cons i indices ih =>
      rw [List.nodup_cons] at hindices
      rw [coordinateReflections, ContinuousMap.comp_apply, coordinateReflection_apply]
      by_cases hji : j = i
      · subst j
        rw [if_pos rfl, ih hindices.2, if_neg hindices.1]
        simp
      · rw [if_neg hji, ih hindices.2]
        simp [hji]

/-- Helper for Exercise 58.10: reflecting every coordinate is the antipodal map. -/
theorem coordinateReflections_all_eq_antipodal (n : ℕ) :
    coordinateReflections n (List.ofFn fun i : Fin (n + 1) ↦ i) = antipodal n := by
  -- The complete coordinate list is duplicate-free and contains every coordinate.
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply PiLp.ext
  intro j
  calc
    (coordinateReflections n (List.ofFn fun i : Fin (n + 1) ↦ i) x :
        EuclideanSpace ℝ (Fin (n + 1))) j =
        if j ∈ List.ofFn (fun i : Fin (n + 1) ↦ i) then
          -(x : EuclideanSpace ℝ (Fin (n + 1))) j
        else (x : EuclideanSpace ℝ (Fin (n + 1))) j :=
      coordinateReflections_apply n (List.ofFn fun i : Fin (n + 1) ↦ i)
        (List.nodup_ofFn.mpr Function.injective_id) x j
    _ = (antipodal n x : EuclideanSpace ℝ (Fin (n + 1))) j := by
      simp [antipodal]

end StandardSphere
