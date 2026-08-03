module

public import Topology_Munkres_2000.Book.Lemma_62_2
public import Topology_Munkres_2000.Book.Theorem_61_3
public import Topology_Munkres_2000.Book.Example_18_6
public import Topology_Munkres_2000.Book.Exercise_51_3.Contractible

public section

open Set Metric

noncomputable section

/-- Helper for Exercise 62.1: the standard coordinate realization of the equator. -/
private def equatorPoint (z : Circle) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(z : ℂ).re, (z : ℂ).im, 0]

/-- Helper for Exercise 62.1: the standard equatorial point has norm one. -/
private lemma equatorPoint_norm (z : Circle) : ‖equatorPoint z‖ = 1 := by
  -- Expand the finite Euclidean norm and use the unit-circle equation.
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp [equatorPoint, Matrix.cons_val_succ, Real.norm_eq_abs]
  rw [← Real.sqrt_one]
  congr 1
  simpa only [Real.sqrt_one, sq_abs, pow_two, Complex.normSq_apply] using Circle.normSq_coe z

/-- Helper for Exercise 62.1: the unit circle embeds as the equator of the standard 2-sphere. -/
private def equatorEmbedding (z : Circle) : StandardSphere 2 :=
  ⟨equatorPoint z, mem_sphere_zero_iff_norm.2 (equatorPoint_norm z)⟩

/-- Helper for Exercise 62.1: the equatorial embedding is continuous. -/
private lemma equatorEmbedding_continuous : Continuous equatorEmbedding := by
  -- Continuity is checked coordinatewise in the ambient Euclidean space.
  apply Continuous.subtype_mk
  apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp
  rw [continuous_pi_iff]
  intro i
  fin_cases i
  · exact Complex.continuous_re.comp continuous_subtype_val
  · exact Complex.continuous_im.comp continuous_subtype_val
  · exact continuous_const

/-- Helper for Exercise 62.1: the equatorial embedding is injective. -/
private lemma equatorEmbedding_injective : Function.Injective equatorEmbedding := by
  -- Equality on the sphere recovers both complex coordinates.
  intro z w h
  apply Circle.ext
  apply Complex.ext
  · exact congrArg (fun x : StandardSphere 2 ↦ (x : EuclideanSpace ℝ (Fin 3)) 0) h
  · exact congrArg (fun x : StandardSphere 2 ↦ (x : EuclideanSpace ℝ (Fin 3)) 1) h

/-- Helper for Exercise 62.1: the standard equator as a subset of the 2-sphere. -/
private def equator : Set (StandardSphere 2) :=
  Set.range equatorEmbedding

/-- Helper for Exercise 62.1: the standard equator is a simple closed curve. -/
private instance : Topology.IsSimpleClosedCurve equator := by
  -- A continuous injection from the compact circle is an embedding onto its range.
  refine ⟨⟨(equatorEmbedding_continuous.isClosedEmbedding equatorEmbedding_injective).isEmbedding
    |>.toHomeomorph.symm.trans ?_⟩⟩
  exact Homeomorph.refl Circle

/-- Helper for Exercise 62.1: the closed interval winds once around the unit circle. -/
private def intervalCircleMap : C(unitInterval, Circle) :=
  ⟨fun t ↦ Real.fourierChar t, Real.continuous_fourierChar.comp continuous_subtype_val⟩

/-- Helper for Exercise 62.1: the interval parametrization covers the entire unit circle. -/
private lemma intervalCircleMap_surjective : Function.Surjective intervalCircleMap := by
  -- Use the established bijection on the half-open unit interval and include it in `[0,1]`.
  intro z
  obtain ⟨t, ht, htz⟩ := fourierChar_bijOn_unitIco.2.2 (Set.mem_univ z)
  exact ⟨⟨t, ht.1, le_of_lt ht.2⟩, htz⟩

/-- Helper for Exercise 62.1: the interval parametrization identifies its two endpoints. -/
private lemma intervalCircleMap_not_injective : ¬ Function.Injective intervalCircleMap := by
  -- The Fourier character has period one, while the interval endpoints are distinct.
  intro h
  have endpoints : intervalCircleMap (0 : unitInterval) = intervalCircleMap (1 : unitInterval) := by
    change Real.fourierChar (0 : ℝ) = Real.fourierChar (1 : ℝ)
    simp [Real.fourierChar_apply']
  have endpoint_values := congrArg Subtype.val (h endpoints)
  norm_num at endpoint_values

/-- Helper for Exercise 62.1: the complement of the equator contains two points in distinct
relative connected components. -/
private lemma exists_points_separated_by_equator :
    ∃ a b : StandardSphere 2, a ∈ equatorᶜ ∧ b ∈ equatorᶜ ∧
      b ∉ connectedComponentIn equatorᶜ a := by
  -- Jordan separation says the complement subtype is not preconnected.
  have complement_not_preconnected : ¬ PreconnectedSpace (equatorᶜ : Set (StandardSphere 2)) :=
    Set.separates_iff.mp (jordanSeparation equator)
  rw [preconnectedSpace_iff_connectedComponent] at complement_not_preconnected
  push Not at complement_not_preconnected
  obtain ⟨a, component_ne_univ⟩ := complement_not_preconnected
  have exists_outside :
      ∃ b : (equatorᶜ : Set (StandardSphere 2)), b ∉ connectedComponent a := by
    by_contra all_inside
    push Not at all_inside
    apply component_ne_univ
    ext b
    simp only [mem_univ, iff_true]
    exact all_inside b
  obtain ⟨b, hb⟩ := exists_outside
  refine ⟨a, b, a.property, b.property, ?_⟩
  rw [connectedComponentIn_eq_image a.property]
  rintro ⟨w, hw, hwb⟩
  have w_eq_b : w = b := Subtype.ext hwb
  exact hb (w_eq_b ▸ hw)

/-- Helper for Exercise 62.1: the interval trace of the equator has exactly the equator as range. -/
private lemma intervalEquator_range :
    Set.range (fun t : unitInterval ↦ equatorEmbedding (intervalCircleMap t)) = equator := by
  -- Surjectivity of the circle parametrization identifies the two ranges.
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    exact ⟨intervalCircleMap t, rfl⟩
  · rintro x ⟨z, rfl⟩
    obtain ⟨t, ht⟩ := intervalCircleMap_surjective z
    exact ⟨t, congrArg equatorEmbedding ht⟩

/-- Exercise 62.1. There is a nullhomotopic noninjective map from the unit interval
into a twice-punctured standard 2-sphere whose image separates the omitted points. -/
theorem borsukLemmaCounterexample :
    ∃ (a b : StandardSphere 2)
      (f : C(unitInterval, ({a, b}ᶜ : Set (StandardSphere 2)))),
      a ≠ b ∧ ¬ Function.Injective f ∧ f.Nullhomotopic ∧
        b ∉ connectedComponentIn
          (Set.range (fun x : unitInterval ↦ (f x : StandardSphere 2)))ᶜ a := by
  -- Choose points in different complementary components of the equator.
  obtain ⟨a, b, ha, hb, hab⟩ := exists_points_separated_by_equator
  have map_mem : ∀ t : unitInterval,
      equatorEmbedding (intervalCircleMap t) ∈ ({a, b}ᶜ : Set (StandardSphere 2)) := by
    intro t
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · intro h
      exact ha ⟨intervalCircleMap t, h⟩
    · intro h
      exact hb ⟨intervalCircleMap t, h⟩
  let f : C(unitInterval, ({a, b}ᶜ : Set (StandardSphere 2))) :=
    ⟨fun t ↦ ⟨equatorEmbedding (intervalCircleMap t), map_mem t⟩,
      (equatorEmbedding_continuous.comp intervalCircleMap.continuous).subtype_mk _⟩
  refine ⟨a, b, f, ?_, ?_, ?_, ?_⟩
  · -- Distinct components force the two omitted points to be distinct.
    intro h
    exact hab (h ▸ mem_connectedComponentIn ha)
  · -- Injectivity of `f` would imply injectivity of the endpoint-identifying circle map.
    intro hf
    apply intervalCircleMap_not_injective
    intro x y hxy
    apply hf
    exact Subtype.ext (congrArg equatorEmbedding hxy)
  · -- Contractibility of the interval nullhomotopes every map out of it.
    simpa only [ContinuousMap.comp_id] using (id_nullhomotopic unitInterval).comp_right f
  · -- Forgetting the punctured codomain leaves exactly the separating equator.
    rw [show Set.range (fun x : unitInterval ↦ (f x : StandardSphere 2)) = equator by
      exact intervalEquator_range]
    exact hab
