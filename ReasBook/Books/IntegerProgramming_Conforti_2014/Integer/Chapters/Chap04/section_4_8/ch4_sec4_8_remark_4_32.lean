import Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_3
import Integer.Chapters.Chap04.section_4_12.ch4_sec4_12_exercise_4_30
import Integer.Chapters.Chap03.section_3_5.ch3_sec3_5_definition_3_5_extra_1

open scoped Matrix

-- Semantic recall note: the mixed-space owner API for rational mixed polyhedra and mixed-integer
-- points is already established upstream in Chapter 4.1, and the generic recession-cone owner is
-- reused through Theorem 4.30. This file adds only the real-coefficient/right-hand-side variants
-- needed by the remark.

section Remark432

variable {m n p : ℕ}

/-- The flattened block matrix `[A G]` whose multiplication against `Fin.append x y` recovers the
mixed system `A *ᵥ x + G *ᵥ y`. -/
def mixedConstraintMatrix
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ) :
    Matrix (Fin m) (Fin (n + p)) ℝ :=
  fun i ↦ Fin.addCases (A i) (G i)

/-- Multiplying the flattened block matrix `[A G]` against `Fin.append x y` recovers the mixed
left-hand side `A *ᵥ x + G *ᵥ y`. -/
theorem mixedConstraintMatrix_mulVec_append
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (x : Fin n → ℝ)
    (y : Fin p → ℝ) :
    mixedConstraintMatrix A G *ᵥ Fin.append x y = A *ᵥ x + G *ᵥ y := by
  ext i
  simp [mixedConstraintMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_add]

/-- Helper for Remark 4.32: flattening by `Fin.appendEquiv` is linear on `ℝ^n × ℝ^p`. -/
private lemma isLinearMap_appendEquiv :
    IsLinearMap ℝ (Fin.appendEquiv (α := ℝ) n p) := by
  refine ⟨?_, ?_⟩
  · intro x y
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [Fin.appendEquiv]
    · intro j
      simp [Fin.appendEquiv]
  · intro a x
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [Fin.appendEquiv]
    · intro j
      simp [Fin.appendEquiv]

/-- Helper for Remark 4.32: flattening commutes with convex hull. -/
private lemma appendEquiv_image_convexHull
    (S : Set (MixedRealPoint n p)) :
    Fin.appendEquiv (α := ℝ) n p '' convexHull ℝ S =
      convexHull ℝ (Fin.appendEquiv (α := ℝ) n p '' S) := by
  simpa using (isLinearMap_appendEquiv (n := n) (p := p)).image_convexHull S

/-- A real matrix has rational entries when each coefficient is the real coercion of some
rational number. -/
def matrix_has_rational_entries
    (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ i j, ∃ q : ℚ, A i j = (q : ℝ)

/-- A real vector has rational entries when each coordinate is the real coercion of some rational
number. -/
def vector_has_rational_entries
    (b : Fin m → ℝ) : Prop :=
  ∀ i, ∃ q : ℚ, b i = (q : ℝ)

/-- The mixed polyhedron
`{(x, y) : ℝ^n × ℝ^p | A x + G y ≤ b}` attached to real data `A`, `G`, and `b`, viewed as the
pullback of the canonical Chapter 3 polyhedron owner along `Fin.appendEquiv`. -/
def real_mixed_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ) :
    Set (MixedRealPoint n p) :=
  (Fin.appendEquiv n p).symm '' polyhedron_le_set (mixedConstraintMatrix A G) b

/-- Membership in `real_mixed_polyhedron A G b` is exactly the mixed system
`A x + G y ≤ b`. -/
theorem mem_real_mixed_polyhedron_iff
    {A : Matrix (Fin m) (Fin n) ℝ}
    {G : Matrix (Fin m) (Fin p) ℝ}
    {b : Fin m → ℝ}
    {xy : MixedRealPoint n p} :
    xy ∈ real_mixed_polyhedron A G b ↔ A *ᵥ xy.1 + G *ᵥ xy.2 ≤ b := by
  rw [real_mixed_polyhedron, Equiv.image_eq_preimage_symm]
  change (mixedConstraintMatrix A G) *ᵥ (Fin.append xy.1 xy.2) ≤ b ↔
    A *ᵥ xy.1 + G *ᵥ xy.2 ≤ b
  rw [mixedConstraintMatrix_mulVec_append]

/-- Source-facing bridge/view: a subset of `ℝ^n × ℝ^p` is a mixed polyhedron when its canonical
flattening in `ℝ^(n + p)` is a polyhedron. -/
def is_mixed_polyhedron
    (P : Set (MixedRealPoint n p)) : Prop :=
  is_polyhedron ((Fin.appendEquiv n p) '' P)

/-- The mixed polyhedron cut out by rational matrices `A`, `G` and a real right-hand side `b`. -/
def rational_matrices_real_rhs_mixed_polyhedron
    (A : Matrix (Fin m) (Fin n) ℚ)
    (G : Matrix (Fin m) (Fin p) ℚ)
    (b : Fin m → ℝ) :
    Set (MixedRealPoint n p) :=
  real_mixed_polyhedron (A.map (Rat.castHom ℝ)) (G.map (Rat.castHom ℝ)) b

/-- Helper for Remark 4.32: the mixed point of `ℝ^0 × ℝ^1` whose unique real coordinate is
`√2`. -/
private noncomputable def sqrtTwoMixedPoint : MixedRealPoint 0 1 :=
  (fun i ↦ Fin.elim0 i, ![Real.sqrt 2])

/-- Helper for Remark 4.32: the singleton `{sqrtTwoMixedPoint}` is not a rational mixed
polyhedron. -/
private lemma sqrtTwoMixedPoint_not_rationalMixedPolyhedron :
    ¬ is_rational_mixed_polyhedron ({sqrtTwoMixedPoint} : Set (MixedRealPoint 0 1)) := by
  let x : Fin 1 → ℝ := ![Real.sqrt 2]
  intro hRational
  have hFlat :
      (Fin.appendEquiv 0 1 '' ({sqrtTwoMixedPoint} : Set (MixedRealPoint 0 1))) =
        ({x} : Set (Fin 1 → ℝ)) := by
    -- Flattening the singleton keeps only its unique real coordinate.
    ext u
    simp [sqrtTwoMixedPoint, x, Fin.appendEquiv]
  have hFlatRational : is_rational_polyhedron ({x} : Set (Fin 1 → ℝ)) := by
    -- Rewrite the mixed singleton through its flattened `Fin 1` presentation.
    simpa [is_rational_mixed_polyhedron, hFlat] using hRational
  rcases hFlatRational with ⟨m, A, b, hAb⟩
  have hx_mem : x ∈ polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) := by
    rw [← hAb]
    simp
  have hx_row :
      ∀ i : Fin m, (A i 0 : ℝ) * Real.sqrt 2 ≤ b i := by
    intro i
    have hxi := hx_mem i
    simpa [x, rational_matrix_polyhedron, Matrix.mulVec, dotProduct] using hxi
  let posRows : Finset (Fin m) := Finset.univ.filter fun i : Fin m ↦ 0 < A i 0
  have hpos_nonempty : posRows.Nonempty := by
    by_contra hpos_empty
    have hA_nonpos : ∀ i : Fin m, (A i 0 : ℝ) ≤ 0 := by
      intro i
      have hi_not_pos : ¬ 0 < A i 0 := by
        intro hi_pos
        exact hpos_empty ⟨i, Finset.mem_filter.2 ⟨by simp, hi_pos⟩⟩
      exact_mod_cast le_of_not_gt hi_not_pos
    let xPlus : Fin 1 → ℝ := ![Real.sqrt 2 + 1]
    have hxPlus_mem : xPlus ∈ polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) := by
      intro i
      have hi := hx_row i
      have hAi_nonpos := hA_nonpos i
      simpa [xPlus, rational_matrix_polyhedron, Matrix.mulVec, dotProduct] using
        (by linarith : (A i 0 : ℝ) * (Real.sqrt 2 + 1) ≤ b i)
    rw [← hAb] at hxPlus_mem
    have hxPlus_eq : xPlus = x := Set.mem_singleton_iff.1 hxPlus_mem
    have hcoord := congrFun hxPlus_eq 0
    norm_num [xPlus, x] at hcoord
  have hactive_pos : ∃ i : Fin m, 0 < A i 0 ∧ (A i 0 : ℝ) * Real.sqrt 2 = b i := by
    by_contra hactive
    let δ : Fin m → ℝ := fun i ↦ ((b i : ℝ) - (A i 0 : ℝ) * Real.sqrt 2) / (A i 0 : ℝ)
    let ε : ℝ := (posRows.inf' hpos_nonempty δ) / 2
    have hδ_pos : ∀ i ∈ posRows, 0 < δ i := by
      intro i hi
      have hi_pos : 0 < A i 0 := (Finset.mem_filter.1 hi).2
      have hi_le := hx_row i
      have hi_ne :
          (A i 0 : ℝ) * Real.sqrt 2 ≠ b i := by
        intro hi_eq
        exact hactive ⟨i, hi_pos, hi_eq⟩
      have hi_lt : (A i 0 : ℝ) * Real.sqrt 2 < b i :=
        lt_of_le_of_ne hi_le hi_ne
      have hnum_pos : 0 < (b i : ℝ) - (A i 0 : ℝ) * Real.sqrt 2 := by
        linarith
      have hden_pos : 0 < (A i 0 : ℝ) := by
        exact_mod_cast hi_pos
      dsimp [δ]
      exact div_pos hnum_pos hden_pos
    have hε_pos : 0 < ε := by
      have hInf_pos : 0 < posRows.inf' hpos_nonempty δ := by
        refine (Finset.lt_inf'_iff _).2 ?_
        intro i hi
        exact hδ_pos i hi
      dsimp [ε]
      exact half_pos hInf_pos
    let xPlus : Fin 1 → ℝ := ![Real.sqrt 2 + ε]
    have hxPlus_mem : xPlus ∈ polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) := by
      intro i
      by_cases hi_pos : 0 < A i 0
      · have hi_mem : i ∈ posRows := Finset.mem_filter.2 ⟨by simp, hi_pos⟩
        have hε_le : ε ≤ δ i := by
          dsimp [ε]
          exact
            (half_le_self
              (show 0 ≤ posRows.inf' hpos_nonempty δ from
                le_of_lt ((Finset.lt_inf'_iff _).2 hδ_pos))).trans
              (Finset.inf'_le _ hi_mem)
        have hAi_pos : 0 < (A i 0 : ℝ) := by
          exact_mod_cast hi_pos
        have hi_bound : (A i 0 : ℝ) * ε ≤ (b i : ℝ) - (A i 0 : ℝ) * Real.sqrt 2 := by
          have hδ_eq :
              (A i 0 : ℝ) * δ i = (b i : ℝ) - (A i 0 : ℝ) * Real.sqrt 2 := by
            dsimp [δ]
            field_simp [ne_of_gt hAi_pos]
          have hmul : (A i 0 : ℝ) * ε ≤ (A i 0 : ℝ) * δ i := by
            exact mul_le_mul_of_nonneg_left hε_le hAi_pos.le
          rwa [hδ_eq] at hmul
        simpa [xPlus, rational_matrix_polyhedron, Matrix.mulVec, dotProduct, add_mul] using
          (by linarith [hx_row i, hi_bound] :
            (A i 0 : ℝ) * (Real.sqrt 2 + ε) ≤ b i)
      · have hAi_nonpos : (A i 0 : ℝ) ≤ 0 := by
          exact_mod_cast le_of_not_gt hi_pos
        simpa [xPlus, rational_matrix_polyhedron, Matrix.mulVec, dotProduct, add_mul] using
          (by nlinarith [hx_row i] : (A i 0 : ℝ) * (Real.sqrt 2 + ε) ≤ b i)
    rw [← hAb] at hxPlus_mem
    have hxPlus_eq : xPlus = x := Set.mem_singleton_iff.1 hxPlus_mem
    have hcoord := congrFun hxPlus_eq 0
    have : Real.sqrt 2 + ε = Real.sqrt 2 := by simpa [xPlus, x] using hcoord
    linarith
  rcases hactive_pos with ⟨i, hi_pos, hi_eq⟩
  have hAi_ne : (A i 0 : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast hi_pos)
  have hdiv : Real.sqrt 2 = (b i : ℝ) / (A i 0 : ℝ) := by
    refine (eq_div_iff hAi_ne).2 ?_
    simpa [mul_comm] using hi_eq
  have hx0 : Real.sqrt 2 = ((b i / A i 0 : ℚ) : ℝ) := by
    simpa using hdiv
  exact irrational_sqrt_two.ne_rat (b i / A i 0) hx0

/-- Remark 4.32 (1). If the mixed-system matrices are allowed to have nonrational entries, the
convex hull of the mixed-integer feasible set need not be a polyhedron. -/
theorem exists_nonrational_matrix_counterexample_to_polyhedral_mixed_integer_hull :
    ∃ m n p : ℕ,
      ∃ A : Matrix (Fin m) (Fin n) ℝ,
        ∃ G : Matrix (Fin m) (Fin p) ℝ,
          ∃ b : Fin m → ℝ,
            (¬ matrix_has_rational_entries A ∨ ¬ matrix_has_rational_entries G) ∧
              ¬ is_mixed_polyhedron
                (convexHull ℝ (mixed_integer_points (real_mixed_polyhedron A G b))) := by
  let A : Matrix (Fin 2) (Fin 2) ℝ := !![-Real.sqrt 2, 1; 0, -1]
  let G : Matrix (Fin 2) (Fin 0) ℝ := 0
  let b : Fin 2 → ℝ := ![0, -1]
  refine ⟨2, 2, 0, A, G, b, ?_⟩
  constructor
  · left
    intro hA_rational
    -- The top-left entry is `-√2`, so a rational presentation would force `√2` to be rational.
    rcases hA_rational 0 0 with ⟨q, hq⟩
    have hentry : (-Real.sqrt 2 : ℝ) = q := by
      simpa [A] using hq
    have hsqrt : Real.sqrt 2 = (-q : ℝ) := by
      linarith
    exact irrational_sqrt_two.ne_rat (-q) (by simpa using hsqrt)
  · intro hHullPolyhedron
    have hFlatPoints :
        Fin.appendEquiv 2 0 '' mixed_integer_points (real_mixed_polyhedron A G b) =
          (LinearEquiv.finTwoArrow ℝ ℝ).symm '' exercise_4_30_real_feasible_set := by
      ext z
      constructor
      · rintro ⟨xy, hxy, rfl⟩
        rcases xy with ⟨x, y⟩
        rcases (mem_mixed_integer_points_iff).1 hxy with ⟨hxP, hxInt⟩
        rw [mem_mixed_integer_lattice_iff, mem_integerVectors_iff] at hxInt
        rcases hxInt with ⟨xInt, rfl⟩
        rw [mem_real_mixed_polyhedron_iff] at hxP
        have hupper : ((xInt 1 : ℤ) : ℝ) ≤ Real.sqrt 2 * (xInt 0 : ℝ) := by
          have hrow0 : -Real.sqrt 2 * (xInt 0 : ℝ) + (xInt 1 : ℝ) ≤ 0 := by
            simpa [A, G, b, Matrix.mulVec, dotProduct] using hxP 0
          linarith
        have hone : 1 ≤ xInt 1 := by
          have hrow1 : -((xInt 1 : ℤ) : ℝ) ≤ -1 := by
            simpa [A, G, b, Matrix.mulVec, dotProduct] using hxP 1
          exact_mod_cast (by linarith : (1 : ℝ) ≤ (xInt 1 : ℝ))
        refine ⟨exercise_4_30_real_point (xInt 0, xInt 1), ?_, ?_⟩
        · -- The two defining rows are exactly the Exercise 4.30 feasibility inequalities.
          exact Set.mem_image_of_mem exercise_4_30_real_point ⟨hone, hupper⟩
        · ext i
          fin_cases i
          · rfl
          · rfl
      · rintro ⟨u, hu, rfl⟩
        rcases hu with ⟨xInt, hxInt, rfl⟩
        refine ⟨((LinearEquiv.finTwoArrow ℝ ℝ).symm (exercise_4_30_real_point xInt),
            fun i ↦ Fin.elim0 i), ?_, ?_⟩
        · refine (mem_mixed_integer_points_iff).2 ?_
          constructor
          · rw [mem_real_mixed_polyhedron_iff]
            intro i
            fin_cases i
            · -- The first row is `x₂ ≤ √2 x₁`.
              simpa [A, G, b, exercise_4_30_real_point, Matrix.mulVec, dotProduct, mul_comm]
                using hxInt.2
            · -- The second row is `1 ≤ x₂`.
              have hrow1 : -(xInt.2 : ℝ) ≤ -1 := by
                have hrow1' : (1 : ℝ) ≤ (xInt.2 : ℝ) := by
                  exact_mod_cast hxInt.1
                linarith
              simpa [A, G, b, exercise_4_30_real_point, Matrix.mulVec, dotProduct]
                using hrow1
          · rw [mem_mixed_integer_lattice_iff, mem_integerVectors_iff]
            refine ⟨![xInt.1, xInt.2], ?_⟩
            ext i
            fin_cases i <;> simp [exercise_4_30_real_point]
        · ext i
          fin_cases i <;> simp [exercise_4_30_real_point, Fin.appendEquiv]
    have hFlatHull :
        (Fin.appendEquiv 2 0 '' convexHull ℝ (mixed_integer_points (real_mixed_polyhedron A G b))) =
          (LinearEquiv.finTwoArrow ℝ ℝ).symm '' convexHull ℝ exercise_4_30_real_feasible_set := by
      calc
        Fin.appendEquiv 2 0 '' convexHull ℝ (mixed_integer_points (real_mixed_polyhedron A G b))
            = convexHull ℝ
                (Fin.appendEquiv 2 0 '' mixed_integer_points (real_mixed_polyhedron A G b)) := by
                  rw [appendEquiv_image_convexHull]
        _ =
            convexHull ℝ
              ((LinearEquiv.finTwoArrow ℝ ℝ).symm '' exercise_4_30_real_feasible_set) := by
              rw [hFlatPoints]
        _ = (LinearEquiv.finTwoArrow ℝ ℝ).symm '' convexHull ℝ exercise_4_30_real_feasible_set := by
              symm
              exact (LinearEquiv.finTwoArrow ℝ ℝ).symm.toLinearMap.image_convexHull
                exercise_4_30_real_feasible_set
    -- Route correction: transport the canonical Exercise 4.30 counterexample through the
    -- `p = 0` flattening equivalence instead of reproving nonpolyhedrality locally.
    exact exercise_4_30_convexHull_real_feasible_set_not_polyhedron <| by
      simpa [is_mixed_polyhedron, hFlatHull] using hHullPolyhedron

/-- Remark 4.32 (2), strengthened using Theorem 4.30 for the rational-right-hand-side case: if
`A` and `G` are rational matrices and `b` is any real right-hand side, then the mixed-integer
hull is still a polyhedron. -/
theorem rational_matrices_real_rhs_mixed_integer_hull_is_polyhedron
    (A : Matrix (Fin m) (Fin n) ℚ)
    (G : Matrix (Fin m) (Fin p) ℚ)
    (b : Fin m → ℝ) :
    is_mixed_polyhedron
      (convexHull ℝ
        (mixed_integer_points (rational_matrices_real_rhs_mixed_polyhedron A G b))) := by
  -- The remaining source-faithful real-right-hand-side decomposition is deferred.
  admit

/-- Remark 4.32 (3), again including the rational-right-hand-side case already covered by
Theorem 4.30: if `A` and `G` are rational matrices and the mixed-integer feasible set is
nonempty, then its mixed-integer hull has the same recession cone as the original mixed
polyhedron. -/
theorem rational_matrices_real_rhs_mixed_integer_hull_recessionCone_eq
    (A : Matrix (Fin m) (Fin n) ℚ)
    (G : Matrix (Fin m) (Fin p) ℚ)
    (b : Fin m → ℝ)
    (hS_nonempty :
      Set.Nonempty (mixed_integer_points (rational_matrices_real_rhs_mixed_polyhedron A G b))) :
    recessionCone
        (convexHull ℝ (mixed_integer_points (rational_matrices_real_rhs_mixed_polyhedron A G b))) =
      recessionCone (rational_matrices_real_rhs_mixed_polyhedron A G b) := by
  -- The remaining source-faithful real-right-hand-side decomposition is deferred.
  admit

/-- Remark 4.32 (4). Even with rational matrices `A` and `G`, a nonrational right-hand side can
yield a mixed-integer hull that is not a rational polyhedron. -/
theorem exists_nonrational_rhs_counterexample_to_rational_mixed_integer_hull :
    ∃ m n p : ℕ,
      ∃ A : Matrix (Fin m) (Fin n) ℚ,
        ∃ G : Matrix (Fin m) (Fin p) ℚ,
          ∃ b : Fin m → ℝ,
            ¬ vector_has_rational_entries b ∧
              ¬ is_rational_mixed_polyhedron
                (convexHull ℝ
                  (mixed_integer_points
                    (rational_matrices_real_rhs_mixed_polyhedron A G b))) := by
  let A : Matrix (Fin 2) (Fin 0) ℚ := 0
  let G : Matrix (Fin 2) (Fin 1) ℚ := !![(1 : ℚ); -1]
  let b : Fin 2 → ℝ := ![Real.sqrt 2, -Real.sqrt 2]
  refine ⟨2, 0, 1, A, G, b, ?_⟩
  constructor
  · intro hb_rational
    rcases hb_rational 0 with ⟨q, hq⟩
    exact irrational_sqrt_two.ne_rat q (by simpa [b] using hq)
  · have hPolyhedronSingleton :
        rational_matrices_real_rhs_mixed_polyhedron A G b = {sqrtTwoMixedPoint} := by
        ext xy
        constructor
        · intro hxy
          rw [rational_matrices_real_rhs_mixed_polyhedron, mem_real_mixed_polyhedron_iff] at hxy
          rcases xy with ⟨x, y⟩
          have hupper : y 0 ≤ Real.sqrt 2 := by
            simpa [A, G, b, Matrix.mulVec, dotProduct] using hxy 0
          have hlower : Real.sqrt 2 ≤ y 0 := by
            have hrow1 : -(y 0) ≤ -Real.sqrt 2 := by
              simpa [A, G, b, Matrix.mulVec, dotProduct] using hxy 1
            linarith
          have hy : y = ![Real.sqrt 2] := by
            ext i
            fin_cases i
            exact le_antisymm hupper hlower
          have hx : x = fun i ↦ Fin.elim0 i := by
            ext i
            exact Fin.elim0 i
          rw [Set.mem_singleton_iff]
          simp [sqrtTwoMixedPoint, hx, hy]
        · rintro rfl
          -- The two rational rows cut out the single coordinate equation `y = √2`.
          rw [rational_matrices_real_rhs_mixed_polyhedron, mem_real_mixed_polyhedron_iff]
          intro i
          fin_cases i <;> simp [A, G, b, sqrtTwoMixedPoint, Matrix.mulVec, dotProduct]
    have hMixedIntegerSingleton :
        mixed_integer_points (rational_matrices_real_rhs_mixed_polyhedron A G b) =
          {sqrtTwoMixedPoint} := by
      ext xy
      rw [mem_mixed_integer_points_iff, hPolyhedronSingleton]
      constructor
      · intro hxy
        exact hxy.1
      · intro hxy
        constructor
        · exact hxy
        · rcases Set.mem_singleton_iff.1 hxy with rfl
          rw [mem_mixed_integer_lattice_iff, mem_integerVectors_iff]
          refine ⟨fun i ↦ Fin.elim0 i, ?_⟩
          ext i
          exact Fin.elim0 i
    have hHullSingleton :
        convexHull ℝ
            (mixed_integer_points (rational_matrices_real_rhs_mixed_polyhedron A G b)) =
          {sqrtTwoMixedPoint} := by
      -- Once the feasible set is already a singleton, taking mixed-integer points and convex hull
      -- does not change it.
      rw [hMixedIntegerSingleton, convexHull_singleton]
    simpa [hHullSingleton] using sqrtTwoMixedPoint_not_rationalMixedPolyhedron

end Remark432
