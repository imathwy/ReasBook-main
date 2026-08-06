import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Definition_16_1_1
import Mathlib.Data.Fin.Tuple.Basic

-- `stdSimplex.map` is the canonical simplex-level map, while `Definition_16_1_1` fixes the
-- source-facing owner `Δ^n`.

/-- The `i`-th face map on standard simplices is the map
`Δ^n → Δ^(n + 1)` induced by `Fin.succAbove i`. -/
noncomputable abbrev standardSimplexFaceMap (n : ℕ) (i : Fin (n + 2)) :
    Δ^n → Δ^(n + 1) :=
  stdSimplex.map i.succAbove

@[continuity]
theorem continuous_standardSimplexFaceMap (n : ℕ) (i : Fin (n + 2)) :
    Continuous (standardSimplexFaceMap n i) := by
  simpa [standardSimplexFaceMap] using (stdSimplex.continuous_map i.succAbove)

/-- Definition 16.1.2 (1): the `i`-th face map inserts a zero coordinate. -/
@[simp]
theorem standardSimplexFaceMap_apply (n : ℕ) (i : Fin (n + 2)) (x : Δ^n)
    (j : Fin (n + 2)) :
    standardSimplexFaceMap n i x j = (i.insertNth 0 x : Fin (n + 2) → ℝ) j := by
  classical
  -- Rewrite the simplex map coordinate as the fiber sum of `i.succAbove`.
  rw [standardSimplexFaceMap, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  -- The missing coordinate has empty fiber, and every other coordinate has a singleton fiber.
  induction j using i.succAboveCases with
  | x =>
      simp [Fin.insertNth_apply_same, Fin.succAbove_ne]
  | p j =>
      rw [Fin.insertNth_apply_succAbove]
      refine Finset.sum_eq_single_of_mem j ?_ ?_
      · simp
      · intro b hb hbne
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        exact False.elim (hbne (Fin.succAbove_right_injective hb))

/-- The `i`-th degeneracy map on standard simplices is the map
`Δ^(n + 1) → Δ^n` induced by `Fin.predAbove i`. -/
noncomputable abbrev standardSimplexDegeneracyMap (n : ℕ) (i : Fin (n + 1)) :
    Δ^(n + 1) → Δ^n :=
  stdSimplex.map i.predAbove

@[continuity]
theorem continuous_standardSimplexDegeneracyMap (n : ℕ) (i : Fin (n + 1)) :
    Continuous (standardSimplexDegeneracyMap n i) := by
  simpa [standardSimplexDegeneracyMap] using (stdSimplex.continuous_map i.predAbove)

/-- Definition 16.1.2 (2): the `i`-th degeneracy map contracts the `i`-th and `(i + 1)`-st
coordinates by addition. -/
@[simp]
theorem standardSimplexDegeneracyMap_apply (n : ℕ) (i : Fin (n + 1))
    (x : Δ^(n + 1)) (j : Fin (n + 1)) :
    standardSimplexDegeneracyMap n i x j = Fin.contractNth i.castSucc (· + ·) x j := by
  classical
  -- Rewrite the simplex map coordinate as the fiber sum of `i.predAbove`.
  rw [standardSimplexDegeneracyMap, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  -- Split according to whether the fiber is a singleton below `i`, a doubleton at `i`,
  -- or a singleton above `i`.
  by_cases hlt : (j : ℕ) < i
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ hlt]
    have hfiber :
        Finset.univ.filter (fun k : Fin (n + 2) => i.predAbove k = j) =
          ({j.castSucc} : Finset (Fin (n + 2))) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hb
        by_cases hbi : b = i.castSucc
        · subst hbi
          rw [Fin.predAbove_castSucc_self] at hb
          exact False.elim ((Fin.ne_of_lt hlt) hb.symm)
        · have hb' : b = i.castSucc.succAbove j := by
            simpa [hb] using (Fin.succAbove_predAbove (p := i) (i := b) hbi).symm
          simpa [Fin.succAbove_castSucc_of_lt _ _ hlt] using hb'
      · rintro rfl
        rw [Fin.predAbove_castSucc_of_le _ _ (Fin.le_of_lt hlt)]
    rw [hfiber]
    simp
  · by_cases heq : (j : ℕ) = i
    · have hj : j = i := Fin.ext heq
      subst j
      rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl]
      have hfiber :
          Finset.univ.filter (fun k : Fin (n + 2) => i.predAbove k = i) =
            insert i.castSucc ({i.succ} : Finset (Fin (n + 2))) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · intro hb
          by_cases hbi : b = i.castSucc
          · exact Or.inl hbi
          · right
            have hb' : b = i.castSucc.succAbove i := by
              simpa [hb] using (Fin.succAbove_predAbove (p := i) (i := b) hbi).symm
            simpa using hb'
        · rintro (rfl | rfl)
          · rw [Fin.predAbove_castSucc_self]
          · rw [Fin.predAbove_succ_self]
      rw [hfiber, Finset.sum_insert]
      · simp
      · simpa using (Fin.ne_of_lt i.castSucc_lt_succ)
    · have hle : (i : ℕ) ≤ j := Nat.le_of_not_gt hlt
      have hne : (i : ℕ) ≠ j := by simpa [eq_comm] using heq
      have hgt : (i : ℕ) < j := lt_of_le_of_ne hle hne
      rw [Fin.contractNth_apply_of_gt _ _ _ _ hgt]
      have hfiber :
          Finset.univ.filter (fun k : Fin (n + 2) => i.predAbove k = j) =
            ({j.succ} : Finset (Fin (n + 2))) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hb
          by_cases hbi : b = i.castSucc
          · subst hbi
            rw [Fin.predAbove_castSucc_self] at hb
            have : (i : ℕ) = j := by simpa using congrArg Fin.val hb
            exact False.elim (hne this)
          · have hb' : b = i.castSucc.succAbove j := by
              simpa [hb] using (Fin.succAbove_predAbove (p := i) (i := b) hbi).symm
            simpa [Fin.succAbove_castSucc_of_le _ _ (Fin.le_of_lt hgt)] using hb'
        · rintro rfl
          rw [Fin.predAbove_succ_of_le _ _ (Fin.le_of_lt hgt)]
      rw [hfiber]
      simp
