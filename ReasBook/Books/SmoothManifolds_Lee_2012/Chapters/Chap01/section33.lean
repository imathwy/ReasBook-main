import Mathlib.Geometry.Manifold.Diffeomorph

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_1_33 (from Chap01/Sec01_04) -/
noncomputable section

open scoped Manifold ContDiff

-- Local API note: `lean_leansearch` was unavailable in this session, so this file follows the
-- existing repository API for `RealProjectiveSpace` and its standard affine charts from
-- `Example_1_5`.

/-- The canonical transition between the `i`th and `j`th standard affine charts on `ℝPⁿ`, viewed
as an open partial homeomorphism of `ℝⁿ`. -/
def realProjectiveChartTransitionPartialHomeomorph (n : ℕ) (i j : Fin (n + 1)) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
  (realProjectiveChart n i).symm.trans (realProjectiveChart n j)

/-- The subset `φ_i (U_i ∩ U_j)` of `ℝⁿ`, expressed as the set of affine coordinates whose
`i`-chart inverse lies in the `j`th standard projective chart domain. -/
def realProjectiveChartOverlap (n : ℕ) (i j : Fin (n + 1)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  (realProjectiveChartTransitionPartialHomeomorph n i j).source

/-- Helper for Example 1.33: inserting `1` into the `i`th homogeneous coordinate really fixes
that coordinate. -/
@[simp] theorem realProjectiveChartInvVector_apply_self (n : ℕ) (i : Fin (n + 1))
    (u : EuclideanSpace ℝ (Fin n)) :
    realProjectiveChartInvVector n i u i = 1 := by
  -- The distinguished coordinate is exactly the inserted value.
  simp [realProjectiveChartInvVector]

/-- Helper for Example 1.33: away from the distinguished slot, the inserted homogeneous vector
recovers the original affine coordinates. -/
@[simp] theorem realProjectiveChartInvVector_apply_succAbove (n : ℕ) (i : Fin (n + 1))
    (u : EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    realProjectiveChartInvVector n i u (i.succAbove k) = u k := by
  -- Every non-distinguished homogeneous coordinate comes from the corresponding affine one.
  simp [realProjectiveChartInvVector]

/-- Helper for Example 1.33: each homogeneous coordinate of the inserted vector is a smooth affine
function of the chart coordinates. -/
theorem realProjectiveChartInvVector_coordinate_contDiff (n : ℕ) (i : Fin (n + 1))
    (l : Fin (n + 1)) :
    ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin n) ↦ realProjectiveChartInvVector n i u l) := by
  by_cases h : l = i
  · subst h
    -- The distinguished coordinate is the constant function `1`.
    simpa using
      (contDiff_const :
        ContDiff ℝ (⊤ : WithTop ℕ∞) (fun _ : EuclideanSpace ℝ (Fin n) ↦ (1 : ℝ)))
  · rcases Fin.exists_succAbove_eq h with ⟨k, rfl⟩
    -- Every other coordinate is just one ambient affine coordinate projection.
    simpa using
      (contDiff_piLp_apply (p := (2 : ENNReal)) (i := k) :
        ContDiff ℝ (⊤ : WithTop ℕ∞) (fun u : EuclideanSpace ℝ (Fin n) ↦ u k))

/-- Membership in the overlap `φ_i (U_i ∩ U_j)` is equivalent to the nonvanishing of the `j`th
homogeneous coordinate of the vector obtained by inserting `1` in the `i`th slot. -/
theorem mem_realProjectiveChartOverlap_iff (n : ℕ) (i j : Fin (n + 1))
    (u : EuclideanSpace ℝ (Fin n)) :
    u ∈ realProjectiveChartOverlap n i j ↔ realProjectiveChartInvVector n i u j ≠ 0 := by
  have hmem :
      (realProjectiveChart n i).symm u ∈ realProjectiveChartDomain n j ↔
        realProjectiveChartInvVector n i u j ≠ 0 := by
    -- The inverse chart is represented by the vector with `1` inserted in the `i`th slot.
    rw [realProjectiveChart_symm_apply]
    simpa using
      (realProjectiveChartDomain_mk n j (realProjectiveChartInvVector n i u)
        (realProjectiveChartInvVector_ne_zero n i u))
  -- The transition source is the locus where the inverse of the `i`th chart lands in `U_j`.
  rw [realProjectiveChartOverlap, realProjectiveChartTransitionPartialHomeomorph,
    OpenPartialHomeomorph.trans_source]
  -- The target of the `i`th chart is all of `ℝⁿ`, so only the domain condition remains.
  simpa [realProjectiveChart] using hmem

/-- The overlap `φ_i (U_i ∩ U_j)` is open in `ℝⁿ`. -/
theorem realProjectiveChartOverlap_isOpen (n : ℕ) (i j : Fin (n + 1)) :
    IsOpen (realProjectiveChartOverlap n i j) := by
  simpa [realProjectiveChartOverlap] using
    (realProjectiveChartTransitionPartialHomeomorph n i j).open_source

/-- The target of the `i`-to-`j` chart transition is the reverse overlap `φ_j (U_i ∩ U_j)`. -/
theorem realProjectiveChartTransition_target_eq_overlap (n : ℕ) (i j : Fin (n + 1)) :
    (realProjectiveChartTransitionPartialHomeomorph n i j).target =
      realProjectiveChartOverlap n j i := by
  ext u
  have hmem :
      (realProjectiveChart n j).symm u ∈ realProjectiveChartDomain n i ↔
        u ∈ realProjectiveChartOverlap n j i := by
    -- Reversing the indices gives the same nonvanishing denominator criterion.
    rw [mem_realProjectiveChartOverlap_iff n j i u, realProjectiveChart_symm_apply]
    simpa using
      (realProjectiveChartDomain_mk n i (realProjectiveChartInvVector n j u)
        (realProjectiveChartInvVector_ne_zero n j u))
  -- The transition target is the locus where the inverse of the `j`th chart lands back in `U_i`.
  rw [realProjectiveChartOverlap, realProjectiveChartTransitionPartialHomeomorph,
    OpenPartialHomeomorph.trans_target]
  -- Again, the chart target is all of `ℝⁿ`, so this reduces to the reverse overlap condition.
  simpa [realProjectiveChart] using hmem

/-- The overlap `φ_i (U_i ∩ U_j)` viewed as an open subset of `ℝⁿ`. -/
def realProjectiveChartOverlapOpens (n : ℕ) (i j : Fin (n + 1)) :
    TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) :=
  ⟨realProjectiveChartOverlap n i j, realProjectiveChartOverlap_isOpen n i j⟩

/-- On the overlap `φ_i (U_i ∩ U_j)`, the restricted chart transition is given by the explicit
homogeneous-coordinate formula obtained by inserting `1` in the `i`th slot and dividing by the
`j`th homogeneous coordinate. -/
theorem realProjectiveChartTransitionPartialHomeomorph_apply (n : ℕ) (i j : Fin (n + 1))
    (u : realProjectiveChartOverlapOpens n i j) :
    realProjectiveChartTransitionPartialHomeomorph n i j u =
      WithLp.toLp 2 fun k ↦
        realProjectiveChartInvVector n i u (j.succAbove k) /
          realProjectiveChartInvVector n i u j := by
  rw [realProjectiveChartTransitionPartialHomeomorph, OpenPartialHomeomorph.trans_apply,
    realProjectiveChart_symm_apply, realProjectiveChart_mk]

/-- Example 1.33 (1): on `φ_i (U_i ∩ U_j)`, the transition map `φ_j ∘ φ_i⁻¹` is given by the
explicit homogeneous-coordinate formula obtained by inserting `1` in the `i`th slot and dividing
by the `j`th homogeneous coordinate. -/
theorem realProjectiveChart_transition_formula (n : ℕ) (i j : Fin (n + 1))
    (u : realProjectiveChartOverlapOpens n i j) :
    realProjectiveChartTransitionPartialHomeomorph n i j u =
      WithLp.toLp 2 fun k ↦
        realProjectiveChartInvVector n i u (j.succAbove k) / realProjectiveChartInvVector n i u j :=
  realProjectiveChartTransitionPartialHomeomorph_apply n i j u

/-- The chart transition as a homeomorphism between the two overlap opens. -/
def realProjectiveChartTransitionHomeomorph (n : ℕ) (i j : Fin (n + 1)) :
    realProjectiveChartOverlapOpens n i j ≃ₜ realProjectiveChartOverlapOpens n j i :=
  (realProjectiveChartTransitionPartialHomeomorph n i j).toHomeomorphSourceTarget.trans
    (Homeomorph.setCongr (realProjectiveChartTransition_target_eq_overlap n i j))

/-- Helper for Example 1.33: the explicit chart transition formula is smooth on the overlap
`φ_i (U_i ∩ U_j)`. -/
theorem realProjectiveChartTransition_contDiffOn (n : ℕ) (i j : Fin (n + 1)) :
    ContDiffOn ℝ (⊤ : WithTop ℕ∞) (realProjectiveChartTransitionPartialHomeomorph n i j)
      (realProjectiveChartOverlap n i j) := by
  let F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun u ↦
    WithLp.toLp 2 fun k ↦
      realProjectiveChartInvVector n i u (j.succAbove k) /
        realProjectiveChartInvVector n i u j
  have hF : ContDiffOn ℝ (⊤ : WithTop ℕ∞) F (realProjectiveChartOverlap n i j) := by
    -- The explicit formula is smooth once each coordinate quotient is smooth.
    refine contDiffOn_piLp' (p := (2 : ENNReal)) ?_
    intro k
    -- Each numerator and the common denominator are smooth affine coordinates.
    refine (realProjectiveChartInvVector_coordinate_contDiff n i (j.succAbove k)).contDiffOn.div
      (realProjectiveChartInvVector_coordinate_contDiff n i j).contDiffOn ?_
    intro u hu
    -- On the overlap, the denominator is precisely the nonvanishing homogeneous coordinate.
    exact (mem_realProjectiveChartOverlap_iff n i j u).1 hu
  have hEq :
      ∀ u ∈ realProjectiveChartOverlap n i j,
        realProjectiveChartTransitionPartialHomeomorph n i j u = F u := by
    intro u hu
    -- On the source overlap, the partial homeomorphism agrees with the explicit formula.
    simpa [F] using
      realProjectiveChartTransitionPartialHomeomorph_apply n i j
        (u := ⟨u, hu⟩)
  -- Replace the transition map by the explicit coordinate formula on its source.
  exact hF.congr hEq

/-- The transition map between the `i`th and `j`th projective affine charts is smooth on the
overlap open subset `φ_i (U_i ∩ U_j)`. -/
theorem realProjectiveChartTransition_contMDiff (n : ℕ) (i j : Fin (n + 1)) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (realProjectiveChartTransitionHomeomorph n i j) := by
  intro x
  refine (ContMDiffAt.subtypeVal_comp_iff
    (realProjectiveChartOverlapOpens n j i)
    (realProjectiveChartTransitionHomeomorph n i j) x).1 ?_
  have hVal :
      Subtype.val ∘ realProjectiveChartTransitionHomeomorph n i j =
        fun u : realProjectiveChartOverlapOpens n i j ↦
          realProjectiveChartTransitionPartialHomeomorph n i j u := by
    funext u
    -- The homeomorphism between overlap opens is the same ambient transition map with codomain
    -- restricted to the reverse overlap.
    cases u
    rfl
  rw [hVal]
  refine (contMDiffAt_subtype_iff
    (U := realProjectiveChartOverlapOpens n i j)
    (f := realProjectiveChartTransitionPartialHomeomorph n i j)
    (x := x)).2 ?_
  have hcont :
      ContDiffAt ℝ (⊤ : WithTop ℕ∞) (realProjectiveChartTransitionPartialHomeomorph n i j) x := by
    -- On an open overlap, ambient Euclidean smoothness upgrades to `ContDiffAt`.
    exact (realProjectiveChartTransition_contDiffOn n i j).contDiffAt
      ((realProjectiveChartOverlap_isOpen n i j).mem_nhds x.2)
  -- The Euclidean and manifold notions of smoothness agree for the standard model `𝓡 n`.
  simpa using (hcont.contMDiffAt.of_le (by simp))

/-- Helper for Example 1.33: the inverse restricted chart transition is smooth on the reverse
overlap open subset. -/
theorem realProjectiveChartTransition_symm_contMDiff (n : ℕ) (i j : Fin (n + 1)) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (realProjectiveChartTransitionHomeomorph n i j).symm := by
  intro y
  refine (ContMDiffAt.subtypeVal_comp_iff
    (realProjectiveChartOverlapOpens n i j)
    (realProjectiveChartTransitionHomeomorph n i j).symm y).1 ?_
  have hVal :
      Subtype.val ∘ (realProjectiveChartTransitionHomeomorph n i j).symm =
        fun u : realProjectiveChartOverlapOpens n j i ↦
          (realProjectiveChartTransitionPartialHomeomorph n i j).symm u := by
    funext u
    -- The inverse homeomorphism is the same ambient inverse transition with source restricted to
    -- the reverse overlap.
    cases u
    rfl
  rw [hVal]
  refine (contMDiffAt_subtype_iff
    (U := realProjectiveChartOverlapOpens n j i)
    (f := (realProjectiveChartTransitionPartialHomeomorph n i j).symm)
    (x := y)).2 ?_
  have hcontOn :
      ContDiffOn ℝ (⊤ : WithTop ℕ∞) ((realProjectiveChartTransitionPartialHomeomorph n i j).symm)
        (realProjectiveChartTransitionPartialHomeomorph n i j).target := by
    -- Reversing the indices identifies the inverse transition with the forward transition `j → i`.
    simpa [realProjectiveChartTransitionPartialHomeomorph,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      realProjectiveChartTransition_target_eq_overlap] using
      realProjectiveChartTransition_contDiffOn n j i
  have hy :
      y.1 ∈ (realProjectiveChartTransitionPartialHomeomorph n i j).target := by
    simpa [realProjectiveChartTransition_target_eq_overlap] using y.2
  have hcont :
      ContDiffAt ℝ (⊤ : WithTop ℕ∞) ((realProjectiveChartTransitionPartialHomeomorph n i j).symm)
        y := by
    -- The target of the forward transition is open, so the inverse is smooth at each target point.
    exact hcontOn.contDiffAt
      ((realProjectiveChartTransitionPartialHomeomorph n i j).open_target.mem_nhds hy)
  -- Again, ambient Euclidean smoothness is the same as manifold smoothness for `𝓡 n`.
  simpa using (hcont.contMDiffAt.of_le (by simp))

/-- Example 1.33 (2): for any indices `i` and `j`, the transition map between the standard affine
charts on `ℝPⁿ` is a diffeomorphism from `φ_i (U_i ∩ U_j)` to `φ_j (U_i ∩ U_j)`. -/
def realProjectiveChartTransitionDiffeomorph (n : ℕ) (i j : Fin (n + 1)) :
    Diffeomorph (𝓡 n) (𝓡 n)
      (realProjectiveChartOverlapOpens n i j)
      (realProjectiveChartOverlapOpens n j i)
      ∞ where
  toEquiv := (realProjectiveChartTransitionHomeomorph n i j).toEquiv
  contMDiff_toFun := realProjectiveChartTransition_contMDiff n i j
  contMDiff_invFun := realProjectiveChartTransition_symm_contMDiff n i j

private def realProjectiveChartAtlas (n : ℕ) :
    Set (OpenPartialHomeomorph (ℝP[n]) (EuclideanSpace ℝ (Fin n))) :=
  { e | ∃ i : Fin (n + 1), e = realProjectiveChart n i }

private noncomputable def realProjectiveChartAt (n : ℕ) (x : ℝP[n]) :
    OpenPartialHomeomorph (ℝP[n]) (EuclideanSpace ℝ (Fin n)) :=
  let i := Classical.choose (real_projective_space_has_standard_chart n x)
  realProjectiveChart n i

private theorem mem_realProjectiveChartAt_source (n : ℕ) (x : ℝP[n]) :
    x ∈ (realProjectiveChartAt n x).source := by
  let hx := Classical.choose_spec (real_projective_space_has_standard_chart n x)
  simpa [realProjectiveChartAt] using hx

private theorem realProjectiveChartAt_mem_atlas (n : ℕ) (x : ℝP[n]) :
    realProjectiveChartAt n x ∈ realProjectiveChartAtlas n := by
  refine ⟨Classical.choose (real_projective_space_has_standard_chart n x), ?_⟩
  simp [realProjectiveChartAt]

/-- The standard affine charts make `ℝPⁿ` into a charted space modelled on `ℝⁿ`. -/
instance realProjectiveSpaceChartedSpace (n : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℝP[n]) where
  atlas := realProjectiveChartAtlas n
  chartAt := realProjectiveChartAt n
  mem_chart_source := mem_realProjectiveChartAt_source n
  chart_mem_atlas := realProjectiveChartAt_mem_atlas n

/-- The standard affine atlas gives `ℝPⁿ` its canonical smooth manifold structure. -/
instance realProjectiveSpaceIsManifold (n : ℕ) :
    IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) (ℝP[n]) := by
  -- The standard affine atlas is smooth because every chart transition is smooth on its overlap.
  apply isManifold_of_contDiffOn
  intro e e' he he'
  change e ∈ realProjectiveChartAtlas n at he
  change e' ∈ realProjectiveChartAtlas n at he'
  simp only [realProjectiveChartAtlas] at he he'
  rcases he with ⟨i, rfl⟩
  rcases he' with ⟨j, rfl⟩
  -- For standard projective charts, the compatibility map is exactly the explicit transition.
  simp only [mfld_simps]
  exact realProjectiveChartTransition_contDiffOn n i j
