import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap02.Sec02_10.Lemma_2_21
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap02.Sec02_11.Definition_2_11_extra_3
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap02.Sec02_11.Proposition_2_28
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_30.Definition_5_30_extra_2
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_35.Proposition_5_43
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_36.Definition_5_36_extra_2
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_36.Definition_5_36_extra_3
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_36.Proposition_5_46

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic recall note: `lean_leansearch` returned only partition-of-unity and bump-function
-- separation lemmas, so the source-facing statements here use the local owners
-- `Set.IsRegularDomain`, `IsDefiningFunction`, and `Function.IsExhaustionFunction`.

open scoped ContDiff Manifold

noncomputable section

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I (⊤ : WithTop ℕ∞) M] [BoundarylessManifold I M]

local notation "dimM" => Module.finrank ℝ E

/-- Helper for Theorem 5.48: a regular domain is closed in the ambient manifold because its
subtype inclusion is properly embedded. -/
lemma regularDomain_isClosed
    {D : Set M} [SmoothManifoldWithBoundary dimM D] [Set.IsRegularDomain I D] [T1Space M] :
    IsClosed D := by
  -- The proper-embedding field in `Set.IsRegularDomain` is exactly the closedness owner here.
  exact Set.IsProperlyEmbedded.isClosed (Set.IsRegularDomain.isProperlyEmbedded (I := I) (S := D))

/-- Helper for Theorem 5.48: shifting a defining function by its witnessing regular value produces
an equivalent defining function cut out at level `0`. -/
lemma exists_zeroLevelDefiningFunction
    {D : Set M} {g : M → ℝ} (hg : IsDefiningFunction I D g) :
    ∃ g0 : M → ℝ,
      IsDefiningFunction I D g0 ∧
        D = g0 ⁻¹' Set.Iic 0 ∧
          Manifold.IsRegularValue I 𝓘(ℝ, ℝ) g0 0 := by
  rcases hg.isRegularSublevelSet.exists_regular_value with ⟨b, hb, hD⟩
  let g0 : M → ℝ := fun x ↦ g x - b
  have hg0Smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ g0 := by
    -- Subtracting the scalar regular value keeps the defining function smooth.
    simpa [g0] using hg.contMDiff.sub contMDiff_const
  have hg0Regular : Manifold.IsRegularValue I 𝓘(ℝ, ℝ) g0 0 := by
    intro x hx
    have hxg : g x = b := by
      dsimp [g0] at hx
      linarith
    have hgDiffAt : MDiffAt g x :=
      hg.contMDiff.contMDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
    have hconstDiffAt : MDiffAt (fun _ : M ↦ b) x := mdifferentiableAt_const
    -- The manifold derivative is unchanged by subtracting a constant, so regularity transfers.
    have hmfderiv :
        (mfderiv% g0 x : TangentSpace I x →L[ℝ] ℝ) = mfderiv% g x := by
      change
        (mfderiv% (g - fun _ : M ↦ b) x : TangentSpace I x →L[ℝ] ℝ) = mfderiv% g x
      rw [mfderiv_sub hgDiffAt hconstDiffAt, mfderiv_const]
      exact sub_zero _
    rw [hmfderiv]
    exact hb x hxg
  have hD0 : D = g0 ⁻¹' Set.Iic 0 := by
    -- The shifted closed ray `(-∞, 0]` is exactly the original closed ray `(-∞, b]`.
    rw [hD]
    ext x
    simp [g0]
  refine ⟨g0, ?_, hD0, hg0Regular⟩
  -- Package the shifted function with its new regular sublevel-set witness.
  exact ⟨hg0Smooth, ⟨⟨0, hg0Regular, hD0⟩⟩⟩

/-- Helper for Theorem 5.48: the zero-dimensional boundary model is boundaryless, so a regular
domain of ambient dimension `0` has no manifold boundary points. -/
lemma zeroDimensionalBoundaryModel_not_isBoundaryPoint
    {n : ℕ} {D : Set M} [SmoothManifoldWithBoundary n D] (h0 : n = 0) (x : D) :
    ¬ (leeBoundaryModelWithCorners n).IsBoundaryPoint x := by
  -- Rewrite the abstract dimension parameter to the exact `0`-dimensional owner, where Lee's
  -- boundary model is boundaryless and every point is interior.
  subst n
  have hxInt : (leeBoundaryModelWithCorners 0).IsInteriorPoint x := by
    -- In dimension `0`, Lee's boundary model is the boundaryless Euclidean owner `𝓡 0`.
    simpa [leeBoundaryModelWithCorners] using
      (show (𝓡 0).IsInteriorPoint x from BoundarylessManifold.isInteriorPoint)
  exact ((leeBoundaryModelWithCorners 0).isInteriorPoint_iff_not_isBoundaryPoint x).1 hxInt

/-- Helper for Theorem 5.48: in ambient dimension `0`, a regular domain is clopen, so a smooth
`{0, 1}`-valued separator shifted by `1 / 2` is already a defining function. -/
lemma zeroDimensionalRegularDomain_hasDefiningFunction
    {D : Set M} [SmoothManifoldWithBoundary dimM D] [Set.IsRegularDomain I D]
    [T2Space M] [SigmaCompactSpace M] (h0 : dimM = 0) :
    ∃ f : M → ℝ, IsDefiningFunction I D f := by
  have hDClosed : IsClosed D := regularDomain_isClosed (I := I) (D := D)
  have hFrontierEmpty : frontier D = ∅ := by
    rw [← regular_domain_manifoldBoundary_image_eq_frontier (I := I) (D := D)]
    ext x
    constructor
    · rintro ⟨y, hyBoundary, rfl⟩
      have hyBoundaryPoint : (leeBoundaryModelWithCorners dimM).IsBoundaryPoint y := by
        simpa [ModelWithCorners.boundary] using hyBoundary
      exact False.elim (zeroDimensionalBoundaryModel_not_isBoundaryPoint (D := D) h0 y hyBoundaryPoint)
    · intro hx
      exact False.elim hx
  have hClopen : IsClopen D := (isClopen_iff_frontier_eq_empty).2 hFrontierEmpty
  have hDComplClosed : IsClosed Dᶜ := hClopen.isOpen.isClosed_compl
  obtain ⟨g, hgSmooth, _hgRange, hDZero, hDComplOne⟩ :=
    exists_contMDiff_zero_iff_one_iff_of_isClosed (I := I) hDClosed hDComplClosed
      (by simpa using disjoint_compl_right)
  refine ⟨fun x ↦ g x - (1 / 2 : ℝ), ?_⟩
  have hfSmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x ↦ g x - (1 / 2 : ℝ)) := by
    -- Shifting the separator by a constant preserves smoothness.
    exact hgSmooth.sub contMDiff_const
  have hZeroFiberEmpty : (fun x ↦ g x - (1 / 2 : ℝ)) ⁻¹' ({0} : Set ℝ) = ∅ := by
    ext x
    constructor
    · intro hx
      have hxEq : g x - (1 / 2 : ℝ) = 0 := by
        simpa using hx
      by_cases hxD : x ∈ D
      · have hgx : g x = 0 := (hDZero x).1 hxD
        linarith
      · have hgx : g x = 1 := (hDComplOne x).1 hxD
        linarith
    · intro hx
      exact False.elim hx
  have hfReg :
      Manifold.IsRegularValue I 𝓘(ℝ, ℝ) (fun x ↦ g x - (1 / 2 : ℝ)) 0 := by
    -- The separator takes only the values `-1 / 2` and `1 / 2`, so the zero fiber is empty.
    exact
      Manifold.isRegularValue_of_preimage_eq_empty (I := I) (J := 𝓘(ℝ, ℝ)) hZeroFiberEmpty
  have hDLevel : D = (fun x ↦ g x - (1 / 2 : ℝ)) ⁻¹' Set.Iic 0 := by
    ext x
    constructor
    · intro hxD
      have hgx : g x = 0 := (hDZero x).1 hxD
      simp [hgx]
    · intro hx
      by_cases hxD : x ∈ D
      · exact hxD
      · have hgx : g x = 1 := (hDComplOne x).1 hxD
        have hPos : 0 < g x - (1 / 2 : ℝ) := by
          rw [hgx]
          norm_num
        exact False.elim (not_le_of_gt hPos hx)
  -- Package the shifted separator as a regular sublevel-set witness at level `0`.
  refine (isDefiningFunction_iff (I := I) (D := D) (f := fun x ↦ g x - (1 / 2 : ℝ))).2 ?_
  refine ⟨hfSmooth, ?_⟩
  refine (isRegularSublevelSet_iff (I := I) (f := fun x ↦ g x - (1 / 2 : ℝ)) (D := D)).2 ?_
  exact ⟨0, hfReg, hDLevel⟩

/-- Helper for Theorem 5.48: positive ambient dimension can be rewritten in successor form. -/
lemma dimM_eq_succ_of_ne_zero (h0 : dimM ≠ 0) :
    ∃ n : ℕ, dimM = n + 1 := by
  -- This is the dimension rewrite needed before invoking the boundary owners on `D`.
  simpa [Nat.succ_eq_add_one] using Nat.exists_eq_succ_of_ne_zero h0

/-- Helper for Theorem 5.48: frontier points of a regular domain are exactly the ambient images of
boundary points of the domain's manifold-with-boundary structure. -/
lemma mem_frontier_iff_exists_boundaryPoint
    {D : Set M} [SmoothManifoldWithBoundary dimM D] [Set.IsRegularDomain I D] {x : M} :
    x ∈ frontier D ↔
      ∃ p : D, (leeBoundaryModelWithCorners dimM).IsBoundaryPoint p ∧ p.1 = x := by
  -- Proposition 5.46 identifies the ambient frontier with the subtype image of the boundary.
  rw [← regular_domain_manifoldBoundary_image_eq_frontier (I := I) (D := D)]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p, ?_, rfl⟩
    simpa [ModelWithCorners.boundary] using hp
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p, ?_, rfl⟩
    simpa [ModelWithCorners.boundary] using hp

/-- Helper for Theorem 5.48: once a smooth signed function is available on an open neighborhood of
the frontier, one can splice it with global sign-control terms to obtain a genuine defining
function for the whole regular domain. -/
lemma globalizeFrontierNeighborhoodSignedFunction
    {D : Set M} [SmoothManifoldWithBoundary dimM D] [Set.IsRegularDomain I D]
    [T2Space M] [SigmaCompactSpace M]
    {U : Set M} (hUOpen : IsOpen U) (hFrontierU : frontier D ⊆ U)
    {ρ : M → ℝ} (hρSmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ)
    (hρSign : ∀ y ∈ U, y ∈ D ↔ ρ y ≤ 0)
    (hρZero : ∀ y ∈ U, y ∈ frontier D ↔ ρ y = 0)
    (hρRegular : ∀ y ∈ U, ρ y = 0 → Function.Surjective (mfderiv I 𝓘(ℝ, ℝ) ρ y)) :
    ∃ f : M → ℝ, IsDefiningFunction I D f := by
  letI : LocallyCompactSpace H := I.locallyCompactSpace
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  letI : ParacompactSpace M := paracompact_of_locallyCompact_sigmaCompact
  letI : T4Space M := T4Space.of_paracompactSpace_t2Space
  have hDClosed : IsClosed D := regularDomain_isClosed (I := I) (D := D)
  have hFrontierClosed : IsClosed (frontier D) := isClosed_frontier
  obtain ⟨U₀, hU₀Open, hFrontierU₀, hClosureU₀⟩ :=
    normal_exists_closure_subset hFrontierClosed hUOpen hFrontierU
  have hU₀SubsetU : U₀ ⊆ U := fun x hx ↦ hClosureU₀ (subset_closure hx)
  rcases exists_contMDiffMap_one_nhds_of_subset_interior (I := I)
      (n := (⊤ : ℕ∞)) hFrontierClosed
      (show frontier D ⊆ interior U₀ by simpa [hU₀Open.interior_eq] using hFrontierU₀) with
    ⟨χ, hχOne, hχZero, hχRange⟩
  obtain ⟨N, hNOpen, hFrontierN, hNχ⟩ := mem_nhdsSet_iff_exists.mp hχOne
  have hNSubsetU₀ : N ⊆ U₀ := by
    intro x hxN
    by_contra hxU₀
    have hχx : χ x = 0 := hχZero x hxU₀
    have : (0 : ℝ) = 1 := by simpa [hχx] using hNχ hxN
    exact zero_ne_one this
  have hNSubsetU : N ⊆ U := fun x hxN ↦ hU₀SubsetU (hNSubsetU₀ hxN)
  have hDdiffNClosed : IsClosed (D \ N) := by
    simpa [Set.diff_eq] using hDClosed.inter hNOpen.isClosed_compl
  have hDdiffNInterior : D \ N ⊆ interior D := by
    intro x hx
    have hxNotFrontier : x ∉ frontier D := fun hxFrontier ↦ hx.2 (hFrontierN hxFrontier)
    by_contra hxInterior
    exact hxNotFrontier ⟨by simpa [hDClosed.closure_eq] using hx.1, hxInterior⟩
  rcases exists_contMDiffMap_one_nhds_of_subset_interior (I := I)
      (n := (⊤ : ℕ∞)) hDdiffNClosed hDdiffNInterior with
    ⟨θ, hθOne, hθZero, hθRange⟩
  obtain ⟨η, hηSmooth, hηRange, hηZero, _hηOneEmpty⟩ :=
    exists_contMDiff_zero_iff_one_iff_of_isClosed (I := I) (n := (⊤ : ℕ∞))
      hDClosed isClosed_empty
      (by simpa using (disjoint_empty_right : Disjoint D (∅ : Set M)))
  let g : M → ℝ := fun x ↦ η x - (1 / 2 : ℝ) * θ x
  let f : M → ℝ := fun x ↦ χ x * ρ x + (1 - χ x) * g x
  have hθOneOnDdiffN : ∀ x ∈ D \ N, θ x = 1 := by
    intro x hx
    have hθxNhds : {y : M | θ y = 1} ∈ nhds x := (mem_nhdsSet_iff_forall.mp hθOne) x hx
    have hxMem : x ∈ {y : M | θ y = 1} := mem_of_mem_nhds hθxNhds
    exact hxMem
  have hgNonposOnD : ∀ x ∈ D, g x ≤ 0 := by
    intro x hxD
    have hηx : η x = 0 := (hηZero x).1 hxD
    have hθNonneg : 0 ≤ θ x := (hθRange x).1
    -- On the domain, the auxiliary separator vanishes and the cutoff subtraction keeps the sign nonpositive.
    simp [g, hηx, hθNonneg]
  have hgStrictNegOnDdiffN : ∀ x ∈ D \ N, g x < 0 := by
    intro x hx
    have hηx : η x = 0 := (hηZero x).1 hx.1
    have hθx : θ x = 1 := hθOneOnDdiffN x hx
    -- Away from the frontier neighborhood, the negative cutoff term forces a strict sign.
    simp [g, hηx, hθx]
  have hgPosOffD : ∀ x ∉ D, 0 < g x := by
    intro x hxD
    have hθx : θ x = 0 := hθZero x hxD
    have hηnonneg : 0 ≤ η x := (hηRange ⟨x, rfl⟩).1
    have hηne : η x ≠ 0 := by
      intro hηx
      exact hxD ((hηZero x).2 hηx)
    have hηpos : 0 < η x := by
      exact lt_of_le_of_ne hηnonneg (by simpa using hηne.symm)
    -- Outside the domain, the exact-zero owner for `η` makes the auxiliary function strictly positive.
    simpa [g, hθx] using hηpos
  have hfNonposOnD : ∀ x ∈ D, f x ≤ 0 := by
    intro x hxD
    by_cases hxU₀ : x ∈ U₀
    · have hxU : x ∈ U := hU₀SubsetU hxU₀
      have hρle : ρ x ≤ 0 := (hρSign x hxU).1 hxD
      have hgle : g x ≤ 0 := hgNonposOnD x hxD
      have hχNonneg : 0 ≤ χ x := (hχRange x).1
      have hOneSubNonneg : 0 ≤ 1 - χ x := by linarith [(hχRange x).2]
      -- On the frontier neighborhood, both summands are nonpositive, so the splice is nonpositive.
      dsimp [f]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hχNonneg hρle,
        mul_nonpos_of_nonneg_of_nonpos hOneSubNonneg hgle]
    · have hχx : χ x = 0 := hχZero x hxU₀
      -- Outside the frontier neighborhood, the splice reduces to the global sign controller `g`.
      simpa [f, hχx] using hgNonposOnD x hxD
  have hfPosOffD : ∀ x ∉ D, 0 < f x := by
    intro x hxD
    by_cases hxU₀ : x ∈ U₀
    · have hxU : x ∈ U := hU₀SubsetU hxU₀
      have hρPos : 0 < ρ x := by
        have hρNotLe : ¬ ρ x ≤ 0 := by
          intro hρle
          exact hxD ((hρSign x hxU).2 hρle)
        exact lt_of_not_ge hρNotLe
      have hgPos : 0 < g x := hgPosOffD x hxD
      have hχNonneg : 0 ≤ χ x := (hχRange x).1
      by_cases hχx : χ x = 0
      · -- If the frontier cutoff vanishes, positivity comes entirely from the global separator.
        simpa [f, hχx] using hgPos
      · have hχPos : 0 < χ x := by
          refine lt_of_le_of_ne hχNonneg ?_
          intro hχx'
          exact hχx hχx'.symm
        have hOneSubNonneg : 0 ≤ 1 - χ x := by linarith [(hχRange x).2]
        have hFirstPos : 0 < χ x * ρ x := mul_pos hχPos hρPos
        have hSecondNonneg : 0 ≤ (1 - χ x) * g x := mul_nonneg hOneSubNonneg hgPos.le
        -- When the frontier cutoff is active, the local signed model and the global separator are both positive.
        dsimp [f]
        nlinarith
    · have hχx : χ x = 0 := hχZero x hxU₀
      -- Away from the frontier neighborhood, positivity again comes from `g`.
      simpa [f, hχx] using hgPosOffD x hxD
  have hDLevel : D = f ⁻¹' Set.Iic 0 := by
    ext x
    constructor
    · intro hxD
      simpa [Set.mem_Iic] using hfNonposOnD x hxD
    · intro hfx
      by_contra hxD
      exact (not_le_of_gt (hfPosOffD x hxD)) hfx
  have hfRegular : Manifold.IsRegularValue I 𝓘(ℝ, ℝ) f 0 := by
    intro x hx0
    have hxD : x ∈ D := by
      have hxLevel : x ∈ f ⁻¹' Set.Iic 0 := by simp [hx0]
      simpa [hDLevel] using hxLevel
    have hxU₀ : x ∈ U₀ := by
      by_contra hxU₀
      have hxNotN : x ∉ N := fun hxN ↦ hxU₀ (hNSubsetU₀ hxN)
      have hgxNeg : g x < 0 := hgStrictNegOnDdiffN x ⟨hxD, hxNotN⟩
      have : f x < 0 := by simpa [f, hχZero x hxU₀] using hgxNeg
      exact (ne_of_lt this) hx0
    have hxU : x ∈ U := hU₀SubsetU hxU₀
    have hxN : x ∈ N := by
      by_contra hxN
      by_cases hχx : χ x = 1
      · have hρx : ρ x = 0 := by simpa [f, hχx] using hx0
        exact hxN (hFrontierN ((hρZero x hxU).2 hρx))
      · have hχLt : χ x < 1 := lt_of_le_of_ne (hχRange x).2 hχx
        have hρle : ρ x ≤ 0 := (hρSign x hxU).1 hxD
        have hgxNeg : g x < 0 := hgStrictNegOnDdiffN x ⟨hxD, hxN⟩
        have hχNonneg : 0 ≤ χ x := (hχRange x).1
        have hOneSubPos : 0 < 1 - χ x := by linarith
        have : f x < 0 := by
          -- Outside the exact `χ = 1` patch, the strict negativity of `g` rules out any new zero.
          dsimp [f]
          nlinarith [mul_nonpos_of_nonneg_of_nonpos hχNonneg hρle,
            mul_neg_of_pos_of_neg hOneSubPos hgxNeg]
        exact (ne_of_lt this) hx0
    have hEq : f =ᶠ[nhds x] ρ := by
      filter_upwards [hNOpen.mem_nhds hxN] with y hyN
      -- On the open patch where `χ = 1`, the splice is exactly the local frontier function `ρ`.
      have hχy : χ y = 1 := hNχ hyN
      simp [f, hχy]
    have hρx : ρ x = 0 := by
      have hfx : f x = ρ x := hEq.eq_of_nhds
      simpa [hx0] using hfx.symm
    -- The regularity test is local, and on the exact `χ = 1` patch the splice agrees with `ρ`.
    rw [hEq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ))]
    exact hρRegular x hxU hρx
  have hgSmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := by
    -- The global sign controller is built from the exact-zero separator and a cutoff-supported constant subtraction.
    exact hηSmooth.sub (contMDiff_const.mul θ.contMDiff)
  refine ⟨f, ?_⟩
  -- Package the global splice with the regular value `0` coming from the frontier neighborhood model.
  refine ⟨?_, ?_⟩
  · exact (χ.contMDiff.mul hρSmooth).add ((contMDiff_const.sub χ.contMDiff).mul hgSmooth)
  · exact ⟨⟨0, hfRegular, hDLevel⟩⟩

/-- Helper for Theorem 5.48: in positive ambient dimension, the remaining task is to build one
smooth signed function on an open neighborhood of `frontier D` with the correct local sign and
regular-value behavior. -/
lemma existsFrontierNeighborhoodSignedFunction
    {D : Set M} [SmoothManifoldWithBoundary dimM D] [Set.IsRegularDomain I D]
    [T2Space M] [SigmaCompactSpace M] (h0 : dimM ≠ 0) :
    ∃ U : Set M, IsOpen U ∧ frontier D ⊆ U ∧
      ∃ ρ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ ∧
        (∀ y ∈ U, y ∈ D ↔ ρ y ≤ 0) ∧
        (∀ y ∈ U, y ∈ frontier D ↔ ρ y = 0) ∧
        (∀ y ∈ U, ρ y = 0 → Function.Surjective (mfderiv I 𝓘(ℝ, ℝ) ρ y)) := by
  rcases dimM_eq_succ_of_ne_zero (E := E) h0 with ⟨n, hn⟩
  have hSmoothBoundarySucc : SmoothManifoldWithBoundary (n + 1) D := by
    -- The boundary model on `D` can be transported to successor form after rewriting the ambient dimension.
    simpa [hn] using (inferInstance : SmoothManifoldWithBoundary dimM D)
  letI : SmoothManifoldWithBoundary (n + 1) D := hSmoothBoundarySucc
  have hBoundaryData :
      ∃ β : D → ℝ, @IsBoundaryDefiningFunction n D _ _ β :=
    exists_boundary_defining_function (n := n) (M := D)
  have hFrontierBoundary :
      ∀ x : M, x ∈ frontier D →
        ∃ p : D, (leeBoundaryModelWithCorners dimM).IsBoundaryPoint p ∧ p.1 = x := by
    intro x hx
    exact (mem_frontier_iff_exists_boundaryPoint (I := I) (D := D)).1 hx
  -- Route correction: the global splice is now handled separately, so the only remaining missing
  -- owner is a local ambient signed model near each frontier point.
  -- TODO: use the successor-dimension boundary defining function on `D` together with the
  -- Euclidean-chart bridge for the subtype inclusion to build a smooth ambient signed function on a
  -- neighborhood of each frontier point, then patch those local models into one neighborhood owner.
  let _ := hBoundaryData
  let _ := hFrontierBoundary
  sorry

/-- Theorem 5.48 (1): every regular domain in a smooth manifold without boundary admits a
defining function. -/
theorem exists_definingFunction_of_isRegularDomain
    {D : Set M} [SmoothManifoldWithBoundary dimM D] [Set.IsRegularDomain I D]
    [T2Space M] [SigmaCompactSpace M] :
    ∃ f : M → ℝ, IsDefiningFunction I D f := by
  by_cases h0 : dimM = 0
  · -- In ambient dimension `0`, the regular domain is clopen and the shifted separator closes the proof.
    exact zeroDimensionalRegularDomain_hasDefiningFunction (I := I) (D := D) h0
  · have hDClosed : IsClosed D := regularDomain_isClosed (I := I) (D := D)
    rcases existsFrontierNeighborhoodSignedFunction (I := I) (D := D) h0 with
      ⟨U, hUOpen, hFrontierU, ρ, hρSmooth, hρSign, hρZero, hρRegular⟩
    -- The only remaining work after the neighborhood construction is the global splice to a true
    -- defining function, handled by the dedicated globalization helper above.
    let _ := hDClosed
    exact globalizeFrontierNeighborhoodSignedFunction (I := I) (D := D)
      hUOpen hFrontierU hρSmooth hρSign hρZero hρRegular

/-- Theorem 5.48 (2): if a compact regular domain `D` lies in a smooth manifold without boundary,
then it admits a defining function that is also an exhaustion function on the ambient manifold. -/
theorem exists_exhaustion_definingFunction_of_isCompact_regularDomain
    {D : Set M} [SmoothManifoldWithBoundary dimM D] [Set.IsRegularDomain I D]
    [T2Space M] [SigmaCompactSpace M] (hD : IsCompact D) :
    ∃ f : M → ℝ, IsDefiningFunction I D f ∧ Function.IsExhaustionFunction f := by
  letI : LocallyCompactSpace H := I.locallyCompactSpace
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  letI : ParacompactSpace M := paracompact_of_locallyCompact_sigmaCompact
  letI : T4Space M := T4Space.of_paracompactSpace_t2Space
  rcases exists_definingFunction_of_isRegularDomain (I := I) (D := D) with ⟨g, hg⟩
  rcases exists_zeroLevelDefiningFunction (I := I) (D := D) hg with
    ⟨g0, hg0, hD0, hg0Regular⟩
  rcases exists_positive_smooth_exhaustion_function (I := I) (M := M) with ⟨h, hhPos, hhExh⟩
  obtain ⟨C, hC⟩ := hD.exists_bound_of_continuousOn h.contMDiff.continuous.continuousOn
  let t : Set M := h ⁻¹' Set.Iio (C + 1)
  have hDsubsett : D ⊆ t := by
    intro x hx
    have hxBound : ‖h x‖ ≤ C := hC x hx
    have hxPos : 0 < h x := hhPos x
    have hxLe : h x ≤ C := by
      simpa [Real.norm_eq_abs, abs_of_pos hxPos] using hxBound
    show h x < C + 1
    linarith
  have htInterior : D ⊆ interior t := by
    have htOpen : IsOpen t := isOpen_Iio.preimage h.contMDiff.continuous
    simpa [t, htOpen.interior_eq] using hDsubsett
  rcases exists_contMDiffMap_one_nhds_of_subset_interior (I := I)
      (n := (⊤ : ℕ∞)) hD.isClosed htInterior with
    ⟨χ, hχOne, hχZero, hχRange⟩
  let f : M → ℝ := fun x ↦ χ x * g0 x + (1 - χ x) * h x
  have hfSmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := by
    -- The splice is a smooth convex combination of the zero-level defining function and the
    -- positive exhaustion function.
    exact
      (χ.contMDiff.mul hg0.contMDiff).add
        ((contMDiff_const.sub χ.contMDiff).mul h.contMDiff)
  have hDLevel : D = f ⁻¹' Set.Iic 0 := by
    -- On `D`, the cutoff is identically `1`, so the splice agrees with `g0`; off `D`, every
    -- convex combination term is positive, so the splice cannot lie in `(-∞, 0]`.
    ext x
    constructor
    · intro hxD
      have hχx : χ x = 1 := hχOne.self_of_nhdsSet x hxD
      have hxg0 : g0 x ≤ 0 := by
        simpa [hD0] using hxD
      simpa [f, hχx] using hxg0
    · intro hxle
      by_cases hxD : x ∈ D
      · exact hxD
      · have hxPos : 0 < f x := by
          by_cases hxt : x ∈ t
          · have hg0Pos : 0 < g0 x := by
              have hxNotLe : ¬ g0 x ≤ 0 := by
                intro hxg0
                exact hxD (by simpa [hD0] using hxg0)
              exact lt_of_not_ge hxNotLe
            have hhxPos : 0 < h x := hhPos x
            have hχNonneg : 0 ≤ χ x := (hχRange x).1
            have hχLe : χ x ≤ 1 := (hχRange x).2
            by_cases hχx : χ x = 1
            · simpa [f, hχx] using hg0Pos
            · have hχLt : χ x < 1 := lt_of_le_of_ne hχLe hχx
              have hOneSubPos : 0 < 1 - χ x := by linarith
              have hFirstNonneg : 0 ≤ χ x * g0 x := mul_nonneg hχNonneg hg0Pos.le
              have hSecondPos : 0 < (1 - χ x) * h x := by positivity
              have : 0 < χ x * g0 x + (1 - χ x) * h x := by linarith
              simpa [f] using this
          · have hχx : χ x = 0 := hχZero x hxt
            simpa [f, hχx] using hhPos x
        exact False.elim (not_le_of_gt hxPos hxle)
  have hfRegular : Manifold.IsRegularValue I 𝓘(ℝ, ℝ) f 0 := by
    -- The regularity test is local on the zero fiber, and near `D` the splice is exactly `g0`.
    intro x hx0
    have hxD : x ∈ D := by
      have hxLevel : x ∈ f ⁻¹' Set.Iic 0 := by simp [hx0]
      simpa [hDLevel] using hxLevel
    have hχNhds : {y : M | χ y = 1} ∈ nhds x := (mem_nhdsSet_iff_forall.mp hχOne) x hxD
    have hEq : f =ᶠ[nhds x] g0 := by
      filter_upwards [hχNhds] with y hy
      simp [f, hy]
    have hxg0 : g0 x = 0 := by
      have hxf : f x = g0 x := hEq.eq_of_nhds
      simpa [hx0] using hxf.symm
    rw [hEq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ))]
    exact hg0Regular x hxg0
  have hfDefining : IsDefiningFunction I D f := by
    -- The splice keeps the same zero-level regular-sublevel witness as `g0`.
    refine ⟨hfSmooth, ?_⟩
    exact ⟨⟨0, hfRegular, hDLevel⟩⟩
  have hfExhaustion : Function.IsExhaustionFunction f := by
    -- Outside the compact exhaustion sublevel `h⁻¹' (-∞, C + 1]`, the cutoff vanishes, so the
    -- splice is exactly the positive exhaustion function `h`.
    refine ⟨hfSmooth.continuous, ?_⟩
    intro c
    let K : Set M := h ⁻¹' Set.Iic (C + 1)
    have hKCompact : IsCompact K := hhExh.isCompact_sublevelSet (C + 1)
    have hSublevelCompact : IsCompact (h ⁻¹' Set.Iic c) := hhExh.isCompact_sublevelSet c
    refine (hKCompact.union hSublevelCompact).of_isClosed_subset
      (isClosed_Iic.preimage hfSmooth.continuous) ?_
    intro x hx
    by_cases hxt : x ∈ t
    · left
      simpa [K, t] using (le_of_lt hxt)
    · right
      have hχx : χ x = 0 := hχZero x hxt
      simpa [K, f, hχx] using hx
  exact ⟨f, hfDefining, hfExhaustion⟩
