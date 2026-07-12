import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0005_Proposition_2_1»
import DifferentialForms_Cartan_1970.II.section05.«0033_Definition_II_1_extra_20»

open MeasureTheory
open scoped BigOperators

universe u

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: if the compact region `K` lies in `D`,
then its frontier already lies in `D`. -/
theorem frontier_subset_domain_of_orientedBoundary
    {ι : Type u} [Fintype ι] {K D : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) :
    frontier K ⊆ D := by
  -- A compact set is closed, so every frontier point belongs to the set itself.
  intro z hz
  exact hKD (hΓ.isCompact.isClosed.frontier_subset hz)

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: every boundary loop of an oriented
boundary family already runs inside the ambient domain `D`. -/
theorem rangeToPathSubsetDomainOfOrientedBoundary
    {ι : Type u} [Fintype ι] {K D : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (i : ι) :
    Set.range (Γ i).toPath ⊆ D := by
  -- First put the loop image on `frontier K`, then send the frontier into `D`.
  intro z hz
  exact frontier_subset_domain_of_orientedBoundary hΓ hKD (hΓ.range_toPath_subset_frontier i hz)

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: if a closed path stays in `D`, then
its whole image lies in the connected component of `D` containing its base point. -/
theorem rangeToPathSubsetConnectedComponentDomain
    {D : Set ℂ} {z : ℂ} {γ : Path z z} (hγD : Set.range γ ⊆ D) :
    Set.range γ ⊆ connectedComponentIn D z := by
  have hRange_preconnected : IsPreconnected (Set.range γ) := by
    -- The image of a continuous path is preconnected.
    simpa using isPreconnected_range γ.continuous
  have hzRange : z ∈ Set.range γ := by
    -- The base point appears at parameter `0`.
    exact ⟨0, by simp⟩
  exact hRange_preconnected.subset_connectedComponentIn hzRange hγD

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: every oriented-boundary loop already
lies in the connected component of `D` containing its base point. -/
theorem rangeToPathSubsetConnectedComponentDomainOfOrientedBoundary
    {ι : Type u} [Fintype ι] {K D : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (i : ι) :
    Set.range (Γ i).toPath ⊆ connectedComponentIn D ((Γ i).toPath 0) := by
  -- First place the boundary loop inside `D`, then use the path-connectedness of its image.
  exact
    rangeToPathSubsetConnectedComponentDomain
      (γ := (Γ i).toPath) (z := (Γ i).toPath 0)
      (rangeToPathSubsetDomainOfOrientedBoundary hΓ hKD i)

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: restricting a local curve
straightening chart to a smaller open neighborhood of the base point preserves the straightening
data. -/
theorem IsLocalCurveStraighteningAt.restrOpen
    {γ : ℝ → Plane} {a b t₀ : ℝ} {δ : OpenPartialHomeomorph Plane Plane}
    (hδ : IsLocalCurveStraighteningAt γ a b t₀ δ)
    {s : Set Plane} (hs : IsOpen s) (ht : (t₀, 0) ∈ s) :
    IsLocalCurveStraighteningAt γ a b t₀ (δ.restrOpen s hs) := by
  refine
    { basePoint_mem_source := ?_
      source_subset := ?_
      contDiffOn := ?_
      contDiffOn_symm := ?_
      map_horizontal_axis := ?_
      isImage_horizontalAxis := ?_ }
  · -- The restricted chart still contains the base point because the new source was chosen to
    -- contain `(t₀, 0)`.
    simpa using And.intro hδ.basePoint_mem_source ht
  · -- Restricting the source can only strengthen the original strip control.
    intro p hp
    exact hδ.source_subset hp.1
  · -- The original regularity simply restricts to the smaller source.
    exact hδ.contDiffOn.mono fun _ hx ↦ hx.1
  · -- The inverse chart inherits the same restriction on the smaller target.
    exact hδ.contDiffOn_symm.mono fun _ hy ↦ hy.1
  · -- On the horizontal axis, the restricted chart agrees pointwise with the original chart.
    intro t ht₀
    exact hδ.map_horizontal_axis ht₀.1
  · -- The horizontal-axis image characterization is unchanged because the restricted chart uses
    -- the same coordinate formula on its smaller source.
    exact
      curve_image_is_horizontal_axis
        (fun {t} ht₀ ↦ hδ.map_horizontal_axis ht₀.1)

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: restricting a boundary straightening
chart to a smaller open neighborhood of the base point preserves the interior/exterior side data. -/
theorem IsBoundaryStraighteningAt.restrOpen
    {K : Set ℂ} {γ : ℝ → Plane} {t₀ : ℝ} {δ : OpenPartialHomeomorph Plane Plane}
    (hδ : IsBoundaryStraighteningAt K γ t₀ δ)
    {s : Set Plane} (hs : IsOpen s) (ht : (t₀, 0) ∈ s) :
    IsBoundaryStraighteningAt K γ t₀ (δ.restrOpen s hs) := by
  refine
    { toIsLocalCurveStraighteningAt := hδ.toIsLocalCurveStraighteningAt.restrOpen hs ht
      exterior_on_right := ?_
      interior_on_left := ?_ }
  · -- Restricting the source only shrinks the negative-side image, so the old empty-intersection
    -- statement still applies.
    have hsubset :
        (Complex.equivRealProdCLM.symm ''
            ((δ.restrOpen s hs) '' ((δ.restrOpen s hs).source ∩ {p | p.2 < 0}))) ∩ K ⊆
          (Complex.equivRealProdCLM.symm '' (δ '' (δ.source ∩ {p | p.2 < 0}))) ∩ K := by
      intro z hz
      rcases hz with ⟨hzImg, hzK⟩
      rcases hzImg with ⟨p, hp, rfl⟩
      rcases hp with ⟨q, hq, rfl⟩
      refine ⟨?_, hzK⟩
      refine ⟨δ q, ?_, by simp⟩
      exact ⟨q, ⟨hq.1.1, hq.2⟩, by simp⟩
    have hempty :
        (Complex.equivRealProdCLM.symm '' (δ '' (δ.source ∩ {p | p.2 < 0}))) ∩ K ⊆
          (∅ : Set ℂ) := by
      simp [hδ.exterior_on_right]
    exact Set.Subset.antisymm (hsubset.trans hempty) (by simp)
  · -- The restricted positive-side image is also a subset of the original one, so the original
    -- inclusion into `interior K` survives unchanged.
    intro z hz
    rcases hz with ⟨p, hp, rfl⟩
    rcases hp with ⟨q, hq, rfl⟩
    exact hδ.interior_on_left ⟨δ q, ⟨q, ⟨hq.1.1, hq.2⟩, by simp⟩, by simp⟩

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: a boundary straightening chart can be
restricted to an open connected-component neighborhood of its base point, so later staircase
constructions may remain inside one boundary component. -/
theorem IsBoundaryStraighteningAt.interBoundaryComponent
    {K C : Set ℂ} {γ : ℝ → Plane} {t₀ : ℝ}
    {δ : OpenPartialHomeomorph Plane Plane}
    (hδ : IsBoundaryStraighteningAt K γ t₀ δ)
    (hC_open : IsOpen C)
    (hγC : Complex.equivRealProdCLM.symm (γ t₀) ∈ C) :
    ∃ δ' : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (K ∩ C) γ t₀ δ' := by
  let Cplane : Set Plane := Complex.equivRealProdCLM '' C
  have hCplane_open : IsOpen Cplane := by
    -- The coordinate equivalence carries open complex neighborhoods to open plane neighborhoods.
    exact Complex.equivRealProdCLM.isOpenMap _ hC_open
  have hs_target_open : IsOpen (Cplane ∩ δ.target) := hCplane_open.inter δ.open_target
  have hs_target_subset : Cplane ∩ δ.target ⊆ δ.target := Set.inter_subset_right
  have hs_open_image : IsOpen (δ.symm '' (Cplane ∩ δ.target)) :=
    δ.symm.isOpen_image_of_subset_source hs_target_open hs_target_subset
  have hs_eq :
      δ.symm '' (Cplane ∩ δ.target) = δ.source ∩ δ ⁻¹' Cplane := by
    -- Rewrite the target-side restriction as the source-side restriction accepted by `restrOpen`.
    rw [δ.symm.image_eq_target_inter_inv_preimage hs_target_subset]
    ext p
    constructor
    · rintro ⟨hp_source, hpCplane_target⟩
      exact ⟨hp_source, hpCplane_target.1⟩
    · intro hp
      exact ⟨hp.1, hp.2, δ.map_source hp.1⟩
  have hs_open : IsOpen (δ.source ∩ δ ⁻¹' Cplane) := by
    -- The source-side description inherits openness from the corresponding target-side set.
    rw [← hs_eq]
    exact hs_open_image
  let δ' := δ.restrOpen (δ.source ∩ δ ⁻¹' Cplane) hs_open
  have hbase_mem : (t₀, 0) ∈ δ.source ∩ δ ⁻¹' Cplane := by
    -- The base point remains in the restricted source because its image lies in the chosen
    -- component.
    refine ⟨hδ.basePoint_mem_source, ?_⟩
    refine ⟨Complex.equivRealProdCLM.symm (γ t₀), hγC, ?_⟩
    exact (hδ.map_horizontal_axis hδ.basePoint_mem_horizontalAxisDomain).symm
  have hlocal : IsLocalCurveStraighteningAt γ 0 1 t₀ δ' :=
    hδ.toIsLocalCurveStraighteningAt.restrOpen hs_open hbase_mem
  refine ⟨δ', ?_⟩
  refine
    { toIsLocalCurveStraighteningAt := hlocal
      exterior_on_right := ?_
      interior_on_left := ?_ }
  · -- Restricting the chart only removes right-side points, so the old exterior statement still
    -- rules out `(K ∩ C)`.
    apply Set.not_nonempty_iff_eq_empty.1
    rintro ⟨z, hz⟩
    rcases hz with ⟨hz_image, hzKC⟩
    have hzK : z ∈ K := hzKC.1
    have hz_old :
        z ∈ Complex.equivRealProdCLM.symm '' (δ '' (δ.source ∩ {p : Plane | p.2 < 0})) := by
      rcases hz_image with ⟨q, hq, rfl⟩
      rcases hq with ⟨p, hp, rfl⟩
      refine ⟨δ p, ?_, rfl⟩
      exact ⟨p, ⟨hp.1.1, hp.2⟩, rfl⟩
    have hz_oldK :
        z ∈ (Complex.equivRealProdCLM.symm '' (δ '' (δ.source ∩ {p : Plane | p.2 < 0}))) ∩ K :=
      ⟨hz_old, hzK⟩
    have : False := by
      simp [hδ.exterior_on_right] at hz_oldK
    exact this
  · -- On the positive side, the old chart puts the image in `interior K`, while the new source
    -- restriction records membership in `C`.
    intro z hz
    rcases hz with ⟨q, hq, rfl⟩
    rcases hq with ⟨p, hp, rfl⟩
    have hp' : p ∈ (δ.source ∩ δ ⁻¹' Cplane) ∩ {p : Plane | 0 < p.2} := by
      simpa [δ'] using hp
    have hzInteriorK :
        Complex.equivRealProdCLM.symm (δ p) ∈ interior K := by
      exact hδ.interior_on_left ⟨δ p, ⟨p, ⟨hp'.1.1, hp'.2⟩, rfl⟩, rfl⟩
    have hzC : Complex.equivRealProdCLM.symm (δ p) ∈ C := by
      rcases hp'.1.2 with ⟨u, huC, huEq⟩
      have huC' : Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM u) ∈ C := by
        simpa using huC
      simpa [huEq] using huC'
    have hzInterKC : Complex.equivRealProdCLM.symm (δ p) ∈ interior K ∩ C :=
      ⟨hzInteriorK, hzC⟩
    have hInterSubset : interior K ∩ C ⊆ interior (K ∩ C) := by
      -- The intersection of the open interior of `K` with the open component `C` is an open set
      -- contained in `K ∩ C`, hence it sits inside the interior of the intersection.
      refine interior_maximal ?_ (isOpen_interior.inter hC_open)
      intro x hx
      exact ⟨interior_subset hx.1, hx.2⟩
    exact hInterSubset hzInterKC

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the degenerate strip
`[a,b] × {0}` has zero planar volume. -/
lemma stripVolume_zero (a b : ℝ) :
    volume (Set.Icc a b ×ˢ ({0} : Set ℝ)) = 0 := by
  -- Rewrite the planar volume as a product measure and collapse the singleton factor.
  simp [MeasureTheory.Measure.volume_eq_prod]

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the image of one `C¹` subdivision
piece of a boundary path has zero planar area in real coordinates. -/
lemma volume_range_realCurveSubinterval_eq_zero
    {γ : ClosedPath ℂ} {a b : ℝ}
    (hγ : ContDiffOn ℝ 1 γ.toPath.extend (Set.Icc a b)) :
    volume (Set.range (fun t : Set.Icc a b ↦ γ.realCurve t.1)) = 0 := by
  have hcurve : ContDiffOn ℝ 1 γ.realCurve (Set.Icc a b) := by
    -- Transport the `C¹` hypothesis through the linear real-coordinate identification of `ℂ`.
    have hlin :
        ContDiffOn ℝ 1 (fun z : ℂ ↦ Complex.equivRealProdCLM z) Set.univ :=
      Complex.equivRealProdCLM.contDiff.contDiffOn
    simpa [ClosedPath.realCurve, Complex.equivRealProd_apply] using
      hlin.comp hγ (by
        intro z hz
        simp)
  have hdiff :
      DifferentiableOn ℝ (fun p : ℝ × ℝ ↦ γ.realCurve p.1)
        (Set.Icc a b ×ˢ ({0} : Set ℝ)) := by
    -- The strip map varies only in the first coordinate, so differentiability comes from the
    -- one-dimensional curve.
    have hcurve' : DifferentiableOn ℝ γ.realCurve (Set.Icc a b) := hcurve.differentiableOn_one
    intro p hp
    exact (hcurve' p.1 hp.1).comp p differentiableWithinAt_fst (by
      intro q hq
      exact hq.1)
  have himage :
      Set.range (fun t : Set.Icc a b ↦ γ.realCurve t.1) =
        (fun p : ℝ × ℝ ↦ γ.realCurve p.1) '' (Set.Icc a b ×ˢ ({0} : Set ℝ)) := by
    -- Repackage the subinterval image as the image of the zero-measure strip.
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨(t.1, 0), ?_, rfl⟩
      exact ⟨t.2, by simp⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p.1, hp.1⟩, rfl⟩
  calc
    volume (Set.range (fun t : Set.Icc a b ↦ γ.realCurve t.1)) =
        volume ((fun p : ℝ × ℝ ↦ γ.realCurve p.1) '' (Set.Icc a b ×ˢ ({0} : Set ℝ))) := by
      rw [himage]
    _ = 0 := by
      -- Apply the Jacobian image-of-null-set theorem to the zero-measure strip.
      exact
        MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
          volume hdiff (stripVolume_zero a b)

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the image of one `C¹` subdivision
piece of a boundary path has zero planar area in the complex plane. -/
lemma volume_range_extendSubinterval_eq_zero
    {γ : ClosedPath ℂ} {a b : ℝ}
    (hγ : ContDiffOn ℝ 1 γ.toPath.extend (Set.Icc a b)) :
    volume (Set.range (fun t : Set.Icc a b ↦ γ.toPath.extend t.1)) = 0 := by
  have hpreimage :
      Complex.measurableEquivRealProd ⁻¹'
          Set.range (fun t : Set.Icc a b ↦ γ.realCurve t.1) =
        Set.range (fun t : Set.Icc a b ↦ γ.toPath.extend t.1) := by
    -- Rewrite the real-coordinate image back through the measure-preserving equivalence.
    ext z
    constructor
    · intro hz
      rcases hz with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      apply Complex.ext
      · simpa [ClosedPath.realCurve, Complex.equivRealProd_apply] using congrArg Prod.fst ht
      · simpa [ClosedPath.realCurve, Complex.equivRealProd_apply] using congrArg Prod.snd ht
    · rintro ⟨t, rfl⟩
      exact ⟨t, by simp [ClosedPath.realCurve, Complex.equivRealProd_apply]⟩
  calc
    volume (Set.range (fun t : Set.Icc a b ↦ γ.toPath.extend t.1)) =
        volume (Complex.measurableEquivRealProd ⁻¹'
          Set.range (fun t : Set.Icc a b ↦ γ.realCurve t.1)) := by
      rw [hpreimage]
    _ = volume (Set.range (fun t : Set.Icc a b ↦ γ.realCurve t.1)) := by
      -- The complex-to-real coordinate equivalence preserves Lebesgue measure.
      rw [Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv]
    _ = 0 := volume_range_realCurveSubinterval_eq_zero hγ

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: every parameter value in `[0,1]`
belongs to one interval of a finite subdivision with endpoints `0` and `1`. -/
lemma mem_subdivision_piece_of_mem_unitInterval
    {n : ℕ} {subdiv : Fin (n + 2) → ℝ} (h0 : subdiv 0 = 0)
    (h1 : subdiv (Fin.last (n + 1)) = 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ i : Fin (n + 1), t ∈ Set.Icc (subdiv i.castSucc) (subdiv i.succ) := by
  let subdivAt : ℕ → ℝ := fun m ↦
    if hm : m ≤ n + 1 then subdiv ⟨m, Nat.lt_succ_of_le hm⟩ else 1
  have hsubdivAt_zero : subdivAt 0 = 0 := by
    -- Read the left endpoint of the subdivision through the auxiliary natural-indexed function.
    simp [subdivAt, h0]
  have hsubdivAt_last : subdivAt (n + 1) = 1 := by
    -- The auxiliary function agrees with the right endpoint of the subdivision at `n + 1`.
    simpa [subdivAt] using h1
  let k : ℕ := Nat.findGreatest (fun m ↦ subdivAt m ≤ t) n
  have hk_le : k ≤ n := Nat.findGreatest_le n
  have hk_mem : subdivAt k ≤ t := by
    -- The subdivision starts at `0`, so `Nat.findGreatest` always returns an index whose left
    -- endpoint is still below `t`.
    have hzero_mem : subdivAt 0 ≤ t := by
      simpa [hsubdivAt_zero] using ht.1
    exact Nat.findGreatest_spec (P := fun m ↦ subdivAt m ≤ t) (m := 0) (n := n)
      (Nat.zero_le _) hzero_mem
  have hk_succ : t ≤ subdivAt (k + 1) := by
    by_cases hkn : k = n
    · -- If `k` is the last piece index, then the right endpoint is `1`.
      simpa [hkn, hsubdivAt_last] using ht.2
    · -- Otherwise, `k + 1` cannot still satisfy the defining inequality of `Nat.findGreatest`.
      have hklt : k < n := lt_of_le_of_ne hk_le hkn
      have hk1_le : k + 1 ≤ n := Nat.succ_le_of_lt hklt
      have hnot_mem : ¬ subdivAt (k + 1) ≤ t :=
        Nat.findGreatest_is_greatest
          (P := fun m ↦ subdivAt m ≤ t) (n := n) (k := k + 1) (Nat.lt_succ_self k) hk1_le
      exact (lt_of_not_ge hnot_mem).le
  let i : Fin (n + 1) := ⟨k, Nat.lt_succ_of_le hk_le⟩
  refine ⟨i, ?_⟩
  constructor
  · -- The chosen piece starts no later than `t`.
    have hk_le_last : k ≤ n + 1 := le_trans hk_le (Nat.le_succ n)
    simpa [i, subdivAt, hk_le_last] using hk_mem
  · by_cases hkn : k = n
    · -- On the last piece, the right endpoint is exactly the final subdivision value `1`.
      have hi_succ : subdiv i.succ = 1 := by
        simpa [i, hkn] using h1
      simpa [hi_succ] using ht.2
    · -- Before the last piece, maximality of `k` forces `t` below the next subdivision point.
      have hklt : k < n := lt_of_le_of_ne hk_le hkn
      have hk1_le_last : k + 1 ≤ n + 1 := Nat.succ_le_succ (Nat.le_of_lt hklt)
      simpa [i, subdivAt, hk1_le_last] using hk_succ

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: a piecewise differentiable closed path
has image of planar volume zero. -/
lemma volume_range_toPath_eq_zero_of_piecewiseDifferentiable
    {γ : ClosedPath ℂ} (hγ : γ.toPath.IsPiecewiseDifferentiable) :
    volume (Set.range γ.toPath) = 0 := by
  rcases hγ with ⟨n, subdiv, _, h0, h1, hpieces⟩
  have hcover :
      Set.range γ.toPath ⊆
        ⋃ i : Fin (n + 1),
          Set.range
            (fun t : Set.Icc (subdiv i.castSucc) (subdiv i.succ) ↦ γ.toPath.extend t.1) := by
    -- Cover the whole loop image by the finitely many `C¹` subdivision pieces.
    intro z hz
    rcases hz with ⟨t, rfl⟩
    rcases mem_subdivision_piece_of_mem_unitInterval h0 h1 t.2 with ⟨i, hi⟩
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    refine ⟨⟨t.1, hi⟩, ?_⟩
    simp [Path.extend_apply γ.toPath t.2]
  have hunion_zero :
      volume
          (⋃ i : Fin (n + 1),
            Set.range (fun t : Set.Icc (subdiv i.castSucc) (subdiv i.succ) ↦
              γ.toPath.extend t.1)) = 0 := by
    -- Each piece image has zero area, so their finite union also has zero area.
    exact MeasureTheory.measure_iUnion_null (μ := volume)
      (fun i ↦ volume_range_extendSubinterval_eq_zero (hpieces i))
  exact measure_mono_null hcover hunion_zero

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the frontier of an oriented boundary
region has planar volume zero. -/
lemma frontierVolume_eq_zero_of_isOrientedBoundary
    {ι : Type u} [Fintype ι] {K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) :
    volume (frontier K) = 0 := by
  -- Rewrite the frontier as the finite union of the boundary loop images.
  rw [← hΓ.iUnion_range_eq_frontier]
  exact MeasureTheory.measure_iUnion_null (μ := volume)
    (fun i ↦ volume_range_toPath_eq_zero_of_piecewiseDifferentiable (hΓ.piecewiseDifferentiable i))

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: each boundary component of an
oriented boundary family comes with the finite `C¹` subdivision supplied by piecewise
differentiability. -/
theorem boundaryComponent_hasContDiffSubdivision
    {ι : Type u} [Fintype ι] {K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (i : ι) :
    ∃ n : ℕ, ∃ subdiv : Fin (n + 2) → ℝ,
      StrictMono subdiv ∧
      subdiv 0 = 0 ∧
      subdiv (Fin.last (n + 1)) = 1 ∧
      ∀ j : Fin (n + 1),
        ContDiffOn ℝ 1 (Γ i).toPath.extend (Set.Icc (subdiv j.castSucc) (subdiv j.succ)) := by
  -- Unpack the subdivision data already stored in `hΓ.piecewiseDifferentiable i`.
  simpa [Path.isPiecewiseDifferentiable_iff] using hΓ.piecewiseDifferentiable i

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: a null frontier lets us replace set
integrals over `K` by set integrals over `interior K`. -/
lemma setIntegral_interior_eq_of_null_frontier
    {f : ℂ → ℝ} {K : Set ℂ} (hfrontier : volume (frontier K) = 0) :
    ∫ z in interior K, f z = ∫ z in K, f z := by
  -- The interior and the whole set agree almost everywhere once the frontier has zero volume.
  exact MeasureTheory.setIntegral_congr_set
    (interior_ae_eq_of_null_frontier (μ := volume) hfrontier)

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: a null frontier also lets us replace
set integrals over `K` by set integrals over `closure K`. -/
lemma setIntegral_closure_eq_of_null_frontier
    {f : ℂ → ℝ} {K : Set ℂ} (hfrontier : volume (frontier K) = 0) :
    ∫ z in closure K, f z = ∫ z in K, f z := by
  -- The closure and the original set differ only on the null frontier.
  exact MeasureTheory.setIntegral_congr_set
    (closure_ae_eq_of_null_frontier (μ := volume) hfrontier)

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: a connected-component key selected by
one boundary loop is an open connected subset of the ambient domain `D`. -/
theorem boundaryComponent_isOpen_isConnected
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD_open : IsOpen D) {C : Set ℂ}
    (hC : C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))) :
    IsOpen C ∧ IsConnected C := by
  rcases Finset.mem_image.mp hC with ⟨i, -, rfl⟩
  have hiD : (Γ i).toPath 0 ∈ D := by
    -- The selected component really comes from a boundary-loop base point lying in `D`.
    exact rangeToPathSubsetDomainOfOrientedBoundary hΓ hKD i ⟨0, by simp⟩
  constructor
  · -- Connected components of an open set are open.
    simpa using hD_open.connectedComponentIn (x := (Γ i).toPath 0)
  · -- The same base point witnesses nonemptiness of the chosen connected component.
    simpa using
      (isConnected_connectedComponentIn_iff
        (F := D) (x := (Γ i).toPath 0)).2 hiD

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: every connected-component key hit by
the boundary family is contained in the ambient domain `D`. -/
theorem boundaryComponent_subset_domain
    {ι : Type u} [Fintype ι] {D : Set ℂ} {Γ : ι → ClosedPath ℂ} {C : Set ℂ}
    (hC : C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))) :
    C ⊆ D := by
  rcases Finset.mem_image.mp hC with ⟨i, -, hiC⟩
  -- A connected component of `D` is contained in `D` by definition.
  intro z hz
  exact connectedComponentIn_subset D ((Γ i).toPath 0) (hiC ▸ hz)

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the frontier of one connected
component of an open set lies on the frontier of the ambient open set. -/
theorem frontier_connectedComponentIn_subset_frontier
    {D : Set ℂ} (hD_open : IsOpen D) {z : ℂ} (hz : z ∈ D) :
    frontier (connectedComponentIn D z) ⊆ frontier D := by
  let C : Set ℂ := connectedComponentIn D z
  have hC_subset : C ⊆ D := connectedComponentIn_subset D z
  have hC_open : IsOpen C := hD_open.connectedComponentIn
  have hcomp_closed : IsClosed (connectedComponent (⟨z, hz⟩ : D)) := isClosed_connectedComponent
  obtain ⟨t, ht_closed, ht_image⟩ := hcomp_closed.image_val
  have hC_eq : C = t ∩ D := by
    -- Rewrite the connected component in the ambient subtype as an intersection in `ℂ`.
    simpa [C, connectedComponentIn_eq_image hz] using ht_image
  have hclosureC_subset_t : closure C ⊆ t := by
    -- The closure of the component stays inside the closed ambient connected component.
    rw [hC_eq]
    exact closure_minimal Set.inter_subset_left ht_closed
  intro x hx
  have hxC : x ∈ frontier C := by
    simpa [C] using hx
  have hx' : x ∈ closure C ∧ x ∉ C := by
    rw [hC_open.frontier_eq] at hxC
    simpa using hxC
  have hx_not_memD : x ∉ D := by
    intro hxD
    have hxt : x ∈ t := hclosureC_subset_t hx'.1
    have hxC' : x ∈ C := by
      rw [hC_eq]
      exact ⟨hxt, hxD⟩
    exact hx'.2 hxC'
  refine ⟨closure_mono hC_subset hx'.1, ?_⟩
  simpa [hD_open.interior_eq] using hx_not_memD

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the compact owner `K` does not meet
the frontier of a boundary component of `D`. -/
theorem boundaryComponent_frontier_disjoint_compactRegion
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD_open : IsOpen D) {C : Set ℂ}
    (hC : C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))) :
    frontier C ∩ K = ∅ := by
  rcases Finset.mem_image.mp hC with ⟨i, -, rfl⟩
  have hizD : (Γ i).toPath 0 ∈ D := by
    -- The selected component comes from a boundary loop, so its base point lies in `D`.
    exact rangeToPathSubsetDomainOfOrientedBoundary hΓ hKD i ⟨0, by simp⟩
  have hfrontierCD :
      frontier (connectedComponentIn D ((Γ i).toPath 0)) ⊆ frontier D :=
    frontier_connectedComponentIn_subset_frontier hD_open hizD
  apply Set.not_nonempty_iff_eq_empty.1
  rintro ⟨x, hx⟩
  rcases hx with ⟨hxFront, hxK⟩
  have hxD : x ∈ D := hKD hxK
  have hxFrontD : x ∈ frontier D := hfrontierCD hxFront
  have hdisj : Disjoint D (frontier D) := by
    -- Open sets are disjoint from their frontiers.
    simpa [hD_open.interior_eq] using (disjoint_interior_frontier (s := D))
  exact hdisj.le_bot ⟨hxD, hxFrontD⟩

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the compact region `K` does not meet
the frontier of any connected component of the ambient open set `D`. -/
theorem connectedComponentIn_frontier_disjoint_compactRegion
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD_open : IsOpen D)
    {z : ℂ} (hz : z ∈ D) :
    frontier (connectedComponentIn D z) ∩ K = ∅ := by
  have hfrontierCD :
      frontier (connectedComponentIn D z) ⊆ frontier D :=
    frontier_connectedComponentIn_subset_frontier hD_open hz
  apply Set.not_nonempty_iff_eq_empty.1
  rintro ⟨x, hx⟩
  rcases hx with ⟨hxFront, hxK⟩
  have hxD : x ∈ D := hKD hxK
  have hxFrontD : x ∈ frontier D := hfrontierCD hxFront
  have hdisj : Disjoint D (frontier D) := by
    -- Open sets are disjoint from their frontiers, so a point of `K ⊆ D` cannot lie there.
    simpa [hD_open.interior_eq] using (disjoint_interior_frontier (s := D))
  exact hdisj.le_bot ⟨hxD, hxFrontD⟩

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: if a boundary loop is keyed by one
component `C`, then its whole path image lies in `C`. -/
theorem range_toPath_subset_component_of_boundaryKey
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) {C : Set ℂ} {i : ι}
    (hiC : connectedComponentIn D ((Γ i).toPath 0) = C) :
    Set.range (Γ i).toPath ⊆ C := by
  have hpathC :
      Set.range (Γ i).toPath ⊆ connectedComponentIn D ((Γ i).toPath 0) :=
    rangeToPathSubsetConnectedComponentDomainOfOrientedBoundary hΓ hKD i
  -- The stored key equality is exactly the target component identity.
  exact hiC ▸ hpathC

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: restricting to the subtype of indices
with connected-component key `C` preserves piecewise differentiability. -/
theorem subtypeBoundaryPaths_piecewiseDifferentiable
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) {C : Set ℂ} :
    ∀ i : {j // connectedComponentIn D ((Γ j).toPath 0) = C},
      ((Γ i.1).toPath).IsPiecewiseDifferentiable := by
  intro i
  -- The subtype forgets no geometric data about the original boundary loop.
  simpa using hΓ.piecewiseDifferentiable i.1

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: every loop in the subtype family with
key `C` stays inside that connected component. -/
theorem subtypeBoundaryPaths_subset_component
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) {C : Set ℂ} :
    ∀ i : {j // connectedComponentIn D ((Γ j).toPath 0) = C},
      Set.range (Γ i.1).toPath ⊆ C := by
  intro i
  -- The subtype equality records the connected-component key needed to apply the range lemma.
  exact range_toPath_subset_component_of_boundaryKey hΓ hKD i.2

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: every interior parameter on a boundary
loop keyed by `C` lands in `C`. -/
theorem realCurve_mem_component_of_boundaryKey
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) {C : Set ℂ} {i : ι}
    (hiC : connectedComponentIn D ((Γ i).toPath 0) = C)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    Complex.equivRealProdCLM.symm ((Γ i).realCurve t) ∈ C := by
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hrange :
      Complex.equivRealProdCLM.symm ((Γ i).realCurve t) ∈ Set.range (Γ i).toPath := by
    -- Repackage the real-curve point as an honest point on the underlying closed path.
    refine ⟨⟨t, htIcc⟩, ?_⟩
    refine Complex.ext ?_ ?_
    · simp [ClosedPath.realCurve, Path.extend_apply, htIcc]
    · simp [ClosedPath.realCurve, Path.extend_apply, htIcc]
  -- Once the point is back on the path image, the boundary-key range lemma places it in `C`.
  exact range_toPath_subset_component_of_boundaryKey hΓ hKD hiC hrange

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: intersecting the compact owner with
one boundary component stays compact. -/
theorem compact_inter_boundaryComponent
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD_open : IsOpen D) {C : Set ℂ}
    (hC : C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))) :
    IsCompact (K ∩ C) := by
  have hC_open : IsOpen C := (boundaryComponent_isOpen_isConnected hΓ hKD hD_open hC).1
  have hfrontierEmpty :
      frontier C ∩ K = ∅ :=
    boundaryComponent_frontier_disjoint_compactRegion hΓ hKD hD_open hC
  have hKC_eq : K ∩ C = K ∩ closure C := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, subset_closure hx.2⟩
    · intro hx
      by_cases hxC : x ∈ C
      · exact ⟨hx.1, hxC⟩
      · have hxFront : x ∈ frontier C := by
          -- Outside `C` but in `closure C`, the point lies on the frontier because `C` is open.
          rw [hC_open.frontier_eq]
          exact ⟨hx.2, hxC⟩
        have hnonempty : (frontier C ∩ K).Nonempty := ⟨x, ⟨hxFront, hx.1⟩⟩
        have hfalse : False := by
          simp [hfrontierEmpty] at hnonempty
        exact False.elim hfalse
  -- After replacing `C` by its closure, compactness comes from compactness of `K`.
  rw [hKC_eq]
  exact hΓ.isCompact.inter_right isClosed_closure

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: intersecting the compact owner with
the connected component of an arbitrary point of `D` stays compact. -/
theorem compact_inter_connectedComponentIn
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD_open : IsOpen D)
    {z : ℂ} (hz : z ∈ D) :
    IsCompact (K ∩ connectedComponentIn D z) := by
  let C : Set ℂ := connectedComponentIn D z
  have hC_open : IsOpen C := by
    simpa [C] using hD_open.connectedComponentIn (x := z)
  have hfrontierEmpty : frontier C ∩ K = ∅ := by
    simpa [C] using
      connectedComponentIn_frontier_disjoint_compactRegion
        (Γ := Γ) hΓ hKD hD_open hz
  have hKC_eq : K ∩ C = K ∩ closure C := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, subset_closure hx.2⟩
    · intro hx
      by_cases hxC : x ∈ C
      · exact ⟨hx.1, hxC⟩
      · have hxFront : x ∈ frontier C := by
          -- Outside `C` but in `closure C`, the point lies on the frontier because `C` is open.
          rw [hC_open.frontier_eq]
          exact ⟨hx.2, hxC⟩
        have hnonempty : (frontier C ∩ K).Nonempty := ⟨x, ⟨hxFront, hx.1⟩⟩
        have hfalse : False := by
          simp [hfrontierEmpty] at hnonempty
        exact False.elim hfalse
  -- The same closure replacement used for boundary components works for any connected component.
  rw [hKC_eq]
  exact hΓ.isCompact.inter_right isClosed_closure

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: intersecting the oriented-boundary
region with one boundary component cuts the frontier down to `frontier K ∩ C`. -/
theorem frontier_inter_boundaryComponent_eq
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD_open : IsOpen D) {C : Set ℂ}
    (hC : C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))) :
    frontier (K ∩ C) = frontier K ∩ C := by
  have hC_open : IsOpen C := (boundaryComponent_isOpen_isConnected hΓ hKD hD_open hC).1
  have hfrontierKC_subset_C : frontier (K ∩ C) ⊆ C := by
    intro x hx
    rw [frontier_eq_closure_inter_closure] at hx
    have hxClosure : x ∈ closure (K ∩ C) := hx.1
    have hxK : x ∈ K :=
      (closure_minimal Set.inter_subset_left hΓ.isCompact.isClosed) hxClosure
    by_contra hx_notC
    have hxFrontC : x ∈ frontier C := by
      -- The point lies in `closure C` through the closure of `K ∩ C`, but not in `C`.
      rw [hC_open.frontier_eq]
      exact ⟨closure_mono Set.inter_subset_right hxClosure, hx_notC⟩
    have hfrontierEmpty :=
      boundaryComponent_frontier_disjoint_compactRegion hΓ hKD hD_open hC
    have hnonempty : (frontier C ∩ K).Nonempty := ⟨x, ⟨hxFrontC, hxK⟩⟩
    have hfalse : False := by
      simp [hfrontierEmpty] at hnonempty
    exact False.elim hfalse
  -- Once the new frontier is known to stay inside `C`, the usual open-intersection formula
  -- becomes an equality.
  calc
    frontier (K ∩ C) = frontier (K ∩ C) ∩ C := by
      symm
      exact Set.inter_eq_left.mpr hfrontierKC_subset_C
    _ = frontier K ∩ C := frontier_inter_open_inter hC_open

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: intersecting the compact region with
the connected component of any point of `D` does not create new frontier points outside that
component. -/
theorem frontier_inter_connectedComponentIn_eq
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD_open : IsOpen D)
    {z : ℂ} (hz : z ∈ D) :
    frontier (K ∩ connectedComponentIn D z) = frontier K ∩ connectedComponentIn D z := by
  let C : Set ℂ := connectedComponentIn D z
  have hC_open : IsOpen C := by
    simpa [C] using hD_open.connectedComponentIn (x := z)
  have hfrontierKC_subset_C : frontier (K ∩ C) ⊆ C := by
    intro x hx
    rw [frontier_eq_closure_inter_closure] at hx
    have hxClosure : x ∈ closure (K ∩ C) := hx.1
    have hxK : x ∈ K :=
      (closure_minimal Set.inter_subset_left hΓ.isCompact.isClosed) hxClosure
    by_contra hx_notC
    have hxFrontC : x ∈ frontier C := by
      -- The point lies in `closure C` through the closure of `K ∩ C`, but not in `C`.
      rw [hC_open.frontier_eq]
      exact ⟨closure_mono Set.inter_subset_right hxClosure, hx_notC⟩
    have hfrontierEmpty :
        frontier C ∩ K = ∅ := by
      simpa [C] using
        connectedComponentIn_frontier_disjoint_compactRegion
          (Γ := Γ) hΓ hKD hD_open hz
    have hnonempty : (frontier C ∩ K).Nonempty := ⟨x, ⟨hxFrontC, hxK⟩⟩
    have hfalse : False := by
      simp [hfrontierEmpty] at hnonempty
    exact False.elim hfalse
  -- Once the new frontier is known to stay inside the component, the open-intersection formula
  -- becomes an equality exactly as in the boundary-keyed case.
  calc
    frontier (K ∩ C) = frontier (K ∩ C) ∩ C := by
      symm
      exact Set.inter_eq_left.mpr hfrontierKC_subset_C
    _ = frontier K ∩ C := frontier_inter_open_inter hC_open

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the interior of `K` is the finite
union of the interiors of `K ∩ C` over the boundary-component keys hit by the oriented boundary
family. -/
theorem interior_eq_biUnion_boundaryComponents
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD_open : IsOpen D) :
    interior K =
      ⋃ C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0)),
        interior (K ∩ C) := by
  classical
  let components : Finset (Set ℂ) :=
    Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))
  ext x
  constructor
  · intro hx
    have hxK : x ∈ K := interior_subset hx
    have hxD : x ∈ D := hKD hxK
    let C : Set ℂ := connectedComponentIn D x
    have hxC : x ∈ C := by
      simpa [C] using mem_connectedComponentIn hxD
    have hC_open : IsOpen C := by
      simpa [C] using hD_open.connectedComponentIn (x := x)
    have hC_mem : C ∈ components := by
      by_contra hC_not
      have hfrontierEmpty : frontier K ∩ C = ∅ := by
        apply Set.not_nonempty_iff_eq_empty.1
        rintro ⟨y, hy⟩
        rcases hy with ⟨hyFront, hyC⟩
        rw [← hΓ.iUnion_range_eq_frontier] at hyFront
        rcases Set.mem_iUnion.mp hyFront with ⟨i, hyi⟩
        have hyKey :
            y ∈ connectedComponentIn D ((Γ i).toPath 0) :=
          rangeToPathSubsetConnectedComponentDomainOfOrientedBoundary hΓ hKD i hyi
        have hKeyEq :
            connectedComponentIn D ((Γ i).toPath 0) = C := by
          calc
            connectedComponentIn D ((Γ i).toPath 0) = connectedComponentIn D y :=
              connectedComponentIn_eq hyKey
            _ = connectedComponentIn D x := (connectedComponentIn_eq hyC).symm
            _ = C := by rfl
        have : C ∈ components := by
          exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hKeyEq⟩
        exact hC_not this
      have hfrontierKC :
          frontier (K ∩ C) = ∅ := by
        simpa [hfrontierEmpty, C] using
          frontier_inter_connectedComponentIn_eq
            (Γ := Γ) hΓ hKD hD_open hxD
      have hclopen : IsClopen (K ∩ C) := by
        -- If the component carried no boundary point of `K`, the whole intersection would be
        -- clopen in `ℂ`.
        exact (isClopen_iff_frontier_eq_empty).2 hfrontierKC
      have hKC_eq_univ : K ∩ C = Set.univ := by
        have hKC_nonempty : (K ∩ C).Nonempty := ⟨x, ⟨hxK, hxC⟩⟩
        rcases (isClopen_iff (s := K ∩ C)).1 hclopen with hEmpty | hUniv
        · exact False.elim (hKC_nonempty.ne_empty hEmpty)
        · exact hUniv
      have hCompactUniv : IsCompact (Set.univ : Set ℂ) := by
        simpa [hKC_eq_univ, C] using
          compact_inter_connectedComponentIn
            (Γ := Γ) hΓ hKD hD_open hxD
      exact (noncompact_univ ℂ) hCompactUniv
    have hxInterKC : x ∈ interior (K ∩ C) := by
      -- Once the boundary component carrying `x` has been identified, the point lies in the
      -- corresponding interior intersection by openness of the component.
      rw [interior_inter, hC_open.interior_eq]
      exact ⟨hx, hxC⟩
    exact Set.mem_iUnion.mpr ⟨C, Set.mem_iUnion.mpr ⟨hC_mem, hxInterKC⟩⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨C, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hC, hx⟩
    -- Each component interior sits inside `interior K` by monotonicity.
    exact interior_mono Set.inter_subset_left hx

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the subtype-indexed boundary family
over one connected component covers exactly `frontier K ∩ C`. -/
theorem iUnion_subtypeBoundaryPaths_eq_frontier_inter_boundaryComponent
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) {C : Set ℂ}
    (hC : C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))) :
    (⋃ i : {j // connectedComponentIn D ((Γ j).toPath 0) = C}, Set.range (Γ i.1).toPath) =
      frontier K ∩ C := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hix⟩
    exact
      ⟨hΓ.range_toPath_subset_frontier i.1 hix,
        (subtypeBoundaryPaths_subset_component hΓ hKD i) hix⟩
  · rintro ⟨hxFront, hxC⟩
    rcases Finset.mem_image.mp hC with ⟨i0, -, hi0C⟩
    rw [← hΓ.iUnion_range_eq_frontier] at hxFront
    rcases Set.mem_iUnion.mp hxFront with ⟨i, hix⟩
    have hxKey :
        x ∈ connectedComponentIn D ((Γ i).toPath 0) := by
      -- Any point on the loop lies in the connected component determined by its base point.
      exact rangeToPathSubsetConnectedComponentDomainOfOrientedBoundary hΓ hKD i hix
    have hCx : C = connectedComponentIn D x := by
      -- The chosen component key matches the connected component of the actual point `x`.
      calc
        C = connectedComponentIn D ((Γ i0).toPath 0) := hi0C.symm
        _ = connectedComponentIn D x := connectedComponentIn_eq (hi0C.symm ▸ hxC)
    have hiC : connectedComponentIn D ((Γ i).toPath 0) = C := by
      exact (connectedComponentIn_eq hxKey).trans hCx.symm
    exact Set.mem_iUnion.mpr ⟨⟨i, hiC⟩, hix⟩

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the boundary family restricted to one
connected component is an oriented boundary of `K ∩ C`. -/
theorem subtypeBoundaryPaths_isOrientedBoundaryOf_inter_boundaryComponent
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD_open : IsOpen D) {C : Set ℂ}
    (hC : C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))) :
    IsOrientedBoundaryOf (K ∩ C)
      (fun i : {j // connectedComponentIn D ((Γ j).toPath 0) = C} ↦ Γ i.1) := by
  let ΓC : {j // connectedComponentIn D ((Γ j).toPath 0) = C} → ClosedPath ℂ := fun i ↦ Γ i.1
  have hC_open : IsOpen C := (boundaryComponent_isOpen_isConnected hΓ hKD hD_open hC).1
  refine
    { isCompact := compact_inter_boundaryComponent hΓ hKD hD_open hC
      piecewiseDifferentiable := ?_
      simple_loops := ?_
      pairwiseDisjoint_ranges := ?_
      iUnion_range_eq_frontier := ?_
      exists_boundary_chart_at_regular_point := ?_ }
  · -- Restricting the index type does not change the underlying curve regularity.
    intro i
    simpa [ΓC] using hΓ.piecewiseDifferentiable i.1
  · -- The simple-loop property is inherited from the original boundary family.
    intro i s t hst
    simpa [ΓC] using hΓ.simple_loops i.1 hst
  · -- Distinct subtype indices remain distinct original loops.
    intro i j hij
    exact hΓ.pairwiseDisjoint_ranges fun hij_eq ↦ hij (Subtype.ext hij_eq)
  · -- The restricted frontier is exactly the frontier of the intersected compact region.
    calc
      (⋃ i : {j // connectedComponentIn D ((Γ j).toPath 0) = C}, Set.range (ΓC i).toPath) =
          frontier K ∩ C := by
        simpa [ΓC] using
          iUnion_subtypeBoundaryPaths_eq_frontier_inter_boundaryComponent hΓ hKD hC
      _ = frontier (K ∩ C) := by
        symm
        exact frontier_inter_boundaryComponent_eq hΓ hKD hD_open hC
  · -- Restrict each regular boundary chart to the ambient connected component carrying the loop.
    intro i t₀ ht₀ hdiff hderiv
    obtain ⟨δ, hδi⟩ := hΓ.exists_boundary_chart_at_regular_point i.1 ht₀ hdiff hderiv
    have hpointC : Complex.equivRealProdCLM.symm ((Γ i.1).realCurve t₀) ∈ C :=
      realCurve_mem_component_of_boundaryKey hΓ hKD i.2 ht₀
    obtain ⟨δ', hδ'⟩ :=
      IsBoundaryStraighteningAt.interBoundaryComponent hδi hC_open hpointC
    exact ⟨δ', hδ'⟩

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the global contour sum groups
fiberwise by the connected-component key in `D`. -/
theorem sum_curveIntegral_eq_sum_component_blocks
    {ι : Type u} [Fintype ι] {D : Set ℂ} (Γ : ι → ClosedPath ℂ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ω : ℂ → ℂ →L[ℝ] F} :
    (∑ i, ∫ᶜ z in (Γ i).toPath, ω z) =
      (Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))).sum
        (fun c =>
          (Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = c).sum
            (fun i => ∫ᶜ z in (Γ i).toPath, ω z)) := by
  classical
  let key : ι → Set ℂ := fun i => connectedComponentIn D ((Γ i).toPath 0)
  let value : ι → F := fun i => ∫ᶜ z in (Γ i).toPath, ω z
  have hkey_mem : ∀ i : ι, key i ∈ Finset.univ.image key := by
    intro i
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  -- Group the finite sum by the connected-component key before any component-local geometry is
  -- applied.
  calc
    ∑ i, value i =
        Finset.univ.sum fun i => if key i ∈ Finset.univ.image key then value i else 0 := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [hkey_mem i]
    _ =
        (Finset.univ.image key).sum
          (fun c => (Finset.univ.filter fun i => key i = c).sum value) := by
      symm
      simpa [Finset.sum_filter] using
        (Finset.sum_fiberwise_eq_sum_filter Finset.univ (Finset.univ.image key) key value)
    _ =
        (Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))).sum
          (fun c =>
            (Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = c).sum
              (fun i => ∫ᶜ z in (Γ i).toPath, ω z)) := by
      simp [key, value]
