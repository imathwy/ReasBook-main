module

public import Topology_Munkres_2000.Book.Definition_21_3.ClosedUnitDisk
public import Topology_Munkres_2000.Book.Theorem_63_4
public import Topology_Munkres_2000.Book.Lemma_61_1
public import Topology_Munkres_2000.Book.Proposition_61_1.Stereographic
public import Topology_Munkres_2000.Book.Theorem_63_6.EmbeddedPaths
public import Topology_Munkres_2000.Book.Theorem_63_6.FiniteCellPatch
public import Topology_Munkres_2000.Book.Theorem_63_6.JordanCrosscut
public import Topology_Munkres_2000.Book.Theorem_63_6.CrosscutSplit
public import Topology_Munkres_2000.Book.Theorem_63_6.PolygonalChains
public import Topology_Munkres_2000.Book.Theorem_63_6.RectangularCollar
public import Topology_Munkres_2000.Book.Theorem_63_6.TracePatch
public import Topology_Munkres_2000.Book.Theorem_63_6.TraceMesh
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Homeomorph.Lemmas

public section

open Set Filter
open scoped Topology

/-- Helper for Theorem 63.6: a finite spherical Jordan partition records
certified Jordan-domain cells whose closures exactly cover the parent closure. -/
private structure FiniteSphericalJordanPartition
    (U : Set (StandardSphere 2)) (ι : Type*) [Fintype ι] where
  cell : ι → Set (StandardSphere 2)
  frontierSimple : ∀ i, Topology.IsSimpleClosedCurve (frontier (cell i))
  component : ∀ i, IsConnectedComponentIn (frontier (cell i))ᶜ (cell i)
  cellSubset : ∀ i, cell i ⊆ U
  pairwiseDisjoint : Pairwise fun i j ↦ Disjoint (cell i) (cell j)
  closureUnion : (⋃ i, closure (cell i)) = closure U

/-- Helper for Theorem 63.6: a coherent finite spherical refinement assigns
each new cell to an old cell and covers every old closure by its fiber. -/
private structure FiniteSphericalJordanRefinement
    {U : Set (StandardSphere 2)} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : FiniteSphericalJordanPartition U ι)
    (Q : FiniteSphericalJordanPartition U κ) where
  parent : κ → ι
  fiberClosureCover : ∀ i,
    (⋃ j : {j // parent j = i}, closure (Q.cell j)) = closure (P.cell i)

/-- Helper for Theorem 63.6: a certified spherical Jordan domain has the
canonical one-cell finite partition. -/
private theorem FiniteSphericalJordanPartition.existsSingleton
    (U : Set (StandardSphere 2))
    [Topology.IsSimpleClosedCurve (frontier U)]
    (hU : IsConnectedComponentIn (frontier U)ᶜ U) :
    ∃ P : FiniteSphericalJordanPartition U (Fin 1), P.cell 0 = U := by
  -- Every index of `Fin 1` names the parent domain, so all structural fields
  -- reduce to the supplied Jordan-domain certificates.
  have hFrontier : ∀ _ : Fin 1, Topology.IsSimpleClosedCurve (frontier U) :=
    fun _ ↦ inferInstance
  have hComponent : ∀ _ : Fin 1, IsConnectedComponentIn (frontier U)ᶜ U :=
    fun _ ↦ hU
  have hSubset : ∀ _ : Fin 1, U ⊆ U := fun _ ↦ Set.Subset.rfl
  have hPairwise : Pairwise fun _ _ : Fin 1 ↦ Disjoint U U := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have hClosureUnion : (⋃ _ : Fin 1, closure U) = closure U := by
    simp only [iUnion_const]
  let P : FiniteSphericalJordanPartition U (Fin 1) :=
    { cell := fun _ ↦ U
      frontierSimple := hFrontier
      component := hComponent
      cellSubset := hSubset
      pairwiseDisjoint := hPairwise
      closureUnion := hClosureUnion }
  -- The unique cell is definitionally the original domain.
  exact ⟨P, rfl⟩

/-- Helper for Theorem 63.6: replacing one cell by the two domains of a
spherical crosscut split gives a coherent binary finite refinement. -/
private theorem FiniteSphericalJordanPartition.existsBinaryRefinementAt
    {U : Set (StandardSphere 2)} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : FiniteSphericalJordanPartition U ι) (i : ι)
    {p q : StandardSphere 2} (gamma : JordanCrosscut (P.cell i) p q)
    (S : gamma.SphericalSplit) :
    ∃ Q : FiniteSphericalJordanPartition U
        (Sum {j : ι // j ≠ i} (Fin 2)),
      Nonempty (FiniteSphericalJordanRefinement P Q) ∧
        (∀ j, Q.cell (Sum.inl j) = P.cell j) ∧
          Q.cell (Sum.inr 0) = S.left ∧ Q.cell (Sum.inr 1) = S.right := by
  classical
  let cell : Sum {j : ι // j ≠ i} (Fin 2) →
      Set (StandardSphere 2) := fun j ↦
    match j with
    | Sum.inl k => P.cell k
    | Sum.inr k => if k = 0 then S.left else S.right
  let parent : Sum {j : ι // j ≠ i} (Fin 2) → ι := fun j ↦
    match j with
    | Sum.inl k => k
    | Sum.inr _ => i
  have hCellOld (j : {j : ι // j ≠ i}) :
      cell (Sum.inl j) = P.cell j := by
    rfl
  have hCellLeft : cell (Sum.inr 0) = S.left := by
    simp only [cell, if_pos rfl]
  have hOneNeZero : (1 : Fin 2) ≠ 0 := by
    decide
  have hCellRight : cell (Sum.inr 1) = S.right := by
    simp only [cell, if_neg hOneNeZero]
  have hLeftSubsetParent : S.left ⊆ P.cell i := by
    -- The split cover places every left-child point in the parent domain.
    intro z hz
    have hzCover : z ∈ P.cell i \ gamma.carrier :=
      S.cover.symm ▸ Or.inl hz
    exact hzCover.1
  have hRightSubsetParent : S.right ⊆ P.cell i := by
    -- The same cover places the right child in the selected parent cell.
    intro z hz
    have hzCover : z ∈ P.cell i \ gamma.carrier :=
      S.cover.symm ▸ Or.inr hz
    exact hzCover.1
  have hChildSubsetParent (k : Fin 2) : cell (Sum.inr k) ⊆ P.cell i := by
    -- Normalize the two finite child indices once for later containment uses.
    by_cases hk : k = 0
    · subst k
      rw [hCellLeft]
      exact hLeftSubsetParent
    · have hkOne : k = 1 := Fin.eq_one_of_ne_zero k hk
      subst k
      rw [hCellRight]
      exact hRightSubsetParent
  have hFrontier : ∀ j, Topology.IsSimpleClosedCurve (frontier (cell j)) := by
    intro j
    rcases j with j | j
    · rw [hCellOld]
      exact P.frontierSimple j
    · by_cases hj : j = 0
      · subst j
        rw [hCellLeft]
        exact S.leftFrontierSimple
      · have hjOne : j = 1 := Fin.eq_one_of_ne_zero j hj
        subst j
        rw [hCellRight]
        exact S.rightFrontierSimple
  have hComponent : ∀ j,
      IsConnectedComponentIn (frontier (cell j))ᶜ (cell j) := by
    intro j
    rcases j with j | j
    · rw [hCellOld]
      exact P.component j
    · by_cases hj : j = 0
      · subst j
        rw [hCellLeft]
        exact S.leftComponent
      · have hjOne : j = 1 := Fin.eq_one_of_ne_zero j hj
        subst j
        rw [hCellRight]
        exact S.rightComponent
  have hSubset : ∀ j, cell j ⊆ U := by
    intro j
    rcases j with j | j
    · rw [hCellOld]
      exact P.cellSubset j
    · exact (hChildSubsetParent j).trans (P.cellSubset i)
  have hPairwise : Pairwise fun a b ↦ Disjoint (cell a) (cell b) := by
    -- Old cells stay disjoint, each child lies in the removed parent cell,
    -- and the two new children are disjoint by the split certificate.
    intro a b hab
    rcases a with a | a
    · rcases b with b | b
      · have habValue : (a : ι) ≠ b := by
          intro h
          exact hab (congrArg Sum.inl (Subtype.ext h))
        simpa only [cell] using P.pairwiseDisjoint habValue
      · have hOldParent : Disjoint (P.cell a) (P.cell i) :=
          P.pairwiseDisjoint a.property
        simpa only [cell] using
          hOldParent.mono Set.Subset.rfl (hChildSubsetParent b)
    · rcases b with b | b
      · have hParentOld : Disjoint (P.cell i) (P.cell b) :=
          P.pairwiseDisjoint b.property.symm
        simpa only [cell] using
          hParentOld.mono (hChildSubsetParent a) Set.Subset.rfl
      · by_cases ha : a = 0
        · subst a
          by_cases hb : b = 0
          · subst b
            exact (hab rfl).elim
          · have hbOne : b = 1 := Fin.eq_one_of_ne_zero b hb
            subst b
            rw [hCellLeft, hCellRight]
            exact S.disjoint
        · have haOne : a = 1 := Fin.eq_one_of_ne_zero a ha
          subst a
          by_cases hb : b = 0
          · subst b
            rw [hCellRight, hCellLeft]
            exact S.disjoint.symm
          · have hbOne : b = 1 := Fin.eq_one_of_ne_zero b hb
            subst b
            exact (hab rfl).elim
  have hClosureUnion : (⋃ j, closure (cell j)) = closure U := by
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp hz
      rcases j with j | j
      · have hzOld : z ∈ ⋃ k, closure (P.cell k) :=
          Set.mem_iUnion.mpr ⟨j, by
            rw [hCellOld] at hzj
            exact hzj⟩
        rwa [P.closureUnion] at hzOld
      · have hzChildren : z ∈ closure S.left ∪ closure S.right := by
          by_cases hj : j = 0
          · subst j
            rw [hCellLeft] at hzj
            exact Or.inl hzj
          · have hjOne : j = 1 := Fin.eq_one_of_ne_zero j hj
            subst j
            rw [hCellRight] at hzj
            exact Or.inr hzj
        have hzParent : z ∈ closure (P.cell i) := by
          rwa [S.closureUnion] at hzChildren
        have hzOld : z ∈ ⋃ k, closure (P.cell k) :=
          Set.mem_iUnion.mpr ⟨i, hzParent⟩
        rwa [P.closureUnion] at hzOld
    · intro z hz
      have hzOld : z ∈ ⋃ j, closure (P.cell j) := by
        rw [P.closureUnion]
        exact hz
      obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp hzOld
      by_cases hji : j = i
      · subst j
        have hzChildren : z ∈ closure S.left ∪ closure S.right := by
          rw [S.closureUnion]
          exact hzj
        rcases hzChildren with hzLeft | hzRight
        · refine Set.mem_iUnion.mpr ⟨Sum.inr 0, ?_⟩
          rw [hCellLeft]
          exact hzLeft
        · refine Set.mem_iUnion.mpr ⟨Sum.inr 1, ?_⟩
          rw [hCellRight]
          exact hzRight
      · refine Set.mem_iUnion.mpr ⟨Sum.inl ⟨j, hji⟩, ?_⟩
        rw [hCellOld]
        exact hzj
  let Q : FiniteSphericalJordanPartition U
      (Sum {j : ι // j ≠ i} (Fin 2)) :=
    { cell := cell
      frontierSimple := hFrontier
      component := hComponent
      cellSubset := hSubset
      pairwiseDisjoint := hPairwise
      closureUnion := hClosureUnion }
  have hQCellOld (j : {j : ι // j ≠ i}) :
      Q.cell (Sum.inl j) = P.cell j := hCellOld j
  have hQCellLeft : Q.cell (Sum.inr 0) = S.left := hCellLeft
  have hQCellRight : Q.cell (Sum.inr 1) = S.right := hCellRight
  have hFiberClosureCover (r : ι) :
      (⋃ j : {j // parent j = r}, closure (Q.cell j)) =
        closure (P.cell r) := by
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨⟨j, hjr⟩, hzj⟩ := Set.mem_iUnion.mp hz
      rcases j with j | j
      · have hj : (j : ι) = r := by
          simpa only [parent] using hjr
        subst r
        rw [hQCellOld] at hzj
        exact hzj
      · have hir : i = r := by
          simpa only [parent] using hjr
        subst r
        have hzChildren : z ∈ closure S.left ∪ closure S.right := by
          by_cases hj : j = 0
          · subst j
            rw [hQCellLeft] at hzj
            exact Or.inl hzj
          · have hjOne : j = 1 := Fin.eq_one_of_ne_zero j hj
            subst j
            rw [hQCellRight] at hzj
            exact Or.inr hzj
        rwa [S.closureUnion] at hzChildren
    · intro z hz
      by_cases hri : r = i
      · subst r
        have hzChildren : z ∈ closure S.left ∪ closure S.right := by
          rw [S.closureUnion]
          exact hz
        rcases hzChildren with hzLeft | hzRight
        · refine Set.mem_iUnion.mpr ⟨⟨Sum.inr 0, ?_⟩, ?_⟩
          · simp only [parent]
          · rw [hQCellLeft]
            exact hzLeft
        · refine Set.mem_iUnion.mpr ⟨⟨Sum.inr 1, ?_⟩, ?_⟩
          · simp only [parent]
          · rw [hQCellRight]
            exact hzRight
      · refine Set.mem_iUnion.mpr
          ⟨⟨Sum.inl ⟨r, hri⟩, ?_⟩, ?_⟩
        · simp only [parent]
        · rw [hQCellOld]
          exact hz
  let R : FiniteSphericalJordanRefinement P Q :=
    { parent := parent
      fiberClosureCover := hFiberClosureCover }
  exact ⟨Q, ⟨R⟩, hQCellOld, hQCellLeft, hQCellRight⟩

/-- Helper for Theorem 63.6: subordination to uniformly small sets bounds
the diameters of every cell closure in a finite spherical Jordan partition. -/
private lemma FiniteSphericalJordanPartition.closureDiam_lt_of_subordinate
    {U : Set (StandardSphere 2)} {ι κ : Type*} [Fintype ι]
    (P : FiniteSphericalJordanPartition U ι)
    (K : κ → Set (StandardSphere 2)) {ε : ℝ}
    (hSubordinate : ∀ i, ∃ k, closure (P.cell i) ⊆ K k)
    (hSmall : ∀ k, Metric.diam (K k) < ε) :
    ∀ i, Metric.diam (closure (P.cell i)) < ε := by
  intro i
  obtain ⟨k, hik⟩ := hSubordinate i
  have hKBounded : Bornology.IsBounded (K k) :=
    isCompact_univ.isBounded.subset (Set.subset_univ (K k))
  -- Monotonicity of diameter transports the cover-member estimate to the cell.
  exact (Metric.diam_mono hik hKBounded).trans_lt (hSmall k)

/-- Helper for Theorem 63.6: every refined cell closure lies in the closure
of the parent cell selected by the refinement map. -/
private lemma FiniteSphericalJordanRefinement.cellClosureSubsetParent
    {U : Set (StandardSphere 2)} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {P : FiniteSphericalJordanPartition U ι}
    {Q : FiniteSphericalJordanPartition U κ}
    (R : FiniteSphericalJordanRefinement P Q) (j : κ) :
    closure (Q.cell j) ⊆ closure (P.cell (R.parent j)) := by
  intro z hz
  -- Insert the selected child into its parent's fiber union, then use the
  -- exact fiber-cover equation stored by the refinement.
  have hzFiber : z ∈
      ⋃ k : {k // R.parent k = R.parent j}, closure (Q.cell k) :=
    Set.mem_iUnion.mpr ⟨⟨j, rfl⟩, hz⟩
  rwa [R.fiberClosureCover (R.parent j)] at hzFiber

/-- Helper for Theorem 63.6: the fibers of two coherent refinements flatten
to the fiber of the composite parent map. -/
private lemma FiniteSphericalJordanRefinement.fiberClosureCover_trans
    {U : Set (StandardSphere 2)} {ι κ μ : Type*}
    [Fintype ι] [Fintype κ] [Fintype μ]
    {P : FiniteSphericalJordanPartition U ι}
    {Q : FiniteSphericalJordanPartition U κ}
    {T : FiniteSphericalJordanPartition U μ}
    (R₁ : FiniteSphericalJordanRefinement P Q)
    (R₂ : FiniteSphericalJordanRefinement Q T) (i : ι) :
    (⋃ k : {k // R₁.parent (R₂.parent k) = i}, closure (T.cell k)) =
      closure (P.cell i) := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨⟨k, hki⟩, hzk⟩ := Set.mem_iUnion.mp hz
    -- Successive child-containment projections place a fine cell in the
    -- closure of its ultimate parent.
    have hzParent : z ∈ closure (P.cell (R₁.parent (R₂.parent k))) :=
      R₁.cellClosureSubsetParent (R₂.parent k)
        (R₂.cellClosureSubsetParent k hzk)
    rwa [hki] at hzParent
  · intro z hz
    -- Expand the coarse fiber first and then the selected intermediate fiber.
    have hzMiddle : z ∈
        ⋃ j : {j // R₁.parent j = i}, closure (Q.cell j) := by
      rw [R₁.fiberClosureCover i]
      exact hz
    obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp hzMiddle
    have hzFine : z ∈
        ⋃ k : {k // R₂.parent k = j}, closure (T.cell k) := by
      rw [R₂.fiberClosureCover j]
      exact hzj
    obtain ⟨k, hzk⟩ := Set.mem_iUnion.mp hzFine
    refine Set.mem_iUnion.mpr ⟨⟨k, ?_⟩, hzk⟩
    calc
      R₁.parent (R₂.parent k) = R₁.parent j :=
        congrArg R₁.parent k.property
      _ = i := j.property

/-- Helper for Theorem 63.6: coherent finite spherical Jordan refinements
compose by composing their parent maps. -/
private def FiniteSphericalJordanRefinement.trans
    {U : Set (StandardSphere 2)} {ι κ μ : Type*}
    [Fintype ι] [Fintype κ] [Fintype μ]
    {P : FiniteSphericalJordanPartition U ι}
    {Q : FiniteSphericalJordanPartition U κ}
    {T : FiniteSphericalJordanPartition U μ}
    (R₁ : FiniteSphericalJordanRefinement P Q)
    (R₂ : FiniteSphericalJordanRefinement Q T) :
    FiniteSphericalJordanRefinement P T :=
  -- The companion lemma supplies the only nontrivial record field.
  { parent := fun k ↦ R₁.parent (R₂.parent k)
    fiberClosureCover := R₁.fiberClosureCover_trans R₂ }

/-- Helper for Theorem 63.6: an open cover of a compact spherical closure
admits a positive diameter scale subordinate to that cover. -/
private lemma existsDiameterSubordinationScale
    {κ : Type*} (U : Set (StandardSphere 2))
    (K : κ → Set (StandardSphere 2))
    (hOpen : ∀ k, IsOpen (K k))
    (hCover : closure U ⊆ ⋃ k, K k) :
    ∃ δ > 0, ∀ B : Set (StandardSphere 2), B.Nonempty →
      B ⊆ closure U → Metric.diam B < δ → ∃ k, B ⊆ K k := by
  obtain ⟨δ, hδ, hBall⟩ :=
    lebesgue_number_lemma_of_metric isClosed_closure.isCompact hOpen hCover
  refine ⟨δ, hδ, ?_⟩
  intro B hB hBU hDiam
  obtain ⟨x, hx⟩ := hB
  obtain ⟨k, hxBall⟩ := hBall x (hBU hx)
  refine ⟨k, ?_⟩
  intro y hy
  apply hxBall
  rw [Metric.mem_ball]
  -- Compactness of the ambient sphere bounds `B`, so its diameter controls
  -- every distance from the chosen center `x`.
  have hBounded : Bornology.IsBounded B :=
    isCompact_univ.isBounded.subset (Set.subset_univ B)
  exact (Metric.dist_le_diam_of_mem hBounded hy hx).trans_lt hDiam

/-- Helper for Theorem 63.6: a finite spherical Jordan partition whose leaf
closures are below a Lebesgue diameter scale is subordinate to the cover. -/
private lemma FiniteSphericalJordanPartition.subordinateOfClosureDiamLt
    {U : Set (StandardSphere 2)} {ι κ : Type*} [Fintype ι]
    (P : FiniteSphericalJordanPartition U ι)
    (K : κ → Set (StandardSphere 2))
    (hOpen : ∀ k, IsOpen (K k))
    (hCover : closure U ⊆ ⋃ k, K k) :
    ∃ δ > 0, (∀ i, Metric.diam (closure (P.cell i)) < δ) →
      ∀ i, ∃ k, closure (P.cell i) ⊆ K k := by
  obtain ⟨δ, hδ, hScale⟩ :=
    existsDiameterSubordinationScale U K hOpen hCover
  refine ⟨δ, hδ, ?_⟩
  intro hDiam i
  -- Each certified component is nonempty, lies in `U`, and hence its closure
  -- meets all hypotheses of the compact-metric scale lemma.
  exact hScale (closure (P.cell i))
    ((P.component i).nonempty.mono subset_closure)
    (closure_mono (P.cellSubset i)) (hDiam i)

/-- Helper for Theorem 63.6: the component containing zero in a bounded open
subset of the real line is a nondegenerate bounded open interval. -/
private lemma connectedLineSlice_eq_Ioo
    (A : Set ℝ) (hAopen : IsOpen A) (hAbounded : Bornology.IsBounded A)
    (hzero : 0 ∈ A) :
    ∃ a b : ℝ, a < 0 ∧ 0 < b ∧
      connectedComponentIn A 0 = Ioo a b ∧
      closure (connectedComponentIn A 0) = Icc a b := by
  -- First record the openness, connectedness, and boundedness of the selected component.
  let I : Set ℝ := connectedComponentIn A 0
  have hIconnected : IsConnected I := (isConnected_connectedComponentIn_iff).mpr hzero
  have hIopen : IsOpen I := hAopen.connectedComponentIn
  have hzeroI : 0 ∈ I := mem_connectedComponentIn hzero
  have hIbounded : Bornology.IsBounded I :=
    hAbounded.subset (connectedComponentIn_subset A 0)
  have hIbddBelow : BddBelow I := hIbounded.bddBelow
  have hIbddAbove : BddAbove I := hIbounded.bddAbove
  have hleft (z : ℝ) (hz : z ∈ I) : sInf I < z := by
    -- An open interval neighborhood supplies a component point strictly to the left.
    obtain ⟨l, u, hzlu, hlu⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp (hIopen.mem_nhds hz)
    obtain ⟨y, hly, hyz⟩ := exists_between hzlu.1
    exact lt_of_le_of_lt
      (csInf_le hIbddBelow (hlu ⟨hly, lt_trans hyz hzlu.2⟩)) hyz
  have hright (z : ℝ) (hz : z ∈ I) : z < sSup I := by
    -- The symmetric neighborhood argument supplies a component point to the right.
    obtain ⟨l, u, hzlu, hlu⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp (hIopen.mem_nhds hz)
    obtain ⟨y, hzy, hyu⟩ := exists_between hzlu.2
    exact lt_of_lt_of_le hzy
      (le_csSup hIbddAbove (hlu ⟨lt_trans hzlu.1 hzy, hyu⟩))
  have hIeq : I = Ioo (sInf I) (sSup I) := by
    -- Connectedness fills every real point between the two extremal bounds.
    apply Set.Subset.antisymm
    · exact fun z hz ↦ ⟨hleft z hz, hright z hz⟩
    · exact hIconnected.Ioo_csInf_csSup_subset hIbddBelow hIbddAbove
  have hIclosure : closure I = Icc (sInf I) (sSup I) := by
    -- Closing the nondegenerate interval adds precisely its two endpoints.
    calc
      closure I = closure (Ioo (sInf I) (sSup I)) := congrArg closure hIeq
      _ = Icc (sInf I) (sSup I) :=
        closure_Ioo (ne_of_lt (lt_trans (hleft 0 hzeroI) (hright 0 hzeroI)))
  exact ⟨sInf I, sSup I, hleft 0 hzeroI, hright 0 hzeroI, hIeq, hIclosure⟩

/-- Helper for Theorem 63.6: a nonconstant affine line through a point of a
bounded open set has an open bounded preimage containing zero. -/
private lemma affineLineSlice_open_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (hUopen : IsOpen U) (hUbounded : Bornology.IsBounded U)
    (x : E) (hx : x ∈ U) (v : E) (hv : v ≠ 0) :
    let line : ℝ → E := AffineMap.lineMap x (x + v)
    IsOpen (line ⁻¹' U) ∧ Bornology.IsBounded (line ⁻¹' U) ∧
      0 ∈ line ⁻¹' U ∧ Function.Injective line := by
  let line : ℝ → E := AffineMap.lineMap x (x + v)
  have hendpoint : x ≠ x + v := by
    -- Equality of the two line endpoints would force the direction to vanish.
    intro h
    apply hv
    simpa only [add_sub_cancel_left, sub_self] using
      congrArg (fun y ↦ y - x) h.symm
  refine ⟨hUopen.preimage AffineMap.lineMap_continuous, ?_, ?_, ?_⟩
  · exact (antilipschitzWith_lineMap hendpoint).isBounded_preimage hUbounded
  · simpa only [line, Set.mem_preimage, AffineMap.lineMap_apply_zero] using hx
  · exact (antilipschitzWith_lineMap hendpoint).injective

/-- Helper for Theorem 63.6: a nonconstant affine line cuts a maximal closed
parameter interval out of a bounded open domain. -/
private lemma affineLineComponent_eq_Ioo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (hUopen : IsOpen U) (hUbounded : Bornology.IsBounded U)
    (x : E) (hx : x ∈ U) (v : E) (hv : v ≠ 0) :
    let line : ℝ → E := AffineMap.lineMap x (x + v)
    ∃ a b : ℝ, a < 0 ∧ 0 < b ∧ Function.Injective line ∧
      connectedComponentIn (line ⁻¹' U) 0 = Ioo a b ∧
      closure (connectedComponentIn (line ⁻¹' U) 0) = Icc a b := by
  let line : ℝ → E := AffineMap.lineMap x (x + v)
  obtain ⟨hpreOpen, hpreBounded, hzero, hlineInjective⟩ :=
    affineLineSlice_open_bounded U hUopen hUbounded x hx v hv
  -- Apply the real-line component normal form to the affine preimage.
  obtain ⟨a, b, ha, hb, hcomponent, hclosure⟩ :=
    connectedLineSlice_eq_Ioo (line ⁻¹' U) hpreOpen hpreBounded hzero
  exact ⟨a, b, ha, hb, hlineInjective, hcomponent, hclosure⟩

/-- Helper for Theorem 63.6: every point of a bounded open set lies on a
straight Jordan crosscut with distinct frontier endpoints. -/
private lemma existsStraightJordanCrosscut
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (hUopen : IsOpen U) (hUbounded : Bornology.IsBounded U)
    (x : E) (hx : x ∈ U) (v : E) (hv : v ≠ 0) :
    ∃ p q : E, p ≠ q ∧ ∃ gamma : JordanCrosscut U p q, x ∈ gamma.carrier := by
  let line : ℝ → E := AffineMap.lineMap x (x + v)
  obtain ⟨a, b, ha, hb, hlineInjective, hcomponent, hclosure⟩ :=
    affineLineComponent_eq_Ioo U hUopen hUbounded x hx v hv
  have hab : a < b := ha.trans hb
  have hlineContinuous : Continuous line := AffineMap.lineMap_continuous
  let intervalLine : Icc a b → E := fun t ↦ line t
  have hintervalLineContinuous : Continuous intervalLine :=
    hlineContinuous.comp continuous_subtype_val
  have hintervalLineInjective : Function.Injective intervalLine :=
    hlineInjective.comp Subtype.val_injective
  let intervalEmbedding : Topology.IsEmbedding intervalLine :=
    (hintervalLineContinuous.isClosedEmbedding hintervalLineInjective).isEmbedding
  let parameterization : unitInterval ≃ₜ Set.range intervalLine :=
    (iccHomeoI a b hab).symm.trans intervalEmbedding.toHomeomorph
  have hcomponentImageSubset :
      line '' connectedComponentIn (line ⁻¹' U) 0 ⊆ U := by
    -- The selected real component is contained in the affine preimage of `U`.
    exact (image_mono (connectedComponentIn_subset (line ⁻¹' U) 0)).trans
      (image_preimage_subset line U)
  have hcarrierClosure : Set.range intervalLine ⊆ closure U := by
    rintro y ⟨t, rfl⟩
    have htClosure : (t : ℝ) ∈ closure (connectedComponentIn (line ⁻¹' U) 0) := by
      rw [hclosure]
      exact t.property
    -- Continuity carries the closed parameter interval into the domain closure.
    exact closure_mono hcomponentImageSubset
      (image_closure_subset_closure_image hlineContinuous ⟨t, htClosure, rfl⟩)
  have haNotMem : line a ∉ U := by
    intro haU
    have hsegmentSubset : Icc a 0 ⊆ line ⁻¹' U := by
      intro t ht
      rcases ht.1.eq_or_lt with rfl | hat
      · exact haU
      · apply connectedComponentIn_subset (line ⁻¹' U) 0
        rw [hcomponent]
        exact ⟨hat, lt_of_le_of_lt ht.2 hb⟩
    have haComponent : a ∈ connectedComponentIn (line ⁻¹' U) 0 :=
      isPreconnected_Icc.subset_connectedComponentIn
        (right_mem_Icc.mpr ha.le) hsegmentSubset (left_mem_Icc.mpr ha.le)
    rw [hcomponent] at haComponent
    exact (lt_irrefl a) haComponent.1
  have hbNotMem : line b ∉ U := by
    intro hbU
    have hsegmentSubset : Icc 0 b ⊆ line ⁻¹' U := by
      intro t ht
      rcases ht.2.lt_or_eq with htb | rfl
      · apply connectedComponentIn_subset (line ⁻¹' U) 0
        rw [hcomponent]
        exact ⟨lt_of_lt_of_le ha ht.1, htb⟩
      · exact hbU
    have hbComponent : b ∈ connectedComponentIn (line ⁻¹' U) 0 :=
      isPreconnected_Icc.subset_connectedComponentIn
        (left_mem_Icc.mpr hb.le) hsegmentSubset (right_mem_Icc.mpr hb.le)
    rw [hcomponent] at hbComponent
    exact (lt_irrefl b) hbComponent.2
  have haFrontier : line a ∈ frontier U := by
    -- The left endpoint lies in the closure but not in the open domain.
    rw [hUopen.frontier_eq]
    exact ⟨hcarrierClosure ⟨⟨a, le_rfl, hab.le⟩, rfl⟩, haNotMem⟩
  have hbFrontier : line b ∈ frontier U := by
    -- The right endpoint satisfies the symmetric frontier characterization.
    rw [hUopen.frontier_eq]
    exact ⟨hcarrierClosure ⟨⟨b, hab.le, le_rfl⟩, rfl⟩, hbNotMem⟩
  have hcarrierInterFrontier :
      Set.range intervalLine ∩ frontier U = {line a, line b} := by
    apply Set.Subset.antisymm
    · rintro y ⟨⟨t, rfl⟩, htFrontier⟩
      by_cases hta : (t : ℝ) = a
      · simpa only [intervalLine, hta] using Set.mem_insert (line a) {line b}
      · by_cases htb : (t : ℝ) = b
        · simpa only [intervalLine, htb] using
            Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton (line b)))
        · have hat : a < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm hta)
          have htb' : (t : ℝ) < b := lt_of_le_of_ne t.property.2 htb
          have htU : line t ∈ U := by
            apply connectedComponentIn_subset (line ⁻¹' U) 0
            rw [hcomponent]
            exact ⟨hat, htb'⟩
          have hcontra : line t ∈ U ∩ frontier U := ⟨htU, htFrontier⟩
          rw [hUopen.inter_frontier_eq] at hcontra
          exact hcontra.elim
    · rintro y (rfl | rfl)
      · exact ⟨⟨⟨a, le_rfl, hab.le⟩, rfl⟩, haFrontier⟩
      · exact ⟨⟨⟨b, hab.le, le_rfl⟩, rfl⟩, hbFrontier⟩
  have hparameterizationSource :
      (parameterization (0 : unitInterval) : E) = line a := by
    -- The interval homeomorphism sends zero to the left endpoint.
    simp only [parameterization, Homeomorph.trans_apply,
      Topology.IsEmbedding.toHomeomorph_apply_coe, intervalLine,
      iccHomeoI_symm_apply_coe, Set.Icc.coe_zero, mul_zero, zero_add]
  have hparameterizationTarget :
      (parameterization (1 : unitInterval) : E) = line b := by
    -- The interval homeomorphism sends one to the right endpoint.
    simp only [parameterization, Homeomorph.trans_apply,
      Topology.IsEmbedding.toHomeomorph_apply_coe, intervalLine,
      iccHomeoI_symm_apply_coe, Set.Icc.coe_one, mul_one]
    congr 1
    linarith
  let gamma : JordanCrosscut U (line a) (line b) :=
    { carrier := Set.range intervalLine
      parameterization := parameterization
      source_eq := hparameterizationSource
      target_eq := hparameterizationTarget
      carrier_subset_closure := hcarrierClosure
      carrier_inter_frontier := hcarrierInterFrontier }
  have hendpointsNe : line a ≠ line b :=
    hlineInjective.ne (ne_of_lt hab)
  refine ⟨line a, line b, hendpointsNe, gamma, ?_⟩
  -- Parameter zero realizes the original point on the crosscut.
  refine ⟨⟨0, ha.le, hb.le⟩, ?_⟩
  simp only [intervalLine, line, AffineMap.lineMap_apply_zero]

/-- Helper for Theorem 63.6: there is a point of the curve complement outside
the connected component containing a prescribed complement point. -/
private lemma exists_complementPoint_not_mem_component
    (C : Set (StandardSphere 2)) [Topology.IsSimpleClosedCurve C]
    (x : (Cᶜ : Set (StandardSphere 2))) :
    ∃ b : (Cᶜ : Set (StandardSphere 2)),
      (b : StandardSphere 2) ∉ connectedComponentIn Cᶜ x := by
  -- The Jordan separation theorem gives a second component class.
  classical
  have hcomponents : Cardinal.mk (ConnectedComponents (Cᶜ : Set (StandardSphere 2))) = 2 :=
    separatesInto_iff.mp (jordanCurveSphere_separatesInto C)
  obtain ⟨q, hqx, _⟩ := (Cardinal.mk_eq_two_iff' (ConnectedComponents.mk x)).mp hcomponents
  obtain ⟨b, rfl⟩ := ConnectedComponents.surjective_coe q
  refine ⟨b, ?_⟩
  -- Membership in the selected component would identify the two component classes.
  intro hb
  rw [connectedComponentIn_eq_image x.property] at hb
  obtain ⟨z, hz, hzb⟩ := hb
  have hzx : b ∈ connectedComponent x := by
    have hzb' : z = b := Subtype.ext hzb
    exact hzb' ▸ hz
  exact hqx (ConnectedComponents.coe_eq_coe'.mpr hzx)

/-- Helper for Theorem 63.6: a point of the curve complement outside a
complementary component also lies outside its closure. -/
private lemma not_mem_componentClosure_of_not_mem_component
    (C : Set (StandardSphere 2)) [Topology.IsSimpleClosedCurve C]
    (x b : (Cᶜ : Set (StandardSphere 2)))
    (hb : (b : StandardSphere 2) ∉ connectedComponentIn Cᶜ x) :
    (b : StandardSphere 2) ∉ closure (connectedComponentIn Cᶜ x) := by
  -- The closure is the component together with its frontier, which is exactly `C`.
  rw [closure_eq_self_union_frontier, jordanCurveSphere_frontier_component C x]
  exact fun hbUnion ↦ hbUnion.elim hb b.property

/-- Helper for Theorem 63.6: a simple closed curve is compact as an ambient
subset of the standard sphere. -/
private lemma isCompact_of_isSimpleClosedCurve_standardSphere
    (C : Set (StandardSphere 2)) [Topology.IsSimpleClosedCurve C] : IsCompact C := by
  -- Transfer compactness from the circle across the defining homeomorphism.
  classical
  obtain ⟨e⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := C)
  letI : CompactSpace C := e.symm.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

/-- Helper for Theorem 63.6: stereographic projection identifies the closure
of a set avoiding the puncture with the closure of its planar image. -/
private lemma componentClosureHomeomorphStereographicImage
    (U : Set (StandardSphere 2)) (b : StandardSphere 2)
    (hb : b ∉ closure U) :
    Nonempty
      (closure U ≃ₜ
        closure (StandardSphere.puncturedHomeomorphPlane b ''
          (Subtype.val ⁻¹' U))) := by
  -- Avoidance places the whole ambient closure in the punctured sphere.
  let h := StandardSphere.puncturedHomeomorphPlane b
  have hclosureSubset : closure U ⊆ ({b}ᶜ : Set (StandardSphere 2)) := by
    intro y hy
    simp only [mem_compl_iff, mem_singleton_iff]
    intro hyb
    exact hb (hyb ▸ hy)
  have hclosureRange : closure U ⊆ Set.range
      (Subtype.val : ({b}ᶜ : Set (StandardSphere 2)) → StandardSphere 2) := by
    intro y hy
    exact ⟨⟨y, hclosureSubset hy⟩, rfl⟩
  -- Openness of the punctured sphere makes closure commute with its subtype inclusion.
  have hpreimageClosure :
      closure (Subtype.val ⁻¹' U : Set ({b}ᶜ : Set (StandardSphere 2))) =
        Subtype.val ⁻¹' closure U := by
    apply Set.Subset.antisymm
    · exact continuous_subtype_val.closure_preimage_subset U
    · exact isOpen_compl_singleton.isOpenMap_subtype_val
        |>.preimage_closure_subset_closure_preimage
  -- Restrict the inclusion, normalize the closure, and then apply the chart.
  let toPunctured : closure U ≃ₜ
      (Subtype.val ⁻¹' closure U : Set ({b}ᶜ : Set (StandardSphere 2))) :=
    (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hclosureRange).symm
  let normalizeClosure :
      (Subtype.val ⁻¹' closure U : Set ({b}ᶜ : Set (StandardSphere 2))) ≃ₜ
        closure (Subtype.val ⁻¹' U : Set ({b}ᶜ : Set (StandardSphere 2))) :=
    Homeomorph.setCongr hpreimageClosure.symm
  let mapClosure := Homeomorph.image h
      (closure (Subtype.val ⁻¹' U : Set ({b}ᶜ : Set (StandardSphere 2))))
  let normalizeImage :
      (h '' closure (Subtype.val ⁻¹' U : Set ({b}ᶜ : Set (StandardSphere 2)))) ≃ₜ
        closure (h '' (Subtype.val ⁻¹' U : Set ({b}ᶜ : Set (StandardSphere 2)))) :=
    Homeomorph.setCongr (h.image_closure _)
  exact ⟨toPunctured.trans (normalizeClosure.trans (mapClosure.trans normalizeImage))⟩

/-- Helper for Theorem 63.6: stereographic projection carries a simple closed
curve avoiding the puncture to a planar simple closed curve. -/
private lemma stereographicImage_homeomorphic_circle
    (C : Set (StandardSphere 2)) [Topology.IsSimpleClosedCurve C]
    (b : StandardSphere 2) (hb : b ∉ C) :
    Nonempty
      ((StandardSphere.puncturedHomeomorphPlane b '' (Subtype.val ⁻¹' C)) ≃ₜ Circle) := by
  -- Restrict the punctured inclusion to the curve and compose with its circle model.
  have hCRange : C ⊆ Set.range
      (Subtype.val : ({b}ᶜ : Set (StandardSphere 2)) → StandardSphere 2) := by
    intro y hy
    exact ⟨⟨y, by simpa [Set.mem_compl_iff] using fun hyb : y = b ↦ hb (hyb ▸ hy)⟩, rfl⟩
  obtain ⟨eC⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := C)
  let ePreimage : (Subtype.val ⁻¹' C : Set ({b}ᶜ : Set (StandardSphere 2))) ≃ₜ C :=
    Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hCRange
  let h := StandardSphere.puncturedHomeomorphPlane b
  exact ⟨(Homeomorph.image h _).symm.trans (ePreimage.trans eC)⟩

/-- Helper for Theorem 63.6: summably bounded consecutive displacements make
a sequence of maps uniformly Cauchy. -/
private lemma uniformCauchySeqOn_of_summable_stepBound
    {X Y : Type*} [PseudoMetricSpace Y]
    (F : ℕ → X → Y) (d : ℕ → ℝ) (hd : Summable d)
    (hstep : ∀ n x, dist (F (n + 1) x) (F n x) ≤ d n) :
    UniformCauchySeqOn F atTop Set.univ := by
  -- The partial sums of the displacement majorant form a Cauchy sequence.
  have hpartial : CauchySeq (fun n ↦ ∑ k ∈ Finset.range n, d k) :=
    hd.hasSum.tendsto_sum_nat.cauchySeq
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hpartial ε hε
  refine ⟨N, ?_⟩
  intro m hm n hn x _
  -- On ordered indices, telescope the stage distances and compare with the
  -- corresponding difference of partial sums.
  have hordered (a b : ℕ) (ha : N ≤ a) (hb : N ≤ b) (hab : a ≤ b) :
      dist (F a x) (F b x) < ε := by
    have hsum :
        (∑ k ∈ Finset.Ico a b, d k) =
          (∑ k ∈ Finset.range b, d k) - ∑ k ∈ Finset.range a, d k := by
      rw [eq_sub_iff_add_eq]
      simpa only [add_comm] using Finset.sum_range_add_sum_Ico d hab
    calc
      dist (F a x) (F b x) ≤ ∑ k ∈ Finset.Ico a b, d k := by
        apply dist_le_Ico_sum_of_dist_le hab
        intro k _ _
        simpa only [Nat.add_comm, dist_comm] using hstep k x
      _ = (∑ k ∈ Finset.range b, d k) - ∑ k ∈ Finset.range a, d k := hsum
      _ ≤ |(∑ k ∈ Finset.range b, d k) - ∑ k ∈ Finset.range a, d k| :=
        le_abs_self _
      _ = dist (∑ k ∈ Finset.range a, d k) (∑ k ∈ Finset.range b, d k) := by
        rw [Real.dist_eq, abs_sub_comm]
      _ < ε := hN a ha b hb
  by_cases hmn : m ≤ n
  · exact hordered m n hm hn hmn
  · rw [dist_comm]
    exact hordered n m hn hm (Nat.le_of_not_ge hmn)

/-- Helper for Theorem 63.6: quantitative data for approximating one planar
circle embedding by ambient homeomorphisms along another. -/
private structure SummableAmbientApproximation
    (γ σ : Circle → EuclideanSpace ℝ (Fin 2)) where
  stage : ℕ → EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2)
  stepBound : ℕ → ℝ
  stepBound_nonneg : ∀ n, 0 ≤ stepBound n
  stepBound_summable : Summable stepBound
  forward_step : ∀ n x, dist (stage (n + 1) x) (stage n x) ≤ stepBound n
  inverse_step : ∀ n x, dist ((stage (n + 1)).symm x) ((stage n).symm x) ≤ stepBound n
  -- Route correction: pointwise trace convergence fixes a parameter orientation;
  -- the target only needs convergence of the underlying compact curve images.
  traceImage_tendsto :
    Tendsto
      (fun n ↦ Metric.hausdorffDist (Set.range (fun z ↦ stage n (γ z))) (Set.range σ))
      atTop (nhds 0)

/-- Helper for Theorem 63.6: corresponding pointwise bounds control the
Hausdorff distance between the two ranges. -/
private lemma hausdorffDist_range_le_of_forall_dist
    {X Y : Type*} [PseudoMetricSpace Y] (f g : X → Y) {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ x, dist (f x) (g x) ≤ ε) :
    Metric.hausdorffDist (Set.range f) (Set.range g) ≤ ε := by
  -- Use the point with the same parameter as the witness in the opposite range.
  apply Metric.hausdorffDist_le_of_mem_dist hε
  · rintro _ ⟨x, rfl⟩
    exact ⟨g x, Set.mem_range_self x, h x⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨f x, Set.mem_range_self x, by simpa only [dist_comm] using h x⟩

/-- Helper for Theorem 63.6: uniform convergence of maps implies convergence
of their ranges in Hausdorff distance. -/
private lemma tendsto_hausdorffDist_range_of_tendstoUniformly
    {I X Y : Type*} [PseudoMetricSpace Y] {l : Filter I}
    (F : I → X → Y) (f : X → Y) (hF : TendstoUniformly F f l) :
    Tendsto (fun i ↦ Metric.hausdorffDist (Set.range (F i)) (Set.range f)) l (nhds 0) := by
  -- At each sufficiently late index, the uniform pointwise estimate bounds
  -- the Hausdorff distance by half the requested radius.
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.mp hF) (ε / 2) (half_pos hε)] with i hi
  rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.hausdorffDist_nonneg]
  calc
    Metric.hausdorffDist (Set.range (F i)) (Set.range f) ≤ ε / 2 :=
      hausdorffDist_range_le_of_forall_dist (F i) f (half_pos hε).le
        (fun x ↦ by simpa only [dist_comm] using (hi x).le)
    _ < ε := half_lt_self hε

/-- Helper for Theorem 63.6: a uniform function limit and a Hausdorff image
limit have the same compact range. -/
private lemma range_eq_of_tendstoUniformly_of_tendsto_hausdorffDist
    {I X Y : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    [MetricSpace Y] {l : Filter I} [NeBot l]
    (F : I → X → Y) (f g : X → Y)
    (hFContinuous : ∀ i, Continuous (F i)) (hf : Continuous f) (hg : Continuous g)
    (hF : TendstoUniformly F f l)
    (hgRange : Tendsto
      (fun i ↦ Metric.hausdorffDist (Set.range (F i)) (Set.range g)) l (nhds 0)) :
    Set.range f = Set.range g := by
  -- Uniform convergence first gives Hausdorff convergence to the range of `f`.
  have hfRange : Tendsto
      (fun i ↦ Metric.hausdorffDist (Set.range f) (Set.range (F i))) l (nhds 0) := by
    simpa only [Metric.hausdorffDist_comm] using
      tendsto_hausdorffDist_range_of_tendstoUniformly F f hF
  have htriangle (i : I) :
      Metric.hausdorffDist (Set.range f) (Set.range g) ≤
        Metric.hausdorffDist (Set.range f) (Set.range (F i)) +
          Metric.hausdorffDist (Set.range (F i)) (Set.range g) := by
    -- Compactness makes the intermediate Hausdorff edistance finite.
    apply Metric.hausdorffDist_triangle
    exact Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
      (Set.range_nonempty f) (Set.range_nonempty (F i))
      (isCompact_range hf).isBounded (isCompact_range (hFContinuous i)).isBounded
  have hconstant : Tendsto
      (fun _ : I ↦ Metric.hausdorffDist (Set.range f) (Set.range g)) l (nhds 0) := by
    -- The triangle bound squeezes the fixed outer distance to zero.
    exact squeeze_zero (fun _ ↦ Metric.hausdorffDist_nonneg) htriangle
      (by simpa only [zero_add] using hfRange.add hgRange)
  have hzero : Metric.hausdorffDist (Set.range f) (Set.range g) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hconstant
  -- Closed compact ranges are determined by vanishing Hausdorff distance.
  have hfinite : Metric.hausdorffEDist (Set.range f) (Set.range g) ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
      (Set.range_nonempty f) (Set.range_nonempty g)
      (isCompact_range hf).isBounded (isCompact_range hg).isBounded
  exact ((isCompact_range hf).isClosed.hausdorffDist_zero_iff_eq
    (isCompact_range hg).isClosed hfinite).mp hzero

/-- Helper for Theorem 63.6: finite geometric data obtained by thickening a
fine cyclic mesh of one embedded planar circle and joining consecutive vertices
inside the corresponding thickening components. -/
private structure PreparedTraceMesh
    (g : Circle → EuclideanSpace ℝ (Fin 2)) (ε : ℝ) where
  n : ℕ
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt_scale : radius < ε / 3
  thickening_diam : ∀ i : Fin (n + 4),
    Metric.diam (Metric.thickening radius
      (g '' (Schoenflies.equalIntervalCircleMesh n).arc i)) < ε
  thickening_disjoint : ∀ i j : Fin (n + 4), i ≠ j →
    ¬(SimpleGraph.cycleGraph (n + 4)).Adj i j →
      Disjoint
        (Metric.thickening radius (g '' (Schoenflies.equalIntervalCircleMesh n).arc i))
        (Metric.thickening radius (g '' (Schoenflies.equalIntervalCircleMesh n).arc j))
  polygonallyJoined : ∀ i : Fin (n + 4),
    Schoenflies.IsPolygonallyJoinedIn
      (connectedComponentIn
        (Metric.thickening radius (g '' (Schoenflies.equalIntervalCircleMesh n).arc i))
        (g ((Schoenflies.equalIntervalCircleMesh n).vertex i)))
      (g ((Schoenflies.equalIntervalCircleMesh n).vertex i))
      (g ((Schoenflies.equalIntervalCircleMesh n).vertex (i + 1)))

/-- Helper for Theorem 63.6: every edge of a prepared mesh admits an embedded
arc inside its selected thickening component. -/
private lemma PreparedTraceMesh.existsEmbeddedArc
    {g : Circle → EuclideanSpace ℝ (Fin 2)} {ε : ℝ}
    (P : PreparedTraceMesh g ε) (hg : Topology.IsEmbedding g)
    (i : Fin (P.n + 4)) :
    ∃ alpha : Path
        (g ((Schoenflies.equalIntervalCircleMesh P.n).vertex i))
        (g ((Schoenflies.equalIntervalCircleMesh P.n).vertex (i + 1))),
      Topology.IsEmbedding alpha ∧
        Set.range alpha ⊆
          connectedComponentIn
            (Metric.thickening P.radius
              (g '' (Schoenflies.equalIntervalCircleMesh P.n).arc i))
            (g ((Schoenflies.equalIntervalCircleMesh P.n).vertex i)) := by
  -- A polygonal-join representative certifies that both prescribed endpoints
  -- already belong to the selected component.
  have hjoin := P.polygonallyJoined i
  obtain ⟨chain⟩ := hjoin.nonempty_chain
  have hstart := chain.start_mem
  have hend := chain.end_mem
  have hopen : IsOpen
      (connectedComponentIn
        (Metric.thickening P.radius
          (g '' (Schoenflies.equalIntervalCircleMesh P.n).arc i))
        (g ((Schoenflies.equalIntervalCircleMesh P.n).vertex i))) :=
    Schoenflies.isOpen_connectedComponentIn_of_isOpen Metric.isOpen_thickening _
  have hconnected : IsConnected
      (connectedComponentIn
        (Metric.thickening P.radius
          (g '' (Schoenflies.equalIntervalCircleMesh P.n).arc i))
        (g ((Schoenflies.equalIntervalCircleMesh P.n).vertex i))) := by
    -- Component nonemptiness follows from the stored membership of its basepoint.
    apply isConnected_connectedComponentIn_iff.mpr
    exact (connectedComponentIn_subset _ _) hstart
  have hendpoints :
      g ((Schoenflies.equalIntervalCircleMesh P.n).vertex i) ≠
        g ((Schoenflies.equalIntervalCircleMesh P.n).vertex (i + 1)) := by
    -- Injectivity of the trace transports distinctness of consecutive mesh vertices.
    intro heq
    apply Schoenflies.equalIntervalCircleVertex_ne_next P.n i
    rw [← Schoenflies.equalIntervalCircleMesh_vertex P.n i,
      ← Schoenflies.equalIntervalCircleMesh_vertex P.n (i + 1)]
    exact hg.injective heq
  exact Schoenflies.existsEmbeddedPathInOpenConnected _ hopen hconnected
    hstart hend hendpoints

/-- Helper for Theorem 63.6: embedded prepared arcs at distinct nonneighboring
indices have disjoint ranges. -/
private lemma PreparedTraceMesh.embeddedArcRanges_disjoint_of_not_adjacent
    {g : Circle → EuclideanSpace ℝ (Fin 2)} {ε : ℝ}
    (P : PreparedTraceMesh g ε)
    (arc : ∀ i : Fin (P.n + 4), Path
      (g ((Schoenflies.equalIntervalCircleMesh P.n).vertex i))
      (g ((Schoenflies.equalIntervalCircleMesh P.n).vertex (i + 1))))
    (harc : ∀ i, Set.range (arc i) ⊆
      connectedComponentIn
        (Metric.thickening P.radius
          (g '' (Schoenflies.equalIntervalCircleMesh P.n).arc i))
        (g ((Schoenflies.equalIntervalCircleMesh P.n).vertex i)))
    {i j : Fin (P.n + 4)} (hne : i ≠ j)
    (hnotAdjacent : ¬(SimpleGraph.cycleGraph (P.n + 4)).Adj i j) :
    Disjoint (Set.range (arc i)) (Set.range (arc j)) := by
  -- Component containment moves both ranges into the prepared thickenings,
  -- where the mesh's stored separation property applies.
  exact (P.thickening_disjoint i j hne hnotAdjacent).mono
    ((harc i).trans (connectedComponentIn_subset _ _))
    ((harc j).trans (connectedComponentIn_subset _ _))

/-- Helper for Theorem 63.6: every embedded planar trace admits separated,
small cyclic thickenings carrying polygonal joins between consecutive vertices. -/
private theorem existsPreparedTraceMesh
    (g : Circle → EuclideanSpace ℝ (Fin 2)) (hg : Topology.IsEmbedding g)
    {ε : ℝ} (hε : 0 < ε) : Nonempty (PreparedTraceMesh g ε) := by
  -- Choose trace arcs smaller than one third of the requested thickening scale.
  obtain ⟨n, htraceDiam⟩ := Schoenflies.existsFineEqualIntervalCircleMesh g
    hg.continuous (div_pos hε zero_lt_three)
  let M := Schoenflies.equalIntervalCircleMesh n
  let K : Fin (n + 4) → Set (EuclideanSpace ℝ (Fin 2)) := fun i ↦ g '' M.arc i
  let R : Fin (n + 4) → Fin (n + 4) → Prop := fun i j ↦
    i ≠ j ∧ ¬(SimpleGraph.cycleGraph (n + 4)).Adj i j
  have hcompact : ∀ i, IsCompact (K i) := by
    intro i
    exact (M.isCompact_arc i).image hg.continuous
  have hdisjoint : ∀ i j, R i j → Disjoint (K i) (K j) := by
    intro i j hij
    exact disjoint_image_of_injective hg.injective
      (M.disjoint_arc_of_not_adjacent i j hij.1 hij.2)
  have hdiam : ∀ i, Metric.diam (K i) < ε / 3 := by
    intro i
    simpa only [K, M, Schoenflies.equalIntervalCircleMesh_arc] using htraceDiam i
  obtain ⟨r, hr, hrε, hthickDisjoint⟩ :=
    Schoenflies.existsUniformThickeningRadius_lt K R hcompact hdisjoint
      (div_pos hε zero_lt_three)
  have hthickDiam : ∀ i, Metric.diam (Metric.thickening r (K i)) < ε := by
    intro i
    -- The stored radius bound is also sufficient for the standard thickening estimate.
    calc
      Metric.diam (Metric.thickening r (K i)) ≤ Metric.diam (K i) + 2 * r :=
        Metric.diam_thickening_le (K i) hr.le
      _ < ε := by linarith [hdiam i]
  refine Nonempty.intro {
    n := n
    radius := r
    radius_pos := hr
    radius_lt_scale := hrε
    thickening_diam := ?_
    thickening_disjoint := ?_
    polygonallyJoined := ?_
  }
  · intro i
    exact hthickDiam i
  · intro i j hne hnotAdj
    exact hthickDisjoint i j ⟨hne, hnotAdj⟩
  · intro i
    -- Connected trace arcs remain preconnected after applying the embedding;
    -- their two distinguished endpoints therefore admit a polygonal join.
    have hpreconnected : IsPreconnected (K i) :=
      ((M.isConnected_arc i).image g hg.continuous.continuousOn).isPreconnected
    have hstart : g (M.vertex i) ∈ K i :=
      Set.mem_image_of_mem g (M.vertex_mem_arc i)
    have hend : g (M.vertex (i + 1)) ∈ K i :=
      Set.mem_image_of_mem g (M.nextVertex_mem_arc i)
    exact Schoenflies.existsPolygonalChainInThickeningComponent hpreconnected hstart hend hr

/-- Helper for Theorem 63.6: a prescribed fine equal-interval mesh can be
thickened into prepared trace data without changing its mesh index. -/
private theorem existsPreparedTraceMeshAt
    (g : Circle → EuclideanSpace ℝ (Fin 2)) (hg : Topology.IsEmbedding g)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (htraceDiam : ∀ i : Fin (n + 4),
      Metric.diam (g '' (Schoenflies.equalIntervalCircleMesh n).arc i) < ε / 3) :
    ∃ P : PreparedTraceMesh g ε, P.n = n := by
  -- Keep the chosen mesh fixed while selecting one radius for all nonadjacent arcs.
  let M := Schoenflies.equalIntervalCircleMesh n
  let K : Fin (n + 4) → Set (EuclideanSpace ℝ (Fin 2)) := fun i ↦ g '' M.arc i
  let R : Fin (n + 4) → Fin (n + 4) → Prop := fun i j ↦
    i ≠ j ∧ ¬(SimpleGraph.cycleGraph (n + 4)).Adj i j
  have hcompact : ∀ i, IsCompact (K i) := by
    intro i
    exact (M.isCompact_arc i).image hg.continuous
  have hdisjoint : ∀ i j, R i j → Disjoint (K i) (K j) := by
    intro i j hij
    exact disjoint_image_of_injective hg.injective
      (M.disjoint_arc_of_not_adjacent i j hij.1 hij.2)
  have hdiam : ∀ i, Metric.diam (K i) < ε / 3 := by
    intro i
    simpa only [K, M, Schoenflies.equalIntervalCircleMesh_arc] using htraceDiam i
  obtain ⟨r, hr, hrε, hthickDisjoint⟩ :=
    Schoenflies.existsUniformThickeningRadius_lt K R hcompact hdisjoint
      (div_pos hε zero_lt_three)
  have hthickDiam : ∀ i, Metric.diam (Metric.thickening r (K i)) < ε := by
    intro i
    -- As above, retain the radius estimate while deriving the requested diameter bound.
    calc
      Metric.diam (Metric.thickening r (K i)) ≤ Metric.diam (K i) + 2 * r :=
        Metric.diam_thickening_le (K i) hr.le
      _ < ε := by linarith [hdiam i]
  refine ⟨{
    n := n
    radius := r
    radius_pos := hr
    radius_lt_scale := hrε
    thickening_diam := ?_
    thickening_disjoint := ?_
    polygonallyJoined := ?_
  }, rfl⟩
  · intro i
    exact hthickDiam i
  · intro i j hne hnotAdj
    exact hthickDisjoint i j ⟨hne, hnotAdj⟩
  · intro i
    -- The embedded trace arc lies in one component of its open thickening.
    have hpreconnected : IsPreconnected (K i) :=
      ((M.isConnected_arc i).image g hg.continuous.continuousOn).isPreconnected
    have hstart : g (M.vertex i) ∈ K i :=
      Set.mem_image_of_mem g (M.vertex_mem_arc i)
    have hend : g (M.vertex (i + 1)) ∈ K i :=
      Set.mem_image_of_mem g (M.nextVertex_mem_arc i)
    exact Schoenflies.existsPolygonalChainInThickeningComponent hpreconnected hstart hend hr

/-- Helper for Theorem 63.6: a diameter bound for a paired image bounds both
of its coordinate images. -/
private lemma coordinateImage_diam_lt_of_pairImage_diam_lt
    {ι X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : ι → X) (g : ι → Y) (s : Set ι) {ε : ℝ}
    (hbounded : Bornology.IsBounded ((fun z ↦ (f z, g z)) '' s))
    (hdiam : Metric.diam ((fun z ↦ (f z, g z)) '' s) < ε) :
    Metric.diam (f '' s) < ε ∧ Metric.diam (g '' s) < ε := by
  -- Rewrite each coordinate image as a Lipschitz projection of the paired image.
  have hfst : f '' s = Prod.fst '' ((fun z ↦ (f z, g z)) '' s) := by
    rw [Set.image_image]
  have hsnd : g '' s = Prod.snd '' ((fun z ↦ (f z, g z)) '' s) := by
    rw [Set.image_image]
  constructor
  · rw [hfst]
    calc
      Metric.diam (Prod.fst '' ((fun z ↦ (f z, g z)) '' s)) ≤
          1 * Metric.diam ((fun z ↦ (f z, g z)) '' s) :=
        LipschitzWith.prod_fst.diam_image_le _ hbounded
      _ = Metric.diam ((fun z ↦ (f z, g z)) '' s) := one_mul _
      _ < ε := hdiam
  · rw [hsnd]
    calc
      Metric.diam (Prod.snd '' ((fun z ↦ (f z, g z)) '' s)) ≤
          1 * Metric.diam ((fun z ↦ (f z, g z)) '' s) :=
        LipschitzWith.prod_snd.diam_image_le _ hbounded
      _ = Metric.diam ((fun z ↦ (f z, g z)) '' s) := one_mul _
      _ < ε := hdiam

/-- Helper for Theorem 63.6: two embedded traces admit prepared data at one
common equal-interval mesh index. -/
private theorem existsSynchronizedPreparedTraceMeshes
    (γ σ : Circle → EuclideanSpace ℝ (Fin 2))
    (hγ : Topology.IsEmbedding γ) (hσ : Topology.IsEmbedding σ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Pγ : PreparedTraceMesh γ ε, ∃ Pσ : PreparedTraceMesh σ ε, Pγ.n = Pσ.n := by
  -- A fine mesh for the product trace is simultaneously fine in both coordinates.
  let pairTrace : Circle →
      EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) := fun z ↦ (γ z, σ z)
  have hpairContinuous : Continuous pairTrace := hγ.continuous.prodMk hσ.continuous
  obtain ⟨n, hpairDiam⟩ := Schoenflies.existsFineEqualIntervalCircleMesh
    pairTrace hpairContinuous (div_pos hε zero_lt_three)
  let M := Schoenflies.equalIntervalCircleMesh n
  have hcoordinateDiam : ∀ i : Fin (n + 4),
      Metric.diam (γ '' M.arc i) < ε / 3 ∧
        Metric.diam (σ '' M.arc i) < ε / 3 := by
    intro i
    have hpairBounded : Bornology.IsBounded (pairTrace '' M.arc i) :=
      ((M.isCompact_arc i).image hpairContinuous).isBounded
    have hpairDiam' : Metric.diam (pairTrace '' M.arc i) < ε / 3 := by
      simpa only [pairTrace, M, Schoenflies.equalIntervalCircleMesh_arc] using hpairDiam i
    exact coordinateImage_diam_lt_of_pairImage_diam_lt γ σ (M.arc i) hpairBounded
      hpairDiam'
  obtain ⟨Pγ, hPγ⟩ := existsPreparedTraceMeshAt γ hγ hε n (fun i ↦ (hcoordinateDiam i).1)
  obtain ⟨Pσ, hPσ⟩ := existsPreparedTraceMeshAt σ hσ hε n (fun i ↦ (hcoordinateDiam i).2)
  exact ⟨Pγ, Pσ, hPγ.trans hPσ.symm⟩

/-- Helper for Theorem 63.6: uniform continuity on a compact set turns a
small source diameter into a prescribed image-diameter bound. -/
private lemma existsDiameterControlOnCompact
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (K : Set X) (hK : IsCompact K) (f : X → Y) (hf : ContinuousOn f K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ s : Set X, Bornology.IsBounded s → s ⊆ K →
      Metric.diam s ≤ ρ → Metric.diam (f '' s) ≤ ε := by
  -- First obtain a pointwise modulus on the compact domain.
  have huniform : UniformContinuousOn f K :=
    hK.uniformContinuousOn_of_continuous hf
  obtain ⟨δ, hδ, hclose⟩ :=
    Metric.uniformContinuousOn_iff_le.mp huniform ε hε
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  intro s hsBounded hsK hsDiam
  -- Halving the modulus leaves room to meet the pointwise bound supplied by
  -- uniform continuity.
  apply Metric.diam_le_of_forall_dist_le hε.le
  intro y hy y' hy'
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨x', hx', rfl⟩ := hy'
  apply hclose x (hsK hx) x' (hsK hx')
  calc
    dist x x' ≤ Metric.diam s :=
      Metric.dist_le_diam_of_mem hsBounded hx hx'
    _ ≤ δ / 2 := hsDiam
    _ ≤ δ := (half_le_self hδ.le)

/-- Helper for Theorem 63.6: a sufficiently thin metric thickening of a set
inside an open ball remains in a slightly larger closed ball. -/
private lemma thickening_subset_closedBall_of_subset_ball
    {X : Type*} [PseudoMetricSpace X] (s : Set X) (c : X)
    {R r a : ℝ} (hs : s ⊆ Metric.ball c R) (hr : r < a) :
    Metric.thickening r s ⊆ Metric.closedBall c (R + a) := by
  -- Pull a thickening point back to a nearby point of the core set and use
  -- the spare radial margin `a`.
  intro y hy
  obtain ⟨x, hx, hyx⟩ := Metric.mem_thickening_iff.mp hy
  rw [Metric.mem_closedBall]
  exact (calc
    dist y c ≤ dist y x + dist x c := dist_triangle _ _ _
    _ < r + R := add_lt_add hyx (hs hx)
    _ < a + R := by simpa only [add_comm] using add_lt_add_right hr R
    _ = R + a := add_comm _ _).le

/-- Helper for Theorem 63.6: a strict pointwise distance bound between two
continuous maps on a compact nonempty space has a smaller uniform scale. -/
private lemma existsSmallerUniformDistanceScale
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    [PseudoMetricSpace Y]
    (f g : X → Y) (hf : Continuous f) (hg : Continuous g)
    {η : ℝ} (hη : 0 < η) (hdist : ∀ z, dist (f z) (g z) < 2 * η) :
    ∃ η₀, 0 < η₀ ∧ η₀ < η ∧ ∀ z, dist (f z) (g z) < 2 * η₀ := by
  -- Attain the maximum of the continuous pointwise-distance function.
  obtain ⟨z, _, hz⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (hf.dist hg).continuousOn
  let η₀ := (dist (f z) (g z) + 2 * η) / 4
  have hmaxNonneg : 0 ≤ dist (f z) (g z) := dist_nonneg
  have hmaxLt : dist (f z) (g z) < 2 * η := hdist z
  have hη₀ : 0 < η₀ := by
    dsimp only [η₀]
    linarith
  have hη₀Lt : η₀ < η := by
    dsimp only [η₀]
    linarith
  refine ⟨η₀, hη₀, hη₀Lt, ?_⟩
  intro y
  -- The midpoint scale lies strictly above half the attained maximum.
  have hy : dist (f y) (g y) ≤ dist (f z) (g z) := hz (Set.mem_univ y)
  dsimp only [η₀]
  linarith


/-- Helper for Theorem 63.6: the forward and inverse stages of a summable
ambient approximation are uniformly Cauchy on the whole plane. -/
private lemma SummableAmbientApproximation.uniformCauchy
    {γ σ : Circle → EuclideanSpace ℝ (Fin 2)}
    (A : SummableAmbientApproximation γ σ) :
    UniformCauchySeqOn (fun n ↦ A.stage n) atTop Set.univ ∧
      UniformCauchySeqOn (fun n ↦ (A.stage n).symm) atTop Set.univ := by
  -- Apply the same summable telescoping estimate in both directions.
  constructor
  · exact uniformCauchySeqOn_of_summable_stepBound
      (fun n ↦ A.stage n) A.stepBound A.stepBound_summable A.forward_step
  · exact uniformCauchySeqOn_of_summable_stepBound
      (fun n ↦ (A.stage n).symm) A.stepBound A.stepBound_summable A.inverse_step

/-- Helper for Theorem 63.6: uniform limits of summably compatible ambient
homeomorphisms and their inverses form an ambient homeomorphism. -/
private lemma SummableAmbientApproximation.limitHomeomorph
    {γ σ : Circle → EuclideanSpace ℝ (Fin 2)}
    (A : SummableAmbientApproximation γ σ) :
    ∃ h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2),
      TendstoUniformly (fun n ↦ A.stage n) h atTop ∧
        TendstoUniformly (fun n ↦ (A.stage n).symm) h.symm atTop := by
  -- Completeness supplies pointwise limits of the two uniformly Cauchy families.
  classical
  obtain ⟨hforwardCauchy, hinverseCauchy⟩ := A.uniformCauchy
  choose f hf using fun x ↦
    cauchySeq_tendsto_of_complete (hforwardCauchy.cauchySeq (Set.mem_univ x))
  choose g hg using fun x ↦
    cauchySeq_tendsto_of_complete (hinverseCauchy.cauchySeq (Set.mem_univ x))
  have hfUniform : TendstoUniformly (fun n ↦ A.stage n) f atTop := by
    rw [← tendstoUniformlyOn_univ]
    exact hforwardCauchy.tendstoUniformlyOn_of_tendsto (fun x _ ↦ hf x)
  have hgUniform : TendstoUniformly (fun n ↦ (A.stage n).symm) g atTop := by
    rw [← tendstoUniformlyOn_univ]
    exact hinverseCauchy.tendstoUniformlyOn_of_tendsto (fun x _ ↦ hg x)
  -- Uniform limits of the continuous stages remain continuous.
  have hfContinuous : Continuous f :=
    hfUniform.continuous (Frequently.of_forall fun n ↦ (A.stage n).continuous)
  have hgContinuous : Continuous g :=
    hgUniform.continuous (Frequently.of_forall fun n ↦ (A.stage n).continuous_symm)
  -- Passing the stagewise inverse identities to the limit gives both inverse laws.
  have hgf (x : EuclideanSpace ℝ (Fin 2)) : g (f x) = x := by
    apply tendsto_nhds_unique
        (hgUniform.tendsto_comp hgContinuous.continuousAt (hf x))
    simpa only [Homeomorph.symm_apply_apply] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ x) atTop (𝓝 x))
  have hfg (x : EuclideanSpace ℝ (Fin 2)) : f (g x) = x := by
    apply tendsto_nhds_unique
        (hfUniform.tendsto_comp hfContinuous.continuousAt (hg x))
    simpa only [Homeomorph.apply_symm_apply] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ x) atTop (𝓝 x))
  let e : EuclideanSpace ℝ (Fin 2) ≃ EuclideanSpace ℝ (Fin 2) :=
    Equiv.mk f g hgf hfg
  let h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2) :=
    Homeomorph.mk e hfContinuous hgContinuous
  refine ⟨h, ?_, ?_⟩
  · simpa only [h, Homeomorph.homeomorph_mk_coe, e, Equiv.coe_fn_mk] using hfUniform
  · simpa only [h, Homeomorph.homeomorph_mk_coe_symm, e, Equiv.coe_fn_symm_mk] using hgUniform

/-- Helper for Theorem 63.6: the standard complex unit circle parameterizes
the Euclidean unit circle in real orthonormal coordinates. -/
private noncomputable def unitCircleParam :
    Circle → EuclideanSpace ℝ (Fin 2) :=
  fun z ↦ Complex.orthonormalBasisOneI.repr (z : ℂ)

/-- Helper for Theorem 63.6: the standard Euclidean unit-circle
parameterization is an embedding. -/
private lemma unitCircleParam_isEmbedding : Topology.IsEmbedding unitCircleParam := by
  -- Compose the circle subtype embedding with the ambient linear isometry.
  exact Complex.orthonormalBasisOneI.repr.toHomeomorph.isEmbedding.comp
    Topology.IsEmbedding.subtypeVal

/-- Helper for Theorem 63.6: inverse orthonormal coordinates of a Euclidean
unit vector define a point of the complex unit circle. -/
private lemma unitCircleParamPreimage_mem
    {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    Complex.orthonormalBasisOneI.repr.symm y ∈ Submonoid.unitSphere ℂ := by
  -- Norm preservation transports the Euclidean sphere equation back to `ℂ`.
  have hmem :
      Complex.orthonormalBasisOneI.repr.symm y ∈ Submonoid.unitSphere ℂ ↔
        ‖Complex.orthonormalBasisOneI.repr.symm y‖ = 1 := by
    exact ⟨fun h ↦ mem_sphere_zero_iff_norm.mp h,
      fun h ↦ mem_sphere_zero_iff_norm.mpr h⟩
  rw [hmem, LinearIsometryEquiv.norm_map]
  simpa only [Metric.mem_sphere, dist_zero_right] using hy

/-- Helper for Theorem 63.6: the range of the standard circle parameterization
is exactly the Euclidean unit sphere. -/
private lemma range_unitCircleParam :
    Set.range unitCircleParam = Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  -- Identify the range pointwise, using the inverse isometry for surjectivity.
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    rw [Metric.mem_sphere, dist_zero_right, unitCircleParam,
      LinearIsometryEquiv.norm_map]
    exact Circle.norm_coe z
  · intro hy
    let z : Circle :=
      ⟨Complex.orthonormalBasisOneI.repr.symm y, unitCircleParamPreimage_mem hy⟩
    refine ⟨z, ?_⟩
    exact Complex.orthonormalBasisOneI.repr.apply_symm_apply y

/-- Helper for Theorem 63.6: a self-homeomorphism of `B²` that fixes its
frontier extends by the identity to a homeomorphism of the Euclidean plane. -/
private theorem existsAmbientHomeomorphExtendingClosedUnitDiskHomeomorph
    (e : B² ≃ₜ B²)
    (hfrontier : ∀ x : B²,
      (x : EuclideanSpace ℝ (Fin 2)) ∈
          frontier (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) →
        (e x : EuclideanSpace ℝ (Fin 2)) = x) :
    ∃ h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2),
      ∀ x : B², h x = e x := by
  -- Regard the closed disk as a one-cell patch carrying the prescribed map.
  let cell : Fin 1 → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun _ ↦ Metric.closedBall 0 1
  let localEquiv : ∀ i, cell i ≃ₜ cell i := fun _ ↦ e
  have hclosed : ∀ i, IsClosed (cell i) := by
    intro i
    exact Metric.isClosed_closedBall
  have hforwardCompat : ∀ i j x (hxi : x ∈ cell i) (hxj : x ∈ cell j),
      (localEquiv i ⟨x, hxi⟩ : EuclideanSpace ℝ (Fin 2)) =
        (localEquiv j ⟨x, hxj⟩ : EuclideanSpace ℝ (Fin 2)) := by
    intro i j x hxi hxj
    have hij : i = j := Subsingleton.elim i j
    subst j
    have hx : (⟨x, hxi⟩ : cell i) = ⟨x, hxj⟩ :=
      SetCoe.ext (Eq.refl x)
    exact congrArg (fun y : cell i ↦ (localEquiv i y : EuclideanSpace ℝ (Fin 2))) hx
  have hinverseCompat : ∀ i j x (hxi : x ∈ cell i) (hxj : x ∈ cell j),
      ((localEquiv i).symm ⟨x, hxi⟩ : EuclideanSpace ℝ (Fin 2)) =
        ((localEquiv j).symm ⟨x, hxj⟩ : EuclideanSpace ℝ (Fin 2)) := by
    intro i j x hxi hxj
    have hij : i = j := Subsingleton.elim i j
    subst j
    have hx : (⟨x, hxi⟩ : cell i) = ⟨x, hxj⟩ :=
      SetCoe.ext (Eq.refl x)
    exact congrArg
      (fun y : cell i ↦ ((localEquiv i).symm y : EuclideanSpace ℝ (Fin 2))) hx
  have hfixFrontier : ∀ i x (hxi : x ∈ cell i)
      (_ : x ∈ frontier (⋃ i, cell i)),
      (localEquiv i ⟨x, hxi⟩ : EuclideanSpace ℝ (Fin 2)) = x := by
    intro i x hxi hxfrontier
    have hunion : (⋃ i, cell i) =
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      simp only [cell, iUnion_const]
    have hxfrontier' : x ∈
        frontier (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
      rwa [hunion] at hxfrontier
    have hxi' : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      simpa only [cell] using hxi
    let xDisk : B² := ⟨x, hxi'⟩
    have hxCell : (⟨x, hxi⟩ : cell i) = xDisk :=
      SetCoe.ext (Eq.refl x)
    calc
      (localEquiv i ⟨x, hxi⟩ : EuclideanSpace ℝ (Fin 2)) =
          (e xDisk : EuclideanSpace ℝ (Fin 2)) :=
        congrArg (fun y : B² ↦ (e y : EuclideanSpace ℝ (Fin 2))) hxCell
      _ = x := hfrontier xDisk hxfrontier'
  obtain ⟨P, _, hsupport, hforward, _⟩ :=
    Schoenflies.FiniteClosedCellPatch.ofLocalEquivsWithSpecs cell hclosed
      localEquiv hforwardCompat hinverseCompat hfixFrontier
  obtain ⟨h, honSupport, _, _, _⟩ := P.existsSupportedHomeomorph
  refine ⟨h, ?_⟩
  intro x
  -- On the disk cell, the supported ambient map computes to `e`.
  have hxCell : (x : EuclideanSpace ℝ (Fin 2)) ∈ cell 0 := by
    simpa only [cell] using x.property
  have hxSupport : (x : EuclideanSpace ℝ (Fin 2)) ∈ P.support := by
    rw [hsupport]
    exact Set.mem_iUnion_of_mem 0 hxCell
  have hxSubtype :
      (⟨(x : EuclideanSpace ℝ (Fin 2)), hxCell⟩ : cell 0) = x :=
    SetCoe.ext (Eq.refl (x : EuclideanSpace ℝ (Fin 2)))
  have hlocal :
      (localEquiv 0 ⟨(x : EuclideanSpace ℝ (Fin 2)), hxCell⟩ :
          EuclideanSpace ℝ (Fin 2)) = (e x : EuclideanSpace ℝ (Fin 2)) :=
    congrArg (fun y : B² ↦ (e y : EuclideanSpace ℝ (Fin 2))) hxSubtype
  calc
    h x = P.forward x := honSupport hxSupport
    _ = Schoenflies.FiniteClosedCellPatch.gluedForward cell localEquiv x :=
      congrFun hforward x
    _ = (localEquiv 0 ⟨(x : EuclideanSpace ℝ (Fin 2)), hxCell⟩ :
        EuclideanSpace ℝ (Fin 2)) :=
      Schoenflies.FiniteClosedCellPatch.gluedForward_eq_local cell localEquiv
        hforwardCompat 0 hxCell
    _ = e x := hlocal

/-- Helper for Theorem 63.6: one controlled paired-collar stage records the
exact finite-cell hypotheses needed for a quantitatively controlled refinement. -/
private structure ControlledPairedCollarStage
    (h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2))
    (γ β σ : Circle → EuclideanSpace ℝ (Fin 2)) (n : ℕ) (ε : ℝ) where
  collar : Schoenflies.FinitePairedRectangularCollar (fun z ↦ h (γ z)) β n
  targetCell_bounded : ∀ i, Bornology.IsBounded (collar.cell i)
  targetCell_diam : ∀ i, Metric.diam (collar.cell i) ≤ ε
  sourceCell_bounded : ∀ i, Bornology.IsBounded (h.symm '' collar.cell i)
  sourceCell_diam : ∀ i, Metric.diam (h.symm '' collar.cell i) ≤ ε
  trace_error : Metric.hausdorffDist (Set.range β) (Set.range σ) ≤ ε

/-- Helper for Theorem 63.6: a controlled paired-collar stage produces an
ambient refinement with exact trace and two-sided displacement control. -/
private lemma ControlledPairedCollarStage.existsRefinement
    {h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2)}
    {γ β σ : Circle → EuclideanSpace ℝ (Fin 2)} {n : ℕ} {ε : ℝ}
    (P : ControlledPairedCollarStage h γ β σ n ε) (hε : 0 ≤ ε) :
    ∃ h' : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2),
      (∀ z, h' (γ z) = β z) ∧
        (∀ x, dist (h' x) (h x) ≤ ε) ∧
        ∀ y, dist (h'.symm y) (h.symm y) ≤ ε := by
  -- The prepared interface is deliberately identical to the quantitative
  -- hypotheses of the finite paired-collar refinement theorem.
  exact P.collar.refineAmbientHomeomorphAlongPairedCollar h ε hε
    P.targetCell_bounded P.targetCell_diam
    P.sourceCell_bounded P.sourceCell_diam

/-- Helper for Theorem 63.6: nested polygonal collars give a summably controlled
ambient approximation from the standard circle to a planar Jordan trace. -/
private theorem existsSummableAmbientApproximationFromPolygonalCollars
    (σ : Circle → EuclideanSpace ℝ (Fin 2)) (hσ : Topology.IsEmbedding σ) :
    Nonempty (SummableAmbientApproximation unitCircleParam σ) := by
  -- Route correction: the paired-collar route requires unavailable nested grid
  -- disks. The crosscut lemmas above instead provide exact side Jordan curves.
  -- TODO: construct finite binary refinements with arbitrarily small leaf closures,
  -- then use coherent nested addresses to build the ambient straightening.
  sorry

/-- Helper for Theorem 63.6: the limit of a summable ambient approximation maps
the source trace range exactly onto its prescribed Hausdorff image limit. -/
private lemma SummableAmbientApproximation.existsLimitHomeomorph_image_sourceRange
    {γ σ : Circle → EuclideanSpace ℝ (Fin 2)}
    (A : SummableAmbientApproximation γ σ)
    (hγ : Continuous γ) (hσ : Continuous σ) :
    ∃ h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2),
      h '' Set.range γ = Set.range σ := by
  -- First take the common uniform limit of the forward stages and their inverses.
  obtain ⟨h, hforward, _⟩ := A.limitHomeomorph
  have htraceLimit : TendstoUniformly
      (fun n z ↦ A.stage n (γ z)) (fun z ↦ h (γ z)) atTop := by
    rw [Metric.tendstoUniformly_iff] at hforward ⊢
    intro ε hε
    filter_upwards [hforward ε hε] with n hn
    exact fun z ↦ hn (γ z)
  -- The uniform trace limit and the stored Hausdorff limit have the same range.
  have hrange : Set.range (fun z ↦ h (γ z)) = Set.range σ :=
    range_eq_of_tendstoUniformly_of_tendsto_hausdorffDist
      (fun n z ↦ A.stage n (γ z)) (fun z ↦ h (γ z)) σ
      (fun n ↦ (A.stage n).continuous.comp hγ)
      (h.continuous.comp hγ) hσ htraceLimit A.traceImage_tendsto
  refine ⟨h, ?_⟩
  -- Rewrite the parameterized range as the image of the source range.
  exact (Set.range_comp' h γ).symm.trans hrange

/-- Helper for Theorem 63.6: the images of any two planar circle embeddings are
related by an ambient homeomorphism of the plane. -/
private theorem existsAmbientHomeomorphImageCircleEmbeddings
    (α β : Circle → EuclideanSpace ℝ (Fin 2))
    (hα : Topology.IsEmbedding α) (hβ : Topology.IsEmbedding β) :
    ∃ h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2),
      h '' Set.range α = Set.range β := by
  -- Straighten both traces through the common standard circle using their
  -- independently constructed summable collar approximations.
  obtain ⟨Aα⟩ := existsSummableAmbientApproximationFromPolygonalCollars α hα
  obtain ⟨Aβ⟩ := existsSummableAmbientApproximationFromPolygonalCollars β hβ
  obtain ⟨kα, hkα⟩ :=
    Aα.existsLimitHomeomorph_image_sourceRange unitCircleParam_isEmbedding.continuous
      hα.continuous
  obtain ⟨kβ, hkβ⟩ :=
    Aβ.existsLimitHomeomorph_image_sourceRange unitCircleParam_isEmbedding.continuous
      hβ.continuous
  have hkαInverse : kα.symm '' Set.range α = Set.range unitCircleParam := by
    calc
      kα.symm '' Set.range α =
          kα.symm '' (kα '' Set.range unitCircleParam) :=
        congrArg (fun S ↦ kα.symm '' S) hkα.symm
      _ = Set.range unitCircleParam := kα.toEquiv.symm_image_image _
  refine ⟨kα.symm.trans kβ, ?_⟩
  -- Composition first returns the source image to the standard circle and
  -- then applies the independent straightening of the target image.
  calc
    (kα.symm.trans kβ) '' Set.range α =
        kβ '' (kα.symm '' Set.range α) := by
      rw [Set.image_image]
      rfl
    _ = kβ '' Set.range unitCircleParam :=
      congrArg (fun S ↦ kβ '' S) hkαInverse
    _ = Set.range β := hkβ

/-- Helper for Theorem 63.6: every planar simple closed curve can be carried
onto the Euclidean unit circle by an ambient homeomorphism of the plane. -/
private theorem existsAmbientHomeomorph_image_eq_unitCircle
    (D : Set (EuclideanSpace ℝ (Fin 2))) [Topology.IsSimpleClosedCurve D] :
    ∃ h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2),
      h '' D = Metric.sphere 0 1 := by
  -- Parameterize the source curve and the standard unit circle by `Circle`.
  classical
  obtain ⟨eD⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := D)
  let γ : Circle → EuclideanSpace ℝ (Fin 2) := fun z ↦ (eD.symm z : EuclideanSpace ℝ (Fin 2))
  have hγ : Topology.IsEmbedding γ :=
    Topology.IsEmbedding.subtypeVal.comp eD.symm.isEmbedding
  have hγRange : Set.range γ = D := by
    exact eD.symm.surjective.range_comp
      (fun p : D ↦ (p : EuclideanSpace ℝ (Fin 2))) |>.trans Subtype.range_coe
  -- Apply the image-level ambient extension to the two chosen parameterizations.
  obtain ⟨h, hh⟩ := existsAmbientHomeomorphImageCircleEmbeddings γ unitCircleParam
    hγ unitCircleParam_isEmbedding
  -- Equality of compact trace ranges identifies the two image sets.
  refine ⟨h, ?_⟩
  calc
    h '' D = h '' Set.range γ := congrArg (fun S ↦ h '' S) hγRange.symm
    _ = Set.range unitCircleParam := hh
    _ = Metric.sphere 0 1 := range_unitCircleParam

/-- Helper for Theorem 63.6: an ambient homeomorphism of the Euclidean plane
carries bounded sets to bounded sets. -/
private lemma isBounded_image_planeHomeomorph
    (h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2))
    {W : Set (EuclideanSpace ℝ (Fin 2))} (hW : Bornology.IsBounded W) :
    Bornology.IsBounded (h '' W) := by
  -- Compactify the bounded set before applying the merely continuous map.
  have hcompact : IsCompact (closure W) := hW.isCompact_closure
  have himageCompact : IsCompact (h '' closure W) := hcompact.image h.continuous
  -- The original image lies in that compact, hence bounded, image.
  exact himageCompact.isBounded.subset (Set.image_mono subset_closure)

/-- Helper for Theorem 63.6: inverse-norm rescaling puts every nonzero vector
on the unit sphere. -/
private lemma invNorm_smul_mem_unitSphere
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (hx : x ≠ 0) : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : E) 1 := by
  -- Norm multiplicativity reduces the assertion to cancellation of `‖x‖`.
  rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

/-- Helper for Theorem 63.6: the exterior of the closed unit ball in a real
normed space of dimension greater than one is connected. -/
private lemma isConnected_compl_closedUnitBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hrank : 1 < Module.rank ℝ E) :
    IsConnected (Metric.closedBall (0 : E) 1)ᶜ := by
  -- Polar coordinates present the exterior as positive radial scalings of the sphere.
  let radialDomain : Set (Metric.sphere (0 : E) 1 × ℝ) :=
    Set.univ ×ˢ Set.Ioi 1
  let radialMap : Metric.sphere (0 : E) 1 × ℝ → E :=
    fun p ↦ p.2 • (p.1 : E)
  have hdomain : IsConnected radialDomain := by
    letI : ConnectedSpace (Metric.sphere (0 : E) 1) :=
      Subtype.connectedSpace (isConnected_sphere hrank 0 zero_le_one)
    exact isConnected_univ.prod (isConnected_Ioi (a := (1 : ℝ)))
  have hcontinuous : ContinuousOn radialMap radialDomain := by
    have hradialContinuous : Continuous radialMap :=
      continuous_snd.smul (continuous_subtype_val.comp continuous_fst)
    exact hradialContinuous.continuousOn
  have himage : radialMap '' radialDomain = (Metric.closedBall (0 : E) 1)ᶜ := by
    apply Set.Subset.antisymm
    · rintro x ⟨⟨u, r⟩, ⟨_, hr⟩, rfl⟩
      -- A radius greater than one lies strictly outside the closed unit ball.
      change 1 < r at hr
      rw [Set.mem_compl_iff, Metric.mem_closedBall, not_le, dist_zero_right, norm_smul]
      rw [Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hr)]
      have huNorm : ‖(u : E)‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using u.property
      rwa [huNorm, mul_one]
    · intro x hx
      -- Normalize an exterior point and retain its norm as the radial coordinate.
      have hxNorm : 1 < ‖x‖ := by
        simpa only [Set.mem_compl_iff, Metric.mem_closedBall, not_le, dist_zero_right]
          using hx
      have hxNe : x ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hxNorm)
      let u : Metric.sphere (0 : E) 1 :=
        ⟨‖x‖⁻¹ • x, invNorm_smul_mem_unitSphere x hxNe⟩
      refine ⟨(u, ‖x‖), ⟨Set.mem_univ _, hxNorm⟩, ?_⟩
      change ‖x‖ • (‖x‖⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hxNe), one_smul]
  -- Connectedness is preserved by the continuous radial image.
  rw [← himage]
  exact hdomain.image radialMap hcontinuous

/-- Helper for Theorem 63.6: the open unit disk and the exterior of the closed
unit disk are the two components of the unit-circle complement. -/
private lemma unitCircle_complementComponents :
    IsConnectedComponentIn
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ
        (Metric.ball 0 1) ∧
      IsConnectedComponentIn
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ
        (Metric.closedBall 0 1)ᶜ := by
  have hdecomp :
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ =
        Metric.ball 0 1 ∪ (Metric.closedBall 0 1)ᶜ := by
    calc
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ =
          (frontier (Metric.closedBall 0 1))ᶜ :=
        congrArg (fun S : Set (EuclideanSpace ℝ (Fin 2)) ↦ Sᶜ)
          (frontier_closedBall 0 one_ne_zero).symm
      _ = interior (Metric.closedBall 0 1) ∪
          interior (Metric.closedBall 0 1)ᶜ := compl_frontier_eq_union_interior
      _ = Metric.ball 0 1 ∪ (Metric.closedBall 0 1)ᶜ := by
        rw [interior_closedBall 0 one_ne_zero,
          Metric.isClosed_closedBall.isOpen_compl.interior_eq]
  have hballSubset : Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ := by
    rw [hdecomp]
    exact subset_union_left
  have hexteriorSubset : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ ⊆
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ := by
    rw [hdecomp]
    exact subset_union_right
  have hsidesDisjoint : Disjoint
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)
      (Metric.closedBall 0 1)ᶜ := by
    rw [Set.disjoint_left]
    exact fun _ hxBall hxExterior ↦ hxExterior (Metric.ball_subset_closedBall hxBall)
  have hballConnected : IsConnected
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) := Metric.isConnected_ball one_pos
  have hexteriorConnected : IsConnected
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ := by
    apply isConnected_compl_closedUnitBall
    rw [← Module.finrank_eq_rank]
    norm_num
  constructor
  · -- The component through zero cannot cross from the disk to the exterior.
    have hzero : (0 : EuclideanSpace ℝ (Fin 2)) ∈ Metric.ball 0 1 :=
      Metric.mem_ball_self one_pos
    have hballEq : Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 =
        connectedComponentIn (Metric.sphere 0 1)ᶜ 0 := by
      have hcomponentSubset : connectedComponentIn
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ
          (0 : EuclideanSpace ℝ (Fin 2)) ⊆
          Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∪
            (Metric.closedBall 0 1)ᶜ := by
        exact (connectedComponentIn_subset
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ
          (0 : EuclideanSpace ℝ (Fin 2))).trans hdecomp.le
      have hcomponentPreconnected : IsPreconnected
          (connectedComponentIn
            (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ 0) :=
        isPreconnected_connectedComponentIn
      apply Set.Subset.antisymm
      · exact hballConnected.isPreconnected.subset_connectedComponentIn hzero hballSubset
      · obtain hsubsetBall | hsubsetExterior :=
          hcomponentPreconnected.subset_or_subset Metric.isOpen_ball
            Metric.isClosed_closedBall.isOpen_compl hsidesDisjoint
            hcomponentSubset
        · exact hsubsetBall
        · exact False.elim
            (hsidesDisjoint.le_bot
              ⟨hzero, hsubsetExterior (mem_connectedComponentIn (hballSubset hzero))⟩)
    rw [hballEq]
    exact IsConnectedComponentIn.of_mem (hballSubset hzero)
  · -- Any exterior point similarly determines the whole connected exterior side.
    obtain ⟨x, hxExterior⟩ := hexteriorConnected.nonempty
    have hexteriorEq : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ =
        connectedComponentIn (Metric.sphere 0 1)ᶜ x := by
      have hcomponentSubset : connectedComponentIn (Metric.sphere 0 1)ᶜ x ⊆
          Metric.ball 0 1 ∪ (Metric.closedBall 0 1)ᶜ := by
        exact (connectedComponentIn_subset _ _).trans hdecomp.le
      apply Set.Subset.antisymm
      · exact hexteriorConnected.isPreconnected.subset_connectedComponentIn
          hxExterior hexteriorSubset
      · obtain hsubsetBall | hsubsetExterior :=
          isPreconnected_connectedComponentIn.subset_or_subset Metric.isOpen_ball
            Metric.isClosed_closedBall.isOpen_compl hsidesDisjoint
            hcomponentSubset
        · exact False.elim
            (hsidesDisjoint.le_bot
              ⟨hsubsetBall (mem_connectedComponentIn (hexteriorSubset hxExterior)), hxExterior⟩)
        · exact hsubsetExterior
    rw [hexteriorEq]
    exact IsConnectedComponentIn.of_mem (hexteriorSubset hxExterior)

/-- Helper for Theorem 63.6: in a nontrivial normed space, a set with bounded
complement is unbounded. -/
private lemma not_isBounded_of_isBounded_compl
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    {S : Set E} (hSc : Bornology.IsBounded Sᶜ) : ¬ Bornology.IsBounded S := by
  -- Boundedness of both sides would make the entire normed space bounded.
  intro hS
  have huniv : Bornology.IsBounded (Set.univ : Set E) := by
    rw [← union_compl_self S]
    exact hS.union hSc
  exact NormedSpace.unbounded_univ ℝ E huniv

/-- Helper for Theorem 63.6: every bounded component of the unit-circle
complement is the open unit disk. -/
private lemma boundedUnitCircleComponent_eq_ball
    (W : Set (EuclideanSpace ℝ (Fin 2)))
    (hW : IsConnectedComponentIn (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ W)
    (hWbounded : Bornology.IsBounded W) : W = Metric.ball 0 1 := by
  have hdecomp :
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ =
        Metric.ball 0 1 ∪ (Metric.closedBall 0 1)ᶜ := by
    calc
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ =
          (frontier (Metric.closedBall 0 1))ᶜ :=
        congrArg (fun S : Set (EuclideanSpace ℝ (Fin 2)) ↦ Sᶜ)
          (frontier_closedBall 0 one_ne_zero).symm
      _ = interior (Metric.closedBall 0 1) ∪
          interior (Metric.closedBall 0 1)ᶜ := compl_frontier_eq_union_interior
      _ = Metric.ball 0 1 ∪ (Metric.closedBall 0 1)ᶜ := by
        rw [interior_closedBall 0 one_ne_zero,
          Metric.isClosed_closedBall.isOpen_compl.interior_eq]
  have hsidesDisjoint : Disjoint
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)
      (Metric.closedBall 0 1)ᶜ := by
    rw [Set.disjoint_left]
    exact fun _ hxBall hxExterior ↦ hxExterior (Metric.ball_subset_closedBall hxBall)
  have hWsubsetUnion : W ⊆
      Metric.ball 0 1 ∪ (Metric.closedBall 0 1)ᶜ := by
    rw [← hdecomp]
    exact hW.subset
  obtain hWinterior | hWexterior :=
      IsPreconnected.subset_or_subset Metric.isOpen_ball
        Metric.isClosed_closedBall.isOpen_compl hsidesDisjoint
        hWsubsetUnion hW.isConnected.isPreconnected
  · -- Meeting the disk identifies `W` with the canonical disk component.
    obtain ⟨w, hwW⟩ := hW.nonempty
    have hwBall := hWinterior hwW
    calc
      W = connectedComponentIn (Metric.sphere 0 1)ᶜ w :=
        hW.eq_connectedComponentIn hwW
      _ = Metric.ball 0 1 :=
        (unitCircle_complementComponents.1.eq_connectedComponentIn hwBall).symm
  · -- Equality with the exterior contradicts boundedness of `W`.
    obtain ⟨w, hwW⟩ := hW.nonempty
    have hwExterior := hWexterior hwW
    have hWexteriorEq : W = (Metric.closedBall 0 1)ᶜ := by
      calc
        W = connectedComponentIn (Metric.sphere 0 1)ᶜ w :=
          hW.eq_connectedComponentIn hwW
        _ = (Metric.closedBall 0 1)ᶜ :=
          (unitCircle_complementComponents.2.eq_connectedComponentIn hwExterior).symm
    have hcomplementBounded : Bornology.IsBounded
        ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ)ᶜ := by
      simpa only [compl_compl] using
        (Metric.isBounded_closedBall : Bornology.IsBounded
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1))
    exact False.elim
      (not_isBounded_of_isBounded_compl hcomplementBounded (hWexteriorEq ▸ hWbounded))

/-- Helper for Remark 65.1: an ambient straightening of a planar Jordan curve
also carries a selected bounded complementary component to the open unit disk. -/
theorem Topology.IsSimpleClosedCurve.existsAmbientHomeomorph_maps_boundedComponentToUnitBall
    (D : Set (EuclideanSpace ℝ (Fin 2))) [Topology.IsSimpleClosedCurve D]
    (p : (Dᶜ : Set (EuclideanSpace ℝ (Fin 2))))
    (hbounded : Bornology.IsBounded (connectedComponentIn Dᶜ p)) :
    ∃ h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2),
      h '' D = Metric.sphere 0 1 ∧
        h '' connectedComponentIn Dᶜ p = Metric.ball 0 1 := by
  -- Straighten the curve using the ambient Schoenflies construction.
  obtain ⟨h, hD⟩ := existsAmbientHomeomorph_image_eq_unitCircle D
  have hpImageComplement : h p ∈
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ := by
    rw [← hD, ← h.image_compl]
    exact Set.mem_image_of_mem h p.property
  have himageComponent : h '' connectedComponentIn Dᶜ p =
      connectedComponentIn
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ (h p) := by
    calc
      h '' connectedComponentIn Dᶜ p =
          connectedComponentIn (h '' Dᶜ) (h p) :=
        h.image_connectedComponentIn p.property
      _ = connectedComponentIn (Metric.sphere 0 1)ᶜ (h p) := by
        rw [h.image_compl, hD]
  have hcomponent : IsConnectedComponentIn
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ
      (h '' connectedComponentIn Dᶜ p) := by
    rw [himageComponent]
    exact IsConnectedComponentIn.of_mem hpImageComplement
  have himageBounded : Bornology.IsBounded
      (h '' connectedComponentIn Dᶜ p) :=
    isBounded_image_planeHomeomorph h hbounded
  -- The bounded side of the standard unit circle is uniquely the open unit disk.
  refine ⟨h, hD, ?_⟩
  exact boundedUnitCircleComponent_eq_ball
    (h '' connectedComponentIn Dᶜ p) hcomponent himageBounded

/-- Helper for Theorem 63.6: the closure of a bounded complementary component
of a planar simple closed curve is homeomorphic to the closed unit disk. -/
private theorem boundedJordanComponentClosure_homeomorph_closedUnitDisk
    (D W : Set (EuclideanSpace ℝ (Fin 2))) [Topology.IsSimpleClosedCurve D]
    (hW : IsConnectedComponentIn Dᶜ W) (hWbounded : Bornology.IsBounded W) :
    Nonempty (closure W ≃ₜ B²) := by
  -- Straighten the curve and transport the chosen component to the standard circle.
  obtain ⟨h, hD⟩ := existsAmbientHomeomorph_image_eq_unitCircle D
  obtain ⟨w, hwW⟩ := hW.nonempty
  have hwComplement : w ∈ Dᶜ := hW.subset hwW
  have hWcomponent : W = connectedComponentIn Dᶜ w :=
    hW.eq_connectedComponentIn hwW
  have hwImageComplement : h w ∈
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ := by
    rw [← hD, ← h.image_compl]
    exact Set.mem_image_of_mem h hwComplement
  have himageEqComponent : h '' W =
      connectedComponentIn (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ (h w) := by
    calc
      h '' W = h '' connectedComponentIn Dᶜ w := congrArg (fun S ↦ h '' S) hWcomponent
      _ = connectedComponentIn (h '' Dᶜ) (h w) :=
        h.image_connectedComponentIn hwComplement
      _ = connectedComponentIn (Metric.sphere 0 1)ᶜ (h w) := by
        rw [h.image_compl, hD]
  have himageComponent : IsConnectedComponentIn
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ (h '' W) := by
    rw [himageEqComponent]
    exact IsConnectedComponentIn.of_mem hwImageComplement
  have himageBounded : Bornology.IsBounded (h '' W) :=
    isBounded_image_planeHomeomorph h hWbounded
  have himageEq : h '' W = Metric.ball 0 1 :=
    boundedUnitCircleComponent_eq_ball (h '' W) himageComponent himageBounded
  -- Closure commutes with the homeomorphism and the open disk closes to `B²`.
  have hclosureImage : h '' closure W = Metric.closedBall 0 1 := by
    calc
      h '' closure W = closure (h '' W) := h.image_closure W
      _ = closure (Metric.ball 0 1) := congrArg closure himageEq
      _ = Metric.closedBall 0 1 := closure_ball 0 one_ne_zero
  exact ⟨(Homeomorph.image h (closure W)).trans (Homeomorph.setCongr hclosureImage)⟩

/-- Theorem 63.6: The closure of each component of the complement of a simple
closed curve in the standard two-sphere is homeomorphic to the closed unit ball `B²`. -/
theorem schoenflies_componentClosure
    (C : Set (StandardSphere 2)) [Topology.IsSimpleClosedCurve C]
    (x : (Cᶜ : Set (StandardSphere 2))) :
    Nonempty (closure (connectedComponentIn Cᶜ x) ≃ₜ B²) := by
  -- Route correction: puncture the other spherical component, then use the canonical
  -- ambient straightening interface instead of circular bounded-domain recognition.
  classical
  let U : Set (StandardSphere 2) := connectedComponentIn Cᶜ x
  obtain ⟨b, hbU⟩ := exists_complementPoint_not_mem_component C x
  have hbClosure : (b : StandardSphere 2) ∉ closure U :=
    not_mem_componentClosure_of_not_mem_component C x b hbU
  let h := StandardSphere.puncturedHomeomorphPlane (b : StandardSphere 2)
  let D : Set (EuclideanSpace ℝ (Fin 2)) := h '' (Subtype.val ⁻¹' C)
  let W : Set (EuclideanSpace ℝ (Fin 2)) := h '' (Subtype.val ⁻¹' U)
  -- The earlier stereographic theorem supplies the planar component and boundedness facts.
  have hCcompact : IsCompact C := isCompact_of_isSimpleClosedCurve_standardSphere C
  have hUComponent : IsConnectedComponentIn Cᶜ U := IsConnectedComponentIn.of_mem x.property
  obtain ⟨hWComponent, hWbounded⟩ :=
    puncturedSphere_componentImage_bounded C U b h hCcompact b.property hUComponent hbU
  have hDcircle : Nonempty (D ≃ₜ Circle) :=
    stereographicImage_homeomorphic_circle C b b.property
  letI : Topology.IsSimpleClosedCurve D :=
    (Topology.IsSimpleClosedCurve.iff_nonempty_homeomorph_circle D).mpr hDcircle
  -- Transport the spherical closure to the bounded planar domain and apply planar Schoenflies.
  obtain ⟨hchart⟩ := componentClosureHomeomorphStereographicImage U b hbClosure
  obtain ⟨hplanar⟩ :=
    boundedJordanComponentClosure_homeomorph_closedUnitDisk D W hWComponent hWbounded
  simpa [U, D, W, h] using Nonempty.intro (hchart.trans hplanar)
