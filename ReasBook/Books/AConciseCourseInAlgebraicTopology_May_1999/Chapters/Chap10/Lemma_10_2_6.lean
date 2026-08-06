module

public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.CWComplex.Classical.Subcomplex
public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace

public section

open Topology

universe u v

/-- The source-facing indexing type for the `n`-cells in a product CW structure on `X × Y`:
pairs consisting of a `p`-cell of `X` and a `q`-cell of `Y` with `p + q = n`. -/
abbrev productCWCellIndex
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)] (n : ℕ) :
    Type (max u v) :=
  Σ pq : { pq : ℕ × ℕ // pq.1 + pq.2 = n },
    Topology.CWComplex.cell (Set.univ : Set X) pq.1.1 ×
      Topology.CWComplex.cell (Set.univ : Set Y) pq.1.2

/-- Reindexes `Fin n → ℝ` as a product `(Fin p → ℝ) × (Fin q → ℝ)` when `p + q = n`. -/
private noncomputable def productCWCellModelEquiv {n p q : ℕ} (h : p + q = n) :
    (Fin n → ℝ) ≃ᵢ (Fin p → ℝ) × (Fin q → ℝ) :=
  (Fin.appendIsometryOfEq h).symm

/-- The characteristic maps of the chosen product CW structure are the products of the factor
characteristic maps after reindexing `Fin n → ℝ` by `Fin p → ℝ` and `Fin q → ℝ`. -/
noncomputable def productCWCellMap
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)] :
    ∀ n : ℕ, productCWCellIndex X Y n → PartialEquiv (Fin n → ℝ) (X × Y)
  | _, ⟨⟨⟨p, q⟩, hpq⟩, i, j⟩ =>
      let eX : PartialEquiv (Fin p → ℝ) X :=
        Topology.CWComplex.map p i
      let eY : PartialEquiv (Fin q → ℝ) Y :=
        Topology.CWComplex.map q j
      (productCWCellModelEquiv hpq).toEquiv.toPartialEquiv.trans (eX.prod eY)

/-- Helper for Lemma 10.2.6: the target of a characteristic map is its open cell. -/
private theorem cwMap_target_eq_openCell
    (Z : Type*) [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    (n : ℕ) (i : Topology.CWComplex.cell (Set.univ : Set Z) n) :
    (Topology.CWComplex.map n i).target =
      Topology.CWComplex.map n i '' Metric.ball (0 : Fin n → ℝ) 1 := by
  -- The target is the image of the source, and the source is the unit ball.
  rw [← (Topology.CWComplex.map n i).image_source_eq_target, Topology.CWComplex.source_eq]

/-- Helper for Lemma 10.2.6: the open image of a product characteristic map is the product of the
factor open cells. -/
private theorem productCWCell_openImage_eq
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)]
    (n : ℕ) (j : productCWCellIndex X Y n) :
    productCWCellMap X Y n j '' Metric.ball (0 : Fin n → ℝ) 1 =
      let ⟨⟨⟨p, q⟩, _hpq⟩, i, k⟩ := j
      (Topology.CWComplex.map p i '' Metric.ball (0 : Fin p → ℝ) 1) ×ˢ
        (Topology.CWComplex.map q k '' Metric.ball (0 : Fin q → ℝ) 1) := by
  rcases j with ⟨⟨⟨p, q⟩, hpq⟩, i, k⟩
  -- Rewrite the product characteristic map as the product of the factor maps after the model
  -- reindexing `Fin n → ℝ ≃ (Fin p → ℝ) × (Fin q → ℝ)`.
  simp only [productCWCellMap]
  rw [PartialEquiv.coe_trans, PartialEquiv.prod_coe, Set.image_comp]
  change Prod.map (Topology.CWComplex.map p i) (Topology.CWComplex.map q k) ''
      ((productCWCellModelEquiv hpq) '' Metric.ball (0 : Fin n → ℝ) 1) = _
  -- The model isometry sends the unit ball to the product unit ball, so the image factorizes.
  rw [IsometryEquiv.image_ball]
  have hzero : productCWCellModelEquiv hpq (0 : Fin n → ℝ) = (0, 0) := by
    ext <;> simp [productCWCellModelEquiv]
  rw [hzero, ← ball_prod_same, Set.prodMap_image_prod]

/-- Helper for Lemma 10.2.6: the closed image of a product characteristic map is the product of the
factor closed cells. -/
private theorem productCWCell_closedImage_eq
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)]
    (n : ℕ) (j : productCWCellIndex X Y n) :
    productCWCellMap X Y n j '' Metric.closedBall (0 : Fin n → ℝ) 1 =
      let ⟨⟨⟨p, q⟩, _hpq⟩, i, k⟩ := j
      (Topology.CWComplex.map p i '' Metric.closedBall (0 : Fin p → ℝ) 1) ×ˢ
        (Topology.CWComplex.map q k '' Metric.closedBall (0 : Fin q → ℝ) 1) := by
  rcases j with ⟨⟨⟨p, q⟩, hpq⟩, i, k⟩
  -- Rewrite the composite characteristic map into the product of the two factor maps.
  simp only [productCWCellMap]
  rw [PartialEquiv.coe_trans, PartialEquiv.prod_coe, Set.image_comp]
  change Prod.map (Topology.CWComplex.map p i) (Topology.CWComplex.map q k) ''
      ((productCWCellModelEquiv hpq) '' Metric.closedBall (0 : Fin n → ℝ) 1) = _
  -- The model isometry identifies the closed unit ball with the product of the factor closed
  -- balls, so the image is exactly the product closed cell.
  rw [IsometryEquiv.image_closedBall]
  have hzero : productCWCellModelEquiv hpq (0 : Fin n → ℝ) = (0, 0) := by
    ext <;> simp [productCWCellModelEquiv]
  rw [hzero, ← closedBall_prod_same, Set.prodMap_image_prod]

/-- Helper for Lemma 10.2.6: the frontier image of a product characteristic map splits into the two
expected frontier branches. -/
private theorem productCWCell_frontier_eq
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)]
    (n : ℕ) (j : productCWCellIndex X Y n) :
    productCWCellMap X Y n j '' Metric.sphere (0 : Fin n → ℝ) 1 =
      let ⟨⟨⟨p, q⟩, _hpq⟩, i, k⟩ := j
      ((Topology.CWComplex.map p i '' Metric.sphere (0 : Fin p → ℝ) 1) ×ˢ
          (Topology.CWComplex.map q k '' Metric.closedBall (0 : Fin q → ℝ) 1)) ∪
        ((Topology.CWComplex.map p i '' Metric.closedBall (0 : Fin p → ℝ) 1) ×ˢ
          (Topology.CWComplex.map q k '' Metric.sphere (0 : Fin q → ℝ) 1)) := by
  rcases j with ⟨⟨⟨p, q⟩, hpq⟩, i, k⟩
  -- Rewrite the product characteristic map into the factor product and transport the sphere
  -- through the model isometry.
  simp only [productCWCellMap]
  rw [PartialEquiv.coe_trans, PartialEquiv.prod_coe, Set.image_comp]
  change Prod.map (Topology.CWComplex.map p i) (Topology.CWComplex.map q k) ''
      ((productCWCellModelEquiv hpq) '' Metric.sphere (0 : Fin n → ℝ) 1) = _
  rw [IsometryEquiv.image_sphere]
  have hzero : productCWCellModelEquiv hpq (0 : Fin n → ℝ) = (0, 0) := by
    ext <;> simp [productCWCellModelEquiv]
  -- The product sphere splits into the two expected frontier branches, and images respect unions
  -- and product maps.
  rw [hzero, sphere_prod, Set.image_union, Set.prodMap_image_prod, Set.prodMap_image_prod]

/-- Each characteristic map of the chosen product CW structure has source `ball 0 1`. -/
theorem productCWCell_source_eq
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)]
    (n : ℕ) (j : productCWCellIndex X Y n) :
    (productCWCellMap X Y n j).source = Metric.ball (0 : Fin n → ℝ) 1 := by
  rcases j with ⟨⟨⟨p, q⟩, hpq⟩, i, k⟩
  -- The source of the composite partial equivalence is the preimage of the factor source product
  -- under the model equivalence.
  simp only [productCWCellMap, PartialEquiv.trans_source, PartialEquiv.prod_source,
    Topology.CWComplex.source_eq, Equiv.toPartialEquiv_source, Set.univ_inter]
  have hball : Metric.ball (0 : Fin p → ℝ) 1 ×ˢ Metric.ball (0 : Fin q → ℝ) 1 =
      Metric.ball ((productCWCellModelEquiv hpq) (0 : Fin n → ℝ)) 1 := by
    rw [show productCWCellModelEquiv hpq (0 : Fin n → ℝ) = (0, 0) by
      ext <;> simp [productCWCellModelEquiv], ← ball_prod_same]
  rw [hball, Equiv.toPartialEquiv_apply]
  -- The model equivalence is an isometry, so pulling the unit ball back recovers the unit ball.
  exact
    ((productCWCellModelEquiv hpq).isometry.preimage_ball (x := (0 : Fin n → ℝ)) (r := 1))

/-- The characteristic maps of the chosen product CW structure are continuous on the closed unit
ball. -/
theorem productCWCell_continuousOn
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)]
    (n : ℕ) (j : productCWCellIndex X Y n) :
    ContinuousOn (productCWCellMap X Y n j) (Metric.closedBall (0 : Fin n → ℝ) 1) := by
  rcases j with ⟨⟨⟨p, q⟩, hpq⟩, i, k⟩
  let e := productCWCellModelEquiv hpq
  have hzero : e (0 : Fin n → ℝ) = (0, 0) := by
    ext <;> simp [e, productCWCellModelEquiv]
  have hmaps : Set.MapsTo e (Metric.closedBall (0 : Fin n → ℝ) 1)
      (Metric.closedBall (0 : Fin p → ℝ) 1 ×ˢ Metric.closedBall (0 : Fin q → ℝ) 1) := by
    intro x hx
    -- The model equivalence sends the source closed ball into the product of the factor closed
    -- balls because it preserves distances.
    have hx' : x ∈ e ⁻¹' Metric.closedBall (e (0 : Fin n → ℝ)) 1 := by
      rwa [e.isometry.preimage_closedBall (x := (0 : Fin n → ℝ)) (r := 1)]
    simpa [hzero, ← closedBall_prod_same] using hx'
  -- Compose the product of the factor continuity statements with the continuous model
  -- reindexing.
  simp only [productCWCellMap, PartialEquiv.coe_trans, PartialEquiv.prod_coe]
  refine ContinuousOn.comp ?_ e.continuous.continuousOn hmaps
  simpa using
    (Topology.CWComplex.continuousOn (C := (Set.univ : Set X)) p i).prodMap
      (Topology.CWComplex.continuousOn (C := (Set.univ : Set Y)) q k)

/-- The inverses of the chosen product characteristic maps are continuous on their targets. -/
theorem productCWCell_continuousOn_symm
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)]
    (n : ℕ) (j : productCWCellIndex X Y n) :
    ContinuousOn (productCWCellMap X Y n j).symm (productCWCellMap X Y n j).target := by
  rcases j with ⟨⟨⟨p, q⟩, hpq⟩, i, k⟩
  let e := productCWCellModelEquiv hpq
  -- Route correction: normalize the target once using the `trans`/`prod` target formulas, then
  -- compose the factor inverse continuity with the inverse model reindexing.
  have htarget :
      (productCWCellMap X Y n ⟨⟨⟨p, q⟩, hpq⟩, i, k⟩).target =
        (Topology.CWComplex.map p i).target ×ˢ (Topology.CWComplex.map q k).target := by
    -- The model equivalence has full target, so the composite target is exactly the product target.
    rw [productCWCellMap, PartialEquiv.trans_target, PartialEquiv.prod_target]
    change
      (Topology.CWComplex.map p i).target ×ˢ (Topology.CWComplex.map q k).target ∩
          ((Topology.CWComplex.map p i).symm.prod (Topology.CWComplex.map q k).symm) ⁻¹'
            (Set.univ : Set ((Fin p → ℝ) × (Fin q → ℝ))) =
        (Topology.CWComplex.map p i).target ×ˢ (Topology.CWComplex.map q k).target
    simp
  have hprod :
      ContinuousOn
        (Prod.map (Topology.CWComplex.map p i).symm (Topology.CWComplex.map q k).symm)
        ((Topology.CWComplex.map p i).target ×ˢ (Topology.CWComplex.map q k).target) := by
    -- On the normalized target, inverse continuity is just the product of the factor inverse
    -- continuity statements.
    simpa only [PartialEquiv.prod_coe] using
      (Topology.CWComplex.continuousOn_symm (C := (Set.univ : Set X)) p i).prodMap
        (Topology.CWComplex.continuousOn_symm (C := (Set.univ : Set Y)) q k)
  rw [htarget]
  -- After normalizing the target, the inverse characteristic map is the inverse model reindexing
  -- composed with the product of the two factor inverses.
  simp only [productCWCellMap, PartialEquiv.trans_symm_eq_symm_trans_symm, PartialEquiv.prod_symm,
    PartialEquiv.coe_trans, PartialEquiv.prod_coe]
  change ContinuousOn
      (e.symm ∘ Prod.map (Topology.CWComplex.map p i).symm (Topology.CWComplex.map q k).symm)
      ((Topology.CWComplex.map p i).target ×ˢ (Topology.CWComplex.map q k).target)
  refine ContinuousOn.comp
      (t := (Set.univ : Set ((Fin p → ℝ) × (Fin q → ℝ))))
      e.symm.continuous.continuousOn hprod ?_
  intro x hx
  simp

/-- The open cells of the chosen product CW structure are pairwise disjoint. -/
theorem productCWCell_pairwiseDisjoint
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)] :
    (Set.univ : Set (Σ n, productCWCellIndex X Y n)).PairwiseDisjoint
      (fun ni ↦ productCWCellMap X Y ni.1 ni.2 '' Metric.ball 0 1) := by
  let encode :
      (Σ n, productCWCellIndex X Y n) →
        (Σ p, Topology.CWComplex.cell (Set.univ : Set X) p) ×
          (Σ q, Topology.CWComplex.cell (Set.univ : Set Y) q)
    | ⟨_, ⟨⟨⟨p, q⟩, _hpq⟩, i, k⟩⟩ => (⟨p, i⟩, ⟨q, k⟩)
  let decode :
      ((Σ p, Topology.CWComplex.cell (Set.univ : Set X) p) ×
          (Σ q, Topology.CWComplex.cell (Set.univ : Set Y) q)) →
        (Σ n, productCWCellIndex X Y n)
    | (⟨p, i⟩, ⟨q, k⟩) =>
        let pq : { pq : ℕ × ℕ // pq.1 + pq.2 = p + q } := ⟨(p, q), rfl⟩
        ⟨p + q, Sigma.mk pq (i, k)⟩
  have hdecode : Function.LeftInverse decode encode := by
    intro ni
    rcases ni with ⟨n, ⟨⟨⟨p, q⟩, hpq⟩, i, k⟩⟩
    -- Forgetting the equality proof and then rebuilding the index recovers the same cell.
    cases hpq
    rfl
  have hpairFactors :
      (Set.univ :
          Set
            ((Σ p, Topology.CWComplex.cell (Set.univ : Set X) p) ×
              (Σ q, Topology.CWComplex.cell (Set.univ : Set Y) q))).PairwiseDisjoint
        (fun ab ↦
          Topology.CWComplex.openCell (C := (Set.univ : Set X)) ab.1.1 ab.1.2 ×ˢ
            Topology.CWComplex.openCell (C := (Set.univ : Set Y)) ab.2.1 ab.2.2) := by
    -- Once the indices are separated into factor indices, pairwise disjointness is just the
    -- product of the factor pairwise-disjointness statements.
    simpa using
      (Topology.CWComplex.pairwiseDisjoint (C := (Set.univ : Set X))).prod
        (Topology.CWComplex.pairwiseDisjoint (C := (Set.univ : Set Y)))
  intro ni _nj nj _nk hne
  have hencode : encode ni ≠ encode nj := fun hij => hne (hdecode.injective hij)
  -- Normalize both open-cell images to products of factor open cells, then appeal to the factor
  -- pairwise-disjointness transferred across the index encoding.
  rcases ni with ⟨n, j⟩
  rcases nj with ⟨m, k⟩
  change Disjoint
      (productCWCellMap X Y n j '' Metric.ball (0 : Fin n → ℝ) 1)
      (productCWCellMap X Y m k '' Metric.ball (0 : Fin m → ℝ) 1)
  rw [productCWCell_openImage_eq, productCWCell_openImage_eq]
  simpa [encode, Topology.CWComplex.openCell] using
    hpairFactors (show encode ⟨n, j⟩ ∈ Set.univ by simp) (show encode ⟨m, k⟩ ∈ Set.univ by simp)
      hencode

/-- The frontier of each chosen product cell lies in finitely many lower-dimensional product
closed cells. -/
theorem productCWCell_mapsTo
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)]
    (n : ℕ) (j : productCWCellIndex X Y n) :
    ∃ I : Π m, Finset (productCWCellIndex X Y m),
      Set.MapsTo (productCWCellMap X Y n j) (Metric.sphere (0 : Fin n → ℝ) 1)
        (⋃ (m < n) (k ∈ I m), productCWCellMap X Y m k '' Metric.closedBall 0 1) := by
  classical
  rcases j with ⟨⟨⟨p, q⟩, hpq⟩, i, k⟩
  obtain ⟨IX, hIX⟩ :=
    Topology.CWComplex.cellFrontier_subset_finite_closedCell (C := (Set.univ : Set X)) p i
  obtain ⟨IY, hIY⟩ :=
    Topology.CWComplex.cellFrontier_subset_finite_closedCell (C := (Set.univ : Set Y)) q k
  let I : Π m, Finset (productCWCellIndex X Y m) := fun m =>
    ((Finset.range (m + 1)).biUnion fun p' =>
      if hpm : p' + q = m then
        (IX p').image fun i' =>
          ((⟨⟨⟨p', q⟩, hpm⟩, i', k⟩ : productCWCellIndex X Y m))
      else ∅) ∪
    ((Finset.range (m + 1)).biUnion fun q' =>
      if hpq' : p + q' = m then
        (IY q').image fun k' =>
          ((⟨⟨⟨p, q'⟩, hpq'⟩, i, k'⟩ : productCWCellIndex X Y m))
      else ∅)
  use I
  -- Route correction: package the two frontier branches once into a finite family indexed by total
  -- dimension, instead of repeating pointwise set rewrites inside the final `MapsTo` goal.
  rw [Set.mapsTo_iff_image_subset, productCWCell_frontier_eq]
  intro x hx
  simp only [Set.mem_union, Set.mem_prod, Set.mem_iUnion, exists_prop] at hx ⊢
  rcases hx with ⟨hxX, hyY⟩ | ⟨hxX, hyY⟩
  · -- The `X`-frontier branch contributes cells of dimensions `p' + q < n`.
    have hxX' := hIX hxX
    simp only [Topology.CWComplex.closedCell, Set.mem_iUnion, exists_prop] at hxX'
    rcases hxX' with ⟨p', hp', i', hi', hxi'⟩
    let j' : productCWCellIndex X Y (p' + q) := ⟨⟨(p', q), rfl⟩, i', k⟩
    refine ⟨p' + q, ?_, j', ?_, ?_⟩
    · -- Arithmetic closes the lower-dimensional inequality after rewriting `n = p + q`.
      omega
    · -- Insert the packaged product cell into the left half of the finite family.
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_biUnion.mpr
      refine ⟨p', Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_add_right p' q)), ?_⟩
      simpa using
        (show
          j' ∈
            Finset.image
              (fun i' => ((⟨⟨⟨p', q⟩, rfl⟩, i', k⟩ : productCWCellIndex X Y (p' + q))))
              (IX p')
         from Finset.mem_image.mpr ⟨i', hi', rfl⟩)
    · -- Rewrite the product closed cell and use the factor closed-cell witnesses directly.
      rw [productCWCell_closedImage_eq]
      exact ⟨hxi', hyY⟩
  · -- The `Y`-frontier branch contributes cells of dimensions `p + q' < n`.
    have hyY' := hIY hyY
    simp only [Topology.CWComplex.closedCell, Set.mem_iUnion, exists_prop] at hyY'
    rcases hyY' with ⟨q', hq', k', hk', hyk'⟩
    let j' : productCWCellIndex X Y (p + q') := ⟨⟨(p, q'), rfl⟩, i, k'⟩
    refine ⟨p + q', ?_, j', ?_, ?_⟩
    · -- The symmetric arithmetic inequality is handled in the same way.
      omega
    · -- Insert the packaged product cell into the right half of the finite family.
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_biUnion.mpr
      refine ⟨q', Finset.mem_range.mpr (by omega), ?_⟩
      simpa using
        (show
          j' ∈
            Finset.image
              (fun k' => ((⟨⟨⟨p, q'⟩, rfl⟩, i, k'⟩ : productCWCellIndex X Y (p + q'))))
              (IY q')
         from Finset.mem_image.mpr ⟨k', hk', rfl⟩)
    · -- The product closed cell formula finishes the second frontier branch.
      rw [productCWCell_closedImage_eq]
      exact ⟨hxX, hyk'⟩

/-- Helper for Lemma 10.2.6: intersecting an `X`-strip with a `Y`-closed-cell strip recovers the
corresponding product closed cell. -/
private theorem inter_prodStrip_closedCell_assoc
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set (X × Y)) (K : Set X) (L : Set Y) :
    A ∩ (K ×ˢ (Set.univ : Set Y)) ∩ ((Set.univ : Set X) ×ˢ L) = A ∩ (K ×ˢ L) := by
  -- Both sides impose the same membership conditions on the two coordinates.
  ext z
  simp [and_assoc, and_left_comm, and_comm]

/-- Helper for Lemma 10.2.6: a finite cover of the projected `Y`-range rewrites the compact-strip
preimage as a finite union of the corresponding `Y`-cell-strip preimages. -/
private theorem preimage_compactStrip_eq_biUnion_of_snd_range_subset_closedCells
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (Set.univ : Set Y)]
    {S : Type*} (A : Set (X × Y)) (K : Set X) (g : S → X × Y)
    (I : Finset (Σ q, Topology.CWComplex.cell (Set.univ : Set Y) q))
    (hI :
      Set.range (fun s ↦ (g s).2) ⊆
        ⋃ a ∈ I, Topology.CWComplex.closedCell (C := (Set.univ : Set Y)) a.1 a.2) :
    g ⁻¹' (A ∩ (K ×ˢ (Set.univ : Set Y))) =
      ⋃ a ∈ I,
        g ⁻¹'
          (A ∩
            (K ×ˢ Topology.CWComplex.closedCell (C := (Set.univ : Set Y)) a.1 a.2)) := by
  -- A point belongs to the whole strip exactly when its `Y`-coordinate lands in one of the chosen
  -- finitely many closed cells covering the projected range.
  ext s
  constructor
  · intro hs
    have hsCover :
        (g s).2 ∈
          ⋃ a ∈ I, Topology.CWComplex.closedCell (C := (Set.univ : Set Y)) a.1 a.2 :=
      hI ⟨s, rfl⟩
    simp only [Set.mem_iUnion, exists_prop] at hsCover
    rcases hsCover with ⟨a, haI, hsa⟩
    refine Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨haI, ?_⟩⟩
    rcases hs with ⟨hsA, hsK, -⟩
    exact ⟨hsA, hsK, by simpa using hsa⟩
  · intro hs
    simp only [Set.mem_iUnion, exists_prop] at hs
    rcases hs with ⟨a, haI, hs⟩
    rcases hs with ⟨hsA, hsK, hsCell⟩
    exact ⟨hsA, hsK, by simp⟩

/-- Helper for Lemma 10.2.6: a finite cover of the projected `X`-range rewrites the whole-set
preimage as a finite union of the corresponding `X`-cell-strip preimages. -/
private theorem preimage_eq_biUnion_of_fst_range_subset_closedCells
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (Set.univ : Set X)]
    {S : Type*} (A : Set (X × Y)) (g : S → X × Y)
    (I : Finset (Σ p, Topology.CWComplex.cell (Set.univ : Set X) p))
    (hI :
      Set.range (fun s ↦ (g s).1) ⊆
        ⋃ a ∈ I, Topology.CWComplex.closedCell (C := (Set.univ : Set X)) a.1 a.2) :
    g ⁻¹' A =
      ⋃ a ∈ I,
        g ⁻¹'
          (A ∩
            (Topology.CWComplex.closedCell (C := (Set.univ : Set X)) a.1 a.2 ×ˢ
              (Set.univ : Set Y))) := by
  -- A point of the preimage of `A` lies in one of the finitely many chosen `X`-closed cells
  -- covering the projected first-coordinate range.
  ext s
  constructor
  · intro hs
    have hsCover :
        (g s).1 ∈
          ⋃ a ∈ I, Topology.CWComplex.closedCell (C := (Set.univ : Set X)) a.1 a.2 :=
      hI ⟨s, rfl⟩
    simp only [Set.mem_iUnion, exists_prop] at hsCover
    rcases hsCover with ⟨a, haI, hsa⟩
    refine Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨haI, ?_⟩⟩
    exact ⟨hs, by simpa using hsa, by simp⟩
  · intro hs
    simp only [Set.mem_iUnion, exists_prop] at hs
    rcases hs with ⟨a, haI, hs⟩
    exact hs.1

/-- Helper for Lemma 10.2.6: a finite closed-cell carrier can be rewritten as a finite open-cell
carrier by expanding each closed cell into its open cell and finitely many lower-dimensional
frontier cells. -/
private theorem finiteClosedCellUnion_subset_finiteOpenCellUnion
    (Z : Type*) [TopologicalSpace Z]
    [CWComplex (Set.univ : Set Z)]
    (J : Finset (Σ n, Topology.CWComplex.cell (Set.univ : Set Z) n)) :
    ∃ K : Finset (Σ n, Topology.CWComplex.cell (Set.univ : Set Z) n),
      (⋃ a ∈ J, Topology.CWComplex.closedCell (C := (Set.univ : Set Z)) a.1 a.2) ⊆
        ⋃ a ∈ K, Topology.CWComplex.openCell (C := (Set.univ : Set Z)) a.1 a.2 := by
  classical
  let Cell := Σ n, Topology.CWComplex.cell (Set.univ : Set Z) n
  induction J using Finset.induction_on with
  | empty =>
      refine ⟨∅, ?_⟩
      simp
  | @insert a J ha hJ =>
      obtain ⟨KJ, hKJ⟩ := hJ
      obtain ⟨I, hI⟩ :=
        Topology.CWComplex.cellFrontier_subset_finite_openCell (C := (Set.univ : Set Z)) a.1 a.2
      let Ka : Finset Cell :=
        insert a <|
          (Finset.range a.1).biUnion fun m =>
            (I m).image fun j ↦ ((⟨m, j⟩ : Cell))
      let K : Finset Cell := Ka ∪ KJ
      refine ⟨K, ?_⟩
      rw [show
          (⋃ b ∈ insert a J, Topology.CWComplex.closedCell (C := (Set.univ : Set Z)) b.1 b.2) =
            Topology.CWComplex.closedCell (C := (Set.univ : Set Z)) a.1 a.2 ∪
              ⋃ b ∈ J, Topology.CWComplex.closedCell (C := (Set.univ : Set Z)) b.1 b.2 by
        ext x
        simp]
      intro x hx
      rcases hx with hx | hx
      · have hxCell :
            x ∈ Topology.CWComplex.cellFrontier (C := (Set.univ : Set Z)) a.1 a.2 ∪
                Topology.CWComplex.openCell (C := (Set.univ : Set Z)) a.1 a.2 := by
          simpa [Topology.RelCWComplex.cellFrontier_union_openCell_eq_closedCell
            (C := (Set.univ : Set Z)) a.1 a.2] using hx
        rcases hxCell with hxFrontier | hxOpen
        · have hxFrontier' :
              x ∈ ⋃ (m < a.1) (j ∈ I m),
                Topology.CWComplex.openCell (C := (Set.univ : Set Z)) m j :=
            hI hxFrontier
          simp only [Set.mem_iUnion, exists_prop] at hxFrontier'
          rcases hxFrontier' with ⟨m, hm, j, hjI, hxj⟩
          have hjKa : (⟨m, j⟩ : Cell) ∈ Ka := by
            unfold Ka
            refine Finset.mem_insert_of_mem ?_
            refine Finset.mem_biUnion.mpr ⟨m, Finset.mem_range.mpr hm, ?_⟩
            exact Finset.mem_image.mpr ⟨j, hjI, rfl⟩
          exact Set.mem_iUnion.2 ⟨⟨m, j⟩, Set.mem_iUnion.2 ⟨Finset.mem_union.mpr (Or.inl hjKa),
            hxj⟩⟩
        · have haKa : a ∈ Ka := by
            simp [Ka]
          exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨Finset.mem_union.mpr (Or.inl haKa),
            hxOpen⟩⟩
      · have hxKJ := hKJ hx
        simp only [Set.mem_iUnion, exists_prop] at hxKJ ⊢
        rcases hxKJ with ⟨b, hbKJ, hxb⟩
        exact ⟨b, Finset.mem_union.mpr (Or.inr hbKJ), hxb⟩

/-- Helper for Lemma 10.2.6: the sigma-indexed owners of closed cells in the absolute CW
structure on `Z`. -/
private abbrev closedCellOwner
    (Z : Type*) [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)] :=
  Σ n, Topology.CWComplex.cell (Set.univ : Set Z) n

/-- Helper for Lemma 10.2.6: the carrier of a finite family of closed cells. -/
private def closedCellCarrier
    (Z : Type*) [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    (J : Finset (closedCellOwner Z)) : Set Z :=
  ⋃ a ∈ J, Topology.CWComplex.closedCell (C := (Set.univ : Set Z)) a.1 a.2

/-- Helper for Lemma 10.2.6: a finite closed-cell carrier is compact because it is a finite union
of compact closed cells. -/
private theorem isCompact_closedCellCarrier
    (Z : Type*) [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    (J : Finset (closedCellOwner Z)) :
    IsCompact (closedCellCarrier Z J) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
      -- The empty carrier is compact.
      simp [closedCellCarrier]
  | @insert a J ha hJ =>
      -- Add one compact closed cell to the previously compact carrier.
      have hUnion :
          closedCellCarrier Z (insert a J) =
            Topology.CWComplex.closedCell (C := (Set.univ : Set Z)) a.1 a.2 ∪
              closedCellCarrier Z J := by
        ext x
        simp [closedCellCarrier]
      rw [hUnion]
      exact
        (Topology.RelCWComplex.isCompact_closedCell
          (C := (Set.univ : Set Z)) (D := (∅ : Set Z)) (n := a.1) (i := a.2)).union hJ

/-- Helper for Lemma 10.2.6: in a Hausdorff ambient space, every finite closed-cell carrier is
closed. -/
private theorem isClosed_closedCellCarrier
    (Z : Type*) [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)] [T2Space Z]
    (J : Finset (closedCellOwner Z)) :
    IsClosed (closedCellCarrier Z J) := by
  -- The carrier is already compact, and Hausdorffness upgrades compact subsets to closed ones.
  exact (isCompact_closedCellCarrier Z J).isClosed

/-- Helper for Lemma 10.2.6: a finite family is frontier-closed when every chosen cell frontier is
already contained in its closed-cell carrier. -/
private def frontierClosedCellFamily
    (Z : Type*) [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    (J : Finset (closedCellOwner Z)) : Prop :=
  ∀ a ∈ J,
    Topology.CWComplex.cellFrontier (C := (Set.univ : Set Z)) a.1 a.2 ⊆ closedCellCarrier Z J

/-- Helper for Lemma 10.2.6: a finite subcomplex can be rewritten as a sigma-indexed finite union
of ambient closed cells. -/
private theorem finiteSubcomplex_closedCellFinset
    (Z : Type*) [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)] [T2Space Z]
    (E : Topology.CWComplex.Subcomplex (Set.univ : Set Z))
    [Topology.CWComplex.Finite (E : Set Z)] :
    ∃ J : Finset (closedCellOwner Z), (E : Set Z) = closedCellCarrier Z J := by
  classical
  have _ : Finite (Σ n, Topology.CWComplex.cell (E : Set Z) n) := by
    simpa using (Topology.CWComplex.finite_cells_of_finite (C := (E : Set Z)))
  let _ : Fintype (Σ n, Topology.CWComplex.cell (E : Set Z) n) := Fintype.ofFinite _
  let I : Finset (Σ n, Topology.CWComplex.cell (E : Set Z) n) := Finset.univ
  let toAmbient : (Σ n, Topology.CWComplex.cell (E : Set Z) n) → closedCellOwner Z
    | ⟨n, j⟩ => ⟨n, j.1⟩
  let J : Finset (closedCellOwner Z) :=
    I.image toAmbient
  refine ⟨J, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    -- Rewrite membership in the subcomplex through its closed-cell union, then package the chosen
    -- subcomplex cell as one sigma-indexed ambient owner.
    rw [← Topology.CWComplex.Subcomplex.union_closedCell E] at hx
    simp only [Set.mem_iUnion] at hx
    rcases hx with ⟨n, j, hxj⟩
    have hij : (⟨n, j⟩ : Σ n, Topology.CWComplex.cell (E : Set Z) n) ∈ I := by
      simp [I]
    exact
      Set.mem_iUnion.2 ⟨⟨n, j.1⟩,
        Set.mem_iUnion.2 ⟨Finset.mem_image.mpr ⟨⟨n, j⟩, hij, rfl⟩, by simpa using hxj⟩⟩
  · intro x hx
    -- Unpack the sigma-indexed owner back to a cell of the finite subcomplex and reassemble the
    -- subcomplex closed-cell union.
    simp only [closedCellCarrier, Set.mem_iUnion, exists_prop] at hx
    rcases hx with ⟨a, haJ, hxa⟩
    rcases Finset.mem_image.mp haJ with ⟨⟨n, j⟩, -, ha⟩
    rcases a with ⟨m, i⟩
    cases ha
    rw [← Topology.CWComplex.Subcomplex.union_closedCell E]
    exact Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨j, by simpa using hxa⟩⟩

/-- Helper for Lemma 10.2.6: every chosen closed cell is contained in its carrier. -/
private theorem closedCell_subset_closedCellCarrier_of_mem
    (Z : Type*) [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    {J : Finset (closedCellOwner Z)} {a : closedCellOwner Z} (ha : a ∈ J) :
    Topology.CWComplex.closedCell (C := (Set.univ : Set Z)) a.1 a.2 ⊆ closedCellCarrier Z J := by
  -- A member cell contributes one summand of the sigma-indexed carrier.
  intro x hx
  exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨ha, hx⟩⟩

/-- Helper for Lemma 10.2.6: enlarging the index family enlarges the closed-cell carrier. -/
private theorem closedCellCarrier_mono
    (Z : Type*) [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    {J K : Finset (closedCellOwner Z)} (hJK : J ⊆ K) :
    closedCellCarrier Z J ⊆ closedCellCarrier Z K := by
  -- Rewrite membership in the carrier as sigma-indexed membership and move the owner along `hJK`.
  intro x hx
  simp only [closedCellCarrier, Set.mem_iUnion, exists_prop] at hx ⊢
  rcases hx with ⟨a, haJ, hxa⟩
  exact ⟨a, hJK haJ, hxa⟩

/-- Helper for Lemma 10.2.6: a finite closed-cell carrier whose owners all have dimension at most
`N` lies in the `N`-skeleton. -/
private theorem closedCellCarrier_subset_skeleton_of_bound
    (Z : Type*) [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)] [T2Space Z]
    {J : Finset (closedCellOwner Z)} {N : ℕ}
    (hJ : ∀ a ∈ J, a.1 ≤ N) :
    closedCellCarrier Z J ⊆ Topology.CWComplex.skeleton (Set.univ : Set Z) N := by
  -- Rewrite carrier membership through one chosen closed cell and then push that cell into the
  -- target skeleton using the ambient monotonicity of skeleta.
  intro x hx
  simp only [closedCellCarrier, Set.mem_iUnion, exists_prop] at hx
  rcases hx with ⟨a, haJ, hxa⟩
  have hxaSke :
      x ∈ Topology.CWComplex.skeleton (Set.univ : Set Z) a.1 :=
    Topology.CWComplex.closedCell_subset_skeleton
      (C := (Set.univ : Set Z)) a.1 a.2 hxa
  exact
    Topology.CWComplex.skeleton_mono
      (C := (Set.univ : Set Z))
      (show (a.1 : ℕ∞) ≤ (N : ℕ∞) by exact_mod_cast hJ a haJ)
      hxaSke

/-- Helper for Lemma 10.2.6: the carrier of a union is the union of the carriers. -/
private theorem closedCellCarrier_union
    (Z : Type*) [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    [DecidableEq (closedCellOwner Z)]
    (J K : Finset (closedCellOwner Z)) :
    closedCellCarrier Z (J ∪ K) = closedCellCarrier Z J ∪ closedCellCarrier Z K := by
  -- A point of the union carrier belongs to a chosen cell coming either from `J` or from `K`.
  ext x
  constructor
  · intro hx
    simp only [closedCellCarrier, Set.mem_iUnion, exists_prop] at hx
    rcases hx with ⟨a, haJK, hxa⟩
    rcases Finset.mem_union.mp haJK with haJ | haK
    · left
      exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨haJ, hxa⟩⟩
    · right
      exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨haK, hxa⟩⟩
  · intro hx
    rcases hx with hx | hx
    · simp only [closedCellCarrier, Set.mem_iUnion, exists_prop] at hx
      rcases hx with ⟨a, haJ, hxa⟩
      exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨Finset.mem_union.mpr (Or.inl haJ), hxa⟩⟩
    · simp only [closedCellCarrier, Set.mem_iUnion, exists_prop] at hx
      rcases hx with ⟨a, haK, hxa⟩
      exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨Finset.mem_union.mpr (Or.inr haK), hxa⟩⟩

/-- Helper for Lemma 10.2.6: frontier-closed finite families stay frontier-closed after taking a
finite union. -/
private theorem frontierClosedCellFamily_union
    (Z : Type*) [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    [DecidableEq (closedCellOwner Z)]
    {J K : Finset (closedCellOwner Z)}
    (hJ : frontierClosedCellFamily Z J) (hK : frontierClosedCellFamily Z K) :
    frontierClosedCellFamily Z (J ∪ K) := by
  -- Route correction: package the directedness step once at the carrier level so the later
  -- compactness contradiction only has to ask for one finite-union witness.
  intro a haJK
  rcases Finset.mem_union.mp haJK with haJ | haK
  · exact (hJ a haJ).trans <| closedCellCarrier_mono Z fun b hb ↦ Finset.mem_union.mpr (Or.inl hb)
  · exact (hK a haK).trans <| closedCellCarrier_mono Z fun b hb ↦ Finset.mem_union.mpr (Or.inr hb)

/-- Helper for Lemma 10.2.6: a finite union of frontier-closed owner families is again
frontier-closed. -/
private theorem frontierClosedCellFamily_biUnion
    (Z : Type*) [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    [DecidableEq (closedCellOwner Z)]
    (U : Finset {J : Finset (closedCellOwner Z) // frontierClosedCellFamily Z J}) :
    frontierClosedCellFamily Z (U.biUnion fun u ↦ u.1) := by
  classical
  induction U using Finset.induction_on with
  | empty =>
      -- The empty family contributes no frontier obligations.
      intro a ha
      exact False.elim (Finset.notMem_empty _ ha)
  | @insert u U hu hU =>
      -- Fold one more frontier-closed family into the inductive union.
      rw [Finset.biUnion_insert]
      exact frontierClosedCellFamily_union Z u.2 hU

/-- Helper for Lemma 10.2.6: the carrier of a finite union of owner families is the union of the
corresponding carriers. -/
private theorem closedCellCarrier_biUnion
    (Z : Type*) [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    [DecidableEq (closedCellOwner Z)]
    (U : Finset {J : Finset (closedCellOwner Z) // frontierClosedCellFamily Z J}) :
    closedCellCarrier Z (U.biUnion fun u ↦ u.1) =
      ⋃ u ∈ U, closedCellCarrier Z u.1 := by
  classical
  induction U using Finset.induction_on with
  | empty =>
      -- Both the owner family and the carrier union are empty in the base case.
      ext x
      simp [closedCellCarrier]
  | @insert u U hu hU =>
      -- Peel off one carrier and rewrite the remaining part by the induction hypothesis.
      rw [Finset.biUnion_insert, closedCellCarrier_union, hU]
      ext x
      simp

/-- Helper for Lemma 10.2.6: once compactness supplies finitely many frontier-closed carriers
covering a set, those carriers can be merged into one finite frontier-closed family. -/
private theorem finiteUnion_frontierClosedCarrier_cover
    (Z : Type*) [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    (S : Set Z)
    (U : Finset {J : Finset (closedCellOwner Z) // frontierClosedCellFamily Z J})
    (hU :
      S ⊆ ⋃ u ∈ U, closedCellCarrier Z u.1) :
    ∃ J : Finset (closedCellOwner Z),
      frontierClosedCellFamily Z J ∧ S ⊆ closedCellCarrier Z J := by
  classical
  refine ⟨U.biUnion fun u ↦ u.1, frontierClosedCellFamily_biUnion Z U, ?_⟩
  -- Collapse the finite family of carriers to the carrier of the finite union of owners.
  rw [closedCellCarrier_biUnion Z U]
  exact hU

/-- Helper for Lemma 10.2.6: every closed cell owner is contained in a finite frontier-closed
family whose dimensions stay below the original owner. -/
private theorem frontierClosedCellFamilyOfOwner
    (Z : Type*) [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    (a : closedCellOwner Z) :
    ∃ J : Finset (closedCellOwner Z),
      a ∈ J ∧ frontierClosedCellFamily Z J ∧ (∀ b ∈ J, b.1 ≤ a.1) := by
  classical
  rcases a with ⟨n, i⟩
  revert i
  refine Nat.strong_induction_on n ?_
  intro n ih i
  obtain ⟨I, hI⟩ :=
    Topology.CWComplex.cellFrontier_subset_finite_closedCell (C := (Set.univ : Set Z)) n i
  let K : Finset (closedCellOwner Z) :=
    (Finset.range n).biUnion fun m =>
      (I m).image fun j ↦ ((⟨m, j⟩ : closedCellOwner Z))
  have hKfrontier :
      Topology.CWComplex.cellFrontier (C := (Set.univ : Set Z)) n i ⊆ closedCellCarrier Z K := by
    -- Rewrite the frontier cover returned by `cellFrontier_subset_finite_closedCell` into the
    -- sigma-indexed carrier language used by the compactness argument.
    intro x hx
    have hx' := hI hx
    simp only [Set.mem_iUnion, exists_prop] at hx'
    rcases hx' with ⟨m, hm, j, hjI, hxj⟩
    refine Set.mem_iUnion.2 ⟨⟨m, j⟩, Set.mem_iUnion.2 ⟨?_, hxj⟩⟩
    exact Finset.mem_biUnion.mpr
      ⟨m, Finset.mem_range.mpr hm, Finset.mem_image.mpr ⟨j, hjI, rfl⟩⟩
  have hRec :
      ∀ b ∈ K,
        ∃ J : Finset (closedCellOwner Z),
          b ∈ J ∧ frontierClosedCellFamily Z J ∧ (∀ c ∈ J, c.1 ≤ n) := by
    intro b hbK
    rcases b with ⟨m, j⟩
    have hm : m < n := by
      -- Membership in `K` records that the owner came from one of the strictly lower-dimensional
      -- frontier cells.
      unfold K at hbK
      rcases Finset.mem_biUnion.mp hbK with ⟨m', hmRange, hmCell⟩
      rcases Finset.mem_image.mp hmCell with ⟨j', _, hbEq⟩
      cases hbEq
      exact Finset.mem_range.mp hmRange
    obtain ⟨J, hbJ, hJ, hBoundJ⟩ := ih m hm j
    refine ⟨J, hbJ, hJ, ?_⟩
    intro c hc
    exact Nat.le_trans (hBoundJ c hc) (Nat.le_of_lt hm)
  choose J hJmem hJfront hJbound using hRec
  let L : Finset (closedCellOwner Z) :=
    K.biUnion fun b => if hb : b ∈ K then J b hb else ∅
  let Jfinal : Finset (closedCellOwner Z) := insert ⟨n, i⟩ L
  refine ⟨Jfinal, by simp [Jfinal], ?_, ?_⟩
  · -- The distinguished cell contributes its frontier cover, and every recursively chosen family
    -- keeps its own frontier cover after enlarging the carrier.
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hbL
    · exact hKfrontier.trans <|
        closedCellCarrier_mono Z fun c hc ↦
          Finset.mem_insert_of_mem <|
            Finset.mem_biUnion.mpr ⟨c, hc, by simpa [hc] using hJmem c hc⟩
    · rcases Finset.mem_biUnion.mp hbL with ⟨c, hcK, hbJ⟩
      have hbJ' : b ∈ J c hcK := by
        simpa [hcK] using hbJ
      exact (hJfront c hcK b hbJ').trans <|
        closedCellCarrier_mono Z fun d hd ↦
          Finset.mem_insert_of_mem <|
            Finset.mem_biUnion.mpr ⟨c, hcK, by simpa [L, hcK] using hd⟩
  · -- Every recursively added owner already satisfies the same ambient dimension bound.
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hbL
    · simp
    · rcases Finset.mem_biUnion.mp hbL with ⟨c, hcK, hbJ⟩
      have hbJ' : b ∈ J c hcK := by
        simpa [hcK] using hbJ
      exact hJbound c hcK b hbJ'

/-- Helper for Lemma 10.2.6: every point of an absolute CW complex lies in a finite
frontier-closed closed-cell carrier. -/
private theorem point_mem_openCell_frontierClosedCarrier
    (Z : Type*) [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    (x : Z) :
    ∃ a : closedCellOwner Z, ∃ J : Finset (closedCellOwner Z),
      a ∈ J ∧ frontierClosedCellFamily Z J ∧
        (∀ b ∈ J, b.1 ≤ a.1) ∧
        x ∈ Topology.CWComplex.openCell (C := (Set.univ : Set Z)) a.1 a.2 := by
  have hx : x ∈ (Set.univ : Set Z) := by
    simp
  -- Choose the open cell containing `x`, then frontier-close that owner while keeping the
  -- resulting dimension bound available for later skeleton arguments.
  rw [← Topology.CWComplex.iUnion_openCell_eq_complex (C := (Set.univ : Set Z))] at hx
  rcases Set.mem_iUnion.1 hx with ⟨n, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  obtain ⟨J, haJ, hJ, hBoundJ⟩ := frontierClosedCellFamilyOfOwner Z ⟨n, i⟩
  exact ⟨⟨n, i⟩, J, haJ, hJ, hBoundJ, hxi⟩

/-- Helper for Lemma 10.2.6: the open cell of an owner inside a frontier-closed family stays
inside the corresponding closed-cell carrier. -/
private theorem openCell_subset_closedCellCarrier_of_mem
    (Z : Type*) [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    {J : Finset (closedCellOwner Z)} {a : closedCellOwner Z} (ha : a ∈ J) :
    Topology.CWComplex.openCell (C := (Set.univ : Set Z)) a.1 a.2 ⊆ closedCellCarrier Z J := by
  -- First place the open cell inside its own closed cell, then embed that closed cell into the
  -- ambient finite carrier using the owner membership `ha`.
  exact
    (Topology.CWComplex.openCell_subset_closedCell (C := (Set.univ : Set Z)) a.1 a.2).trans
      (closedCell_subset_closedCellCarrier_of_mem Z ha)

/-- Helper for Lemma 10.2.6: every point of an absolute CW complex lies in a finite
frontier-closed closed-cell carrier. -/
private theorem point_mem_frontierClosedCarrier
    (Z : Type*) [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    (x : Z) :
    ∃ J : Finset (closedCellOwner Z), frontierClosedCellFamily Z J ∧ x ∈ closedCellCarrier Z J := by
  obtain ⟨a, J, haJ, hJ, -, hxOpen⟩ := point_mem_openCell_frontierClosedCarrier Z x
  refine ⟨J, hJ, ?_⟩
  exact closedCell_subset_closedCellCarrier_of_mem Z haJ
    (Topology.CWComplex.openCell_subset_closedCell (C := (Set.univ : Set Z)) a.1 a.2 hxOpen)

/-- Helper for Lemma 10.2.6: once the image is known to lie in one finite closed-cell carrier,
the target finite-union conclusion is just a reindexing of that carrier. -/
private theorem rangeSubset_finiteClosedCellUnion_of_subset_closedCellCarrier
    (Z : Type*) [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    {K : Type*} [TopologicalSpace K]
    (g : K → Z)
    {J : Finset (closedCellOwner Z)}
    (hRange : Set.range g ⊆ closedCellCarrier Z J) :
    ∃ I : Finset (Σ n, Topology.CWComplex.cell (Set.univ : Set Z) n),
      Set.range g ⊆ ⋃ a ∈ I, Topology.CWComplex.closedCell (C := (Set.univ : Set Z)) a.1 a.2 := by
  -- Forget the sigma-indexed carrier wrapper: `closedCellCarrier Z J` is already the required
  -- finite union of ambient closed cells.
  refine ⟨J, ?_⟩
  simpa [closedCellCarrier] using hRange

/-- Helper for Lemma 10.2.6: every subset of an absolute CW complex lies in the sigma-indexed
union of all ambient closed cells. -/
private theorem subset_iUnion_closedCell
    (Z : Type*) [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    (S : Set Z) :
    S ⊆
      ⋃ a : closedCellOwner Z,
        Topology.CWComplex.closedCell (C := (Set.univ : Set Z)) a.1 a.2 := by
  intro x hx
  have hxUniv : x ∈ (Set.univ : Set Z) := by
    simp
  -- Rewrite the absolute CW union axiom into the sigma-indexed closed-cell language.
  rw [← Topology.CWComplex.union (C := (Set.univ : Set Z))] at hxUniv
  simpa [closedCellOwner, Set.mem_iUnion, exists_prop] using hxUniv

/-- Helper for Lemma 10.2.6: every compact subset of an absolute CW complex is contained in
finitely many ambient closed cells. -/
private theorem compactSubset_subset_finiteClosedCellUnion
    (Z : Type*) [TopologicalSpace Z]
    [CWComplex (Set.univ : Set Z)]
    {S : Set Z} (hS : IsCompact S) :
    ∃ I : Finset (Σ n, Topology.CWComplex.cell (Set.univ : Set Z) n),
      S ⊆ ⋃ a ∈ I, Topology.CWComplex.closedCell (C := (Set.univ : Set Z)) a.1 a.2 := by
  -- Route correction: the attempted ambient-open-cell subcover route is invalid because
  -- `openCell` need not be open in the ambient topology. We still normalize the global carrier to
  -- the sigma-indexed closed-cell cover that the missing compactness compression theorem must
  -- finitely shrink.
  have hCover :
      S ⊆ ⋃ a : closedCellOwner Z,
        Topology.CWComplex.closedCell (C := (Set.univ : Set Z)) a.1 a.2 :=
    subset_iUnion_closedCell Z S
  -- TODO: compress the sigma-indexed closed-cell cover `hCover` to a finite subcover by a valid
  -- compactness argument that does not assume ambient open-cell openness.
  sorry

/-- Helper for Lemma 10.2.6: the image of a continuous map from a compact Hausdorff source lies in
finitely many ambient closed cells. -/
private theorem rangeSubset_sigmaFiniteClosedCellUnion_of_compHausMap
    (Z : Type*) [TopologicalSpace Z]
    [CWComplex (Set.univ : Set Z)]
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (g : K → Z) (hg : Continuous g) :
    ∃ I : Finset (Σ n, Topology.CWComplex.cell (Set.univ : Set Z) n),
      Set.range g ⊆ ⋃ a ∈ I, Topology.CWComplex.closedCell (C := (Set.univ : Set Z)) a.1 a.2 := by
  -- Specialize the compact-subset owner theorem to the compact image of `g`.
  exact compactSubset_subset_finiteClosedCellUnion Z (isCompact_range hg)

/-- Helper for Lemma 10.2.6: frontier saturation is a pure post-processing step on any finite
closed-cell cover. -/
private theorem subset_frontierClosedCarrier_of_finiteClosedCellUnion
    (Z : Type*) [TopologicalSpace Z]
    [CWComplex (Set.univ : Set Z)]
    (S : Set Z)
    {I : Finset (closedCellOwner Z)}
    (hI :
      S ⊆ ⋃ a ∈ I, Topology.CWComplex.closedCell (C := (Set.univ : Set Z)) a.1 a.2) :
    ∃ J : Finset (closedCellOwner Z),
      frontierClosedCellFamily Z J ∧ S ⊆ closedCellCarrier Z J := by
  classical
  choose J hJmem hJfrontier hJbound using
    frontierClosedCellFamilyOfOwner (Z := Z)
  let U : Finset {J : Finset (closedCellOwner Z) // frontierClosedCellFamily Z J} :=
    I.image fun a ↦ ⟨J a, hJfrontier a⟩
  have hCover :
      S ⊆ ⋃ u ∈ U, closedCellCarrier Z u.1 := by
    intro z hz
    have hz' := hI hz
    simp only [Set.mem_iUnion, exists_prop] at hz' ⊢
    rcases hz' with ⟨a, haI, hza⟩
    refine ⟨⟨J a, hJfrontier a⟩, Finset.mem_image.mpr ⟨a, haI, rfl⟩, ?_⟩
    -- Saturate the chosen owner by its finite frontier-closed family.
    exact closedCell_subset_closedCellCarrier_of_mem Z (hJmem a) hza
  -- Collapse the finitely many frontier-closed families to one frontier-closed carrier.
  exact finiteUnion_frontierClosedCarrier_cover Z S U hCover

/-- Helper for Lemma 10.2.6: the real compactness step is to compress the image of a compact
Hausdorff source into one finite frontier-closed carrier. -/
private theorem rangeSubset_frontierClosedCarrier_of_compHausMap
    (Z : Type*) [TopologicalSpace Z]
    [CWComplex (Set.univ : Set Z)]
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (g : K → Z) (hg : Continuous g) :
    ∃ J : Finset (closedCellOwner Z),
      frontierClosedCellFamily Z J ∧ Set.range g ⊆ closedCellCarrier Z J := by
  obtain ⟨I, hI⟩ := rangeSubset_sigmaFiniteClosedCellUnion_of_compHausMap Z g hg
  -- Route correction: once the compact image is covered by finitely many closed cells, frontier
  -- saturation is now a separate transport lemma rather than part of the compactness core.
  exact subset_frontierClosedCarrier_of_finiteClosedCellUnion Z (Set.range g) hI

/-- Helper for Lemma 10.2.6: the image of a continuous map from a compact Hausdorff source lies in
finitely many closed cells. -/
private theorem rangeSubset_finiteClosedCellUnion_of_compHausMap
    (Z : Type*) [TopologicalSpace Z]
    [CWComplex (Set.univ : Set Z)]
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (g : K → Z) (hg : Continuous g) :
    ∃ I : Finset (Σ n, Topology.CWComplex.cell (Set.univ : Set Z) n),
      Set.range g ⊆ ⋃ a ∈ I, Topology.CWComplex.closedCell (C := (Set.univ : Set Z)) a.1 a.2 := by
  -- The frontier-closed carrier theorem is now transport-only, so the core compactness statement
  -- is the direct finite closed-cell cover of the image.
  exact rangeSubset_sigmaFiniteClosedCellUnion_of_compHausMap Z g hg

/-- Helper for Lemma 10.2.6: closedness on every `K ×ˢ closedCell_Y q k` forces closedness on the
entire strip `K ×ˢ univ` when `K` is compact. -/
private theorem closedOnCompactStrip_of_closedOnYCells
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)]
    (A : Set (X × Y)) (K : Set X)
    (hClosed :
      ∀ q (k : Topology.CWComplex.cell (Set.univ : Set Y) q),
        IsClosed
          (A ∩ (K ×ˢ Topology.CWComplex.closedCell (C := (Set.univ : Set Y)) q k))) :
    IsClosed (A ∩ (K ×ˢ (Set.univ : Set Y))) := by
  -- Route correction: test closedness against compact Hausdorff maps into `X × Y`, then reduce the
  -- second-coordinate image to finitely many `Y`-closed cells.
  refine CompactlyGeneratedSpace.isClosed' ?_
  intro S _ _ _ g hg
  let gY : S → Y := fun s ↦ (g s).2
  have hgY : Continuous gY := continuous_snd.comp hg
  obtain ⟨I, hI⟩ :=
    rangeSubset_finiteClosedCellUnion_of_compHausMap Y gY hgY
  have hpiece :
      ∀ a ∈ I,
        IsClosed
          (g ⁻¹'
            (A ∩
              (K ×ˢ Topology.CWComplex.closedCell (C := (Set.univ : Set Y)) a.1 a.2))) := by
    intro a ha
    exact (hClosed a.1 a.2).preimage hg
  have hunion :=
    preimage_compactStrip_eq_biUnion_of_snd_range_subset_closedCells X Y A K g I hI
  rw [hunion]
  exact isClosed_biUnion_finset hpiece

/-- Helper for Lemma 10.2.6: the main product-cell closedness hypothesis implies closedness on each
`X`-cell strip. -/
private theorem closedOnXCellStrip
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)]
    (A : Set (X × Y))
    (hClosed :
      ∀ n (j : productCWCellIndex X Y n),
        IsClosed (A ∩ productCWCellMap X Y n j '' Metric.closedBall (0 : Fin n → ℝ) 1))
    (p : ℕ) (i : Topology.CWComplex.cell (Set.univ : Set X) p) :
    IsClosed
      (A ∩
        (Topology.CWComplex.closedCell (C := (Set.univ : Set X)) p i ×ˢ
          (Set.univ : Set Y))) := by
  have hK :
      IsCompact (Topology.CWComplex.closedCell (C := (Set.univ : Set X)) p i) :=
    Topology.RelCWComplex.isCompact_closedCell
      (C := (Set.univ : Set X)) (D := (∅ : Set X)) (n := p) (i := i)
  -- Apply the compact-strip bridge to the compact `X`-closed cell and normalize the product-cell
  -- intersections using the already-proved closed-image formula.
  refine closedOnCompactStrip_of_closedOnYCells X Y A
    (Topology.CWComplex.closedCell (C := (Set.univ : Set X)) p i) ?_
  intro q k
  let j : productCWCellIndex X Y (p + q) := ⟨⟨(p, q), rfl⟩, i, k⟩
  have hjClosed := hClosed (p + q) j
  rw [productCWCell_closedImage_eq] at hjClosed
  simpa [inter_prodStrip_closedCell_assoc] using hjClosed

/-- Helper for Lemma 10.2.6: if every `X`-cell strip is closed, then the whole subset is closed in
`X × Y`. -/
private theorem closedOfClosedOnXCellStrips
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)]
    (A : Set (X × Y))
    (hClosed :
      ∀ p (i : Topology.CWComplex.cell (Set.univ : Set X) p),
        IsClosed
          (A ∩ (Topology.CWComplex.closedCell (C := (Set.univ : Set X)) p i ×ˢ
            (Set.univ : Set Y)))) :
    IsClosed A := by
  -- Route correction: test closedness against compact Hausdorff maps into `X × Y`, then reduce the
  -- first-coordinate image to finitely many `X`-closed cells.
  refine CompactlyGeneratedSpace.isClosed' ?_
  intro S _ _ _ g hg
  let gX : S → X := fun s ↦ (g s).1
  have hgX : Continuous gX := continuous_fst.comp hg
  obtain ⟨I, hI⟩ :=
    rangeSubset_finiteClosedCellUnion_of_compHausMap X gX hgX
  have hpiece :
      ∀ a ∈ I,
        IsClosed
          (g ⁻¹'
            (A ∩
              (Topology.CWComplex.closedCell (C := (Set.univ : Set X)) a.1 a.2 ×ˢ
                (Set.univ : Set Y)))) := by
    intro a ha
    exact (hClosed a.1 a.2).preimage hg
  have hunion :=
    preimage_eq_biUnion_of_fst_range_subset_closedCells X Y A g I hI
  rw [hunion]
  exact isClosed_biUnion_finset hpiece

/-- Closedness for the chosen product CW structure. -/
theorem productCWClosed
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)]
    (A : Set (X × Y)) (hA : A ⊆ (Set.univ : Set (X × Y))) :
    (∀ n j, IsClosed (A ∩ productCWCellMap X Y n j '' Metric.closedBall 0 1)) → IsClosed A := by
  let _hA : A ⊆ (Set.univ : Set (X × Y)) := hA
  intro hClosed
  -- Route correction: reduce the product-cell hypothesis first to closedness on each `X`-cell
  -- strip, and then close the ambient weak-topology step through the finite-cell compact-image
  -- reduction.
  exact closedOfClosedOnXCellStrips X Y A fun p i ↦ closedOnXCellStrip X Y A hClosed p i

/-- Helper for Lemma 10.2.6: the product open cells cover `X × Y`. -/
private theorem productCWOpenCell_union
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)] :
    ⋃ (n : ℕ) (j : productCWCellIndex X Y n), productCWCellMap X Y n j '' Metric.ball 0 1 =
      (Set.univ : Set (X × Y)) := by
  ext x
  constructor
  · intro hx
    simp
  · intro _hx
    have hxX : x.1 ∈
        ⋃ (p : ℕ) (i : Topology.CWComplex.cell (Set.univ : Set X) p),
          Topology.CWComplex.map p i '' Metric.ball (0 : Fin p → ℝ) 1 := by
      have hxX' : x.1 ∈ (Set.univ : Set X) := by
        simp
      -- The factor CW structure covers `X` by its open cells.
      rw [← Topology.CWComplex.iUnion_openCell_eq_complex (C := (Set.univ : Set X))] at hxX'
      simpa only [Topology.CWComplex.openCell] using hxX'
    have hxY : x.2 ∈
        ⋃ (q : ℕ) (k : Topology.CWComplex.cell (Set.univ : Set Y) q),
          Topology.CWComplex.map q k '' Metric.ball (0 : Fin q → ℝ) 1 := by
      have hxY' : x.2 ∈ (Set.univ : Set Y) := by
        simp
      -- The same open-cell cover holds in the second factor.
      rw [← Topology.CWComplex.iUnion_openCell_eq_complex (C := (Set.univ : Set Y))] at hxY'
      simpa only [Topology.CWComplex.openCell] using hxY'
    rcases Set.mem_iUnion.1 hxX with ⟨p, hxX⟩
    rcases Set.mem_iUnion.1 hxX with ⟨i, hxi⟩
    rcases Set.mem_iUnion.1 hxY with ⟨q, hxY⟩
    rcases Set.mem_iUnion.1 hxY with ⟨k, hyk⟩
    -- Repackage the two factor open cells as the `(p,q)`-product cell of dimension `p + q`.
    let pq : { pq : ℕ × ℕ // pq.1 + pq.2 = p + q } := ⟨(p, q), rfl⟩
    let j : productCWCellIndex X Y (p + q) := Sigma.mk pq (i, k)
    refine Set.mem_iUnion.2 ⟨p + q, Set.mem_iUnion.2 ⟨j, ?_⟩⟩
    rw [productCWCell_openImage_eq]
    exact Set.mem_prod.2 ⟨hxi, hyk⟩

/-- Helper for Lemma 10.2.6: each product closed cell is compact. -/
private theorem productCWCell_isCompact_closedImage
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)]
    (n : ℕ) (j : productCWCellIndex X Y n) :
    IsCompact (productCWCellMap X Y n j '' Metric.closedBall (0 : Fin n → ℝ) 1) := by
  rcases j with ⟨⟨⟨p, q⟩, hpq⟩, i, k⟩
  -- Normalize the product closed cell to the product of the two factor closed cells.
  rw [productCWCell_closedImage_eq]
  exact
    (Topology.RelCWComplex.isCompact_closedCell
      (C := (Set.univ : Set X)) (D := (∅ : Set X)) (n := p) (i := i)).prod
    (Topology.RelCWComplex.isCompact_closedCell
      (C := (Set.univ : Set Y)) (D := (∅ : Set Y)) (n := q) (i := k))

/-- The closed cells of the chosen product CW structure cover `X × Y`. -/
theorem productCWCell_union
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)] :
    ⋃ (n : ℕ) (j : productCWCellIndex X Y n), productCWCellMap X Y n j '' Metric.closedBall 0 1 =
      (Set.univ : Set (X × Y)) := by
  ext x
  constructor
  · intro hx
    simp
  · intro _hx
    have hxX : x.1 ∈
        ⋃ (p : ℕ) (i : Topology.CWComplex.cell (Set.univ : Set X) p),
          Topology.CWComplex.map p i '' Metric.closedBall (0 : Fin p → ℝ) 1 := by
      have hxX' : x.1 ∈ (Set.univ : Set X) := by simp
      -- The factor CW structure covers `X` by its closed cells.
      rw [← Topology.CWComplex.union (C := (Set.univ : Set X))] at hxX'
      simpa only [Topology.CWComplex.closedCell] using hxX'
    have hxY : x.2 ∈
        ⋃ (q : ℕ) (k : Topology.CWComplex.cell (Set.univ : Set Y) q),
          Topology.CWComplex.map q k '' Metric.closedBall (0 : Fin q → ℝ) 1 := by
      have hxY' : x.2 ∈ (Set.univ : Set Y) := by simp
      -- The same closed-cell cover holds in the second factor.
      rw [← Topology.CWComplex.union (C := (Set.univ : Set Y))] at hxY'
      simpa only [Topology.CWComplex.closedCell] using hxY'
    rcases Set.mem_iUnion.1 hxX with ⟨p, hxX⟩
    rcases Set.mem_iUnion.1 hxX with ⟨i, hxi⟩
    rcases Set.mem_iUnion.1 hxY with ⟨q, hxY⟩
    rcases Set.mem_iUnion.1 hxY with ⟨k, hyk⟩
    -- Repackage the two factor closed cells as the `(p,q)`-product cell of dimension `p + q`.
    let pq : { pq : ℕ × ℕ // pq.1 + pq.2 = p + q } := ⟨(p, q), rfl⟩
    let j : productCWCellIndex X Y (p + q) := Sigma.mk pq (i, k)
    refine Set.mem_iUnion.2 ⟨p + q, Set.mem_iUnion.2 ⟨j, ?_⟩⟩
    rw [productCWCell_closedImage_eq]
    exact Set.mem_prod.2 ⟨hxi, hyk⟩

/-- Lemma 10.2.6. The product `X × Y` of CW complexes carries a chosen CW structure on the
compactly generated product topology, with one `n`-cell for each pair consisting of a `p`-cell of
`X` and a `q`-cell of `Y` with `p + q = n`. The explicit hypothesis
`[CompactlyGeneratedSpace (X × Y)]` records the Chapter 5/10 convention that the product carries
the compactly generated replacement of the ordinary product topology. -/
@[expose, implicit_reducible]
noncomputable def productCWComplex
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)] :
    CWComplex (Set.univ : Set (X × Y)) where
  cell := productCWCellIndex X Y
  map := productCWCellMap X Y
  source_eq := productCWCell_source_eq X Y
  continuousOn := productCWCell_continuousOn X Y
  continuousOn_symm := productCWCell_continuousOn_symm X Y
  pairwiseDisjoint' := productCWCell_pairwiseDisjoint X Y
  mapsTo' := productCWCell_mapsTo X Y
  closed' := productCWClosed X Y
  union' := productCWCell_union X Y

/-- The product of two CW complexes carries the chosen product CW structure `productCWComplex`. -/
noncomputable instance instCWComplexProd
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)] :
    CWComplex (Set.univ : Set (X × Y)) :=
  productCWComplex X Y

/-- In the chosen product CW structure from `productCWComplex`, the `n`-cells are indexed by pairs
consisting of a `p`-cell of `X` and a `q`-cell of `Y` with `p + q = n`. -/
abbrev productCWComplex_cellEquiv
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)] (n : ℕ) :
    (productCWComplex X Y).cell n ≃ productCWCellIndex X Y n :=
  Equiv.refl _

theorem productCWComplex_cellEquiv_apply
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)] (n : ℕ)
    (j : (productCWComplex X Y).cell n) :
    productCWComplex_cellEquiv X Y n j = j :=
  rfl

/-- The compactly generated product of two CW complexes is a CW complex. -/
theorem prod_isCWComplex
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)] :
    Nonempty (CWComplex (Set.univ : Set (X × Y))) := by
  exact ⟨productCWComplex X Y⟩
