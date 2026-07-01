import SmoothManifoldsLee.Chap05.Sec05_29.Theorem_5_8.LocalSliceAtlas

open scoped Manifold

universe u

open Set ChartedSpace

section

variable {n k : ℕ} {M : Type u} [TopologicalSpace M]
variable [TopologicalManifold n M]
variable [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]

/-- Helper for Theorem 5.8: after centering both the subtype chart and the ambient slice chart at
the chosen point, Lee's coordinate comparison can be expressed through named centered charts. -/
noncomputable def slice_condition_centered_subtype_chart
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k) (x : S) :
    OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin k)) :=
  (slice_condition_chartAt (S := S) hS x).centerAt
    ⟨x, slice_condition_chartAt_mem_source (S := S) hS x⟩

/-- Helper for Theorem 5.8: the ambient slice chart centered at the same base point is packaged as
a named local chart for the immersion normal form. -/
noncomputable def slice_condition_centered_ambient_chart
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k) (x : S) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
  (slice_condition_ambient_chart (S := S) hS x).centerAt
    ⟨x.1, slice_condition_ambient_chart_mem_source (S := S) hS x⟩

/-- Helper for Theorem 5.8: after centering both the subtype chart and the ambient slice chart at
the chosen point, the subtype inclusion has the literal zero-tail coordinate form. -/
theorem centered_slice_condition_subtype_val_coordinate_formula
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k)
    (x : S) (hk : k ≤ n)
    {z : EuclideanSpace ℝ (Fin k)}
    (hz : z ∈ (slice_condition_centered_subtype_chart (S := S) hS x).target) :
    (slice_condition_centered_ambient_chart (S := S) hS x)
      ((((slice_condition_centered_subtype_chart (S := S) hS x).symm z).1)) =
      euclidean_slice_inclusion hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) z := by
  let eS := slice_condition_chartAt (S := S) hS x
  let eM := slice_condition_ambient_chart (S := S) hS x
  let domChart := slice_condition_centered_subtype_chart (S := S) hS x
  let codChart := slice_condition_centered_ambient_chart (S := S) hS x
  let pS : eS.source := ⟨x, slice_condition_chartAt_mem_source (S := S) hS x⟩
  let pM : eM.source := ⟨x.1, slice_condition_ambient_chart_mem_source (S := S) hS x⟩
  let c := slice_condition_tail_constants (S := S) hS x hk
  have hz_uncentered : z + eS x ∈ eS.target := by
    -- Undo the centering translation to recover the original subtype-chart target membership.
    simpa [domChart, eS, pS, slice_condition_centered_subtype_chart] using
      centerAt_add_base_mem_target eS pS hz
  have hx_target : eS x ∈ eS.target := eS.map_source pS.2
  have hsymm :
      ((domChart.symm z : S)) = eS.symm (z + eS x) := by
    -- The centered inverse is the old inverse evaluated after adding back the basepoint value.
    simpa [domChart, eS, pS, slice_condition_centered_subtype_chart] using
      centerAt_symm_apply_eq_symm_add eS pS hz
  have hmove :
      eM (((domChart.symm z).1)) =
        euclidean_slice_inclusion hk c (z + eS x) := by
    -- Rewrite the centered inverse back into the uncentered chart and apply the raw slice formula.
    calc
      eM (((domChart.symm z).1)) = eM ((eS.symm (z + eS x)).1) := by
        rw [hsymm]
      _ = euclidean_slice_inclusion hk c (z + eS x) := by
        exact slice_condition_subtype_val_coordinate_formula (S := S) hS x hk hz_uncentered
  have hbase :
      eM x.1 = euclidean_slice_inclusion hk c (eS x) := by
    -- Evaluate the uncentered inclusion formula at the base point itself.
    calc
      eM x.1 = eM (((eS.symm (eS x)).1)) := by
        rw [eS.left_inv pS.2]
      _ = euclidean_slice_inclusion hk c (eS x) := by
        exact slice_condition_subtype_val_coordinate_formula (S := S) hS x hk hx_target
  -- Subtract the fixed basepoint tail to reach Lee's literal zero-tail normal form.
  calc
    codChart ((((domChart.symm z).1))) =
      eM ((((domChart.symm z).1))) - eM x.1 := by
        simp [codChart, eM, slice_condition_centered_ambient_chart,
          centerAt_apply_eq_sub_basepoint]
    _ = euclidean_slice_inclusion hk c (z + eS x) -
          euclidean_slice_inclusion hk c (eS x) := by
        rw [hmove, hbase]
    _ = euclidean_slice_inclusion hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) z := by
        simpa [c] using euclidean_slice_inclusion_sub_base hk c z (eS x)

/-- Helper for Theorem 5.8: on the target of the centered subtype chart, the transport-heavy
written-in-charts composite reduces to the ordinary centered ambient chart formula. -/
theorem centered_subtype_val_extend_formula
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k)
    (x : S) {z : EuclideanSpace ℝ (Fin k)}
    (_hz : z ∈ (slice_condition_centered_subtype_chart (S := S) hS x).target) :
    ((slice_condition_centered_ambient_chart (S := S) hS x).extend (𝓡 n) ∘
        Subtype.val ∘
        ((slice_condition_centered_subtype_chart (S := S) hS x).extend (𝓡 k)).symm) z =
      (slice_condition_centered_ambient_chart (S := S) hS x)
        ((((slice_condition_centered_subtype_chart (S := S) hS x).symm z).1)) := by
  let domChart := slice_condition_centered_subtype_chart (S := S) hS x
  let codChart := slice_condition_centered_ambient_chart (S := S) hS x
  -- Route correction: cache the `extend`/`symm`/Subtype normalization before the immersion proof
  -- asks for the zero-tail coordinate formula.
  simp [domChart, codChart, Function.comp, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm]

/-- Helper for Theorem 5.8: at a fixed point of the slice-induced atlas, the subtype inclusion is
an immersion with complement `ℝ^{n-k}`. -/
theorem subtype_val_isImmersionAtOfComplement_of_local_slice_condition
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k)
    (hk : k ≤ n) (x : S) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) S :=
      slice_condition_chartedSpace (S := S) hS
    let _ : TopologicalManifold k S := topologicalManifoldOfChartedSpace k S
    let _ : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S :=
      slice_condition_chartedSpace_isManifold (S := S) hS
    Manifold.IsImmersionAtOfComplement (EuclideanSpace ℝ (Fin (n - k)))
      (𝓡 k) (𝓡 n) (⊤ : WithTop ℕ∞) (Subtype.val : S → M) x := by
  let cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) S :=
    slice_condition_chartedSpace (S := S) hS
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) S := cs
  let tm : TopologicalManifold k S := topologicalManifoldOfChartedSpace k S
  let _ : TopologicalManifold k S := tm
  let hs : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S :=
    slice_condition_chartedSpace_isManifold (S := S) hS
  let _ : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S := hs
  let domChart := slice_condition_centered_subtype_chart (S := S) hS x
  let codChart := slice_condition_centered_ambient_chart (S := S) hS x
  have hx_dom : x ∈ domChart.source := by
    simpa [domChart, OpenPartialHomeomorph.centerAt_source] using
      slice_condition_chartAt_mem_source (S := S) hS x
  have hx_cod : x.1 ∈ codChart.source := by
    simpa [codChart, OpenPartialHomeomorph.centerAt_source] using
      slice_condition_ambient_chart_mem_source (S := S) hS x
  have hdom_base :
      slice_condition_chartAt (S := S) hS x ∈
        cs.atlas := by
    -- In the induced atlas, `chartAt x` is definitionally the chosen slice chart at `x`.
    exact ⟨x, rfl⟩
  have hdom_max :
      domChart ∈ IsManifold.maximalAtlas (𝓡 k) (⊤ : WithTop ℕ∞) S := by
    -- First pass from the induced atlas to the maximal atlas, then center the chart.
    exact centerAt_mem_maximalAtlas
      (e := slice_condition_chartAt (S := S) hS x)
      (he := IsManifold.subset_maximalAtlas hdom_base)
      ⟨x, slice_condition_chartAt_mem_source (S := S) hS x⟩
  have hcod_max :
      codChart ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M := by
    -- The ambient slice chart is already in the ambient maximal atlas, and centering preserves
    -- that membership.
    exact centerAt_mem_maximalAtlas
      (e := slice_condition_ambient_chart (S := S) hS x)
      (he := slice_condition_ambient_chart_mem_maximalAtlas (S := S) hS x)
      ⟨x.1, slice_condition_ambient_chart_mem_source (S := S) hS x⟩
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    (euclidean_slice_product_equiv hk) domChart codChart
    hx_dom hx_cod hdom_max hcod_max ?_ ?_
  · intro y hy
    -- Centering does not change the source sets, so the ambient-source inclusion reduces to the
    -- previously proved uncentered source-containment lemma.
    simpa [domChart, codChart, OpenPartialHomeomorph.centerAt_source] using
      slice_condition_chartAt_source_subset_ambient_source (S := S) hS x
        (by simpa [domChart, OpenPartialHomeomorph.centerAt_source] using hy)
  · intro z hz
    have hz_target :
        z ∈ domChart.target := by
      -- In the Euclidean model, the extended chart target agrees with the original chart target.
      simpa [domChart, OpenPartialHomeomorph.extend_target', modelWithCornersSelf_coe] using hz
    -- First collapse the written-in-charts transport, then apply Lee's centered zero-tail
    -- formula, and finally rewrite the result through the product-model equivalence.
    calc
      ((codChart.extend (𝓡 n)) ∘ Subtype.val ∘ (domChart.extend (𝓡 k)).symm) z =
        codChart ((((domChart).symm z).1)) := by
          exact centered_subtype_val_extend_formula (S := S) hS x hz_target
      _ = euclidean_slice_inclusion hk (fun _ : Fin (n - k) ↦ (0 : ℝ)) z := by
          exact centered_slice_condition_subtype_val_coordinate_formula
            (S := S) hS x hk hz_target
      _ = euclidean_slice_product_equiv hk (z, (0 : EuclideanSpace ℝ (Fin (n - k)))) := by
          symm
          exact euclidean_slice_product_equiv_apply_zero hk z

/-- Helper for Theorem 5.8: the subtype inclusion is an immersion with the fixed complement
`ℝ^{n-k}` once the local `k`-slice atlas has been installed on `S`. -/
theorem subtype_val_isImmersionOfComplement_of_local_slice_condition
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k)
    (hk : k ≤ n) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) S :=
      slice_condition_chartedSpace (S := S) hS
    let _ : TopologicalManifold k S := topologicalManifoldOfChartedSpace k S
    let _ : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S :=
      slice_condition_chartedSpace_isManifold (S := S) hS
    Manifold.IsImmersionOfComplement (EuclideanSpace ℝ (Fin (n - k)))
      (𝓡 k) (𝓡 n) (⊤ : WithTop ℕ∞) (Subtype.val : S → M) := by
  let cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) S :=
    slice_condition_chartedSpace (S := S) hS
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) S := cs
  let tm : TopologicalManifold k S := topologicalManifoldOfChartedSpace k S
  let _ : TopologicalManifold k S := tm
  let hs : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S :=
    slice_condition_chartedSpace_isManifold (S := S) hS
  let _ : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S := hs
  change Manifold.IsImmersionOfComplement (EuclideanSpace ℝ (Fin (n - k)))
    (𝓡 k) (𝓡 n) (⊤ : WithTop ℕ∞) (Subtype.val : S → M)
  intro x
  -- The global immersion statement is now just the pointwise normal-form theorem specialized at
  -- each subtype point.
  exact subtype_val_isImmersionAtOfComplement_of_local_slice_condition
    (S := S) hS hk x

/-- Helper for Theorem 5.8: the local slice condition equips `S` with the induced smooth
boundaryless manifold structure for which the subtype inclusion is a smooth embedding. -/
theorem local_slice_condition_has_embedded_submanifold_structure
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k) :
    ∃ tm : TopologicalManifold k S,
      let _ : TopologicalManifold k S := tm
      ∃ hs : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S,
        let _ : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S := hs
        IsEmbeddedSubmanifold (𝓡 n) (𝓡 k) S := by
  by_cases hEmpty : S = ∅
  · subst hEmpty
    exact empty_subtype_embedded_submanifold_structure
  · have hS_nonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
    have hk : k ≤ n :=
      satisfies_local_slice_condition_dimension_le (S := S) hS_nonempty hS
    let cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) S :=
      slice_condition_chartedSpace (S := S) hS
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) S := cs
    let tm : TopologicalManifold k S := topologicalManifoldOfChartedSpace k S
    refine ⟨tm, ?_⟩
    let _ : TopologicalManifold k S := tm
    let hs : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S :=
      slice_condition_chartedSpace_isManifold (S := S) hS
    refine ⟨hs, ?_⟩
    let _ : IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S := hs
    have hImm :
        Manifold.IsImmersionOfComplement (EuclideanSpace ℝ (Fin (n - k)))
          (𝓡 k) (𝓡 n) (⊤ : WithTop ℕ∞) (Subtype.val : S → M) :=
      subtype_val_isImmersionOfComplement_of_local_slice_condition (S := S) hS hk
    -- The slice-induced structure is boundaryless, and the subtype inclusion is the canonical
    -- topological embedding together with the immersion just proved.
    refine
      { toBoundarylessManifold := inferInstance
        isSmoothEmbedding_subtype_val := ?_ }
    exact ⟨hImm.isImmersion, Topology.IsEmbedding.subtypeVal⟩

end
