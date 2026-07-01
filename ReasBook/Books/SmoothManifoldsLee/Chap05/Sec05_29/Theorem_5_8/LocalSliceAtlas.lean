import SmoothManifoldsLee.Chap05.Sec05_29.Theorem_5_8.Common

open scoped Manifold

universe u

open Set ChartedSpace

section

variable {n k : ℕ} {M : Type u} [TopologicalSpace M]
variable [TopologicalManifold n M]
variable [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]

/-- Helper for Theorem 5.8: the open patch of the subtype `S` cut out by an ambient chart source is
homeomorphic to the corresponding intersection subset of `M`. -/
noncomputable def subtype_patch_intersection_homeomorph
    (S T : Set M) :
    {y : S | y.1 ∈ T} ≃ₜ (S ∩ T : Set M) where
  toEquiv := Equiv.subtypeSubtypeEquivSubtypeInter (fun x : M ↦ x ∈ S) (fun x : M ↦ x ∈ T)
  -- The forward map just forgets the nested subtype structure and remembers the intersection data.
  continuous_toFun := by
    exact Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun y ↦ by exact ⟨y.1.2, y.2⟩)
  -- The inverse repackages an intersection point as a point of `S` lying in `T`.
  continuous_invFun := by
    have hToS : Continuous fun y : (S ∩ T : Set M) ↦ (⟨y.1, y.2.1⟩ : S) :=
      Continuous.subtype_mk continuous_subtype_val (fun y ↦ y.2.1)
    exact Continuous.subtype_mk hToS (fun y ↦ y.2.2)

/-- Helper for Theorem 5.8: once the ambient slice image equality is fixed, the subtype patch of
`S` inside the chart source is homeomorphic to the Euclidean slice from Lee's construction. -/
noncomputable def slice_chart_patch_homeomorph
    (S : Set M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {hk : k ≤ n} {c : Fin (n - k) → ℝ}
    (hSlice : e '' (S ∩ e.source) = Set.euclideanSlice e.target k hk c) :
    {y : S | y.1 ∈ e.source} ≃ₜ Set.euclideanSlice e.target k hk c :=
  -- First identify the subtype patch with the ambient intersection, then use the ambient chart.
  (subtype_patch_intersection_homeomorph (S := S) (T := e.source)).trans
    (e.homeomorphOfImageSubsetSource
      (fun _ hx ↦ hx.2)
      hSlice)

/-- Helper for Theorem 5.8: the patch homeomorphism sends a subtype point to its ambient chart
coordinates. -/
theorem slice_chart_patch_homeomorph_apply
    (S : Set M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {hk : k ≤ n} {c : Fin (n - k) → ℝ}
    (hSlice : e '' (S ∩ e.source) = Set.euclideanSlice e.target k hk c)
    (y : {z : S | z.1 ∈ e.source}) :
    (slice_chart_patch_homeomorph (S := S) (e := e) hSlice y).1 = e y.1.1 := by
  -- Both ingredients of the composed homeomorphism are literal restriction maps, so the result is
  -- the ambient chart value of the underlying point.
  rfl

/-- Helper for Theorem 5.8: the inverse patch homeomorphism recovers the ambient point by the
inverse ambient chart. -/
theorem slice_chart_patch_homeomorph_symm_apply
    (S : Set M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {hk : k ≤ n} {c : Fin (n - k) → ℝ}
    (hSlice : e '' (S ∩ e.source) = Set.euclideanSlice e.target k hk c)
    (z : Set.euclideanSlice e.target k hk c) :
    ((slice_chart_patch_homeomorph (S := S) (e := e) hSlice).symm z).1.1 = e.symm z.1 := by
  -- Unfold the inverse of the restricted ambient-chart homeomorphism and forget the subtype data.
  rfl

/-- Helper for Theorem 5.8: the canonical open patch of `S` cut out by the ambient chart source. -/
noncomputable def subtype_source_patch
    (S : Set M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) :
    TopologicalSpace.Opens S :=
  ⟨{y : S | y.1 ∈ e.source}, by
    simpa [Set.preimage, Function.comp] using e.open_source.preimage continuous_subtype_val⟩

/-- Helper for Theorem 5.8: the canonical open patch type is definitionally the raw subtype patch
appearing in Lee's construction. -/
noncomputable def subtype_source_patch_opens_homeomorph
    (S : Set M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) :
    subtype_source_patch (S := S) e ≃ₜ {y : S | y.1 ∈ e.source} := by
  -- Route correction: fix the source type first, then all later chart compositions occur on the
  -- canonical `Opens S` owner instead of fighting coercions between equivalent subtype carriers.
  change subtype_source_patch (S := S) e ≃ₜ subtype_source_patch (S := S) e
  exact Homeomorph.refl _

/-- Helper for Theorem 5.8: an ambient slice chart induces a chart on the canonical patch
`V = U ∩ S` by projecting to the first `k` coordinates. -/
noncomputable def slice_chart_induces_patch_chart
    (S : Set M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e.IsSliceChart S k)
    (x : S) (hx : x.1 ∈ e.source) :
    OpenPartialHomeomorph (subtype_source_patch (S := S) e) (EuclideanSpace ℝ (Fin k)) := by
  classical
  let hk : k ≤ n := Classical.choose he.2
  have hc :
      ∃ c : Fin (n - k) → ℝ,
        e '' (S ∩ e.source) = Set.euclideanSlice e.target k hk c :=
    by simpa [hk] using (Classical.choose_spec he.2)
  let c : Fin (n - k) → ℝ := Classical.choose hc
  let hSlice : e '' (S ∩ e.source) = Set.euclideanSlice e.target k hk c :=
    Classical.choose_spec hc
  let xPatch : {y : S | y.1 ∈ e.source} := ⟨x, hx⟩
  let xSlice : Set.euclideanSlice e.target k hk c :=
    slice_chart_patch_homeomorph (S := S) (e := e) hSlice xPatch
  -- First identify `V = U ∩ S` with the Euclidean slice, then project away the fixed tail
  -- coordinates exactly as in the source proof.
  change OpenPartialHomeomorph {y : S | y.1 ∈ e.source} (EuclideanSpace ℝ (Fin k))
  exact OpenPartialHomeomorph.trans'
    ((slice_chart_patch_homeomorph (S := S) (e := e) hSlice).toOpenPartialHomeomorph)
    (euclidean_slice_projection_partial_homeomorph e.target e.open_target hk c xSlice)
    rfl

/-- Helper for Theorem 5.8: composing the patch chart with the inclusion of the canonical open
patch into `S` gives the pointed chart on `S` used for the induced atlas. -/
noncomputable def slice_chart_induces_pointed_subtype_chart
    (S : Set M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e.IsSliceChart S k)
    (x : S) (hx : x.1 ∈ e.source) :
    OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin k)) := by
  let P : TopologicalSpace.Opens S := subtype_source_patch (S := S) e
  let xP : P := ⟨x, hx⟩
  -- Route correction: the transport-heavy step is isolated in the chart on `P`; including `P`
  -- back into `S` is now a single clean composition.
  exact ((P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).symm).trans
    (slice_chart_induces_patch_chart (S := S) (e := e) he x hx)

/-- Helper for Theorem 5.8: the patch chart induced from an ambient slice chart is defined at the
distinguished point of the canonical patch. -/
theorem slice_chart_induces_patch_chart_mem_source
    (S : Set M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e.IsSliceChart S k)
    (x : S) (hx : x.1 ∈ e.source) :
    (⟨x, hx⟩ : subtype_source_patch (S := S) e) ∈
      (slice_chart_induces_patch_chart (S := S) (e := e) he x hx).source := by
  classical
  let hk : k ≤ n := Classical.choose he.2
  let hc :
      ∃ c : Fin (n - k) → ℝ,
        e '' (S ∩ e.source) = Set.euclideanSlice e.target k hk c :=
    by simpa [hk] using (Classical.choose_spec he.2)
  let c : Fin (n - k) → ℝ := Classical.choose hc
  let hSlice : e '' (S ∩ e.source) = Set.euclideanSlice e.target k hk c :=
    Classical.choose_spec hc
  let xPatch : {y : S | y.1 ∈ e.source} := ⟨x, hx⟩
  let xSlice : Set.euclideanSlice e.target k hk c :=
    slice_chart_patch_homeomorph (S := S) (e := e) hSlice xPatch
  -- The first stage is a global homeomorphism, so the only source condition comes from the
  -- Euclidean slice chart, which is defined at the distinguished slice point by construction.
  change xPatch ∈
    (OpenPartialHomeomorph.trans'
      ((slice_chart_patch_homeomorph (S := S) (e := e) hSlice).toOpenPartialHomeomorph)
      (euclidean_slice_projection_partial_homeomorph e.target e.open_target hk c xSlice)
      rfl).source
  exact mem_univ xPatch

/-- Helper for Theorem 5.8: choose, for each `x : S`, the induced subtype chart coming from a
slice-chart witness for `x`. -/
noncomputable def slice_condition_ambient_chart
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k) (x : S) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
  Classical.choose (hS.exists_sliceChart x.1 x.2)

/-- Helper for Theorem 5.8: the chosen ambient chart for `x : S` contains `x` in its source. -/
theorem slice_condition_ambient_chart_mem_source
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k) (x : S) :
    x.1 ∈ (slice_condition_ambient_chart (S := S) hS x).source :=
  (Classical.choose_spec (hS.exists_sliceChart x.1 x.2)).1

/-- Helper for Theorem 5.8: the chosen ambient chart for `x : S` is a `k`-slice chart for `S`. -/
theorem slice_condition_ambient_chart_isSliceChart
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k) (x : S) :
    (slice_condition_ambient_chart (S := S) hS x).IsSliceChart S k :=
  (Classical.choose_spec (hS.exists_sliceChart x.1 x.2)).2

/-- Helper for Theorem 5.8: the ambient chart chosen from the local slice condition already lies
in the smooth maximal atlas of `M`. -/
theorem slice_condition_ambient_chart_mem_maximalAtlas
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k) (x : S) :
    slice_condition_ambient_chart (S := S) hS x ∈
      IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M := by
  -- The local slice witness packages maximal-atlas membership together with the Euclidean slice
  -- description, and only the former is needed for later compatibility arguments.
  exact (slice_condition_ambient_chart_isSliceChart (S := S) hS x).mem_maximalAtlas

/-- Helper for Theorem 5.8: a nonempty subset satisfying the local `k`-slice condition can only
occur when `k ≤ n`. -/
theorem satisfies_local_slice_condition_dimension_le
    (S : Set M) (hS_nonempty : S.Nonempty)
    (hS : Set.SatisfiesLocalSliceCondition n S k) :
    k ≤ n := by
  rcases hS_nonempty with ⟨x, hx⟩
  rcases hS.exists_sliceChart x hx with ⟨e, hxsource, he⟩
  -- Any one slice witness already records the Euclidean-slice codimension `n - k`.
  rcases he.2 with ⟨hk, c, hSlice⟩
  exact hk

/-- Helper for Theorem 5.8: once a global inequality `k ≤ n` is fixed, each chosen ambient slice
chart has canonical tail constants compatible with that global choice. -/
noncomputable def slice_condition_tail_constants
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k)
    (x : S) (_hk : k ≤ n) : Fin (n - k) → ℝ :=
  let he := slice_condition_ambient_chart_isSliceChart (S := S) hS x
  let hc := Classical.choose_spec he.2
  Classical.choose hc

/-- Helper for Theorem 5.8: the image of the chosen ambient chart for `x : S` is the Euclidean
slice cut out by the canonical tail constants attached to that chart. -/
theorem slice_condition_ambient_chart_image_eq_slice
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k)
    (x : S) (hk : k ≤ n) :
    slice_condition_ambient_chart (S := S) hS x '' (S ∩
        (slice_condition_ambient_chart (S := S) hS x).source) =
      Set.euclideanSlice
        (slice_condition_ambient_chart (S := S) hS x).target
        k hk
        (slice_condition_tail_constants (S := S) hS x hk) := by
  let e := slice_condition_ambient_chart (S := S) hS x
  let he := slice_condition_ambient_chart_isSliceChart (S := S) hS x
  let hk' : k ≤ n := Classical.choose he.2
  let hc :
      ∃ c : Fin (n - k) → ℝ,
        e '' (S ∩ e.source) = Set.euclideanSlice e.target k hk' c :=
    Classical.choose_spec he.2
  let c : Fin (n - k) → ℝ := Classical.choose hc
  let hSlice : e '' (S ∩ e.source) = Set.euclideanSlice e.target k hk' c :=
    Classical.choose_spec hc
  -- The local slice witness already has the right constants; proof irrelevance identifies its
  -- inequality witness with the globally fixed `hk`.
  have hhk : hk' = hk := Subsingleton.elim _ _
  subst hk'
  simpa [slice_condition_tail_constants, e, he] using hSlice

/-- Helper for Theorem 5.8: choose, for each `x : S`, the induced subtype chart coming from a
slice-chart witness for `x`. -/
noncomputable def slice_condition_chartAt
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k) (x : S) :
    OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin k)) :=
  slice_chart_induces_pointed_subtype_chart (S := S)
    (slice_condition_ambient_chart (S := S) hS x)
    (slice_condition_ambient_chart_isSliceChart (S := S) hS x)
    x
    (slice_condition_ambient_chart_mem_source (S := S) hS x)

/-- Helper for Theorem 5.8: the chosen induced subtype chart is centered at the point it was
selected for, so its source contains that point. -/
theorem slice_condition_chartAt_mem_source
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k) (x : S) :
    x ∈ (slice_condition_chartAt (S := S) hS x).source := by
  let e := slice_condition_ambient_chart (S := S) hS x
  let he := slice_condition_ambient_chart_isSliceChart (S := S) hS x
  let hx := slice_condition_ambient_chart_mem_source (S := S) hS x
  let P : TopologicalSpace.Opens S := subtype_source_patch (S := S) e
  let xP : P := ⟨x, hx⟩
  -- The pointed chart source is the intersection of the open-patch inclusion source and the patch
  -- chart source; both contain the distinguished point by construction.
  change x ∈
    (((P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).symm).trans
      (slice_chart_induces_patch_chart (S := S) (e := e) he x hx)).source
  rw [OpenPartialHomeomorph.trans_source]
  constructor
  · simpa [P] using hx
  · simpa [P, xP] using
      slice_chart_induces_patch_chart_mem_source (S := S) (e := e) he x hx

/-- Helper for Theorem 5.8: any point lying in an induced subtype chart source already lies in the
source of the ambient slice chart from which that subtype chart was built. -/
theorem slice_condition_chartAt_source_subset_ambient_source
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k)
    (x : S) {y : S}
    (hy : y ∈ (slice_condition_chartAt (S := S) hS x).source) :
    y.1 ∈ (slice_condition_ambient_chart (S := S) hS x).source := by
  let e := slice_condition_ambient_chart (S := S) hS x
  let he := slice_condition_ambient_chart_isSliceChart (S := S) hS x
  let hx := slice_condition_ambient_chart_mem_source (S := S) hS x
  let P : TopologicalSpace.Opens S := subtype_source_patch (S := S) e
  let xP : P := ⟨x, hx⟩
  -- Membership in the source of the pointed chart already forces membership in the target of the
  -- open-patch inclusion, which is exactly the ambient-chart source condition on the subtype.
  change y.1 ∈ e.source
  change y ∈
    (((P.openPartialHomeomorphSubtypeCoe ⟨xP⟩).symm).trans
      (slice_chart_induces_patch_chart (S := S) (e := e) he x hx)).source at hy
  rw [OpenPartialHomeomorph.trans_source] at hy
  simpa [P, xP] using hy.1

/-- Helper for Theorem 5.8: the pointed subtype chart evaluates by first restricting to the open
patch and then applying the patch chart. -/
theorem pointed_subtype_chart_apply_via_patch
    (S : Set M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e.IsSliceChart S k)
    (x : S) (hx : x.1 ∈ e.source) {y : S}
    (hy : y ∈
      ((((subtype_source_patch (S := S) e).openPartialHomeomorphSubtypeCoe ⟨⟨x, hx⟩⟩).symm).trans
        (slice_chart_induces_patch_chart (S := S) (e := e) he x hx)).source) :
    (((((subtype_source_patch (S := S) e).openPartialHomeomorphSubtypeCoe ⟨⟨x, hx⟩⟩).symm).trans
        (slice_chart_induces_patch_chart (S := S) (e := e) he x hx)) y) =
      slice_chart_induces_patch_chart (S := S) (e := e) he x hx
        ⟨y, by
          -- The trans-source condition supplies the ambient-source proof for the patch subtype.
          rw [OpenPartialHomeomorph.trans_source] at hy
          simpa [subtype_source_patch] using hy.1⟩ := by
  let P : TopologicalSpace.Opens S := subtype_source_patch (S := S) e
  let iP : OpenPartialHomeomorph P S := P.openPartialHomeomorphSubtypeCoe ⟨⟨x, hx⟩⟩
  -- Split the trans-source hypothesis once, so the remaining proof only uses the open-patch
  -- inclusion and the patch chart separately.
  rw [OpenPartialHomeomorph.trans_source] at hy
  -- After unfolding the composition, it is enough to rewrite the inverse of the open-patch
  -- inclusion as the canonical subtype packaging of `y`.
  rw [OpenPartialHomeomorph.trans_apply]
  have hyTarget : y ∈ iP.target := by
    simpa [iP, P, subtype_source_patch] using hy.1
  have hsymm :
      (iP.symm y : P) =
        ⟨y, by
          simpa [P, subtype_source_patch] using hy.1⟩ := by
    -- Two points of the patch subtype are equal once their underlying points of `S` agree.
    apply Subtype.ext
    simpa using iP.right_inv hyTarget
  rw [hsymm]

/-- Helper for Theorem 5.8: the inverse pointed subtype chart is the patch-chart inverse followed
by the canonical inclusion of the open patch into `S`. -/
theorem pointed_subtype_chart_symm_via_patch
    (S : Set M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e.IsSliceChart S k)
    (x : S) (hx : x.1 ∈ e.source)
    {z : EuclideanSpace ℝ (Fin k)}
    (_hz : z ∈
      ((((subtype_source_patch (S := S) e).openPartialHomeomorphSubtypeCoe ⟨⟨x, hx⟩⟩).symm).trans
        (slice_chart_induces_patch_chart (S := S) (e := e) he x hx)).target) :
    ((((((subtype_source_patch (S := S) e).openPartialHomeomorphSubtypeCoe ⟨⟨x, hx⟩⟩).symm).trans
        (slice_chart_induces_patch_chart (S := S) (e := e) he x hx)).symm z : S)) =
      ((slice_chart_induces_patch_chart (S := S) (e := e) he x hx).symm z :
        subtype_source_patch (S := S) e) := by
  -- Rewrite the inverse of the composition as the composition of inverses; the final inclusion of
  -- the patch into `S` is definitionally the subtype coercion.
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
  rfl

/-- Helper for Theorem 5.8: the induced pointed subtype chart is literally the projection of the
ambient slice chart on source points. -/
theorem slice_condition_chartAt_apply
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k)
    (x : S) (hk : k ≤ n) {y : S}
    (hy : y ∈ (slice_condition_chartAt (S := S) hS x).source) :
    slice_condition_chartAt (S := S) hS x y =
      euclidean_slice_projection hk
        ((slice_condition_ambient_chart (S := S) hS x) y.1) := by
  classical
  let e := slice_condition_ambient_chart (S := S) hS x
  let he := slice_condition_ambient_chart_isSliceChart (S := S) hS x
  let hx := slice_condition_ambient_chart_mem_source (S := S) hS x
  let hk' : k ≤ n := Classical.choose he.2
  have hhk : hk' = hk := Subsingleton.elim _ _
  subst hk'
  let c := slice_condition_tail_constants (S := S) hS x hk
  have hSlice :
      e '' (S ∩ e.source) = Set.euclideanSlice e.target k hk c := by
    simpa [e, he, slice_condition_tail_constants] using
      slice_condition_ambient_chart_image_eq_slice (S := S) hS x hk
  let yPatch : subtype_source_patch (S := S) e := ⟨y, by
    -- Source points of the induced subtype chart lie in the ambient chart source.
    exact slice_condition_chartAt_source_subset_ambient_source (S := S) hS x hy⟩
  -- Route correction: first flatten the pointed subtype chart to the patch chart, then read off
  -- Lee's literal `π ∘ φ` formula from the patch-level projection chart.
  change
    (((((subtype_source_patch (S := S) e).openPartialHomeomorphSubtypeCoe ⟨⟨x, hx⟩⟩).symm).trans
      (slice_chart_induces_patch_chart (S := S) (e := e) he x hx)) y) =
      euclidean_slice_projection hk (e y.1)
  rw [pointed_subtype_chart_apply_via_patch (S := S) (e := e) he x hx hy]
  change
    (slice_chart_induces_patch_chart (S := S) (e := e) he x hx) yPatch =
      euclidean_slice_projection hk (e y.1)
  change
    (euclidean_slice_projection_partial_homeomorph e.target e.open_target hk c
      (slice_chart_patch_homeomorph (S := S) (e := e) hSlice ⟨x, hx⟩))
        ((slice_chart_patch_homeomorph (S := S) (e := e) hSlice) yPatch) =
      euclidean_slice_projection hk (e y.1)
  rw [euclidean_slice_projection_partial_homeomorph_apply]
  rw [slice_chart_patch_homeomorph_apply]

/-- Helper for Theorem 5.8: the inverse pointed subtype chart recovers the ambient point by
reinserting the fixed tail coordinates, and the same fixed-tail point lies in the ambient chart
target. -/
theorem slice_condition_chartAt_symm_image_data
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k)
    (x : S) (hk : k ≤ n) {z : EuclideanSpace ℝ (Fin k)}
    (hz : z ∈ (slice_condition_chartAt (S := S) hS x).target) :
    ((slice_condition_chartAt (S := S) hS x).symm z).1 =
        (slice_condition_ambient_chart (S := S) hS x).symm
          (euclidean_slice_inclusion hk
            (slice_condition_tail_constants (S := S) hS x hk) z) ∧
      euclidean_slice_inclusion hk
          (slice_condition_tail_constants (S := S) hS x hk) z ∈
        (slice_condition_ambient_chart (S := S) hS x).target := by
  -- Route correction: this combined inverse-data lemma replaces the previous duplicated pair
  -- `slice_condition_chartAt_symm_val` / `slice_condition_chartAt_target_mem_ambient_target`.
  classical
  let e := slice_condition_ambient_chart (S := S) hS x
  let he := slice_condition_ambient_chart_isSliceChart (S := S) hS x
  let hx := slice_condition_ambient_chart_mem_source (S := S) hS x
  let c := slice_condition_tail_constants (S := S) hS x hk
  have hSlice :
      e '' (S ∩ e.source) = Set.euclideanSlice e.target k hk c := by
    simpa [e, he, c, slice_condition_tail_constants] using
      slice_condition_ambient_chart_image_eq_slice (S := S) hS x hk
  let xPatch : {y : S | y.1 ∈ e.source} := ⟨x, hx⟩
  let xSlice : Set.euclideanSlice e.target k hk c :=
    slice_chart_patch_homeomorph (S := S) (e := e) hSlice xPatch
  let patchChart :=
    slice_chart_induces_patch_chart (S := S) (e := e) he x hx
  let sliceChart :=
    euclidean_slice_projection_partial_homeomorph e.target e.open_target hk c xSlice
  have hzPatch : z ∈ patchChart.target := by
    -- The pointed subtype chart only differs from the patch chart by the open-patch inclusion,
    -- whose inverse has full target.
    simpa [slice_condition_chartAt, slice_chart_induces_pointed_subtype_chart, e, he, hx,
      patchChart, OpenPartialHomeomorph.trans_target] using hz
  have hzSlice : z ∈ sliceChart.target := by
    -- The patch-to-slice homeomorphism is global, so the patch-chart target is exactly the
    -- Euclidean-slice chart target.
    simpa [patchChart, sliceChart, OpenPartialHomeomorph.trans_target] using hzPatch
  let w : Set.euclideanSlice e.target k hk c := sliceChart.symm z
  have hw_val : w.1 = euclidean_slice_inclusion hk c z := by
    -- The Euclidean slice chart inverse is the fixed-tail inclusion.
    simpa [w, sliceChart] using
      euclidean_slice_projection_partial_homeomorph_symm_apply e.target e.open_target hk c xSlice
        hzSlice
  have hw_target : euclidean_slice_inclusion hk c z ∈ e.target := by
    -- The inverse slice point automatically lies in the ambient target of the slice subtype.
    simpa [hw_val] using w.2.1
  have hpatch_to_slice_source :
      slice_chart_patch_homeomorph (S := S) (e := e) hSlice (patchChart.symm z) ∈ sliceChart.source := by
    -- Read the trans-source condition off the inverse image point of the composed patch chart.
    have hzPatchSymm : patchChart.symm z ∈ patchChart.source := by
      exact patchChart.symm.map_source hzPatch
    simpa [patchChart, OpenPartialHomeomorph.trans_source] using hzPatchSymm
  have hpatch_apply :
      sliceChart
          (slice_chart_patch_homeomorph (S := S) (e := e) hSlice (patchChart.symm z)) = z := by
    -- Expanding the composed patch chart gives the literal `π`-formula on the slice patch.
    simpa [patchChart, sliceChart, OpenPartialHomeomorph.trans_apply] using
      patchChart.right_inv hzPatch
  have hpatch_to_slice :
      slice_chart_patch_homeomorph (S := S) (e := e) hSlice (patchChart.symm z) = w := by
    apply Subtype.ext
    calc
      (slice_chart_patch_homeomorph (S := S) (e := e) hSlice (patchChart.symm z)).1 =
          (sliceChart.symm
            (sliceChart
              (slice_chart_patch_homeomorph (S := S) (e := e) hSlice (patchChart.symm z)))).1 := by
            simpa [sliceChart, w] using
              congrArg Subtype.val
                ((sliceChart.left_inv hpatch_to_slice_source).symm)
      _ = (sliceChart.symm z).1 := by rw [hpatch_apply]
      _ = w.1 := rfl
  have hpatch_symm :
      (patchChart.symm z : subtype_source_patch (S := S) e) =
        (slice_chart_patch_homeomorph (S := S) (e := e) hSlice).symm w := by
    -- Invert the patch homeomorphism after identifying its image in the Euclidean slice.
    calc
      (patchChart.symm z : subtype_source_patch (S := S) e) =
          (slice_chart_patch_homeomorph (S := S) (e := e) hSlice).symm
            ((slice_chart_patch_homeomorph (S := S) (e := e) hSlice) (patchChart.symm z)) := by
              symm
              exact (slice_chart_patch_homeomorph (S := S) (e := e) hSlice).left_inv _
      _ = (slice_chart_patch_homeomorph (S := S) (e := e) hSlice).symm w := by
            rw [hpatch_to_slice]
  have hsubtype_symm :
      ((slice_condition_chartAt (S := S) hS x).symm z : S) =
        (patchChart.symm z : subtype_source_patch (S := S) e) := by
    -- The pointed subtype chart inverse is the patch inverse followed by the canonical inclusion
    -- of the open patch into `S`.
    simpa [slice_condition_chartAt, slice_chart_induces_pointed_subtype_chart, e, patchChart] using
      pointed_subtype_chart_symm_via_patch (S := S) (e := e) he x hx hz
  constructor
  · -- Replace the pointed inverse by the patch inverse, then unwind the patch and slice inverses.
    calc
      ((slice_condition_chartAt (S := S) hS x).symm z).1 =
          ((patchChart.symm z : subtype_source_patch (S := S) e)).1.1 := by
            simpa using congrArg Subtype.val hsubtype_symm
      _ = ((slice_chart_patch_homeomorph (S := S) (e := e) hSlice).symm w :
              subtype_source_patch (S := S) e).1.1 := by
            rw [hpatch_symm]
      _ = e.symm w.1 := by
            simpa using
              slice_chart_patch_homeomorph_symm_apply (S := S) (e := e) hSlice w
      _ = e.symm (euclidean_slice_inclusion hk c z) := by rw [hw_val]
  · -- The slice inverse lands in the Euclidean slice subtype, so its underlying point is already
    -- in the ambient chart target.
    simpa [e, c] using hw_target

/-- Helper for Theorem 5.8: the inverse pointed subtype chart recovers the ambient point by
reinserting the fixed tail coordinates. -/
theorem slice_condition_chartAt_symm_val
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k)
    (x : S) (hk : k ≤ n) {z : EuclideanSpace ℝ (Fin k)}
    (hz : z ∈ (slice_condition_chartAt (S := S) hS x).target) :
    ((slice_condition_chartAt (S := S) hS x).symm z).1 =
      (slice_condition_ambient_chart (S := S) hS x).symm
        (euclidean_slice_inclusion hk
          (slice_condition_tail_constants (S := S) hS x hk) z) := by
  -- The first component of the combined inverse-data lemma is Lee's inverse-chart formula.
  exact (slice_condition_chartAt_symm_image_data (S := S) hS x hk hz).1

/-- Helper for Theorem 5.8: overlap maps of the induced subtype atlas have Lee's literal
`π ∘ e_y ∘ e_x.symm ∘ j_x` coordinate formula. -/
theorem slice_condition_chartAt_transition_formula
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k)
    (x y : S) (hk : k ≤ n) {z : EuclideanSpace ℝ (Fin k)}
    (hz : z ∈ ((slice_condition_chartAt (S := S) hS x).symm.trans
      (slice_condition_chartAt (S := S) hS y)).source) :
    slice_condition_chartAt (S := S) hS y
      ((slice_condition_chartAt (S := S) hS x).symm z) =
        euclidean_slice_projection hk
          ((slice_condition_ambient_chart (S := S) hS y)
            ((slice_condition_ambient_chart (S := S) hS x).symm
              (euclidean_slice_inclusion hk
                (slice_condition_tail_constants (S := S) hS x hk) z))) := by
  rw [OpenPartialHomeomorph.trans_source] at hz
  have hzTarget : z ∈ (slice_condition_chartAt (S := S) hS x).target := by
    simpa using hz.1
  have hval :
      ((slice_condition_chartAt (S := S) hS x).symm z).1 =
        (slice_condition_ambient_chart (S := S) hS x).symm
          (euclidean_slice_inclusion hk
            (slice_condition_tail_constants (S := S) hS x hk) z) :=
    (slice_condition_chartAt_symm_image_data (S := S) hS x hk hzTarget).1
  -- Apply Lee's explicit chart formula for the target chart, then rewrite the underlying point
  -- of the inverse subtype chart using the combined inverse-data lemma.
  calc
    slice_condition_chartAt (S := S) hS y
        ((slice_condition_chartAt (S := S) hS x).symm z) =
      euclidean_slice_projection hk
        ((slice_condition_ambient_chart (S := S) hS y)
          (((slice_condition_chartAt (S := S) hS x).symm z).1)) := by
        rw [slice_condition_chartAt_apply (S := S) hS y hk hz.2]
    _ = euclidean_slice_projection hk
        ((slice_condition_ambient_chart (S := S) hS y)
          ((slice_condition_ambient_chart (S := S) hS x).symm
            (euclidean_slice_inclusion hk
              (slice_condition_tail_constants (S := S) hS x hk) z))) := by
        rw [hval]

/-- Helper for Theorem 5.8: a point in the target of the induced subtype chart has its fixed-tail
ambient representative in the target of the ambient slice chart. -/
theorem slice_condition_chartAt_target_mem_ambient_target
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k)
    (x : S) (hk : k ≤ n) {z : EuclideanSpace ℝ (Fin k)}
    (hz : z ∈ (slice_condition_chartAt (S := S) hS x).target) :
    euclidean_slice_inclusion hk
        (slice_condition_tail_constants (S := S) hS x hk) z ∈
      (slice_condition_ambient_chart (S := S) hS x).target := by
  -- The second component of the combined inverse-data lemma is exactly the needed target proof.
  exact (slice_condition_chartAt_symm_image_data (S := S) hS x hk hz).2

/-- Helper for Theorem 5.8: the fixed-tail inclusion sends overlap points of the induced subtype
charts into the source of the ambient chart transition `e_x.symm.trans e_y`. -/
theorem slice_condition_chartAt_transition_source_mapsTo_ambient_transition_source
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k)
    (x y : S) (hk : k ≤ n) :
    Set.MapsTo
      (euclidean_slice_inclusion hk (slice_condition_tail_constants (S := S) hS x hk))
      (((slice_condition_chartAt (S := S) hS x).symm.trans
          (slice_condition_chartAt (S := S) hS y)).source)
      (((slice_condition_ambient_chart (S := S) hS x).symm.trans
          (slice_condition_ambient_chart (S := S) hS y)).source) := by
  intro z hz
  rw [OpenPartialHomeomorph.trans_source] at hz ⊢
  have hzTarget : z ∈ (slice_condition_chartAt (S := S) hS x).target := by
    simpa using hz.1
  have hdata :=
    slice_condition_chartAt_symm_image_data (S := S) hS x hk hzTarget
  have hyAmbient :
      (((slice_condition_chartAt (S := S) hS x).symm z).1) ∈
        (slice_condition_ambient_chart (S := S) hS y).source :=
    slice_condition_chartAt_source_subset_ambient_source (S := S) hS y hz.2
  constructor
  · exact hdata.2
  · -- Rewriting the source point through the combined inverse-data lemma aligns the overlap source
    -- with the ambient transition source.
    simpa [hdata.1] using hyAmbient

/-- Helper for Theorem 5.8: Lee's overlap map factors through the ambient maximal-atlas
transition, precomposed with the fixed slice inclusion and postcomposed with the slice projection,
so it is smooth on the overlap source. -/
theorem ambient_transition_precomp_slice_inclusion_contDiffOn
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k)
    (x y : S) (hk : k ≤ n) :
    ContDiffOn ℝ (⊤ : WithTop ℕ∞)
      (fun z =>
        euclidean_slice_projection hk
          ((slice_condition_ambient_chart (S := S) hS y)
            ((slice_condition_ambient_chart (S := S) hS x).symm
              (euclidean_slice_inclusion hk
                (slice_condition_tail_constants (S := S) hS x hk) z))))
      (((slice_condition_chartAt (S := S) hS x).symm.trans
          (slice_condition_chartAt (S := S) hS y)).source) := by
  let ex := slice_condition_ambient_chart (S := S) hS x
  let ey := slice_condition_ambient_chart (S := S) hS y
  let c := slice_condition_tail_constants (S := S) hS x hk
  have hex : ex ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M :=
    slice_condition_ambient_chart_mem_maximalAtlas (S := S) hS x
  have hey : ey ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M :=
    slice_condition_ambient_chart_mem_maximalAtlas (S := S) hS y
  have hcompat :
      ex.symm.trans ey ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n) :=
    IsManifold.compatible_of_mem_maximalAtlas hex hey
  have hambient :
      ContDiffOn ℝ (⊤ : WithTop ℕ∞)
        (fun u => ey (ex.symm u))
        ((ex.symm.trans ey).source) := by
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid] at hcompat
    simpa [ex, ey, Function.comp, modelWithCornersSelf_coe, OpenPartialHomeomorph.coe_trans]
      using hcompat.1
  have hinclusion :
      ContDiffOn ℝ (⊤ : WithTop ℕ∞) (euclidean_slice_inclusion hk c)
        (((slice_condition_chartAt (S := S) hS x).symm.trans
            (slice_condition_chartAt (S := S) hS y)).source) := by
    simpa [contMDiff_iff_contDiff] using
      (euclidean_slice_inclusion_contMDiff hk c).contDiff.contDiffOn
  have hprecompose :
      ContDiffOn ℝ (⊤ : WithTop ℕ∞)
        (fun z => ey (ex.symm (euclidean_slice_inclusion hk c z)))
        (((slice_condition_chartAt (S := S) hS x).symm.trans
            (slice_condition_chartAt (S := S) hS y)).source) := by
    -- The overlap-source maps-to lemma aligns the subtype-chart source with the ambient chart
    -- transition source needed for chart compatibility.
    exact hambient.comp hinclusion
      (slice_condition_chartAt_transition_source_mapsTo_ambient_transition_source
        (S := S) hS x y hk)
  have hprojection :
      ContDiffOn ℝ (⊤ : WithTop ℕ∞) (euclidean_slice_projection hk) Set.univ := by
    simpa [contMDiff_iff_contDiff] using
      (euclidean_slice_projection_contMDiff hk).contDiff.contDiffOn
  -- Postcompose the ambient transition with the Euclidean slice projection.
  exact hprojection.comp hprecompose (by intro z hz; simp)

/-- Helper for Theorem 5.8: overlap maps of the induced subtype atlas are smooth because Lee's
formula factors them through the ambient maximal-atlas transition and the fixed Euclidean slice
projection/inclusion maps. -/
theorem slice_condition_chartAt_transition_contDiffOn
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k)
    (x y : S) (hk : k ≤ n) :
    ContDiffOn ℝ (⊤ : WithTop ℕ∞)
      (fun z =>
        slice_condition_chartAt (S := S) hS y
          ((slice_condition_chartAt (S := S) hS x).symm z))
      (((slice_condition_chartAt (S := S) hS x).symm.trans
          (slice_condition_chartAt (S := S) hS y)).source) := by
  -- Lee's formula is now explicit, so smoothness follows by replacing the transition map with the
  -- already-controlled ambient factorization.
  refine (ambient_transition_precomp_slice_inclusion_contDiffOn
    (S := S) hS x y hk).congr ?_
  intro z hz
  exact slice_condition_chartAt_transition_formula (S := S) hS x y hk hz

/-- Helper for Theorem 5.8: in the induced slice coordinates, the subtype inclusion is exactly the
fixed-tail Euclidean inclusion. -/
theorem slice_condition_subtype_val_coordinate_formula
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k)
    (x : S) (hk : k ≤ n) {z : EuclideanSpace ℝ (Fin k)}
    (hz : z ∈ (slice_condition_chartAt (S := S) hS x).target) :
    (slice_condition_ambient_chart (S := S) hS x)
      (((slice_condition_chartAt (S := S) hS x).symm z).1) =
        euclidean_slice_inclusion hk
          (slice_condition_tail_constants (S := S) hS x hk) z := by
  have hdata :=
    slice_condition_chartAt_symm_image_data (S := S) hS x hk hz
  -- Apply the ambient chart to Lee's inverse-chart formula and use the target-membership part of
  -- the same data to collapse `e (e.symm _)`.
  calc
    (slice_condition_ambient_chart (S := S) hS x)
        (((slice_condition_chartAt (S := S) hS x).symm z).1) =
      (slice_condition_ambient_chart (S := S) hS x)
        ((slice_condition_ambient_chart (S := S) hS x).symm
          (euclidean_slice_inclusion hk
            (slice_condition_tail_constants (S := S) hS x hk) z)) := by
        rw [hdata.1]
    _ = euclidean_slice_inclusion hk
        (slice_condition_tail_constants (S := S) hS x hk) z := by
        exact (slice_condition_ambient_chart (S := S) hS x).right_inv hdata.2

/-- Helper for Theorem 5.8: the local slice condition packages the induced subtype charts into a
charted-space structure on `S`. -/
noncomputable abbrev slice_condition_chartedSpace
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k) :
    ChartedSpace (EuclideanSpace ℝ (Fin k)) S where
  atlas := {e | ∃ x : S, e = slice_condition_chartAt (S := S) hS x}
  chartAt := slice_condition_chartAt (S := S) hS
  mem_chart_source := slice_condition_chartAt_mem_source (S := S) hS
  chart_mem_atlas x := by
    -- The chosen chart at `x` is, by construction, one of the distinguished slice-induced
    -- charts forming the atlas.
    exact ⟨x, rfl⟩

/-- Helper for Theorem 5.8: the slice-induced atlas on `S` is smooth because Lee's transition
formula factors every overlap map through the ambient maximal-atlas transition. -/
theorem slice_condition_chartedSpace_isManifold
    (S : Set M) (hS : Set.SatisfiesLocalSliceCondition n S k) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) S :=
      slice_condition_chartedSpace (S := S) hS
    let _ : TopologicalManifold k S := topologicalManifoldOfChartedSpace k S
    IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S := by
  let cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) S :=
    slice_condition_chartedSpace (S := S) hS
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) S := cs
  let tm : TopologicalManifold k S := topologicalManifoldOfChartedSpace k S
  let _ : TopologicalManifold k S := tm
  -- The atlas is generated by the distinguished slice charts, so smooth compatibility reduces
  -- exactly to the previously established overlap formula.
  refine isManifold_of_contDiffOn (I := 𝓡 k) (n := (⊤ : WithTop ℕ∞)) (M := S) ?_
  intro e e' he he'
  rcases he with ⟨x, rfl⟩
  rcases he' with ⟨y, rfl⟩
  have hk : k ≤ n := satisfies_local_slice_condition_dimension_le
    (S := S) (hS_nonempty := ⟨x.1, x.2⟩) hS
  simpa using slice_condition_chartAt_transition_contDiffOn (S := S) hS x y hk

/-- A local `k`-slice structure on `S ⊆ M` yields a boundaryless topological `k`-manifold
structure on the subtype `S` with the induced topology. -/
-- Proof sketch: from each slice chart for `S`, project the ambient coordinates to the first `k`
-- coordinates to obtain charts on the subtype, then check that the resulting transition maps are
-- continuous; in fact they are smooth because they are compositions of smooth ambient chart
-- transitions with the coordinate projection and the inclusion of the fixed slice.
theorem satisfiesLocalSliceCondition_has_topological_manifold_structure
    (S : Set M)
    (hS : Set.SatisfiesLocalSliceCondition n S k) :
    ∃ tm : TopologicalManifold k S,
      let _ : TopologicalManifold k S := tm
      IsManifold (𝓡 k) (0 : WithTop ℕ∞) S ∧ BoundarylessManifold (𝓡 k) S := by
  -- The slice-induced pointed charts already define a charted-space structure on the subtype.
  let cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) S :=
    slice_condition_chartedSpace (S := S) hS
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) S := cs
  -- The standard `topologicalManifoldOfChartedSpace` constructor then supplies the `C^0`
  -- manifold structure, and boundarylessness is inherited from the Euclidean model.
  let tm : TopologicalManifold k S := topologicalManifoldOfChartedSpace k S
  refine ⟨tm, ?_⟩
  let _ : TopologicalManifold k S := tm
  constructor
  · infer_instance
  · infer_instance

end
