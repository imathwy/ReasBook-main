import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.Topology.Homeomorph.Lemmas
import Books.AConciseCourseInAlgebraicTopology_May_1999.BasedCWComplex
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Proposition_5_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Lemma_5_1_15
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Lemma_10_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Lemma_10_2_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Definition_22_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Lemma_22_1_5.Comparison

universe u v w

-- The repository-wide owner `IsBasedCWComplex` forgets the source-side chosen base `0`-cell /
-- vertex data. This file therefore keeps the explicit finite-subproduct cell description and
-- states the labeled weak-product closure theorem with an explicit vertex conclusion.

variable {ι : Type v}

/-- The points of the weak product supported on the finite set of coordinates `s`. -/
def weakProductSupportedOn (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι) :
    Set ((weakProduct X).toCompactlyGenerated) :=
  { x | ∀ i, i ∉ s → x.1 i = (X i).point }

/-- Membership in `weakProductSupportedOn X s` means that all coordinates outside `s` are the
distinguished basepoints. -/
@[simp] theorem mem_weakProductSupportedOn
    (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι)
    (x : (weakProduct X).toCompactlyGenerated) :
    x ∈ weakProductSupportedOn X s ↔ ∀ i, i ∉ s → x.1 i = (X i).point :=
  Iff.rfl

/-- The closed cell of the weak-product CW structure determined by finitely many factor cells. -/
def weakProductFiniteSubproductClosedCellImage
    (X : ι → PointedCompactlyGenerated.{u, w})
    (cwX : ∀ i, Topology.CWComplex (Set.univ : Set (X i).toCompactlyGenerated))
    (s : Finset ι) (d : s → ℕ) (c : ∀ i : s, (cwX i).cell (d i)) :
    Set ((weakProduct X).toCompactlyGenerated) :=
  { x | x ∈ weakProductSupportedOn X s ∧
      ∀ i : s, x.1 i ∈ (cwX i).map (d i) (c i) '' Metric.closedBall 0 1 }

/-- Membership in `weakProductFiniteSubproductClosedCellImage X cwX s d c` means finite support
outside `s` together with coordinatewise membership in the chosen factor closed cells. -/
@[simp] theorem mem_weakProductFiniteSubproductClosedCellImage
    (X : ι → PointedCompactlyGenerated.{u, w})
    (cwX : ∀ i, Topology.CWComplex (Set.univ : Set (X i).toCompactlyGenerated))
    (s : Finset ι) (d : s → ℕ) (c : ∀ i : s, (cwX i).cell (d i))
    (x : (weakProduct X).toCompactlyGenerated) :
    x ∈ weakProductFiniteSubproductClosedCellImage X cwX s d c ↔
      x ∈ weakProductSupportedOn X s ∧
        ∀ i : s, x.1 i ∈ (cwX i).map (d i) (c i) '' Metric.closedBall 0 1 :=
  Iff.rfl

/-- Helper for Lemma 22.1.6: there is an explicit equivalence between the weak-product slice
supported on `s` and the finite dependent product over `s`, together with its coordinate formulas. -/
theorem weakProductSupportedOnEquivFinitePi_spec
    (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι) :
    ∃ e : {x : (weakProduct X).toCompactlyGenerated // x ∈ weakProductSupportedOn X s} ≃
        ((i : s) → (X i).toCompactlyGenerated),
      (∀ x i, e x i = x.1.1 i) ∧
        (∀ y {i : ι} (hi : i ∈ s), (e.symm y).1.1 i = y ⟨i, hi⟩) ∧
          ∀ y {i : ι}, i ∉ s → (e.symm y).1.1 i = (X i).point := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine
      { toFun := fun x i ↦ x.1.1 i
        invFun := fun y ↦ ?_
        left_inv := ?_
        right_inv := ?_ }
    refine ⟨⟨fun i ↦ if hi : i ∈ s then y ⟨i, hi⟩ else (X i).point, ?_⟩, ?_⟩
    · -- Only coordinates in `s` can differ from the distinguished basepoint.
      change hasFiniteNonbasepointSupport X
        (fun i ↦ if hi : i ∈ s then y ⟨i, hi⟩ else (X i).point)
      rw [hasFiniteNonbasepointSupport_iff]
      refine s.finite_toSet.subset ?_
      intro i hi
      by_contra his
      simp at hi
      exact his hi.choose
    · -- Outside the chosen support, the constructed point is exactly the basepoint tuple.
      intro i hi
      simp [hi]
    · intro x
      apply Subtype.ext
      apply Subtype.ext
      funext i
      -- Coordinates in `s` are read back directly, and outside `s` the support condition rewrites
      -- them to the distinguished basepoint.
      by_cases hi : i ∈ s
      · simp [hi]
      · simpa [hi] using (x.2 i hi).symm
    · intro y
      funext i
      -- On supported coordinates the inverse simply forgets the finite-support proof.
      have hsub : (⟨(i : ι), i.2⟩ : s) = i := by
        apply Subtype.ext
        rfl
      simp [hsub, i.2]
  · intro x i
    rfl
  · intro y i hi
    simp [hi]
  · intro y i hi
    simp [hi]

/-- Helper for Lemma 22.1.6: the supported slice of the weak product is explicitly equivalent to
the finite dependent product over the same support. -/
noncomputable def weakProductSupportedOnEquivFinitePi
    (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι) :
    {x : (weakProduct X).toCompactlyGenerated // x ∈ weakProductSupportedOn X s} ≃
      ((i : s) → (X i).toCompactlyGenerated) :=
  Classical.choose (weakProductSupportedOnEquivFinitePi_spec X s)

/-- Helper for Lemma 22.1.6: the forward direction of
`weakProductSupportedOnEquivFinitePi` is coordinate restriction. -/
@[simp] theorem weakProductSupportedOnEquivFinitePi_apply
    (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι)
    (x : {x : (weakProduct X).toCompactlyGenerated // x ∈ weakProductSupportedOn X s})
    (i : s) :
    weakProductSupportedOnEquivFinitePi X s x i = x.1.1 i :=
  (Classical.choose_spec (weakProductSupportedOnEquivFinitePi_spec X s)).1 x i

/-- Helper for Lemma 22.1.6: on a coordinate lying in `s`, the inverse of
`weakProductSupportedOnEquivFinitePi` recovers the prescribed coordinate value. -/
@[simp] theorem weakProductSupportedOnEquivFinitePi_symm_apply_of_mem
    (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι)
    (y : (i : s) → (X i).toCompactlyGenerated) {i : ι} (hi : i ∈ s) :
    ((weakProductSupportedOnEquivFinitePi X s).symm y).1.1 i = y ⟨i, hi⟩ :=
  (Classical.choose_spec (weakProductSupportedOnEquivFinitePi_spec X s)).2.1 y hi

/-- Helper for Lemma 22.1.6: outside `s`, the inverse of `weakProductSupportedOnEquivFinitePi`
inserts the distinguished basepoint. -/
@[simp] theorem weakProductSupportedOnEquivFinitePi_symm_apply_of_not_mem
    (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι)
    (y : (i : s) → (X i).toCompactlyGenerated) {i : ι} (hi : i ∉ s) :
    ((weakProductSupportedOnEquivFinitePi X s).symm y).1.1 i = (X i).point :=
  (Classical.choose_spec (weakProductSupportedOnEquivFinitePi_spec X s)).2.2 y hi

/-- Helper for Lemma 22.1.6: under the plain supported-slice equivalence, a coordinatewise product
of chosen factor closed cells pulls back to the matching closed-cell condition on the
supported slice. -/
theorem weakProductSupportedOnEquivFinitePi_symm_image_closedCellSet
    (X : ι → PointedCompactlyGenerated.{u, w})
    (cwX : ∀ i, Topology.CWComplex (Set.univ : Set (X i).toCompactlyGenerated))
    (s : Finset ι) (d : s → ℕ) (c : ∀ i : s, (cwX i).cell (d i)) :
    (weakProductSupportedOnEquivFinitePi X s).symm ''
        {y | ∀ i : s, y i ∈ (cwX i).map (d i) (c i) '' Metric.closedBall 0 1} =
      {x | ∀ i : s, x.1.1 i ∈ (cwX i).map (d i) (c i) '' Metric.closedBall 0 1} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    -- On supported coordinates, the inverse equivalence just inserts the prescribed entries.
    intro i
    have hcoord :
        ((weakProductSupportedOnEquivFinitePi X s).symm y).1.1 i = y i := by
      simpa using weakProductSupportedOnEquivFinitePi_symm_apply_of_mem X s y i.2
    exact hcoord ▸ hy i
  · intro hx
    -- Apply the forward equivalence and read the chosen coordinates back coordinatewise.
    refine ⟨weakProductSupportedOnEquivFinitePi X s x, ?_, ?_⟩
    · intro i
      have hcoord :
          weakProductSupportedOnEquivFinitePi X s x i = x.1.1 i := by
        simpa using weakProductSupportedOnEquivFinitePi_apply X s x i
      exact hcoord ▸ hx i
    · simp

/-- Helper for Lemma 22.1.6: forgetting the subtype from the transported supported-slice cell set
recovers the ambient weak-product closed cell determined by the same finite subproduct data. -/
theorem weakProductSupportedOnEquivFinitePi_symm_image_eq_finiteSubproductClosedCellImage
    (X : ι → PointedCompactlyGenerated.{u, w})
    (cwX : ∀ i, Topology.CWComplex (Set.univ : Set (X i).toCompactlyGenerated))
    (s : Finset ι) (d : s → ℕ) (c : ∀ i : s, (cwX i).cell (d i)) :
    Subtype.val '' ((weakProductSupportedOnEquivFinitePi X s).symm ''
        {y | ∀ i : s, y i ∈ (cwX i).map (d i) (c i) '' Metric.closedBall 0 1}) =
      weakProductFiniteSubproductClosedCellImage X cwX s d c := by
  ext x
  constructor
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    -- The subtype witness records the finite support condition, and the coordinate formulas give
    -- the closed-cell membership on each supported index.
    refine ⟨((weakProductSupportedOnEquivFinitePi X s).symm y).2, ?_⟩
    intro i
    have hcoord :
        ((weakProductSupportedOnEquivFinitePi X s).symm y).1.1 i = y i := by
      simpa using weakProductSupportedOnEquivFinitePi_symm_apply_of_mem X s y i.2
    exact hcoord ▸ hy i
  · rintro ⟨hxSupport, hxCell⟩
    -- Repackage the ambient weak-product point as a supported-slice point and then apply the
    -- forward equivalence to obtain the finite-product witness.
    refine ⟨⟨x, hxSupport⟩, ?_, rfl⟩
    refine ⟨weakProductSupportedOnEquivFinitePi X s ⟨x, hxSupport⟩, ?_, ?_⟩
    · intro i
      have hcoord :
          weakProductSupportedOnEquivFinitePi X s ⟨x, hxSupport⟩ i = x.1 i := by
        simpa using weakProductSupportedOnEquivFinitePi_apply X s ⟨x, hxSupport⟩ i
      exact hcoord ▸ hxCell i
    · simp

/-- Helper for Lemma 22.1.6: the compactly generated replacement topology is again
`UCompactlyGeneratedSpace`. -/
private theorem compactlyGeneratedTopologyUCompactlyGeneratedSpace
    (Y : Type w) [TopologicalSpace Y] :
    @UCompactlyGeneratedSpace.{u} Y (TopologicalSpace.compactlyGenerated.{u} Y) := by
  -- Present the replacement topology as the standard coinduced topology on compact probes.
  let f : (Σ (i : (S : CompHaus.{u}) × C(S, Y)), i.fst) → Y := fun y ↦ y.1.2 y.2
  have hf : @Continuous ((Σ (i : (S : CompHaus.{u}) × C(S, Y)), i.fst)) Y
      instTopologicalSpaceSigma (TopologicalSpace.coinduced f inferInstance) f := by
    rw [continuous_iff_coinduced_le]
  exact @uCompactlyGeneratedSpace_of_coinduced.{u, _, _}
    ((Σ (i : (S : CompHaus.{u}) × C(S, Y)), i.fst)) Y instTopologicalSpaceSigma
    (TopologicalSpace.coinduced f inferInstance) inferInstance f hf rfl

/-- Helper for Lemma 22.1.6: compact generation transfers across a homeomorphism. -/
private theorem uCompactlyGeneratedSpace_homeomorph
    {X : Type w} [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X]
    {Y : Type w} [TopologicalSpace Y] (e : X ≃ₜ Y) :
    UCompactlyGeneratedSpace.{u} Y := by
  -- Check continuity after pulling back along the homeomorphism, then compose with the inverse.
  refine uCompactlyGeneratedSpace_of_continuous_maps ?_
  intro Z tZ f hf
  have hPullback : Continuous (f ∘ e) := by
    refine continuous_from_uCompactlyGeneratedSpace (f ∘ e) ?_
    intro S g
    have hComp : Continuous ((f ∘ e) ∘ g) := by
      simpa [Function.comp_def] using hf (CompHaus.of S) ⟨e ∘ g, e.continuous.comp g.continuous⟩
    simpa [Function.comp_def] using hComp
  simpa [Function.comp_def] using hPullback.comp e.symm.continuous

/-- Helper for Lemma 22.1.6: if the first factor is compact Hausdorff and the second factor is
compactly generated, then the ordinary product is compactly generated. -/
private theorem uCompactlyGeneratedSpace_compact_prod
    (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (Y : Type w) [TopologicalSpace Y] [UCompactlyGeneratedSpace.{u} Y] :
    UCompactlyGeneratedSpace.{u} (K × Y) := by
  -- Prove continuity on `K × Y` by currying in the compact variable `K`.
  refine uCompactlyGeneratedSpace_of_continuous_maps ?_
  intro Z tZ f hf
  let F : Y → C(K, Z) := fun y ↦
    ⟨fun k ↦ f (k, y), by
      let gy : C(K, K × Y) := ⟨fun k ↦ (k, y), continuous_id.prodMk continuous_const⟩
      have hsec : Continuous fun k : K ↦ f (k, y) := by
        simpa [gy] using hf (CompHaus.of K) gy
      simpa using hsec⟩
  have hF : Continuous F := by
    -- Check continuity into `C(K, Z)` after testing on compact sources for `Y`.
    refine continuous_from_uCompactlyGeneratedSpace F ?_
    intro S g
    apply ContinuousMap.continuous_of_continuous_uncurry
    let h : C(K × S, K × Y) :=
      ⟨fun p ↦ (p.1, g p.2), continuous_fst.prodMk (g.continuous.comp continuous_snd)⟩
    have huncurry : Continuous fun p : K × S ↦ f (p.1, g p.2) := by
      simpa [Function.comp_def, h] using hf (CompHaus.of (K × S)) h
    have hswap : Continuous fun p : S × K ↦ f (p.2, g p.1) := by
      simpa using huncurry.comp (Homeomorph.prodComm S K).continuous
    simpa [F, Function.comp_def] using hswap
  -- Uncurrying the continuous family `y ↦ (k ↦ f (k, y))` recovers `f`.
  have huncurry : Continuous fun p : Y × K ↦ F p.1 p.2 :=
    ContinuousMap.continuous_uncurry_of_continuous ⟨F, hF⟩
  simpa [F] using huncurry.comp (Homeomorph.prodComm K Y).continuous

/-- Helper for Lemma 22.1.6: compact generation lifts to larger probe universes by precomposing
compact tests with `ULift`. -/
private theorem uCompactlyGeneratedSpaceLift
    (Z : Type u) [TopologicalSpace Z] [UCompactlyGeneratedSpace.{u} Z] :
    UCompactlyGeneratedSpace.{max u v} Z := by
  refine uCompactlyGeneratedSpace_of_isClosed fun s hs ↦ ?_
  refine UCompactlyGeneratedSpace.isClosed fun S ⟨f, hf⟩ ↦ ?_
  let g : ULift.{v} S → Z := f ∘ ULift.down
  have hg : Continuous g := hf.comp continuous_uliftDown
  simpa [g, Set.preimage_comp, Function.comp] using
    (hs (CompHaus.of (ULift.{v} S)) ⟨g, hg⟩).preimage continuous_uliftUp

/-- Helper for Lemma 22.1.6: each weak-product coordinate projection is continuous. -/
theorem weakProductCoordinateContinuous
    (X : ι → PointedCompactlyGenerated.{u, w}) (i : ι) :
    Continuous fun x : (weakProduct X).toCompactlyGenerated ↦ x.1 i := by
  -- The weak product carries the compactly-generated reflection of the raw subtype topology.
  have hraw :
      @Continuous ((weakProduct X).toCompactlyGenerated) (weakProductType X)
        inferInstance instTopologicalSpaceSubtype
        (fun x : (weakProduct X).toCompactlyGenerated ↦ (x : weakProductType X)) := by
    simpa using
      (continuous_id_compactlyGenerated (X := weakProductType X) :
        @Continuous (weakProductType X) (weakProductType X)
          (TopologicalSpace.compactlyGenerated.{u} (weakProductType X))
          instTopologicalSpaceSubtype
          (id : weakProductType X → weakProductType X))
  -- Once we are back in the raw subtype, the coordinate map is the usual subtype projection
  -- followed by evaluation at `i`.
  exact
    (continuous_apply i).comp
      ((continuous_subtype_val : Continuous fun x : weakProductType X ↦ x.1).comp hraw)

/-- Helper for Lemma 22.1.6: restricting a supported weak-product point to one coordinate is
continuous on the supported slice. -/
theorem weakProductSupportedOnCoordinateContinuous
    (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι) (i : ι) :
    Continuous fun x : {x : (weakProduct X).toCompactlyGenerated // x ∈ weakProductSupportedOn X s} ↦
      x.1.1 i := by
  -- The supported slice is a subtype of the weak product, so continuity is inherited.
  exact (weakProductCoordinateContinuous X i).comp continuous_subtype_val

/-- Helper for Lemma 22.1.6: every coordinate of the inverse
`weakProductSupportedOnEquivFinitePi X s` is continuous. -/
theorem weakProductSupportedOnEquivFinitePi_symm_coordinateContinuous
    (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι) (i : ι) :
    Continuous fun y : (j : s) → (X j).toCompactlyGenerated ↦
      ((weakProductSupportedOnEquivFinitePi X s).symm y).1.1 i := by
  -- On supported coordinates the inverse is evaluation, and elsewhere it is constant.
  by_cases hi : i ∈ s
  · simpa [hi] using
      (let ii : s := ⟨i, hi⟩
       (continuous_apply ii :
        Continuous fun y : (j : s) → (X j).toCompactlyGenerated ↦ y ii))
  · simpa [hi] using
      (continuous_const :
        Continuous fun _ : (j : s) → (X j).toCompactlyGenerated ↦ (X i).point)

/-- Helper for Lemma 22.1.6: the forward map
`weakProductSupportedOnEquivFinitePi X s` is continuous. -/
theorem weakProductSupportedOnEquivFinitePi_continuous
    (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι) :
    Continuous (weakProductSupportedOnEquivFinitePi X s) := by
  -- The forward equivalence just restricts a supported weak-product point to the coordinates in
  -- `s`, so continuity reduces to the coordinate projections.
  refine continuous_pi ?_
  intro i
  simpa using weakProductSupportedOnCoordinateContinuous X s i

/-- Helper for Lemma 22.1.6: the inverse of `weakProductSupportedOnEquivFinitePi` is continuous
for the raw subtype topology on `weakProductType X`. -/
theorem weakProductSupportedOnEquivFinitePi_symm_continuousRaw
    (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι) :
    @Continuous ((i : s) → (X i).toCompactlyGenerated) (weakProductType X)
      inferInstance instTopologicalSpaceSubtype
      (fun y ↦ ((weakProductSupportedOnEquivFinitePi X s).symm y).1) := by
  -- The raw weak-product topology is induced from the full product, so coordinatewise
  -- continuity is enough.
  rw [continuous_induced_rng]
  refine continuous_pi ?_
  intro i
  simpa using weakProductSupportedOnEquivFinitePi_symm_coordinateContinuous X s i

/-- Helper for Lemma 22.1.6: a compact-source continuous map stays continuous after replacing the
codomain by its compactly generated topology. -/
private theorem continuousCompHausToCompactlyGeneratedLocal
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {Z : Type w} [TopologicalSpace Z] {f : K → Z} (hf : Continuous f) :
    @Continuous K Z ‹TopologicalSpace K›
      (TopologicalSpace.compactlyGenerated.{u, w} Z) f := by
  let F : (Σ (j : (S : CompHaus.{u}) × C(S, Z)), j.fst) → Z := fun x ↦ x.1.2 x.2
  let i : (S : CompHaus.{u}) × C(S, Z) := ⟨CompHaus.of K, ⟨f, hf⟩⟩
  -- The chosen compact-source map is one of the generators defining the k-ification.
  have hgenerator :
      ∀ j : (S : CompHaus.{u}) × C(S, Z),
        @Continuous j.fst Z inferInstance
          (TopologicalSpace.compactlyGenerated.{u, w} Z)
          (fun a : j.fst ↦ F ⟨j, a⟩) := by
    -- Rewriting to the sigma-family owner exposes the canonical continuity statement.
    rw [TopologicalSpace.compactlyGenerated, ← @continuous_sigma_iff]
    exact continuous_coinduced_rng
  -- Specializing the sigma-family statement recovers continuity of the original map.
  simpa [F, i] using hgenerator i

/-- Helper for Lemma 22.1.6: once the finite supported product carries a compactly generated
topology, the inverse of `weakProductSupportedOnEquivFinitePi` is continuous for the actual
compactly generated weak-product topology. -/
theorem weakProductSupportedOnEquivFinitePi_symm_continuous
    (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι)
    [UCompactlyGeneratedSpace.{u} ((i : s) → (X i).toCompactlyGenerated)] :
    Continuous (weakProductSupportedOnEquivFinitePi X s).symm := by
  let hcont :
      Continuous fun y : (i : s) → (X i).toCompactlyGenerated ↦
        ((weakProductSupportedOnEquivFinitePi X s).symm y).1 := by
    -- Because the domain is compactly generated, it suffices to test compact probes.
    refine continuous_from_uCompactlyGeneratedSpace _ ?_
    intro S g
    have hraw :
        @Continuous S (weakProductType X) inferInstance instTopologicalSpaceSubtype
          (fun y ↦ ((weakProductSupportedOnEquivFinitePi X s).symm (g y)).1) := by
      -- The already-proved raw continuity composes directly with the compact probe.
      exact (weakProductSupportedOnEquivFinitePi_symm_continuousRaw X s).comp g.continuous
    -- Upgrade the codomain from the raw subtype topology to its compactly generated reflection.
    simpa using continuousCompHausToCompactlyGeneratedLocal hraw
  exact hcont.subtype_mk fun y ↦ ((weakProductSupportedOnEquivFinitePi X s).symm y).2

/-- Helper for Lemma 22.1.6: once the finite supported product is compactly generated, the
supported slice of the weak product is homeomorphic to the finite dependent product over `s`. -/
noncomputable def weakProductSupportedOnHomeomorphFinitePi
    (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι)
    [UCompactlyGeneratedSpace.{u} ((i : s) → (X i).toCompactlyGenerated)] :
    {x : (weakProduct X).toCompactlyGenerated // x ∈ weakProductSupportedOn X s} ≃ₜ
      ((i : s) → (X i).toCompactlyGenerated) :=
  { toEquiv := weakProductSupportedOnEquivFinitePi X s
    continuous_toFun := weakProductSupportedOnEquivFinitePi_continuous X s
    continuous_invFun := weakProductSupportedOnEquivFinitePi_symm_continuous X s }

/-- Helper for Lemma 22.1.6: under the supported-slice homeomorphism, a coordinatewise product of
chosen factor closed cells pulls back to the matching closed-cell condition on the weak-product
slice. -/
theorem weakProductSupportedOnHomeomorphFinitePi_symm_image_closedCellSet
    (X : ι → PointedCompactlyGenerated.{u, w})
    (cwX : ∀ i, Topology.CWComplex (Set.univ : Set (X i).toCompactlyGenerated))
    (s : Finset ι) [UCompactlyGeneratedSpace.{u} ((i : s) → (X i).toCompactlyGenerated)]
    (d : s → ℕ) (c : ∀ i : s, (cwX i).cell (d i)) :
    (weakProductSupportedOnHomeomorphFinitePi X s).symm ''
        {y | ∀ i : s, y i ∈ (cwX i).map (d i) (c i) '' Metric.closedBall 0 1} =
      {x | ∀ i : s, x.1.1 i ∈ (cwX i).map (d i) (c i) '' Metric.closedBall 0 1} := by
  -- Route correction: this normalization is set-theoretic, so reduce it to the equivalence lemma
  -- instead of re-proving it through the stronger homeomorphism packaging.
  simpa [weakProductSupportedOnHomeomorphFinitePi] using
    weakProductSupportedOnEquivFinitePi_symm_image_closedCellSet X cwX s d c

/-- Helper for Lemma 22.1.6: the one-point cell family has one `0`-cell and no higher cells. -/
private abbrev pointSpaceCell (n : ℕ) :=
  ULift (PLift (n = 0))

/-- Helper for Lemma 22.1.6: the degree-`0` cell index in the one-point CW model is unique. -/
private theorem pointSpaceCell_zero_eq (c : pointSpaceCell 0) :
    c = ⟨⟨rfl⟩⟩ := by
  -- The degree-`0` cell type is `PLift True`, so every inhabitant is canonical.
  cases c with
  | up c =>
      cases c
      rfl

/-- Helper for Lemma 22.1.6: the one-point cell family has no positive-dimensional cells. -/
private theorem pointSpaceCell_false_of_pos {n : ℕ} (hn : 0 < n) (c : pointSpaceCell n) :
    False :=
  (Nat.ne_of_gt hn) c.down.down

/-- Helper for Lemma 22.1.6: the degree-`0` cell of the one-point model is unique. -/
private abbrev pointSpaceZeroCellUnique : Unique (pointSpaceCell 0) where
  default := ⟨⟨rfl⟩⟩
  uniq := pointSpaceCell_zero_eq

/-- Helper for Lemma 22.1.6: the chosen `0`-cell index in the one-point model. -/
private abbrev pointSpaceZeroCell : pointSpaceCell 0 :=
  pointSpaceZeroCellUnique.default

/-- Helper for Lemma 22.1.6: positive-dimensional one-point cells are absent. -/
private abbrev pointSpaceCellIsEmptyOfPos {n : ℕ} (hn : 0 < n) : IsEmpty (pointSpaceCell n) where
  false := pointSpaceCell_false_of_pos hn

/-- Helper for Lemma 22.1.6: the total one-point cell family has a single sigma-index. -/
private theorem pointSpaceCells_subsingleton :
    Subsingleton (Σ n, pointSpaceCell n) := by
  -- Any cell index must lie in degree `0`, and the degree-`0` index is itself unique.
  refine ⟨fun a b ↦ ?_⟩
  rcases a with ⟨na, ⟨⟨ha⟩⟩⟩
  rcases b with ⟨nb, ⟨⟨hb⟩⟩⟩
  subst ha
  subst hb
  rfl

/-- Helper for Lemma 22.1.6: the unique `0`-cell of a one-point space is the constant
characteristic map. -/
private def pointSpaceCellMap (X : Type*) [TopologicalSpace X] [Unique X] (n : ℕ)
    (c : pointSpaceCell n) : PartialEquiv (Fin n → ℝ) X :=
  match n with
  | 0 => PartialEquiv.single 0 (default : X)
  | k + 1 => False.elim (Nat.succ_ne_zero k c.down.down)

/-- Helper for Lemma 22.1.6: only degree `0` survives in the one-point cell family. -/
private theorem pointSpaceCell_eventuallyIsEmpty :
    ∀ᶠ n in Filter.atTop, IsEmpty (pointSpaceCell n) := by
  -- Beyond degree `0`, every cell index is impossible.
  rw [Filter.eventually_atTop]
  refine ⟨1, ?_⟩
  intro n hn
  exact pointSpaceCellIsEmptyOfPos (Nat.succ_le_iff.mp hn)

/-- Helper for Lemma 22.1.6: each degree of the one-point cell family is finite. -/
private theorem pointSpaceCell_finite (n : ℕ) : Finite (pointSpaceCell n) := by
  exact Finite.of_subsingleton

/-- Helper for Lemma 22.1.6: the one-point characteristic map has the usual open-ball source. -/
private theorem pointSpaceCell_source_eq (X : Type*) [TopologicalSpace X] [Unique X] :
    ∀ (n : ℕ) (c : pointSpaceCell n),
      (pointSpaceCellMap X n c).source = Metric.ball 0 1 := by
  intro n c
  cases n with
  | zero =>
      -- In dimension `0`, the unit ball is the singleton empty tuple.
      ext x
      simp [pointSpaceCellMap, Matrix.empty_eq]
  | succ n =>
      exact False.elim (Nat.succ_ne_zero n c.down.down)

/-- Helper for Lemma 22.1.6: the one-point characteristic map is continuous on the closed unit
ball. -/
private theorem pointSpaceCell_continuousOn (X : Type*) [TopologicalSpace X] [Unique X] :
    ∀ (n : ℕ) (c : pointSpaceCell n),
      ContinuousOn (pointSpaceCellMap X n c) (Metric.closedBall 0 1) := by
  intro n c
  cases n with
  | zero =>
      -- The unique `0`-cell is represented by a constant map.
      simpa [pointSpaceCellMap] using
        (continuous_const.continuousOn :
          ContinuousOn (Function.const (Fin 0 → ℝ) (default : X)) (Metric.closedBall 0 1))
  | succ n =>
      exact False.elim (Nat.succ_ne_zero n c.down.down)

/-- Helper for Lemma 22.1.6: the inverse of the one-point characteristic map is continuous on its
target. -/
private theorem pointSpaceCell_continuousOn_symm (X : Type*) [TopologicalSpace X] [Unique X] :
    ∀ (n : ℕ) (c : pointSpaceCell n),
      ContinuousOn (pointSpaceCellMap X n c).symm (pointSpaceCellMap X n c).target := by
  intro n c
  cases n with
  | zero =>
      -- The inverse is constant because the target is a singleton.
      simpa [pointSpaceCellMap] using
        (continuous_const.continuousOn :
          ContinuousOn (Function.const X (0 : Fin 0 → ℝ)) {default})
  | succ n =>
      exact False.elim (Nat.succ_ne_zero n c.down.down)

/-- Helper for Lemma 22.1.6: one-point open cells are pairwise disjoint because there is only one
total cell index. -/
private theorem pointSpaceCell_pairwiseDisjoint (X : Type*) [TopologicalSpace X] [Unique X] :
    (Set.univ : Set (Σ n, pointSpaceCell n)).PairwiseDisjoint
      (fun ni ↦ pointSpaceCellMap X ni.1 ni.2 '' Metric.ball 0 1) := by
  -- Distinct sigma-indices cannot occur in the one-point cell family.
  intro a _ b _ hab
  exact (hab (pointSpaceCells_subsingleton.elim a b)).elim

/-- Helper for Lemma 22.1.6: the frontier condition in the one-point model is vacuous because only
a `0`-cell exists. -/
private theorem pointSpaceCell_mapsTo (X : Type*) [TopologicalSpace X] [Unique X] :
    ∀ (n : ℕ) (c : pointSpaceCell n),
      Set.MapsTo
        (pointSpaceCellMap X n c)
        (Metric.sphere 0 1)
        (⋃ (m : ℕ) (_ : m < n) (j : pointSpaceCell m),
          pointSpaceCellMap X m j '' Metric.closedBall 0 1) := by
  intro n c x hx
  cases n with
  | zero =>
      -- The boundary of a `0`-cell is empty.
      simpa [Metric.sphere_eq_empty_of_subsingleton] using hx
  | succ n =>
      exact False.elim (Nat.succ_ne_zero n c.down.down)

/-- Helper for Lemma 22.1.6: the closed `0`-cell of the one-point model covers the whole space. -/
private theorem pointSpaceCell_union (X : Type*) [TopologicalSpace X] [Unique X] :
    (⋃ (n : ℕ) (j : pointSpaceCell n),
      pointSpaceCellMap X n j '' Metric.closedBall 0 1) = (Set.univ : Set X) := by
  -- Every point is the image of the unique closed `0`-cell.
  ext x
  constructor
  · intro _
    simp
  · intro _
    refine Set.mem_iUnion.2 ⟨0, ?_⟩
    refine Set.mem_iUnion.2 ⟨pointSpaceZeroCell, ?_⟩
    refine ⟨0, ?_, ?_⟩
    · simp
    · have hx : x = default := Subsingleton.elim _ _
      simpa [pointSpaceCellMap, hx]

/-- Helper for Lemma 22.1.6: any one-point space carries the obvious CW structure with one
`0`-cell. -/
private noncomputable abbrev pointSpaceCWComplex (X : Type*) [TopologicalSpace X] [Unique X] :
    Topology.CWComplex (Set.univ : Set X) :=
  Topology.CWComplex.mkFinite
    (Set.univ : Set X)
    pointSpaceCell
    (pointSpaceCellMap X)
    pointSpaceCell_eventuallyIsEmpty
    pointSpaceCell_finite
    (pointSpaceCell_source_eq X)
    (pointSpaceCell_continuousOn X)
    (pointSpaceCell_continuousOn_symm X)
    (pointSpaceCell_pairwiseDisjoint X)
    (pointSpaceCell_mapsTo X)
    (pointSpaceCell_union X)

/-- Helper for Lemma 22.1.6: the empty finite dependent product is the one-point CW complex. -/
private noncomputable abbrev emptyFinitePiCWComplex
    (X : ι → PointedCompactlyGenerated.{u, w}) :
    Topology.CWComplex
      (Set.univ : Set ((i : (∅ : Finset ι)) → (X i).toCompactlyGenerated)) :=
  pointSpaceCWComplex _

/-- Helper for Lemma 22.1.6: removing the inserted coordinate from `insert a s` recovers the
original finite index set `s`. -/
private def insertComplementSubtypeEquiv
    [DecidableEq ι] (s : Finset ι) {a : ι} (ha : a ∉ s) :
    {j : (insert a s : Finset ι) // j ≠ ⟨a, Finset.mem_insert_self a s⟩} ≃ s where
  toFun := fun j ↦
    ⟨j.1.1, by
      refine (Finset.mem_insert.mp j.1.2).resolve_left ?_
      intro h
      apply j.2
      apply Subtype.ext
      simpa using h⟩
  invFun := fun i ↦
    ⟨⟨i.1, Finset.mem_insert_of_mem i.2⟩, by
      intro h
      have hval : i.1 = a := congrArg Subtype.val h
      exact ha (show a ∈ s from hval ▸ i.2)⟩
  left_inv := by
    intro j
    cases j with
    | mk j hj =>
        cases j with
        | mk j hjmem =>
            apply Subtype.ext
            rfl
  right_inv := by
    intro i
    apply Subtype.ext
    rfl

/-- Helper for Lemma 22.1.6: `insertComplementSubtypeEquiv` sends the evident non-inserted
coordinate in `insert a s` back to the original coordinate of `s`. -/
@[simp] private theorem insertComplementSubtypeEquiv_apply_of_mem
    [DecidableEq ι] (s : Finset ι) {a : ι} (ha : a ∉ s) (i : s) :
    insertComplementSubtypeEquiv (s := s) ha
        ⟨⟨i.1, Finset.mem_insert_of_mem i.2⟩, by
          intro h
          have hval : i.1 = a := congrArg Subtype.val h
          exact ha (show a ∈ s from hval.symm ▸ i.2)⟩ = i := by
  -- The complement equivalence only forgets the proof that the coordinate is not the inserted one.
  apply Subtype.ext
  rfl

/-- Helper for Lemma 22.1.6: the inverse of `insertComplementSubtypeEquiv` is the evident
inclusion of `s` into `insert a s` away from the inserted coordinate. -/
@[simp] private theorem insertComplementSubtypeEquiv_symm_apply
    [DecidableEq ι] (s : Finset ι) {a : ι} (ha : a ∉ s) (i : s) :
    (insertComplementSubtypeEquiv (s := s) ha).symm i =
      ⟨⟨i.1, Finset.mem_insert_of_mem i.2⟩, by
        intro h
        have hval : i.1 = a := congrArg Subtype.val h
        exact ha (show a ∈ s from hval.symm ▸ i.2)⟩ := by
  -- On supported coordinates, the inverse simply inserts the old index into `insert a s`.
  apply Subtype.ext
  rfl

/-- Helper for Lemma 22.1.6: a finite dependent product over `insert a s` splits as the product
of the `a`-coordinate and the product over `s`. -/
private noncomputable def finitePiInsertHomeomorph
    [DecidableEq ι]
    (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι) {a : ι} (ha : a ∉ s) :
    ((i : (insert a s : Finset ι)) → (X i).toCompactlyGenerated) ≃ₜ
      (X a).toCompactlyGenerated × ((i : s) → (X i).toCompactlyGenerated) :=
  let eRest :
      {j : (insert a s : Finset ι) // j ≠ ⟨a, Finset.mem_insert_self a s⟩} ≃ s :=
    insertComplementSubtypeEquiv (s := s) ha
  let hSplit :=
    Homeomorph.piSplitAt
      (ι := (insert a s : Finset ι))
      ⟨a, Finset.mem_insert_self a s⟩
      (fun i ↦ (X i).toCompactlyGenerated)
  let hRest :
      ((j : {j : (insert a s : Finset ι) // j ≠ ⟨a, Finset.mem_insert_self a s⟩}) →
          (X j.1).toCompactlyGenerated) ≃ₜ
        ((i : s) → (X i).toCompactlyGenerated) :=
    Homeomorph.piCongr eRest
      (fun j ↦
        show (X j.1).toCompactlyGenerated ≃ₜ (X (eRest j)).toCompactlyGenerated from
          Homeomorph.refl _)
  -- First split off the inserted coordinate, then reindex the remaining coordinates by `s`.
  hSplit.trans <| (Homeomorph.refl _).prodCongr hRest

/-- Helper for Lemma 22.1.6: `finitePiInsertHomeomorph` reads the inserted coordinate as the first
product factor. -/
@[simp] private theorem finitePiInsertHomeomorph_apply_insert
    [DecidableEq ι]
    (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι) {a : ι} (ha : a ∉ s)
    (y : (i : (insert a s : Finset ι)) → (X i).toCompactlyGenerated) :
    (finitePiInsertHomeomorph X s ha y).1 = y ⟨a, Finset.mem_insert_self a s⟩ := by
  -- The split homeomorphism evaluates the distinguished inserted coordinate directly.
  simp [finitePiInsertHomeomorph]

/-- Helper for Lemma 22.1.6: the inverse of `finitePiInsertHomeomorph` restores the inserted
coordinate from the first product factor. -/
@[simp] private theorem finitePiInsertHomeomorph_symm_apply_insert
    [DecidableEq ι]
    (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι) {a : ι} (ha : a ∉ s)
    (x : (X a).toCompactlyGenerated) (y : (i : s) → (X i).toCompactlyGenerated) :
    (finitePiInsertHomeomorph X s ha).symm (x, y) ⟨a, Finset.mem_insert_self a s⟩ = x := by
  -- The inverse homeomorphism inserts the distinguished coordinate as the first product factor.
  simp [finitePiInsertHomeomorph]

/-- Helper for Lemma 22.1.6: `finitePiInsertHomeomorph` reads every non-inserted coordinate from
the second product factor after reindexing back along the complement equivalence. -/
@[simp] private theorem finitePiInsertHomeomorph_apply_of_mem
    [DecidableEq ι]
    (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι) {a : ι} (ha : a ∉ s)
    (y : (i : (insert a s : Finset ι)) → (X i).toCompactlyGenerated) (i : s) :
    (finitePiInsertHomeomorph X s ha y).2 i = y ⟨i.1, Finset.mem_insert_of_mem i.2⟩ := by
  -- After splitting off the inserted coordinate, the remaining coordinates are just reindexed by
  -- `insertComplementSubtypeEquiv`.
  change
    (Equiv.piCongrLeft (fun k : s ↦ (X k).toCompactlyGenerated)
        (insertComplementSubtypeEquiv (s := s) ha))
        ((Equiv.piCongrRight
          fun j : {j : (insert a s : Finset ι) // j ≠ ⟨a, Finset.mem_insert_self a s⟩} ↦
            Equiv.refl ((X j.1).toCompactlyGenerated)) fun j ↦ y j.1) i =
      y ⟨i.1, Finset.mem_insert_of_mem i.2⟩
  rw [Equiv.piCongrLeft_apply_eq_cast]
  have hsymm := insertComplementSubtypeEquiv_symm_apply (s := s) (ha := ha) i
  cases hsymm
  have happly := insertComplementSubtypeEquiv_apply_of_mem (s := s) (ha := ha) i
  cases happly
  rfl

/-- Helper for Lemma 22.1.6: the inverse of `finitePiInsertHomeomorph` restores each supported
coordinate from the second product factor. -/
@[simp] private theorem finitePiInsertHomeomorph_symm_apply_of_mem
    [DecidableEq ι]
    (X : ι → PointedCompactlyGenerated.{u, w}) (s : Finset ι) {a : ι} (ha : a ∉ s)
    (x : (X a).toCompactlyGenerated) (y : (i : s) → (X i).toCompactlyGenerated) (i : s) :
    (finitePiInsertHomeomorph X s ha).symm (x, y) ⟨i.1, Finset.mem_insert_of_mem i.2⟩ = y i := by
  -- The inverse map inserts the distinguished coordinate and leaves the old coordinates unchanged.
  have hsnd :
      (finitePiInsertHomeomorph X s ha ((finitePiInsertHomeomorph X s ha).symm (x, y))).2 = y := by
    simpa using congrArg Prod.snd ((finitePiInsertHomeomorph X s ha).left_inv (x, y))
  have hsndi :
      (finitePiInsertHomeomorph X s ha ((finitePiInsertHomeomorph X s ha).symm (x, y))).2 i = y i := by
    simpa using congrArg (fun f ↦ f i) hsnd
  calc
    (finitePiInsertHomeomorph X s ha).symm (x, y) ⟨i.1, Finset.mem_insert_of_mem i.2⟩ =
        (finitePiInsertHomeomorph X s ha ((finitePiInsertHomeomorph X s ha).symm (x, y))).2 i := by
      symm
      exact finitePiInsertHomeomorph_apply_of_mem X s ha ((finitePiInsertHomeomorph X s ha).symm (x, y)) i
    _ = y i := hsndi

/-- Helper for Lemma 22.1.6: transporting a product of chosen closed cells across
`finitePiInsertHomeomorph` rewrites it as the explicit coordinatewise closed-cell condition on
`insert a s`. -/
private theorem finitePiInsertHomeomorph_symm_image_coordinateClosedCellSet
    [DecidableEq ι]
    (X : ι → PointedCompactlyGenerated.{u, w})
    (cwX : ∀ i, Topology.CWComplex (Set.univ : Set (X i).toCompactlyGenerated))
    (s : Finset ι) {a : ι} (ha : a ∉ s)
    (p : ℕ) (ca : (cwX a).cell p)
    (d : s → ℕ) (c : ∀ i : s, (cwX i).cell (d i)) :
    (finitePiInsertHomeomorph X s ha).symm ''
        {z : (X a).toCompactlyGenerated × ((i : s) → (X i).toCompactlyGenerated) |
          z.1 ∈ (cwX a).map p ca '' Metric.closedBall 0 1 ∧
            ∀ i : s, z.2 i ∈ (cwX i).map (d i) (c i) '' Metric.closedBall 0 1} =
      {y : ((i : (insert a s : Finset ι)) → (X i).toCompactlyGenerated) |
        y ⟨a, Finset.mem_insert_self a s⟩ ∈ (cwX a).map p ca '' Metric.closedBall 0 1 ∧
          ∀ i : s,
            y ⟨i.1, Finset.mem_insert_of_mem i.2⟩ ∈
              (cwX i).map (d i) (c i) '' Metric.closedBall 0 1} := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases z with ⟨x, z⟩
    dsimp at hz ⊢
    -- The inverse map restores the inserted coordinate from the first factor and the old
    -- supported coordinates from the second factor.
    refine ⟨?_, ?_⟩
    · simpa using hz.1
    · intro i
      simpa using hz.2 i
  · intro hy
    -- Apply the forward homeomorphism to package the coordinatewise conditions back into the split
    -- product cell.
    refine ⟨finitePiInsertHomeomorph X s ha y, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simpa using hy.1
      · intro i
        simpa using hy.2 i
    · simp

/-- Helper for Lemma 22.1.6: enlarging the finite support set enlarges the supported slice. -/
theorem weakProductSupportedOn_mono
    (X : ι → PointedCompactlyGenerated.{u, w}) {s t : Finset ι} (hst : s ⊆ t) :
    weakProductSupportedOn X s ⊆ weakProductSupportedOn X t := by
  intro x hx i hi
  -- Any coordinate outside the larger support is also outside the smaller support.
  exact hx i fun his ↦ hi (hst his)

/-- Helper for Lemma 22.1.6: the finite-support slices exhaust the whole weak product. -/
theorem iUnion_weakProductSupportedOn_eq_univ
    (X : ι → PointedCompactlyGenerated.{u, w}) :
    (⋃ s : Finset ι, weakProductSupportedOn X s) =
      (Set.univ : Set ((weakProduct X).toCompactlyGenerated)) := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    -- Use the finite non-basepoint support already built into the weak-product carrier.
    have hxSupport : hasFiniteNonbasepointSupport X x.1 := x.2
    have hxFinite : {i | x.1 i ≠ (X i).point}.Finite := by
      exact (hasFiniteNonbasepointSupport_iff X x.1).1 hxSupport
    refine Set.mem_iUnion.2 ⟨hxFinite.toFinset, ?_⟩
    intro i hi
    by_contra hneq
    apply hi
    simpa using hxFinite.mem_toFinset.mpr hneq

/-- Helper for Lemma 22.1.6: extending a finite direct-limit stage gives a finite-support weak
product point. -/
private theorem weakProductFiniteStage_hasFiniteNonbasepointSupport
    (X : ι → PointedCompactlyGenerated.{u, w}) (a : weakProductFiniteStage X) :
    hasFiniteNonbasepointSupport X (weakProductFiniteStage.extend X a) := by
  classical
  -- Only coordinates inside the chosen finite stage can differ from the distinguished basepoint.
  refine a.1.finite_toSet.subset ?_
  intro i hi
  by_contra his
  exact hi (weakProductFiniteStage.extend_of_not_mem X a his)

/-- Helper for Lemma 22.1.6: a finite direct-limit stage determines the corresponding weak-product
point obtained by padding with basepoints away from the chosen support. -/
private noncomputable def weakProductFiniteStageToWeakProduct
    (X : ι → PointedCompactlyGenerated.{u, w}) (a : weakProductFiniteStage X) :
    (weakProduct X).toCompactlyGenerated :=
  ⟨weakProductFiniteStage.extend X a,
    weakProductFiniteStage_hasFiniteNonbasepointSupport X a⟩

/-- Helper for Lemma 22.1.6: the weak-product point attached to a finite stage is supported on
that same finite set of coordinates. -/
private theorem weakProductFiniteStageToWeakProduct_mem_supportedOn
    (X : ι → PointedCompactlyGenerated.{u, w}) (a : weakProductFiniteStage X) :
    weakProductFiniteStageToWeakProduct X a ∈ weakProductSupportedOn X a.1 := by
  intro i hi
  -- Outside the chosen finite stage, the padded tuple is exactly the distinguished basepoint.
  simpa [weakProductFiniteStageToWeakProduct] using
    weakProductFiniteStage.extend_of_not_mem X a hi

/-- Helper for Lemma 22.1.6: the supported-slice point attached to a finite stage reads back the
original coordinate on indices in the chosen support. -/
@[simp] private theorem weakProductFiniteStageToWeakProduct_apply_of_mem
    (X : ι → PointedCompactlyGenerated.{u, w}) (a : weakProductFiniteStage X)
    {i : ι} (hi : i ∈ a.1) :
    (weakProductFiniteStageToWeakProduct X a).1 i = a.2 ⟨i, hi⟩ := by
  -- On supported coordinates, the padded weak-product point is just the original stage entry.
  simpa [weakProductFiniteStageToWeakProduct] using
    weakProductFiniteStage.extend_of_mem X a hi

/-- Helper for Lemma 22.1.6: the supported-slice point attached to a finite stage is the
distinguished basepoint away from the chosen support. -/
@[simp] private theorem weakProductFiniteStageToWeakProduct_apply_of_not_mem
    (X : ι → PointedCompactlyGenerated.{u, w}) (a : weakProductFiniteStage X)
    {i : ι} (hi : i ∉ a.1) :
    (weakProductFiniteStageToWeakProduct X a).1 i = (X i).point := by
  -- Off the chosen support, the padded weak-product point is the distinguished basepoint.
  simpa [weakProductFiniteStageToWeakProduct] using
    weakProductFiniteStage.extend_of_not_mem X a hi

/-- Helper for Lemma 22.1.6: a classical CW structure on `Set.univ` is Hausdorff. -/
private theorem t2SpaceOfUnivCWComplex
    (X : Type*) [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)] :
    T2Space X := by
  -- Reuse the earlier chapter bridge from classical CW complexes to Hausdorff spaces.
  exact instT2SpaceOfCWComplexUniv X

/-- Helper for Lemma 22.1.6: a homeomorphism transports a classical CW structure on `Set.univ`. -/
@[implicit_reducible] private noncomputable def cwComplexUnivHomeomorph
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (cwX : Topology.CWComplex (Set.univ : Set X)) :
    Topology.CWComplex (Set.univ : Set Y) := by
  let transportedMap : ∀ n, cwX.cell n → PartialEquiv (Fin n → ℝ) Y := fun n i ↦
    { toFun := fun x ↦ e (cwX.map n i x)
      invFun := fun y ↦ (cwX.map n i).symm (e.symm y)
      source := (cwX.map n i).source
      target := e '' (cwX.map n i).target
      map_source' := by
        intro x hx
        exact ⟨cwX.map n i x, (cwX.map n i).map_source hx, rfl⟩
      map_target' := by
        rintro y ⟨x, hx, rfl⟩
        simpa using (cwX.map n i).map_target hx
      left_inv' := by
        intro x hx
        simp [(cwX.map n i).left_inv hx]
      right_inv' := by
        rintro y ⟨x, hx, rfl⟩
        simp [(cwX.map n i).right_inv hx] }
  refine
    { cell := cwX.cell
      map := transportedMap
      source_eq := ?_
      continuousOn := ?_
      continuousOn_symm := ?_
      pairwiseDisjoint' := ?_
      mapsTo' := ?_
      closed' := ?_
      union' := ?_ }
  · intro n i
    -- The transported characteristic map keeps the same source ball.
    simpa [transportedMap] using cwX.source_eq n i
  · intro n i
    -- Postcomposing the original characteristic map with the homeomorphism preserves continuity.
    exact
      e.continuous.continuousOn.comp (cwX.continuousOn n i)
        (by intro x hx; exact Set.mem_univ _)
  · intro n i
    -- The transported inverse is the original inverse followed by `e.symm`.
    refine (cwX.continuousOn_symm n i).comp ?_ ?_
    · simpa [transportedMap] using e.symm.continuous.continuousOn
    · intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      simpa [transportedMap]
  · intro a ha b hb hab
    -- Open-cell disjointness is preserved by the injective homeomorphism.
    have hdisjoint := cwX.pairwiseDisjoint' ha hb hab
    simpa [transportedMap, Set.image_image, Function.comp] using
      Set.disjoint_image_of_injective e.injective hdisjoint
  · intro n i
    -- The boundary lands in the same finite family of lower-dimensional cells after transport.
    rcases cwX.mapsTo' n i with ⟨I, hI⟩
    refine ⟨I, ?_⟩
    intro x hx
    rcases Set.mem_iUnion.mp (hI hx) with ⟨m, hm⟩
    rcases Set.mem_iUnion.mp hm with ⟨hmn, hm⟩
    rcases Set.mem_iUnion.mp hm with ⟨j, hj⟩
    rcases Set.mem_iUnion.mp hj with ⟨hjmem, hj⟩
    rcases hj with ⟨z, hz, hjz⟩
    refine
      Set.mem_iUnion.mpr
        ⟨m, Set.mem_iUnion.mpr ⟨hmn, Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hjmem, ?_⟩⟩⟩⟩
    refine ⟨z, hz, ?_⟩
    simpa [transportedMap] using congrArg e hjz
  · intro A _ hA
    -- Pull the closed-set test back along `e`, use the original weak-topology axiom, and push
    -- the result forward again through the homeomorphism.
    apply (e.isClosed_preimage).1
    refine cwX.closed' (e ⁻¹' A) (by intro x hx; simp) ?_
    intro n j
    have hPreimageImage :
        e ⁻¹' (transportedMap n j '' Metric.closedBall 0 1) =
          cwX.map n j '' Metric.closedBall 0 1 := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨z, hz, hxz⟩
        refine ⟨z, hz, ?_⟩
        exact e.injective <| by simpa [transportedMap] using hxz
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, by simp [transportedMap]⟩
    have hClosedImage : IsClosed (A ∩ transportedMap n j '' Metric.closedBall 0 1) := hA n j
    have hClosedPreimage :
        IsClosed (e ⁻¹' (A ∩ transportedMap n j '' Metric.closedBall 0 1)) :=
      (e.isClosed_preimage).2 hClosedImage
    simpa [Set.preimage_inter, hPreimageImage] using hClosedPreimage
  · -- The transported closed cells still cover the whole space because `e` is surjective.
    ext y
    constructor
    · intro _
      simp
    · intro _
      rcases e.surjective y with ⟨x, rfl⟩
      have hx :
          x ∈ ⋃ (n : ℕ) (j : cwX.cell n), cwX.map n j '' Metric.closedBall 0 1 := by
        simpa [cwX.union'] using (show x ∈ (Set.univ : Set X) from Set.mem_univ x)
      rcases Set.mem_iUnion.mp hx with ⟨n, hx⟩
      rcases Set.mem_iUnion.mp hx with ⟨j, hx⟩
      rcases hx with ⟨z, hz, rfl⟩
      refine Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨j, ?_⟩⟩
      exact ⟨z, hz, rfl⟩

/-- Helper for Lemma 22.1.6: a homeomorphism transports a classical CW structure on `Set.univ`. -/
private theorem cwComplexUnivOfHomeomorph
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    Nonempty (Topology.CWComplex (Set.univ : Set X)) →
      Nonempty (Topology.CWComplex (Set.univ : Set Y)) := by
  rintro ⟨cwX⟩
  exact ⟨cwComplexUnivHomeomorph e cwX⟩

/-- Helper for Lemma 22.1.6: the weak topology of a classical CW complex is compactly generated.
The closed-cell inclusions themselves supply the compact Hausdorff tests. -/
private theorem cwComplexUCompactlyGeneratedSpace
    (X : Type u) [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)] :
    UCompactlyGeneratedSpace.{u} X := by
  let _ : T2Space X := t2SpaceOfUnivCWComplex X
  refine uCompactlyGeneratedSpace_of_isClosed ?_
  intro A hA
  rw [Topology.CWComplex.closed Set.univ A (Set.subset_univ A)]
  intro n j
  let K := Topology.CWComplex.closedCell n j
  let _ : CompactSpace K :=
    isCompact_iff_compactSpace.mp Topology.CWComplex.isCompact_closedCell
  have hPreimage :
      IsClosed ((Subtype.val : K → X) ⁻¹' A) :=
    hA (CompHaus.of K) ⟨Subtype.val, continuous_subtype_val⟩
  have hCompact :
      IsCompact ((Subtype.val : K → X) '' ((Subtype.val : K → X) ⁻¹' A)) :=
    hPreimage.isCompact.image continuous_subtype_val
  have hImage :
      (Subtype.val : K → X) '' ((Subtype.val : K → X) ⁻¹' A) =
        A ∩ Topology.CWComplex.closedCell n j := by
    ext x
    simp [K, and_comm]
  rw [← hImage]
  exact hCompact.isClosed

/-- Helper for Lemma 22.1.6: the ordinary product of two compactly generated classical CW
spaces is again compactly generated. -/
private theorem cwComplexProdUCompactlyGenerated
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [UCompactlyGeneratedSpace.{w} X] [UCompactlyGeneratedSpace.{w} Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)] :
    UCompactlyGeneratedSpace.{w} (X × Y) := by
  -- The source construction needs the categorical (kified) product here, whereas the carrier
  -- currently has Lean's ordinary product topology.  Arbitrary products of k-spaces need not be
  -- k-spaces, even when both factors are CW complexes.  The final weak-product construction below
  -- is already intentionally unfinished; keep this exact missing topology bridge local as well.
  sorry

/-- Helper for Lemma 22.1.6: the finite-support induction state packages the chosen CW structure on
the finite dependent product over `s` together with the explicit coordinatewise closed-cell
description for every cell of that product CW structure. -/
private structure FinitePiCellData
    (X : ι → PointedCompactlyGenerated.{u, w})
    (cwX : ∀ i, Topology.CWComplex (Set.univ : Set (X i).toCompactlyGenerated))
    (s : Finset ι) where
  inst : UCompactlyGeneratedSpace.{u} ((i : s) → (X i).toCompactlyGenerated)
  cw : Topology.CWComplex (Set.univ : Set ((i : s) → (X i).toCompactlyGenerated))
  closedCell :
    ∀ n (j : cw.cell n),
      ∃ d : s → ℕ,
        ∃ c : ∀ i : s, (cwX i).cell (d i),
          n = ∑ i : s, d i ∧
            cw.map n j '' Metric.closedBall 0 1 =
              {y | ∀ i : s, y i ∈ (cwX i).map (d i) (c i) '' Metric.closedBall 0 1}

/-- Helper for Lemma 22.1.6: the public product-cell map API already determines the closed image
of a chosen product cell as the product of the two factor closed cells. -/
private theorem productCWCellMap_closedCellImage_eq
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)]
    (n : ℕ) (j : productCWCellIndex X Y n) :
    productCWCellMap X Y n j '' Metric.closedBall (0 : Fin n → ℝ) 1 =
      let ⟨⟨⟨p, q⟩, _hpq⟩, i, k⟩ := j
      (Topology.CWComplex.map p i '' Metric.closedBall (0 : Fin p → ℝ) 1) ×ˢ
        (Topology.CWComplex.map q k '' Metric.closedBall (0 : Fin q → ℝ) 1) := by
  rcases j with ⟨⟨⟨p, q⟩, hpq⟩, i, k⟩
  -- Unfold the public product-cell map and push the model closed ball through the splitting
  -- isometry `Fin (p + q) ≃ Fin p × Fin q`.
  simp only [productCWCellMap]
  rw [PartialEquiv.coe_trans, PartialEquiv.prod_coe, Set.image_comp]
  change Prod.map (Topology.CWComplex.map p i) (Topology.CWComplex.map q k) ''
      (((Fin.appendIsometryOfEq hpq).symm : (Fin n → ℝ) ≃ᵢ (Fin p → ℝ) × (Fin q → ℝ)) ''
        Metric.closedBall (0 : Fin n → ℝ) 1) = _
  rw [IsometryEquiv.image_closedBall]
  have hzero :
      ((Fin.appendIsometryOfEq hpq).symm : (Fin n → ℝ) ≃ᵢ (Fin p → ℝ) × (Fin q → ℝ))
        (0 : Fin n → ℝ) = (0, 0) := by
    -- The splitting isometry sends the zero vector to the product zero vector coordinatewise.
    ext <;> simp
  rw [hzero, ← closedBall_prod_same, Set.prodMap_image_prod]

/-- Helper for Lemma 22.1.6: after reindexing product cells by
`productCWComplex_cellEquiv`, the closed image in the chosen product CW structure is still the
product of the two factor closed cells. -/
private theorem productCWComplex_closedCellImage_eq
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    [CompactlyGeneratedSpace (X × Y)]
    (n : ℕ) (j : (productCWComplex X Y).cell n) :
    (productCWComplex X Y).map n j '' Metric.closedBall (0 : Fin n → ℝ) 1 =
      let ⟨⟨⟨p, q⟩, _hpq⟩, i, k⟩ := productCWComplex_cellEquiv X Y n j
      (Topology.CWComplex.map p i '' Metric.closedBall (0 : Fin p → ℝ) 1) ×ˢ
        (Topology.CWComplex.map q k '' Metric.closedBall (0 : Fin q → ℝ) 1) := by
  -- Route correction: normalize through the public cell-index equivalence first, instead of
  -- repeatedly unfolding the product CW constructor inside the insert-step proof.
  simpa [productCWComplex_cellEquiv_apply] using
    (productCWCellMap_closedCellImage_eq X Y n (productCWComplex_cellEquiv X Y n j))

/-- Helper for Lemma 22.1.6: the empty finite dependent product already carries the packaged
coordinatewise cell description. -/
private noncomputable abbrev emptyFinitePiCellData
    (X : ι → PointedCompactlyGenerated.{u, w})
    (cwX : ∀ i, Topology.CWComplex (Set.univ : Set (X i).toCompactlyGenerated)) :
    FinitePiCellData X cwX (∅ : Finset ι) := by
  classical
  refine
    { inst := inferInstance
      cw := emptyFinitePiCWComplex X
      closedCell := ?_ }
  intro n j
  cases n with
  | zero =>
      refine ⟨(fun i ↦ nomatch i), ⟨(fun i ↦ nomatch i), ?_, ?_⟩⟩
      · -- The empty support contributes no dimensions.
        simp
      · -- The closed `0`-cell of the one-point model is the whole empty product.
        ext y
        constructor
        · intro _
          simp
        · intro _
          refine ⟨0, ?_, ?_⟩
          · simp
          · have hy : y = default := Subsingleton.elim _ _
            have hj : j = pointSpaceZeroCell := pointSpaceCell_zero_eq j
            cases hj
            have hmap :
                (emptyFinitePiCWComplex X).map 0 pointSpaceZeroCell (0 : Fin 0 → ℝ) = default := by
              exact Subsingleton.elim _ _
            simpa [hy] using hmap
  | succ n =>
      -- Positive-dimensional cells are impossible in the one-point CW model.
      exact False.elim (pointSpaceCell_false_of_pos (Nat.succ_pos _) j)

set_option maxHeartbeats 800000 in
/-- Helper for Lemma 22.1.6: adjoining one fresh coordinate to a finite product preserves the
packaged coordinatewise closed-cell description. -/
private noncomputable abbrev finitePiCellData_insert
    [DecidableEq ι]
    (X : ι → PointedCompactlyGenerated.{u, w})
    (cwX : ∀ i, Topology.CWComplex (Set.univ : Set (X i).toCompactlyGenerated))
    (s : Finset ι) {a : ι} (ha : a ∉ s)
    (data : FinitePiCellData X cwX s) :
    FinitePiCellData X cwX (insert a s) := by
  classical
  letI : Topology.CWComplex (Set.univ : Set (X a).toCompactlyGenerated) := cwX a
  letI : UCompactlyGeneratedSpace.{u} ((i : s) → (X i).toCompactlyGenerated) := data.inst
  letI : Topology.CWComplex
      (Set.univ : Set ((i : s) → (X i).toCompactlyGenerated)) := data.cw
  letI : UCompactlyGeneratedSpace.{w} (X a).toCompactlyGenerated :=
    cwComplexUCompactlyGeneratedSpace (X a).toCompactlyGenerated
  letI : UCompactlyGeneratedSpace.{max v w} (X a).toCompactlyGenerated :=
    uCompactlyGeneratedSpaceLift.{w, v} (Z := (X a).toCompactlyGenerated)
  letI : UCompactlyGeneratedSpace.{max v w}
      ((i : s) → (X i).toCompactlyGenerated) :=
    cwComplexUCompactlyGeneratedSpace ((i : s) → (X i).toCompactlyGenerated)
  let prodInst :
      UCompactlyGeneratedSpace.{u}
        ((X a).toCompactlyGenerated × ((i : s) → (X i).toCompactlyGenerated)) :=
    cwComplexProdUCompactlyGenerated.{w, max v w, u}
      ((X a).toCompactlyGenerated) ((i : s) → (X i).toCompactlyGenerated)
  let prodInstSameUniverse :
      CompactlyGeneratedSpace
        ((X a).toCompactlyGenerated × ((i : s) → (X i).toCompactlyGenerated)) :=
    cwComplexProdUCompactlyGenerated.{w, max v w, max v w}
      ((X a).toCompactlyGenerated) ((i : s) → (X i).toCompactlyGenerated)
  letI :
      CompactlyGeneratedSpace
        ((X a).toCompactlyGenerated × ((i : s) → (X i).toCompactlyGenerated)) :=
    prodInstSameUniverse
  let prodCw :
      Topology.CWComplex
        (Set.univ : Set ((X a).toCompactlyGenerated × ((i : s) → (X i).toCompactlyGenerated))) :=
    productCWComplex ((X a).toCompactlyGenerated) ((i : s) → (X i).toCompactlyGenerated)
  letI :
      UCompactlyGeneratedSpace.{u}
        ((X a).toCompactlyGenerated × ((i : s) → (X i).toCompactlyGenerated)) := prodInst
  let insertedInst :
      UCompactlyGeneratedSpace.{u} ((i : (insert a s : Finset ι)) → (X i).toCompactlyGenerated) :=
    uCompactlyGeneratedSpace_homeomorph (finitePiInsertHomeomorph X s ha).symm
  let insertedCw :
      Topology.CWComplex
        (Set.univ : Set ((i : (insert a s : Finset ι)) → (X i).toCompactlyGenerated)) :=
    cwComplexUnivHomeomorph (finitePiInsertHomeomorph X s ha).symm prodCw
  refine
    { inst := insertedInst
      cw := insertedCw
      closedCell := ?_ }
  intro n j
  let jProd : prodCw.cell n := j
  rcases hCell :
      productCWComplex_cellEquiv
          ((X a).toCompactlyGenerated) ((i : s) → (X i).toCompactlyGenerated) n jProd with
    ⟨⟨⟨p, q⟩, hpq⟩, ca, k⟩
  rcases data.closedCell q k with ⟨d, c, hq, hclosed⟩
  let dInsert : (i : ↥(insert a s)) → ℕ := fun i ↦
    if hia : i.1 = a then
      p
    else
      d ⟨i.1, (Finset.mem_insert.mp i.2).resolve_left hia⟩
  let cInsert : ∀ i : (insert a s : Finset ι), (cwX i).cell (dInsert i) :=
    fun ⟨b, hb⟩ ↦ by
      by_cases hba : b = a
      · subst b
        simpa [dInsert] using ca
      · have hbs : b ∈ s := (Finset.mem_insert.mp hb).resolve_left hba
        simpa [dInsert, hba] using c ⟨b, hbs⟩
  have cellImage_eq (b : ι) {m n : ℕ}
      (hmn : m = n) (cm : (cwX b).cell m) (cn : (cwX b).cell n)
      (hcmn : HEq cm cn) :
      (cwX b).map m cm '' Metric.closedBall 0 1 =
        (cwX b).map n cn '' Metric.closedBall 0 1 := by
    subst n
    have hcmn' : cm = cn := eq_of_heq hcmn
    subst cn
    rfl
  have hcellInsert :
      (cwX (⟨a, Finset.mem_insert_self a s⟩ : ↥(insert a s))).map
          (dInsert ⟨a, Finset.mem_insert_self a s⟩)
          (cInsert ⟨a, Finset.mem_insert_self a s⟩) '' Metric.closedBall 0 1 =
        (cwX a).map p ca '' Metric.closedBall 0 1 := by
    let ia : ↥(insert a s) := ⟨a, Finset.mem_insert_self a s⟩
    have hd : dInsert ia = p := by simp [ia, dInsert]
    have hc : HEq (cInsert ia) ca := by
      simp only [ia, cInsert]
      apply cast_heq
    exact cellImage_eq a hd (cInsert ia) ca hc
  have hcellOld (i : s) :
      (cwX (⟨i.1, Finset.mem_insert_of_mem i.2⟩ : ↥(insert a s))).map
          (dInsert ⟨i.1, Finset.mem_insert_of_mem i.2⟩)
          (cInsert ⟨i.1, Finset.mem_insert_of_mem i.2⟩) '' Metric.closedBall 0 1 =
        (cwX i).map (d i) (c i) '' Metric.closedBall 0 1 := by
    have hne : i.1 ≠ a := fun h ↦ ha (h ▸ i.2)
    let ii : ↥(insert a s) := ⟨i.1, Finset.mem_insert_of_mem i.2⟩
    have hd : dInsert ii = d i := by simp [ii, dInsert, hne]
    have hc : HEq (cInsert ii) (c i) := by
      simp only [ii, cInsert]
      rw [dif_neg hne]
      apply cast_heq
    exact cellImage_eq i hd (cInsert ii) (c i) hc
  refine ⟨dInsert, cInsert, ?_, ?_⟩
  · -- Split the total dimension into the inserted coordinate and the old finite support.
    calc
      n = p + q := by
        simpa using hpq.symm
      _ = p + ∑ i : s, d i := by
        rw [hq]
      _ = ∑ i : (insert a s : Finset ι), dInsert i := by
        symm
        calc
          ∑ i : (insert a s : Finset ι), dInsert i =
              dInsert ⟨a, Finset.mem_insert_self a s⟩ +
                ∑ j : {j : ↥(insert a s) //
                  j ≠ ⟨a, Finset.mem_insert_self a s⟩}, dInsert j.1 :=
            Fintype.sum_eq_add_sum_subtype_ne dInsert
              ⟨a, Finset.mem_insert_self a s⟩
          _ = p + ∑ i : s, d i := by
            congr 1
            · simp [dInsert]
            · apply Fintype.sum_equiv (insertComplementSubtypeEquiv (s := s) ha)
              intro j
              have hne : j.1.1 ≠ a := by
                intro h
                apply j.2
                apply Subtype.ext
                exact h
              simp [dInsert, insertComplementSubtypeEquiv, hne]
  · -- Transport the chosen product cell across `finitePiInsertHomeomorph` and then rewrite the
    -- supported coordinates in the explicit coordinatewise normal form on `insert a s`.
    have hmap :
        insertedCw.map n j '' Metric.closedBall (0 : Fin n → ℝ) 1 =
          (finitePiInsertHomeomorph X s ha).symm ''
            (prodCw.map n jProd '' Metric.closedBall (0 : Fin n → ℝ) 1) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨prodCw.map n j x, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨z, hz, rfl⟩
    have hprod :
        prodCw.map n jProd '' Metric.closedBall (0 : Fin n → ℝ) 1 =
          ((cwX a).map p ca '' Metric.closedBall (0 : Fin p → ℝ) 1) ×ˢ
            (data.cw.map q k '' Metric.closedBall (0 : Fin q → ℝ) 1) := by
      have hjProd :
          jProd = ⟨⟨⟨p, q⟩, hpq⟩, ca, k⟩ := by
        simpa only [productCWComplex_cellEquiv_apply] using hCell
      rw [hjProd]
      simpa [prodCw] using
        productCWComplex_closedCellImage_eq
          ((X a).toCompactlyGenerated) ((i : s) → (X i).toCompactlyGenerated) n
            ⟨⟨⟨p, q⟩, hpq⟩, ca, k⟩
    have hsplit :
        ((cwX a).map p ca '' Metric.closedBall (0 : Fin p → ℝ) 1) ×ˢ
            (data.cw.map q k '' Metric.closedBall (0 : Fin q → ℝ) 1) =
          {z : (X a).toCompactlyGenerated × ((i : s) → (X i).toCompactlyGenerated) |
            z.1 ∈ (cwX a).map p ca '' Metric.closedBall 0 1 ∧
              ∀ i : s, z.2 i ∈ (cwX i).map (d i) (c i) '' Metric.closedBall 0 1} := by
      ext z
      constructor
      · intro hz
        rcases Set.mem_prod.mp hz with ⟨hz₁, hz₂⟩
        refine ⟨hz₁, ?_⟩
        simpa [hclosed] using hz₂
      · intro hz
        refine Set.mem_prod.mpr ⟨hz.1, ?_⟩
        simpa [hclosed] using hz.2
    have hcoord :
        {y : ((i : (insert a s : Finset ι)) → (X i).toCompactlyGenerated) |
          y ⟨a, Finset.mem_insert_self a s⟩ ∈ (cwX a).map p ca '' Metric.closedBall 0 1 ∧
            ∀ i : s,
              y ⟨i.1, Finset.mem_insert_of_mem i.2⟩ ∈
                (cwX i).map (d i) (c i) '' Metric.closedBall 0 1} =
          {y | ∀ i : (insert a s : Finset ι),
            y i ∈ (cwX i).map (dInsert i) (cInsert i) '' Metric.closedBall 0 1} := by
      ext y
      constructor
      · intro hy
        intro i
        by_cases hia : i.1 = a
        · have hi : i = ⟨a, Finset.mem_insert_self a s⟩ := Subtype.ext hia
          rw [hi, hcellInsert]
          exact hy.1
        · have his : i.1 ∈ s := (Finset.mem_insert.mp i.2).resolve_left hia
          let iOld : s := ⟨i.1, his⟩
          have hi : i = ⟨iOld.1, Finset.mem_insert_of_mem iOld.2⟩ := Subtype.ext rfl
          rw [hi, hcellOld]
          exact hy.2 iOld
      · intro hy
        refine ⟨?_, ?_⟩
        · rw [← hcellInsert]
          exact hy ⟨a, Finset.mem_insert_self a s⟩
        · intro i
          rw [← hcellOld i]
          exact hy ⟨i.1, Finset.mem_insert_of_mem i.2⟩
    calc
      insertedCw.map n j '' Metric.closedBall (0 : Fin n → ℝ) 1
          = (finitePiInsertHomeomorph X s ha).symm ''
              (prodCw.map n jProd '' Metric.closedBall (0 : Fin n → ℝ) 1) := hmap
      _ = (finitePiInsertHomeomorph X s ha).symm ''
            (((cwX a).map p ca '' Metric.closedBall (0 : Fin p → ℝ) 1) ×ˢ
              (data.cw.map q k '' Metric.closedBall (0 : Fin q → ℝ) 1)) := by
            rw [hprod]
      _ = (finitePiInsertHomeomorph X s ha).symm ''
            {z : (X a).toCompactlyGenerated × ((i : s) → (X i).toCompactlyGenerated) |
              z.1 ∈ (cwX a).map p ca '' Metric.closedBall 0 1 ∧
                ∀ i : s, z.2 i ∈ (cwX i).map (d i) (c i) '' Metric.closedBall 0 1} := by
            rw [hsplit]
      _ = {y : ((i : (insert a s : Finset ι)) → (X i).toCompactlyGenerated) |
            y ⟨a, Finset.mem_insert_self a s⟩ ∈ (cwX a).map p ca '' Metric.closedBall 0 1 ∧
              ∀ i : s,
                y ⟨i.1, Finset.mem_insert_of_mem i.2⟩ ∈
                  (cwX i).map (d i) (c i) '' Metric.closedBall 0 1} := by
            exact finitePiInsertHomeomorph_symm_image_coordinateClosedCellSet
              X cwX s ha p ca d c
      _ = {y | ∀ i : (insert a s : Finset ι),
            y i ∈ (cwX i).map (dInsert i) (cInsert i) '' Metric.closedBall 0 1} := hcoord

/-- Helper for Lemma 22.1.6: every finite supported product admits the packaged coordinatewise
closed-cell description obtained by iterating the insert constructor. -/
private theorem finitePi_hasCoordinateCellStructure
    (X : ι → PointedCompactlyGenerated.{u, w})
    (cwX : ∀ i, Topology.CWComplex (Set.univ : Set (X i).toCompactlyGenerated))
    (s : Finset ι) :
    ∃ _inst : UCompactlyGeneratedSpace.{u} ((i : s) → (X i).toCompactlyGenerated),
      ∃ cw : Topology.CWComplex (Set.univ : Set ((i : s) → (X i).toCompactlyGenerated)),
        ∀ n (j : cw.cell n),
          ∃ d : s → ℕ,
            ∃ c : ∀ i : s, (cwX i).cell (d i),
              n = ∑ i : s, d i ∧
                cw.map n j '' Metric.closedBall 0 1 =
                  {y | ∀ i : s, y i ∈ (cwX i).map (d i) (c i) '' Metric.closedBall 0 1} := by
  classical
  -- Route correction: keep the finite-support induction itself in the packaged `FinitePiCellData`
  -- format, and only unwrap the package at the end.
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨(emptyFinitePiCellData X cwX).inst, (emptyFinitePiCellData X cwX).cw,
        (emptyFinitePiCellData X cwX).closedCell⟩
  | @insert a s ha ih =>
      rcases ih with ⟨inst, cw, hclosed⟩
      let data : FinitePiCellData X cwX s :=
        { inst := inst
          cw := cw
          closedCell := hclosed }
      exact
        ⟨(finitePiCellData_insert X cwX s ha data).inst,
          (finitePiCellData_insert X cwX s ha data).cw,
          (finitePiCellData_insert X cwX s ha data).closedCell⟩

/-- Helper for Lemma 22.1.6: each finite-support slice of the weak product inherits a classical CW
structure whose closed cells are exactly the finite-subproduct closed-cell images in the ambient
weak product. -/
private theorem weakProductSupportedOn_hasFiniteSubproductCellStructure
    (X : ι → PointedCompactlyGenerated.{u, w})
    (cwX : ∀ i, Topology.CWComplex (Set.univ : Set (X i).toCompactlyGenerated))
    (s : Finset ι) :
    ∃ cw : Topology.CWComplex
        (Set.univ : Set {x : (weakProduct X).toCompactlyGenerated // x ∈ weakProductSupportedOn X s}),
      ∀ n (j : cw.cell n),
        ∃ d : s → ℕ,
          ∃ c : ∀ i : s, (cwX i).cell (d i),
            n = ∑ i : s, d i ∧
              Subtype.val '' (cw.map n j '' Metric.closedBall 0 1) =
                weakProductFiniteSubproductClosedCellImage X cwX s d c := by
  classical
  rcases finitePi_hasCoordinateCellStructure X cwX s with ⟨inst, cw, hclosed⟩
  letI := inst
  let transportedCw :
      Topology.CWComplex
        (Set.univ :
          Set {x : (weakProduct X).toCompactlyGenerated // x ∈ weakProductSupportedOn X s}) :=
    cwComplexUnivHomeomorph (weakProductSupportedOnHomeomorphFinitePi X s).symm cw
  refine ⟨transportedCw, ?_⟩
  intro n j
  rcases hclosed n j with ⟨d, c, hd, hcell⟩
  refine ⟨d, c, hd, ?_⟩
  -- Transport the finite-product closed cell through the supported-slice homeomorphism, then
  -- forget the subtype to recover the ambient weak-product closed-cell image.
  have hmap :
      transportedCw.map n j '' Metric.closedBall 0 1 =
        (weakProductSupportedOnHomeomorphFinitePi X s).symm ''
          (cw.map n j '' Metric.closedBall 0 1) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨cw.map n j z, ⟨z, hz, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, rfl⟩
  calc
    Subtype.val '' (transportedCw.map n j '' Metric.closedBall 0 1)
        = Subtype.val '' ((weakProductSupportedOnHomeomorphFinitePi X s).symm ''
            (cw.map n j '' Metric.closedBall 0 1)) := by
          rw [hmap]
    _ = Subtype.val '' ((weakProductSupportedOnHomeomorphFinitePi X s).symm ''
          {y | ∀ i : s, y i ∈ (cwX i).map (d i) (c i) '' Metric.closedBall 0 1}) := by
          rw [hcell]
    _ = weakProductFiniteSubproductClosedCellImage X cwX s d c := by
          simpa [weakProductSupportedOnHomeomorphFinitePi] using
            weakProductSupportedOnEquivFinitePi_symm_image_eq_finiteSubproductClosedCellImage
              X cwX s d c

/-- Helper for Lemma 22.1.6: choose one classical CW structure on the weak-product slice supported
on `s`, so later arguments can work with a fixed owner instead of repeatedly unpacking an
existential witness. -/
private noncomputable def weakProductSupportedOnCWComplex
    (X : ι → PointedCompactlyGenerated.{u, w})
    (cwX : ∀ i, Topology.CWComplex (Set.univ : Set (X i).toCompactlyGenerated))
    (s : Finset ι) :
    Topology.CWComplex
      (Set.univ : Set {x : (weakProduct X).toCompactlyGenerated // x ∈ weakProductSupportedOn X s}) :=
  Classical.choose (weakProductSupportedOn_hasFiniteSubproductCellStructure X cwX s)

/-- Helper for Lemma 22.1.6: every cell of the chosen supported-slice CW structure still comes
from one finite subproduct cell image in the ambient weak product. -/
private theorem weakProductSupportedOnCWComplex_closedCellImage
    (X : ι → PointedCompactlyGenerated.{u, w})
    (cwX : ∀ i, Topology.CWComplex (Set.univ : Set (X i).toCompactlyGenerated))
    (s : Finset ι) (n : ℕ)
    (j : (weakProductSupportedOnCWComplex X cwX s).cell n) :
    ∃ d : s → ℕ,
      ∃ c : ∀ i : s, (cwX i).cell (d i),
        n = ∑ i : s, d i ∧
          Subtype.val ''
              ((weakProductSupportedOnCWComplex X cwX s).map n j '' Metric.closedBall 0 1) =
            weakProductFiniteSubproductClosedCellImage X cwX s d c := by
  -- This is exactly the closed-cell formula stored in the existential slice witness selected
  -- above.
  exact (Classical.choose_spec (weakProductSupportedOn_hasFiniteSubproductCellStructure X cwX s))
    n j

/-- Helper for Lemma 22.1.6: every supported slice is Hausdorff because the chosen classical
whole-space CW structure on that slice is Hausdorff. -/
private theorem weakProductSupportedOn_t2Space
    (X : ι → PointedCompactlyGenerated.{u, w})
    (cwX : ∀ i, Topology.CWComplex (Set.univ : Set (X i).toCompactlyGenerated))
    (s : Finset ι) :
    T2Space {x : (weakProduct X).toCompactlyGenerated // x ∈ weakProductSupportedOn X s} := by
  letI := weakProductSupportedOnCWComplex X cwX s
  -- The chosen whole-space CW owner on the slice brings Hausdorffness for free.
  exact t2SpaceOfUnivCWComplex
    {x : (weakProduct X).toCompactlyGenerated // x ∈ weakProductSupportedOn X s}

/-- If each factor is equipped with a chosen classical CW structure whose distinguished point is a
vertex, then the weak product admits a classical CW structure whose closed cells come from finite
subproducts of chosen factor cells. -/
theorem weakProduct_hasFiniteSubproductCellStructure
    (X : ι → PointedCompactlyGenerated.{u, w})
    (cwX : ∀ i, Topology.CWComplex (Set.univ : Set (X i).toCompactlyGenerated))
    (hVertex : ∀ i, @IsCWVertex ((X i).toCompactlyGenerated) _ (cwX i) (X i).point) :
    ∃ cw : Topology.CWComplex (Set.univ : Set ((weakProduct X).toCompactlyGenerated)),
      ∀ n (j : cw.cell n),
        ∃ s : Finset ι,
          ∃ d : s → ℕ,
            ∃ c : ∀ i : s, (cwX i).cell (d i),
              n = ∑ i : s, d i ∧
                cw.map n j '' Metric.closedBall 0 1 =
                  weakProductFiniteSubproductClosedCellImage X cwX s d c := sorry

/-- Lemma 22.1.6: a weak product of based CW complexes, represented by chosen factor CW
structures whose distinguished points are vertices, admits a CW structure for which the weak-product
basepoint is a vertex. -/
theorem weakProduct_isBasedCWComplex
    (X : ι → PointedCompactlyGenerated.{u, w})
    (cwX : ∀ i, Topology.CWComplex (Set.univ : Set (X i).toCompactlyGenerated))
    (hVertex : ∀ i, @IsCWVertex ((X i).toCompactlyGenerated) _ (cwX i) (X i).point) :
    ∃ cw : Topology.CWComplex (Set.univ : Set ((weakProduct X).toCompactlyGenerated)),
      @IsCWVertex ((weakProduct X).toCompactlyGenerated) _ cw (weakProduct X).point := sorry

/-- The weak product from Lemma 22.1.6 has an underlying CW-complex structure, hence satisfies the
ambient repository owner `IsBasedCWComplex`. -/
theorem weakProduct_hasUnderlyingBasedCWComplex
    (X : ι → PointedCompactlyGenerated.{u, w})
    (cwX : ∀ i, Topology.CWComplex (Set.univ : Set (X i).toCompactlyGenerated))
    (hVertex : ∀ i, @IsCWVertex ((X i).toCompactlyGenerated) _ (cwX i) (X i).point) :
    IsBasedCWComplex ((weakProduct X).toBasedSpace) := sorry
