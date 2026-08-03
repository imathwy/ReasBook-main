module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.PNat.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.ShrinkingLemma
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Topology.UrysohnsLemma

public section

open scoped Topology

universe u

/-- Helper for Exercise 36.2: a finite open cover of a normal space admits nested open and
closed refinements that still cover the space. -/
lemma existsNestedFiniteChartRefinement {X : Type u} [TopologicalSpace X] [NormalSpace X]
    {ι : Type*} [Finite ι] (O : ι → Set X) (hO : ∀ i, IsOpen (O i))
    (hcover : ⋃ i, O i = Set.univ) :
    ∃ (W K : ι → Set X),
      (⋃ i, W i = Set.univ) ∧ (∀ i, IsOpen (W i)) ∧
      (∀ i, closure (W i) ⊆ O i) ∧ (⋃ i, K i = Set.univ) ∧
      (∀ i, IsClosed (K i)) ∧ ∀ i, K i ⊆ W i := by
  letI := Fintype.ofFinite ι
  -- First shrink the cover by open sets whose closures remain in the original charts.
  obtain ⟨W, hWcover, hWopen, hWclosure⟩ :=
    exists_iUnion_eq_closure_subset hO (fun x ↦ Set.toFinite {i | x ∈ O i}) hcover
  -- A second shrinking produces a closed cover inside those open sets.
  obtain ⟨K, hKcover, hKclosed, hKW⟩ :=
    exists_iUnion_eq_closed_subset hWopen (fun x ↦ Set.toFinite {i | x ∈ W i}) hWcover
  exact ⟨W, K, hWcover, hWopen, hWclosure, hKcover, hKclosed, hKW⟩

/-- Helper for Exercise 36.2: a continuous Euclidean-valued map on a closed subset of a normal
space extends continuously to the whole space. -/
lemma existsContinuousEuclideanExtension {X : Type u} [TopologicalSpace X] [NormalSpace X]
    {C : Set X} (hC : IsClosed C) {ι : Type*}
    (f : C(C, EuclideanSpace ℝ ι)) :
    ∃ g : C(X, EuclideanSpace ℝ ι), ∀ x (hx : x ∈ C), g x = f ⟨x, hx⟩ := by
  -- Tietze extension applies coordinatewise through the finite product representation.
  let fCoordinates : C(C, ι → ℝ) :=
    ⟨fun x ↦ EuclideanSpace.equiv ι ℝ (f x),
      (EuclideanSpace.equiv ι ℝ).continuous.comp f.continuous⟩
  obtain ⟨gCoordinates, hgCoordinates⟩ := fCoordinates.exists_restrict_eq hC
  let g : C(X, EuclideanSpace ℝ ι) :=
    ⟨fun x ↦ (EuclideanSpace.equiv ι ℝ).symm (gCoordinates x),
      (EuclideanSpace.equiv ι ℝ).symm.continuous.comp gCoordinates.continuous⟩
  refine ⟨g, ?_⟩
  intro x hx
  have hvalue := congrArg (fun q : C(C, ι → ℝ) ↦ q ⟨x, hx⟩) hgCoordinates
  -- Apply the inverse coordinate equivalence to the extension equation.
  change (EuclideanSpace.equiv ι ℝ).symm (gCoordinates x) = f ⟨x, hx⟩
  have hcoordinateValue : gCoordinates x = (EuclideanSpace.equiv ι ℝ) (f ⟨x, hx⟩) := by
    simpa [fCoordinates] using hvalue
  calc
    (EuclideanSpace.equiv ι ℝ).symm (gCoordinates x) =
        (EuclideanSpace.equiv ι ℝ).symm ((EuclideanSpace.equiv ι ℝ) (f ⟨x, hx⟩)) :=
      congrArg (EuclideanSpace.equiv ι ℝ).symm hcoordinateValue
    _ = f ⟨x, hx⟩ := (EuclideanSpace.equiv ι ℝ).symm_apply_apply _

/-- Helper for Exercise 36.2: a local Euclidean chart admits a global extension together with a
continuous marker that is one on a closed core and zero off the chart region. -/
lemma existsMarkedChartExtension {X : Type u} [TopologicalSpace X] [NormalSpace X]
    {K W U : Set X} (hKclosed : IsClosed K) (hWopen : IsOpen W) (hKW : K ⊆ W)
    (hWU : closure W ⊆ U) {ι : Type*}
    (e : U → EuclideanSpace ℝ ι) (he : Continuous e) :
    ∃ (b : C(X, ℝ)) (g : C(X, EuclideanSpace ℝ ι)),
      Set.EqOn b 1 K ∧ Set.EqOn b 0 Wᶜ ∧
      ∀ x (hx : x ∈ closure W), g x = e ⟨x, hWU hx⟩ := by
  -- Restrict the chart to the closed set on which Tietze extension is available.
  have hrestricted : Continuous (fun x : closure W ↦ e ⟨x, hWU x.property⟩) := by
    fun_prop
  let restricted : C(closure W, EuclideanSpace ℝ ι) :=
    ⟨fun x ↦ e ⟨x, hWU x.property⟩, hrestricted⟩
  obtain ⟨g, hg⟩ := existsContinuousEuclideanExtension isClosed_closure restricted
  -- Urysohn's lemma separates the closed core from the complement of the open chart region.
  have hdisjoint : Disjoint Wᶜ K := by
    rw [Set.disjoint_left]
    intro x hxW hxK
    exact hxW (hKW hxK)
  obtain ⟨b, hb0, hb1, -⟩ :=
    exists_continuous_zero_one_of_isClosed hWopen.isClosed_compl hKclosed hdisjoint
  exact ⟨b, g, hb1, hb0, hg⟩

/-- Helper for Exercise 36.2: the marker and extended coordinates of one chart separate a point
in its closed core from every other point. -/
lemma markedChartCoordinates_separate {X : Type u} [TopologicalSpace X]
    {K W U : Set X} (hKW : K ⊆ W) (hWU : closure W ⊆ U)
    {ι : Type*} (e : U → EuclideanSpace ℝ ι)
    (he : Function.Injective e) (b : X → ℝ) (g : X → EuclideanSpace ℝ ι)
    (hb1 : Set.EqOn b 1 K) (hb0 : Set.EqOn b 0 Wᶜ)
    (hg : ∀ x (hx : x ∈ closure W), g x = e ⟨x, hWU hx⟩)
    {x y : X} (hxK : x ∈ K) (hbxy : b x = b y) (hgxy : g x = g y) : x = y := by
  -- Marker equality forces the second point into the open chart region.
  have hbx : b x = 1 := hb1 hxK
  have hby : b y = 1 := hbxy.symm.trans hbx
  have hyW : y ∈ W := by
    by_contra hyW
    have hby0 : b y = 0 := hb0 hyW
    linarith
  have hxW : x ∈ W := hKW hxK
  have hxClosure : x ∈ closure W := subset_closure hxW
  have hyClosure : y ∈ closure W := subset_closure hyW
  -- On the closure, the extensions are the original injective chart.
  have hexy : e ⟨x, hWU hxClosure⟩ = e ⟨y, hWU hyClosure⟩ := by
    rw [← hg x hxClosure, ← hg y hyClosure]
    exact hgxy
  exact congrArg Subtype.val (he hexy)

/-- Exercise 36.2. A compact Hausdorff space that is locally embeddable in
positive-dimensional Euclidean spaces embeds in one positive-dimensional Euclidean space. -/
theorem existsEuclideanEmbeddingOfCompactOfLocallyEmbeddable {X : Type u}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (hlocal : ∀ x : X, ∃ (U : Set X) (k : ℕ+),
      U ∈ 𝓝 x ∧ ∃ f : U → EuclideanSpace ℝ (Fin k), Topology.IsEmbedding f) :
    ∃ (N : ℕ+) (f : X → EuclideanSpace ℝ (Fin N)), Topology.IsEmbedding f := by
  classical
  -- Choose one chart at every point and replace its neighborhood by an open subset.
  choose U k hU e he using hlocal
  let O : X → Set X := fun x ↦ interior (U x)
  have hOopen : ∀ x, IsOpen (O x) := fun x ↦ isOpen_interior
  have hxO : ∀ x, x ∈ O x := fun x ↦ mem_interior_iff_mem_nhds.mpr (hU x)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hOopen
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxO x⟩)
  let I := {x // x ∈ t}
  have hfiniteCover : ⋃ i : I, O i.1 = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    intro x hx
    rcases Set.mem_iUnion₂.mp (ht hx) with ⟨z, hzt, hxz⟩
    exact Set.mem_iUnion.mpr ⟨⟨z, hzt⟩, hxz⟩
  -- Shrink the finite chart cover twice to obtain the nested geometry used below.
  obtain ⟨W, K, hWcover, hWopen, hWclosure, hKcover, hKclosed, hKW⟩ :=
    existsNestedFiniteChartRefinement (fun i : I ↦ O i.1) (fun i ↦ hOopen i.1) hfiniteCover
  have hOU : ∀ i : I, O i.1 ⊆ U i.1 := fun i ↦ interior_subset
  have hWU : ∀ i : I, closure (W i) ⊆ U i.1 := fun i ↦ (hWclosure i).trans (hOU i)
  -- Extend every chart from the closed refinement and construct its Urysohn marker.
  have hmarked : ∀ i : I, ∃ (b : C(X, ℝ)) (g : C(X, EuclideanSpace ℝ (Fin (k i.1)))),
      Set.EqOn b 1 (K i) ∧ Set.EqOn b 0 (W i)ᶜ ∧
      ∀ x (hx : x ∈ closure (W i)), g x = e i.1 ⟨x, hWU i hx⟩ := by
    intro i
    exact existsMarkedChartExtension (hKclosed i) (hWopen i) (hKW i) (hWU i)
      (e i.1) (he i.1).continuous
  choose b g hb1 hb0 hg using hmarked
  let J := Unit ⊕ Σ i : I, Option (Fin (k i.1))
  let coordinates : X → J → ℝ := fun x q ↦
    match q with
    | Sum.inl _ => 0
    | Sum.inr ⟨i, none⟩ => b i x
    | Sum.inr ⟨i, some j⟩ => g i x j
  let F : X → EuclideanSpace ℝ J := fun x ↦ (EuclideanSpace.equiv J ℝ).symm (coordinates x)
  have hFcontinuous : Continuous F := by
    apply (EuclideanSpace.equiv J ℝ).symm.continuous.comp
    apply continuous_pi
    intro q
    rcases q with q | q
    · exact continuous_const
    · rcases q with ⟨i, q⟩
      rcases q with _ | j
      · exact (b i).continuous
      · exact (EuclideanSpace.proj j).continuous.comp (g i).continuous
  have hFinjective : Function.Injective F := by
    intro x y hxy
    have hcoordinates : coordinates x = coordinates y := by
      simpa [F] using congrArg (EuclideanSpace.equiv J ℝ) hxy
    rcases Set.mem_iUnion.mp (Set.ext_iff.mp hKcover x |>.mpr trivial) with ⟨i, hxi⟩
    have hbxy : b i x = b i y := by
      exact congrFun hcoordinates (Sum.inr ⟨i, none⟩)
    have hgxy : g i x = g i y := by
      apply (EuclideanSpace.equiv (Fin (k i.1)) ℝ).injective
      ext j
      exact congrFun hcoordinates (Sum.inr ⟨i, some j⟩)
    exact markedChartCoordinates_separate (hKW i) (hWU i) (e i.1) (he i.1).injective
      (b i) (g i) (hb1 i) (hb0 i) (hg i) hxi hbxy hgxy
  -- Reindex the finite coordinate type by `Fin`, retaining a positive dimension via `Unit`.
  let reindex := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin J)
  have hcard : 0 < Fintype.card J := Fintype.card_pos
  let N : ℕ+ := ⟨Fintype.card J, hcard⟩
  let finalMap : X → EuclideanSpace ℝ (Fin N) := fun x ↦ reindex (F x)
  have hfinalContinuous : Continuous finalMap := reindex.continuous.comp hFcontinuous
  have hfinalInjective : Function.Injective finalMap := reindex.injective.comp hFinjective
  exact ⟨N, finalMap, (hfinalContinuous.isClosedEmbedding hfinalInjective).isEmbedding⟩
