import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Real.Cardinality
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_2_8
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Proposition_5_2_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Remark_5_1_5

open CategoryTheory CategoryTheory.Limits

universe u v w z

noncomputable section

-- Semantic search hits: `CategoryTheory.Limits.limit.isLimit`; local
-- Chapter 5 precedent: `weakHausdorffKification` and
-- `compactlyGeneratedWeakHausdorffSpaceCatToTop` from `Definition_5_2_8`.

/-- Helper for Proposition 5.2.11: arbitrary products of weak Hausdorff spaces are weak
Hausdorff. -/
lemma weaklyHausdorffSpacePi
    {ι : Type u} {X : ι → Type w} [∀ i, TopologicalSpace (X i)]
    [∀ i, WeaklyHausdorffSpace.{w, w} (X i)] :
    WeaklyHausdorffSpace.{max u w, w} (∀ i, X i) := by
  refine WeaklyHausdorffSpace.mk ?_
  intro K _ _ _ g hg
  let gCoord : ∀ i, K → X i := fun i k ↦ g k i
  have hgCoord : ∀ i, Continuous (gCoord i) := fun i ↦ (continuous_apply i).comp hg
  let rangeMap : K → ∀ i, Set.range (gCoord i) := fun k i ↦ ⟨gCoord i k, ⟨k, rfl⟩⟩
  have hRangeMap : Continuous rangeMap := by
    -- Factor the compact-source map through the product of its coordinate ranges.
    refine continuous_pi fun i ↦ ?_
    exact (hgCoord i).subtype_mk fun k ↦ ⟨k, rfl⟩
  let _ : ∀ i, T2Space (Set.range (gCoord i)) := fun i ↦
    range_t2Space_of_compactHausdorffMap (K := K) (X := X i) (g := gCoord i) (hg := hgCoord i)
  have hClosedRangeMap : IsClosed (Set.range rangeMap) :=
    Continuous.isClosed_range hRangeMap
  have hClosedEmbedding :
      Topology.IsClosedEmbedding (Pi.map fun i ↦ ((↑) : Set.range (gCoord i) → X i)) := by
    -- The product of the closed range inclusions is a closed embedding into the ambient product.
    refine Topology.IsClosedEmbedding.piMap fun i ↦ ?_
    letI : WeaklyHausdorffSpace (X i) := inferInstance
    exact (Continuous.isClosed_range (g := gCoord i) (hg := hgCoord i)).isClosedEmbedding_subtypeVal
  have hClosedImage :
      IsClosed ((Pi.map fun i ↦ ((↑) : Set.range (gCoord i) → X i)) '' Set.range rangeMap) := by
    -- Push the closed range in the product of coordinate ranges back to the ambient product.
    exact hClosedEmbedding.isClosedMap _ hClosedRangeMap
  have hRangeEq :
      (Pi.map fun i ↦ ((↑) : Set.range (gCoord i) → X i)) '' Set.range rangeMap = Set.range g := by
    -- Forgetting the range coordinates recovers exactly the original image in the ambient product.
    ext x
    constructor
    · rintro ⟨y, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨rangeMap k, ⟨k, rfl⟩, rfl⟩
  simpa [hRangeEq] using hClosedImage

/-- Helper for Proposition 5.2.11: point-set limits of weak Hausdorff spaces are weak
Hausdorff. -/
instance instWeaklyHausdorffSpaceLimit
    {J : Type u} [Category.{v} J] (F : J ⥤ TopCat.{w}) [HasLimit F]
    [∀ j, WeaklyHausdorffSpace.{w, w} (F.obj j)] :
    WeaklyHausdorffSpace.{w, w} (limit F : TopCat.{w}) := by
  let toProduct : ↥(limit F : TopCat.{w}) → ∀ j, ↥(F.obj j) := fun x j ↦ limit.π F j x
  have hInj : Function.Injective toProduct := by
    intro x y hxy
    let fx : TopCat.of PUnit ⟶ limit F := TopCat.ofHom ⟨fun _ ↦ x, continuous_const⟩
    let fy : TopCat.of PUnit ⟶ limit F := TopCat.ofHom ⟨fun _ ↦ y, continuous_const⟩
    have hMor : fx = fy := by
      apply limit.hom_ext
      intro j
      ext u
      exact congrFun hxy j
    exact congrArg (fun f : TopCat.of PUnit ⟶ limit F ↦ f PUnit.unit) hMor
  have hEmbedding : Topology.IsEmbedding toProduct := by
    have hTop :
        (limit F : TopCat.{w}).str =
          TopologicalSpace.induced toProduct Pi.topologicalSpace := by
      rw [TopCat.limit_topology, induced_to_pi]
    -- The chosen limit topology is induced from the product of the projection maps.
    exact hTop.symm ▸ (hInj.isEmbedding_induced (f := toProduct))
  have hProd : WeaklyHausdorffSpace.{max u w, w} (∀ j, F.obj j) := by
    let _ : ∀ j, WeaklyHausdorffSpace.{w, w} (F.obj j) := fun j ↦ inferInstance
    exact weaklyHausdorffSpacePi
  let _ : WeaklyHausdorffSpace.{max u w, w} (∀ j, F.obj j) := hProd
  exact hEmbedding.weaklyHausdorffSpace

/-- Helper for Proposition 5.2.11: the `n`-th level slice in `ι → ℕ` consists of functions taking
only the values `0` and `n`, with at most `n` zero-coordinates. -/
private def levelSlice (ι : Type u) (n : ℕ+) : Set (ι → ℕ) :=
  {f | (∀ i, f i = 0 ∨ f i = n) ∧
      ∀ t : Finset ι, (∀ i ∈ t, f i = 0) → t.card ≤ n}

/-- Helper for Proposition 5.2.11: the union of all positive level slices is the compactly-closed
but nonclosed subset used to refute compact generation for the product witness. -/
private def levelCounterexample (ι : Type u) : Set (ι → ℕ) :=
  ⋃ n : ℕ+, levelSlice ι n

/-- Helper for Proposition 5.2.11: a function in a level slice has only finitely many
zero-coordinates. -/
private lemma zeroSetFinite_of_mem_levelSlice {ι : Type u} {n : ℕ+} {f : ι → ℕ}
    (hf : f ∈ levelSlice ι n) : Set.Finite {i | f i = 0} := by
  classical
  -- If there were infinitely many zeros, we could choose `n + 1` of them and violate the bound.
  by_contra hfinite
  have hinf : Set.Infinite {i | f i = 0} := by
    simpa only [Set.Infinite] using hfinite
  obtain ⟨t, htsubset, htcard⟩ := hinf.exists_subset_card_eq ((n : ℕ) + 1)
  have hle := hf.2 t fun i hi ↦ htsubset hi
  rw [htcard] at hle
  exact Nat.not_succ_le_self _ hle

/-- Helper for Proposition 5.2.11: the function that is `0` on a finite set and `s.card + 1`
elsewhere lies in the corresponding positive level slice. -/
private lemma finsetPiecewiseZero_mem_levelSlice {ι : Type u} [DecidableEq ι] (s : Finset ι) :
    let n : ℕ+ := ⟨s.card + 1, Nat.succ_pos _⟩
    s.piecewise (fun _ : ι ↦ 0) (fun _ : ι ↦ (n : ℕ)) ∈ levelSlice ι n := by
  let n : ℕ+ := ⟨s.card + 1, Nat.succ_pos _⟩
  -- The only zero-coordinates are those in `s`, so every zero-set witness is bounded by `s.card`.
  refine ⟨?_, ?_⟩
  · intro i
    by_cases hi : i ∈ s
    · left
      simp [Finset.piecewise, hi]
    · right
      simp [Finset.piecewise, hi]
  · intro t ht
    have hsubset : t ⊆ s := by
      intro i hi
      by_contra his
      have hzero := ht i hi
      simp [Finset.piecewise, his] at hzero
    exact le_trans (Finset.card_le_card hsubset) (Nat.le_succ _)

/-- Helper for Proposition 5.2.11: every level slice is closed in the product topology on
`ι → ℕ`. -/
private lemma levelSliceIsClosed {ι : Type u} (n : ℕ+) : IsClosed (levelSlice ι n) := by
  classical
  rw [← isOpen_compl_iff]
  let badValues : Set (ι → ℕ) := {f | ∃ i, f i ≠ 0 ∧ f i ≠ n}
  let tooManyZeros : Set (ι → ℕ) :=
    ⋃ t : {t : Finset ι // (n : ℕ) < t.1.card}, {f | ∀ i ∈ (t : Finset ι), f i = 0}
  have hbadValues : IsOpen badValues := by
    -- A forbidden coordinate value is detected on a single coordinate, hence by an open cylinder.
    rw [show badValues = ⋃ i : ι, {f : ι → ℕ | f i ≠ 0 ∧ f i ≠ n} by
      ext f
      simp [badValues]]
    refine isOpen_iUnion fun i ↦ ?_
    exact IsOpen.preimage (f := fun f : ι → ℕ ↦ f i)
      (t := ({m : ℕ | m ≠ 0 ∧ m ≠ n} : Set ℕ))
      (continuous_apply i) (isOpen_discrete ({m : ℕ | m ≠ 0 ∧ m ≠ n} : Set ℕ))
  have htooManyZeros : IsOpen tooManyZeros := by
    -- A witness finite set of zero-coordinates also defines an open cylinder in the product.
    refine isOpen_iUnion fun t ↦ ?_
    simpa [tooManyZeros, Set.pi, Finset.mem_coe] using
      isOpen_set_pi (i := ((t : Finset ι) : Set ι)) (s := fun _ ↦ ({0} : Set ℕ))
        t.1.finite_toSet (fun _ _ ↦ isOpen_discrete ({0} : Set ℕ))
  have hcompl :
      (levelSlice ι n)ᶜ = badValues ∪ tooManyZeros := by
    ext f
    constructor
    · intro hf
      by_cases hvals : ∀ i, f i = 0 ∨ f i = n
      · right
        have hbound : ¬ ∀ t : Finset ι, (∀ i ∈ t, f i = 0) → t.card ≤ n := by
          exact fun hcount ↦ hf ⟨hvals, hcount⟩
        push Not at hbound
        rcases hbound with ⟨t, htzero, htcard⟩
        exact Set.mem_iUnion.2 ⟨⟨t, htcard⟩, htzero⟩
      · left
        push Not at hvals
        rcases hvals with ⟨i, hi0, hin⟩
        exact ⟨i, hi0, hin⟩
    · intro hf
      rcases hf with hbad | hzeros
      · intro hslice
        rcases hbad with ⟨i, hi0, hin⟩
        rcases hslice.1 i with hzero | hlevel
        · exact hi0 hzero
        · exact hin hlevel
      · rcases Set.mem_iUnion.1 hzeros with ⟨t, htzero⟩
        intro hslice
        exact (Nat.not_lt_of_ge (hslice.2 t htzero)) t.2
  simpa [hcompl] using hbadValues.union htooManyZeros

/-- Helper for Proposition 5.2.11: the zero function lies in the closure of the level
counterexample, but it does not belong to the counterexample itself. -/
private lemma zeroFunction_mem_closure_levelCounterexample {ι : Type u} [Uncountable ι] :
    (fun _ : ι ↦ 0) ∈ closure (levelCounterexample ι) ∧
      (fun _ : ι ↦ 0) ∉ levelCounterexample ι := by
  classical
  constructor
  · -- Every neighborhood of the zero function contains one of the finite-support approximants.
    rw [mem_closure_iff_nhds]
    intro s hs
    rcases mem_nhds_iff.1 hs with ⟨u, hu_subset, hu_open, hzero_mem⟩
    rcases (isOpen_pi_iff.1 hu_open) (fun _ : ι ↦ 0) hzero_mem with ⟨I, v, hv, hIv⟩
    let n : ℕ+ := ⟨I.card + 1, Nat.succ_pos _⟩
    refine ⟨I.piecewise (fun _ : ι ↦ 0) (fun _ : ι ↦ (n : ℕ)), hu_subset ?_, ?_⟩
    · exact hIv fun i hi ↦ by
        have hi' : i ∈ I := Finset.mem_coe.mp hi
        have hvalue : I.piecewise (fun _ : ι ↦ 0) (fun _ : ι ↦ (n : ℕ)) i = 0 := by
          simp [Finset.piecewise, hi']
        simpa [hvalue] using (hv i hi).2
    · exact Set.mem_iUnion.2 ⟨n, by simpa [n] using finsetPiecewiseZero_mem_levelSlice I⟩
  · -- The zero function has infinitely many zero-coordinates, so it cannot sit in any level slice.
    intro hz
    rcases Set.mem_iUnion.1 hz with ⟨n, hn⟩
    have hfinite : Set.Finite ({i : ι | (fun _ : ι ↦ 0) i = 0}) :=
      zeroSetFinite_of_mem_levelSlice (ι := ι) hn
    have : Finite ι := by
      simpa [Set.finite_univ_iff] using hfinite
    exact Finite.false this

/-- Helper for Proposition 5.2.11: the coordinates that never attain the value `n` on the image
of `g`. -/
private def badCoordinates {ι : Type u} {K : Type*} [TopologicalSpace K] (g : C(K, ι → ℕ))
    (n : ℕ+) : Set ι :=
  {i | (n : ℕ) ∉ Set.range fun x : K ↦ g x i}

/-- Helper for Proposition 5.2.11: the positive levels that actually occur on the image of `g`.
-/
private def relevantLevels {ι : Type u} {K : Type*} [TopologicalSpace K] (g : C(K, ι → ℕ)) :
    Set ℕ+ :=
  {n | ∃ x : K, g x ∈ levelSlice ι n}

/-- Helper for Proposition 5.2.11: a compact image in `ι → ℕ` meets only finitely many positive
level slices when `ι` is uncountable. -/
private lemma relevantLevelsFiniteOfCompact {ι : Type u} [Uncountable ι] {K : Type*}
    [TopologicalSpace K] [CompactSpace K] (g : C(K, ι → ℕ)) :
    Set.Finite (relevantLevels (ι := ι) g) := by
  classical
  let R : Set ℕ+ := relevantLevels (ι := ι) g
  let U : Set ι := ⋃ n ∈ R, badCoordinates g n
  have hUcount : U.Countable := by
    -- Each relevant level has only finitely many bad coordinates, and there are countably many
    -- positive levels to begin with.
    refine Set.Countable.biUnion (Set.to_countable R) ?_
    intro n hn
    rcases hn with ⟨x, hx⟩
    refine (zeroSetFinite_of_mem_levelSlice (ι := ι) hx).countable.mono ?_
    intro i hi
    have hnot : g x i ≠ n := by
      intro hgi
      exact hi ⟨x, hgi⟩
    rcases hx.1 i with hzero | hlevel
    · exact hzero
    · exact (hnot hlevel).elim
  have hnotall : ¬ ∀ i : ι, i ∈ U := by
    intro hall
    have hUeq : U = Set.univ := by
      ext i
      simp [hall i]
    exact Set.not_countable_univ (hUeq ▸ hUcount)
  push Not at hnotall
  rcases hnotall with ⟨i, hiU⟩
  have hcoordFinite : Set.Finite (Set.range fun x : K ↦ g x i) := by
    exact (isCompact_range ((continuous_apply i).comp g.continuous)).finite_of_discrete
  have himageFinite : Set.Finite ((fun n : ℕ+ ↦ (n : ℕ)) '' R) := by
    refine hcoordFinite.subset ?_
    rintro m ⟨n, hnR, rfl⟩
    have hnotBad : i ∉ badCoordinates g n := by
      intro hiBad
      exact hiU <| Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨hnR, hiBad⟩⟩
    simpa [badCoordinates] using hnotBad
  exact himageFinite.of_finite_image fun a _ b _ hab ↦ PNat.coe_injective hab

/-- Helper for Proposition 5.2.11: the union of the positive level slices is compactly closed. -/
private lemma levelCounterexampleIsCompactlyClosed {ι : Type u} [Uncountable ι] :
    IsCompactlyClosed (levelCounterexample ι) := by
  intro K _ _ g
  classical
  let R : Set ℕ+ := relevantLevels (ι := ι) g
  have hRfinite : R.Finite := relevantLevelsFiniteOfCompact (ι := ι) g
  have hpreimage :
      g ⁻¹' levelCounterexample ι = ⋃ n ∈ R, g ⁻¹' levelSlice ι n := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨n, hnx⟩
      exact Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨⟨x, hnx⟩, hnx⟩⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨n, hx⟩
      rcases Set.mem_iUnion.1 hx with ⟨_, hnx⟩
      exact Set.mem_iUnion.2 ⟨n, hnx⟩
  -- On a compact source, only finitely many levels matter, so the preimage is a finite union.
  rw [hpreimage]
  exact hRfinite.isClosed_biUnion fun n hn ↦
    (levelSliceIsClosed (ι := ι) n).preimage g.continuous

/-- Helper for Proposition 5.2.11: compact generation transfers across a homeomorphism. -/
private theorem uCompactlyGeneratedSpaceHomeomorph
    {X : Type w} [TopologicalSpace X] (hX : UCompactlyGeneratedSpace.{z} X)
    {Y : Type w} [TopologicalSpace Y] (e : X ≃ₜ Y) :
    UCompactlyGeneratedSpace.{z} Y := by
  -- Check continuity after pulling back along the homeomorphism, then compose with the inverse.
  let _ : UCompactlyGeneratedSpace.{z} X := hX
  refine uCompactlyGeneratedSpace_of_continuous_maps ?_
  intro Z tZ f hf
  have hPullback : Continuous (f ∘ e) := by
    refine continuous_from_uCompactlyGeneratedSpace (f ∘ e) ?_
    intro S g
    have hComp : Continuous ((f ∘ e) ∘ g) := by
      simpa [Function.comp_def] using hf (CompHaus.of S) ⟨e ∘ g, e.continuous.comp g.continuous⟩
    simpa [Function.comp_def] using hComp
  simpa [Function.comp_def] using hPullback.comp e.symm.continuous

/-- Helper for Proposition 5.2.11: the pointwise `ULift.down` homeomorphism identifies
`ℝ → ULift.{w} ℕ` with `ℝ → ℕ`. -/
private def uliftNatDownHomeomorph : (ℝ → ULift.{w} ℕ) ≃ₜ (ℝ → ℕ) :=
  Homeomorph.piCongrRight fun _ : ℝ ↦ (Homeomorph.ulift : ULift.{w} ℕ ≃ₜ ℕ)

/-- Helper for Proposition 5.2.11: the universe-lifted product `ℝ → ULift.{w} ℕ` is not compactly
generated. -/
private theorem uliftNatProduct_not_uCompactlyGenerated :
    ¬ UCompactlyGeneratedSpace.{z} (ℝ → ULift.{w} ℕ) := by
  intro hk
  let A : Set (ℝ → ULift.{w} ℕ) := uliftNatDownHomeomorph ⁻¹' levelCounterexample ℝ
  have hAcompact : IsCompactlyClosed A := by
    -- Pull back the standard uncountable-product counterexample along the pointwise `ULift.down`.
    exact (levelCounterexampleIsCompactlyClosed (ι := ℝ)).preimage uliftNatDownHomeomorph.continuous
  have hAclosed : IsClosed A := by
    -- In a compactly generated space, every compactly closed subset is closed.
    let _ : UCompactlyGeneratedSpace.{z} (ℝ → ULift.{w} ℕ) := hk
    exact IsCompactlyClosed.isClosed hAcompact
  have hBaseClosed : IsClosed (levelCounterexample ℝ) := by
    -- Transport closedness back to the simpler product `ℝ → ℕ`.
    simpa [A, uliftNatDownHomeomorph] using hAclosed.preimage uliftNatDownHomeomorph.symm.continuous
  have hzero := zeroFunction_mem_closure_levelCounterexample (ι := ℝ)
  exact hzero.2 <| by
    simpa [hBaseClosed.closure_eq] using hzero.1

/-- Helper for Proposition 5.2.11: the constant family of copies of `ULift.{w} ℕ` indexed by
`ℝ`. -/
private abbrev baseDiscreteNatFamily : ℝ → TopCat.{w} :=
  fun _ : ℝ ↦ TopCat.of.{w} (ULift.{w} ℕ)

/-- Helper for Proposition 5.2.11: the corresponding discrete diagram in `TopCat`. -/
private abbrev baseDiscreteNatDiagram : Discrete ℝ ⥤ TopCat.{w} :=
  Discrete.functor baseDiscreteNatFamily

/-- Helper for Proposition 5.2.11: the standard product cone on `ℝ → ULift.{w} ℕ`. -/
private abbrev baseDiscreteNatCone : Fan baseDiscreteNatFamily :=
  Fan.mk (TopCat.of.{w} (ℝ → ULift.{w} ℕ))
    (fun r ↦ TopCat.ofHom ⟨fun f ↦ f r, continuous_apply r⟩)

/-- Helper for Proposition 5.2.11: the standard product cone is limiting for the discrete family.
-/
private def baseDiscreteNatConeIsLimit : IsLimit baseDiscreteNatCone := by
  -- Maps into the product are assembled coordinatewise, and equalities are checked coordinatewise.
  refine Limits.mkFanLimit _ ?_ ?_ ?_
  · intro s
    exact
      TopCat.ofHom
        ⟨fun x r ↦ s.proj r x, continuous_pi fun r ↦ (s.proj r).hom.continuous⟩
  · intro s r
    ext x
    rfl
  · intro s m hm
    ext x
    funext r
    exact congrArg (fun g : s.pt ⟶ baseDiscreteNatFamily r ↦ g x) (hm r)

/-- Proposition 5.2.11 (2): there exists a point-set limit of `k`-spaces that is not a
`k`-space. -/
theorem exists_limit_uCompactlyGeneratedSpace_not_uCompactlyGeneratedSpace :
    ∃ (J : Type u) (hJ : Category.{v} J) (F : J ⥤ TopCat.{w}) (hF : HasLimit F),
      (∀ j, UCompactlyGeneratedSpace (F.obj j)) ∧
        ¬ UCompactlyGeneratedSpace (limit F : TopCat.{w}) := by
  -- Route correction: build the non-`k` witness locally from the uncountable product
  -- `ℝ → ULift.{w} ℕ`, then package it as a discrete-diagram limit and lift the index universes.
  let baseF : Discrete ℝ ⥤ TopCat.{w} := baseDiscreteNatDiagram
  have hBaseObj : ∀ j, UCompactlyGeneratedSpace (baseF.obj j) := by
    rintro ⟨r⟩
    simpa [baseF, baseDiscreteNatDiagram, baseDiscreteNatFamily] using
      (inferInstance : UCompactlyGeneratedSpace (TopCat.of.{w} (ULift.{w} ℕ) : TopCat.{w}))
  have hBaseConeLimit : IsLimit (baseDiscreteNatCone : Cone baseF) := by
    simpa [baseF, baseDiscreteNatDiagram, baseDiscreteNatFamily, baseDiscreteNatCone] using
      baseDiscreteNatConeIsLimit
  let hBaseLimit : HasLimit baseF := HasLimit.mk
    { cone := baseDiscreteNatCone
      isLimit := hBaseConeLimit }
  have hBaseNot : ¬ UCompactlyGeneratedSpace (limit baseF : TopCat.{w}) := by
    intro hLimit
    let _ : HasLimit baseF := hBaseLimit
    have hBaseIso : baseDiscreteNatCone.pt ≅ limit baseF :=
      IsLimit.conePointUniqueUpToIso hBaseConeLimit (limit.isLimit baseF)
    have hProduct : UCompactlyGeneratedSpace baseDiscreteNatCone.pt := by
      exact uCompactlyGeneratedSpaceHomeomorph hLimit (e := TopCat.homeoOfIso hBaseIso.symm)
    exact uliftNatProduct_not_uCompactlyGenerated hProduct
  letI : Category.{0} (ULift.{u} (Discrete ℝ)) :=
    CategoryTheory.uliftCategory (C := Discrete ℝ)
  let J : Type u := CategoryTheory.ULiftHom.{v} (ULift.{u} (Discrete ℝ))
  let eIndex : Discrete ℝ ≌ J :=
    CategoryTheory.ULiftHomULiftCategory.equiv (Discrete ℝ)
  let F : J ⥤ TopCat.{w} := eIndex.inverse ⋙ baseF
  let _ : HasLimit baseF := hBaseLimit
  let _ : HasLimit F := by
    -- Transport the known limit of the base discrete diagram across the index equivalence.
    exact (hasLimit_inverse_equivalence_comp_iff (F := baseF) eIndex).2 inferInstance
  have hIndexIso : eIndex.functor ⋙ F ≅ baseF :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerRight eIndex.unitIso.symm baseF ≪≫
      Functor.leftUnitor baseF
  have hLimitIso : limit baseF ≅ limit F :=
    HasLimit.isoOfEquivalence eIndex hIndexIso
  refine ⟨J, inferInstance, F, inferInstance, ?_⟩
  refine ⟨?_, ?_⟩
  · intro j
    -- Objectwise compact generation is inherited from the base discrete diagram.
    change UCompactlyGeneratedSpace (TopCat.of.{w} (ULift.{w} ℕ) : TopCat.{w})
    infer_instance
  · intro hLimit
    have hBaseLimit' : UCompactlyGeneratedSpace (limit baseF : TopCat.{w}) := by
      exact uCompactlyGeneratedSpaceHomeomorph hLimit (e := TopCat.homeoOfIso hLimitIso.symm)
    exact hBaseNot hBaseLimit'

private def compactlyGeneratedWeakHausdorffDiagramToTop
    {J : Type u} [Category.{v} J] (F : J ⥤ compactlyGeneratedWeakHausdorffSpaceCat.{w}) :
    J ⥤ TopCat.{w} :=
  F ⋙ compactlyGeneratedWeakHausdorffSpaceCatToTop

private def compactlyGeneratedWeakHausdorffDiagramToWeakHausdorff
    {J : Type u} [Category.{v} J] (F : J ⥤ compactlyGeneratedWeakHausdorffSpaceCat.{w}) :
    J ⥤ weakHausdorffSpaceCat.{w} :=
  F ⋙ compactlyGeneratedWeakHausdorffToWeakHausdorff

private def compactlyGeneratedWeakHausdorffPointSetLimitToTop
    {J : Type u} [Category.{v} J] (F : J ⥤ compactlyGeneratedWeakHausdorffSpaceCat.{w})
    [HasLimit (compactlyGeneratedWeakHausdorffDiagramToTop F)] :
    TopCat.{w} :=
  limit (compactlyGeneratedWeakHausdorffDiagramToTop F)

private def compactlyGeneratedWeakHausdorffPointSetLimitπToTop
    {J : Type u} [Category.{v} J] (F : J ⥤ compactlyGeneratedWeakHausdorffSpaceCat.{w})
    [HasLimit (compactlyGeneratedWeakHausdorffDiagramToTop F)] (j : J) :
    compactlyGeneratedWeakHausdorffPointSetLimitToTop F ⟶
      (compactlyGeneratedWeakHausdorffDiagramToTop F).obj j :=
  limit.π (compactlyGeneratedWeakHausdorffDiagramToTop F) j

/-- The weak-Hausdorff point-set limit object underlying Proposition 5.2.11 (3). -/
def weakHausdorffPointSetLimitObj
    {J : Type u} [Category.{v} J] (F : J ⥤ compactlyGeneratedWeakHausdorffSpaceCat.{w})
    [HasLimit (compactlyGeneratedWeakHausdorffDiagramToTop F)] :
    weakHausdorffSpaceCat.{w} :=
  let _ : ∀ j, WeaklyHausdorffSpace ((compactlyGeneratedWeakHausdorffDiagramToTop F).obj j) :=
    fun j ↦ (F.obj j).property.toWeaklyHausdorffSpace
  let _ : WeaklyHausdorffSpace (compactlyGeneratedWeakHausdorffPointSetLimitToTop F) :=
    instWeaklyHausdorffSpaceLimit (compactlyGeneratedWeakHausdorffDiagramToTop F)
  ⟨compactlyGeneratedWeakHausdorffPointSetLimitToTop F, inferInstance⟩

/-- The point-set limit projection to the `j`-th object is a morphism in `wU`. -/
def weakHausdorffPointSetLimitπ
    {J : Type u} [Category.{v} J] (F : J ⥤ compactlyGeneratedWeakHausdorffSpaceCat.{w})
    [HasLimit (compactlyGeneratedWeakHausdorffDiagramToTop F)] (j : J) :
    weakHausdorffPointSetLimitObj F ⟶
      (compactlyGeneratedWeakHausdorffDiagramToWeakHausdorff F).obj j :=
  ObjectProperty.homMk
    (compactlyGeneratedWeakHausdorffPointSetLimitπToTop F j)

/-- The point-set limit projections are natural in `wU`. -/
private theorem weakHausdorffPointSetLimitConeNaturality
    {J : Type u} [Category.{v} J] (F : J ⥤ compactlyGeneratedWeakHausdorffSpaceCat.{w})
    [HasLimit (compactlyGeneratedWeakHausdorffDiagramToTop F)]
    {j j' : J} (f : j ⟶ j') :
    ((Functor.const J).obj (weakHausdorffPointSetLimitObj F)).map f ≫
        weakHausdorffPointSetLimitπ F j' =
      weakHausdorffPointSetLimitπ F j ≫
        (compactlyGeneratedWeakHausdorffDiagramToWeakHausdorff F).map f := by
  -- Forget to `TopCat`, where this is the defining naturality of `limit.π`.
  apply ObjectProperty.hom_ext
  change compactlyGeneratedWeakHausdorffPointSetLimitπToTop F j' =
      compactlyGeneratedWeakHausdorffPointSetLimitπToTop F j ≫
        (compactlyGeneratedWeakHausdorffDiagramToTop F).map f
  exact (limit.w (compactlyGeneratedWeakHausdorffDiagramToTop F) f).symm

/-- The cone in `wU` given by the point-set limit of the underlying `TopCat` diagram. -/
def weakHausdorffPointSetLimitCone
    {J : Type u} [Category.{v} J] (F : J ⥤ compactlyGeneratedWeakHausdorffSpaceCat.{w})
    [HasLimit (compactlyGeneratedWeakHausdorffDiagramToTop F)] :
    Cone (compactlyGeneratedWeakHausdorffDiagramToWeakHausdorff F) where
  pt := weakHausdorffPointSetLimitObj F
  π :=
    { app := weakHausdorffPointSetLimitπ F
      naturality := fun _ _ f ↦ weakHausdorffPointSetLimitConeNaturality F f }

/-- Helper for Proposition 5.2.11: the weak-Hausdorff cone induced from the underlying `TopCat`
limit is already limiting in `wU`. -/
private def weakHausdorffPointSetLimitConeIsLimit
    {J : Type u} [Category.{v} J] (F : J ⥤ compactlyGeneratedWeakHausdorffSpaceCat.{w})
    [HasLimit (compactlyGeneratedWeakHausdorffDiagramToTop F)] :
    IsLimit (weakHausdorffPointSetLimitCone F) where
  lift s := by
    -- Repackage the underlying `TopCat` limit lift as a morphism in the full subcategory.
    exact
      ObjectProperty.homMk <|
        limit.lift (compactlyGeneratedWeakHausdorffDiagramToTop F)
          (weakHausdorffSpaceCatToTop.mapCone s)
  fac := by
    intro s j
    -- After forgetting to `TopCat`, this is the standard `limit.lift_π` computation.
    apply ObjectProperty.hom_ext
    simpa [weakHausdorffPointSetLimitπ] using
      (limit.lift_π (F := compactlyGeneratedWeakHausdorffDiagramToTop F)
        (c := weakHausdorffSpaceCatToTop.mapCone s) (j := j))
  uniq := by
    intro s m hm
    -- Uniqueness is inherited from the underlying `TopCat` limit by comparing all projections.
    apply ObjectProperty.hom_ext
    apply limit.hom_ext
    intro j
    have hmj :
        m.hom ≫ limit.π (compactlyGeneratedWeakHausdorffDiagramToTop F) j = (s.π.app j).hom := by
      simpa [weakHausdorffPointSetLimitπ] using congrArg (fun g ↦ g.hom) (hm j)
    have hliftj :
        limit.lift (compactlyGeneratedWeakHausdorffDiagramToTop F)
            (weakHausdorffSpaceCatToTop.mapCone s) ≫
              limit.π (compactlyGeneratedWeakHausdorffDiagramToTop F) j =
          (s.π.app j).hom := by
      simpa using
        (limit.lift_π (F := compactlyGeneratedWeakHausdorffDiagramToTop F)
          (c := weakHausdorffSpaceCatToTop.mapCone s) (j := j))
    exact hmj.trans hliftj.symm

private def compactlyGeneratedWeakHausdorffConeToTop
    {J : Type u} [Category.{v} J] (F : J ⥤ compactlyGeneratedWeakHausdorffSpaceCat.{w})
    (s : Cone F) :
    Cone (compactlyGeneratedWeakHausdorffDiagramToTop F) where
  pt := s.pt.obj
  π :=
    { app := fun j ↦ (s.π.app j).hom
      naturality := by
        intro j j' f
        change (s.π.app j').hom =
          (s.π.app j).hom ≫ (compactlyGeneratedWeakHausdorffDiagramToTop F).map f
        exact (congrArg (fun g ↦ g.hom) (s.w f)).symm }

/-- The `U`-object obtained by applying `weakHausdorffKification` to the weak-Hausdorff
point-set limit. -/
def weakHausdorffKifiedPointSetLimitObj
    {J : Type u} [Category.{v} J] (F : J ⥤ compactlyGeneratedWeakHausdorffSpaceCat.{w})
    [HasLimit (compactlyGeneratedWeakHausdorffDiagramToTop F)] :
    compactlyGeneratedWeakHausdorffSpaceCat :=
  weakHausdorffKification.obj (weakHausdorffPointSetLimitObj F)

/-- The canonical projection from the kified point-set limit to the `j`-th object of `F`. -/
def weakHausdorffKifiedPointSetLimitπ
    {J : Type u} [Category.{v} J] (F : J ⥤ compactlyGeneratedWeakHausdorffSpaceCat.{w})
    [HasLimit (compactlyGeneratedWeakHausdorffDiagramToTop F)] (j : J) :
    weakHausdorffKifiedPointSetLimitObj F ⟶ F.obj j :=
  -- Route correction: use the counit `j(kL) ⟶ L` and the point-set projection in `wU`,
  -- then repackage the underlying `TopCat` map as a morphism in `U`.
  ObjectProperty.homMk
    ((weakHausdorffKificationCounitApp (weakHausdorffPointSetLimitObj F) ≫
        weakHausdorffPointSetLimitπ F j).hom)

/-- The canonical projections from the kified point-set limit are natural in `j`. -/
private theorem weakHausdorffKifiedPointSetLimitConeNaturality
    {J : Type u} [Category.{v} J] (F : J ⥤ compactlyGeneratedWeakHausdorffSpaceCat.{w})
    [HasLimit (compactlyGeneratedWeakHausdorffDiagramToTop F)]
    {j j' : J} (f : j ⟶ j') :
    ((Functor.const J).obj (weakHausdorffKifiedPointSetLimitObj F)).map f ≫
        weakHausdorffKifiedPointSetLimitπ F j' =
      weakHausdorffKifiedPointSetLimitπ F j ≫ F.map f := by
  -- Forget to `wU`, where the claim is the point-set cone naturality composed with the counit.
  apply ObjectProperty.hom_ext
  exact congrArg
    (fun g ↦ g.hom)
    (congrArg
      (fun g ↦ weakHausdorffKificationCounitApp (weakHausdorffPointSetLimitObj F) ≫ g)
      (weakHausdorffPointSetLimitConeNaturality F f))

/-- The cone in `U` whose point is the kification of the underlying point-set limit. -/
def weakHausdorffKifiedPointSetLimitCone
    {J : Type u} [Category.{v} J] (F : J ⥤ compactlyGeneratedWeakHausdorffSpaceCat.{w})
    [HasLimit (compactlyGeneratedWeakHausdorffDiagramToTop F)] :
    Cone F where
  pt := weakHausdorffKifiedPointSetLimitObj F
  π :=
    { app := weakHausdorffKifiedPointSetLimitπ F
      naturality := fun _ _ f ↦ weakHausdorffKifiedPointSetLimitConeNaturality F f }

/-- Helper for Proposition 5.2.11: a kified point is determined by its underlying point. -/
private theorem kified_eq_mk_of {X : Type w} (x : Kified X) :
    Kified.mk x.of = x := by
  cases x
  rfl

/-- Helper for Proposition 5.2.11: the limiting map into the kified point-set limit is the
underlying `TopCat` limit lift followed by `Kified.mk`. -/
private def weakHausdorffKifiedPointSetLimitLift
    {J : Type u} [Category.{v} J] (F : J ⥤ compactlyGeneratedWeakHausdorffSpaceCat.{w})
    [HasLimit (compactlyGeneratedWeakHausdorffDiagramToTop F)] (s : Cone F) :
    s.pt ⟶ weakHausdorffKifiedPointSetLimitObj F :=
  let m :=
    limit.lift (compactlyGeneratedWeakHausdorffDiagramToTop F)
      (compactlyGeneratedWeakHausdorffConeToTop F s)
  let _ : UCompactlyGeneratedSpace s.pt.obj := s.pt.property.toUCompactlyGeneratedSpace
  ObjectProperty.homMk <|
    TopCat.ofHom
      ⟨fun x : s.pt.obj ↦ Kified.mk (m.hom x),
        continuousToKifiedOfContinuous m.hom.continuous⟩

/-- The kified point-set limit cone is limiting via the kification adjunction from
Proposition 5.2.9. -/
def weakHausdorffKifiedPointSetLimitIsLimit
    {J : Type u} [Category.{v} J] (F : J ⥤ compactlyGeneratedWeakHausdorffSpaceCat.{w})
    [HasLimit (compactlyGeneratedWeakHausdorffDiagramToTop F)] :
    IsLimit (weakHausdorffKifiedPointSetLimitCone F) where
  lift s := weakHausdorffKifiedPointSetLimitLift F s
  fac := by
    intro s j
    -- Compare the underlying pointwise functions and then apply `limit.lift_π`.
    apply ObjectProperty.hom_ext
    ext x
    have hπ :
        (limit.lift (compactlyGeneratedWeakHausdorffDiagramToTop F)
            (compactlyGeneratedWeakHausdorffConeToTop F s) ≫
              limit.π (compactlyGeneratedWeakHausdorffDiagramToTop F) j).hom x =
          ((compactlyGeneratedWeakHausdorffConeToTop F s).π.app j).hom x := by
      exact
        congrArg (fun g ↦ g.hom x)
          (limit.lift_π (F := compactlyGeneratedWeakHausdorffDiagramToTop F)
            (c := compactlyGeneratedWeakHausdorffConeToTop F s) (j := j))
    change
      (limit.lift (compactlyGeneratedWeakHausdorffDiagramToTop F)
          (compactlyGeneratedWeakHausdorffConeToTop F s) ≫
            limit.π (compactlyGeneratedWeakHausdorffDiagramToTop F) j).hom x =
        ((compactlyGeneratedWeakHausdorffConeToTop F s).π.app j).hom x
    simpa [weakHausdorffKifiedPointSetLimitLift, weakHausdorffKifiedPointSetLimitπ,
      compactlyGeneratedWeakHausdorffConeToTop] using hπ
  uniq := by
    intro s m hm
    have hmToPointSet :
        compactlyGeneratedWeakHausdorffToWeakHausdorff.map m ≫
            weakHausdorffKificationCounitApp (weakHausdorffPointSetLimitObj F) =
          (weakHausdorffPointSetLimitConeIsLimit F).lift
            (compactlyGeneratedWeakHausdorffToWeakHausdorff.mapCone s) := by
      -- Compose a candidate `m` with the counit to get a cone map into the weak-Hausdorff limit.
      apply (weakHausdorffPointSetLimitConeIsLimit F).hom_ext
      intro j
      apply ObjectProperty.hom_ext
      have hmj :
          m.hom ≫ ((weakHausdorffKifiedPointSetLimitCone F).π.app j).hom = (s.π.app j).hom := by
        exact congrArg (fun g ↦ g.hom) (hm j)
      have hliftj :
          ((weakHausdorffPointSetLimitConeIsLimit F).lift
              (compactlyGeneratedWeakHausdorffToWeakHausdorff.mapCone s)).hom ≫
              (weakHausdorffPointSetLimitπ F j).hom =
            ((compactlyGeneratedWeakHausdorffToWeakHausdorff.mapCone s).π.app j).hom := by
        simpa using
          congrArg (fun g ↦ g.hom)
            ((weakHausdorffPointSetLimitConeIsLimit F).fac
              (compactlyGeneratedWeakHausdorffToWeakHausdorff.mapCone s) j)
      have hmj' :
          (m.hom ≫ (weakHausdorffKificationCounitApp (weakHausdorffPointSetLimitObj F)).hom) ≫
              (weakHausdorffPointSetLimitπ F j).hom =
            (s.π.app j).hom := by
        simpa [weakHausdorffKifiedPointSetLimitπ, Category.assoc] using hmj
      exact hmj'.trans hliftj.symm
    apply ObjectProperty.hom_ext
    ext x
    have hPoint :
        (m.hom.hom x).of =
          (limit.lift (compactlyGeneratedWeakHausdorffDiagramToTop F)
            (compactlyGeneratedWeakHausdorffConeToTop F s)) x := by
      -- The weak-Hausdorff uniqueness result identifies the underlying point-set maps.
      simpa [weakHausdorffPointSetLimitConeIsLimit] using
        congrArg (fun f ↦ f x) (congrArg (fun g ↦ g.hom) hmToPointSet)
    rw [← kified_eq_mk_of (m.hom.hom x)]
    change Kified.mk ((m.hom.hom x).of) =
      Kified.mk
        ((limit.lift (compactlyGeneratedWeakHausdorffDiagramToTop F)
          (compactlyGeneratedWeakHausdorffConeToTop F s)) x)
    exact congrArg Kified.mk hPoint

/-- Helper for Proposition 5.2.11: for a diagram `F : J ⥤ U`, applying
`weakHausdorffKification` to the weak-Hausdorff point-set limit yields the canonical limit cone
of `F` in `U`. -/
def weakHausdorffKifiedPointSetLimit
    {J : Type u} [Category.{v} J] (F : J ⥤ compactlyGeneratedWeakHausdorffSpaceCat.{w})
    [HasLimit (compactlyGeneratedWeakHausdorffDiagramToTop F)] :
    LimitCone F where
  cone := weakHausdorffKifiedPointSetLimitCone F
  isLimit := weakHausdorffKifiedPointSetLimitIsLimit F

/-- If the underlying point-set diagram of `F : J ⥤ U` has a limit in `TopCat`, then `F` has a
limit in `U`, realized by the kification of that point-set limit. -/
instance instHasLimitCompactlyGeneratedWeakHausdorffSpaceCatOfHasLimitToTop
    {J : Type u} [Category.{v} J] (F : J ⥤ compactlyGeneratedWeakHausdorffSpaceCat.{w})
    [HasLimit (compactlyGeneratedWeakHausdorffDiagramToTop F)] :
    HasLimit F :=
  HasLimit.mk (weakHausdorffKifiedPointSetLimit F)

end
