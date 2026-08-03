module

public import Topology_Munkres_2000.Book.Exercise_41_6.BoxTopology
public import Topology_Munkres_2000.Book.Exercise_20_4.RealSequences
public import Topology_Munkres_2000.Book.Exercise_44_2
public import Topology_Munkres_2000.Book.Theorem_20_4
public import Topology_Munkres_2000.Book.Theorem_19_1
public import Topology_Munkres_2000.Book.Proposition_19_3
public import Topology_Munkres_2000.Book.Exercise_44_3.UniformTopology
public import Mathlib.Topology.Compactness.SigmaCompact

public section

/-- Helper for Exercise 44.3: a countable family of compact subsets of real sequence
space misses a single diagonal sequence. -/
lemma existsSequence_avoids_compactFamily (K : ℕ → Set (ℕ → ℝ))
    (hK : ∀ n, IsCompact (K n)) :
    ∃ x : ℕ → ℝ, ∀ n, x ∉ K n := by
  classical
  -- Compactness bounds the `n`th coordinate on the `n`th compact set.
  have hBound (n : ℕ) : ∃ b : ℝ, ∀ y ∈ K n, y n ≤ b := by
    obtain ⟨b, hb⟩ := (hK n).bddAbove_image (continuous_apply n).continuousOn
    refine ⟨b, ?_⟩
    intro y hy
    exact hb (Set.mem_image_of_mem (fun z : ℕ → ℝ ↦ z n) hy)
  choose b hb using hBound
  refine ⟨fun n ↦ b n + 1, ?_⟩
  intro n hmem
  -- The diagonal coordinate exceeds its chosen bound.
  have hle := hb n _ hmem
  linarith

/-- Exercise 44.3: The countable product of real lines is not sigma compact. -/
theorem realSequenceProduct_notSigmaCompact :
    ¬ SigmaCompactSpace (ℕ → ℝ) := by
  -- A compact covering is contradicted by the diagonal sequence.
  intro hSigma
  letI : SigmaCompactSpace (ℕ → ℝ) := hSigma
  obtain ⟨K, hK, hcover⟩ :=
    (@SigmaCompactSpace.exists_compact_covering (ℕ → ℝ) _ hSigma)
  obtain ⟨x, hx⟩ := existsSequence_avoids_compactFamily K hK
  have hxcover : x ∈ ⋃ n, K n := by
    rw [hcover]
    exact Set.mem_univ x
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hxcover
  exact hx n hxn

/-- Helper for Exercise 44.3 (1): With the product topology, no continuous map from `ℝ` onto
`ℕ → ℝ` is surjective. -/
theorem notExistsContinuousSurjectiveRealSequenceProduct :
    ¬ ∃ f : C(ℝ, ℕ → ℝ), Function.Surjective f := by
  -- A continuous image of the sigma-compact real line is sigma compact.
  rintro ⟨f, hf⟩
  have hrange : Set.range f = Set.univ := Set.range_eq_univ.mpr hf
  have huniv : IsSigmaCompact (Set.univ : Set (ℕ → ℝ)) := by
    rw [← hrange]
    exact isSigmaCompact_range f.continuous
  exact realSequenceProduct_notSigmaCompact (isSigmaCompact_univ_iff.mp huniv)

/-- Helper for Exercise 44.3: extend finitely many real coordinates by zero. -/
def finiteCoordinateExtensionSequence (n : ℕ) (y : Fin n → ℝ) : ℕ → ℝ :=
  fun i ↦ if h : i < n then y ⟨i, h⟩ else 0

/-- Helper for Exercise 44.3: zero extension from `Fin n` has finite support. -/
lemma finiteCoordinateExtension_hasFiniteSupport (n : ℕ) (y : Fin n → ℝ) :
    (finiteCoordinateExtensionSequence n y).HasFiniteSupport := by
  -- Every nonzero coordinate lies in the finite initial segment.
  refine Set.Finite.subset (Finset.finite_toSet (Finset.range n)) ?_
  intro i hi
  simp only [Function.mem_support, finiteCoordinateExtensionSequence] at hi ⊢
  by_contra hin
  have hnot : ¬ i < n := by
    intro hlt
    exact hin (Finset.mem_range.mpr hlt)
  simp only [hnot, ↓reduceDIte, ne_eq, not_true_eq_false] at hi

/-- Helper for Exercise 44.3: zero extension defines an eventually-zero sequence. -/
lemma finiteCoordinateExtension_mem (n : ℕ) (y : Fin n → ℝ) :
    finiteCoordinateExtensionSequence n y ∈ eventuallyZeroRealSequences := by
  -- Membership is exactly finite support.
  exact mem_eventuallyZeroRealSequences.mpr
    (finiteCoordinateExtension_hasFiniteSupport n y)

/-- Helper for Exercise 44.3: package finite-coordinate zero extension in the
eventually-zero box topology. -/
def finiteCoordinateExtension (n : ℕ) (y : Fin n → ℝ) : EventuallyZeroRealBox :=
  WithTopology.toTopology eventuallyZeroRealBoxTopology
    ⟨finiteCoordinateExtensionSequence n y, finiteCoordinateExtension_mem n y⟩

/-- Helper for Exercise 44.3: finite-coordinate zero extension is continuous into
the ambient real box topology. -/
lemma continuous_finiteCoordinateExtensionSequence (n : ℕ) :
    @Continuous (Fin n → ℝ) (ℕ → ℝ) Pi.topologicalSpace
      (Pi.boxTopologicalSpace fun _ : ℕ ↦ ℝ) (finiteCoordinateExtensionSequence n) := by
  -- Compute preimages of basic coordinate boxes.
  refine (@TopologicalSpace.IsTopologicalBasis.continuous_iff
    (Fin n → ℝ) (ℕ → ℝ) Pi.topologicalSpace
    (Pi.boxTopologicalSpace fun _ : ℕ ↦ ℝ)
    (Pi.boxBasis fun _ : ℕ ↦ ℝ) Pi.isTopologicalBasis_boxBasis
    (finiteCoordinateExtensionSequence n)).mpr ?_
  intro s hs
  obtain ⟨U, hU, rfl⟩ := (Pi.mem_boxBasis s).mp hs
  by_cases houtside : ∀ i, n ≤ i → 0 ∈ U i
  · have hpreimage :
        finiteCoordinateExtensionSequence n ⁻¹' Set.pi Set.univ U =
          ⋂ j : Fin n, (fun y : Fin n → ℝ ↦ y j) ⁻¹' U j := by
      ext y
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
        Set.mem_iInter]
      constructor
      · intro hy j
        simpa only [finiteCoordinateExtensionSequence, j.isLt, ↓reduceDIte] using hy j
      · intro hy i
        by_cases hi : i < n
        · simpa only [finiteCoordinateExtensionSequence, hi, ↓reduceDIte] using hy ⟨i, hi⟩
        · simp only [finiteCoordinateExtensionSequence, hi, ↓reduceDIte]
          exact houtside i (Nat.le_of_not_gt hi)
    rw [hpreimage]
    exact isOpen_iInter_of_finite fun j ↦ (hU j).preimage (continuous_apply j)
  · push Not at houtside
    obtain ⟨i, hi, hzero⟩ := houtside
    have hpreimage : finiteCoordinateExtensionSequence n ⁻¹' Set.pi Set.univ U = ∅ := by
      ext y
      constructor
      · intro hy
        have hnot : ¬ i < n := Nat.not_lt.mpr hi
        have hyi := hy i (Set.mem_univ i)
        simp only [finiteCoordinateExtensionSequence, hnot, ↓reduceDIte] at hyi
        exact (hzero hyi).elim
      · intro hy
        exact hy.elim
    rw [hpreimage]
    exact isOpen_empty

/-- Helper for Exercise 44.3: the packaged finite-coordinate extension is continuous. -/
lemma continuous_finiteCoordinateExtension (n : ℕ) :
    Continuous (finiteCoordinateExtension n) := by
  -- First map into the induced subtype topology, then apply the topology wrapper.
  exact @Continuous.comp
    (Fin n → ℝ)
    eventuallyZeroRealSequences
    EventuallyZeroRealBox
    Pi.topologicalSpace
    eventuallyZeroRealBoxTopology
    _ _ _ continuous_coinduced_rng
    (by
      rw [eventuallyZeroRealBoxTopology_def, continuous_induced_rng]
      simpa only [Function.comp_def, finiteCoordinateExtension] using
        continuous_finiteCoordinateExtensionSequence n)

/-- Helper for Exercise 44.3: zero extension preserves coordinates below its cutoff. -/
@[simp]
lemma finiteCoordinateExtension_apply_lt {n i : ℕ} (y : Fin n → ℝ) (hi : i < n) :
    (finiteCoordinateExtension n y).ofTopology.1 i = y ⟨i, hi⟩ := by
  -- Unfold the zero-extension formula at an in-range coordinate.
  simp [finiteCoordinateExtension, finiteCoordinateExtensionSequence, hi]

/-- Helper for Exercise 44.3: zero extension vanishes at coordinates beyond its cutoff. -/
@[simp]
lemma finiteCoordinateExtension_apply_ge {n i : ℕ} (y : Fin n → ℝ) (hi : n ≤ i) :
    (finiteCoordinateExtension n y).ofTopology.1 i = 0 := by
  -- Unfold the zero-extension formula at an out-of-range coordinate.
  simp [finiteCoordinateExtension, finiteCoordinateExtensionSequence, Nat.not_lt.mpr hi]


/-- Helper for Exercise 44.3: the zero real sequence is eventually zero. -/
lemma zeroRealSequence_mem_eventuallyZero :
    (fun _ : ℕ ↦ (0 : ℝ)) ∈ eventuallyZeroRealSequences := by
  -- The zero function has empty, hence finite, support.
  exact mem_eventuallyZeroRealSequences.mpr Function.hasFiniteSupport_zero

/-- Helper for Exercise 44.3: the zero point of the eventually-zero sequence subtype. -/
def eventuallyZeroRealZero : eventuallyZeroRealSequences :=
  ⟨fun _ ↦ 0, zeroRealSequence_mem_eventuallyZero⟩

/-- Helper for Exercise 44.3: zero extension sends the zero vector to the zero sequence. -/
lemma finiteCoordinateExtension_zero (n : ℕ) :
    finiteCoordinateExtension n (0 : Fin n → ℝ) =
      WithTopology.toTopology eventuallyZeroRealBoxTopology
        eventuallyZeroRealZero := by
  -- Equality follows coordinatewise on the underlying sequences.
  apply WithTopology.ext
  apply Subtype.ext
  funext i
  by_cases hi : i < n
  · simp [finiteCoordinateExtension, finiteCoordinateExtensionSequence,
      eventuallyZeroRealZero, hi]
  · simp [finiteCoordinateExtension, finiteCoordinateExtensionSequence,
      eventuallyZeroRealZero, hi]

/-- Helper for Exercise 44.3: a based loop covers every bounded sequence supported
below a prescribed coordinate cutoff. -/
lemma existsEventuallyZeroBoxLoop_coveringBounds (n m : ℕ) :
    ∃ γ : Path
        (WithTopology.toTopology eventuallyZeroRealBoxTopology
          eventuallyZeroRealZero)
        (WithTopology.toTopology eventuallyZeroRealBoxTopology
          eventuallyZeroRealZero),
      ∀ x : EventuallyZeroRealBox,
        (∀ i, n ≤ i → x.ofTopology.1 i = 0) →
        (∀ i, |x.ofTopology.1 i| ≤ m) → x ∈ Set.range γ := by
  -- Map a finite-dimensional loop through the zero-extension inclusion.
  obtain ⟨g, hg⟩ := existsContinuousSurjectiveUnitCube n
  obtain ⟨γ, hγ⟩ := existsBasedLoop_range_contains_coordinateBox g hg m
  let coordinates : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ) := fun y i ↦ y i
  have coordinates_continuous : Continuous coordinates := by
    fun_prop
  let extension : EuclideanSpace ℝ (Fin n) → EventuallyZeroRealBox :=
    finiteCoordinateExtension n ∘ coordinates
  have extension_continuous : Continuous extension :=
    (continuous_finiteCoordinateExtension n).comp coordinates_continuous
  have extension_zero : extension 0 =
      WithTopology.toTopology eventuallyZeroRealBoxTopology eventuallyZeroRealZero := by
    apply WithTopology.ext
    apply Subtype.ext
    funext i
    simp [extension, coordinates, finiteCoordinateExtension,
      finiteCoordinateExtensionSequence, eventuallyZeroRealZero]
  let mapped := γ.map extension_continuous
  let loop := mapped.cast extension_zero.symm extension_zero.symm
  refine ⟨loop, ?_⟩
  intro x hsupp hbound
  let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i ↦ x.ofTopology.1 i)
  have hybound : ∀ i, |y i| ≤ (m : ℝ) + 1 := by
    intro i
    have hm : |x.ofTopology.1 i| ≤ (m : ℝ) := by exact_mod_cast hbound i
    simpa [y, PiLp.toLp_apply] using hm.trans (by linarith : (m : ℝ) ≤ (m : ℝ) + 1)
  obtain ⟨t, ht⟩ := hγ y hybound
  refine ⟨t, ?_⟩
  have hloop : loop t = extension y := by
    -- The cast changes only the endpoints, while the mapped path follows the extension.
    change extension (γ t) = extension y
    exact congrArg extension ht
  rw [hloop]
  apply WithTopology.ext
  apply Subtype.ext
  funext i
  unfold extension
  simp only [Function.comp_apply]
  by_cases hi : i < n
  · rw [finiteCoordinateExtension_apply_lt (coordinates y) hi]
  · rw [finiteCoordinateExtension_apply_ge (coordinates y) (Nat.le_of_not_gt hi)]
    exact (hsupp i (Nat.le_of_not_gt hi)).symm

/-- Helper for Exercise 44.3: the box-topologized eventually-zero sequences are a
continuous image of the real line. -/
lemma existsContinuousSurjectiveEventuallyZeroRealBoxAux :
    ∃ f : C(ℝ, EventuallyZeroRealBox), Function.Surjective f := by
  classical
  -- Pair support and radius bounds into one integer-indexed loop family.
  choose γ hγ using fun k : ℤ =>
    existsEventuallyZeroBoxLoop_coveringBounds (Nat.unpair k.natAbs).1
      (Nat.unpair k.natAbs).2
  obtain ⟨F, hF⟩ := existsContinuousMap_range_contains_integerLoops γ
  refine ⟨F, ?_⟩
  intro x
  have hfinite : x.ofTopology.1.support.Finite :=
    mem_eventuallyZeroRealSequences.mp x.ofTopology.2
  obtain ⟨M, hM⟩ := hfinite.exists_le
  let n := M + 1
  let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i ↦ x.ofTopology.1 i)
  obtain ⟨m, hm⟩ := exists_nat_coordinatewise_abs_le y
  let k : ℤ := Nat.pair n m
  have hpair : Nat.unpair k.natAbs = (n, m) := by
    simp [k]
  have hsupp : ∀ i, n ≤ i → x.ofTopology.1 i = 0 := by
    intro i hi
    by_contra hxi
    have himem : i ∈ x.ofTopology.1.support := hxi
    have hiM := hM i himem
    omega
  have hbound : ∀ i, |x.ofTopology.1 i| ≤ m := by
    intro i
    by_cases hi : i < n
    · have hmi := hm ⟨i, hi⟩
      simpa [y, PiLp.toLp_apply] using hmi
    · rw [hsupp i (Nat.le_of_not_gt hi), abs_zero]
      exact Nat.cast_nonneg m
  have hxloop : x ∈ Set.range (γ k) := by
    have hk := hγ k x
    rw [hpair] at hk
    exact hk hsupp hbound
  exact hF k hxloop

/-- Helper for Exercise 44.3: forgetting the box topology on eventually-zero
sequences is continuous into the product-subspace topology. -/
lemma continuous_eventuallyZeroBox_to_product :
    Continuous (fun x : EventuallyZeroRealBox ↦ x.ofTopology) := by
  -- The box topology is finer than the product topology before inducing on the subtype.
  rw [continuous_iff_le_induced, WithTopology.topology_eq_induced]
  exact induced_mono (induced_mono (Pi.box_le_product (X := fun _ : ℕ ↦ ℝ)))

/-- Helper for Exercise 44.3: an identity map from a finer named topology to a
coarser named topology is continuous. -/
lemma continuous_withTopology_mono {X : Type*} (t₁ t₂ : TopologicalSpace X)
    (h : t₁ ≤ t₂) :
    Continuous (fun x : WithTopology X t₁ ↦ WithTopology.toTopology t₂ x.ofTopology) := by
  -- Factor the identity through the two wrapper equivalences.
  have hforget : @Continuous (WithTopology X t₁) X _ t₂ WithTopology.ofTopology := by
    rw [continuous_iff_le_induced, WithTopology.topology_eq_induced]
    exact induced_mono h
  exact continuous_coinduced_rng.comp hforget

/-- Helper for Exercise 44.3: forgetting the box topology on eventually-zero
sequences is continuous into the induced uniform topology. -/
lemma continuous_eventuallyZeroBox_to_uniform :
    Continuous (fun x : EventuallyZeroRealBox ↦
      WithTopology.toTopology eventuallyZeroRealUniformTopology x.ofTopology) := by
  -- The induced box topology is finer than the induced uniform topology.
  exact continuous_withTopology_mono _ _
    (induced_mono (UniformMetric.box_le_topology ℕ))

/-- Helper for Exercise 44.3: forgetting the uniform topology on eventually-zero
sequences is continuous into the product-subspace topology. -/
lemma continuous_eventuallyZeroUniform_to_product :
    Continuous (fun x : EventuallyZeroRealUniform ↦ x.ofTopology) := by
  -- The uniform topology is finer than the product topology before inducing on the subtype.
  rw [continuous_iff_le_induced, WithTopology.topology_eq_induced]
  exact induced_mono (induced_mono (UniformMetric.topology_le_product ℕ))

/-- Helper for Exercise 44.3: forgetting the uniform topology on all real sequences
is continuous into the product topology. -/
lemma continuous_uniformRealSequence_to_product :
    Continuous (fun x : UniformRealSequence ↦ x.ofTopology) := by
  -- This is the defining comparison between uniform and product topologies.
  rw [continuous_iff_le_induced, WithTopology.topology_eq_induced]
  exact induced_mono (UniformMetric.topology_le_product ℕ)

/-- Helper for Exercise 44.3: forgetting the box topology on all real sequences is
continuous into the product topology. -/
lemma continuous_boxRealSequence_to_product :
    Continuous (fun x : BoxRealSequence ↦ x.ofTopology) := by
  -- This is the defining comparison between box and product topologies.
  rw [continuous_iff_le_induced, WithTopology.topology_eq_induced]
  exact induced_mono (Pi.box_le_product (X := fun _ : ℕ ↦ ℝ))

/-- Exercise 44.3 (2): With the product-subspace topology, there is a continuous
surjection from `ℝ` onto the eventually-zero real sequences. -/
theorem existsContinuousSurjectiveEventuallyZeroRealProduct :
    ∃ f : C(ℝ, eventuallyZeroRealSequences), Function.Surjective f := by
  -- Compose the box-continuous surjection with the topology-forgetting identity.
  obtain ⟨f, hf⟩ := existsContinuousSurjectiveEventuallyZeroRealBoxAux
  let g : C(ℝ, eventuallyZeroRealSequences) :=
    ⟨fun t ↦ f t |>.ofTopology,
      continuous_eventuallyZeroBox_to_product.comp f.continuous⟩
  refine ⟨g, ?_⟩
  intro x
  obtain ⟨t, ht⟩ := hf (WithTopology.toTopology eventuallyZeroRealBoxTopology x)
  refine ⟨t, ?_⟩
  exact congrArg WithTopology.ofTopology ht

/-- Exercise 44.3 (3): With the uniform topology, no continuous map from `ℝ` onto
`ℕ → ℝ` is surjective. -/
theorem notExistsContinuousSurjectiveUniformRealSequence :
    ¬ ∃ f : C(ℝ, UniformRealSequence), Function.Surjective f := by
  -- A uniform-topology surjection would remain surjective after forgetting to product topology.
  rintro ⟨f, hf⟩
  let g : C(ℝ, ℕ → ℝ) :=
    ⟨fun t ↦ (f t).ofTopology,
      continuous_uniformRealSequence_to_product.comp f.continuous⟩
  apply notExistsContinuousSurjectiveRealSequenceProduct
  refine ⟨g, ?_⟩
  intro x
  obtain ⟨t, ht⟩ := hf (WithTopology.toTopology (UniformMetric.topology ℕ) x)
  refine ⟨t, ?_⟩
  exact congrArg WithTopology.ofTopology ht

/-- Exercise 44.3 (4): With the induced uniform topology, there is a continuous
surjection from `ℝ` onto the eventually-zero real sequences. -/
theorem existsContinuousSurjectiveEventuallyZeroRealUniform :
    ∃ f : C(ℝ, EventuallyZeroRealUniform), Function.Surjective f := by
  -- Compose the box-continuous surjection with the identity into the uniform topology.
  obtain ⟨f, hf⟩ := existsContinuousSurjectiveEventuallyZeroRealBoxAux
  let g : C(ℝ, EventuallyZeroRealUniform) :=
    ⟨fun t ↦ WithTopology.toTopology eventuallyZeroRealUniformTopology (f t).ofTopology,
      continuous_eventuallyZeroBox_to_uniform.comp f.continuous⟩
  refine ⟨g, ?_⟩
  intro x
  obtain ⟨t, ht⟩ := hf
    (WithTopology.toTopology eventuallyZeroRealBoxTopology x.ofTopology)
  refine ⟨t, ?_⟩
  apply WithTopology.ext
  simpa [g] using congrArg WithTopology.ofTopology ht

/-- Exercise 44.3 (5): With the box topology, no continuous map from `ℝ` onto
`ℕ → ℝ` is surjective. -/
theorem notExistsContinuousSurjectiveBoxRealSequence :
    ¬ ∃ f : C(ℝ, BoxRealSequence), Function.Surjective f := by
  -- A box-topology surjection would remain surjective after forgetting to product topology.
  rintro ⟨f, hf⟩
  let g : C(ℝ, ℕ → ℝ) :=
    ⟨fun t ↦ (f t).ofTopology,
      continuous_boxRealSequence_to_product.comp f.continuous⟩
  apply notExistsContinuousSurjectiveRealSequenceProduct
  refine ⟨g, ?_⟩
  intro x
  obtain ⟨t, ht⟩ := hf
    (WithTopology.toTopology (Pi.boxTopologicalSpace fun _ : ℕ ↦ ℝ) x)
  refine ⟨t, ?_⟩
  exact congrArg WithTopology.ofTopology ht

/-- Exercise 44.3 (6): With the induced box topology, there is a continuous
surjection from `ℝ` onto the eventually-zero real sequences. -/
theorem existsContinuousSurjectiveEventuallyZeroRealBox :
    ∃ f : C(ℝ, EventuallyZeroRealBox), Function.Surjective f := by
  -- The shared box-space construction is exactly this target.
  exact existsContinuousSurjectiveEventuallyZeroRealBoxAux
