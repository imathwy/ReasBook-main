module

public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.ContinuousMap.Interval
public import Mathlib.Topology.GDelta.MetrizableSpace

public section

open Filter Set
open scoped Topology

universe u

/-- Helper for Exercise 38.9: a sequence converging outside its range has an injective
subsequence, selected along an injective map of indices, with the same limit. -/
private lemma existsInjectiveSubsequenceTendsto {Y : Type*} [TopologicalSpace Y] [T1Space Y]
    {u : ℕ → Y} {y : Y} (hu : Tendsto u atTop (𝓝 y)) (hy : y ∉ Set.range u) :
    ∃ φ : ℕ → ℕ, Function.Injective φ ∧ Function.Injective (u ∘ φ) ∧
      Tendsto (u ∘ φ) atTop (𝓝 y) := by
  classical
  -- The range must be infinite, since a finite range is closed and would contain its limit.
  have hinfinite : (Set.range u).Infinite := by
    intro hfinite
    have hyRange : y ∈ Set.range u :=
      hfinite.isClosed.mem_of_tendsto hu (Eventually.of_forall fun n ↦ Set.mem_range_self n)
    exact hy hyRange
  let values : ℕ ↪ Set.range u := hinfinite.natEmbedding _
  choose φ hφ using fun n ↦ (values n).property
  -- Distinct enumerated range values force both the chosen indices and the subsequence values
  -- to be distinct; injective indices also preserve convergence to the original limit.
  have hφInjective : Function.Injective φ := by
    intro m n hmn
    apply values.injective
    apply Subtype.ext
    rw [← hφ m, ← hφ n, hmn]
  have hsubsequenceInjective : Function.Injective (u ∘ φ) := by
    intro m n hmn
    apply values.injective
    apply Subtype.ext
    simpa only [Function.comp_apply, hφ] using hmn
  exact ⟨φ, hφInjective, hsubsequenceInjective, hu.comp hφInjective.nat_tendsto_atTop⟩

/-- Helper for Exercise 38.9: if a sequence converges outside the range of an embedding into a
Hausdorff space, then the sequence's range in the source is closed. -/
private lemma isClosed_range_of_tendsto_embedding {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {e : X → Y} (he : Topology.IsEmbedding e) {s : ℕ → X}
    {y : Y} (hy : y ∉ Set.range e) (hs : Tendsto (e ∘ s) atTop (𝓝 y)) :
    IsClosed (Set.range s) := by
  -- The convergent sequence together with its limit is compact, hence closed in the codomain.
  have hclosed : IsClosed (insert y (Set.range (e ∘ s))) := hs.isCompact_insert_range.isClosed
  have hpreimage : e ⁻¹' (insert y (Set.range (e ∘ s))) = Set.range s := by
    ext x
    constructor
    · intro hx
      rcases hx with hxy | hx
      · exact (hy ⟨x, hxy⟩).elim
      · obtain ⟨n, hn⟩ := hx
        exact ⟨n, he.injective hn⟩
    · rintro ⟨n, rfl⟩
      exact Or.inr ⟨n, rfl⟩
  -- Pulling this closed compact set back along the embedding gives exactly the source range.
  rw [← hpreimage]
  exact hclosed.preimage he.continuous

/-- Helper for Exercise 38.9: disjoint closed sets in a normal space are separated by a
continuous `unitInterval`-valued map taking the endpoint values `0` and `1`. -/
private lemma existsUnitIntervalSeparator {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
    ∃ f : C(X, unitInterval), Set.EqOn f 0 A ∧ Set.EqOn f 1 B := by
  obtain ⟨f, hfA, hfB, -⟩ := exists_continuous_zero_one_of_isClosed hA hB hAB
  -- Projecting Urysohn's real-valued separator to `[0, 1]` preserves both endpoint values.
  refine ⟨ContinuousMap.projIccCM.comp f, ?_, ?_⟩
  · intro x hx
    have hfx : f x = 0 := by
      simpa only [Pi.zero_apply] using hfA hx
    rw [ContinuousMap.comp_apply, hfx]
    apply Subtype.ext
    unfold ContinuousMap.projIccCM
    simpa only [ContinuousMap.coe_mk, Pi.zero_apply, Set.Icc.coe_zero] using congrArg Subtype.val
      (Set.projIcc_left (a := (0 : ℝ)) (b := 1) zero_le_one)
  · intro x hx
    have hfx : f x = 1 := by
      simpa only [Pi.one_apply] using hfB hx
    rw [ContinuousMap.comp_apply, hfx]
    apply Subtype.ext
    unfold ContinuousMap.projIccCM
    simpa only [ContinuousMap.coe_mk, Pi.one_apply, Set.Icc.coe_one] using congrArg Subtype.val
      (Set.projIcc_right (a := (0 : ℝ)) (b := 1) zero_le_one)

/-- Helper for Exercise 38.9: an injective sequence in `X` cannot converge under
`stoneCechUnit` to a point outside the canonical range. -/
private lemma not_tendsto_stoneCechUnit_of_injective {X : Type u} [TopologicalSpace X]
    [T4Space X] {y : StoneCech X} (hy : y ∉ Set.range (stoneCechUnit : X → StoneCech X))
    {s : ℕ → X} (hs : Function.Injective s) :
    ¬ Tendsto (stoneCechUnit ∘ s) atTop (𝓝 y) := by
  intro htendsto
  let evenSequence : ℕ → X := fun n ↦ s (2 * n)
  let oddSequence : ℕ → X := fun n ↦ s (2 * n + 1)
  -- Both parity subsequences still converge to `y` after applying the canonical embedding.
  have hevenIndex : Function.Injective (fun n : ℕ ↦ 2 * n) := by
    intro m n hmn
    dsimp only at hmn
    omega
  have hoddIndex : Function.Injective (fun n : ℕ ↦ 2 * n + 1) := by
    intro m n hmn
    dsimp only at hmn
    omega
  have hevenTendsto : Tendsto (stoneCechUnit ∘ evenSequence) atTop (𝓝 y) := by
    simpa only [Function.comp_def, evenSequence] using
      htendsto.comp hevenIndex.nat_tendsto_atTop
  have hoddTendsto : Tendsto (stoneCechUnit ∘ oddSequence) atTop (𝓝 y) := by
    simpa only [Function.comp_def, oddSequence] using
      htendsto.comp hoddIndex.nat_tendsto_atTop
  -- Their ranges are closed in `X`, and injectivity of `s` makes the two ranges disjoint.
  have hevenClosed : IsClosed (Set.range evenSequence) :=
    isClosed_range_of_tendsto_embedding isEmbedding_stoneCechUnit hy hevenTendsto
  have hoddClosed : IsClosed (Set.range oddSequence) :=
    isClosed_range_of_tendsto_embedding isEmbedding_stoneCechUnit hy hoddTendsto
  have hdisjoint : Disjoint (Set.range evenSequence) (Set.range oddSequence) := by
    rw [Set.disjoint_left]
    rintro x ⟨m, hm⟩ ⟨n, hn⟩
    have hindices : 2 * m = 2 * n + 1 := hs (hm.trans hn.symm)
    omega
  obtain ⟨f, hfEven, hfOdd⟩ :=
    existsUnitIntervalSeparator hevenClosed hoddClosed hdisjoint
  -- Extend the separator to `StoneCech X`; continuity gives a common limit for both parity
  -- subsequences, while the extension equation makes those limits `0` and `1` respectively.
  have hevenValue :
      stoneCechExtend f.continuous ∘ (stoneCechUnit ∘ evenSequence) =
        fun _ : ℕ ↦ (0 : unitInterval) := by
    funext n
    rw [Function.comp_apply, Function.comp_apply, stoneCechExtend_stoneCechUnit]
    exact hfEven ⟨n, rfl⟩
  have hoddValue :
      stoneCechExtend f.continuous ∘ (stoneCechUnit ∘ oddSequence) =
        fun _ : ℕ ↦ (1 : unitInterval) := by
    funext n
    rw [Function.comp_apply, Function.comp_apply, stoneCechExtend_stoneCechUnit]
    exact hfOdd ⟨n, rfl⟩
  have hevenAtExtension : Tendsto
      (stoneCechExtend f.continuous ∘ (stoneCechUnit ∘ evenSequence)) atTop
      (𝓝 (stoneCechExtend f.continuous y)) :=
    (continuous_stoneCechExtend f.continuous).tendsto y |>.comp hevenTendsto
  have hoddAtExtension : Tendsto
      (stoneCechExtend f.continuous ∘ (stoneCechUnit ∘ oddSequence)) atTop
      (𝓝 (stoneCechExtend f.continuous y)) :=
    (continuous_stoneCechExtend f.continuous).tendsto y |>.comp hoddTendsto
  have hevenAtZero : Tendsto
      (stoneCechExtend f.continuous ∘ (stoneCechUnit ∘ evenSequence)) atTop (𝓝 0) := by
    rw [hevenValue]
    exact tendsto_const_nhds
  have hoddAtOne : Tendsto
      (stoneCechExtend f.continuous ∘ (stoneCechUnit ∘ oddSequence)) atTop (𝓝 1) := by
    rw [hoddValue]
    exact tendsto_const_nhds
  have hextensionZero : stoneCechExtend f.continuous y = 0 :=
    tendsto_nhds_unique hevenAtExtension hevenAtZero
  have hextensionOne : stoneCechExtend f.continuous y = 1 :=
    tendsto_nhds_unique hoddAtExtension hoddAtOne
  exact zero_ne_one (hextensionZero.symm.trans hextensionOne)

/-- Helper for Exercise 38.9: a noncompact T₃.₅ space has a point of `StoneCech X` outside
the range of `stoneCechUnit`. -/
private lemma exists_stoneCech_not_mem_range {X : Type u} [TopologicalSpace X]
    [T35Space X] [NoncompactSpace X] :
    ∃ y : StoneCech X, y ∉ Set.range (stoneCechUnit : X → StoneCech X) := by
  classical
  -- Surjectivity of the embedding would transfer compactness of `StoneCech X` back to `X`.
  by_contra h
  push Not at h
  have hsurjective : Function.Surjective (stoneCechUnit : X → StoneCech X) := by
    intro y
    exact h y
  have hcompactImage : IsCompact
      ((stoneCechUnit : X → StoneCech X) '' (Set.univ : Set X)) := by
    rw [Set.image_univ, hsurjective.range_eq]
    exact isCompact_univ
  have hcompact : IsCompact (Set.univ : Set X) :=
    isEmbedding_stoneCechUnit.isCompact_iff.mpr hcompactImage
  exact noncompact_univ X hcompact

/-- Exercise 38.9 (1): If `y` lies outside the canonical copy
`Set.range (stoneCechUnit : X → StoneCech X)` of a normal space `X` in `StoneCech X`,
then no sequence of points of `X` converges to `y` after applying `stoneCechUnit`. -/
theorem not_tendsto_stoneCechUnit_of_not_mem_range {X : Type u} [TopologicalSpace X]
    [T4Space X] {y : StoneCech X}
    (hy : y ∉ Set.range (stoneCechUnit : X → StoneCech X)) (sequence : ℕ → X) :
    ¬ Tendsto (stoneCechUnit ∘ sequence) atTop (𝓝 y) := by
  intro htendsto
  -- Extract an injective subsequence in the compactification, then transfer injectivity back to
  -- `X` and apply the parity-separation contradiction.
  have hySequence : y ∉ Set.range (stoneCechUnit ∘ sequence) := by
    rintro ⟨n, hn⟩
    exact hy ⟨sequence n, hn⟩
  obtain ⟨φ, -, hsubsequenceInjective, hsubsequenceTendsto⟩ :=
    existsInjectiveSubsequenceTendsto htendsto hySequence
  have hsourceInjective : Function.Injective (sequence ∘ φ) := by
    intro m n hmn
    apply hsubsequenceInjective
    exact congrArg stoneCechUnit hmn
  apply not_tendsto_stoneCechUnit_of_injective hy hsourceInjective
  simpa only [Function.comp_def] using hsubsequenceTendsto

/-- Exercise 38.9 (2): If `X` is completely regular in Munkres's sense and noncompact,
then its Stone–Čech compactification `StoneCech X` is not metrizable. -/
theorem not_metrizableSpace_stoneCech {X : Type u} [TopologicalSpace X]
    [T35Space X] [NoncompactSpace X] :
    ¬ TopologicalSpace.MetrizableSpace (StoneCech X) := by
  intro hmetrizable
  classical
  letI : TopologicalSpace.MetrizableSpace (StoneCech X) := hmetrizable
  letI : TopologicalSpace.MetrizableSpace X := isEmbedding_stoneCechUnit.metrizableSpace
  obtain ⟨y, hy⟩ := exists_stoneCech_not_mem_range (X := X)
  -- Density and metrizability provide a sequence in the canonical range converging to `y`.
  have hyClosure : y ∈ closure (Set.range (stoneCechUnit : X → StoneCech X)) := by
    rw [denseRange_stoneCechUnit.closure_eq]
    exact Set.mem_univ y
  obtain ⟨points, hpointsRange, hpointsTendsto⟩ :=
    mem_closure_iff_seq_limit.mp hyClosure
  choose sequence hsequence using hpointsRange
  -- Lifting every range point to `X` contradicts part (1).
  apply not_tendsto_stoneCechUnit_of_not_mem_range hy sequence
  have hpoints : stoneCechUnit ∘ sequence = points := by
    funext n
    exact hsequence n
  rw [hpoints]
  exact hpointsTendsto
