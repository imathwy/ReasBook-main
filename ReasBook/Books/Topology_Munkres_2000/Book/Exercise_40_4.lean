module

public import Topology_Munkres_2000.Book.Definition_6_0_2.SigmaLocallyFinite
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Constructions.SumProd

public section

/-- The topological sum of an uncountable discrete family of real lines. -/
abbrev UncountableLineSum := WithDiscreteTopology ℝ × ℝ

namespace UncountableLineSum

/-- Helper for Exercise 40.4: products of a fixed set with the singleton fibers of a
discrete space form a locally finite family. -/
private lemma locallyFiniteSingletonProducts
    {D Y : Type*} [TopologicalSpace D] [DiscreteTopology D] [TopologicalSpace Y]
    (V : Set Y) : LocallyFinite (fun d : D ↦ ({d} : Set D) ×ˢ V) := by
  intro x
  -- The open fiber through `x` can meet only the member indexed by `x.1`.
  refine ⟨{x.1} ×ˢ Set.univ,
    ((isOpen_discrete {x.1}).prod isOpen_univ).mem_nhds ⟨rfl, Set.mem_univ x.2⟩, ?_⟩
  refine Set.finite_singleton x.1 |>.subset ?_
  intro d hd
  rcases hd with ⟨z, hzd, hzx⟩
  exact Set.mem_singleton_iff.mpr
    ((Set.mem_singleton_iff.mp hzd.1).symm.trans (Set.mem_singleton_iff.mp hzx.1))

/-- Helper for Exercise 40.4: the product of the singleton basis with a sequential
basis is the union of its fixed-rank singleton-product families. -/
private lemma productSingletonBasis_eq_iUnion
    {D Y : Type*} (b : ℕ → Set Y) :
    Set.image2 (· ×ˢ ·) {s : Set D | ∃ d : D, s = {d}} (Set.range b) =
      ⋃ n, Set.range (fun d : D ↦ ({d} : Set D) ×ˢ b n) := by
  ext s
  constructor
  · -- Record the sequential-basis index of the second factor.
    rintro ⟨u, ⟨d, rfl⟩, v, ⟨n, rfl⟩, rfl⟩
    exact Set.mem_iUnion.mpr ⟨n, Set.mem_range_self d⟩
  · -- Conversely, each fixed-rank member belongs to the product basis.
    intro hs
    rcases Set.mem_iUnion.mp hs with ⟨n, hn⟩
    rcases hn with ⟨d, rfl⟩
    exact ⟨{d}, ⟨d, rfl⟩, b n, ⟨n, rfl⟩, rfl⟩

/-- Helper for Exercise 40.4: a product with a discrete left factor and a
second-countable right factor has a σ-locally finite basis. -/
private lemma hasSigmaLocallyFiniteBasis_prod_of_discrete_left
    (D Y : Type*) [TopologicalSpace D] [DiscreteTopology D]
    [TopologicalSpace Y] [SecondCountableTopology Y] :
    HasSigmaLocallyFiniteBasis (D × Y) := by
  obtain ⟨b, hb⟩ := TopologicalSpace.exists_seq_basis Y
  rw [hasSigmaLocallyFiniteBasis_iff]
  -- Use product basis members of fixed `b n` as the `n`th locally finite piece.
  refine ⟨Set.image2 (· ×ˢ ·) {s : Set D | ∃ d : D, s = {d}} (Set.range b),
    fun n ↦ Set.range (fun d : D ↦ ({d} : Set D) ×ˢ b n), ?_, ?_, ?_⟩
  · exact (isTopologicalBasis_singletons D).prod hb
  · exact productSingletonBasis_eq_iUnion b
  · intro n
    exact (locallyFiniteSingletonProducts (b n)).on_range

/-- Helper for Exercise 40.4: the uncountable topological sum of real lines is
nondiscrete. -/
theorem notDiscrete : ¬ DiscreteTopology UncountableLineSum := by
  intro hdiscrete
  letI : DiscreteTopology UncountableLineSum := hdiscrete
  -- The real-coordinate slice would inherit the discrete topology.
  have hrealDiscrete : DiscreteTopology ℝ :=
    (isEmbedding_prodMkRight (WithTopology.toTopology ⊥ (0 : ℝ))).discreteTopology
  letI : DiscreteTopology ℝ := hrealDiscrete
  have hsubsingleton : Subsingleton ℝ :=
    DenselyOrdered.subsingleton_of_discreteTopology
  exact zero_ne_one (hsubsingleton.elim 0 1)

/-- Helper for Exercise 40.4: the uncountable topological sum of real lines has a
σ-locally finite basis. -/
theorem hasSigmaLocallyFiniteBasis :
    HasSigmaLocallyFiniteBasis UncountableLineSum := by
  -- Instantiate the product construction with an uncountable discrete real factor.
  exact hasSigmaLocallyFiniteBasis_prod_of_discrete_left
    (WithDiscreteTopology ℝ) ℝ

/-- Helper for Exercise 40.4: the uncountable topological sum of real lines does not
have a countable basis. -/
theorem notSecondCountable : ¬ SecondCountableTopology UncountableLineSum := by
  intro hsecond
  letI : SecondCountableTopology UncountableLineSum := hsecond
  -- The discrete-coordinate slice would be second countable and hence countable.
  have hdiscreteSecond : SecondCountableTopology (WithDiscreteTopology ℝ) :=
    (isEmbedding_prodMkLeft (0 : ℝ)).secondCountableTopology
  letI : SecondCountableTopology (WithDiscreteTopology ℝ) := hdiscreteSecond
  have hdiscreteCountable : Countable (WithDiscreteTopology ℝ) :=
    TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  letI : Countable (WithDiscreteTopology ℝ) := hdiscreteCountable
  have hrealCountable : Countable ℝ :=
    Countable.of_equiv (WithDiscreteTopology ℝ) (WithTopology.equiv ℝ ⊥)
  exact not_countable hrealCountable

/-- Exercise 40.4: The uncountable topological sum of real lines is a nondiscrete space
with a σ-locally finite basis but no countable basis. -/
theorem properties :
    ¬ DiscreteTopology UncountableLineSum ∧
      HasSigmaLocallyFiniteBasis UncountableLineSum ∧
        ¬ SecondCountableTopology UncountableLineSum :=
  ⟨notDiscrete, hasSigmaLocallyFiniteBasis, notSecondCountable⟩

end UncountableLineSum
