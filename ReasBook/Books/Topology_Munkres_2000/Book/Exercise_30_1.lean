module

public import Topology_Munkres_2000.Book.Exercise_20_4.RealSequences
public import Topology_Munkres_2000.Book.Theorem_19_1.Basis
import Mathlib.Topology.Separation.GDelta
import Mathlib.Topology.WithTopology

public section

/- Exercise 30.1 (a): In a first-countable `T₁` space, every singleton is a
`Gδ` set. -/
#check IsGδ.singleton

namespace Pi

/-- Helper for Exercise 30.1: coordinate evaluation is continuous for the box topology. -/
theorem continuous_apply_box {ι X : Type*} [TopologicalSpace X] (i : ι) :
    Continuous
      (fun x : WithTopology (ι → X) (boxTopologicalSpace (fun _ : ι ↦ X)) ↦
        x.ofTopology i) := by
  -- Prove continuity on the raw box product, then compose with the wrapper projection.
  classical
  letI : TopologicalSpace (ι → X) := boxTopologicalSpace (fun _ : ι ↦ X)
  have hraw : Continuous (fun x : ι → X ↦ x i) := by
    rw [continuous_def]
    intro s hs
    let U : ι → Set X := fun j ↦ if j = i then s else Set.univ
    have hU : ∀ j, IsOpen (U j) := by
      intro j
      by_cases hji : j = i
      · simpa [U, hji] using hs
      · simp [U, hji]
    have hopen : IsOpen (Set.pi Set.univ U) := isOpen_box U hU
    have hpreimage :
        (fun x : ι → X ↦ x i) ⁻¹' s = Set.pi Set.univ U := by
      ext x
      simp [U]
    rwa [hpreimage]
  exact hraw.comp (WithTopology.continuous_ofTopology _)

end Pi

namespace BoxRealSequence

/-- Helper for Exercise 30.1: equality of sequences is equality at every coordinate. -/
theorem singleton_eq_iInter_coordinate (x : BoxRealSequence) :
    ({x} : Set BoxRealSequence) =
      ⋂ n : ℕ, (fun y : BoxRealSequence ↦ y.ofTopology n) ⁻¹'
        ({x.ofTopology n} : Set ℝ) := by
  -- Reduce singleton membership to pointwise equality, then use function extensionality.
  ext y
  simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_preimage,
    Set.mem_singleton_iff]
  constructor
  · intro hy
    rw [hy]
    exact fun _ ↦ rfl
  · intro hy
    apply WithTopology.ofTopology_injective _
    exact funext hy

/-- Helper for Exercise 30.1: every neighborhood of zero contains a coordinatewise open box. -/
theorem exists_box_subset_nhds_zero {U : Set BoxRealSequence}
    (hU : U ∈ nhds (ofSequence 0)) :
    ∃ V : ℕ → Set ℝ,
      (∀ i, IsOpen (V i)) ∧ (∀ i, 0 ∈ V i) ∧
        WithTopology.ofTopology ⁻¹' Set.pi Set.univ V ⊆ U := by
  -- First replace the neighborhood by an open neighborhood, then refine its raw preimage.
  letI : TopologicalSpace (ℕ → ℝ) := Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)
  obtain ⟨O, hOU, hOopen, hzero⟩ := mem_nhds_iff.mp hU
  have hOraw : IsOpen
      (WithTopology.toTopology (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) ⁻¹' O) :=
    (WithTopology.isOpen_iff _).mp hOopen
  have hraw :
      WithTopology.toTopology (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) ⁻¹' O ∈
        nhds (0 : ℕ → ℝ) := by
    apply hOraw.mem_nhds
    simpa [ofSequence_eq_toTopology] using hzero
  have hb := (Pi.isTopologicalBasis_boxBasis :
    (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)).IsTopologicalBasis
      (Pi.boxBasis (fun _ : ℕ ↦ ℝ)))
  obtain ⟨s, hs, hzero, hsU⟩ := hb.mem_nhds_iff.mp hraw
  obtain ⟨V, hV, rfl⟩ := (Pi.mem_boxBasis s).mp hs
  refine ⟨V, hV, fun i ↦ hzero i (Set.mem_univ i), ?_⟩
  intro x hx
  apply hOU
  exact hsU hx

/-- Helper for Exercise 30.1: a countable family of open boxes at zero misses one diagonal
open box at every stage. -/
theorem exists_diagonal_box_not_containing (V : ℕ → ℕ → Set ℝ)
    (hVopen : ∀ n i, IsOpen (V n i)) (hVzero : ∀ n i, 0 ∈ V n i) :
    ∃ W : Set BoxRealSequence,
      IsOpen W ∧ ofSequence 0 ∈ W ∧
        ∀ n, ¬ (WithTopology.ofTopology ⁻¹' Set.pi Set.univ (V n)) ⊆ W := by
  -- Choose a positive ball inside the diagonal coordinate of each candidate box.
  classical
  letI : TopologicalSpace (ℕ → ℝ) := Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)
  have hVnhds : ∀ n, V n n ∈ nhds (0 : ℝ) := by
    intro n
    exact (hVopen n n).mem_nhds (hVzero n n)
  choose r hrpos hrsub using fun n ↦ Metric.mem_nhds_iff.mp (hVnhds n)
  let D : ℕ → Set ℝ := fun n ↦ Metric.ball 0 (r n / 4)
  let W : Set BoxRealSequence :=
    WithTopology.ofTopology ⁻¹' Set.pi Set.univ D
  refine ⟨W, ?_, ?_, ?_⟩
  · -- The diagonal box is open because each coordinate is an open ball.
    exact (WithTopology.continuous_ofTopology _).isOpen_preimage _
      (Pi.isOpen_box D fun _ ↦ Metric.isOpen_ball)
  · -- Positivity of every radius puts the zero sequence in the diagonal box.
    intro n _
    simp only [D, ofSequence_eq_toTopology, WithTopology.ofTopology_toTopology,
      Metric.mem_ball, Pi.zero_apply, dist_self]
    linarith [hrpos n]
  · intro n
    -- Update only coordinate `n`; this remains in the `n`th candidate box.
    let z : BoxRealSequence := ofSequence (Function.update (0 : ℕ → ℝ) n (r n / 2))
    have hzV : z ∈ WithTopology.ofTopology ⁻¹' Set.pi Set.univ (V n) := by
      intro i _
      by_cases hin : i = n
      · subst i
        apply hrsub n
        simp only [z, ofSequence_eq_toTopology, WithTopology.ofTopology_toTopology,
          Function.update_self, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
        rw [abs_of_pos]
        · linarith [hrpos n]
        · linarith [hrpos n]
      · simpa [z, ofSequence_eq_toTopology, Function.update, hin] using hVzero n i
    have hzW : z ∉ W := by
      intro hz
      have hcoord := hz n (Set.mem_univ n)
      simp only [D, z, ofSequence_eq_toTopology, WithTopology.ofTopology_toTopology,
        Function.update_self, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hcoord
      rw [abs_of_pos] at hcoord
      · linarith [hrpos n]
      · linarith [hrpos n]
    exact fun hsubset ↦ hzW (hsubset hzV)

end BoxRealSequence

/- Exercise 30.1 (b): In the countable Cartesian power of `ℝ` with the box topology,
every singleton is a `Gδ` set, but the space is not first-countable. -/
mutual

/-- Every singleton in the countable Cartesian power of `ℝ` with the box topology is a
`Gδ` set. -/
theorem boxRealSequences_singleton_isGδ (x : BoxRealSequence) : IsGδ {x} := by
  -- Rewrite the singleton as the countable intersection of its coordinate fibers.
  rw [BoxRealSequence.singleton_eq_iInter_coordinate]
  apply IsGδ.iInter
  intro n
  -- Each fiber is the continuous preimage of a real singleton.
  exact (IsGδ.singleton (x.ofTopology n)).preimage (Pi.continuous_apply_box n)

/-- The countable Cartesian power of `ℝ` with the box topology is not first-countable. -/
theorem boxRealSequences_not_firstCountable : ¬FirstCountableTopology BoxRealSequence := by
  -- A hypothetical first-countable structure gives a countable neighborhood basis at zero.
  intro hfirst
  letI : FirstCountableTopology BoxRealSequence := hfirst
  obtain ⟨U, hUbasis⟩ := Filter.exists_antitone_basis (nhds (BoxRealSequence.ofSequence 0))
  have hUnhds : ∀ n, U n ∈ nhds (BoxRealSequence.ofSequence 0) := hUbasis.mem
  choose V hVopen hVzero hVU using fun n ↦
    BoxRealSequence.exists_box_subset_nhds_zero (hUnhds n)
  obtain ⟨W, hWopen, hWzero, hVW⟩ :=
    BoxRealSequence.exists_diagonal_box_not_containing V hVopen hVzero
  have hWnhds : W ∈ nhds (BoxRealSequence.ofSequence 0) := hWopen.mem_nhds hWzero
  obtain ⟨n, hUnW⟩ := hUbasis.mem_iff.mp hWnhds
  -- The refined box lies in `U n`, contradicting its diagonal obstruction.
  exact hVW n (Set.Subset.trans (hVU n) hUnW)

end
