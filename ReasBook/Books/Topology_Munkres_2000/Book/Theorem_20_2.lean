module

public import Topology_Munkres_2000.Book.Theorem_19_1.Basis
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.WithTopology

public section

universe u

namespace Pi

/-- Helper for Theorem 20.2: first countability of a real product forces the index type
to be countable. -/
lemma countable_of_firstCountable_real_pi (J : Type u)
    [FirstCountableTopology (J → ℝ)] : Countable J := by
  -- Choose a countable decreasing neighborhood basis at the zero function.
  classical
  obtain ⟨U, hUbasis⟩ := Filter.exists_antitone_basis (nhds (0 : J → ℝ))
  have hUnhds : ∀ n, U n ∈ nhds (0 : J → ℝ) := hUbasis.mem
  -- Each basis member contains a function supported on finitely many coordinates.
  choose I hIpiece using fun n ↦
    exists_finset_piecewise_mem_of_mem_nhds (hUnhds n) (fun _ ↦ (1 : ℝ))
  have hcover : (Set.univ : Set J) ⊆ ⋃ n, (I n : Set J) := by
    intro j _
    by_contra hj
    -- A cylinder restricting coordinate `j` must contain some basis member.
    have hcylinder : Set.pi ({j} : Set J) (fun _ ↦ Metric.ball (0 : ℝ) 1) ∈
        nhds (0 : J → ℝ) := by
      apply set_pi_mem_nhds (Set.finite_singleton j)
      intro i hi
      exact Metric.ball_mem_nhds 0 zero_lt_one
    obtain ⟨n, hUn⟩ := hUbasis.mem_iff.mp hcylinder
    have hjI : j ∉ I n := by
      intro hjmem
      exact hj (Set.mem_iUnion.2 ⟨n, hjmem⟩)
    -- The chosen function equals one at `j`, contradicting membership in the unit ball.
    have hpiece := hUn (hIpiece n) j (Set.mem_singleton j)
    simp only [Finset.piecewise, hjI, ↓reduceIte, Metric.mem_ball, Real.dist_eq, sub_zero,
      abs_one] at hpiece
    exact lt_irrefl 1 hpiece
  -- The index type is covered by countably many finite supports.
  apply Set.countable_univ_iff.mp
  exact (Set.countable_iUnion fun n ↦ (I n).countable_toSet).mono hcover

/-- Helper for Theorem 20.2: radii prescribed on an embedded copy of `ℕ`, with a
positive default radius elsewhere. -/
noncomputable def diagonalRadius {J : Type u} (e : ℕ ↪ J) (r : ℕ → ℝ) : J → ℝ :=
  Function.extend e (fun n ↦ r n / 4) (fun _ ↦ 1)

/-- Helper for Theorem 20.2: the diagonal radius has the prescribed value on every
embedded coordinate. -/
lemma diagonalRadius_apply {J : Type u} (e : ℕ ↪ J) (r : ℕ → ℝ) (n : ℕ) :
    diagonalRadius e r (e n) = r n / 4 := by
  -- Injectivity of the embedding makes `Function.extend` compute directly here.
  exact e.injective.extend_apply _ _ n

/-- Helper for Theorem 20.2: positive prescribed radii produce a positive diagonal
radius at every coordinate. -/
lemma diagonalRadius_pos {J : Type u} (e : ℕ ↪ J) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (j : J) : 0 < diagonalRadius e r j := by
  -- Separate coordinates in the embedded copy from coordinates using the default radius.
  classical
  by_cases hj : ∃ n, e n = j
  · obtain ⟨n, rfl⟩ := hj
    rw [diagonalRadius_apply]
    linarith [hr n]
  · rw [diagonalRadius, Function.extend_apply' _ _ _ hj]
    norm_num

/-- Helper for Theorem 20.2: every neighborhood of zero in a real box product contains
a coordinatewise open box. -/
lemma exists_box_subset_nhds_zero {J : Type u}
    {U : Set (WithTopology (J → ℝ) (boxTopologicalSpace (fun _ : J ↦ ℝ)))}
    (hU : U ∈ nhds
      (WithTopology.toTopology (boxTopologicalSpace (fun _ : J ↦ ℝ)) (0 : J → ℝ))) :
    ∃ V : J → Set ℝ,
      (∀ j, IsOpen (V j)) ∧ (∀ j, 0 ∈ V j) ∧
        WithTopology.ofTopology ⁻¹' Set.pi Set.univ V ⊆ U := by
  -- Replace the neighborhood by an open one and move it to the raw box product.
  letI : TopologicalSpace (J → ℝ) := boxTopologicalSpace (fun _ : J ↦ ℝ)
  obtain ⟨O, hOU, hOopen, hzero⟩ := mem_nhds_iff.mp hU
  have hOraw : IsOpen
      (WithTopology.toTopology (boxTopologicalSpace (fun _ : J ↦ ℝ)) ⁻¹' O) :=
    (WithTopology.isOpen_iff _).mp hOopen
  have hraw :
      WithTopology.toTopology (boxTopologicalSpace (fun _ : J ↦ ℝ)) ⁻¹' O ∈
        nhds (0 : J → ℝ) := by
    apply hOraw.mem_nhds
    exact hzero
  -- Refine the raw neighborhood by the box basis from Theorem 19.1.
  have hb := (Pi.isTopologicalBasis_boxBasis :
    (Pi.boxTopologicalSpace (fun _ : J ↦ ℝ)).IsTopologicalBasis
      (Pi.boxBasis (fun _ : J ↦ ℝ)))
  obtain ⟨s, hs, hzero', hsU⟩ := hb.mem_nhds_iff.mp hraw
  obtain ⟨V, hV, rfl⟩ := (Pi.mem_boxBasis s).mp hs
  refine ⟨V, hV, fun j ↦ hzero' j (Set.mem_univ j), ?_⟩
  intro x hx
  apply hOU
  exact hsU hx

/-- Helper for Theorem 20.2: a sequence of open boxes at zero misses one diagonal
open box at every stage. -/
lemma exists_diagonal_box_not_containing {J : Type u} (e : ℕ ↪ J)
    (V : ℕ → J → Set ℝ) (hVopen : ∀ n j, IsOpen (V n j))
    (hVzero : ∀ n j, 0 ∈ V n j) :
    ∃ W : Set (WithTopology (J → ℝ) (boxTopologicalSpace (fun _ : J ↦ ℝ))),
      IsOpen W ∧
        WithTopology.toTopology (boxTopologicalSpace (fun _ : J ↦ ℝ)) (0 : J → ℝ) ∈ W ∧
        ∀ n, ¬ (WithTopology.ofTopology ⁻¹' Set.pi Set.univ (V n)) ⊆ W := by
  -- Choose a positive ball inside the diagonal coordinate of each candidate box.
  classical
  letI : TopologicalSpace (J → ℝ) := boxTopologicalSpace (fun _ : J ↦ ℝ)
  have hVnhds : ∀ n, V n (e n) ∈ nhds (0 : ℝ) := by
    intro n
    exact (hVopen n (e n)).mem_nhds (hVzero n (e n))
  choose r hrpos hrsub using fun n ↦ Metric.mem_nhds_iff.mp (hVnhds n)
  let D : J → Set ℝ := fun j ↦ Metric.ball 0 (diagonalRadius e r j)
  let W : Set (WithTopology (J → ℝ) (boxTopologicalSpace (fun _ : J ↦ ℝ))) :=
    WithTopology.ofTopology ⁻¹' Set.pi Set.univ D
  refine ⟨W, ?_, ?_, ?_⟩
  · -- Coordinate balls make the diagonal box open.
    exact (WithTopology.continuous_ofTopology _).isOpen_preimage _
      (Pi.isOpen_box D fun _ ↦ Metric.isOpen_ball)
  · -- Positivity places the zero function in the diagonal box.
    intro j _
    simp only [D, Metric.mem_ball, Pi.zero_apply, dist_self]
    exact diagonalRadius_pos e hrpos j
  · intro n
    -- Change only coordinate `e n`; the resulting point stays in the `n`th candidate box.
    let z : WithTopology (J → ℝ) (boxTopologicalSpace (fun _ : J ↦ ℝ)) :=
      WithTopology.toTopology _ (Function.update (0 : J → ℝ) (e n) (r n / 2))
    have hzV : z ∈ WithTopology.ofTopology ⁻¹' Set.pi Set.univ (V n) := by
      intro j _
      by_cases hj : j = e n
      · subst j
        apply hrsub n
        simp only [z, Function.update_self, Metric.mem_ball, Real.dist_eq, sub_zero]
        rw [abs_of_pos]
        · linarith [hrpos n]
        · linarith [hrpos n]
      · simpa [z, Function.update, hj] using hVzero n j
    have hzW : z ∉ W := by
      intro hz
      have hcoord := hz (e n) (Set.mem_univ (e n))
      simp only [D, z, Function.update_self, Metric.mem_ball, diagonalRadius_apply,
        Real.dist_eq, sub_zero] at hcoord
      rw [abs_of_pos] at hcoord
      · linarith [hrpos n]
      · linarith [hrpos n]
    exact fun hsubset ↦ hzW (hsubset hzV)

/-- Helper for Theorem 20.2: an infinite real box product is not first-countable. -/
lemma realBox_not_firstCountable (J : Type u) [Infinite J] :
    ¬FirstCountableTopology
      (WithTopology (J → ℝ) (boxTopologicalSpace (fun _ : J ↦ ℝ))) := by
  -- A hypothetical first-countable structure supplies a countable local basis at zero.
  intro hfirst
  letI : FirstCountableTopology
      (WithTopology (J → ℝ) (boxTopologicalSpace (fun _ : J ↦ ℝ))) := hfirst
  let zeroBox :=
    WithTopology.toTopology (boxTopologicalSpace (fun _ : J ↦ ℝ)) (0 : J → ℝ)
  obtain ⟨U, hUbasis⟩ := Filter.exists_antitone_basis (nhds zeroBox)
  have hUnhds : ∀ n, U n ∈ nhds zeroBox := hUbasis.mem
  choose V hVopen hVzero hVU using fun n ↦ exists_box_subset_nhds_zero (hUnhds n)
  obtain ⟨W, hWopen, hWzero, hVW⟩ :=
    exists_diagonal_box_not_containing (Infinite.natEmbedding J) V hVopen hVzero
  have hWnhds : W ∈ nhds zeroBox := hWopen.mem_nhds hWzero
  obtain ⟨n, hUnW⟩ := hUbasis.mem_iff.mp hWnhds
  -- The refined box lies in `U n`, contradicting its diagonal obstruction.
  exact hVW n (Set.Subset.trans (hVU n) hUnW)

/-- Theorem 20.2 (1): The product topology on `J → ℝ` is metrizable exactly when
`J` is countable. The theorem's stated infinite-index case is the direct specialization. -/
theorem real_product_metrizable_iff_countable (J : Type u) :
    TopologicalSpace.MetrizableSpace (J → ℝ) ↔ Countable J := by
  constructor
  · -- Metrizability gives first countability, hence countability of the coordinate set.
    intro hmetric
    letI : TopologicalSpace.MetrizableSpace (J → ℝ) := hmetric
    exact countable_of_firstCountable_real_pi J
  · -- A countable product of metrizable real lines is metrizable.
    intro hJ
    letI : Countable J := hJ
    infer_instance

/-- Theorem 20.2 (2): For an infinite index type, the box topology on `J → ℝ` is not
metrizable. -/
theorem real_box_not_metrizable (J : Type u) [Infinite J] :
    ¬TopologicalSpace.MetrizableSpace
      (WithTopology (J → ℝ) (boxTopologicalSpace (fun _ : J ↦ ℝ))) := by
  -- Any metrizable space is first-countable, contradicting the diagonal obstruction.
  intro hmetric
  letI : TopologicalSpace.MetrizableSpace
      (WithTopology (J → ℝ) (boxTopologicalSpace (fun _ : J ↦ ℝ))) := hmetric
  exact realBox_not_firstCountable J inferInstance

end Pi
