module

public import Topology_Munkres_2000.Book.Definition_19_1.BoxTopology
public import Mathlib.Topology.Instances.Real.Lemmas

public section

/- Exercise 19.6 (1): convergence in a dependent product with the product topology
is exactly coordinatewise convergence. -/
#check tendsto_pi_nhds

/-- Every coordinate of the moving spikes `Pi.single n (1 : ℝ)` converges to zero. -/
theorem tendsto_pi_single_apply (i : ℕ) :
    Filter.Tendsto (fun n : ℕ ↦ Pi.single n (1 : ℝ) i) Filter.atTop (nhds 0) := by
  -- Past the fixed coordinate `i`, every moving spike evaluates to zero at `i`.
  have hEventuallyZero :
      (fun n : ℕ ↦ Pi.single n (1 : ℝ) i) =ᶠ[Filter.atTop] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [Filter.eventually_gt_atTop i] with n hn
    simp only [Pi.single_eq_of_ne hn.ne]
  -- Transport convergence of the constant zero sequence across this eventual equality.
  exact tendsto_const_nhds.congr' hEventuallyZero.symm

/-- The moving spikes `Pi.single n (1 : ℝ)` do not converge to zero in the box topology. -/
theorem not_tendsto_pi_single_box :
    ¬ Filter.Tendsto (fun n : ℕ ↦ Pi.single n (1 : ℝ)) Filter.atTop
      (Pi.boxNhds (fun _ : ℕ ↦ (0 : ℝ))) := by
  let U : ℕ → Set ℝ := fun _ ↦ Set.Iio (1 / 2 : ℝ)
  let box : Set (ℕ → ℝ) := Set.pi Set.univ U
  -- The box with every coordinate below `1 / 2` is an open neighborhood of zero.
  have hBoxOpen :
      (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)).IsOpen box := by
    exact Pi.isOpen_box U (fun _ ↦ isOpen_Iio)
  have hZeroMem : (fun _ : ℕ ↦ (0 : ℝ)) ∈ box := by
    intro i hi
    norm_num [box, U]
  have hBoxMem : box ∈ Pi.boxNhds (fun _ : ℕ ↦ (0 : ℝ)) :=
    @IsOpen.mem_nhds (ℕ → ℝ) (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ))
      (fun _ : ℕ ↦ (0 : ℝ)) box hBoxOpen hZeroMem
  intro hTendsto
  -- Hypothetical convergence forces all sufficiently late spikes into this box.
  have hEventuallyBox : ∀ᶠ n in Filter.atTop, Pi.single n (1 : ℝ) ∈ box :=
    hTendsto.eventually hBoxMem
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hEventuallyBox
  have hSpikeMem := hN N le_rfl
  -- The `N`-th spike has value one at coordinate `N`, contradicting the box bound.
  have hDiagonal := hSpikeMem N (Set.mem_univ N)
  norm_num [box, U, Pi.single_eq_same] at hDiagonal

/-- Exercise 19.6 (2): coordinatewise convergence does not characterize convergence
in the box topology. -/
theorem piSingle_counterexample :
    (∀ i, Filter.Tendsto (fun n : ℕ ↦ Pi.single n (1 : ℝ) i) Filter.atTop (nhds 0)) ∧
      ¬ Filter.Tendsto (fun n : ℕ ↦ Pi.single n (1 : ℝ)) Filter.atTop
        (Pi.boxNhds (fun _ : ℕ ↦ (0 : ℝ))) :=
  ⟨tendsto_pi_single_apply, not_tendsto_pi_single_box⟩
