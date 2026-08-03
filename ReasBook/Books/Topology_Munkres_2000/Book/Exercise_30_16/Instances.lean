module

public import Mathlib.Analysis.Complex.Tietze
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

public section

/-- The product of real lines indexed by the unit interval is separable. -/
instance unitIntervalRealPowerSeparable :
    TopologicalSpace.SeparableSpace (unitInterval → ℝ) := by
  -- Continuous real-valued functions are dense for the product topology because
  -- any prescribed values on finitely many coordinates extend by Tietze's theorem.
  have hDense : DenseRange (fun f : C(unitInterval, ℝ) ↦ (f : unitInterval → ℝ)) := by
    refine dense_iff_inter_open.2 fun U hU hUne ↦ ?_
    obtain ⟨g, hgU⟩ := hUne
    obtain ⟨I, V, hV, hVU⟩ := isOpen_pi_iff.mp hU g hgU
    let s : Set unitInterval := I
    have hsClosed : IsClosed s := I.finite_toSet.isClosed
    let f : C(s, ℝ) := ⟨fun x ↦ g x, continuous_of_discreteTopology⟩
    obtain ⟨F, hF⟩ := f.exists_restrict_eq hsClosed
    have hFI : ∀ i : I, F i = g i := by
      intro i
      exact congrArg (fun q : C(s, ℝ) ↦ q ⟨i, i.2⟩) hF
    refine ⟨F, hVU fun i hi ↦ ?_, ⟨F, rfl⟩⟩
    rw [hFI ⟨i, hi⟩]
    exact (hV i hi).2
  exact hDense.separableSpace (continuous_pi fun i ↦ continuous_eval_const i)
