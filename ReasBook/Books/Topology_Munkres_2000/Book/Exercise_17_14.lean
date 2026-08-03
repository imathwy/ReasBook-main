module

public import Mathlib.Topology.Constructions
public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Real.Basic

public section

open Filter

/-- Helper for Exercise 17.14: the reciprocal sequence on positive natural numbers is injective. -/
lemma oneDivPNatInjective : Function.Injective (fun n : ℕ+ ↦ (1 : ℝ) / (n : ℝ)) := by
  -- Equality of reciprocals first gives equality of the corresponding real casts.
  intro m n h
  have hCast : (m : ℝ) = (n : ℝ) := by
    apply inv_injective
    simpa only [one_div] using h
  -- Injectivity of the natural-number cast then recovers equality in `ℕ+`.
  apply PNat.coe_inj.mp
  exact Nat.cast_injective hCast

/-- Helper for Exercise 17.14: the at-top filter on `ℕ+` refines the cofinite filter. -/
lemma pNatAtTop_le_cofinite : (atTop : Filter ℕ+) ≤ cofinite := by
  -- Beyond the successor of a fixed positive natural, every term differs from it.
  refine le_cofinite_iff_eventually_ne.mpr fun n ↦ ?_
  refine (eventually_ge_atTop (Nat.succPNat n)).mono fun m hm ↦ ?_
  exact ne_of_gt ((PNat.lt_succ_self n).trans_le hm)

/-- Helper for Exercise 17.14: the reciprocal sequence tends to the cofinite filter. -/
lemma oneDivTendstoCofinite :
    Tendsto (fun n : ℕ+ ↦ CofiniteTopology.of ((1 : ℝ) / (n : ℝ))) atTop cofinite := by
  -- Injectivity makes the sequence cofinite-to-cofinite continuous.
  have hInjective :
      Function.Injective (fun n : ℕ+ ↦ CofiniteTopology.of ((1 : ℝ) / (n : ℝ))) :=
    CofiniteTopology.of.injective.comp oneDivPNatInjective
  -- The at-top filter on positive naturals is finer than the cofinite filter.
  exact hInjective.tendsto_cofinite.mono_left pNatAtTop_le_cofinite

/-- Exercise 17.14: In the finite complement topology on `ℝ`, the sequence
`n : ℕ+ ↦ 1 / (n : ℝ)` converges to every point. -/
theorem oneDivTendstoEverywhere (x : CofiniteTopology ℝ) :
    Tendsto (fun n : ℕ+ ↦ CofiniteTopology.of ((1 : ℝ) / (n : ℝ))) atTop (nhds x) := by
  -- Every neighborhood filter contains the cofinite filter as a summand.
  rw [CofiniteTopology.nhds_eq]
  exact oneDivTendstoCofinite.mono_right le_sup_right
