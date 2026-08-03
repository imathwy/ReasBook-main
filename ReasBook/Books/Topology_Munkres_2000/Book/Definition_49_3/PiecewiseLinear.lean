module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Instances.Real.Lemmas

public section

open Set

namespace UnitIntervalPiecewiseLinear

/-- A function on the closed unit interval is piecewise linear if it has a finite
broken-line presentation. -/
def IsPiecewiseLinear (g : Icc (0 : ℝ) 1 → ℝ) : Prop :=
  ∃ k : ℕ, ∃ knots : Fin (k + 2) → Icc (0 : ℝ) 1, ∃ slopes : Fin (k + 1) → ℝ,
    StrictMono knots ∧
      knots 0 = ⊥ ∧
      knots (Fin.last (k + 1)) = ⊤ ∧
      ∀ (i : Fin (k + 1)) (t : Icc (0 : ℝ) 1),
        knots i.castSucc ≤ t → t ≤ knots i.succ →
          g t = g (knots i.castSucc) + slopes i * ((t : ℝ) - knots i.castSucc)

/-- A piecewise-linear function is `IsSteep` with parameter `α` if every segment
in one finite broken-line presentation has slope of magnitude at least `α`. -/
def IsSteep (g : Icc (0 : ℝ) 1 → ℝ) (α : ℝ) : Prop :=
  ∃ k : ℕ, ∃ knots : Fin (k + 2) → Icc (0 : ℝ) 1, ∃ slopes : Fin (k + 1) → ℝ,
    StrictMono knots ∧
      knots 0 = ⊥ ∧
      knots (Fin.last (k + 1)) = ⊤ ∧
      (∀ (i : Fin (k + 1)) (t : Icc (0 : ℝ) 1),
        knots i.castSucc ≤ t → t ≤ knots i.succ →
          g t = g (knots i.castSucc) + slopes i * ((t : ℝ) - knots i.castSucc)) ∧
      ∀ i, α ≤ |slopes i|

/-- Helper for Definition 49.3: the finite knot-and-slope certificate characterizing
`IsPiecewiseLinear`. -/
theorem isPiecewiseLinear_iff (g : Icc (0 : ℝ) 1 → ℝ) :
    IsPiecewiseLinear g ↔
      ∃ k : ℕ, ∃ knots : Fin (k + 2) → Icc (0 : ℝ) 1, ∃ slopes : Fin (k + 1) → ℝ,
        StrictMono knots ∧
          knots 0 = ⊥ ∧
          knots (Fin.last (k + 1)) = ⊤ ∧
          ∀ (i : Fin (k + 1)) (t : Icc (0 : ℝ) 1),
            knots i.castSucc ≤ t → t ≤ knots i.succ →
              g t = g (knots i.castSucc) + slopes i * ((t : ℝ) - knots i.castSucc) :=
  Iff.rfl

/-- The finite knot-and-slope certificate characterizing `IsSteep`. -/
theorem isSteep_iff (g : Icc (0 : ℝ) 1 → ℝ) (α : ℝ) :
    IsSteep g α ↔
      ∃ k : ℕ, ∃ knots : Fin (k + 2) → Icc (0 : ℝ) 1, ∃ slopes : Fin (k + 1) → ℝ,
        StrictMono knots ∧
          knots 0 = ⊥ ∧
          knots (Fin.last (k + 1)) = ⊤ ∧
          (∀ (i : Fin (k + 1)) (t : Icc (0 : ℝ) 1),
            knots i.castSucc ≤ t → t ≤ knots i.succ →
              g t = g (knots i.castSucc) + slopes i * ((t : ℝ) - knots i.castSucc)) ∧
          ∀ i, α ≤ |slopes i| :=
  Iff.rfl

/-- A function that is steep in a finite broken-line presentation is piecewise linear. -/
theorem IsSteep.isPiecewiseLinear {g : Icc (0 : ℝ) 1 → ℝ} {α : ℝ}
    (hg : IsSteep g α) : IsPiecewiseLinear g := by
  rcases hg with ⟨k, knots, slopes, hknots, hzero, hone, hlinear, _⟩
  exact ⟨k, knots, slopes, hknots, hzero, hone, hlinear⟩

/-- Helper for Definition 49.3: monotone knots joining bottom to top have adjacent
closed intervals covering the whole bounded linear order. -/
lemma iUnion_adjacentIcc_eq_univ {β : Type*} [LinearOrder β] [OrderBot β] [OrderTop β]
    (k : ℕ) (knots : Fin (k + 2) → β) (hknots : Monotone knots)
    (hzero : knots 0 = ⊥) (hone : knots (Fin.last (k + 1)) = ⊤) :
    ⋃ i : Fin (k + 1), Icc (knots i.castSucc) (knots i.succ) = univ := by
  -- Choose the least knot lying weakly above an arbitrary point.
  ext x
  simp only [mem_iUnion, mem_Icc, mem_univ, iff_true]
  let indices : Set (Fin (k + 2)) := {j | x ≤ knots j}
  have hindicesFinite : indices.Finite := toFinite indices
  have hlast : Fin.last (k + 1) ∈ indices := by
    rw [Set.mem_setOf_eq, hone]
    exact le_top
  obtain ⟨j, hj, hjmin⟩ :=
    Set.exists_min_image indices (fun j ↦ j) hindicesFinite ⟨Fin.last (k + 1), hlast⟩
  change x ≤ knots j at hj
  by_cases hjzero : j = 0
  · -- At the first knot, monotonicity places the point in the first segment.
    subst j
    refine ⟨0, ?_, ?_⟩
    · simpa only [Fin.castSucc_zero, hzero] using (bot_le : (⊥ : β) ≤ x)
    · exact hj.trans (hknots (Fin.zero_le _))
  · -- Otherwise minimality forces the preceding knot to lie below the point.
    let i : Fin (k + 1) := j.pred hjzero
    refine ⟨i, ?_, ?_⟩
    · by_contra hlower
      have hmem : i.castSucc ∈ indices := by
        change x ≤ knots i.castSucc
        exact le_of_not_ge hlower
      have hle : j ≤ i.castSucc := hjmin i.castSucc hmem
      have hsucc : i.succ = j := by
        dsimp [i]
        exact Fin.succ_pred j hjzero
      have himpossible : i.succ ≤ i.castSucc := hsucc.le.trans hle
      exact (not_le_of_gt (Fin.castSucc_lt_succ (i := i))) himpossible
    · rw [Fin.succ_pred j hjzero]
      exact hj

/-- Helper for Definition 49.3: agreement with an affine function on an interval
implies continuity on that interval. -/
lemma continuousOn_of_eq_affine {g : Icc (0 : ℝ) 1 → ℝ}
    {a b : Icc (0 : ℝ) 1} {c m : ℝ}
    (h : ∀ t ∈ Icc a b, g t = c + m * ((t : ℝ) - (a : ℝ))) :
    ContinuousOn g (Icc a b) := by
  -- The affine comparison map is continuous on the unit-interval subtype.
  have haffine : Continuous
      (fun t : Icc (0 : ℝ) 1 ↦ c + m * ((t : ℝ) - (a : ℝ))) := by
    fun_prop
  -- Transfer continuity through the prescribed pointwise agreement.
  exact haffine.continuousOn.congr fun t ht ↦ h t ht

end UnitIntervalPiecewiseLinear
