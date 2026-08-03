module

public import Topology_Munkres_2000.Book.Exercise_36_4.PointFinite
public import Topology_Munkres_2000.Book.Example_39_1.ReciprocalIntervals
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocalAtTarget

open Filter TopologicalSpace Topology

public section

/-- The open family in Exercise 39.2, consisting of `Set.univ` together with the
intervals `Set.Ioo 0 (1 / (n + 1))`. -/
@[expose]
def realPointFiniteOpenCover : ℕ → Opens ℝ
  | 0 => ⊤
  | n + 1 =>
      ⟨reciprocalInitialInterval n.succPNat, isOpen_reciprocalInitialInterval _⟩

/-- The first member of `realPointFiniteOpenCover` is `Set.univ`. -/
@[simp]
theorem realPointFiniteOpenCover_zero : realPointFiniteOpenCover 0 = ⊤ := rfl

/-- The positive-index members of `realPointFiniteOpenCover` are the reciprocal
initial intervals from Example 39.1. -/
@[simp]
theorem realPointFiniteOpenCover_succ (n : ℕ) :
    (realPointFiniteOpenCover (n + 1) : Set ℝ) =
      reciprocalInitialInterval n.succPNat := rfl

/-- The positive-index members of `realPointFiniteOpenCover` are the shrinking
intervals `Set.Ioo 0 (1 / (n + 1))`. -/
@[simp]
public theorem realPointFiniteOpenCover_succ_eq_Ioo (n : ℕ) :
    (realPointFiniteOpenCover (n + 1) : Set ℝ) = Set.Ioo 0 (1 / (n + 1 : ℝ)) := by
  ext x
  simp only [realPointFiniteOpenCover_succ, mem_reciprocalInitialInterval,
    Set.mem_Ioo, Nat.succPNat_coe, Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one]

/-- The family `realPointFiniteOpenCover` covers `ℝ`. -/
theorem isOpenCover_realPointFiniteOpenCover :
    IsOpenCover realPointFiniteOpenCover := by
  -- The zeroth member is already the whole space, so the supremum is top.
  apply IsOpenCover.mk
  apply top_unique
  rw [← realPointFiniteOpenCover_zero]
  exact le_iSup realPointFiniteOpenCover 0

/-- Each real number belongs to only finitely many members of
`realPointFiniteOpenCover`. -/
theorem pointFinite_realPointFiniteOpenCover :
    PointFinite (fun n ↦ (realPointFiniteOpenCover n : Set ℝ)) := by
  rw [pointFinite_iff]
  intro x
  by_cases hx : x ≤ 0
  · -- A nonpositive point can occur only in the zeroth, universal member.
    apply (Set.finite_singleton 0).subset
    intro n hn
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hn ⊢
    cases n with
    | zero => rfl
    | succ n =>
      rw [realPointFiniteOpenCover_succ_eq_Ioo, Set.mem_Ioo] at hn
      exact False.elim ((not_lt_of_ge hx) hn.1)
  · -- For a positive point, reciprocal endpoints eventually lie below it.
    have hxpos : 0 < x := lt_of_not_ge hx
    have hlimit :
        Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have heventually : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < x :=
      (tendsto_order.1 hlimit).2 x hxpos
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 heventually
    apply (Set.finite_Iio (N + 1)).subset
    intro n hn
    simp only [Set.mem_setOf_eq, Set.mem_Iio] at hn ⊢
    cases n with
    | zero => omega
    | succ n =>
      rw [realPointFiniteOpenCover_succ_eq_Ioo, Set.mem_Ioo] at hn
      by_contra hbound
      have hNn : N ≤ n := by omega
      have hendpoint := hN n hNn
      linarith

/-- Helper for Exercise 39.2: An injectively indexed sequence of family members containing
points converging to one limit prevents local finiteness. -/
lemma notLocallyFinite_of_tendsto_mem_injective {ι X : Type*} [TopologicalSpace X]
    {f : ι → Set X} {e : ℕ → ι} {y : ℕ → X} {x : X}
    (he : Function.Injective e) (hy : Filter.Tendsto y Filter.atTop (𝓝 x))
    (hmem : ∀ n, y n ∈ f (e n)) :
    ¬ LocallyFinite f := by
  -- A locally finite neighborhood would meet only finitely many selected members.
  intro hlocal
  obtain ⟨U, hU, hfinite⟩ := hlocal x
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hy.eventually hU)
  let g : Set.Ici N → ι := fun n ↦ e n.1
  have hg : Function.Injective g := by
    intro m n hmn
    exact Subtype.ext (he hmn)
  have hinfinite : (Set.range g).Infinite := Set.infinite_range_of_injective hg
  apply hinfinite
  apply hfinite.subset
  intro i hi
  obtain ⟨n, rfl⟩ := hi
  -- The selected point witnesses that the corresponding member meets the neighborhood.
  exact ⟨y n, hmem n, hN n n.property⟩

/-- The family `realPointFiniteOpenCover` is not locally finite. -/
theorem not_locallyFinite_realPointFiniteOpenCover :
    ¬ LocallyFinite (fun n ↦ (realPointFiniteOpenCover n : Set ℝ)) := by
  -- Use positive indices and interior half-reciprocal points converging to zero.
  let e : ℕ → ℕ := fun n ↦ n + 1
  let y : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) * (1 / ((n : ℝ) + 1))
  have he : Function.Injective e := Nat.succ_injective
  have hy : Filter.Tendsto y Filter.atTop (𝓝 0) := by
    simpa only [y, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop
          (𝓝 (0 : ℝ))).const_mul (1 / 2)
  have hmem : ∀ n, y n ∈ (realPointFiniteOpenCover (e n) : Set ℝ) := by
    intro n
    dsimp only [e, y]
    rw [realPointFiniteOpenCover_succ_eq_Ioo, Set.mem_Ioo]
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    constructor
    · linarith
    · linarith
  exact notLocallyFinite_of_tendsto_mem_injective he hy hmem

/-- Exercise 39.2: `realPointFiniteOpenCover` is a point-finite open covering of
`ℝ` that is not locally finite. -/
theorem realPointFiniteOpenCover_spec :
    IsOpenCover realPointFiniteOpenCover ∧
      PointFinite (fun n ↦ (realPointFiniteOpenCover n : Set ℝ)) ∧
        ¬ LocallyFinite (fun n ↦ (realPointFiniteOpenCover n : Set ℝ)) :=
  ⟨isOpenCover_realPointFiniteOpenCover, pointFinite_realPointFiniteOpenCover,
    not_locallyFinite_realPointFiniteOpenCover⟩
