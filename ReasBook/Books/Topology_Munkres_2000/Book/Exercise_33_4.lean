module

public import Topology_Munkres_2000.Book.Definition_33_4.ZeroSet
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.UrysohnsLemma

public section

open Set

universe u

namespace ContinuousMap.VanishesPreciselyOn

/-- Helper for Exercise 33.4: the precise zero set of an interval-valued continuous map is
closed. -/
theorem isClosed {X : Type u} [TopologicalSpace X] {f : C(X, Set.Icc (0 : ℝ) 1)}
    {A : Set X} (h : f.VanishesPreciselyOn A) : IsClosed A := by
  -- Rewrite `A` as the preimage of the closed singleton `{0}`.
  rw [← h.zeroSet_eq]
  exact isClosed_singleton.preimage (continuous_subtype_val.comp f.continuous)

/-- Helper for Exercise 33.4: the precise zero set of an interval-valued continuous map is `Gδ`. -/
theorem isGδ {X : Type u} [TopologicalSpace X] {f : C(X, Set.Icc (0 : ℝ) 1)}
    {A : Set X} (h : f.VanishesPreciselyOn A) : IsGδ A := by
  -- Rewrite `A` as the preimage of the `Gδ` singleton `{0}`.
  rw [← h.zeroSet_eq]
  exact (IsGδ.singleton (0 : ℝ)).preimage (continuous_subtype_val.comp f.continuous)

end ContinuousMap.VanishesPreciselyOn

namespace IsClosed

/-- Helper for Exercise 33.4: a closed `Gδ` set in a normal space is the zero set of a
continuous real-valued function whose values lie in `Set.Icc 0 1`. -/
theorem exists_continuous_zeroSet_eq_of_isGδ {X : Type u} [TopologicalSpace X]
    [NormalSpace X] {A : Set X} (hA : IsClosed A) (hG : IsGδ A) :
    ∃ g : C(X, ℝ), A = g ⁻¹' {(0 : ℝ)} ∧ ∀ x, g x ∈ Set.Icc (0 : ℝ) 1 := by
  -- Express `A` as a countable intersection of open neighborhoods.
  obtain ⟨U, hUOpen, hAInter⟩ := hG.eq_iInter_nat
  have hDisjoint (n : ℕ) : Disjoint A (U n)ᶜ := by
    apply LE.le.disjoint_compl_right
    grw [hAInter, iInter_subset]
  -- Separate `A` from each complementary closed set by an interval-valued real function.
  choose f hfA hfCompl hfRange using fun n ↦
    exists_continuous_zero_one_of_isClosed hA (hUOpen n).isClosed_compl (hDisjoint n)
  have hBound (x : X) (n : ℕ) : ‖(f n) x * (1 / 2 / 2 ^ n)‖ ≤ 1 / 2 / 2 ^ n := by
    simp [abs_of_nonneg (hfRange n x).1, (hfRange n x).2]
  have hSummable (x : X) : Summable fun n ↦ f n x * (1 / 2 / 2 ^ n) :=
    (summable_geometric_two' 1).of_norm_bounded fun n ↦ hBound x n
  have hContinuous : Continuous fun x ↦ ∑' n, f n x * (1 / 2 / 2 ^ n) :=
    continuous_tsum (fun n ↦ by fun_prop) (summable_geometric_two' 1) fun n x ↦ hBound x n
  let g : C(X, ℝ) := ⟨fun x ↦ ∑' n, f n x * (1 / 2 / 2 ^ n), hContinuous⟩
  refine ⟨g, ?_, fun x ↦ ⟨?_, ?_⟩⟩
  · -- The sum vanishes on `A`, while outside `A` one separator contributes positively.
    ext x
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · suffices ∀ n, f n x = 0 by simp [g, this]
      exact fun n ↦ hfA n hx
    · contrapose hx
      apply ne_of_gt
      obtain ⟨i, hi⟩ := mem_iUnion.1 <| compl_iInter _ ▸ mem_compl (hAInter ▸ hx)
      calc
        0 < 1 / 2 / 2 ^ i := by positivity
        _ = f i x * (1 / 2 / 2 ^ i) := by simp [hfCompl i hi]
        _ ≤ ∑' n, f n x * (1 / 2 / 2 ^ n) :=
          (hSummable x).le_tsum i fun j hj ↦ by positivity [(hfRange j x).1]
  · -- Every summand is nonnegative.
    exact tsum_nonneg fun n ↦ by simp [(hfRange n x).1]
  · -- Compare termwise with the geometric series of total mass one.
    calc
      g x = ∑' n, f n x * (1 / 2 / 2 ^ n) := by rfl
      _ ≤ ∑' n, 1 / 2 / 2 ^ n :=
        (hSummable x).tsum_le_tsum (fun n ↦ by simp [(hfRange n x).2])
          (summable_geometric_two' 1)
      _ = 1 := tsum_geometric_two' 1

end IsClosed

/-- Exercise 33.4: In a normal space, a subset `A` is closed and `Gδ` if and only if
there is a continuous map to `Set.Icc 0 1` that vanishes precisely on `A`. Here
`T4Space` expresses the book's convention for a normal space. -/
theorem ContinuousMap.exists_vanishesPreciselyOn_iff_closed_isGδ
    {X : Type u} [TopologicalSpace X] [T4Space X] (A : Set X) :
    (∃ f : C(X, Set.Icc (0 : ℝ) 1), f.VanishesPreciselyOn A) ↔
      IsClosed A ∧ IsGδ A := by
  constructor
  · -- Exact zero sets are closed and `Gδ` by the two companion lemmas.
    rintro ⟨f, hf⟩
    exact ⟨hf.isClosed, hf.isGδ⟩
  · -- Build a real-valued zero-set function, then restrict its codomain to the unit interval.
    rintro ⟨hA, hG⟩
    obtain ⟨g, hZero, hRange⟩ := hA.exists_continuous_zeroSet_eq_of_isGδ hG
    have hContinuous : Continuous fun x ↦ (⟨g x, hRange x⟩ : Set.Icc (0 : ℝ) 1) :=
      g.continuous.subtype_mk _
    let f : C(X, Set.Icc (0 : ℝ) 1) := ⟨fun x ↦ ⟨g x, hRange x⟩, hContinuous⟩
    refine ⟨f, (ContinuousMap.vanishesPreciselyOn_iff f A).2 fun x ↦ ?_⟩
    -- The codomain restriction does not change the real value or the zero set.
    simpa [f, preimage] using (Set.ext_iff.mp hZero x).symm
