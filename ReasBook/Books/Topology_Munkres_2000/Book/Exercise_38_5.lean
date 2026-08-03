module

public import Topology_Munkres_2000.Book.Exercise_38_5.Compactifications
public import Topology_Munkres_2000.Book.Example_32_2.Separation
public import Topology_Munkres_2000.Book.Exercise_38_4.Comparison
public import Topology_Munkres_2000.Book.Theorem_29_3
public import Topology_Munkres_2000.Book.Theorem_38_5

public section

universe u v w

namespace Compactification

/-- Helper for Exercise 38.5: a surjective map over a noncompact space from a one-point
compactification forces the target compactification to have one-point remainder. -/
lemma IsOnePoint.ofSurjectiveOver {X : Type u} [TopologicalSpace X] [NoncompactSpace X]
    {C : Compactification.{u, v} X} {D : Compactification.{u, w} X} (hD : D.IsOnePoint)
    {q : D → C} (hq : Function.Surjective q) (hqOver : ∀ x, q (D x) = C x) :
    C.IsOnePoint := by
  classical
  obtain ⟨d, hd⟩ := hD
  refine ⟨q d, Set.Subset.antisymm ?_ ?_⟩
  · -- Every target remainder point comes from the unique source remainder point.
    intro z hz
    obtain ⟨a, ha⟩ := hq z
    have haOutside : a ∈ (Set.range D)ᶜ := by
      intro haRange
      obtain ⟨x, hx⟩ := haRange
      apply hz
      refine ⟨x, ?_⟩
      calc
        C x = q (D x) := (hqOver x).symm
        _ = q a := congrArg q hx
        _ = z := ha
    have had : a = d := by
      have : a ∈ ({d} : Set D) := by
        rw [← hd]
        exact haOutside
      exact Set.mem_singleton_iff.mp this
    rw [Set.mem_singleton_iff, ← ha, had]
  · -- If the source remainder mapped into the embedded copy, the target embedding
    -- would be surjective and would incorrectly make the noncompact source compact.
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    intro hdRange
    obtain ⟨x₀, hx₀⟩ := hdRange
    have hCSurjective : Function.Surjective C := by
      intro z
      obtain ⟨a, ha⟩ := hq z
      by_cases haRange : a ∈ Set.range D
      · obtain ⟨x, hx⟩ := haRange
        refine ⟨x, ?_⟩
        calc
          C x = q (D x) := (hqOver x).symm
          _ = q a := congrArg q hx
          _ = z := ha
      · have haOutside : a ∈ (Set.range D)ᶜ := haRange
        have had : a = d := by
          have : a ∈ ({d} : Set D) := by
            rw [← hd]
            exact haOutside
          exact Set.mem_singleton_iff.mp this
        refine ⟨x₀, ?_⟩
        calc
          C x₀ = q d := hx₀
          _ = q a := congrArg q had.symm
          _ = z := ha
    have hHomeomorph : IsHomeomorph C :=
      isHomeomorph_iff_isEmbedding_surjective.mpr
        ⟨C.isDenseEmbedding.isEmbedding, hCSurjective⟩
    have hCompact : CompactSpace X := (hHomeomorph.homeomorph C).symm.compactSpace
    exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace X)) hCompact

end Compactification

namespace OpenOmegaOne

/-- Helper for Exercise 38.5: a continuous real map has arbitrarily small oscillation on
some final segment of `OpenOmegaOne`. -/
lemma existsTailDistLt (f : OpenOmegaOne → ℝ) (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ α : OpenOmegaOne, ∀ β, α ≤ β → dist (f β) (f α) < ε := by
  classical
  by_contra hTail
  push Not at hTail
  let next : OpenOmegaOne → OpenOmegaOne := fun α ↦ (hTail α).choose
  have hNextLe (α : OpenOmegaOne) : α ≤ next α := (hTail α).choose_spec.1
  have hNextDist (α : OpenOmegaOne) : ε ≤ dist (f (next α)) (f α) :=
    (hTail α).choose_spec.2
  let sequence : ℕ → OpenOmegaOne :=
    fun n ↦ next^[n] (Classical.choice (inferInstance : Nonempty OpenOmegaOne))
  have hSequenceSucc (n : ℕ) : sequence (n + 1) = next (sequence n) := by
    simp only [sequence, Function.iterate_succ_apply']
  have hSequenceStep (n : ℕ) : sequence n ≤ sequence (n + 1) := by
    rw [hSequenceSucc]
    exact hNextLe (sequence n)
  have hSequenceMonotone : Monotone sequence :=
    monotone_nat_of_le_succ hSequenceStep
  obtain ⟨b, hSequenceLimit⟩ := monotoneSequence_tendsto sequence hSequenceMonotone
  have hFunctionLimit : Filter.Tendsto (fun n ↦ f (sequence n)) Filter.atTop (nhds (f b)) :=
    (hf.tendsto b).comp hSequenceLimit
  have hShiftLimit :
      Filter.Tendsto (fun n ↦ f (sequence (n + 1))) Filter.atTop (nhds (f b)) :=
    hFunctionLimit.comp (Filter.tendsto_add_atTop_nat 1)
  have hDistanceLimit :
      Filter.Tendsto (fun n ↦ dist (f (sequence (n + 1))) (f (sequence n)))
        Filter.atTop (nhds 0) := by
    simpa only [dist_self] using hShiftLimit.dist hFunctionLimit
  have hDistanceLower :
      ∀ᶠ n in Filter.atTop, ε ≤ dist (f (sequence (n + 1))) (f (sequence n)) := by
    apply Filter.Eventually.of_forall
    intro n
    rw [hSequenceSucc]
    exact hNextDist (sequence n)
  -- The consecutive distances tend to zero but remain at least `ε`, contradicting positivity.
  have hεNonpositive : ε ≤ 0 := ge_of_tendsto hDistanceLimit hDistanceLower
  exact (not_le_of_gt hε) hεNonpositive

/-- Exercise 38.5 (1): Every continuous real-valued function on the open first-uncountable
ordinal `S_Ω` is constant on a final segment. -/
theorem continuousEventuallyConstant (f : OpenOmegaOne → ℝ) (hf : Continuous f) :
    ∃ α : OpenOmegaOne, ∀ β, α ≤ β → f β = f α := by
  classical
  have hTail : ∀ n : ℕ, ∃ α : OpenOmegaOne,
      ∀ β, α ≤ β → dist (f β) (f α) < 1 / (n + 1 : ℝ) := by
    intro n
    have hDenominatorPositive : 0 < (n + 1 : ℝ) := by
      positivity
    have hRadiusPositive : 0 < 1 / (n + 1 : ℝ) :=
      one_div_pos.mpr hDenominatorPositive
    exact existsTailDistLt f hf hRadiusPositive
  choose α hα using hTail
  obtain ⟨a, ha⟩ := bddAbove_of_countable (Set.range α) (Set.countable_range α)
  refine ⟨a, fun β hβ ↦ ?_⟩
  -- A common upper bound for the countably many epsilon tails makes both values
  -- arbitrarily close to the same comparison value.
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
  have hαa : α n ≤ a := ha (Set.mem_range_self n)
  have hαβ : α n ≤ β := hαa.trans hβ
  have hFirst : dist (f β) (f (α n)) < 1 / (n + 1 : ℝ) := hα n β hαβ
  have hSecond : dist (f (α n)) (f a) < 1 / (n + 1 : ℝ) := by
    simpa only [dist_comm] using hα n a hαa
  apply le_of_lt
  calc
    dist (f β) (f a) ≤ dist (f β) (f (α n)) + dist (f (α n)) (f a) :=
      dist_triangle _ _ _
    _ < ε := by linarith

/-- A continuous real-valued function on `S_Ω` is eventually equal, along `Filter.atTop`,
to one of its values. -/
theorem continuousEventuallyEq (f : OpenOmegaOne → ℝ) (hf : Continuous f) :
    ∃ α : OpenOmegaOne, f =ᶠ[Filter.atTop] fun _ ↦ f α := by
  -- Convert final-segment constancy into the standard `atTop` eventual-equality form.
  obtain ⟨α, hα⟩ := continuousEventuallyConstant f hf
  exact ⟨α, Filter.eventually_atTop.2 ⟨α, fun β hβ ↦ hα β hβ⟩⟩

/-- Helper for Exercise 38.5: eventual equality at `Filter.atTop` gives the limit used by
the one-point compactification of `OpenOmegaOne`. -/
lemma eventuallyEqTendstoCoclosedCompact {Y : Type*} [TopologicalSpace Y]
    {g : OpenOmegaOne → Y} {y : Y} (h : g =ᶠ[Filter.atTop] fun _ ↦ y) :
    Filter.Tendsto g (Filter.coclosedCompact OpenOmegaOne) (nhds y) := by
  letI : NoMaxOrder OpenOmegaOne := ⟨OpenOmegaOne.exists_gt⟩
  letI : OrderBot OpenOmegaOne := {
    bot := CountableOrdinal.zero
    bot_le := fun a ↦ CountableOrdinal.zero_isLeast.2 (Set.mem_univ a) }
  letI : CompactIccSpace OpenOmegaOne := {
    isCompact_Icc := fun {a b} ↦
      (OpenOmegaOne.isCompact_Iic b).of_isClosed_subset isClosed_Icc
        Set.Icc_subset_Iic_self }
  -- In this ordered locally compact space, escaping closed compact sets is exactly
  -- convergence along the final-segment filter.
  rw [Filter.coclosedCompact_eq_cocompact, cocompact_eq_atTop]
  exact h.tendsto

/-- Helper for Exercise 38.5: the canonical one-point compactification extends every bounded
continuous real-valued function on `OpenOmegaOne`. -/
lemma onePointCompactificationExtendsBoundedContinuousReal :
    onePointCompactification.ExtendsBoundedContinuousReal := by
  intro f
  obtain ⟨α, hα⟩ := continuousEventuallyEq f f.continuous
  have hLimit : Filter.Tendsto f (Filter.coclosedCompact OpenOmegaOne) (nhds (f α)) :=
    eventuallyEqTendstoCoclosedCompact hα
  let extension : ContinuousMap (OnePoint OpenOmegaOne) ℝ :=
    OnePoint.continuousMapMk f.toContinuousMap (f α) hLimit
  refine ⟨extension, ?_, ?_⟩
  · -- The extension constructor agrees definitionally with `f` on ordinary points.
    intro x
    rw [onePointCompactification_apply]
    rfl
  · intro g hg
    -- Two continuous extensions agree on the dense copy of `OpenOmegaOne`.
    apply ContinuousMap.ext
    apply congrFun
    apply Continuous.ext_on OnePoint.denseRange_coe g.continuous extension.continuous
    rintro _ ⟨x, rfl⟩
    rw [← onePointCompactification_apply x, hg x]
    rfl

/-- Exercise 38.5 (2): The one-point compactification of `S_Ω` and its Stone–Čech
compactification are equivalent over `S_Ω`. -/
theorem onePointEquivalentStoneCech :
    Compactification.Equivalent onePointCompactification stoneCechCompactification := by
  -- Both compactifications have the same bounded-real extension universal property.
  exact Compactification.equivalent_of_extendsBoundedContinuousReal
    onePointCompactification stoneCechCompactification
    onePointCompactificationExtendsBoundedContinuousReal
    (Compactification.stoneCech_extendsBoundedContinuousReal OpenOmegaOne)

/-- Helper for Exercise 38.5: the canonical one-point compactification has singleton
remainder. -/
lemma onePointCompactificationIsOnePoint : onePointCompactification.IsOnePoint := by
  refine ⟨OnePoint.infty, ?_⟩
  have hRange : Set.range onePointCompactification =
      Set.range ((↑) : OpenOmegaOne → OnePoint OpenOmegaOne) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, (onePointCompactification_apply x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, onePointCompactification_apply x⟩
  -- Rewrite only the embedding range, leaving the compactification constructor opaque.
  exact (congrArg (fun s : Set (OnePoint OpenOmegaOne) ↦ sᶜ) hRange).trans
    OnePoint.compl_range_coe

/-- Exercise 38.5 (3): Every compactification of `S_Ω` is equivalent over `S_Ω` to its
one-point compactification. -/
theorem compactificationEquivalentOnePoint (C : Compactification OpenOmegaOne) :
    Compactification.Equivalent C onePointCompactification := by
  classical
  obtain ⟨e⟩ := onePointEquivalentStoneCech
  let q : onePointCompactification → C :=
    fun y ↦ Compactification.stoneCechComparison C (e y)
  have hqSurjective : Function.Surjective q :=
    (Compactification.stoneCechComparison_surjective C).comp e.toHomeomorph.surjective
  have hqOver (x : OpenOmegaOne) : q (onePointCompactification x) = C x := by
    dsimp only [q]
    rw [e.commutes x, Compactification.stoneCechComparison_apply]
  -- The Stone–Čech comparison is a quotient of a one-point compactification, so `C`
  -- itself has one-point remainder.
  have hCOnePoint : C.IsOnePoint :=
    Compactification.IsOnePoint.ofSurjectiveOver onePointCompactificationIsOnePoint
      hqSurjective hqOver
  apply (Compactification.equivalent_iff C onePointCompactification).2
  exact Compactification.IsOnePoint.equivalent hCOnePoint onePointCompactificationIsOnePoint

end OpenOmegaOne

end
