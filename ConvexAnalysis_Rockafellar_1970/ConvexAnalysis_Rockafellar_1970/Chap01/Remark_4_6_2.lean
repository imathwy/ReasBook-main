import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {𝕜 : Type v} {E : Type u} {β : Type w} {I : Sort*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
variable [Module 𝕜 β] [PosSMulMono 𝕜 β]

/-
Source/core/bridge triage:
- `source-facing`: Remark 4.6.2 has two clauses. First, systems of convex inequalities define
  convex feasible sets. Second, classical inequalities are recovered as Jensen specializations.
- `core/canonical`: the first clause is owned intrinsically by
  `Function.IsConvexOn.convex_setOf_forall_le`, where each member `f i` is only required to be
  convex on the active domain `s`.
- `bridge/view`: the owner theorem is proved in this file by identifying the common feasible set
  with an indexed intersection of relative closed sublevel sets, then mapping
  `ConvexOn 𝕜 s (f i)` to `QuasiconvexOn 𝕜 s (f i)` with `ConvexOn.quasiconvexOn`; the
  global-convex form is then a specialization bridge.
  The Jensen side uses `convexOn_iff_finset_jensen` (and whole-space specialization
  `convexOn_univ_iff_finset_jensen`) from Theorem 4.3.

Abstraction audit for this file:
- Codomain layer: statements are stated for a generic ordered codomain `β`; the chapter's
  `WithTopBot α` setting is recovered by specialization.
- Scalar layer: assumptions stay at the minimal ordered-semiring/module layer required by
  `ConvexOn.quasiconvexOn` and the `ConvexOn`-to-sublevel bridge.
- Intrinsic/relative form: the primary theorem is on a relative domain `s`; ambient form is a
  derived specialization.
-/

namespace Function

omit [AddCommMonoid β] [IsOrderedAddMonoid β] [Module 𝕜 β] [PosSMulMono 𝕜 β] in
/-- Helper for Remark 4.6.2: a family of quasiconvex functions on a convex domain has a convex
common relative closed-sublevel set. -/
private theorem convex_setOf_forall_le_on_of_quasiconvex
    {s : Set E} (hs : Convex 𝕜 s) (f : I → E → β) (μ : I → β)
    (hf : ∀ i, QuasiconvexOn 𝕜 s (f i)) :
    Convex 𝕜 {x ∈ s | ∀ i, f i x ≤ μ i} := by
  by_cases hI : Nonempty I
  · rcases hI with ⟨i0⟩
    -- Rewrite the feasible region as the intersection of the single-inequality slices.
    have hset :
        {x ∈ s | ∀ i, f i x ≤ μ i} =
          ⋂ i, {x ∈ s | f i x ≤ μ i} := by
      ext x
      constructor
      · intro hx
        exact Set.mem_iInter.2 fun i ↦ ⟨hx.1, hx.2 i⟩
      · intro hx
        have hx' : ∀ i, x ∈ {x ∈ s | f i x ≤ μ i} := Set.mem_iInter.1 hx
        exact ⟨(hx' i0).1, fun i ↦ (hx' i).2⟩
    -- Each slice is convex by quasiconvexity, so the indexed intersection is convex.
    rw [hset]
    exact convex_iInter fun i ↦ hf i (μ i)
  · -- With no indices, the universal inequality constraint is vacuous, so the feasible set is `s`.
    have hset : {x ∈ s | ∀ i, f i x ≤ μ i} = s := by
      ext x
      constructor
      · intro hx
        exact hx.1
      · intro hx
        refine ⟨hx, ?_⟩
        intro i
        exact (hI ⟨i⟩).elim
    rw [hset]
    exact hs

end Function

namespace Function.IsConvexOn

/-- Remark 4.6.2 (nonlinear-inequalities side), intrinsic owner form: if each `f i` is convex on
`s`, then the common relative sublevel set `{x ∈ s | ∀ i, f i x ≤ μ i}` is convex. -/
theorem convex_setOf_forall_le
    {s : Set E} (hs : Convex 𝕜 s) (f : I → E → β) (μ : I → β)
    (hf : ∀ i, ConvexOn 𝕜 s (f i)) :
    Convex 𝕜 {x ∈ s | ∀ i, f i x ≤ μ i} := by
  -- Reduce each convex branch to quasiconvexity, then use the family sublevel theorem.
  exact Function.convex_setOf_forall_le_on_of_quasiconvex (s := s) hs f μ fun i =>
    (hf i).quasiconvexOn

end Function.IsConvexOn

namespace Function.IsConvex

/-- Remark 4.6.2 (nonlinear-inequalities side), intrinsic form: if each `f i` is globally convex,
then on any convex domain `s` the common relative sublevel set
`{x ∈ s | ∀ i, f i x ≤ μ i}` is convex. -/
theorem convex_setOf_forall_le_on
    {s : Set E} (hs : Convex 𝕜 s) (f : I → E → β) (μ : I → β)
    (hf : ∀ i, ConvexOn 𝕜 (Set.univ : Set E) (f i)) :
    Convex 𝕜 {x ∈ s | ∀ i, f i x ≤ μ i} := by
  -- Route correction: restrict the whole-space quasiconvexity of each branch to the active
  -- convex domain `s`, then reuse the family-sublevel-set skeleton.
  exact Function.convex_setOf_forall_le_on_of_quasiconvex (s := s) hs f μ fun i =>
    Convex.quasiconvexOn_restrict ((hf i).quasiconvexOn) (Set.subset_univ s) hs

/-- Remark 4.6.2 (nonlinear-inequalities side), ambient specialization of
`convex_setOf_forall_le_on` to `s = Set.univ`. -/
theorem convex_setOf_forall_le
    (f : I → E → β) (μ : I → β)
    (hf : ∀ i, ConvexOn 𝕜 (Set.univ : Set E) (f i)) :
    Convex 𝕜 {x | ∀ i, f i x ≤ μ i} := by
  -- Specialize the relative-domain theorem to `Set.univ`.
  simpa using
    (convex_setOf_forall_le_on
      (s := Set.univ)
      (hs := (convex_univ : Convex 𝕜 (Set.univ : Set E)))
      f μ hf)

end Function.IsConvex

/-
Remark 4.6.2 (classical-inequalities side): the canonical finite Jensen owner theorem is
`convexOn_iff_finset_jensen`, with textbook whole-space form
`convexOn_univ_iff_finset_jensen`; `convexOn_exp` and
`Real.geom_mean_le_arith_mean_weighted` remain standard companion instances.
-/

end
