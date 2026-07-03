import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_4_6_1 (from Chap01) -/
universe u v

section

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E] {I : Sort*} {β : Type v} [LE β]

namespace Function

/- 
Source/core/bridge triage:
- `source-facing`: Corollary 4.6.1 says that the common sublevel set of an arbitrary family of
  convex inequalities on `R^n` is convex; the formal statement should therefore live at the
  primitive sublevel-owner layer rather than at the stronger `EReal` epigraph owner.
- `core/canonical`: the primitive owner for this file is `QuasiconvexOn 𝕜 s` for each member of
  the family on an intrinsic domain `s : Set E`, since quasiconvexity is exactly the assertion
  that all closed sublevel sets on `s` are convex.
- `bridge/view`: the intrinsic feasible set is the indexed intersection
  `⋂ i, {x ∈ s | f i x ≤ α i}`; the source-facing ambient set
  `{x | ∀ i, f i x ≤ α i}` is recovered by specializing `s = Set.univ`.
- Primitive data vs derived API: the family `f`, the levels `α`, and the owner-level
  quasiconvexity hypotheses are primitive; convexity of the common sublevel set is the derived
  theorem.
- Domain-style sampling: this item is guided by the order-level owner `QuasiconvexOn`, the set
  owner `Convex 𝕜`, the source-to-owner bridge `Convex.quasiconvexOn_of_convex_le`, and
  arbitrary-intersection closure `convex_iInter`.
- Layer target: intrinsic/relative first; keep the source-facing ambient statement as a thin
  specialization instead of the primary owner.
-/

/-- Helper for Corollary 4.6.1: the indexed intersection of the individual relative sublevel
sets of a quasiconvex family is convex. -/
theorem convex_iInter_setOf_le_on
    {s : Set E} (f : I → E → β) (α : I → β)
    (hf : ∀ i, QuasiconvexOn 𝕜 s (f i)) :
    Convex 𝕜 (⋂ i, {x ∈ s | f i x ≤ α i}) := by
  -- Route correction: stay with the set-builder sublevel sets from `QuasiconvexOn` directly,
  -- since rewriting through `Set.Iic` would add an unnecessary `Preorder β` assumption.
  exact convex_iInter fun i ↦ hf i (α i)

/-
The next two helpers are set-theoretic identities, so they do not use the additive structure on
`E`; omit that section variable locally to keep the file warning-free.
-/
omit [AddCommMonoid E] in
/-- Helper for Corollary 4.6.1: on a nonempty index type, the intrinsic feasible set is exactly
the indexed intersection of the individual sublevel constraints. -/
theorem setOf_forall_le_on_eq_iInter_of_nonempty
    {s : Set E} [Nonempty I] (f : I → E → β) (α : I → β) :
    {x ∈ s | ∀ i, f i x ≤ α i} =
      ⋂ i, {x ∈ s | f i x ≤ α i} := by
  ext x
  constructor
  · intro hx
    -- A feasible point belongs to every individual sublevel constraint.
    exact Set.mem_iInter.2 fun i ↦ ⟨hx.1, hx.2 i⟩
  · intro hx
    -- Any chosen index recovers the domain membership, while all indices recover the inequalities.
    have hx' : ∀ i, x ∈ {x ∈ s | f i x ≤ α i} := Set.mem_iInter.1 hx
    obtain ⟨i0⟩ := (inferInstance : Nonempty I)
    exact ⟨(hx' i0).1, fun i ↦ (hx' i).2⟩

omit [AddCommMonoid E] in
/-- Helper for Corollary 4.6.1: on an empty index type, the intrinsic feasible set reduces to the
ambient domain because the inequality family is vacuous. -/
theorem setOf_forall_le_on_eq_of_isEmpty
    {s : Set E} [IsEmpty I] (f : I → E → β) (α : I → β) :
    {x ∈ s | ∀ i, f i x ≤ α i} = s := by
  ext x
  -- With no indices, the quantified constraint simplifies away.
  simp

/-- Helper for Corollary 4.6.1: when the index type is nonempty, the intrinsic feasible set
equals the indexed intersection of the individual sublevel constraints, hence is convex. -/
theorem convex_setOf_forall_le_on_of_nonempty
    {s : Set E} [Nonempty I] (f : I → E → β) (α : I → β)
    (hf : ∀ i, QuasiconvexOn 𝕜 s (f i)) :
    Convex 𝕜 {x ∈ s | ∀ i, f i x ≤ α i} := by
  -- Rewrite the feasible region to the indexed-intersection form from the previous lemma.
  rw [setOf_forall_le_on_eq_iInter_of_nonempty (s := s) f α]
  exact convex_iInter_setOf_le_on (s := s) f α hf

/-- Helper for Corollary 4.6.1: for an arbitrary index type, the intrinsic feasible set is
convex on a convex domain. -/
theorem convex_setOf_forall_le_on
    {s : Set E} (hs : Convex 𝕜 s) (f : I → E → β) (α : I → β)
    (hf : ∀ i, QuasiconvexOn 𝕜 s (f i)) :
    Convex 𝕜 {x ∈ s | ∀ i, f i x ≤ α i} := by
  by_cases hI : Nonempty I
  · letI : Nonempty I := hI
    -- The nonempty branch is exactly the intersection argument above.
    exact convex_setOf_forall_le_on_of_nonempty (s := s) f α hf
  · letI : IsEmpty I := not_nonempty_iff.mp hI
    -- After simplifying the empty-index case, we recover the given convex domain.
    simpa [setOf_forall_le_on_eq_of_isEmpty (s := s) f α] using hs

/-- Corollary 4.6.1: if each function `f i` on an ambient `𝕜`-space is quasiconvex, then for
any levels `α i` the common sublevel set `{x | ∀ i, f i x ≤ α i}` is convex. -/
theorem convex_setOf_forall_le
    (f : I → E → β) (α : I → β)
    (hf : ∀ i, QuasiconvexOn 𝕜 Set.univ (f i)) :
    Convex 𝕜 {x | ∀ i, f i x ≤ α i} := by
  -- Specialize the intrinsic-domain theorem to the ambient domain `Set.univ`.
  simpa using
    convex_setOf_forall_le_on (s := Set.univ)
      (hs := (convex_univ : Convex 𝕜 (Set.univ : Set E))) f α hf

end Function

end

/-! ### Remark_4_6_1 (from Chap01) -/
universe u v

/-!
Source/core/bridge triage for this item.

-- `source-facing`: the remark rewrites properness in terms of the domain `{x | f x < ⊤}` and the
  finiteness of the restricted function.
- `core/canonical`: the owner predicate already introduced in this chapter is
  `Function.IsProper` for functions `f : E → WithBotTop α`.
- `bridge/view`: the present item is a pointwise restatement of that owner predicate using the
  textbook's domain language, not a new owner abstraction.

Mathlib/project sampling used here:
- the owner predicate `Function.IsProper` from the preceding item `Definition_4_6`;
- the bridge theorems `Function.isProper_iff` and
  `Function.isProper_iff_nonempty_dom_and_bot_lt` from the same item;
- the chapter owner bridge `mem_effectiveDomain`, which identifies `x ∈ dom(f)` with `f x < ⊤`;
- the order bridges `WithBot.bot_lt_iff_ne_bot` and `WithBotTop.bot_lt_coe`, which encode the
  textbook finiteness side as strict separation from `⊥` and `⊤`.

Primitive data vs derived API:
- primitive data: the owner predicate `Function.IsProper f`;
- derived API: the domain-language restatement `dom(f).Nonempty` together with pointwise
  finite-valuedness of `f` on `dom(f)`.

Layer target: `bridge/view`; this remark is a source-facing restatement of the chapter owner
predicate, not a second properness definition.
-/

section

variable {E : Type u}
variable {α : Type v} [Preorder α]

namespace Function

-- Proof sketch: first keep the primitive owner layer explicit:
-- `f.IsProper ↔ dom(f).Nonempty ∧ ∀ x ∈ dom(f), f x ≠ ⊥`.
-- This is equivalent to the Definition 4.6 owner because `f x = ⊥` forces `x ∈ dom(f)`.
--
-- Then move to the intrinsic order phrase on `dom(f)`:
-- `⊥ < f x`.
-- Finally recover the textbook existential finite-valued phrase by lifting each value away from
-- `⊥` and `⊤`.
/-- Helper for Remark 4.6.1: properness is equivalent to nonempty effective domain and pointwise
exclusion of `⊥` on that domain. This is the primitive domain-restricted owner bridge. -/
theorem isProper_iff_nonempty_dom_and_ne_bot_on_dom
    (f : E → WithBotTop α) :
    f.IsProper ↔ dom(f).Nonempty ∧ ∀ x ∈ dom(f), f x ≠ ⊥ := by
  rw [isProper_iff]
  constructor
  · rintro ⟨hdom, hne_bot⟩
    exact ⟨hdom, fun x _ ↦ hne_bot x⟩
  · rintro ⟨hdom, hne_bot⟩
    refine ⟨hdom, ?_⟩
    intro x
    by_cases hx : x ∈ dom(f)
    · exact hne_bot x hx
    · intro hfx_bot
      exact hx <| mem_effectiveDomain.mpr <| by
        simpa [hfx_bot] using (WithBot.bot_lt_coe (⊤ : WithTop α))

/-- Helper for Remark 4.6.1: properness is equivalent to nonempty effective domain and strict
separation from `⊥` on `dom(f)`. This is the intrinsic order form of finite-valuedness on the
restricted domain. -/
theorem isProper_iff_nonempty_dom_and_bot_lt_on_dom
    (f : E → WithBotTop α) :
    f.IsProper ↔ dom(f).Nonempty ∧ ∀ x ∈ dom(f), ⊥ < f x := by
  rw [isProper_iff_nonempty_dom_and_ne_bot_on_dom]
  constructor
  · rintro ⟨hdom, hne_bot⟩
    refine ⟨hdom, ?_⟩
    intro x hx
    exact (WithBot.bot_lt_iff_ne_bot).2 (hne_bot x hx)
  · rintro ⟨hdom, hbot_lt⟩
    refine ⟨hdom, ?_⟩
    intro x hx
    exact (WithBot.bot_lt_iff_ne_bot).1 (hbot_lt x hx)

/-- Helper for Remark 4.6.1: a `WithBotTop α`-valued function that is finite on the effective
domain and never equal to `⊥` there must actually take a finite `α`-value there. -/
private theorem finite_value_of_mem_dom_and_ne_bot_withBotTop
    {f : E → WithBotTop α} {x : E} (hx : x ∈ dom(f)) (hfx_bot : f x ≠ ⊥) :
    ∃ a : α, f x = a := by
  -- Domain membership removes the `⊤` branch, while the hypothesis removes the `⊥` branch.
  have hfx_top : f x ≠ ⊤ := (mem_effectiveDomain.mp hx).ne
  cases hfx : f x using WithBotTop.rec with
  | bot =>
      exact (hfx_bot hfx).elim
  | coe a =>
      exact ⟨a, rfl⟩
  | top =>
      exact (hfx_top hfx).elim

/-- Helper for Remark 4.6.1: properness is equivalent to nonempty effective domain and
finite-valuedness on `dom(f)`, expressed in existential finite-value form. -/
theorem isProper_iff_nonempty_dom_and_finite_restriction
    (f : E → WithBotTop α) :
    f.IsProper ↔ dom(f).Nonempty ∧ ∀ x ∈ dom(f), ∃ a : α, f x = a := by
  rw [isProper_iff_nonempty_dom_and_bot_lt_on_dom]
  constructor
  · rintro ⟨hdom, hbot_lt⟩
    refine ⟨hdom, ?_⟩
    intro x hx
    -- Route correction: the imported extractor is stated for `WithTopBot`, so we eliminate the
    -- two boundary branches directly in the `WithBotTop` nesting used by this remark.
    have hne_bot : f x ≠ ⊥ := (WithBot.bot_lt_iff_ne_bot).1 (hbot_lt x hx)
    exact finite_value_of_mem_dom_and_ne_bot_withBotTop hx hne_bot
  · rintro ⟨hdom, hfinite⟩
    refine ⟨hdom, ?_⟩
    intro x hx
    rcases hfinite x hx with ⟨a, ha⟩
    -- Convert the finite witness back into strict separation from `⊥` on the domain.
    have hne_bot : f x ≠ ⊥ := by
      intro hfx_bot
      simp [ha] at hfx_bot
    exact (WithBot.bot_lt_iff_ne_bot).2 hne_bot

/-- Remark 4.6.1: `f` is proper exactly when its domain `C = {x | f x < ⊤}` is nonempty and the
restriction of `f` to `C` is finite-valued, i.e. every `f x` with `x ∈ C` is equal to a finite
number. -/
theorem isProper_iff_nonempty_effectiveDomain_and_finite_restriction
    (f : E → WithBotTop α) :
    f.IsProper ↔ dom(f).Nonempty ∧ ∀ x ∈ dom(f), ∃ a : α, f x = a := by
  exact isProper_iff_nonempty_dom_and_finite_restriction (f := f)

end Function

end

/-! ### Remark_4_6_2 (from Chap01) -/
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

/-! ### Definition_4_6 (from Chap01) -/
universe u v

open Set

/-!
Source triage for this item.

- `source-facing`: the item defines properness of a convex function through its epigraph.
- `core/canonical`: the owner abstraction is properness of a codomain-agnostic function
  `f : E → β` when the codomain has ordered-top and bottom structure, using nonemptiness of the
  effective domain `dom(f)` for the finite-point part;
  convexity is separate data supplied elsewhere.
- `bridge/view`: the useful bridge is the standard pointwise reformulation saying that `f` is proper
  exactly when its effective domain is nonempty and it is nowhere `⊥`. The source epigraph
  phrasing is retained as a theorem-level characterization rather than as the primary owner.

Mathlib sampling used here:
- `ConvexOn` in `Mathlib/Analysis/Convex/Function.lean`;
- `ConvexOn.convex_epigraph` in the same file;
- `lowerSemicontinuousOn_iff_isClosed_epigraph` in
  `Mathlib/Topology/Semicontinuity/Basic.lean`.

Project sampling used here:
- `effectiveDomain`, notation `dom(·)`, and `mem_effectiveDomain` from `Definition_4_4`;
- `effectiveDomain_eq_image_fst_epi` from `Definition_4_4`, which already identifies the
  effective domain with the projection of the epigraph;
- the chapter owner pattern `Function.IsConvex` from `Theorem_4_2`, where the reusable owner stays
  concise and source phrasing is exposed through companion theorems.

The book's "contains no vertical lines" is rendered directly on the ambient height type `α`. The
vertical-line bridge uses `NoMinOrder α` (to descend strictly below a finite height) and
`Nonempty α` (to witness finite levels); for the final properness characterization, the latter is
recovered from the hypotheses on either side.
-/

namespace Function

variable {E : Type u} {α : Type v} {β : Type v}

/-- Definition 4.6: a function into a codomain with strict order, top, and bottom is proper exactly when
its effective domain is nonempty and it is nowhere equal to `⊥`. This reuses the chapter owner
`dom(·)` for finite points while keeping the textbook epigraph formulation as derived API in the
`WithTopBot` specialization below. -/
def IsProper [LT β] [Top β] [Bot β] (f : E → β) : Prop :=
  dom(f).Nonempty ∧ ∀ x, f x ≠ ⊥

/-- A function is proper exactly when it has a finite point and is nowhere equal to `⊥`. -/
theorem isProper_iff [LT β] [Top β] [Bot β] (f : E → β) :
    f.IsProper ↔ dom(f).Nonempty ∧ ∀ x, f x ≠ ⊥ :=
  Iff.rfl

/-- With a nonempty effective domain fixed, improperness is exactly existence of a point where the
function takes the value `⊥`. -/
theorem not_isProper_iff_exists_eq_bot_of_nonempty_dom [LT β] [Top β] [Bot β]
    {f : E → β} (hdom : dom(f).Nonempty) :
    ¬ f.IsProper ↔ ∃ x, f x = ⊥ := by
  constructor
  · intro hf_not_proper
    by_contra h_exists_bot
    exact hf_not_proper ⟨hdom, fun x hx_bot ↦ h_exists_bot ⟨x, hx_bot⟩⟩
  · rintro ⟨x, hx_bot⟩ hf_proper
    exact (hf_proper.2 x) hx_bot

/-- Bridge form of properness using strict inequality above `⊥`. -/
theorem isProper_iff_nonempty_dom_and_bot_lt
    [PartialOrder β] [Top β] [OrderBot β] [NoBotOrder β] (f : E → β) :
    f.IsProper ↔ dom(f).Nonempty ∧ ∀ x, ⊥ < f x := by
  rw [isProper_iff]
  constructor
  · rintro ⟨hdom, hne_bot⟩
    -- Rewrite the owner predicate pointwise into strict separation from `⊥`.
    refine ⟨hdom, ?_⟩
    intro x
    simpa using
      ((bot_lt_iff_ne_bot : (⊥ : β) < f x ↔ f x ≠ (⊥ : β)).2 (hne_bot x))
  · rintro ⟨hdom, hbot_lt⟩
    -- Conversely, `⊥ < f x` is exactly the exclusion of the bottom value.
    refine ⟨hdom, ?_⟩
    intro x
    exact
      (bot_lt_iff_ne_bot : (⊥ : β) < f x ↔ f x ≠ (⊥ : β)).1 (hbot_lt x)

/-- A proper function has a nonempty effective domain. -/
theorem IsProper.nonempty_dom [LT β] [Top β] [Bot β] {f : E → β} (hf : f.IsProper) :
    dom(f).Nonempty :=
  hf.1

/-- A proper function is nowhere equal to `⊥`. -/
theorem IsProper.ne_bot [LT β] [Top β] [Bot β] {f : E → β} (hf : f.IsProper) (x : E) :
    f x ≠ ⊥ :=
  hf.2 x

/-- A proper function is everywhere strictly above `⊥` whenever `<` is bottom-separated. -/
theorem IsProper.bot_lt [PartialOrder β] [Top β] [OrderBot β] [NoBotOrder β]
    {f : E → β} (hf : f.IsProper) (x : E) :
    ⊥ < f x :=
  by
    -- The owner already records the only pointwise obstruction to `⊥ < f x`.
    simpa using
      ((bot_lt_iff_ne_bot : (⊥ : β) < f x ↔ f x ≠ (⊥ : β)).2 (hf.ne_bot x))

/-!
The direct `WithTopBot` abbreviation in this mathlib snapshot has no dedicated namespace API.
These local bridges keep the coercion/order manipulations explicit and stable inside Definition 4.6.
-/

/-- Helper for Definition 4.6: finite values of `WithTopBot α` are strictly above `⊥`. -/
private theorem withTopBot_bot_lt_coe {δ : Type*} [LT δ] (a : δ) :
    (⊥ : WithTopBot δ) < (a : WithTopBot δ) := by
  change (((⊥ : WithBot δ) : WithTop (WithBot δ)) <
    (((a : WithBot δ) : WithTop (WithBot δ))))
  exact WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe a)

/-- Helper for Definition 4.6: finite values of `WithTopBot α` are strictly below `⊤`. -/
private theorem withTopBot_coe_lt_top {δ : Type*} [LT δ] (a : δ) :
    (a : WithTopBot δ) < (⊤ : WithTopBot δ) := by
  change (((a : WithBot δ) : WithTop (WithBot δ)) < (⊤ : WithTop (WithBot δ)))
  exact WithTop.coe_lt_top _

/-- Helper for Definition 4.6: finite values of `WithTopBot α` are never `⊥`. -/
private theorem withTopBot_coe_ne_bot {δ : Type*} (a : δ) :
    (a : WithTopBot δ) ≠ (⊥ : WithTopBot δ) := by
  intro h
  change (((a : WithBot δ) : WithTop (WithBot δ)) =
    (((⊥ : WithBot δ) : WithTop (WithBot δ)))) at h
  cases h

/-- Helper for Definition 4.6: on `WithTopBot α`, strict separation from `⊥` is exactly exclusion
of the bottom value. -/
private theorem withTopBot_bot_lt_iff_ne_bot {δ : Type*} [Preorder δ] {x : WithTopBot δ} :
    (⊥ : WithTopBot δ) < x ↔ x ≠ (⊥ : WithTopBot δ) := by
  cases x with
  | none =>
      constructor
      · intro _ h
        cases h
      · intro _
        change (((⊥ : WithBot δ) : WithTop (WithBot δ)) < (⊤ : WithTop (WithBot δ)))
        exact WithTop.coe_lt_top _
  | some y =>
      cases y with
      | bot =>
          constructor
          · intro h
            exact (lt_irrefl (⊥ : WithTopBot δ) h).elim
          · intro h
            exact False.elim (h rfl)
      | coe a =>
          constructor
          · intro _
            exact withTopBot_coe_ne_bot a
          · intro _
            exact withTopBot_bot_lt_coe a

/-- Helper for Definition 4.6: the canonical codomain lift views a finite-valued map as
`WithTopBot`-valued. -/
abbrev toWithTopBot {X : Type*} {δ : Type*} (g : X → δ) : X → WithTopBot δ :=
  fun x ↦ (g x : WithTopBot δ)

/-- Helper for Definition 4.6: `extendBotTop φ` preserves the two boundary points and applies `φ`
to finite values. -/
def extendBotTop {δ ε : Type*} [Top ε] [Bot ε] (φ : δ → ε) : WithTopBot δ → ε
  | ⊥ => ⊥
  | ⊤ => ⊤
  | (a : δ) => φ a

/-- Helper for Definition 4.6: `extendBotTop` sends `⊥` to `⊥`. -/
@[simp] theorem extendBotTop_bot {δ ε : Type*} [Top ε] [Bot ε] (φ : δ → ε) :
    φ.extendBotTop (⊥ : WithTopBot δ) = ⊥ :=
  rfl

/-- Helper for Definition 4.6: `extendBotTop` sends `⊤` to `⊤`. -/
@[simp] theorem extendBotTop_top {δ ε : Type*} [Top ε] [Bot ε] (φ : δ → ε) :
    φ.extendBotTop (⊤ : WithTopBot δ) = ⊤ :=
  rfl

/-- Helper for Definition 4.6: `extendBotTop` agrees with `φ` on finite values. -/
@[simp] theorem extendBotTop_coe {δ ε : Type*} [Top ε] [Bot ε] (φ : δ → ε) (a : δ) :
    φ.extendBotTop (a : WithTopBot δ) = φ a :=
  rfl

/-- Helper for Definition 4.6: a domain point of a `WithTopBot α`-valued function that is not
`⊥` must be represented by a finite value of `α`. -/
theorem finite_value_of_mem_dom_and_ne_bot [Preorder α] {f : E → WithTopBot α} {x : E}
    (hx : x ∈ dom(f)) (hfx_bot : f x ≠ ⊥) :
    ∃ a : α, f x = a := by
  -- Membership in the effective domain excludes `⊤`, so only the finite branch remains.
  have hfx_top : f x ≠ ⊤ := (mem_effectiveDomain.mp hx).ne
  cases hfx : f x with
  | none =>
      exact (hfx_top hfx).elim
  | some y =>
      cases y with
      | bot =>
          exact (hfx_bot hfx).elim
      | coe a =>
          exact ⟨a, rfl⟩

/-- Composing a proper `WithTopBot α`-valued function with a boundary-preserving extension
`φ.extendBotTop` preserves properness when `φ` stays strictly below `⊤` and away from `⊥` on all
finite inputs. -/
theorem IsProper.comp_extendBotTop_of_lt_top_and_ne_bot {γ : Type*} [Preorder α] [Preorder γ]
    {f : E → WithTopBot α} (hf : f.IsProper) (φ : α → WithTopBot γ)
    (hφ_lt_top : ∀ a, φ a < ⊤) (hφ_ne_bot : ∀ a, φ a ≠ ⊥) :
    (φ.extendBotTop ∘ f).IsProper := by
  refine ⟨?_, ?_⟩
  · rcases hf.nonempty_dom with ⟨x, hx⟩
    -- Start from a finite witness in the effective domain of `f`.
    rcases finite_value_of_mem_dom_and_ne_bot (f := f) hx (hf.ne_bot x) with ⟨a, ha⟩
    refine ⟨x, ?_⟩
    simpa [Function.comp, ha] using hφ_lt_top a
  · intro x
    by_cases hfx_top : f x = ⊤
    · -- The extension preserves the top boundary point.
      intro h
      have htop_bot : (⊤ : WithTopBot γ) = (⊥ : WithTopBot γ) := by
        simpa [Function.comp, hfx_top] using h
      cases htop_bot
    · -- Away from `⊤`, properness of `f` lets us descend to a finite branch of `φ`.
      have hx_dom : x ∈ dom(f) := by
        exact mem_effectiveDomain.mpr
          ((WithTop.lt_top_iff_ne_top : f x < (⊤ : WithTopBot α) ↔ f x ≠ ⊤).2 hfx_top)
      rcases finite_value_of_mem_dom_and_ne_bot (f := f) hx_dom (hf.ne_bot x) with ⟨a, ha⟩
      intro h
      have h' : φ a = ⊥ := by
        simpa [Function.comp, ha] using h
      exact hφ_ne_bot a h'

/-- Finite-branch companion of `IsProper.comp_extendBotTop_of_lt_top_and_ne_bot`: composing with
`((φ.toWithTopBot).extendBotTop)` preserves properness. -/
theorem IsProper.comp_extendBotTop {γ : Type*} [Preorder α] [Preorder γ]
    {f : E → WithTopBot α}
    (hf : f.IsProper) (φ : α → γ) :
    (((φ.toWithTopBot).extendBotTop) ∘ f).IsProper := by
  refine hf.comp_extendBotTop_of_lt_top_and_ne_bot (φ := φ.toWithTopBot) ?_ ?_
  · intro a
    -- Finite values stay finite under the canonical codomain lift.
    exact withTopBot_coe_lt_top (φ a)
  · intro a
    exact withTopBot_coe_ne_bot (φ a)

/-- A proper `WithTopBot α`-valued function has nonempty finite codomain layer `α`. -/
private theorem IsProper.nonempty_codomain [Preorder α] {f : E → WithTopBot α}
    (hf : f.IsProper) :
    Nonempty α := by
  rcases hf.nonempty_dom with ⟨x, hx⟩
  -- A proper function has a finite value somewhere in its effective domain.
  rcases finite_value_of_mem_dom_and_ne_bot (f := f) hx (hf.ne_bot x) with ⟨a, ha⟩
  exact ⟨a⟩

/-- A proper `WithTopBot α`-valued function has a nonempty epigraph. -/
private theorem IsProper.epigraph_nonempty [Preorder α] {f : E → WithTopBot α}
    (hf : f.IsProper) :
    (epi f).Nonempty := by
  rcases hf.nonempty_dom with ⟨x, hx⟩
  -- Use a finite point of `f` to produce an explicit epigraph witness.
  rcases finite_value_of_mem_dom_and_ne_bot (f := f) hx (hf.ne_bot x) with ⟨a, ha⟩
  refine ⟨(x, a), ?_⟩
  exact (mem_epi_restrict_iff).2
    ⟨by simp, by simp [ha]⟩

/-- The epigraph of a `WithTopBot α`-valued function is nonempty exactly when its effective domain
is nonempty. -/
private theorem epigraph_nonempty_iff_nonempty_dom [Preorder α] [Nonempty α]
    (f : E → WithTopBot α) :
    (epi f).Nonempty ↔ dom(f).Nonempty := by
  rw [effectiveDomain_eq_image_fst_epi]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.1, ⟨p, hp, rfl⟩⟩
  · rintro ⟨x, ⟨p, hp, rfl⟩⟩
    exact ⟨p, hp⟩

/-- The vertical line above `x` fails to lie in the epigraph exactly when `f x` is strictly above
`⊥`. -/
private theorem no_vertical_line_iff_bot_lt [Preorder α] [Nonempty α] [NoMinOrder α]
    (f : E → WithTopBot α) (x : E) :
    (¬ ∀ r : α, (x, r) ∈ epi f) ↔ ⊥ < f x := by
  constructor
  · intro hnoVertical
    by_cases hfx_top : f x = ⊤
    · rw [hfx_top]
      rcases ‹Nonempty α› with ⟨a⟩
      exact lt_trans (withTopBot_bot_lt_coe a) (withTopBot_coe_lt_top a)
    · by_cases hfx_bot : f x = (⊥ : WithTopBot α)
      · -- If `f x = ⊥`, every finite height lies above it, giving a full vertical line.
        exact False.elim <|
          hnoVertical (fun r ↦ (mem_epi_restrict_iff).2 ⟨by simp, by simp [hfx_bot]⟩)
      · -- Otherwise `f x` is finite, so strict positivity above `⊥` is immediate.
        have hx_dom : x ∈ dom(f) := by
          exact mem_effectiveDomain.mpr
            ((WithTop.lt_top_iff_ne_top : f x < (⊤ : WithTopBot α) ↔ f x ≠ ⊤).2 hfx_top)
        rcases finite_value_of_mem_dom_and_ne_bot (f := f) hx_dom hfx_bot with ⟨a, ha⟩
        simpa [ha] using withTopBot_bot_lt_coe a
  · intro hbot hx
    by_cases hfx_top : f x = ⊤
    · -- A top value cannot lie below any finite height in the epigraph.
      rcases ‹Nonempty α› with ⟨r⟩
      have htop_le : (⊤ : WithTopBot α) ≤ (r : WithTopBot α) := by
        simpa [hfx_top] using (mem_epi_restrict_iff.1 (hx r)).2
      have hr_top : ((r : α) : WithTopBot α) < (⊤ : WithTopBot α) := by
        exact withTopBot_coe_lt_top r
      exact (not_le_of_gt hr_top) htop_le
    · -- In the finite branch, move strictly below the realized height to leave the epigraph.
      have hfx_bot : f x ≠ ⊥ := by
        exact (withTopBot_bot_lt_iff_ne_bot).1 hbot
      have hx_dom : x ∈ dom(f) := by
        exact mem_effectiveDomain.mpr
          ((WithTop.lt_top_iff_ne_top : f x < (⊤ : WithTopBot α) ↔ f x ≠ ⊤).2 hfx_top)
      rcases finite_value_of_mem_dom_and_ne_bot (f := f) hx_dom hfx_bot with ⟨a, ha⟩
      obtain ⟨r, hr⟩ : ∃ r : α, r < a := exists_lt a
      have hxa : (a : WithTopBot α) ≤ r := by
        simpa [ha] using (mem_epi_restrict_iff.1 (hx r)).2
      exact (not_le_of_gt (show ((r : α) : WithTopBot α) < a by simpa using hr)) hxa

/-- The vertical line above `x` fails to lie in the epigraph exactly when `f x` is not `⊥`. -/
private theorem no_vertical_line_iff_ne_bot [Preorder α] [Nonempty α] [NoMinOrder α]
    (f : E → WithTopBot α) (x : E) :
    (¬ ∀ r : α, (x, r) ∈ epi f) ↔ f x ≠ ⊥ := by
  constructor
  · intro hnoVertical hfx_bot
    have hbot : (⊥ : WithTopBot α) < f x := (no_vertical_line_iff_bot_lt f x).1 hnoVertical
    rw [hfx_bot] at hbot
    exact lt_irrefl _ hbot
  · intro hfx_bot
    have hbot : (⊥ : WithTopBot α) < f x := by
      exact (withTopBot_bot_lt_iff_ne_bot).2 hfx_bot
    exact (no_vertical_line_iff_bot_lt f x).2 hbot

/-- Definition 4.6 in epigraph form: a `WithTopBot α`-valued function is proper exactly when its
epigraph is nonempty and contains no full vertical line. -/
theorem isProper_iff_nonempty_epigraph_and_no_vertical_line [Preorder α] [NoMinOrder α]
    (f : E → WithTopBot α) : f.IsProper ↔ (epi f).Nonempty ∧ ∀ x, ¬ ∀ r : α, (x, r) ∈ epi f := by
  rw [isProper_iff]
  constructor
  · rintro ⟨hdom, hne_bot⟩
    have hf : f.IsProper := ⟨hdom, hne_bot⟩
    letI : Nonempty α := hf.nonempty_codomain
    -- Properness supplies both a finite epigraph witness and pointwise exclusion of vertical lines.
    refine ⟨hf.epigraph_nonempty, ?_⟩
    intro x
    exact (no_vertical_line_iff_ne_bot f x).2 (hne_bot x)
  · rintro ⟨hepi, hnoVertical⟩
    rcases hepi with ⟨⟨x₀, r₀⟩, hx₀⟩
    letI : Nonempty α := ⟨r₀⟩
    -- A single epigraph point already gives a finite-domain witness for properness.
    refine ⟨⟨x₀, lt_of_le_of_lt (mem_epi_restrict_iff.1 hx₀).2
      (withTopBot_coe_lt_top r₀)⟩, ?_⟩
    intro x
    exact (no_vertical_line_iff_ne_bot f x).1 (hnoVertical x)

end Function

/-! ### Theorem_4_6 (from Chap01) -/
universe u v w

section ClosedSublevel

variable {𝕜 : Type v} {E : Type u} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
variable [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]

/-!
Source/core/bridge triage:

-- `source-facing`: Theorem 4.6 asserts convexity of the strict and closed sublevel sets of a
  convex function at a fixed height. The source states this on `R^n`; the owner theorem is
  formalized at the intrinsic ordered-module level for `WithTopBot α`-valued functions, with
  `R^n` as a specialization.
- `core/canonical`: the owner abstraction is first relative-domain
  `Function.IsConvexOn 𝕜 s f`, with global `Function.IsConvex 𝕜 f` recovered by the
  specialization `s = Set.univ`; quasiconvexity is similarly exposed first on `s`.
- `bridge/view`: scalar-height closed sublevels are projections of intersections of the canonical
  epigraph with horizontal closed half-spaces, while strict sublevels are then obtained from
  the canonical ordered bridge `QuasiconvexOn.convex_lt`.

Domain-style sampling used here:
- the chapter owner abstractions `Function.IsConvexOn` / `Function.IsConvex` from `Theorem_4_2`;
- `Function.IsConvex.convex_epigraph`;
- `convex_halfSpace_le`;
- `QuasiconvexOn.convex_lt`.

Textual repair note: the source uses the same symbol `x` both for the point variable and for the
level value in `[-∞, +∞]`. The Lean statements below use `μ : WithTopBot α` for the level height.
-/

omit [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] [NoBotOrder α] in
private theorem withTopBot_exists_coe_of_ne_top_ne_bot {x : WithTopBot α}
    (hxtop : x ≠ ⊤) (hxbot : x ≠ ⊥) :
    ∃ a : α, (a : WithTopBot α) = x := by
  cases x with
  | none =>
      exact (hxtop rfl).elim
  | some x' =>
      cases x' with
      | bot =>
          exact (hxbot rfl).elim
      | coe a =>
          exact ⟨a, rfl⟩

omit [NoBotOrder α] in
/-- Primitive finite-height closed-sublevel form: if `f` is convex on `s`, then for each
finite level `r : α`, the relative closed sublevel `{x ∈ s | f x ≤ r}` is convex. -/
theorem Function.IsConvexOn.convex_le_coe {s : Set E} {f : E → WithTopBot α}
    (hf : Function.IsConvexOn 𝕜 s f) (r : α) :
    Convex 𝕜 {x : E | x ∈ s ∧ f x ≤ (r : WithTopBot α)} := by
  have hset :
      {x : E | x ∈ s ∧ f x ≤ (r : WithTopBot α)} =
        Prod.fst '' ((epi[s] f : Set (E × α)) ∩ {p : E × α | p.2 ≤ r}) := by
    ext x
    constructor
    · intro hx
      refine ⟨(x, r), ?_, rfl⟩
      constructor
      · exact (mem_epi_restrict_iff).2 hx
      · simp
    · rintro ⟨⟨x, t⟩, hpt, rfl⟩
      rcases hpt with ⟨hxt, htr⟩
      have hsx : x ∈ s := (mem_epi_restrict_iff.1 hxt).1
      have hfx : f x ≤ (t : WithTopBot α) := (mem_epi_restrict_iff.1 hxt).2
      have htr' : (t : WithTopBot α) ≤ (r : WithTopBot α) := by
        change (((t : WithBot α) : WithTop (WithBot α)) ≤
          ((r : WithBot α) : WithTop (WithBot α)))
        exact WithTop.coe_le_coe.mpr (WithBot.coe_le_coe.mpr (by simpa using htr))
      exact ⟨hsx, le_trans hfx htr'⟩
  rw [hset]
  have hconv_epi : Convex 𝕜 (epi[s] f) := by
    simpa [Function.IsConvexOn] using hf
  simpa using
    (hconv_epi.inter (by
      simpa using convex_halfSpace_le (LinearMap.snd 𝕜 E α).isLinear r)).linear_image
      (LinearMap.fst 𝕜 E α)

/-- Relative owner form of Theorem 4.6 (2): if `f` is convex on `s`, then for any level
`μ ∈ [-∞, +∞]` the relative closed sublevel set `{x ∈ s | f x ≤ μ}` is convex. -/
theorem Function.IsConvexOn.convex_le {s : Set E} {f : E → WithTopBot α}
    (hf : Function.IsConvexOn 𝕜 s f) (hs : Convex 𝕜 s)
    (μ : WithTopBot α) :
    Convex 𝕜 {x : E | x ∈ s ∧ f x ≤ μ} := by
  by_cases hμ_top : μ = ⊤
  · subst hμ_top
    simpa using hs
  by_cases hμ_bot : μ = ⊥
  · subst hμ_bot
    have hset :
        {x : E | x ∈ s ∧ f x ≤ (⊥ : WithTopBot α)} =
          ⋂ r : α, {x : E | x ∈ s ∧ f x ≤ (r : WithTopBot α)} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro hx r
        exact ⟨hx.1, le_trans hx.2 bot_le⟩
      · intro hx
        have hsx : x ∈ s := by
          let r0 : α := Classical.choice (inferInstance : Nonempty α)
          exact (hx r0).1
        refine ⟨hsx, ?_⟩
        by_contra hfx_bot
        have hfx_ne_bot : f x ≠ (⊥ : WithTopBot α) := by
          intro hfx
          exact hfx_bot (hfx ▸ le_rfl)
        have hfx_ne_top : f x ≠ (⊤ : WithTopBot α) := by
          intro hfx
          have htop_le : (⊤ : WithTopBot α) ≤ (0 : α) := by
            simpa [hfx] using (hx 0).2
          have hzero_top : ((0 : α) : WithTopBot α) = ⊤ := top_le_iff.mp htop_le
          simpa using hzero_top.symm
        rcases withTopBot_exists_coe_of_ne_top_ne_bot hfx_ne_top hfx_ne_bot with ⟨a, ha⟩
        rcases exists_not_ge a with ⟨r, hr⟩
        have hxr : (a : WithTopBot α) ≤ (r : WithTopBot α) := by
          simpa [ha] using (hx r).2
        have har : a ≤ r := by
          change (((a : WithBot α) : WithTop (WithBot α)) ≤
            ((r : WithBot α) : WithTop (WithBot α))) at hxr
          exact WithBot.coe_le_coe.mp (WithTop.coe_le_coe.mp hxr)
        exact hr har
    rw [hset]
    exact convex_iInter fun r ↦ hf.convex_le_coe r
  rcases withTopBot_exists_coe_of_ne_top_ne_bot hμ_top hμ_bot with ⟨r, hr⟩
  simpa [hr] using hf.convex_le_coe r

/-- A `WithTopBot α`-valued function convex on `s` is quasiconvex on `s`. -/
theorem Function.IsConvexOn.quasiconvexOn {s : Set E} {f : E → WithTopBot α}
    (hf : Function.IsConvexOn 𝕜 s f) (hs : Convex 𝕜 s) :
    QuasiconvexOn 𝕜 s f := by
  intro r
  exact hf.convex_le hs r

/-- Theorem 4.6 (2): for a convex `WithTopBot α`-valued function on a `𝕜`-module and any level
`μ ∈ [-∞, +∞]`, the closed sublevel set `{x | f x ≤ μ}` is convex. -/
theorem Function.IsConvex.convex_le {f : E → WithTopBot α} (hf : Function.IsConvex 𝕜 f)
    (μ : WithTopBot α) :
    Convex 𝕜 {x : E | f x ≤ μ} := by
  simpa [Function.IsConvex] using
    (Function.IsConvexOn.convex_le
      (𝕜 := 𝕜)
      (s := Set.univ)
      (f := f)
      hf
      (convex_univ : Convex 𝕜 (Set.univ : Set E))
      μ)

/-- A convex `WithTopBot α`-valued function is quasiconvex on its whole ambient space. -/
theorem Function.IsConvex.quasiconvexOn {f : E → WithTopBot α} (hf : Function.IsConvex 𝕜 f) :
    QuasiconvexOn 𝕜 (Set.univ : Set E) f := by
  simpa [Function.IsConvex] using
    (Function.IsConvexOn.quasiconvexOn
      (𝕜 := 𝕜)
      (s := Set.univ)
      (f := f)
      hf
      (convex_univ : Convex 𝕜 (Set.univ : Set E)))

end ClosedSublevel

section StrictSublevel

variable {𝕜 : Type v} {E : Type u} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid α] [LinearOrder α] [IsOrderedAddMonoid α]
variable [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]

/-- Relative owner form of Theorem 4.6 (1): if `f` is convex on `s`, then for any level
`μ ∈ [-∞, +∞]` the relative strict sublevel set `{x ∈ s | f x < μ}` is convex. -/
theorem Function.IsConvexOn.convex_lt {s : Set E} {f : E → WithTopBot α}
    (hf : Function.IsConvexOn 𝕜 s f) (hs : Convex 𝕜 s) (μ : WithTopBot α) :
    Convex 𝕜 {x : E | x ∈ s ∧ f x < μ} := by
  simpa using (hf.quasiconvexOn hs).convex_lt μ

/-- Theorem 4.6 (1): for a convex `WithTopBot α`-valued function on a `𝕜`-module and any level
`μ ∈ [-∞, +∞]`, the strict sublevel set `{x | f x < μ}` is convex. -/
theorem Function.IsConvex.convex_lt {f : E → WithTopBot α} (hf : Function.IsConvex 𝕜 f)
    (μ : WithTopBot α) :
    Convex 𝕜 {x : E | f x < μ} := by
  simpa [Function.IsConvex] using
    (Function.IsConvexOn.convex_lt
      (𝕜 := 𝕜)
      (s := Set.univ)
      (f := f)
      hf
      (convex_univ : Convex 𝕜 (Set.univ : Set E))
      μ)

end StrictSublevel
