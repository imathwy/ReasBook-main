import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
