import Mathlib.Analysis.Convex.Basic
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_3_1

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Pointwise

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [DistribSMul 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Text 3.5.4 asserts that if `C` is convex, then `C - C` is convex.
- `core/canonical`: the theorem surface should stay on the standard owner `Convex 𝕜` with
  pointwise set subtraction notation.
- `bridge/view`: mathlib's canonical subtraction-closure theorem `Convex.sub` is ring-layer; this
  source item needs only semiring scalar assumptions, so we expose the semiring bridge theorem
  `Convex.sub_semiring` via the chapter's weak-layer sum theorem `Convex.add_set` plus a local
  weak-layer negation bridge `Convex.neg_set`, and then
  specialize to `C - C`.
- Primitive data vs derived API: convexity of `C` is primitive; convexity of `C - C` is derived.
- Layer target: expose both the semiring-primitive bridge and the source-facing self-difference
  specialization on the canonical owner surface.

Abstraction audit (canonicalize):
- Codomain/ambient layer more concrete than needed? `No`: there is no extra codomain owner here.
- Scalar/ambient structure stronger than needed? `No`: this stays at the weaker semiring action
  layer `[DistribSMul 𝕜 E]`, avoiding both ring assumptions and unnecessary module structure.
- Owner tied to a concrete model? `No`: owner is intrinsic `Convex 𝕜` on sets.
- Ambient-vs-intrinsic topology mismatch? `Not applicable`: no topology in this item.
- Owner name too concrete/long? `No`: public surfaces use short canonical owner names.
- Missing notation surface? `No`: the primary pointwise subtraction notation `C - C` is used.
-/
/-- Helper for Text 3.5.4: negating a convex set preserves convexity at the weak semiring
`DistribSMul` layer. -/
theorem Convex.neg_set {C : Set E} (hC : Convex 𝕜 C) : Convex 𝕜 (-C) := by
  intro x hx y hy a b ha hb hab
  -- Rewrite the target back to membership in `C` so the original convexity hypothesis applies.
  rw [Set.mem_neg] at hx hy ⊢
  -- A convex combination of negatives is the negative of the corresponding convex combination.
  simpa [smul_neg, neg_add, add_comm, add_left_comm, add_assoc] using hC hx hy ha hb hab

/-- Helper for Text 3.5.4: semiring-level subtraction closure for convex sets.

This is the primitive bridge that removes the ring-only restriction of `Convex.sub` on the
canonical owner `Convex 𝕜`. -/
theorem Convex.sub_semiring {C D : Set E} (hC : Convex 𝕜 C) (hD : Convex 𝕜 D) :
    Convex 𝕜 (C - D) := by
  -- Rewrite subtraction as addition with the negated set and reuse the chapter sum theorem.
  simpa [sub_eq_add_neg] using hC.add_set hD.neg_set

/-- Text 3.5.4: if `C` is convex, then the self-difference set `C - C` is convex.

This is the source-facing specialization of the semiring bridge theorem `Convex.sub_semiring`. -/
theorem Convex.sub_self {C : Set E} (hC : Convex 𝕜 C) : Convex 𝕜 (C - C) := by
  -- Specialize the general subtraction-closure lemma to the self-difference case.
  simpa using hC.sub_semiring hC

end
