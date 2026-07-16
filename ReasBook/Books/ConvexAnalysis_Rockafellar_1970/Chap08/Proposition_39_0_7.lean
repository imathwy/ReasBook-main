import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_3_6
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped SetRel Rockafellar

universe u v w

namespace SetRel

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 39.0.7 introduces two operations on convex processes: codomain
  scalar multiplication `(a A)u := a (A u)` and fiberwise Minkowski addition
  `(A + B)u := A u + B u`.
- `core/canonical`: convex processes already live on the relation owner `A : SetRel U X` via
  `A.IsConvexProcess R`, and the chapter already provides the canonical fiberwise-sum owner `+ᶠ`
  on subsets of a product.
- `bridge/view`: codomain scalar multiplication is post-composition with the graph relation of the
  output scaling map `a • ·`, while the source domain formula is the `SetRel.dom` projection of
  the graph-level fiberwise sum.

Primary mathematical domain:
- convex processes as graph relations in ordered semimodule-like settings.

Domain-style sampling used here:
- `SetRel.dom`, `SetRel.image`, and relation membership notation from `Mathlib.Data.Rel`;
- `SetRel.IsConvexProcess` from `Chap08.Definition_39_0_1`;
- `Set.fiberwiseSum`, notation `+ᶠ`, and `Set.mem_fiberwiseSum` from `Chap01.Theorem_3_6`.

Primitive data vs derived API:
  `A.IsConvexProcess R`, post-composition `A ○ (a • ·).graph`, and the chapter
  fiberwise-sum owner `A +ᶠ B`;
- derived API: the two closure theorems for convex processes and the domain identity for the
  fiberwise sum.

Layer target: `source-facing`, stated directly on the canonical `SetRel` owner.
-/

section RightScalarMul

variable {S : Type*} {U : Type v} {X : Type w}
variable [SMul S X]

/-- Source-facing notation for Proposition 39.0.7 (1): `a •ʳ A` denotes codomain scaling of the
process `A` by the scalar `a`. -/
scoped[SetRel] infixr:73 " •ʳ " => fun a A => A ○ Function.graph (a • ·)

-- Proof sketch: unfold `a •ʳ A` as relation composition with a graph relation, then use
-- `SetRel.mem_comp` and `Function.mem_graph`.
/-- Membership in `a •ʳ A` means that the output is a scalar multiple of some output related by
`A` over the same input. -/
@[simp] theorem mem_rightScalarMul_iff {a : S} {A : SetRel U X} {u : U} {x : X} :
    u ~[a •ʳ A] x ↔ ∃ y : X, u ~[A] y ∧ a • y = x := by
  constructor
  · intro hux
    rcases SetRel.mem_comp.mp hux with ⟨y, huy, hyx⟩
    exact ⟨y, huy, Function.mem_graph.mp hyx⟩
  · rintro ⟨y, huy, hyx⟩
    exact SetRel.mem_comp.mpr ⟨y, huy, Function.mem_graph.mpr hyx⟩

end RightScalarMul

section FiberwiseSum

variable {U : Type u} {X : Type v}
variable [Add X]

/-- Relation-surface membership for the chapter fiberwise sum owner. -/
@[simp] theorem mem_fiberwiseSum {A B : SetRel U X} {u : U} {x : X} :
    u ~[A +ᶠ B] x ↔ ∃ x₁ x₂ : X, u ~[A] x₁ ∧ u ~[B] x₂ ∧ x₁ + x₂ = x := by
  simp [Set.mem_fiberwiseSum]

end FiberwiseSum

namespace IsConvexProcess

section RightScalarMul

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [SMul R U]
variable {S : Type*}
variable {X : Type w} [AddCommMonoid X] [SMul R X] [DistribSMul S X] [SMulCommClass S R X]
variable {A : SetRel U X}

-- Proof sketch: `a •ʳ A = A ○ (a • ·).graph`; combine convex-process
-- closure of `A` with closure of post-composition by the graph of codomain scaling.
/-- Proposition 39.0.7 (1): codomain scaling `(a A)u := a (A u)` preserves convex processes.
The source statement is recovered by taking `S = R`. -/
theorem rightScalarMul (hA : A.IsConvexProcess R) (a : S) :
    (a •ʳ A).IsConvexProcess R := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro c p hc hp
    rcases p with ⟨u, x⟩
    change c • u ~[a •ʳ A] c • x
    rcases mem_rightScalarMul_iff.mp hp with ⟨y, hy, hyx⟩
    refine mem_rightScalarMul_iff.mpr ⟨c • y, hA.smul_mem hc hy, ?_⟩
    calc
      a • (c • y) = c • (a • y) := by simpa using (smul_comm a c y)
      _ = c • x := by rw [hyx]
  · rintro ⟨u₁, x₁⟩ hx ⟨u₂, x₂⟩ hy c d hc hd hcd
    rcases mem_rightScalarMul_iff.mp hx with ⟨y₁, hy₁, hyx₁⟩
    rcases mem_rightScalarMul_iff.mp hy with ⟨y₂, hy₂, hyx₂⟩
    change c • u₁ + d • u₂ ~[a •ʳ A] (c • x₁ + d • x₂)
    refine mem_rightScalarMul_iff.mpr ⟨c • y₁ + d • y₂, ?_, ?_⟩
    · simpa [Prod.smul_mk, Prod.mk_add_mk] using hA.convex hy₁ hy₂ hc hd hcd
    · calc
        a • (c • y₁ + d • y₂) = a • (c • y₁) + a • (d • y₂) := smul_add a _ _
        _ = c • (a • y₁) + d • (a • y₂) := by
          rw [smul_comm a c y₁, smul_comm a d y₂]
        _ = c • x₁ + d • x₂ := by rw [hyx₁, hyx₂]
  · exact mem_rightScalarMul_iff.mpr ⟨0, hA.zero_mem, by simp⟩

end RightScalarMul

section FiberwiseSum

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [SMul R U]
variable {X : Type w} [AddCommMonoid X] [DistribSMul R X]
variable {A B : SetRel U X}

-- Proof sketch: combine graph witnesses fiberwise. Addition in each process provides the two
-- witnesses over `u₁ + u₂`, positive scalar closure scales each witness separately, and
-- `Convex.fiberwiseSum` supplies convexity of the graph-level sum.
/-- Proposition 39.0.7 (2): the fiberwise Minkowski sum `(A + B)u := A u + B u` of two convex
processes is again a convex process. -/
theorem fiberwiseSum (hA : A.IsConvexProcess R) (hB : B.IsConvexProcess R) :
    SetRel.IsConvexProcess R (A +ᶠ B) := by
  refine ⟨⟨?_, Convex.fiberwiseSum hA.convex hB.convex⟩, ?_⟩
  · intro c p hc hp
    rcases p with ⟨u, x⟩
    rcases mem_fiberwiseSum.mp hp with ⟨x₁, x₂, hx₁, hx₂, rfl⟩
    exact mem_fiberwiseSum.mpr
      ⟨c • x₁, c • x₂, hA.smul_mem hc hx₁, hB.smul_mem hc hx₂, by simp [smul_add]⟩
  · exact mem_fiberwiseSum.mpr
      ⟨0, 0, hA.zero_mem, hB.zero_mem, by simp⟩

end FiberwiseSum

end IsConvexProcess

section FiberwiseSum

variable {U : Type u} {X : Type v}
variable [Add X]

-- Proof sketch: unfold `SetRel.dom` and `SetRel.mem_fiberwiseSum`; a witness in the fiberwise sum
-- over `u` is exactly a pair of witnesses showing `u ∈ A.dom` and `u ∈ B.dom`, and conversely.
/-- Proposition 39.0.7 (3): the domain of the fiberwise Minkowski sum is the intersection of the
domains of the two processes. -/
theorem dom_fiberwiseSum (A B : SetRel U X) :
    SetRel.dom (A +ᶠ B) = A.dom ∩ B.dom := by
  ext u
  constructor
  · rintro ⟨x, hx⟩
    rcases mem_fiberwiseSum.mp hx with ⟨x₁, x₂, hx₁, hx₂, _⟩
    exact ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
  · rintro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
    refine ⟨x₁ + x₂, ?_⟩
    exact mem_fiberwiseSum.mpr ⟨x₁, x₂, hx₁, hx₂, rfl⟩

end FiberwiseSum

end SetRel
