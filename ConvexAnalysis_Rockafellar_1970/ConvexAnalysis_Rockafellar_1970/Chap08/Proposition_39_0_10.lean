import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped SetRel

universe u v w z

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 39.0.10 says the product of convex processes is again a convex
  process, and identifies the inverse of that product with the product of the inverses.
- `core/canonical`: the project owner for convex processes is `A.IsConvexProcess R` on
  `A : SetRel U X`, while the product `BA` is exactly the canonical relation composition `A ○ B`.
- `bridge/view`: the inverse clause is already the exact canonical `SetRel` theorem
  `SetRel.inv_comp`, so only the convex-process closure under composition needs a new declaration
  here.

Domain-style sampling used here:
- `SetRel.comp`, `SetRel.mem_comp`, and `SetRel.inv_comp` from `Mathlib.Data.Rel`;
- `Set.IsConvexCone` from `Chap01.Definition_2_5_10`;
- `SetRel.IsConvexProcess` and `SetRel.IsConvexProcess.isConvexCone` from
  `Chap08.Definition_39_0_1`.

Primitive data vs derived API:
- primitive owners: relations `A : SetRel U X` and `B : SetRel X Y`;
- primitive operation: the canonical composition `A ○ B`;
- primitive closure theorem: `SetRel.isConvexCone_comp` on graph owners;
- derived API here: closure of `IsConvexProcess R` under that composition.

Layer target: `source-facing`, stated directly on the canonical `SetRel` owner.
-/

namespace SetRel

section

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [SMul R U]
variable {X : Type w} [AddCommMonoid X] [SMul R X]
variable {Y : Type z} [AddCommMonoid Y] [SMul R Y]
variable {A : SetRel U X} {B : SetRel X Y}

-- Proof sketch: this is the graph-level convex-cone closure under relation composition. For
-- positive-scalar closure, scale the middle witness in `SetRel.mem_comp`; for convexity, combine
-- two middle witnesses by the same affine combination and use convexity of each graph.
/-- Primitive relation owner: composition preserves graph convex-cone structure on relations. -/
theorem isConvexCone_comp (hA : Set.IsConvexCone R A) (hB : Set.IsConvexCone R B) :
    Set.IsConvexCone R (A ○ B) := by
  refine ⟨?_, ?_⟩
  · intro c p hc hp
    rcases SetRel.mem_comp.mp hp with ⟨x, hAx, hBx⟩
    exact SetRel.mem_comp.mpr ⟨c • x, hA.isCone.smul_mem hc hAx, hB.isCone.smul_mem hc hBx⟩
  · intro p hp q hq a b ha hb hab
    rcases SetRel.mem_comp.mp hp with ⟨x₁, hAx₁, hBx₁⟩
    rcases SetRel.mem_comp.mp hq with ⟨x₂, hAx₂, hBx₂⟩
    refine SetRel.mem_comp.mpr ?_
    exact ⟨a • x₁ + b • x₂, hA.convex hAx₁ hAx₂ ha hb hab, hB.convex hBx₁ hBx₂ ha hb hab⟩

end

end SetRel

namespace SetRel.IsConvexProcess

section

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [SMul R U]
variable {X : Type w} [AddCommMonoid X] [SMul R X]
variable {Y : Type z} [AddCommMonoid Y] [SMul R Y]
variable {A : SetRel U X} {B : SetRel X Y}

-- Proof sketch: first compose the graph convex-cone owners via `SetRel.isConvexCone_comp`, then
-- provide the origin witness in the composite graph using the origin witnesses from the factors.
/-- Proposition 39.0.10: the product of two convex processes is again a convex process. In the
canonical `SetRel` owner, the textbook product `(BA)` is the relation composition `A ○ B`. -/
theorem comp (hA : A.IsConvexProcess R) (hB : B.IsConvexProcess R) :
    (A ○ B).IsConvexProcess R := by
  refine ⟨SetRel.isConvexCone_comp hA.isConvexCone hB.isConvexCone, ?_⟩
  · exact SetRel.mem_comp.mpr ⟨0, hA.zero_mem, hB.zero_mem⟩

end

end SetRel.IsConvexProcess

namespace SetRel

section

variable {U : Type v} {X : Type w} {Y : Type z}
variable {A : SetRel U X} {B : SetRel X Y}

/- Proposition 39.0.10 (inverse clause): with the textbook convention `(BA) = A ○ B`, the
canonical relation identity `SetRel.inv_comp` is exactly `(BA)⁻¹ = A⁻¹B⁻¹`. -/
recall SetRel.inv_comp

end

end SetRel
