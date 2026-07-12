import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap08.Proposition_38_5_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Proposition_38_7_5

noncomputable section

open scoped Rockafellar

universe u v w z

namespace Bifunction

section Assoc

variable {U : Type u} {X : Type v} {Y : Type w} {Z : Type z}

-- Proof sketch: expand both sides with `comp_apply_eq_iInf`. Both expressions are the same
-- iterated infimum over the intermediate variables, so the equality follows by extensionality.
/-- The Chapter 38 product of `EReal`-valued bifunctions is associative. -/
theorem comp_assoc
    (F : U → X → EReal) (G : X → Y → EReal) (H : Y → Z → EReal) :
    comp H (comp G F) = comp (comp H G) F := sorry

end Assoc

end Bifunction

namespace Rockafellar

scoped instance endobifunctionMul
    {U : Type u} :
    Mul (U → U → EReal) where
  mul F G := Bifunction.comp F G

scoped instance endobifunctionSemigroup
    {U : Type u} :
    Semigroup (U → U → EReal) where
  mul_assoc F G H := by
    simpa using (Bifunction.comp_assoc H G F).symm

end Rockafellar

namespace Bifunction

section Mul

variable {U : Type u}

/-- Endobifunction multiplication is the Chapter 38 product `F * G = comp F G`. -/
@[simp] theorem mul_apply (F G : U → U → EReal) (u x : U) :
    (F * G) u x = comp F G u x :=
  rfl

end Mul

section Semigroup

variable {U : Type u}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 38.7.6 studies the Chapter 38 product on closed-convex co-finite
  bifunction endomorphisms and records that, under a noncommuting pair of linear endomorphisms,
  this semigroup is noncommutative.
- `core/canonical`: the owner abstractions are `Bifunction.comp`, the `Rockafellar`-scoped
  semigroup structure on actual endobifunctions `U → U → EReal` induced by `comp`, mathlib's
  `Subsemigroup`, and the regularity owners `Bifunction.IsClosedConvex` and
  `Bifunction.IsCofinite`.
- `bridge/view`: the final noncommutativity witness passes through singleton-graph indicator
  bifunctions of linear maps and the bridge theorem `comp_graphIndicator_eq_graphIndicator_comp`.

Primary mathematical domain:
- semigroup structure on closed-convex co-finite endobifunctions under Chapter 38 composition.

Domain-style sampling used here:
- `Bifunction.comp` from `Theorem_38_5`;
- `Subsemigroup` from mathlib's algebraic subobject API;
- `Bifunction.IsClosedConvex` from `Chap07.Defn_34_2`;
- `Bifunction.isClosedConvex_comp_of_common_riDom_adjoint_inverse` from `Proposition_38_5_1`;
- `Bifunction.isCofinite_comp_of_isClosedConvex_of_isCofinite` from `Proposition_38_7_5`.

Primitive data vs derived API:
- primitive source data: endobifunctions `F : U → U → EReal`;
- primitive owner operation: `comp`;
- derived API: the `Rockafellar`-scoped multiplication surface `F * G = comp F G`, together with
  the canonical `Subsemigroup` cut out by `IsClosedConvex` and `IsCofinite`.

Layer target: `source-facing`.
-/

variable (U)

-- Proof sketch: Proposition 38.7.5 supplies co-finiteness of the Chapter 38 product under the
-- closed-convex/co-finite owner hypotheses, and Proposition 38.5.1 supplies closed-convexity of
-- the same product after deriving the common-`riDom` qualification from those hypotheses.
/-- The closed-convex co-finite endobifunctions form the canonical `Subsemigroup` of
`U → U → EReal` cut out by the Chapter 38 product and the Chapter 38.5/38.7 closure theorems. -/
def closedConvexCofinite
    (U : Type u) [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
    [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ] :
    Subsemigroup (U → U → EReal) where
  carrier := {F | IsClosedConvex F ∧ IsCofinite U U F}
  mul_mem' hF hG := by
    sorry

@[simp] theorem mem_closedConvexCofinite {F : U → U → EReal} :
    F ∈ closedConvexCofinite U ↔ IsClosedConvex F ∧ IsCofinite U U F :=
  Iff.rfl

-- Proof sketch: choose noncommuting linear endomorphisms `A` and `B`, represent them by their
-- singleton-graph indicator bifunctions, and use Proposition 38.4.3 to identify the Chapter 38
-- products with the graph indicators of `B.comp A` and `A.comp B`.
/-- Proposition 38.7.6: if `U` admits two noncommuting linear endomorphisms, then the
closed-convex co-finite endobifunctions from `U` to itself form a noncommutative subsemigroup of
`U → U → EReal` under the Chapter 38 product. Noncommutativity is expressed by two elements of
`closedConvexCofinite U` whose products in opposite orders are unequal. -/
theorem exists_noncommuting_closedConvexCofinite_of_exists_noncommuting_linearMap
    (hlin : ∃ A B : U →ₗ[ℝ] U, B.comp A ≠ A.comp B) :
    ∃ F G : closedConvexCofinite U, F * G ≠ G * F := sorry

end Semigroup

end Bifunction
