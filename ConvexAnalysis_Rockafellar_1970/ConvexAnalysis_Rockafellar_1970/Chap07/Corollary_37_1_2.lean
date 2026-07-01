import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_18
import ConvexAnalysis_Rockafellar_1970.Chap07.Corollary_34_2_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Corollary_37_1_1

noncomputable section

universe u v

open SaddleFunction
open scoped Rockafellar

namespace Bifunction

section

variable {R : Type*} {α : Type*}
variable {U : Type u} {UStar : Type*} {X : Type v} {XStar : Type*}
variable [Ring R] [PartialOrder R]
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [AddCommGroup α]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module R UStar]
variable [TopologicalSpace X] [AddCommGroup X] [Module R X]
variable [HasPairing U UStar (WithTopBot α)] [HasPairing X XStar (WithTopBot α)]
variable [SMul R (WithTopBot α)]

local notation "lowerConjugate" =>
  (Bifunction.lowerConjugate : (U → XStar → WithTopBot α) → UStar → X → WithTopBot α)
local notation "upperConjugate" =>
  (Bifunction.upperConjugate : (U → XStar → WithTopBot α) → UStar → X → WithTopBot α)

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 37.1.2 is a pointwise agreement statement for the lower and upper
  conjugates of a closed concave-convex saddle-function.
- `core/canonical`: the existing owners are `lowerConjugate`, `upperConjugate`, `dom₁`, `dom₂`,
  `dom`, `IsClosed`, and the relative-interior notation `ri[R](·)`.
- `bridge/view`: the source phrase "common conjugate-domain factors" is written using the
  Chapter 34 coordinate-domain owners of `lowerConjugate K`.

Domain-style sampling used here:

- `Bifunction.lowerConjugate` and `Bifunction.upperConjugate` from `Definition_37_1_1`;
- `SaddleFunction.IsClosed` and `SaddleFunction.IsConcaveConvex` from `Defn_34_2`;
- `SaddleFunction.dom₁` and `SaddleFunction.dom₂` from `Defn_34_3`;
- `ri[R](·)` from `Chap02.Text_6_8`.

Primitive data vs derived API:

- primitive data: a saddle-function `K : U → XStar → WithTopBot α`;
- primitive hypotheses: `IsConcaveConvex R (lowerConjugate K)`,
  `IsClosed (lowerConjugate K)`, and
  `lowerConjugate K ∼ upperConjugate K`;
- derived API: pointwise equality of `lowerConjugate K` and `upperConjugate K` on the relative
  interior of either coordinate-domain factor, plus the intrinsic-domain reformulation on
  `ri[R](dom (lowerConjugate K))`.

Layer target: `source-facing`.
-/

-- Proof sketch: combine the Chapter 37 equivalence of the two conjugates with the Chapter 34
-- relative-interior agreement theorem for equivalent representatives, applied to the common
-- coordinate domains of the conjugate class.
/-- Core owner form of Corollary 37.1.2: if the lower conjugate of `K` is a closed concave-convex
representative equivalent to the upper conjugate, then the two conjugates agree at `(uStar, x)`
whenever either coordinate lies in the corresponding relative-interior conjugate-domain factor. -/
theorem lowerConjugate_eq_upperConjugate_of_mem_ri_dom₁_or_mem_ri_dom₂
    {K : U → XStar → WithTopBot α}
    (hLower_shape : IsConcaveConvex R (lowerConjugate K))
    (hLower_closed : IsClosed (lowerConjugate K))
    (hLower_equiv_upper : lowerConjugate K ∼ upperConjugate K)
    {uStar : UStar} {x : X}
    (hri :
      uStar ∈ ri[R](dom₁ (lowerConjugate K)) ∨
        x ∈ ri[R](dom₂ (lowerConjugate K))) :
    K _*(uStar, x) = K ^*(uStar, x) := by
  symm
  exact
    SaddleFunction.eq_of_equivalent_of_isConcaveConvex_of_isClosed_of_mem_ri_dom₁_or_mem_ri_dom₂
      hLower_shape hLower_closed hLower_equiv_upper hri

-- Proof sketch: combine the Chapter 37 equivalence of the two conjugates with Corollary 34.2.1's
-- effective-domain invariance on an equivalent closed concave-convex class.
/-- Core owner form of Corollary 37.1.2: equivalent closed concave-convex lower/upper conjugate
representatives have the same Chapter 34 effective domain. -/
theorem dom_upperConjugate_eq_dom_lowerConjugate_of_equivalent_of_isConcaveConvex_of_isClosed
    {K : U → XStar → WithTopBot α}
    (hLower_shape : IsConcaveConvex R (lowerConjugate K))
    (hLower_closed : IsClosed (lowerConjugate K))
    (hLower_equiv_upper : lowerConjugate K ∼ upperConjugate K) :
    dom (upperConjugate K) = dom (lowerConjugate K) := by
  exact
    SaddleFunction.dom_eq_of_equivalent_of_isConcaveConvex_of_isClosed
      hLower_shape hLower_closed hLower_equiv_upper

-- Proof sketch: rewrite `ri[R](dom (lowerConjugate K))` as the product
-- `ri[R](dom₁ (lowerConjugate K)) ×ˢ ri[R](dom₂ (lowerConjugate K))`, then apply the
-- source-facing pointwise corollary at each point of that intrinsic-relative domain.
/-- Intrinsic-domain core owner form: on the relative interior of the common effective domain, the
equivalent closed concave-convex lower/upper conjugate representatives agree pointwise. -/
theorem eqOn_ri_dom_lowerConjugate_upperConjugate_of_equivalent_of_isConcaveConvex_of_isClosed
    {K : U → XStar → WithTopBot α}
    (hLower_shape : IsConcaveConvex R (lowerConjugate K))
    (hLower_closed : IsClosed (lowerConjugate K))
    (hLower_equiv_upper : lowerConjugate K ∼ upperConjugate K) :
    Set.EqOn (Function.uncurry (lowerConjugate K))
      (Function.uncurry (upperConjugate K))
      (ri[R](dom (lowerConjugate K))) := by
  intro p hp
  have hp_fst_snd :
      p.1 ∈ ri[R](dom₁ (lowerConjugate K)) ∧
        p.2 ∈ ri[R](dom₂ (lowerConjugate K)) := by
    simpa [SaddleFunction.dom, ri_prod_eq, Set.mem_prod] using hp
  simpa [Function.uncurry] using
    lowerConjugate_eq_upperConjugate_of_mem_ri_dom₁_or_mem_ri_dom₂
      hLower_shape hLower_closed hLower_equiv_upper (Or.inl hp_fst_snd.1)

end

section

variable [TopologicalSpace U] [AddCommGroup U] [Module R U]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module R XStar]

-- Proof sketch: derive the lower-conjugate closed concave-convex representative data from the
-- source hypotheses on `K` via Corollary 37.1.1, then invoke the core owner theorem above.
/-- Source-facing Corollary 37.1.2 owner form: for a closed concave-convex `K`, the two
conjugates agree at `(uStar, x)` whenever either coordinate lies in the corresponding
relative-interior conjugate-domain factor. -/
theorem lowerConjugate_eq_upperConjugate_of_isConcaveConvex_of_isClosed_of_mem_ri_dom₁_or_mem_ri_dom₂
    {K : U → XStar → WithTopBot α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K)
    {uStar : UStar} {x : X}
    (hri :
      uStar ∈ ri[R](dom₁ (lowerConjugate K)) ∨
        x ∈ ri[R](dom₂ (lowerConjugate K))) :
    K _*(uStar, x) = K ^*(uStar, x) := by
  have hLower_shape : IsConcaveConvex R (lowerConjugate K) :=
    lowerConjugate_isConcaveConvex hK_shape hK_closed
  have hLower_lowerClosed : IsLowerClosed (lowerConjugate K) :=
    lowerConjugate_isLowerClosed hK_shape hK_closed
  have hLower_closed : IsClosed (lowerConjugate K) :=
    SaddleFunction.isClosed_of_isLowerClosed hLower_lowerClosed
  have hLower_equiv_upper : lowerConjugate K ∼ upperConjugate K :=
    lowerConjugate_equivalent_upperConjugate hK_shape hK_closed
  exact
    lowerConjugate_eq_upperConjugate_of_mem_ri_dom₁_or_mem_ri_dom₂
      hLower_shape hLower_closed hLower_equiv_upper hri

-- Proof sketch: derive the conjugate representative hypotheses from Corollary 37.1.1 and
-- delegate to the core effective-domain invariance theorem above.
/-- Source-facing Corollary 37.1.2 owner form: for a closed concave-convex `K`, the lower and
upper conjugates have the same Chapter 34 effective domain. -/
theorem dom_upperConjugate_eq_dom_lowerConjugate_of_isConcaveConvex_of_isClosed
    {K : U → XStar → WithTopBot α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K) :
    dom (upperConjugate K) = dom (lowerConjugate K) := by
  have hLower_shape : IsConcaveConvex R (lowerConjugate K) :=
    lowerConjugate_isConcaveConvex hK_shape hK_closed
  have hLower_lowerClosed : IsLowerClosed (lowerConjugate K) :=
    lowerConjugate_isLowerClosed hK_shape hK_closed
  have hLower_closed : IsClosed (lowerConjugate K) :=
    SaddleFunction.isClosed_of_isLowerClosed hLower_lowerClosed
  have hLower_equiv_upper : lowerConjugate K ∼ upperConjugate K :=
    lowerConjugate_equivalent_upperConjugate hK_shape hK_closed
  exact
    dom_upperConjugate_eq_dom_lowerConjugate_of_equivalent_of_isConcaveConvex_of_isClosed
      hLower_shape hLower_closed hLower_equiv_upper

-- Proof sketch: obtain the source-level lower/upper conjugate representative hypotheses from
-- Corollary 37.1.1 and then apply the intrinsic-domain core owner theorem.
/-- Source-facing intrinsic-domain corollary: for a closed concave-convex `K`, the lower and upper
conjugates agree pointwise on `ri[R](dom (lowerConjugate K))`. -/
theorem eqOn_ri_dom_lowerConjugate_upperConjugate_of_isConcaveConvex_of_isClosed
    {K : U → XStar → WithTopBot α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K) :
    Set.EqOn (Function.uncurry (lowerConjugate K))
      (Function.uncurry (upperConjugate K))
      (ri[R](dom (lowerConjugate K))) := by
  have hLower_shape : IsConcaveConvex R (lowerConjugate K) :=
    lowerConjugate_isConcaveConvex hK_shape hK_closed
  have hLower_lowerClosed : IsLowerClosed (lowerConjugate K) :=
    lowerConjugate_isLowerClosed hK_shape hK_closed
  have hLower_closed : IsClosed (lowerConjugate K) :=
    SaddleFunction.isClosed_of_isLowerClosed hLower_lowerClosed
  have hLower_equiv_upper : lowerConjugate K ∼ upperConjugate K :=
    lowerConjugate_equivalent_upperConjugate hK_shape hK_closed
  exact
    eqOn_ri_dom_lowerConjugate_upperConjugate_of_equivalent_of_isConcaveConvex_of_isClosed
      hLower_shape hLower_closed hLower_equiv_upper

end

end Bifunction
