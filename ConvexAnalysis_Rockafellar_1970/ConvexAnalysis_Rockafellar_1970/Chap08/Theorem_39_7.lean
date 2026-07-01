import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_14
import ConvexAnalysis_Rockafellar_1970.Chap08.Proposition_39_0_15
import ConvexAnalysis_Rockafellar_1970.Chap08.Proposition_39_0_9
import ConvexAnalysis_Rockafellar_1970.Chap08.Theorem_38_4

noncomputable section

open scoped Rockafellar SetRel

universe u v w z

namespace SetRel

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 39.7 studies the image `Af` of a convex function `f` under a
  supremum-oriented convex process `A`, together with the dual image under the inverse adjoint
  process `A^{*-1}`.
- `core/canonical`: the chapter already owns process fibers through `indicatorFibers ℝ A`,
  bifunction images through `Bifunction.image`, process adjoints through `A∗[XStar, UStar; ℝ]`,
  relation inverse through `A⁻¹`, and closedness of extended-real functions through
  `LowerSemicontinuous` and `cl(·)`.
- `bridge/view`: the textbook `Af` is therefore exposed by the source-facing notation `A ◁ f`,
  backed by the thin owner
  `SetRel.functionImage A f := Bifunction.image (indicatorFibers ℝ A) f`, while
  `A^{*-1} f^*` is the same owner applied to the inverse adjoint relation.

Primary mathematical domain:
- convex processes acting on extended-real convex functions via infimal image.

Domain-style sampling used here:
- `Bifunction.image` from `Chap08.Definition_38_0_4`;
- `functionImage`, `indicatorFibers`, and `dom_indicatorFibers_eq_dom` from
  `Chap08.Proposition_39_0_9`;
- `SetRel.adjoint` / `A∗[XStar, UStar; ℝ]` from `Chap08.Definition_39_0_14`;
- the Chapter 38 image-duality theorem family from `Chap08.Theorem_38_4` and
  `Chap08.Corollary_38_4_1`.

Primitive data vs derived API:
- primitive source data: a convex process `A : SetRel U X` and an extended-real convex function
  `f`;
- primitive source-facing owner reused here: `A ◁ f`, the textbook image `Af`;
- derived API: the function-level conjugacy identity, the dual and primal attainment clauses, the
  lower-semicontinuity/closedness clause, and the adjoint-side closure formula.

Layer target: `source-facing`, stated directly on the Chapter 39 process owners and the Chapter 38
image owner, without a surrogate package for “image data” or “attainment data”.
-/

section Conjugacy

variable {U : Type u} {X : Type v} {UStar : Type w} {XStar : Type z}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [_root_.FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [_root_.FiniteDimensional ℝ X]
variable [Neg UStar]
variable [HasPairing U UStar ℝ] [HasPairing X XStar ℝ]
variable {A : SetRel U X} (hA : A.IsConvexProcess ℝ)
variable {f : U → EReal} (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)

local notation "ri(" C ")" => intrinsicInterior ℝ C
local notation:100 A "∗ᵣ" => (A∗[XStar, UStar; ℝ])
local notation "f⋆" => (convexConjugate f : UStar → EReal)
variable (hri : (riDom(f) ∩ ri(A.dom)).Nonempty)

-- Proof sketch: specialize Theorem 38.4 to the fiber-indicator bifunction `indicatorFibers ℝ A`.
-- `dom_indicatorFibers_eq_dom` identifies the qualification hypothesis with `ri(A.dom)`, and the
-- adjoint-side image `image (Function.swap (indicatorFibers ℝ A)⋆) (f⋆)` is read process-side as
-- `((A∗ᵣ)⁻¹) ◁ f⋆`.
/-- Theorem 39.7 (1): if `f` is proper convex and `ri(dom f)` meets `ri(dom A)`, then the
conjugate of the process image `Af` is the inverse-adjoint image `A^{*-1} f^*`. -/
theorem convexConjugate_functionImage_eq_functionImage_inverse_adjoint_conjugate_of_common_ri_dom
    :
    ((A ◁ f)⋆ : XStar → EReal) =
      ((A∗ᵣ)⁻¹) ◁ f⋆ := sorry

-- Proof sketch: the attainment clause in Theorem 38.4 gives a minimizing dual point for the
-- adjoint-side image of `f⋆`. Reading that image through `((A∗ᵣ)⁻¹) ◁ f⋆` yields a point
-- `u⋆ ∈ A∗ x⋆` with equality `A^{*-1} f^*(x⋆) = f^*(u⋆)`.
/-- Theorem 39.7 (2): under the same qualification, the infimum defining
`A^{*-1} f^*(x⋆)` is attained for every `x⋆`; equivalently, there exists `u⋆ ∈ A^* x⋆` with
`A^{*-1} f^*(x⋆) = f^*(u⋆)`. -/
theorem exists_mem_adjoint_eq_functionImage_inverse_adjoint_conjugate_of_common_ri_dom
    (xStar : XStar) :
    ∃ uStar : UStar,
      xStar ~[A∗ᵣ] uStar ∧
        (((A∗ᵣ)⁻¹) ◁ f⋆) xStar = f⋆ uStar := sorry

end Conjugacy

section ClosedCase

variable {U : Type u} {X : Type v}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [_root_.FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [_root_.FiniteDimensional ℝ X]
variable [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]
variable [HasLinearPairing X X ℝ] [HasContinuousPairing X X ℝ]
variable {A : SetRel U X} (hA : A.IsConvexProcess ℝ) (hA_closed : A.IsClosed)
variable {f : U → EReal} (hf : Function.IsClosedProperConvex ℝ f)

local notation "ri(" C ")" => intrinsicInterior ℝ C
local notation:100 A "∗ᵣ" => (A∗[X, U; ℝ])
local notation "f⋆" => (convexConjugate f : U → EReal)
variable (hri : (riDom(f⋆) ∩ ri(((A∗ᵣ)⁻¹).dom)).Nonempty)

-- Proof sketch: specialize Corollary 38.4.1 to the same fiber-indicator bifunction. The dual
-- qualification is transported from the bifunction owner `dom (Function.swap (F⋆))` to the
-- process owner `((A∗ᵣ)⁻¹).dom`, and the resulting lower semicontinuity statement is the process
-- closedness clause for `Af`.
/-- Theorem 39.7 (3): if `A` and `f` are closed and
`ri(dom f^*)` meets `ri(dom A^{*-1})`, then the process image `Af`, rendered here as `A ◁ f`, is
closed; equivalently, `A ◁ f` is lower semicontinuous. -/
theorem lowerSemicontinuous_functionImage_of_isClosed_of_common_ri_dom_inverse_adjoint
    :
    LowerSemicontinuous (A ◁ f) := sorry

-- Proof sketch: the closed-case attainment theorem for bifunction images specializes to the
-- fiber-indicator bifunction of `A`; rewriting the indicator term through relation membership gives
-- a point `u` with `x ∈ A u` and `Af(x) = f(u)`.
/-- Theorem 39.7 (4): under the same closedness and dual qualification hypotheses, the infimum in
`Af(x)` is attained for every `x`; equivalently, there exists `u` with `x ∈ A u` and
`Af(x) = f(u)`. -/
theorem exists_mem_eq_functionImage_of_isClosed_of_common_ri_dom_inverse_adjoint
    (x : X) :
    ∃ u : U, u ~[A] x ∧ (A ◁ f) x = f u := sorry

-- Proof sketch: the same specialization of Corollary 38.4.1 yields the adjoint-side closure
-- identity for the process image. Translating the generic adjoint-side image into the process owner
-- gives `cl(A^{*-1} f^*)`.
/-- Theorem 39.7 (5): under the same closedness and dual qualification hypotheses,
`(Af)^*` is the closure of `A^{*-1} f^*`. -/
theorem convexConjugate_functionImage_eq_closure_inverse_adjoint_image_of_common_ri_dom
    :
    ((A ◁ f)⋆ : X → EReal) =
      cl(((A∗ᵣ)⁻¹) ◁ f⋆) := sorry

end ClosedCase

end SetRel
