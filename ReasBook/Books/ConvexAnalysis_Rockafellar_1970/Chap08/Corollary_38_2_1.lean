import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_24
import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_31_0_8
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2
import ConvexAnalysis_Rockafellar_1970.Chap08.Theorem_38_1

noncomputable section

open scoped Rockafellar

namespace Bifunction

section

universe u v

variable {U : Type u} {X : Type v}

local notation "ri(" C ")" => intrinsicInterior ℝ C

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 38.2.1 is about the bifunction infimal convolution `F₁ D F₂`, the
  slice-domain `dom F`, the properness owner `IsProper`, and the adjoint-side closure formula.
- `core/canonical`: the chapter owners already present upstream are `Bifunction.infimalConvolution`
  with notation `D`, `Bifunction.dom`, `Bifunction.IsProper`, `Bifunction.adjoint`,
  `Bifunction.IsClosedConvex`, and `Bifunction.closure`.
- `bridge/view`: the only remaining bridge is the relation between that source-facing bifunction
  owner and the Chapter 2 one-variable closure owner `cl(·)` on ordinary graph functions.

Domain-style sampling used here:
- `Bifunction.infimalConvolution`, notation `D`, and `Bifunction.dom` from `Chap08.Theorem_38_1`;
- `Bifunction.IsProper` from `Chap08.Theorem_38_1`;
- `Bifunction.adjoint` from `Chap06.Lemma_31_0_8`;
- `Bifunction.closure` from `Chap06.Definition_6_29_24`;
- `Bifunction.IsClosedConvex` from `Chap07.Defn_34_2`;
- `dom(·)`, `riDom(·)`, and `cl(·)` on ordinary graph functions from earlier chapters.

Primitive data vs derived API:
- primitive owner data reused from the chapter: `F₁`, `F₂`, `dom F`, `IsProper F`, `F₁ D F₂`,
  `adjoint F`, and `closure F`;
- derived API: the closed-convex clause for `F₁ D F₂` and the adjoint-side closure identity.

Layer target:
- the corollary remains `source-facing` on the chapter's bifunction owners `dom`, `D`, and
  `IsProper`, `adjoint`;
- the closure on the right-hand side is `bridge/view`, written through the source-facing owner
  `closure`.
-/

section Closedness

variable [TopologicalSpace U] [AddCommGroup U] [Module ℝ U]
variable [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]

-- Proof sketch: the graph function of `F₁ D F₂` is the Chapter 1 partial infimal convolution of
-- the two graph functions, and the common-relative-interior hypothesis is already expressed on the
-- Chapter 38 slice-domain owner `dom`. Apply the corresponding closed-convex infimal-convolution
-- theorem to the graph functions and read the result back through `Bifunction.IsClosedConvex`.
/-- Corollary 38.2.1 (1): if closed convex bifunctions `F₁` and `F₂` have a common point in
`ri (dom F₁) ∩ ri (dom F₂)`, then `F₁ D F₂` is closed convex. The separate properness hypotheses
are redundant here, since the common-relative-interior assumption already forces both slice-domains
to be nonempty. -/
theorem isClosedConvex_infimalConvolution_of_common_riDom
    {F₁ F₂ : U → X → EReal}
    (hF₁ : IsClosedConvex F₁) (hF₂ : IsClosedConvex F₂)
    (hri : (ri(dom F₁) ∩ ri(dom F₂)).Nonempty) :
    IsClosedConvex (F₁ D F₂) := by
  sorry

end Closedness

section Adjoint

variable {UStar : Type u} {XStar : Type v}
variable [TopologicalSpace U] [AddCommGroup U] [Module ℝ U]
variable [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Neg UStar]
variable [TopologicalSpace XStar]
variable [HasPairing U UStar ℝ] [HasPairing X XStar ℝ]

-- Proof sketch: identify the pairing-based adjoint of `F₁ D F₂` with the closure of the
-- adjoint-side infimal convolution, using the same common-relative-interior hypothesis on
-- `dom F₁` and `dom F₂`. The right-hand side is expressed through the source-facing closure owner.
/-- Corollary 38.2.1 (2): under the same common-relative-interior hypothesis,
`(F₁ D F₂)^* = cl (F₁^* D F₂^*)`, rendered by `adjoint`, `D`, and `closure`. -/
theorem
    adjointFunction_infimalConvolution_eq_closure_adjoint_infimalConvolution_of_common_riDom
    {F₁ F₂ : U → X → EReal}
    (hF₁ : IsClosedConvex F₁) (hF₂ : IsClosedConvex F₂)
    (hri : (ri(dom F₁) ∩ ri(dom F₂)).Nonempty) :
    adjoint XStar UStar (F₁ D F₂) =
      closure
        ((adjoint XStar UStar F₁) D
          (adjoint XStar UStar F₂)) := by
  sorry

end Adjoint

end

end Bifunction
