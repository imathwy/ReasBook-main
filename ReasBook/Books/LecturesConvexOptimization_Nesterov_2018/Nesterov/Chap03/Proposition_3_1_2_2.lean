import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Chap03.Proposition_3_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped SupportFunction

/- Proposition 3.1.2.2 lies in the chapter's support-function / positive-homogeneity domain.

Sampled declarations in this domain:
- `supportFunction` from `Definition_3_9`
- `supportFunction_apply` from `Definition_3_9`
- `supportFunction_smul` from `Proposition_3_10`

Best owner abstraction:
- the existing chapter theorem `supportFunction_smul`

Primitive data:
- a set `Q : Set E`
- a nonemptiness witness `hQ : Q.Nonempty`
- a direction `x : E`
- a bundled nonnegative scalar `τ : NNReal`

Derived API:
- the support-function homogeneity identity itself

Source/core/bridge triage:
- source-facing: the textbook positive-homogeneity statement for support functions
- core/canonical: the already formalized chapter theorem `supportFunction_smul`
- bridge/view: this numbered file is recall-only

This file therefore recalls the existing chapter theorem directly instead of keeping a duplicate
public declaration with the same interface. -/

/- Proposition 3.1.2.2 recalls the chapter theorem `supportFunction_smul`. -/
recall supportFunction_smul
    (Q : Set E) (hQ : Q.Nonempty) (x : E) (τ : NNReal) :
    ξ[Q] (τ • x) = (τ : EReal) * ξ[Q] x
