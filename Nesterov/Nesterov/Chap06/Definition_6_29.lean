import Mathlib.Tactic.Recall
import Nesterov.Chap06.Definition_6_31

/- Definition 6.29 lies in the chapter's prox-function / prox-center domain.

Sampled owner-style declarations:
- `IsProxFunction` in `Definition_6_31`, the chapter's canonical owner for the
  prox-function hypothesis on `d`;
- `IsProxCenter` in `Definition_6_31`, the chapter's canonical owner for the
  normalized prox-center condition;
- project `StrongConvexOnWith`, the chapter owner reused by `IsProxFunction`;
- mathlib `IsMinOn`, the ambient minimizer owner reused by `IsProxCenter`.

Best owner abstraction:
- source-facing: the prox-function condition on `Q` and the normalized
  prox-center condition at `x₀`;
- core/canonical: `IsProxFunction Q d` and `IsProxCenter Q d x₀`;
- bridge/view: this numbered item is a recall-only surface for those canonical
  owners rather than a second pair of duplicate local definitions.

Primitive data:
- the norm-like seminorm `p`, the feasible set `Q`, the prox-function
  candidate `d`, and the candidate center `x₀`.

Derived API:
- `IsProxFunction.continuousOn` and `IsProxFunction.strongConvexOnWith`;
- `IsProxCenter.mem`, `IsProxCenter.isMinOn`, and
  `IsProxCenter.value_eq_zero`.

The previous version duplicated the prox owners with the separate public names
`is_prox_function_on` and `is_prox_center_on`. Those notions already have a
canonical chapter owner in `Definition_6_31`, so this file now keeps only the
direct recall surface.
-/

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (p : Seminorm ℝ E) [Seminorm.IsNorm p]

variable (Q : Set E) (d : E → ℝ) (x₀ : E)

/- Definition 6.29 uses the chapter's canonical prox-function owner and the
canonical normalized prox-center owner. -/
recall IsProxFunction
recall IsProxFunction.continuousOn
recall IsProxFunction.strongConvexOnWith
recall IsProxCenter
recall IsProxCenter.mem
recall IsProxCenter.isMinOn
recall IsProxCenter.value_eq_zero

set_option linter.hashCommand false in
#check IsProxFunction p Q d

set_option linter.hashCommand false in
#check IsProxCenter Q d x₀

end
