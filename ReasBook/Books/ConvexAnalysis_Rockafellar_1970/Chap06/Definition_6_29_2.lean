universe u v w

namespace Bifunction

section

variable {U : Type u} {X : Type v} {α : Type w}

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.2 names the graph function of a bifunction `F : U → X → α`.
- `core/canonical`: this is exactly the pre-existing owner `Function.uncurry F`.
- `bridge/view`: no extra bifunction owner or wrapper theorem is needed; use the canonical
  `Function` API directly.

Domain-style sampling used here:
- `Function.uncurry`;
- `Function.uncurry_apply_pair`;
- `Function.curry`;
- `Function.curry_uncurry`;
- `Function.uncurry_curry`.

Layer target: `core/canonical recall/use`.
-/

/- Definition 6.29.2: the graph function of a bifunction is exactly the canonical uncurried map
`Function.uncurry`. -/
#check (Function.uncurry : (U → X → α) → U × X → α)
#check (Function.uncurry_apply_pair : ∀ (F : U → X → α) (u : U) (x : X),
  Function.uncurry F (u, x) = F u x)
#check (Function.curry : (U × X → α) → U → X → α)
#check (Function.curry_uncurry : ∀ F : U → X → α, Function.curry (Function.uncurry F) = F)
#check (Function.uncurry_curry : ∀ f : U × X → α, Function.uncurry (Function.curry f) = f)

end

end Bifunction
