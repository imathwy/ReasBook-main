import Mathlib.Tactic.Recall
import Mathlib.RepresentationTheory.Character

-- Declarations for this item will be appended below by the statement pipeline.

/- Source/core/bridge triage:
- `source-facing`: Proposition 2-2.1-2 (1) and (2), the two character identities recalled below;
- `core/canonical`: `Representation.character` with `Representation.char_prod` and
  `Representation.char_tensor`;
- `bridge/view`: none.

Primitive data is already owned by `Representation`; this file is pure recall of the canonical
derived API, so there is no parallel local wrapper to keep. -/

/- Proposition 2-2.1-2 (1): the character of the binary direct-sum representation
`ρ₁.prod ρ₂` is the sum of the two characters. This is the canonical owner theorem
`Representation.char_prod`. -/
/-- Proposition 2-2.1-2 (1): the character of a binary product representation is the sum of the
two characters. -/
theorem Representation.char_prod
    {G k V W : Type*} [Monoid G] [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W) :
    (Representation.prod ρ σ).character = ρ.character + σ.character := by
  -- Evaluate the product representation pointwise and use additivity of trace on `V × W`.
  ext g
  simpa [Representation.character, Representation.prod] using
    (LinearMap.trace_prodMap' (ρ g) (σ g))

/- Proposition 2-2.1-2 (2): the character of the tensor-product representation is the product of
the two characters. This is the existing theorem `Representation.char_tensor`. -/
recall Representation.char_tensor
