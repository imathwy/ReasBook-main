import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Polynomial
open scoped RatFunc

/-
Domain-style sampling for Example 9.3.5:
- primary domain: rational functions as the canonical fraction-field construction for a polynomial
  ring;
- sampled owner API:
  `RatFunc`,
  `RatFunc.instField`,
  `RatFunc.instIsFractionRingPolynomial`,
  `RatFunc.num_div_denom`;
- best owner abstraction: the canonical owner type `RatFunc k`, written `k⟮X⟯`.

Primitive-vs-derived split:
- primitive data: the owner type `RatFunc k` itself;
- derived API: the field instance `RatFunc.instField`, the fraction-ring instance
  `RatFunc.instIsFractionRingPolynomial`, and the numerator/denominator presentation
  `RatFunc.num_div_denom`.

Source/core/bridge triage:
- `source-facing`: the textbook rational function field `k(x)`;
- `core/canonical`: `RatFunc`;
- `bridge/view`: the notation `k⟮X⟯` and the fraction-field presentation over `k[X]`.

This file should therefore keep `RatFunc` as the owner, but place the main source-facing entry at
the fraction-field layer appropriate to `k(x)`. The field and fraction-field facts only need
`[IsDomain k]`, while the numerator/denominator presentation theorem uses the stronger `[Field k]`
hypothesis from mathlib.
-/

section

variable {k : Type u} [CommRing k] [IsDomain k]

/- Example 9.3.5 (Field of rational functions): for an integral domain `k`, the rational function
field `k(x)` is the canonical owner `k⟮X⟯`, and this owner is the fraction field of `k[X]`. -/
recall RatFunc.instIsFractionRingPolynomial (k : Type u) [CommRing k] [IsDomain k] :
    IsFractionRing k[X] k⟮X⟯

/- Companion recall: the underlying owner construction for the rational function field is
`RatFunc`, written `k⟮X⟯`. -/
recall RatFunc

/- Companion recall: when `k` is an integral domain, `k⟮X⟯` carries its canonical field structure
given by the owner instance `RatFunc.instField`. In particular this applies when `k` is a field. -/
recall RatFunc.instField (k : Type u) [CommRing k] [IsDomain k] : Field k⟮X⟯

end

section

variable {k : Type u} [Field k]

/- Companion recall: every rational function over a field `k` is represented by its numerator
divided by its denominator. -/
recall RatFunc.num_div_denom

end
