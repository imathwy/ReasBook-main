import Mathlib.FieldTheory.Separable
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Definition 9.12.2:
- primary domain: separability for polynomials, algebraic elements, and field extensions;
- sampled owner declarations:
  `Polynomial.Separable`,
  `IsSeparable`,
  `Algebra.IsSeparable`;
- sampled derived/specification API:
  `Polynomial.separable_def`,
  `IsSeparable.isIntegral`,
  `Algebra.isSeparable_iff`;
- best owner abstraction: the primitive pointwise owners are `Polynomial.Separable` for
  polynomials and `IsSeparable` for elements; the extension-level owner `Algebra.IsSeparable` is
  the canonical quantified packaging of the pointwise element predicate;
- primitive data: none locally, since all three notions are already owned by mathlib;
- derived API: the textbook coprime-with-derivative criterion for polynomials, the integrality
  consequence for separable elements, and the extension-level characterization that makes the
  source's algebraicity clause explicit.

Source/core/bridge triage:
- `source-facing`: the textbook notions "a polynomial is separable", "an algebraic element is
  separable", and "an algebraic extension is separable";
- `core/canonical`: `Polynomial.Separable`, `IsSeparable`, and `Algebra.IsSeparable`;
- `bridge/view`: `Polynomial.separable_def`, `IsSeparable.isIntegral`, and
  `Algebra.isSeparable_iff`, which restate the owner predicates in the source's derivative and
  algebraic-pointwise forms.

This file should therefore remain a pure recall surface. Any local wrapper around these owners
would only duplicate existing upstream API without adding mathematics. -/

/- Definition 9.12.2 (1): the textbook notion that an irreducible polynomial over `F` is
separable is the canonical mathlib predicate `Polynomial.Separable`; this predicate is defined for
all polynomials, and on the irreducible input of the text it is exactly the same notion. -/
recall Polynomial.Separable

/- Companion recall for Definition 9.12.2 (1): `Polynomial.separable_def` is exactly the textbook
criterion that separability means being relatively prime to the derivative. -/
recall Polynomial.separable_def

/- Definition 9.12.2 (2): for an element `α` of an extension `K/F`, the textbook notion that an
algebraic element is separable over `F` is the canonical predicate `IsSeparable F α`, defined by
requiring the minimal polynomial over `F` to be separable; the algebraicity hypothesis is absorbed
canonically because nonintegral elements have minimal polynomial `0`. -/
recall IsSeparable

/- Companion recall for Definition 9.12.2 (2): `IsSeparable.isIntegral` is the canonical bridge
showing that the source's algebraicity hypothesis is already a consequence of the owner predicate
`IsSeparable F α`. -/
recall IsSeparable.isIntegral

/- Definition 9.12.2 (3): the textbook notion that an algebraic field extension `K/F` is
separable is the canonical typeclass `Algebra.IsSeparable F K`; algebraicity is again absorbed
canonically by the pointwise separability condition. -/
recall Algebra.IsSeparable

/- Companion recall for Definition 9.12.2 (3): `Algebra.isSeparable_iff` is the source-facing
characterization that makes the absorbed algebraicity clause explicit, expressing
`Algebra.IsSeparable F K` as the condition that every element of `K` is both integral and
separable over `F`. -/
recall Algebra.isSeparable_iff
