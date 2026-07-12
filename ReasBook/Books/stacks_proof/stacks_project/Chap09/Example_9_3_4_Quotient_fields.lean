import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling for Example 9.3.4:
- primary domain: fraction fields and their universal property for integral domains;
- sampled owner API:
  `FractionRing`,
  `FractionRing.field`,
  `IsFractionRing.injective`,
  `IsFractionRing.lift`;
- best owner abstraction: the quotient-field owner `FractionRing A` together with the canonical
  embedding `algebraMap A (FractionRing A)` and the interface `IsFractionRing A (FractionRing A)`.

Primitive-vs-derived split:
- primitive data: the owner type `FractionRing A` and its canonical embedding
  `algebraMap A (FractionRing A)`;
- derived API: the field structure on `FractionRing A`, the instance
  `IsFractionRing A (FractionRing A)`, injectivity of the canonical embedding, and the universal
  property morphism `IsFractionRing.lift`.

Source/core/bridge triage:
- `source-facing`: the quotient field of `A` and its canonical embedding into a field;
- `core/canonical`: `FractionRing A`;
- `bridge/view`: `IsFractionRing.lift`, expressing the universal property of the quotient field.

This file should therefore recall `FractionRing` and its canonical embedding/interface directly,
and keep `IsFractionRing.lift` only as the universal-property companion.
-/

section

variable {A : Type u} [CommRing A] [IsDomain A] {K : Type v} [Field K]

/-
Example 9.3.4 (Quotient fields): the quotient field of a domain `A` is the canonical owner
construction `FractionRing A`.
-/
recall FractionRing

/- Companion recall: when `A` is a domain, `FractionRing A` carries its canonical field
structure. -/
recall FractionRing.field (A : Type u) [CommRing A] [IsDomain A] : Field (FractionRing A)

/- Companion recall: the quotient field of a domain is canonically a fraction ring of that
domain. -/
#check (inferInstance : IsFractionRing A (FractionRing A))

/- Companion recall: the canonical embedding of `A` into its quotient field is `algebraMap`. -/
#check (algebraMap A (FractionRing A) : A →+* FractionRing A)

/- Companion recall: the canonical embedding `A → FractionRing A` is injective. -/
#check (IsFractionRing.injective A (FractionRing A) :
    Function.Injective (algebraMap A (FractionRing A)))

/- Companion recall: every injective ring map from `A` to a field extends uniquely from the
quotient field by `IsFractionRing.lift`. -/
recall IsFractionRing.lift

/-- Example 9.3.4, source-form companion: for a domain `A`, every injective ring map
`φ : A →+* K` to a field `K` extends uniquely to `FractionRing A`. Equivalently, a ring
homomorphism `ψ : FractionRing A →+* K` restricts to `φ` on `A` if and only if
`ψ = IsFractionRing.lift hφ`. -/
@[stacks 09FJ]
theorem fractionRing_universal_property
    (φ : A →+* K) (hφ : Function.Injective φ) (ψ : FractionRing A →+* K) :
    ψ.comp (algebraMap A (FractionRing A)) = φ ↔ ψ = IsFractionRing.lift hφ := by
  constructor
  · intro hψ
    simpa using (IsFractionRing.lift_unique hφ fun x ↦ RingHom.congr_fun hψ x).symm
  · intro hψ
    subst hψ
    ext x
    exact IsFractionRing.lift_algebraMap hφ x

end
