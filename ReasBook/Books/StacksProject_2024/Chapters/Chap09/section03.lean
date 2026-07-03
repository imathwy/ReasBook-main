import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_9_3_1_Rational_numbers (from Chap09) -/
/-
Domain-style sampling for Example 9.3.1:
- primary domain: basic field structure on the rational numbers;
- sampled owner API:
  `Rat.instField`,
  `Rat.instCharZero`,
  `RatFunc`,
  `AdjoinRoot.instField`;
- best owner abstraction: the canonical type `ℚ` equipped with the upstream owner instance
  `Rat.instField : Field ℚ`.

Primitive-vs-derived split:
- primitive data: the type `ℚ`;
- derived API: the field operations and axioms supplied by `Rat.instField`, with companions such
  as `Rat.instCharZero`.

Source/core/bridge triage:
- `source-facing`: the textbook statement that the rational numbers form a field;
- `core/canonical`: `Rat.instField`;
- `bridge/view`: the notation `ℚ` presenting the source object.

There is no extra source-facing data to package locally, so this file should recall the owner
instance directly rather than use an anonymous `inferInstance` check.
-/

/- Example 9.3.1 (Rational numbers): the rational numbers form a field, represented in Lean by the
canonical type `ℚ`. The field structure is the upstream owner instance `Rat.instField`. -/
recall Rat.instField

/-! ### Example_9_3_2_Prime_fields (from Chap09) -/
/- Domain-style sampling for Example 9.3.2:
- primary domain: prime fields and the canonical finite field owner `ZMod p`;
- sampled owner API:
  `Int.quotientSpanNatEquivZMod`,
  `ZMod.instField`,
  `Nat.card_zmod`,
  `Int.ideal_span_isMaximal_of_prime`;
- best owner abstraction: the field `ZMod p` itself, with `Int.quotientSpanNatEquivZMod` as the
  bridge from the quotient presentation `ℤ/(p)`;
- primitive data: `p : ℕ` together with `[Fact p.Prime]`;
- derived API: the field structure on `ZMod p`, the bridge equivalence
  `ℤ ⧸ Ideal.span {(p : ℤ)} ≃+* ZMod p`, and the cardinality statement
  `Nat.card (ZMod p) = p`.

Primitive-vs-derived split:
- primitive owner data: the prime field object `ZMod p`;
- bridge/view data: the quotient presentation `ℤ/(p)` and the equivalence
  `Int.quotientSpanNatEquivZMod p`;
- derived consequences: `ZMod.instField` and `Nat.card_zmod`.

Source/core/bridge triage:
- `source-facing`: the example that the quotient ring `ℤ/(p)` is the usual prime field `𝔽_p`;
- `core/canonical`: `ZMod p` with its canonical field instance `ZMod.instField`;
- `bridge/view`: `Int.quotientSpanNatEquivZMod`.

The quotient maximality theorem `Int.ideal_span_isMaximal_of_prime` explains why the bridge model is
a field, but it is support for the quotient presentation rather than the owner-level public API for
`𝔽_p`, so the refined file should stop at `ZMod.instField` and `Nat.card_zmod`.
-/

/- Example 9.3.2 (Prime fields): the quotient ring `ℤ/(n)` is canonically identified with
`ZMod n`; for prime `p`, this is the usual model for `𝔽_p`. -/
recall Int.quotientSpanNatEquivZMod (n : ℕ) : ℤ ⧸ Ideal.span {(n : ℤ)} ≃+* ZMod n

section

variable (p : ℕ) [Fact p.Prime]

/- Example 9.3.2, core/canonical recall: for prime `p`, the prime field `𝔽_p` is the canonical
owner `ZMod p`, equipped with the standard field structure. The quotient-ring presentation
`ℤ/(p)` is only a bridge to this owner via `Int.quotientSpanNatEquivZMod p`. -/
recall ZMod.instField (p : ℕ) [Fact p.Prime] : Field (ZMod p)

end

/- Example 9.3.2, owner-level consequence: the prime field `𝔽_p = ZMod p` has exactly `p`
elements. The quotient cardinality of `ℤ/(p)` is recovered by transporting this statement across
`Int.quotientSpanNatEquivZMod p`, not vice versa. -/
recall Nat.card_zmod (n : ℕ) : Nat.card (ZMod n) = n

/-! ### Example_9_3_3 (from Chap09) -/
open Polynomial

noncomputable section

universe u

variable {k : Type u} [Field k]

/- 
Domain-style sampling for Example 9.3.3:
- primary domain: polynomial quotients and adjoining a root of an irreducible polynomial;
- sampled owner API:
  `AdjoinRoot`,
  `AdjoinRoot.span_maximal_of_irreducible`,
  `AdjoinRoot.instField`,
  `Ideal.Quotient.field`;
- best owner abstraction: the upstream instance
  `AdjoinRoot.instField : Field (AdjoinRoot P)`,
  used here through the definitional equality
  `AdjoinRoot P = k[X] ⧸ Ideal.span {P}`.

Primitive-vs-derived split:
- primitive data: the polynomial `P : k[X]` and the quotient ring `k[X] ⧸ Ideal.span {P}`;
- derived API: maximality of `(P)` under irreducibility and the induced field structure.

Source/core/bridge triage:
- `source-facing`: the textbook quotient-ring statement `k[X]/(P)` is a field for irreducible `P`;
- `core/canonical`: `AdjoinRoot.instField`;
- `bridge/view`: the quotient-ring type expression `k[X] ⧸ Ideal.span {P}`.

There is no extra local mathematics to package, so the file should recall the canonical owner
instance directly rather than introduce a parallel local field construction.
-/
/-
Example 9.3.3: if `P : k[X]` is irreducible, then the quotient `k[X] ⧸ Ideal.span {P}`
is a field. This is the canonical `AdjoinRoot.instField` instance, definitionally on the same
quotient ring.
-/
recall AdjoinRoot.instField (P : k[X]) [Fact (Irreducible P)] :
    Field (k[X] ⧸ Ideal.span {P})

/-! ### Example_9_3_4_Quotient_fields (from Chap09) -/
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

/-! ### Example_9_3_5_Field_of_rational_functions (from Chap09) -/
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

/-! ### Example_9_3_6 (from Chap09) -/
open scoped Manifold Topology

universe u

section

variable (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

private noncomputable abbrev chartExpression (x : X) (f : X → ℂ) : ℂ → ℂ :=
  writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f

private def IsMeromorphic (f : X → ℂ) : Prop :=
  ∀ x, MeromorphicAt (chartExpression X x f) (extChartAt 𝓘(ℂ) x x)

private def meromorphicSubalgebra : Subalgebra ℂ (X → ℂ) where
  carrier := {f | IsMeromorphic X f}
  zero_mem' := by
    intro x
    change MeromorphicAt (fun _ : ℂ ↦ (0 : ℂ)) ((chartAt ℂ x) x)
    exact MeromorphicAt.const (0 : ℂ) ((chartAt ℂ x) x)
  add_mem' := by
    intro f g hf hg x
    simpa [IsMeromorphic, writtenInExtChartAt, Function.comp] using (hf x).add (hg x)
  one_mem' := by
    intro x
    change MeromorphicAt (fun _ : ℂ ↦ (1 : ℂ)) ((chartAt ℂ x) x)
    exact MeromorphicAt.const (1 : ℂ) ((chartAt ℂ x) x)
  mul_mem' := by
    intro f g hf hg x
    simpa [IsMeromorphic, writtenInExtChartAt, Function.comp] using (hf x).mul (hg x)
  algebraMap_mem' := by
    intro c x
    change MeromorphicAt (fun _ : ℂ ↦ c) ((chartAt ℂ x) x)
    exact MeromorphicAt.const c ((chartAt ℂ x) x)

omit [IsManifold 𝓘(ℂ) 1 X] in
private theorem isMeromorphic_inv {f : X → ℂ} (hf : IsMeromorphic X f) :
    IsMeromorphic X f⁻¹ := by
  intro x
  change MeromorphicAt ((chartExpression X x f)⁻¹) ((chartAt ℂ x) x)
  simpa [IsMeromorphic, chartExpression] using (hf x).inv

private noncomputable instance : Inv ↥(meromorphicSubalgebra X) where
  inv f := ⟨(f : X → ℂ)⁻¹, isMeromorphic_inv X f.property⟩

private def meromorphicCon : RingCon ↥(meromorphicSubalgebra X) where
  r f g := (f : X → ℂ) =ᶠ[Filter.codiscrete X] (g : X → ℂ)
  iseqv := ⟨fun f ↦ Filter.EventuallyEq.rfl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩
  add' := by
    intro a b c d hab hcd
    exact hab.add hcd
  mul' := by
    intro a b c d hab hcd
    exact hab.mul hcd

/-- The meromorphic function field `ℂ(X)`, realized as meromorphic representatives modulo
codiscrete equality, which forgets inessential point values at isolated poles. -/
abbrev MeromorphicFunctionField := RingCon.Quotient (meromorphicCon X)

end

notation:max "ℂ(" X ")" => MeromorphicFunctionField X

section

variable (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [ConnectedSpace X]

/-- Helper for Example 9.3.1 (Rational numbers): punctured neighborhoods on a connected complex
manifold are nontrivial. -/
private theorem manifold_punctured_nhds_neBot (x : X) :
    Filter.NeBot (𝓝[≠] x) := by
  sorry

/-- Helper for Example 9.3.1 (Rational numbers): a meromorphic representative is either eventually
zero or eventually nonzero on each punctured neighborhood. -/
private theorem isMeromorphic_eventually_eq_zero_or_eventually_ne_zero {f : X → ℂ}
    (hf : IsMeromorphic X f) (x : X) :
    f =ᶠ[𝓝[≠] x] 0 ∨ ∀ᶠ y in 𝓝[≠] x, f y ≠ 0 := by
  sorry

/-- Helper for Example 9.3.1 (Rational numbers): on a connected manifold, a meromorphic
representative is either codiscretely zero or codiscretely nonzero. -/
private theorem isMeromorphic_eq_zero_or_nonzero_mem_codiscrete {f : X → ℂ}
    (hf : IsMeromorphic X f) :
    f =ᶠ[Filter.codiscrete X] 0 ∨ {x | f x ≠ 0} ∈ Filter.codiscrete X := by
  sorry

private theorem meromorphicFunctionField_zero_ne_one :
    (0 : ℂ(X)) ≠ 1 := by
  sorry

noncomputable instance : Nontrivial (ℂ(X)) :=
  ⟨0, 1, meromorphicFunctionField_zero_ne_one X⟩

private theorem meromorphicFunctionField_isUnit_or_eq_zero (f : ℂ(X)) :
    IsUnit f ∨ f = 0 := by
  sorry

noncomputable instance : Field (ℂ(X)) :=
  Field.ofIsUnitOrEqZero fun f ↦ meromorphicFunctionField_isUnit_or_eq_zero X f

/- Example 9.3.6: the meromorphic function field `ℂ(X)` of a connected Riemann surface carries
its canonical field structure. -/
#check (inferInstance : Field (ℂ(X)))

end
