import Mathlib
import Mathlib.FieldTheory.Tower
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_9_7_1 (from Chap09) -/
universe u v

variable (E : Type u) (F : Type v) [Field E] [Field F] [Algebra E F]

namespace FieldExtensionDegree
end FieldExtensionDegree

/- Source/core/bridge triage for Definition 9.7.1:
- `source-facing`: the textbook degree notation `[F : E]`
- `core/canonical`: `Module.rank E F`
- `bridge/view`: `FiniteDimensional E F` and `Module.finrank E F` for the finite-degree case

Primitive data are only the field extension and its canonical `E`-module structure on `F`. The
finite-dimensionality predicate and natural-number degree are derived API, so the owner file should
expose the notation on `Module.rank` and then derive the finite view from it.
-/

/- Definition 9.7.1: for a field extension `F/E`, the chapter's degree notation `[F : E]` is the
canonical owner `Module.rank E F`. -/
scoped[FieldExtensionDegree] notation:max "[" F " : " E "]" => Module.rank E F

open scoped FieldExtensionDegree

/- Source-facing check: the textbook degree notation `[F : E]` denotes the cardinal dimension of
`F` as an `E`-vector space. -/
#check ([F : E] : Cardinal)

/-
Definition 9.7.1 (Tag 09G3): for a field extension `F/E`, the degree `[F : E]` is the dimension
of `F` as an `E`-vector space. In Lean this source-facing notion is the canonical owner
`Module.rank E F`.
-/
recall Module.rank

/- Definition 9.7.1 also uses the canonical `FiniteDimensional E F` typeclass for the notion that
the field extension `F/E` is finite. -/
recall FiniteDimensional

/- Companion recall: `Module.finrank E F` is the canonical natural-number view of the same degree;
by definition it is `Cardinal.toNat (Module.rank E F)`, so `Cardinal.toNat [F : E]` already
reduces to `Module.finrank E F`. -/
recall Module.finrank

/-! ### Example_9_7_2 (from Chap09) -/
open scoped FieldExtensionDegree

/- Example 9.7.2: the canonical `ℝ`-basis of `ℂ` is the ordered pair `(1, I)`, so `ℂ` is a
two-dimensional `ℝ`-vector space and hence a finite extension of `ℝ` of degree `2`. -/
recall Complex.coe_basisOneI

/- Example 9.7.2: in the chapter's degree notation, the complex numbers form a degree-`2`
extension of the real numbers. This is the source-facing natural-number view of the canonical
owner theorem `Complex.rank_real_complex`. -/
theorem complex_degree_eq_two : Cardinal.toNat [ℂ : ℝ] = 2 := by
  simp [Complex.rank_real_complex]

/-! ### Lemma_9_7_3 (from Chap09) -/
/- Domain-style sampling:
* primary domain: finite-dimensional field extensions in a scalar tower;
* sampled owner declarations:
  `Module.Finite.right`,
  `FiniteDimensional.right`,
  `FiniteDimensional.trans`;
* best owner abstraction: the field-extension owner theorem `FiniteDimensional.right`, which is the
  chapter-natural field-specialized surface over the more primitive module-theoretic owner
  `Module.Finite.right`;
* primitive data: a tower of fields `F ⟶ E ⟶ K` and finite dimensionality of `K` over `F`;
* derived API: finiteness of `K` over the intermediate field `E`.

Layer triage:
* `source-facing`: Lemma 9.7.3 is the textbook tower-law finiteness statement for field
  extensions;
* `core/canonical`: `Module.Finite.right`;
* `bridge/view`: the field-specialized alias `FiniteDimensional.right`.

So this file should stay as a direct recall of the field-level owner theorem rather than introduce a
local wrapper or restate the module-theoretic theorem under a second chapter-specific name. -/
/- Lemma 9.7.3: if `K/E/F` is a tower of algebraic field extensions and `K` is finite over `F`,
then `K` is finite over `E`. This is exactly the canonical scalar-tower finiteness theorem
`FiniteDimensional.right`; the algebraicity assumptions from the source text are ambient and are
not needed for the formal statement. -/
recall FiniteDimensional.right

/-! ### Example_9_7_4_Degree_of_a_rational_function_field (from Chap09) -/
universe u

open scoped RatFunc

/-- Example 9.7.4 (Degree of a rational function field): the rational function field `k(t)` is not
a finite extension of `k`, equivalently it is not finite-dimensional as a `k`-vector space. -/
theorem ratFunc_not_finiteDimensional
    (k : Type u) [Field k] :
    ¬ FiniteDimensional k k⟮X⟯ := by
  intro h
  letI := h
  exact (Algebra.transcendental_iff_not_isAlgebraic.mp RatFunc.transcendental)
    (Algebra.IsAlgebraic.of_finite k k⟮X⟯)

/-! ### Lemma_9_7_5 (from Chap09) -/
universe u v

open scoped RatFunc

section

variable (k : Type u) (F : Type v) [Field k] [Field F] [Algebra k F] [FiniteDimensional k F]

/- A finite extension of fields is essentially of finite type via the canonical
`Algebra.EssFiniteType` instance induced by finite-dimensionality. -/
#synth Algebra.EssFiniteType k F

end

section

open IntermediateField

variable {k : Type u} [Field k]

/-- Helper for Lemma 9.7.5: the top intermediate field of `k⟮X⟯ / k` is generated by the
singleton `{X}`. -/
lemma ratFunc_top_fg : (⊤ : IntermediateField k k⟮X⟯).FG := by
  -- The rational function field is generated by adjoining the single element `X`.
  simpa [Finset.coe_singleton, RatFunc.adjoin_X] using
    (IntermediateField.fg_adjoin_finset (F := k) ({(RatFunc.X : k⟮X⟯)} : Finset k⟮X⟯))

/-- Lemma 9.7.5: the rational function field `k⟮X⟯ = k(X)` is a finitely generated field
extension of `k`, generated by the single element `X`. -/
-- Proof sketch: use `IntermediateField.fg_top_iff` together with `RatFunc.adjoin_X` to show
-- that `k⟮X⟯` is generated as an intermediate field by the singleton `{X}`.
theorem ratFunc_essFiniteType : Algebra.EssFiniteType k k⟮X⟯ := by
  -- Translate essential finite type into finite generation of the top intermediate field.
  rw [← IntermediateField.fg_top_iff]
  -- The helper records the source proof's single-generator argument.
  exact ratFunc_top_fg

/- The converse fails for the rational function field: `k⟮X⟯` is essentially of finite type over
`k`, but by Example 9.7.4 it is not finite-dimensional over `k`. -/
recall ratFunc_not_finiteDimensional

end

/-! ### Example_9_7_6_Degree_of_a_simple_algebraic_extension (from Chap09) -/
open Polynomial

open scoped FieldExtensionDegree

universe u

section

variable {k : Type u} [Field k]

/- Domain-style sampling for Example 9.7.6:
- `source-facing`: the degree of the simple extension `k[t]/(P)`
- `core/canonical`: `finrank_quotient_span_eq_natDegree`
- `bridge/view`: `AdjoinRoot.instField`, which uses irreducibility to view the same quotient as a
  field

Primitive data is only the polynomial quotient. The irreducibility hypothesis belongs to the
derived field/simple-extension interface, not to a duplicate local degree theorem.
-/

/- Example 9.7.6 (Degree of a simple algebraic extension): once `P` is irreducible, Example 9.3.3
supplies the field structure on `k[X] ⧸ Ideal.span {P}`. The degree computation itself is the
canonical theorem `finrank_quotient_span_eq_natDegree`. -/
recall finrank_quotient_span_eq_natDegree (P : k[X]) :
    Module.finrank k (k[X] ⧸ Ideal.span {P}) = P.natDegree

end

/- Example 9.7.2: the canonical `ℝ`-basis of `ℂ` is the ordered pair `(1, I)`, so `ℂ` is a
two-dimensional `ℝ`-vector space and hence a finite extension of `ℝ` of degree `2`. -/
recall Complex.coe_basisOneI

/- Example 9.7.2: in the chapter's degree notation, the complex numbers form a degree-`2`
extension of the real numbers. This is the source-facing natural-number view of the canonical
owner theorem `Complex.rank_real_complex`. -/
theorem complex_degree_eq_two : Cardinal.toNat [ℂ : ℝ] = 2 := by
  -- The chapter notation `[ℂ : ℝ]` is `Module.rank ℝ ℂ`, so the canonical rank theorem closes it.
  simp [Complex.rank_real_complex]

/-! ### Lemma_9_7_7_Multiplicativity (from Chap09) -/
open scoped FieldExtensionDegree

universe u

/- Domain-style sampling for Lemma 9.7.7:
- primary domain: towers of field extensions and cardinal extension degree;
- sampled owner declarations:
  `Module.rank`,
  the chapter notation `[F : E]` from Definition 9.7.1,
  `rank_mul_rank`,
  `Module.finrank_mul_finrank`;
- best owner abstraction: the canonical tower-law owner is `rank_mul_rank`, while `[F : E]` is
  only the source-facing notation for `Module.rank E F`;
- primitive data: the tower `k ⟶ E ⟶ F`;
- derived API: the degree formula in textbook notation.

Layer triage:
- `source-facing`: the displayed equality `[F : k] = [F : E] * [E : k]`;
- `core/canonical`: `rank_mul_rank`;
- `bridge/view`: the notation from Definition 9.7.1 rewriting `Module.rank` into degree notation.
-/

variable {k E F : Type u} [Field k] [Field E] [Field F]
variable [Algebra k E] [Algebra E F] [Algebra k F] [IsScalarTower k E F]

/- Lemma 9.7.7 (Multiplicativity): for a tower of fields `F / E / k`, the extension degrees
multiply:
`[F : k] = [F : E] * [E : k]`. This is exactly the canonical mathlib tower law `rank_mul_rank`,
viewed through the chapter notation `[L : K] = Module.rank K L`. -/
recall rank_mul_rank

/-! ### Definition_9_7_8 (from Chap09) -/
/- Definition 9.7.8: a number field is the canonical mathlib class `NumberField`, i.e. a field of
characteristic `0` that is finite-dimensional over `ℚ`. -/
recall NumberField

/- Companion recalls: the defining textbook properties of a number field are provided by the
canonical `NumberField` instances. -/
recall NumberField.to_charZero
recall NumberField.to_finiteDimensional
