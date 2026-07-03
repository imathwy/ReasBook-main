import Mathlib
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Data.Rat.Cardinal
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_9_6_1 (from Chap09) -/
/- Domain-style sampling:
* primary domain: injectivity of ring homomorphisms out of fields and, more generally, simple
  rings;
* sampled owner declarations:
  `DivisionRing.isSimpleRing`,
  `RingHom.injective`,
  `IsSimpleRing.iff_injective_ringHom`,
  `FaithfulSMul.algebraMap_injective`;
* best owner abstraction: `RingHom.injective`;
* primitive data: a ring homomorphism `φ : F →+* R` with field source and nontrivial target;
* derived API: `Function.Injective φ`.

Layer triage:
* `source-facing`: the textbook field-specialized injectivity statement;
* `core/canonical`: `RingHom.injective`, using the owner fact that a field is a simple ring;
* `bridge/view`: `FaithfulSMul.algebraMap_injective` for the special case of algebra maps.

This item should therefore remain a direct recall of the canonical owner theorem, not a local
field-specific wrapper.
-/

/- Lemma 9.6.1: if `F` is a field and `R` is a nonzero ring, then any ring homomorphism
`φ : F →+* R` is injective. This is the field-specialized textbook reading of the canonical
mathlib theorem `RingHom.injective`, whose native owner signature is stated for homomorphisms out
of simple rings into nontrivial semirings. -/
recall RingHom.injective

/-! ### Definition_9_6_2 (from Chap09) -/
universe u v

/- Source/core/bridge triage for Definition 9.6.2:
- `source-facing`: a field extension `E/F`
- `core/canonical`: the `F`-algebra structure `Algebra F E`
- `bridge/view`: injectivity of the canonical map `algebraMap F E`

Primitive data are only the two fields and the `F`-algebra structure on `E`; injectivity of the
canonical map is derived API from the owner abstraction.
-/

section

variable {F : Type u} {E : Type v} [Field F] [Field E]

/- Definition 9.6.2: a field extension `E/F` is modeled in Lean by a field `E` equipped with the
canonical `F`-algebra structure, i.e. by the type expression `Algebra F E`. -/
#check (Algebra F E)

section

variable [Algebra F E]

/- Companion check: for such a field extension, the canonical map `F →+* E` is injective, so the
textbook phrasing that `F` is contained in `E` is recovered from the canonical `F`-algebra
structure. -/
recall FaithfulSMul.algebraMap_injective

end
end

/-! ### Definition_9_6_3 (from Chap09) -/
universe u

/- Domain-style sampling for towers of field extensions:
- primary domain: finite chains of field extensions;
- sampled owner declarations:
  `Algebra F E` from Definition 9.6.2,
  `IsScalarTower`,
  `rank_mul_rank`,
  `Algebra.IsSeparable.trans`;
- best owner abstraction: a finite tower is source-facing primitive data consisting of the
  successive field extensions `E_{i + 1} / E_i`, so the public entry should remain the direct
  family of adjacent `Algebra` structures indexed by `Fin n`;
- primitive data: the family of fields `E : Fin (n + 1) → Type u` and the consecutive algebra
  structures;
- derived API: once one focuses on a fixed three-stage subtower and equips the composite stage
  with its algebra structure, `IsScalarTower` and downstream tower lemmas become the canonical
  compatibility layer.

Layer triage:
- `source-facing`: the finite tower `E_n / E_{n - 1} / ... / E_0`;
- `core/canonical`: `Algebra F E` for each adjacent extension;
- `bridge/view`: `IsScalarTower` and the standard transitivity lemmas for a chosen triple.
-/

section

variable {n : ℕ} (E : Fin (n + 1) → Type u)
variable [∀ i : Fin (n + 1), Field (E i)]

/- Definition 9.6.3: building on Definition 9.6.2, a tower of fields
`E_n / E_{n - 1} / ... / E_0` is expressed in Lean by a family of fields
`E : Fin (n + 1) → Type u` together with the canonical extension structure on each consecutive
pair. The source-facing primitive data are exactly these successive `Algebra` structures;
`IsScalarTower` is the canonical derived compatibility notion for a fixed three-stage subtower,
not the owner abstraction for the whole finite chain. -/
#check (∀ i : Fin n, Algebra (E i.castSucc) (E i.succ))

end

/-! ### Example_9_6_4 (from Chap09) -/
open Polynomial

universe u

noncomputable section

section

variable {k : Type u} [Field k]

/-
Domain-style sampling for Example 9.6.4:
- primary domain: simple algebraic extensions presented by adjoining a root of a polynomial;
- sampled owner API:
  `AdjoinRoot`,
  `AdjoinRoot.instField`,
  `AdjoinRoot.instAlgebra`,
  `finrank_quotient_span_eq_natDegree`;
- best owner abstraction: the quotient owner `AdjoinRoot P`, with its canonical field and
  `k`-algebra structures supplied upstream.

Primitive-vs-derived split:
- primitive data: the polynomial `P : k[X]` and the quotient owner `AdjoinRoot P`;
- derived API: the field structure under irreducibility and the ambient `k`-algebra structure.

Source/core/bridge triage:
- `source-facing`: the simple extension `k[t]/(P)` viewed as an extension field of `k`;
- `core/canonical`: `AdjoinRoot`, `AdjoinRoot.instField`, `AdjoinRoot.instAlgebra`;
- `bridge/view`: the quotient spelling `k[X] ⧸ Ideal.span {P}` from Example 9.3.3.

This example adds no new data, so the canonical owner instances should be recalled directly, with
the quotient spelling used only as a source-facing bridge check.
-/

section

variable (P : k[X]) [Fact (Irreducible P)]

/- Example 9.6.4: the simple extension `k[t]/(P)` is formalized by `AdjoinRoot P`, which is
definitionally the quotient `k[X] ⧸ Ideal.span {P}`. For irreducible `P`, the canonical
instance `AdjoinRoot.instField` from Example 9.3.3 makes it a field. -/
recall AdjoinRoot.instField (P : k[X]) [Fact (Irreducible P)] :
    Field (k[X] ⧸ Ideal.span {P})

end

section
variable (P : k[X])

/- The canonical owner instance for the adjoin-root construction is `AdjoinRoot.instAlgebra`. -/
recall AdjoinRoot.instAlgebra

/- Therefore the quotient spelling `k[X] ⧸ Ideal.span {P}` inherits the same canonical
`k`-algebra structure. Together with the field instance above, this exhibits `k[t]/(P)` as an
extension of `k`. -/
#check (inferInstance : Algebra k (k[X] ⧸ Ideal.span {P}))

end

end

/-! ### Example_9_6_5 (from Chap09) -/
open Polynomial

universe u

noncomputable section

section

variable {k : Type u} [Field k]

/- 
Domain-style sampling for Example 9.6.4:
- primary domain: simple algebraic extensions presented by adjoining a root of a polynomial;
- sampled owner API:
  `AdjoinRoot`,
  `AdjoinRoot.instField`,
  `AdjoinRoot.instAlgebra`,
  `finrank_quotient_span_eq_natDegree`;
- best owner abstraction: the quotient owner `AdjoinRoot P`, with its canonical field and
  `k`-algebra structures supplied upstream.

Primitive-vs-derived split:
- primitive data: the polynomial `P : k[X]` and the quotient owner `AdjoinRoot P`;
- derived API: the field structure under irreducibility and the ambient `k`-algebra structure.

Source/core/bridge triage:
- `source-facing`: the simple extension `k[t]/(P)` viewed as an extension field of `k`;
- `core/canonical`: `AdjoinRoot`, `AdjoinRoot.instField`, `AdjoinRoot.instAlgebra`;
- `bridge/view`: the quotient spelling `k[X] ⧸ Ideal.span {P}` from Example 9.3.3.

This example adds no new data, so the canonical owner instances should be recalled directly, with
the quotient spelling used only as a source-facing bridge check.
-/

section

variable (P : k[X]) [Fact (Irreducible P)]

/- Example 9.6.4: the simple extension `k[t]/(P)` is formalized by `AdjoinRoot P`, which is
definitionally the quotient `k[X] ⧸ Ideal.span {P}`. The key step is to recall the canonical
field instance supplied upstream for irreducible `P`. -/
recall AdjoinRoot.instField (P : k[X]) [Fact (Irreducible P)] :
    Field (k[X] ⧸ Ideal.span {P})

end

section

variable (P : k[X])

/- The extension structure is the second canonical ingredient: the quotient spelling inherits the
ambient `k`-algebra structure from `AdjoinRoot.instAlgebra`. -/
recall AdjoinRoot.instAlgebra

/- Combining the previous field recall with this algebra recall is exactly the textbook claim that
`k[X] / (P)` is an extension of `k`. We record that bridge by checking the induced algebra
structure on the quotient spelling. -/
#check (inferInstance : Algebra k (k[X] ⧸ Ideal.span {P}))

end

end

/-! ### Definition_9_6_6 (from Chap09) -/
universe u v

/-
Domain-style sampling for finitely generated field extensions:
- primary domain: field extensions and finite generation of the top intermediate field;
- sampled owner declarations:
  `Algebra.EssFiniteType`,
  `IntermediateField.fg_top_iff`,
  `IntermediateField.fg_def`,
  `IntermediateField.essFiniteType_iff`;
- best owner abstraction: `Algebra.EssFiniteType k F`;
- primitive data: only the field extension structure `[Algebra k F]`;
- derived API: the textbook generator statement `∃ S, S.Finite ∧ adjoin k S = ⊤`, obtained by
  combining the owner bridge `fg_top_iff` with the finite-set description `fg_def`.

Source/core/bridge triage:
- `source-facing`: Definition 9.6.6 as the textbook assertion that `F / k` is generated by a
  finite subset of `F`;
- `core/canonical`: the owner class `Algebra.EssFiniteType k F`;
- `bridge/view`: the theorem `isFinitelyGeneratedFieldExtension_iff`, which restates the owner in
  the textbook `adjoin` language without introducing any parallel local wrapper.
-/

section

variable (k : Type u) (F : Type v) [Field k] [Field F] [Algebra k F]

/- Definition 9.6.6: a finitely generated field extension `F / k` is the canonical mathlib owner
`Algebra.EssFiniteType k F`. The textbook formulation in terms of `F = k(S)` for a finite subset
`S ⊆ F` is derived below from `IntermediateField.fg_top_iff` and `IntermediateField.fg_def`. -/
#check (Algebra.EssFiniteType k F)

end

section

open IntermediateField

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

/-- Definition 9.6.6: a field extension `F / k` is finitely generated exactly when there exists a
finite subset `S ⊆ F` such that `F = k(S)`, expressed canonically as `adjoin k S = ⊤`. -/
theorem isFinitelyGeneratedFieldExtension_iff :
    Algebra.EssFiniteType k F ↔ ∃ S : Set F, S.Finite ∧ adjoin k S = ⊤ := by
  rw [← fg_top_iff, fg_def]

end

/-! ### Exercise_9_6_7 (from Chap09) -/
open Cardinal IntermediateField

/- Domain-style sampling for countable generation of field extensions by adjoining subsets:
- same-domain declarations inspected:
  `IntermediateField.adjoin`,
  `IntermediateField.cardinalMk_adjoin_le`,
  `Cardinal.mkRat`,
  `not_countable_complex`
- owner abstraction: `IntermediateField.adjoin`

Layer triage:
- `source-facing`: the exercise statement that no countable subset of `ℂ` generates `ℂ` over `ℚ`
- `core/canonical`: the intermediate field `adjoin ℚ s`
- `bridge/view`: the canonical cardinality bound `cardinalMk_adjoin_le` together with the
  uncountability theorem `not_countable_complex`

Primitive data is just the owner object `adjoin ℚ s`. Countability of the generated intermediate
field is derived API from the canonical cardinality estimate, so this file should remain a thin
bridge theorem rather than introducing any local wrapper for countable generation. -/

/-- Exercise 9.6.7: no countable subset of `ℂ` generates `ℂ` as a field extension of `ℚ`. -/
-- Proof sketch: if `s` is countable, then `IntermediateField.adjoin ℚ s` has cardinality at most
-- `ℵ₀` by the cardinality bound for adjoins over a countable base. But `ℂ` is uncountable, so the
-- adjoin cannot be all of `ℂ`.
theorem complex_not_countably_generated_over_rat
    (s : Set ℂ) (hs : s.Countable) : adjoin ℚ s ≠ ⊤ := by
  intro htop
  have hadjoin : #(adjoin ℚ s) ≤ ℵ₀ := by
    calc
      #(adjoin ℚ s) ≤ #ℚ ⊔ #s ⊔ ℵ₀ := cardinalMk_adjoin_le ℚ s
      _ = ℵ₀ := by
        rw [Cardinal.mkRat, sup_assoc, sup_eq_right.2 hs.le_aleph0, sup_eq_right.2 le_rfl]
  have hs' : (adjoin ℚ s : Set ℂ).Countable := le_aleph0_iff_set_countable.mp hadjoin
  have huniv : (Set.univ : Set ℂ).Countable := by simpa [htop] using hs'
  exact not_countable_complex huniv

/-! ### Lemma_9_6_8_Classification_of_simple_extensions (from Chap09) -/
universe u v

open IntermediateField

/- Domain-style sampling for Lemma 9.6.8:
- `source-facing`: a field extension generated by one element, expressed as `∃ α, k⟮α⟯ = ⊤`;
- sampled owner declarations:
  `IntermediateField`,
  `RatFunc.algEquivOfTranscendental`,
  `IntermediateField.adjoinRootEquivAdjoin`,
  `minpoly.irreducible`;
- `core/canonical`: the owner lattice point `IntermediateField k F`, with the simple generator
  condition `k⟮α⟯ = ⊤`;
- `bridge/view`: the transcendental branch is the canonical equivalence from `RatFunc`, while the
  algebraic branch is the canonical equivalence from `AdjoinRoot (minpoly k α)` to `k⟮α⟯`.

Primitive data is only the chosen generator `α` together with `k⟮α⟯ = ⊤`. The polynomial
`minpoly k α`, its irreducibility, and the two resulting equivalences are all derived API from the
owner declarations above, so this file should not introduce any parallel wrapper for simple
extensions.
-/

-- Proof sketch: choose `α : F` with `k⟮α⟯ = ⊤`. If `α` is transcendental over `k`, the
-- evaluation map `k[X] → F` is injective and extends to the fraction field, giving
-- `RatFunc k ≃ₐ[k] F`. If `α` is algebraic, then `F` is identified with the simple algebraic
-- extension generated by `α`, hence with `AdjoinRoot (minpoly k α)`, and `minpoly k α` is
-- irreducible.
/-- Lemma 9.6.8 (Classification of simple extensions): if the field extension `F/k` is generated
by one element, then `F` is `k`-isomorphic either to the rational function field `RatFunc k` or
to `AdjoinRoot P = k[t]/(P)` for some irreducible polynomial `P : k[X]`. -/
theorem simple_extension_isomorphic_to_ratFunc_or_adjoinRoot
    {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
    (hgen : ∃ α : F, k⟮α⟯ = ⊤) :
    Nonempty (RatFunc k ≃ₐ[k] F) ∨
      ∃ P : Polynomial k, Irreducible P ∧ Nonempty (AdjoinRoot P ≃ₐ[k] F) := by
  obtain ⟨α, htop⟩ := hgen
  have eTop : k⟮α⟯ ≃ₐ[k] F := (equivOfEq htop).trans topEquiv
  by_cases halg : IsAlgebraic k α
  · refine Or.inr ?_
    refine ⟨minpoly k α, minpoly.irreducible halg.isIntegral, ?_⟩
    exact ⟨(adjoinRootEquivAdjoin k halg.isIntegral).trans eTop⟩
  · refine Or.inl ?_
    exact ⟨(RatFunc.algEquivOfTranscendental α halg).trans eTop⟩

/-! ### Lemma_9_6_9 (from Chap09) -/
open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

/-
Domain-style sampling for common overfields of field extensions:
- primary domain: tensor-product constructions for field extensions over a base field;
- sampled canonical declarations: `Ideal.exists_maximal`, `Ideal.Quotient.field`,
  `Ideal.Quotient.mkₐ`, `Algebra.TensorProduct.includeLeft`, `Algebra.TensorProduct.includeRight`,
  and the stronger nearby owner theorems
  `Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective` and
  `IntermediateField.LinearDisjoint.exists_field_of_isDomain`;
- best owner abstraction for this weaker source-facing item: the tensor product `E ⊗[k] F`
  together with a maximal-ideal quotient;
- the stronger `LinearDisjoint` owners are not exact replacements here: they additionally require
  `IsDomain (E ⊗[k] F)` and conclude linearly disjoint images, while Lemma 9.6.9 is
  unconditional and only asks for a common overfield;
- primitive data: only the base field `k`, the fields `E`, `F`, their `k`-algebra structures, and
  the two resulting `k`-algebra maps into the quotient field;
- derived API: injectivity of those maps, which is automatic because their source and target are
  fields.

Source/core/bridge triage:
- `source-facing`: existence of a common extension field for `E/k` and `F/k`;
- `core/canonical`: the quotient field `(E ⊗[k] F) ⧸ m` for a maximal ideal `m`;
- `bridge/view`: the maps `E →ₐ[k] M` and `F →ₐ[k] M` obtained by composing the quotient map with
  `includeLeft` and `includeRight`.
-/

section

variable {k : Type u} {E : Type v} {F : Type w} [Field k] [Field E] [Field F]
variable [Algebra k E] [Algebra k F]

-- Proof sketch: the canonical common-overfield construction is the quotient of the tensor product
-- `E ⊗[k] F` by a maximal ideal. Since the quotient by a maximal ideal is a field, composing the
-- quotient map with the two tensor-factor maps gives `k`-algebra maps from `E` and `F` into a
-- common field extension.
/-- Lemma 9.6.9: any two field extensions `E/k` and `F/k` admit a common extension field over `k`,
together with `k`-algebra maps from `E` and `F` into it. The usual embedding formulation is the
same statement, because any ring homomorphism out of a field is injective. -/
theorem exists_common_field_extension :
    ∃ (M : Type (max v w)) (_ : Field M) (_ : Algebra k M) (iE : E →ₐ[k] M) (iF : F →ₐ[k] M),
      Function.Injective iE ∧ Function.Injective iF := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (E ⊗[k] F)
  let M : Type (max v w) := (E ⊗[k] F) ⧸ m
  letI : m.IsMaximal := hm
  letI : Field M := Ideal.Quotient.field m
  refine ⟨M, inferInstance, inferInstance, (Ideal.Quotient.mkₐ k m).comp includeLeft,
    (Ideal.Quotient.mkₐ k m).comp includeRight, RingHom.injective _, RingHom.injective _⟩

end
