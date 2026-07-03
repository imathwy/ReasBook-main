import Mathlib
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_9_12_1 (from Chap09) -/
universe u

open Polynomial

/- Domain-style sampling:
- primary domain: irreducible polynomials over a field, their separability, and the
  positive-characteristic `expand`/contraction interface;
- sampled owner declarations:
  `Polynomial.separable_iff_derivative_ne_zero`,
  `Polynomial.separable_def`,
  `Polynomial.HasSeparableContraction.isSeparableContraction`,
  `Irreducible.hasSeparableContraction`;
- best owner abstractions:
  `Polynomial.separable_iff_derivative_ne_zero` for the derivative criterion and
  `Polynomial.HasSeparableContraction` for the positive-characteristic factorization;
- primitive data: an irreducible polynomial `P : F[X]`;
- derived API: the source-facing `or` and existence reformulations below, together with their
  coprimeness companions.

Layer triage:
- `source-facing`: the four bridge theorems in this file;
- `core/canonical`: the two recalled owner declarations above;
- `bridge/view`: the coprimeness restatements obtained from `Polynomial.separable_def`.
-/

/- Lemma 9.12.1: the irreducible-case derivative criterion is the canonical theorem
`Polynomial.separable_iff_derivative_ne_zero`; the source-facing `or` reformulation below is only
its textbook bridge. -/
recall Polynomial.separable_iff_derivative_ne_zero

/- Lemma 9.12.1: the positive-characteristic factorization is organized by the owner abstraction
`Polynomial.HasSeparableContraction`, produced canonically for irreducibles by
`Irreducible.hasSeparableContraction`. The source-facing existence theorem below unpacks this owner
and adds the irreducibility of the contracted factor. -/
recall Irreducible.hasSeparableContraction

variable {F : Type u} [Field F] {P : F[X]}

/-- Source-facing bridge for Lemma 9.12.1: an irreducible polynomial is separable unless its
derivative vanishes. -/
theorem irreducible_separable_or_derivative_eq_zero (hP : Irreducible P) :
    P.Separable ∨ P.derivative = 0 := by
  by_cases hderiv : P.derivative = 0
  · exact Or.inr hderiv
  · exact Or.inl <| (separable_iff_derivative_ne_zero hP).2 hderiv

/-- Companion bridge for Lemma 9.12.1: via `Polynomial.separable_def`, the textbook wording is
that an irreducible polynomial is coprime to its derivative unless the derivative vanishes. -/
theorem irreducible_isCoprime_derivative_or_derivative_eq_zero (hP : Irreducible P) :
    IsCoprime P P.derivative ∨ P.derivative = 0 := by
  simpa [separable_def] using irreducible_separable_or_derivative_eq_zero hP

/-- Source-facing bridge for Lemma 9.12.1: if an irreducible polynomial over a field has zero
derivative, then the field has positive characteristic and the polynomial is an iterated `expand`
of an irreducible separable polynomial. -/
theorem exists_irreducible_separable_expand_of_derivative_eq_zero
    (hP : Irreducible P) (hderiv : P.derivative = 0) :
    0 < ringChar F ∧
      ∃ n : ℕ, ∃ Q : F[X],
        P = expand F ((ringChar F) ^ n) Q ∧ Irreducible Q ∧ Q.Separable := by
  have hchar_ne_zero : ringChar F ≠ 0 := by
    intro hchar
    letI : CharZero F := (CharP.ringChar_zero_iff_CharZero F).1 hchar
    exact (separable_iff_derivative_ne_zero hP).1 hP.separable hderiv
  have hchar : 0 < ringChar F := Nat.pos_of_ne_zero hchar_ne_zero
  letI : NeZero (ringChar F) := ⟨hchar_ne_zero⟩
  letI : Fact (ringChar F).Prime := CharP.char_is_prime_of_pos F (ringChar F)
  have hcontraction := hP.hasSeparableContraction (ringChar F)
  obtain ⟨hQsep, n, hQP⟩ := hcontraction.isSeparableContraction
  have hQirr : Irreducible hcontraction.contraction :=
    of_irreducible_expand_pow (Nat.ne_of_gt hchar) (hQP ▸ hP)
  exact ⟨hchar, n, hcontraction.contraction, hQP.symm, hQirr, hQsep⟩

/-- Companion bridge for Lemma 9.12.1: rewriting separability as coprimeness with the derivative
recovers the textbook formulation of the positive-characteristic case. -/
theorem exists_irreducible_isCoprime_derivative_expand_of_derivative_eq_zero
    (hP : Irreducible P) (hderiv : P.derivative = 0) :
    0 < ringChar F ∧
      ∃ n : ℕ, ∃ Q : F[X],
        P = expand F ((ringChar F) ^ n) Q ∧ Irreducible Q ∧ IsCoprime Q Q.derivative := by
  simpa [separable_def] using
    exists_irreducible_separable_expand_of_derivative_eq_zero hP hderiv

/-! ### Definition_9_12_2 (from Chap09) -/
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

/-! ### Lemma_9_12_3 (from Chap09) -/
/- Domain-style sampling for Lemma 9.12.3:
- primary domain: separability of elements and field extensions in a tower of field extensions;
- sampled owner declarations:
  `IsSeparable`,
  `Algebra.IsSeparable`;
- sampled derived API:
  `IsSeparable.tower_top`,
  `Algebra.isSeparable_tower_top_of_isSeparable`;
- best owner abstraction: the pointwise owner is `IsSeparable`, and the extension-level owner is
  `Algebra.IsSeparable`; the source lemma's two parts are exactly the tower-stability theorems
  derived from these owners;
- primitive data: none locally, since both the elementwise and extensionwise notions already have
  canonical mathlib owners;
- derived API: the pointwise descent theorem `IsSeparable.tower_top` and its quantified
  extension-level companion `Algebra.isSeparable_tower_top_of_isSeparable`.

Source/core/bridge triage:
- `source-facing`: in a tower `F ⟶ E ⟶ K`, separability over `F` implies separability over `E`,
  first for elements and then for the whole extension;
- `core/canonical`: `IsSeparable` and `Algebra.IsSeparable`;
- `bridge/view`: `IsSeparable.tower_top` and `Algebra.isSeparable_tower_top_of_isSeparable`,
  which restate the source lemma directly on the canonical owners.

This file should therefore stay recall-only: any local theorem shell would duplicate upstream
owner-derived API without adding new mathematics or a better statement surface. -/

/- Lemma 9.12.3 (1): the source states this for a tower of algebraic field extensions `K/E/F`,
but the canonical theorem `IsSeparable.tower_top` proves the same conclusion in any tower of
fields: if `α : K` is separable over `F`, then it is separable over `E`. -/
recall IsSeparable.tower_top

/- Lemma 9.12.3 (2): the source likewise assumes a tower of algebraic field extensions, while the
canonical theorem `Algebra.isSeparable_tower_top_of_isSeparable` is stronger and shows directly
that if `K/F` is separable, then `K/E` is separable. -/
recall Algebra.isSeparable_tower_top_of_isSeparable

/-! ### Lemma_9_12_4 (from Chap09) -/
universe u

open Polynomial

/- Domain-style sampling:
- primary domain: irreducible polynomials over a field, their separability, and the
  positive-characteristic `expand`/contraction interface;
- sampled owner declarations:
  `Polynomial.separable_iff_derivative_ne_zero`,
  `Polynomial.separable_def`,
  `Polynomial.HasSeparableContraction.isSeparableContraction`,
  `Irreducible.hasSeparableContraction`;
- best owner abstractions:
  `Polynomial.separable_iff_derivative_ne_zero` for the derivative criterion and
  `Polynomial.HasSeparableContraction` for the positive-characteristic factorization;
- primitive data: an irreducible polynomial `P : F[X]`;
- derived API: the source-facing `or` and existence reformulations below, together with their
  coprimeness companions.

Layer triage:
- `source-facing`: the four bridge theorems in this file;
- `core/canonical`: the two recalled owner declarations above;
- `bridge/view`: the coprimeness restatements obtained from `Polynomial.separable_def`.
-/

/- Lemma 9.12.1: the irreducible-case derivative criterion is the canonical theorem
`Polynomial.separable_iff_derivative_ne_zero`; the source-facing `or` reformulation below is only
its textbook bridge. -/
recall Polynomial.separable_iff_derivative_ne_zero

/- Lemma 9.12.1: the positive-characteristic factorization is organized by the owner abstraction
`Polynomial.HasSeparableContraction`, produced canonically for irreducibles by
`Irreducible.hasSeparableContraction`. The source-facing existence theorem below unpacks this owner
and adds the irreducibility of the contracted factor. -/
recall Irreducible.hasSeparableContraction

variable {F : Type u} [Field F] {P : F[X]}

/-- Helper for Lemma 9.12.1: an irreducible polynomial is separable unless its derivative
vanishes. -/
theorem irreducible_separable_or_derivative_eq_zero (hP : Irreducible P) :
    P.Separable ∨ P.derivative = 0 := by
  -- Split along the source-proof dichotomy: either the derivative is already zero or the
  -- owner criterion turns non-vanishing into separability.
  by_cases hderiv : P.derivative = 0
  · exact Or.inr hderiv
  · exact Or.inl <| (separable_iff_derivative_ne_zero hP).2 hderiv

/-- Helper for Lemma 9.12.1: via `Polynomial.separable_def`, the textbook wording is that an
irreducible polynomial is coprime to its derivative unless the derivative vanishes. -/
theorem irreducible_isCoprime_derivative_or_derivative_eq_zero (hP : Irreducible P) :
    IsCoprime P P.derivative ∨ P.derivative = 0 := by
  -- This is only the source-facing rewrite of separability into coprimeness with the derivative.
  simpa [separable_def] using irreducible_separable_or_derivative_eq_zero hP

/-- Helper for Lemma 9.12.1: if an irreducible polynomial has zero derivative, then the base
field has positive characteristic. -/
lemma characteristic_positive_of_irreducible_derivative_eq_zero
    (hP : Irreducible P) (hderiv : P.derivative = 0) :
    0 < ringChar F := by
  -- In characteristic zero, irreducibility forces separability, contradicting the zero derivative.
  have hchar_ne_zero : ringChar F ≠ 0 := by
    intro hchar
    letI : CharZero F := (CharP.ringChar_zero_iff_CharZero F).1 hchar
    exact (separable_iff_derivative_ne_zero hP).1 hP.separable hderiv
  exact Nat.pos_of_ne_zero hchar_ne_zero

/-- Lemma 9.12.1: if an irreducible polynomial over a field has zero derivative, then the field
has positive characteristic and the polynomial is an iterated `expand` of an irreducible
separable polynomial. -/
theorem exists_irreducible_separable_expand_of_derivative_eq_zero
    (hP : Irreducible P) (hderiv : P.derivative = 0) :
    0 < ringChar F ∧
      ∃ n : ℕ, ∃ Q : F[X],
        P = expand F ((ringChar F) ^ n) Q ∧ Irreducible Q ∧ Q.Separable := by
  -- First isolate the characteristic obstruction from the zero-derivative hypothesis.
  have hchar : 0 < ringChar F :=
    characteristic_positive_of_irreducible_derivative_eq_zero hP hderiv
  have hchar_ne_zero : ringChar F ≠ 0 := Nat.ne_of_gt hchar
  letI : NeZero (ringChar F) := ⟨hchar_ne_zero⟩
  letI : Fact (ringChar F).Prime := CharP.char_is_prime_of_pos F (ringChar F)
  -- Then use the canonical separable contraction supplied by mathlib for irreducible polynomials.
  have hcontraction := hP.hasSeparableContraction (ringChar F)
  obtain ⟨hQsep, n, hQP⟩ := hcontraction.isSeparableContraction
  -- The `expand` equality transfers irreducibility from `P` back to the contraction `Q`.
  have hQirr : Irreducible hcontraction.contraction :=
    of_irreducible_expand_pow hchar_ne_zero (hQP ▸ hP)
  exact ⟨hchar, n, hcontraction.contraction, hQP.symm, hQirr, hQsep⟩

/-- Helper for Lemma 9.12.1: rewriting separability as coprimeness with the derivative recovers
the textbook formulation of the positive-characteristic case. -/
theorem exists_irreducible_isCoprime_derivative_expand_of_derivative_eq_zero
    (hP : Irreducible P) (hderiv : P.derivative = 0) :
    0 < ringChar F ∧
      ∃ n : ℕ, ∃ Q : F[X],
        P = expand F ((ringChar F) ^ n) Q ∧ Irreducible Q ∧ IsCoprime Q Q.derivative := by
  -- This is the same factorization theorem, viewed through `Polynomial.separable_def`.
  simpa [separable_def] using
    exists_irreducible_separable_expand_of_derivative_eq_zero hP hderiv

/-! ### Lemma_9_12_5 (from Chap09) -/
universe u v

variable {F : Type u} [Field F]
variable {p : ℕ} [Fact p.Prime] [CharP F p]
variable {Ω : Type v} [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]

/- Source/core/bridge triage for Lemma 9.12.5:
- `source-facing`: the root-count statement for `P.comp (X ^ p)`;
- `core/canonical`: `Polynomial.natSepDegree` and its characteristic-`p` invariance
  `Polynomial.natSepDegree_expand`;
- `bridge/view`: `Polynomial.deg_s_eq_card_rootSet`, identifying separable degree with the number
  of distinct roots in an algebraic closure.
- primary domain: separable degree of polynomials in characteristic `p` and its interpretation as
  the number of distinct roots in an algebraic closure;
- sampled owner declarations:
  * `Polynomial.natSepDegree`
  * `Polynomial.natSepDegree_expand`
  * `Polynomial.deg_s_eq_card_rootSet`
- best owner abstraction: `Polynomial.natSepDegree`; counting roots in an algebraic closure is
  derived API coming from `Polynomial.deg_s_eq_card_rootSet`.
- primitive data: the polynomial `P`;
- ambient context: the characteristic-`p` field structure and an algebraically closed extension;
- derived API: the root-counting equality for `P` and `P.comp (X ^ p)`.
-/

namespace Polynomial

open scoped PolynomialSeparableDegree

/-- Lemma 9.12.5: over an algebraically closed extension of a field of characteristic `p > 0`, a
polynomial `P` and `P(x^p)`, i.e. `P.comp (X ^ p)`, have the same number of distinct roots. -/
theorem card_rootSet_comp_X_pow_eq (P : F[X]) :
    Fintype.card ((P.comp (X ^ p)).rootSet Ω) = Fintype.card (P.rootSet Ω) := by
  rw [← deg_s_eq_card_rootSet Ω (P.comp (X ^ p)), ← deg_s_eq_card_rootSet Ω P]
  simpa [pow_one, expand_eq_comp_X_pow] using
    (natSepDegree_expand P p : deg_s(expand F (p ^ 1) P) = deg_s(P))

end Polynomial

/-! ### Definition_9_12_6 (from Chap09) -/
universe u v

namespace Polynomial

/- Domain-style sampling for Definition 9.12.6:
- primary domain: separable degree of polynomials over a field and its root-count realization over
  an algebraically closed extension;
- sampled owner declarations:
  * `Polynomial.natSepDegree`
  * `Polynomial.natSepDegree_eq_of_isAlgClosed`
  * `Polynomial.rootSet_def`
- best owner abstraction: the polynomial owner `P : F[X]` with canonical separable degree
  `P.natSepDegree`;
- primitive data: only the polynomial `P`;
- derived API: the textbook notation `deg_s(P)` and the root-set cardinality bridge below.

Source/core/bridge triage:
- `source-facing`: the textbook separable-degree notation `deg_s(P)`
- `core/canonical`: `natSepDegree`
- `bridge/view`: counting distinct roots in an algebraic closure via `rootSet`

The primitive owner is the canonical mathlib definition `natSepDegree`; the root-set formula is
derived API coming from `natSepDegree_eq_of_isAlgClosed`.
-/
scoped[PolynomialSeparableDegree] notation:max "deg_s(" P ")" => Polynomial.natSepDegree P

open scoped PolynomialSeparableDegree

variable {F : Type u} [Field F]

section

variable (Ω : Type v) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]

/-- Source-facing reformulation of Definition 9.12.6 over an algebraic closure: `deg_s(P)` is the
cardinality of the set of roots of `P` in `Ω`. This equality in fact holds for every
polynomial. -/
theorem deg_s_eq_card_rootSet (P : F[X]) :
    deg_s(P) = Fintype.card (P.rootSet Ω) := by
  classical
  simpa only [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe] using
    (natSepDegree_eq_of_isAlgClosed Ω P)

end

end Polynomial

/-! ### Lemma_9_12_8 (from Chap09) -/
open Polynomial
open Situation_9_12_7
open scoped Situation_9_12_7

noncomputable section

universe u v w

namespace Situation_9_12_7

section

variable {F : Type u} {K : Type v} {L : Type w}
variable [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
variable [FiniteDimensional F K]
variable {n : ℕ}

variable (F)
variable (α : Fin n → K)

local notation "K[" i "]" => stage F α i
local notation "P[" i "]" => P[F, α; i]

/- Domain-style sampling:
* primary domain: towers of simple field extensions, transported minimal polynomials, and the
  canonical simple-adjoin embedding API;
* sampled owner declarations:
  `K[F, α; i]`,
  `P[F, α; i]`,
  `IntermediateField.algHomAdjoinIntegralEquiv`,
  `IntermediateField.equivOfEq`;
* best owner abstraction: the source-facing tuple predicate should be built from the successive
  root clauses for the chapter owner polynomials `P[F, α; i]`, while the corresponding stage
  embeddings are derived recursively from those clauses through the canonical simple-adjoin owner;
* primitive data: only the transported root conditions for the tuple `β`;
* derived API: the recursively constructed family of stage embeddings and the resulting bijection
  with `F`-algebra embeddings `K →ₐ[F] L`.
-/

-- Proof sketch: unfold the source-facing stage as an adjoin of the empty prefix of generators.
/-- The zeroth stage in the generator tower is the base field. -/
theorem stage_zero_eq_bot : K[(0 : Fin (n + 1))] = (⊥ : IntermediateField F K) := by
  -- The zeroth prefix contains no generators, so adjoining it yields the base field.
  rw [show K[(0 : Fin (n + 1))] =
      IntermediateField.adjoin F
        ({x : K | ∃ j : Fin n, j.1 < (0 : Fin (n + 1)).1 ∧ α j = x}) by
      rfl]
  rw [IntermediateField.adjoin_eq_bot_iff]
  intro x hx
  rcases hx with ⟨j, hj, rfl⟩
  exact (Nat.not_lt_zero _ hj).elim

-- Proof sketch: compare the prefix of generators at `i + 1` with the previous prefix plus
-- the single new generator `α i`.
/-- The successor stage is obtained by adjoining the next generator to the preceding stage. -/
theorem stage_succ_eq_adjoin (i : Fin n) :
    K[i.succ] =
      (IntermediateField.adjoin K[i.castSucc] ({α i} : Set K)).restrictScalars F := by
  -- The next stage is generated by the earlier prefix together with the new element `α i`.
  rw [show K[i.succ] =
      IntermediateField.adjoin F ({x : K | ∃ j : Fin n, j.1 < i.succ.1 ∧ α j = x}) by
      rfl]
  rw [IntermediateField.restrictScalars_adjoin]
  apply le_antisymm
  · -- Every generator in the larger prefix is either old or is the new generator `α i`.
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rcases hx with ⟨j, hj, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hji
    · have hmem : α j ∈ K[i.castSucc] := by
        change α j ∈
          IntermediateField.adjoin F ({x : K | ∃ k : Fin n, k.1 < i.castSucc.1 ∧ α k = x})
        exact IntermediateField.mem_adjoin_of_mem F ⟨j, hj, rfl⟩
      exact IntermediateField.mem_adjoin_of_mem F (Or.inl hmem)
    · have hji' : j = i := Fin.ext hji
      subst hji'
      exact IntermediateField.mem_adjoin_of_mem F (Or.inr (by simp))
  · -- Conversely, both the previous stage and the new generator lie in the successor stage.
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rcases hx with hx | hx
    · have hle :
        K[i.castSucc] ≤
          IntermediateField.adjoin F ({x : K | ∃ j : Fin n, j.1 < i.succ.1 ∧ α j = x}) := by
        rw [show K[i.castSucc] =
            IntermediateField.adjoin F ({x : K | ∃ j : Fin n, j.1 < i.castSucc.1 ∧ α j = x}) by
            rfl]
        rw [IntermediateField.adjoin_le_iff]
        intro y hy
        rcases hy with ⟨j, hj, rfl⟩
        exact IntermediateField.mem_adjoin_of_mem F ⟨j, Nat.lt_succ_of_lt hj, rfl⟩
      exact hle hx
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact IntermediateField.mem_adjoin_of_mem F ⟨i, Nat.lt_succ_self i.1, rfl⟩

private noncomputable def stageZeroEmbedding : K[(0 : Fin (n + 1))] →ₐ[F] L :=
  (Algebra.ofId F L).comp
    (((IntermediateField.equivOfEq (stage_zero_eq_bot F α)).trans
      (IntermediateField.botEquiv F K)).toAlgHom)

private noncomputable def successiveRootDataAux (m : ℕ) (hm : m ≤ n) (β : Fin n → L) :
    Σ p : Prop, p → K[⟨m, Nat.lt_succ_of_le hm⟩] →ₐ[F] L := by
  classical
  exact match m with
  | 0 => ⟨True, fun _ ↦ stageZeroEmbedding F α⟩
  | k + 1 =>
      let hk : k ≤ n := Nat.le_of_succ_le hm
      let i : Fin n := ⟨k, Nat.lt_of_succ_le hm⟩
      let prev := successiveRootDataAux k hk β
      let rootProp : Prop :=
        if hp : prev.1 then
          ((P[i]).map (prev.2 hp).toRingHom).IsRoot (β i)
        else
          False
      ⟨prev.1 ∧ rootProp, fun h ↦
        let hp : prev.1 := h.1
        let ψ := prev.2 hp
        let _ : Algebra K[i.castSucc] L := ψ.toRingHom.toAlgebra
        let _ : IsScalarTower F K[i.castSucc] L :=
          IsScalarTower.of_algebraMap_eq' (ψ.comp_algebraMap_of_tower F).symm
        let _ : Module.Finite K[i.castSucc] K := FiniteDimensional.right F K[i.castSucc] K
        let hαi : IsIntegral K[i.castSucc] (α i) :=
          (Algebra.IsIntegral.of_finite K[i.castSucc] K).isIntegral (α i)
        have hroot : ((P[i]).map ψ.toRingHom).IsRoot (β i) := by
          dsimp [rootProp] at h
          simpa [hp] using h.2
        have hroot' : Polynomial.aeval (β i) (P[i]) = 0 := by
          change Polynomial.eval₂ ψ.toRingHom (β i) (P[i]) = 0
          rw [Polynomial.eval₂_eq_eval_map]
          simpa [Polynomial.IsRoot] using hroot
        let ψ' :=
          (IntermediateField.algHomAdjoinIntegralEquiv K[i.castSucc] hαi).symm
            ⟨β i, mem_aroots.mpr ⟨minpoly.ne_zero hαi, hroot'⟩⟩
        (ψ'.restrictScalars F).comp
          (IntermediateField.equivOfEq (stage_succ_eq_adjoin F α i)).toAlgHom⟩

private noncomputable def successiveRootData (i : Fin (n + 1)) (β : Fin n → L) :
    Σ p : Prop, p → K[i] →ₐ[F] L := by
  cases i with
  | mk m hm =>
      simpa [stage] using successiveRootDataAux F α m (Nat.le_of_lt_succ hm) β

/-- The stagewise root condition from Lemma 9.12.8 up to stage `i`: recursively adjoining
`β 0, ..., β (i - 1)` yields stage embeddings `φ_j`, and at each successor step `β j` is a root
of the transported polynomial `P_j` over the preceding embedding. -/
def IsSuccessiveRootTupleUpTo (i : Fin (n + 1)) (β : Fin n → L) : Prop :=
  (successiveRootData F α i β).1

/-- The recursively constructed stage embedding `φ_i : K_i → L` attached to a tuple satisfying the
stagewise root conditions up to `i`. -/
noncomputable def stageEmbedding (i : Fin (n + 1)) (β : Fin n → L)
    (hβ : IsSuccessiveRootTupleUpTo F α i β) :
    K[i] →ₐ[F] L :=
  (successiveRootData F α i β).2 hβ

/-- The successor-stage root clause for the tuple `β` at stage `i`: once the previous stage
embedding `K_i →ₐ[F] L` has been recursively constructed, the next coordinate `β i` is a root of
the transported polynomial `P_i`. -/
def IsRootAtStage (i : Fin n) (β : Fin n → L) : Prop :=
  ∀ hβ : IsSuccessiveRootTupleUpTo F α i.castSucc β,
    ((P[i]).map (stageEmbedding F α i.castSucc β hβ).toRingHom).IsRoot (β i)

/-- The initial stage condition is empty. -/
@[simp] theorem isSuccessiveRootTupleUpTo_zero (β : Fin n → L) :
    IsSuccessiveRootTupleUpTo F α 0 β := by
  -- At stage zero the recursive data starts from the tautological proposition `True`.
  simp [IsSuccessiveRootTupleUpTo, successiveRootData, successiveRootDataAux]

-- Proof sketch: unfold the recursive construction at the base stage.
/-- The initial stage embedding is the canonical base embedding `F →ₐ[F] L`. -/
@[simp] theorem stageEmbedding_zero (β : Fin n → L)
    (hβ : IsSuccessiveRootTupleUpTo F α 0 β) :
    stageEmbedding F α 0 β hβ = stageZeroEmbedding F α := by
  -- The stage-zero constructor returns the canonical base embedding by definition.
  simp [stageEmbedding, IsSuccessiveRootTupleUpTo, successiveRootData, successiveRootDataAux]

-- Proof sketch: the recursive predicate is proof-irrelevant, so the constructed embedding does
-- not depend on the particular proof of the stage condition.
@[simp] theorem stageEmbedding_congr {i : Fin (n + 1)} {β : Fin n → L}
    {hβ hβ' : IsSuccessiveRootTupleUpTo F α i β} :
    stageEmbedding F α i β hβ = stageEmbedding F α i β hβ' := by
  -- The recursive constructor is a fixed function on a proposition, so equal proofs give
  -- identical embeddings.
  unfold stageEmbedding
  exact congrArg ((successiveRootData F α i β).2) (Subsingleton.elim hβ hβ')

-- Proof sketch: unfold one step of the recursive auxiliary construction and simplify the
-- conditional carrying the previous-stage proof.
private theorem successiveRootDataAux_succ_exists_iff
    (k : ℕ) (hm : k + 1 ≤ n) (β : Fin n → L) :
    (successiveRootDataAux F α (k + 1) hm β).1 ↔
      ∃ hprev : (successiveRootDataAux F α k (Nat.le_of_succ_le hm) β).1,
        ((P[⟨k, Nat.lt_of_succ_le hm⟩]).map
          ((successiveRootDataAux F α k (Nat.le_of_succ_le hm) β).2 hprev).toRingHom).IsRoot
          (β ⟨k, Nat.lt_of_succ_le hm⟩) := by
  -- Unfold one recursive layer: the successor proposition is precisely the previous stage
  -- together with the transported root condition for the new coordinate.
  dsimp [successiveRootDataAux]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    simpa [h.1] using h.2
  · rintro ⟨hprev, hroot⟩
    refine ⟨hprev, ?_⟩
    simpa [hprev] using hroot

-- Proof sketch: specialize the auxiliary successor characterization to the finite index `i`.
private theorem isSuccessiveRootTupleUpTo_succ_exists_iff (i : Fin n) (β : Fin n → L) :
    IsSuccessiveRootTupleUpTo F α i.succ β ↔
      ∃ hprev : IsSuccessiveRootTupleUpTo F α i.castSucc β,
        ((P[i]).map (stageEmbedding F α i.castSucc β hprev).toRingHom).IsRoot (β i) := by
  -- This is the finite-index restatement of the recursive successor clause above.
  cases i with
  | mk k hk =>
      simpa [IsSuccessiveRootTupleUpTo, stageEmbedding, successiveRootData] using
        (successiveRootDataAux_succ_exists_iff (F := F) (α := α) k (Nat.succ_le_of_lt hk) β)

-- Proof sketch: combine the previous-stage existence with proof-irrelevance of the recursively
-- constructed embedding.
/-- The recursive stage condition at `k + 1` says that the previous stage has already been built
and that `β k` is a root of the transported polynomial `P_k` over the preceding stage embedding
`φ_k`. -/
theorem isSuccessiveRootTupleUpTo_succ_iff (i : Fin n) (β : Fin n → L) :
    IsSuccessiveRootTupleUpTo F α i.succ β ↔
      IsSuccessiveRootTupleUpTo F α i.castSucc β ∧ IsRootAtStage F α i β := by
  constructor
  · intro hsucc
    rcases (isSuccessiveRootTupleUpTo_succ_exists_iff (F := F) (α := α) i β).mp hsucc with
      ⟨hprev, hroot⟩
    refine ⟨hprev, ?_⟩
    intro hprev'
    simpa [IsRootAtStage, stageEmbedding_congr (F := F) (α := α) (hβ := hprev) (hβ' := hprev')]
      using hroot
  · rintro ⟨hprev, hroot⟩
    exact (isSuccessiveRootTupleUpTo_succ_exists_iff (F := F) (α := α) i β).mpr
      ⟨hprev, hroot hprev⟩

/-- A tuple `β` satisfies the successive root conditions of Lemma 9.12.8 if its full stagewise
construction reaches stage `n`. This is the concise chapter shorthand for the recursive owner
predicate `IsSuccessiveRootTupleUpTo`. -/
abbrev IsSuccessiveRootTuple (β : Fin n → L) : Prop :=
  IsSuccessiveRootTupleUpTo F α (Fin.last n) β

end

end Situation_9_12_7

section

variable (F : Type u) (K : Type v) (L : Type w)
variable [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
variable [FiniteDimensional F K]
variable {n : ℕ}

variable {F K}
variable {L}

-- Proof sketch: induct on the stage number, comparing the recursively constructed stage map with
-- the honest restriction of the ambient embedding `φ`.
/-- Helper for Lemma 9.12.8: at every stage, the recursive construction applied to the tuple
`φ(α_i)` recovers the actual restriction of `φ` to that stage. -/
private lemma exists_stage_embedding_eq_restrict (α : Fin n → K) (φ : K →ₐ[F] L)
    (i : Fin (n + 1)) :
    ∃ hβ : IsSuccessiveRootTupleUpTo F α i (φ ∘ α),
      stageEmbedding F α i (φ ∘ α) hβ = φ.comp (K[F, α; i]).val := by
  cases i with
  | mk m hm =>
      have haux :
          ∀ m' (hm' : m' ≤ n),
            ∃ hβ : (successiveRootDataAux F α m' hm' (φ ∘ α)).1,
              (successiveRootDataAux F α m' hm' (φ ∘ α)).2 hβ =
                φ.comp (K[F, α; ⟨m', Nat.lt_succ_of_le hm'⟩]).val := by
        intro m'
        induction m' with
        | zero =>
            intro hm'
            refine ⟨trivial, ?_⟩
            -- At stage zero there is only the canonical `F`-algebra map into `L`.
            let e : K[F, α; 0] ≃ₐ[F] F :=
              (IntermediateField.equivOfEq (stage_zero_eq_bot F α)).trans
                (IntermediateField.botEquiv F K)
            have hsub : Subsingleton (K[F, α; 0] →ₐ[F] L) := by
              refine ⟨fun f g => ?_⟩
              have hfg :
                  (AlgEquiv.arrowCongr e (AlgEquiv.refl : L ≃ₐ[F] L)) f =
                    (AlgEquiv.arrowCongr e (AlgEquiv.refl : L ≃ₐ[F] L)) g := by
                exact Subsingleton.elim _ _
              exact (AlgEquiv.arrowCongr e (AlgEquiv.refl : L ≃ₐ[F] L)).injective hfg
            exact hsub.elim _ _
        | succ k ih =>
            intro hm'
            let j : Fin n := ⟨k, Nat.lt_of_succ_le hm'⟩
            obtain ⟨hprev, hprev_eq⟩ := ih (Nat.le_of_succ_le hm')
            let Kprev : IntermediateField F K := K[F, α; j.castSucc]
            let ψaux : Kprev →ₐ[F] L :=
              (successiveRootDataAux F α k (Nat.le_of_succ_le hm') (φ ∘ α)).2 hprev
            letI : Algebra Kprev L := ψaux.toRingHom.toAlgebra
            letI : IsScalarTower F Kprev L := IsScalarTower.of_algebraMap_eq' (by
              ext x
              exact (ψaux.commutes x).symm)
            let φKprev : K →ₐ[Kprev] L :=
              { toRingHom := φ.toRingHom
                commutes' := by
                  intro x
                  simpa [ψaux, Kprev] using
                    (congrArg (fun f : Kprev →ₐ[F] L => f x) hprev_eq).symm }
            have hroot_stage : Polynomial.aeval ((φ ∘ α) j) (P[F, α; j]) = 0 := by
              -- Evaluate the minimal polynomial of `α j` through the induced `K_j`-algebra map.
              calc
                Polynomial.aeval ((φ ∘ α) j) (P[F, α; j]) =
                    φKprev (Polynomial.aeval (α j) (P[F, α; j])) := by
                  exact Polynomial.aeval_algHom_apply φKprev (α j) (P[F, α; j])
                _ = 0 := by
                  rw [minpoly.aeval, map_zero]
            have hroot :
                ((P[F, α; j]).map ψaux.toRingHom).IsRoot
                  ((φ ∘ α) j) := by
              -- Rewrite the transported root clause back into the `aeval` identity above.
              rw [Polynomial.IsRoot, ← Polynomial.eval₂_eq_eval_map]
              simpa [Polynomial.aeval_def, ψaux] using hroot_stage
            have hsucc :
                (successiveRootDataAux F α (k + 1) hm' (φ ∘ α)).1 := by
              -- The successor proposition asks for the predecessor proof and the next root clause.
              dsimp [successiveRootDataAux]
              refine ⟨hprev, ?_⟩
              simpa [hprev, ψaux] using hroot
            refine ⟨hsucc, ?_⟩
            -- Route correction: compare the recursive successor map with the restricted `φ`
            -- through the simple-adjoin universal property, rather than unfolding the whole adjoin.
            let S : IntermediateField Kprev K := IntermediateField.adjoin Kprev ({α j} : Set K)
            let hαj : IsIntegral Kprev (α j) :=
              (Algebra.IsIntegral.of_finite Kprev K).isIntegral (α j)
            let ψ :
                S →ₐ[K[F, α; j.castSucc]] L := by
              exact
                { toRingHom := φ.toRingHom.comp S.val.toRingHom
                  commutes' := by
                    intro x
                    simpa [ψaux, Kprev] using
                      (congrArg (fun f : Kprev →ₐ[F] L => f x) hprev_eq).symm }
            have hmem_root : (φ ∘ α) j ∈ (P[F, α; j]).aroots L := by
              -- The same `aeval` identity is exactly the root witness needed for the simple adjoin.
              rw [mem_aroots]
              exact ⟨minpoly.ne_zero hαj, hroot_stage⟩
            have hψ :
                ((IntermediateField.algHomAdjoinIntegralEquiv Kprev hαj).symm
                    ⟨(φ ∘ α) j, hmem_root⟩) = ψ := by
              -- Both `K_j⟮α_j⟯ → L` maps are determined by the image of the new generator.
              have hgen :
                  ((IntermediateField.algHomAdjoinIntegralEquiv Kprev hαj).symm
                      ⟨(φ ∘ α) j, hmem_root⟩)
                    (IntermediateField.AdjoinSimple.gen Kprev (α j)) =
                    ψ (IntermediateField.AdjoinSimple.gen Kprev (α j)) := by
                rw [IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen]
                rfl
              apply IntermediateField.adjoin_algHom_ext (F := Kprev)
              intro x hx
              rcases Set.mem_singleton_iff.mp hx with rfl
              simpa using hgen
            dsimp [successiveRootDataAux]
            -- The successor-stage map is the simple-adjoin extension of the predecessor map.
            have hrestrict :
                (ψ.restrictScalars F).comp
                    (IntermediateField.equivOfEq (stage_succ_eq_adjoin F α j)).toAlgHom =
                  φ.comp (K[F, α; j.succ]).val := by
              ext x
              rfl
            have hψF :
                (AlgHom.restrictScalars F
                    ((IntermediateField.algHomAdjoinIntegralEquiv Kprev hαj).symm
                      ⟨(φ ∘ α) j, hmem_root⟩)) =
                  ψ.restrictScalars F := by
              simpa using congrArg (AlgHom.restrictScalars F) hψ
            calc
              (AlgHom.restrictScalars F
                    ((IntermediateField.algHomAdjoinIntegralEquiv Kprev hαj).symm
                      ⟨(φ ∘ α) j, hmem_root⟩)).comp
                  (IntermediateField.equivOfEq (stage_succ_eq_adjoin F α j)).toAlgHom =
                  (ψ.restrictScalars F).comp
                    (IntermediateField.equivOfEq (stage_succ_eq_adjoin F α j)).toAlgHom := by
                rw [hψF]
              _ = φ.comp (K[F, α; j.succ]).val := hrestrict
      rcases haux m (Nat.le_of_lt_succ hm) with ⟨hβ, hhβ⟩
      refine ⟨?_, ?_⟩
      · simpa [IsSuccessiveRootTupleUpTo, successiveRootData] using hβ
      · simpa [stageEmbedding, successiveRootData] using hhβ

-- Proof sketch: transport each minimal-polynomial relation along the algebra homomorphism.
/-- Evaluating an `F`-algebra embedding `K → L` on the chosen generators produces a
tuple satisfying the successive root conditions. The algebraic-closure case from the source is a
specialization of this canonical statement. -/
lemma algHom_isSuccessiveRootTuple (α : Fin n → K) (φ : K →ₐ[F] L) :
    IsSuccessiveRootTuple F α (φ ∘ α) := by
  -- The full tuple condition is exactly the last-stage instance of the stagewise construction.
  exact (exists_stage_embedding_eq_restrict (F := F) (L := L) α φ (Fin.last n)).choose

/-- Helper for Lemma 9.12.8: at the final stage, the recursive embedding attached to the tuple
`φ(α_i)` is exactly the restriction of `φ` to the top stage. -/
private lemma stageEmbedding_full_eq_algHom_restrict (α : Fin n → K) (φ : K →ₐ[F] L) :
    stageEmbedding F α (Fin.last n) (φ ∘ α) (algHom_isSuccessiveRootTuple (F := F) (L := L) α φ) =
      φ.comp (K[F, α; Fin.last n]).val := by
  -- The final-stage existence theorem already builds this restriction map; only proof
  -- irrelevance is needed to replace its witness by the canonical tuple proof.
  simpa [algHom_isSuccessiveRootTuple] using
    (exists_stage_embedding_eq_restrict (F := F) (L := L) α φ (Fin.last n)).choose_spec

/-- Helper for Lemma 9.12.8: two embeddings `K →ₐ[F] L` agreeing on the top stage generated by
`α` agree everywhere once that stage is all of `K`. -/
private lemma algHom_ext_of_top_stage_eq (α : Fin n → K)
    (hα : K[F, α; Fin.last n] = ⊤) {φ ψ : K →ₐ[F] L}
    (h : φ.comp (K[F, α; Fin.last n]).val = ψ.comp (K[F, α; Fin.last n]).val) :
    φ = ψ := by
  -- Transport an arbitrary element of `K` back to the top stage and compare the two restrictions
  -- there.
  let eTop : K[F, α; Fin.last n] ≃ₐ[F] K :=
    (IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv
  ext x
  have hx :
      φ.comp (K[F, α; Fin.last n]).val (eTop.symm x) =
        ψ.comp (K[F, α; Fin.last n]).val (eTop.symm x) := by
    exact congrArg (fun f : K[F, α; Fin.last n] →ₐ[F] L => f (eTop.symm x)) h
  simpa [eTop] using hx

/-- Helper for Lemma 9.12.8: at any stage, the recursive embedding sends each already adjoined
generator to the prescribed tuple entry. -/
private lemma stageEmbedding_apply_generator_at_stage
    (α : Fin n → K) :
    ∀ m (hm : m ≤ n) (β : Fin n → L)
      (hβ : (successiveRootDataAux F α m hm β).1)
      (i : Fin n) (hi : i.1 < m),
        (successiveRootDataAux F α m hm β).2 hβ
            ⟨α i, IntermediateField.mem_adjoin_of_mem F ⟨i, hi, rfl⟩⟩ =
          β i := by
  intro m
  induction m with
  | zero =>
      intro hm β hβ i hi
      exact (Nat.not_lt_zero _ hi).elim
  | succ k ih =>
      intro hm β hβ i hi
      let j : Fin n := ⟨k, Nat.lt_of_succ_le hm⟩
      rcases (Nat.lt_succ_iff_lt_or_eq.mp hi) with hi' | hi'
      · -- Old generators are handled by restricting the successor-stage map to the previous stage.
        let hprev :
            (successiveRootDataAux F α k (Nat.le_of_succ_le hm) β).1 := hβ.1
        let ψprev :
            K[F, α; j.castSucc] →ₐ[F] L :=
          (successiveRootDataAux F α k (Nat.le_of_succ_le hm) β).2 hprev
        letI : Algebra K[F, α; j.castSucc] L := ψprev.toRingHom.toAlgebra
        letI : IsScalarTower F K[F, α; j.castSucc] L :=
          IsScalarTower.of_algebraMap_eq' (ψprev.comp_algebraMap_of_tower F).symm
        let hαj : IsIntegral K[F, α; j.castSucc] (α j) :=
          (Algebra.IsIntegral.of_finite K[F, α; j.castSucc] K).isIntegral (α j)
        let xprev : K[F, α; j.castSucc] :=
          ⟨α i, IntermediateField.mem_adjoin_of_mem F ⟨i, hi', rfl⟩⟩
        let ψnext :
            IntermediateField.adjoin K[F, α; j.castSucc] ({α j} : Set K) →ₐ[K[F, α; j.castSucc]] L :=
          (IntermediateField.algHomAdjoinIntegralEquiv K[F, α; j.castSucc] hαj).symm
            ⟨β j, by
              have hroot' :
                  ((P[F, α; j]).map ψprev.toRingHom).IsRoot (β j) := by
                dsimp [successiveRootDataAux] at hβ
                simpa [hβ.1, ψprev] using hβ.2
              have hroot :
                  Polynomial.aeval (β j) (P[F, α; j]) = 0 := by
                change Polynomial.eval₂ ψprev.toRingHom (β j) (P[F, α; j]) = 0
                rw [Polynomial.eval₂_eq_eval_map]
                simpa [Polynomial.IsRoot] using hroot' 
              rw [mem_aroots]
              exact ⟨minpoly.ne_zero hαj, hroot⟩⟩
        have hx :
            ((IntermediateField.equivOfEq (stage_succ_eq_adjoin F α j)).toAlgHom
              ⟨α i, IntermediateField.mem_adjoin_of_mem F ⟨i, hi, rfl⟩⟩ : 
                IntermediateField.adjoin K[F, α; j.castSucc] ({α j} : Set K)) =
              algebraMap K[F, α; j.castSucc]
                (IntermediateField.adjoin K[F, α; j.castSucc] ({α j} : Set K)) xprev := by
          rfl
        -- The successor map agrees with the previous-stage map on the old stage because the
        -- simple-adjoin extension commutes with the `K_j`-algebra structure.
        dsimp [successiveRootDataAux]
        have hx' :
            ψnext ((IntermediateField.equivOfEq (stage_succ_eq_adjoin F α j)).toAlgHom
              ⟨α i, IntermediateField.mem_adjoin_of_mem F ⟨i, hi, rfl⟩⟩) =
              ψnext (algebraMap K[F, α; j.castSucc]
                (IntermediateField.adjoin K[F, α; j.castSucc] ({α j} : Set K)) xprev) := by
          simpa [ψnext] using congrArg ψnext hx
        calc
          ψnext ((IntermediateField.equivOfEq (stage_succ_eq_adjoin F α j)).toAlgHom
              ⟨α i, IntermediateField.mem_adjoin_of_mem F ⟨i, hi, rfl⟩⟩) =
              ψnext (algebraMap K[F, α; j.castSucc]
                (IntermediateField.adjoin K[F, α; j.castSucc] ({α j} : Set K)) xprev) := hx'
          _ =
              algebraMap K[F, α; j.castSucc] L xprev := by
            simpa [ψnext] using ψnext.commutes xprev
          _ = ψprev xprev := rfl
          _ = β i := by
            simpa [ψprev, xprev] using ih (Nat.le_of_succ_le hm) β hprev i hi'
      · -- The newly adjoined generator is sent to the chosen root by the simple-adjoin API.
        have hij : i = j := Fin.ext hi'
        subst hij
        let hprev :
            (successiveRootDataAux F α k (Nat.le_of_succ_le hm) β).1 := hβ.1
        let ψprev :
            K[F, α; j.castSucc] →ₐ[F] L :=
          (successiveRootDataAux F α k (Nat.le_of_succ_le hm) β).2 hprev
        letI : Algebra K[F, α; j.castSucc] L := ψprev.toRingHom.toAlgebra
        letI : IsScalarTower F K[F, α; j.castSucc] L :=
          IsScalarTower.of_algebraMap_eq' (ψprev.comp_algebraMap_of_tower F).symm
        let hαj : IsIntegral K[F, α; j.castSucc] (α j) :=
          (Algebra.IsIntegral.of_finite K[F, α; j.castSucc] K).isIntegral (α j)
        have hroot :
            Polynomial.aeval (β j) (P[F, α; j]) = 0 := by
          have hroot' :
              ((P[F, α; j]).map ψprev.toRingHom).IsRoot (β j) := by
            dsimp [successiveRootDataAux] at hβ
            simpa [hβ.1, ψprev] using hβ.2
          change Polynomial.eval₂ ψprev.toRingHom (β j) (P[F, α; j]) = 0
          rw [Polynomial.eval₂_eq_eval_map]
          simpa [Polynomial.IsRoot] using hroot'
        have hmem_root : β j ∈ (P[F, α; j]).aroots L := by
          rw [mem_aroots]
          exact ⟨minpoly.ne_zero hαj, hroot⟩
        have hx :
            ((IntermediateField.equivOfEq (stage_succ_eq_adjoin F α j)).toAlgHom
              ⟨α j, IntermediateField.mem_adjoin_of_mem F
                ⟨j, Nat.lt_succ_self j.1, rfl⟩⟩ :
                IntermediateField.adjoin K[F, α; j.castSucc] ({α j} : Set K)) =
              IntermediateField.AdjoinSimple.gen K[F, α; j.castSucc] (α j) := by
          rfl
        -- The recursive successor step is built precisely from the simple-adjoin extension that
        -- sends the new generator to `β j`.
        dsimp [successiveRootDataAux]
        have hx' :
            ((IntermediateField.algHomAdjoinIntegralEquiv K[F, α; j.castSucc] hαj).symm
                ⟨β j, hmem_root⟩)
              ((IntermediateField.equivOfEq (stage_succ_eq_adjoin F α j)).toAlgHom
                ⟨α j, IntermediateField.mem_adjoin_of_mem F
                  ⟨j, Nat.lt_succ_self j.1, rfl⟩⟩) =
              ((IntermediateField.algHomAdjoinIntegralEquiv K[F, α; j.castSucc] hαj).symm
                  ⟨β j, hmem_root⟩)
                (IntermediateField.AdjoinSimple.gen K[F, α; j.castSucc] (α j)) := by
          simpa using congrArg
            ((IntermediateField.algHomAdjoinIntegralEquiv K[F, α; j.castSucc] hαj).symm
              ⟨β j, hmem_root⟩) hx
        calc
          ((IntermediateField.algHomAdjoinIntegralEquiv K[F, α; j.castSucc] hαj).symm
                ⟨β j, hmem_root⟩)
              ((IntermediateField.equivOfEq (stage_succ_eq_adjoin F α j)).toAlgHom
                ⟨α j, IntermediateField.mem_adjoin_of_mem F
                  ⟨j, Nat.lt_succ_self j.1, rfl⟩⟩) =
              ((IntermediateField.algHomAdjoinIntegralEquiv K[F, α; j.castSucc] hαj).symm
                  ⟨β j, hmem_root⟩)
                (IntermediateField.AdjoinSimple.gen K[F, α; j.castSucc] (α j)) := hx'
          _ = β j := by
            rw [IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen]

/-- Helper for Lemma 9.12.8: the full recursive embedding sends every chosen generator `α i` to
the prescribed tuple entry `β i`. -/
private lemma stageEmbedding_last_apply_generator (α : Fin n → K)
    (β : Fin n → L) (hβ : IsSuccessiveRootTuple F α β) (i : Fin n) :
    stageEmbedding F α (Fin.last n) β hβ
        ⟨α i, by
          exact IntermediateField.mem_adjoin_of_mem F ⟨i, i.2, rfl⟩⟩ =
      β i := by
  -- Specialize the stagewise generator lemma to the final stage `m = n`.
  simpa [IsSuccessiveRootTuple, stageEmbedding, successiveRootData] using
    stageEmbedding_apply_generator_at_stage (F := F) (L := L) α n (le_rfl : n ≤ n) β hβ i i.2

-- Proof sketch: construct the inverse map recursively along the stage tower using the root
-- conditions and the simple-adjoin universal property, then use the top-stage hypothesis.
/-- Lemma 9.12.8: evaluating an `F`-algebra embedding `K → L` on the chosen generators gives a
bijection from embeddings of `K` into `L` to the subtype of tuples satisfying the successive root
conditions for the polynomials `P_i`. The source's algebraic-closure formulation is the special
case where `L` is an algebraic closure of `F`. -/
lemma embeddingTuple_bijective (α : Fin n → K)
    (hα : K[F, α; Fin.last n] = ⊤) :
    Function.Bijective
      (fun φ : K →ₐ[F] L ↦
        (⟨φ ∘ α, algHom_isSuccessiveRootTuple α φ⟩ :
          {β : Fin n → L // IsSuccessiveRootTuple F α β})) := by
  constructor
  · intro φ ψ h
    -- Equality in the subtype first identifies the tuple of generator-images.
    have htuple : φ ∘ α = ψ ∘ α := congrArg Subtype.val h
    have hφ :=
      stageEmbedding_full_eq_algHom_restrict (F := F) (K := K) (L := L) α φ
    have hψ :=
      stageEmbedding_full_eq_algHom_restrict (F := F) (K := K) (L := L) α ψ
    have hψ_tuple :
        stageEmbedding F α (Fin.last n) (φ ∘ α)
            (by
              simpa [htuple] using
                algHom_isSuccessiveRootTuple (F := F) (L := L) α ψ) =
          ψ.comp (K[F, α; Fin.last n]).val := by
      -- Rewrite the second restriction lemma along the equality of tuples.
      simpa [htuple] using hψ
    -- Route correction: compare the honest embeddings via equality on the top generated stage.
    have hrestrict :
        φ.comp (K[F, α; Fin.last n]).val = ψ.comp (K[F, α; Fin.last n]).val := by
      calc
        φ.comp (K[F, α; Fin.last n]).val =
            stageEmbedding F α (Fin.last n) (φ ∘ α)
              (algHom_isSuccessiveRootTuple (F := F) (L := L) α φ) := by
          symm
          exact hφ
        _ =
            stageEmbedding F α (Fin.last n) (φ ∘ α)
              (by
                simpa [htuple] using
                  algHom_isSuccessiveRootTuple (F := F) (L := L) α ψ) := by
          exact stageEmbedding_congr (F := F) (α := α)
        _ = ψ.comp (K[F, α; Fin.last n]).val := hψ_tuple
    exact algHom_ext_of_top_stage_eq (F := F) (K := K) (L := L) α hα hrestrict
  · intro β
    let eTop : K[F, α; Fin.last n] ≃ₐ[F] K :=
      (IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv
    let φ : K →ₐ[F] L :=
      (stageEmbedding F α (Fin.last n) β.1 β.2).comp eTop.symm.toAlgHom
    refine ⟨φ, ?_⟩
    refine Subtype.ext ?_
    ext i
    -- Evaluate the constructed inverse on each generator using the explicit top-stage lift.
    change
      stageEmbedding F α (Fin.last n) β.1 β.2
          (((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv).symm (α i)) =
        β.1 i
    simpa [eTop] using
      stageEmbedding_last_apply_generator (F := F) (K := K) (L := L) α β.1 β.2 i

end

/-! ### Lemma_9_12_9 (from Chap09) -/
open Polynomial
open Situation_9_12_7
open scoped PolynomialSeparableDegree
open scoped Situation_9_12_7

noncomputable section

universe u v w

section

/- Domain-style sampling for Lemma 9.12.9:
- primary domain: finite field extensions, separable degree, and counting `F`-algebra embeddings
  into algebraically closed extensions;
- sampled owner declarations:
  * `Field.finSepDegree`
  * `Field.finSepDegree_eq_of_isAlgClosed`
  * `Polynomial.natSepDegree_eq_of_isAlgClosed`
  * `embeddingTuple_bijective`
- best owner abstraction: `Field.finSepDegree F K`;
- primitive data: the finite extension `K/F`, the generator tuple `α`, and the induced tower
  stages `K[F, α; i]` with minimal polynomials `P[F, α; i]`;
- derived API: the `Nat.card` formula for `K →ₐ[F] L` after choosing an algebraic closure `L`.

Source/core/bridge triage:
- `source-facing`: the product formula for the finite separable degree `[K : F]_s`;
- `core/canonical`: `Field.finSepDegree F K`;
- `bridge/view`: the cardinality of `K →ₐ[F] L` for algebraically closed `L`.

The owner theorem should therefore avoid carrying a chosen algebraic closure as primitive data.
-/

variable (F : Type u) (K : Type v)
variable [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K]
variable {n : ℕ}

variable (α : Fin n → K)

local notation "K[" i "]" => stage F α i
local notation "P[" i "]" => P[F, α; i]

/-- Helper for Lemma 9.12.9: the range-product form of the first `m` separable-degree factors in
the generator tower. -/
private abbrev prefix_deg_s_prod (m : ℕ) : ℕ :=
  ∏ j ∈ Finset.range m, if hj : j < n then deg_s(P[⟨j, hj⟩]) else 1

/-- Helper for Lemma 9.12.9: the separable degree along the tower multiplies by the next factor at
each successor stage. -/
private lemma stage_finSepDegree_succ (i : Fin n) :
    Field.finSepDegree F K[i.succ] = Field.finSepDegree F K[i.castSucc] * deg_s(P[i]) := by
  let M := IntermediateField.adjoin K[i.castSucc] ({α i} : Set K)
  let _ : Module.Finite K[i.castSucc] K := FiniteDimensional.right F K[i.castSucc] K
  let halg : IsAlgebraic K[i.castSucc] (α i) :=
    ((Algebra.IsIntegral.of_finite K[i.castSucc] K).isIntegral (α i)).isAlgebraic
  have hstep : Field.finSepDegree K[i.castSucc] M = deg_s(P[i]) := by
    -- The simple-adjoin separable degree is the separable degree of the corresponding minpoly.
    simpa [M] using
      (IntermediateField.finSepDegree_adjoin_simple_eq_natSepDegree
        (F := K[i.castSucc]) (E := K) halg)
  -- Rewrite the successor stage to the simple-adjoin stage and apply the tower law.
  rw [stage_succ_eq_adjoin F α i]
  calc
    Field.finSepDegree F M =
        Field.finSepDegree F K[i.castSucc] * Field.finSepDegree K[i.castSucc] M := by
      symm
      exact Field.finSepDegree_mul_finSepDegree_of_isAlgebraic F K[i.castSucc] M
    _ = Field.finSepDegree F K[i.castSucc] * deg_s(P[i]) := by
      rw [hstep]

/-- Helper for Lemma 9.12.9: the separable degree of the `m`th stage is the product of the first
`m` separable-degree factors. -/
private lemma prefix_stage_finSepDegree_eq_prod_deg_s :
    ∀ m : ℕ, ∀ hm : m ≤ n,
      Field.finSepDegree F K[⟨m, Nat.lt_succ_of_le hm⟩] =
        prefix_deg_s_prod (F := F) (K := K) (α := α) m
  | 0, hm => by
      -- The zeroth stage is the base field, whose separable degree is `1`.
      have hzero : K[⟨0, Nat.lt_succ_of_le hm⟩] = (⊥ : IntermediateField F K) := by
        simpa using stage_zero_eq_bot F α
      rw [hzero]
      simp [prefix_deg_s_prod]
  | m + 1, hm => by
      let i : Fin n := ⟨m, Nat.lt_of_succ_le hm⟩
      -- Advance one stage using the multiplicative recursion from the simple-adjoin step.
      calc
        Field.finSepDegree F K[⟨m + 1, Nat.lt_succ_of_le hm⟩] =
            Field.finSepDegree F K[i.succ] := by
          rfl
        _ = Field.finSepDegree F K[i.castSucc] * deg_s(P[i]) :=
            stage_finSepDegree_succ (F := F) (K := K) (α := α) i
        _ = Field.finSepDegree F K[⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hm)⟩] *
              deg_s(P[i]) := by
          rfl
        _ = prefix_deg_s_prod (F := F) (K := K) (α := α) m * deg_s(P[i]) := by
          rw [prefix_stage_finSepDegree_eq_prod_deg_s m (Nat.le_of_succ_le hm)]
        _ = prefix_deg_s_prod (F := F) (K := K) (α := α) (m + 1) := by
          simp [prefix_deg_s_prod, Finset.prod_range_succ, i, Nat.lt_of_succ_le hm]

/-- Helper for Lemma 9.12.9: once the final stage is all of `K`, its separable degree is the
separable degree of `K/F`. -/
private lemma last_stage_finSepDegree_eq_main_field (hα : K[Fin.last n] = ⊤) :
    Field.finSepDegree F K[Fin.last n] = Field.finSepDegree F K := by
  let _ : FiniteDimensional F K := inferInstance
  -- The top intermediate field is canonically equivalent to the ambient extension field.
  rw [hα, IntermediateField.finSepDegree_top]

/-- Lemma 9.12.9: in Situation 9.12.7, the finite separable degree `[K : F]_s` is the product of
the separable degrees of the successive minimal polynomials `P_i`. -/
theorem finSepDegree_eq_prod_deg_s (hα : K[Fin.last n] = ⊤) :
    Field.finSepDegree F K = ∏ i : Fin n, deg_s(P[i]) := by
  -- Route correction: follow the source tower argument stage-by-stage via separable degrees,
  -- then rewrite the last stage to `K`.
  calc
    Field.finSepDegree F K = Field.finSepDegree F K[Fin.last n] := by
      symm
      exact last_stage_finSepDegree_eq_main_field (F := F) (K := K) (α := α) hα
    _ = prefix_deg_s_prod (F := F) (K := K) (α := α) n := by
      simpa using prefix_stage_finSepDegree_eq_prod_deg_s (F := F) (K := K) (α := α) n le_rfl
    _ = ∏ i : Fin n, deg_s(P[i]) := by
      simpa [prefix_deg_s_prod] using
        (Fin.prod_univ_eq_prod_range
          (fun j : ℕ => if hj : j < n then deg_s(P[⟨j, hj⟩]) else 1) n).symm

end

section

variable (F : Type u) (K : Type v) (L : Type w)
variable [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L] [IsAlgClosure F L]
variable [FiniteDimensional F K]
variable {n : ℕ}

attribute [local instance] IsAlgClosure.isAlgClosed

variable (α : Fin n → K)

local notation "K[" i "]" => stage F α i
local notation "P[" i "]" => P[F, α; i]

/-- Bridge reformulation of Lemma 9.12.9 for a chosen algebraic closure `L` of `F`. -/
theorem card_algHom_eq_prod_deg_s (hα : K[Fin.last n] = ⊤) :
    Nat.card (K →ₐ[F] L) = ∏ i : Fin n, deg_s(P[i]) := by
  rw [← Field.finSepDegree_eq_of_isAlgClosed F K L]
  exact finSepDegree_eq_prod_deg_s F K α hα

end

/-! ### Lemma_9_12_10 (from Chap09) -/
open Situation_9_12_7
open IntermediateField

noncomputable section

universe u v w

section

/- Domain-style sampling for Lemma 9.12.10:
- primary domain: finite field extensions generated by a tower of simple adjunctions, separability
  in towers, and counting `F`-algebra embeddings into an algebraically closed field;
- sampled owner declarations:
  `IntermediateField.isSeparable_adjoin_simple_iff_isSeparable`,
  `Algebra.IsSeparable.trans`,
  `Field.finSepDegree_eq_of_isAlgClosed`,
  `Field.finSepDegree_eq_finrank_iff`;
- best owner abstractions: the source-facing stage tower `K[F, α; i]` from
  `Situation_9_12_7`, the extension-level owner `Algebra.IsSeparable F K`, and the numerical owner
  `Field.finSepDegree F K`;
- primitive data: only the chosen generators `α : Fin n → K` and the canonical recursive stages
  `K[F, α; i]`;
- derived API: the source-facing embedding-count equality and strict inequality over an algebraic
  closure.

Source/core/bridge triage:
- `source-facing`: the three consequences about separable generators, the number of
  `F`-algebra morphisms, and separability of `K/F`;
- `core/canonical`: `Algebra.IsSeparable F K`, `Field.finSepDegree F K`, and
  `IntermediateField.isSeparable_adjoin_simple_iff_isSeparable`;
- `bridge/view`: `Field.finSepDegree_eq_of_isAlgClosed`, which converts the canonical separable
  degree into `Nat.card (K →ₐ[F] L)` for algebraically closed `L`.
-/

variable (F : Type u) (K : Type v)
variable [Field F] [Field K] [Algebra F K]
variable {n : ℕ}

variable (α : Fin n → K)

local notation "K[" i "]" => stage F α i

/-- Helper for Lemma 9.12.10: the zeroth stage in the generator tower is the base field, without
assuming finite-dimensionality of the ambient extension. -/
private theorem stage_zero_eq_bot' : K[(0 : Fin (n + 1))] = (⊥ : IntermediateField F K) := by
  -- The zeroth prefix contains no generators, so adjoining it gives the base field.
  rw [show K[(0 : Fin (n + 1))] =
      IntermediateField.adjoin F
        ({x : K | ∃ j : Fin n, j.1 < (0 : Fin (n + 1)).1 ∧ α j = x}) by
      rfl]
  rw [IntermediateField.adjoin_eq_bot_iff]
  intro x hx
  rcases hx with ⟨j, hj, rfl⟩
  exact (Nat.not_lt_zero _ hj).elim

/-- Helper for Lemma 9.12.10: each successor stage is the simple adjunction of the next
generator over the preceding stage, without assuming finite-dimensionality of the ambient
extension. -/
private theorem stage_succ_eq_adjoin' (i : Fin n) :
    K[i.succ] =
      (IntermediateField.adjoin K[i.castSucc] ({α i} : Set K)).restrictScalars F := by
  -- The successor prefix adds exactly the new generator `α i`.
  rw [show K[i.succ] =
      IntermediateField.adjoin F ({x : K | ∃ j : Fin n, j.1 < i.succ.1 ∧ α j = x}) by
      rfl]
  rw [IntermediateField.restrictScalars_adjoin]
  apply le_antisymm
  · -- Every generator in the longer prefix is either already present or is the new one.
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rcases hx with ⟨j, hj, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hji
    · have hmem : α j ∈ K[i.castSucc] := by
        change α j ∈
          IntermediateField.adjoin F ({x : K | ∃ k : Fin n, k.1 < i.castSucc.1 ∧ α k = x})
        exact IntermediateField.mem_adjoin_of_mem F ⟨j, hj, rfl⟩
      exact IntermediateField.mem_adjoin_of_mem F (Or.inl hmem)
    · have hji' : j = i := Fin.ext hji
      subst hji'
      have hsingleton : α j ∈ ({α j} : Set K) := by
        simp
      exact IntermediateField.mem_adjoin_of_mem F (Or.inr hsingleton)
  · -- Conversely, the previous stage and the new generator lie in the successor stage.
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rcases hx with hx | hx
    · have hle :
        K[i.castSucc] ≤
          IntermediateField.adjoin F ({x : K | ∃ j : Fin n, j.1 < i.succ.1 ∧ α j = x}) := by
        rw [show K[i.castSucc] =
            IntermediateField.adjoin F ({x : K | ∃ j : Fin n, j.1 < i.castSucc.1 ∧ α j = x}) by
            rfl]
        rw [IntermediateField.adjoin_le_iff]
        intro y hy
        rcases hy with ⟨j, hj, rfl⟩
        exact IntermediateField.mem_adjoin_of_mem F ⟨j, Nat.lt_succ_of_lt hj, rfl⟩
      exact hle hx
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact IntermediateField.mem_adjoin_of_mem F ⟨i, Nat.lt_succ_self i.1, rfl⟩

-- Proof sketch: induct on the source-facing tower stages, using that the zeroth stage is `F`
-- and that each successor stage is obtained by adjoining the next separable generator.
/-- Helper for Lemma 9.12.10: every stage in the generator tower is separable over the base field
once each newly adjoined generator is separable over the previous stage. -/
private lemma prefix_stage_isSeparable
    (hsep : ∀ i : Fin n, IsSeparable K[i.castSucc] (α i)) :
    ∀ m : ℕ, ∀ hm : m ≤ n,
      Algebra.IsSeparable F K[⟨m, Nat.lt_succ_of_le hm⟩]
  | 0, hm => by
      -- The zeroth stage is the base field, so separability comes from the canonical `F/F`.
      have hzero : K[⟨0, Nat.lt_succ_of_le hm⟩] = (⊥ : IntermediateField F K) := by
        simpa using stage_zero_eq_bot' (F := F) (K := K) (α := α)
      rw [hzero]
      exact AlgEquiv.Algebra.isSeparable ((IntermediateField.botEquiv F K).symm)
  | m + 1, hm => by
      let i : Fin n := ⟨m, Nat.lt_of_succ_le hm⟩
      -- The successor stage is a simple adjunction over the previous stage.
      have hprev : Algebra.IsSeparable F K[i.castSucc] :=
        prefix_stage_isSeparable hsep m (Nat.le_of_succ_le hm)
      have hnext :
          Algebra.IsSeparable K[i.castSucc]
            ↥(IntermediateField.adjoin K[i.castSucc] ({α i} : Set K)) := by
        simpa using
          (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
            (F := K[i.castSucc]) (E := K) (x := α i)).2 (hsep i)
      rw [show K[⟨m + 1, Nat.lt_succ_of_le hm⟩] = K[i.succ] by
        rfl]
      rw [stage_succ_eq_adjoin' (F := F) (K := K) (α := α) i]
      change Algebra.IsSeparable F ↥(IntermediateField.adjoin K[i.castSucc] ({α i} : Set K))
      -- Compose separability of the previous stage with separability of the simple adjunction.
      let _ : Algebra.IsSeparable F K[i.castSucc] := hprev
      let _ : Algebra.IsSeparable K[i.castSucc]
          ↥(IntermediateField.adjoin K[i.castSucc] ({α i} : Set K)) := hnext
      exact Algebra.IsSeparable.trans F K[i.castSucc]
        ↥(IntermediateField.adjoin K[i.castSucc] ({α i} : Set K))

/-- A tower generated by adjoining elements separable over the preceding stage is separable over
the base field. -/
private theorem generators_isSeparable
    (hα : K[Fin.last n] = ⊤)
    (hsep : ∀ i : Fin n, IsSeparable K[i.castSucc] (α i)) :
    Algebra.IsSeparable F K := by
  -- The source proof first shows the last stage is separable over `F`.
  have hlast : Algebra.IsSeparable F K[Fin.last n] :=
    prefix_stage_isSeparable (F := F) (K := K) (α := α) hsep n le_rfl
  let eTop : K[Fin.last n] ≃ₐ[F] K :=
    (IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv
  -- Transport separability from the final stage to the ambient field `K`.
  let _ : Algebra.IsSeparable F K[Fin.last n] := hlast
  exact AlgEquiv.Algebra.isSeparable eTop

end

section

variable (F : Type u) (K : Type v) (L : Type w)
variable [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L] [IsAlgClosure F L]
variable {n : ℕ}

attribute [local instance] IsAlgClosure.isAlgClosed

variable (α : Fin n → K)

local notation "K[" i "]" => stage F α i

-- Proof sketch: first promote the source hypotheses to the canonical owner
-- `Algebra.IsSeparable F K`, then rewrite the source-facing cardinality through
-- `Field.finSepDegree_eq_of_isAlgClosed`.
/-- Lemma 9.12.10 (1): if each chosen generator `α_i` is separable over the preceding stage
`K_{i - 1} = F(α_1, ..., α_{i - 1})`, then the number of `F`-algebra morphisms `K → \overline F`
is exactly the degree `[K : F]`. -/
theorem card_algHom_eq_finrank_of_separable_generators
    (hα : K[Fin.last n] = ⊤)
    (hsep : ∀ i : Fin n, IsSeparable K[i.castSucc] (α i)) :
    Nat.card (K →ₐ[F] L) = Module.finrank F K := by
  -- First package the source hypotheses as separability of the whole extension.
  have hKsep : Algebra.IsSeparable F K :=
    generators_isSeparable F K α hα hsep
  let _ : Algebra.IsSeparable F K := hKsep
  -- Then pass through the canonical separable-degree owner.
  rw [← Field.finSepDegree_eq_of_isAlgClosed F K L]
  simpa using Field.finSepDegree_eq_finrank_of_isSeparable F K

end

section

variable (F : Type u) (K : Type v)
variable [Field F] [Field K] [Algebra F K]
variable {n : ℕ}

variable (α : Fin n → K)

local notation "K[" i "]" => stage F α i

-- Proof sketch: this is the canonical separability owner extracted in the helper theorem above;
-- no algebraic-closure data is part of the intrinsic extension statement.
/-- Lemma 9.12.10 (2): if each chosen generator `α_i` is separable over the preceding stage
`K_{i - 1} = F(α_1, ..., α_{i - 1})`, then the finite extension `K/F` is separable. -/
theorem isSeparable_of_separable_generators
    (hα : K[Fin.last n] = ⊤)
    (hsep : ∀ i : Fin n, IsSeparable K[i.castSucc] (α i)) :
    Algebra.IsSeparable F K :=
  generators_isSeparable F K α hα hsep

end

section

variable (F : Type u) (K : Type v) (L : Type w)
variable [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L] [IsAlgClosure F L]
variable [FiniteDimensional F K]
variable {n : ℕ}

attribute [local instance] IsAlgClosure.isAlgClosed

variable (α : Fin n → K)

local notation "K[" i "]" => stage F α i

-- Proof sketch: equality in the general inequality
-- `Nat.card (K →ₐ[F] L) ≤ [K : F]` would force `K/F` to be separable by the canonical criterion
-- `Field.finSepDegree_eq_finrank_iff`; then every element of `K`, hence every `α_i`, would be
-- separable over each intermediate stage, contradicting the hypothesis.
/-- Lemma 9.12.10 (3): if one chosen generator `α_i` is not separable over the preceding stage
`K_{i - 1} = F(α_1, ..., α_{i - 1})`, then the number of `F`-algebra morphisms `K → \overline F`
is strictly smaller than the degree `[K : F]`. -/
theorem card_algHom_lt_finrank_of_exists_not_separable_generator
    (hinsep : ∃ i : Fin n, ¬ IsSeparable K[i.castSucc] (α i)) :
    Nat.card (K →ₐ[F] L) < Module.finrank F K := by
  rcases hinsep with ⟨i, hi⟩
  refine lt_of_le_of_ne (card_algHom_le_finrank F K L) ?_
  intro hEq
  -- Equality with the degree identifies the extension as separable.
  have hKsep : Algebra.IsSeparable F K := by
    rw [← Field.finSepDegree_eq_of_isAlgClosed F K L] at hEq
    exact (Field.finSepDegree_eq_finrank_iff F K).1 hEq
  -- Any element of a separable extension is separable over every intermediate stage in the tower.
  have hsep_i : IsSeparable K[i.castSucc] (α i) := by
    let _ : Algebra.IsSeparable F K := hKsep
    exact
      IsSeparable.tower_top (L := K[i.castSucc])
        (Algebra.IsSeparable.isSeparable F (α i))
  exact hi hsep_i

end

/-! ### Lemma_9_12_11 (from Chap09) -/
universe u v

section

variable {F : Type u} {K : Type v}
variable [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/- Domain-style sampling for Lemma 9.12.11:
- primary domain: finite field extensions, separable degree, and counting `F`-algebra embeddings
  into an algebraic closure;
- sampled owner declarations:
  `Field.finSepDegree`,
  `Field.finSepDegree_eq_of_isAlgClosed`,
  `Field.finSepDegree_le_finrank`,
  `Field.finSepDegree_eq_finrank_iff`;
- best owner abstraction: the numerical owner `Field.finSepDegree F K`;
- primitive data: only the finite field extension `K/F`;
- derived API: the source-facing embedding count in `AlgebraicClosure F`, obtained by the canonical
  algebraically-closed bridge `Field.finSepDegree_eq_of_isAlgClosed`.

Source/core/bridge triage:
- `source-facing`: the combined inequality and equality criterion for
  `Nat.card (K →ₐ[F] AlgebraicClosure F)`;
- `core/canonical`: `Field.finSepDegree F K` and its finrank comparison theorems;
- `bridge/view`: `Field.finSepDegree_eq_of_isAlgClosed`, which identifies the embedding count with
  the canonical owner. -/

/-- Lemma 9.12.11: for a finite field extension `K/F`, the number of `F`-algebra morphisms
`K → AlgebraicClosure F` is at most `[K : F]`, and equality holds exactly when `K/F` is
separable. -/
-- Proof sketch: identify `Nat.card (K →ₐ[F] AlgebraicClosure F)` with `finSepDegree F K` via
-- `finSepDegree_eq_of_isAlgClosed`, then combine `finSepDegree_le_finrank` with
-- `finSepDegree_eq_finrank_iff`.
theorem algHom_natCard_to_algebraicClosure_le_finrank_and_eq_iff_isSeparable :
    Nat.card (K →ₐ[F] AlgebraicClosure F) ≤ Module.finrank F K ∧
      (Nat.card (K →ₐ[F] AlgebraicClosure F) = Module.finrank F K ↔
        Algebra.IsSeparable F K) := by
  rw [← Field.finSepDegree_eq_of_isAlgClosed F K (AlgebraicClosure F)]
  exact ⟨Field.finSepDegree_le_finrank F K, Field.finSepDegree_eq_finrank_iff F K⟩

end

/-! ### Lemma_9_12_12 (from Chap09) -/
/- Domain-style sampling for Lemma 9.12.12:
- primary domain: transitivity of separable field extensions in a tower;
- sampled owner declarations:
  `IsSeparable.tower_top`,
  `Algebra.isSeparable_tower_top_of_isSeparable`,
  `Algebra.IsSeparable`,
  `Algebra.IsSeparable.trans`;
- best owner abstraction: the extension-level owner theorem `Algebra.IsSeparable.trans`;
- primitive data: a tower of field extensions with separability hypotheses on the two stages;
- derived API: the pointwise tower-stability lemmas `IsSeparable.tower_top` and
  `Algebra.isSeparable_tower_top_of_isSeparable`, from which the owner theorem is packaged.

Source/core/bridge triage:
- `source-facing`: separability of the composite extension in a tower `k ⊆ E ⊆ F`;
- `core/canonical`: `Algebra.IsSeparable.trans`;
- `bridge/view`: the pointwise tower-stability lemmas for separable elements.

This file should therefore remain a pure recall surface: the source lemma is already exactly the
canonical owner theorem, so any local restatement would only duplicate upstream API. -/

/- Lemma 9.12.12: in a tower of fields `k ⊆ E ⊆ F`, if `E/k` and `F/E` are separable field
extensions, then `F/k` is also a separable field extension; this is the canonical transitivity
theorem `Algebra.IsSeparable.trans`. -/
recall Algebra.IsSeparable.trans
