import Mathlib
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic.Recall
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_9_10_1 (from Chap09) -/
universe u v

/- Domain triage:
- primary domain: algebraically closed fields and algebraic field extensions;
- sampled owner declarations: `IsAlgClosed`,
  `IsAlgClosed.algebraMap_bijective_of_isIntegral`,
  `IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic`, and `isAlgClosure_iff`;
- core/canonical owner abstraction: `IsAlgClosed F`;
- layer: `core/canonical`, since Definition 9.10.1 is the owner notion itself;
- primitive data: only the field `F`;
- derived API: the triviality of algebraic extensions via the structure map and via intermediate
  fields.
-/

variable (F : Type u) [Field F]

/- Definition 9.10.1: a field `F` is algebraically closed. This is the canonical mathlib owner
notion `IsAlgClosed F`. -/
recall IsAlgClosed

section

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

/- Companion recall: the source-facing statement that every algebraic field extension of an
algebraically closed field is trivial via a bijective structure map is already the canonical owner
theorem `IsAlgClosed.algebraMap_bijective_of_isIntegral`, specialized to field extensions. -/
recall IsAlgClosed.algebraMap_bijective_of_isIntegral

/- Companion recall: the equivalent intermediate-field formulation of the Stacks definition is the
existing theorem `IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic`. -/
recall IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic

end

/-! ### Lemma_9_10_2 (from Chap09) -/
open Polynomial

universe u

section

variable (F : Type u) [Field F]

/- Domain triage:
- primary domain: algebraically closed fields, expressed through polynomial factorization and root
  existence criteria;
- sampled owner declarations: `IsAlgClosed`, `IsAlgClosed.exists_root`,
  `IsAlgClosed.of_exists_root`, and `IsAlgClosed.degree_eq_one_of_irreducible`;
- core/canonical owner abstraction: `IsAlgClosed F`;
- layer: `source-facing`, since Lemma 9.10.2 is genuinely a list of equivalent textbook
  characterizations rather than a bare recall item;
- primitive data: only the field `F`;
- derived API: the irreducible-linear, nonconstant-root, and nonconstant-splitting criteria below.

The textbook clause “every polynomial splits” is already exactly the owner notion `IsAlgClosed F`,
so this file keeps the owner directly in the main `List.TFAE` statement instead of introducing a
parallel local wrapper for that clause.
-/

/-- A field is algebraically closed iff every irreducible polynomial over it is linear. -/
theorem isAlgClosed_iff_forall_irreducible_degree_eq_one :
    IsAlgClosed F ↔ ∀ (p : F[X]) (_ : Irreducible p), p.degree = 1 := by
  refine ⟨fun _ p hp ↦ IsAlgClosed.degree_eq_one_of_irreducible F hp, fun h ↦ ?_⟩
  exact IsAlgClosed.of_exists_root F fun p _ hp ↦ exists_root_of_degree_eq_one (h p hp)

/-- A field is algebraically closed iff every nonconstant polynomial over it has a root. -/
theorem isAlgClosed_iff_forall_nonconstant_exists_root :
    IsAlgClosed F ↔ ∀ (p : F[X]) (_ : p.natDegree ≠ 0), ∃ x : F, IsRoot p x := by
  refine ⟨?_, ?_⟩
  · intro _ p hp
    exact IsAlgClosed.exists_root p (degree_ne_of_natDegree_ne hp)
  · intro h
    exact IsAlgClosed.of_exists_root F fun p _ hp ↦ h p hp.natDegree_pos.ne'

/-- A field is algebraically closed iff every nonconstant polynomial over it splits. -/
theorem isAlgClosed_iff_forall_nonconstant_splits :
    IsAlgClosed F ↔ ∀ (p : F[X]) (_ : p.natDegree ≠ 0), p.Splits := by
  refine ⟨fun _ p _ ↦ IsAlgClosed.splits p, ?_⟩
  intro h
  refine (isAlgClosed_iff_forall_nonconstant_exists_root F).2 fun p hp ↦ ?_
  exact (h p hp).exists_eval_eq_zero (degree_ne_of_natDegree_ne hp)

/-- Lemma 9.10.2: for a field `F`, the following are equivalent: `F` is algebraically closed,
every irreducible polynomial over `F` is linear, every nonconstant polynomial over `F` has a
root, and every nonconstant polynomial over `F` splits as a product of linear factors. -/
theorem isAlgClosed_tfae :
    List.TFAE [
      IsAlgClosed F,
      ∀ (p : F[X]) (_ : Irreducible p), p.degree = 1,
      ∀ (p : F[X]) (_ : p.natDegree ≠ 0), ∃ x : F, IsRoot p x,
      ∀ (p : F[X]) (_ : p.natDegree ≠ 0), p.Splits
    ] := by
  tfae_have 1 ↔ 2 := isAlgClosed_iff_forall_irreducible_degree_eq_one F
  tfae_have 1 ↔ 3 := isAlgClosed_iff_forall_nonconstant_exists_root F
  tfae_have 1 ↔ 4 := isAlgClosed_iff_forall_nonconstant_splits F
  tfae_finish

end

/-! ### Definition_9_10_3 (from Chap09) -/
universe u v

variable (F : Type u) (Fbar : Type v) [Field F] [Field Fbar] [Algebra F Fbar]

/- Domain triage:
- primary domain: algebraic closures of fields;
- sampled owner declarations: `IsAlgClosure`, `isAlgClosure_iff`, `IsAlgClosure.isAlgClosed`, and
  the nearby chapter specializations `Lemma_9_10_5` and `Lemma_9_10_6`;
- core/canonical owner abstraction: `IsAlgClosure F Fbar`;
- layer: `core/canonical`, since Definition 9.10.3 is the owner notion itself;
- primitive data: the fields `F`, `Fbar`, and the `F`-algebra structure on `Fbar`;
- derived API: the source-form decomposition into algebraic-over-`F` and algebraically-closed is
  already the canonical theorem `isAlgClosure_iff`.
-/

/- Definition 9.10.3: an algebraic closure of a field `F` is a field extension `Fbar/F` that is
algebraic over `F` and algebraically closed; this is the canonical mathlib typeclass
`IsAlgClosure F Fbar`. -/
recall IsAlgClosure

/- Companion recall: the source-form specification of `IsAlgClosure F Fbar` is the existing
canonical theorem `isAlgClosure_iff`, expressing that `Fbar` is algebraically closed and
algebraic over `F`. -/
recall isAlgClosure_iff

/-! ### Theorem_9_10_4 (from Chap09) -/
universe u

variable (F : Type u) [Field F]

/-
Domain triage for Theorem 9.10.4:
- primary domain: algebraic closures of fields;
- sampled owner declarations: `AlgebraicClosure`, `IsAlgClosure`, `isAlgClosure_iff`,
  `IsAlgClosure.equiv`;
- best owner abstraction: the canonical field `AlgebraicClosure F`;
- primitive data: only the base field `F`;
- derived API: the extension structure `Algebra F (AlgebraicClosure F)`, the proof that this
  extension is an algebraic closure, and the source-facing existential statement obtained from that
  owner.

Source/core/bridge triage:
- `source-facing`: the existence statement `exists_algebraic_closure`;
- `core/canonical`: `AlgebraicClosure F`;
- `bridge/view`: the canonical instance `IsAlgClosure F (AlgebraicClosure F)`.
-/
recall AlgebraicClosure

/- Companion check: the canonical field `AlgebraicClosure F` carries the standard instance of an
algebraic closure of `F`. -/
#check (inferInstance : IsAlgClosure F (AlgebraicClosure F))

/-- Theorem 9.10.4, source-facing bridge: every field `F` admits an algebraic closure. -/
theorem exists_algebraic_closure :
    ∃ (Fbar : Type u) (_ : Field Fbar) (_ : Algebra F Fbar), IsAlgClosure F Fbar := by
  -- Package the canonical algebraic closure as the existential witness.
  exact ⟨AlgebraicClosure F, inferInstance, inferInstance, inferInstance⟩

/-! ### Lemma_9_10_5 (from Chap09) -/
universe u v w

section

/- Domain triage:
- primary domain: embeddings of algebraic field extensions into algebraically closed extensions;
- sampled owner declarations: `IsAlgClosed.lift`, `IsAlgClosure`, `IsAlgClosure.isAlgClosed`, and
  the nearby recall-first chapter owners `Definition_9_10_3` and `Lemma_9_10_6`;
- owner abstraction: `IsAlgClosed.lift`;
- layer targeted here: `core/canonical`, since the numbered item is a direct specialization of the
  existing owner theorem;
- primitive data: the fields `F`, `M`, `Fbar`, the `F`-algebra structures on `M` and `Fbar`, and
  the algebraicity hypothesis on `M/F`;
- derived API: the source-facing existence statement is obtained by specializing the canonical
  lift to an algebraic closure `Fbar/F`.
-/

variable {F : Type u} {M : Type v} {Fbar : Type w}
variable [Field F] [Field M] [Field Fbar] [Algebra F M] [Algebra F Fbar]
variable [Algebra.IsAlgebraic F M] [IsAlgClosure F Fbar]

attribute [local instance] IsAlgClosure.isAlgClosed

/- Lemma 9.10.5: if `Fbar/F` is an algebraic closure and `M/F` is algebraic, the required
`F`-algebra morphism `M → Fbar` is the canonical lift into the algebraically closed extension
`Fbar`. -/
#check (IsAlgClosed.lift : M →ₐ[F] Fbar)

end

/-! ### Lemma_9_10_6 (from Chap09) -/
universe u v w

/- Domain triage:
- primary domain: algebraic closures of fields and canonical comparison isomorphisms;
- sampled owner declarations: `IsAlgClosure`, `IsAlgClosed.lift`, `IsAlgClosure.isAlgClosed`, and
  `IsAlgClosure.equiv`;
- owner abstraction: `IsAlgClosure.equiv`;
- layer targeted here: `source-facing`, since Lemma 9.10.6 is the textbook field-level statement
  that any two algebraic closures of a field are isomorphic, obtained by specializing the
  canonical owner theorem;
- primitive data: a field `F`, two `F`-algebra fields `L` and `M`, and `IsAlgClosure` instances on
  `L` and `M`;
- derived API: the broader integral-domain theorem remains upstream as the canonical owner, while
  this file records only its field-specialized surface.
-/

variable (F : Type u) (L : Type v) (M : Type w)
variable [Field F] [Field L] [Field M] [Algebra F L] [Algebra F M]
variable [IsAlgClosure F L] [IsAlgClosure F M]

/- Lemma 9.10.6: any two algebraic closures of a field are isomorphic. For algebraic closures
`L/F` and `M/F`, the canonical `F`-algebra isomorphism is `IsAlgClosure.equiv F L M`. -/
#check (IsAlgClosure.equiv F L M : L ≃ₐ[F] M)
