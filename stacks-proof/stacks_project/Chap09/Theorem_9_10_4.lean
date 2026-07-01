import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

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
