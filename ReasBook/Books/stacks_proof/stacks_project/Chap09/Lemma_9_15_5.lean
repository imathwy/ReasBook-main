import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IntermediateField

variable {F : Type u} {E : Type v}
variable [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E]

/- Domain-style sampling for Lemma 9.15.5:
- primary domain: normal algebraic field extensions, detected by the image fields of embeddings
  into an algebraic closure;
- sampled owner declarations:
  `IntermediateField.normal_iff_forall_fieldRange_eq`,
  `AlgHom.fieldRange_of_normal`,
  `AlgHom.map_fieldRange`,
  `AlgEquiv.transfer_normal`;
- best owner abstraction: the canonical owner is
  `IntermediateField.normal_iff_forall_fieldRange_eq`, applied to the intermediate field
  `ι.fieldRange` cut out by a chosen embedding `ι : E →ₐ[F] AlgebraicClosure F`;
- primitive data vs. derived API:
  primitive data is just that chosen embedding `ι`;
  derived API is the induced equivalence `AlgEquiv.ofInjectiveField ι : E ≃ₐ[F] ι.fieldRange`,
  transport of normality along this equivalence, and the field-range comparison obtained from
  `AlgHom.map_fieldRange`.

Source/core/bridge triage:
- `source-facing`: the textbook statement quantifying over pairs of embeddings
  `E →ₐ[F] AlgebraicClosure F`;
- `core/canonical`: `IntermediateField.normal_iff_forall_fieldRange_eq`;
- `bridge/view`: identify the abstract extension `E/F` with the concrete intermediate field
  `ι.fieldRange ⊆ AlgebraicClosure F`.

This file should therefore keep only the source-facing bridge theorem, while routing the proof
directly through the owner theorem instead of maintaining a parallel local normality criterion.
-/

/- Companion recall: the canonical owner theorem is the intermediate-field statement inside a
normal ambient extension. -/
recall IntermediateField.normal_iff_forall_fieldRange_eq

/-- Lemma 9.15.5: for an algebraic extension `E/F`, the extension is normal if and only if any
two `F`-algebra embeddings of `E` into `AlgebraicClosure F` have the same image subfield. -/
@[stacks 09HQ]
theorem normal_iff_forall_algHom_fieldRange_eq :
    Normal F E ↔
      ∀ σ σ' : E →ₐ[F] AlgebraicClosure F, σ.fieldRange = σ'.fieldRange := by
  let ι : E →ₐ[F] AlgebraicClosure F := IsAlgClosed.lift
  let e : E ≃ₐ[F] ι.fieldRange := AlgEquiv.ofInjectiveField ι
  constructor
  · intro h σ σ'
    have hι (τ : E →ₐ[F] AlgebraicClosure F) : τ.fieldRange = ι.fieldRange := by
      letI : Normal F ι.fieldRange := e.transfer_normal.1 h
      have hcomp :
          IntermediateField.map τ ((e.symm : ι.fieldRange →ₐ[F] E).fieldRange) =
            (τ.comp e.symm.toAlgHom).fieldRange := by
        simpa using AlgHom.map_fieldRange e.symm.toAlgHom τ
      have htop : (e.symm : ι.fieldRange →ₐ[F] E).fieldRange = ⊤ :=
        AlgEquiv.fieldRange_eq_top e.symm
      calc
        τ.fieldRange = IntermediateField.map τ ⊤ := AlgHom.fieldRange_eq_map τ
        _ = IntermediateField.map τ ((e.symm : ι.fieldRange →ₐ[F] E).fieldRange) := by
          rw [htop]
        _ = (τ.comp e.symm.toAlgHom).fieldRange := hcomp
        _ = ι.fieldRange := AlgHom.fieldRange_of_normal (τ.comp e.symm.toAlgHom)
    exact (hι σ).trans (hι σ').symm
  · intro h
    have hfieldRange (τ : ι.fieldRange →ₐ[F] AlgebraicClosure F) :
        τ.fieldRange = ι.fieldRange := by
      have hcomp :
          IntermediateField.map τ ((e : E →ₐ[F] ι.fieldRange).fieldRange) =
            (τ.comp e.toAlgHom).fieldRange := by
        simpa using AlgHom.map_fieldRange e.toAlgHom τ
      have htop : (e : E →ₐ[F] ι.fieldRange).fieldRange = ⊤ := AlgEquiv.fieldRange_eq_top e
      calc
        τ.fieldRange = IntermediateField.map τ ⊤ := AlgHom.fieldRange_eq_map τ
        _ = IntermediateField.map τ ((e : E →ₐ[F] ι.fieldRange).fieldRange) := by rw [htop]
        _ = (τ.comp e.toAlgHom).fieldRange := hcomp
        _ = ι.fieldRange := h (τ.comp e.toAlgHom) ι
    exact e.transfer_normal.2 <| normal_iff_forall_fieldRange_eq.2 hfieldRange
