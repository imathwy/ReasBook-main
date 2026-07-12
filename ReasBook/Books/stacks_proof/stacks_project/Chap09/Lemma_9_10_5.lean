import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

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
