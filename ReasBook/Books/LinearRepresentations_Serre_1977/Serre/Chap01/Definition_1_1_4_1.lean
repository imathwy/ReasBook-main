import Mathlib
import LinearRepresentations_Serre_1977.Chap01.Definition_1_1_2_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {G : Type u} [Monoid G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V)

/- Definition 1-1.4-1: an irreducible or simple complex representation is the canonical mathlib
notion `ρ.IsIrreducible`, meaning that `ρ` is nontrivial and has no proper
nontrivial stable subspaces. -/
recall Representation.IsIrreducible

/-- A degree-1 complex representation is irreducible. -/
-- Proof sketch: a one-dimensional `ℂ`-vector space is a simple `ℂ`-module, so every
-- `G`-stable subspace of `V` is either `⊥` or `⊤`; hence the lattice of
-- subrepresentations of `ρ` is simple.
theorem isIrreducible_of_finrank_eq_one (hV : Module.finrank ℂ V = 1) :
    ρ.IsIrreducible := by
  letI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  letI : Nontrivial (Subrepresentation ρ) :=
    ⟨⊥, ⊤, fun h ↦
      bot_ne_top <| by simpa using congrArg Subrepresentation.toSubmodule h⟩
  letI : IsSimpleOrder (Submodule ℂ V) :=
    (isSimpleModule_iff ℂ V).1 ((isSimpleModule_iff_finrank_eq_one).2 hV)
  refine IsSimpleOrder.of_forall_eq_top fun σ hσ ↦ ?_
  have hσtop : σ.toSubmodule = ⊤ := by
    rcases eq_bot_or_eq_top σ.toSubmodule with hσbot | hσtop
    · exact False.elim <| hσ <| Subrepresentation.toSubmodule_injective (by simpa using hσbot)
    · exact hσtop
  exact Subrepresentation.toSubmodule_injective (by simpa using hσtop)

namespace MonoidHom

/-- A degree-1 complex character yields an irreducible one-dimensional complex representation. -/
theorem toRepresentation_isIrreducible {G : Type u} [Group G] (ρ : G →* ℂˣ) :
    ρ.toRepresentation.IsIrreducible := by
  simpa using
    (isIrreducible_of_finrank_eq_one ρ.toRepresentation
      (by simp : Module.finrank ℂ ℂ = 1))

end MonoidHom

end
