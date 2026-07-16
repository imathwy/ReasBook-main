import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap10.Lemma_10_78_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Module

/-
Domain-style sampling:
- primary domain: torsion-free, flat, finite locally free, and free modules over Dedekind domains
  and principal ideal domains;
- sampled owner declarations:
  `IsDedekindDomain.flat_iff_torsion_eq_bot`,
  `Submodule.isTorsionFree_iff_torsion_eq_bot`,
  `Module.finiteLocallyFree_of_finitePresentation_of_flat`,
  `Module.free_of_finite_type_torsion_free'`;
- best owner abstraction: the public statements should be organized around the owner predicates
  `IsTorsionFree`, `FiniteLocallyFree`, and `Module.Free`, with vanishing torsion and finite
  presentation used only as bridge data;
- primitive data: the ring, the module, and for parts `(2)` and `(3)` the finiteness hypothesis;
- derived API: flatness over a Dedekind domain, finite local freeness via
  `Module.finiteLocallyFree_of_finitePresentation_of_flat`, and freeness over a PID via the canonical owner
  `Module.free_of_finite_type_torsion_free'`.

Source/core/bridge triage:
- part `(1)` is `bridge/view`, translating the canonical Dedekind-domain flatness criterion into
  the source-facing torsion-free owner;
- part `(2)` is `bridge/view`, translating the finite torsion-free hypothesis into the chapter
  owner `FiniteLocallyFree`;
- part `(3)` is `core/canonical`, since the textbook statement already coincides with an existing
  mathlib owner and should be recalled directly.
-/

section

variable {A : Type u} [CommRing A] [IsDedekindDomain A]
variable {M : Type v} [AddCommGroup M] [Module A M]

-- Proof sketch: rewrite flatness over a Dedekind domain using the canonical mathlib theorem
-- `IsDedekindDomain.flat_iff_torsion_eq_bot`, then identify vanishing torsion with
-- `IsTorsionFree A M` via `Submodule.isTorsionFree_iff_torsion_eq_bot`.
/-- Lemma 15.22.11 (1): over a Dedekind domain `A` (hence in particular over a discrete valuation
ring or a PID), an `A`-module is flat if and only if it is torsion free. -/
@[stacks 0AUW]
theorem flat_iff_isTorsionFree_of_isDedekindDomain :
    Flat A M ↔ IsTorsionFree A M := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, ← Submodule.isTorsionFree_iff_torsion_eq_bot]

-- Proof sketch: a finite module over a Dedekind domain is finitely presented because Dedekind
-- domains are Noetherian, and a torsion-free module is flat by the canonical Dedekind-domain
-- owner theorem. The chapter owner bridge
-- `Module.finiteLocallyFree_of_finitePresentation_of_flat` then upgrades the finitely presented
-- flat module directly to `FiniteLocallyFree`.
/-- Lemma 15.22.11 (2): a finite torsion-free module over a Dedekind domain is finite locally
free. -/
@[stacks 0AUW]
theorem finiteLocallyFree_of_finite_of_isTorsionFree_of_isDedekindDomain
    [Module.Finite A M] [IsTorsionFree A M] :
    FiniteLocallyFree A M := by
  letI : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  exact finiteLocallyFree_of_finitePresentation_of_flat

end

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
variable {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
variable [IsTorsionFree A M]

/- Lemma 15.22.11 (3): a finite torsion-free module over a principal ideal domain is free.
This is exactly the canonical mathlib owner `Module.free_of_finite_type_torsion_free'`. -/
recall free_of_finite_type_torsion_free'

end
