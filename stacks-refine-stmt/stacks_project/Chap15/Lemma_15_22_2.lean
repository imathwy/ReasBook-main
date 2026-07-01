import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling:
- primary domain: torsion theory for modules over commutative rings and its domain specialization;
- sampled owner API:
  `Submodule.torsion`,
  `Submodule.isTorsionFree_iff_torsion_eq_bot`,
  `Submodule.QuotientTorsion.torsion_eq_bot`,
  the quotient torsion-free instance on `M ⧸ Submodule.torsion R M`;
- source-facing: the torsion submodule and the torsion-free quotient by it;
- core/canonical: the mathlib owners `Submodule.torsion` and `Module.IsTorsionFree`;
- bridge/view: none.

Primitive data are only the module over the base ring. The torsion-free structure on the quotient by
`Submodule.torsion R M` is derived API already owned upstream, with proposition-level owner
`Module.IsTorsionFree R (M ⧸ Submodule.torsion R M)` and implementation supplied by
`Submodule.QuotientTorsion.instIsTorsionFree`. The public entry here should expose the
proposition-level owner rather than the internal instance name.
-/

section

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/- Lemma 15.22.2 (1): the set of torsion elements of an `R`-module `M` is the canonical submodule
`Submodule.torsion R M`; the source's domain hypothesis is redundant for this owner declaration. -/
recall Submodule.torsion

end

section

open Module

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Lemma 15.22.2 (2): the quotient of an `R`-module by its torsion submodule is torsion free. -/
#check (inferInstance : IsTorsionFree R (M ⧸ Submodule.torsion R M))

end
