import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling:
- primary domain: flatness and torsion theory for modules over commutative domains;
- sampled owner API:
  `Module.IsTorsionFree`,
  `Submodule.torsion`,
  `Submodule.isTorsionFree_iff_torsion_eq_bot`,
  `Module.Flat.torsion_eq_bot`;
- best owner abstraction: the proposition-level owner is `Module.IsTorsionFree R M`; the torsion
  submodule `Submodule.torsion R M` is the primitive data owner, and flatness supplies the derived
  vanishing statement `Module.Flat.torsion_eq_bot`;
- source/core/bridge triage:
  `source-facing`: the textbook implication that flat modules over a domain are torsion free;
  `core/canonical`: `Submodule.torsion` together with the owner property `Module.IsTorsionFree`;
  `bridge/view`: the present lemma, converting the canonical flatness hypothesis into the
  canonical torsion-free conclusion.

Primitive data here are only the ambient ring/module and the flatness hypothesis. The torsion
submodule and torsion-free predicate are already owned upstream, so this file should not introduce a
parallel wrapper or entrywise reformulation: it should expose the source-facing implication through
the canonical bridge from `Module.Flat.torsion_eq_bot` to
`Submodule.isTorsionFree_iff_torsion_eq_bot`.
-/

section

open Module

variable {R : Type u} {M : Type v} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]

/-- Lemma 15.22.9: over a domain, every flat `R`-module is torsion free. -/
-- Proof sketch: use `Submodule.isTorsionFree_iff_torsion_eq_bot` to reduce torsion-freeness to the
-- vanishing of the torsion submodule, then apply `Module.Flat.torsion_eq_bot`.
theorem flat_isTorsionFree [Flat R M] : IsTorsionFree R M :=
  Submodule.isTorsionFree_iff_torsion_eq_bot.2 Module.Flat.torsion_eq_bot

end
