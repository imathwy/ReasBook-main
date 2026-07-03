import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_10_111_1 (from Chap10) -/
open CategoryTheory

universe u v

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-
Domain-style sampling:
* primary domain: projective dimension and local depth for finite modules over Noetherian local
  rings;
* sampled owner declarations:
  `projectiveDimension`,
  `projectiveDimension_ne_top_iff`,
  `projectiveDimension_le_iff`,
  `moduleDepth`;
* best owner abstraction: the theorem should use the canonical owners
  `projectiveDimension (ModuleCat.of R M)` and `moduleDepth R _` directly;
* source/core/bridge triage:
  `source-facing`: the Auslander--Buchsbaum equality for a finite module over a Noetherian local
    ring;
  `core/canonical`: `projectiveDimension` and `moduleDepth`;
  `bridge/view`: the self-module specialization `moduleDepth R R`, which is the chapter's canonical
    surface for ring depth rather than a separate local definition.

Primitive data are only the finite module and the canonical projective-dimension value. The
`Nontrivial M` assumption is derived from `hpd : projectiveDimension (ModuleCat.of R M) = d`, since
the zero module has projective dimension `⊥`, so it should not remain a primitive hypothesis.
-/

-- Proof sketch: choose a minimal finite free resolution of `M`; the Buchsbaum--Eisenbud
-- acyclicity criterion and the depth inequalities for short exact sequences handle the case
-- `moduleDepth R M = 0`. For positive depth, choose a nonzerodivisor in the maximal ideal that is
-- regular on both `R` and `M`, pass to the quotient by that element, use that projective
-- dimension is unchanged modulo such a nonzerodivisor and that both depths drop by one, and then
-- conclude by induction on `moduleDepth R M`.
/-- Proposition 10.111.1: for a nonzero finite module `M` over a Noetherian local ring `R`, if the
projective dimension of `M` is the natural number `d`, then the depth of `R` is `d` plus the depth
of `M` (the Auslander--Buchsbaum formula). -/
theorem ringDepth_eq_projectiveDimension_add_moduleDepth
    {d : ℕ} (hpd : projectiveDimension (ModuleCat.of R M) = d) :
    moduleDepth R R = d + moduleDepth R M := sorry

end
