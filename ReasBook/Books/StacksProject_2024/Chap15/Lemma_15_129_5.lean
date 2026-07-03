import StacksProject_2024.Chap15.Definition_15_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommGroup P] [Module R P] [Module.Projective R P]
variable [IsNoetherianRing (R ⧸ Ring.jacobson R)]

/- Domain triage:
- primary domain: projective modules, complemented direct summands, and finite stably free
  submodules;
- sampled owner declarations: `MaximalSpectrum R`, `IsComplemented`, `Module.Finite`,
  `Module.StablyFree`, and `exists_perturbation_with_cyclicSpan_free_directSummand`;
- `source-facing`: the numbered item says a chosen element `s : P` lies in a finite stably free
  direct summand of `P`;
- `core/canonical`: the ambient owner is the concrete submodule `M : Submodule R P` together with
  the standard predicates `IsComplemented M`, `Module.Finite R M`, and `Module.StablyFree R M`,
  while maximal-local conditions are canonically indexed by `MaximalSpectrum R`;
- `bridge/view`: the theorem below is already the source-facing existence statement, so there is no
  additional owner-level bridge to a stronger free-summand property in this file.

Primitive data are only the ambient projective module `P`, the chosen element `s`, and the
submodule `M ≤ P` containing `s`. Complementedness, finiteness, and stable freeness are canonical
properties of that fixed submodule, so the public source-facing statement should expose `M`
directly instead of packaging it first as an element of `Complementeds (Submodule R P)`. -/

-- Proof sketch: first apply Lemma `15.129.3` to place `(0, s)` inside a finite free direct summand
-- of `F ⊕ P`. Induct on the finite free rank of `F`, reducing to a complemented finite stably free
-- submodule of `R ⊕ P` containing `(0, s)`. Then use Lemma `15.129.4` on the complement to split
-- off a free rank-one summand and identify the kernel of the resulting projection `P → K''` as a
-- complemented submodule of `P` containing `s`; this kernel is finite stably free because
-- `R ⊕ ker(π')` is isomorphic to the sum of the original finite stably free summand and a free
-- rank-one summand.
/-- Lemma 15.129.5: if `R ⧸ Ring.jacobson R` is Noetherian and `P` is a projective `R`-module
whose localizations at maximal ideals are not finitely generated, then every element `s : P` is
contained in a finite stably free direct summand of `P`, expressed directly by a submodule
`M ≤ P` together with `IsComplemented M`, `Module.Finite R M`, and `Module.StablyFree R M`. -/
theorem exists_finiteStablyFree_directSummand_submodule_containing
    (s : P)
    (hnotFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal P)) :
    ∃ M : Submodule R P, s ∈ M ∧ IsComplemented M ∧ Module.Finite R M ∧ Module.StablyFree R M :=
  sorry

end
