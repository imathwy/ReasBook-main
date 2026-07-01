import Mathlib
import stacks_project.Chap10.Definition_10_78_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage:
- primary domain: commutative algebra of finite projective modules, finite free splittings, and
  Zariski-local freeness on `Spec R`;
- sampled owner declarations of the same kind:
  `Module.Projective.iff_split`,
  `Module.freeLocus_eq_univ_iff`,
  `Module.freeLocus_eq_univ`,
  `Module.isLocallyConstant_rankAtStalk`;
- owner abstraction: the chapter owner `Module.FiniteLocallyFree R M`, together with the canonical
  mathlib owners `Module.Projective R M` and `Module.freeLocus R M`;
- primitive data: only the ring `R` and the module `M`;
- derived API: the finite-free direct-summand clause, the free-locus formulations, and the
  finite-locally-free bridge theorem below.

Source/core/bridge triage:
- `module_finite_projective_tfae` is `source-facing`: it records the textbook list of equivalent
  criteria, but each clause should use the most canonical available owner surface;
- `Module.finiteLocallyFree_of_finitePresentation_of_flat` is `bridge/view`: it extracts the
  chapter owner `Module.FiniteLocallyFree` from the source-facing TFAE.

Refinement note:
- clause `(3)` is stated using the canonical finite free model `ι → R` with `[Finite ι]`, rather
  than existentially packaging an arbitrary free finite ambient module and its instance data.
-/

-- Proof sketch: the implications use the standard chain of results for finitely presented flat
-- modules: `Module.Flat.projective_of_finitePresentation`, the direct-summand characterization
-- `Module.Projective.iff_split`, local freeness over local rings via
-- `Module.free_of_flat_of_isLocalRing`, descent of projectivity from maximal localizations by
-- `Module.projective_of_localization_maximal`, and the canonical local-constancy theorem for the
-- rank function `Module.isLocallyConstant_rankAtStalk`. The textbook clauses (6) and (7) are
-- expressed directly by Zariski-local freeness on a standard-open cover.
/-- Lemma 10.78.2: for an `R`-module `M`, the following are equivalent: `M` is finitely presented
and flat; `M` is finite projective; `M` is a direct summand of a finite free `R`-module; `M` is
finitely presented and all prime localizations are free; `M` is finitely presented and all maximal
localizations are free; `M` is finite and locally free; `M` is finite locally free; and `M` is
finite, all prime localizations are free, and the fiber-rank function `ρ_M` is locally constant on
`Spec R`. -/
theorem module_finite_projective_tfae :
    List.TFAE [
      Module.FinitePresentation R M ∧ Module.Flat R M,
      Module.Finite R M ∧ Module.Projective R M,
      ∃ (ι : Type (max u v)) (_ : Finite ι) (i : M →ₗ[R] (ι → R)) (s : (ι → R) →ₗ[R] M),
        s.comp i = LinearMap.id,
      Module.FinitePresentation R M ∧ Module.freeLocus R M = Set.univ,
      Module.FinitePresentation R M ∧
        ∀ (P : Ideal R) [P.IsMaximal],
          Module.Free (Localization.AtPrime P) (LocalizedModule.AtPrime P M),
      Module.Finite R M ∧ Module.LocallyFree R M,
      Module.FiniteLocallyFree R M,
      Module.Finite R M ∧
        Module.freeLocus R M = Set.univ ∧
          IsLocallyConstant (fun p : PrimeSpectrum R ↦ (Module.rankAtStalk M p : ℤ))
    ] := sorry

namespace Module

/-- A finitely presented flat module is finite locally free. -/
theorem finiteLocallyFree_of_finitePresentation_of_flat
    [FinitePresentation R M] [Flat R M] :
    FiniteLocallyFree R M := by
  simpa using (module_finite_projective_tfae.out 0 6).mp
    (show FinitePresentation R M ∧ Flat R M from ⟨inferInstance, inferInstance⟩)

end Module

end
