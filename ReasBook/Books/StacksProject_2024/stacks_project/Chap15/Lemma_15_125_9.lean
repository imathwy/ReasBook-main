import Mathlib
import StacksProject_2024.stacks_project.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DirectSum

universe u v

/-
Domain-style sampling:
- primary domain: finitely generated modules over principal ideal domains and their structure
  theorem;
- sampled owner declarations:
  `Module.equiv_free_prod_directSum`,
  `principalIdeal`,
  `Fintype.equivFin`,
  `DirectSum.lequivCongrLeft`;
- best owner abstraction: this item is `source-facing`, while the canonical owner for the
  decomposition is mathlib's `Module.equiv_free_prod_directSum`;
- primitive data vs. derived API:
  primitive data is the PID `R` and the finite `R`-module `M`;
  derived API is the finite index type `ι`, the family `f : ι → R` of nonzero elements, and the
  resulting linear equivalence to a free part times cyclic principal quotients;

Source/core/bridge triage:
- `source-facing`: the textbook existence statement with finitely many cyclic summands
  `R ⧸ principalIdeal (f i)`;
- `core/canonical`: `Module.equiv_free_prod_directSum`;
- `bridge/view`: the sampled `Fintype.equivFin` and `DirectSum.lequivCongrLeft` reindexing bridge
  was rejected as non-canonical for the public statement; only the quotient ideals are rewritten
  through the chapter owner `principalIdeal`. -/

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

-- Proof sketch: apply the stronger mathlib structure theorem
-- `Module.equiv_free_prod_directSum`. It gives a decomposition of `M` as a free part together
-- with a finite direct sum of cyclic modules `R ⧸ R ∙ p_i ^ e_i` for irreducible `p_i`. Then set
-- `f i = p_i ^ e_i`; these are nonzero because `R` is a domain.
/-- Lemma 15.125.9: every finite module over a principal ideal domain is linearly isomorphic to a
free finite-rank module times a finite direct sum of cyclic quotient modules `R ⧸ (fᵢ)` with
`fᵢ ≠ 0`. -/
lemma finite_module_exists_linearEquiv_free_prod_directSum_principal_quotients :
    ∃ (r : ℕ) (ι : Type u) (_ : Fintype ι) (f : ι → R),
      (∀ i, f i ≠ 0) ∧
        Nonempty (M ≃ₗ[R] (Fin r →₀ R) × ⨁ i : ι, R ⧸ principalIdeal (f i)) := by
  classical
  obtain ⟨r, ι, hι, p, hp, e, hM⟩ := Module.equiv_free_prod_directSum R M
  let f : ι → R := fun i ↦ p i ^ e i
  refine ⟨r, ι, hι, f, ?_, ?_⟩
  · intro i
    dsimp [f]
    exact pow_ne_zero _ (hp _).ne_zero
  · simpa [f, principalIdeal] using hM

end
