import stacks_project.Chap15.Lemma_15_129_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [Ring R]
variable {P : Type v} [AddCommGroup P] [Module R P] [Module.Projective R P]

/- Domain sampling:
- primary domain: projective modules, free ambient modules, and complemented submodules;
- sampled owner declarations: `Module.Projective.exists_free_prod_free`,
  `Module.Free.chooseBasis`, `Finsupp.supported`, and `Complementeds (Submodule R M)`;
- source-facing layer: existence of a finite free direct summand of `F ⊕ P` containing `(0, s)`;
- core/canonical layer: the owner `Complementeds (Submodule R (F × P))` for the summand itself,
  with the finite-support submodule `Finsupp.supported R R S` as the canonical free finite model
  on basis coordinates;
- bridge/view: Lemma `15.129.2` provides the free ambient module `F₀ × P`, and a chosen basis of
  that free module identifies finite-support coordinate submodules with finite free complemented
  submodules in the ambient module.

Primitive data are the ambient finite free module `F` and the complemented submodule `K ≤ F × P`.
The properties `Module.Free R K` and `Module.Finite R K` are standard derived API on that owner
and should remain theorem-level output, not primitive wrapper fields. -/

-- Proof sketch: invoke `Module.Projective.exists_free_prod_free` to place `P` in a free ambient
-- module `F₀ × P`. In coordinates with respect to a chosen basis of that free module, the element
-- `(0, s)` has finite support, so it lies in the canonical finite-support submodule
-- `Finsupp.supported R R S`. Transport that finite free complemented submodule back to the ambient
-- module, then shrink the first factor of `F₀` to a finite free summand containing all first
-- coordinates occurring in this transported submodule so that the witness lives in some `F × P`.
/-- Lemma 15.129.3: for a projective `R`-module `P` and an element `s : P`, there exist a finite
free `R`-module `F` and a finite free direct summand `K` of `F ⊕ P`, modeled in Lean as a
complemented submodule `K ≤ F × P` together with the standard properties `Module.Free R K` and
`Module.Finite R K`, such that `(0, s) ∈ K`. -/
theorem exists_finiteFree_directSummand_prod_contains_zero_s (s : P) :
    ∃ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module R F) (_ : Module.Free R F)
      (_ : Module.Finite R F),
      ∃ K : Complementeds (Submodule R (F × P)),
        Module.Free R (K : Submodule R (F × P)) ∧
          Module.Finite R (K : Submodule R (F × P)) ∧ ((0 : F), s) ∈ (K : Submodule R (F × P)) :=
    sorry

end
