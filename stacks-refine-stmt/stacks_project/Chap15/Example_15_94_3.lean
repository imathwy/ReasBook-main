import Mathlib
import stacks_project.Chap15.Definition_15_89_1
import stacks_project.Chap15.Definition_15_92_4
import stacks_project.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped IdealPowerTorsion PrincipalIdeal

universe u

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: derived completeness of `A`-modules with respect to `(f)` and short exact
  sequences in `ModuleCat A`;
- sampled owner-side declarations:
  `ModuleCat.IsDerivedCompleteWithRespectTo`,
  `principalIdeal` together with the owner notation `(f)`,
  `ShortComplex.mk`,
  `ShortComplex.ShortExact`;
- best owner abstraction: the short exact sequence data `K ⟶ L ⟶ M` itself, rather than a
  wrapper predicate on an arbitrary short complex;
- primitive data: the module objects `K`, `L`, the maps `ι`, `π`, and the relation `ι ≫ π = 0`;
- derived API: short exactness of `ShortComplex.mk ι π h`, `(f)`-adic completeness of `K` and `L`,
  and vanishing of their `f`-torsion.

Layer triage:
- `source-facing`: the existence of a short exact sequence `0 → K → L → M → 0` with the listed
  completeness and torsion conditions;
- `core/canonical`: `ModuleCat.IsDerivedCompleteWithRespectTo`, `principalIdeal`/`(f)`, and
  `ShortComplex.ShortExact`;
- `bridge/view`: the realization of the source sequence as `ShortComplex.mk ι π h`. -/

-- Proof sketch: for the forward implication, choose a surjection from a free module onto `M`,
-- replace the free module by its `(f)`-adic completion, and let `K` be the kernel of the induced
-- map to `M`; derived completeness of kernels is supplied by Lemma `15.92.6`, while the free and
-- kernel terms are `(f)`-adically complete with zero `f`-torsion. For the reverse implication,
-- tensor the short exact sequence with the two-term complexes `(A \xrightarrow{f^n} A)`, use the
-- vanishing of `f`-torsion on the complete terms to identify the derived tensors with
-- `(K / f^n K \to L / f^n L)`, and pass to `R lim`; Lemma `15.92.17` then gives derived
-- completeness of `M`.
/-- Example 15.94.3: if `f` is a nonzerodivisor in a ring `A`, then an `A`-module `M` is derived
complete with respect to `(f)` if and only if it fits into a short exact sequence
`0 → K → L → M → 0` in which `K` and `L` are `(f)`-adically complete and have zero
`f`-torsion. -/
theorem isDerivedCompleteWithRespectTo_principalIdeal_iff_exists_principalDerivedCompletePresentation
    (f : A) (M : ModuleCat A) (hf : IsRegular f) :
    M.IsDerivedCompleteWithRespectTo ((f) : Ideal A) ↔
      ∃ (K L : ModuleCat A) (ι : K ⟶ L) (π : L ⟶ M) (h : ι ≫ π = 0),
        (ShortComplex.mk ι π h).ShortExact ∧
          IsAdicComplete ((f) : Ideal A) K ∧
          IsAdicComplete ((f) : Ideal A) L ∧
          (K[f^1] : Submodule A K) = ⊥ ∧
          (L[f^1] : Submodule A L) = ⊥ := sorry

end
