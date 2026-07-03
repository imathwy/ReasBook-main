import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.RingTheory.Bezout
import stacks_project.Chap15.Lemma_15_22_2
import stacks_project.Chap15.Lemma_15_125_4
import stacks_project.Chap15.Lemma_15_125_7
import stacks_project.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DirectSum

universe u v

/-
Domain-style sampling:
- primary domain: finitely presented modules over Bézout domains, their torsion submodules, and
  split decompositions into torsion and torsion-free parts;
- sampled owner declarations:
  `IsBezout`,
  `Submodule.torsion`,
  `Module.IsTorsionFree R (M ⧸ Submodule.torsion R M)`,
  `nonempty_linearEquiv_quotient_torsionBy_prod_of_fittingIdeal_eq_principalIdeal`,
  `lequivProdOfRightSplitExact`,
  `directSummand_iff_surjective_compRight_of_principalPure_shortExact`;
- best owner abstraction:
  this file is mostly `source-facing`, while the core owners are the Bézout property
  `IsBezout`, the canonical torsion submodule `Submodule.torsion`, and the chapter’s direct-sum
  product decomposition owner for split exact sequences, specialized here to the torsion
  short exact sequence; for part (4), the direct-summand surface should match the owner theorem
  `directSummand_iff_surjective_compRight_of_principalPure_shortExact` by using a finite index
  type rather than a chosen `Fin n` encoding;
- primitive data vs. derived API:
  primitive data are the ambient Bézout domain and finitely presented module;
  derived API are the torsion-free quotient, the split product decomposition, and the retract of
  the torsion submodule into a finite direct sum of principal quotients indexed by a finite type,
  using the canonical quotient-torsion-free owner from Lemma `15.22.2` instead of a parallel
  local predicate.

Source/core/bridge triage:
- `source-facing`: the four assertions of Lemma `15.125.8`;
- `core/canonical`: `IsBezout`, `Submodule.torsion`, and the quotient torsion-free owner API from
  Lemma `15.22.2`, together with the split-exact product equivalence owner;
- `bridge/view`: the local-global retract theorem from Lemma `15.125.4`, specialized here to
  finitely presented modules over Bézout domains via Lemma `15.125.7`.
-/

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]

-- Proof sketch: reduce from an arbitrary free ambient module to a finite free one by choosing
-- finitely many basis vectors supporting a finite generating set of the submodule. Then argue by
-- induction on the rank, projecting to the last coordinate and using that a finitely generated
-- ideal in a Bézout domain is principal.
/-- Lemma 15.125.8 (1): every finite submodule of a free `R`-module is finite free. -/
theorem finite_submodule_free_of_free_over_isBezout
    {F : Type v} [AddCommGroup F] [Module R F] [Module.Free R F]
    (N : Submodule R F) [Module.Finite R N] :
    Module.Free R N := sorry

section

variable {M : Type v} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]

-- Proof sketch: apply Lemma `15.125.4` using Lemma `15.125.7` to realize `M` as a direct summand
-- of a finite direct sum of cyclic quotients. The quotient by `Submodule.torsion R M` is then a
-- finite torsion-free summand of a free module; the torsion-free input is the canonical owner
-- `Module.IsTorsionFree R (M ⧸ Submodule.torsion R M)` from Lemma `15.22.2`, so part (1) gives
-- freeness without introducing a local wrapper for torsion-freeness.
/-- Lemma 15.125.8 (2): for a finitely presented `R`-module `M`, the quotient by its torsion
submodule is a finite free `R`-module. -/
theorem torsion_quotient_free_of_finitelyPresented_over_isBezout :
    Module.Free R (M ⧸ Submodule.torsion R M) := sorry

-- Proof sketch: the quotient `M ⧸ Submodule.torsion R M` is free by part (2), hence projective.
-- Apply the canonical splitting of the short exact sequence
-- `0 → Submodule.torsion R M → M → M ⧸ Submodule.torsion R M → 0`; a section of the quotient map
-- then gives the source-facing product decomposition via the canonical split-exact owner
-- `lequivProdOfRightSplitExact`.
/-- Lemma 15.125.8 (3): a finitely presented `R`-module splits as the product of its torsion-free
quotient and its torsion submodule. -/
theorem nonempty_linearEquiv_quotient_torsion_prod_of_finitelyPresented_over_isBezout :
    Nonempty (M ≃ₗ[R] (M ⧸ Submodule.torsion R M) × Submodule.torsion R M) := sorry

-- Proof sketch: again start from the direct-summand presentation of Lemma `15.125.4`. Applying
-- the torsion functor to the finite direct sum `⨁ i, R ⧸ (f i)` identifies `Submodule.torsion R M`
-- with a direct summand of that torsion module; because each `f i` is nonzero in a domain, the
-- whole direct sum is already torsion, so the torsion submodule is a direct summand of a module of
-- the required form. The public surface keeps the finite-index owner level, quantifying over a
-- finite type `ι` rather than choosing a specific encoding `Fin n`.
/-- Lemma 15.125.8 (4): the torsion submodule of a finitely presented `R`-module is a direct
summand of a finite direct sum of cyclic modules `R ⧸ (fᵢ)` with `fᵢ ≠ 0`. -/
theorem torsion_directSummand_finite_directSum_principal_quotients_of_finitelyPresented_over_isBezout :
    ∃ (ι : Type v) (_ : Fintype ι) (f : ι → R),
      (∀ i, f i ≠ 0) ∧
        ∃ (i : Submodule.torsion R M →ₗ[R] (⨁ j : ι, R ⧸ principalIdeal (f j)))
          (s : (⨁ j : ι, R ⧸ principalIdeal (f j)) →ₗ[R] Submodule.torsion R M),
            s.comp i = LinearMap.id := sorry

end

end
