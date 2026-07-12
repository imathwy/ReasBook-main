import Mathlib.RingTheory.AdjoinRoot
import StacksProject_2024.Chap15.Lemma_15_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u

/- Domain sampling for this item:
* primary domain: commutative algebra of monic polynomials, finite free extensions, and linear
  factorization after adjoining a root;
* sampled owner declarations: `dvd_iff_isRoot`, `AdjoinRoot.isRoot_root`,
  `Polynomial.Monic.free_adjoinRoot`, and `Polynomial.Monic.finite_adjoinRoot`;
* layer triage:
  - `source-facing`: existence of a finite free `R`-algebra in which the base change of `P` has a
    linear factor with monic quotient;
  - `core/canonical`: the canonical witness algebra `AdjoinRoot P` and its distinguished root;
  - `bridge/view`: the specialization of `exists_monic_factor_of_isRoot` to `AdjoinRoot P`.
* owner decision: the numbered lemma should remain source-facing and expose the extension data,
  while `AdjoinRoot` remains only the canonical proof witness.
* primitive data: the extension ring `R'`, its `R`-algebra structure, the finite/free module
  structure, and the root `α`;
* derived API: the monic factorization over `R'[X]`, obtained by applying
  `exists_monic_factor_of_isRoot` to `AdjoinRoot.isRoot_root`. -/

/-- Lemma 15.21.2: for a monic polynomial `P` over a commutative ring `R`, there exists a finite
free `R`-algebra `R'` and an element `α : R'` such that `P` base-changed to `R'` factors as
`(X - C α) * Q` with `Q` monic. -/
-- Proof sketch: take `R' = AdjoinRoot P` and `α = AdjoinRoot.root P`. The extension is finite free
-- by `Polynomial.Monic.free_adjoinRoot` and `Polynomial.Monic.finite_adjoinRoot`, and
-- `AdjoinRoot.isRoot_root P` identifies the canonical quotient by `X - C α`.
theorem exists_finiteFree_extension_with_monic_linear_factor {R : Type u} [CommRing R]
    {P : R[X]} (hP : P.Monic) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Module.Finite R R')
      (_ : Module.Free R R') (α : R') (Q : R'[X]),
      Q.Monic ∧ P.map (algebraMap R R') = (X - C α) * Q := by
  letI : Module.Finite R (AdjoinRoot P) := hP.finite_adjoinRoot
  letI : Module.Free R (AdjoinRoot P) := hP.free_adjoinRoot
  have hroot : (P.map (algebraMap R (AdjoinRoot P))).IsRoot (AdjoinRoot.root P) := by
    simpa [-AdjoinRoot.algebraMap_eq] using AdjoinRoot.isRoot_root P
  obtain ⟨Q, hQ, hfactor⟩ :=
    exists_monic_factor_of_isRoot (P.map (algebraMap R (AdjoinRoot P))) (hP.map _) hroot
  exact ⟨AdjoinRoot P, inferInstance, inferInstance, inferInstance, inferInstance,
    AdjoinRoot.root P, Q, hQ, hfactor⟩
