import Mathlib
import StacksProject_2024.stacks_project.Chap10.Remark_10_75_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/- Domain-style sampling:
- primary domain: low-degree `Tor₁` over a local ring, propagated from the residue field to
  finite-length modules in the textbook source-facing argument order;
- sampled owner declarations of the same kind:
  `CategoryTheory.Tor`,
  `CategoryTheory.isZero_Tor_succ_of_projective`,
  `ModuleCat.torTensorSixTermSequence_exact`,
  `CategoryTheory.tor_flip_iso`;
- best owner abstraction: the homological owner is the canonical bifunctor
  `CategoryTheory.Tor (ModuleCat R) 1`, while the induction owner on the finite-length source
  module is `IsFiniteLength R N`;
- primitive data vs derived API: the primitive data are only the fixed right `R`-module `M`, the
  local ring `R`, and the finite-length source module `N`. The vanishing statement below is
  derived API; the proof may pass through the canonical exact-sequence orientation
  `Tor₁^R(M, -)` via `tor_flip_iso`, but that symmetry comparison is bridge data rather than the
  main public statement.

Source/core/bridge triage:
- `source-facing`: Lemma 10.99.6, propagating vanishing of `Tor₁^R(ResidueField R, M)` to
  `Tor₁^R(N, M)` for finite-length `N`;
- `core/canonical`: `CategoryTheory.Tor (ModuleCat R) 1` and `IsFiniteLength R N`;
- `bridge/view`: the composition-series reduction to simple factors and the symmetry comparison
  `tor_flip_iso` used to move to the exact-sequence-friendly orientation belong to the proof, not
  to the public statement.
-/

-- Proof sketch: argue by induction on a finite-length composition series for `N`. Use
-- `tor_flip_iso` only as an internal bridge to pass to the exact-sequence-friendly orientation
-- `Tor₁^R(M, -)`. The base case is the simple-module case, which over a local ring identifies `N`
-- with `ResidueField R`. For the induction step, splice a short exact sequence with smaller
-- finite-length subquotients and apply the six-term exact Tor sequence from Lemma `10.75.2`.
/-- Lemma 10.99.6: if `Tor₁^R(ResidueField R, M)` vanishes for a local ring `R`, then
`Tor₁^R(N, M)` vanishes for every finite-length `R`-module `N`. -/
theorem isZero_tor_one_of_isFiniteLength_of_residueField_vanishing
    (hκ : IsZero (Tor₁[R](ResidueField R, M))) (hN : IsFiniteLength R N) :
    IsZero (Tor₁[R](N, M)) := sorry

end
