import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import stacks_project.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped DirectSum

universe u v w

section

variable {R : Type u} [CommRing R]

namespace LinearMap

variable {M : Type*} {N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A linear map is principal-pure if multiplication by every principal ideal meets its range
exactly as in the Stacks Project hypothesis `fA = A ∩ fB`. -/
def IsPrincipalPure (f : M →ₗ[R] N) : Prop :=
  ∀ r : R,
    principalIdeal r • f.range = f.range ⊓ principalIdeal r • ⊤

end LinearMap

open LinearMap

/- Domain-style sampling:
- primary domain: short exact sequences of `R`-modules tested against cyclic quotient modules
  `R ⧸ (f)` and the resulting split-summand criterion;
- sampled owner declarations:
  `principalIdeal`,
  `CategoryTheory.ShortComplex.ShortExact`,
  `LinearMap.IsPrincipalPure`,
  `LinearMap.compRight`,
  `Module.Projective.iff_split`;
- best owner abstraction: this file is `source-facing`; the exact-sequence side should reuse the
  canonical short-complex owner `ShortComplex.ShortExact`. No upstream chapter/mathlib owner was
  found for the principal-purity condition `fA = A ∩ fB`, so the source-facing owner in this file
  should be the left map itself via `LinearMap.IsPrincipalPure`, with its range expression kept
  internal to that definition;
  the cyclic quotient side should use the chapter owner `principalIdeal`, and the surjectivity
  statement should remain on the canonical postcomposition map `LinearMap.compRight`; although
  `IsSplitMono` is the categorical owner of a split inclusion, this theorem quantifies modules in
  different universes, so the stable source-facing direct-summand witness remains the explicit
  split data `s.comp i = LinearMap.id`;
- primitive data vs. derived API:
  primitive data are the short complex `S`, the principal-purity property of the image submodule
  carried by the left map `S.f.hom`, and a split inclusion of `P` into a direct sum of principal
  quotients;
  derived API is the lifting-surjectivity criterion phrased through `LinearMap.compRight`.

Source/core/bridge triage:
- `source-facing`: the equivalence theorem below;
- `core/canonical`: `principalIdeal`, `ShortComplex.ShortExact`,
  `LinearMap.IsPrincipalPure`, `LinearMap.compRight`, `Module.Projective.iff_split`, and the
  range submodule `S.f.hom.range` appearing only inside the owner definition;
- `bridge/view`: the theorem below, which combines the exact short-complex owner with the
  map-level principal-purity owner in the source lifting criterion.
-/

-- Proof sketch: for the forward implication, reduce to a summand `R ⧸ (f)` and lift a map
-- `R ⧸ (f) → C` by choosing a preimage of `1` in `B` and correcting it using the hypothesis
-- `fA = A ∩ fB`. For the reverse implication, take the direct sum over all maps `R ⧸ (f) → P`,
-- map it onto `P`, and apply the assumed lifting property to the resulting short exact sequence;
-- the principal-purity condition on its kernel gives a splitting.
variable {P : Type v} [AddCommGroup P] [Module R P]

/-- Lemma 15.125.1: an `R`-module `P` is a direct summand of a direct sum of modules of the form
`R ⧸ (f)` if and only if for every short exact sequence `0 → A → B → C → 0` of `R`-modules with
`fA = A ∩ fB` for all `f : R`, the induced map `Hom_R(P, B) → Hom_R(P, C)` is surjective. -/
theorem directSummand_iff_surjective_compRight_of_principalPure_shortExact :
    (∃ (ι : Type w) (r : ι → R)
      (i : P →ₗ[R] (⨁ j : ι, R ⧸ principalIdeal (r j)))
      (s : (⨁ j : ι, R ⧸ principalIdeal (r j)) →ₗ[R] P),
      s.comp i = LinearMap.id) ↔
      ∀ ⦃S : ShortComplex (ModuleCat R)⦄
        (hS : S.ShortExact)
        (hi : IsPrincipalPure S.f.hom),
        Function.Surjective
          (LinearMap.compRight R S.g.hom : (P →ₗ[R] S.X₂) →ₗ[R] P →ₗ[R] S.X₃) := sorry

end
