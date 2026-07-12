import Mathlib
import StacksProject_2024.Chap10.Definition_10_112_5
import StacksProject_2024.Chap10.Definition_10_137_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v

namespace Algebra

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

/- Domain-style sampling:
- primary domain: local smoothness criteria for commutative algebras at a prime, with fiber rings
  over residue fields;
- sampled owner declarations:
  `Algebra.SmoothAtPrime`,
  `Algebra.smoothAtPrime_iff_isSmoothAt`,
  `Algebra.fiberPrimeAt`,
  `Algebra.IsSmoothAt.of_formallySmooth_fiber`;
- best owner abstraction: `SmoothAtPrime` is the source-facing owner for smoothness on a basic open
  neighborhood, and `fiberPrimeAt R S q` is the chapter-owned point of the fiber ring over
  `q ∩ R`; the fiber smoothness hypothesis should therefore be stated directly as
  `SmoothAtPrime` at `fiberPrimeAt R S q`, not via a parallel witness prime plus compatibility
  equality;
- primitive vs. derived:
  the primitive source-facing inputs are the point `q`, a finite-presentation neighborhood near
  `q`, the local flatness of `R_(q ∩ R) → S_q`, and smoothness of the fiber ring at the canonical
  fiber prime. The auxiliary prime `qf` and the equality
  `q.asIdeal = qf.asIdeal.comap includeRight.toRingHom` were derived bridge data already owned by
  `fiberPrimeAt`.

Source/core/bridge triage:
- `source-facing`: the local Stacks criterion proving `SmoothAtPrime R S q`;
- `core/canonical`: `SmoothAtPrime`, `fiberPrimeAt`, and the local owner `IsSmoothAt`;
- `bridge/view`: the finite-presentation neighborhood witness and the implicit identification of
  `q` with the canonical fiber prime.
-/

-- Proof sketch: choose `g ∉ q` such that `R → S_g` is of finite presentation. The local map
-- `R_(q ∩ R) → S_q` is unchanged after replacing `S` by `S_g`, and the prime `qf` of the fiber
-- ring corresponds to `q`. The fiber smoothness hypothesis gives a principal-open neighborhood of
-- `qf` on which the fiber is smooth over `κ(q ∩ R)`, and the finitely presented local flatness +
-- smooth-fiber criterion then produces a principal-open neighborhood of `q` on which `R → S` is
-- smooth.
/-- Lemma 10.137.16: if some basic open neighborhood `S_g` of `q` is of finite presentation over
`R`, the local ring homomorphism `R_(q ∩ R) → S_q` is flat, and the fiber
`κ(q ∩ R) ⊗[R] S` is smooth over `κ(q ∩ R)` at the prime corresponding to `q`, then `R → S` is
smooth at `q`, i.e. some localization `S_h` with `h ∉ q` is smooth over `R`. -/
lemma smoothAtPrime_of_exists_finitePresentation_nearPrime_flat_and_fiberSmoothAtPrime
    (q : PrimeSpectrum S)
    (hfp : ∃ g : S, g ∉ q.asIdeal ∧ FinitePresentation R (Localization.Away g))
    (hflat :
      (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R S) rfl).Flat)
    (hfiber :
      SmoothAtPrime (q.asIdeal.under R).ResidueField ((q.asIdeal.under R).Fiber S)
        (fiberPrimeAt R S q)) :
    SmoothAtPrime R S q := sorry

end Algebra
