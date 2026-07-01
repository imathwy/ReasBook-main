import Mathlib
import Mathlib.Data.List.TFAE
import stacks_project.Chap10.Lemma_10_122_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum
open TopologicalSpace
open scoped PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/- Domain-style sampling for Lemma 10.122.2:
- primary domain: the fiber of `Spec S → Spec R` over a prime `p`, viewed through the canonical
  fiber ring `p.asIdeal.Fiber S = κ(p) ⊗[R] S`;
- sampled owner declarations:
  `PrimeSpectrum.preimageEquivFiber`,
  `PrimeSpectrum.preimageHomeomorphFiber`,
  `isolatedPoint_tfae`,
  `topologicalKrullDimAt`;
- best owner abstraction: the canonical fiber-prime owner
  `PrimeSpectrum.preimageEquivFiber R S p`, with Lemma `10.122.1` supplying the derived
  isolated-point `List.TFAE` on the fiber ring;
- primitive data: `p : PrimeSpectrum R`, `q : PrimeSpectrum S`, and the lies-over witness
  `hq : PrimeSpectrum.comap (algebraMap R S) q = p`;
- derived API: the six equivalent fiberwise conditions.

Source/core/bridge triage:
- `source-facing`: `prime_over_isolated_point_in_fiber_tfae`;
- `core/canonical`: `PrimeSpectrum.preimageEquivFiber`, `PrimeSpectrum.preimageHomeomorphFiber`,
  and `isolatedPoint_tfae`;
- `bridge/view`: clause `(3)`, which keeps the textbook basic-open singleton condition on primes
  of `S` lying over `p` while the other clauses live directly on the fiber prime. -/

-- Proof sketch: identify the fiber of `Spec S → Spec R` over `p` with `Spec (κ(p) ⊗[R] S)` via
-- `PrimeSpectrum.preimageHomeomorphFiber`. Under this correspondence, the point `q` becomes
-- `PrimeSpectrum.preimageEquivFiber R S p ⟨q, hq⟩`, and the six clauses are exactly the six
-- clauses of Lemma `10.122.1` for the finite type `κ(p)`-algebra `p.asIdeal.Fiber S`, with
-- clause `(3)` restated in the source-facing primes-over-`p` basic-open language.
/-- Lemma 10.122.2: for a finite type ring map `R → S`, a prime `q` of `S` lying over `p`, and the
corresponding point `\bar q` of the fiber `Spec (κ(p) ⊗[R] S)`, the following are equivalent:
`\bar q` is an isolated point of the fiber; the local fiber ring at `\bar q` is finite over
`κ(p)`; there exists `g ∉ q` such that the primes of `S` lying over `p` inside `D(g)` are exactly
`{q}`; the local topological dimension of the fiber at `\bar q` is zero; `\bar q` is closed and
the local fiber ring has Krull dimension zero; and the residue field extension at `\bar q` is
finite over `κ(p)` while the local fiber ring has Krull dimension zero. -/
theorem prime_over_isolated_point_in_fiber_tfae (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    let qbar : PrimeSpectrum (p.asIdeal.Fiber S) := PrimeSpectrum.preimageEquivFiber R S p ⟨q, hq⟩
    List.TFAE
      [ IsOpen ({qbar} : Set (PrimeSpectrum (p.asIdeal.Fiber S)))
      , Module.Finite p.asIdeal.ResidueField (Localization.AtPrime qbar.asIdeal)
      , ∃ g : S, g ∉ q.asIdeal ∧
          ({q' : PrimeSpectrum S | PrimeSpectrum.comap (algebraMap R S) q' = p} ∩
            (D(g) : Set (PrimeSpectrum S)) = ({q} : Set (PrimeSpectrum S)))
      , topologicalKrullDimAt qbar = 0
      , IsClosed ({qbar} : Set (PrimeSpectrum (p.asIdeal.Fiber S))) ∧
          ringKrullDim (Localization.AtPrime qbar.asIdeal) = 0
      , Module.Finite p.asIdeal.ResidueField qbar.asIdeal.ResidueField ∧
          ringKrullDim (Localization.AtPrime qbar.asIdeal) = 0
      ] := sorry

end
