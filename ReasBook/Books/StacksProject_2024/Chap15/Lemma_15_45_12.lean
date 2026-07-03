import StacksProject_2024.Chap15.Lemma_15_105_14
import StacksProject_2024.Chap15.Lemma_15_105_17

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

namespace PrimeSpectrum

/- Domain triage:
* primary domain: fibers `κ(p) ⊗[A] B`, primes of `B` lying over `p`, and their residue fields;
* source-facing items in this file: finiteness of the fiber over `p`, the resulting product
  decomposition of the fiber ring, and separable algebraicity of the residue-field extensions;
* sampled owners for the refinement:
  `RingHom.IsFilteredColimitOfEtale`,
  `isWeaklyEtale_of_isFilteredColimitOfEtale`,
  `Ideal.primesOver`,
  `Ideal.Fiber`,
  `IsArtinianRing.equivPi`;
* bridge/view data removed by this refinement: arbitrary indexing types, bijections for the
  product decomposition, and the existence-only wrapper around the decomposition map. The
  canonical owner data are `Ideal.Fiber p B` and `p.primesOver B`; the primitive bridge data are
  the coordinate maps from the fiber ring to each residue field over `p`, and part `(2)` derives
  the product map from those owners instead of treating the whole product packaging as primitive.

Primitive data are `A`, `B`, the filtered-colimit-of-étale hypothesis on `algebraMap A B`, and the
chosen prime `p : PrimeSpectrum A`. The product decomposition in part `(2)` is therefore stated
directly over the owner set `p.asIdeal.primesOver B`, rather than via an auxiliary `ι` and a
reindexing bijection, with the canonical product map exposed as data and bijectivity as the
source-facing theorem. -/

/- Lemma 15.45.12 (1): if `B` is a filtered colimit of étale `A`-algebras and the fiber ring
`p.asIdeal.Fiber B` is Noetherian, then only finitely many primes of `B` lie over `p`.

 Proof sketch: base change the filtered-colimit-of-étale presentation of `B` along
 `A → κ(p)` to see that the fiber ring `p.asIdeal.Fiber B` is a filtered colimit of étale
 `κ(p)`-algebras. Each stage is a finite product of finite separable field extensions, hence has
 discrete spectrum. The Noetherian fiber ring therefore has finitely many primes, and
 `PrimeSpectrum.primesOverOrderIsoFiber` identifies those primes with the primes of `B` over `p`. -/
theorem primesOver_finite_of_isFilteredColimitOfEtale_of_isNoetherianFiber
    (hcolim : (algebraMap A B).IsFilteredColimitOfEtale)
    (p : PrimeSpectrum A) [IsNoetherianRing (p.asIdeal.Fiber B)] :
    Finite (p.asIdeal.primesOver B) := sorry

end PrimeSpectrum

namespace Ideal

/-- The canonical ring homomorphism from the fiber ring `p.Fiber B = κ(p) ⊗[A] B` to the product
of the residue fields of the primes of `B` lying over `p`, indexed by the canonical owner set
`p.primesOver B`. -/
noncomputable def fiberToPiResidueField (p : Ideal A) [p.IsPrime]
    (B : Type v) [CommRing B] [Algebra A B] :
    p.Fiber B →+* ∀ q : p.primesOver B, q.1.ResidueField :=
  let φ : ∀ q : p.primesOver B, p.Fiber B →+* q.1.ResidueField :=
    fun q ↦
      (Algebra.TensorProduct.lift
        (Ideal.ResidueField.mapₐ p q.1 (Algebra.ofId _ _) (q.1.over_def p))
        (IsScalarTower.toAlgHom _ _ _)
        (fun _ _ ↦ Commute.all _ _)).toRingHom
  Pi.ringHom φ

end Ideal

namespace PrimeSpectrum

-- Proof sketch: the fiber ring `p.asIdeal.Fiber B = κ(p) ⊗[A] B` is both Noetherian and a
-- filtered colimit of étale `κ(p)`-algebras, so it is reduced with finitely many prime ideals, all
-- of which are maximal. Hence it is canonically a finite product of fields. Transport the index
-- set of those factors back to the canonical owner set `p.asIdeal.primesOver B` using
-- `PrimeSpectrum.primesOverOrderIsoFiber`, and then identify the canonical coordinate map
-- `Ideal.fiberToPiResidueField` with the reduced Artinian-ring product decomposition
-- `IsArtinianRing.equivPi`.
/-- Lemma 15.45.12 (2): if `B` is a filtered colimit of étale `A`-algebras and the fiber ring
`p.asIdeal.Fiber B` is Noetherian, then the canonical map from `p.asIdeal.Fiber B` to the finite
product of the residue fields of the primes of `B` lying over `p` is bijective. -/
theorem fiberToPiResidueField_bijective_of_isFilteredColimitOfEtale_of_isNoetherianFiber
    (hcolim : (algebraMap A B).IsFilteredColimitOfEtale)
    (p : PrimeSpectrum A) [IsNoetherianRing (p.asIdeal.Fiber B)] :
    Function.Bijective (p.asIdeal.fiberToPiResidueField B) := sorry

-- Proof sketch: a filtered colimit of étale `A`-algebras is weakly étale, so the source-facing
-- statement is a direct bridge to the chapter owner
-- `residueField_isAlgebraic_and_separable_of_isWeaklyEtale`. The Noetherian hypothesis used in
-- parts `(1)` and `(2)` is not part of the mathematical content of this residue-field claim.
/-- Lemma 15.45.12 (3): if `B` is a filtered colimit of étale `A`-algebras, then for every prime
`p` of `A` and every prime `q` of `B` lying over `p`, the residue field extension `κ(q) / κ(p)`
is separable algebraic. -/
theorem residueField_isAlgebraic_and_separable_of_isFilteredColimitOfEtale
    (hcolim : (algebraMap A B).IsFilteredColimitOfEtale)
    (p : PrimeSpectrum A) (q : p.asIdeal.primesOver B) :
    Algebra.IsAlgebraic p.asIdeal.ResidueField q.1.ResidueField ∧
      Algebra.IsSeparable p.asIdeal.ResidueField q.1.ResidueField := sorry

end PrimeSpectrum

end
