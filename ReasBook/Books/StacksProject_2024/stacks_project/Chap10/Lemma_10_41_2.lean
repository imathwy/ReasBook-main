import StacksProject_2024.Chap05.Lemma_5_23_6
import StacksProject_2024.Chap10.Lemma_10_29_2
import StacksProject_2024.Chap10.Lemma_10_41_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open PrimeSpectrum
open Algebra.HasGoingDown
open Topology

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain triage:
* primary domain: going down for commutative algebras, expressed through the induced map on prime
  spectra;
* sampled owner declarations:
  `Algebra.HasGoingDown`,
  `Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`,
  `primeSpectrum_comap_isSpectralMap`,
  `exists_specializingPoint_of_mem_closure_of_isClosed_constructibleTopology`;
* best owner abstraction: `Algebra.HasGoingDown R S`, with the prime-spectrum
  `GeneralizingMap (comap (algebraMap R S))` formulation as derived API;
* layer: `source-facing`, since Lemma 10.41.2 adds the textbook open-map criterion for going down
  rather than merely recalling an existing equivalence.

Primitive-vs-derived split:
* primitive data: the ambient `R`-algebra structure on `S` and the open-map hypothesis on
  `PrimeSpectrum.comap (algebraMap R S)`;
* derived API: the reformulation of going down as
  `GeneralizingMap (comap (algebraMap R S))`, plus the constructible-topology closedness of
  singleton fibers obtained from the spectral-map owner.
-/
/-- Lemma 10.41.2: if the canonical map `Spec(S) → Spec(R)` is open, then the `R`-algebra `S`
has the canonical going-down property `Algebra.HasGoingDown R S`. -/
-- Proof sketch: this is the Stacks proof. Let `p ⊆ p'` in `R` and let `q'` lie over `p'`. For
-- every `g ∉ q'`, the basic open `D(g)` contains `q'`, so its image in `Spec(R)` is an open
-- neighborhood of `p'`; since opens in `Spec(R)` are stable under generalization, it also contains
-- `p`. By Lemma `10.18.6`, this says `S_g ⊗[R] κ(p)` is nontrivial for every `g ∉ q'`. Passing to
-- the directed colimit over `g ∉ q'` shows `S_{q'} ⊗[R] κ(p)` is nontrivial, so `p` lies in the
-- image of `Spec(S_{q'}) → Spec(R)` by Lemma `10.18.6` again. Unwinding this gives a prime of `S`
-- below `q'` lying over `p`.
@[stacks 0407]
theorem hasGoingDown_of_isOpenMap_primeSpectrum_comap
    (hopen : IsOpenMap (comap (algebraMap R S))) :
    Algebra.HasGoingDown R S := by
  rw [Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap]
  intro q p hpq
  let f : PrimeSpectrum S → PrimeSpectrum R := comap (algebraMap R S)
  have hcompact : IsSpectralMap f := primeSpectrum_comap_isSpectralMap (algebraMap R S)
  have hfiber_closed : IsClosed[constructibleTopology (PrimeSpectrum S)] (f ⁻¹' ({p} : Set _)) := by
    have hp_closed : @IsClosed (PrimeSpectrum R) (constructibleTopology (PrimeSpectrum R))
        ({p} : Set (PrimeSpectrum R)) := by
      letI : @T2Space (PrimeSpectrum R) (constructibleTopology (PrimeSpectrum R)) :=
        constructibleTopology_t2Space_of_spectralSpace
      exact @isClosed_singleton (PrimeSpectrum R) (constructibleTopology (PrimeSpectrum R)) _ p
    exact
      @IsClosed.preimage (PrimeSpectrum S) (PrimeSpectrum R)
        (constructibleTopology (PrimeSpectrum S)) (constructibleTopology (PrimeSpectrum R))
        f hcompact.continuous_constructibleTopology ({p} : Set (PrimeSpectrum R)) hp_closed
  have hq_mem : q ∈ closure (f ⁻¹' ({p} : Set _)) := by
    rw [← hopen.preimage_closure_eq_closure_preimage (continuous_comap (algebraMap R S))
      ({p} : Set _)]
    simpa [f, specializes_iff_mem_closure] using hpq
  obtain ⟨q', hq', hq'q⟩ :=
    exists_specializingPoint_of_mem_closure_of_isClosed_constructibleTopology hfiber_closed hq_mem
  exact ⟨q', hq'q, by simpa [f] using hq'⟩

end
