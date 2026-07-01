import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open PrimeSpectrum

section

variable {S : Type u} [CommRing S]
variable (𝒜 : ℤ → Submodule ℤ S) [GradedRing 𝒜]

/- Domain triage:
* primary domain: graded commutative algebra and spectral maps on homogeneous-prime loci;
* sampled declarations:
  `Ideal.IsHomogeneous`,
  `HomogeneousIdeal`,
  `GradedRing.projZeroRingHom'`,
  `PrimeSpectrum.isHomeomorph_comap`;
* best owner abstraction: the canonical spectrum map `comap (algebraMap (𝒜 0) S)`;
* layer: `bridge/view`;
* primitive data: the subtype `{ p : PrimeSpectrum S // p.asIdeal.IsHomogeneous 𝒜 }`;
* derived API: the restriction of `comap (algebraMap (𝒜 0) S)` along the subtype coercion.
-/

/-- Lemma 10.57.2 (Stacks, Tag `00JO`): if a `ℤ`-graded ring contains a homogeneous invertible
element in some positive degree, then the restriction of `PrimeSpectrum.comap` along
`algebraMap (𝒜 0) S` to the subtype of homogeneous prime ideals is a homeomorphism. The source
carries the induced topology from `Spec(S)`. -/
-- Proof sketch: this is the restriction of `PrimeSpectrum.comap` along `algebraMap (𝒜 0) S`.
-- For a prime `𝔭₀ ⊆ 𝒜 0`, the proof of Tag `00JO` constructs the inverse by sending
-- `𝔭₀` to `√(𝔭₀S)`, which is homogeneous and prime because a positive-degree homogeneous unit
-- lets one compare degrees with degree zero. To prove openness, if `g = ∑ gᵢ`, then the image of
-- `G ∩ D(g)` is `⋃ᵢ D(gᵢ^d / f^i)` in `Spec (𝒜 0)`.
@[stacks 00JO]
theorem Lemma_10_57_2
    (hunit : ∃ d > 0, ∃ f : 𝒜 d, IsUnit (f : S)) :
    IsHomeomorph
      ((comap (algebraMap (𝒜 0) S)) ∘
        (Subtype.val : { p : PrimeSpectrum S // p.asIdeal.IsHomogeneous 𝒜 } → PrimeSpectrum S)) := by
  sorry

end
