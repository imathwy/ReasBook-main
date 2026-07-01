import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Topology

/-
Domain-style sampling:
- primary domain: quasi-finite finite-type algebras, integral closures, and the algebraic
  Zariski Main Theorem;
- sampled owner declarations:
  `Algebra.ZariskisMainProperty`,
  `Algebra.ZariskisMainProperty.of_finiteType`,
  `Algebra.ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bijective`,
  `Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective`;
- best owner abstraction: the primewise local comparison data are owned upstream by
  `Algebra.ZariskisMainProperty`; the present lemma is the `source-facing` globalized integral
  closure statement built from those local owners together with the induced map on prime spectra;
- primitive data: an intermediate subalgebra `S'' : Subalgebra R S`, the inclusion
  `S'' ≤ integralClosure R S`, finiteness `Module.Finite R S''`, the open-embedding statement on
  `PrimeSpectrum`, and the away-map bijectivity clause for basic opens in the image;
- derived API to avoid as primitive wrappers: one-off conjunction packages for “finite subalgebra
  of the integral closure” and for the combined Zariski-main comparison property.

Source/core/bridge triage:
- `source-facing`: the global open-embedding and finite intermediate-subalgebra formulation of
  Lemma `10.123.14`;
- `core/canonical`: `Algebra.ZariskisMainProperty` for the local comparison ingredient;
- `bridge/view`: passing from the primewise owner theorem to the global spectrum/open-cover
  formulation used here.
-/

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S] [Algebra.QuasiFinite R S]

/-- Lemma 10.123.14 (1): if `S' = integralClosure R S` and `R → S` is finite type and
quasi-finite, then the induced map `Spec(S) → Spec(S')` is a homeomorphism onto an open subset,
i.e. an open embedding. -/
-- Proof sketch: apply Zariski's Main Theorem pointwise to each prime of `S` to obtain basic open
-- neighborhoods on which `Spec(S) → Spec(S')` is identified with the spectrum map of a bijective
-- localization-away map. Quasi-compactness of `Spec(S)` then lets one glue these local
-- identifications into a global open embedding.
theorem primeSpectrum_comap_integralClosure_isOpenEmbedding :
    IsOpenEmbedding (PrimeSpectrum.comap (integralClosure R S).val.toRingHom) := sorry

/-- Lemma 10.123.14 (2): if `g ∈ S' = integralClosure R S` and the basic open `D(g)` of
`Spec(S')` is contained in the image of `Spec(S) → Spec(S')`, then the canonical localization map
`S'_g → S_g` is bijective, equivalently `S'_g ≅ S_g`. -/
-- Proof sketch: cover the image of `Spec(S) → Spec(S')` by finitely many principal opens coming
-- from the pointwise Zariski-main theorem. Over each overlap with `D(g)` the away map is
-- bijective; apply the standard local-on-a-principal-cover criterion to descend bijectivity to the
-- away map at `g`.
theorem awayMap_bijective_of_basicOpen_subset_range_integralClosure
    (g : integralClosure R S)
    (hg :
      ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum (integralClosure R S))) ⊆
        Set.range (PrimeSpectrum.comap (integralClosure R S).val.toRingHom))) :
    Function.Bijective (Localization.awayMap (integralClosure R S).val.toRingHom g) := sorry

/-- Lemma 10.123.14 (3): there exists a finite `R`-subalgebra `S''` of the integral closure
`S' = integralClosure R S` such that the induced map `Spec(S) → Spec(S'')` is an open embedding,
and whenever a basic open `D(g)` of `Spec(S'')` is contained in its image, the canonical
localization map `S''_g → S_g` is bijective. -/
-- Proof sketch: choose finitely many elements of the integral closure whose principal opens cover
-- `Spec(S)` and on which the away maps to `S` are bijective. Generate an `R`-subalgebra of the
-- integral closure by these elements together with finitely many auxiliary generators for the
-- corresponding localized rings; this subalgebra is module-finite over `R` and inherits the two
-- local properties from the chosen finite cover.
theorem exists_finite_subalgebra_of_integralClosure_with_zariskiMain_properties :
    ∃ S'' : Subalgebra R S,
      S'' ≤ integralClosure R S ∧
      Module.Finite R S'' ∧
      IsOpenEmbedding (PrimeSpectrum.comap S''.val.toRingHom) ∧
      ∀ g : S'',
        ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S'')) ⊆
          Set.range (PrimeSpectrum.comap S''.val.toRingHom)) →
          Function.Bijective (Localization.awayMap S''.val.toRingHom g) := sorry

end
