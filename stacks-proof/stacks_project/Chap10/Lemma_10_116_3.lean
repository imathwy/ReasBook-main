import Mathlib
import stacks_project.Chap05.Definition_5_10_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open TopologicalSpace

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/- 
Domain-style sampling for the local dimension formula on affine schemes of finite type over a
field:
- primary domain: local Krull dimension on `Spec(S)`, organized around the owner
  `topologicalKrullDimAt` and the local ring `Localization.AtPrime x.asIdeal`;
- sampled owner declarations of the same kind:
  `topologicalKrullDimAt`,
  `topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over`,
  `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`,
  `IsLocalization.AtPrime.ringKrullDim_eq_height`;
- best owner abstraction: the ambient owner is the local-dimension object `topologicalKrullDimAt`
  on `PrimeSpectrum S`, while the local algebra data are already canonically owned by
  `Localization.AtPrime x.asIdeal` and `x.asIdeal.ResidueField`;
- primitive data: the point `x : PrimeSpectrum S` of the finite type affine scheme `Spec(S)`;
- derived API: the additive decomposition of `topologicalKrullDimAt x` into the Krull dimension of
  the canonical local ring and the transcendence degree of the canonical residue field.

Source/core/bridge triage:
* `source-facing`: the textbook local dimension formula at a prime of a finite type algebra over a
  field;
* `core/canonical`: `topologicalKrullDimAt`, `Localization.AtPrime`, `Ideal.ResidueField`, and
  mathlib's localization-height owner `IsLocalization.AtPrime.ringKrullDim_eq_height`;
* `bridge/view`: the comparison from the local topological owner to maximal localizations from
  Lemma `10.114.5`, together with the chain-length interpretation of heights.

There is no separate local wrapper to keep here: the theorem should speak directly in terms of the
owner objects `topologicalKrullDimAt`, `Localization.AtPrime x.asIdeal`, and
`x.asIdeal.ResidueField`.
-/

-- Proof sketch: combine the description of the local dimension at `x` as the maximum dimension of
-- irreducible components through `x` with the chain decomposition through the prime `x.asIdeal`.
-- The part of a maximal chain below `x.asIdeal` contributes `ringKrullDim (Localization.AtPrime
-- x.asIdeal)`, while the part above it is measured by the transcendence degree of
-- `x.asIdeal.ResidueField` over `k`.
/-- Lemma 10.116.3: for a point `x` of `X = Spec(S)`, where `S` is a finite type `k`-algebra and
`x.asIdeal` is the corresponding prime ideal `𝔭`, the local dimension `dim_x(X)` equals the Krull
dimension of the localization `S_𝔭` plus the transcendence degree of the residue field
`κ(𝔭) = x.asIdeal.ResidueField` over `k`. -/
theorem topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField
    (x : PrimeSpectrum S) :
    topologicalKrullDimAt x =
      ringKrullDim (Localization.AtPrime x.asIdeal) +
        Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := sorry

end
