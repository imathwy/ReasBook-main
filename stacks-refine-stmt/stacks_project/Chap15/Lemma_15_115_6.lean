import Mathlib
import stacks_project.Chap15.Definition_15_112_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

/- Domain-style sampling:
- source-facing owner: `IsTamelyRamifiedWithRespectTo A L` from `Definition_15_112_7`;
- sampled canonical declarations in this domain:
  `IsTamelyRamifiedWithRespectTo`,
  `FiniteDimensional.trans`,
  `Algebra.IsSeparable.trans`,
  `FiniteDimensional.right`,
  `Algebra.isSeparable_tower_top_of_isSeparable`;
- best owner abstraction: the chapter owner `IsTamelyRamifiedWithRespectTo A L`;
- primitive-vs-derived split: the branchwise residue-field separability and ramification-index
  coprimality data stay primitive in `Definition_15_112_7`, while this file only adds the derived
  tower-descent API.

Source/core/bridge triage:
- `source-facing`: the Stacks Project tower-descent statement for tame ramification;
- `core/canonical`: `IsTamelyRamifiedWithRespectTo`, together with the standard tower finiteness
  and separability owners;
- `bridge/view`: this file, which packages those tower hypotheses into the single descended tame
  owner rather than introducing branchwise duplicate local data.
-/

end

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

local notation "K" => FractionRing A

-- Proof sketch: let `B` and `C` be the integral closures of `A` in `L` and `M`. Since `C` is
-- finite over `B`, every maximal ideal of `B` over `maximalIdeal A` is the contraction of some
-- maximal ideal of `C`. For such a pair, multiplicativity of ramification indices shows that the
-- ramification index of `B` over `A` divides the one for `C` over `A`, hence is still prime to
-- the residue characteristic. Separability of the residue-field extension for `B` over `A`
-- descends along the finite separable tower `κ(P) / κ(p) / κA`.
/-- Lemma 15.115.6: let `A` be a discrete valuation ring with fraction field `FractionRing A`. If
`M / L / K` is a tower of finite separable extensions, where `K = FractionRing A`, and `M` is
tamely ramified with respect to `A`, then `L` is tamely ramified with respect to `A`. -/
theorem isTamelyRamifiedWithRespectTo_of_tower
    {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    {M : Type w} [Field M] [Algebra A M] [Algebra K M] [Algebra L M]
    [IsScalarTower A K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L M]
    (hM : IsTamelyRamifiedWithRespectTo A M) :
    IsTamelyRamifiedWithRespectTo A L := by
  sorry

end
