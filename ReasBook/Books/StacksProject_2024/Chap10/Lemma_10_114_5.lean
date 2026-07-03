import Mathlib
import stacks_project.Chap05.Definition_5_10_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open TopologicalSpace

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/- 
Domain-style sampling for local Krull dimension on affine schemes of finite type over a field:
- primary domain: local dimension in `Spec(S)`, compared both with irreducible components through a
  point and with localizations at maximal ideals above that point;
- sampled owner declarations of the same kind:
  `topologicalKrullDimAt`,
  `PrimeSpectrum.localizationAtPrimeIrreducibleComponents`,
  `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`,
  `IsLocalization.AtPrime.ringKrullDim_eq_height`;
- best owner abstraction: the local dimension owner is `topologicalKrullDimAt`, while irreducible
  components should be indexed through the canonical owner subtype `irreducibleComponents
  (PrimeSpectrum S)` rather than through a parallel raw-set wrapper;
- primitive data: the point `x : PrimeSpectrum S`;
- derived API: the supremum formula over irreducible components through `x` and the infimum formula
  over maximal localizations above `x`.

Source/core/bridge triage:
* `source-facing`: the two textbook formulas for the local Krull dimension at `x`;
* `core/canonical`: `topologicalKrullDimAt`, `irreducibleComponents (PrimeSpectrum S)`,
  `MaximalSpectrum S`, and the localization owner `Localization.AtPrime`;
* `bridge/view`: `PrimeSpectrum.localizationAtPrimeIrreducibleComponents` and the ring/topological
  Krull-dimension comparison on spectra.

This file should expose only those source-facing formulas, written against the existing owner
abstractions, rather than introducing parallel wrappers for components-through-`x` or maximal
ideals above `x`.
-/

-- Proof sketch: remove the irreducible components not containing `x` and work on the resulting
-- open neighbourhood of `x`. On every smaller open neighbourhood, the surviving irreducible
-- components are precisely the intersections with those components through `x`, and each such
-- intersection has the same Krull dimension as the ambient component. This identifies the local
-- dimension at `x` with the maximum of the dimensions of the irreducible components passing
-- through `x`.
/-- Lemma 10.114.5 (1): if `S` is a finite type `k`-algebra and `x : PrimeSpectrum S` is the point
of `X = Spec(S)` corresponding to a prime ideal `𝔭 ⊂ S`, then the local Krull dimension
`topologicalKrullDimAt x` equals the supremum, hence the
maximum, of the Krull dimensions of the irreducible components of `X` containing `x`. -/
theorem topologicalKrullDimAt_eq_iSup_topologicalKrullDim_irreducibleComponents_through
    (x : PrimeSpectrum S) :
    topologicalKrullDimAt x =
      ⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) // x ∈ (Z : Set (PrimeSpectrum S)) },
        topologicalKrullDim (Z : Set (PrimeSpectrum S)) := sorry

-- Proof sketch: for each maximal ideal `m` containing `x.asIdeal`, the local ring `Sₘ` has
-- Krull dimension equal to the maximum of the dimensions of the irreducible components through the
-- corresponding closed point. Choosing a closed point of `V(x.asIdeal)` outside the union of the
-- components not containing `x` ensures that exactly the components through `x` occur, so this
-- common maximum is also the minimum of the dimensions of the localizations `Sₘ` with
-- `x.asIdeal ≤ m.asIdeal`.
/-- The local Krull dimension at a point of `Spec(S)` is the infimum, hence the minimum, of the
Krull dimensions of the localizations `Sₘ` at maximal ideals `m` containing `x.asIdeal`. -/
theorem topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over
    (x : PrimeSpectrum S) :
    topologicalKrullDimAt x =
      ⨅ m : { m : MaximalSpectrum S // x.asIdeal ≤ m.asIdeal },
        ringKrullDim (Localization.AtPrime m.1.asIdeal) := sorry

end
