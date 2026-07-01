import Mathlib
import stacks_project.Chap10.Lemma_10_50_11
import stacks_project.Chap15.Definition_15_105_3
import stacks_project.Chap15.Lemma_15_105_19

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open CommRingCat

universe u

section

variable {A : Type u} {K : Type u} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
variable [IsFractionRing A K] [IsIntegrallyClosed A]

/-
Domain-style sampling:
- primary domain: commutative algebra of normal domains, valuation-theoretic presentations of
  fraction fields, and cartesian squares in `CommRingCat`;
- sampled owner declarations:
  `CategoryTheory.IsPullback`,
  `HasWeakDimensionLE`,
  `RingHom.Flat`,
  `CategoryTheory.Epi`;
- best owner abstraction: the source-facing object here is the cartesian square over the canonical
  map `A → K`, and the correct square owner is `IsPullback` itself rather than a new local
  package. The Stacks lemma is a single existence statement, so the lower-left weak-dimension
  condition and the flat/injective/epimorphism properties of the bottom map belong on the same
  witness instead of being split into parallel existential theorems.

Primitive-vs-derived split:
- primitive data: rings `V` and `L`, morphisms `i`, `j`, `k`, and the pullback witness
  `IsPullback i (ofHom (algebraMap A K)) k j` together with the properties
  `HasWeakDimensionLE V 1`, `k.hom.Flat`, `Function.Injective k.hom`, and `Epi k`;
- derived API: forgetful consequences such as the existence of the cartesian square alone are
  derived from the single source-facing witness and do not need separate public owners here.

Source/core/bridge triage:
- `source-facing`: the Stacks existence assertion for one cartesian square over `A → K` carrying
  all listed properties at once;
- `core/canonical`: `IsPullback`, `HasWeakDimensionLE`, `Function.Injective`, and `Epi`;
- `bridge/view`: no additional bridge object is needed here, because the categorical pullback
  square is already the owner abstraction used downstream.
-/

-- Proof sketch: for each `x : K` outside the image of `A`, choose a valuation subring `Vₓ ⊆ K`
-- containing `A` but not `x` by Lemma `10.50.11`. Take `V` to be the product of these valuation
-- rings and `L` the product of the ambient field `K`; the induced square with `A → K` is
-- cartesian by the intersection description of a normal domain inside its fraction field. Lemma
-- `15.105.19` gives weak dimension at most `1` for this product and identifies `V → L` as a
-- localization. Localizations are flat and epimorphisms, and here the map is also injective
-- because each component `Vₓ → K` is injective.
/-- Lemma 15.105.20: if `A` is a normal domain with fraction field `K`, then there exists a
cartesian square
\[
\require{AMScd}
\begin{CD}
A @>>> K \\
@VVV @VVV \\
V @>>> L
\end{CD}
\]
of commutative rings where `V` has weak dimension at most `1` and the bottom map `V → L` is flat,
injective, and an epimorphism. -/
theorem exists_cartesian_square_over_fractionField_with_weakDimensionLEOne_and_flat_injective_epi :
    ∃ (V L : CommRingCat.{u}) (i : of A ⟶ V) (k : V ⟶ L) (j : of K ⟶ L),
      IsPullback i (ofHom (algebraMap A K)) k j ∧
        HasWeakDimensionLE V 1 ∧
        k.hom.Flat ∧ Function.Injective k.hom ∧ Epi k := sorry

end
