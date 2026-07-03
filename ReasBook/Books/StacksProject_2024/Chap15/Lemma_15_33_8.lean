import Mathlib
import stacks_project.Chap10.Definition_10_134_1
import stacks_project.Chap10.Lemma_10_154_3
import stacks_project.Chap15.Lemma_15_33_7

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open scoped TensorProduct

universe u v

noncomputable section

section

variable {A : Type u} {B : Type u} {Ah : Type u} {Bh : Type u}
variable [CommRing A] [CommRing B] [CommRing Ah] [CommRing Bh]
variable [Algebra A B] [Algebra A Ah] [Algebra B Bh] [Algebra A Bh] [Algebra Ah Bh]
variable [IsScalarTower A B Bh] [IsScalarTower A Ah Bh]

/-
Domain-style sampling for Lemma 15.33.8:
* primary domain: cotangent-homology and Kähler-differential comparison maps for a compatible
  square of commutative rings under ind-étale hypotheses;
* sampled owner declarations:
  - `RingHom.IsFilteredColimitOfEtale`, the chapter owner for ind-étale ring maps;
  - `tensor_presentation_cotangent_h1_to_h1_cotangent`, the source-facing `H^{-1}` map from a
    tensorized naive cotangent complex to cotangent homology;
  - `H1Cotangent.map`, the owner change-of-base map on `H^{-1}`;
  - `KaehlerDifferential.mapBaseChange` and `KaehlerDifferential.map`, the owner maps on degree
    `0`.
* best owner abstraction: the primitive data here are the two cohomology comparison maps induced
  by the source-facing comparison
  `NL_{B/A} ⊗[B] Bh ⟶ NL_{Bh/Ah}`. The current chapter already has canonical owners for these
  induced maps on `H^{-1}` and `H^0`, but not for a general non-flat tensorized morphism in
  `D(Bh)`, so this file should expose those cohomology-level maps directly instead of inventing a
  parallel derived-category owner.

Source/core/bridge triage:
* `source-facing`: the comparison
  `NL_{B/A} ⊗[B] Bh ⟶ NL_{Bh/Ah}` through its induced maps on `H^{-1}` and `H^0`;
* `core/canonical`: `RingHom.IsFilteredColimitOfEtale`,
  `tensor_presentation_cotangent_h1_to_h1_cotangent`, `H1Cotangent.map`,
  `KaehlerDifferential.mapBaseChange`, and `KaehlerDifferential.map`;
* `bridge/view`: the named cohomology comparison composites below.
-/

attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Algebra.H1Cotangent

/-- The degree `-1` comparison
`H₁(NL(P/A) ⊗[B] Bh) → H₁(L_{Bh/Ah})`
attached to a compatible square `A → Ah`, `A → B`, `B → Bh`, `Ah → Bh`, written through the
chapter owners for the presentation-level Jacobi-Zariski map and the change-of-base map. -/
noncomputable abbrev presentationBaseChangeComparison
    (A Ah B Bh : Type u)
    [CommRing A] [CommRing B] [CommRing Ah] [CommRing Bh]
    [Algebra A B] [Algebra A Ah] [Algebra B Bh] [Algebra A Bh] [Algebra Ah Bh]
    [IsScalarTower A B Bh] [IsScalarTower A Ah Bh] {ι : Type v}
    (P : Generators A B ι) :
    LinearMap.ker (LinearMap.baseChange Bh P.toExtension.cotangentComplex) →ₗ[Bh]
      H1Cotangent Ah Bh :=
  (map A Ah Bh Bh).comp (tensor_presentation_cotangent_h1_to_h1_cotangent Bh P)

end Algebra.H1Cotangent

namespace KaehlerDifferential

/-- The degree `0` comparison
`Bh ⊗[B] Ω[B⁄A] → Ω[Bh⁄Ah]`
attached to a compatible square `A → Ah`, `A → B`, `B → Bh`, `Ah → Bh`. -/
noncomputable abbrev baseChangeComparison
    (A Ah B Bh : Type u)
    [CommRing A] [CommRing B] [CommRing Ah] [CommRing Bh]
    [Algebra A B] [Algebra A Ah] [Algebra B Bh] [Algebra A Bh] [Algebra Ah Bh]
    [IsScalarTower A B Bh] [IsScalarTower A Ah Bh] :
    Bh ⊗[B] Ω[B⁄A] →ₗ[Bh] Ω[Bh⁄Ah] :=
  (map A Ah Bh Bh).comp (mapBaseChange A B Bh)

end KaehlerDifferential

-- Proof sketch: `A → Ah` and `B → Bh` being filtered colimits of étale algebras makes
-- `NL_{Ah/A}` and `NL_{Bh/B}` acyclic. Apply the Jacobi-Zariski sequence to `A → Ah → Bh` to
-- identify `NL_{Bh/A}` and `NL_{Bh/Ah}` on cohomology, then apply Lemma `15.33.7` to
-- `A → B → Bh`, using that étale maps are local complete intersections, to identify
-- `NL_{B/A} ⊗[B] Bh` and `NL_{Bh/A}` on cohomology. Composing these identifications gives the
-- stated bijectivity in degrees `1` and `0`. 
/-- Lemma 15.33.8, degree `-1`: if `A → Ah` and `B → Bh` are filtered colimits of étale
algebras compatible with `A → B`, then the canonical comparison
`NL_{B/A} ⊗[B] Bh → NL_{Bh/Ah}` induces a bijection on `H^{-1}`. -/
theorem naiveCotangentFilteredColimitOfEtaleComparison_h1_bijective
    (hAh : (algebraMap A Ah).IsFilteredColimitOfEtale)
    (hBh : (algebraMap B Bh).IsFilteredColimitOfEtale) :
    Function.Bijective
      (H1Cotangent.presentationBaseChangeComparison A Ah B Bh (Generators.self A B)) := sorry

/-- Lemma 15.33.8, degree `0`: if `A → Ah` and `B → Bh` are filtered colimits of étale
algebras compatible with `A → B`, then the canonical comparison
`NL_{B/A} ⊗[B] Bh → NL_{Bh/Ah}` induces a bijection on `H^0 = Ω`. -/
theorem naiveCotangentFilteredColimitOfEtaleComparison_kaehler_bijective
    (hAh : (algebraMap A Ah).IsFilteredColimitOfEtale)
    (hBh : (algebraMap B Bh).IsFilteredColimitOfEtale) :
    Function.Bijective (KaehlerDifferential.baseChangeComparison A Ah B Bh) := sorry

/-- Lemma 15.33.8: if `A → Ah` and `B → Bh` are filtered colimits of étale algebras compatible
with `A → B`, then the canonical comparison
`NL_{B/A} ⊗[B] Bh → NL_{Bh/Ah}` induces bijections on the two cohomology groups of the naive
cotangent complex. In particular, this applies to henselizations and strict henselizations. -/
theorem naiveCotangent_cohomology_comparison_bijective_of_filteredColimitOfEtale
    (hAh : (algebraMap A Ah).IsFilteredColimitOfEtale)
    (hBh : (algebraMap B Bh).IsFilteredColimitOfEtale) :
    Function.Bijective
      (H1Cotangent.presentationBaseChangeComparison A Ah B Bh (Generators.self A B)) ∧
      Function.Bijective (KaehlerDifferential.baseChangeComparison A Ah B Bh) := by
  exact ⟨
    naiveCotangentFilteredColimitOfEtaleComparison_h1_bijective hAh hBh,
    naiveCotangentFilteredColimitOfEtaleComparison_kaehler_bijective hAh hBh
  ⟩

end
