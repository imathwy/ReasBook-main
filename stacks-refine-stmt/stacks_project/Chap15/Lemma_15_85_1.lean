import Mathlib
import Mathlib.Data.List.TFAE
import stacks_project.Chap15.Lemma_15_69_2
import stacks_project.Chap15.Lemma_15_78_4

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedExt

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/- Domain-style sampling:
- primary domain: projective-amplitude criteria in the derived category of modules, specialized to
  two-term cohomology and degree-`1` derived `Ext`;
- sampled owner declarations:
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`,
  `HasProjectiveAmplitudeIn` from `Definition_15_69_1`,
  `derivedExtToModuleFunctor` and `projectiveAmplitudeIn_ext_vanishing_tfae` from
    `Lemma_15_69_2`,
  `projectiveAmplitudeIn_perfect_finitelyPresented_ext_tfae_of_isPseudoCoherent` from
    `Lemma_15_78_4`;
- best owner abstraction: the unrestricted degree-`1` vanishing condition is already the canonical
  zero-object statement `IsZero (derivedExtToModuleFunctor K 1)`, while the Noetherian
  specialization should keep the source-facing finite-module `Ext¹` clause explicit and use the
  finitely presented degree-`1` clause from `Lemma_15_78_4` only as the bridge justified by
  Noetherianness. The two-term cohomology-support hypothesis itself should live on the canonical
  t-structure owners `K.IsGE (-1)` and `K.IsLE 0`, with the entrywise vanishing formulation
  demoted to the bridge `DerivedCategory.isGE_iff` / `DerivedCategory.isLE_iff`.

Source/core/bridge triage:
- `source-facing`: the two-term cohomology projectivity criterion of Lemma `15.85.1`;
- `core/canonical`: `K.IsGE (-1)`, `K.IsLE 0`, `HasProjectiveAmplitudeIn`,
  `derivedExtToModuleFunctor`, and
  `projectiveAmplitudeIn_perfect_finitelyPresented_ext_tfae_of_isPseudoCoherent` from
  `Lemma_15_78_4`;
- `bridge/view`: the equivalence between the two-term cohomology condition
  `IsZero (H⁻¹ K) ∧ Projective (H⁰ K)` and the projective-amplitude owner specialized to
  `[0, 0]` under the canonical two-term bounds `K.IsGE (-1)` and `K.IsLE 0`.

Primitive data here are only the canonical two-term support bounds and the two-term cohomology
condition. The unrestricted `Ext¹` test is already canonical upstream as
`IsZero (derivedExtToModuleFunctor K 1)`; the finite-module test in the Noetherian specialization
is source-facing data and should stay visible in the public `TFAE`, with the finitely presented
degree-`1` clause demoted to a companion bridge.
-/

-- Proof sketch: apply Lemma `15.69.2` with `a = b = 0`. Under the hypothesis that the
-- canonical two-term bounds `K.IsGE (-1)` and `K.IsLE 0`, projective-amplitude in `[0, 0]`
-- means exactly that `H⁻¹(K) = 0` and `H⁰(K)` is projective, while
-- `IsZero (derivedExtToModuleFunctor K 1)` is the same as vanishing of `Ext¹_R(K, M)` for every
-- `R`-module `M`.
/-- Lemma 15.85.1: for a derived `R`-complex whose cohomology is concentrated in degrees `-1`
and `0`, encoded by `K.IsGE (-1)` and `K.IsLE 0`, the condition `H⁻¹(K) = 0` together with
projectivity of `H⁰(K)` is equivalent to the vanishing of `Ext¹_R(K, M)` for every
`R`-module `M`. -/
theorem two_term_cohomology_projective_iff_ext1_vanishes
    (K : DMod)
    (hKGE : K.IsGE (-1))
    (hKLE : K.IsLE 0) :
    (IsZero ((H (-1)).obj K) ∧ Projective ((H 0).obj K)) ↔
      IsZero (derivedExtToModuleFunctor K (1 : ℤ)) := sorry

end

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => (ModuleCat.single0Functor : ModuleCat R ⥤ DMod)

-- Proof sketch: the finiteness of `H⁻¹(K)` and `H⁰(K)` together with the canonical two-term
-- bounds `K.IsGE (-1)` and `K.IsLE 0` implies that `K` is pseudo-coherent by Lemma `15.65.17`.
-- Apply Lemma `15.78.4` with `a = b = 0`, and use the canonical bridge
-- `Module.finitePresentation_of_finite` to replace the finitely presented `Ext¹` test by the
-- source-facing finite-module version with finiteness exposed as an explicit hypothesis.
/-- Over a Noetherian ring, a two-term derived complex with finite cohomology in degrees `-1`
and `0` satisfies the same projectivity criterion when `Ext¹_R(K, M)` is tested only on finite
`R`-modules. -/
theorem two_term_cohomology_projective_ext1_tfae_of_noetherian
    (K : DMod)
    (hKGE : K.IsGE (-1))
    (hKLE : K.IsLE 0)
    (hfin_neg_one : Module.Finite R ((H (-1)).obj K))
    (hfin_zero : Module.Finite R ((H 0).obj K)) :
    List.TFAE [
      IsZero ((H (-1)).obj K) ∧ Projective ((H 0).obj K),
      IsZero (derivedExtToModuleFunctor K (1 : ℤ)),
      ∀ (M : ModuleCat R), Module.Finite R M →
        ∀ e : Ext^(1 : ℤ)(K, (single₀).obj M), e = 0
    ] := sorry

end

end CategoryTheory
