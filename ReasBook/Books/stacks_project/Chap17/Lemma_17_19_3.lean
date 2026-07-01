import Mathlib
import stacks_project.Chap06.Lemma_6_21_5
import stacks_project.Chap05.Lemma_5_23_14
import stacks_project.Chap17.«17_19_2_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open scoped TopCat

attribute [local instance] CategoryTheory.Types.instConcreteCategory CategoryTheory.Types.instFunLike

noncomputable section

universe u

/- Domain-style sampling for Lemma 17.19.3:
- primary domain: set-valued sheaves on spectral spaces, descended along spectral maps to finite
  sober spaces;
- sampled owner declarations:
  `HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn`,
  `spectralSpace_iff_homeomorphic_directed_limit_finite_sober`,
  `IsSpectralMap`,
  `QuasiSober`;
- best owner abstraction: the source-facing hypothesis is already the chapter owner
  `HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn` specialized to quasi-compact
  opens, while the spectral-space input is governed upstream by the chapter-5 directed-limit
  characterization `spectralSpace_iff_homeomorphic_directed_limit_finite_sober`; the chapter-5
  owner for the source sober conclusion is the pair `T0Space Y` and `QuasiSober Y`, so the finite
  stage returned here should expose both pieces directly;
- primitive data: a sheaf `ℱ` on a spectral space `X` with the finite coequalizer presentation
  from `17.19.2.1` on quasi-compact opens;
- derived API: the descended finite `T₀` space `Y`, the spectral map `f : X ⟶ Y`, the model sheaf
  `𝒢`, its finite stalk condition, and the resulting inverse-image isomorphism.

Source/core/bridge triage:
- `source-facing`: the existence of a finite sober model for a constructible sheaf presentation,
  expressed canonically as `Finite Y`, `T0Space Y`, and `QuasiSober Y`;
- `core/canonical`: `HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn`,
  `spectralSpace_iff_homeomorphic_directed_limit_finite_sober`, `IsSpectralMap`, and
  `QuasiSober`;
- `bridge/view`: the comparison isomorphism identifying `ℱ` with the inverse image of `𝒢` along the
  spectral map `f`.
-/

-- Proof sketch: combine the finite coequalizer presentation from `17.19.2.1` with the directed
-- inverse-limit presentation of a spectral space by finite `T₀` stages from Lemma `5.23.14`,
-- together with the canonical sober-space owner form `T0Space ∧ QuasiSober`.
-- Descend the finitely many quasi-compact opens and the finitely many structure maps defining the
-- coequalizer to one finite `T₀` stage, then take on that stage the corresponding coequalizer
-- sheaf `𝒢`; its stalks are finite because it is built from finitely many finite constant sheaves
-- by finite colimits, and inverse image along the projection recovers `ℱ`.
/-- Lemma 17.19.3: a sheaf of sets on a spectral space admitting the finite coequalizer
presentation of `17.19.2.1` is the inverse image of a sheaf with finite stalks along some spectral
map
to a finite sober topological space, expressed canonically by `Finite Y`, `T0Space Y`, and
`QuasiSober Y`. Here the source-facing hypothesis is the owner predicate
`HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn (fun U ↦ IsCompact (U : Set X))`. -/
theorem exists_finite_sober_sheaf_model_of_constructible_set_presentation
    {X : TopCat.{u}} [SpectralSpace X]
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
    (ℱ : Sh(X))
    (hℱ :
      HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn
        (fun U ↦ IsCompact (U : Set X)) ℱ) :
    ∃ (Y : TopCat.{u}) (_ : Finite Y) (_ : T0Space Y) (_ : QuasiSober Y) (f : X ⟶ Y)
      (_ : IsSpectralMap f) (𝒢 : Sh(Y)) (e : ((f⁻¹).obj 𝒢) ≅ ℱ),
      ∀ y : Y, Finite (𝒢.presheaf.stalk y) := sorry
