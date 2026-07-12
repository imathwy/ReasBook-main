import StacksProject_2024.Chap30.Lemma_30_15_2
import StacksProject_2024.Chap12.Lemma_12_10_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped DirectSum

noncomputable section

universe u v w wv

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` surfaced the Serre-quotient and equivalence layer around
categorical quotients, and local Proposition 30.14.4 verifies the project convention: keep
`Proj 𝒜` and `RingedSpace.Coh (Proj 𝒜).toRingedSpace` as canonical targets, while passing the
not-yet-formalized finite graded-module category, associated-sheaf functor, irrelevant Serre
class, and twisted-global-sections functor as explicit source-facing parameters. -/

/-- Proposition 30.15.3 (1): let `A` be a Noetherian graded ring and set `X = Proj(A)`.
For a chosen category `GrModfg` of finite graded `A`-modules, the Serre subcategory
`irrelevant` of irrelevant modules, and the associated-sheaf functor `M ↦ \widetilde M`, the
functor induced on the Serre quotient
`Mod_A^{fg} / Mod_{A, irrelevant}^{fg}` is an equivalence with
`Coh(\mathcal O_X)`. The hypothesis `hdesc` records that the displayed functor is induced by
`M ↦ \widetilde M`, and `hglobalSectionsFunctor_obj` records the object formula for the stated
quasi-inverse. -/
@[stacks 0BXF]
theorem projAssociatedSheafFunctor_irrelevantSerreQuotient_isEquivalence
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] [IsNoetherianRing A]
    (GrModfg : Type w) [Category.{wv} GrModfg] [Abelian GrModfg]
    (irrelevant : ObjectProperty GrModfg) [irrelevant.IsSerreClass]
    (forgetGradedModule : GrModfg ⥤ ModuleCat.{u} A)
    (associatedSheafFunctor : GrModfg ⥤ RingedSpace.Coh (Proj 𝒜).toRingedSpace)
    (twist : RingedSpace.Coh (Proj 𝒜).toRingedSpace → ℤ → (Proj 𝒜).Modules)
    [∀ ℱ : RingedSpace.Coh (Proj 𝒜).toRingedSpace,
      Module A (projCoherentSheafTruncatedGlobalSections 𝒜 (twist ℱ) 0)]
    (twistedGlobalSectionsFunctor : RingedSpace.Coh (Proj 𝒜).toRingedSpace ⥤ GrModfg)
    (hglobalSectionsFunctor_obj : ∀ ℱ : RingedSpace.Coh (Proj 𝒜).toRingedSpace,
      forgetGradedModule.obj (twistedGlobalSectionsFunctor.obj ℱ) ≅
        ModuleCat.of A (projCoherentSheafTruncatedGlobalSections 𝒜 (twist ℱ) 0))
    (descendedAssociatedSheafFunctor : irrelevant.isoModSerre.Localization ⥤
      RingedSpace.Coh (Proj 𝒜).toRingedSpace)
    (hdesc : irrelevant.isoModSerre.Q ⋙ descendedAssociatedSheafFunctor ≅
      associatedSheafFunctor) :
    descendedAssociatedSheafFunctor.IsEquivalence := sorry

/-- Proposition 30.15.3 (2): under the equivalence of
`Mod_A^{fg} / Mod_{A, irrelevant}^{fg}` with `Coh(\mathcal O_{Proj(A)})`, the quasi-inverse is
the functor
`\mathcal F ↦ \bigoplus_{n ≥ 0} Γ(Proj(A), \mathcal F(n))`, followed by the quotient functor to
`Mod_A^{fg} / Mod_{A, irrelevant}^{fg}`. -/
@[stacks 0BXF]
theorem projAssociatedSheafFunctor_irrelevantSerreQuotient_inverse_iso
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] [IsNoetherianRing A]
    (GrModfg : Type w) [Category.{wv} GrModfg] [Abelian GrModfg]
    (irrelevant : ObjectProperty GrModfg) [irrelevant.IsSerreClass]
    (forgetGradedModule : GrModfg ⥤ ModuleCat.{u} A)
    (associatedSheafFunctor : GrModfg ⥤ RingedSpace.Coh (Proj 𝒜).toRingedSpace)
    (twist : RingedSpace.Coh (Proj 𝒜).toRingedSpace → ℤ → (Proj 𝒜).Modules)
    [∀ ℱ : RingedSpace.Coh (Proj 𝒜).toRingedSpace,
      Module A (projCoherentSheafTruncatedGlobalSections 𝒜 (twist ℱ) 0)]
    (twistedGlobalSectionsFunctor : RingedSpace.Coh (Proj 𝒜).toRingedSpace ⥤ GrModfg)
    (hglobalSectionsFunctor_obj : ∀ ℱ : RingedSpace.Coh (Proj 𝒜).toRingedSpace,
      forgetGradedModule.obj (twistedGlobalSectionsFunctor.obj ℱ) ≅
        ModuleCat.of A (projCoherentSheafTruncatedGlobalSections 𝒜 (twist ℱ) 0))
    (descendedAssociatedSheafFunctor : irrelevant.isoModSerre.Localization ⥤
      RingedSpace.Coh (Proj 𝒜).toRingedSpace)
    (hdesc : irrelevant.isoModSerre.Q ⋙ descendedAssociatedSheafFunctor ≅
      associatedSheafFunctor)
    [descendedAssociatedSheafFunctor.IsEquivalence] :
    Nonempty (descendedAssociatedSheafFunctor.inv ≅
      twistedGlobalSectionsFunctor ⋙ irrelevant.isoModSerre.Q) := sorry

end AlgebraicGeometry
