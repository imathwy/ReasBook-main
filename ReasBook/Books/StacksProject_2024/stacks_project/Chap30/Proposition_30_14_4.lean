import StacksProject_2024.Chap30.Lemma_30_14_2
import StacksProject_2024.Chap12.Lemma_12_10_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped DirectSum

noncomputable section

universe u v w wv

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` surfaced the categorical equivalence API
`Functor.IsEquivalence` / `Functor.inv` and the Serre-quotient owner
`ObjectProperty.isoModSerre.Q`. Local Chapter 30 precedent provides the `Proj 𝒜` owner and
`projCoherentSheafTruncatedGlobalSections`, but the current project does not yet expose a
concrete category of finite graded `A`-modules, the associated sheaf functor on `Proj(A)`, or the
twisted-global-sections functor as canonical declarations. The source-facing statements therefore
take those functors as explicit parameters while using the canonical Serre quotient and
`RingedSpace.Coh (Proj 𝒜).toRingedSpace` as the categorical targets. -/

/-- Proposition 30.14.4 (1): let `A` be a graded ring with `A₀` Noetherian and generated over
`A₀` by finitely many degree-one elements, and set `X = Proj(A)`. For a chosen category
`GrModfg` of finitely generated graded `A`-modules, a Serre subcategory `torsion` of torsion
objects, and the associated-sheaf functor `M ↦ \widetilde M`, any descended functor from the
Serre quotient
`Mod_A^{fg} / Mod_{A,torsion}^{fg}` to `Coh(\mathcal O_X)` is an equivalence. The hypotheses
`hdesc` and `hglobalSectionsFunctor_obj` record, respectively, that the functor is induced by
`M ↦ \widetilde M` and that the chosen quasi-inverse has underlying modules
`\bigoplus_{n ≥ 0} Γ(X, \mathcal F(n))`. -/
@[stacks 0BXD]
theorem projAssociatedSheafFunctor_serreQuotient_isEquivalence
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    [IsNoetherianRing (𝒜 0)]
    (hgenerated : ∃ s : Finset A,
      Algebra.adjoin (𝒜 0) (s : Set A) = ⊤ ∧ ∀ x ∈ s, x ∈ 𝒜 1)
    (GrModfg : Type w) [Category.{wv} GrModfg] [Abelian GrModfg]
    (torsion : ObjectProperty GrModfg) [torsion.IsSerreClass]
    (forgetGradedModule : GrModfg ⥤ ModuleCat.{u} A)
    (associatedSheafFunctor : GrModfg ⥤ RingedSpace.Coh (Proj 𝒜).toRingedSpace)
    (twist : RingedSpace.Coh (Proj 𝒜).toRingedSpace → ℤ → (Proj 𝒜).Modules)
    [∀ ℱ : RingedSpace.Coh (Proj 𝒜).toRingedSpace,
      Module A (projCoherentSheafTruncatedGlobalSections 𝒜 (twist ℱ) 0)]
    (twistedGlobalSectionsFunctor : RingedSpace.Coh (Proj 𝒜).toRingedSpace ⥤ GrModfg)
    (hglobalSectionsFunctor_obj : ∀ ℱ : RingedSpace.Coh (Proj 𝒜).toRingedSpace,
      forgetGradedModule.obj (twistedGlobalSectionsFunctor.obj ℱ) ≅
        ModuleCat.of A (projCoherentSheafTruncatedGlobalSections 𝒜 (twist ℱ) 0))
    (descendedAssociatedSheafFunctor : torsion.isoModSerre.Localization ⥤
      RingedSpace.Coh (Proj 𝒜).toRingedSpace)
    (hdesc : torsion.isoModSerre.Q ⋙ descendedAssociatedSheafFunctor ≅
      associatedSheafFunctor) :
    descendedAssociatedSheafFunctor.IsEquivalence := sorry

/-- Proposition 30.14.4 (2): under the equivalence of the Serre quotient with
`Coh(\mathcal O_{Proj(A)})`, the quasi-inverse is the functor
`\mathcal F ↦ \bigoplus_{n ≥ 0} Γ(Proj(A), \mathcal F(n))`, followed by the quotient functor to
`Mod_A^{fg} / Mod_{A,torsion}^{fg}`. -/
@[stacks 0BXD]
theorem projAssociatedSheafFunctor_serreQuotient_inverse_iso
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    [IsNoetherianRing (𝒜 0)]
    (hgenerated : ∃ s : Finset A,
      Algebra.adjoin (𝒜 0) (s : Set A) = ⊤ ∧ ∀ x ∈ s, x ∈ 𝒜 1)
    (GrModfg : Type w) [Category.{wv} GrModfg] [Abelian GrModfg]
    (torsion : ObjectProperty GrModfg) [torsion.IsSerreClass]
    (forgetGradedModule : GrModfg ⥤ ModuleCat.{u} A)
    (associatedSheafFunctor : GrModfg ⥤ RingedSpace.Coh (Proj 𝒜).toRingedSpace)
    (twist : RingedSpace.Coh (Proj 𝒜).toRingedSpace → ℤ → (Proj 𝒜).Modules)
    [∀ ℱ : RingedSpace.Coh (Proj 𝒜).toRingedSpace,
      Module A (projCoherentSheafTruncatedGlobalSections 𝒜 (twist ℱ) 0)]
    (twistedGlobalSectionsFunctor : RingedSpace.Coh (Proj 𝒜).toRingedSpace ⥤ GrModfg)
    (hglobalSectionsFunctor_obj : ∀ ℱ : RingedSpace.Coh (Proj 𝒜).toRingedSpace,
      forgetGradedModule.obj (twistedGlobalSectionsFunctor.obj ℱ) ≅
        ModuleCat.of A (projCoherentSheafTruncatedGlobalSections 𝒜 (twist ℱ) 0))
    (descendedAssociatedSheafFunctor : torsion.isoModSerre.Localization ⥤
      RingedSpace.Coh (Proj 𝒜).toRingedSpace)
    (hdesc : torsion.isoModSerre.Q ⋙ descendedAssociatedSheafFunctor ≅
      associatedSheafFunctor)
    [descendedAssociatedSheafFunctor.IsEquivalence] :
    Nonempty (descendedAssociatedSheafFunctor.inv ≅
      twistedGlobalSectionsFunctor ⋙ torsion.isoModSerre.Q) := sorry

end AlgebraicGeometry
