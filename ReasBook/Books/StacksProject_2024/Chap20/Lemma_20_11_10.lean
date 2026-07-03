import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The lattice of open subsets of a ringed space has a top element. -/
instance opensOrderTop (X : RingedSpace.{u}) : OrderTop (Opens X.carrier) where
  top := ⟨Set.univ, isOpen_univ⟩
  le_top := by
    intro U x hx
    trivial

/-- The structure sheaf of a ringed space, viewed as a sheaf with values in `RingCat`. -/
/-- The category of `\mathcal O_X`-modules on a ringed space. -/
/-- The structure-sheaf morphism `\mathcal O_Y ⟶ f_*\mathcal O_X` attached to a morphism of
ringed spaces, after forgetting commutativity. -/
noncomputable abbrev pushforwardStructureSheafHom
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.ringCatSheaf Y) ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj (RingedSpace.ringCatSheaf X) :=
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).map
    (show Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf from
      ⟨f.hom.c⟩)

/-- The pushforward functor on `\mathcal O`-modules induced by a morphism of ringed spaces. -/
noncomputable abbrev modulePushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.Modules X) ⥤ (RingedSpace.Modules Y) :=
  SheafOfModules.pushforward (pushforwardStructureSheafHom f)

/-- The underlying abelian sheaf of an `\mathcal O_X`-module. -/
abbrev moduleUnderlyingSheaf {X : RingedSpace.{u}} (ℱ : (RingedSpace.Modules X)) :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ

/-- The underlying additive presheaf of an `\mathcal O_X`-module. -/
abbrev moduleUnderlyingPresheaf {X : RingedSpace.{u}} (ℱ : (RingedSpace.Modules X)) :
    X.carrier.Presheaf AddCommGrpCat.{u} :=
  (moduleUnderlyingSheaf ℱ).1

/-- The lattice of opens of a ringed space has finite limits. -/
instance opensHasFiniteLimits (X : RingedSpace.{u}) :
    HasFiniteLimits (Opens X.carrier) :=
  hasFiniteLimits_of_semilatticeInf_orderTop

/-- The category of opens of a ringed space has finite products. -/
instance opensHasFiniteProducts (X : RingedSpace.{u}) :
    HasFiniteProducts (Opens X.carrier) :=
  inferInstance

-- Proof sketch: pull the cover `𝒱` of `V` back along `f` to a cover of `f⁻¹(V)`. The underlying
-- additive presheaf of `f_* \mathcal I` evaluates on each Čech intersection as
-- `\mathcal I(f^{-1}(V_{j_0 \dots j_p}))`, so its Čech complex identifies with the Čech complex of
-- `\mathcal I` on the pulled-back cover. Then apply injective Čech-acyclicity.
/-- Lemma 20.11.10 (1): if `f : X ⟶ Y` is a morphism of ringed spaces and `\mathcal I` is an
injective `\mathcal O_X`-module, then the positive Čech cohomology of `f_* \mathcal I` vanishes
for every open covering of every open subset `V ⊆ Y`. -/
theorem cech_cohomology_isZero_modulePushforward_of_injective
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (ℐ : (RingedSpace.Modules X)) (hℐ : Injective ℐ)
    {V : Opens Y.carrier} {ι : Type u} (𝒱 : ι → Opens Y.carrier) (h𝒱 : iSup 𝒱 = V)
    (p : ℕ) (hp : 0 < p) :
    IsZero
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).obj
        ((cechComplexFunctor 𝒱).obj
          (moduleUnderlyingPresheaf ((modulePushforward f).obj ℐ)))) := sorry

-- Proof sketch: the first part gives vanishing of higher Čech cohomology for every open covering
-- of every open subset of `Y`. Apply the comparison from Čech cohomology to sheaf cohomology to
-- deduce the vanishing of `H^p(V, f_* \mathcal I)` for all `p > 0`.
/-- Lemma 20.11.10 (2): if `f : X ⟶ Y` is a morphism of ringed spaces and `\mathcal I` is an
injective `\mathcal O_X`-module, then `H^p(V, f_* \mathcal I) = 0` for every open subset
`V ⊆ Y` and every `p > 0`; equivalently, `f_* \mathcal I` is right acyclic for `\Gamma(V, -)`. -/
theorem higherCohomology_isZero_modulePushforward_of_injective
    {X Y : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Y) (ℐ : (RingedSpace.Modules X)) (hℐ : Injective ℐ)
    (V : Opens Y.carrier) (p : ℕ) (hp : 0 < p) :
    IsZero ((moduleUnderlyingSheaf ((modulePushforward f).obj ℐ)).H' p V) := sorry

end AlgebraicGeometry.RingedSpace
