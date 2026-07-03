import Mathlib
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_15_1 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The underlying continuous map of a morphism of ringed spaces. -/
abbrev baseMap {X Y : RingedSpace.{u}} (f : X ⟶ Y) : X.carrier ⟶ Y.carrier :=
  f.hom.base

/-- The lattice of open subsets of a ringed space has a top element. -/
instance opensOrderTop (X : RingedSpace.{u}) : OrderTop (Opens X.carrier) where
  top := ⟨Set.univ, isOpen_univ⟩
  le_top := by
    intro U x hx
    trivial

/-- The category of open subsets of a ringed space has finite products given by intersections. -/
instance opensHasFiniteProducts (X : RingedSpace.{u}) : HasFiniteProducts (Opens X.carrier) := by
  letI : HasFiniteLimits (Opens X.carrier) :=
    hasFiniteLimits_of_semilatticeInf_orderTop
  infer_instance

/-- The open subset `f^{-1}(V)` of `X` attached to an open subset `V ⊆ Y`. -/
abbrev preimageOpen {X Y : RingedSpace.{u}} (f : X ⟶ Y) (V : Opens Y.carrier) :
    Opens X.carrier :=
  Opens.comap (baseMap f).hom V

/-- The structure sheaf of a ringed space, regarded as a sheaf with values in `RingCat`. -/
abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
    (CategoryTheory.forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The direct-image functor on `\mathcal O_X`-modules attached to a morphism of ringed spaces. -/
noncomputable abbrev modulePushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    SheafOfModules (ringedSpaceRingCatSheaf X) ⥤
      SheafOfModules (ringedSpaceRingCatSheaf Y) :=
  SheafOfModules.pushforward
    ((CategoryTheory.sheafCompose (Opens.grothendieckTopology Y)
        (CategoryTheory.forget₂ CommRingCat RingCat.{u})).map
      (show Y.sheaf ⟶
          (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf from
        ⟨f.hom.c⟩))

/-- The underlying additive sheaf of an `\mathcal O_X`-module on a ringed space. -/
abbrev moduleUnderlyingSheaf (X : RingedSpace.{u}) :
    SheafOfModules (ringedSpaceRingCatSheaf X) ⥤
      Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X)

/-- The degree-`p` global sheaf cohomology of an `\mathcal O_X`-module on a ringed space. -/
abbrev moduleGlobalCohomology {X : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) (p : ℕ) :
    AddCommGrpCat.{u} :=
  ((moduleUnderlyingSheaf X).obj ℱ).H' p (⊤ : Opens X.carrier)

/-- The underlying additive presheaf of an `\mathcal O_X`-module. -/
abbrev moduleUnderlyingAdditivePresheaf (X : RingedSpace.{u}) :
    SheafOfModules (ringedSpaceRingCatSheaf X) ⥤ X.carrier.Presheaf AddCommGrpCat.{u} :=
  moduleUnderlyingSheaf X ⋙
    sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}

/-- The degree-`p` Čech cohomology group of an `\mathcal O_X`-module with respect to a family of
opens `\mathcal U`. -/
abbrev moduleCechCohomology
    {X : RingedSpace.{u}} {ι : Type u} (𝒰 : ι → Opens X.carrier)
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) (p : ℕ) : AddCommGrpCat.{u} :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).obj
    ((cechComplexFunctor 𝒰).obj ((moduleUnderlyingAdditivePresheaf X).obj ℱ))

/-- A cover `\mathcal U` of `X` refines the pulled-back cover `f^{-1}\mathcal V` if each `U_i`
is contained in the preimage of some `V_j`. -/
def IsPreimageRefinement
    {X Y : RingedSpace.{u}} {I J : Type u} (f : X ⟶ Y)
    (𝒰 : I → Opens X.carrier) (𝒱 : J → Opens Y.carrier) : Prop :=
  ∃ c : I → J, ∀ i : I, 𝒰 i ≤ preimageOpen f (𝒱 (c i))

/-- The map on sheaf cohomology induced by an `f`-map of module sheaves, in the library-facing
form with codomain `H^p(Y, f_* \mathcal F)`. -/
abbrev moduleSheafCohomologyMapToPushforward
    {X Y : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Y)
    {𝒢 : SheafOfModules (ringedSpaceRingCatSheaf Y)}
    {ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)}
    (φ : 𝒢 ⟶ (modulePushforward f).obj ℱ) (p : ℕ) :
    moduleGlobalCohomology 𝒢 p ⟶ moduleGlobalCohomology ((modulePushforward f).obj ℱ) p :=
  ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Y.carrier) p).map
      ((moduleUnderlyingSheaf Y).map φ)).app (op (⊤ : Opens Y.carrier))

-- Proof sketch: choose a function `c : I → J` witnessing that `\mathcal U` refines
-- `f^{-1}\mathcal V`, and use it together with `φ` to define the usual morphism of Čech complexes
-- from `\check C^\bullet(\mathcal V, \mathcal G)` to `\check C^\bullet(\mathcal U, \mathcal F)`.
-- Compare the two Čech-to-cohomology morphisms by passing to injective resolutions and the
-- double-complex diagram from the source text; the outer boundary gives the stated commutative
-- square on cohomology groups.
/-- Lemma 20.15.1: if `f : X ⟶ Y` is a morphism of ringed spaces, `φ : \mathcal G ⟶ f_* \mathcal F`
is an `f`-map, `\mathcal U` and `\mathcal V` are open coverings of `X` and `Y`, and
`\mathcal U` refines `f^{-1}\mathcal V`, then for every degree `p` there exists a morphism
`γ : \check H^p(\mathcal V, \mathcal G) ⟶ \check H^p(\mathcal U, \mathcal F)` making the Čech
comparison square commute with the canonical cohomology map
`H^p(Y, \mathcal G) ⟶ H^p(Y, f_* \mathcal F)`. This is the cohomology-level form of the
commutative derived diagram in the textbook statement. -/
theorem exists_cech_cohomology_square_of_f_map_and_refinement
    {X Y : RingedSpace.{u}} {I J : Type u}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Y)
    (𝒢 : SheafOfModules (ringedSpaceRingCatSheaf Y))
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X))
    (φ : 𝒢 ⟶ (modulePushforward f).obj ℱ)
    (𝒰 : I → Opens X.carrier) (h𝒰 : iSup 𝒰 = ⊤)
    (𝒱 : J → Opens Y.carrier) (h𝒱 : iSup 𝒱 = ⊤)
    (href : IsPreimageRefinement f 𝒰 𝒱) (p : ℕ) :
    ∃ γ : moduleCechCohomology 𝒱 𝒢 p ⟶ moduleCechCohomology 𝒰 ℱ p,
      ∃ α𝒰 :
          moduleCechCohomology 𝒰 ℱ p ⟶
            moduleGlobalCohomology ((modulePushforward f).obj ℱ) p,
        ∃ α𝒱 :
            moduleCechCohomology 𝒱 𝒢 p ⟶ moduleGlobalCohomology 𝒢 p,
          α𝒱 ≫ moduleSheafCohomologyMapToPushforward f φ p = γ ≫ α𝒰 := sorry

end AlgebraicGeometry.RingedSpace
