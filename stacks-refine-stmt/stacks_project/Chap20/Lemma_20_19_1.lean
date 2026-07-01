import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, viewed as a sheaf with values in `RingCat`. -/
private abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
    (CategoryTheory.forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The functor sending an `\mathcal O_X`-module to its degree-`q` cohomology on the open subset
`U`. -/
private noncomputable abbrev ringedSpaceModuleCohomologyAtOpenFunctor
    (X : RingedSpace.{u})
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (U : Opens X.carrier) (q : ℕ) :
    SheafOfModules (ringedSpaceRingCatSheaf X) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X) ⋙
    Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X.carrier) q ⋙
    (CategoryTheory.evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- The canonical morphism from the filtered colimit of the groups `H^q(U, \mathcal F_i)` to the
cohomology group `H^q(U, \operatorname{colim}_i \mathcal F_i)`. -/
noncomputable def ringedSpaceModuleCohomologyColimitComparison
    {X : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    {I : Type v} [SmallCategory I]
    (U : Opens X.carrier) (q : ℕ)
    (ℱ : I ⥤ SheafOfModules (ringedSpaceRingCatSheaf X))
    [HasColimit ℱ]
    [HasColimit (ℱ ⋙ ringedSpaceModuleCohomologyAtOpenFunctor X U q)] :
    colimit (ℱ ⋙ ringedSpaceModuleCohomologyAtOpenFunctor X U q) ⟶
      (ringedSpaceModuleCohomologyAtOpenFunctor X U q).obj (colimit ℱ) :=
  colimit.desc _ ((ringedSpaceModuleCohomologyAtOpenFunctor X U q).mapCocone (colimit.cocone ℱ))

-- Proof sketch: first prove the degree-zero statement for every compact open simultaneously, using
-- that filtered colimits commute with sections on compact opens in a prespectral space whose
-- compact opens are stable under binary intersections. Then choose functorial injective embeddings
-- of the diagram, use exactness of filtered colimits of abelian groups and the vanishing of higher
-- Čech cohomology for injectives on finite covers by compact opens, and conclude by induction on
-- `q`.
/-- Lemma 20.19.1: if the underlying topological space of a ringed space `X` has a basis of
quasi-compact opens and the intersection of any two quasi-compact opens is quasi-compact, then for
every filtered diagram `(\mathcal F_i)` of `\mathcal O_X`-modules, every quasi-compact open subset
`U`, and every `q \geq 0`, the canonical map
`colim_i H^q(U, \mathcal F_i) \to H^q(U, \operatorname{colim}_i \mathcal F_i)` is an
isomorphism. -/
theorem ringedSpaceModuleCohomologyColimitComparison_isIso_of_isCompact
    {X : RingedSpace.{u}}
    [PrespectralSpace X.carrier]
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (hinter : ∀ U V : Opens X.carrier, IsCompact (U : Set X.carrier) →
      IsCompact (V : Set X.carrier) → IsCompact ((U ⊓ V : Opens X.carrier) : Set X.carrier))
    (U : Opens X.carrier) (hU : IsCompact (U : Set X.carrier)) (q : ℕ)
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (ℱ : I ⥤ SheafOfModules (ringedSpaceRingCatSheaf X))
    [HasColimit ℱ]
    [HasColimit (ℱ ⋙ ringedSpaceModuleCohomologyAtOpenFunctor X U q)] :
    IsIso (ringedSpaceModuleCohomologyColimitComparison U q ℱ) := sorry

end AlgebraicGeometry.RingedSpace
