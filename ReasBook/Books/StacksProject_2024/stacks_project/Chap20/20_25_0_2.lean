import StacksProject_2024.stacks_project.Chap20.«20_9_0_1»
import StacksProject_2024.stacks_project.Chap20.«20_9_0_2»
import StacksProject_2024.stacks_project.Chap20.«20_25_3_2»
import StacksProject_2024.stacks_project.Chap20.OpensInstances

open CategoryTheory Opposite TopologicalSpace ComplexShape HomologicalComplex₂
open CategoryTheory.Limits
open AlgebraicTopology

noncomputable section

universe w v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
variable [HasFiniteProducts C]

/-- Internal owner-level bridge: a morphism of indexed families induces the corresponding natural
transformation between the associated Čech complex functors. -/
private noncomputable abbrev cechComplexRefinementNatTrans {ι κ : Type w} (U : ι → C)
    (V : κ → C)
    (σ : (FormalCoproduct.mk ι U : FormalCoproduct C) ⟶ (FormalCoproduct.mk κ V : FormalCoproduct C)) :=
  Functor.whiskerRight
    (Functor.whiskerLeft (FormalCoproduct.evalOp C A)
      ((Functor.whiskeringLeft SimplexCategory ((FormalCoproduct C)ᵒᵖ) A).map
        ((FormalCoproduct.cechFunctor.map σ).rightOp)))
    (alternatingCofaceMapComplex A)

end CategoryTheory

variable {X : TopCat.{u}} {I J : Type v}

local notation "PresheafCochain" => CochainComplex (X.Presheaf AddCommGrpCat) ℤ

/- Domain-style sampling for 20.25.0.2:
- primary domain: refinement functoriality of Čech complexes and the induced maps on rowwise total
  Čech double complexes of presheaf complexes;
- sampled owner declarations:
  `rowCechFunctor`,
  `doubleCechFunctor`,
  `totalCechFunctor`,
  `NatTrans.mapHomologicalComplex`,
  `(inferInstance : HasFiniteProducts (Opens X))`;
- best owner abstraction: the chapter owner declarations `rowCechFunctor 𝒰` and
  `doubleCechFunctor 𝒰`, together with the total-owner `totalCechFunctor 𝒰`, already package the
  extended rowwise Čech construction canonically, so this file should build only the refinement
  maps on top of that owner layer;
- primitive data: an indexed family of opens `𝒰`, a refinement witness `IsRefinement 𝒰 𝒱 t`, and
  a coefficient complex `F`;
- derived API: the refinement natural transformations on Čech complexes and on the induced
  rowwise double-complex functors, together with the induced map on total Čech functors and its
  evaluation at `F`.

Source/core/bridge triage:
- `source-facing`: `cechTotalRefinementMap`;
- `core/canonical`: `rowCechFunctor`, `doubleCechFunctor`, `totalCechFunctor`,
  `NatTrans.mapHomologicalComplex`, the canonical finite-product instance on `Opens X`, and the
  imported chapter refinement owner `IsRefinement`;
- `bridge/view`: `refinementHom`, `cechRefinementNatTrans`, and the induced
  `doubleCechNatTrans` and `totalCechNatTrans`.

The former version rebuilt the rowwise double-complex owner locally. The refined file reuses the
chapter owners `rowCechFunctor`, `doubleCechFunctor`, and `totalCechFunctor` from `20_25_3_2`
and keeps only the refinement maps as the local bridge layer, with the generic Čech-complex
refinement bridge factored through the same owner-level whiskering pattern used elsewhere in the
project.
-/

/-- The natural transformation of Čech complexes induced by a refinement of indexed open covers. -/
noncomputable abbrev cechRefinementNatTrans (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I)
    (ht : IsRefinement 𝒰 𝒱 t) :
    (cechComplexFunctor 𝒰 :
      X.Presheaf AddCommGrpCat ⥤ CochainComplex AddCommGrpCat ℕ) ⟶
      (cechComplexFunctor 𝒱 :
        X.Presheaf AddCommGrpCat ⥤ CochainComplex AddCommGrpCat ℕ) :=
  CategoryTheory.cechComplexRefinementNatTrans 𝒱 𝒰 (refinementHom 𝒰 𝒱 t ht)

/-- The refinement natural transformation on the extended rowwise Čech complex functors. -/
noncomputable abbrev rowCechNatTrans
    (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I) (ht : IsRefinement 𝒰 𝒱 t) :
    rowCechFunctor 𝒰 ⟶ rowCechFunctor 𝒱 :=
  Functor.whiskerRight (cechRefinementNatTrans 𝒰 𝒱 t ht)
    (embeddingUpNat.extendFunctor AddCommGrpCat)

/-- The natural transformation of rowwise Čech double-complex functors induced by a refinement of
indexed open covers. -/
noncomputable abbrev doubleCechNatTrans
    (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I) (ht : IsRefinement 𝒰 𝒱 t) :
    doubleCechFunctor 𝒰 ⟶ doubleCechFunctor 𝒱 :=
  NatTrans.mapHomologicalComplex (rowCechNatTrans 𝒰 𝒱 t ht) (up ℤ)

/-- The refinement natural transformation on total Čech complex functors. -/
noncomputable abbrev totalCechNatTrans
    (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I) (ht : IsRefinement 𝒰 𝒱 t) :
    totalCechFunctor 𝒰 ⟶ totalCechFunctor 𝒱 :=
  Functor.whiskerRight (doubleCechNatTrans 𝒰 𝒱 t ht)
    (totalFunctor AddCommGrpCat.{max u v} (up ℤ) (up ℤ) (up ℤ))

/-- 20.25.0.2: if `𝒱` is a refinement of `𝒰` via `t : J → I`, then `t` induces the canonical map
`T_t : Tot(Čech(𝒰, 𝓕)) ⟶ Tot(Čech(𝒱, 𝓕))` on the associated total Čech complexes of a cochain
complex `𝓕` of presheaves of abelian groups. -/
@[stacks 08BM]
noncomputable def cechTotalRefinementMap (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I)
    (ht : IsRefinement 𝒰 𝒱 t) (F : PresheafCochain) :
    (totalCechFunctor 𝒰).obj F ⟶ (totalCechFunctor 𝒱).obj F :=
  (totalCechNatTrans 𝒰 𝒱 t ht).app F

/-- On each coefficient complex `F`, the textbook map `T_t` is the totalization of the
refinement morphism of Čech double complexes. -/
@[simp]
theorem cechTotalRefinementMap_eq_total_map (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I)
    (ht : IsRefinement 𝒰 𝒱 t) (F : PresheafCochain) :
    cechTotalRefinementMap 𝒰 𝒱 t ht F =
      HomologicalComplex₂.total.map ((doubleCechNatTrans 𝒰 𝒱 t ht).app F) (up ℤ) :=
  rfl
