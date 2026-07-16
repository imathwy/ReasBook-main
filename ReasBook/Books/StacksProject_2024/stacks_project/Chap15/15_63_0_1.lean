import Mathlib
import StacksProject_2024.stacks_project.Chap15.Lemma_15_59_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape
open ModuleCat.MonoidalCategory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "KMod" => HomotopyCategory (ModuleCat R) (up ℤ)
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

variable (K L : DMod) (i j : ℤ)

open HomologicalComplex

/- Domain-style sampling for 15.63.0.1:
- primary domain: cohomology pairings in the derived category of `R`-modules;
- sampled owner declarations:
  `DerivedCategory.homologyFunctor`,
  `HomologicalComplex.ιTensorObj`,
  `ShortComplex.descHomology`,
  `derivedCategory_tensorObj_iso_derivedTensorProduct`,
  `Functor.Monoidal.μIso`;
- best owner abstraction: the source-facing product pairing belongs over the ambient monoidal
  tensor on `D(R)`, together with the tensor/derived-tensor bridge from Section `15.59`; the
  actual owner map is obtained by applying the chain-level cohomology pairing to the chosen
  cochain-complex preimages `DerivedCategory.Q.objPreimage K` and `DerivedCategory.Q.objPreimage L`
  and then transporting along the canonical comparison isomorphisms to `K ⊗[R]^L L`;
  comparison isomorphisms from `DerivedCategory.homologyFunctorFactors`,
  `DerivedCategory.Q.objObjPreimageIso`, `Functor.Monoidal.μIso`, and
  `derivedCategory_tensorObj_iso_derivedTensorProduct`;
- derived API: the direct product morphism
  `H^i(K) ⊗ H^j(L) ⟶ H^{i+j}(K ⊗[R]^L L)`. -/

private lemma cycleTensorToComponent_d_eq_zero (K L : Cpx) (i j : ℤ) :
    ((((K.iCycles i) ⊗ₘ (L.iCycles j) : K.cycles i ⊗ L.cycles j ⟶ K.X i ⊗ L.X j) ≫
      (HomologicalComplex.ιTensorObj K L i j (i + j) rfl :
        K.X i ⊗ L.X j ⟶ (K ⊗ L).X (i + j))) ≫
      (K ⊗ L).d (i + j) (i + j + 1) = 0) := sorry

/-- The chain-level product map on cohomology for cochain complexes of `R`-modules. -/
private noncomputable def cochainCohomologyProduct (K L : Cpx) (i j : ℤ) :
    K.homology i ⊗ L.homology j ⟶ (K ⊗ L).homology (i + j) :=
  let target : ModuleCat R := (K ⊗ L).homology (i + j)
  let f0 : K.cycles i ⊗ L.cycles j ⟶ target :=
    (K ⊗ L).liftCycles
      (((((K.iCycles i) ⊗ₘ (L.iCycles j) : K.cycles i ⊗ L.cycles j ⟶ K.X i ⊗ L.X j) ≫
        (HomologicalComplex.ιTensorObj K L i j (i + j) rfl :
          K.X i ⊗ L.X j ⟶ (K ⊗ L).X (i + j))) :
          K.cycles i ⊗ L.cycles j ⟶ (K ⊗ L).X (i + j)))
      (i + j + 1) (by simp)
      (cycleTensorToComponent_d_eq_zero K L i j) ≫
        (K ⊗ L).homologyπ (i + j)
  let g0 : L.cycles j ⟶ (ihom (K.cycles i)).obj target :=
    MonoidalClosed.curry f0
  let hg0 : (L.sc j).toCycles ≫ g0 = 0 := by
    sorry
  let g1 : L.homology j ⟶ (ihom (K.cycles i)).obj target :=
    (L.sc j).descHomology g0 hg0
  let f1 : K.cycles i ⊗ L.homology j ⟶ target :=
    MonoidalClosed.uncurry g1
  let g1' : K.cycles i ⟶ (ihom (L.homology j)).obj target :=
    MonoidalClosed.curry
      (((β_ (L.homology j) (K.cycles i)).hom :
          L.homology j ⊗ K.cycles i ⟶ K.cycles i ⊗ L.homology j) ≫ f1)
  let hg1' : (K.sc i).toCycles ≫ g1' = 0 := by
    sorry
  let g2 : K.homology i ⟶ (ihom (L.homology j)).obj target :=
    (K.sc i).descHomology g1' hg1'
  ((β_ (K.homology i) (L.homology j)).hom :
      K.homology i ⊗ L.homology j ⟶ L.homology j ⊗ K.homology i) ≫
    MonoidalClosed.uncurry g2

private noncomputable def preimageTensorIso (K L : DMod) :
    (DerivedCategory.Q : Cpx ⥤ DMod).obj
      (DerivedCategory.Q.objPreimage K ⊗ DerivedCategory.Q.objPreimage L) ≅ K ⊗[R]^L L :=
  let KQ : Cpx ⥤ KMod := HomotopyCategory.quotient (ModuleCat R) (up ℤ)
  let Qh : KMod ⥤ DMod := DerivedCategory.Qh
  ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app
      (DerivedCategory.Q.objPreimage K ⊗ DerivedCategory.Q.objPreimage L)).symm ≪≫
    Qh.mapIso
      ((Functor.Monoidal.μIso KQ
        (DerivedCategory.Q.objPreimage K)
        (DerivedCategory.Q.objPreimage L)).symm) ≪≫
    (Functor.Monoidal.μIso Qh
      (KQ.obj (DerivedCategory.Q.objPreimage K))
      (KQ.obj (DerivedCategory.Q.objPreimage L))).symm ≪≫
    (((DerivedCategory.quotientCompQhIso (ModuleCat R)).app
        (DerivedCategory.Q.objPreimage K)) ⊗ᵢ
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app
        (DerivedCategory.Q.objPreimage L))) ≪≫
    (DerivedCategory.Q.objObjPreimageIso K ⊗ᵢ DerivedCategory.Q.objObjPreimageIso L) ≪≫
      derivedCategory_tensorObj_iso_derivedTensorProduct K L

/-- 15.63.0.1: the canonical product morphism
`H^i(K^\bullet) \otimes_R H^j(L^\bullet) ⟶ H^{i + j}(K^\bullet \otimes_R^{\mathbf L} L^\bullet)`.
It is defined by applying the chain-level cohomology pairing to the chosen cochain-complex
preimages of `K` and `L` and then transporting along the canonical comparison isomorphisms to the
derived tensor product. -/
noncomputable def derivedCohomologyProduct :
    ((H i).obj K ⊗ (H j).obj L) ⟶ (H (i + j)).obj (K ⊗[R]^L L) :=
  let K' := DerivedCategory.Q.objPreimage K
  let L' := DerivedCategory.Q.objPreimage L
  ((((H i).mapIso (DerivedCategory.Q.objObjPreimageIso K)).inv ⊗ₘ
      ((H j).mapIso (DerivedCategory.Q.objObjPreimageIso L)).inv) ≫
    (((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).hom.app K') ⊗ₘ
      ((DerivedCategory.homologyFunctorFactors (ModuleCat R) j).hom.app L')) ≫
    cochainCohomologyProduct K' L' i j ≫
    ((DerivedCategory.homologyFunctorFactors (ModuleCat R) (i + j)).inv.app (K' ⊗ L')) ≫
      (H (i + j)).map (preimageTensorIso K L).hom)

end

end CategoryTheory
