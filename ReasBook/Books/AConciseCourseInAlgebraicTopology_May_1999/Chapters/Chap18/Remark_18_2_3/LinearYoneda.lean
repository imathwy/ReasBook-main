module

public import Mathlib.CategoryTheory.Abelian.Ext

public section

open CategoryTheory
open CategoryTheory.Linear
open HomologicalComplex

noncomputable section

universe u

namespace ChainComplex

/-- The cochain map induced by a chain map on `linearYonedaObj`; in each degree it acts by
precomposition with the corresponding chain-group map. -/
abbrev linearYonedaMap
    {X Y : ChainComplex (ModuleCat ℤ) ℕ} (φ : X ⟶ Y)
    (π : Type u) [AddCommGroup π] :
    Y.linearYonedaObj ℤ (ModuleCat.of ℤ π) ⟶ X.linearYonedaObj ℤ (ModuleCat.of ℤ π) :=
  (unopFunctor (ModuleCat ℤ) (ComplexShape.down ℕ)).map
    (((((linearYoneda ℤ (ModuleCat ℤ)).obj (ModuleCat.of ℤ π)).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).map φ).op)

/-- In degree `n`, `linearYonedaMap φ π` is precomposition by `φ.f n`. -/
@[simp] theorem linearYonedaMap_f
    {X Y : ChainComplex (ModuleCat ℤ) ℕ} (φ : X ⟶ Y)
    (π : Type u) [AddCommGroup π] (n : ℕ) :
    (linearYonedaMap φ π).f n = ModuleCat.ofHom (leftComp ℤ (ModuleCat.of ℤ π) (φ.f n)) :=
  rfl

@[simp] theorem linearYonedaMap_id
    (X : ChainComplex (ModuleCat ℤ) ℕ) (π : Type u) [AddCommGroup π] :
    linearYonedaMap (𝟙 X) π = 𝟙 (X.linearYonedaObj ℤ (ModuleCat.of ℤ π)) :=
  rfl

@[simp] theorem linearYonedaMap_comp
    {X Y Z : ChainComplex (ModuleCat ℤ) ℕ} (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    (π : Type u) [AddCommGroup π] :
    linearYonedaMap (φ ≫ ψ) π = linearYonedaMap ψ π ≫ linearYonedaMap φ π :=
  rfl

end ChainComplex
