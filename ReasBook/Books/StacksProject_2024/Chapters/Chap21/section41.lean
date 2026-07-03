import Mathlib
import Mathlib.CategoryTheory.Triangulated.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_21_41_1 (from Chap21) -/
open CategoryTheory Opposite
open SheafOfModules

noncomputable section

universe u

namespace CategoryTheory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

private abbrev simplicialRing
    (A : SimplicialObject (Sheaf J CommRingCat.{u})) (Δ : SimplexCategoryᵒᵖ) :
    Sheaf J RingCat.{u} :=
  ringSheaf J (A.obj Δ)

private abbrev simplicialRingMap
    (A : SimplicialObject (Sheaf J CommRingCat.{u}))
    {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') :
    simplicialRing A Δ ⟶ simplicialRing A Δ' :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).map (A.map θ)

private noncomputable abbrev simplicialSheafModuleIdIso
    (A : SimplicialObject (Sheaf J CommRingCat.{u})) (Δ : SimplexCategoryᵒᵖ) :
    SheafOfModules.restrictScalars (simplicialRingMap A (𝟙 Δ)) ≅
      𝟭 (SheafOfModules (simplicialRing A Δ)) :=
  SheafOfModules.pushforwardCongr
      (by
        simpa [simplicialRingMap] using
          congrArg ((sheafCompose J (forget₂ CommRingCat RingCat)).map) (A.map_id Δ)) ≪≫
    SheafOfModules.pushforwardId (simplicialRing A Δ)

private noncomputable abbrev simplicialSheafModuleCompIso
    (A : SimplicialObject (Sheaf J CommRingCat.{u}))
    {Δ₁ Δ₂ Δ₃ : SimplexCategoryᵒᵖ} (θ : Δ₁ ⟶ Δ₂) (η : Δ₂ ⟶ Δ₃) :
    SheafOfModules.restrictScalars (simplicialRingMap A η) ⋙
      SheafOfModules.restrictScalars (simplicialRingMap A θ) ≅
      SheafOfModules.restrictScalars (simplicialRingMap A (θ ≫ η)) :=
  SheafOfModules.pushforwardComp
      (φ := simplicialRingMap A θ) (ψ := simplicialRingMap A η) ≪≫
    SheafOfModules.pushforwardCongr
      (by
        simpa [simplicialRingMap] using
          congrArg ((sheafCompose J (forget₂ CommRingCat RingCat)).map) (A.map_comp θ η))

/-- Definition 21.41.1: for a site `\mathcal C` and a simplicial sheaf of rings
`\mathcal A_\bullet`, a simplicial `\mathcal A_\bullet`-module is a family of sheaves of
modules on `\mathcal C`, one in each simplicial degree, together with simplicial transition maps
that are linear over the corresponding structure-ring maps and satisfy the simplicial identities
through the canonical restriction-of-scalars comparison isomorphisms. This is the degreewise form
of a sheaf of modules over the sheaf of rings on `\Delta \times \mathcal C` associated to
`\mathcal A_\bullet`. -/
structure SimplicialSheafOfModules
    (A : SimplicialObject (Sheaf J CommRingCat.{u})) where
  /-- The sheaf of modules in a fixed simplicial degree. -/
  obj : ∀ Δ : SimplexCategoryᵒᵖ, SheafOfModules.{u} (simplicialRing A Δ)
  /-- The semilinear transition morphism attached to a simplicial operator. -/
  map : ∀ {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ'),
    obj Δ ⟶ (SheafOfModules.restrictScalars (simplicialRingMap A θ)).obj (obj Δ')
  /-- The transition map attached to the identity simplicial operator is the identity. -/
  map_id : ∀ Δ : SimplexCategoryᵒᵖ,
    map (𝟙 Δ) = (simplicialSheafModuleIdIso A Δ).inv.app (obj Δ)
  /-- The transition map attached to a composite simplicial operator is the composite of the
  corresponding semilinear transition morphisms. -/
  map_comp : ∀ {Δ₁ Δ₂ Δ₃ : SimplexCategoryᵒᵖ} (θ : Δ₁ ⟶ Δ₂) (η : Δ₂ ⟶ Δ₃),
    map (θ ≫ η) =
      map θ ≫
        (SheafOfModules.restrictScalars (simplicialRingMap A θ)).map (map η) ≫
        (simplicialSheafModuleCompIso A θ η).hom.app (obj Δ₃)

namespace SimplicialSheafOfModules

variable {A : SimplicialObject (Sheaf J CommRingCat.{u})}

/-- A simplicial sheaf of modules can be evaluated at a simplicial degree to recover its sheaf of
modules in that degree. -/
instance : CoeFun (SimplicialSheafOfModules A) (fun _ ↦
    ∀ Δ : SimplexCategoryᵒᵖ, SheafOfModules.{u} (simplicialRing A Δ)) where
  coe M := M.obj

end SimplicialSheafOfModules

end CategoryTheory

/-! ### Lemma_21_41_2 (from Chap21) -/
open CategoryTheory

noncomputable section

universe u v w w'

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {DA : Type w} [Category.{w} DA]
variable {DC : Type w'} [Category.{w'} DC]

variable
  (sourceUnit : SimplicialObject (Sheaf J CommRingCat.{max u v}) → DA)
variable
  (targetAsSourceModule :
    {A B : SimplicialObject (Sheaf J CommRingCat.{max u v})} → (A ⟶ B) → DA)
variable
  (structureMap :
    {A B : SimplicialObject (Sheaf J CommRingCat.{max u v})} → (α : A ⟶ B) →
      sourceUnit A ⟶ targetAsSourceModule α)
variable
  (derivedLowerShriek :
    SimplicialObject (Sheaf J CommRingCat.{max u v}) → DA ⥤ DC)
variable
  (derivedTensorWithTarget :
    {A B : SimplicialObject (Sheaf J CommRingCat.{max u v})} → (α : A ⟶ B) → DA ⥤ DA)

-- Proof sketch: resolve `K` by a bounded-above complex of termwise flat simplicial
-- `\mathcal A_\bullet`-modules so that derived tensoring with `\mathcal B_\bullet` becomes the
-- ordinary tensor product. Compute the cohomology sheaves of both sides fiberwise using
-- Lemmas `21.40.1` and `21.40.2`, and then apply the category-over-a-point comparison of
-- Lemma `21.39.12` on each fiber.
/-- Lemma 21.41.2: let `\mathcal C` be a site and let
`\alpha : \mathcal A_\bullet \to \mathcal B_\bullet` be a morphism of simplicial sheaves of
commutative rings on `\mathcal C`. In the abstract interface used here, `sourceUnit A` is a chosen
model of `\mathcal A_\bullet` in `D(\mathcal A_\bullet)`, `targetAsSourceModule α` is a chosen
model of `\mathcal B_\bullet` viewed as an `\mathcal A_\bullet`-module, `structureMap α` realizes
the map induced by `\alpha`, `derivedLowerShriek A` is a chosen model of `L\pi_! :
D(\mathcal A_\bullet) \to D(\mathcal C)`, and `derivedTensorWithTarget α` is the endofunctor
`K \mapsto K \otimes_{\mathcal A_\bullet}^{\mathbf L} \mathcal B_\bullet`. If
`L\pi_!(\mathcal A_\bullet) \to L\pi_!(\mathcal B_\bullet)` is an isomorphism, then for every
`K ∈ D(\mathcal A_\bullet)` the objects `L\pi_!(K)` and
`L\pi_!(K \otimes_{\mathcal A_\bullet}^{\mathbf L} \mathcal B_\bullet)` are canonically
isomorphic in `D(\mathcal C)`. -/
theorem derivedLowerShriek_isomorphic_after_tensor_simplicialSheafChange
    {A B : SimplicialObject (Sheaf J CommRingCat.{max u v})} (α : A ⟶ B)
    (hα : IsIso ((derivedLowerShriek A).map (structureMap α))) (K : DA) :
    IsIsomorphic
      ((derivedLowerShriek A).obj K)
      ((derivedLowerShriek A).obj ((derivedTensorWithTarget α).obj K)) := sorry

end

end CategoryTheory

/-! ### Remark_21_41_3 (from Chap21) -/
open CategoryTheory

noncomputable section

universe u v w x y z

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {DA : Type w} [Category.{w} DA]
variable {Dπ𝒪 : Type x} [Category.{x} Dπ𝒪]
variable {D𝒪 : Type y} [Category.{y} D𝒪]
variable {DAb : Type z} [Category.{z} DAb]

variable
  (augmentationQuasiIso :
    {A 𝒪 : SimplicialObject (Sheaf J CommRingCat.{max u v})} → (A ⟶ 𝒪) → Prop)
variable
  (derivedLowerShriekToAb :
    SimplicialObject (Sheaf J CommRingCat.{max u v}) → DA ⥤ DAb)
variable
  (derivedTensorAlongAugmentation :
    {A 𝒪 : SimplicialObject (Sheaf J CommRingCat.{max u v})} → (A ⟶ 𝒪) → DA ⥤ Dπ𝒪)
variable
  (projectionDerivedLowerShriek :
    SimplicialObject (Sheaf J CommRingCat.{max u v}) → Dπ𝒪 ⥤ D𝒪)
variable (targetForget : D𝒪 ⥤ DAb)
variable
  (forgetComparison :
    {A 𝒪 : SimplicialObject (Sheaf J CommRingCat.{max u v})} →
      (ε : A ⟶ 𝒪) → augmentationQuasiIso ε →
        ∀ K : DA,
          IsIsomorphic
            ((derivedLowerShriekToAb A).obj K)
            (targetForget.obj
              ((projectionDerivedLowerShriek 𝒪).obj
                ((derivedTensorAlongAugmentation ε).obj K))))

/-- The `D(\mathcal O)`-valued derived lower shriek attached to an augmentation
`ε : \mathcal A_\bullet \to \mathcal O`, defined by first derived tensoring with `\mathcal O` and
then applying the target-side derived lower shriek `L\pi_!`. -/
abbrev augmentationDerivedLowerShriek
    {A 𝒪 : SimplicialObject (Sheaf J CommRingCat.{max u v})} (ε : A ⟶ 𝒪) :
    DA ⥤ D𝒪 :=
  derivedTensorAlongAugmentation ε ⋙ projectionDerivedLowerShriek 𝒪

-- Proof sketch: this is exactly the canonical comparison supplied by Lemma `21.41.2`, rewritten
-- using the definition of `augmentationDerivedLowerShriek` as tensoring with `\mathcal O` followed
-- by the target-side `L\pi_!` from Remark `21.38.6`.
/-- Remark 21.41.3: if an augmentation `ε : \mathcal A_\bullet \to \mathcal O` induces a
quasi-isomorphism `s(\mathcal A_\bullet) \to \mathcal O`, then for every
`K ∈ D(\mathcal A_\bullet)` the underlying abelian derived lower shriek `L\pi_!(K)` is
canonically isomorphic to the underlying abelian sheaf of the `D(\mathcal O)`-valued object
obtained by first tensoring `K` with `\mathcal O` over `\mathcal A_\bullet` and then applying the
target-side derived lower shriek. This is the functorial identification that gives `L\pi_!(K)` its
`\mathcal O`-module structure. -/
theorem augmentationDerivedLowerShriek_forget_obj_iso
    {A 𝒪 : SimplicialObject (Sheaf J CommRingCat.{max u v})} (ε : A ⟶ 𝒪)
    (hε : augmentationQuasiIso ε) (K : DA) :
    IsIsomorphic
      ((derivedLowerShriekToAb A).obj K)
      (targetForget.obj
        ((augmentationDerivedLowerShriek
            derivedTensorAlongAugmentation projectionDerivedLowerShriek ε).obj K)) := sorry

section Triangulated

variable [HasShift DA ℤ] [HasShift Dπ𝒪 ℤ] [HasShift D𝒪 ℤ]
variable [Limits.HasZeroObject DA] [Limits.HasZeroObject Dπ𝒪] [Limits.HasZeroObject D𝒪]
variable [Preadditive DA] [Preadditive Dπ𝒪] [Preadditive D𝒪]
variable [∀ n : ℤ, (shiftFunctor DA n).Additive]
variable [∀ n : ℤ, (shiftFunctor Dπ𝒪 n).Additive]
variable [∀ n : ℤ, (shiftFunctor D𝒪 n).Additive]
variable [Pretriangulated DA] [Pretriangulated Dπ𝒪] [Pretriangulated D𝒪]

/-- If the derived tensor functor along the augmentation and the target-side derived lower shriek
commute with triangulated shifts, then their composite does as well. -/
instance augmentationDerivedLowerShriek_commShift
    {A 𝒪 : SimplicialObject (Sheaf J CommRingCat.{max u v})} (ε : A ⟶ 𝒪)
    [(derivedTensorAlongAugmentation ε).CommShift ℤ]
    [(projectionDerivedLowerShriek 𝒪).CommShift ℤ] :
    (augmentationDerivedLowerShriek
        derivedTensorAlongAugmentation projectionDerivedLowerShriek ε).CommShift ℤ :=
  Functor.CommShift.comp
    (derivedTensorAlongAugmentation ε)
    (projectionDerivedLowerShriek 𝒪)

-- Proof sketch: the functor is the composite of the derived tensor functor along the augmentation
-- with the target-side derived lower shriek. Exact functors of triangulated categories are closed
-- under composition, so the composite is triangulated once both factors are.
/-- The augmentation-derived lower shriek is exact in the triangulated sense whenever both of its
factor functors are exact. -/
theorem augmentationDerivedLowerShriek_isTriangulated
    {A 𝒪 : SimplicialObject (Sheaf J CommRingCat.{max u v})} (ε : A ⟶ 𝒪)
    [(derivedTensorAlongAugmentation ε).CommShift ℤ]
    [(projectionDerivedLowerShriek 𝒪).CommShift ℤ]
    [(derivedTensorAlongAugmentation ε).IsTriangulated]
    [(projectionDerivedLowerShriek 𝒪).IsTriangulated] :
    (augmentationDerivedLowerShriek
      derivedTensorAlongAugmentation projectionDerivedLowerShriek ε).IsTriangulated := sorry

end Triangulated

end

end CategoryTheory
