import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.IsConnected
import StacksProject_2024.Chap13.Definition_13_14_10
import StacksProject_2024.Chap13.Lemma_13_30_1
import StacksProject_2024.Chap13.Situation_13_15_1
import StacksProject_2024.Chap21.Lemma_21_39_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 21.39.5:
- primary domain: connected-indexed colimits of constant diagrams and the derived adjunction
  obtained from `colim ⊣ const` for the projection to a point;
- sampled owner declarations:
  `Limits.isColimitConstCocone`,
  `Limits.colimConstAdj`,
  `Limits.IsColimit.isIso_colimMap_ι`,
  `CategoryTheory.isConnected_of_hasInitial`,
  `CategoryTheory.isConnected_of_hasTerminal`;
- best owner abstraction:
  `source-facing`: the underived and derived counit-isomorphism statements of Lemma 21.39.5;
  `core/canonical`: the connected-category owner `IsConnected C`, the constant-diagram functor,
    the colimit adjunction, and the canonical derived adjunction/counit owners;
  `bridge/view`: the initial/final-object hypothesis from the source text, used only to produce
    the connectedness instance needed by the owner-level theorem.

Primitive-vs-derived split:
- primitive data: the indexing category `C`, the abelian target `A`, the constant-diagram functor,
  the colimit functor, the connectedness hypothesis, and the left-derived existence hypothesis;
- derived API: the underived counit-isomorphism theorem, the canonical derived adjunction and
  derived-counit owners `CategoryTheory.Adjunction.derived` and
  `CategoryTheory.Adjunction.derivedε`, and the specialization from initial/final objects to
  connectedness.
-/

private theorem isConnected_of_hasInitial_or_hasTerminal
    (hC : Nonempty (Limits.HasInitial C) ∨ Nonempty (Limits.HasTerminal C)) :
    IsConnected C := by
  cases hC with
  | inl hC =>
      letI : Limits.HasInitial C := hC.some
      exact isConnected_of_hasInitial C
  | inr hC =>
      letI : Limits.HasTerminal C := hC.some
      exact isConnected_of_hasTerminal C

section Underived

variable {A : Type w} [Category A]
variable [HasColimitsOfShape Cᵒᵖ A]

local notation "PresheafCat" => Cᵒᵖ ⥤ A
local notation "ConstDiag" => (Functor.const (Cᵒᵖ) : A ⥤ PresheafCat)

-- Proof sketch: for a connected indexing category, mathlib's owner-level constant-diagram API
-- identifies the chosen colimit cocone of the constant diagram with the obvious cocone
-- `Limits.constCocone`, and the counit component is the corresponding comparison isomorphism.
instance categoryOverPointLowerShriekCounit_isIso [IsConnected C] :
    IsIso
      ((Limits.colimConstAdj : (colim : PresheafCat ⥤ A) ⊣ ConstDiag).counit) := by
  let underivedCounit :
      ConstDiag ⋙ (colim : PresheafCat ⥤ A) ⟶ 𝟭 A :=
    (Limits.colimConstAdj : (colim : PresheafCat ⥤ A) ⊣ ConstDiag).counit
  change IsIso underivedCounit
  letI (X : A) :
      IsIso (underivedCounit.app X) := by
    let e :=
      (colimit.isColimit ((Functor.const (Cᵒᵖ)).obj X)).coconePointUniqueUpToIso
        (Limits.isColimitConstCocone (Cᵒᵖ) X)
    change IsIso e.hom
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- If the indexing category is connected, then the underived lower shriek for the projection to a
point has invertible counit `π⁻¹ ⋙ π! ⟶ 𝟭`. -/
theorem categoryOverPointLowerShriek_comp_inverseImage_counit_isIso
    [IsConnected C] :
    IsIso
      ((Limits.colimConstAdj : (colim : PresheafCat ⥤ A) ⊣ ConstDiag).counit) := by
  infer_instance

/-- If the indexing category has an initial or a final object, then the underived lower shriek for
the projection to a point has invertible counit `π⁻¹ ⋙ π! ⟶ 𝟭`. -/
theorem categoryOverPointLowerShriek_comp_inverseImage_counit_isIso_of_hasInitial_or_hasTerminal
    (hC : Nonempty (Limits.HasInitial C) ∨ Nonempty (Limits.HasTerminal C)) :
    IsIso
      ((Limits.colimConstAdj : (colim : PresheafCat ⥤ A) ⊣ ConstDiag).counit) := by
  letI : IsConnected C := isConnected_of_hasInitial_or_hasTerminal hC
  infer_instance

end Underived

section Derived

variable {A : Type w} [Category A] [Abelian A] [HasDerivedCategory A]
variable [HasDerivedCategory (Cᵒᵖ ⥤ A)]
variable [HasColimitsOfShape Cᵒᵖ A]

local notation "PresheafCat" => Cᵒᵖ ⥤ A
local notation "ColimitToDerived" =>
  (categoryOverPointColimitToDerived C A :
    HomotopyCategory PresheafCat (up ℤ) ⥤ DerivedCategory A)
local notation "QPresheaf" => (DerivedCategory.Qh :
  HomotopyCategory PresheafCat (up ℤ) ⥤ DerivedCategory PresheafCat)
local notation "QA" => (DerivedCategory.Qh :
  HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)
local notation "QisPresheaf" => HomotopyCategory.quasiIso PresheafCat (up ℤ)
local notation "QisA" => HomotopyCategory.quasiIso A (up ℤ)
local notation "ConstDiag" => (Functor.const (Cᵒᵖ) : A ⥤ PresheafCat)
local notation "DerivedLowerShriek" =>
  (categoryOverPointDerivedColimit C A :
    DerivedCategory PresheafCat ⥤ DerivedCategory A)

/-- The constant-diagram inverse-image functor over a point is additive. -/
local instance constDiag_additive :
    ((Functor.const (Cᵒᵖ) : A ⥤ PresheafCat)).Additive where
  map_add := by
    -- The constant functor acts objectwise, so additivity reduces to the identity on components.
    intro X Y f g
    ext U
    rfl

/-- The inverse-image functor on derived categories for the projection from a category over a
point. -/
abbrev categoryOverPointDerivedInverseImage :
    DerivedCategory A ⥤ DerivedCategory PresheafCat :=
  (Functor.const (Cᵒᵖ) : A ⥤ PresheafCat).mapDerivedCategory

local notation "DerivedInverseImage" =>
  (categoryOverPointDerivedInverseImage :
    DerivedCategory A ⥤ DerivedCategory PresheafCat)

omit [HasColimitsOfShape Cᵒᵖ A] in
private theorem constDiagMapDerivedCategory_isRightDerivedFunctor :
    Functor.IsRightDerivedFunctor
      ((Functor.const (Cᵒᵖ) : A ⥤ PresheafCat).mapDerivedCategory)
      ((Functor.const (Cᵒᵖ) : A ⥤ PresheafCat).mapDerivedCategoryFactorsh.inv)
      QisA := by
  simpa [mapHomotopyCategoryToDerived] using
    (Functor.isRightDerivedFunctor_of_inverts
      QisA
      ((Functor.const (Cᵒᵖ) : A ⥤ PresheafCat).mapDerivedCategory)
      (Functor.const (Cᵒᵖ) : A ⥤ PresheafCat).mapDerivedCategoryFactorsh)

attribute [local instance] constDiagMapDerivedCategory_isRightDerivedFunctor

variable
  [Functor.HasLeftDerivedFunctor
    (categoryOverPointColimitToDerived C A :
      HomotopyCategory (Cᵒᵖ ⥤ A) (up ℤ) ⥤ DerivedCategory A)
    (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (up ℤ))]

private theorem categoryOverPointDerivedLowerShriek_isLeftDerivedFunctor :
    Functor.IsLeftDerivedFunctor
      (categoryOverPointDerivedColimit C A :
        DerivedCategory PresheafCat ⥤ DerivedCategory A)
      (Functor.totalLeftDerivedCounit ColimitToDerived QPresheaf QisPresheaf)
      QisPresheaf := by
  simpa [categoryOverPointDerivedColimit, categoryOverPointColimitToDerived] using
    (show Functor.IsLeftDerivedFunctor
        (Functor.totalLeftDerived ColimitToDerived QPresheaf QisPresheaf)
        (Functor.totalLeftDerivedCounit ColimitToDerived QPresheaf QisPresheaf)
        QisPresheaf from inferInstance)

attribute [local instance] categoryOverPointDerivedLowerShriek_isLeftDerivedFunctor

private theorem categoryOverPointDerivedInverseImage_comp_lowerShriek_isRightDerivedFunctor :
    Functor.IsRightDerivedFunctor
      (DerivedInverseImage ⋙ DerivedLowerShriek)
      (Functor.whiskerRight
          ((Functor.const (Cᵒᵖ) : A ⥤ PresheafCat).mapDerivedCategoryFactorsh.inv)
          DerivedLowerShriek ≫
        (Functor.associator
          QA
          ((Functor.const (Cᵒᵖ) : A ⥤ PresheafCat).mapDerivedCategory)
          DerivedLowerShriek).hom)
      QisA := by
  -- The displayed comparison is an isomorphism from `QA ⋙ (π⁻¹ ⋙ Lπ_!)` to the homotopy-level
  -- source functor, so the generic "inverts quasi-isomorphisms" owner gives the right-derived
  -- structure directly.
  let e :
      QA ⋙ (DerivedInverseImage ⋙ DerivedLowerShriek) ≅
        (mapHomotopyCategoryToDerived
          (Functor.const (Cᵒᵖ) : A ⥤ PresheafCat)) ⋙ DerivedLowerShriek :=
    (asIso
      (Functor.whiskerRight
          ((Functor.const (Cᵒᵖ) : A ⥤ PresheafCat).mapDerivedCategoryFactorsh.inv)
          DerivedLowerShriek ≫
        (Functor.associator
          QA
          ((Functor.const (Cᵒᵖ) : A ⥤ PresheafCat).mapDerivedCategory)
          DerivedLowerShriek).hom)).symm
  simpa [mapHomotopyCategoryToDerived] using
    (Functor.isRightDerivedFunctor_of_inverts
      QisA
      (DerivedInverseImage ⋙ DerivedLowerShriek)
      e)

attribute [local instance]
  categoryOverPointDerivedInverseImage_comp_lowerShriek_isRightDerivedFunctor

/-- The canonical derived counit `π⁻¹ ⋙ Lπ![C, A] ⟶ 𝟭` for the projection from a category over a
point. -/
noncomputable abbrev categoryOverPointDerivedLowerShriekCounit :
    DerivedInverseImage ⋙ Lπ![C, A] ⟶ 𝟭 (DerivedCategory A) :=
  Adjunction.derivedε
    ((Limits.colimConstAdj : (colim : PresheafCat ⥤ A) ⊣ ConstDiag).mapHomotopyCategory)
    QisA
    (Functor.totalLeftDerivedCounit ColimitToDerived QPresheaf QisPresheaf)
    ((Functor.const (Cᵒᵖ) : A ⥤ PresheafCat).mapDerivedCategoryFactorsh.inv)

local notation "DerivedCounit" =>
  (categoryOverPointDerivedLowerShriekCounit :
    DerivedInverseImage ⋙ Lπ![C, A] ⟶ 𝟭 (DerivedCategory A))

instance categoryOverPointDerivedLowerShriekCounit_isIso [IsConnected C] :
    IsIso DerivedCounit := by
  let derivedCounit := DerivedCounit
  change IsIso derivedCounit
  sorry

/-- Lemma 21.39.5, owner-level connected form: in the category-over-a-point situation of Example
21.39.1, if `C` is connected, then inverse image followed by the derived lower shriek is
naturally isomorphic to the identity on `D(A)`, equivalently the counit
`π⁻¹ ⋙ Lπ![C, A] ⟶ 𝟭` is an isomorphism. The source-text initial/final-object assumption is
recovered by the specialization theorem below. Specializing `A` to `AddCommGrpCat` and to
`ModuleCat B` recovers the textbook statements on `DerivedCategory AddCommGrpCat` and
`DerivedCategory (ModuleCat B)`. -/
@[stacks 08Q7]
theorem categoryOverPointDerivedLowerShriek_comp_inverseImage_counit_isIso
    [IsConnected C] :
    IsIso DerivedCounit := by
  infer_instance

/-- Lemma 21.39.5 in the source-text initial/final-object form. -/
@[stacks 08Q7]
theorem categoryOverPointDerivedLowerShriek_comp_inverseImage_counit_isIso_of_hasInitial_or_hasTerminal
    (hC : Nonempty (Limits.HasInitial C) ∨ Nonempty (Limits.HasTerminal C)) :
    IsIso DerivedCounit := by
  letI : IsConnected C := isConnected_of_hasInitial_or_hasTerminal hC
  infer_instance

end Derived

end

end CategoryTheory
