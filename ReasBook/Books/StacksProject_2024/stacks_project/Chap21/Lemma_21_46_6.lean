import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Shift.Localization
import Mathlib.CategoryTheory.Shift.Quotient
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.Subcategory
import StacksProject_2024.stacks_project.Chap15.Lemma_15_58_3
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategory
import StacksProject_2024.stacks_project.Chap21.Definition_21_17_13_Core
import StacksProject_2024.stacks_project.Chap21.Definition_21_46_1_Core

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open RingedSite.Hom (ModuleCat ModuleDerived)
open scoped RingedSite.Hom
open scoped RingedSiteDerivedTensor

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable {X : RingedSite.{u, v}}

variable [Abelian (ringedSiteModuleCategory X.siteTopology X.structureSheaf)]
variable [CategoryWithHomology (ringedSiteModuleCategory X.siteTopology X.structureSheaf)]
variable [MonoidalCategory (ringedSiteModuleCategory X.siteTopology X.structureSheaf)]
variable [MonoidalCategory (DerivedCategory (ringedSiteModuleCategory X.siteTopology X.structureSheaf))]
variable [SymmetricCategory (ringedSiteModuleCategory X.siteTopology X.structureSheaf)]
variable [MonoidalPreadditive (ringedSiteModuleCategory X.siteTopology X.structureSheaf)]
variable [HasCountableCoproducts (ringedSiteModuleCategory X.siteTopology X.structureSheaf)]
variable [HasColimits (ringedSiteModuleCategory X.siteTopology X.structureSheaf)]
variable [(curriedTensor (ringedSiteModuleCategory X.siteTopology X.structureSheaf)).Additive]
variable [∀ M : ringedSiteModuleCategory X.siteTopology X.structureSheaf,
  ((curriedTensor (ringedSiteModuleCategory X.siteTopology X.structureSheaf)).obj M).Additive]
variable [∀ (K L : CochainComplex (ringedSiteModuleCategory X.siteTopology X.structureSheaf) ℤ),
  CochainComplex.HasMapBifunctor K L
    (curriedTensor (ringedSiteModuleCategory X.siteTopology X.structureSheaf))]
variable [∀ G₁ G₂ : GradedObject ℤ (ringedSiteModuleCategory X.siteTopology X.structureSheaf),
  GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (ringedSiteModuleCategory X.siteTopology X.structureSheaf),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (ringedSiteModuleCategory X.siteTopology X.structureSheaf),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ :
  GradedObject ℤ (ringedSiteModuleCategory X.siteTopology X.structureSheaf),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ M : ringedSiteModuleCategory X.siteTopology X.structureSheaf,
  PreservesColimit
    (Functor.empty.{0} (ringedSiteModuleCategory X.siteTopology X.structureSheaf))
    ((curriedTensor (ringedSiteModuleCategory X.siteTopology X.structureSheaf)).obj M)]
variable [∀ M : ringedSiteModuleCategory X.siteTopology X.structureSheaf,
  PreservesColimit
    (Functor.empty.{0} (ringedSiteModuleCategory X.siteTopology X.structureSheaf))
    ((curriedTensor (ringedSiteModuleCategory X.siteTopology X.structureSheaf)).flip.obj M)]

variable {a b : ℤ}

local notation "Mod" => ringedSiteModuleCategory X.siteTopology X.structureSheaf
local notation "DMod" => DerivedCategory Mod
local notation "H" => DerivedCategory.homologyFunctor Mod
local notation "single0" => DerivedCategory.singleFunctor Mod (0 : ℤ)
local notation "Complexes" => CochainComplex Mod ℤ
local notation "KMod" => HomotopyCategory Mod (ComplexShape.up ℤ)
local notation "Q" => (HomotopyCategory.quotient Mod (ComplexShape.up ℤ) : Complexes ⥤ KMod)
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)
local notation "Qis" => HomotopyCategory.quasiIso Mod (ComplexShape.up ℤ)

local instance : MonoidalCategory KMod := inferInstance

local instance : (Q : Complexes ⥤ KMod).Monoidal := inferInstance

local instance :
    Functor.Monoidal
      (DerivedCategory.Qh :
        HomotopyCategory Mod (ComplexShape.up ℤ) ⥤
          DMod) :=
  inferInstance

/-- Helper for Lemma 21.46.6: the composite quotient functor
`DerivedCategory.Q : Complexes ⥤ D(\mathcal O_X)` carries the ambient monoidal structure. -/
private noncomputable instance quotientFunctorMonoidal :
    (DerivedCategory.Q : Complexes ⥤ DMod).Monoidal := by
  change (((Q : Complexes ⥤ KMod) ⋙ (Qh : KMod ⥤ DMod))).Monoidal
  infer_instance

/-- Helper for Lemma 21.46.6: the fixed-right representative in `KMod` chosen from a derived
right tensor factor. -/
private noncomputable abbrev tensorRightRepresentative
    (L : DMod) :
    KMod :=
  (Q : Complexes ⥤ KMod).obj ((DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L)

/-- Helper for Lemma 21.46.6: passing the chosen right representative through `Qh` recovers the
original derived object. -/
private noncomputable def tensorRightRepresentativeIso
    (L : DMod) :
    (((Qh : KMod ⥤ DMod)).obj (tensorRightRepresentative L)) ≅ L :=
  (DerivedCategory.quotientCompQhIso Mod).app
      ((DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L) ≪≫
    (DerivedCategory.Q : Complexes ⥤ DMod).objObjPreimageIso L

/-- Helper for Lemma 21.46.6: a monoidal functor commutes with right tensoring by a fixed
object. -/
private noncomputable def tensorRightCommIso
    {A : Type*} [Category A] [MonoidalCategory A]
    {B : Type*} [Category B] [MonoidalCategory B]
    (F : A ⥤ B) [Functor.Monoidal F] (Y : A) :
    F ⋙ (tensoringRight B).obj (F.obj Y) ≅ (tensoringRight A).obj Y ⋙ F :=
  NatIso.ofComponents
    (fun X ↦ Functor.Monoidal.μIso F X Y)
    (fun {_ _} f ↦ by
      -- Proof comment: the componentwise compatibility is exactly tensorator naturality in the
      -- varying left factor.
      simpa using Functor.Monoidal.μIso_hom_natural_right (F := F) _ f)

/-- Helper for Lemma 21.46.6: before applying `Qh`, the source tensor functor is computed in
`KMod` by tensoring with a chosen representative of the right factor. -/
private noncomputable abbrev derivedTensorSourceLiftFunctor
    (L : DMod) :
    KMod ⥤ KMod :=
  let L' := (DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L
  CategoryTheory.Quotient.lift
      (homotopic Mod (ComplexShape.up ℤ))
      ((((curriedTensor Mod).map₂CochainComplex).flip.obj L') ⋙ Q)
      (fun _ _ _ _ ⟨h⟩ ↦
        HomotopyCategory.eq_of_homotopy _ _
          (HomologicalComplex.mapBifunctorMapHomotopy₁ h
            (𝟙 L')
            (curriedTensor Mod)
            (ComplexShape.up ℤ)))

/-- Helper for Lemma 21.46.6: on represented morphisms, the quotient lift computes the source
tensor map by tensoring with the chosen right representative in complexes. -/
private theorem derivedTensorSourceLiftFunctor_map_quotientMap
    (L : DMod) {A B : Complexes} (f : A ⟶ B) :
    (derivedTensorSourceLiftFunctor L).map ((Q : Complexes ⥤ KMod).map f) =
      ((((curriedTensor Mod).map₂CochainComplex).flip.obj
        ((DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L)) ⋙ Q).map f := by
  let L' := (DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L
  -- Proof comment: this is the defining map formula of the quotient lift before whiskering by
  -- `Qh`.
  simpa [L', derivedTensorSourceLiftFunctor] using
    (CategoryTheory.Quotient.lift_map_functor_map
      (r := homotopic Mod (ComplexShape.up ℤ))
      (F := ((((curriedTensor Mod).map₂CochainComplex).flip.obj L') ⋙ Q))
      (H := fun _ _ _ _ ⟨h⟩ ↦
        HomotopyCategory.eq_of_homotopy _ _
          (HomologicalComplex.mapBifunctorMapHomotopy₁ h
            (𝟙 L')
            (curriedTensor Mod)
            (ComplexShape.up ℤ)))
      ((Q : Complexes ⥤ KMod).map f))

/-- Helper for Lemma 21.46.6: in `KMod`, right tensoring by the chosen representative agrees
with the quotient-side source tensor lift. -/
private theorem tensoringRightRepresentativeIsoDerivedTensorSourceLiftFunctor_hom_naturality_repr
    (L : DMod) {A B : Complexes} (f : A ⟶ B) :
    ((tensoringRight KMod).obj (tensorRightRepresentative L)).map ((Q : Complexes ⥤ KMod).map f) ≫
        (Functor.Monoidal.μIso Q ((Q : Complexes ⥤ KMod).obj A)
          ((DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L)).hom =
      (Functor.Monoidal.μIso Q ((Q : Complexes ⥤ KMod).obj B)
        ((DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L)).hom ≫
          (derivedTensorSourceLiftFunctor L).map ((Q : Complexes ⥤ KMod).map f) := by
  let L' := (DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L
  -- Proof comment: after rewriting the quotient-lift map, this is the right-factor naturality
  -- of the monoidal structure on `Q`.
  rw [derivedTensorSourceLiftFunctor_map_quotientMap (L := L) f]
  simpa [L', tensorRightRepresentative, Category.assoc] using
    Functor.Monoidal.μIso_hom_natural_right (F := Q) L' f

/-- Helper for Lemma 21.46.6: the represented comparison in `KMod` descends to a natural
isomorphism. -/
private noncomputable def tensoringRightRepresentativeIsoDerivedTensorSourceLiftFunctor
    (L : DMod) :
    (tensoringRight KMod).obj (tensorRightRepresentative L) ≅ derivedTensorSourceLiftFunctor L := by
  let L' := (DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L
  refine NatIso.ofComponents
    (fun A ↦ ?_)
    (fun {A B} f ↦ ?_)
  · -- Proof comment: on represented objects, the comparison is just the monoidal tensorator of
    -- `Q`.
    simpa [L', derivedTensorSourceLiftFunctor, tensorRightRepresentative] using
      (Functor.Monoidal.μIso Q A.as L')
  · -- Proof comment: quotient induction reduces arbitrary morphisms in `KMod` to represented
    -- chain maps.
    refine Quotient.inductionOn f (fun f ↦ ?_)
    simpa using
      tensoringRightRepresentativeIsoDerivedTensorSourceLiftFunctor_hom_naturality_repr
        (L := L) f

/-- Helper for Lemma 21.46.6: after whiskering by `Qh`, the quotient-side comparison reaches the
actual source tensor functor. -/
private noncomputable def tensoringRightRepresentativeIsoDerivedTensorSourceFunctor
    (L : DMod) :
    (tensoringRight KMod).obj (tensorRightRepresentative L) ⋙ Qh ≅ derivedTensorSourceFunctor L := by
  -- Proof comment: whiskering transfers the cheaper `KMod` comparison to the DMod-valued source
  -- tensor functor.
  simpa [derivedTensorSourceFunctor, derivedTensorSourceLiftFunctor] using
    (Functor.isoWhiskerRight
      (tensoringRightRepresentativeIsoDerivedTensorSourceLiftFunctor L)
      (Qh : KMod ⥤ DMod))

/-- Helper for Lemma 21.46.6: ambient right tensoring on `D(\mathcal O)` identifies with the
source tensor functor before left deriving. -/
private noncomputable def tensoringRightObjIsoDerivedTensorSourceFunctor
    (L : DMod) :
    Qh ⋙ (tensoringRight DMod).obj L ≅ derivedTensorSourceFunctor L :=
  -- Route correction: compare the ambient tensor owner to the quotient-side source tensor functor
  -- first, and only then pass to the left-derived uniqueness statement.
  Functor.isoWhiskerLeft Qh (((tensoringRight DMod).mapIso (tensorRightRepresentativeIso L)).symm) ≪≫
    tensorRightCommIso Qh (tensorRightRepresentative L) ≪≫
      tensoringRightRepresentativeIsoDerivedTensorSourceFunctor L

/-- Helper for Lemma 21.46.6: the ambient right-tensor functor is already a left derived functor
of the source tensor functor. -/
private noncomputable instance tensoringRightObj_isLeftDerivedFunctor
    (L : DMod) :
    ((tensoringRight DMod).obj L).IsLeftDerivedFunctor
      (tensoringRightObjIsoDerivedTensorSourceFunctor L).hom
      Qis :=
  Functor.isLeftDerivedFunctor_of_inverts
    Qis
    ((tensoringRight DMod).obj L)
    (tensoringRightObjIsoDerivedTensorSourceFunctor L)

/-- Helper for Lemma 21.46.6: uniqueness of left derived functors identifies ambient right
tensoring with the source-facing derived tensor functor. -/
private noncomputable def tensoringRightObjIsoDerivedTensorProduct
    (L : DMod) :
    (tensoringRight DMod).obj L ≅ derivedTensorProduct L :=
  let F : KMod ⥤ DMod := derivedTensorSourceFunctor L
  -- Proof comment: both functors are left derived functors of the same source functor, so
  -- `Functor.leftDerivedNatIso` gives the comparison directly.
  (show (tensoringRight DMod).obj L ≅ derivedTensorProduct L from
    Functor.leftDerivedNatIso
      ((tensoringRight DMod).obj L)
      (derivedTensorProduct L)
      (tensoringRightObjIsoDerivedTensorSourceFunctor L).hom
      (derivedTensorProductCounit L)
      Qis
      (Iso.refl F))

/-- Helper for Lemma 21.46.6: the exact owner `- ⊗^L \mathcal F[0]` is triangulated-exact. -/
private noncomputable instance derivedTensorProductSingleIsTriangulated
    (ℱ : Mod) :
    (derivedTensorProduct ((single0).obj ℱ)).IsTriangulated := by
  -- Proof comment: the triangulated structure is inherited from the canonical total left derived
  -- functor.
  change ((derivedTensorSourceFunctor ((single0).obj ℱ)).totalLeftDerived Qh Qis).IsTriangulated
  infer_instance

/-- Helper for Lemma 21.46.6: the ambient tensor test object with `\mathcal F[0]` agrees with the
canonical derived tensor owner `- ⊗^L \mathcal F[0]`. -/
private noncomputable def ambientTensorSingleIsoDerivedTensorProduct
    (K : DMod) (ℱ : Mod) :
    (K ⊗ (single0).obj ℱ) ≅ ((derivedTensorProduct ((single0).obj ℱ)).obj K) :=
  (tensoringRightObjIsoDerivedTensorProduct ((single0).obj ℱ)).app K

/-- Helper for Lemma 21.46.6: translating the test degree by `n` matches translating the
tor-amplitude interval by `n`. -/
private theorem not_mem_Icc_add_iff (i a b n : ℤ) :
    i + n ∉ Set.Icc (a + n) (b + n) ↔ i ∉ Set.Icc a b := by
  simp [Set.mem_Icc]

/-- Helper for Lemma 21.46.6: the shifted degree `i - n` lies outside `[a, b]` exactly when `i`
lies outside the translated interval `[a + n, b + n]`. -/
private theorem not_mem_Icc_sub_iff (i a b n : ℤ) :
    i - n ∉ Set.Icc a b ↔ i ∉ Set.Icc (a + n) (b + n) := by
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (not_mem_Icc_add_iff (i := i - n) (a := a) (b := b) (n := n))

/-- Helper for Lemma 21.46.6: tor-amplitude gives vanishing on the canonical exact owner
`- ⊗^L \mathcal F[0]` after transporting across the ambient-to-derived comparison. -/
private theorem isZeroHomologyDerivedTensorOfHasTorAmplitudeIn
    {K : DMod} {p q i : ℤ} (hK : HasTorAmplitudeIn K p q)
    (ℱ : Mod) (hi : i ∉ Set.Icc p q) :
    IsZero ((H i).obj ((derivedTensorProduct ((single0).obj ℱ)).obj K)) := by
  -- Proof comment: first use the source-facing tor-amplitude hypothesis on the ambient tensor
  -- test object, then transport that vanishing across the comparison isomorphism.
  have hz : IsZero ((H i).obj (K ⊗ (single0).obj ℱ)) :=
    hK ℱ i hi
  simpa using hz.of_iso (ambientTensorSingleIsoDerivedTensorProduct K ℱ)

-- Proof sketch: map the distinguished triangle through the exact owner
-- `derivedTensorProduct ((single0).obj ℱ)`, then use the third homology exact segment. The
-- vanishing of the first two vertices comes from the tor-amplitude hypotheses after translating
-- the degree on the first vertex by `+1`.
/-- Lemma 21.46.6 (1): in a distinguished triangle in `D(\mathcal O_X)`, if the first term has
tor-amplitude in `[a + 1, b + 1]` and the second term has tor-amplitude in `[a, b]`, then the
third term has tor-amplitude in `[a, b]`. -/
@[stacks 08G2]
theorem hasTorAmplitudeIn_obj₃_of_distinguishedTriangle
    (T : Triangle (ModuleDerived X)) (hT : T ∈ distTriang (ModuleDerived X))
    (h₁ : HasTorAmplitudeIn T.obj₁ (a + 1) (b + 1))
    (h₂ : HasTorAmplitudeIn T.obj₂ a b) :
    HasTorAmplitudeIn T.obj₃ a b := by
  intro ℱ i hi
  let G : DMod ⥤ DMod := derivedTensorProduct ((single0).obj ℱ)
  let S : Triangle DMod := G.mapTriangle.obj T
  have hS : S ∈ distTriang DMod := by
    -- Proof comment: the exact owner preserves distinguished triangles.
    simpa [G, S] using G.map_distinguished T hT
  have hi' : i + 1 ∉ Set.Icc (a + 1) (b + 1) := by
    -- Proof comment: clause `(1)` uses the first hypothesis in degree `i + 1`.
    simpa [Set.mem_Icc] using hi
  have h₁' : IsZero ((H (i + 1)).obj S.obj₁) := by
    -- Proof comment: transport the first tor-amplitude hypothesis to the exact owner.
    simpa [G, S] using
      isZeroHomologyDerivedTensorOfHasTorAmplitudeIn h₁ ℱ hi'
  have h₂' : IsZero ((H i).obj S.obj₂) := by
    -- Proof comment: the middle vertex vanishes in degree `i` by the second hypothesis.
    simpa [G, S] using
      isZeroHomologyDerivedTensorOfHasTorAmplitudeIn h₂ ℱ hi
  -- Proof comment: the third exact segment kills the remaining homology object once the adjacent
  -- maps are zero.
  refine (hS.homology_exact₃ i (i + 1) (by simp)).isZero_X₂ ?_ ?_
  · simpa [S] using h₂'.eq_of_src ((H i).map S.mor₂) 0
  · simpa [S] using h₁'.eq_of_tgt (hS.δ i (i + 1) (by simp)) 0

-- Proof sketch: map the distinguished triangle through the exact owner
-- `derivedTensorProduct ((single0).obj ℱ)` and use the middle homology exact segment. The outer
-- vertices vanish directly in degree `i`.
/-- Lemma 21.46.6 (2): in a distinguished triangle in `D(\mathcal O_X)`, if the first and third
terms have tor-amplitude in `[a, b]`, then the second term has tor-amplitude in `[a, b]`. -/
@[stacks 08G2]
theorem hasTorAmplitudeIn_obj₂_of_distinguishedTriangle
    (T : Triangle (ModuleDerived X)) (hT : T ∈ distTriang (ModuleDerived X))
    (h₁ : HasTorAmplitudeIn T.obj₁ a b)
    (h₃ : HasTorAmplitudeIn T.obj₃ a b) :
    HasTorAmplitudeIn T.obj₂ a b := by
  intro ℱ i hi
  let G : DMod ⥤ DMod := derivedTensorProduct ((single0).obj ℱ)
  let S : Triangle DMod := G.mapTriangle.obj T
  have hS : S ∈ distTriang DMod := by
    -- Proof comment: the exact owner preserves distinguished triangles.
    simpa [G, S] using G.map_distinguished T hT
  have h₁' : IsZero ((H i).obj S.obj₁) := by
    -- Proof comment: transport the first tor-amplitude hypothesis to the exact owner.
    simpa [G, S] using
      isZeroHomologyDerivedTensorOfHasTorAmplitudeIn h₁ ℱ hi
  have h₃' : IsZero ((H i).obj S.obj₃) := by
    -- Proof comment: transport the third tor-amplitude hypothesis to the exact owner.
    simpa [G, S] using
      isZeroHomologyDerivedTensorOfHasTorAmplitudeIn h₃ ℱ hi
  -- Proof comment: the middle exact segment kills the homology of the second vertex.
  refine (hS.homology_exact₂ i).isZero_X₂ ?_ ?_
  · simpa [S] using h₁'.eq_of_src ((H i).map S.mor₁) 0
  · simpa [S] using h₃'.eq_of_tgt ((H i).map S.mor₂) 0

-- Proof sketch: map the distinguished triangle through the exact owner
-- `derivedTensorProduct ((single0).obj ℱ)` and use the first homology exact segment. The third
-- hypothesis is read in degree `j - 1`, matching the connecting morphism.
/-- Lemma 21.46.6 (3): in a distinguished triangle in `D(\mathcal O_X)`, if the second term has
tor-amplitude in `[a + 1, b + 1]` and the third term has tor-amplitude in `[a, b]`, then the
first term has tor-amplitude in `[a + 1, b + 1]`. -/
@[stacks 08G2]
theorem hasTorAmplitudeIn_obj₁_of_distinguishedTriangle
    (T : Triangle (ModuleDerived X)) (hT : T ∈ distTriang (ModuleDerived X))
    (h₂ : HasTorAmplitudeIn T.obj₂ (a + 1) (b + 1))
    (h₃ : HasTorAmplitudeIn T.obj₃ a b) :
    HasTorAmplitudeIn T.obj₁ (a + 1) (b + 1) := by
  intro ℱ j hj
  let G : DMod ⥤ DMod := derivedTensorProduct ((single0).obj ℱ)
  let S : Triangle DMod := G.mapTriangle.obj T
  have hS : S ∈ distTriang DMod := by
    -- Proof comment: the exact owner preserves distinguished triangles.
    simpa [G, S] using G.map_distinguished T hT
  have hj' : j - 1 ∉ Set.Icc a b := by
    -- Proof comment: clause `(3)` reads the third tor-amplitude hypothesis in degree `j - 1`.
    exact (not_mem_Icc_sub_iff j a b 1).1 <| by
      simpa using hj
  have h₂' : IsZero ((H j).obj S.obj₂) := by
    -- Proof comment: transport the second tor-amplitude hypothesis to the exact owner.
    simpa [G, S] using
      isZeroHomologyDerivedTensorOfHasTorAmplitudeIn h₂ ℱ hj
  have h₃' : IsZero ((H (j - 1)).obj S.obj₃) := by
    -- Proof comment: transport the third tor-amplitude hypothesis to the exact owner.
    simpa [G, S] using
      isZeroHomologyDerivedTensorOfHasTorAmplitudeIn h₃ ℱ hj'
  -- Proof comment: the first exact segment now forces vanishing on the first vertex.
  refine (hS.homology_exact₁ (j - 1) j (by simp)).isZero_X₂ ?_ ?_
  · simpa [S] using h₃'.eq_of_src (hS.δ (j - 1) j (by simp)) 0
  · simpa [S] using h₂'.eq_of_tgt ((H j).map S.mor₁) 0

end

end SheafOfModules.RingedSite
