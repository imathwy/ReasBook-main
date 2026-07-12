import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import StacksProject_2024.Chap13.Lemma_13_14_15

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe v₁ v₂ u₁ u₂

section

variable {Kₐ : Type u₁} {H : Type u₂}
variable [Category.{v₁} Kₐ]
variable [Category.{v₂} H]

-- Semantic recall hits: `Functor.leftDerivedNatTrans` constructs the derived transformation,
-- `Functor.leftDerivedNatTrans_fac` gives its defining counit compatibility, and
-- `Functor.ComputesLeftDerivedAt` is the Chapter `13` owner for objects on which the total left
-- derived functor is computed by the underived one.
variable (Wₐ : MorphismProperty Kₐ)
variable (tensorN tensorN' : Kₐ ⥤ H)
variable [tensorN.HasLeftDerivedFunctor Wₐ] [tensorN'.HasLeftDerivedFunctor Wₐ]
variable (oneTensorF : tensorN ⟶ tensorN')

/-- Transport an appwise isomorphism of a natural transformation across an isomorphism of source
objects. -/
private theorem natTrans_app_isIso_of_iso {C E : Type*} [Category C] [Category E]
    {F G : C ⥤ E} (τ : F ⟶ G) {X Y : C} (e : X ≅ Y) [IsIso (τ.app Y)] :
    IsIso (τ.app X) := by
  let inverse : G.obj X ⟶ F.obj X :=
    G.map e.hom ≫ inv (τ.app Y) ≫ F.map e.inv
  refine ⟨⟨inverse, ?_, ?_⟩⟩
  · dsimp [inverse]
    rw [← NatTrans.naturality_assoc]
    simp
  · dsimp [inverse]
    rw [Category.assoc, Category.assoc, NatTrans.naturality]
    simp

/-- The canonical derived tensor transformation attached to `oneTensorF` is characterized by the
usual counit compatibility square. -/
theorem derivedTensorNatTrans_fac :
    Wₐ.Q.whiskerLeft
        (Functor.leftDerivedNatTrans
          (tensorN.totalLeftDerived Wₐ.Q Wₐ) (tensorN'.totalLeftDerived Wₐ.Q Wₐ)
          (tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ)
          (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ) Wₐ oneTensorF) ≫
      tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ =
        tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ ≫ oneTensorF := by
  simpa using
    Functor.leftDerivedNatTrans_fac
      (tensorN.totalLeftDerived Wₐ.Q Wₐ) (tensorN'.totalLeftDerived Wₐ.Q Wₐ)
      (tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ)
      (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ) Wₐ oneTensorF

/-- If `P` computes the left derived functors of both tensor functors and `1 ⊗ f` is already an
isomorphism on `P`, then the induced derived tensor transformation is an isomorphism at `Q(P)`. -/
instance derivedTensorNatTrans_app_isIso_of_computesLeftDerivedAt
    {P : Kₐ}
    [Wₐ.ContainsIdentities]
    [tensorN.HasPointwiseLeftDerivedFunctor Wₐ]
    [tensorN'.HasPointwiseLeftDerivedFunctor Wₐ]
    [tensorN.ComputesLeftDerivedAt Wₐ P]
    [tensorN'.ComputesLeftDerivedAt Wₐ P]
    [IsIso (oneTensorF.app P)] :
    IsIso
      ((Functor.leftDerivedNatTrans
        (tensorN.totalLeftDerived Wₐ.Q Wₐ) (tensorN'.totalLeftDerived Wₐ.Q Wₐ)
        (tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ)
        (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ) Wₐ oneTensorF).app (Wₐ.Q.obj P)) := by
  have hTensorN :
      IsIso ((tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ).app P) :=
    (tensorN.computesLeftDerivedAt_iff Wₐ P).1 inferInstance
  letI : IsIso ((tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ).app P) := hTensorN
  have hTensorN' :
      IsIso ((tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ).app P) :=
    (tensorN'.computesLeftDerivedAt_iff Wₐ P).1 inferInstance
  letI : IsIso ((tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ).app P) := hTensorN'
  letI : IsIso (oneTensorF.app P) := inferInstance
  have hcomp :
      IsIso ((tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ).app P ≫ oneTensorF.app P) := by
    infer_instance
  have hcomp' :
      IsIso
        (((Functor.leftDerivedNatTrans
            (tensorN.totalLeftDerived Wₐ.Q Wₐ) (tensorN'.totalLeftDerived Wₐ.Q Wₐ)
            (tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ)
            (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ) Wₐ oneTensorF).app (Wₐ.Q.obj P)) ≫
          (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ).app P) := by
    rw [show
      ((Functor.leftDerivedNatTrans
          (tensorN.totalLeftDerived Wₐ.Q Wₐ) (tensorN'.totalLeftDerived Wₐ.Q Wₐ)
          (tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ)
          (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ) Wₐ oneTensorF).app (Wₐ.Q.obj P)) ≫
        (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ).app P =
          (tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ).app P ≫ oneTensorF.app P by
        simpa using NatTrans.congr_app
          (derivedTensorNatTrans_fac Wₐ tensorN tensorN' oneTensorF) P]
    simpa using hcomp
  letI :
      IsIso
        (((Functor.leftDerivedNatTrans
            (tensorN.totalLeftDerived Wₐ.Q Wₐ) (tensorN'.totalLeftDerived Wₐ.Q Wₐ)
            (tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ)
            (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ) Wₐ oneTensorF).app (Wₐ.Q.obj P)) ≫
          (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ).app P) := hcomp'
  let e :=
    asIso
        (((Functor.leftDerivedNatTrans
            (tensorN.totalLeftDerived Wₐ.Q Wₐ) (tensorN'.totalLeftDerived Wₐ.Q Wₐ)
            (tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ)
            (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ) Wₐ oneTensorF).app (Wₐ.Q.obj P)) ≫
          (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ).app P) ≪≫
      (asIso ((tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ).app P)).symm
  have hfac :
      ((Functor.leftDerivedNatTrans
          (tensorN.totalLeftDerived Wₐ.Q Wₐ) (tensorN'.totalLeftDerived Wₐ.Q Wₐ)
          (tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ)
          (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ) Wₐ oneTensorF).app (Wₐ.Q.obj P)) ≫
        (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ).app P =
      (tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ).app P ≫ oneTensorF.app P := by
    simpa using NatTrans.congr_app
      (derivedTensorNatTrans_fac Wₐ tensorN tensorN' oneTensorF) P
  have he :
      e.hom =
        ((Functor.leftDerivedNatTrans
            (tensorN.totalLeftDerived Wₐ.Q Wₐ) (tensorN'.totalLeftDerived Wₐ.Q Wₐ)
            (tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ)
            (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ) Wₐ oneTensorF).app (Wₐ.Q.obj P)) := by
    have hleft :
        e.hom =
          (tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ).app P ≫
            oneTensorF.app P ≫
              inv ((tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ).app P) := by
      simp [e, Category.assoc, hfac]
    have hright₁ :
        (tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ).app P ≫
            oneTensorF.app P ≫
              inv ((tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ).app P) =
          (((Functor.leftDerivedNatTrans
              (tensorN.totalLeftDerived Wₐ.Q Wₐ) (tensorN'.totalLeftDerived Wₐ.Q Wₐ)
              (tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ)
              (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ) Wₐ oneTensorF).app (Wₐ.Q.obj P)) ≫
            (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ).app P) ≫
              inv ((tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ).app P) := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ k ≫ inv ((tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ).app P))
          hfac.symm
    have hright₂ :
        (((Functor.leftDerivedNatTrans
            (tensorN.totalLeftDerived Wₐ.Q Wₐ) (tensorN'.totalLeftDerived Wₐ.Q Wₐ)
            (tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ)
            (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ) Wₐ oneTensorF).app (Wₐ.Q.obj P)) ≫
          (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ).app P) ≫
            inv ((tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ).app P) =
          ((Functor.leftDerivedNatTrans
              (tensorN.totalLeftDerived Wₐ.Q Wₐ) (tensorN'.totalLeftDerived Wₐ.Q Wₐ)
              (tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ)
              (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ) Wₐ oneTensorF).app (Wₐ.Q.obj P)) := by
      calc
        (((Functor.leftDerivedNatTrans
            (tensorN.totalLeftDerived Wₐ.Q Wₐ) (tensorN'.totalLeftDerived Wₐ.Q Wₐ)
            (tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ)
            (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ) Wₐ oneTensorF).app (Wₐ.Q.obj P)) ≫
          (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ).app P) ≫
            inv ((tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ).app P) =
          ((Functor.leftDerivedNatTrans
              (tensorN.totalLeftDerived Wₐ.Q Wₐ) (tensorN'.totalLeftDerived Wₐ.Q Wₐ)
              (tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ)
              (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ) Wₐ oneTensorF).app (Wₐ.Q.obj P)) ≫
            ((tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ).app P ≫
              inv ((tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ).app P)) := by
                rw [Category.assoc]
        _ =
          ((Functor.leftDerivedNatTrans
              (tensorN.totalLeftDerived Wₐ.Q Wₐ) (tensorN'.totalLeftDerived Wₐ.Q Wₐ)
              (tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ)
              (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ) Wₐ oneTensorF).app (Wₐ.Q.obj P)) := by
                simp
    exact hleft.trans (hright₁.trans hright₂)
  rw [← he]
  infer_instance

/-- If every object receives a denominator from a good `P`-object on which both tensor functors
compute their left derived functors and `1 ⊗ f` is an isomorphism, then the induced derived
tensor transformation is an isomorphism. -/
instance derivedTensorNatTrans_isIso_of_computesLeftDerivedAt
    [Wₐ.ContainsIdentities]
    (propertyP : ObjectProperty Kₐ)
    (hP_reaches :
      ∀ X : Kₐ, ∃ (P : Kₐ) (s : P ⟶ X), propertyP P ∧ Wₐ s)
    (hP_tensorN :
      ∀ P : Kₐ, propertyP P → tensorN.ComputesLeftDerivedAt Wₐ P)
    (hP_tensorN' :
      ∀ P : Kₐ, propertyP P → tensorN'.ComputesLeftDerivedAt Wₐ P)
    (hP_tensorMap_isIso :
      ∀ P : Kₐ, propertyP P → IsIso (oneTensorF.app P)) :
    IsIso
      (Functor.leftDerivedNatTrans
        (tensorN.totalLeftDerived Wₐ.Q Wₐ) (tensorN'.totalLeftDerived Wₐ.Q Wₐ)
        (tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ)
        (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ) Wₐ oneTensorF) := by
  let τ :
      tensorN.totalLeftDerived Wₐ.Q Wₐ ⟶
        tensorN'.totalLeftDerived Wₐ.Q Wₐ :=
    Functor.leftDerivedNatTrans
      (tensorN.totalLeftDerived Wₐ.Q Wₐ) (tensorN'.totalLeftDerived Wₐ.Q Wₐ)
      (tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ)
      (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ) Wₐ oneTensorF
  letI : tensorN.HasPointwiseLeftDerivedFunctor Wₐ :=
    Functor.hasPointwiseLeftDerivedFunctor_of_exists_computesLeftDerivedAt
      tensorN Wₐ
      (fun X ↦ by
        rcases hP_reaches X with ⟨P, s, hP, hs⟩
        exact ⟨P, s, hs, hP_tensorN P hP⟩)
  letI : tensorN'.HasPointwiseLeftDerivedFunctor Wₐ :=
    Functor.hasPointwiseLeftDerivedFunctor_of_exists_computesLeftDerivedAt
      tensorN' Wₐ
      (fun X ↦ by
        rcases hP_reaches X with ⟨P, s, hP, hs⟩
        exact ⟨P, s, hs, hP_tensorN' P hP⟩)
  letI : Wₐ.Q.EssSurj := Localization.essSurj Wₐ.Q Wₐ
  have hτ : ∀ X : Wₐ.Localization, IsIso (τ.app X) := by
    intro X
    let X' : Kₐ := Wₐ.Q.objPreimage X
    obtain ⟨P, s, hP, hs⟩ := hP_reaches X'
    letI : tensorN.ComputesLeftDerivedAt Wₐ P := hP_tensorN P hP
    letI : tensorN'.ComputesLeftDerivedAt Wₐ P := hP_tensorN' P hP
    letI : IsIso (oneTensorF.app P) := hP_tensorMap_isIso P hP
    have hPapp : IsIso (τ.app (Wₐ.Q.obj P)) := by
      dsimp [τ]
      infer_instance
    letI : IsIso (Wₐ.Q.map s) := Localization.inverts Wₐ.Q Wₐ s hs
    have hPreimage : IsIso (τ.app (Wₐ.Q.obj X')) := by
      simpa [X'] using
        natTrans_app_isIso_of_iso τ ((asIso (Wₐ.Q.map s)).symm)
    simpa [X'] using
      natTrans_app_isIso_of_iso τ ((Wₐ.Q.objObjPreimageIso X).symm)
  letI : IsIso τ := NatIso.isIso_of_isIso_app τ
  simpa [τ]

/-- Lemma 22.33.3: a homomorphism `f : N ⟶ N'` of differential graded `(A, B)`-bimodules
induces the natural transformation
`1 ⊗ f : - ⊗_A^L N ⟶ - ⊗_A^L N'` on derived tensor functors. If `f` is a
quasi-isomorphism, expressed here by the Stacks-style subset criterion from Lemma `22.33.2`:
every object admits a denominator from a good `P`-object, both tensor functors invert
denominators between such `P`-objects, and tensoring with `f` is an isomorphism on those good
objects, then this induced natural transformation is an isomorphism. In the Chapter `13`
API, the subset criterion is converted to `Functor.ComputesLeftDerivedAt` on the good
objects, and the present instance is the source-facing bridge to that canonical owner. -/
@[stacks 09S3]
instance derivedTensorNatTrans_isIso_of_quasiIso
    [Wₐ.IsSaturatedMultiplicativeSystem]
    (propertyP : ObjectProperty Kₐ)
    (hP_reaches :
      ∀ X : Kₐ, ∃ (P : Kₐ) (s : P ⟶ X), propertyP P ∧ Wₐ s)
    (hP_tensorN :
      ∀ {P P' : Kₐ} (s : P ⟶ P'), propertyP P → propertyP P' → Wₐ s →
        IsIso (tensorN.map s))
    (hP_tensorN' :
      ∀ {P P' : Kₐ} (s : P ⟶ P'), propertyP P → propertyP P' → Wₐ s →
        IsIso (tensorN'.map s))
    (hP_tensorMap_isIso :
      ∀ P : Kₐ, propertyP P → IsIso (oneTensorF.app P)) :
    IsIso
      (Functor.leftDerivedNatTrans
        (tensorN.totalLeftDerived Wₐ.Q Wₐ) (tensorN'.totalLeftDerived Wₐ.Q Wₐ)
        (tensorN.totalLeftDerivedCounit Wₐ.Q Wₐ)
        (tensorN'.totalLeftDerivedCounit Wₐ.Q Wₐ) Wₐ oneTensorF) := by
  let hP_tensorN_computes :
      ∀ P : Kₐ, propertyP P → tensorN.ComputesLeftDerivedAt Wₐ P :=
    fun P hP ↦
      Functor.computesLeftDerivedAt_of_mem_subset
        tensorN Wₐ propertyP hP_reaches hP_tensorN hP
  let hP_tensorN'_computes :
      ∀ P : Kₐ, propertyP P → tensorN'.ComputesLeftDerivedAt Wₐ P :=
    fun P hP ↦
      Functor.computesLeftDerivedAt_of_mem_subset
        tensorN' Wₐ propertyP hP_reaches hP_tensorN' hP
  exact
    derivedTensorNatTrans_isIso_of_computesLeftDerivedAt
      Wₐ tensorN tensorN' oneTensorF propertyP hP_reaches
      hP_tensorN_computes hP_tensorN'_computes hP_tensorMap_isIso

end
