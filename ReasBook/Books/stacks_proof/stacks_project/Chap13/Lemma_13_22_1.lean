import Mathlib
import StacksProject_2024.Chap13.Definition_13_15_3
import StacksProject_2024.Chap13.Lemma_13_14_16
import StacksProject_2024.Chap13.Lemma_13_16_7_Leray_s_acyclicity_lemma
import StacksProject_2024.Chap13.Lemma_13_20_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.Localization
open scoped CategoryTheory

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂} {𝒞 : Type u₃}
variable [Category.{v₁} 𝒜] [Category.{v₂} ℬ] [Category.{v₃} 𝒞]
variable [Abelian 𝒜] [Abelian ℬ] [Abelian 𝒞]
variable [HasInjectiveResolutions 𝒜]
variable [HasDerivedCategory.{w} 𝒞]

variable (F : 𝒜 ⥤ ℬ)

variable (G : ℬ ⥤ 𝒞)
variable [F.Additive] [G.Additive]

local notation "QisA" => boundedBelowHomotopyQuasiIso 𝒜
local notation "QisB" => boundedBelowHomotopyQuasiIso ℬ
local notation "QA" => (boundedBelowHomotopyQuasiIso 𝒜).Q
local notation "QB" => (boundedBelowHomotopyQuasiIso ℬ).Q
local notation "KplusF" => mapBoundedBelowHomotopyCategory F
local notation "KplusG" => mapBoundedBelowHomotopyCategoryToDerivedBelow G
local notation "RF" => Functor.totalRightDerived (KplusF ⋙ QB) QA QisA
local notation "RG" => Functor.totalRightDerived KplusG QB QisB
local notation "RGF" => Functor.totalRightDerived (KplusF ⋙ KplusG) QA QisA
local notation "α₁" => Functor.totalRightDerivedUnit (KplusF ⋙ QB) QA QisA
local notation "αG" => Functor.totalRightDerivedUnit KplusG QB QisB
local notation "αGF" => Functor.totalRightDerivedUnit (KplusF ⋙ KplusG) QA QisA

/- Domain-style sampling for bounded-below Grothendieck-comparison morphisms:
- primary domain: composition comparisons for right derived functors on bounded-below homotopy and
  derived categories of abelian categories
- sampled owner declarations:
  `Functor.rightDerivedCompComparison`,
  `Functor.rightDerivedCompComparison_fac`,
  `mapBoundedBelowHomotopyCategory`,
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`,
  `HasInjectiveResolutions`
- best owner abstraction: the canonical comparison morphism
  `Functor.rightDerivedCompComparison`, specialized to the bounded-below source functors
- primitive data: the source category `𝒜` with injective resolutions, the additive functors `F`,
  `G`, and the three `HasRightDerivedFunctor` instances needed to form the comparison
- derived API: the acyclicity criterion asserting that this canonical comparison is an isomorphism
- layer targeted here: `bridge/view`; this lemma is the bounded-below source-facing criterion, not
  a new owner for the comparison morphism itself
-/

-- Proof sketch: for the forward implication, apply Leray's acyclicity lemma to an injective
-- resolution of each bounded-below complex of `𝒜`, using that every injective term is sent by
-- `F` to a `G`-acyclic object; this identifies the comparison map with an objectwise
-- quasi-isomorphism. For the converse, evaluate the comparison isomorphism on the degree-zero
-- complex of an injective object `I`; since `I` already computes `RF`, the comparison forces
-- `F.obj I` to compute the right derived functor of `G`, hence to be right acyclic.
namespace Functor

/-- Helper for Lemma 13.22.1: if a bounded-below homotopy object has injective terms, then the
image under `F` is termwise bounded-below right `G`-acyclic as soon as `F` sends every injective
object of `𝒜` to a bounded-below right `G`-acyclic object. -/
lemma image_of_termwise_injective_is_termwise_boundedBelowRightAcyclic
    (hAcyclic : ∀ (I : 𝒜) [Injective I],
      IsBoundedBelowRightAcyclicForAdditiveFunctor G (F.obj I))
    (X : K⁺(𝒜))
    (hX : ∀ n : ℤ, Injective (X.obj.as.X n)) :
    IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor G (KplusF.obj X) := by
  -- Each term of `KplusF.obj X` is `F.obj` of a term of `X`, so the injective-term hypothesis
  -- reduces the goal to the objectwise acyclicity assumption on `F`.
  intro n
  let _ : Injective (X.obj.as.X n) := hX n
  simpa [IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor] using
    hAcyclic (X.obj.as.X n)

/-- Helper for Lemma 13.22.1: the degree-zero bounded-below complex on an injective object has
injective terms in every degree. -/
lemma single0Plus_termwise_injective
    (I : 𝒜) [Injective I] :
    ∀ n : ℤ, Injective (((single0Plus 𝒜).obj I).obj.as.X n) := by
  intro n
  by_cases hn : n = 0
  · subst hn
    simpa using (inferInstance : Injective I)
  ·
    let hzero :
        IsZero (((single0Plus 𝒜).obj I).obj.as.X n) := by
      simpa using
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 I n hn)
    exact hzero.injective

/-- Helper for Lemma 13.22.1: the degree-zero bounded-below complex on an injective object is a
bounded-below complex of injectives. -/
abbrev single0Plus_to_injectivePlus
    (I : 𝒜) [Injective I] :
    CochainComplex.InjectivePlus 𝒜 :=
  ⟨⟨((single0Plus 𝒜).obj I).obj.as, ((single0Plus 𝒜).obj I).property⟩,
    single0Plus_termwise_injective (𝒜 := 𝒜) I⟩

variable [Functor.HasRightDerivedFunctor
  (KplusF ⋙ KplusG)
  QisA]
variable [Functor.HasRightDerivedFunctor
  (KplusF ⋙ QB)
  QisA]
variable [Functor.HasRightDerivedFunctor
  KplusG
  QisB]

/-- Helper for Lemma 13.22.1: once the comparison component is an isomorphism at a bounded-below
quasi-isomorphic target, naturality transports the same conclusion back to the source. -/
lemma rightDerivedCompComparison_app_isIso_of_quasiIso
    {X Y : K⁺(𝒜)} (f : X ⟶ Y) (hf : QisA f)
    (hY :
      IsIso
        ((rightDerivedCompComparison QisA QisB KplusF KplusG).app
          (QisA.Q.obj Y))) :
    IsIso
      ((rightDerivedCompComparison QisA QisB KplusF KplusG).app
        (QA.obj X)) := by
  let τ : RGF ⟶ RF ⋙ RG := rightDerivedCompComparison QisA QisB KplusF KplusG
  have hQf : IsIso (QA.map f) := Localization.inverts QA QisA f hf
  have hcod : IsIso ((RF ⋙ RG).map (QA.map f)) := by
    infer_instance
  have hcomp :
      IsIso
        (τ.app (QA.obj X) ≫
          (RF ⋙ RG).map (QA.map f)) := by
    rw [← τ.naturality (QA.map f)]
    infer_instance
  exact
    (isIso_comp_right_iff
      (τ.app (QA.obj X))
      ((RF ⋙ RG).map (QA.map f))).1 hcomp

/-- Helper for Lemma 13.22.1: naturality along an isomorphism in `D^+(\mathcal A)` transports
invertibility of the comparison component to the source object. -/
lemma rightDerivedCompComparison_app_isIso_of_iso
    {X Y : D⁺(𝒜)} (e : X ≅ Y)
    (hY :
      IsIso
        ((rightDerivedCompComparison QisA QisB KplusF KplusG).app Y)) :
    IsIso
      ((rightDerivedCompComparison QisA QisB KplusF KplusG).app X) := by
  let τ : RGF ⟶ RF ⋙ RG := rightDerivedCompComparison QisA QisB KplusF KplusG
  have hcod : IsIso ((RF ⋙ RG).map e.hom) := by
    infer_instance
  have hcomp :
      IsIso
        (τ.app X ≫
          (RF ⋙ RG).map e.hom) := by
    rw [τ.naturality e.hom]
    infer_instance
  exact
    (isIso_comp_right_iff
      (τ.app X)
      ((RF ⋙ RG).map e.hom)).1 hcomp

/-- Helper for Lemma 13.22.1: on a bounded-below injective model, the comparison component is an
isomorphism because all three unit factors in `rightDerivedCompComparison_fac` are isomorphisms. -/
lemma rightDerivedCompComparison_app_isIso_of_boundedBelow_injective_complex
    (hAcyclic : ∀ (I : 𝒜) [Injective I],
      IsBoundedBelowRightAcyclicForAdditiveFunctor G (F.obj I))
    (J : CochainComplex.InjectivePlus 𝒜) :
    IsIso
      ((rightDerivedCompComparison QisA QisB KplusF KplusG).app
        (QA.obj ((HomotopyCategory.Plus.quotient 𝒜).obj J))) := by
  let X : K⁺(𝒜) := (HomotopyCategory.Plus.quotient 𝒜).obj J
  have hComputeGF :
      (KplusF ⋙ KplusG).ComputesRightDerivedAt QisA X := by
    -- Proof comment: a bounded-below injective complex already computes any bounded-below right
    -- derived functor by Lemma `13.20.1`.
    simpa [X] using
      (CategoryTheory.boundedBelowInjectiveComplex_computesRightDerivedFunctorAt
        (F := KplusF ⋙ KplusG) (I := J))
  have hαGF : IsIso (αGF.app X) := by
    -- Proof comment: convert the injective-model computation into invertibility of the total unit.
    exact
      (Functor.computesRightDerivedAt_iff
        (F := KplusF ⋙ KplusG) (S := QisA) (X := X)).1 hComputeGF
  have hComputeF :
      (KplusF ⋙ QB).ComputesRightDerivedAt QisA X := by
    -- Proof comment: the same injective-model computation applies to `F` viewed in `D^+(ℬ)`.
    simpa [X] using
      (CategoryTheory.boundedBelowInjectiveComplex_computesRightDerivedFunctorAt
        (F := KplusF ⋙ QB) (I := J))
  have hα₁ : IsIso (α₁.app X) := by
    -- Proof comment: the first comparison unit is invertible on the chosen injective model.
    exact
      (Functor.computesRightDerivedAt_iff
        (F := KplusF ⋙ QB) (S := QisA) (X := X)).1 hComputeF
  have hTermwise :
      IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor G (KplusF.obj X) := by
    -- Proof comment: each term of `J` is injective, so the hypothesis on injective objects gives
    -- the termwise `G`-acyclicity of `F(J)`.
    exact
      image_of_termwise_injective_is_termwise_boundedBelowRightAcyclic
        (F := F) (G := G) hAcyclic X (fun n ↦ by simpa [X] using J.term_mem n)
  have hComputeG :
      KplusG.ComputesRightDerivedAt QisB (KplusF.obj X) := by
    -- Proof comment: Leray's bounded-below acyclicity lemma upgrades the termwise acyclicity of
    -- `F(J)` to the statement that `F(J)` computes `RG`.
    exact
      CategoryTheory.computesRightDerivedAt_of_termwise_boundedBelowRightAcyclic
        (F := G) (A := KplusF.obj X) inferInstance hTermwise
  have hαG : IsIso (αG.app (KplusF.obj X)) := by
    -- Proof comment: the Leray computation is again equivalent to invertibility of the total unit.
    exact
      (Functor.computesRightDerivedAt_iff
        (F := KplusG) (S := QisB) (X := KplusF.obj X)).1 hComputeG
  have hfac :
      αGF.app X ≫
          ((rightDerivedCompComparison QisA QisB KplusF KplusG).app (QA.obj X)) =
        (((Functor.whiskerLeft KplusF αG).app X) ≫
            (Functor.associator KplusF QB RG).hom.app X) ≫
          ((Functor.whiskerRight α₁ RG).app X) ≫
            (Functor.associator QA RF RG).hom.app X := by
    -- Proof comment: this is the source comparison factorization from Lemma `13.14.16`,
    -- specialized to the injective model `X`.
    simpa [X, Category.assoc] using
      NatTrans.congr_app
        (Functor.rightDerivedCompComparison_fac
          (S := QisA) (S' := QisB) (F := KplusF) (G := KplusG)) X
  have htail :
      IsIso
        ((((Functor.whiskerLeft KplusF αG).app X) ≫
            (Functor.associator KplusF QB RG).hom.app X) ≫
          ((Functor.whiskerRight α₁ RG).app X) ≫
            (Functor.associator QA RF RG).hom.app X) := by
    -- Proof comment: every factor on the right-hand side of the comparison factorization is now
    -- known to be an isomorphism.
    let _ : IsIso (αG.app (KplusF.obj X)) := hαG
    let _ : IsIso (α₁.app X) := hα₁
    simpa [Category.assoc] using
      (show IsIso
        ((((Functor.whiskerLeft KplusF αG).app X) ≫
            (Functor.associator KplusF QB RG).hom.app X) ≫
          ((Functor.whiskerRight α₁ RG).app X) ≫
            (Functor.associator QA RF RG).hom.app X) from inferInstance)
  have hcomp :
      IsIso
        (αGF.app X ≫
          ((rightDerivedCompComparison QisA QisB KplusF KplusG).app (QA.obj X))) := by
    -- Proof comment: rewrite the left-hand side of the comparison factorization to the already
    -- invertible right-hand side.
    rw [hfac]
    exact htail
  -- Proof comment: cancel the invertible source-side unit `αGF.app X` to isolate the desired
  -- comparison component.
  let _ : IsIso (αGF.app X) := hαGF
  exact
    (isIso_comp_left_iff
      (αGF.app X)
      ((rightDerivedCompComparison QisA QisB KplusF KplusG).app (QA.obj X))).1 hcomp

/-- Helper for Lemma 13.22.1: evaluating the comparison on the degree-zero injective model `I[0]`
forces the unit for `G` at `F(I)[0]` to be an isomorphism, hence `F(I)` is bounded-below right
acyclic for `G`. -/
lemma boundedBelowRightAcyclic_of_single0Plus_comparison_app_isIso
    (I : 𝒜) [Injective I]
    (hComparison :
      IsIso
        ((rightDerivedCompComparison QisA QisB KplusF KplusG).app
          (QA.obj ((single0Plus 𝒜).obj I)))) :
    IsBoundedBelowRightAcyclicForAdditiveFunctor G (F.obj I) := by
  let X : K⁺(𝒜) := (single0Plus 𝒜).obj I
  have hComputeGF :
      (KplusF ⋙ KplusG).ComputesRightDerivedAt QisA X := by
    -- Proof comment: the degree-zero complex on an injective object is itself a bounded-below
    -- injective complex, so it computes the derived functor of `G ∘ F`.
    simpa [X, single0Plus_to_injectivePlus] using
      (CategoryTheory.boundedBelowInjectiveComplex_computesRightDerivedFunctorAt
        (F := KplusF ⋙ KplusG) (I := single0Plus_to_injectivePlus (𝒜 := 𝒜) I))
  have hαGF : IsIso (αGF.app X) := by
    -- Proof comment: convert the injective-model computation to the unit-isomorphism form.
    exact
      (Functor.computesRightDerivedAt_iff
        (F := KplusF ⋙ KplusG) (S := QisA) (X := X)).1 hComputeGF
  have hComputeF :
      (KplusF ⋙ QB).ComputesRightDerivedAt QisA X := by
    -- Proof comment: the same injective-model argument computes `RF(I[0])`.
    simpa [X, single0Plus_to_injectivePlus] using
      (CategoryTheory.boundedBelowInjectiveComplex_computesRightDerivedFunctorAt
        (F := KplusF ⋙ QB) (I := single0Plus_to_injectivePlus (𝒜 := 𝒜) I))
  have hα₁ : IsIso (α₁.app X) := by
    -- Proof comment: the first unit in the comparison factorization is invertible on `I[0]`.
    exact
      (Functor.computesRightDerivedAt_iff
        (F := KplusF ⋙ QB) (S := QisA) (X := X)).1 hComputeF
  have hfac :
      αGF.app X ≫
          ((rightDerivedCompComparison QisA QisB KplusF KplusG).app (QA.obj X)) =
        (((Functor.whiskerLeft KplusF αG).app X) ≫
            (Functor.associator KplusF QB RG).hom.app X) ≫
          ((Functor.whiskerRight α₁ RG).app X) ≫
            (Functor.associator QA RF RG).hom.app X := by
    -- Proof comment: specialize the comparison factorization to the degree-zero injective model.
    simpa [X, Category.assoc] using
      NatTrans.congr_app
        (Functor.rightDerivedCompComparison_fac
          (S := QisA) (S' := QisB) (F := KplusF) (G := KplusG)) X
  have htail :
      IsIso
        ((((Functor.whiskerLeft KplusF αG).app X) ≫
            (Functor.associator KplusF QB RG).hom.app X) ≫
          ((Functor.whiskerRight α₁ RG).app X) ≫
            (Functor.associator QA RF RG).hom.app X) := by
    -- Proof comment: the comparison component is assumed invertible at `I[0]`, and the source
    -- unit `αGF.app X` is invertible by Lemma `13.20.1`, so the whole right-hand side is invertible.
    have hcomp :
        IsIso
          (αGF.app X ≫
            ((rightDerivedCompComparison QisA QisB KplusF KplusG).app (QA.obj X))) := by
      let _ : IsIso (αGF.app X) := hαGF
      let _ : IsIso
          ((rightDerivedCompComparison QisA QisB KplusF KplusG).app (QA.obj X)) := hComparison
      infer_instance
    rw [← hfac]
    simpa [Category.assoc] using hcomp
  let _ : IsIso (α₁.app X) := hα₁
  have hmid :
      IsIso
        (((Functor.whiskerLeft KplusF αG).app X) ≫
          (Functor.associator KplusF QB RG).hom.app X ≫
            (Functor.whiskerRight α₁ RG).app X) := by
    -- Proof comment: remove the final associator isomorphism from the right.
    exact
      (isIso_comp_right_iff
        (((Functor.whiskerLeft KplusF αG).app X) ≫
          (Functor.associator KplusF QB RG).hom.app X ≫
            (Functor.whiskerRight α₁ RG).app X)
        ((Functor.associator QA RF RG).hom.app X)).1
        (by simpa [Category.assoc] using htail)
  have hleft :
      IsIso
        (((Functor.whiskerLeft KplusF αG).app X) ≫
          (Functor.associator KplusF QB RG).hom.app X) := by
    -- Proof comment: remove the mapped `RF`-unit from the right.
    exact
      (isIso_comp_right_iff
        (((Functor.whiskerLeft KplusF αG).app X) ≫
          (Functor.associator KplusF QB RG).hom.app X)
        ((Functor.whiskerRight α₁ RG).app X)).1 hmid
  have hαG :
      IsIso ((Functor.whiskerLeft KplusF αG).app X) := by
    -- Proof comment: remove the remaining associator to isolate the middle unit `αG`.
    exact
      (isIso_comp_right_iff
        ((Functor.whiskerLeft KplusF αG).app X)
        ((Functor.associator KplusF QB RG).hom.app X)).1 hleft
  have hComputeG :
      KplusG.ComputesRightDerivedAt QisB (KplusF.obj X) := by
    -- Proof comment: the isolated middle unit says exactly that `F(I)[0]` computes `RG`.
    exact
      (Functor.computesRightDerivedAt_iff
        (F := KplusG) (S := QisB) (X := KplusF.obj X)).2
        (by simpa [X] using hαG)
  -- Proof comment: `KplusF.obj I[0]` is the degree-zero bounded-below complex on `F.obj I`, so
  -- this is precisely the bounded-below right acyclicity of `F.obj I`.
  simpa [IsBoundedBelowRightAcyclicForAdditiveFunctor, X, HomotopyCategory.quotient_obj_as] using
    hComputeG

/-- Helper for Lemma 13.22.1: an injective resolution of a bounded-below representative packages
its comparison map as a bounded-below quasi-isomorphism in `K^+(\mathcal A)`. -/
lemma homotopy_quasiIso_of_injectiveResolution
    (K : K⁺(𝒜))
    (J : CochainComplex.InjectiveResolution K.obj.as) :
    ∃ s : K ⟶ (HomotopyCategory.Plus.quotient 𝒜).obj J, QisA s := by
  let Xc : CochainComplex.Plus 𝒜 := ⟨K.obj.as, K.property⟩
  have hKeq : (HomotopyCategory.Plus.quotient 𝒜).obj Xc = K := by
    rfl
  let α' : Xc ⟶ J := ⟨J.ι⟩
  let s : K ⟶ (HomotopyCategory.Plus.quotient 𝒜).obj J := by
    -- Proof comment: pass the cochain-level injective-resolution map to the bounded-below
    -- homotopy category.
    simpa [hKeq] using (HomotopyCategory.Plus.quotient 𝒜).map α'
  refine ⟨s, ?_⟩
  -- Proof comment: the bounded-below localizer detects exactly the quasi-isomorphisms of the
  -- underlying homotopy-category morphisms.
  simpa [boundedBelowHomotopyQuasiIso, s, hKeq] using
    (show HomotopyCategory.quasiIso 𝒜 (up ℤ)
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).map J.ι) by
      rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
      infer_instance)

/-- Helper for Lemma 13.22.1: if `K` is represented by an injective resolution `J`, then the
comparison component is already an isomorphism at `QA.obj K`. -/
lemma rightDerivedCompComparison_app_isIso_of_injectiveResolution
    (hAcyclic : ∀ (I : 𝒜) [Injective I],
      IsBoundedBelowRightAcyclicForAdditiveFunctor G (F.obj I))
    (K : K⁺(𝒜))
    (J : CochainComplex.InjectiveResolution K.obj.as) :
    IsIso
      ((rightDerivedCompComparison QisA QisB KplusF KplusG).app
        (QA.obj K)) := by
  obtain ⟨s, hs⟩ :=
    homotopy_quasiIso_of_injectiveResolution (𝒜 := 𝒜) K J
  have hJ :
      IsIso
        ((rightDerivedCompComparison QisA QisB KplusF KplusG).app
          (QA.obj ((HomotopyCategory.Plus.quotient 𝒜).obj J))) := by
    -- Proof comment: the chosen injective resolution is itself a bounded-below injective model.
    exact
      rightDerivedCompComparison_app_isIso_of_boundedBelow_injective_complex
        (F := F) (G := G) hAcyclic J
  -- Proof comment: transport the injective-model comparison isomorphism back along the
  -- quasi-isomorphism induced by the resolution map.
  exact
    rightDerivedCompComparison_app_isIso_of_quasiIso
      (F := F) (G := G) s hs hJ

/-- Helper for Lemma 13.22.1: a chosen injective resolution of `QisA.Q.objPreimage X` gives the
comparison isomorphism at the original bounded-below derived object `X`. -/
lemma objPreimage_injectiveResolution_transport
    (hAcyclic : ∀ (I : 𝒜) [Injective I],
      IsBoundedBelowRightAcyclicForAdditiveFunctor G (F.obj I))
    (X : D⁺(𝒜))
    (J : CochainComplex.InjectiveResolution (QisA.Q.objPreimage X).obj.as) :
    IsIso
      ((rightDerivedCompComparison QisA QisB KplusF KplusG).app X) := by
  let K : K⁺(𝒜) := QisA.Q.objPreimage X
  have hK :
      IsIso
        ((rightDerivedCompComparison QisA QisB KplusF KplusG).app
          (QA.obj K)) := by
    -- Proof comment: first solve the comparison on the chosen bounded-below representative of
    -- `X`.
    simpa [K] using
      rightDerivedCompComparison_app_isIso_of_injectiveResolution
        (F := F) (G := G) hAcyclic K J
  -- Proof comment: then transport along the canonical localization isomorphism
  -- `QA.obj (Q.objPreimage X) ≅ X`.
  exact
    rightDerivedCompComparison_app_isIso_of_iso
      (F := F) (G := G) (QisA.Q.objObjPreimageIso X).symm hK

/-- Helper for Lemma 13.22.1: the only remaining source-faithful input is a chosen cochain-level
injective resolution of the bounded-below representative `K.obj.as`. -/
lemma nonempty_injectiveResolution_of_homotopyObject
    (K : K⁺(𝒜)) :
    Nonempty (CochainComplex.InjectiveResolution K.obj.as) := by
  -- TODO: recover the earlier-owner bridge from `[HasInjectiveResolutions 𝒜]` to a chapter
  -- `CochainComplex.InjectiveResolution` of the representing bounded-below complex `K.obj.as`.
  sorry

/-- Lemma 13.22.1 in bounded-below owner form: assume the canonical bounded-below right derived
functors of `F ⋙ G`, of `F` viewed in `D⁺(ℬ)`, and of `G` are defined. Then the canonical
comparison morphism
`rightDerivedCompComparison QisA QisB KplusF KplusG : R(G \circ F) ⟶ RG ∘ RF`
is an isomorphism if and only if, for every injective object `I` of `𝒜`, the object `F.obj I`
is right acyclic for the bounded-below right derived functor of `G`. -/
@[stacks 015M]
theorem rightDerivedCompComparison_isIso_iff
    :
      IsIso (rightDerivedCompComparison QisA QisB KplusF KplusG) ↔
        ∀ (I : 𝒜) [Injective I],
          IsBoundedBelowRightAcyclicForAdditiveFunctor G (F.obj I) := by
  constructor
  · intro hComparison I hI
    -- Route correction: follow the source exactly by evaluating the comparison on the degree-zero
    -- injective model `I[0]` and then solving for the remaining `G`-unit.
    let _ : Injective I := hI
    let _ : IsIso (rightDerivedCompComparison QisA QisB KplusF KplusG) := hComparison
    have hApp :
        IsIso
          ((rightDerivedCompComparison QisA QisB KplusF KplusG).app
            (QA.obj ((single0Plus 𝒜).obj I))) := by
      infer_instance
    exact
      boundedBelowRightAcyclic_of_single0Plus_comparison_app_isIso
        (F := F) (G := G) I hApp
  · intro hAcyclic
    -- Proof comment: follow the source proof literally. For each bounded-below derived object,
    -- choose a bounded-below representative, resolve it by a bounded-below injective complex,
    -- prove the comparison on that injective model, and transport back to the original object.
    refine (NatTrans.isIso_iff_isIso_app _).2 ?_
    intro X
    let K : K⁺(𝒜) := QisA.Q.objPreimage X
    let J : CochainComplex.InjectiveResolution K.obj.as :=
      Classical.choice (nonempty_injectiveResolution_of_homotopyObject (𝒜 := 𝒜) K)
    -- Proof comment: the helper lemma packages the resolution map as the needed quasi-isomorphism
    -- in `K^+(\mathcal A)` and performs the two transport steps.
    exact
      objPreimage_injectiveResolution_transport
        (F := F) (G := G) hAcyclic X J

end Functor

end

end CategoryTheory
