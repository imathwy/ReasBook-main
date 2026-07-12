import Mathlib
import StacksProject_2024.Chap15.Situation_15_7_1
import StacksProject_2024.Chap15.Lemma_15_6_2
import StacksProject_2024.Chap15.Lemma_15_6_7
import StacksProject_2024.Chap15.Lemma_15_7_3

open CategoryTheory
open CategoryTheory.Limits
open CommRingCat
open scoped TensorProduct

universe u

noncomputable section

section

variable {B A A' Dp : Type u}
variable [CommRing B] [CommRing A] [CommRing A'] [CommRing Dp]

namespace FiberProductBaseChangeSituation

local notation "Situation" => @FiberProductBaseChangeSituation B A A' Dp _ _ _ _
variable (S : Situation)

local notation "fiberProductFunctor" =>
  (@module_tensor_pullback_right_adjoint
    S.C
    S.CPrime
    S.D
    Dp
    _ _ _ _
    S.dToC
    S.cprimeToC
    S.dprimeToD
    S.dprimeToCPrime
    S.tensor_square_commutes : S.relativeModuleCategory ⥤ ModuleCat Dp)

/- Domain-style sampling for Lemma 15.7.4:
- primary domain: module finiteness for the canonical fibre-product functor attached to the
  tensor square `D' → D`, `D' → C'`, `D → C`, `C' → C`;
- sampled owner declarations:
  `SurjectiveRingPullbackSituation`,
  `surjectiveRingPullbackModuleAdjunctionMap_surjective`,
  `surjectiveRingPullbackModuleFiberProduct_finite`,
  `Algebra.TensorProduct.map_surjective`;
- best owner abstraction: the tensor square should be handled through the owner theorem
  `surjectiveRingPullbackModuleFiberProduct_finite`, after packaging the square
  `D → C`, `C' → C` as a `SurjectiveRingPullbackSituation`;
- primitive data: the base-change situation `S`;
- derived API: the tensor-square surjective pullback situation and the canonical comparison map
  `D' → D ×_C C'`.

Source/core/bridge triage:
- `source-facing`: `relativeModuleFiberProduct_finite`;
- `core/canonical`: `surjectiveRingPullbackModuleFiberProduct_finite`;
- `bridge/view`: the tensor-square surjective pullback situation and the comparison
  `D' → D ×_C C'`. -/

private theorem cprimeToC_surjective
    (S : Situation) :
    Function.Surjective S.cprimeToC := by
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · exact ⟨0, by simp⟩
  · intro d a
    obtain ⟨a', rfl⟩ := S.fromAprime_surjective a
    refine ⟨d ⊗ₜ[S.Bprime] a', ?_⟩
    let _ : Algebra A' A := S.fromAprime.toAlgebra
    rfl
  · intro z₁ z₂ hz₁ hz₂
    rcases hz₁ with ⟨w₁, rfl⟩
    rcases hz₂ with ⟨w₂, rfl⟩
    exact ⟨w₁ + w₂, by simp⟩

/-- The tensor square `D → C`, `C' → C` defines a surjective pullback situation whose source ring
is the canonical pullback `D ×_C C'`. -/
private def tensorPullbackSituation
    (S : Situation) :
    SurjectiveRingPullbackSituation S.D S.C S.CPrime where
  toA := S.dToC
  fromAprime := S.cprimeToC
  fromAprime_surjective := cprimeToC_surjective S

/- The specialized fibre-product functor for the tensor pullback situation. -/
/-- Helper for Lemma 15.7.4: the canonical fibre-product functor for the tensor pullback square
`D → C ← C'`. -/
private noncomputable abbrev tensorPullbackFiberProductFunctor
    (S : Situation) :
    S.relativeModuleCategory ⥤ ModuleCat (tensorPullbackSituation S).Bprime :=
  @module_tensor_pullback_right_adjoint
    S.D
    S.C
    S.CPrime
    (tensorPullbackSituation S).Bprime
    _ _ _ _
    (tensorPullbackSituation S).bprimeToB
    (tensorPullbackSituation S).bprimeToAprime
    (tensorPullbackSituation S).comm

/-- Helper for Lemma 15.7.4: when two composite scalar maps into a common target ring agree, the
induced transport between the corresponding restricted-scalar structures is the canonical identity
map on the underlying carrier. -/
private def restrictScalars_comm_hom
    {R S T U : Type u}
    [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    (f : R →+* S) (g : R →+* T)
    (φ : S →+* U) (ψ : T →+* U)
    (hcomm : φ.comp f = ψ.comp g)
    (M : ModuleCat U) :
    (ModuleCat.restrictScalars (φ.comp f)).obj M ⟶
      (ModuleCat.restrictScalars (ψ.comp g)).obj M :=
  (eqToIso (congrArg
    (fun h ↦ (ModuleCat.restrictScalars h).obj M)
    hcomm)).hom

/-- Helper for Lemma 15.7.4: the left comparison map from the restricted first component of a
pullback-module object to the common extended-scalar target. -/
private abbrev module_tensor_pullback_left_map
    {B₀ A₀ A₀' B₀' : Type u}
    [CommRing B₀] [CommRing A₀] [CommRing A₀'] [CommRing B₀']
    {toA : B₀ →+* A₀} {fromAprime : A₀' →+* A₀}
    (f : B₀' →+* B₀) (g : B₀' →+* A₀')
    (hcomm : toA.comp f = fromAprime.comp g)
    (X : CategoricalPullback (ModuleCat.extendScalars toA) (ModuleCat.extendScalars fromAprime)) :
    (ModuleCat.restrictScalars f).obj X.fst ⟶
      (ModuleCat.restrictScalars (fromAprime.comp g)).obj
        ((ModuleCat.extendScalars fromAprime).obj X.snd) :=
  (ModuleCat.restrictScalars f).map ((ModuleCat.extendRestrictScalarsAdj toA).unit.app X.fst) ≫
    (ModuleCat.restrictScalarsComp f toA).inv.app ((ModuleCat.extendScalars toA).obj X.fst) ≫
    (ModuleCat.restrictScalars (toA.comp f)).map X.iso.hom ≫
    restrictScalars_comm_hom f g toA fromAprime hcomm
      ((ModuleCat.extendScalars fromAprime).obj X.snd)

/-- Helper for Lemma 15.7.4: the right comparison map from the restricted second component of a
pullback-module object to the same extended-scalar target. -/
private abbrev module_tensor_pullback_right_map
    {B₀ A₀ A₀' B₀' : Type u}
    [CommRing B₀] [CommRing A₀] [CommRing A₀'] [CommRing B₀']
    {toA : B₀ →+* A₀} {fromAprime : A₀' →+* A₀}
    (g : B₀' →+* A₀')
    (X : CategoricalPullback (ModuleCat.extendScalars toA) (ModuleCat.extendScalars fromAprime)) :
    (ModuleCat.restrictScalars g).obj X.snd ⟶
      (ModuleCat.restrictScalars (fromAprime.comp g)).obj
        ((ModuleCat.extendScalars fromAprime).obj X.snd) :=
  (ModuleCat.restrictScalars g).map ((ModuleCat.extendRestrictScalarsAdj fromAprime).unit.app X.snd) ≫
    (ModuleCat.restrictScalarsComp g fromAprime).inv.app
      ((ModuleCat.extendScalars fromAprime).obj X.snd)

/-- Helper for Lemma 15.7.4: the ambient product module whose kernel realizes the canonical
fibre-product module for a surjective pullback situation. -/
private abbrev fiber_product_ambient_product
    {B₀ A₀ A₀' : Type u}
    [CommRing B₀] [CommRing A₀] [CommRing A₀']
    (S : SurjectiveRingPullbackSituation B₀ A₀ A₀')
    (X : CategoricalPullback (ModuleCat.extendScalars S.toA) (ModuleCat.extendScalars S.fromAprime)) :
    ModuleCat S.Bprime :=
  Limits.prod ((ModuleCat.restrictScalars S.bprimeToB).obj X.fst)
    ((ModuleCat.restrictScalars S.bprimeToAprime).obj X.snd)

/-- Helper for Lemma 15.7.4: the first projection from the ambient product module. -/
private abbrev fiber_product_ambient_fst
    {B₀ A₀ A₀' : Type u}
    [CommRing B₀] [CommRing A₀] [CommRing A₀']
    (S : SurjectiveRingPullbackSituation B₀ A₀ A₀')
    (X : CategoricalPullback (ModuleCat.extendScalars S.toA) (ModuleCat.extendScalars S.fromAprime)) :
    fiber_product_ambient_product S X ⟶
      (ModuleCat.restrictScalars S.bprimeToB).obj X.fst :=
  Limits.prod.fst

/-- Helper for Lemma 15.7.4: the second projection from the ambient product module. -/
private abbrev fiber_product_ambient_snd
    {B₀ A₀ A₀' : Type u}
    [CommRing B₀] [CommRing A₀] [CommRing A₀']
    (S : SurjectiveRingPullbackSituation B₀ A₀ A₀')
    (X : CategoricalPullback (ModuleCat.extendScalars S.toA) (ModuleCat.extendScalars S.fromAprime)) :
    fiber_product_ambient_product S X ⟶
      (ModuleCat.restrictScalars S.bprimeToAprime).obj X.snd :=
  Limits.prod.snd

/-- Helper for Lemma 15.7.4: the explicit ambient difference map whose kernel realizes the
canonical fibre-product module for a surjective pullback situation. -/
private abbrev fiber_product_ambient_difference
    {B₀ A₀ A₀' : Type u}
    [CommRing B₀] [CommRing A₀] [CommRing A₀']
    (S : SurjectiveRingPullbackSituation B₀ A₀ A₀')
    (X : CategoricalPullback (ModuleCat.extendScalars S.toA) (ModuleCat.extendScalars S.fromAprime)) :
    fiber_product_ambient_product S X ⟶
      (ModuleCat.restrictScalars (S.fromAprime.comp S.bprimeToAprime)).obj
        ((ModuleCat.extendScalars S.fromAprime).obj X.snd) :=
  fiber_product_ambient_fst S X ≫
      module_tensor_pullback_left_map
        S.bprimeToB
        S.bprimeToAprime
        S.comm
        X -
    fiber_product_ambient_snd S X ≫
      module_tensor_pullback_right_map
        S.bprimeToAprime
        X

/-- Helper for Lemma 15.7.4: evaluating the ambient difference map subtracts the left and right
comparison maps on the two ambient coordinates. -/
private theorem fiber_product_ambient_difference_apply
    {B₀ A₀ A₀' : Type u}
    [CommRing B₀] [CommRing A₀] [CommRing A₀']
    (S : SurjectiveRingPullbackSituation B₀ A₀ A₀')
    (X : CategoricalPullback (ModuleCat.extendScalars S.toA) (ModuleCat.extendScalars S.fromAprime))
    (z : fiber_product_ambient_product S X) :
    fiber_product_ambient_difference S X z =
      module_tensor_pullback_left_map
          S.bprimeToB
          S.bprimeToAprime
          S.comm
          X
          ((fiber_product_ambient_fst S X) z) -
        module_tensor_pullback_right_map
          S.bprimeToAprime
          X
          ((fiber_product_ambient_snd S X) z) := by
  rfl

/-- Helper for Lemma 15.7.4: the first pullback projection of the tensor comparison map is the
canonical map `D' → D`. -/
private theorem tensorPullbackComparison_fst
    (S : Situation) :
    S.tensorPullbackComparison ≫
        pullback.fst (CommRingCat.ofHom S.dToC) (CommRingCat.ofHom S.cprimeToC) =
      CommRingCat.ofHom S.dprimeToD := by
  -- The comparison morphism is the universal pullback lift of the two tensor-square maps.
  simpa [FiberProductBaseChangeSituation.tensorPullbackComparison] using
    (pullback.lift_fst
      (CommRingCat.ofHom S.dprimeToD)
      (CommRingCat.ofHom S.dprimeToCPrime)
      (by simpa using S.tensorSquare.w))

/-- Helper for Lemma 15.7.4: the second pullback projection of the tensor comparison map is the
canonical map `D' → C'`. -/
private theorem tensorPullbackComparison_snd
    (S : Situation) :
    S.tensorPullbackComparison ≫
        pullback.snd (CommRingCat.ofHom S.dToC) (CommRingCat.ofHom S.cprimeToC) =
      CommRingCat.ofHom S.dprimeToCPrime := by
  -- The same universal property identifies the second projection with `D' → C'`.
  simpa [FiberProductBaseChangeSituation.tensorPullbackComparison] using
    (pullback.lift_snd
      (CommRingCat.ofHom S.dprimeToD)
      (CommRingCat.ofHom S.dprimeToCPrime)
      (by simpa using S.tensorSquare.w))

/-- Helper for Lemma 15.7.4: Lemma `15.6.7` applied to the tensor pullback situation gives
finiteness of the fibre-product module over the canonical pullback ring `D ×_C C'`. -/
private theorem tensor_pullback_fiber_product_finite
    (S : Situation)
    (X : S.relativeModuleCategory)
    (hfst : Module.Finite S.D X.fst)
    (hsnd : Module.Finite S.CPrime X.snd) :
    Module.Finite (tensorPullbackSituation S).Bprime
      ((tensorPullbackFiberProductFunctor S).obj X) := by
  -- Apply the owner finiteness theorem to the surjective pullback situation defined by the tensor
  -- square `D → C`, `C' → C`.
  exact surjectiveRingPullbackModuleFiberProduct_finite
    (tensorPullbackSituation S) X hfst hsnd

/-- Helper for Lemma 15.7.4: once the comparison map `D' → D ×_C C'` is surjective, the
canonical pullback ring is finite over `D'`. -/
private theorem tensor_pullback_ring_finite_of_surjective
    (S : Situation)
    (hsurj : Function.Surjective S.tensorPullbackComparison.hom) :
    let _ : Algebra Dp (tensorPullbackSituation S).Bprime := S.tensorPullbackComparison.hom.toAlgebra
    Module.Finite Dp (tensorPullbackSituation S).Bprime := by
  let _ : Algebra Dp (tensorPullbackSituation S).Bprime := S.tensorPullbackComparison.hom.toAlgebra
  -- A surjective algebra map makes the target ring a finite module over the source ring.
  exact Module.Finite.of_surjective (Algebra.linearMap Dp (tensorPullbackSituation S).Bprime) hsurj

/-- Helper for Lemma 15.7.4: multiplying an element of `D'` by the image of a pullback element
maps to the corresponding pure tensor in `D = D' ⊗[B'] B`. -/
/-- Helper for Lemma 15.7.4: the `D`-side tensor factor map agrees with the original base-change
map `B' → B` after composing with `D' → D`. -/
private theorem dprimeToD_comp_bprimeToDp
    (S : Situation) :
    S.dprimeToD.comp S.bprimeToDp = S.bToD.comp S.bprimeToB := by
  -- Both composites are the two canonical maps from `B'` into `D' ⊗[B'] B`.
  ext z
  change
    (((Algebra.TensorProduct.includeLeft : Dp →ₐ[S.Bprime] S.D).toRingHom.comp
      (algebraMap S.Bprime Dp)) z) =
      (((Algebra.TensorProduct.includeRight : B →ₐ[S.Bprime] S.D).toRingHom.comp
        (algebraMap S.Bprime B)) z)
  simpa using congrArg (fun f : S.Bprime →+* S.D ↦ f z)
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap :
      ((Algebra.TensorProduct.includeLeft : Dp →ₐ[S.Bprime] S.D).toRingHom.comp
          (algebraMap S.Bprime Dp)) =
        ((Algebra.TensorProduct.includeRight : B →ₐ[S.Bprime] S.D).toRingHom.comp
          (algebraMap S.Bprime B)))

/-- Helper for Lemma 15.7.4: multiplying an element of `D'` by the image of a pullback element
maps to the corresponding pure tensor in `D = D' ⊗[B'] B`. -/
private theorem dprimeToD_mul_bprimeToDp
    (S : Situation)
    (x : Dp)
    (z : S.Bprime) :
    S.dprimeToD (x * S.bprimeToDp z) = (x ⊗ₜ[S.Bprime] S.bprimeToB z : S.D) := by
  calc
    S.dprimeToD (x * S.bprimeToDp z)
      = S.dprimeToD x * S.dprimeToD (S.bprimeToDp z) := by
          rw [map_mul]
    _ = ((x ⊗ₜ[S.Bprime] (1 : B) : S.D) * (1 ⊗ₜ[S.Bprime] S.bprimeToB z : S.D)) := by
          congr 1
          · rfl
          · simpa using congrArg (fun f : S.Bprime →+* S.D ↦ f z) (dprimeToD_comp_bprimeToDp S)
    _ = (x ⊗ₜ[S.Bprime] S.bprimeToB z : S.D) := by
          simp [tmul_mul_tmul]

/-- Helper for Lemma 15.7.4: multiplying an element of `D'` by the image of a pullback element
maps to the corresponding pure tensor in `C' = D' ⊗[B'] A'`. -/
private theorem dprimeToCPrime_mul_bprimeToDp
    (S : Situation)
    (x : Dp)
    (z : S.Bprime) :
    S.dprimeToCPrime (x * S.bprimeToDp z) = (x ⊗ₜ[S.Bprime] S.bprimeToAprime z : S.CPrime) := by
  calc
    S.dprimeToCPrime (x * S.bprimeToDp z)
      = S.dprimeToCPrime x * S.dprimeToCPrime (S.bprimeToDp z) := by
          rw [map_mul]
    _ = ((x ⊗ₜ[S.Bprime] (1 : A') : S.CPrime) * (1 ⊗ₜ[S.Bprime] S.bprimeToAprime z : S.CPrime)) := by
          congr 1
          · rfl
          · simpa using congrArg (fun f : S.Bprime →+* S.CPrime ↦ f z)
              (dprimeToCPrime_comp_bprimeToDp S)
    _ = (x ⊗ₜ[S.Bprime] S.bprimeToAprime z : S.CPrime) := by
          simp [tmul_mul_tmul]

/-- Helper for Lemma 15.7.4: an element of `ker(A' → A)` lifts to an element of `ker(B' → B)` in
the original pullback ring. -/
private theorem pullback_kernel_element_lift
    (S : Situation)
    (t : RingHom.ker S.fromAprime) :
    ∃ s : RingHom.ker S.bprimeToB, (S.bprimeToAprime s : A') = t := by
  have hpb :=
    CategoryTheory.Functor.map_isPullback
      (F := forget CommRingCat)
      S.toSurjectiveRingPullbackSituation.isPullback
  obtain ⟨s, hsB, hsA⟩ :=
    CategoryTheory.Limits.Types.exists_of_isPullback hpb 0 t.1 (by simpa using t.2.symm)
  refine ⟨⟨s, hsB⟩, ?_⟩
  exact hsA

/-- Helper for Lemma 15.7.4: an element of `C'` mapping to zero in `C` lifts to an element of
`D'` whose image in `D` is zero. -/
private theorem tensor_pullback_comparison_lift_of_target_zero
    (S : Situation)
    {δ : S.CPrime}
    (hδ : S.cprimeToC δ = 0) :
    ∃ x : Dp, S.dprimeToD x = 0 ∧ S.dprimeToCPrime x = δ := by
  let K : Ideal A' := RingHom.ker S.fromAprime
  have hker_eq :
      (RingHom.ker S.cprimeToC).restrictScalars S.Bprime =
        LinearMap.range
          (LinearMap.lTensor Dp (Submodule.subtype (K.restrictScalars S.Bprime))) := by
    let _ : Algebra A' A := S.fromAprime.toAlgebra
    simpa [FiberProductBaseChangeSituation.cprimeToC, K] using
      (Algebra.TensorProduct.lTensor_ker (R := S.Bprime) (A := Dp) (g := S.fromAprime)
        S.fromAprime_surjective)
  have hδ_range :
      δ ∈ LinearMap.range
        (LinearMap.lTensor Dp (Submodule.subtype (K.restrictScalars S.Bprime))) := by
    rw [← hker_eq]
    exact hδ
  rcases hδ_range with ⟨t, rfl⟩
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · exact ⟨0, by simp, by simp⟩
  · intro x k
    obtain ⟨s, hsA⟩ := pullback_kernel_element_lift S k
    refine ⟨x * S.bprimeToDp s, ?_, ?_⟩
    · rw [dprimeToD_mul_bprimeToDp]
      simp [s.2]
    · rw [dprimeToCPrime_mul_bprimeToDp]
      simp [LinearMap.lTensor_tmul, hsA]
  · intro t₁ t₂ ht₁ ht₂
    rcases ht₁ with ⟨x₁, hx₁D, hx₁C⟩
    rcases ht₂ with ⟨x₂, hx₂D, hx₂C⟩
    refine ⟨x₁ + x₂, ?_, ?_⟩
    · simp [hx₁D, hx₂D]
    · simp [hx₁C, hx₂C]

/-- Helper for Lemma 15.7.4: the comparison map `D' → D ×_C C'` is the surjective adjunction
unit from Lemma `15.6.5` for the original pullback square, specialized to the regular
`D'`-module. -/
private theorem tensorPullbackComparison_surjective
    (S : Situation) :
    Function.Surjective S.tensorPullbackComparison.hom := by
  -- Induct on the `D`-component, lifting compatible pure tensors from the original pullback
  -- square and correcting the remaining kernel term on the `C'`-side.
  have lift_compatible_pair :
      ∀ {b : B} {a' : A'}, S.toA b = S.fromAprime a' →
        ∃ z : S.Bprime, S.bprimeToB z = b ∧ S.bprimeToAprime z = a' := by
    intro b a' h
    have hpb :=
      CategoryTheory.Functor.map_isPullback
        (F := forget CommRingCat)
        S.toSurjectiveRingPullbackSituation.isPullback
    obtain ⟨z, hzB, hzA⟩ :=
      CategoryTheory.Limits.Types.exists_of_isPullback hpb b a' h
    exact ⟨z, hzB, hzA⟩
  have hsurj :
      ∀ d : S.D, ∀ c : S.CPrime, S.dToC d = S.cprimeToC c →
        ∃ x : Dp, S.dprimeToD x = d ∧ S.dprimeToCPrime x = c := by
    intro d
    refine TensorProduct.induction_on d ?_ ?_ ?_
    · intro c h
      simpa using tensor_pullback_comparison_lift_of_target_zero S (by simpa using h.symm)
    · intro x b c h
      obtain ⟨a', ha'⟩ := S.fromAprime_surjective (S.toA b)
      obtain ⟨z, hzB, hzA⟩ := lift_compatible_pair ha'.symm
      let x₀ : Dp := x * S.bprimeToDp z
      have hx₀D : S.dprimeToD x₀ = (x ⊗ₜ[S.Bprime] b : S.D) := by
        simpa [x₀, hzB] using dprimeToD_mul_bprimeToDp S x z
      have hx₀C : S.dprimeToCPrime x₀ = (x ⊗ₜ[S.Bprime] a' : S.CPrime) := by
        simpa [x₀, hzA] using dprimeToCPrime_mul_bprimeToDp S x z
      have hδ :
          S.cprimeToC (c - S.dprimeToCPrime x₀) = 0 := by
        rw [map_sub]
        have hxcomm :
            S.cprimeToC (S.dprimeToCPrime x₀) = S.dToC (S.dprimeToD x₀) := by
          simpa using congrArg (fun f : Dp →+* S.C ↦ f x₀) S.tensor_square_commutes
        rw [hxcomm, hx₀D, h, sub_self]
      obtain ⟨x₁, hx₁D, hx₁C⟩ := tensor_pullback_comparison_lift_of_target_zero S hδ
      refine ⟨x₀ + x₁, ?_, ?_⟩
      · simp [hx₀D, hx₁D]
      · simp [hx₀C, hx₁C]
    · intro d₁ d₂ hd₁ hd₂ c h
      obtain ⟨c₁, hc₁⟩ := cprimeToC_surjective S (S.dToC d₁)
      obtain ⟨x₁, hx₁D, hx₁C⟩ := hd₁ c₁ hc₁.symm
      have h₂ : S.dToC d₂ = S.cprimeToC (c - c₁) := by
        rw [map_sub]
        have hsum : S.dToC d₁ + S.dToC d₂ = S.cprimeToC c := by
          simpa [map_add] using h
        have hdiff := congrArg (fun t : S.C => t - S.dToC d₁) hsum
        simpa [hc₁, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hdiff
      obtain ⟨x₂, hx₂D, hx₂C⟩ := hd₂ (c - c₁) h₂
      refine ⟨x₁ + x₂, ?_, ?_⟩
      · simpa [FiberProductBaseChangeSituation.dprimeToD, hx₁D, hx₂D] using
          congrArg₂ (fun a b : S.D ↦ a + b) hx₁D hx₂D
      · simpa [FiberProductBaseChangeSituation.dprimeToCPrime, hx₁C, hx₂C] using
          congrArg₂ (fun a b : S.CPrime ↦ a + b) hx₁C hx₂C
  intro y
  let d : S.D :=
    (pullback.fst (CommRingCat.ofHom S.dToC) (CommRingCat.ofHom S.cprimeToC)).hom y
  let c : S.CPrime :=
    (pullback.snd (CommRingCat.ofHom S.dToC) (CommRingCat.ofHom S.cprimeToC)).hom y
  have hdc : S.dToC d = S.cprimeToC c := by
    simpa [d, c] using congrArg
      (fun k :
        pullback (CommRingCat.ofHom S.dToC) (CommRingCat.ofHom S.cprimeToC) ⟶
          CommRingCat.of S.C ↦ k.hom y)
      (pullback.condition)
  obtain ⟨x, hxD, hxC⟩ := hsurj d c hdc
  refine ⟨x, ?_⟩
  apply Subtype.ext
  simp [d, c, hxD, hxC, FiberProductBaseChangeSituation.tensorPullbackComparison]

/-- Helper for Lemma 15.7.4: after restricting scalars along `D' → D ×_C C'`, the finite
pullback-ring module remains finite over `D'`. -/
private theorem tensor_pullback_fiber_product_finite_restrictScalars
    (S : Situation)
    (X : S.relativeModuleCategory)
    (hfst : Module.Finite S.D X.fst)
    (hsnd : Module.Finite S.CPrime X.snd) :
    Module.Finite Dp
      ((ModuleCat.restrictScalars S.tensorPullbackComparison.hom).obj
        ((tensorPullbackFiberProductFunctor S).obj X)) := by
  -- First make the pullback ring finite over `D'`, then descend finiteness by restriction.
  let _ : Algebra Dp (tensorPullbackSituation S).Bprime := S.tensorPullbackComparison.hom.toAlgebra
  let _ : Module.Finite Dp (tensorPullbackSituation S).Bprime :=
    tensor_pullback_ring_finite_of_surjective S (tensorPullbackComparison_surjective S)
  let _ : Module.Finite (tensorPullbackSituation S).Bprime
      ((tensorPullbackFiberProductFunctor S).obj X) :=
    tensor_pullback_fiber_product_finite S X hfst hsnd
  exact Module.Finite.of_restrictScalars_finite Dp (tensorPullbackSituation S).Bprime
    ((tensorPullbackFiberProductFunctor S).obj X)

/-- Helper for Lemma 15.7.4: the original `D'`-side fibre product is presented as a kernel inside
an ambient product of restricted modules. -/
private abbrev relative_ambient_product
    (S : Situation)
    (X : S.relativeModuleCategory) : ModuleCat Dp :=
  Limits.prod ((ModuleCat.restrictScalars S.dprimeToD).obj X.fst)
    ((ModuleCat.restrictScalars S.dprimeToCPrime).obj X.snd)

/-- Helper for Lemma 15.7.4: the common target of the two original comparison maps. -/
private abbrev relative_ambient_target
    (S : Situation)
    (X : S.relativeModuleCategory) : ModuleCat Dp :=
  (ModuleCat.restrictScalars (S.cprimeToC.comp S.dprimeToCPrime)).obj
    ((ModuleCat.extendScalars S.cprimeToC).obj X.snd)

/-- Helper for Lemma 15.7.4: the explicit difference map whose kernel is the original
`D'`-linear fibre product. -/
private abbrev relative_ambient_difference
    (S : Situation)
    (X : S.relativeModuleCategory) :
    relative_ambient_product S X ⟶ relative_ambient_target S X :=
  Limits.prod.fst ≫
      module_tensor_pullback_left_map
        S.dprimeToD
        S.dprimeToCPrime
        S.tensor_square_commutes
        X -
    Limits.prod.snd ≫ module_tensor_pullback_right_map S.dprimeToCPrime X

/-- Helper for Lemma 15.7.4: transport between equal restricted-scalar structures is the identity
on the underlying carrier. -/
private theorem restrictScalars_eqToIso_hom_apply
    {R S : Type u}
    [CommRing R] [CommRing S]
    {f g : R →+* S}
    (hfg : f = g)
    (M : ModuleCat S)
    (x : (ModuleCat.restrictScalars f).obj M) :
    ((eqToIso (congrArg (fun h ↦ (ModuleCat.restrictScalars h).obj M) hfg)).hom) x = x := by
  -- Reduce to the reflexive equality so the scalar-transport becomes definitional.
  cases hfg
  rfl

/-- Helper for Lemma 15.7.4: on ring homs, the first pullback projection composed with the
comparison map is exactly `D' → D`. -/
private theorem tensorPullbackComparison_fst_hom
    (S : Situation) :
    S.dprimeToD = (tensorPullbackSituation S).bprimeToB.comp S.tensorPullbackComparison.hom := by
  -- Rewrite the categorical projection identity as an equality of ring homs.
  symm
  simpa [tensorPullbackSituation, SurjectiveRingPullbackSituation.bprimeToB] using
    congrArg CommRingCat.Hom.hom (tensorPullbackComparison_fst S)

/-- Helper for Lemma 15.7.4: on ring homs, the second pullback projection composed with the
comparison map is exactly `D' → C'`. -/
private theorem tensorPullbackComparison_snd_hom
    (S : Situation) :
    S.dprimeToCPrime =
      (tensorPullbackSituation S).bprimeToAprime.comp S.tensorPullbackComparison.hom := by
  -- Rewrite the categorical projection identity as an equality of ring homs.
  symm
  simpa [tensorPullbackSituation, SurjectiveRingPullbackSituation.bprimeToAprime] using
    congrArg CommRingCat.Hom.hom (tensorPullbackComparison_snd S)

/-- Helper for Lemma 15.7.4: the restricted tensor-side target module is obtained from the
original target by the canonical scalar-composition isomorphism. -/
private theorem tensorPullbackComparison_target_hom
    (S : Situation) :
    S.cprimeToC.comp S.dprimeToCPrime =
      ((tensorPullbackSituation S).fromAprime.comp (tensorPullbackSituation S).bprimeToAprime).comp
        S.tensorPullbackComparison.hom := by
  -- Compose the second projection identity with `C' → C`.
  rw [tensorPullbackComparison_snd_hom]
  rfl

/-- Helper for Lemma 15.7.4: the original ambient product is the restriction of scalars of the
tensor-pullback ambient product. -/
private noncomputable def tensor_pullback_ambient_product_restrictScalars_iso
    (S : Situation)
    (X : S.relativeModuleCategory) :
    relative_ambient_product S X ≅
      ((ModuleCat.restrictScalars S.tensorPullbackComparison.hom).obj
        (fiber_product_ambient_product (S := tensorPullbackSituation S) X)) := by
  -- The two factors differ only by composing scalars along the pullback projections.
  refine Limits.prodIso ?_ ?_
  · refine eqToIso ?_
    rw [tensorPullbackComparison_fst_hom]
  · refine eqToIso ?_
    rw [tensorPullbackComparison_snd_hom]

/-- Helper for Lemma 15.7.4: the original target module is the restriction of scalars of the
tensor-pullback target module. -/
private noncomputable def tensor_pullback_ambient_target_restrictScalars_iso
    (S : Situation)
    (X : S.relativeModuleCategory) :
    relative_ambient_target S X ≅
      ((ModuleCat.restrictScalars S.tensorPullbackComparison.hom).obj
        ((ModuleCat.restrictScalars
            ((tensorPullbackSituation S).fromAprime.comp (tensorPullbackSituation S).bprimeToAprime)).obj
          ((ModuleCat.extendScalars (tensorPullbackSituation S).fromAprime).obj X.snd))) := by
  -- The common target only changes by composing the scalar action with the comparison map.
  refine eqToIso ?_
  rw [tensorPullbackComparison_target_hom]

/-- Helper for Lemma 15.7.4: on ambient product elements, the source restriction-of-scalars
transport acts componentwise by the identity. -/
private theorem tensor_pullback_ambient_product_restrictScalars_iso_hom_apply
    (S : Situation)
    (X : S.relativeModuleCategory)
    (z : relative_ambient_product S X) :
    (tensor_pullback_ambient_product_restrictScalars_iso S X).hom z = z := by
  -- Each product component transport is definitionally the identity after reducing the scalar
  -- equalities.
  rcases z with ⟨z₁, z₂⟩
  ext <;> simp [tensor_pullback_ambient_product_restrictScalars_iso,
    restrictScalars_eqToIso_hom_apply]

/-- Helper for Lemma 15.7.4: on the ambient target module, the restriction-of-scalars
isomorphism acts as the identity on elements. -/
private theorem tensor_pullback_ambient_target_restrictScalars_iso_hom_apply
    (S : Situation)
    (X : S.relativeModuleCategory)
    (z : relative_ambient_target S X) :
    (tensor_pullback_ambient_target_restrictScalars_iso S X).hom z = z := by
  -- After reducing the scalar-transport equality, the map is definitional.
  simp [tensor_pullback_ambient_target_restrictScalars_iso,
    restrictScalars_eqToIso_hom_apply]

/-- Helper for Lemma 15.7.4: after transporting the codomain to the restricted tensor target, the
original left comparison map agrees pointwise with the tensor-pullback left map. -/
private theorem tensor_pullback_left_map_apply
    (S : Situation)
    (X : S.relativeModuleCategory)
    (n : X.fst) :
    module_tensor_pullback_left_map
        (tensorPullbackSituation S).bprimeToB
        (tensorPullbackSituation S).bprimeToAprime
        (tensorPullbackSituation S).comm
        X
        n =
      restrictScalars_comm_hom
        (tensorPullbackSituation S).bprimeToB
        (tensorPullbackSituation S).bprimeToAprime
        (tensorPullbackSituation S).toA
        (tensorPullbackSituation S).fromAprime
        (tensorPullbackSituation S).comm
        ((ModuleCat.extendScalars (tensorPullbackSituation S).fromAprime).obj X.snd)
        (X.iso.hom ((1 : S.C) ⊗ₜ[S.D] n)) := by
  -- Unfold the left comparison map in the specialized tensor-pullback square.
  let _ : Algebra S.D S.C := S.dToC.toAlgebra
  rfl

/-- Helper for Lemma 15.7.4: after transporting the codomain to the restricted tensor target, the
original right comparison map is the standard pure tensor. -/
private theorem tensor_pullback_right_map_apply
    (S : Situation)
    (X : S.relativeModuleCategory)
    (m : X.snd) :
    let _ : Algebra S.CPrime S.C := S.cprimeToC.toAlgebra
    module_tensor_pullback_right_map
        (tensorPullbackSituation S).bprimeToAprime
        X
        m =
      ((1 : S.C) ⊗ₜ[S.CPrime] m :
        (ModuleCat.extendScalars (tensorPullbackSituation S).fromAprime).obj X.snd) := by
  -- The right comparison map is the adjunction unit on the second tensor factor.
  let _ : Algebra S.CPrime S.C := S.cprimeToC.toAlgebra
  rfl

/-- Helper for Lemma 15.7.4: after transporting the codomain to the restricted tensor target, the
original left comparison map agrees pointwise with the tensor-pullback left map. -/
private theorem relative_left_map_target_apply
    (S : Situation)
    (X : S.relativeModuleCategory)
    (n : X.fst) :
    (tensor_pullback_ambient_target_restrictScalars_iso S X).hom
        (module_tensor_pullback_left_map
          S.dprimeToD
          S.dprimeToCPrime
          S.tensor_square_commutes
          X
          n) =
      module_tensor_pullback_left_map
        (tensorPullbackSituation S).bprimeToB
        (tensorPullbackSituation S).bprimeToAprime
        (tensorPullbackSituation S).comm
        X
        n := by
  -- Both maps send `n` to the same standard tensor generator in the common restricted target.
  rw [tensor_pullback_left_map_apply]
  let _ : Algebra S.D S.C := S.dToC.toAlgebra
  simp [module_tensor_pullback_left_map,
    tensor_pullback_ambient_target_restrictScalars_iso,
    tensorPullbackComparison_target_hom,
    restrictScalars_eqToIso_hom_apply]

/-- Helper for Lemma 15.7.4: after transporting the codomain to the restricted tensor target, the
original right comparison map agrees pointwise with the tensor-pullback right map. -/
private theorem relative_right_map_target_apply
    (S : Situation)
    (X : S.relativeModuleCategory)
    (m : X.snd) :
    (tensor_pullback_ambient_target_restrictScalars_iso S X).hom
        (module_tensor_pullback_right_map S.dprimeToCPrime X m) =
      module_tensor_pullback_right_map
        (tensorPullbackSituation S).bprimeToAprime
        X
        m := by
  -- Both right maps are the same pure tensor `1 ⊗ m` after the target transport is removed.
  rw [tensor_pullback_right_map_apply]
  let _ : Algebra S.CPrime S.C := S.cprimeToC.toAlgebra
  simp [module_tensor_pullback_right_map,
    tensor_pullback_ambient_target_restrictScalars_iso,
    tensorPullbackComparison_target_hom,
    restrictScalars_eqToIso_hom_apply]

/-- Helper for Lemma 15.7.4: after rewriting both ambient objects by restriction of scalars, the
original difference map matches the tensor-pullback difference map. -/
private theorem tensor_pullback_ambient_difference_restrictScalars
    (S : Situation)
    (X : S.relativeModuleCategory) :
    relative_ambient_difference S X ≫ (tensor_pullback_ambient_target_restrictScalars_iso S X).hom =
      (tensor_pullback_ambient_product_restrictScalars_iso S X).hom ≫
        (ModuleCat.restrictScalars S.tensorPullbackComparison.hom).map
          (fiber_product_ambient_difference (S := tensorPullbackSituation S) X) := by
  -- Evaluate both sides on an ambient pair `(n, m)` and compare the two components pointwise
  -- after transporting the source and target by the restriction-of-scalars isomorphisms.
  apply ModuleCat.hom_injective
  ext z
  rcases z with ⟨n, m⟩
  simp [relative_ambient_difference, fiber_product_ambient_difference_apply,
    tensor_pullback_ambient_product_restrictScalars_iso_hom_apply,
    tensor_pullback_ambient_target_restrictScalars_iso_hom_apply,
    relative_left_map_target_apply, relative_right_map_target_apply]

/-- Helper for Lemma 15.7.4: the original fibre-product module over `D'` is the restriction of
scalars of the canonical fibre-product module over the pullback ring `D ×_C C'`. -/
private noncomputable theorem fiber_product_restrictScalars_iso
    (S : Situation)
    (X : S.relativeModuleCategory) :
    (fiberProductFunctor.obj X) ≅
      ((ModuleCat.restrictScalars S.tensorPullbackComparison.hom).obj
        ((tensorPullbackFiberProductFunctor S).obj X)) := by
  -- Compare the two kernel objects via the ambient product and target isomorphisms, then use that
  -- restriction of scalars preserves kernels.
  exact
    (kernel.mapIso
      (relative_ambient_difference S X)
      ((ModuleCat.restrictScalars S.tensorPullbackComparison.hom).map
        (fiber_product_ambient_difference (S := tensorPullbackSituation S) X))
      (tensor_pullback_ambient_product_restrictScalars_iso S X)
      (tensor_pullback_ambient_target_restrictScalars_iso S X)
      (tensor_pullback_ambient_difference_restrictScalars S X)) ≪≫
      (PreservesKernel.iso
        (ModuleCat.restrictScalars S.tensorPullbackComparison.hom)
        (fiber_product_ambient_difference (S := tensorPullbackSituation S) X)).symm

-- Proof sketch: apply Lemma `15.6.7` to the canonical surjective pullback situation attached to
-- the tensor square. The comparison map `D' → D ×_C C'` is surjective by Lemma `15.6.5` applied
-- to the original pullback square `B' → B`, `B' → A'`, `B → A`, `A' → A`, and then finiteness
-- descends along that surjection.
/-- Lemma 15.7.4: in the base-changed fibre-product situation of Lemma `15.7.2`, if `N` is finite
over `D` and `M'` is finite over `C'`, then the fibre-product module `N ×_φ M'` is finite over
`D'`. -/
theorem relativeModuleFiberProduct_finite
    (X : S.relativeModuleCategory)
    (hfst : Module.Finite S.D X.fst)
    (hsnd : Module.Finite S.CPrime X.snd) :
    Module.Finite Dp ((fiberProductFunctor).obj X) := by
  -- Proof comment: the source proof finishes by transporting the already-known finite pullback-ring
  -- module across the explicit kernel identification.
  let _ : Module.Finite Dp
      ((ModuleCat.restrictScalars S.tensorPullbackComparison.hom).obj
        ((tensorPullbackFiberProductFunctor S).obj X)) :=
    tensor_pullback_fiber_product_finite_restrictScalars S X hfst hsnd
  exact Module.Finite.equiv (fiber_product_restrictScalars_iso S X).symm.toLinearEquiv

end FiberProductBaseChangeSituation

end
