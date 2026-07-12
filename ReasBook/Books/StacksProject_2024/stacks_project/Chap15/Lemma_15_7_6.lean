import Mathlib
import StacksProject_2024.Chap15.Situation_15_7_1
import StacksProject_2024.Chap15.Lemma_15_5_4
import StacksProject_2024.Chap15.Lemma_15_6_2
import StacksProject_2024.Chap15.Lemma_15_6_6
import StacksProject_2024.Chap15.Lemma_15_7_5

open CategoryTheory
open CategoryTheory.Limits
open CommRingCat
open scoped TensorProduct

universe u

noncomputable section

section

variable {R S : Type u} [CommRing R] [CommRing S]

/- Domain-style sampling for Lemma 15.7.6:
- primary domain: commutative algebra of flat/finitely presented factorizations of ring maps and
  finite presentation of fibre-product modules in a tensor-base-change square;
- sampled owner declarations:
  `RingHom.Flat`,
  `RingHom.FinitePresentation`,
  `module_tensor_pullback_right_adjoint`,
  `Module.FinitePresentation`;
- best owner abstraction: the factorization hypothesis should use the canonical ring-map owners
  `g.Flat` and `h.FinitePresentation`, while the fibre-product module itself is owned by
  `module_tensor_pullback_right_adjoint`;
- primitive data: the relative pullback object `X` and a factorization `B' → P → D'`;
- derived API: finite presentation of the induced fibre-product module over `D'`.

Source/core/bridge triage:
- `source-facing`: the finite-presentation theorem for the fibre-product module;
- `core/canonical`: `RingHom.Flat`, `RingHom.FinitePresentation`,
  `Module.FinitePresentation`, and `module_tensor_pullback_right_adjoint`;
- `bridge/view`: the explicit existential factorization hypothesis on `S.bprimeToDp`. -/

section

variable {B A A' Dp : Type u}
variable [CommRing B] [CommRing A] [CommRing A'] [CommRing Dp]

namespace FiberProductBaseChangeSituation

local notation "Situation" => @FiberProductBaseChangeSituation B A A' Dp _ _ _ _
variable (S : Situation)

local notation "fiberProductFunctor" =>
  module_tensor_pullback_right_adjoint
    S.dprimeToD
    S.dprimeToCPrime
    S.tensor_square_commutes

/-- Restricting scalars along `B → D` gives the first component of a relative pullback object its
canonical `B`-module structure. -/
private instance instModuleFstOverB
    (X : S.relativeModuleCategory) : Module B X.fst :=
  Module.compHom X.fst (algebraMap B S.D)

/-- Restricting scalars along `A' → C'` gives the second component of a relative pullback object
its canonical `A'`-module structure. -/
private instance instModuleSndOverAprime
    (X : S.relativeModuleCategory) : Module A' X.snd :=
  Module.compHom X.snd (algebraMap A' S.CPrime)

/-- Helper for Lemma 15.7.6: the fibre-product module is flat over `B'` once the two pullback
components are flat over `B` and `A'`. -/
private theorem relativeModuleFiberProduct_flat_of_component_flat
    (X : S.relativeModuleCategory)
    [Module.Flat B X.fst]
    [Module.Flat A' X.snd] :
    Module.Flat S.Bprime (fiberProductFunctor.obj X) := by
  -- Proof comment: this is exactly Lemma `15.7.5` specialized to the pullback triple `X`.
  simpa [relativeFlatPullbackProperty, relativeFlatModuleProperty, fiberProductFunctor] using
    (relativeModuleFiberProduct_flat S
      (X := X)
      ⟨inferInstance, inferInstance⟩)

/-- Helper for Lemma 15.7.6: finite presentation of the two components implies that the
fibre-product module is finite over `D'`. -/
/-- Helper for Lemma 15.7.6: the map `C' → C` is surjective in every fibre-product base-change
situation. -/
private theorem cprimeToC_surjective
    (S : Situation) :
    Function.Surjective S.cprimeToC := by
  -- Proof comment: every tensor in `D' ⊗[B'] A` comes from a tensor in `D' ⊗[B'] A'` because
  -- `A' → A` is surjective in the underlying pullback situation.
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

/-- Helper for Lemma 15.7.6: the tensor square `D → C`, `C' → C` defines the surjective pullback
situation used in Lemma `15.7.4`. -/
private def tensorPullbackSituation
    (S : Situation) :
    SurjectiveRingPullbackSituation S.D S.C S.CPrime where
  toA := S.dToC
  fromAprime := S.cprimeToC
  fromAprime_surjective := cprimeToC_surjective S

local notation "tensorPullbackFiberProductFunctor" =>
  (@module_tensor_pullback_right_adjoint
    S.D
    S.C
    S.CPrime
    (tensorPullbackSituation S).Bprime
    _ _ _ _
    (tensorPullbackSituation S).bprimeToB
    (tensorPullbackSituation S).bprimeToAprime
    (tensorPullbackSituation S).comm : S.relativeModuleCategory ⥤
      ModuleCat (tensorPullbackSituation S).Bprime)

/-- Helper for Lemma 15.7.6: the first projection of the tensor pullback comparison recovers the
canonical map `D' → D`. -/
private theorem tensorPullbackComparison_fst
    (S : Situation) :
    S.tensorPullbackComparison ≫
        pullback.fst (CommRingCat.ofHom S.dToC) (CommRingCat.ofHom S.cprimeToC) =
      CommRingCat.ofHom S.dprimeToD := by
  -- Proof comment: the comparison map is the universal pullback lift of the two tensor-square
  -- structure maps.
  simpa [FiberProductBaseChangeSituation.tensorPullbackComparison] using
    (pullback.lift_fst
      (CommRingCat.ofHom S.dprimeToD)
      (CommRingCat.ofHom S.dprimeToCPrime)
      (by simpa using S.tensorSquare.w))

/-- Helper for Lemma 15.7.6: the second projection of the tensor pullback comparison recovers the
canonical map `D' → C'`. -/
private theorem tensorPullbackComparison_snd
    (S : Situation) :
    S.tensorPullbackComparison ≫
        pullback.snd (CommRingCat.ofHom S.dToC) (CommRingCat.ofHom S.cprimeToC) =
      CommRingCat.ofHom S.dprimeToCPrime := by
  -- Proof comment: the same pullback universal property identifies the second projection.
  simpa [FiberProductBaseChangeSituation.tensorPullbackComparison] using
    (pullback.lift_snd
      (CommRingCat.ofHom S.dprimeToD)
      (CommRingCat.ofHom S.dprimeToCPrime)
      (by simpa using S.tensorSquare.w))

/-- Helper for Lemma 15.7.6: the tensor-side fibre product is finite over the pullback ring once
its two components are finite. -/
private theorem tensor_pullback_fiber_product_finite
    (S : Situation)
    (X : S.relativeModuleCategory)
    (hfst : Module.Finite S.D X.fst)
    (hsnd : Module.Finite S.CPrime X.snd) :
    Module.Finite (tensorPullbackSituation S).Bprime
      (tensorPullbackFiberProductFunctor.obj X) := by
  -- Proof comment: this is the owner theorem from Lemma `15.6.7` applied to the tensor-square
  -- pullback situation attached to `S`.
  exact surjectiveRingPullbackModuleFiberProduct_finite
    (tensorPullbackSituation S) X hfst hsnd

/-- Helper for Lemma 15.7.6: the pullback ring `D ×_C C'` is finite over `D'` once the comparison
map is surjective. -/
private theorem tensor_pullback_ring_finite_of_surjective
    (S : Situation)
    (hsurj : Function.Surjective S.tensorPullbackComparison.hom) :
    let _ : Algebra Dp (tensorPullbackSituation S).Bprime := S.tensorPullbackComparison.hom.toAlgebra
    Module.Finite Dp (tensorPullbackSituation S).Bprime := by
  let _ : Algebra Dp (tensorPullbackSituation S).Bprime := S.tensorPullbackComparison.hom.toAlgebra
  -- Proof comment: a surjective algebra map makes the target ring a finite module over the
  -- source ring.
  exact Module.Finite.of_surjective (Algebra.linearMap Dp (tensorPullbackSituation S).Bprime) hsurj

/-- Helper for Lemma 15.7.6: the tensor pullback comparison is the surjective adjunction unit from
Lemma `15.6.5` specialized to the regular `D'`-module. -/
private theorem tensorPullbackComparison_surjective
    (S : Situation) :
    Function.Surjective S.tensorPullbackComparison.hom := by
  -- Proof comment: this is the same surjective unit map used in Lemma `15.7.4`.
  simpa [FiberProductBaseChangeSituation.tensorPullbackComparison] using
    surjectiveRingPullbackModuleAdjunctionMap_surjective
      S.toSurjectiveRingPullbackSituation
      (ModuleCat.of S.Bprime Dp)

/-- Helper for Lemma 15.7.6: after restricting scalars along the comparison map, the tensor-side
fibre product remains finite over `D'`. -/
private theorem tensor_pullback_fiber_product_finite_restrictScalars
    (S : Situation)
    (X : S.relativeModuleCategory)
    (hfst : Module.Finite S.D X.fst)
    (hsnd : Module.Finite S.CPrime X.snd) :
    Module.Finite Dp
      ((ModuleCat.restrictScalars S.tensorPullbackComparison.hom).obj
        (tensorPullbackFiberProductFunctor.obj X)) := by
  -- Proof comment: make the pullback ring finite over `D'`, then descend finiteness by scalar
  -- restriction.
  let _ : Algebra Dp (tensorPullbackSituation S).Bprime := S.tensorPullbackComparison.hom.toAlgebra
  let _ : Module.Finite Dp (tensorPullbackSituation S).Bprime :=
    tensor_pullback_ring_finite_of_surjective S (tensorPullbackComparison_surjective S)
  let _ : Module.Finite (tensorPullbackSituation S).Bprime
      (tensorPullbackFiberProductFunctor.obj X) :=
    tensor_pullback_fiber_product_finite S X hfst hsnd
  exact Module.Finite.of_restrictScalars_finite Dp (tensorPullbackSituation S).Bprime
    (tensorPullbackFiberProductFunctor.obj X)

/-- Helper for Lemma 15.7.6: the ambient product in the original `D'`-linear fibre-product
construction. -/
private abbrev relative_ambient_product
    (S : Situation)
    (X : S.relativeModuleCategory) : ModuleCat Dp :=
  Limits.prod ((ModuleCat.restrictScalars S.dprimeToD).obj X.fst)
    ((ModuleCat.restrictScalars S.dprimeToCPrime).obj X.snd)

/-- Helper for Lemma 15.7.6: the common target of the two comparison maps defining the original
`D'`-linear fibre product. -/
private abbrev relative_ambient_target
    (S : Situation)
    (X : S.relativeModuleCategory) : ModuleCat Dp :=
  (ModuleCat.restrictScalars (S.cprimeToC.comp S.dprimeToCPrime)).obj
    ((ModuleCat.extendScalars S.cprimeToC).obj X.snd)

/-- Helper for Lemma 15.7.6: the explicit ambient difference map whose kernel is the original
fibre-product module. -/
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

/-- Helper for Lemma 15.7.6: transport between equal restricted-scalar structures acts as the
identity on the underlying carrier. -/
private theorem restrictScalars_eqToIso_hom_apply
    {R S : Type u}
    [CommRing R] [CommRing S]
    {f g : R →+* S}
    (hfg : f = g)
    (M : ModuleCat S)
    (x : (ModuleCat.restrictScalars f).obj M) :
    ((eqToIso (congrArg (fun h ↦ (ModuleCat.restrictScalars h).obj M) hfg)).hom) x = x := by
  -- Proof comment: after reducing to the reflexive equality, the transport becomes definitional.
  cases hfg
  rfl

/-- Helper for Lemma 15.7.6: on ring homs, the first pullback projection composed with the
comparison map is exactly `D' → D`. -/
private theorem tensorPullbackComparison_fst_hom
    (S : Situation) :
    S.dprimeToD = (tensorPullbackSituation S).bprimeToB.comp S.tensorPullbackComparison.hom := by
  -- Proof comment: this is the ring-hom form of the first projection identity above.
  symm
  simpa [tensorPullbackSituation, SurjectiveRingPullbackSituation.bprimeToB] using
    congrArg CommRingCat.Hom.hom (tensorPullbackComparison_fst S)

/-- Helper for Lemma 15.7.6: on ring homs, the second pullback projection composed with the
comparison map is exactly `D' → C'`. -/
private theorem tensorPullbackComparison_snd_hom
    (S : Situation) :
    S.dprimeToCPrime =
      (tensorPullbackSituation S).bprimeToAprime.comp S.tensorPullbackComparison.hom := by
  -- Proof comment: this is the corresponding ring-hom identity for the second projection.
  symm
  simpa [tensorPullbackSituation, SurjectiveRingPullbackSituation.bprimeToAprime] using
    congrArg CommRingCat.Hom.hom (tensorPullbackComparison_snd S)

/-- Helper for Lemma 15.7.6: the restricted tensor-side target agrees with the original target up
to the canonical scalar-composition isomorphism. -/
private theorem tensorPullbackComparison_target_hom
    (S : Situation) :
    S.cprimeToC.comp S.dprimeToCPrime =
      ((tensorPullbackSituation S).fromAprime.comp (tensorPullbackSituation S).bprimeToAprime).comp
        S.tensorPullbackComparison.hom := by
  -- Proof comment: compose the second projection identity with `C' → C`.
  rw [tensorPullbackComparison_snd_hom]
  rfl

/-- Helper for Lemma 15.7.6: the original ambient product is the restriction of scalars of the
tensor-pullback ambient product. -/
private noncomputable def tensor_pullback_ambient_product_restrictScalars_iso
    (S : Situation)
    (X : S.relativeModuleCategory) :
    relative_ambient_product S X ≅
      ((ModuleCat.restrictScalars S.tensorPullbackComparison.hom).obj
        (fiber_product_ambient_product (S := tensorPullbackSituation S) X)) := by
  -- Proof comment: both factors are obtained by restricting scalars from the two tensor-side
  -- components using the projection identities above.
  refine Limits.prodIso ?_ ?_
  · refine eqToIso ?_
    rw [tensorPullbackComparison_fst_hom]
  · refine eqToIso ?_
    rw [tensorPullbackComparison_snd_hom]

/-- Helper for Lemma 15.7.6: on ambient pairs, the product restriction-of-scalars isomorphism acts
as the identity on the underlying carrier. -/
private theorem tensor_pullback_ambient_product_restrictScalars_iso_hom_apply
    (S : Situation)
    (X : S.relativeModuleCategory)
    (z : relative_ambient_product S X) :
    (tensor_pullback_ambient_product_restrictScalars_iso S X).hom z = z := by
  -- Proof comment: each product component transport is definitional after the projection
  -- equalities are reduced.
  rcases z with ⟨z₁, z₂⟩
  ext <;> simp [tensor_pullback_ambient_product_restrictScalars_iso,
    restrictScalars_eqToIso_hom_apply]

/-- Helper for Lemma 15.7.6: the original ambient target is the restriction of scalars of the
tensor-pullback ambient target. -/
private noncomputable def tensor_pullback_ambient_target_restrictScalars_iso
    (S : Situation)
    (X : S.relativeModuleCategory) :
    relative_ambient_target S X ≅
      ((ModuleCat.restrictScalars S.tensorPullbackComparison.hom).obj
        (fiber_product_ambient_target (S := tensorPullbackSituation S) X)) := by
  -- Proof comment: the target restriction is again just scalar-composition along the comparison
  -- map.
  refine eqToIso ?_
  rw [tensorPullbackComparison_target_hom]

/-- Helper for Lemma 15.7.6: on the ambient target module, the restriction-of-scalars isomorphism
acts as the identity on elements. -/
private theorem tensor_pullback_ambient_target_restrictScalars_iso_hom_apply
    (S : Situation)
    (X : S.relativeModuleCategory)
    (z : relative_ambient_target S X) :
    (tensor_pullback_ambient_target_restrictScalars_iso S X).hom z = z := by
  -- Proof comment: after reducing the scalar-transport equality, the map is definitional.
  simp [tensor_pullback_ambient_target_restrictScalars_iso,
    restrictScalars_eqToIso_hom_apply]

/-- Helper for Lemma 15.7.6: in the tensor pullback square, the left comparison map evaluates to
the standard tensor expression coming from the first component. -/
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
        (S := tensorPullbackSituation S)
        (tensorPullbackSituation S).bprimeToB
        (tensorPullbackSituation S).bprimeToAprime
        (tensorPullbackSituation S).comm
        ((ModuleCat.extendScalars (tensorPullbackSituation S).fromAprime).obj X.snd)
        (X.iso.hom ((1 : S.C) ⊗ₜ[S.D] n)) := by
  -- Proof comment: this is just the unfolded definition of the left comparison map in the
  -- specialized tensor square.
  let _ : Algebra S.D S.C := S.dToC.toAlgebra
  rfl

/-- Helper for Lemma 15.7.6: in the tensor pullback square, the right comparison map is the
standard pure tensor on the second component. -/
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
  -- Proof comment: the right comparison map is the adjunction unit on the second tensor factor.
  let _ : Algebra S.CPrime S.C := S.cprimeToC.toAlgebra
  rfl

/-- Helper for Lemma 15.7.6: after transporting the codomain to the restricted tensor target, the
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
  -- Proof comment: both maps send `n` to the same standard tensor generator in the common target.
  rw [tensor_pullback_left_map_apply]
  let _ : Algebra S.D S.C := S.dToC.toAlgebra
  simp [module_tensor_pullback_left_map,
    tensor_pullback_ambient_target_restrictScalars_iso,
    tensorPullbackComparison_target_hom,
    restrictScalars_eqToIso_hom_apply,
    ModuleCat.restrictScalarsComp'App_hom_apply]

/-- Helper for Lemma 15.7.6: after transporting the codomain to the restricted tensor target, the
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
  -- Proof comment: both right maps are the same pure tensor after removing the target transport.
  rw [tensor_pullback_right_map_apply]
  let _ : Algebra S.CPrime S.C := S.cprimeToC.toAlgebra
  simp [module_tensor_pullback_right_map,
    tensor_pullback_ambient_target_restrictScalars_iso,
    tensorPullbackComparison_target_hom,
    restrictScalars_eqToIso_hom_apply,
    ModuleCat.restrictScalarsComp'App_hom_apply]

/-- Helper for Lemma 15.7.6: after rewriting both ambient objects by restriction of scalars, the
original difference map matches the tensor-pullback difference map. -/
private theorem tensor_pullback_ambient_difference_restrictScalars
    (S : Situation)
    (X : S.relativeModuleCategory) :
    relative_ambient_difference S X ≫ (tensor_pullback_ambient_target_restrictScalars_iso S X).hom =
      (tensor_pullback_ambient_product_restrictScalars_iso S X).hom ≫
        (ModuleCat.restrictScalars S.tensorPullbackComparison.hom).map
          (fiber_product_ambient_difference (S := tensorPullbackSituation S) X) := by
  -- Proof comment: evaluate both sides on a pair `(n, m)` and compare the two target formulas
  -- pointwise after the two restriction-of-scalars identifications.
  apply ModuleCat.hom_injective
  ext z
  rcases z with ⟨n, m⟩
  simp [relative_ambient_difference, fiber_product_ambient_difference_apply,
    tensor_pullback_ambient_product_restrictScalars_iso_hom_apply,
    tensor_pullback_ambient_target_restrictScalars_iso_hom_apply,
    relative_left_map_target_apply, relative_right_map_target_apply]

/-- Helper for Lemma 15.7.6: the original fibre-product module over `D'` is the restriction of
scalars of the canonical tensor-pullback fibre-product module. -/
private noncomputable theorem fiber_product_restrictScalars_iso
    (S : Situation)
    (X : S.relativeModuleCategory) :
    (fiberProductFunctor.obj X) ≅
      ((ModuleCat.restrictScalars S.tensorPullbackComparison.hom).obj
        (tensorPullbackFiberProductFunctor.obj X)) := by
  -- Proof comment: compare the two kernel objects via the ambient product and target
  -- isomorphisms, then use preservation of kernels under restriction of scalars.
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

/-- Helper for Lemma 15.7.6: finite `D`- and `C'`-components already force finiteness of the
fibre-product module over `D'`. -/
private theorem relativeModuleFiberProduct_finite_of_finite
    (X : S.relativeModuleCategory)
    [Module.Finite S.D X.fst]
    [Module.Finite S.CPrime X.snd] :
    Module.Finite Dp (fiberProductFunctor.obj X) := by
  -- Proof comment: this is exactly the local `15.7.4` comparison route already built above.
  let _ : Module.Finite Dp
      ((ModuleCat.restrictScalars S.tensorPullbackComparison.hom).obj
        (tensorPullbackFiberProductFunctor.obj X)) :=
    tensor_pullback_fiber_product_finite_restrictScalars S X inferInstance inferInstance
  exact Module.Finite.equiv (fiber_product_restrictScalars_iso S X).symm.toLinearEquiv

/-- Helper for Lemma 15.7.6: finite presentation of the two components implies that the
fibre-product module is finite over `D'`. -/
private theorem relativeModuleFiberProduct_finite_of_finitePresentation
    (X : S.relativeModuleCategory)
    [Module.FinitePresentation S.D X.fst]
    [Module.FinitePresentation S.CPrime X.snd] :
    Module.Finite Dp (fiberProductFunctor.obj X) := by
  -- Proof comment: finitely presented modules are finite, so the finite-component bridge applies.
  exact relativeModuleFiberProduct_finite_of_finite (S := S) X

/-- Helper for Lemma 15.7.6: a finitely presented factor map in the ring-hom sense yields the
corresponding algebra finite-presentation instance. -/
private theorem factorization_target_algebra_finitePresentation
    {P : Type u} [CommRing P]
    (h : P →+* Dp)
    (hhfp : h.FinitePresentation) :
    let _ : Algebra P Dp := h.toAlgebra
    Algebra.FinitePresentation P Dp := by
  -- Proof comment: translate the owner predicate from ring maps to the equivalent algebra form.
  simpa [AlgHom.FinitePresentation, RingHom.FinitePresentation] using hhfp

/-- Helper for Lemma 15.7.6: a finitely presented factor map admits a surjective polynomial cover
with finitely generated kernel. -/
private theorem factorization_target_polynomial_cover
    {P : Type u} [CommRing P]
    (h : P →+* Dp)
    (hhfp : h.FinitePresentation) :
    ∃ n : ℕ, ∃ β : MvPolynomial (Fin n) P →ₐ[P] Dp,
      Function.Surjective β ∧ (RingHom.ker β.toRingHom).FG := by
  let _ : Algebra P Dp := h.toAlgebra
  let _ : Algebra.FinitePresentation P Dp :=
    factorization_target_algebra_finitePresentation (Dp := Dp) h hhfp
  -- Proof comment: unpack the standard polynomial presentation attached to finite presentation.
  obtain ⟨n, β, hβ, hkerβ⟩ := (inferInstance : Algebra.FinitePresentation P Dp).out
  exact ⟨n, β, hβ, hkerβ⟩

/-- Helper for Lemma 15.7.6: after choosing a polynomial cover of the finitely presented factor,
the new base ring is still flat over `B'`. -/
private theorem factorization_polynomial_cover_flat
    {P : Type u} [CommRing P]
    (g : S.Bprime →+* P)
    (hgflat : g.Flat)
    (n : ℕ) :
    ((algebraMap P (MvPolynomial (Fin n) P)).toRingHom.comp g).Flat := by
  let _ : Algebra S.Bprime P := g.toAlgebra
  let _ : Algebra S.Bprime (MvPolynomial (Fin n) P) :=
    ((algebraMap P (MvPolynomial (Fin n) P)).toRingHom.comp g).toAlgebra
  -- Proof comment: polynomial algebras are free over the coefficient ring, so flatness
  -- composes from `B' → P` to `B' → P[x₁, ..., xₙ]`.
  simpa [RingHom.Flat] using (inferInstance : Module.Flat S.Bprime (MvPolynomial (Fin n) P))

/-- Helper for Lemma 15.7.6: the chosen polynomial cover still factors the original map
`B' → D'` after composing with `B' → P`. -/
private theorem polynomial_cover_refines_factorization
    {P : Type u} [CommRing P]
    (g : S.Bprime →+* P)
    (h : P →+* Dp)
    (n : ℕ)
    (β : MvPolynomial (Fin n) P →ₐ[P] Dp)
    (hcomp : S.bprimeToDp = h.comp g) :
    S.bprimeToDp =
      β.toRingHom.comp ((algebraMap P (MvPolynomial (Fin n) P)).toRingHom.comp g) := by
  -- Proof comment: the polynomial cover refines `h`, and `h` itself already refines
  -- `S.bprimeToDp` by hypothesis.
  ext b
  rw [hcomp]
  change h (g b) = β (algebraMap P (MvPolynomial (Fin n) P) (g b))
  symm
  simpa using β.commutes (g b)

/-- Helper for Lemma 15.7.6: tensoring a surjective left algebra map with the identity on the
right stays surjective. -/
private theorem tensorProduct_map_surjective_of_left_surjective
    {R S₁ S₂ T : Type u}
    [CommRing R] [CommRing S₁] [CommRing S₂] [CommRing T]
    [Algebra R S₁] [Algebra R S₂] [Algebra R T]
    (f : S₁ →ₐ[R] S₂)
    (hf : Function.Surjective f) :
    Function.Surjective
      ((Algebra.TensorProduct.map f (AlgHom.id R T)).toRingHom :
        S₁ ⊗[R] T →+* S₂ ⊗[R] T) := by
  -- Proof comment: every pure tensor lifts by surjectivity of the left factor map, and additive
  -- generation of the tensor product finishes the argument.
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · exact ⟨0, by simp⟩
  · intro s₂ t
    rcases hf s₂ with ⟨s₁, rfl⟩
    exact ⟨s₁ ⊗ₜ[R] t, rfl⟩
  · intro z₁ z₂ hz₁ hz₂
    rcases hz₁ with ⟨w₁, rfl⟩
    rcases hz₂ with ⟨w₂, rfl⟩
    exact ⟨w₁ + w₂, by simp⟩

/-- Helper for Lemma 15.7.6: tensoring the polynomial-cover map with the identity on `B`, `A'`,
and `A` gives the four structural comparison identities between the auxiliary flat situation over
`Q` and the original situation over `D'`. -/
private theorem polynomial_cover_comparison_package
    {Q : Type u} [CommRing Q]
    (bprimeToQ : S.Bprime →+* Q)
    (βBprime : Q →ₐ[S.Bprime] Dp) :
    let T : @FiberProductBaseChangeSituation B A A' Q _ _ _ _ where
      toSurjectiveRingPullbackSituation := S.toSurjectiveRingPullbackSituation
      bprimeToDp := bprimeToQ
    let δD : T.D →+* S.D :=
      (Algebra.TensorProduct.map βBprime (AlgHom.id S.Bprime B)).toRingHom
    let δCPrime : T.CPrime →+* S.CPrime :=
      (Algebra.TensorProduct.map βBprime (AlgHom.id S.Bprime A')).toRingHom
    let δC : T.C →+* S.C :=
      (Algebra.TensorProduct.map βBprime (AlgHom.id S.Bprime A)).toRingHom
    δD.comp T.bToD = S.bToD ∧
      δCPrime.comp T.aprimeToCPrime = S.aprimeToCPrime ∧
      δC.comp T.dToC = S.dToC.comp δD ∧
      δC.comp T.cprimeToC = S.cprimeToC.comp δCPrime := by
  -- Proof comment: each comparison is the direct tensor-product map induced by `βBprime`; on the
  -- `B` and `A'` legs nothing changes, and the two routes into `C` agree by evaluation on pure
  -- tensors.
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext b
    rfl
  · ext a'
    rfl
  · ext z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · rfl
    · intro q b
      rfl
    · intro z₁ z₂ hz₁ hz₂
      simp [hz₁, hz₂]
  · ext z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · rfl
    · intro q a'
      rfl
    · intro z₁ z₂ hz₁ hz₂
      simp [hz₁, hz₂]

/-- Helper for Lemma 15.7.6: finite presentation over a surjective polynomial cover descends to
the target ring after restricting scalars along the cover map. -/
private theorem finitePresentation_of_surjective_polynomial_cover_restrictScalars
    {P : Type u} [CommRing P]
    {M : Type u} [AddCommGroup M] [Module Dp M]
    (n : ℕ)
    (β : MvPolynomial (Fin n) P →ₐ[P] Dp)
    (hβ : Function.Surjective β)
    (hPM :
      let Q := MvPolynomial (Fin n) P
      let _ : Module Q M := Module.compHom M β.toRingHom
      Module.FinitePresentation Q M) :
    Module.FinitePresentation Dp M := by
  let Q := MvPolynomial (Fin n) P
  letI : Algebra Q Dp := β.toAlgebra
  letI : Module Q M := Module.compHom M β.toRingHom
  letI : IsScalarTower Q Dp M := IsScalarTower.of_compHom Q Dp M
  letI : Algebra.FiniteType Q Dp := by
    -- Proof comment: a surjective polynomial cover exhibits the target ring as finite type over
    -- the polynomial source.
    have hβ' : Function.Surjective (algebraMap Q Dp) := by
      change Function.Surjective β
      simpa using hβ
    rw [← RingHom.finiteType_algebraMap]
    exact RingHom.FiniteType.of_surjective (algebraMap Q Dp) hβ'
  letI : Module.FinitePresentation Q M := by
    -- Proof comment: restate the restricted-scalars finite-presentation hypothesis in the local
    -- notation `Q`.
    simpa [Q] using hPM
  -- Proof comment: finite presentation descends from the polynomial cover to the target ring
  -- because the target algebra is finite type over the source.
  exact Module.FinitePresentation.of_restrictScalars_finiteType Q

/-- Helper for Lemma 15.7.6: restricting scalars along a surjective polynomial cover preserves
finiteness of the target module. -/
private theorem finite_of_surjective_polynomial_cover_restrictScalars
    {P : Type u} [CommRing P]
    {M : Type u} [AddCommGroup M] [Module Dp M]
    (n : ℕ)
    (β : MvPolynomial (Fin n) P →ₐ[P] Dp)
    (hβ : Function.Surjective β)
    [Module.Finite Dp M] :
    let Q := MvPolynomial (Fin n) P
    let _ : Module Q M := Module.compHom M β.toRingHom
    Module.Finite Q M := by
  let Q := MvPolynomial (Fin n) P
  letI : Algebra Q Dp := β.toAlgebra
  letI : Module Q M := Module.compHom M β.toRingHom
  letI : IsScalarTower Q Dp M := IsScalarTower.of_compHom Q Dp M
  letI : Module.Finite Q Dp := by
    -- Proof comment: a surjective algebra map exhibits `D'` as a finite module over the
    -- polynomial-cover ring.
    exact Module.Finite.of_surjective (Algebra.linearMap Q Dp) hβ
  -- Proof comment: after making the target ring finite over the cover, finiteness of `M`
  -- descends by transitivity of finite modules.
  exact Module.Finite.trans Dp M

/-- Helper for Lemma 15.7.6: finite presentation descends along a surjective finitely presented
algebra map after restricting scalars. -/
private theorem finitePresentation_restrictScalars_of_surjective_finitePresentation
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (hf : Function.Surjective f)
    [Algebra R S] [Module.Finite R S] [Algebra.FinitePresentation R S]
    {M : Type u} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [Module.FinitePresentation S M] :
    Module.FinitePresentation R M := by
  -- Proof comment: once `S` is finite and finitely presented over `R`, the canonical
  -- finite-presentation equivalence transports the given `S`-module presentation to `R`.
  let _ : Module.Finite R S :=
    Module.Finite.of_surjective (Algebra.linearMap R S) hf
  exact
    (@Module.FinitePresentation.iff_of_finite_finitePresentation
      R S M _ _ inferInstance _ _ inferInstance inferInstance).mpr inferInstance

/-- Helper for Lemma 15.7.6: once the polynomial-cover comparison maps on the `D`- and `C'`-sides
are known to be surjective and finitely presented, finite presentation and flatness transport to
the restricted components over the auxiliary situation. -/
private theorem polynomial_cover_restricted_component_hypotheses
    {Q : Type u} [CommRing Q]
    (T : @FiberProductBaseChangeSituation B A A' Q _ _ _ _)
    (X : S.relativeModuleCategory)
    (δD : T.D →+* S.D)
    (δCPrime : T.CPrime →+* S.CPrime)
    [Module T.D X.fst]
    [Algebra T.D S.D]
    [Module.Finite T.D S.D]
    [Algebra.FinitePresentation T.D S.D]
    [Module T.CPrime X.snd]
    [Algebra T.CPrime S.CPrime]
    [Module.Finite T.CPrime S.CPrime]
    [Algebra.FinitePresentation T.CPrime S.CPrime]
    (hδDsurj : Function.Surjective δD)
    (hδCPrime_surj : Function.Surjective δCPrime)
    (hδD_comp_bToD : δD.comp T.bToD = S.bToD)
    (hδCPrime_comp_aprimeToCPrime : δCPrime.comp T.aprimeToCPrime = S.aprimeToCPrime) :
    Module.FinitePresentation T.D ((ModuleCat.restrictScalars δD).obj X.fst) ∧
      Module.FinitePresentation T.CPrime ((ModuleCat.restrictScalars δCPrime).obj X.snd) ∧
      Module.Flat B ((ModuleCat.restrictScalars δD).obj X.fst) ∧
      Module.Flat A' ((ModuleCat.restrictScalars δCPrime).obj X.snd) := by
  -- Proof comment: finite presentation descends along the surjective finitely presented
  -- comparison maps, while flatness is unchanged after rewriting the restricted scalar actions.
  constructor
  · exact finitePresentation_restrictScalars_of_surjective_finitePresentation δD hδDsurj
  constructor
  · exact
      finitePresentation_restrictScalars_of_surjective_finitePresentation
        δCPrime hδCPrime_surj
  constructor
  · simpa [hδD_comp_bToD] using (inferInstance : Module.Flat B X.fst)
  · simpa [hδCPrime_comp_aprimeToCPrime] using (inferInstance : Module.Flat A' X.snd)

/-- Helper for Lemma 15.7.6: restricting scalars of a concrete module only changes the owner
ring, not the underlying carrier. -/
private noncomputable def restrictOfIso
    {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] :
    (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S M) ≅ ModuleCat.of R M :=
  (show
      ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S M)) ≃ₗ[R] M from
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun x ↦ rfl
        right_inv := fun x ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }).toModuleIso

/-- Helper for Lemma 15.7.6: extending the `δD`-restricted `D`-component across `T.dToC`
matches restricting scalars on the already-extended `S.dToC`-side. -/
private noncomputable theorem restricted_fst_extend_iso
    {Q : Type u} [CommRing Q]
    (T : @FiberProductBaseChangeSituation B A A' Q _ _ _ _)
    (δD : T.D →+* S.D)
    (δC : T.C →+* S.C)
    (hδC_comp_dToC : δC.comp T.dToC = S.dToC.comp δD)
    (M : ModuleCat S.D) :
    (ModuleCat.extendScalars T.dToC).obj ((ModuleCat.restrictScalars δD).obj M) ≅
      (ModuleCat.restrictScalars δC).obj ((ModuleCat.extendScalars S.dToC).obj M) := by
  -- Proof comment: this is the mixed change-of-rings comparison for the `D`-component.
  -- TODO: package the square `T.D → T.C`, `T.D → S.D`, `S.D → S.C` as an explicit tensor
  -- pushout over `S.Bprime`, then compose the resulting `cancelBaseChange` bridge with
  -- `restrictOfIso` to avoid the current mixed `extendScalars`/`restrictScalars` elaboration
  -- loop.
  sorry

/-- Helper for Lemma 15.7.6: extending the `δCPrime`-restricted `C'`-component across
`T.cprimeToC` matches restricting scalars on the already-extended `S.cprimeToC`-side. -/
private noncomputable theorem restricted_snd_extend_iso
    {Q : Type u} [CommRing Q]
    (T : @FiberProductBaseChangeSituation B A A' Q _ _ _ _)
    (δCPrime : T.CPrime →+* S.CPrime)
    (δC : T.C →+* S.C)
    (hδC_comp_cprimeToC : δC.comp T.cprimeToC = S.cprimeToC.comp δCPrime)
    (M : ModuleCat S.CPrime) :
    (ModuleCat.extendScalars T.cprimeToC).obj ((ModuleCat.restrictScalars δCPrime).obj M) ≅
      (ModuleCat.restrictScalars δC).obj ((ModuleCat.extendScalars S.cprimeToC).obj M) := by
  -- Proof comment: this is the symmetric mixed change-of-rings comparison for the `C'`-side.
  -- TODO: repeat the same tensor-pushout normalization for the square
  -- `T.CPrime → T.C`, `T.CPrime → S.CPrime`, `S.CPrime → S.C`, again using `restrictOfIso`
  -- only after the pushout-side tensor module has been made explicit.
  sorry

/-- Helper for Lemma 15.7.6: the restricted `D`- and `C'`-components of `X` form a pullback
object over the auxiliary polynomial-cover situation `T`. -/
private noncomputable theorem polynomial_cover_restricted_object_compat
    {Q : Type u} [CommRing Q]
    (T : @FiberProductBaseChangeSituation B A A' Q _ _ _ _)
    (X : S.relativeModuleCategory)
    (δD : T.D →+* S.D)
    (δCPrime : T.CPrime →+* S.CPrime)
    (δC : T.C →+* S.C)
    (hδC_comp_dToC : δC.comp T.dToC = S.dToC.comp δD)
    (hδC_comp_cprimeToC : δC.comp T.cprimeToC = S.cprimeToC.comp δCPrime) :
    (ModuleCat.extendScalars T.dToC).obj ((ModuleCat.restrictScalars δD).obj X.fst) ≅
      (ModuleCat.extendScalars T.cprimeToC).obj ((ModuleCat.restrictScalars δCPrime).obj X.snd) := by
  -- Proof comment: once the two one-sided change-of-rings adapters are isolated, the desired
  -- compatibility is just their composition with the restricted form of `X.iso`.
  exact
    restricted_fst_extend_iso (S := S) T δD δC hδC_comp_dToC X.fst ≪≫
      (ModuleCat.restrictScalars δC).mapIso X.iso ≪≫
      (restricted_snd_extend_iso (S := S) T δCPrime δC hδC_comp_cprimeToC X.snd).symm

-- Proof sketch: factor `B' → D'` through a flat intermediate ring `D''` over which `D'` is
-- finitely presented, replace the original tensor square by the corresponding flat base-changed
-- one, and then combine Lemmas `15.7.4`, `15.6.8`, and the standard finite-presentation
-- criterion via a presentation of the kernel of a finite free cover.
/-- Lemma 15.7.6: in the fibre-product base-change situation of Lemma `15.7.2`, if the `D`-module
`N` is finitely presented and flat over `B`, the `C'`-module `M'` is finitely presented and flat
over `A'`, and the map `B' → D'` factors as a flat ring map followed by a finitely presented ring
map, then the fibre-product module `N ×_M M'` is finitely presented over `D'`. -/
theorem relativeModuleFiberProduct_finitePresentation_of_flat_of_factorization
    (X : S.relativeModuleCategory)
    [Module.FinitePresentation S.D X.fst]
    [Module.Flat B X.fst]
    [Module.FinitePresentation S.CPrime X.snd]
    [Module.Flat A' X.snd]
    (hfactor :
      ∃ (P : Type u) (_ : CommRing P) (g : S.Bprime →+* P) (h : P →+* Dp),
        g.Flat ∧ h.FinitePresentation ∧ S.bprimeToDp = h.comp g) :
    Module.FinitePresentation Dp (fiberProductFunctor.obj X) := by
  letI : Module.Flat S.Bprime (fiberProductFunctor.obj X) :=
    relativeModuleFiberProduct_flat_of_component_flat (S := S) X
  letI : Module.Finite Dp (fiberProductFunctor.obj X) :=
    relativeModuleFiberProduct_finite_of_finitePresentation (S := S) X
  rcases hfactor with ⟨P, hP, g, h, hgflat, hhfp, hcomp⟩
  letI : CommRing P := hP
  letI : Algebra P Dp := h.toAlgebra
  letI : Algebra.FinitePresentation P Dp :=
    factorization_target_algebra_finitePresentation (Dp := Dp) h hhfp
  obtain ⟨n, β, hβ, hkerβ⟩ :=
    factorization_target_polynomial_cover (Dp := Dp) h hhfp
  have hpolyflat :
      ((algebraMap P (MvPolynomial (Fin n) P)).toRingHom.comp g).Flat :=
    factorization_polynomial_cover_flat (S := S) g hgflat n
  have hpolyCover :
      let Q := MvPolynomial (Fin n) P
      let _ : Module Q (fiberProductFunctor.obj X) :=
        Module.compHom (fiberProductFunctor.obj X) β.toRingHom
      Module.FinitePresentation Q (fiberProductFunctor.obj X) := by
    let Q := MvPolynomial (Fin n) P
    letI : Module Q (fiberProductFunctor.obj X) :=
      Module.compHom (fiberProductFunctor.obj X) β.toRingHom
    letI : Module.Finite Q (fiberProductFunctor.obj X) :=
      finite_of_surjective_polynomial_cover_restrictScalars
        (Dp := Dp) (M := fiberProductFunctor.obj X) n β hβ
    let T : @FiberProductBaseChangeSituation B A A' Q _ _ _ _ where
      toSurjectiveRingPullbackSituation := S.toSurjectiveRingPullbackSituation
      bprimeToDp := ((algebraMap P Q).toRingHom.comp g)
    have hβcomp :
        S.bprimeToDp = β.toRingHom.comp ((algebraMap P Q).toRingHom.comp g) :=
      polynomial_cover_refines_factorization (S := S) g h n β hcomp
    letI : Algebra S.Bprime Q := T.bprimeToDp.toAlgebra
    let βBprime : Q →ₐ[S.Bprime] Dp :=
      { toRingHom := β.toRingHom
        commutes' := by
          intro b
          -- Proof comment: `β` respects the chosen `B'`-algebra structures exactly because it
          -- refines the original map `S.bprimeToDp`.
          change β (T.bprimeToDp b) = S.bprimeToDp b
          rw [hβcomp]
          rfl }
    have hδDsurj :
        Function.Surjective
          ((Algebra.TensorProduct.map βBprime (AlgHom.id S.Bprime B)).toRingHom :
            T.D →+* S.D) := by
      -- Proof comment: the `D`-side comparison is a tensor product of the surjective cover `β`
      -- with the identity on `B`.
      exact tensorProduct_map_surjective_of_left_surjective
        (R := S.Bprime) (S₁ := Q) (S₂ := Dp) (T := B) βBprime hβ
    have hδCPrime_surj :
        Function.Surjective
          ((Algebra.TensorProduct.map βBprime (AlgHom.id S.Bprime A')).toRingHom :
            T.CPrime →+* S.CPrime) := by
      -- Proof comment: the same tensor-surjectivity argument gives the `C'`-side comparison.
      exact tensorProduct_map_surjective_of_left_surjective
        (R := S.Bprime) (S₁ := Q) (S₂ := Dp) (T := A') βBprime hβ
    have hδCsurj :
        Function.Surjective
          ((Algebra.TensorProduct.map βBprime (AlgHom.id S.Bprime A)).toRingHom :
            T.C →+* S.C) := by
      -- Proof comment: tensoring with the identity on `A` gives the final comparison map on `C`.
      exact tensorProduct_map_surjective_of_left_surjective
        (R := S.Bprime) (S₁ := Q) (S₂ := Dp) (T := A) βBprime hβ
    let δD : T.D →+* S.D :=
      (Algebra.TensorProduct.map βBprime (AlgHom.id S.Bprime B)).toRingHom
    let δCPrime : T.CPrime →+* S.CPrime :=
      (Algebra.TensorProduct.map βBprime (AlgHom.id S.Bprime A')).toRingHom
    let δC : T.C →+* S.C :=
      (Algebra.TensorProduct.map βBprime (AlgHom.id S.Bprime A)).toRingHom
    have hcomparison :
        δD.comp T.bToD = S.bToD ∧
          δCPrime.comp T.aprimeToCPrime = S.aprimeToCPrime ∧
          δC.comp T.dToC = S.dToC.comp δD ∧
          δC.comp T.cprimeToC = S.cprimeToC.comp δCPrime := by
      -- Proof comment: package the four tensor comparison identities once so the later
      -- restricted-object construction can reuse them without repeating transport calculations.
      simpa [T, δD, δCPrime, δC] using
        (polynomial_cover_comparison_package (S := S)
          (((algebraMap P Q).toRingHom.comp g)) βBprime)
    rcases hcomparison with
      ⟨hδD_comp_bToD, hδCPrime_comp_aprimeToCPrime, hδC_comp_dToC, hδC_comp_cprimeToC⟩
    letI : Module T.D X.fst := Module.compHom X.fst δD
    letI : Module T.CPrime X.snd := Module.compHom X.snd δCPrime
    letI : Algebra T.D S.D := δD.toAlgebra
    letI : Algebra T.CPrime S.CPrime := δCPrime.toAlgebra
    have hβBprime_fp : Algebra.FinitePresentation Q Dp := by
      -- Proof comment: the chosen polynomial cover is surjective with finitely generated kernel,
      -- so `Dp` is a finitely presented `Q`-algebra.
      exact Algebra.FinitePresentation.of_surjective (f := βBprime) hβ hkerβ
    have hδD_fp : Algebra.FinitePresentation T.D S.D := by
      -- Proof comment: finite presentation of algebras is stable under the tensor base change
      -- from `Q` to `T.D = Q ⊗[B'] B`.
      letI : Algebra Q Dp := βBprime.toAlgebra
      letI : Algebra.FinitePresentation Q Dp := hβBprime_fp
      infer_instance
    have hδCPrime_fp : Algebra.FinitePresentation T.CPrime S.CPrime := by
      -- Proof comment: the same base-change stability gives finite presentation on the `C'`
      -- side after tensoring with `A'`.
      letI : Algebra Q Dp := βBprime.toAlgebra
      letI : Algebra.FinitePresentation Q Dp := hβBprime_fp
      infer_instance
    letI : Algebra.FinitePresentation T.D S.D := hδD_fp
    letI : Algebra.FinitePresentation T.CPrime S.CPrime := hδCPrime_fp
    letI : Module.Finite T.D S.D :=
      Module.Finite.of_surjective (Algebra.linearMap T.D S.D) hδDsurj
    letI : Module.Finite T.CPrime S.CPrime :=
      Module.Finite.of_surjective (Algebra.linearMap T.CPrime S.CPrime) hδCPrime_surj
    obtain ⟨hfst_restricted_fp_obj, hsnd_restricted_fp_obj,
        hfst_restricted_flat, hsnd_restricted_flat⟩ :=
      polynomial_cover_restricted_component_hypotheses
        (S := S) T X δD δCPrime hδDsurj hδCPrime_surj
        hδD_comp_bToD hδCPrime_comp_aprimeToCPrime
    have hfst_restricted_fp : Module.FinitePresentation T.D X.fst := by
      -- Proof comment: the restricted-scalar object has the same underlying carrier as `X.fst`.
      simpa using hfst_restricted_fp_obj
    have hsnd_restricted_fp : Module.FinitePresentation T.CPrime X.snd := by
      -- Proof comment: the same carrier identification gives the `C'`-side statement.
      simpa using hsnd_restricted_fp_obj
    let XT : T.relativeModuleCategory :=
      CategoricalPullback.mk
        ((ModuleCat.restrictScalars δD).obj X.fst)
        ((ModuleCat.restrictScalars δCPrime).obj X.snd)
        (polynomial_cover_restricted_object_compat
          (S := S) T X δD δCPrime δC hδC_comp_dToC hδC_comp_cprimeToC)
    have hXT_fst_fp : Module.FinitePresentation T.D XT.fst := by
      -- Proof comment: by construction the first component of `XT` is exactly the restricted
      -- first component of `X`.
      simpa [XT] using hfst_restricted_fp_obj
    have hXT_snd_fp : Module.FinitePresentation T.CPrime XT.snd := by
      -- Proof comment: the same definitional identification applies to the second component.
      simpa [XT] using hsnd_restricted_fp_obj
    have hXT_fst_flat : Module.Flat B XT.fst := by
      -- Proof comment: flatness has already been transported to the restricted first component.
      simpa [XT] using hfst_restricted_flat
    have hXT_snd_flat : Module.Flat A' XT.snd := by
      -- Proof comment: flatness on the second component transports in the same way.
      simpa [XT] using hsnd_restricted_flat
    -- Route correction: the auxiliary pullback object over `T` is now packaged, so the transport
    -- layer is stabilized. The remaining blocker is the source's next step: compare
    -- `relativeFiberProductFunctor T.obj XT` with the `Q`-restriction of the original fibre
    -- product, and then run the finite free cover / kernel pullback argument over `Q`.
    -- TODO: prove the fibre-product comparison isomorphism over `T`, choose a finite free cover of
    -- `relativeFiberProductFunctor T.obj XT`, identify its kernel as a fibre product of component
    -- kernels using flat tensor exactness, and apply `Module.finitePresentation_of_surjective`.
    sorry
  -- Proof comment: once the fibre-product module is finitely presented over the polynomial cover,
  -- the surjective cover `β` descends finite presentation to the target ring `D'`.
  exact finitePresentation_of_surjective_polynomial_cover_restrictScalars
    (Dp := Dp) (M := fiberProductFunctor.obj X) n β hβ hpolyCover

end FiberProductBaseChangeSituation

end

end
