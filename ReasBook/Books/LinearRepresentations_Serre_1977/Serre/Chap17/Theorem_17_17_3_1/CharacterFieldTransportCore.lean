import Mathlib
import LinearRepresentations_Serre_1977.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_1
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_3
import LinearRepresentations_Serre_1977.Chap07.Remark_7_7_1_4
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_4_1.IdentityProjectionRepresentativeSeeds
import LinearRepresentations_Serre_1977.Chap08.Corollary_8_8_3_8
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_5_3.ResidueFieldLift
import LinearRepresentations_Serre_1977.GroupTheory.PSolvable
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CyclicNormalByPGroupBasics
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CliffordIsotypicTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ResidueFieldLiftTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CyclicOrbitSpan
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ProperOvergroupRecursion
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ResidueFieldLiftInductionTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ULiftScalarExtensionPreparation
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.InducedScalarExtensionTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.InducedCoinvariantsMaps

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace Representation

open CategoryTheory Rep
open scoped Representation

section

variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable {G : Type v} [Group G] [Finite G]
variable {p : ℕ}

variable [CharP (IsLocalRing.ResidueField A) p]
variable {V : Type w} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
variable [FiniteDimensional (IsLocalRing.ResidueField A) V]
variable {C P : Subgroup G}

local notation "k" => IsLocalRing.ResidueField A
noncomputable local instance characterFieldTransportCoreResidueFieldModule
    {W : Type*} [AddCommGroup W] [Module k W] : Module A W :=
  Module.compHom W (algebraMap A k)
local instance characterFieldTransportCoreResidueFieldIsScalarTower
    {W : Type*} [AddCommGroup W] [Module k W] : IsScalarTower A k W :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.3-1: every residue-field lift has surjective reduction map, because
its base-change equivalence identifies the target with the tensor product over the residue field. -/
theorem residueFieldLift_surjective
    {G' : Type*} [Group G']
    {V' : Type*} [AddCommGroup V'] [Module k V']
    {W : Type*} [AddCommGroup W] [Module A W]
    [Module.Free A W] [Module.Finite A W]
    {ρ : Representation k G' V'}
    {ρA : Representation A G' W}
    {red : W →ₗ[A] V'}
    (hLift : IsResidueFieldLift ρ ρA red) :
    Function.Surjective red := by
  letI : Module A k := Algebra.toModule
  -- Unpack the tensor-product base change equivalence and use surjectivity of `A → k`.
  intro y
  obtain ⟨t, ht⟩ := hLift.1.equiv.surjective y
  obtain ⟨x, hx⟩ :=
    TensorProduct.mk_surjective A W (IsLocalRing.ResidueField A) Ideal.Quotient.mk_surjective t
  refine ⟨x, ?_⟩
  calc
    red x = hLift.1.equiv (TensorProduct.mk A (IsLocalRing.ResidueField A) W 1 x) := by
      simpa using (hLift.1.equiv_tmul (1 : k) x).symm
    _ = hLift.1.equiv t := by rw [hx]
    _ = y := ht

/-- Helper for Theorem 17-17.3-1: conjugating the restricted `C`-representation by an element of
`P` is equivalent to the original restricted action via `ρ s` on the carrier. -/
noncomputable def restricted_conjugation_equiv_of_p_local
    (ρ : Representation k G V)
    (hC : C.Normal)
    (s : P) :
    Representation.Equiv
      (((ρ.comp C.subtype).comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom))
      (ρ.comp C.subtype) := by
  let _ := hC
  let e : V ≃ₗ[k] V :=
    LinearEquiv.ofBijective (ρ (s : G)) (ρ.apply_bijective (s : G))
  refine Representation.Equiv.mk e ?_
  intro c
  ext v
  -- Rewrite the conjugated `C`-action as literal multiplication in `G`, then cancel the
  -- conjugation by the defining formula for `MulAut.conjNormal`.
  calc
    e ((((ρ.comp C.subtype).comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom) c) v)
        = ρ (s : G) (ρ (((MulAut.conjNormal ((s : G))⁻¹) c : C)) v) := by
            rfl
    _ = ρ ((s : G) * (((MulAut.conjNormal ((s : G))⁻¹) c : C))) v := by
          exact
            (LinearMap.congr_fun
              (ρ.map_mul (s : G) (((MulAut.conjNormal ((s : G))⁻¹) c : C))) v).symm
    _ = ρ ((c : G) * (s : G)) v := by
          simp [mul_assoc]
    _ = ((ρ.comp C.subtype) c) (e v) := by
          exact LinearMap.congr_fun (ρ.map_mul (c : G) (s : G)) v

/-- Helper for Theorem 17-17.3-1: for each `s : P`, Serre's conjugated `C`-lift and the chosen
fixed `C`-lift are already compared by Chapter `15` uniqueness after shrinking `C` into the
coefficient universe. -/
theorem character_field_transport_conjugate_lift_compare_local
    (ρ : Representation k G V)
    (hC : C.Normal)
    (hCndvd : ¬ p ∣ Nat.card C)
    {W : Type u} [AddCommGroup W] [Module A W]
    [Module.Free A W] [Module.Finite A W]
    (ρA_C : Representation A C W)
    (red_C : W →ₗ[A] V)
    (hLiftC : IsResidueFieldLift (ρ.comp C.subtype) ρA_C red_C)
    (s : P) :
    ∃ u :
        Representation.Equiv
          (ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
          ρA_C,
      red_C.comp u.toLinearMap =
        (((restricted_conjugation_equiv_of_p_local (ρ := ρ) (C := C) hC s).toLinearMap.restrictScalars
          A).comp red_C) := by
  let ρC : Representation k C V := ρ.comp C.subtype
  let ρA_conj_s : Representation A C W :=
    ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom
  let red_s : W →ₗ[A] V :=
    (((restricted_conjugation_equiv_of_p_local (ρ := ρ) (C := C) hC s).toLinearMap.restrictScalars
      A).comp red_C)
  have hConjLift :
      IsResidueFieldLift
        (ρC.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
        ρA_conj_s
        red_C := by
    -- Restrict the chosen `C`-lift along the conjugation action of `s⁻¹`.
    simpa [ρC, ρA_conj_s] using
      (Representation.isResidueFieldLift_comp hLiftC
        (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
  have hLiteralTransport :
      IsResidueFieldLift ρC ρA_conj_s red_s := by
    -- Transport the conjugated reduced target back to the original restricted `C`-action.
    simpa [ρC, ρA_conj_s, red_s] using
      (residueFieldLift_of_equiv_target
        (A := A) (G := C) (V := V) (ρA := ρA_conj_s) hConjLift
        (restricted_conjugation_equiv_of_p_local (ρ := ρ) (C := C) hC s))
  have hSmallC : Small.{u} C := by
    obtain ⟨n, ⟨efin⟩⟩ := Finite.exists_equiv_fin C
    exact Small.mk' (efin.trans Equiv.ulift.symm)
  letI : Small.{u} C := hSmallC
  let eShrink : Shrink.{u} C ≃* C := Shrink.mulEquiv
  have hShrink_ndvd : ¬ p ∣ Nat.card (Shrink.{u} C) := by
    simpa [Nat.card_congr eShrink.toEquiv] using hCndvd
  have hConjLift_shrink :
      IsResidueFieldLift
        (ρC.comp eShrink.toMonoidHom)
        (ρA_conj_s.comp eShrink.toMonoidHom)
        red_s := by
    exact Representation.isResidueFieldLift_comp hLiteralTransport eShrink.toMonoidHom
  have hFixedLift_shrink :
      IsResidueFieldLift
        (ρC.comp eShrink.toMonoidHom)
        (ρA_C.comp eShrink.toMonoidHom)
        red_C := by
    exact Representation.isResidueFieldLift_comp hLiftC eShrink.toMonoidHom
  obtain ⟨uShrink, hu⟩ :=
    residueFieldLift_unique_up_to_equivariant_iso
      (A := A) (p := p) (G := Shrink.{u} C) (V := V)
      hShrink_ndvd
      (ρC.comp eShrink.toMonoidHom)
      (ρA_conj_s.comp eShrink.toMonoidHom)
      red_s
      hConjLift_shrink
      (ρA_C.comp eShrink.toMonoidHom)
      red_C
      hFixedLift_shrink
  let u : ρA_conj_s.Equiv ρA_C :=
    Representation.Equiv.mk uShrink.toLinearEquiv fun g ↦ by
      -- The shrink comparison is equivariant for every `g' : Shrink C`, hence also for the
      -- original element `g : C` after rewriting along `eShrink`.
      simpa [ρA_conj_s] using uShrink.isIntertwining' (eShrink.symm g)
  refine ⟨u, ?_⟩
  change red_C.comp uShrink.toLinearMap = red_s
  exact hu

/-- Helper for Theorem 17-17.3-1: the Chapter `15` comparison sends the chosen lifted generator
`w0` to another lift of the same `P`-fixed residue vector `ν`. -/
theorem character_field_transport_conjugate_lift_compare_fixed_vector_local
    (ρ : Representation k G V)
    (hC : C.Normal)
    (hCndvd : ¬ p ∣ Nat.card C)
    {W : Type u} [AddCommGroup W] [Module A W]
    [Module.Free A W] [Module.Finite A W]
    (ρA_C : Representation A C W)
    (red_C : W →ₗ[A] V)
    (hLiftC : IsResidueFieldLift (ρ.comp C.subtype) ρA_C red_C)
    (w0 : W) (ν : V)
    (hw0 : red_C w0 = ν)
    (hνfixed : ∀ s : P, (ρ.comp P.subtype) s ν = ν)
    (s : P) :
    ∃ u :
        Representation.Equiv
          (ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
          ρA_C,
      red_C.comp u.toLinearMap =
          (((restricted_conjugation_equiv_of_p_local (ρ := ρ) (C := C) hC s).toLinearMap.restrictScalars
            A).comp red_C) ∧
        red_C (u w0) = ν := by
  obtain ⟨u, hu⟩ :=
    character_field_transport_conjugate_lift_compare_local
      (A := A) (G := G) (p := p) (V := V) (C := C) (P := P)
      ρ hC hCndvd ρA_C red_C hLiftC s
  refine ⟨u, hu, ?_⟩
  -- Evaluate the uniqueness comparison on `w0`; the residue-side action is `ρ s`, hence it fixes
  -- `ν` by the `P`-fixed hypothesis.
  have huw0 :
      red_C (u w0) =
        (((restricted_conjugation_equiv_of_p_local (ρ := ρ) (C := C) hC s).toLinearMap.restrictScalars
          A).comp red_C) w0 := by
    simpa [LinearMap.comp_apply] using congrArg (fun f : W →ₗ[A] V ↦ f w0) hu
  calc
    red_C (u w0)
        = (((restricted_conjugation_equiv_of_p_local (ρ := ρ) (C := C) hC s).toLinearMap.restrictScalars
            A).comp red_C) w0 := huw0
    _ = (restricted_conjugation_equiv_of_p_local (ρ := ρ) (C := C) hC s) (red_C w0) := by
          rfl
    _ = (restricted_conjugation_equiv_of_p_local (ρ := ρ) (C := C) hC s) ν := by
          rw [hw0]
    _ = ρ (s : G) ν := by
          rfl
    _ = (ρ.comp P.subtype) s ν := by
          rfl
    _ = ν := hνfixed s

/-- Helper for Theorem 17-17.3-1: every comparison image `u w0` still generates the lifted
`C`-module because it reduces to the same cyclic residue generator `ν`. -/
theorem character_field_transport_compare_generator_span_local
    (ρ : Representation k G V)
    {W : Type u} [AddCommGroup W] [Module A W]
    [Module.Free A W] [Module.Finite A W]
    (ρA_C : Representation A C W)
    (red_C : W →ₗ[A] V)
    (hLiftC : IsResidueFieldLift (ρ.comp C.subtype) ρA_C red_C)
    (w1 : W) (ν : V)
    (hw1 : red_C w1 = ν)
    (hOrbitSpan : Submodule.span k (Set.range fun c : C ↦ ρ c ν) = ⊤) :
    Submodule.span A (Set.range fun c : C ↦ ρA_C c w1) = ⊤ := by
  -- Once `w1` reduces to the same residue generator, the previously proved cyclic-lift argument
  -- applies verbatim with `w1` in place of the original chosen lift.
  exact
    cyclic_lift_span_top_of_fixed_lift
      (A := A) (G := G) (ρ := ρ) (C := C) ρA_C red_C hLiftC w1 ν hw1 hOrbitSpan

/-- Helper for Theorem 17-17.3-1: on the regular `A[C]`-module of a lifted `C`-representation,
left multiplication by any `r : A[C]` is `C`-equivariant because `C` is cyclic and hence
`A[C]` is commutative. This is the source-level commutativity input in Serre's cyclic-presentation
comparison. -/
theorem character_field_transport_regular_action_isIntertwining_local
    {C0 : Type*} [Group C0] [IsMulCommutative C0]
    {W : Type u} [AddCommGroup W] [Module A W]
    (ρA_C : Representation A C0 W)
    (r : MonoidAlgebra A C0) :
    ρA_C.IsIntertwiningMap ρA_C (ρA_C.asAlgebraHom r) := by
  rw [Representation.isIntertwiningMap_iff]
  intro c x
  -- The `A[C]`-action commutes with the `C`-action because both come from the same commutative
  -- group algebra `A[C]`.
  have hcomm :
      (ρA_C.asAlgebraHom r) * (ρA_C.asAlgebraHom (MonoidAlgebra.of A C0 c)) =
        (ρA_C.asAlgebraHom (MonoidAlgebra.of A C0 c)) * (ρA_C.asAlgebraHom r) := by
    ext y
    have hmul : r * MonoidAlgebra.of A C0 c = MonoidAlgebra.of A C0 c * r := by
      ext g
      simpa [MonoidAlgebra.of_apply] using congrArg r (mul_comm' g c⁻¹)
    calc
      (ρA_C.asAlgebraHom r) ((ρA_C.asAlgebraHom (MonoidAlgebra.of A C0 c)) y)
          = (ρA_C.asAlgebraHom (r * MonoidAlgebra.of A C0 c)) y := by
              simp [Module.End.mul_apply]
      _ = (ρA_C.asAlgebraHom (MonoidAlgebra.of A C0 c * r)) y := by
            rw [hmul]
      _ = (ρA_C.asAlgebraHom (MonoidAlgebra.of A C0 c)) ((ρA_C.asAlgebraHom r) y) := by
            simp [Module.End.mul_apply]
  simpa [Representation.asAlgebraHom_single, MonoidAlgebra.of_apply, Module.End.mul_apply] using
    LinearMap.congr_fun hcomm x

/-- Helper for Theorem 17-17.3-1: two cyclic generators with full `C`-orbit span define the same
kernel in the regular `A[C]`-module. This is the common cyclic presentation behind Serre's
normalization step. -/
theorem character_field_transport_cyclic_kernel_eq_local
    {W : Type u} [AddCommGroup W] [Module A W] [IsMulCommutative C]
    (ρA_C : Representation A C W)
    (w0 w1 : W)
    (hspan0 : Submodule.span A (Set.range fun c : C ↦ ρA_C c w0) = ⊤)
    (hspan1 : Submodule.span A (Set.range fun c : C ↦ ρA_C c w1) = ⊤) :
    letI : Module (MonoidAlgebra A C) W := Module.compHom W ρA_C.asAlgebraHom.toRingHom
    letI : IsScalarTower A (MonoidAlgebra A C) W :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change ρA_C.asAlgebraHom (algebraMap A (MonoidAlgebra A C) a) x = a • x
        simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA_C.asAlgebraHom.commutes a) x
    ∀ r : MonoidAlgebra A C, r • w0 = 0 ↔ r • w1 = 0 := by
  intro r
  let fr : W →ₗ[A] W := ρA_C.asAlgebraHom r
  have hfr : ρA_C.IsIntertwiningMap ρA_C fr := by
    -- The source-faithful input is that the regular `A[C]`-action commutes with the `C`-action.
    simpa [fr] using
      character_field_transport_regular_action_isIntertwining_local
        (A := A) (C0 := C) (ρA_C := ρA_C) r
  rw [Representation.isIntertwiningMap_iff] at hfr
  constructor
  · intro hr0
    have hr0' : fr w0 = 0 := by
      simpa [fr] using hr0
    have hzero_on_span0 :
        ∀ y ∈ Submodule.span A (Set.range fun c : C ↦ ρA_C c w0), fr y = 0 := by
      intro y hy
      -- Once `r` kills the cyclic generator `w0`, `C`-equivariance forces it to kill the whole
      -- `C`-orbit span, hence every vector of `W`.
      refine Submodule.span_induction (s := Set.range fun c : C ↦ ρA_C c w0) ?_ ?_ ?_ ?_ hy
      · intro z hz
        rcases hz with ⟨c, rfl⟩
        calc
          fr (ρA_C c w0) = ρA_C c (fr w0) := hfr c w0
          _ = ρA_C c 0 := by rw [hr0']
          _ = 0 := by simp
      · rw [map_zero]
      · intro y z hy hz hy0 hz0
        simpa [map_add, hy0, hz0]
      · intro a y hy hy0
        simpa [map_smul, hy0]
    have hfr_w1 : fr w1 = 0 := by
      have hy : w1 ∈ Submodule.span A (Set.range fun c : C ↦ ρA_C c w0) := by
        rw [hspan0]
        exact Submodule.mem_top
      exact hzero_on_span0 w1 hy
    simpa [fr] using hfr_w1
  · intro hr1
    have hr1' : fr w1 = 0 := by
      simpa [fr] using hr1
    have hzero_on_span1 :
        ∀ y ∈ Submodule.span A (Set.range fun c : C ↦ ρA_C c w1), fr y = 0 := by
      intro y hy
      -- The same cyclic-presentation argument in the opposite direction gives the reverse
      -- kernel inclusion.
      refine Submodule.span_induction (s := Set.range fun c : C ↦ ρA_C c w1) ?_ ?_ ?_ ?_ hy
      · intro z hz
        rcases hz with ⟨c, rfl⟩
        calc
          fr (ρA_C c w1) = ρA_C c (fr w1) := hfr c w1
          _ = ρA_C c 0 := by rw [hr1']
          _ = 0 := by simp
      · rw [map_zero]
      · intro y z hy hz hy0 hz0
        simpa [map_add, hy0, hz0]
      · intro a y hy hy0
        simpa [map_smul, hy0]
    have hfr_w0 : fr w0 = 0 := by
      have hy : w0 ∈ Submodule.span A (Set.range fun c : C ↦ ρA_C c w1) := by
        rw [hspan1]
        exact Submodule.mem_top
      exact hzero_on_span1 w0 hy
    simpa [fr] using hfr_w0

/-- Helper for Theorem 17-17.3-1: if the `C`-orbit of `w` spans `W`, then every vector of `W`
is of the form `r • w` for some `r ∈ A[C]`. This is the surjectivity input needed before passing
to Serre's common cyclic quotient. -/
theorem character_field_transport_cyclic_presentation_surjective_local
    {W : Type u} [AddCommGroup W] [Module A W]
    (ρA_C : Representation A C W)
    (w : W)
    (hspan : Submodule.span A (Set.range fun c : C ↦ ρA_C c w) = ⊤) :
    letI : Module (MonoidAlgebra A C) W := Module.compHom W ρA_C.asAlgebraHom.toRingHom
    letI : IsScalarTower A (MonoidAlgebra A C) W :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change ρA_C.asAlgebraHom (algebraMap A (MonoidAlgebra A C) a) x = a • x
        simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA_C.asAlgebraHom.commutes a) x
    ∀ y : W, ∃ r : MonoidAlgebra A C, r • w = y := by
  letI : Module (MonoidAlgebra A C) W := Module.compHom W ρA_C.asAlgebraHom.toRingHom
  letI : IsScalarTower A (MonoidAlgebra A C) W :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρA_C.asAlgebraHom (algebraMap A (MonoidAlgebra A C) a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA_C.asAlgebraHom.commutes a) x
  intro y
  have hy : y ∈ Submodule.span A (Set.range fun c : C ↦ ρA_C c w) := by
    rw [hspan]
    exact Submodule.mem_top
  -- Build the desired coefficient `r` by induction on the cyclic `A`-span of the `C`-orbit.
  refine Submodule.span_induction (s := Set.range fun c : C ↦ ρA_C c w) ?_ ?_ ?_ ?_ hy
  · intro z hz
    rcases hz with ⟨c, rfl⟩
    refine ⟨MonoidAlgebra.single c (1 : A), ?_⟩
    change ρA_C.asAlgebraHom (MonoidAlgebra.single c (1 : A)) w = ρA_C c w
    simp [Representation.asAlgebraHom_single]
  · exact ⟨0, by simp⟩
  · intro y z hy' hz' hriy hriz
    rcases hriy with ⟨ry, rfl⟩
    rcases hriz with ⟨rz, rfl⟩
    refine ⟨ry + rz, by simp [add_smul]⟩
  · intro a y hy' hriy
    rcases hriy with ⟨r, rfl⟩
    refine ⟨(algebraMap A (MonoidAlgebra A C) a) * r, ?_⟩
    calc
      ((algebraMap A (MonoidAlgebra A C) a) * r) • w
          = (algebraMap A (MonoidAlgebra A C) a) • (r • w) := by
              rw [mul_smul]
      _ = a • (r • w) := by
            simpa using (IsScalarTower.algebraMap_smul (MonoidAlgebra A C) a (r • w))

/-- Helper for Theorem 17-17.3-1: an equality of annihilator submodules transports the common
cyclic quotient without introducing any new carrier-level data. This isolates the only quotient
transport used in Serre's normalization step. -/
noncomputable def quotient_transport_linearEquiv_local
    {M : Type*} [AddCommGroup M] [Module A M]
    {K L : Submodule A M} (h : K = L) :
    (M ⧸ K) ≃ₗ[A] M ⧸ L :=
  h ▸ (LinearEquiv.refl A (M ⧸ K))

/-- Helper for Theorem 17-17.3-1: the quotient transport above sends each quotient generator class
to the identically represented class in the transported quotient. -/
theorem quotient_transport_linearEquiv_apply_mk_local
    {M : Type*} [AddCommGroup M] [Module A M]
    {K L : Submodule A M} (h : K = L) (x : M) :
    quotient_transport_linearEquiv_local (A := A) (M := M) h (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x : M ⧸ L) := by
  -- After rewriting by the kernel equality, the transport is literally the identity map.
  cases h
  rfl

/-- Helper for Theorem 17-17.3-1: two surjective linear maps with the same kernel identify the
same target with one frozen quotient of the common source. This packages the common cyclic model
used later with `π₀ r = r • w₀` and `π₁ r = r • w₁`. -/
theorem common_quotient_model_of_surjective_linearMaps_local
    {M : Type*} [AddCommGroup M] [Module A M]
    {W : Type*} [AddCommGroup W] [Module A W]
    (π0 π1 : M →ₗ[A] W)
    (hπ0 : Function.Surjective π0)
    (hπ1 : Function.Surjective π1)
    (hker : LinearMap.ker π0 = LinearMap.ker π1) :
    let Q := M ⧸ LinearMap.ker π0
    ∃ e0 e1 : Q ≃ₗ[A] W,
      (∀ x : M, e0 (Submodule.Quotient.mk x) = π0 x) ∧
        ∀ x : M, e1 (Submodule.Quotient.mk x) = π1 x := by
  let Q := M ⧸ LinearMap.ker π0
  let e0 : Q ≃ₗ[A] W := π0.quotKerEquivOfSurjective hπ0
  let q01 : Q ≃ₗ[A] M ⧸ LinearMap.ker π1 :=
    quotient_transport_linearEquiv_local (A := A) (M := M) hker
  let e1 : Q ≃ₗ[A] W := q01.trans (π1.quotKerEquivOfSurjective hπ1)
  refine ⟨e0, e1, ?_, ?_⟩
  · intro x
    -- The first model is the standard first-isomorphism-theorem quotient for `π0`.
    simpa [Q, e0] using LinearMap.quotKerEquivOfSurjective_apply_mk π0 hπ0 x
  · intro x
    -- The second model uses the same quotient after one kernel transport, then applies the
    -- standard first-isomorphism-theorem quotient for `π1`.
    change (π1.quotKerEquivOfSurjective hπ1) (q01 (Submodule.Quotient.mk x)) = π1 x
    rw [quotient_transport_linearEquiv_apply_mk_local
      (A := A) (M := M) (h := hker)]
    simpa using LinearMap.quotKerEquivOfSurjective_apply_mk π1 hπ1 x

/-- Helper for Theorem 17-17.3-1: once two lifts `w0` and `w1` of the same cyclic residue
generator define the same annihilator in `A[C]`, Serre's common-quotient argument yields a
`C`-equivariant automorphism reducing to the identity and sending `w1` back to `w0`. -/
theorem character_field_transport_correction_equiv_local
    (ρ : Representation k G V)
    {W : Type u} [AddCommGroup W] [Module A W]
    [Module.Free A W] [Module.Finite A W]
    [IsMulCommutative C]
    (ρA_C : Representation A C W)
    (red_C : W →ₗ[A] V)
    (hLiftC : IsResidueFieldLift (ρ.comp C.subtype) ρA_C red_C)
    (w0 w1 : W) (ν : V)
    (hw0 : red_C w0 = ν)
    (hw1 : red_C w1 = ν)
    (hspan0 : Submodule.span A (Set.range fun c : C ↦ ρA_C c w0) = ⊤)
    (hspan1 : Submodule.span A (Set.range fun c : C ↦ ρA_C c w1) = ⊤) :
    ∃ corr : ρA_C.Equiv ρA_C,
      red_C.comp corr.toLinearMap = red_C ∧
        corr w1 = w0 := by
  -- Route correction: the common quotient model is now packaged by
  -- `common_quotient_model_of_surjective_linearMaps_local`. The remaining blocker is to descend
  -- the reduction map through the frozen quotient and then promote the resulting comparison
  -- `e0.trans e1.symm` from a linear equivalence to a `C`-equivariant automorphism of `ρA_C`.
  letI : Module (MonoidAlgebra A C) W := Module.compHom W ρA_C.asAlgebraHom.toRingHom
  letI : IsScalarTower A (MonoidAlgebra A C) W :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change
        ρA_C.asAlgebraHom (algebraMap A (MonoidAlgebra A C) a) x =
          (algebraMap A (Module.End A W) a) x
      exact LinearMap.congr_fun (ρA_C.asAlgebraHom.commutes a) x
  let ρC : Representation A C V := Representation.restrictScalars A (ρ.comp C.subtype)
  letI : Module (MonoidAlgebra A C) V := Module.compHom V ρC.asAlgebraHom.toRingHom
  letI : IsScalarTower A (MonoidAlgebra A C) V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change
        ρC.asAlgebraHom (algebraMap A (MonoidAlgebra A C) a) x =
          (algebraMap A (Module.End A V) a) x
      exact LinearMap.congr_fun (ρC.asAlgebraHom.commutes a) x
  letI : Module A A := Semiring.toModule
  letI : Module A (MonoidAlgebra A C) := MonoidAlgebra.module
  let π0 : MonoidAlgebra A C →ₗ[A] W :=
    { toFun := fun r ↦ r • w0
      map_add' := by
        intro r s
        simp [add_smul]
      map_smul' := by
        intro a r
        -- Read `π0` through the algebra homomorphism `A[C] → End_A(W)` and evaluate its
        -- `A`-linearity at the cyclic generator `w0`.
        exact congrArg (fun f : Module.End A W ↦ f w0) (ρA_C.asAlgebraHom.toLinearMap.map_smul a r) }
  let π1 : MonoidAlgebra A C →ₗ[A] W :=
    { toFun := fun r ↦ r • w1
      map_add' := by
        intro r s
        simp [add_smul]
      map_smul' := by
        intro a r
        -- The same `A`-linearity computation evaluated at `w1`.
        exact congrArg (fun f : Module.End A W ↦ f w1) (ρA_C.asAlgebraHom.toLinearMap.map_smul a r) }
  have hπ0 : Function.Surjective π0 := by
    intro y
    simpa [π0] using
      character_field_transport_cyclic_presentation_surjective_local
        (A := A) (C := C) ρA_C w0 hspan0 y
  have hπ1 : Function.Surjective π1 := by
    intro y
    simpa [π1] using
      character_field_transport_cyclic_presentation_surjective_local
        (A := A) (C := C) ρA_C w1 hspan1 y
  have hker : LinearMap.ker π0 = LinearMap.ker π1 := by
    ext r
    change r • w0 = 0 ↔ r • w1 = 0
    exact
      character_field_transport_cyclic_kernel_eq_local
        (A := A) (C := C) ρA_C w0 w1 hspan0 hspan1 r
  rcases
      common_quotient_model_of_surjective_linearMaps_local
        (A := A) (M := MonoidAlgebra A C) (W := W) π0 π1 hπ0 hπ1 hker with
    ⟨e0, e1, he0, he1⟩
  let corrLin : W ≃ₗ[A] W := e1.symm.trans e0
  have hredInter :
      ρA_C.IsIntertwiningMap (Representation.restrictScalars A (ρ.comp C.subtype)) red_C :=
    residueFieldLift_isIntertwining_restrictScalars (A := A) hLiftC
  have hred_smul : ∀ r : MonoidAlgebra A C, ∀ x : W, red_C (r • x) = r • red_C x := by
    intro r
    -- The reduction map is `A[C]`-linear because it intertwines the lifted and reduced
    -- `C`-actions on group generators.
    refine MonoidAlgebra.induction_on
      (p := fun r : MonoidAlgebra A C ↦ ∀ x : W, red_C (r • x) = r • red_C x) r ?_ ?_ ?_
    · intro c
      intro x
      calc
        red_C (MonoidAlgebra.of A C c • x) = red_C (ρA_C c x) := by
          change red_C ((ρA_C.asAlgebraHom (MonoidAlgebra.single c (1 : A))) x) = _
          simp [Representation.asAlgebraHom_single, MonoidAlgebra.of_apply]
        _ = ρC c (red_C x) := hredInter.isIntertwining c x
        _ = MonoidAlgebra.of A C c • red_C x := by
          change ρC c (red_C x) = (ρC.asAlgebraHom (MonoidAlgebra.single c (1 : A))) (red_C x)
          simp [Representation.asAlgebraHom_single, MonoidAlgebra.of_apply]
    · intro a b ha hb x
      simp [add_smul, ha x, hb x]
    · intro a r hr x
      calc
        red_C ((a • r) • x) = red_C (a • (r • x)) := by
          simpa [smul_assoc]
        _ = a • red_C (r • x) := by rw [LinearMap.map_smul]
        _ = a • (r • red_C x) := by rw [hr x]
        _ = (a • r) • red_C x := by
          simpa [smul_assoc]
  have hred_classes :
      ∀ r : MonoidAlgebra A C,
        red_C (e0 (Submodule.Quotient.mk r)) = red_C (e1 (Submodule.Quotient.mk r)) := by
    intro r
    -- Both quotient models reduce to the same cyclic residue vector `ν`, so they agree after
    -- applying `red_C` on every quotient class.
    calc
      red_C (e0 (Submodule.Quotient.mk r)) = red_C (r • w0) := by simpa [π0] using congrArg red_C (he0 r)
      _ = r • red_C w0 := hred_smul r w0
      _ = r • ν := by rw [hw0]
      _ = r • red_C w1 := by rw [hw1]
      _ = red_C (r • w1) := by rw [hred_smul r w1]
      _ = red_C (e1 (Submodule.Quotient.mk r)) := by simpa [π1] using congrArg red_C (he1 r).symm
  have he0_mul :
      ∀ c : C, ∀ r : MonoidAlgebra A C,
        e0 (Submodule.Quotient.mk (MonoidAlgebra.of A C c * r)) =
          ρA_C c (e0 (Submodule.Quotient.mk r)) := by
    intro c r
    -- On quotient classes, `e0` is the cyclic presentation `r ↦ r • w0`, so left
    -- multiplication by `c` becomes the original `C`-action on `W`.
    calc
      e0 (Submodule.Quotient.mk (MonoidAlgebra.of A C c * r))
          = (MonoidAlgebra.of A C c * r) • w0 := by
              simpa [π0] using he0 (MonoidAlgebra.of A C c * r)
      _ = MonoidAlgebra.of A C c • (r • w0) := by rw [mul_smul]
      _ = ρA_C c (r • w0) := by
            change (ρA_C.asAlgebraHom (MonoidAlgebra.single c (1 : A))) (r • w0) = _
            simp [Representation.asAlgebraHom_single, MonoidAlgebra.of_apply]
      _ = ρA_C c (e0 (Submodule.Quotient.mk r)) := by
            simpa [π0] using congrArg (ρA_C c) (he0 r).symm
  have he1_mul :
      ∀ c : C, ∀ r : MonoidAlgebra A C,
        e1 (Submodule.Quotient.mk (MonoidAlgebra.of A C c * r)) =
          ρA_C c (e1 (Submodule.Quotient.mk r)) := by
    intro c r
    -- The same computation for the second cyclic model identifies its transported generator.
    calc
      e1 (Submodule.Quotient.mk (MonoidAlgebra.of A C c * r))
          = (MonoidAlgebra.of A C c * r) • w1 := by
              simpa [π1] using he1 (MonoidAlgebra.of A C c * r)
      _ = MonoidAlgebra.of A C c • (r • w1) := by rw [mul_smul]
      _ = ρA_C c (r • w1) := by
            change (ρA_C.asAlgebraHom (MonoidAlgebra.single c (1 : A))) (r • w1) = _
            simp [Representation.asAlgebraHom_single, MonoidAlgebra.of_apply]
      _ = ρA_C c (e1 (Submodule.Quotient.mk r)) := by
            simpa [π1] using congrArg (ρA_C c) (he1 r).symm
  have hcorrRedLin : red_C.comp corrLin.toLinearMap = red_C := by
    apply LinearMap.ext
    intro x
    obtain ⟨q, rfl⟩ := e1.surjective x
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.ker π0) q
    -- Compare both quotient models on the same class and use the common reduction above.
    calc
      red_C (corrLin (e1 (Submodule.Quotient.mk r)))
          = red_C (e0 (Submodule.Quotient.mk r)) := by
              simp [corrLin]
      _ = red_C (e1 (Submodule.Quotient.mk r)) := hred_classes r
  have hcorrw : corrLin w1 = w0 := by
    -- The class of `1 ∈ A[C]` is the common cyclic generator of both quotient models.
    calc
      corrLin w1 = corrLin (e1 (Submodule.Quotient.mk (1 : MonoidAlgebra A C))) := by
        change corrLin w1 = corrLin (e1 (Submodule.Quotient.mk (1 : MonoidAlgebra A C)))
        rw [he1]
        simp [π1]
      _ = e0 (Submodule.Quotient.mk (1 : MonoidAlgebra A C)) := by
        change corrLin (e1 (Submodule.Quotient.mk (1 : MonoidAlgebra A C))) =
          e0 (Submodule.Quotient.mk (1 : MonoidAlgebra A C))
        simp [corrLin]
      _ = w0 := by
        rw [he0]
        simp [π0]
  have hcorrInter : ρA_C.IsIntertwiningMap ρA_C corrLin.toLinearMap := by
    rw [Representation.isIntertwiningMap_iff]
    intro c x
    obtain ⟨q, rfl⟩ := e1.surjective x
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.ker π0) q
    -- The correction map compares the two quotient models of the same cyclic presentation, so
    -- it commutes with the `C`-action generatorwise on quotient classes.
    calc
      corrLin (ρA_C c (e1 (Submodule.Quotient.mk r)))
          = corrLin (e1 (Submodule.Quotient.mk (MonoidAlgebra.of A C c * r))) := by
              rw [← he1_mul c r]
      _ = e0 (Submodule.Quotient.mk (MonoidAlgebra.of A C c * r)) := by
            simp [corrLin]
      _ = ρA_C c (e0 (Submodule.Quotient.mk r)) := he0_mul c r
      _ = ρA_C c (corrLin (e1 (Submodule.Quotient.mk r))) := by
            simp [corrLin]
  let corr : ρA_C.Equiv ρA_C := Representation.Equiv.mk corrLin fun g ↦ by
    ext x
    exact hcorrInter.isIntertwining g x
  refine ⟨corr, ?_, hcorrw⟩
  -- Forgetting the equivariant structure leaves the already proved reduction identity.
  simpa [corr] using hcorrRedLin



end

end Representation
