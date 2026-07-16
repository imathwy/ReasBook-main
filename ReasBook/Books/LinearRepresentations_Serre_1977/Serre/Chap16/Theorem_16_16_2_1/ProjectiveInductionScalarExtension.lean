import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_2_1.ProjectiveSubgroupInduction

noncomputable section

universe u

open CategoryTheory
open scoped MonoidAlgebra Representation TensorProduct

namespace Representation

section InducedScalarExtension

variable {A : Type u} [CommRing A]
variable {K : Type u} [Field K] [Algebra A K]
variable {G : Type u} [Group G] [Finite G]
variable {H : Subgroup G}
variable {W : Type u} [AddCommGroup W] [Module A W]

private abbrev inducedScalarExtensionTarget
    (ρ : Representation A H W) : Type u :=
  Representation.IndV H.subtype (Representation.scalarExtension (k := K) ρ)

local instance inducedScalarExtensionTargetModuleA
    (ρ : Representation A H W) :
    Module A (inducedScalarExtensionTarget (A := A) (K := K) (G := G) ρ) :=
  Module.compHom _ (algebraMap A K)

local instance inducedScalarExtensionTargetIsScalarTower
    (ρ : Representation A H W) :
    IsScalarTower A K (inducedScalarExtensionTarget (A := A) (K := K) (G := G) ρ) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

private abbrev inducedScalarExtensionForwardSingle
    (ρ : Representation A H W) (g : G) :
    W →ₗ[A] inducedScalarExtensionTarget (A := A) (K := K) (G := G) ρ :=
  ((Representation.IndV.mk H.subtype (Representation.scalarExtension (k := K) ρ) g).restrictScalars A).comp
    (TensorProduct.mk A K W 1)

private noncomputable def inducedScalarExtensionForwardRaw
    (ρ : Representation A H W) :
    TensorProduct A (G →₀ A) W →ₗ[A]
      inducedScalarExtensionTarget (A := A) (K := K) (G := G) ρ :=
  TensorProduct.lift
    (Finsupp.linearCombination A
      (inducedScalarExtensionForwardSingle (A := A) (K := K) (G := G) (H := H) ρ))

private theorem inducedScalarExtensionForwardRaw_single_tmul
    (ρ : Representation A H W) (g : G) (a : A) (x : W) :
    inducedScalarExtensionForwardRaw (A := A) (K := K) (G := G) (H := H) ρ
        ((Finsupp.single g a) ⊗ₜ[A] x) =
      (algebraMap A K a) •
        Representation.IndV.mk H.subtype (Representation.scalarExtension (k := K) ρ) g
          ((1 : K) ⊗ₜ[A] x) := by
  simp [inducedScalarExtensionForwardRaw, inducedScalarExtensionForwardSingle]

private theorem inducedScalarExtensionForwardRaw_comp_source
    (ρ : Representation A H W) (h : H) :
    inducedScalarExtensionForwardRaw (A := A) (K := K) (G := G) (H := H) ρ ∘ₗ
        (Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρ) h =
      inducedScalarExtensionForwardRaw (A := A) (K := K) (G := G) (H := H) ρ := by
  classical
  apply LinearMap.ext
  intro y
  refine TensorProduct.induction_on y ?_ ?_ ?_
  · simp
  · intro f x
    induction f using Finsupp.induction_linear with
    | zero =>
        simp
    | add f₁ f₂ hf₁ hf₂ =>
        simpa [TensorProduct.add_tmul, map_add] using congrArg₂ HAdd.hAdd hf₁ hf₂
    | single g a =>
        have hcoinv :
            Representation.IndV.mk H.subtype (Representation.scalarExtension (k := K) ρ)
                ((h : G) * g) ((1 : K) ⊗ₜ[A] (ρ h x)) =
              Representation.IndV.mk H.subtype (Representation.scalarExtension (k := K) ρ)
                g ((1 : K) ⊗ₜ[A] x) := by
          simpa [Representation.IndV.mk, Representation.tprod_apply,
            Representation.ofMulAction_single] using
            (Representation.Coinvariants.mk_self_apply
              (Representation.tprod ((Representation.leftRegular K G).comp H.subtype)
                (Representation.scalarExtension (k := K) ρ))
              h ((Finsupp.single g (1 : K)) ⊗ₜ[K] ((1 : K) ⊗ₜ[A] x)))
        simp [Representation.tprod_apply, Representation.ofMulAction_single,
          inducedScalarExtensionForwardRaw_single_tmul, hcoinv]
  · intro y₁ y₂ hy₁ hy₂
    simpa [map_add] using congrArg₂ HAdd.hAdd hy₁ hy₂

private noncomputable def inducedScalarExtensionForwardFixedOne
    (ρ : Representation A H W) :
    Representation.IndV H.subtype ρ →ₗ[A]
      inducedScalarExtensionTarget (A := A) (K := K) (G := G) ρ := by
  let ρrawA : Representation A H (TensorProduct A (G →₀ A) W) :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρ
  let raw : TensorProduct A (G →₀ A) W →ₗ[A]
      inducedScalarExtensionTarget (A := A) (K := K) (G := G) ρ :=
    inducedScalarExtensionForwardRaw (A := A) (K := K) (G := G) (H := H) ρ
  exact Representation.Coinvariants.lift ρrawA raw
    (fun h => by
      simpa [ρrawA, raw] using
        inducedScalarExtensionForwardRaw_comp_source
          (A := A) (K := K) (G := G) (H := H) ρ h)

private theorem inducedScalarExtensionForwardFixedOne_apply_mk
    (ρ : Representation A H W) (g : G) (x : W) :
    inducedScalarExtensionForwardFixedOne (A := A) (K := K) (G := G) (H := H) ρ
        (Representation.IndV.mk H.subtype ρ g x) =
      Representation.IndV.mk H.subtype (Representation.scalarExtension (k := K) ρ) g
        ((1 : K) ⊗ₜ[A] x) := by
  simp [inducedScalarExtensionForwardFixedOne, Representation.IndV.mk,
    inducedScalarExtensionForwardRaw_single_tmul]

private noncomputable def inducedScalarExtensionForward
    (ρ : Representation A H W) :
    K ⊗[A] Representation.IndV H.subtype ρ →ₗ[K]
      inducedScalarExtensionTarget (A := A) (K := K) (G := G) ρ :=
  (inducedScalarExtensionForwardFixedOne (A := A) (K := K) (G := G) (H := H) ρ).liftBaseChange K

private theorem inducedScalarExtensionForward_apply_tmul_mk
    (ρ : Representation A H W) (z : K) (g : G) (x : W) :
    inducedScalarExtensionForward (A := A) (K := K) (G := G) (H := H) ρ
        (z ⊗ₜ[A] Representation.IndV.mk H.subtype ρ g x) =
      Representation.IndV.mk H.subtype (Representation.scalarExtension (k := K) ρ) g
        (z ⊗ₜ[A] x) := by
  calc
    inducedScalarExtensionForward (A := A) (K := K) (G := G) (H := H) ρ
        (z ⊗ₜ[A] Representation.IndV.mk H.subtype ρ g x) =
      z •
        inducedScalarExtensionForwardFixedOne (A := A) (K := K) (G := G) (H := H) ρ
          (Representation.IndV.mk H.subtype ρ g x) := by
            simp [inducedScalarExtensionForward, LinearMap.liftBaseChange_tmul]
    _ = z •
      Representation.IndV.mk H.subtype (Representation.scalarExtension (k := K) ρ) g
        ((1 : K) ⊗ₜ[A] x) := by
          rw [inducedScalarExtensionForwardFixedOne_apply_mk]
    _ = Representation.IndV.mk H.subtype (Representation.scalarExtension (k := K) ρ) g
        (z ⊗ₜ[A] x) := by
          rw [← (Representation.IndV.mk H.subtype
            (Representation.scalarExtension (k := K) ρ) g).map_smul]
          congr 1
          simpa [one_mul] using TensorProduct.smul_tmul' z (1 : K) x

private noncomputable def inducedScalarExtensionBackwardSingle
    (ρ : Representation A H W) (g : G) :
    (K ⊗[A] W) →ₗ[K] K ⊗[A] Representation.IndV H.subtype ρ :=
  (Representation.IndV.mk H.subtype ρ g).baseChange K

private noncomputable def inducedScalarExtensionBackwardRaw
    (ρ : Representation A H W) :
    TensorProduct K (G →₀ K) (K ⊗[A] W) →ₗ[K]
      K ⊗[A] Representation.IndV H.subtype ρ :=
  TensorProduct.lift
    (Finsupp.linearCombination K
      (inducedScalarExtensionBackwardSingle (A := A) (K := K) (G := G) (H := H) ρ))

private theorem inducedScalarExtensionBackwardRaw_single_tmul_tmul
    (ρ : Representation A H W) (g : G) (c z : K) (x : W) :
    inducedScalarExtensionBackwardRaw (A := A) (K := K) (G := G) (H := H) ρ
        ((Finsupp.single g c) ⊗ₜ[K] (z ⊗ₜ[A] x)) =
      (c * z) ⊗ₜ[A] Representation.IndV.mk H.subtype ρ g x := by
  calc
    inducedScalarExtensionBackwardRaw (A := A) (K := K) (G := G) (H := H) ρ
        ((Finsupp.single g c) ⊗ₜ[K] (z ⊗ₜ[A] x)) =
      c • (z ⊗ₜ[A] Representation.IndV.mk H.subtype ρ g x) := by
        simp [inducedScalarExtensionBackwardRaw, inducedScalarExtensionBackwardSingle,
          LinearMap.baseChange_tmul]
    _ = (c * z) ⊗ₜ[A] Representation.IndV.mk H.subtype ρ g x := by
        simpa using TensorProduct.smul_tmul' c z (Representation.IndV.mk H.subtype ρ g x)

private theorem inducedScalarExtensionBackwardRaw_comp_source
    (ρ : Representation A H W) (h : H) :
    inducedScalarExtensionBackwardRaw (A := A) (K := K) (G := G) (H := H) ρ ∘ₗ
        (Representation.tprod ((Representation.leftRegular K G).comp H.subtype)
          (Representation.scalarExtension (k := K) ρ)) h =
      inducedScalarExtensionBackwardRaw (A := A) (K := K) (G := G) (H := H) ρ := by
  classical
  apply LinearMap.ext
  intro y
  refine TensorProduct.induction_on y ?_ ?_ ?_
  · simp
  · intro f x
    induction f using Finsupp.induction_linear with
    | zero =>
        simp
    | add f₁ f₂ hf₁ hf₂ =>
        simpa [TensorProduct.add_tmul, map_add] using congrArg₂ HAdd.hAdd hf₁ hf₂
    | single g c =>
        refine TensorProduct.induction_on x ?_ ?_ ?_
        · simp
        · intro z x
          have hcoinv :
              Representation.IndV.mk H.subtype ρ ((h : G) * g) (ρ h x) =
                Representation.IndV.mk H.subtype ρ g x := by
            simpa [Representation.IndV.mk, Representation.tprod_apply,
              Representation.ofMulAction_single] using
              (Representation.Coinvariants.mk_self_apply
                (Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρ)
                h ((Finsupp.single g (1 : A)) ⊗ₜ[A] x))
          have hbase :
              (Representation.scalarExtension (k := K) ρ h) (z ⊗ₜ[A] x) =
                z ⊗ₜ[A] (ρ h x) := by
            change ((ρ h).baseChange K) (z ⊗ₜ[A] x) = z ⊗ₜ[A] (ρ h x)
            rw [LinearMap.baseChange_tmul]
          calc
            (inducedScalarExtensionBackwardRaw (A := A) (K := K) (G := G) (H := H) ρ ∘ₗ
                (Representation.tprod ((Representation.leftRegular K G).comp H.subtype)
                  (Representation.scalarExtension (k := K) ρ)) h)
                ((Finsupp.single g c) ⊗ₜ[K] (z ⊗ₜ[A] x)) =
              inducedScalarExtensionBackwardRaw (A := A) (K := K) (G := G) (H := H) ρ
                ((Finsupp.single ((h : G) * g) c) ⊗ₜ[K]
                  ((Representation.scalarExtension (k := K) ρ h) (z ⊗ₜ[A] x))) := by
                  simp [Representation.tprod_apply, Representation.ofMulAction_single]
            _ =
              inducedScalarExtensionBackwardRaw (A := A) (K := K) (G := G) (H := H) ρ
                ((Finsupp.single ((h : G) * g) c) ⊗ₜ[K] (z ⊗ₜ[A] (ρ h x))) := by
                  rw [hbase]
            _ = (c * z) ⊗ₜ[A]
                  Representation.IndV.mk H.subtype ρ ((h : G) * g) (ρ h x) := by
                  rw [inducedScalarExtensionBackwardRaw_single_tmul_tmul]
            _ = (c * z) ⊗ₜ[A] Representation.IndV.mk H.subtype ρ g x := by
                  rw [hcoinv]
            _ = inducedScalarExtensionBackwardRaw (A := A) (K := K) (G := G) (H := H) ρ
                ((Finsupp.single g c) ⊗ₜ[K] (z ⊗ₜ[A] x)) := by
                  rw [inducedScalarExtensionBackwardRaw_single_tmul_tmul]
        · intro x₁ x₂ hx₁ hx₂
          simpa [TensorProduct.tmul_add, map_add] using congrArg₂ HAdd.hAdd hx₁ hx₂
  · intro y₁ y₂ hy₁ hy₂
    simpa [map_add] using congrArg₂ HAdd.hAdd hy₁ hy₂

private noncomputable def inducedScalarExtensionBackward
    (ρ : Representation A H W) :
    inducedScalarExtensionTarget (A := A) (K := K) (G := G) ρ →ₗ[K]
      K ⊗[A] Representation.IndV H.subtype ρ := by
  let ρrawK : Representation K H (TensorProduct K (G →₀ K) (K ⊗[A] W)) :=
    Representation.tprod ((Representation.leftRegular K G).comp H.subtype)
      (Representation.scalarExtension (k := K) ρ)
  let raw : TensorProduct K (G →₀ K) (K ⊗[A] W) →ₗ[K]
      K ⊗[A] Representation.IndV H.subtype ρ :=
    inducedScalarExtensionBackwardRaw (A := A) (K := K) (G := G) (H := H) ρ
  exact Representation.Coinvariants.lift ρrawK raw
    (fun h => by
      simpa [ρrawK, raw] using
        inducedScalarExtensionBackwardRaw_comp_source
          (A := A) (K := K) (G := G) (H := H) ρ h)

private theorem inducedScalarExtensionBackward_apply_mk_tmul
    (ρ : Representation A H W) (g : G) (z : K) (x : W) :
    inducedScalarExtensionBackward (A := A) (K := K) (G := G) (H := H) ρ
        (Representation.IndV.mk H.subtype (Representation.scalarExtension (k := K) ρ) g
          (z ⊗ₜ[A] x)) =
      z ⊗ₜ[A] Representation.IndV.mk H.subtype ρ g x := by
  simp [inducedScalarExtensionBackward, Representation.IndV.mk,
    inducedScalarExtensionBackwardRaw_single_tmul_tmul]

private theorem inducedScalarExtension_forward_backward
    (ρ : Representation A H W) :
    inducedScalarExtensionForward (A := A) (K := K) (G := G) (H := H) ρ ∘ₗ
        inducedScalarExtensionBackward (A := A) (K := K) (G := G) (H := H) ρ =
      LinearMap.id := by
  apply Representation.IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [LinearMap.comp_apply]
  · intro z x
    calc
      (inducedScalarExtensionForward (A := A) (K := K) (G := G) (H := H) ρ ∘ₗ
          inducedScalarExtensionBackward (A := A) (K := K) (G := G) (H := H) ρ)
          (Representation.IndV.mk H.subtype (Representation.scalarExtension (k := K) ρ) g
            (z ⊗ₜ[A] x)) =
        inducedScalarExtensionForward (A := A) (K := K) (G := G) (H := H) ρ
          (z ⊗ₜ[A] Representation.IndV.mk H.subtype ρ g x) := by
            rw [LinearMap.comp_apply, inducedScalarExtensionBackward_apply_mk_tmul]
      _ = Representation.IndV.mk H.subtype (Representation.scalarExtension (k := K) ρ) g
            (z ⊗ₜ[A] x) := by
            rw [inducedScalarExtensionForward_apply_tmul_mk]
      _ = (LinearMap.id :
            inducedScalarExtensionTarget (A := A) (K := K) (G := G) ρ →ₗ[K]
              inducedScalarExtensionTarget (A := A) (K := K) (G := G) ρ)
          (Representation.IndV.mk H.subtype (Representation.scalarExtension (k := K) ρ) g
            (z ⊗ₜ[A] x)) := by
            rfl
  · intro x₁ x₂ hx₁ hx₂
    simpa [map_add, LinearMap.comp_apply] using congrArg₂ HAdd.hAdd hx₁ hx₂

private theorem inducedScalarExtension_backward_forward
    (ρ : Representation A H W) :
    inducedScalarExtensionBackward (A := A) (K := K) (G := G) (H := H) ρ ∘ₗ
        inducedScalarExtensionForward (A := A) (K := K) (G := G) (H := H) ρ =
      LinearMap.id := by
  apply LinearMap.ext
  intro y
  refine TensorProduct.induction_on y ?_ ?_ ?_
  · simp [LinearMap.comp_apply]
  · intro z v
    let lhs : Representation.IndV H.subtype ρ →ₗ[A]
        K ⊗[A] Representation.IndV H.subtype ρ :=
      ((inducedScalarExtensionBackward (A := A) (K := K) (G := G) (H := H) ρ ∘ₗ
        inducedScalarExtensionForward (A := A) (K := K) (G := G) (H := H) ρ).restrictScalars A).comp
        (TensorProduct.mk A K (Representation.IndV H.subtype ρ) z)
    let rhs : Representation.IndV H.subtype ρ →ₗ[A]
        K ⊗[A] Representation.IndV H.subtype ρ :=
      TensorProduct.mk A K (Representation.IndV H.subtype ρ) z
    change lhs v = rhs v
    apply LinearMap.congr_fun
    apply Representation.IndV.hom_ext
    intro g
    apply LinearMap.ext
    intro x
    change lhs (Representation.IndV.mk H.subtype ρ g x) =
      rhs (Representation.IndV.mk H.subtype ρ g x)
    calc
      lhs (Representation.IndV.mk H.subtype ρ g x) =
        inducedScalarExtensionBackward (A := A) (K := K) (G := G) (H := H) ρ
          (inducedScalarExtensionForward (A := A) (K := K) (G := G) (H := H) ρ
            (z ⊗ₜ[A] Representation.IndV.mk H.subtype ρ g x)) := by
            rfl
      _ = inducedScalarExtensionBackward (A := A) (K := K) (G := G) (H := H) ρ
          (Representation.IndV.mk H.subtype (Representation.scalarExtension (k := K) ρ) g
            (z ⊗ₜ[A] x)) := by
            rw [inducedScalarExtensionForward_apply_tmul_mk]
      _ = z ⊗ₜ[A] Representation.IndV.mk H.subtype ρ g x := by
            rw [inducedScalarExtensionBackward_apply_mk_tmul]
      _ = rhs (Representation.IndV.mk H.subtype ρ g x) := by
            rfl
  · intro y₁ y₂ hy₁ hy₂
    simpa [map_add, LinearMap.comp_apply] using congrArg₂ HAdd.hAdd hy₁ hy₂

/-- Scalar extension commutes with subgroup induction on the concrete induced module. -/
noncomputable def inducedScalarExtensionLinearEquiv
    (ρ : Representation A H W) :
    (K ⊗[A] Representation.IndV H.subtype ρ) ≃ₗ[K]
      Representation.IndV H.subtype (Representation.scalarExtension (k := K) ρ) :=
  LinearEquiv.ofLinear
    (inducedScalarExtensionForward (A := A) (K := K) (G := G) (H := H) ρ)
    (inducedScalarExtensionBackward (A := A) (K := K) (G := G) (H := H) ρ)
    (inducedScalarExtension_forward_backward (A := A) (K := K) (G := G) (H := H) ρ)
    (inducedScalarExtension_backward_forward (A := A) (K := K) (G := G) (H := H) ρ)

theorem inducedScalarExtensionLinearEquiv_apply_tmul_mk
    (ρ : Representation A H W) (z : K) (g : G) (x : W) :
    inducedScalarExtensionLinearEquiv (A := A) (K := K) (G := G) (H := H) ρ
        (z ⊗ₜ[A] Representation.IndV.mk H.subtype ρ g x) =
      Representation.IndV.mk H.subtype (Representation.scalarExtension (k := K) ρ) g
        (z ⊗ₜ[A] x) :=
  by
    change inducedScalarExtensionForward (A := A) (K := K) (G := G) (H := H) ρ
        (z ⊗ₜ[A] Representation.IndV.mk H.subtype ρ g x) =
      Representation.IndV.mk H.subtype (Representation.scalarExtension (k := K) ρ) g
        (z ⊗ₜ[A] x)
    exact inducedScalarExtensionForward_apply_tmul_mk
      (A := A) (K := K) (G := G) (H := H) ρ z g x

private theorem inducedScalarExtensionLinearEquiv_comm
    (ρ : Representation A H W) (g₀ : G) (x : K ⊗[A] Representation.IndV H.subtype ρ) :
    inducedScalarExtensionLinearEquiv (A := A) (K := K) (G := G) (H := H) ρ
        ((Representation.scalarExtension (k := K) (Representation.ind H.subtype ρ)) g₀ x) =
      Representation.ind H.subtype (Representation.scalarExtension (k := K) ρ) g₀
        (inducedScalarExtensionLinearEquiv (A := A) (K := K) (G := G) (H := H) ρ x) := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro z v
    let e : (K ⊗[A] Representation.IndV H.subtype ρ) ≃ₗ[K]
        Representation.IndV H.subtype (Representation.scalarExtension (k := K) ρ) :=
      inducedScalarExtensionLinearEquiv (A := A) (K := K) (G := G) (H := H) ρ
    let lhs : Representation.IndV H.subtype ρ →ₗ[A]
        Representation.IndV H.subtype (Representation.scalarExtension (k := K) ρ) :=
      (e.toLinearMap.restrictScalars A).comp
        ((TensorProduct.mk A K (Representation.IndV H.subtype ρ) z).comp
          ((Representation.ind H.subtype ρ) g₀))
    let rhs : Representation.IndV H.subtype ρ →ₗ[A]
        Representation.IndV H.subtype (Representation.scalarExtension (k := K) ρ) :=
      (((Representation.ind H.subtype (Representation.scalarExtension (k := K) ρ)) g₀).restrictScalars A).comp
        ((e.toLinearMap.restrictScalars A).comp
          (TensorProduct.mk A K (Representation.IndV H.subtype ρ) z))
    change lhs v = rhs v
    apply LinearMap.congr_fun
    apply Representation.IndV.hom_ext
    intro g
    apply LinearMap.ext
    intro x
    calc
      lhs (Representation.IndV.mk H.subtype ρ g x) =
        e (z ⊗ₜ[A] Representation.ind H.subtype ρ g₀
          (Representation.IndV.mk H.subtype ρ g x)) := by
          rfl
      _ = e (z ⊗ₜ[A] Representation.IndV.mk H.subtype ρ (g * g₀⁻¹) x) := by
          rw [Representation.ind_mk]
      _ = Representation.IndV.mk H.subtype (Representation.scalarExtension (k := K) ρ)
          (g * g₀⁻¹) (z ⊗ₜ[A] x) := by
          rw [inducedScalarExtensionLinearEquiv_apply_tmul_mk]
      _ = Representation.ind H.subtype (Representation.scalarExtension (k := K) ρ) g₀
          (Representation.IndV.mk H.subtype (Representation.scalarExtension (k := K) ρ) g
            (z ⊗ₜ[A] x)) := by
          rw [Representation.ind_mk]
      _ = rhs (Representation.IndV.mk H.subtype ρ g x) := by
          change
            Representation.ind H.subtype (Representation.scalarExtension (k := K) ρ) g₀
                (Representation.IndV.mk H.subtype (Representation.scalarExtension (k := K) ρ) g
                  (z ⊗ₜ[A] x)) =
              Representation.ind H.subtype (Representation.scalarExtension (k := K) ρ) g₀
                (e (z ⊗ₜ[A] Representation.IndV.mk H.subtype ρ g x))
          rw [inducedScalarExtensionLinearEquiv_apply_tmul_mk]
  · intro x₁ x₂ hx₁ hx₂
    simp [map_add, hx₁, hx₂]

/-- Scalar extension of a `Rep.ind` representation is isomorphic to induction of the scalar
extended source representation. -/
noncomputable def scalarExtension_ind_iso_ind_scalarExtension
    (ρ : Representation A H W) :
    Rep.of (Representation.scalarExtension (k := K) (Representation.ind H.subtype ρ)) ≅
      Rep.ind H.subtype (Rep.of (Representation.scalarExtension (k := K) ρ)) :=
  Rep.mkIso
    (Representation.Equiv.mk
      (inducedScalarExtensionLinearEquiv (A := A) (K := K) (G := G) (H := H) ρ)
      (by
        intro g
        apply LinearMap.ext
        intro x
        exact inducedScalarExtensionLinearEquiv_comm
          (A := A) (K := K) (G := G) (H := H) ρ g x))

end InducedScalarExtension

section ProjectiveClasses

variable {A : Type u} [CommRing A]
variable {K : Type u} [Field K] [Algebra A K]
variable {G : Type u} [Group G] [Finite G]

private noncomputable def scalarExtensionIsoOfRepIso
    {V W : Type u} [AddCommGroup V] [Module A V]
    [AddCommGroup W] [Module A W]
    {ρ : Representation A G V} {σ : Representation A G W}
    (e : Rep.of ρ ≅ Rep.of σ) :
    Rep.of (Representation.scalarExtension (k := K) ρ) ≅
      Rep.of (Representation.scalarExtension (k := K) σ) := by
  let eA : V ≃ₗ[A] W :=
    { toFun := e.hom.hom.toLinearMap
      invFun := e.inv.hom.toLinearMap
      left_inv := by
        intro x
        have h := congrArg (fun f : Rep.of ρ ⟶ Rep.of ρ => f.hom.toLinearMap x)
          e.hom_inv_id
        simpa using h
      right_inv := by
        intro x
        have h := congrArg (fun f : Rep.of σ ⟶ Rep.of σ => f.hom.toLinearMap x)
          e.inv_hom_id
        simpa using h
      map_add' := e.hom.hom.toLinearMap.map_add
      map_smul' := e.hom.hom.toLinearMap.map_smul }
  let eK : K ⊗[A] V ≃ₗ[K] K ⊗[A] W :=
    eA.baseChange A K V W
  refine Rep.mkIso (Representation.Equiv.mk eK ?_)
  intro g
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  have hx := LinearMap.congr_fun (e.hom.hom.isIntertwining' g) x
  simpa [Representation.scalarExtension, eK, eA] using
    congrArg (fun y => a ⊗ₜ[A] y) hx

private theorem fdRepClass_eq_of_rep_iso
    {V W : FDRep K G}
    (eRep : ((forget₂ (FDRep K G) (Rep K G)).obj V) ≅
      ((forget₂ (FDRep K G) (Rep K G)).obj W)) :
    [V]₀ = [W]₀ := by
  let e : V ≅ W := by
    refine ⟨(FDRep.forget₂HomLinearEquiv V W) eRep.hom,
      (FDRep.forget₂HomLinearEquiv W V) eRep.inv, ?_, ?_⟩
    · apply (forget₂ (FDRep K G) (Rep K G)).map_injective
      change eRep.hom ≫ eRep.inv = 𝟙 _
      exact eRep.hom_inv_id
    · apply (forget₂ (FDRep K G) (Rep K G)).map_injective
      change eRep.inv ≫ eRep.hom = 𝟙 _
      exact eRep.inv_hom_id
  exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := K) (G := G) ⟨e⟩

/-- On projective generators, finite-representation induction commutes with scalar extension. -/
theorem finiteRep_subgroupInduction_projective_scalarExtension_class_eq
    (H : Subgroup G) (Q : FiniteProjectiveGroupAlgebraModule A H) :
    finiteRep_subgroupInduction (G := G) H [Q.scalarExtension K]₀ =
      [(Q.subgroupInductionBase (G := G)).scalarExtension K]₀ := by
  rw [finiteRep_subgroupInduction_apply_class]
  apply fdRepClass_eq_of_rep_iso (K := K) (G := G)
  let ρ : Representation A H Q.V := Representation.ofModule' Q.V
  let e₁ :
      ((forget₂ (FDRep K G) (Rep K G)).obj
        (FDRep.subgroupInduction (k := K) (G := G) (H := H) (Q.scalarExtension K))) ≅
        Rep.ind H.subtype (Rep.of (Representation.scalarExtension (k := K) ρ)) := by
    simpa [FDRep.subgroupInduction, FiniteProjectiveGroupAlgebraModule.scalarExtension, ρ] using
      (Iso.refl (Rep.ind H.subtype (Rep.of (Representation.scalarExtension (k := K) ρ))))
  let e₂ :
      Rep.ind H.subtype (Rep.of (Representation.scalarExtension (k := K) ρ)) ≅
        Rep.of (Representation.scalarExtension (k := K) (Representation.ind H.subtype ρ)) := by
    exact (scalarExtension_ind_iso_ind_scalarExtension
      (A := A) (K := K) (G := G) (H := H) ρ).symm
  let e₃ :
      Rep.of (Representation.scalarExtension (k := K) (Representation.ind H.subtype ρ)) ≅
        ((forget₂ (FDRep K G) (Rep K G)).obj
          ((Q.subgroupInductionBase (G := G)).scalarExtension K)) := by
    let σ : Representation A G (Representation.IndV H.subtype ρ) :=
      Representation.ind H.subtype ρ
    let M : ModuleCat A[G] := Rep.toModuleMonoidAlgebra.obj (Rep.of σ)
    letI : Module A M := Module.compHom M (algebraMap A A[G])
    letI : IsScalarTower A A[G] M :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    let τ : Representation A G M := Representation.ofModule' M
    have eBase : Rep.of σ ≅ Rep.of τ := by
      simpa [σ, τ, M] using Rep.unitIso (Rep.of σ)
    have eK := scalarExtensionIsoOfRepIso (A := A) (K := K) (G := G) eBase
    simpa [σ, τ, M, FiniteProjectiveGroupAlgebraModule.subgroupInductionBase,
      FiniteProjectiveGroupAlgebraModule.scalarExtension, FiniteProjectiveGroupAlgebraModule.toRep,
      ρ] using eK
  exact e₁ ≪≫ e₂ ≪≫ e₃

end ProjectiveClasses

section ReductionClasses

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {G : Type u} [Group G] [Finite G]

local notation "κ" => IsLocalRing.ResidueField A

/-- On projective generators, residue-field reduction commutes with subgroup induction. -/
theorem projective_subgroupInduction_residueFieldReduction_class_eq
    (H : Subgroup G) (Q : FiniteProjectiveGroupAlgebraModule A H) :
    projective_subgroupInduction (G := G) H [Q.residueFieldReduction]ₚ₀ =
      [(Q.subgroupInductionBase (G := G)).residueFieldReduction]ₚ₀ := by
  rw [projective_subgroupInduction_apply_class_base]
  apply finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso
  apply
    (finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
      (A := κ) (G := G)
      ((Q.residueFieldReduction).subgroupInductionBase (G := G))
      ((Q.subgroupInductionBase (G := G)).residueFieldReduction)).2
  refine ⟨?_⟩
  let ρ : Representation A H Q.toRep := Q.toRep.ρ
  let σ : Representation A G (Representation.IndV H.subtype ρ) :=
    Representation.ind H.subtype ρ
  let M : ModuleCat A[G] := Rep.toModuleMonoidAlgebra.obj (Rep.of σ)
  letI : Module A M := Module.compHom M (algebraMap A A[G])
  letI : IsScalarTower A A[G] M :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let τ : Representation A G M := Representation.ofModule' M
  have eBase : Rep.of σ ≅ Rep.of τ := by
    simpa [σ, τ, M] using Rep.unitIso (Rep.of σ)
  let e₁ :
      Rep.ind H.subtype (Rep.of (Representation.scalarExtension (k := κ) ρ)) ≅
        Rep.of (Representation.scalarExtension (k := κ) σ) :=
    (scalarExtension_ind_iso_ind_scalarExtension
      (A := A) (K := κ) (G := G) (H := H) ρ).symm
  let e₂ :
      Rep.of (Representation.scalarExtension (k := κ) σ) ≅
        Rep.of (Representation.scalarExtension (k := κ) τ) :=
    scalarExtensionIsoOfRepIso (A := A) (K := κ) (G := G) eBase
  have eSrcBase :
      (Q.residueFieldReduction).toRep ≅
        Rep.of (Representation.scalarExtension (k := κ) ρ) := by
    simpa [FiniteProjectiveGroupAlgebraModule.residueFieldReduction,
      FiniteProjectiveGroupAlgebraModule.toRep, ρ] using
      (Rep.unitIso (Rep.of (Representation.scalarExtension (k := κ) ρ))).symm
  let eSrc :=
    (Rep.toModuleMonoidAlgebra.mapIso
      ((Rep.indFunctor κ H.subtype).mapIso eSrcBase)).toLinearEquiv
  let eCore :=
    (Rep.toModuleMonoidAlgebra.mapIso (e₁ ≪≫ e₂)).toLinearEquiv
  let eTgtRep :
      Rep.of (Representation.scalarExtension (k := κ) τ) ≅
        Rep.ofModuleMonoidAlgebra.obj (ModuleCat.of κ[G] (κ ⊗[A] M)) := by
    simpa [τ] using
      Rep.unitIso (Rep.of (Representation.scalarExtension (k := κ) τ))
  let eTgt :
      Rep.toModuleMonoidAlgebra.obj (Rep.of (Representation.scalarExtension (k := κ) τ)) ≅
        ModuleCat.of κ[G] (κ ⊗[A] M) := by
    exact
      Rep.toModuleMonoidAlgebra.mapIso eTgtRep ≪≫
        Rep.counitIso (ModuleCat.of κ[G] (κ ⊗[A] M))
  let e := eSrc.trans (eCore.trans eTgt.toLinearEquiv)
  simpa [FiniteProjectiveGroupAlgebraModule.subgroupInductionBase,
    FiniteProjectiveGroupAlgebraModule.residueFieldReduction,
    FiniteProjectiveGroupAlgebraModule.toRep, ρ, σ, M, τ] using e

end ReductionClasses

end Representation
