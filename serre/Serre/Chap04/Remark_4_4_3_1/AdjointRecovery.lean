import Mathlib
import Serre.Chap04.Remark_4_4_3_1.InvariantDual

noncomputable section

universe u v w

namespace Representation

namespace Remark_4_4_3_1

section AdjointRecovery

variable {G : Type u} [MeasurableSpace G] [Group G] [TopologicalSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
variable {W : Type v} [TopologicalSpace W] [AddCommGroup W] [Module ℂ W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℂ W] [T2Space W] [FiniteDimensional ℂ W]
variable {V : Type w} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable (σ : Representation ℂ G W) (τ : Representation ℂ G V)

/-- Helper for Remark 4-4.3-1: for a unitary target representation, the `J`-adjoint candidate
exists as the vector representing `x ↦ inner ℂ v (T x)`. -/
theorem exists_intertwiningMap_toDualAdjointLinear_generic
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (T : σ.IntertwiningMap τ) :
    ∃ A : V →ₗ[ℂ] W,
      ∀ (v : V) (x : W), J (A v) x = inner ℂ v (T x) := by
  refine ⟨{
      toFun := fun v ↦
        J.symm
          { toFun := fun x ↦ inner ℂ v (T x)
            map_add' := by
              intro x y
              simp
            map_smul' := by
              intro a x
              simp }
      map_add' := by
        intro v w
        apply J.injective
        ext x
        simp
      map_smul' := by
        intro a v
        apply J.injective
        ext x
        simp [LinearEquiv.map_smulₛₗ, mul_comm]
    }, ?_⟩
  intro v x
  simp

/-- Helper for Remark 4-4.3-1: the generic `J`-adjoint linear candidate chosen from the Riesz
representation data. -/
noncomputable def intertwiningMap_toDualAdjointLinear_generic
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (T : σ.IntertwiningMap τ) :
    V →ₗ[ℂ] W :=
  Classical.choose (exists_intertwiningMap_toDualAdjointLinear_generic
    (σ := σ) (τ := τ) J T)

/-- Helper for Remark 4-4.3-1: evaluating the generic `J`-adjoint candidate against a source
vector recovers the target inner product. -/
theorem intertwiningMap_toDualAdjointLinear_generic_apply
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (T : σ.IntertwiningMap τ) (v : V) (x : W) :
    J (intertwiningMap_toDualAdjointLinear_generic (σ := σ) (τ := τ) J T v) x =
      inner ℂ v (T x) :=
  Classical.choose_spec (exists_intertwiningMap_toDualAdjointLinear_generic
    (σ := σ) (τ := τ) J T) v x

/-- Helper for Remark 4-4.3-1: the generic `J`-adjoint candidate is again an intertwining map
whenever the target representation preserves the inner product. -/
theorem intertwiningMap_toDualAdjointLinear_generic_isIntertwining
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hτ_inner_map_map : ∀ g : G, ∀ v w : V, inner ℂ (τ g v) (τ g w) = inner ℂ v w)
    (T : σ.IntertwiningMap τ) :
    ∀ g : G,
      intertwiningMap_toDualAdjointLinear_generic (σ := σ) (τ := τ) J T ∘ₗ τ g =
        σ g ∘ₗ intertwiningMap_toDualAdjointLinear_generic (σ := σ) (τ := τ) J T := by
  intro g
  ext v
  apply J.injective
  ext x
  calc
    J (intertwiningMap_toDualAdjointLinear_generic (σ := σ) (τ := τ) J T (τ g v)) x
        = inner ℂ (τ g v) (T x) := by
            rw [intertwiningMap_toDualAdjointLinear_generic_apply (σ := σ) (τ := τ)]
    _ = inner ℂ v (τ g⁻¹ (T x)) := by
          have hinner := hτ_inner_map_map g v (τ g⁻¹ (T x))
          simpa [map_mul] using hinner
    _ = inner ℂ v (T (σ g⁻¹ x)) := by
          have hT : T (σ g⁻¹ x) = τ g⁻¹ (T x) := by
            simpa using congr($(T.isIntertwining' g⁻¹) x)
          exact congrArg (fun z ↦ inner ℂ v z) hT.symm
    _ = J (intertwiningMap_toDualAdjointLinear_generic (σ := σ) (τ := τ) J T v) (σ g⁻¹ x) := by
          rw [intertwiningMap_toDualAdjointLinear_generic_apply (σ := σ) (τ := τ)]
    _ = J (σ g (intertwiningMap_toDualAdjointLinear_generic (σ := σ) (τ := τ) J T v)) x := by
          have hrewrite :=
            hJ g
              (intertwiningMap_toDualAdjointLinear_generic (σ := σ) (τ := τ) J T v)
              (σ g⁻¹ x)
          simpa [map_mul] using hrewrite.symm

/-- Helper for Remark 4-4.3-1: package the generic `J`-adjoint candidate as an intertwining map
from the unitary target back to `σ`. -/
noncomputable def intertwiningMap_toDualAdjoint_generic
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hτ_inner_map_map : ∀ g : G, ∀ v w : V, inner ℂ (τ g v) (τ g w) = inner ℂ v w)
    (T : σ.IntertwiningMap τ) :
    τ.IntertwiningMap σ :=
  { toLinearMap := intertwiningMap_toDualAdjointLinear_generic (σ := σ) (τ := τ) J T
    isIntertwining' :=
      intertwiningMap_toDualAdjointLinear_generic_isIntertwining
        (σ := σ) (τ := τ) J hJ hτ_inner_map_map T }

/-- Helper for Remark 4-4.3-1: the generic `J`-adjoint construction is conjugate-linear in the
original intertwiner. -/
theorem exists_intertwiningMap_toDualAdjointMap_generic
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hτ_inner_map_map : ∀ g : G, ∀ v w : V, inner ℂ (τ g v) (τ g w) = inner ℂ v w) :
    ∃ A : σ.IntertwiningMap τ →ₗ⋆[ℂ] τ.IntertwiningMap σ,
      ∀ (T : σ.IntertwiningMap τ) (v : V) (x : W),
        J (A T v) x = inner ℂ v (T x) := by
  refine ⟨{
      toFun := fun T ↦ intertwiningMap_toDualAdjoint_generic
        (σ := σ) (τ := τ) J hJ hτ_inner_map_map T
      map_add' := by
        intro T₁ T₂
        apply Representation.IntertwiningMap.ext
        ext v
        apply J.injective
        ext x
        simp [intertwiningMap_toDualAdjoint_generic,
          intertwiningMap_toDualAdjointLinear_generic_apply]
      map_smul' := by
        intro a T
        apply Representation.IntertwiningMap.ext
        ext v
        apply J.injective
        ext x
        simp [LinearEquiv.map_smulₛₗ, intertwiningMap_toDualAdjoint_generic,
          intertwiningMap_toDualAdjointLinear_generic_apply]
    }, ?_⟩
  intro T v x
  exact intertwiningMap_toDualAdjointLinear_generic_apply (σ := σ) (τ := τ) J T v x

/-- Helper for Remark 4-4.3-1: the generic conjugate-linear `J`-adjoint map. -/
noncomputable def intertwiningMap_toDualAdjointMap_generic
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hτ_inner_map_map : ∀ g : G, ∀ v w : V, inner ℂ (τ g v) (τ g w) = inner ℂ v w) :
    σ.IntertwiningMap τ →ₗ⋆[ℂ] τ.IntertwiningMap σ :=
  Classical.choose (exists_intertwiningMap_toDualAdjointMap_generic
    (σ := σ) (τ := τ) J hJ hτ_inner_map_map)

/-- Helper for Remark 4-4.3-1: evaluating the generic conjugate-linear `J`-adjoint construction
against `J` recovers the target inner product pairing. -/
theorem intertwiningMap_toDualAdjointMap_generic_apply
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hτ_inner_map_map : ∀ g : G, ∀ v w : V, inner ℂ (τ g v) (τ g w) = inner ℂ v w)
    (T : σ.IntertwiningMap τ) (v : V) (x : W) :
    J
        (intertwiningMap_toDualAdjointMap_generic
          (σ := σ) (τ := τ) J hJ hτ_inner_map_map T v) x =
      inner ℂ v (T x) :=
  Classical.choose_spec (exists_intertwiningMap_toDualAdjointMap_generic
    (σ := σ) (τ := τ) J hJ hτ_inner_map_map) T v x

/-- Helper for Remark 4-4.3-1: for fixed `T`, the starred Schur test pairing is additive in the
vector argument for any coefficient family `Φ`. -/
theorem testPairing_map_add_generic [σ.IsIrreducible]
    (Φ : Module.Dual ℂ W →ₗ[ℂ] σ.IntertwiningMap τ)
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hτ_inner_map_map : ∀ g : G, ∀ v w : V, inner ℂ (τ g v) (τ g w) = inner ℂ v w)
    (T : σ.IntertwiningMap τ) (x y : W) :
    star
        (scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap_generic
              (σ := σ) (τ := τ) J hJ hτ_inner_map_map T).comp
            (Φ (J (x + y))))) =
      star
        (scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap_generic
              (σ := σ) (τ := τ) J hJ hτ_inner_map_map T).comp
            (Φ (J x)))) +
        star
          (scalar_of_intertwining_end (G := G) σ
            ((intertwiningMap_toDualAdjointMap_generic
                (σ := σ) (τ := τ) J hJ hτ_inner_map_map T).comp
              (Φ (J y)))) := by
  simp [J.map_add, Representation.IntertwiningMap.add_comp, star_add]

/-- Helper for Remark 4-4.3-1: for fixed `T`, the starred Schur test pairing is linear in the
vector argument for any coefficient family `Φ`. -/
theorem testPairing_map_smul_generic [σ.IsIrreducible]
    (Φ : Module.Dual ℂ W →ₗ[ℂ] σ.IntertwiningMap τ)
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hτ_inner_map_map : ∀ g : G, ∀ v w : V, inner ℂ (τ g v) (τ g w) = inner ℂ v w)
    (T : σ.IntertwiningMap τ) (a : ℂ) (x : W) :
    star
        (scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap_generic
              (σ := σ) (τ := τ) J hJ hτ_inner_map_map T).comp
            (Φ (J (a • x))))) =
      a *
        star
          (scalar_of_intertwining_end (G := G) σ
            ((intertwiningMap_toDualAdjointMap_generic
                (σ := σ) (τ := τ) J hJ hτ_inner_map_map T).comp
              (Φ (J x)))) := by
  simp [LinearEquiv.map_smulₛₗ, Representation.IntertwiningMap.comp_smul]

/-- Helper for Remark 4-4.3-1: the starred Schur test pairing is additive in the intertwiner
argument after composing with a generic coefficient family `Φ`. -/
theorem recovery_map_add_generic [σ.IsIrreducible]
    (Φ : Module.Dual ℂ W →ₗ[ℂ] σ.IntertwiningMap τ)
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hτ_inner_map_map : ∀ g : G, ∀ v w : V, inner ℂ (τ g v) (τ g w) = inner ℂ v w)
    (T₁ T₂ : σ.IntertwiningMap τ) (x : W) :
    star
        (scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap_generic
              (σ := σ) (τ := τ) J hJ hτ_inner_map_map (T₁ + T₂)).comp
            (Φ (J x)))) =
      star
        (scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap_generic
              (σ := σ) (τ := τ) J hJ hτ_inner_map_map T₁).comp
            (Φ (J x)))) +
        star
          (scalar_of_intertwining_end (G := G) σ
            ((intertwiningMap_toDualAdjointMap_generic
                (σ := σ) (τ := τ) J hJ hτ_inner_map_map T₂).comp
              (Φ (J x)))) := by
  simp [Representation.IntertwiningMap.comp_add, star_add]

/-- Helper for Remark 4-4.3-1: the starred Schur test pairing is linear in the intertwiner
argument after the final conjugation for any coefficient family `Φ`. -/
theorem recovery_map_smul_generic [σ.IsIrreducible]
    (Φ : Module.Dual ℂ W →ₗ[ℂ] σ.IntertwiningMap τ)
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hτ_inner_map_map : ∀ g : G, ∀ v w : V, inner ℂ (τ g v) (τ g w) = inner ℂ v w)
    (a : ℂ) (T : σ.IntertwiningMap τ) (x : W) :
    star
        (scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap_generic
              (σ := σ) (τ := τ) J hJ hτ_inner_map_map (a • T)).comp
            (Φ (J x)))) =
      a *
        star
          (scalar_of_intertwining_end (G := G) σ
            ((intertwiningMap_toDualAdjointMap_generic
                (σ := σ) (τ := τ) J hJ hτ_inner_map_map T).comp
              (Φ (J x)))) := by
  simp [Representation.IntertwiningMap.smul_comp]

/-- Helper for Remark 4-4.3-1: package the Schur scalars obtained from the generic `J`-adjoint
tests into the dual of `W`. -/
theorem exists_dualRecovery_generic [σ.IsIrreducible]
    (Φ : Module.Dual ℂ W →ₗ[ℂ] σ.IntertwiningMap τ)
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hτ_inner_map_map : ∀ g : G, ∀ v w : V, inner ℂ (τ g v) (τ g w) = inner ℂ v w) :
    ∃ Ψ : σ.IntertwiningMap τ →ₗ[ℂ] Module.Dual ℂ W,
      ∀ T x,
        Ψ T x =
          star
            (scalar_of_intertwining_end (G := G) σ
              ((intertwiningMap_toDualAdjointMap_generic
                  (σ := σ) (τ := τ) J hJ hτ_inner_map_map T).comp
                (Φ (J x)))) := by
  refine ⟨
    { toFun := fun T ↦
        { toFun := fun x ↦
            star
              (scalar_of_intertwining_end (G := G) σ
                ((intertwiningMap_toDualAdjointMap_generic
                    (σ := σ) (τ := τ) J hJ hτ_inner_map_map T).comp
                  (Φ (J x))))
          map_add' := by
            intro x y
            simpa using testPairing_map_add_generic
              (G := G) (σ := σ) (τ := τ) Φ J hJ hτ_inner_map_map T x y
          map_smul' := by
            intro a x
            simpa [smul_eq_mul] using testPairing_map_smul_generic
              (G := G) (σ := σ) (τ := τ) Φ J hJ hτ_inner_map_map T a x }
      map_add' := by
        intro T₁ T₂
        apply LinearMap.ext
        intro x
        simpa using recovery_map_add_generic
          (G := G) (σ := σ) (τ := τ) Φ J hJ hτ_inner_map_map T₁ T₂ x
      map_smul' := by
        intro a T
        apply LinearMap.ext
        intro x
        simpa [smul_eq_mul] using recovery_map_smul_generic
          (G := G) (σ := σ) (τ := τ) Φ J hJ hτ_inner_map_map a T x }, ?_⟩
  intro T x
  rfl

/-- Helper for Remark 4-4.3-1: the generic dual recovery map attached to a coefficient family
`Φ`. -/
noncomputable def dualRecovery_generic [σ.IsIrreducible]
    (Φ : Module.Dual ℂ W →ₗ[ℂ] σ.IntertwiningMap τ)
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hτ_inner_map_map : ∀ g : G, ∀ v w : V, inner ℂ (τ g v) (τ g w) = inner ℂ v w) :
    σ.IntertwiningMap τ →ₗ[ℂ] Module.Dual ℂ W :=
  Classical.choose (exists_dualRecovery_generic
    (G := G) (σ := σ) (τ := τ) Φ J hJ hτ_inner_map_map)

/-- Helper for Remark 4-4.3-1: the generic recovery functional evaluates to the conjugated Schur
scalar used in the source proof. -/
theorem dualRecovery_generic_apply [σ.IsIrreducible]
    (Φ : Module.Dual ℂ W →ₗ[ℂ] σ.IntertwiningMap τ)
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hτ_inner_map_map : ∀ g : G, ∀ v w : V, inner ℂ (τ g v) (τ g w) = inner ℂ v w)
    (T : σ.IntertwiningMap τ) (x : W) :
    dualRecovery_generic (G := G) (σ := σ) (τ := τ) Φ J hJ hτ_inner_map_map T x =
      star
        (scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap_generic
              (σ := σ) (τ := τ) J hJ hτ_inner_map_map T).comp
            (Φ (J x)))) :=
  Classical.choose_spec (exists_dualRecovery_generic
    (G := G) (σ := σ) (τ := τ) Φ J hJ hτ_inner_map_map) T x

/-- Helper for Remark 4-4.3-1: pairing a test intertwiner with a coefficient from `Φ` evaluates
the dual vector on the `J`-representative of the generic recovery functional. -/
theorem pairing_eval_generic [σ.IsIrreducible]
    (Φ : Module.Dual ℂ W →ₗ[ℂ] σ.IntertwiningMap τ)
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hτ_inner_map_map : ∀ g : G, ∀ v w : V, inner ℂ (τ g v) (τ g w) = inner ℂ v w)
    (S : σ.IntertwiningMap τ) (ℓ : Module.Dual ℂ W) :
    scalar_of_intertwining_end (G := G) σ
      ((intertwiningMap_toDualAdjointMap_generic
          (σ := σ) (τ := τ) J hJ hτ_inner_map_map S).comp
        (Φ ℓ)) =
    ℓ (J.symm
      (dualRecovery_generic (G := G) (σ := σ) (τ := τ) Φ J hJ hτ_inner_map_map S)) := by
  let Ψ := dualRecovery_generic (G := G) (σ := σ) (τ := τ) Φ J hJ hτ_inner_map_map
  let x : W := J.symm ℓ
  have hx : J x = ℓ := by
    simp [x]
  have hrecover :
      Ψ S x =
        star
          (scalar_of_intertwining_end (G := G) σ
            ((intertwiningMap_toDualAdjointMap_generic
                (σ := σ) (τ := τ) J hJ hτ_inner_map_map S).comp (Φ (J x)))) := by
    simpa [Ψ, x] using
      dualRecovery_generic_apply
        (G := G) (σ := σ) (τ := τ) (Φ := Φ) (J := J)
        (hJ := hJ) (hτ_inner_map_map := hτ_inner_map_map) (T := S) (x := x)
  calc
    scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap_generic
            (σ := σ) (τ := τ) J hJ hτ_inner_map_map S).comp (Φ ℓ))
      =
        scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap_generic
              (σ := σ) (τ := τ) J hJ hτ_inner_map_map S).comp (Φ (J x))) := by
            rw [hx]
    _ = star (Ψ S x) := by
          rw [hrecover]
          simp
    _ = star (J (J.symm (Ψ S)) x) := by
          rw [LinearEquiv.apply_symm_apply]
    _ = J x (J.symm (Ψ S)) := by
          simpa using hJ_herm (J.symm (Ψ S)) x
    _ = ℓ (J.symm (Ψ S)) := by
          rw [hx]

/-- Helper for Remark 4-4.3-1: the Schur scalar attached to a generic adjoint-test composite can
be read as an inner product of two fixed test vectors. -/
theorem scalar_of_intertwining_end_comp_eq_inner_generic [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hτ_inner_map_map : ∀ g : G, ∀ v w : V, inner ℂ (τ g v) (τ g w) = inner ℂ v w)
    (S T : σ.IntertwiningMap τ) :
    scalar_of_intertwining_end (G := G) σ
      ((intertwiningMap_toDualAdjointMap_generic
          (σ := σ) (τ := τ) J hJ hτ_inner_map_map S).comp T) =
    inner ℂ
      (S (J.symm (chosen_irreducible_dual (G := G) σ)))
      (T (chosen_irreducible_vector (G := G) σ)) := by
  let x₀ : W := chosen_irreducible_vector (G := G) σ
  let ℓ₀ : Module.Dual ℂ W := chosen_irreducible_dual (G := G) σ
  let y₀ : W := J.symm ℓ₀
  have hy₀ : J y₀ = ℓ₀ := by
    simp [y₀]
  calc
    scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap_generic
            (σ := σ) (τ := τ) J hJ hτ_inner_map_map S).comp T)
      = ℓ₀
          (((intertwiningMap_toDualAdjointMap_generic
              (σ := σ) (τ := τ) J hJ hτ_inner_map_map S).comp T) x₀) := by
            rfl
    _ = J y₀
          (((intertwiningMap_toDualAdjointMap_generic
              (σ := σ) (τ := τ) J hJ hτ_inner_map_map S).comp T) x₀) := by
            rw [hy₀]
    _ =
        star
          (J
            (((intertwiningMap_toDualAdjointMap_generic
                (σ := σ) (τ := τ) J hJ hτ_inner_map_map S).comp T) x₀)
            y₀) := by
              simpa using
                (hJ_herm
                  (((intertwiningMap_toDualAdjointMap_generic
                      (σ := σ) (τ := τ) J hJ hτ_inner_map_map S).comp T) x₀)
                  y₀).symm
    _ = star (inner ℂ (T x₀) (S y₀)) := by
          rw [Representation.IntertwiningMap.comp_apply,
            intertwiningMap_toDualAdjointMap_generic_apply
              (G := G) (σ := σ) (τ := τ) (J := J)
              (hJ := hJ) (hτ_inner_map_map := hτ_inner_map_map)]
    _ = inner ℂ (S y₀) (T x₀) := by
          simp
    _ =
        inner ℂ
          (S (J.symm (chosen_irreducible_dual (G := G) σ)))
          (T (chosen_irreducible_vector (G := G) σ)) := by
            simp [x₀, y₀, ℓ₀]

/-- Helper for Remark 4-4.3-1: if the self-test Schur scalar of a generic intertwiner vanishes,
then the intertwiner itself vanishes. -/
theorem self_test_zero_implies_zero_generic [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hτ_inner_map_map : ∀ g : G, ∀ v w : V, inner ℂ (τ g v) (τ g w) = inner ℂ v w)
    (D : σ.IntertwiningMap τ)
    (hD :
      scalar_of_intertwining_end (G := G) σ
        ((intertwiningMap_toDualAdjointMap_generic
            (σ := σ) (τ := τ) J hJ hτ_inner_map_map D).comp D) = 0) :
    D = 0 := by
  have hcomp :
      (intertwiningMap_toDualAdjointMap_generic
          (σ := σ) (τ := τ) J hJ hτ_inner_map_map D).comp D = 0 := by
    have hsmul :=
      scalar_of_intertwining_end_smul_id (G := G) σ
        ((intertwiningMap_toDualAdjointMap_generic
            (σ := σ) (τ := τ) J hJ hτ_inner_map_map D).comp D)
    rw [hD, zero_smul] at hsmul
    exact hsmul.symm
  apply Representation.IntertwiningMap.ext
  ext x
  have hDx :
      ((intertwiningMap_toDualAdjointMap_generic
          (σ := σ) (τ := τ) J hJ hτ_inner_map_map D).comp D) x = 0 := by
    simpa using congrArg (fun F : σ.IntertwiningMap σ ↦ F x) hcomp
  have hinner :
      inner ℂ (D x) (D x) = 0 := by
    have hJzero := congrArg (fun v ↦ J v x) hDx
    simpa [Representation.IntertwiningMap.comp_apply,
      intertwiningMap_toDualAdjointMap_generic_apply
        (G := G) (σ := σ) (τ := τ) (J := J)
        (hJ := hJ) (hτ_inner_map_map := hτ_inner_map_map)] using hJzero
  exact inner_self_eq_zero.mp hinner

/-- Helper for Remark 4-4.3-1: the generic recovery pairing against a test intertwiner is
represented by evaluating the recovered dual vector on the `J`-representative of that test
intertwiner. -/
theorem recovery_represents_testPairing_generic [σ.IsIrreducible]
    (Φ : Module.Dual ℂ W →ₗ[ℂ] σ.IntertwiningMap τ)
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hτ_inner_map_map : ∀ g : G, ∀ v w : V, inner ℂ (τ g v) (τ g w) = inner ℂ v w)
    (S T : σ.IntertwiningMap τ) :
    scalar_of_intertwining_end (G := G) σ
      ((intertwiningMap_toDualAdjointMap_generic
          (σ := σ) (τ := τ) J hJ hτ_inner_map_map S).comp
        (Φ.comp
          (dualRecovery_generic (G := G) (σ := σ) (τ := τ) Φ J hJ hτ_inner_map_map) T)) =
    (dualRecovery_generic (G := G) (σ := σ) (τ := τ) Φ J hJ hτ_inner_map_map) T
      (J.symm
        ((dualRecovery_generic (G := G) (σ := σ) (τ := τ) Φ J hJ hτ_inner_map_map) S)) := by
  simpa using pairing_eval_generic
    (G := G) (σ := σ) (τ := τ) (Φ := Φ) (J := J)
    (hJ := hJ) (hJ_herm := hJ_herm) (hτ_inner_map_map := hτ_inner_map_map)
    (S := S)
    (ℓ := (dualRecovery_generic (G := G) (σ := σ) (τ := τ) Φ J hJ hτ_inner_map_map) T)

end AdjointRecovery

end Remark_4_4_3_1

end Representation
