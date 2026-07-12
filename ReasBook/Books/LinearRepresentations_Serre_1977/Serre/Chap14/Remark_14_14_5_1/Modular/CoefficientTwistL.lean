import Mathlib
import LinearRepresentations_Serre_1977.RepresentationTheory.RealizableOver
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.CoefficientTwist

/-!
# The `L`-level coefficient twist `LTwist` and its commutation with scalar extension (Brick C2)

This module mirrors `CoefficientTwist.lean` at the level of a finite Galois intermediate field
`L/k` (in place of the algebraic closure `k̄/k`), building the **`L`-level coefficient twist**
`LTwist σ W : FDRep L G` of a finite-dimensional `L[G]`-representation `W` along an automorphism
`σ : L ≃ₐ[k] L`.  As in the `k̄` case, `LTwist σ W` has the same underlying additive group and the
same `G`-action as `W`, but the `L`-scalar `c` acts as `σ⁻¹ c`.

The **deliverable** is the *commutation isomorphism* `scalarExtension_LTwist_iso`:  for a Galois
automorphism `τ : k̄ ≃ₐ[k] k̄` restricting to `σ` on `L`,

> `(LTwist σ T_L) ⊗ k̄  ≅  Twist τ (T_L ⊗ k̄)`     (as `FDRep k̄ G`),

i.e. scalar-extending the `L`-level twist agrees with the `k̄`-level twist of the scalar extension.
On underlying spaces both sides are `k̄ ⊗[L] T_L`, and the isomorphism is the `τ⁻¹`-coefficient map
`μ ⊗ v ↦ τ⁻¹(μ) ⊗ v`, which is well defined because `τ|_L = σ`.
-/

noncomputable section

universe u

open scoped TensorProduct Representation MonoidAlgebra

open CategoryTheory

namespace Representation

section LTwist

variable {k : Type u} [Field k]
variable {L : Type u} [Field L] [Algebra k L]
variable {G : Type u} [Group G] [Finite G]

/-- The `σ⁻¹` ring homomorphism `L →+* L` used to precompose the scalar action in the `L`-twist. -/
private abbrev LtwistRingHom (σ : L ≃ₐ[k] L) : L →+* L := (σ.symm : L →+* L)

/-- **The carrier of the `L`-level σ-twist.**  A `def`-wrapped type synonym for the underlying
additive group of `W`, so that the twisted `L`-scalar action can be registered without clashing with
the ambient `Module L` instance of `W`. -/
def LTwistSpace (σ : L ≃ₐ[k] L) (W : FDRep L G) : Type u := W

namespace LTwistSpace

variable {σ : L ≃ₐ[k] L} {W : FDRep L G}

instance ringHomInvPair : RingHomInvPair (σ : L →+* L) (σ.symm : L →+* L) :=
  RingHomInvPair.of_ringEquiv σ.toRingEquiv

instance ringHomInvPair' : RingHomInvPair (σ.symm : L →+* L) (σ : L →+* L) :=
  RingHomInvPair.of_ringEquiv σ.symm.toRingEquiv

instance : AddCommGroup (LTwistSpace σ W) := inferInstanceAs (AddCommGroup W)

/-- The twisted `L`-scalar action: `c • v = σ⁻¹ c • v`. -/
instance : Module L (LTwistSpace σ W) := Module.compHom (W : Type u) (LtwistRingHom σ)

/-- The canonical additive equivalence `W ≃+ LTwist σ W` (identity on the underlying group). -/
def LofBase : W ≃+ LTwistSpace σ W := AddEquiv.refl _

@[simp] theorem LofBase_apply (v : W) : (LofBase (σ := σ) v : LTwistSpace σ W) = v := rfl

/-- Unfolding the twisted scalar action: `c • v = σ⁻¹ c • v`, transported across `LofBase`. -/
theorem LofBase_smul (c : L) (v : W) :
    (c • LofBase (σ := σ) v : LTwistSpace σ W) = LofBase (σ := σ) (LtwistRingHom σ c • v) := rfl

/-- The σ-semilinear identity equivalence `W ≃ₛₗ[σ] LTwist σ W`. -/
def LofBaseₛₗ : W ≃ₛₗ[(σ : L →+* L)] LTwistSpace σ W where
  toFun v := LofBase (σ := σ) v
  map_add' v w := by rfl
  map_smul' c v := by
    change LofBase (σ := σ) (c • v) = (σ c) • LofBase (σ := σ) v
    rw [LofBase_smul]
    simp [LtwistRingHom]
  invFun v := LofBase (σ := σ).symm v
  left_inv v := by rfl
  right_inv v := by rfl

@[simp] theorem LofBaseₛₗ_apply (v : W) :
    (LofBaseₛₗ (σ := σ) v : LTwistSpace σ W) = LofBase (σ := σ) v := rfl

@[simp] theorem LofBaseₛₗ_symm_apply (v : LTwistSpace σ W) :
    (LofBaseₛₗ (σ := σ)).symm v = LofBase (σ := σ).symm v := rfl

instance : Module.Finite L (LTwistSpace σ W) := by
  classical
  refine ⟨?_⟩
  refine ⟨(Finset.univ.image fun i => LofBase (σ := σ)
      (Module.Free.chooseBasis L W i) : Finset (LTwistSpace σ W)), ?_⟩
  rw [eq_top_iff]
  rintro v -
  have hw : LofBase (σ := σ) (LofBase (σ := σ).symm v) = v := by simp
  rw [← hw]
  have hmem : (LofBase (σ := σ).symm v) ∈
      Submodule.span L (Set.range (Module.Free.chooseBasis L W)) := by
    rw [(Module.Free.chooseBasis L W).span_eq]; trivial
  have hspan := Submodule.apply_mem_span_image_of_mem_span
    (f := (LofBaseₛₗ (σ := σ)).toLinearMap)
    (s := Set.range (Module.Free.chooseBasis L W)) hmem
  refine Submodule.span_mono ?_ hspan
  rintro _ ⟨w, ⟨i, rfl⟩, rfl⟩
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact ⟨i, rfl⟩

/-- Transport of an ambient-`L`-linear endomorphism of `W` to a twisted-`L`-linear endomorphism of
`LTwist σ W`: the underlying additive map is unchanged. -/
def LtwistMap (f : W →ₗ[L] W) : LTwistSpace σ W →ₗ[L] LTwistSpace σ W where
  toFun v := LofBase (σ := σ) (f (LofBase (σ := σ).symm v))
  map_add' v w := by simp [map_add]
  map_smul' c v := by
    simp only [RingHom.id_apply]
    rw [show (c • v : LTwistSpace σ W) =
        LofBase (σ := σ) (LtwistRingHom σ c • LofBase (σ := σ).symm v) from rfl]
    rw [show (c • LofBase (σ := σ) (f (LofBase (σ := σ).symm v)) : LTwistSpace σ W) =
        LofBase (σ := σ) (LtwistRingHom σ c • f (LofBase (σ := σ).symm v)) from rfl]
    rw [AddEquiv.symm_apply_apply, map_smul]

@[simp] theorem LtwistMap_apply (f : W →ₗ[L] W) (v : W) :
    LtwistMap (σ := σ) f (LofBase (σ := σ) v) = LofBase (σ := σ) (f v) := rfl

@[simp] theorem LtwistMap_one : LtwistMap (σ := σ) (1 : W →ₗ[L] W) = 1 := by ext v; rfl

theorem LtwistMap_mul (f g : W →ₗ[L] W) :
    LtwistMap (σ := σ) (f * g) = LtwistMap (σ := σ) f * LtwistMap (σ := σ) g := by ext v; rfl

end LTwistSpace

/-- **The `L`-level σ-twist representation** on the twisted carrier. -/
def LtwistRepresentation (σ : L ≃ₐ[k] L) (W : FDRep L G) :
    Representation L G (LTwistSpace σ W) where
  toFun g := LTwistSpace.LtwistMap (σ := σ) (W.ρ g)
  map_one' := by simp [LTwistSpace.LtwistMap_one]
  map_mul' g h := by
    rw [map_mul]
    exact LTwistSpace.LtwistMap_mul (σ := σ) (W.ρ g) (W.ρ h)

/-- **The `L`-level σ-twist as a bundled `FDRep`.** -/
def LTwist (σ : L ≃ₐ[k] L) (W : FDRep L G) : FDRep L G :=
  FDRep.of (LtwistRepresentation σ W)

variable {σ : L ≃ₐ[k] L} {W : FDRep L G}

@[simp] theorem LtwistRepresentation_apply (g : G) :
    LtwistRepresentation σ W g = LTwistSpace.LtwistMap (σ := σ) (W.ρ g) := rfl

@[simp] theorem LTwist_ρ : (LTwist σ W).ρ = LtwistRepresentation σ W := rfl

end LTwist

/-! ## Part 2: the commutation isomorphism `scalarExtension (LTwist σ T_L) ≅ Twist τ (...)` -/

section Commutation

variable {k : Type u} [Field k]
variable {L : Type u} [Field L] [Algebra k L]
variable {G : Type u} [Group G] [Finite G]
variable [Algebra L (AlgebraicClosure k)] [IsScalarTower k L (AlgebraicClosure k)] [Normal k L]

local notation3 "k̄" => AlgebraicClosure k

variable {σ : L ≃ₐ[k] L} (τ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)

/-- From `τ|_L = σ`: the commuting square `τ (algebraMap L k̄ c) = algebraMap L k̄ (σ c)`. -/
private theorem comm_algebraMap
    (hτ : AlgEquiv.restrictNormalHom L τ = σ) (c : L) :
    τ (algebraMap L (AlgebraicClosure k) c) = algebraMap L (AlgebraicClosure k) (σ c) := by
  have hRN : τ.restrictNormal L = σ := hτ
  rw [← AlgEquiv.restrictNormal_commutes τ L c, hRN]

/-- The `τ⁻¹`-commuting-square identity `τ⁻¹ (algebraMap L k̄ c) = algebraMap L k̄ (σ⁻¹ c)`. -/
private theorem comm_symm_algebraMap
    (hτ : AlgEquiv.restrictNormalHom L τ = σ) (c : L) :
    τ.symm (algebraMap L k̄ c) = algebraMap L k̄ (σ.symm c) := by
  have h : τ (algebraMap L k̄ (σ.symm c)) = algebraMap L k̄ c := by
    rw [comm_algebraMap τ hτ (σ.symm c), AlgEquiv.apply_symm_apply]
  rw [← h, AlgEquiv.symm_apply_apply]

variable (T_L : FDRep L G)

/-- The bi-additive `τ⁻¹`-coefficient map `(μ, v) ↦ τ⁻¹(μ) ⊗ v` underlying the forward direction. -/
private def commForwardBihom :
    (AlgebraicClosure k) →+ (LTwistSpace σ T_L) →+
      (AlgebraicClosure k) ⊗[L] T_L.V :=
  (LinearMap.toAddMonoidHom'.comp (TensorProduct.mk L k̄ T_L.V).toAddMonoidHom).comp
    (τ.symm : AlgebraicClosure k →+* AlgebraicClosure k).toAddMonoidHom

private theorem commForwardBihom_apply (μ : AlgebraicClosure k) (v : LTwistSpace σ T_L) :
    commForwardBihom τ T_L μ v =
      ((τ.symm μ) ⊗ₜ[L] v : (AlgebraicClosure k) ⊗[L] T_L.V) := rfl

/-- The bi-additive `τ`-coefficient map `(μ, v) ↦ τ(μ) ⊗ v` underlying the inverse direction. -/
private def commInverseBihom :
    (AlgebraicClosure k) →+ T_L.V →+
      (AlgebraicClosure k) ⊗[L] (LTwistSpace σ T_L) :=
  (LinearMap.toAddMonoidHom'.comp
      (TensorProduct.mk L (AlgebraicClosure k) (LTwistSpace σ T_L)).toAddMonoidHom).comp
    (τ : AlgebraicClosure k →+* AlgebraicClosure k).toAddMonoidHom

private theorem commInverseBihom_apply (μ : AlgebraicClosure k) (v : T_L.V) :
    commInverseBihom τ T_L μ v =
      ((τ μ) ⊗ₜ[L] v : (AlgebraicClosure k) ⊗[L] (LTwistSpace σ T_L)) := rfl

/-- The forward `τ⁻¹`-coefficient additive map on the scalar-extension carriers. -/
private def commForward (hτ : AlgEquiv.restrictNormalHom L τ = σ) :
    ((AlgebraicClosure k) ⊗[L] (LTwistSpace σ T_L)) →+
      ((AlgebraicClosure k) ⊗[L] T_L.V) :=
  TensorProduct.liftAddHom (commForwardBihom τ T_L) (by
    intro c μ v
    rw [commForwardBihom_apply, commForwardBihom_apply,
      Algebra.smul_def, map_mul, comm_symm_algebraMap τ hτ, ← Algebra.smul_def,
      TensorProduct.smul_tmul]
    rfl)

/-- The inverse `τ`-coefficient additive map on the scalar-extension carriers. -/
private def commInverse (hτ : AlgEquiv.restrictNormalHom L τ = σ) :
    ((AlgebraicClosure k) ⊗[L] T_L.V) →+
      ((AlgebraicClosure k) ⊗[L] (LTwistSpace σ T_L)) :=
  TensorProduct.liftAddHom (commInverseBihom τ T_L) (by
    intro c μ v
    rw [commInverseBihom_apply, commInverseBihom_apply,
      Algebra.smul_def, map_mul, comm_algebraMap τ hτ, ← Algebra.smul_def,
      TensorProduct.smul_tmul]
    congr 1
    -- `(σ c) •ₜ v = c • v` because the twisted action is `σ⁻¹ ∘ σ = id`.
    change σ.symm (σ c) • v = c • v
    rw [AlgEquiv.symm_apply_apply])

private theorem commForward_tmul (hτ : AlgEquiv.restrictNormalHom L τ = σ)
    (μ : AlgebraicClosure k) (v : LTwistSpace σ T_L) :
    commForward τ T_L hτ (μ ⊗ₜ[L] v) =
      ((τ.symm μ) ⊗ₜ[L] v : (AlgebraicClosure k) ⊗[L] T_L.V) := rfl

private theorem commInverse_tmul (hτ : AlgEquiv.restrictNormalHom L τ = σ)
    (μ : AlgebraicClosure k) (v : T_L.V) :
    commInverse τ T_L hτ (μ ⊗ₜ[L] v) =
      ((τ μ) ⊗ₜ[L] v : (AlgebraicClosure k) ⊗[L] (LTwistSpace σ T_L)) := rfl

/-- The `τ⁻¹`-semilinear equivalence `μ ⊗ v ↦ τ⁻¹(μ) ⊗ v` between the underlying spaces. -/
private def commSemilinearEquiv (hτ : AlgEquiv.restrictNormalHom L τ = σ) :
    (k̄ ⊗[L] (LTwistSpace σ T_L)) ≃ₛₗ[(τ.symm : AlgebraicClosure k →+* AlgebraicClosure k)]
      ((AlgebraicClosure k) ⊗[L] T_L.V) where
  toFun := commForward τ T_L hτ
  map_add' := map_add _
  map_smul' r x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul μ v =>
        rw [TensorProduct.smul_tmul', smul_eq_mul, commForward_tmul, commForward_tmul, map_mul,
          TensorProduct.smul_tmul', smul_eq_mul]
        rfl
    | add a b ha hb => simp only [smul_add, map_add, ha, hb]
  invFun := commInverse τ T_L hτ
  left_inv x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul μ v => rw [commForward_tmul, commInverse_tmul, AlgEquiv.apply_symm_apply]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  right_inv x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul μ v => rw [commInverse_tmul, commForward_tmul, AlgEquiv.symm_apply_apply]
    | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- The full `k̄`-linear equivalence between the underlying spaces: post-compose the
`τ⁻¹`-semilinear map with the `τ`-semilinear `TwistSpace` identity, giving a `k̄`-linear map. -/
private def commFullEquiv (hτ : AlgEquiv.restrictNormalHom L τ = σ) :
    ((AlgebraicClosure k) ⊗[L] (LTwistSpace σ T_L)) ≃ₗ[AlgebraicClosure k]
      TwistSpace τ (FDRep.scalarExtension (k := AlgebraicClosure k) T_L) :=
  (commSemilinearEquiv τ T_L hτ).trans
    (TwistSpace.ofBaseₛₗ (σ := τ) (T := FDRep.scalarExtension (k := AlgebraicClosure k) T_L))

/-- The commutation **representation equivalence**: the `k̄`-linear iso `commFullEquiv` intertwines
the scalar extension of the `L`-twist with the `k̄`-twist of the scalar extension. -/
private def commRepEquiv (hτ : AlgEquiv.restrictNormalHom L τ = σ) :
    (Representation.scalarExtension (k := AlgebraicClosure k) (LTwist σ T_L).ρ).Equiv
      (twistRepresentation τ (FDRep.scalarExtension (k := AlgebraicClosure k) T_L)) :=
  Representation.Equiv.mk (commFullEquiv τ T_L hτ) (by
    intro g
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul μ v =>
        -- On a pure tensor both sides reduce definitionally to
        -- `ofBase (τ⁻¹ μ ⊗ T_L.ρ g v)`.
        simp only [LinearMap.comp_apply]
        rfl
    | add a b ha hb => simp only [map_add, ha, hb])

/-- **The commutation isomorphism (the deliverable).**  For `τ : k̄ ≃ₐ[k] k̄` restricting to
`σ : L ≃ₐ[k] L` on the finite Galois extension `L`, scalar-extending the `L`-level coefficient twist
agrees with the `k̄`-level coefficient twist of the scalar extension:

> `(LTwist σ T_L) ⊗ k̄ ≅ Twist τ (T_L ⊗ k̄)`     in `FDRep k̄ G`.

The underlying map is the `τ⁻¹`-coefficient map `μ ⊗ v ↦ τ⁻¹(μ) ⊗ v`. -/
def scalarExtension_LTwist_iso (hτ : AlgEquiv.restrictNormalHom L τ = σ) :
    FDRep.scalarExtension (k := AlgebraicClosure k) (LTwist σ T_L) ≅
      Twist τ (FDRep.scalarExtension (k := AlgebraicClosure k) T_L) :=
  (commRepEquiv τ T_L hτ).toFDRepIso

end Commutation

end Representation

