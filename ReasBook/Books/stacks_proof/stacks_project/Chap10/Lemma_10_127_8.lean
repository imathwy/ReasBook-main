import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {Λ : Type v} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
variable (RStage : Λ → Type u) [∀ i, CommRing (RStage i)]
variable (map : ∀ i j, i ≤ j → RStage i →+* RStage j)
variable [DirectedSystem RStage (fun i j h ↦ map i j h)]
variable (colimitIso : Ring.DirectLimit RStage (fun i j h ↦ map i j h) ≃+* R)

/-
Domain sampling:
* Primary domain: filtered colimits of commutative rings and finite-presentation descent.
* Core/canonical owners inspected:
  - `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit`
  - `RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit`
  - `CommRingCat.FilteredColimits.colimitCoconeIsColimit`
* Owner choice: the mathlib filtered-colimit / `Under` API is the core owner abstraction.
* Layer triage:
  - `source-facing`: the three direct-limit descent lemmas below
  - `core/canonical`: the filtered-colimit / `Under` lemmas above
  - `bridge/view`: the chosen `Ring.DirectLimit ... ≃+* R` and the induced stage maps into `R`
* Primitive vs. derived:
  - primitive data: the raw directed system and its chosen limit identification
  - derived bridge data: the stage maps to `R` and the resulting scalar-tower compatibility
-/

namespace Ring.DirectLimit

/-- The map from a stage of a directed system to the chosen limit ring. -/
noncomputable def toLimitHom (i : Λ) : RStage i →+* R :=
  colimitIso.toRingHom.comp (Ring.DirectLimit.of RStage (fun i j h ↦ map i j h) i)

-- Proof sketch: this is the compatibility of the direct-limit structure maps, transported across
-- the chosen identification with `R`.
/-- The stage maps to the chosen limit ring are compatible with the transition maps. -/
theorem toLimitHom_comp_map {i j : Λ} (h : i ≤ j) :
    (toLimitHom RStage map colimitIso j).comp (map i j h) =
      toLimitHom RStage map colimitIso i :=
  RingHom.ext fun x => congrArg colimitIso (Ring.DirectLimit.of_f h x)

-- Proof sketch: convert the preceding compatibility of ring homomorphisms into the standard
-- algebra-tower compatibility condition.
/-- The transition map to a later stage and the induced maps to the limit ring form a scalar tower.
-/
theorem toLimit_isScalarTower {i j : Λ} (h : i ≤ j) :
    letI : Algebra (RStage i) (RStage j) := (map i j h).toAlgebra
    letI : Algebra (RStage i) R := (toLimitHom RStage map colimitIso i).toAlgebra
    letI : Algebra (RStage j) R := (toLimitHom RStage map colimitIso j).toAlgebra
    IsScalarTower (RStage i) (RStage j) R :=
  letI : Algebra (RStage i) (RStage j) := (map i j h).toAlgebra
  letI : Algebra (RStage i) R := (toLimitHom RStage map colimitIso i).toAlgebra
  letI : Algebra (RStage j) R := (toLimitHom RStage map colimitIso j).toAlgebra
  IsScalarTower.of_algebraMap_eq' (toLimitHom_comp_map RStage map colimitIso h).symm

attribute [instance] toLimit_isScalarTower

end Ring.DirectLimit

namespace M2F1278P1

/-- Every element of the chosen limit ring comes from some stage. -/
theorem exists_stage (r : R) :
    ∃ (i : Λ) (x : RStage i), Ring.DirectLimit.toLimitHom RStage map colimitIso i x = r := by
  obtain ⟨i, x, hx⟩ := Ring.DirectLimit.exists_of (colimitIso.symm r)
  refine ⟨i, x, ?_⟩
  have hrfl : Ring.DirectLimit.toLimitHom RStage map colimitIso i x
      = colimitIso (Ring.DirectLimit.of RStage (fun i j h ↦ map i j h) i x) := rfl
  rw [hrfl, hx, RingEquiv.apply_symm_apply]

/-- Every multivariate polynomial over the limit ring lifts to a polynomial over some stage. -/
theorem exists_poly_lift {n : ℕ} (g : MvPolynomial (Fin n) R) :
    ∃ (i : Λ) (p : MvPolynomial (Fin n) (RStage i)),
      MvPolynomial.map (Ring.DirectLimit.toLimitHom RStage map colimitIso i) p = g := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨i, x, hx⟩ := exists_stage RStage map colimitIso a
    exact ⟨i, MvPolynomial.C x, by rw [MvPolynomial.map_C, hx]⟩
  | add p q hp hq =>
    obtain ⟨i₁, p₁, h₁⟩ := hp
    obtain ⟨i₂, p₂, h₂⟩ := hq
    obtain ⟨k, hk₁, hk₂⟩ := exists_ge_ge i₁ i₂
    refine ⟨k, MvPolynomial.map (map i₁ k hk₁) p₁ + MvPolynomial.map (map i₂ k hk₂) p₂, ?_⟩
    rw [map_add, MvPolynomial.map_map, MvPolynomial.map_map,
      Ring.DirectLimit.toLimitHom_comp_map, Ring.DirectLimit.toLimitHom_comp_map, h₁, h₂]
  | mul_X p k hp =>
    obtain ⟨i, p₀, h₀⟩ := hp
    exact ⟨i, p₀ * MvPolynomial.X k, by rw [map_mul, MvPolynomial.map_X, h₀]⟩

/-- Finitely many polynomials over the limit ring lift simultaneously to a single stage. -/
theorem exists_common_lift {n : ℕ} (s : Finset (MvPolynomial (Fin n) R)) :
    ∃ (i : Λ) (F : s → MvPolynomial (Fin n) (RStage i)),
      ∀ g : s, MvPolynomial.map (Ring.DirectLimit.toLimitHom RStage map colimitIso i) (F g)
        = (g : MvPolynomial (Fin n) R) := by
  classical
  choose idx p hp using fun g : s =>
    exists_poly_lift RStage map colimitIso (g : MvPolynomial (Fin n) R)
  obtain ⟨i, hi⟩ := Finset.exists_le (Finset.univ.image idx)
  refine ⟨i, fun g => MvPolynomial.map
    (map (idx g) i (hi _ (Finset.mem_image_of_mem idx (Finset.mem_univ g)))) (p g), fun g => ?_⟩
  rw [MvPolynomial.map_map, Ring.DirectLimit.toLimitHom_comp_map]
  exact hp g

/-- Base-changing the model quotient algebra at a stage along `R₀ → R` recovers the original
quotient of the polynomial ring over `R`, provided the chosen generators lift the original ones. -/
theorem equiv_baseChange (R₀ : Type u) [CommRing R₀] [Algebra R₀ R] {n : ℕ}
    (s : Finset (MvPolynomial (Fin n) R)) (F : s → MvPolynomial (Fin n) R₀)
    (hF : ∀ g : s, MvPolynomial.map (algebraMap R₀ R) (F g) = (g : MvPolynomial (Fin n) R)) :
    letI : Algebra R ((MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range F)) ⊗[R₀] R) :=
      Algebra.TensorProduct.rightAlgebra
    Nonempty (((MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range F)) ⊗[R₀] R) ≃ₐ[R]
      (MvPolynomial (Fin n) R ⧸ Ideal.span (s : Set (MvPolynomial (Fin n) R)))) := by
  classical
  letI : Algebra R ((MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range F)) ⊗[R₀] R) :=
    Algebra.TensorProduct.rightAlgebra
  have hgen : ∀ g : s,
      (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R₀ R)
        (Algebra.TensorProduct.includeRight (F g)) = (g : MvPolynomial (Fin n) R) := by
    intro g
    rw [Algebra.TensorProduct.includeRight_apply, MvPolynomial.algebraTensorAlgEquiv_tmul,
      one_smul]
    exact hF g
  refine Nonempty.intro (AlgEquiv.trans (AlgEquiv.trans
    (Algebra.TensorProduct.commRight R₀ R
      (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range F))).symm
    (Algebra.TensorProduct.tensorQuotientEquiv (R := R₀) R (MvPolynomial (Fin n) R₀) R
      (Ideal.span (Set.range F))))
    (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R₀ R) ?_))
  rw [Ideal.map_span, Ideal.map_span, Set.image_image, ← Set.range_comp]
  refine (congrArg Ideal.span ?_).symm
  ext q
  simp only [Set.mem_range, Function.comp_apply, Finset.mem_coe, RingHom.coe_coe]
  constructor
  · rintro ⟨g, rfl⟩
    rw [hgen g]
    exact g.2
  · intro hq
    exact ⟨⟨q, hq⟩, hgen ⟨q, hq⟩⟩

end M2F1278P1

/-! ### Helper infrastructure for parts (2) and (3)

We realize `B ⊗[R_i] R` as a module direct limit of `B ⊗[R_i] R_j` over the directed set of
stages `j ≥ i`, and derive the two fundamental facts (every element comes from a finite stage;
an element that dies in the limit dies at some finite stage). -/

namespace M2F1278P23

/-- The directed set of stages above `i`. -/
abbrev Up (i₀ : Λ) : Type v := {j : Λ // i₀ ≤ j}

section Helpers

variable (i : Λ)

@[local instance] theorem up_nonempty : Nonempty (Up i) := ⟨⟨i, le_rfl⟩⟩

@[local instance] theorem up_isDirectedOrder : IsDirectedOrder (Up i) := by
  constructor
  intro a b
  obtain ⟨c, hac, hbc⟩ := exists_ge_ge a.1 b.1
  exact ⟨⟨c, le_trans a.2 hac⟩, hac, hbc⟩

@[local instance] noncomputable def upDecEq : DecidableEq (Up i) := Classical.decEq _

variable [stA : ∀ j : Up i, Algebra (RStage i) (RStage j.1)] [limA : Algebra (RStage i) R]

/-- A `Prop`-class recording that the ambient algebra structures on the stages above `i` and on
`R` are the ones induced by the transition maps and the limit-stage maps. -/
class StagePins : Prop where
  stA_eq : ∀ j : Up i, algebraMap (RStage i) (RStage j.1) = map i j.1 j.2
  limA_eq : algebraMap (RStage i) R = Ring.DirectLimit.toLimitHom RStage map colimitIso i

variable [pins : StagePins RStage map colimitIso i]

/-- The transition map between stages above `i`, as an `RStage i`-algebra map. -/
def stageHom {j k : Up i} (h : j ≤ k) : RStage j.1 →ₐ[RStage i] RStage k.1 where
  toRingHom := map j.1 k.1 h
  commutes' := fun r => by
    show map j.1 k.1 h (algebraMap (RStage i) (RStage j.1) r)
        = algebraMap (RStage i) (RStage k.1) r
    rw [RingHom.congr_fun (pins.stA_eq j) r, RingHom.congr_fun (pins.stA_eq k) r]
    exact DirectedSystem.map_map' (fun a b hab => map a b hab) j.2 h r

theorem stageHom_comp {j k l : Up i} (hjk : j ≤ k) (hkl : k ≤ l) :
    (stageHom RStage map colimitIso i hkl).comp (stageHom RStage map colimitIso i hjk)
      = stageHom RStage map colimitIso i (le_trans hjk hkl) :=
  AlgHom.ext fun x => DirectedSystem.map_map' (fun a b hab => map a b hab) hjk hkl x

/-- The transition map between stages above `i`, as an `RStage i`-linear map. -/
def stageLin (j k : Up i) (h : j ≤ k) : RStage j.1 →ₗ[RStage i] RStage k.1 :=
  (stageHom RStage map colimitIso i h).toLinearMap

@[local instance] theorem stageLin_directedSystem :
    DirectedSystem (fun j : Up i => RStage j.1)
      (fun j k h => stageLin RStage map colimitIso i j k h) where
  map_self := by
    intro j x
    exact DirectedSystem.map_self' (fun a b hab => map a b hab) x
  map_map := by
    intro l k j h1 h2 x
    exact DirectedSystem.map_map' (fun a b hab => map a b hab) h1 h2 x

/-- The map from a stage above `i` to the limit ring, as an `RStage i`-algebra map. -/
def toLimitAlgHom (j : Up i) : RStage j.1 →ₐ[RStage i] R where
  toRingHom := Ring.DirectLimit.toLimitHom RStage map colimitIso j.1
  commutes' := fun r => by
    show Ring.DirectLimit.toLimitHom RStage map colimitIso j.1
        (algebraMap (RStage i) (RStage j.1) r) = algebraMap (RStage i) R r
    rw [RingHom.congr_fun (pins.stA_eq j) r, RingHom.congr_fun pins.limA_eq r]
    exact RingHom.congr_fun (Ring.DirectLimit.toLimitHom_comp_map RStage map colimitIso j.2) r

theorem toLimitAlgHom_comp_stageHom {j k : Up i} (hjk : j ≤ k) :
    (toLimitAlgHom RStage map colimitIso i k).comp (stageHom RStage map colimitIso i hjk)
      = toLimitAlgHom RStage map colimitIso i j :=
  AlgHom.ext fun x =>
    RingHom.congr_fun (Ring.DirectLimit.toLimitHom_comp_map RStage map colimitIso hjk) x

/-- The canonical linear map from the direct limit of the stages above `i` to `R`. -/
def limLift :
    Module.DirectLimit (fun j : Up i => RStage j.1) (stageLin RStage map colimitIso i)
      →ₗ[RStage i] R :=
  Module.DirectLimit.lift (RStage i) (Up i) (fun j : Up i => RStage j.1)
    (stageLin RStage map colimitIso i)
    (fun j => (toLimitAlgHom RStage map colimitIso i j).toLinearMap)
    (fun j k hjk x =>
      RingHom.congr_fun (Ring.DirectLimit.toLimitHom_comp_map RStage map colimitIso hjk) x)

theorem limLift_of (j : Up i) (x : RStage j.1) :
    limLift RStage map colimitIso i
        (Module.DirectLimit.of (RStage i) (Up i) (fun j : Up i => RStage j.1)
          (stageLin RStage map colimitIso i) j x)
      = Ring.DirectLimit.toLimitHom RStage map colimitIso j.1 x :=
  Module.DirectLimit.lift_of _ _ _

theorem limLift_injective : Function.Injective (limLift RStage map colimitIso i) := by
  rw [injective_iff_map_eq_zero]
  intro z
  induction z using Module.DirectLimit.induction_on with
  | ih j x =>
    intro hz
    rw [limLift_of] at hz
    have hz' : Ring.DirectLimit.of RStage (fun i j h ↦ map i j h) j.1 x = 0 := by
      apply colimitIso.injective
      rw [map_zero]
      exact hz
    obtain ⟨k, hjk, hk⟩ := Ring.DirectLimit.of.zero_exact hz'
    calc Module.DirectLimit.of (RStage i) (Up i) (fun j : Up i => RStage j.1)
          (stageLin RStage map colimitIso i) j x
        = Module.DirectLimit.of (RStage i) (Up i) (fun j : Up i => RStage j.1)
            (stageLin RStage map colimitIso i) ⟨k, le_trans j.2 hjk⟩
            (stageLin RStage map colimitIso i j ⟨k, le_trans j.2 hjk⟩ hjk x) :=
          (Module.DirectLimit.of_f (f := stageLin RStage map colimitIso i)
            (i := j) (j := ⟨k, le_trans j.2 hjk⟩) (hij := hjk) (x := x)).symm
      _ = 0 := by
          rw [show stageLin RStage map colimitIso i j ⟨k, le_trans j.2 hjk⟩ hjk x = 0 from hk,
            map_zero]

theorem limLift_surjective : Function.Surjective (limLift RStage map colimitIso i) := by
  intro r
  obtain ⟨j₀, x₀, hx₀⟩ := Ring.DirectLimit.exists_of (colimitIso.symm r)
  obtain ⟨c, hic, hjc⟩ := exists_ge_ge i j₀
  refine ⟨Module.DirectLimit.of (RStage i) (Up i) (fun j : Up i => RStage j.1)
    (stageLin RStage map colimitIso i) ⟨c, hic⟩ (map j₀ c hjc x₀), ?_⟩
  rw [limLift_of]
  show colimitIso (Ring.DirectLimit.of RStage (fun i j h ↦ map i j h) c (map j₀ c hjc x₀)) = r
  have h2 : Ring.DirectLimit.of RStage (fun i j h ↦ map i j h) c (map j₀ c hjc x₀)
      = Ring.DirectLimit.of RStage (fun i j h ↦ map i j h) j₀ x₀ :=
    Ring.DirectLimit.of_f hjc x₀
  rw [h2, hx₀]
  exact colimitIso.apply_symm_apply r

/-- The direct limit of the stages above `i` is `R`. -/
noncomputable def limEquiv :
    Module.DirectLimit (fun j : Up i => RStage j.1) (stageLin RStage map colimitIso i)
      ≃ₗ[RStage i] R :=
  LinearEquiv.ofBijective (limLift RStage map colimitIso i)
    ⟨limLift_injective RStage map colimitIso i, limLift_surjective RStage map colimitIso i⟩

theorem limEquiv_symm_toLimitHom (j : Up i) (x : RStage j.1) :
    (limEquiv RStage map colimitIso i).symm
        (Ring.DirectLimit.toLimitHom RStage map colimitIso j.1 x)
      = Module.DirectLimit.of (RStage i) (Up i) (fun j : Up i => RStage j.1)
          (stageLin RStage map colimitIso i) j x := by
  rw [LinearEquiv.symm_apply_eq]
  exact (limLift_of RStage map colimitIso i j x).symm

variable (B : Type w) [CommRing B] [Algebra (RStage i) B]

/-- Push a tensor at a stage above `i` into the limit. -/
def pushHom (j : Up i) : (B ⊗[RStage i] RStage j.1) →ₐ[RStage i] (B ⊗[RStage i] R) :=
  Algebra.TensorProduct.map (AlgHom.id (RStage i) B) (toLimitAlgHom RStage map colimitIso i j)

/-- Push a tensor at a stage above `i` to a later stage. -/
def pushStage {j k : Up i} (hjk : j ≤ k) :
    (B ⊗[RStage i] RStage j.1) →ₐ[RStage i] (B ⊗[RStage i] RStage k.1) :=
  Algebra.TensorProduct.map (AlgHom.id (RStage i) B) (stageHom RStage map colimitIso i hjk)

theorem pushHom_tmul (j : Up i) (b : B) (x : RStage j.1) :
    pushHom RStage map colimitIso i B j (b ⊗ₜ[RStage i] x)
      = b ⊗ₜ[RStage i] (Ring.DirectLimit.toLimitHom RStage map colimitIso j.1 x) := rfl

theorem pushStage_tmul {j k : Up i} (hjk : j ≤ k) (b : B) (x : RStage j.1) :
    pushStage RStage map colimitIso i B hjk (b ⊗ₜ[RStage i] x)
      = b ⊗ₜ[RStage i] (map j.1 k.1 hjk x) := rfl

theorem pushHom_comp_pushStage {j k : Up i} (hjk : j ≤ k) :
    (pushHom RStage map colimitIso i B k).comp (pushStage RStage map colimitIso i B hjk)
      = pushHom RStage map colimitIso i B j := by
  have h := Algebra.TensorProduct.map_id_comp (S := RStage i) (A := B)
    (toLimitAlgHom RStage map colimitIso i k) (stageHom RStage map colimitIso i hjk)
  rw [toLimitAlgHom_comp_stageHom] at h
  exact h.symm

theorem pushStage_comp_pushStage {j k l : Up i} (hjk : j ≤ k) (hkl : k ≤ l) :
    (pushStage RStage map colimitIso i B hkl).comp (pushStage RStage map colimitIso i B hjk)
      = pushStage RStage map colimitIso i B (le_trans hjk hkl) := by
  have h := Algebra.TensorProduct.map_id_comp (S := RStage i) (A := B)
    (stageHom RStage map colimitIso i hkl) (stageHom RStage map colimitIso i hjk)
  rw [stageHom_comp] at h
  exact h.symm

theorem pushStage_apply_eq_lTensor {j k : Up i} (hjk : j ≤ k) (y : B ⊗[RStage i] RStage j.1) :
    pushStage RStage map colimitIso i B hjk y
      = LinearMap.lTensor B (stageLin RStage map colimitIso i j k hjk) y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul b x => rfl
  | add y₁ y₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]

/-- `B ⊗[R_i] R` as a direct limit of the `B ⊗[R_i] R_j`. -/
noncomputable def tensorLimEquiv :
    (B ⊗[RStage i] R) ≃ₗ[RStage i]
      Module.DirectLimit (fun j : Up i => B ⊗[RStage i] RStage j.1)
        (fun j k h => LinearMap.lTensor B (stageLin RStage map colimitIso i j k h)) :=
  (LinearEquiv.lTensor B (limEquiv RStage map colimitIso i).symm).trans
    (TensorProduct.directLimitRight (stageLin RStage map colimitIso i) B)

theorem tensorLimEquiv_pushHom (j : Up i) (y : B ⊗[RStage i] RStage j.1) :
    tensorLimEquiv RStage map colimitIso i B (pushHom RStage map colimitIso i B j y)
      = Module.DirectLimit.of (RStage i) (Up i) (fun j : Up i => B ⊗[RStage i] RStage j.1)
          (fun j k h => LinearMap.lTensor B (stageLin RStage map colimitIso i j k h)) j y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b x =>
    have h1 : tensorLimEquiv RStage map colimitIso i B
        (pushHom RStage map colimitIso i B j (b ⊗ₜ[RStage i] x))
        = TensorProduct.directLimitRight (stageLin RStage map colimitIso i) B
            (b ⊗ₜ[RStage i] ((limEquiv RStage map colimitIso i).symm
              (Ring.DirectLimit.toLimitHom RStage map colimitIso j.1 x))) := rfl
    rw [h1, limEquiv_symm_toLimitHom]
    exact TensorProduct.directLimitRight_tmul_of (stageLin RStage map colimitIso i) B b x
  | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- L2 (zero detection): if a tensor at stage `j` dies in `B ⊗[R_i] R`, it dies at a later
stage. -/
theorem pushHom_eq_zero_exact (j : Up i) (y : B ⊗[RStage i] RStage j.1)
    (hy : pushHom RStage map colimitIso i B j y = 0) :
    ∃ (k : Up i) (hjk : j ≤ k), pushStage RStage map colimitIso i B hjk y = 0 := by
  have h0 : Module.DirectLimit.of (RStage i) (Up i)
      (fun j : Up i => B ⊗[RStage i] RStage j.1)
      (fun j k h => LinearMap.lTensor B (stageLin RStage map colimitIso i j k h)) j y = 0 := by
    rw [← tensorLimEquiv_pushHom RStage map colimitIso i B j y, hy, map_zero]
  obtain ⟨k, hjk, hk⟩ := Module.DirectLimit.of.zero_exact h0
  refine ⟨k, hjk, ?_⟩
  rw [pushStage_apply_eq_lTensor]
  exact hk

/-- L1 (lift): every element of `B ⊗[R_i] R` comes from a finite stage. -/
theorem exists_pushHom (x : B ⊗[RStage i] R) :
    ∃ (j : Up i) (y : B ⊗[RStage i] RStage j.1),
      pushHom RStage map colimitIso i B j y = x := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨⟨i, le_rfl⟩, 0, map_zero _⟩
  | tmul b r =>
    obtain ⟨j₀, x₀, hx₀⟩ := Ring.DirectLimit.exists_of (colimitIso.symm r)
    obtain ⟨c, hic, hjc⟩ := exists_ge_ge i j₀
    refine ⟨⟨c, hic⟩, b ⊗ₜ[RStage i] (map j₀ c hjc x₀), ?_⟩
    have h1 : Ring.DirectLimit.toLimitHom RStage map colimitIso c (map j₀ c hjc x₀) = r := by
      change colimitIso (Ring.DirectLimit.of RStage (fun i j h ↦ map i j h) c (map j₀ c hjc x₀)) = r
      have h2 : Ring.DirectLimit.of RStage (fun i j h ↦ map i j h) c (map j₀ c hjc x₀)
          = Ring.DirectLimit.of RStage (fun i j h ↦ map i j h) j₀ x₀ :=
        Ring.DirectLimit.of_f hjc x₀
      rw [h2, hx₀]
      exact colimitIso.apply_symm_apply r
    rw [pushHom_tmul, h1]
  | add x₁ x₂ ih₁ ih₂ =>
    obtain ⟨j₁, y₁, h₁⟩ := ih₁
    obtain ⟨j₂, y₂, h₂⟩ := ih₂
    obtain ⟨k, hk₁, hk₂⟩ := exists_ge_ge j₁ j₂
    refine ⟨k, pushStage RStage map colimitIso i B hk₁ y₁
      + pushStage RStage map colimitIso i B hk₂ y₂, ?_⟩
    rw [map_add]
    have e₁ := AlgHom.congr_fun (pushHom_comp_pushStage RStage map colimitIso i B hk₁) y₁
    have e₂ := AlgHom.congr_fun (pushHom_comp_pushStage RStage map colimitIso i B hk₂) y₂
    simp only [AlgHom.comp_apply] at e₁ e₂
    rw [e₁, e₂, h₁, h₂]

include map colimitIso in
/-- Equality of `b ⊗ 1 = b' ⊗ 1` in `B ⊗[R_i] R` descends to some finite stage. -/
theorem eventually_tmul_one_eq (b b' : B)
    (h : b ⊗ₜ[RStage i] (1 : R) = b' ⊗ₜ[RStage i] (1 : R)) (j : Up i) :
    ∃ (k : Up i) (_ : j ≤ k),
      b ⊗ₜ[RStage i] (1 : RStage k.1) = b' ⊗ₜ[RStage i] (1 : RStage k.1) := by
  have h0 : pushHom RStage map colimitIso i B j
      ((b - b') ⊗ₜ[RStage i] (1 : RStage j.1)) = 0 := by
    rw [pushHom_tmul, map_one, TensorProduct.sub_tmul, h, sub_self]
  obtain ⟨k, hjk, hk⟩ := pushHom_eq_zero_exact RStage map colimitIso i B j _ h0
  rw [pushStage_tmul, map_one, TensorProduct.sub_tmul, sub_eq_zero] at hk
  exact ⟨k, hjk, hk⟩

/-- Core of part (2): an algebra map from a finitely presented stage algebra into
`B ⊗[R_i] R` factors through `B ⊗[R_i] R_k` for some stage `k ≥ i`. -/
theorem P2core (A : Type w) [CommRing A] [Algebra (RStage i) A]
    [Algebra.FinitePresentation (RStage i) A]
    (φ : A →ₐ[RStage i] B ⊗[RStage i] R) :
    ∃ (k : Up i) (φ_k : A →ₐ[RStage i] B ⊗[RStage i] RStage k.1),
      (pushHom RStage map colimitIso i B k).comp φ_k = φ := by
  classical
  obtain ⟨n, f, hfsurj, hfker⟩ := Algebra.FinitePresentation.out (R := RStage i) (A := A)
  obtain ⟨s, hs⟩ := hfker
  -- find a common stage for the images of the variables
  choose jv yv hyv using fun tv : Fin n =>
    exists_pushHom RStage map colimitIso i B (φ (f (MvPolynomial.X tv)))
  obtain ⟨J, hJ⟩ := Finset.exists_le (Finset.univ.image jv)
  let u : Fin n → B ⊗[RStage i] RStage J.1 := fun tv =>
    pushStage RStage map colimitIso i B
      (hJ (jv tv) (Finset.mem_image_of_mem jv (Finset.mem_univ tv))) (yv tv)
  have hu : ∀ tv, pushHom RStage map colimitIso i B J (u tv) = φ (f (MvPolynomial.X tv)) := by
    intro tv
    have e := AlgHom.congr_fun (pushHom_comp_pushStage RStage map colimitIso i B
      (hJ (jv tv) (Finset.mem_image_of_mem jv (Finset.mem_univ tv)))) (yv tv)
    simp only [AlgHom.comp_apply] at e
    exact e.trans (hyv tv)
  have hnat : (pushHom RStage map colimitIso i B J).comp (MvPolynomial.aeval u) = φ.comp f := by
    apply MvPolynomial.algHom_ext
    intro tv
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    exact hu tv
  -- kill the relations at a later stage
  choose kg hJkg hkg using fun g : {x // x ∈ s} =>
    pushHom_eq_zero_exact RStage map colimitIso i B J ((MvPolynomial.aeval u) g.1) (by
      have h2 := AlgHom.congr_fun hnat g.1
      simp only [AlgHom.comp_apply] at h2
      have hgker : (g.1 : MvPolynomial (Fin n) (RStage i)) ∈ RingHom.ker f.toRingHom := by
        rw [← hs]
        exact Submodule.subset_span g.2
      have hf0 : f g.1 = 0 := RingHom.mem_ker.mp hgker
      rw [hf0, map_zero] at h2
      exact h2)
  obtain ⟨K, hK⟩ := Finset.exists_le (insert J (Finset.univ.image kg))
  have hJK : J ≤ K := hK J (Finset.mem_insert_self _ _)
  have hgK : ∀ g : {x // x ∈ s}, kg g ≤ K := fun g =>
    hK (kg g) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem kg (Finset.mem_univ g)))
  have hker_le : RingHom.ker f.toRingHom ≤
      RingHom.ker ((pushStage RStage map colimitIso i B hJK).comp
        (MvPolynomial.aeval u)).toRingHom := by
    rw [← hs]
    refine Submodule.span_le.mpr ?_
    intro g hg
    have hg' : g ∈ s := Finset.mem_coe.mp hg
    have h3 := AlgHom.congr_fun
      (pushStage_comp_pushStage RStage map colimitIso i B (hJkg ⟨g, hg'⟩) (hgK ⟨g, hg'⟩))
      ((MvPolynomial.aeval u) g)
    simp only [AlgHom.comp_apply] at h3
    have h4 : pushStage RStage map colimitIso i B hJK ((MvPolynomial.aeval u) g) = 0 := by
      calc pushStage RStage map colimitIso i B hJK ((MvPolynomial.aeval u) g)
          = pushStage RStage map colimitIso i B (le_trans (hJkg ⟨g, hg'⟩) (hgK ⟨g, hg'⟩))
              ((MvPolynomial.aeval u) g) := rfl
        _ = pushStage RStage map colimitIso i B (hgK ⟨g, hg'⟩)
              (pushStage RStage map colimitIso i B (hJkg ⟨g, hg'⟩)
                ((MvPolynomial.aeval u) g)) := h3.symm
        _ = 0 := by rw [hkg ⟨g, hg'⟩, map_zero]
    exact RingHom.mem_ker.mpr h4
  refine ⟨K, AlgHom.liftOfSurjective f hfsurj
    ((pushStage RStage map colimitIso i B hJK).comp (MvPolynomial.aeval u)) hker_le, ?_⟩
  apply AlgHom.ext
  intro a
  obtain ⟨p, rfl⟩ := hfsurj a
  have h5 := AlgHom.congr_fun (AlgHom.liftOfSurjective_comp f hfsurj
    ((pushStage RStage map colimitIso i B hJK).comp (MvPolynomial.aeval u)) hker_le) p
  simp only [AlgHom.comp_apply] at h5 ⊢
  rw [h5]
  have h6 := AlgHom.congr_fun (pushHom_comp_pushStage RStage map colimitIso i B hJK)
    ((MvPolynomial.aeval u) p)
  simp only [AlgHom.comp_apply] at h6
  rw [h6]
  have h7 := AlgHom.congr_fun hnat p
  simp only [AlgHom.comp_apply] at h7
  exact h7

include map colimitIso in
/-- Core of part (3): two maps that agree after base change to `R` agree after base change
to some finite stage. -/
theorem P3core (A : Type w) [CommRing A] [Algebra (RStage i) A]
    [Algebra.FiniteType (RStage i) A]
    (φ ψ : A →ₐ[RStage i] B)
    (hφψ : Algebra.TensorProduct.map φ (AlgHom.id (RStage i) R)
         = Algebra.TensorProduct.map ψ (AlgHom.id (RStage i) R)) :
    ∃ k : Up i,
      Algebra.TensorProduct.map φ (AlgHom.id (RStage i) (RStage k.1))
        = Algebra.TensorProduct.map ψ (AlgHom.id (RStage i) (RStage k.1)) := by
  classical
  obtain ⟨t, ht⟩ := (inferInstance : Algebra.FiniteType (RStage i) A).out
  have step : ∀ a : A, ∃ k : Up i,
      (φ a) ⊗ₜ[RStage i] (1 : RStage k.1) = (ψ a) ⊗ₜ[RStage i] (1 : RStage k.1) := by
    intro a
    have h1 : (φ a) ⊗ₜ[RStage i] (1 : R) = (ψ a) ⊗ₜ[RStage i] (1 : R) := by
      have h := AlgHom.congr_fun hφψ (a ⊗ₜ[RStage i] (1 : R))
      simpa using h
    obtain ⟨k, _, hk⟩ := eventually_tmul_one_eq RStage map colimitIso i B (φ a) (ψ a) h1
      ⟨i, le_rfl⟩
    exact ⟨k, hk⟩
  choose sel hsel using step
  obtain ⟨K, hK⟩ := Finset.exists_le (t.image sel)
  refine ⟨K, ?_⟩
  have hLeft : ∀ a ∈ (↑t : Set A),
      (Algebra.TensorProduct.includeLeft.comp φ :
        A →ₐ[RStage i] B ⊗[RStage i] RStage K.1) a
        = (Algebra.TensorProduct.includeLeft.comp ψ :
            A →ₐ[RStage i] B ⊗[RStage i] RStage K.1) a := by
    intro a ha
    have ha' : a ∈ t := Finset.mem_coe.mp ha
    have h2 : sel a ≤ K := hK (sel a) (Finset.mem_image_of_mem sel ha')
    have h3 := congrArg (pushStage RStage map colimitIso i B h2) (hsel a)
    rw [pushStage_tmul, pushStage_tmul, map_one] at h3
    change (φ a) ⊗ₜ[RStage i] (1 : RStage K.1) = (ψ a) ⊗ₜ[RStage i] (1 : RStage K.1)
    exact h3
  apply Algebra.TensorProduct.ext
  · rw [Algebra.TensorProduct.map_comp_includeLeft, Algebra.TensorProduct.map_comp_includeLeft]
    exact AlgHom.ext_of_adjoin_eq_top ht hLeft
  · rw [Algebra.TensorProduct.map_restrictScalars_comp_includeRight,
      Algebra.TensorProduct.map_restrictScalars_comp_includeRight]

end Helpers

end M2F1278P23

-- Proof sketch: choose a finite presentation of `A` over `R`; only finitely many coefficients of
-- the defining equations are involved, so they already lie in some stage `R_i`. Defining the same
-- quotient algebra over `R_i` gives a finitely presented model whose base change to `R` recovers
-- `A`.
/-- Lemma 10.127.8 (1): every finitely presented `R`-algebra is obtained by base change from a
finitely presented algebra over some stage of a directed colimit presentation of `R`.

The descended algebra is produced in `Type u`, the universe of the stages (where the canonical
model `MvPolynomial (Fin n) (RStage i) ⧸ J` lives); quantifying it over the universe of `A`
would make the statement false whenever `w < u`. -/
@[stacks 05N9]
theorem finitelyPresented_algebra_is_baseChange_of_stage
    (A : Type w) [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A] :
    ∃ (i : Λ) (A_i : Type u) (_ : CommRing A_i) (_ : Algebra (RStage i) A_i)
      (_ : Algebra.FinitePresentation (RStage i) A_i),
      letI : Algebra (RStage i) R := (Ring.DirectLimit.toLimitHom RStage map colimitIso i).toAlgebra
      letI : Algebra R (A_i ⊗[RStage i] R) := Algebra.TensorProduct.rightAlgebra
      Nonempty (A_i ⊗[RStage i] R ≃ₐ[R] A) := by
  classical
  obtain ⟨n, I, e, hIfg⟩ := (Algebra.FinitePresentation.iff (R := R) (A := A)).mp inferInstance
  obtain ⟨s, hs⟩ := hIfg
  subst hs
  obtain ⟨i, F, hF⟩ := M2F1278P1.exists_common_lift RStage map colimitIso s
  letI : Algebra (RStage i) R := (Ring.DirectLimit.toLimitHom RStage map colimitIso i).toAlgebra
  have hF' : ∀ g : s, MvPolynomial.map (algebraMap (RStage i) R) (F g)
      = (g : MvPolynomial (Fin n) R) := hF
  letI : Algebra R ((MvPolynomial (Fin n) (RStage i) ⧸ Ideal.span (Set.range F)) ⊗[RStage i] R) :=
    Algebra.TensorProduct.rightAlgebra
  obtain ⟨E⟩ := M2F1278P1.equiv_baseChange (RStage i) s F hF'
  exact ⟨i, MvPolynomial (Fin n) (RStage i) ⧸ Ideal.span (Set.range F), inferInstance,
    inferInstance,
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range F)),
    ⟨E.trans e⟩⟩

-- Proof sketch: the given morphism over `R` is equivalently an `R_i`-algebra map from `A_i` to
-- `B_i ⊗[R_i] R` by the tensor-product universal property. The filtered-colimit descent theorem
-- `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit` then descends that map to some later
-- stage `R_j`.
/-- Lemma 10.127.8 (2): an `RStage i`-algebra map from a finitely presented stage algebra into
the base change `B_i ⊗[RStage i] R` (equivalently, by the universal property of base change, an
`R`-algebra map `A_i ⊗[RStage i] R → B_i ⊗[RStage i] R`) descends to `B_i ⊗[RStage i] RStage j`
for some later stage `j`. -/
@[stacks 05N9]
theorem finitePresentation_hom_to_limit_baseChange_descends {i : Λ}
    (A_i : Type w) [CommRing A_i] [Algebra (RStage i) A_i]
    [Algebra.FinitePresentation (RStage i) A_i]
    (B_i : Type w) [CommRing B_i] [Algebra (RStage i) B_i]
    [Algebra.FinitePresentation (RStage i) B_i]
    (φ :
      letI : Algebra (RStage i) R := (Ring.DirectLimit.toLimitHom RStage map colimitIso i).toAlgebra
      A_i →ₐ[RStage i] B_i ⊗[RStage i] R) :
    ∃ (j : Λ) (hij : i ≤ j),
      letI : Algebra (RStage i) (RStage j) := (map i j hij).toAlgebra
      letI : Algebra (RStage i) R := (Ring.DirectLimit.toLimitHom RStage map colimitIso i).toAlgebra
      letI : Algebra (RStage j) R := (Ring.DirectLimit.toLimitHom RStage map colimitIso j).toAlgebra
      letI : IsScalarTower (RStage i) (RStage j) R :=
        Ring.DirectLimit.toLimit_isScalarTower RStage map colimitIso hij
      ∃ φ_j : A_i →ₐ[RStage i] B_i ⊗[RStage i] RStage j,
        (Algebra.TensorProduct.map (AlgHom.id (RStage i) B_i)
          (IsScalarTower.toAlgHom (RStage i) (RStage j) R)).comp φ_j = φ := by
  letI : Algebra (RStage i) R := (Ring.DirectLimit.toLimitHom RStage map colimitIso i).toAlgebra
  letI : ∀ j : M2F1278P23.Up i, Algebra (RStage i) (RStage j.1) :=
    fun j => (map i j.1 j.2).toAlgebra
  letI : M2F1278P23.StagePins RStage map colimitIso i := ⟨fun j => rfl, rfl⟩
  obtain ⟨k, φ_k, hφ_k⟩ := M2F1278P23.P2core RStage map colimitIso i B_i A_i φ
  refine ⟨k.1, k.2, ?_⟩
  letI : Algebra (RStage i) (RStage k.1) := (map i k.1 k.2).toAlgebra
  letI : Algebra (RStage k.1) R := (Ring.DirectLimit.toLimitHom RStage map colimitIso k.1).toAlgebra
  letI : IsScalarTower (RStage i) (RStage k.1) R :=
    Ring.DirectLimit.toLimit_isScalarTower RStage map colimitIso k.2
  change ∃ φ_j : A_i →ₐ[RStage i] B_i ⊗[RStage i] RStage k.1,
    (Algebra.TensorProduct.map (AlgHom.id (RStage i) B_i)
      (IsScalarTower.toAlgHom (RStage i) (RStage k.1) R)).comp φ_j = φ
  exact ⟨φ_k, hφ_k⟩

-- Proof sketch: equality after base change to `R` is equality of the corresponding maps into
-- `B_i ⊗[R_i] R`. The filtered-colimit injectivity theorem
-- `RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit` shows that the equality already holds
-- after enlarging to one stage `R_j`.
/-- Lemma 10.127.8 (3): if two maps between finitely presented stage algebras become equal after
base change to the colimit ring `R`, then they become equal after base change to some later stage.
-/
@[stacks 05N9]
theorem finitePresentation_map_equality_stabilizes {i : Λ}
    (A_i : Type w) [CommRing A_i] [Algebra (RStage i) A_i]
    [Algebra.FinitePresentation (RStage i) A_i]
    (B_i : Type w) [CommRing B_i] [Algebra (RStage i) B_i]
    [Algebra.FinitePresentation (RStage i) B_i]
    (φ ψ : A_i →ₐ[RStage i] B_i)
    (hφψ :
      letI : Algebra (RStage i) R := (Ring.DirectLimit.toLimitHom RStage map colimitIso i).toAlgebra
      Algebra.TensorProduct.map φ (AlgHom.id (RStage i) R) =
        Algebra.TensorProduct.map ψ (AlgHom.id (RStage i) R)) :
    ∃ (j : Λ) (hij : i ≤ j),
      letI : Algebra (RStage i) (RStage j) := (map i j hij).toAlgebra
      Algebra.TensorProduct.map φ (AlgHom.id (RStage i) (RStage j)) =
        Algebra.TensorProduct.map ψ (AlgHom.id (RStage i) (RStage j)) := by
  letI : Algebra (RStage i) R := (Ring.DirectLimit.toLimitHom RStage map colimitIso i).toAlgebra
  letI : ∀ j : M2F1278P23.Up i, Algebra (RStage i) (RStage j.1) :=
    fun j => (map i j.1 j.2).toAlgebra
  letI : M2F1278P23.StagePins RStage map colimitIso i := ⟨fun j => rfl, rfl⟩
  obtain ⟨k, hk⟩ := M2F1278P23.P3core RStage map colimitIso i B_i A_i φ ψ hφψ
  exact ⟨k.1, k.2, hk⟩

end
