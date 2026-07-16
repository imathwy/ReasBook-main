import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_52_13
import StacksProject_2024.stacks_project.Chap15.Lemma_15_121_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open Module.End
open scoped TensorProduct

universe u v w

section

variable {R : Type u} {R' : Type v} {M : Type w}
variable [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R']
variable [Algebra R R'] [IsLocalHom (algebraMap R R')] [Module.Flat R R']
variable [AddCommGroup M] [Module R M]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) R'
local notation "κ" => ResidueField R
local notation "κ'" => ResidueField R'

namespace Module.End

/-- Helper for Lemma 15.121.3: the finite-length closed-fiber hypothesis upgrades a finite-length
`R`-module to a finite-length tensor base change over `R'`. -/
private theorem finiteLength_of_tensorBaseChange
    (hM : IsFiniteLength R M)
    (hClosedFiber : IsFiniteLength ClosedFiber ClosedFiber) :
    IsFiniteLength R' (R' ⊗[R] M) := by
  -- This is the owner theorem from the earlier base-change finite-length lemma.
  exact (finite_length_iff_finite_length_base_change (A := R) (B := R') (M := M)
    hClosedFiber).1 hM

/-- Helper for Lemma 15.121.3: if `maximalIdeal R` acts trivially on `M`, then any `R`-linear
endomorphism of `M` descends to a `ResidueField R`-linear endomorphism with the same underlying
function. -/
private noncomputable def endHom_over_residueField_of_isTorsionBySet_maximalIdeal
    (htors : Module.IsTorsionBySet R M (maximalIdeal R))
    (φ : Module.End R M) :
    let _ : Module (ResidueField R) M := htors.module
    Module.End (ResidueField R) M := by
  let _ : Module (ResidueField R) M := htors.module
  -- The descended endomorphism has the same underlying function as `φ`; only the scalar owner
  -- changes from `R` to `ResidueField R`.
  exact
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := by
        intro a x
        rfl }

/-- Helper for Lemma 15.121.3: scalar multiplication by an element of `R` commutes with the
canonical `R[X]`-action attached to `φ`. -/
private theorem smul_comm_toPolynomialModule
    (φ : Module.End R M) (a : R) (p : R[X]) (x : M) :
    let _ : Module R[X] M := φ.toPolynomialModule
    a • (p • x) = p • (a • x) := by
  let _ : Module R[X] M := φ.toPolynomialModule
  -- Read the polynomial action through `aeval φ`, where every operator is `R`-linear.
  change a • (((aeval φ) p) x) = ((aeval φ) p) (a • x)
  exact ((aeval φ) p).map_smulₛₗ a x

/-- Helper for Lemma 15.121.3: scalar multiplication by an element of `R` is `R[X]`-linear for
the polynomial-module structure induced by `φ`. -/
private noncomputable def scalarPolynomialLinearMap
    (φ : Module.End R M) (a : R) :
    let _ : Module R[X] M := φ.toPolynomialModule
    M →ₗ[R[X]] M :=
  let _ : Module R[X] M := φ.toPolynomialModule
  { toFun := fun x ↦ a • x
    map_add' := smul_add a
    map_smul' := smul_comm_toPolynomialModule (φ := φ) a }

/-- Helper for Lemma 15.121.3: a simple `R[X]`-object of finite `R`-length is annihilated by the
maximal ideal of the local ring. -/
private theorem simple_object_isTorsionBySet_maximalIdeal
    (φ : Module.End R M) (hM : IsFiniteLength R M)
    (hsimple :
      let _ : Module R[X] M := φ.toPolynomialModule
      IsSimpleModule R[X] M) :
    Module.IsTorsionBySet R M (maximalIdeal R) := by
  let _ : Module R[X] M := φ.toPolynomialModule
  let _ : IsSimpleModule R[X] M := hsimple
  let _ : IsNoetherian R M := isNoetherian_of_isFiniteLength hM
  let _ : Module.Finite R M := Module.Finite.of_noetherian R M
  have hJac : maximalIdeal R ≤ Ring.jacobson R := by
    simpa [Ideal.jacobson_bot] using
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
  intro x a ha
  let fa : M →ₗ[R[X]] M := scalarPolynomialLinearMap (φ := φ) a
  rcases eq_bot_or_eq_top (LinearMap.ker fa) with hker | hker
  · have hrange_top : LinearMap.range fa = ⊤ := by
      rcases eq_bot_or_eq_top (LinearMap.range fa) with hrange | hrange
      · exfalso
        have hker_top : LinearMap.ker fa = ⊤ := by
          ext y
          constructor
          · intro hy
            simp
          · intro hy
            have hy' : fa y ∈ LinearMap.range fa := ⟨y, rfl⟩
            rw [hrange] at hy'
            simpa using hy'
        have hbot_top : (⊥ : Submodule R[X] M) = ⊤ := by
          simpa [hker] using hker_top
        exact bot_ne_top hbot_top
      · exact hrange
    have hsmul_top : maximalIdeal R • (⊤ : Submodule R M) = ⊤ := by
      apply top_unique
      intro y hy
      have hy' : y ∈ LinearMap.range fa := by
        simpa [hrange_top]
      rcases hy' with ⟨z, rfl⟩
      rw [Submodule.mem_smul_top_iff]
      exact ⟨a, ha, z, rfl⟩
    have hsubsingleton : Subsingleton M := by
      refine (Submodule.subsingleton_iff R).mp ?_
      refine subsingleton_of_bot_eq_top ?_
      symm
      have htop :
          (⊤ : Submodule R M) ≤ Ring.jacobson R • (⊤ : Submodule R M) := by
        exact hsmul_top.ge.trans <| Submodule.smul_mono hJac le_rfl
      exact Submodule.FG.eq_bot_of_le_jacobson_smul Module.Finite.fg_top htop
    have hnot : ¬ Subsingleton M := by
      exact not_subsingleton_iff_nontrivial.mpr inferInstance
    exact (hnot hsubsingleton).elim
  · have hxker : x ∈ LinearMap.ker fa := by
      simpa [hker]
    -- Membership in the top kernel means scalar multiplication by `a` vanishes on `x`.
    simpa [fa, scalarPolynomialLinearMap] using hxker

/-- Helper for Lemma 15.121.3: when `maximalIdeal R` acts trivially on `M`, the residue-field
tensor model collapses back to `M`. -/
private noncomputable def residueFieldTensor_linearEquiv_of_isTorsionBySet_maximalIdeal
    (htors : Module.IsTorsionBySet R M (maximalIdeal R)) :
    let _ : Module κ M := htors.module
    κ ⊗[R] M ≃ₗ[κ] M := by
  let _ : Algebra R κ := (IsLocalRing.residue R).toAlgebra
  let _ : Module κ M := htors.module
  -- Once the scalar action factors through the residue field, the left tensor unit collapses.
  exact (Algebra.TensorProduct.lidOfCompatibleSMul R κ M).toLinearEquiv

-- Proof sketch: the source proof first reduces along a `φ`-stable composition series and then
-- handles the simple-object branch by filtering the closed fiber and comparing the induced tensor
-- endomorphisms factor by factor.
/-- Lemma 15.121.3: let `R → R'` be a flat local homomorphism of local rings, and let
`ClosedFiber = (maximalIdeal R).Fiber R'` have finite length over itself. For a finite-length
`R`-module endomorphism `φ`, the image of `det_κ(φ)` raised to the closed-fiber length equals the
determinant of the base-changed endomorphism on `R' ⊗[R] M`. -/
theorem finiteLengthDeterminant_baseChange_pow_closedFiberLength
    (φ : Module.End R M) (hM : IsFiniteLength R M)
    (hClosedFiber : IsFiniteLength ClosedFiber ClosedFiber) :
    (ResidueField.map (algebraMap R R') (φ.finiteLengthDeterminant hM)) ^
        (Module.length ClosedFiber ClosedFiber).toNat =
      finiteLengthDeterminant ((TensorProduct.isBaseChange R M R').endHom φ)
        ((finite_length_iff_finite_length_base_change hClosedFiber).1 hM) := by
  -- Route correction: stabilize the file around the actual theorem statement before rebuilding the
  -- source-faithful reduction through stable short exact sequences and the simple closed-fiber
  -- filtration.
  have hBaseChange : IsFiniteLength R' (R' ⊗[R] M) :=
    finiteLength_of_tensorBaseChange (R := R) (R' := R') (M := M) hM hClosedFiber
  have hSimpleTorsion :
      ∀ hsimple :
        let _ : Module R[X] M := φ.toPolynomialModule
        IsSimpleModule R[X] M,
        Module.IsTorsionBySet R M (maximalIdeal R) :=
    fun hsimple ↦ simple_object_isTorsionBySet_maximalIdeal
      (R := R) (M := M) φ hM hsimple
  -- TODO: implement the source-proof reduction:
  -- 1. reduce to the simple `R[X]`-module case using multiplicativity of
  --    `finiteLengthDeterminant` on stable short exact sequences;
  -- 2. in the simple branch, descend `φ` to a `ResidueField R`-linear endomorphism;
  -- 3. transport `R' ⊗[R] M` to `ClosedFiber ⊗[ResidueField R] M`;
  -- 4. filter `ClosedFiber` by residue-field quotients and compute the determinant factorwise.
  have _ : IsFiniteLength R' (R' ⊗[R] M) := hBaseChange
  have _ := hSimpleTorsion
  sorry

end Module.End

end
