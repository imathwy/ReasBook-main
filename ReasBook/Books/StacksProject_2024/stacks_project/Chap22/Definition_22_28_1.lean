import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Algebra.Ring.Opposite
open scoped DirectSum

universe u v w x

/- Source/core/bridge triage:
- source-facing: the graded-algebra, fixed-module bimodule, graded bimodule, and differential
  graded bimodule owners introduced in Definition 22.28.1;
- core/canonical: `ZGradedAlgebra` is the canonical owner for the graded algebra layer in this
  file;
- bridge/view: no additional bridge layer is kept here, since Definition 22.28.1 only introduces
  the source-facing fixed-ring graded and differential graded algebra/bimodule data. -/

section

variable (R : Type u) [Ring R]

/-- An `ℤ`-graded `R`-algebra on the fixed ring `A`, recorded by its homogeneous pieces and
their direct-sum decomposition. -/
structure ZGradedAlgebra
    (A : Type v) [Ring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] where
  /-- The degree-`n` homogeneous piece. -/
  grading : ℤ → Submodule R A
  /-- The direct-sum decomposition `A = ⨁ A^n`. -/
  gradingEquiv : A ≃ₗ[R] ⨁ n : ℤ, grading n
  /-- A homogeneous element is sent to the matching summand of the direct sum decomposition. -/
  gradingEquiv_apply_homogeneous :
    ∀ {n : ℤ} (a : grading n),
      gradingEquiv a = DirectSum.lof R ℤ (fun n ↦ grading n) n a
  /-- The unit lies in degree `0`. -/
  one_mem : (1 : A) ∈ grading 0
  /-- The product of homogeneous elements has the summed degree. -/
  mul_mem :
    ∀ ⦃n m : ℤ⦄ ⦃a b : A⦄, a ∈ grading n → b ∈ grading m → a * b ∈ grading (n + m)

namespace ZGradedAlgebra

section CoeFun

variable {R : Type u} [Ring R]
variable {A : Type v} [Ring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

/-- A graded algebra can be used through its grading function. -/
instance : CoeFun (ZGradedAlgebra R A) (fun _ ↦ ℤ → Submodule R A) where
  coe 𝒜 := 𝒜.grading

@[simp] theorem gradingEquiv_apply
    (𝒜 : ZGradedAlgebra R A) {n : ℤ} (a : 𝒜 n) :
    𝒜.gradingEquiv a = DirectSum.lof R ℤ (fun n ↦ 𝒜 n) n a :=
  𝒜.gradingEquiv_apply_homogeneous a

@[simp] theorem gradingEquiv_symm_lof
    (𝒜 : ZGradedAlgebra R A) {n : ℤ} (a : 𝒜 n) :
    𝒜.gradingEquiv.symm (DirectSum.lof R ℤ (fun n ↦ 𝒜 n) n a) = a := by
  apply 𝒜.gradingEquiv.injective
  simp

end CoeFun

section Ground

variable (R : Type u) [CommRing R]

/-- The canonical `ℤ`-grading on the ground ring `R`, concentrated in degree `0`. -/
def groundGrading : ℤ → Submodule R R :=
  fun n ↦ if n = 0 then ⊤ else ⊥

private abbrev groundTopEquiv : (⊤ : Submodule R R) ≃ₗ[R] R :=
  Submodule.topEquiv

private def groundDecompose : R →ₗ[R] ⨁ n : ℤ, groundGrading R n :=
  (DirectSum.lof R ℤ (fun n ↦ groundGrading R n) 0).comp (groundTopEquiv R).symm.toLinearMap

private instance instGroundDecomposition : DirectSum.Decomposition (groundGrading R) :=
  DirectSum.Decomposition.ofLinearMap (groundGrading R) (groundDecompose R)
    (by
      apply LinearMap.ext
      intro r
      rw [LinearMap.comp_apply, groundDecompose, LinearMap.comp_apply, LinearMap.id_apply]
      have h :
          DirectSum.coeLinearMap (groundGrading R)
              ((DirectSum.lof R ℤ (fun n ↦ groundGrading R n) 0) ((groundTopEquiv R).symm r)) =
            (((groundTopEquiv R).symm r : (⊤ : Submodule R R)) : R) := by
        simpa using
          (DirectSum.coeLinearMap_lof (groundGrading R) 0 ((groundTopEquiv R).symm r))
      exact h.trans rfl)
    (by
      apply DirectSum.linearMap_ext
      intro i
      by_cases hi : i = 0
      · subst hi
        apply LinearMap.ext
        intro x
        rw [LinearMap.comp_apply, groundDecompose, LinearMap.comp_apply, LinearMap.comp_apply]
        simp only [DirectSum.coeLinearMap_lof]
        have hx : ((groundTopEquiv R).symm (x : R) : groundGrading R 0) = x := by
          ext
          rfl
        exact congrArg (DirectSum.lof R ℤ (fun n ↦ groundGrading R n) 0) hx
      · apply LinearMap.ext
        intro x
        have hx : x = 0 := by
          ext
          simpa [groundGrading, hi] using x.2
        subst hx
        rw [LinearMap.comp_apply, groundDecompose, LinearMap.comp_apply, LinearMap.comp_apply]
        simp)

/-- The ground ring `R`, viewed as a `ℤ`-graded `R`-algebra concentrated in degree `0`. -/
def ground : ZGradedAlgebra R R :=
  { grading := groundGrading R
    gradingEquiv := DirectSum.decomposeLinearEquiv (groundGrading R)
    gradingEquiv_apply_homogeneous := by
      intro n a
      simpa using DirectSum.decompose_coe (groundGrading R) a
    one_mem := by
      simp [groundGrading]
    mul_mem := by
      intro i j a b ha hb
      by_cases hi : i = 0
      · by_cases hj : j = 0
        · simp [groundGrading, hi, hj]
        · have hb0 : b = 0 := by
            simpa [groundGrading, hj] using hb
          subst hb0
          simpa using (groundGrading R (i + j)).zero_mem
      · have ha0 : a = 0 := by
          simpa [groundGrading, hi] using ha
        subst ha0
        simpa using (groundGrading R (i + j)).zero_mem }

end Ground

end ZGradedAlgebra

/-- A differential graded `R`-algebra on the fixed ring `A` is a graded `R`-algebra equipped with
a degree-`1` differential squaring to zero and satisfying the graded Leibniz rule. -/
structure DifferentialGradedAlgebra
    (A : Type v) [Ring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
    extends ZGradedAlgebra R A where
  /-- The differential on the underlying graded algebra. -/
  differential : A →ₗ[R] A
  /-- The differential raises degree by `1`. -/
  differential_mem :
    ∀ ⦃n : ℤ⦄ ⦃a : A⦄, a ∈ grading n → differential a ∈ grading (n + 1)
  /-- The differential squares to zero. -/
  differential_sq : differential.comp differential = 0
  /-- The differential satisfies the graded Leibniz rule on homogeneous elements. -/
  differential_mul :
    ∀ ⦃n m : ℤ⦄ ⦃a b : A⦄,
      a ∈ grading n → b ∈ grading m →
        differential (a * b) =
          differential a * b + (n.negOnePow : R) • a * differential b

namespace DifferentialGradedAlgebra

variable {R : Type u} [Ring R]
variable {A : Type v} [Ring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

/-- A differential graded algebra can be used through its grading function. -/
instance : CoeFun (DifferentialGradedAlgebra R A) (fun _ ↦ ℤ → Submodule R A) where
  coe 𝒜 := 𝒜.toZGradedAlgebra.grading

/-- A differential graded algebra carries its underlying graded algebra. -/
instance : CoeOut (DifferentialGradedAlgebra R A) (ZGradedAlgebra R A) where
  coe 𝒜 := 𝒜.toZGradedAlgebra

end DifferentialGradedAlgebra

namespace DifferentialGradedAlgebra

section Ground

variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

/-- The ground ring `R`, concentrated in degree `0` with zero differential. -/
def ground (R : Type u) [CommRing R] : DifferentialGradedAlgebra R R :=
  { toZGradedAlgebra := ZGradedAlgebra.ground R
    differential := 0
    differential_mem := by
      intro n a ha
      simpa using (ZGradedAlgebra.groundGrading R (n + 1)).zero_mem
    differential_sq := by
      ext
      simp
    differential_mul := by
      intro n m a b ha hb
      simp }

end Ground

end DifferentialGradedAlgebra

section AlgebraBimodule

variable (R : Type u) [Ring R]
variable (A : Type v) [Ring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable (B : Type w) [Ring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
variable (M : Type x) [AddCommGroup M] [Module R M]
local notation "DGAA" => DifferentialGradedAlgebra R A
local notation "DGAB" => DifferentialGradedAlgebra R B

/-- Definition 22.28.1 (1): an `(A, B)`-bimodule is an `R`-module `M` equipped with `R`-bilinear
left and right actions satisfying associativity, compatibility of the two actions, and the unit
identities. We record the left action as a `Module A M` structure and the right action as a
`Module Bᵐᵒᵖ M` structure so downstream files can reuse the canonical module/opposite-module API
directly. -/
@[stacks 0FQH]
structure AlgebraBimodule where
  /-- The left `A`-module structure on `M`. -/
  [instModuleA : Module A M]
  /-- The right `B`-module structure on `M`, encoded as a left `Bᵐᵒᵖ`-module. -/
  [instModuleBOp : Module Bᵐᵒᵖ M]
  /-- The left and right actions commute. -/
  [instSMulCommClass : SMulCommClass A Bᵐᵒᵖ M]
  /-- The left `A`-action is `R`-linear in the algebra variable. -/
  [instSMulCommClassLeft : SMulCommClass R A M]
  /-- The left `A`-action is compatible with the ambient `R`-module structure. -/
  [instIsScalarTowerLeft : IsScalarTower R A M]
  /-- The right `Bᵐᵒᵖ`-action is `R`-linear in the algebra variable. -/
  [instSMulCommClassRight : SMulCommClass R Bᵐᵒᵖ M]
  /-- The right `Bᵐᵒᵖ`-action is compatible with the ambient `R`-module structure. -/
  [instIsScalarTowerRight : IsScalarTower R Bᵐᵒᵖ M]

namespace AlgebraBimodule

variable {R : Type u} [Ring R]
variable {A : Type v} [Ring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable {B : Type w} [Ring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
variable {M : Type x} [AddCommGroup M] [Module R M]

abbrev moduleA (N : AlgebraBimodule R A B M) : Module A M :=
  N.instModuleA

abbrev moduleBOp (N : AlgebraBimodule R A B M) : Module Bᵐᵒᵖ M :=
  N.instModuleBOp

/-- The left action of an `(A, B)`-bimodule, exposed through the canonical `A`-module structure. -/
abbrev leftMul (N : AlgebraBimodule R A B M) (a : A) (x : M) : M :=
  letI := N.moduleA
  a • x

/-- The right action of an `(A, B)`-bimodule, exposed through the canonical `Bᵐᵒᵖ`-module
structure. -/
abbrev rightMul (N : AlgebraBimodule R A B M) (x : M) (b : B) : M :=
  letI := N.moduleBOp
  (MulOpposite.op b) • x

end AlgebraBimodule

/-- Definition 22.28.1 (2): a graded `(A, B)`-bimodule over `ℤ`-graded `R`-algebras
`𝒜` and `𝒝` is an `(A, B)`-bimodule together with a direct-sum grading whose homogeneous pieces are
preserved by the left `A`-action and the right `B`-action in the expected degrees. -/
@[stacks 0FQH]
structure GradedAlgebraBimodule
    (𝒜 : ZGradedAlgebra R A) (𝒝 : ZGradedAlgebra R B)
    extends AlgebraBimodule R A B M where
  /-- The degree-`n` homogeneous piece of `M`. -/
  grading : ℤ → Submodule R M
  /-- The direct-sum decomposition `M = ⨁ M^n`. -/
  gradingEquiv : M ≃ₗ[R] ⨁ n : ℤ, grading n
  /-- Left multiplication by a homogeneous element of degree `n` sends `M^m` to `M^(n + m)`. -/
  left_smul_mem :
    ∀ ⦃n m : ℤ⦄ ⦃a : A⦄ ⦃x : M⦄,
      a ∈ 𝒜 n → x ∈ grading m → a • x ∈ grading (n + m)
  /-- Right multiplication by a homogeneous element of degree `m` sends `M^n` to `M^(n + m)`. -/
  right_smul_mem :
    ∀ ⦃n m : ℤ⦄ ⦃x : M⦄ ⦃b : B⦄,
      x ∈ grading n → b ∈ 𝒝 m → (MulOpposite.op b) • x ∈ grading (n + m)

namespace GradedAlgebraBimodule

variable {R : Type u} [Ring R]
variable {A : Type v} [Ring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable {B : Type w} [Ring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
variable {M : Type x} [AddCommGroup M] [Module R M]
variable {𝒜 : ZGradedAlgebra R A} {𝒝 : ZGradedAlgebra R B}

abbrev moduleA (N : GradedAlgebraBimodule R A B M 𝒜 𝒝) : Module A M :=
  N.toAlgebraBimodule.instModuleA

abbrev moduleBOp (N : GradedAlgebraBimodule R A B M 𝒜 𝒝) : Module Bᵐᵒᵖ M :=
  N.toAlgebraBimodule.instModuleBOp

abbrev leftMul (N : GradedAlgebraBimodule R A B M 𝒜 𝒝) (a : A) (x : M) : M :=
  N.toAlgebraBimodule.leftMul a x

abbrev rightMul (N : GradedAlgebraBimodule R A B M 𝒜 𝒝) (x : M) (b : B) : M :=
  N.toAlgebraBimodule.rightMul x b

end GradedAlgebraBimodule

/-- Definition 22.28.1 (3): a differential graded `(A, B)`-bimodule over differential graded
`R`-algebras `𝒜` and `𝒝` is a graded `(A, B)`-bimodule equipped with a degree-`1` differential
squaring to zero and satisfying the graded Leibniz rules for both actions. -/
@[stacks 0FQH]
structure DifferentialGradedAlgebraBimodule
    (𝒜 : DGAA)
    (𝒝 : DGAB)
    extends GradedAlgebraBimodule R A B M 𝒜 𝒝 where
  /-- The differential on the underlying graded bimodule. -/
  differential : M →ₗ[R] M
  /-- The differential raises degree by `1`. -/
  differential_mem :
    ∀ ⦃n : ℤ⦄ ⦃x : M⦄, x ∈ grading n → differential x ∈ grading (n + 1)
  /-- The differential squares to zero. -/
  differential_sq : differential.comp differential = 0
  /-- The differential satisfies the graded Leibniz rule for the left action. -/
  differential_left_smul :
    ∀ ⦃n m : ℤ⦄ ⦃a : A⦄ ⦃x : M⦄,
      a ∈ 𝒜 n → x ∈ grading m →
        differential (a • x) =
          𝒜.differential a • x + (n.negOnePow : R) • a • differential x
  /-- The differential satisfies the graded Leibniz rule for the right action. -/
  differential_right_smul :
    ∀ ⦃n m : ℤ⦄ ⦃x : M⦄ ⦃b : B⦄,
      x ∈ grading n → b ∈ 𝒝 m →
        differential ((MulOpposite.op b) • x) =
          (MulOpposite.op b) • differential x +
            (n.negOnePow : R) • ((MulOpposite.op (𝒝.differential b)) • x)

namespace DifferentialGradedAlgebraBimodule

end DifferentialGradedAlgebraBimodule

end AlgebraBimodule

end
