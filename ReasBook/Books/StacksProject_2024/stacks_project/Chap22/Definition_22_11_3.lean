import StacksProject_2024.stacks_project.Chap22.Definition_22_28_1

open scoped DirectSum

universe u v w x

/- Source/core/bridge triage:
- source-facing: the right and left shifts of graded modules over a `ℤ`-graded algebra;
- core/canonical: `ZGradedAlgebra` and `GradedAlgebraBimodule` from `Definition_22_28_1`;
- bridge/view: the degreewise graded-object and homogeneous-action APIs below let the source
  shifts reuse the canonical total graded-algebra and bimodule owners without reintroducing a
  parallel owner layer. -/

section

variable {R : Type u} [Ring R]
variable {A : Type v} [Ring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable {B : Type w} [Ring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
variable {M : Type x} [AddCommGroup M] [Module R M]

namespace ZGradedAlgebra

/-- The unit of a graded algebra is a homogeneous element of degree `0`. -/
abbrev homogeneousOne (𝒜 : ZGradedAlgebra R A) : 𝒜 0 :=
  ⟨1, 𝒜.one_mem⟩

/-- The product of homogeneous elements of degrees `i` and `j` lands in degree `i + j`. -/
def mulHom (𝒜 : ZGradedAlgebra R A) (i j : ℤ) :
    𝒜 i → 𝒜 j → 𝒜 (i + j) :=
  fun a b ↦ ⟨(a : A) * (b : A), 𝒜.mul_mem a.2 b.2⟩

@[simp] theorem homogeneousOne_val (𝒜 : ZGradedAlgebra R A) :
    (homogeneousOne 𝒜 : A) = 1 :=
  rfl

@[simp] theorem mulHom_apply
    (𝒜 : ZGradedAlgebra R A) (i j : ℤ) (a : 𝒜 i) (b : 𝒜 j) :
    ((mulHom 𝒜 i j a b : 𝒜 (i + j)) : A) = (a : A) * (b : A) :=
  rfl

end ZGradedAlgebra

namespace GradedAlgebraBimodule

variable {𝒜 : ZGradedAlgebra R A} {𝒝 : ZGradedAlgebra R B}

/-- The homogeneous left action of a graded bimodule. -/
def leftMulHom (N : GradedAlgebraBimodule R A B M 𝒜 𝒝) (i j : ℤ) :
    𝒜 i → N.grading j → N.grading (i + j) :=
  fun a x ↦ ⟨N.leftMul (a : A) (x : M), N.left_smul_mem a.2 x.2⟩

/-- The homogeneous right action of a graded bimodule. -/
def rightMulHom (N : GradedAlgebraBimodule R A B M 𝒜 𝒝) (i j : ℤ) :
    N.grading i → 𝒝 j → N.grading (i + j) :=
  fun x b ↦ ⟨N.rightMul (x : M) (b : B), N.right_smul_mem x.2 b.2⟩

@[simp] theorem leftMulHom_apply
    (N : GradedAlgebraBimodule R A B M 𝒜 𝒝) (i j : ℤ) (a : 𝒜 i) (x : N.grading j) :
    (N.leftMulHom i j a x : M) = N.leftMul a x := by
  rfl

@[simp] theorem rightMulHom_apply
    (N : GradedAlgebraBimodule R A B M 𝒜 𝒝) (i j : ℤ) (x : N.grading i) (b : 𝒝 j) :
    (N.rightMulHom i j x b : M) = N.rightMul x b := by
  rfl

/-- The Koszul sign twisting the left action on the shift by `k`. -/
abbrev dgSign (i k : ℤ) : R :=
  ((i * k).negOnePow : R)

private def shiftGradingEquiv
    (N : GradedAlgebraBimodule R A B M 𝒜 𝒝) (k : ℤ) :
    (⨁ n : ℤ, N.grading n) ≃ₗ[R] ⨁ n : ℤ, N.grading (n + - -k) :=
  by
    simpa using DirectSum.lequivCongrLeft R (Equiv.addRight (-k))

/-- Helper for Definition 22.11.3: the original left action still lands in the shifted degree on
the right shift. -/
private theorem rightShift_leftSmulMem
    (N : GradedAlgebraBimodule R A B M 𝒜 𝒝) (k n m : ℤ) {a : A} {x : M}
    (ha : a ∈ 𝒜 n) (hx : x ∈ N.grading (m + - -k)) :
    N.leftMul a x ∈ N.grading ((n + m) + - -k) := by
  -- The right shift only reindexes degrees, so the original closure statement applies after one
  -- reassociation of the target degree.
  simpa [GradedAlgebraBimodule.leftMul, AlgebraBimodule.leftMul, add_assoc] using N.left_smul_mem ha hx

/-- Helper for Definition 22.11.3: the original right action still lands in the shifted degree on
the right shift. -/
private theorem rightShift_rightSmulMem
    (N : GradedAlgebraBimodule R A B M 𝒜 𝒝) (k n m : ℤ) {x : M} {b : B}
    (hx : x ∈ N.grading (n + - -k)) (hb : b ∈ 𝒝 m) :
    N.rightMul x b ∈ N.grading ((n + m) + - -k) := by
  -- The target degree is the same after reassociating the shifted index.
  simpa [GradedAlgebraBimodule.rightMul, AlgebraBimodule.rightMul, add_assoc, add_left_comm,
    add_comm] using N.right_smul_mem hx hb

/-- Definition 22.11.3: (1) shifting a graded bimodule on the right keeps the underlying left and
right actions and replaces the grading by `N[k]^n = N^{n + k}`. For a genuine right module, this
is exactly the textbook shift. -/
@[stacks 0FQ1]
def rightShift (N : GradedAlgebraBimodule R A B M 𝒜 𝒝) (k : ℤ) :
    GradedAlgebraBimodule R A B M 𝒜 𝒝 where
  toAlgebraBimodule := N.toAlgebraBimodule
  grading n := N.grading (n + - -k)
  gradingEquiv := N.gradingEquiv.trans (shiftGradingEquiv N k)
  left_smul_mem := by
    intro n m a x ha hx
    -- The shifted grading closure has been isolated so the definition stays bookkeeping-only.
    simpa [GradedAlgebraBimodule.leftMul, AlgebraBimodule.leftMul] using
      rightShift_leftSmulMem N k n m ha hx
  right_smul_mem := by
    intro n m x b hx hb
    -- The right action uses the same shifted-degree calculation as the left companion lemma.
    simpa [GradedAlgebraBimodule.rightMul, AlgebraBimodule.rightMul] using
      rightShift_rightSmulMem N k n m hx hb

/-- The degree-`n` piece of `N[k]` is `N^{n + k}`. -/
@[simp] theorem rightShift_grading
    (N : GradedAlgebraBimodule R A B M 𝒜 𝒝)
    (k n : ℤ) :
    (N.rightShift k).grading n = N.grading (n + k) :=
  by simp [rightShift]

/-- Membership in the degree-`n` piece of `N[k]` is membership in degree `n + k` of `N`. -/
@[simp] theorem mem_rightShift_grading_iff
    (N : GradedAlgebraBimodule R A B M 𝒜 𝒝)
    (k n : ℤ) {x : M} :
    x ∈ (N.rightShift k).grading n ↔ x ∈ N.grading (n + k) :=
  by simp [rightShift]

@[simp] theorem rightShift_leftMulHom_apply
    (N : GradedAlgebraBimodule R A B M 𝒜 𝒝)
    (k i j : ℤ) (a : 𝒜 i) (x : (N.rightShift k).grading j) :
    ((N.rightShift k).leftMulHom i j a x : M) = (N.rightShift k).leftMul a x := by
  simp [leftMulHom, rightShift]

@[simp] theorem rightShift_leftMul_apply
    (N : GradedAlgebraBimodule R A B M 𝒜 𝒝)
    (k : ℤ) (a : A) (x : M) :
    (N.rightShift k).leftMul a x = N.leftMul a x :=
  rfl

@[simp] theorem rightShift_rightMulHom_apply
    (N : GradedAlgebraBimodule R A B M 𝒜 𝒝)
    (k i j : ℤ) (x : (N.rightShift k).grading i) (b : 𝒝 j) :
    ((N.rightShift k).rightMulHom i j x b : M) = (N.rightShift k).rightMul x b := by
  simp [rightMulHom, rightShift]

@[simp] theorem rightShift_rightMul_apply
    (N : GradedAlgebraBimodule R A B M 𝒜 𝒝)
    (k : ℤ) (x : M) (b : B) :
    (N.rightShift k).rightMul x b = N.rightMul x b :=
  rfl

namespace leftShift

private def signedLinear
    (𝒜 : ZGradedAlgebra R A) (k : ℤ) : A →ₗ[R] A :=
  (DirectSum.toModule R ℤ A
      fun i ↦
        { toFun := fun (a : 𝒜 i) ↦ ((i * k).negOnePow : R) • (a : A)
          map_add' := by
            intro a b
            simp [smul_add]
          map_smul' := by
            intro r a
            rcases Int.even_or_odd (i * k) with hEven | hOdd
            · rw [Int.negOnePow_even _ hEven]
              simp [smul_smul]
            · rw [Int.negOnePow_odd _ hOdd]
              simpa [smul_smul, neg_one_mul, mul_neg_one] }).comp
    𝒜.gradingEquiv.toLinearMap

/-- Helper for Definition 22.11.3: `gradingEquiv` places a homogeneous element into its matching
direct-sum summand. -/
private theorem gradingEquiv_apply_homogeneous
    (𝒜 : ZGradedAlgebra R A) {i : ℤ} (a : 𝒜 i) :
    (𝒜.gradingEquiv : A →ₗ[R] ⨁ n : ℤ, 𝒜 n) a =
      DirectSum.of (fun n ↦ 𝒜 n) i a := by
  -- Re-express the graded decomposition using the standard `DirectSum.of` constructor.
  simpa [DirectSum.lof_eq_of] using 𝒜.gradingEquiv_apply a

@[simp] private theorem signedLinear_apply_homogeneous
    (𝒜 : ZGradedAlgebra R A) (k : ℤ) {i : ℤ} (a : 𝒜 i) :
    leftShift.signedLinear 𝒜 k a = (dgSign i k : R) • (a : A) := by
  -- Rewrite the decomposition of a homogeneous element to its unique direct-sum summand.
  have hdecomp :
      (𝒜.gradingEquiv : A →ₗ[R] ⨁ n : ℤ, 𝒜 n) a =
        DirectSum.lof R ℤ (fun n ↦ 𝒜 n) i a := by
    simpa using 𝒜.gradingEquiv_apply a
  rw [signedLinear, LinearMap.comp_apply, hdecomp, DirectSum.toModule_lof]
  rfl

/-- Helper for Definition 22.11.3: `gradingEquiv.symm` sends a single homogeneous direct-sum
summand back to the corresponding homogeneous element. -/
@[simp] private theorem gradingEquiv_symm_of
    (𝒜 : ZGradedAlgebra R A) {i : ℤ} (a : 𝒜 i) :
    𝒜.gradingEquiv.symm (DirectSum.of (fun n ↦ 𝒜 n) i a) = a := by
  -- Route correction: rewrite the direct-sum summand back to `gradingEquiv a` before applying
  -- the inverse/evaluation identity.
  rw [← gradingEquiv_apply_homogeneous 𝒜 a]
  exact 𝒜.gradingEquiv.symm_apply_apply a

/-- Helper for Definition 22.11.3: transporting the zero direct-sum element back through
`gradingEquiv.symm` gives zero. -/
@[simp] private theorem gradingEquiv_symm_zero
    (𝒜 : ZGradedAlgebra R A) :
    𝒜.gradingEquiv.symm 0 = 0 := by
  -- A linear equivalence preserves zero, so the transport back from the zero summand is trivial.
  simp

private theorem dgSign_add_left (i j k : ℤ) :
    (dgSign (i + j) k : R) = (dgSign i k : R) * (dgSign j k : R) := by
  unfold dgSign
  have hmul : (i + j) * k = i * k + j * k := by ring
  rw [hmul, Int.negOnePow_add]
  simp [Int.cast_mul]

private theorem signedLinear_mul_homogeneous
    (𝒜 : ZGradedAlgebra R A) (k : ℤ) {i j : ℤ} (a : 𝒜 i) (b : 𝒜 j) :
    leftShift.signedLinear 𝒜 k ((a : A) * (b : A)) =
      leftShift.signedLinear 𝒜 k a * leftShift.signedLinear 𝒜 k b := by
  calc
    leftShift.signedLinear 𝒜 k ((a : A) * (b : A)) =
        (dgSign (i + j) k : R) • ((a : A) * (b : A)) := by
          simpa using
            (signedLinear_apply_homogeneous 𝒜 k (ZGradedAlgebra.mulHom 𝒜 i j a b))
    _ = ((dgSign i k : R) • (a : A)) * ((dgSign j k : R) • (b : A)) := by
      rw [leftShift.dgSign_add_left]
      symm
      simpa using
        (smul_mul_smul (dgSign i k : R) (a : A) (dgSign j k : R) (b : A))
    _ = leftShift.signedLinear 𝒜 k a * leftShift.signedLinear 𝒜 k b := by
      simp [signedLinear_apply_homogeneous]

/-- Helper for Definition 22.11.3: if the left factor is homogeneous, the signed map sends its
product with any element to the product of the signed images. -/
private theorem signedLinear_mul_homogeneous_left
    (𝒜 : ZGradedAlgebra R A) (k : ℤ) {i : ℤ} (a : 𝒜 i) :
    ∀ b : A,
      leftShift.signedLinear 𝒜 k ((a : A) * b) =
        leftShift.signedLinear 𝒜 k a * leftShift.signedLinear 𝒜 k b := by
  intro b
  suffices h :
      ∀ z : ⨁ n : ℤ, 𝒜 n,
        leftShift.signedLinear 𝒜 k ((a : A) * 𝒜.gradingEquiv.symm z) =
          leftShift.signedLinear 𝒜 k a * leftShift.signedLinear 𝒜 k (𝒜.gradingEquiv.symm z) by
    simpa using h (𝒜.gradingEquiv b)
  intro z
  refine DirectSum.induction_on z ?_ ?_ ?_
  · -- The zero summand becomes the zero element after transporting back through `gradingEquiv`.
    rw [gradingEquiv_symm_zero 𝒜]
    simp
  · intro j c
    -- Collapse the transported homogeneous summand before using the homogeneous multiplicativity
    -- lemma.
    rw [gradingEquiv_symm_of 𝒜 c]
    exact signedLinear_mul_homogeneous 𝒜 k a c
  · intro v₁ v₂ hv₁ hv₂
    -- Extend the homogeneous formula to sums by additivity in the second variable.
    simpa [mul_add, hv₁, hv₂]

private theorem signedLinear_map_mul
    (𝒜 : ZGradedAlgebra R A) (k : ℤ) (a b : A) :
    leftShift.signedLinear 𝒜 k (a * b) =
      leftShift.signedLinear 𝒜 k a * leftShift.signedLinear 𝒜 k b := by
  suffices h :
      ∀ z : ⨁ n : ℤ, 𝒜 n,
        leftShift.signedLinear 𝒜 k (𝒜.gradingEquiv.symm z * b) =
          leftShift.signedLinear 𝒜 k (𝒜.gradingEquiv.symm z) * leftShift.signedLinear 𝒜 k b by
    simpa using h (𝒜.gradingEquiv a)
  intro z
  refine DirectSum.induction_on z ?_ ?_ ?_
  · -- The zero summand branch reduces to the multiplicative zero laws after transporting back.
    rw [gradingEquiv_symm_zero 𝒜]
    simp
  · intro i a
    -- Collapse the transported homogeneous left factor before invoking the mixed lemma.
    rw [gradingEquiv_symm_of 𝒜 a]
    exact signedLinear_mul_homogeneous_left 𝒜 k a b
  · intro u₁ u₂ hu₁ hu₂
    -- Extend multiplicativity from homogeneous left factors by additivity in the first variable.
    simpa [add_mul, hu₁, hu₂]

private def signedRingHom (𝒜 : ZGradedAlgebra R A) (k : ℤ) : A →+* A where
  toFun := leftShift.signedLinear 𝒜 k
  map_zero' := (leftShift.signedLinear 𝒜 k).map_zero
  map_one' := by
    simpa [dgSign] using
      (signedLinear_apply_homogeneous 𝒜 k (ZGradedAlgebra.homogeneousOne 𝒜))
  map_add' := (leftShift.signedLinear 𝒜 k).map_add
  map_mul' := signedLinear_map_mul 𝒜 k

@[simp] private theorem signedRingHom_apply_homogeneous
    (𝒜 : ZGradedAlgebra R A) (k : ℤ) {i : ℤ} (a : 𝒜 i) :
    leftShift.signedRingHom 𝒜 k (a : A) = (dgSign i k : R) • (a : A) := by
  simpa [leftShift.signedRingHom] using leftShift.signedLinear_apply_homogeneous 𝒜 k a

/-- Helper for Definition 22.11.3: the Koszul-twisted left action lands in the shifted degree. -/
private theorem leftSmulMem
    (N : GradedAlgebraBimodule R A B M 𝒜 𝒝) (k n m : ℤ) {a : A} {x : M}
    (ha : a ∈ 𝒜 n) (hx : x ∈ N.grading (m + - -k)) :
    N.leftMul (leftShift.signedRingHom 𝒜 k a) x ∈ N.grading ((n + m) + - -k) := by
  -- Rewrite the twisted action on a homogeneous algebra element to the Koszul sign formula.
  letI : Module A M := N.moduleA
  rw [leftShift.signedRingHom_apply_homogeneous 𝒜 k ⟨a, ha⟩]
  letI : IsScalarTower R A M := N.toAlgebraBimodule.instIsScalarTowerLeft
  have hsmul : (dgSign n k : R) • (a • x) ∈ N.grading (n + (m + - -k)) := by
    -- First use the original graded action, then use scalar closure of the target degree piece.
    exact (N.grading (n + (m + - -k))).smul_mem (dgSign n k : R)
      (by
        simpa [smul_assoc] using N.left_smul_mem ha hx)
  simpa [GradedAlgebraBimodule.leftMul, AlgebraBimodule.leftMul, smul_assoc, add_assoc] using hsmul

@[reducible] private def moduleA
    (N : GradedAlgebraBimodule R A B M 𝒜 𝒝) (k : ℤ) : Module A M :=
  let _ : Module A M := N.moduleA
  Module.compHom M (leftShift.signedRingHom 𝒜 k)

private def algebraBimodule
    (N : GradedAlgebraBimodule R A B M 𝒜 𝒝) (k : ℤ) : AlgebraBimodule R A B M where
  instModuleA := leftShift.moduleA N k
  instModuleBOp := N.toAlgebraBimodule.instModuleBOp
  instSMulCommClass := by
    letI : Module A M := leftShift.moduleA N k
    letI : Module Bᵐᵒᵖ M := N.moduleBOp
    exact
      { smul_comm := by
          intro a b x
          letI : Module A M := N.moduleA
          letI : Module Bᵐᵒᵖ M := N.moduleBOp
          letI : SMulCommClass A Bᵐᵒᵖ M := N.toAlgebraBimodule.instSMulCommClass
          simpa [leftShift.moduleA, leftShift.signedRingHom, GradedAlgebraBimodule.leftMul,
            AlgebraBimodule.leftMul, smul_assoc] using
            (smul_comm (leftShift.signedRingHom 𝒜 k a) b x) }
  instSMulCommClassLeft := by
    letI : Module A M := leftShift.moduleA N k
    exact
      { smul_comm := by
          intro r a x
          letI : Module A M := N.moduleA
          letI : SMulCommClass R A M := N.toAlgebraBimodule.instSMulCommClassLeft
          change r • ((leftShift.signedRingHom 𝒜 k a) • x) =
            (leftShift.signedRingHom 𝒜 k a) • (r • x)
          simpa [leftShift.moduleA, leftShift.signedRingHom, GradedAlgebraBimodule.leftMul,
            AlgebraBimodule.leftMul] using
            (smul_comm r (leftShift.signedRingHom 𝒜 k a) x) }
  instIsScalarTowerLeft := by
    letI : Module A M := leftShift.moduleA N k
    exact
      { smul_assoc := by
          intro r a x
          letI : Module A M := N.moduleA
          letI : IsScalarTower R A M := N.toAlgebraBimodule.instIsScalarTowerLeft
          change (leftShift.signedRingHom 𝒜 k (r • a)) • x =
            r • ((leftShift.signedRingHom 𝒜 k a) • x)
          simp [leftShift.signedRingHom, smul_assoc] }
  instSMulCommClassRight := N.toAlgebraBimodule.instSMulCommClassRight
  instIsScalarTowerRight := N.toAlgebraBimodule.instIsScalarTowerRight

end leftShift

/-- Definition 22.11.3 (2): the left-shift companion keeps the grading `N[k]^n = N^{n + k}` and
twists the left action by the usual Koszul sign. For a genuine left module, this is exactly the
textbook shift. -/
@[stacks 0FQ1]
def leftShift (N : GradedAlgebraBimodule R A B M 𝒜 𝒝) (k : ℤ) :
    GradedAlgebraBimodule R A B M 𝒜 𝒝 where
  toAlgebraBimodule := leftShift.algebraBimodule N k
  grading n := N.grading (n + - -k)
  gradingEquiv := N.gradingEquiv.trans (shiftGradingEquiv N k)
  left_smul_mem := by
    intro n m a x ha hx
    -- Route correction: keep the source Koszul-sign route, but isolate the degree argument in a
    -- helper lemma so the `def` body only assembles the shifted structure.
    simpa [leftShift.moduleA] using leftShift.leftSmulMem N k n m ha hx
  right_smul_mem := by
    intro n m x b hx hb
    simpa [add_assoc, add_left_comm, add_comm] using N.right_smul_mem hx hb

/-- The degree-`n` piece of the left shift is the degree-`n + k` piece of the original bimodule.
-/
@[simp] theorem leftShift_grading
    (N : GradedAlgebraBimodule R A B M 𝒜 𝒝)
    (k n : ℤ) :
    (N.leftShift k).grading n = N.grading (n + k) :=
  by simp [leftShift]

/-- Membership in the degree-`n` piece of the left shift is membership in degree `n + k` of the
original bimodule. -/
@[simp] theorem mem_leftShift_grading_iff
    (N : GradedAlgebraBimodule R A B M 𝒜 𝒝)
    (k n : ℤ) {x : M} :
    x ∈ (N.leftShift k).grading n ↔ x ∈ N.grading (n + k) :=
  by simp [leftShift]

/-- On homogeneous algebra elements, the left action of the shifted bimodule is the Koszul sign
times the original action. -/
@[simp] theorem leftShift_leftMulHom_apply
    (N : GradedAlgebraBimodule R A B M 𝒜 𝒝)
    (k i j : ℤ) (a : 𝒜 i) (x : (N.leftShift k).grading j) :
    ((N.leftShift k).leftMulHom i j a x : M) = (dgSign i k : R) • N.leftMul a x := by
  change (N.leftShift k).leftMul a x = (dgSign i k : R) • N.leftMul a x
  change N.leftMul (leftShift.signedRingHom 𝒜 k a) x = (dgSign i k : R) • N.leftMul a x
  rw [leftShift.signedRingHom_apply_homogeneous 𝒜 k a]
  letI : Module A M := N.moduleA
  letI : IsScalarTower R A M := N.toAlgebraBimodule.instIsScalarTowerLeft
  simp [GradedAlgebraBimodule.leftMul, AlgebraBimodule.leftMul, smul_assoc]

/-- On homogeneous algebra elements and homogeneous elements of the shifted bimodule, the left
action on `N[k]` is the Koszul-sign twist of the original left action. -/
theorem leftShift_leftMul_apply
    (N : GradedAlgebraBimodule R A B M 𝒜 𝒝)
    (k i j : ℤ) {a : A} {x : M}
    (ha : a ∈ 𝒜.grading i) (hx : x ∈ (N.leftShift k).grading j) :
    (N.leftShift k).leftMul a x = (dgSign i k : R) • N.leftMul a x := by
  simpa using
    (leftShift_leftMulHom_apply N k i j ⟨a, ha⟩ ⟨x, hx⟩)

@[simp] theorem leftShift_rightMulHom_apply
    (N : GradedAlgebraBimodule R A B M 𝒜 𝒝)
    (k i j : ℤ) (x : (N.leftShift k).grading i) (b : 𝒝 j) :
    ((N.leftShift k).rightMulHom i j x b : M) = (N.leftShift k).rightMul x b := by
  simp [rightMulHom, leftShift]

@[simp] theorem leftShift_rightMul_apply
    (N : GradedAlgebraBimodule R A B M 𝒜 𝒝)
    (k : ℤ) (x : M) (b : B) :
    (N.leftShift k).rightMul x b = N.rightMul x b :=
  rfl

end GradedAlgebraBimodule

end
