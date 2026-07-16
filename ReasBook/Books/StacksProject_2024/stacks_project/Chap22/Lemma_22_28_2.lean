import StacksProject_2024.stacks_project.Chap22.Lemma_22_13_3

universe u

section

variable {R : Type u} [CommRing R]

local notation "DGA" => CochainDGAlgebra R

/-- Reassociate the degree target `p + (q + r)` as `(p + q) + r`. -/
theorem dgModuleAddAssocTargetEq (M : ℤ → ModuleCat R) (p q r : ℤ) :
    (M (p + (q + r)) : Type u) = M ((p + q) + r) := by
  rw [add_assoc]

/-- Helper for Lemma 22.28.2: the fixed-family identification transports `M p` back to the
underlying right differential graded module of `rhoB` in degree `p`. -/
theorem fixedUnderlyingRightActionSourceEq
    {B : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)}
    (rhoB : DifferentialGradedModule.WithFixedUnderlying B M dM) (p : ℤ) :
    (M p : Type u) = rhoB.toRightDifferentialGradedModule.X p := by
  simpa using congrArg (fun X : ℤ → ModuleCat R ↦ (X p : Type u)) rhoB.X_eq.symm

/-- Helper for Lemma 22.28.2: after applying the underlying right action of `rhoB`, the
resulting degree `q + p` is transported to the source-facing degree `p + q`. -/
theorem fixedUnderlyingRightActionTargetEq
    {B : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)}
    (rhoB : DifferentialGradedModule.WithFixedUnderlying B M dM) (p q : ℤ) :
    (rhoB.toRightDifferentialGradedModule.X (q + p) : Type u) = M (p + q) := by
  rw [rhoB.X_eq, add_comm]

/-- Helper for Lemma 22.28.2: the source-facing right action of a fixed-underlying right
differential graded `B`-module on the chosen graded pieces `M`. -/
def fixedUnderlyingRightAction
    {B : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)}
    (rhoB : DifferentialGradedModule.WithFixedUnderlying B M dM)
    (p q : ℤ) (x : M p) (b : B.X q) : M (p + q) :=
  cast (fixedUnderlyingRightActionTargetEq rhoB p q)
    (rhoB.toRightDifferentialGradedModule.smul q p b
      (cast (fixedUnderlyingRightActionSourceEq rhoB p) x))

/-- A left differential graded `A`-module structure on `(M, dM)` is compatible with the fixed
right differential graded `B`-module structure `rhoB` when the two actions commute. -/
def CompatibleDGBimoduleStructure
    {A B : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)}
    (rhoB : DifferentialGradedModule.WithFixedUnderlying B M dM)
    (rhoA : LeftDifferentialGradedModule.WithFixedUnderlying A M dM) : Prop :=
  ∀ (i p q : ℤ) (a : A.X i) (x : M p) (b : B.X q),
    cast (dgModuleAddAssocTargetEq M i p q)
        (rhoA i (p + q) a (fixedUnderlyingRightAction rhoB p q x b)) =
      fixedUnderlyingRightAction rhoB (i + p) q (rhoA i p a x) b

/-- A homomorphism from `A` to the endomorphism differential graded algebra of `(M, dM)` is
right `B`-linear when every homogeneous endomorphism in its image commutes with the fixed right
`B`-action `rhoB`. -/
def IsBLinearEndomorphismDGAHom
    {A B : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)}
    (rhoB : DifferentialGradedModule.WithFixedUnderlying B M dM)
    (tau : EndomorphismDGAHom A M dM) : Prop :=
  ∀ (i p q : ℤ) (a : A.X i) (x : M p) (b : B.X q),
    cast (dgModuleAddAssocTargetEq M i p q)
        (((tau.map i) a) (p + q) (fixedUnderlyingRightAction rhoB p q x b)) =
      fixedUnderlyingRightAction rhoB (i + p) q (((tau.map i) a) p x) b

variable {A B : DGA} {M : ℤ → ModuleCat R}
variable {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)}
variable {rhoB : DifferentialGradedModule.WithFixedUnderlying B M dM}

/-- Helper for Lemma 22.28.2: after transporting the left action across Lemma 22.13.1, the
commuting-action equation is exactly the right-`B`-linearity equation for the associated
endomorphism-DGA map. -/
lemma commutingActionEq_iff_toEndomorphismDGAHomEq
    (rhoA : LeftDifferentialGradedModule.WithFixedUnderlying A M dM)
    (i p q : ℤ) (a : A.X i) (x : M p) (b : B.X q) :
    cast (dgModuleAddAssocTargetEq M i p q)
        (rhoA i (p + q) a (fixedUnderlyingRightAction rhoB p q x b)) =
      fixedUnderlyingRightAction rhoB (i + p) q (rhoA i p a x) b ↔
    cast (dgModuleAddAssocTargetEq M i p q)
        ((((LeftDifferentialGradedModule.WithFixedUnderlying.toEndomorphismDGAHom rhoA).map i) a)
          (p + q) (fixedUnderlyingRightAction rhoB p q x b)) =
      fixedUnderlyingRightAction rhoB (i + p) q
        ((((LeftDifferentialGradedModule.WithFixedUnderlying.toEndomorphismDGAHom rhoA).map i) a)
          p x) b := by
  -- Unfold currying of the left action so both sides become the same commuting-action equation.
  rcases rhoA with ⟨rhoA, hX, hd⟩
  cases hX
  cases hd
  constructor <;> intro h <;> simpa
    [fixedUnderlyingRightAction,
      LeftDifferentialGradedModule.WithFixedUnderlying.toEndomorphismDGAHom,
      LeftDifferentialGradedModule.WithFixedUnderlying.smul] using h

/-- Helper for Lemma 22.28.2: packaging an endomorphism-DGA map back into the fixed-underlying
left module fiber leaves the commuting-action equation unchanged. -/
lemma commutingActionEq_iff_ofEndomorphismDGAHomEq
    (tau : EndomorphismDGAHom A M dM)
    (i p q : ℤ) (a : A.X i) (x : M p) (b : B.X q) :
    cast (dgModuleAddAssocTargetEq M i p q)
        ((LeftDifferentialGradedModule.WithFixedUnderlying.ofEndomorphismDGAHom tau)
          i (p + q) a (fixedUnderlyingRightAction rhoB p q x b)) =
      fixedUnderlyingRightAction rhoB (i + p) q
        ((LeftDifferentialGradedModule.WithFixedUnderlying.ofEndomorphismDGAHom tau) i p a x) b ↔
    cast (dgModuleAddAssocTargetEq M i p q)
        ((((tau.map i) a) (p + q) (fixedUnderlyingRightAction rhoB p q x b))) =
      fixedUnderlyingRightAction rhoB (i + p) q ((((tau.map i) a) p x)) b := by
  -- Unfold packaging into the fixed-underlying left-module fiber to recover the original map.
  constructor <;> intro h <;> simpa
    [fixedUnderlyingRightAction,
      LeftDifferentialGradedModule.WithFixedUnderlying.ofEndomorphismDGAHom,
      LeftDifferentialGradedModule.WithFixedUnderlying.smul,
      EndomorphismDGAHom.toLeftDifferentialGradedModule] using h

/-- Lemma 22.28.2: a left differential graded `A`-module structure on `(M, dM)` compatible with
the fixed right differential graded `B`-module structure `rhoB` is equivalent, via Lemma
`22.13.1`, to a right-`B`-linear homomorphism from `A` to the endomorphism differential graded
algebra of `(M, dM)`. -/
@[stacks 0FQI, simp] theorem compatibleDGBimoduleStructure_toEndomorphismDGAHom_iff
    (rhoA : LeftDifferentialGradedModule.WithFixedUnderlying A M dM) :
    CompatibleDGBimoduleStructure rhoB rhoA ↔
      IsBLinearEndomorphismDGAHom rhoB
        (LeftDifferentialGradedModule.WithFixedUnderlying.toEndomorphismDGAHom rhoA) := by
  constructor
  · intro h i p q a x b
    -- Normalize the endomorphism side to the original commuting-action equation.
    simpa using
      (commutingActionEq_iff_toEndomorphismDGAHomEq
        (rhoB := rhoB) rhoA i p q a x b).mp (h i p q a x b)
  · intro h i p q a x b
    -- The same bridge rewrite recovers compatibility from right `B`-linearity.
    simpa using
      (commutingActionEq_iff_toEndomorphismDGAHomEq
        (rhoB := rhoB) rhoA i p q a x b).mpr (h i p q a x b)

/-- Packaging an endomorphism-DGA map into the fixed-underlying left module fiber preserves the
right-`B`-linearity condition of Lemma 22.28.2. Together with Lemma 22.13.1, this is the
source-facing converse direction needed to recover the textbook bijection on the compatible
subfiber. -/
@[simp] theorem ofEndomorphismDGAHom_compatibleDGBimoduleStructure_iff
    (tau : EndomorphismDGAHom A M dM) :
    CompatibleDGBimoduleStructure rhoB
        (LeftDifferentialGradedModule.WithFixedUnderlying.ofEndomorphismDGAHom tau) ↔
      IsBLinearEndomorphismDGAHom rhoB tau := by
  constructor
  · intro h i p q a x b
    -- Rewriting the packaged left action identifies compatibility with the original map `tau`.
    simpa using
      (commutingActionEq_iff_ofEndomorphismDGAHomEq
        (rhoB := rhoB) tau i p q a x b).mp (h i p q a x b)
  · intro h i p q a x b
    -- Reversing the same rewrite packages a right `B`-linear map back into the compatible fiber.
    simpa using
      (commutingActionEq_iff_ofEndomorphismDGAHomEq
        (rhoB := rhoB) tau i p q a x b).mpr (h i p q a x b)

end
