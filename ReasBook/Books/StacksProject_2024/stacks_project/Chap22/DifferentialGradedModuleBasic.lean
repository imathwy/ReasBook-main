import StacksProject_2024.stacks_project.Chap22.Definition_22_3_1

noncomputable section

universe u v

section

variable {R : Type u} [CommRing R]

/-- Transport a linear map across an equality of codomain `R`-modules. -/
def castLinearMap
    {M N N' : ModuleCat.{v} R}
    (h : N = N') (f : M →ₗ[R] N) : M →ₗ[R] N' :=
  match h with
  | rfl => f

/-- Transporting along the reflexive equality does nothing. -/
@[simp] theorem castLinearMap_rfl
    {M N : ModuleCat.{v} R}
    (f : M →ₗ[R] N) :
    castLinearMap rfl f = f :=
  rfl

/-- Applying a transported linear map is the same as transporting the output. -/
@[simp] theorem castLinearMap_apply
    {M N N' : ModuleCat.{v} R}
    (h : N = N') (f : M →ₗ[R] N) (x : M) :
    castLinearMap h f x =
      cast (congrArg (fun X : ModuleCat.{v} R ↦ (X : Type v)) h) (f x) := by
  subst h
  rfl

/-- The degree-`0` part of a right differential graded module action on `M^p` lands in
`M^(p + 0)`. -/
theorem rightDGModuleZeroTargetEq {M : ℤ → ModuleCat.{v} R} (p : ℤ) :
    (M p : Type v) = M (p + 0) := by
  rw [add_zero]

/-- Successive right actions by degrees `i` and `j` land in `M^(p + (i + j))`. -/
theorem rightDGModuleMulTargetEq {M : ℤ → ModuleCat.{v} R} (p i j : ℤ) :
    (M ((p + i) + j) : Type v) = M (p + (i + j)) := by
  rw [add_assoc]

/-- In the right Leibniz rule, applying `d_M` first lands in degree `p + i + 1`. -/
theorem rightDGModuleDLeftTargetEq {M : ℤ → ModuleCat.{v} R} (p i : ℤ) :
    (M ((p + 1) + i) : Type v) = M (p + i + 1) := by
  calc
    (M ((p + 1) + i) : Type v) = M (p + (1 + i)) := by rw [add_assoc]
    _ = M (p + (i + 1)) := by rw [add_comm 1 i]
    _ = M (p + i + 1) := by rw [add_assoc]

/-- In the right Leibniz rule, applying `d_A` first also lands in degree `p + i + 1`. -/
theorem rightDGModuleDRightTargetEq {M : ℤ → ModuleCat.{v} R} (p i : ℤ) :
    (M (p + (i + 1)) : Type v) = M (p + i + 1) := by
  rw [add_assoc]

end
