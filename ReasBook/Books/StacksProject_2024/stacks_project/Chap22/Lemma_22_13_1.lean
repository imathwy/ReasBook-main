import StacksProject_2024.stacks_project.Chap22.Lemma_22_11_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

-- Semantic search hit: `Algebra.lmul` and `DistribMulAction.toModuleEnd` confirm the standard
-- endomorphism-algebra owner for a module action; the DG-specific statement here is recorded as
-- the fixed-underlying fiber of the chapter's `LeftDifferentialGradedModule` owner.

section

variable {R : Type u} [CommRing R]

local notation "DGA" => CochainDGAlgebra R

/-- A homomorphism from `A` to the endomorphism differential graded algebra of the fixed
differential graded `R`-module `(M, dM)`, written directly in degreewise form. -/
structure EndomorphismDGAHom (A : DGA)
    (M : ℤ → ModuleCat R) (dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)) where
  /-- The degree-`m` piece of the map sends `A^m` to degree-`m` endomorphisms of `M`. -/
  map : ∀ m : ℤ, A.X m →ₗ[R] ∀ p : ℤ, M p →ₗ[R] M (m + p)
  /-- The unit of `A` acts by scalar multiples of the identity endomorphism. -/
  map_one :
    ∀ (r : R) (p : ℤ) (x : M p),
      map 0 (r • A.one) p x = cast (leftDGModuleZeroTargetEq p) (r • x)
  /-- Multiplication in `A` is sent to composition in the endomorphism differential graded
  algebra. -/
  map_mul :
    ∀ (i j : ℤ) (a : A.X i) (b : A.X j) (p : ℤ) (x : M p),
      map (i + j) (A.mul i j a b) p x =
        cast (leftDGModuleMulTargetEq p i j) (map i a (j + p) (map j b p x))
  /-- The differential on `A` is sent to the differential on the endomorphism Hom complex. -/
  comm_d :
    ∀ (m : ℤ) (a : A.X m) (p : ℤ) (x : M p),
      map (m + 1) (A.d m a) p x =
        cast (leftDGModuleDLeftTargetEq p m) (dM (m + p) (map m a p x)) -
          (((-1 : R) ^ Int.natAbs m) : R) •
            cast (leftDGModuleDRightTargetEq p m) (map m a (p + 1) (dM p x))

namespace EndomorphismDGAHom

/-- A map to the endomorphism differential graded algebra can be applied directly to a homogeneous
algebra element and then to a homogeneous module element. -/
instance (A : DGA) (M : ℤ → ModuleCat R)
    (dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)) :
    CoeFun (EndomorphismDGAHom A M dM)
      (fun _ ↦ ∀ m : ℤ, A.X m → ∀ p : ℤ, M p → M (m + p)) where
  coe tau := fun m a p x ↦ tau.map m a p x

/-- Coercion of an endomorphism-DGA map recovers its degreewise action. -/
@[simp] theorem coe_apply {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} (tau : EndomorphismDGAHom A M dM)
    (m : ℤ) (a : A.X m) (p : ℤ) (x : M p) :
    tau m a p x = tau.map m a p x :=
  rfl

/-- Two endomorphism-DGA maps are equal when they agree on every homogeneous algebra element and
homogeneous module element. -/
@[ext] theorem ext {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)}
    {tau₁ tau₂ : EndomorphismDGAHom A M dM}
    (h : ∀ (m : ℤ) (a : A.X m) (p : ℤ) (x : M p), tau₁ m a p x = tau₂ m a p x) :
    tau₁ = tau₂ := by
  cases tau₁ with
  | mk map₁ map_one₁ map_mul₁ comm_d₁ =>
      cases tau₂ with
      | mk map₂ map_one₂ map_mul₂ comm_d₂ =>
          have hmap : map₁ = map₂ := by
            funext m
            ext a p x
            exact h m a p x
          subst hmap
          have hmap_one : map_one₁ = map_one₂ := Subsingleton.elim _ _
          subst hmap_one
          have hmap_mul : map_mul₁ = map_mul₂ := Subsingleton.elim _ _
          subst hmap_mul
          have hcomm_d : comm_d₁ = comm_d₂ := Subsingleton.elim _ _
          subst hcomm_d
          rfl

/-- Multiplication for a map into the endomorphism differential graded algebra is ordinary
composition, as recorded in `map_mul`. -/
theorem map_mul_apply {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)}
    (tau : EndomorphismDGAHom A M dM)
    (i j : ℤ) (a : A.X i) (b : A.X j) (p : ℤ) (x : M p) :
    tau (i + j) (A.mul i j a b) p x =
      cast (leftDGModuleMulTargetEq p i j) (tau i a (j + p) (tau j b p x)) :=
  tau.map_mul i j a b p x

/-- Differential compatibility for a map into the endomorphism differential graded algebra is the
Hom-complex differential formula recorded in `comm_d`. -/
theorem comm_d_apply {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)}
    (tau : EndomorphismDGAHom A M dM)
    (m : ℤ) (a : A.X m) (p : ℤ) (x : M p) :
    tau (m + 1) (A.d m a) p x =
      cast (leftDGModuleDLeftTargetEq p m) (dM (m + p) (tau m a p x)) -
        (((-1 : R) ^ Int.natAbs m) : R) •
          cast (leftDGModuleDRightTargetEq p m) (tau m a (p + 1) (dM p x)) :=
  tau.comm_d m a p x

/-- A map to the endomorphism differential graded algebra packages canonically into the chapter's
left differential graded module owner on the fixed underlying graded `R`-module `(M, dM)`. -/
def toLeftDifferentialGradedModule {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} (tau : EndomorphismDGAHom A M dM) :
    LeftDifferentialGradedModule A where
  X := M
  d := dM
  smul n m :=
    { toFun := fun a ↦ tau.map n a m
      map_add' := by
        intro a b
        simpa using congrFun (LinearMap.map_add (tau.map n) a b) m
      map_smul' := by
        intro r a
        simpa using congrFun (LinearMap.map_smul (tau.map n) r a) m }
  smul_one := tau.map_one
  smul_mul := fun i j p a b x ↦ tau.map_mul i j a b p x
  comm_d := fun i p a x ↦ tau.comm_d i a p x

/-- The packaged left differential graded module induced by an endomorphism-DGA map has the given
graded pieces. -/
@[simp] theorem toLeftDifferentialGradedModule_X {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} (tau : EndomorphismDGAHom A M dM) (n : ℤ) :
    tau.toLeftDifferentialGradedModule.X n = M n :=
  rfl

/-- The packaged left differential graded module induced by an endomorphism-DGA map has the given
differential. -/
@[simp] theorem toLeftDifferentialGradedModule_d {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} (tau : EndomorphismDGAHom A M dM) (n : ℤ) :
    tau.toLeftDifferentialGradedModule.d n = dM n :=
  rfl

/-- The packaged left differential graded module induced by an endomorphism-DGA map acts by
evaluation in each degree. -/
@[simp] theorem toLeftDifferentialGradedModule_smul {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} (tau : EndomorphismDGAHom A M dM)
    (n m : ℤ) (a : A.X n) (x : M m) :
    tau.toLeftDifferentialGradedModule.smul n m a x = tau n a m x :=
  rfl

end EndomorphismDGAHom

namespace LeftDifferentialGradedModule

/-- A left differential graded `A`-module whose underlying graded `R`-module and differential are
the fixed pair `(M, dM)`. This is the source-facing fiber of the chapter's
`LeftDifferentialGradedModule` owner that Lemma 22.13.1 compares with endomorphism-DGA maps. -/
structure WithFixedUnderlying (A : DGA) (M : ℤ → ModuleCat R)
    (dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)) where
  /-- The underlying left differential graded `A`-module. -/
  toLeftDifferentialGradedModule : LeftDifferentialGradedModule A
  /-- The graded pieces are the fixed family `M`. -/
  X_eq : toLeftDifferentialGradedModule.X = M
  /-- After transporting along `X_eq`, the differential is the fixed differential `dM`. -/
  d_eq : X_eq ▸ toLeftDifferentialGradedModule.d = dM

namespace WithFixedUnderlying

/-- The fixed-underlying fiber carries its underlying left differential graded `A`-module. -/
instance instCoeOut {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} :
    CoeOut (WithFixedUnderlying A M dM) (LeftDifferentialGradedModule A) where
  coe Nfix := Nfix.toLeftDifferentialGradedModule

/-- The left action of a fixed-underlying differential graded module, viewed directly on the fixed
graded `R`-module `(M, dM)`. -/
abbrev smul {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)}
    (Nfix : WithFixedUnderlying A M dM) (n m : ℤ) :
    A.X n →ₗ[R] M m →ₗ[R] M (n + m) := by
  rcases Nfix with ⟨N, hX, hd⟩
  cases hX
  exact N.smul n m

/-- A fixed-underlying differential graded module can be applied directly to its degreewise action
on the fixed graded pieces. -/
instance instCoeFun {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} :
    CoeFun (WithFixedUnderlying A M dM)
      (fun _ ↦ ∀ n m : ℤ, A.X n → M m → M (n + m)) where
  coe Nfix := fun n m a x ↦ Nfix.smul n m a x

/-- Coercion of a fixed-underlying differential graded module recovers its degreewise action. -/
@[simp] theorem coe_apply {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} (Nfix : WithFixedUnderlying A M dM)
    (n m : ℤ) (a : A.X n) (x : M m) :
    Nfix n m a x = Nfix.smul n m a x :=
  rfl

/-- A left differential graded module structure on the fixed `(M, dM)` determines the
corresponding map to the endomorphism differential graded algebra by currying the left action. -/
def toEndomorphismDGAHom {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)}
    (Nfix : WithFixedUnderlying A M dM) :
    EndomorphismDGAHom A M dM := by
  rcases Nfix with ⟨N, hX, hd⟩
  cases hX
  cases hd
  exact
    { map := fun m ↦
        { toFun := fun a p ↦ N.smul m p a
          map_add' := by
            intro a b
            ext p x
            simp
          map_smul' := by
            intro r a
            ext p x
            simp }
      map_one := N.smul_one
      map_mul := fun i j a b p x ↦ N.smul_mul i j p a b x
      comm_d := fun m a p x ↦ N.comm_d m p a x }

/-- Recovering the endomorphism-DGA map from a fixed-underlying differential graded module is
currying the left action in the module degree. -/
@[simp] theorem toEndomorphismDGAHom_apply {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)}
    (Nfix : WithFixedUnderlying A M dM) (n : ℤ) (a : A.X n) (m : ℤ) (x : M m) :
    Nfix.toEndomorphismDGAHom n a m x = Nfix n m a x := by
  rcases Nfix with ⟨N, hX, hd⟩
  cases hX
  cases hd
  simp [toEndomorphismDGAHom, smul]

/-- Packaging an endomorphism-DGA map into the fixed-underlying fiber preserves the underlying
left differential graded module. -/
def ofEndomorphismDGAHom {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} (tau : EndomorphismDGAHom A M dM) :
    WithFixedUnderlying A M dM :=
  ⟨tau.toLeftDifferentialGradedModule, rfl, rfl⟩

/-- Applying the fixed-underlying module built from an endomorphism-DGA map recovers the original
degreewise action. -/
@[simp] theorem ofEndomorphismDGAHom_apply {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} (tau : EndomorphismDGAHom A M dM)
    (n m : ℤ) (a : A.X n) (x : M m) :
    ofEndomorphismDGAHom tau n m a x = tau n a m x := by
  rfl

/-- Passing from endomorphism-picture action data to the fixed-underlying fiber and back is the
identity. -/
@[simp] theorem toEndomorphismDGAHom_ofEndomorphismDGAHom {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} (tau : EndomorphismDGAHom A M dM) :
    (ofEndomorphismDGAHom tau).toEndomorphismDGAHom = tau := by
  ext n p a x
  rfl

/-- Passing from a fixed-underlying left differential graded module structure to its
endomorphism-picture action data and back is the identity. -/
@[simp] theorem ofEndomorphismDGAHom_toEndomorphismDGAHom {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} (Nfix : WithFixedUnderlying A M dM) :
    ofEndomorphismDGAHom Nfix.toEndomorphismDGAHom = Nfix := by
  cases Nfix with
  | mk N hX hd =>
      cases hX
      cases hd
      rfl

/-- Lemma 22.13.1: for a fixed differential graded `R`-module `(M, d_M)` and a differential
graded `R`-algebra `A`, giving a left differential graded `A`-module structure on `(M, dM)` is
equivalent to giving a homomorphism of differential graded `R`-algebras from `A` to the
endomorphism differential graded algebra of `M`. This is the source-facing bridge from the fixed
underlying fiber of the chapter's module owner to the endomorphism-picture action data. -/
@[stacks 0FQ3]
def equivEndomorphismDGAHom
    (A : DGA) (M : ℤ → ModuleCat R)
    (dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)) :
    WithFixedUnderlying A M dM ≃ EndomorphismDGAHom A M dM where
  toFun := toEndomorphismDGAHom
  invFun := ofEndomorphismDGAHom
  left_inv := by
    intro Nfix
    cases Nfix with
    | mk N hX hd =>
        cases hX
        cases hd
        rfl
  right_inv := by
    intro tau
    cases tau
    rfl

/-- Applying the bridge of Lemma 22.13.1 is definitionally the recovery of the endomorphism-DGA
map from the fixed-underlying left differential graded module structure. -/
@[simp] theorem equivEndomorphismDGAHom_apply
    {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} (Nfix : WithFixedUnderlying A M dM) :
    equivEndomorphismDGAHom A M dM Nfix = Nfix.toEndomorphismDGAHom :=
  rfl

/-- Applying the inverse bridge of Lemma 22.13.1 is definitionally the packaging of the
endomorphism-picture action data into the fixed-underlying fiber of the chapter's module owner. -/
@[simp] theorem equivEndomorphismDGAHom_symm_apply
    {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} (tau : EndomorphismDGAHom A M dM) :
    (equivEndomorphismDGAHom A M dM).symm tau = ofEndomorphismDGAHom tau :=
  rfl

/-- Recovering the endomorphism-DGA map from a fixed-underlying left differential graded module is
injective. -/
theorem toEndomorphismDGAHom_injective {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} :
    Function.Injective
      (fun Nfix : WithFixedUnderlying A M dM ↦ Nfix.toEndomorphismDGAHom) := by
  intro Nfix₁ Nfix₂ h
  calc
    Nfix₁ = ofEndomorphismDGAHom Nfix₁.toEndomorphismDGAHom := by
      symm
      exact ofEndomorphismDGAHom_toEndomorphismDGAHom Nfix₁
    _ = ofEndomorphismDGAHom Nfix₂.toEndomorphismDGAHom := by
      simpa using congrArg ofEndomorphismDGAHom h
    _ = Nfix₂ := ofEndomorphismDGAHom_toEndomorphismDGAHom Nfix₂

/-- Two fixed-underlying left differential graded module structures are equal when their
degreewise actions agree on every homogeneous algebra element and module element. -/
@[ext] theorem ext {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)}
    {Nfix₁ Nfix₂ : WithFixedUnderlying A M dM}
    (h : ∀ (n m : ℤ) (a : A.X n) (x : M m), Nfix₁ n m a x = Nfix₂ n m a x) :
    Nfix₁ = Nfix₂ := by
  apply toEndomorphismDGAHom_injective
  ext n a p x
  rw [toEndomorphismDGAHom_apply, toEndomorphismDGAHom_apply]
  exact h n p a x

/-- The source-facing map from left differential graded module structures on `(M, dM)` to
endomorphism-DGA maps is bijective. -/
theorem toEndomorphismDGAHom_bijective {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} :
    Function.Bijective
      (fun Nfix : WithFixedUnderlying A M dM ↦ Nfix.toEndomorphismDGAHom) := by
  simpa using (equivEndomorphismDGAHom A M dM).bijective

end WithFixedUnderlying

end LeftDifferentialGradedModule

end
