import StacksProject_2024.Chap22.Definition_22_4_1
import StacksProject_2024.Chap22.Lemma_22_13_1

universe u

section

variable {R : Type u} [CommRing R]

local notation "DGA" => CochainDGAlgebra R

namespace DifferentialGradedModule

/-- A right differential graded `A`-module whose underlying graded `R`-module and differential are
the fixed pair `(M, dM)`. This is the fixed-underlying fiber of the canonical Chapter 22 right
DG-module owner `RightDifferentialGradedModule`. -/
structure WithFixedUnderlying (A : DGA) (M : ℤ → ModuleCat R)
    (dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)) where
  /-- The underlying right differential graded `A`-module. -/
  toRightDifferentialGradedModule : RightDifferentialGradedModule A
  /-- The graded pieces are the fixed family `M`. -/
  X_eq : toRightDifferentialGradedModule.X = M
  /-- After transporting along `X_eq`, the differential is the fixed differential `dM`. -/
  d_eq : X_eq ▸ toRightDifferentialGradedModule.d = dM

namespace WithFixedUnderlying

/-- The fixed-underlying right-module fiber is the same data as the fixed-underlying left-module
fiber over `A.opposite`. -/
private def leftFixedUnderlyingEquiv (A : DGA) (M : ℤ → ModuleCat R)
    (dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)) :
    WithFixedUnderlying A M dM ≃
      LeftDifferentialGradedModule.WithFixedUnderlying A.opposite M dM where
  toFun rho :=
    ⟨rho.toRightDifferentialGradedModule, rho.X_eq, rho.d_eq⟩
  invFun rho :=
    ⟨rho.toLeftDifferentialGradedModule, rho.X_eq, rho.d_eq⟩
  left_inv := by
    intro rho
    cases rho
    rfl
  right_inv := by
    intro rho
    cases rho
    rfl

/-- The fixed-underlying fiber carries its underlying right differential graded `A`-module. -/
instance instCoeOut {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} :
    CoeOut (WithFixedUnderlying A M dM) (RightDifferentialGradedModule A) where
  coe rho := rho.toRightDifferentialGradedModule

/-- Recover the opposite-endomorphism DGA map corresponding to a fixed-underlying right
differential graded module structure. -/
def toEndomorphismDGAHom {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)}
    (rho : WithFixedUnderlying A M dM) :
    EndomorphismDGAHom A.opposite M dM :=
  LeftDifferentialGradedModule.WithFixedUnderlying.toEndomorphismDGAHom
    (leftFixedUnderlyingEquiv A M dM rho)

/-- Package an opposite-endomorphism DGA map into the fixed-underlying right differential graded
module fiber on `(M, dM)`. -/
def ofEndomorphismDGAHom {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} (tau : EndomorphismDGAHom A.opposite M dM) :
    WithFixedUnderlying A M dM :=
  (leftFixedUnderlyingEquiv A M dM).symm
    (LeftDifferentialGradedModule.WithFixedUnderlying.ofEndomorphismDGAHom tau)

/-- Lemma 22.13.3: for a fixed differential graded `R`-module `(M, dM)` and a differential
graded `R`-algebra `A`, giving a right differential graded `A`-module structure on `(M, dM)` is
equivalent to giving a homomorphism of differential graded `R`-algebras from `Aᵒᵖ` to the
endomorphism differential graded algebra of `M`. This is the source-facing bridge from the fixed
underlying fiber of the chapter's canonical right module owner to the opposite-endomorphism
action data. -/
@[stacks 0FQ5]
def ofEndomorphismDGAHom_comm_d_normalized
    (A : DGA) (M : ℤ → ModuleCat R)
    (dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)) :
    WithFixedUnderlying A M dM ≃ EndomorphismDGAHom A.opposite M dM :=
  (leftFixedUnderlyingEquiv A M dM).trans
    (LeftDifferentialGradedModule.WithFixedUnderlying.equivEndomorphismDGAHom A.opposite M dM)

/-- Compatibility alias for the source-facing equivalence of Lemma 22.13.3. -/
def equivEndomorphismDGAHom
    (A : DGA) (M : ℤ → ModuleCat R)
    (dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)) :
    WithFixedUnderlying A M dM ≃ EndomorphismDGAHom A.opposite M dM :=
  ofEndomorphismDGAHom_comm_d_normalized A M dM

/-- The degree-reordering equality from `M^(i + p)` to `M^(p + i)`. -/
theorem smulTargetEq {M : ℤ → ModuleCat R} (p i : ℤ) :
    (M (i + p) : Type u) = M (p + i) := by
  rw [add_comm]

private theorem cast_smulTargetEq {M : ℤ → ModuleCat R} (p i : ℤ) (x : M (i + p)) :
    cast (smulTargetEq p i).symm (cast (smulTargetEq p i) x) = x := by
  simp

private theorem cast_add {M : ℤ → ModuleCat R} {a b : ℤ} (h : a = b) (x y : M a) :
    cast (congrArg (fun n : ℤ ↦ (M n : Type u)) h) (x + y) =
      cast (congrArg (fun n : ℤ ↦ (M n : Type u)) h) x +
        cast (congrArg (fun n : ℤ ↦ (M n : Type u)) h) y := by
  cases h
  rfl

private theorem cast_smul {M : ℤ → ModuleCat R} {a b : ℤ} (h : a = b) (r : R) (x : M a) :
    cast (congrArg (fun n : ℤ ↦ (M n : Type u)) h) (r • x) =
      r • cast (congrArg (fun n : ℤ ↦ (M n : Type u)) h) x := by
  cases h
  rfl

/-- The right action of a fixed-underlying differential graded module, viewed directly on the
fixed graded `R`-module `(M, dM)` in the source-facing order `M^p × A^i → M^(p + i)`. -/
abbrev smul {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)}
    (rho : WithFixedUnderlying A M dM) (p i : ℤ) :
    M p →ₗ[R] A.X i →ₗ[R] M (p + i) := by
  rcases rho with ⟨rho, hX, hd⟩
  cases hX
  exact
    { toFun := fun x ↦
        { toFun := fun a ↦
            cast (smulTargetEq p i)
              ((CochainDGAlgebra.oppositeSign R i p) • rho.smul i p a x)
          map_add' := by
            intro a b
            rw [show rho.smul i p (a + b) x = rho.smul i p a x + rho.smul i p b x by
                simpa using congrFun (LinearMap.map_add (rho.smul i p) a b) x]
            rw [smul_add, cast_add (add_comm i p)]
          map_smul' := by
            intro r a
            rw [show rho.smul i p (r • a) x = r • rho.smul i p a x by
                simpa using congrFun (LinearMap.map_smul (rho.smul i p) r a) x]
            simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using
              cast_smul (add_comm i p) r
                ((CochainDGAlgebra.oppositeSign R i p) • rho.smul i p a x) }
      map_add' := by
        intro x y
        ext a
        change
          cast (smulTargetEq p i)
              ((CochainDGAlgebra.oppositeSign R i p) • rho.smul i p a (x + y)) =
            cast (smulTargetEq p i)
                ((CochainDGAlgebra.oppositeSign R i p) • rho.smul i p a x) +
              cast (smulTargetEq p i)
                ((CochainDGAlgebra.oppositeSign R i p) • rho.smul i p a y)
        rw [show rho.smul i p a (x + y) = rho.smul i p a x + rho.smul i p a y by
            exact LinearMap.map_add (rho.smul i p a) x y]
        rw [smul_add, cast_add (add_comm i p)]
      map_smul' := by
        intro r x
        ext a
        change
          cast (smulTargetEq p i)
              ((CochainDGAlgebra.oppositeSign R i p) • rho.smul i p a (r • x)) =
            r •
              cast (smulTargetEq p i)
                ((CochainDGAlgebra.oppositeSign R i p) • rho.smul i p a x)
        rw [show rho.smul i p a (r • x) = r • rho.smul i p a x by
            exact LinearMap.map_smul (rho.smul i p a) r x]
        simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using
          cast_smul (add_comm i p) r
            ((CochainDGAlgebra.oppositeSign R i p) • rho.smul i p a x) }

/-- A fixed-underlying right differential graded module can be applied directly to its degreewise
right action on the fixed graded pieces. -/
instance instCoeFun {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} :
    CoeFun (WithFixedUnderlying A M dM)
      (fun _ ↦ ∀ p i : ℤ, M p → A.X i → M (p + i)) where
  coe rho := fun p i x a ↦ rho.smul p i x a

/-- Coercion of a fixed-underlying right differential graded module recovers its degreewise right
action. -/
@[simp] theorem coe_apply {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} (rho : WithFixedUnderlying A M dM)
    (p i : ℤ) (x : M p) (a : A.X i) :
    rho p i x a = rho.smul p i x a :=
  rfl

/-- The source-facing right action can be recovered from its opposite-endomorphism DGA map. -/
@[simp] theorem smul_eq_cast_toEndomorphismDGAHom_apply {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} (rho : WithFixedUnderlying A M dM)
    (p i : ℤ) (x : M p) (a : A.X i) :
    rho.smul p i x a =
      cast (smulTargetEq p i)
        ((CochainDGAlgebra.oppositeSign R i p) • rho.toEndomorphismDGAHom i a p x) := by
  rcases rho with ⟨rho, hX, hd⟩
  cases hX
  cases hd
  delta smul toEndomorphismDGAHom leftFixedUnderlyingEquiv
    LeftDifferentialGradedModule.WithFixedUnderlying.toEndomorphismDGAHom
  rfl

/-- Recovering the opposite-endomorphism DGA map from a fixed-underlying right differential
graded module structure is applying the equivalence of Lemma 22.13.3. -/
@[simp] theorem equivEndomorphismDGAHom_apply
    {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} (rho : WithFixedUnderlying A M dM) :
    equivEndomorphismDGAHom A M dM rho = rho.toEndomorphismDGAHom :=
  rfl

/-- Applying the inverse bridge of Lemma 22.13.3 is definitionally the packaging of the
opposite-endomorphism-picture action data into the fixed-underlying fiber of the chapter's right
differential graded module owner. -/
@[simp] theorem equivEndomorphismDGAHom_symm_apply
    {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} (tau : EndomorphismDGAHom A.opposite M dM) :
    (equivEndomorphismDGAHom A M dM).symm tau = ofEndomorphismDGAHom tau :=
  rfl

/-- Evaluating the opposite-endomorphism DGA map attached to a fixed-underlying right
differential graded module structure gives the Koszul-twisted source-facing right action. -/
@[simp] theorem toEndomorphismDGAHom_apply {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)}
    (rho : WithFixedUnderlying A M dM) (i : ℤ) (a : A.X i) (p : ℤ) (x : M p) :
    rho.toEndomorphismDGAHom i a p x =
      (CochainDGAlgebra.oppositeSign R i p) •
        cast (smulTargetEq p i).symm (rho.smul p i x a) := by
  rw [smul_eq_cast_toEndomorphismDGAHom_apply]
  simp

/-- Applying the fixed-underlying right differential graded module built from an
opposite-endomorphism DGA map recovers the corresponding source-facing right action. -/
@[simp] theorem ofEndomorphismDGAHom_apply {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} (tau : EndomorphismDGAHom A.opposite M dM)
    (p i : ℤ) (x : M p) (a : A.X i) :
    ofEndomorphismDGAHom tau p i x a =
      cast (smulTargetEq p i) ((CochainDGAlgebra.oppositeSign R i p) • tau i a p x) := by
  simpa [equivEndomorphismDGAHom, toEndomorphismDGAHom, ofEndomorphismDGAHom] using
    (smul_eq_cast_toEndomorphismDGAHom_apply (ofEndomorphismDGAHom tau) p i x a)

/-- Passing from opposite-endomorphism-picture action data to the fixed-underlying fiber and back
is the identity. -/
@[simp] theorem toEndomorphismDGAHom_ofEndomorphismDGAHom {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} (tau : EndomorphismDGAHom A.opposite M dM) :
    (ofEndomorphismDGAHom tau).toEndomorphismDGAHom = tau := by
  simpa [equivEndomorphismDGAHom, toEndomorphismDGAHom, ofEndomorphismDGAHom] using
    (equivEndomorphismDGAHom A M dM).apply_symm_apply tau

/-- Passing from a fixed-underlying right differential graded module structure to its
opposite-endomorphism-picture action data and back is the identity. -/
@[simp] theorem ofEndomorphismDGAHom_toEndomorphismDGAHom {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} (rho : WithFixedUnderlying A M dM) :
    ofEndomorphismDGAHom rho.toEndomorphismDGAHom = rho := by
  simpa [equivEndomorphismDGAHom, toEndomorphismDGAHom, ofEndomorphismDGAHom] using
    (equivEndomorphismDGAHom A M dM).symm_apply_apply rho

/-- Recovering the opposite-endomorphism DGA map from a fixed-underlying right differential
graded module structure is injective. -/
theorem toEndomorphismDGAHom_injective {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} :
    Function.Injective (fun rho : WithFixedUnderlying A M dM ↦ rho.toEndomorphismDGAHom) := by
  simpa [toEndomorphismDGAHom] using (equivEndomorphismDGAHom A M dM).injective

/-- Two fixed-underlying right differential graded module structures are equal when their
degreewise right actions agree on every homogeneous module element and homogeneous algebra
element. -/
@[ext] theorem ext {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)}
    {rho₁ rho₂ : WithFixedUnderlying A M dM}
    (h : ∀ (p i : ℤ) (x : M p) (a : A.X i), rho₁ p i x a = rho₂ p i x a) :
    rho₁ = rho₂ := by
  apply toEndomorphismDGAHom_injective
  ext i a p x
  rw [toEndomorphismDGAHom_apply, toEndomorphismDGAHom_apply]
  exact congrArg
    (fun y ↦ (CochainDGAlgebra.oppositeSign R i p) • cast (smulTargetEq p i).symm y)
    (h p i x a)

/-- The source-facing map from fixed-underlying right differential graded module structures on
`(M, dM)` to opposite-endomorphism DGA maps is bijective. -/
theorem toEndomorphismDGAHom_bijective {A : DGA} {M : ℤ → ModuleCat R}
    {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)} :
    Function.Bijective (fun rho : WithFixedUnderlying A M dM ↦ rho.toEndomorphismDGAHom) := by
  simpa [toEndomorphismDGAHom] using (equivEndomorphismDGAHom A M dM).bijective

end WithFixedUnderlying

end DifferentialGradedModule

end
