import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.TFAE
import stacks_proof.stacks_project.Chap10.Definition_10_88_2
import stacks_proof.stacks_project.Chap10.Lemma_10_11_1
import stacks_proof.stacks_project.Chap10.Lemma_10_11_4
import stacks_proof.stacks_project.Chap10.Lemma_10_79_4
import stacks_proof.stacks_project.Chap10.Lemma_10_82_14
import stacks_proof.stacks_project.Chap10.Lemma_10_88_3
import stacks_proof.stacks_project.Chap10.Lemma_10_88_5

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped TensorProduct MonoidalCategory

universe u v w

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {M : Type (max v w)} [AddCommGroup M] [Module R M]

/-- Helper for Proposition 10.88.6: if `g` factors through `f`, then `g` dominates `f`. -/
lemma dominates_of_factorization
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    (hfac : ∃ h : B →ₗ[R] C, g = h.comp f) :
    g.Dominates f := by
  rcases hfac with ⟨h, rfl⟩
  intro Q
  intro _ _
  -- Tensoring preserves the displayed factorization, so the kernel inclusion is immediate.
  simpa [LinearMap.rTensor_comp] using
    LinearMap.ker_le_ker_comp (f.rTensor Q) (h.rTensor Q)

/-- Helper for Proposition 10.88.6: domination is stable under precomposition. -/
lemma dominates_comp_right
    {A A' B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup A'] [Module R A']
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C} {u : A' →ₗ[R] A}
    (hdom : g.Dominates f) :
    (g.comp u).Dominates (f.comp u) := by
  intro Q
  intro _ _
  intro x hx
  -- After rewriting the tensor of a composite, the claim reduces to the original domination.
  have hx' : (u.rTensor Q) x ∈ LinearMap.ker (f.rTensor Q) := by
    simpa [LinearMap.mem_ker, LinearMap.rTensor_comp] using hx
  have hx'' : (u.rTensor Q) x ∈ LinearMap.ker (g.rTensor Q) := hdom Q hx'
  simpa [LinearMap.mem_ker, LinearMap.rTensor_comp] using hx''

/-- Helper for Proposition 10.88.6: domination is a transitive relation. -/
lemma dominates_trans
    {A B C D : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    [AddCommGroup D] [Module R D]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C} {h : A →ₗ[R] D}
    (hhg : h.Dominates g) (hgf : g.Dominates f) :
    h.Dominates f := by
  intro Q
  intro _ _
  intro x hx
  exact hhg Q (hgf Q hx)

/-- Helper for Proposition 10.88.6: mutual domination is exactly the kernel equality needed in
clause `(1)` once a test module is fixed. -/
lemma tensor_kernel_eq_of_mutual_domination
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    (hgf : g.Dominates f) (hfg : f.Dominates g)
    (N : Type (max u v w)) [AddCommMonoid N] [Module R N] :
    LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := by
  -- Proof comment: the two domination inclusions are exactly the two inequalities needed for
  -- antisymmetry of the tensor kernels.
  exact le_antisymm (hgf N) (hfg N)

/-- Helper for Proposition 10.88.6: the bundled-`ModuleCat` version of mutual domination gives the
same tensor-kernel equality as the unbundled type-level statement. -/
lemma tensor_kernel_eq_of_mutual_domination_moduleCat
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    (hgf : g.Dominates f) (hfg : f.Dominates g)
    (N : ModuleCat.{max v w} R) :
    LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := by
  let eA : A ⊗[R] N ≃ₗ[R] A ⊗[R] ULift.{u} N :=
    TensorProduct.congr (LinearEquiv.refl R A) ULift.moduleEquiv.symm
  let eB : B ⊗[R] N ≃ₗ[R] B ⊗[R] ULift.{u} N :=
    TensorProduct.congr (LinearEquiv.refl R B) ULift.moduleEquiv.symm
  let eC : C ⊗[R] N ≃ₗ[R] C ⊗[R] ULift.{u} N :=
    TensorProduct.congr (LinearEquiv.refl R C) ULift.moduleEquiv.symm
  have hf_square :
      (f.rTensor (ULift.{u} N)).comp eA.toLinearMap =
        eB.toLinearMap.comp (f.rTensor N) := by
    -- Proof comment: changing the tensor factor from `N` to `ULift N` commutes with `f ⊗ 1`.
    ext a n
    rfl
  have hg_square :
      (g.rTensor (ULift.{u} N)).comp eA.toLinearMap =
        eC.toLinearMap.comp (g.rTensor N) := by
    -- Proof comment: the same transport square holds for `g ⊗ 1`.
    ext a n
    rfl
  have hf_apply (x : A ⊗[R] N) :
      (f.rTensor (ULift.{u} N)) (eA x) = eB ((f.rTensor N) x) := by
    -- Proof comment: evaluate the transport square on a tensor element.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp [eA, eB]
    · intro a n
      rfl
    · intro x₁ x₂ hx₁ hx₂
      simp [hx₁, hx₂]
  have hg_apply (x : A ⊗[R] N) :
      (g.rTensor (ULift.{u} N)) (eA x) = eC ((g.rTensor N) x) := by
    -- Proof comment: the analogous transport formula holds for `g`.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp [eA, eC]
    · intro a n
      rfl
    · intro x₁ x₂ hx₁ hx₂
      simp [hx₁, hx₂]
  refine le_antisymm ?_ ?_
  · intro x hx
    have hx_zero : (f.rTensor N) x = 0 := by
      simpa [LinearMap.mem_ker] using hx
    have hx_lift :
        (f.rTensor (ULift.{u} N)) (eA x) = 0 := by
      calc
        (f.rTensor (ULift.{u} N)) (eA x)
            = eB ((f.rTensor N) x) := hf_apply x
        _ = 0 := by simp [hx_zero]
    have hx_lift_mem :
        eA x ∈ LinearMap.ker (f.rTensor (ULift.{u} N)) := by
      simpa [LinearMap.mem_ker] using hx_lift
    have hy_lift_mem :
        eA x ∈ LinearMap.ker (g.rTensor (ULift.{u} N)) := hgf (ULift.{u} N) hx_lift_mem
    have hy_lift : (g.rTensor (ULift.{u} N)) (eA x) = 0 := by
      simpa [LinearMap.mem_ker] using hy_lift_mem
    have hy_zero : (g.rTensor N) x = 0 := by
      apply eC.injective
      calc
        eC ((g.rTensor N) x)
            = (g.rTensor (ULift.{u} N)) (eA x) := by
                symm
                exact hg_apply x
        _ = 0 := hy_lift
        _ = eC 0 := by simp [eC]
    simpa [LinearMap.mem_ker] using hy_zero
  · intro x hx
    have hx_zero : (g.rTensor N) x = 0 := by
      simpa [LinearMap.mem_ker] using hx
    have hx_lift :
        (g.rTensor (ULift.{u} N)) (eA x) = 0 := by
      calc
        (g.rTensor (ULift.{u} N)) (eA x)
            = eC ((g.rTensor N) x) := hg_apply x
        _ = 0 := by simp [hx_zero]
    have hx_lift_mem :
        eA x ∈ LinearMap.ker (g.rTensor (ULift.{u} N)) := by
      simpa [LinearMap.mem_ker] using hx_lift
    have hy_lift_mem :
        eA x ∈ LinearMap.ker (f.rTensor (ULift.{u} N)) := hfg (ULift.{u} N) hx_lift_mem
    have hy_lift : (f.rTensor (ULift.{u} N)) (eA x) = 0 := by
      simpa [LinearMap.mem_ker] using hy_lift_mem
    have hy_zero : (f.rTensor N) x = 0 := by
      apply eB.injective
      calc
        eB ((f.rTensor N) x)
            = (f.rTensor (ULift.{u} N)) (eA x) := by
                symm
                exact hf_apply x
        _ = 0 := hy_lift
        _ = eB 0 := by simp [eB]
    simpa [LinearMap.mem_ker] using hy_zero

/-- Helper for Proposition 10.88.6: equality of all tensor kernels implies domination. -/
lemma dominates_of_tensor_kernel_eq
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    (hker : ∀ (N : Type (max u v w)) [AddCommMonoid N] [Module R N],
      LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) :
    g.Dominates f := by
  intro N _ _
  -- Rewriting the source kernel with the assumed equality turns the goal into the identity
  -- inclusion.
  simpa [hker N]

/-- Helper for Proposition 10.88.6: the cokernel of a map between finitely presented modules is
again finitely presented. -/
lemma finitePresentation_cokernel_of_finitePresentation_map
    {A B : ModuleCat.{max v w} R}
    [Module.FinitePresentation R A] [Module.FinitePresentation R B]
    (f : A →ₗ[R] B) :
    Module.FinitePresentation R (B ⧸ LinearMap.range f) := by
  letI : Module.Finite R A := inferInstance
  have hfg : (LinearMap.range f).FG := Submodule.fg_range f
  -- The quotient map is surjective, and its kernel is exactly the finitely generated range.
  exact Module.finitePresentation_of_surjective (LinearMap.range f).mkQ
    (Submodule.mkQ_surjective _) <| by
      simpa [Submodule.ker_mkQ] using hfg

/-- Helper for Proposition 10.88.6: finite presentation transfers across a ring equivalence by
restricting scalars along that equivalence. -/
lemma module_finitePresentation_compHom_of_ringEquiv
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    {N : Type*} [AddCommGroup N] [Module B N] [Module.FinitePresentation B N] :
    let _ : Algebra A B := e.toRingHom.toAlgebra
    let _ : Module A N := Module.compHom N e.toRingHom
    let _ : IsScalarTower A B N := RestrictScalars.isScalarTower A B N
    Module.FinitePresentation A N := by
  let _ : Algebra A B := e.toRingHom.toAlgebra
  let _ : Module A N := Module.compHom N e.toRingHom
  let _ : IsScalarTower A B N := RestrictScalars.isScalarTower A B N
  have hB : Module.FinitePresentation A B := by
    -- Proof comment: via the ring equivalence, `B` is just the free rank-one `A`-module.
    exact Module.FinitePresentation.of_equiv (Module.compHom.toLinearEquiv e)
  -- Proof comment: once `B` is finitely presented over `A`, transitivity upgrades finite
  -- presentation of `N` over `B` to finite presentation over `A`.
  exact Module.FinitePresentation.trans (R := A) (S := B) (M := N)

/-- Helper for Proposition 10.88.6: reinterpret an `R`-linear map as a linear map over the lifted
scalar ring `ULift R`. -/
def LinearMap.over_ulift_ring
    {A B : Type (max u v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) :
    A →ₗ[ULift.{max v w} R] B where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    -- Proof comment: the lifted scalar action is defined by `ULift.down`, so `R`-linearity of
    -- `f` immediately gives linearity over `ULift R`.
    simpa [ULift.smul_def] using f.map_smul r.down x

/-- Helper for Proposition 10.88.6: forget the lifted scalar ring on a linear map over `ULift R`.
-/
def LinearMap.from_ulift_ring
    {A B : Type (max u v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (f : A →ₗ[ULift.{max v w} R] B) :
    A →ₗ[R] B where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    -- Proof comment: `R` acts through `ULift.up`, so linearity over `ULift R` restricts back to
    -- ordinary `R`-linearity.
    simpa using f.map_smul (ULift.up r) x

/-- Helper for Proposition 10.88.6: changing the scalar ring to `ULift R` does not change the
underlying range membership of a linear map. -/
lemma LinearMap.mem_range_over_ulift_ring_iff
    {A B : Type (max u v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (x : B) :
    x ∈ LinearMap.range (LinearMap.over_ulift_ring.{u, v, w} (R := R) f) ↔
      x ∈ LinearMap.range f := by
  constructor
  · rintro ⟨a, rfl⟩
    -- Proof comment: the lifted-scalar map has the same underlying function as `f`.
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    -- Proof comment: the same source element witnesses membership in the lifted-scalar range.
    exact ⟨a, rfl⟩

/-- Helper for Proposition 10.88.6: forgetting the lifted scalar ring after changing scalars gives
back the original linear map. -/
lemma LinearMap.from_ulift_ring_over_ulift_ring
    {A B : Type (max u v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) :
    LinearMap.from_ulift_ring.{u, v, w} (R := R)
      (LinearMap.over_ulift_ring.{u, v, w} (R := R) f) = f := by
  -- Proof comment: both maps evaluate by applying the original function `f`.
  ext x
  rfl

/-- Helper for Proposition 10.88.6: a factorization found after changing scalars to `ULift R`
descends to the original `R`-linear factorization. -/
lemma LinearMap.factorization_of_over_ulift_ring_factorization
    {A B C : Type (max u v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    {h : B →ₗ[ULift.{max v w} R] C}
    (hh : LinearMap.over_ulift_ring.{u, v, w} (R := R) g =
      h.comp (LinearMap.over_ulift_ring.{u, v, w} (R := R) f)) :
    g = (LinearMap.from_ulift_ring.{u, v, w} (R := R) h).comp f := by
  -- Proof comment: evaluate the lifted-scalar equality and forget that the factor map was
  -- `ULift R`-linear.
  ext x
  exact LinearMap.congr_fun hh x

/-- Helper for Proposition 10.88.6: finite presentation over `R` transfers to the lifted scalar
ring `ULift R`. -/
lemma module_finitePresentation_over_ulift_ring_of_finitePresentation
    {N : Type*} [AddCommGroup N] [Module R N] [Module.FinitePresentation R N] :
    Module.FinitePresentation (ULift.{max v w} R) N := by
  -- Proof comment: specialize the ring-equivalence transfer to `ULift.ringEquiv`.
  simpa using
    (module_finitePresentation_compHom_of_ringEquiv
      (e := (ULift.ringEquiv : ULift.{max v w} R ≃+* R))
      (N := N))

/-- Helper for Proposition 10.88.6: lift a linear map to `ULift`ed source and target modules in
the common ambient universe. -/
def LinearMap.ulift_map
    {A : Type*} {B : Type*}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) :
    ULift.{u} A →ₗ[R] ULift.{u} B :=
  ULift.moduleEquiv.symm.toLinearMap.comp (f.comp ULift.moduleEquiv.toLinearMap)

/-- Helper for Proposition 10.88.6: lifting source and target modules by `ULift` commutes with
composition of linear maps. -/
lemma LinearMap.ulift_map_comp
    {A : Type*} {B : Type*} {C : Type*}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (g : B →ₗ[R] C) (f : A →ₗ[R] B) :
    LinearMap.ulift_map (g.comp f) =
      (LinearMap.ulift_map g).comp (LinearMap.ulift_map f) := by
  -- Proof comment: both sides evaluate to the same lifted formula `up (g (f x.down))`.
  ext x
  rfl

/-- Helper for Proposition 10.88.6: lifting source and target modules by `ULift` does not change
injectivity of a linear map. -/
lemma LinearMap.injective_ulift_map_iff
    {A : Type*} {B : Type*}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) :
    Function.Injective (LinearMap.ulift_map (R := R) f) ↔ Function.Injective f := by
  constructor
  · intro h x y hxy
    -- Proof comment: compare the lifted images of `x` and `y`, then descend the resulting
    -- equality in `ULift A` back to the original carrier.
    have hxy_lift :
        LinearMap.ulift_map (R := R) f (ULift.up x) =
          LinearMap.ulift_map (R := R) f (ULift.up y) := by
      simpa [LinearMap.ulift_map, hxy]
    exact congrArg ULift.down (h hxy_lift)
  · intro h x y hxy
    -- Proof comment: after unpacking the `ULift` wrappers, injectivity upstairs is exactly
    -- injectivity of `f` on the original carrier.
    cases x with
    | up x =>
        cases y with
        | up y =>
            apply congrArg ULift.up
            exact h (by simpa [LinearMap.ulift_map] using congrArg ULift.down hxy)

/-- Helper for Proposition 10.88.6: transporting the range of `LinearMap.ulift_map f` back along
`ULift.moduleEquiv` recovers the original range of `f`. -/
lemma LinearMap.range_ulift_map_eq
    {A : Type*} {B : Type*}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) :
    Submodule.map (ULift.moduleEquiv : ULift.{u} B ≃ₗ[R] B).toLinearMap
      (LinearMap.range (LinearMap.ulift_map (R := R) f)) = LinearMap.range f := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨a, rfl⟩
    -- Proof comment: every element in the lifted range is literally `f a` after forgetting the
    -- `ULift` wrapper.
    exact ⟨a.down, rfl⟩
  · rintro ⟨x, rfl⟩
    -- Proof comment: conversely, the witness `ULift.up x` realizes `f x` inside the lifted
    -- range.
    refine ⟨ULift.up (f x), ?_, rfl⟩
    exact ⟨ULift.up x, rfl⟩

/-- Helper for Proposition 10.88.6: finite presentation of the cokernel is preserved after lifting
the codomain of a linear map to `ULift`. -/
lemma LinearMap.ulift_map_cokernel_finitePresentation
    {A : Type*} {B : Type*}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B)
    [Module.FinitePresentation R (B ⧸ LinearMap.range f)] :
    Module.FinitePresentation R
      (ULift.{u} B ⧸ LinearMap.range (LinearMap.ulift_map (R := R) f)) := by
  let eQ :
      (ULift.{u} B ⧸ LinearMap.range (LinearMap.ulift_map (R := R) f)) ≃ₗ[R]
        (B ⧸ LinearMap.range f) :=
    Submodule.Quotient.equiv
      (LinearMap.range (LinearMap.ulift_map (R := R) f))
      (LinearMap.range f)
      (ULift.moduleEquiv : ULift.{u} B ≃ₗ[R] B)
      (LinearMap.range_ulift_map_eq (R := R) f)
  -- Proof comment: the two cokernels differ only by the canonical `ULift` equivalence on the
  -- codomain, so finite presentation transports across that quotient equivalence.
  exact Module.FinitePresentation.of_equiv eQ.symm

/-- Helper for Proposition 10.88.6: linear-map factorization is unchanged after lifting the source
and target modules to a common universe. -/
lemma LinearMap.factorization_iff_exists_ulift_factorization
    {A : Type*} {B : Type*} {C : Type*}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C} :
    (∃ h : B →ₗ[R] C, g = h.comp f) ↔
      ∃ h : ULift.{u} B →ₗ[R] ULift.{u} C,
        LinearMap.ulift_map g = h.comp (LinearMap.ulift_map f) := by
  constructor
  · rintro ⟨h, rfl⟩
    -- Proof comment: once a factor map exists downstairs, lifting every module preserves the same
    -- factorization shape upstairs.
    refine ⟨LinearMap.ulift_map h, ?_⟩
    simpa [LinearMap.ulift_map_comp]
  · rintro ⟨h, hh⟩
    let h' : B →ₗ[R] C :=
      ULift.moduleEquiv.toLinearMap.comp (h.comp ULift.moduleEquiv.symm.toLinearMap)
    refine ⟨h', ?_⟩
    -- Proof comment: evaluate the lifted equality on `ULift.up x` and descend through
    -- `ULift.moduleEquiv`.
    ext x
    have hh_apply :
        LinearMap.ulift_map g (ULift.up x) =
          (h.comp (LinearMap.ulift_map f)) (ULift.up x) := by
      exact LinearMap.congr_fun hh (ULift.up x)
    simpa [LinearMap.ulift_map, h'] using congrArg ULift.down hh_apply

/-- Helper for Proposition 10.88.6: a displayed factorization still implies domination in the
ambient module universe `max v w`. -/
lemma LinearMap.dominates_of_displayed_factorization_mixedUniverse
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    (h : B →ₗ[R] C) (hg : ∀ x, g x = h (f x)) :
    g.Dominates f := by
  intro Q
  intro _ _
  intro x hx
  have hTensor :
      g.rTensor Q = ((h.rTensor Q).comp (f.rTensor Q) : A ⊗[R] Q →ₗ[R] C ⊗[R] Q) := by
    ext a q
    simp [LinearMap.rTensor_tmul, hg a]
  have hx0 : (f.rTensor Q) x = 0 := by
    simpa [LinearMap.mem_ker] using hx
  calc
    (g.rTensor Q) x = ((h.rTensor Q).comp (f.rTensor Q)) x := by rw [hTensor]
    _ = (h.rTensor Q) ((f.rTensor Q) x) := rfl
    _ = 0 := by rw [hx0, LinearMap.map_zero]

/-- Helper for Proposition 10.88.6: after identifying the tensor products of the `ULift`ed source
and target with the original tensor products, tensoring `LinearMap.ulift_map f` agrees with
tensoring `f`. -/
lemma LinearMap.ulift_map_rTensor_apply
    {A : Type*} {B : Type*}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B)
    (Q : Type (max u v w)) [AddCommMonoid Q] [Module R Q]
    (x : ULift.{u} A ⊗[R] Q) :
    ((ULift.moduleEquiv : ULift.{u} B ≃ₗ[R] B).rTensor Q)
        (((LinearMap.ulift_map (R := R) f).rTensor Q) x) =
      (f.rTensor Q) (((ULift.moduleEquiv : ULift.{u} A ≃ₗ[R] A).rTensor Q) x) := by
  -- Proof comment: both sides are linear in `x`, so it suffices to check the formula on pure
  -- tensors where `LinearMap.ulift_map` is definitionally `ULift.up ∘ f ∘ ULift.down`.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro a q
    rfl
  · intro x₁ x₂ hx₁ hx₂
    simp [hx₁, hx₂]

/-- Helper for Proposition 10.88.6: a same-universe kernel inclusion hypothesis on bundled
`ModuleCat` morphisms already gives the factorization conclusion from Lemma `10.88.5`. -/
lemma pushout_inr_universallyInjective_of_same_universe_kernel_le
    {A B C : ModuleCat.{max v w} R}
    (f : A ⟶ B) (g : A ⟶ C)
    (hker : ∀ N : ModuleCat.{max v w} R,
      LinearMap.ker (f.hom.rTensor N) ≤ LinearMap.ker (g.hom.rTensor N)) :
    LinearMap.UniversallyInjective.{u, max v w, max v w, max v w}
      ((pushout.inr f g).hom) := by
  intro Q _ _
  -- Proof comment: the fixed-universe pushout criterion from Lemma `10.88.4` turns the bundled
  -- tensor-kernel inclusion hypothesis directly into injectivity after tensoring with `Q`.
  exact
    (LinearMap.injective_rTensor_pushout_inr_iff (f := f.hom) (g := g.hom) (Q := Q)).2
      (by simpa using hker (ModuleCat.of.{max v w} R Q))

/-- Helper for Proposition 10.88.6: injectivity of `f ⊗ 1_R` recovers injectivity of `f` by
transporting along the right unitor isomorphisms. -/
private lemma LinearMap.injective_of_injective_rTensor_self
    {A B : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    {f : A →ₗ[R] B}
    (hf : Function.Injective (f.rTensor R)) :
    Function.Injective f := by
  intro x y hxy
  have hxy_tensor :
      (f.rTensor R) ((TensorProduct.rid R A).symm x) =
        (f.rTensor R) ((TensorProduct.rid R A).symm y) := by
    -- Proof comment: after identifying `A` with `A ⊗[R] R`, the tensorized map is just `f`.
    apply (TensorProduct.rid R B).injective
    simp [TensorProduct.rid_symm_apply, LinearMap.rTensor_tmul, hxy]
  -- Proof comment: the right unitor identifies equality of the tensorized images with equality of
  -- the original source elements.
  exact (TensorProduct.rid R A).symm.injective (hf hxy_tensor)

/-- Helper for Proposition 10.88.6: universal injectivity tested only on bundled modules in the
ambient stage universe already implies ordinary injectivity, by specializing to the monoidal unit
and transporting back through the right unitor. -/
lemma LinearMap.injective_of_universallyInjective_same_test_universe_of_small_ring
    [Small.{max v w} R]
    {A B : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    {f : A →ₗ[R] B}
    (hf : LinearMap.UniversallyInjective.{u, max v w, max v w, max v w} f) :
    Function.Injective f := by
  have hShrink :
      Function.Injective (f.rTensor (Shrink.{max v w} R)) := by
    -- Proof comment: the shrunken copy of `R` is a legitimate stage-universe test module.
    exact hf (Shrink.{max v w} R) inferInstance inferInstance
  have hRTensor : Function.Injective (f.rTensor R) := by
    -- Proof comment: `Shrink.linearEquiv` identifies tensoring with `Shrink R` and tensoring with
    -- `R`, so injectivity transports back along that equivalence.
    exact
      injective_rTensor_of_linearEquiv
        (R := R) (M := A) (M' := B) f
        (Shrink.linearEquiv R R).symm hShrink
  -- Proof comment: once tensoring with the unit object is injective, the shared unitor argument
  -- recovers injectivity of the original linear map.
  exact
    LinearMap.injective_of_injective_rTensor_self.{u, v, w}
      (R := R) (A := A) (B := B) hRTensor

/-- Helper for Proposition 10.88.6: universal injectivity tested only on bundled modules in the
ambient stage universe already implies ordinary injectivity, by specializing to the monoidal unit
and transporting back through the right unitor. -/
lemma LinearMap.injective_of_universallyInjective_same_test_universe
    [Small.{max v w} R]
    {A B : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    {f : A →ₗ[R] B}
    (hf : LinearMap.UniversallyInjective.{u, max v w, max v w, max v w} f) :
    Function.Injective f := by
  -- Proof comment: this repaired helper is the small-ring specialization already proved just
  -- above, now stated with the missing smallness hypothesis made explicit.
  have hShrink :
      Function.Injective (f.rTensor (Shrink.{max v w} R)) := by
    -- Proof comment: the shrunken copy of `R` is a legitimate stage-universe test module.
    exact hf (Shrink.{max v w} R) inferInstance inferInstance
  have hRTensor : Function.Injective (f.rTensor R) := by
    -- Proof comment: `Shrink.linearEquiv` identifies tensoring with `Shrink R` and tensoring with
    -- `R`, so injectivity transports back along that equivalence.
    exact
      injective_rTensor_of_linearEquiv
        (R := R) (M := A) (M' := B) f
        (Shrink.linearEquiv R R).symm hShrink
  -- Proof comment: reuse the tensor-unit injectivity bridge instead of repeating the same unitor
  -- argument.
  exact
    LinearMap.injective_of_injective_rTensor_self.{u, v, w}
      (R := R) (A := A) (B := B) hRTensor

/-- Helper for Proposition 10.88.6: a bundled kernel inclusion hypothesis in the ambient stage
universe remains valid after replacing the test module by its `ULift`. -/
lemma LinearMap.kernel_le_ulift_test_of_same_universe_kernel_le
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    (hker : ∀ N : ModuleCat.{max v w} R,
      LinearMap.ker (f.rTensor N) ≤ LinearMap.ker (g.rTensor N))
    (N : ModuleCat.{max v w} R) :
    LinearMap.ker (f.rTensor (ULift.{u} (N : Type (max v w)))) ≤
      LinearMap.ker (g.rTensor (ULift.{u} (N : Type (max v w)))) := by
  let eA : A ⊗[R] ULift.{u} (N : Type (max v w)) ≃ₗ[R] A ⊗[R] N :=
    TensorProduct.congr (LinearEquiv.refl R A) ULift.moduleEquiv
  let eB : B ⊗[R] ULift.{u} (N : Type (max v w)) ≃ₗ[R] B ⊗[R] N :=
    TensorProduct.congr (LinearEquiv.refl R B) ULift.moduleEquiv
  let eC : C ⊗[R] ULift.{u} (N : Type (max v w)) ≃ₗ[R] C ⊗[R] N :=
    TensorProduct.congr (LinearEquiv.refl R C) ULift.moduleEquiv
  have hf_apply (x : A ⊗[R] ULift.{u} (N : Type (max v w))) :
      (f.rTensor N) (eA x) = eB ((f.rTensor (ULift.{u} (N : Type (max v w)))) x) := by
    -- Proof comment: forgetting the `ULift` on the tensor factor commutes with tensoring by `f`.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp [eA, eB]
    · intro a n
      rfl
    · intro x₁ x₂ hx₁ hx₂
      simp [hx₁, hx₂]
  have hg_apply (x : A ⊗[R] ULift.{u} (N : Type (max v w))) :
      (g.rTensor N) (eA x) = eC ((g.rTensor (ULift.{u} (N : Type (max v w)))) x) := by
    -- Proof comment: the same transport square holds for `g ⊗ 1`.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp [eA, eC]
    · intro a n
      rfl
    · intro x₁ x₂ hx₁ hx₂
      simp [hx₁, hx₂]
  intro x hx
  have hx_zero : (f.rTensor (ULift.{u} (N : Type (max v w)))) x = 0 := by
    simpa [LinearMap.mem_ker] using hx
  have hx_base :
      (f.rTensor N) (eA x) = 0 := by
    calc
      (f.rTensor N) (eA x) = eB ((f.rTensor (ULift.{u} N)) x) := hf_apply x
      _ = 0 := by simp [hx_zero]
  have hx_base_mem :
      eA x ∈ LinearMap.ker (f.rTensor N) := by
    simpa [LinearMap.mem_ker] using hx_base
  have hy_base_mem :
      eA x ∈ LinearMap.ker (g.rTensor N) := hker N hx_base_mem
  have hy_base : (g.rTensor N) (eA x) = 0 := by
    simpa [LinearMap.mem_ker] using hy_base_mem
  have hy_zero : (g.rTensor (ULift.{u} (N : Type (max v w)))) x = 0 := by
    apply eC.injective
    calc
      eC ((g.rTensor (ULift.{u} N)) x) = (g.rTensor N) (eA x) := by
        symm
        exact hg_apply x
      _ = 0 := hy_base
      _ = eC 0 := by simp [eC]
  simpa [LinearMap.mem_ker] using hy_zero

/-- Helper for Proposition 10.88.6: if the tensor-kernel inclusion is known for every bundled
same-universe test object, then the map already dominates in the full sense. -/
lemma LinearMap.dominates_of_sameUniverseKernelLe
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    (hker : ∀ N : ModuleCat.{max v w} R,
      LinearMap.ker (f.rTensor N) ≤ LinearMap.ker (g.rTensor N)) :
    g.Dominates f := by
  -- TODO: replan route: prove domination by moving from bundled same-universe tests to the full
  -- `Dominates` quantifier through a support-level shrink/change-of-universe bridge, rather than
  -- reopening that transport boundary inside Proposition `10.88.6`.
  sorry

end
