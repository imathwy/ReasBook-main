import Mathlib

noncomputable section

open Algebra

universe u v w

namespace Algebra.Extension

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

/- Domain-style sampling for Definition 10.149.2:
- primary domain: commutative-ring extensions, square-zero thickenings, and the conormal/cotangent
  module attached to an extension;
- sampled owner declarations:
  `Extension.Cotangent`,
  `Extension.cotangentEquivCotangentKer`,
  `Extension.Cotangent.mk`,
  `Extension.Cotangent.map`;
- best owner abstraction: the mathlib owner `Extension.Cotangent`, i.e. the cotangent module
  `P.ker / P.ker²` attached to an extension `P : Extension R S`;
- primitive data vs. derived API:
  the primitive data are only the extension `P` and its kernel ideal `P.ker`,
  while the source-facing conormal module for a square-zero thickening is the same kernel ideal
  with its induced `S`-module structure, and its bridge to the owner `Extension.Cotangent` is
  derived API;
- source/core/bridge triage:
  `source-facing`: the universal first-order thickening predicate on an extension and the conormal
  module of a chosen universal thickening,
  `core/canonical`: `Extension.Cotangent`,
  `bridge/view`: the source-defined conormal module is the square-zero kernel ideal of the chosen
  universal thickening, regarded as an `S`-module and canonically equivalent to
  `Extension.Cotangent`, so the file should expose that thin bridge instead of a parallel owner. -/

/-- An `R`-algebra extension `P → S` is a universal first-order thickening if it has square-zero
kernel and satisfies the expected unique lifting property against square-zero quotients. -/
def IsUniversalFirstOrderThickening (P : Extension R S) : Prop :=
  P.ker ^ 2 = ⊥ ∧
    ∀ {A : Type w} [CommRing A] [Algebra R A] (I : Ideal A) (_ : I ^ 2 = ⊥)
      (f : S →ₐ[R] A ⧸ I),
        ∃! f' : P.Ring →ₐ[R] A,
          (Ideal.Quotient.mkₐ R I).comp f' = f.comp (IsScalarTower.toAlgHom R P.Ring S)

variable (P : Extension R S)

/-- The kernel of a universal first-order thickening is square-zero. -/
theorem IsUniversalFirstOrderThickening.square_zero
    (hP : P.IsUniversalFirstOrderThickening) : P.ker ^ 2 = ⊥ :=
  hP.1

/-- For a square-zero extension `P → S`, the source-facing conormal module is the kernel ideal
viewed as an `S`-module through the quotient `P.Ring ⟶ S`. -/
def ConormalModule (_ : P.ker ^ 2 = ⊥) : Type _ := P.ker

namespace ConormalModule

attribute [local simp] RingHom.mem_ker

variable {P}
variable {hsq : P.ker ^ 2 = ⊥}

/-- The identity map from the kernel ideal into the conormal module type synonym. -/
def of (x : P.ker) : ConormalModule P hsq := x

/-- The identity map from the conormal module type synonym back to the kernel ideal. -/
def val (x : ConormalModule P hsq) : P.ker := x

@[simp] lemma of_val (x : ConormalModule P hsq) : of x.val = x := rfl
@[simp] lemma val_of (x : P.ker) : ((of x : ConormalModule P hsq)).val = x := rfl

@[ext] lemma ext {x y : ConormalModule P hsq} (h : x.val = y.val) : x = y := h

instance : AddCommGroup (ConormalModule P hsq) := inferInstanceAs (AddCommGroup P.ker)

lemma mul_eq_zero_of_mem (x : P.Ring) (hx : x ∈ P.ker) (y : ConormalModule P hsq) :
    x * y.val = 0 := by
  have hxy : x * y.val ∈ P.ker ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hx y.val.2
  simpa [hsq, Ideal.mem_bot] using hxy

noncomputable instance : SMul S (ConormalModule P hsq) where
  smul r x := of ⟨P.σ r * x.val, Ideal.mul_mem_left _ _ x.val.2⟩

@[simp] lemma val_smul (r : S) (x : ConormalModule P hsq) :
    (r • x).val = ⟨P.σ r * x.val, Ideal.mul_mem_left _ _ x.val.2⟩ := rfl

noncomputable instance : Module S (ConormalModule P hsq) where
  smul_zero r := by
    apply ext
    apply Subtype.ext
    exact mul_zero (P.σ r)
  smul_add r x y := by
    apply ext
    apply Subtype.ext
    exact mul_add (P.σ r) x.val y.val
  add_smul r s x := by
    apply ext
    apply Subtype.ext
    have hzero := mul_eq_zero_of_mem
      (P.σ (r + s) - (P.σ r + P.σ s)) (by simp) x
    simpa [sub_eq_zero, sub_mul, add_mul] using hzero
  zero_smul x := by
    apply ext
    apply Subtype.ext
    exact mul_eq_zero_of_mem (P.σ 0) (by simp) x
  one_smul x := by
    apply ext
    apply Subtype.ext
    have hzero := mul_eq_zero_of_mem (P.σ 1 - 1) (by simp) x
    simpa [sub_eq_zero, sub_mul] using hzero
  mul_smul r s x := by
    apply ext
    apply Subtype.ext
    have hzero := mul_eq_zero_of_mem
      (P.σ (r * s) - P.σ r * P.σ s) (by simp) x
    simpa [sub_eq_zero, sub_mul, mul_assoc] using hzero

noncomputable instance {R₀ : Type*} [CommRing R₀] [Algebra R₀ S] :
    Module R₀ (ConormalModule P hsq) :=
  Module.compHom _ (algebraMap R₀ S)

end ConormalModule

/-- Over the base ring `R`, the raw kernel ideal and the source-facing conormal module of a
square-zero extension are canonically identified. -/
noncomputable def kerEquivConormalModuleOfSquareZeroRestrictScalars
    (hsq : P.ker ^ 2 = ⊥) : P.ker ≃ₗ[R] ConormalModule P hsq := by
  let toConormal : P.ker →ₗ[R] ConormalModule P hsq :=
    { toFun := fun x ↦ (ConormalModule.of x : ConormalModule P hsq)
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro r x
        apply ConormalModule.ext
        apply Subtype.ext
        have hk : P.σ (algebraMap R S r) - algebraMap R P.Ring r ∈ P.ker := by
          change algebraMap P.Ring S
              (P.σ (algebraMap R S r) - algebraMap R P.Ring r) = 0
          rw [map_sub, P.algebraMap_σ, IsScalarTower.algebraMap_eq R P.Ring S]
          simp
        have hzero := ConormalModule.mul_eq_zero_of_mem
          (P.σ (algebraMap R S r) - algebraMap R P.Ring r) hk
          (ConormalModule.of x : ConormalModule P hsq)
        have hEq : P.σ (algebraMap R S r) * x = (algebraMap R P.Ring r) * x := by
          simpa [sub_eq_zero, sub_mul] using hzero
        simpa [ConormalModule.val_smul, Algebra.smul_def] using hEq.symm }
  refine LinearEquiv.ofBijective toConormal ⟨?_, ?_⟩
  · intro x y h
    exact by simpa using congrArg ConormalModule.val h
  · intro x
    exact ⟨x.val, by rfl⟩

/-- For a square-zero extension `P → S`, the source-facing conormal module is canonically
identified with the owner cotangent module `P.Cotangent`. -/
noncomputable def conormalModuleEquivCotangentOfSquareZero
    (hsq : P.ker ^ 2 = ⊥) : ConormalModule P hsq ≃ₗ[S] P.Cotangent := by
  let mk : ConormalModule P hsq →ₗ[S] P.Cotangent :=
    { toFun := fun x ↦ Extension.Cotangent.mk x.val
      map_add' := by
        intro x y
        exact (Ideal.toCotangent P.ker).map_add x.val y.val
      map_smul' := by
        intro r x
        apply Extension.Cotangent.ext
        exact (Ideal.toCotangent P.ker).map_smul (P.σ r) x.val }
  refine LinearEquiv.ofBijective mk ⟨?_, ?_⟩
  · intro x y hxy
    apply ConormalModule.ext
    apply Subtype.ext
    have hmem : x.val.1 - y.val.1 ∈ P.ker ^ 2 :=
      (Extension.Cotangent.mk_eq_mk_iff_sub_mem x.val y.val).mp hxy
    exact sub_eq_zero.mp <| by
      simpa [hsq, Ideal.mem_bot] using hmem
  · intro x
    have hmk :
        Function.Surjective (Extension.Cotangent.mk : P.ker →ₗ[P.Ring] P.Cotangent) :=
      Extension.Cotangent.mk_surjective
    obtain ⟨y, rfl⟩ := hmk x
    exact ⟨ConormalModule.of y, rfl⟩

/-- The `R`-linear companion of
`conormalModuleEquivCotangentOfSquareZero`, used when comparing the conormal module to owners that
still live over the base ring. -/
noncomputable def conormalModuleEquivCotangentOfSquareZeroRestrictScalars
    (hsq : P.ker ^ 2 = ⊥) : ConormalModule P hsq ≃ₗ[R] P.Cotangent where
  toFun := conormalModuleEquivCotangentOfSquareZero P hsq
  invFun := (conormalModuleEquivCotangentOfSquareZero P hsq).symm
  left_inv := (conormalModuleEquivCotangentOfSquareZero P hsq).left_inv
  right_inv := (conormalModuleEquivCotangentOfSquareZero P hsq).right_inv
  map_add' _ _ := (conormalModuleEquivCotangentOfSquareZero P hsq).map_add _ _
  map_smul' _ _ := rfl

@[simp] theorem conormalModuleEquivCotangentOfSquareZero_apply
    (hsq : P.ker ^ 2 = ⊥) (x : ConormalModule P hsq) :
    conormalModuleEquivCotangentOfSquareZero P hsq x = Extension.Cotangent.mk x.val :=
  rfl

/-- Definition 10.149.2: if `P` is a universal first-order thickening of the `R`-algebra `S`,
then the source-defined conormal module `C_{S/R}` is the square-zero kernel of `P`, viewed as an
`S`-module, and it is canonically identified with the owner cotangent module `P.Cotangent`. -/
noncomputable def conormalModuleEquivCotangent
    (hP : P.IsUniversalFirstOrderThickening) :
    ConormalModule P hP.square_zero ≃ₗ[S] P.Cotangent :=
  conormalModuleEquivCotangentOfSquareZero P hP.square_zero

/-- The base-ring linear companion of `conormalModuleEquivCotangent`, for source-facing conormal
comparisons that are still formulated over `R`. -/
noncomputable def conormalModuleEquivCotangentRestrictScalars
    (hP : P.IsUniversalFirstOrderThickening) :
    ConormalModule P hP.square_zero ≃ₗ[R] P.Cotangent :=
  conormalModuleEquivCotangentOfSquareZeroRestrictScalars P hP.square_zero

end Algebra.Extension
