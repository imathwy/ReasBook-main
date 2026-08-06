import Mathlib.Algebra.Homology.ShortComplex.Ab

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

universe u

-- Analogue retrieval: semantic search did not find an existing `lim^1` API for inverse sequences
-- of abelian groups in this project. The local model therefore follows the `ShortComplex Ab`
-- pattern from mathlib: `lim` is presented as a kernel and `limOne` as the quotient by the range
-- of the standard product-difference map.

/-- An inverse sequence of abelian groups indexed by `ℕ`. -/
structure InverseSequence where
  A : ℕ → Ab.{u}
  d : ∀ n : ℕ, A (n + 1) ⟶ A n

namespace InverseSequence

variable (S : InverseSequence)

/-- The product `∏ A_i` attached to an inverse sequence `S`. -/
abbrev sections : Ab.{u} :=
  AddCommGrpCat.of ((n : ℕ) → S.A n)

/-- Additivity of the standard difference map `x ↦ (x_i - d_i(x_{i + 1}))`. -/
theorem productDifferenceHom_add (x y : (n : ℕ) → S.A n) :
    (fun n ↦ (x n + y n) - S.d n (x (n + 1) + y (n + 1))) =
      fun n ↦ (x n - S.d n (x (n + 1))) + (y n - S.d n (y (n + 1))) := by
  -- Compare the two formulas coordinatewise and push `d_n` through addition.
  funext n
  rw [map_add]
  -- The remaining identity is commutative-group arithmetic.
  abel

/-- The standard map `∏ A_i → ∏ A_i` sending `x` to `(x_i - d_i(x_{i + 1}))`. -/
def productDifferenceHom : ((n : ℕ) → S.A n) →+ ((n : ℕ) → S.A n) :=
  AddMonoidHom.mk'
    (fun x n ↦ x n - S.d n (x (n + 1)))
    (S.productDifferenceHom_add)

/-- Evaluating `productDifferenceHom` gives the usual formula `x_i - d_i(x_{i + 1})`. -/
theorem productDifferenceHom_apply (x : (n : ℕ) → S.A n) (n : ℕ) :
    S.productDifferenceHom x n = x n - S.d n (x (n + 1)) := rfl

/-- The morphism `∏ A_i ⟶ ∏ A_i` associated to `productDifferenceHom`. -/
def productDifference : S.sections ⟶ S.sections :=
  AddCommGrpCat.ofHom S.productDifferenceHom

/-- Evaluating `productDifference` gives the usual formula `x_i - d_i(x_{i + 1})`. -/
theorem productDifference_apply (x : S.sections) (n : ℕ) :
    S.productDifference x n = x n - S.d n (x (n + 1)) := rfl

/-- The inverse limit `S.lim` of `S`, realized as the kernel of the standard
product-difference map `∏ A_i ⟶ ∏ A_i`.
-/
abbrev lim : Ab.{u} :=
  AddCommGrpCat.of (AddMonoidHom.ker S.productDifferenceHom)

/-- An element of the kernel defining `S.lim` is exactly a compatible family. -/
theorem mem_lim_iff (x : (n : ℕ) → S.A n) :
    x ∈ AddMonoidHom.ker S.productDifferenceHom ↔ ∀ n : ℕ, x n = S.d n (x (n + 1)) := by
  constructor
  · intro hx n
    -- Read kernel membership as vanishing of each coordinate of the difference map.
    have hx0 := congrFun (AddMonoidHom.mem_ker.mp hx) n
    simpa [productDifferenceHom_apply, sub_eq_zero] using hx0
  · intro hx
    -- Reassemble the pointwise compatibility into vanishing of the whole section.
    rw [AddMonoidHom.mem_ker]
    ext n
    simpa [productDifferenceHom_apply, sub_eq_zero] using hx n

/-- The inclusion `S.lim ⟶ ∏ A_i`. -/
def limι : S.lim ⟶ S.sections :=
  AddCommGrpCat.ofHom (AddMonoidHom.ker S.productDifferenceHom).subtype

/-- Applying `S.limι` forgets the compatibility proof. -/
theorem limι_apply (x : S.lim) (n : ℕ) :
    S.limι x n = x.1 n := rfl

/-- `lim¹` of `S`, presented as the quotient of `∏ A_i` by the range of the standard
product-difference map.
-/
abbrev limOne : Ab.{u} :=
  AddCommGrpCat.of (((n : ℕ) → S.A n) ⧸ AddMonoidHom.range S.productDifferenceHom)

/-- The quotient map `∏ A_i ⟶ lim¹ A_i`. -/
def limOneπ : S.sections ⟶ S.limOne :=
  AddCommGrpCat.ofHom (QuotientAddGroup.mk' (AddMonoidHom.range S.productDifferenceHom))

/-- The composite `∏ A_i ⟶ ∏ A_i ⟶ lim¹ A_i` is zero. -/
theorem productDifference_comp_limOneπ :
    S.productDifference ≫ S.limOneπ = 0 := by
  -- Route correction: prove the composite is zero by showing every image class is trivial in
  -- the quotient by `AddMonoidHom.range S.productDifferenceHom`.
  ext x
  dsimp [productDifference, limOneπ]
  rw [QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range]
  exact ⟨x, rfl⟩

/-- The composite `S.lim ⟶ ∏ A_i ⟶ ∏ A_i` is zero. -/
theorem limι_comp_productDifference :
    S.limι ≫ S.productDifference = 0 := by
  ext x n
  -- Elements of `S.lim` satisfy the kernel equation defining compatibility.
  exact congrFun (AddMonoidHom.mem_ker.mp x.2) n

/-- The fork `S.lim ⟶ ∏ A_i ⟶ ∏ A_i` exhibits `S.lim` as the kernel of
`S.productDifference`.
-/
abbrev limIsKernel : IsLimit (KernelFork.ofι S.limι S.limι_comp_productDifference) :=
  AddCommGrpCat.kernelIsLimit S.productDifference

/-- The cofork `∏ A_i ⟶ lim¹ A_i` exhibits `S.limOne` as the cokernel of
`S.productDifference`.
-/
abbrev limOneIsCokernel :
    IsColimit (CokernelCofork.ofπ S.limOneπ S.productDifference_comp_limOneπ) :=
  AddCommGrpCat.cokernelIsColimit S.productDifference

/-- For Definition 19.4.1 (1), in the standard exact sequence
`0 ⟶ S.lim ⟶ ∏ A_i ⟶ ∏ A_i ⟶ S.limOne ⟶ 0`, the map `S.limι` is a monomorphism.
-/
instance limι_mono : Mono S.limι := by
  rw [AddCommGrpCat.mono_iff_injective]
  intro x y h
  ext n
  exact congrFun h n

/-- The inclusion `S.lim ⟶ ∏ A_i` and the product-difference map form the
kernel-side short complex. -/
def kernelShortComplex : ShortComplex Ab.{u} :=
  ShortComplex.mk S.limι S.productDifference S.limι_comp_productDifference

/-- Definition 19.4.1 (2): in the standard exact sequence
`0 ⟶ S.lim ⟶ ∏ A_i ⟶ ∏ A_i ⟶ S.limOne ⟶ 0`, the kernel-side short complex is exact.
-/
theorem kernelShortComplex_exact :
    S.kernelShortComplex.Exact := by
  apply ShortComplex.exact_of_f_is_kernel
  exact S.limIsKernel

/-- The map `∏ A_i ⟶ ∏ A_i ⟶ lim¹ A_i` forms the quotient-side short complex. -/
def quotientShortComplex : ShortComplex Ab.{u} :=
  ShortComplex.mk S.productDifference S.limOneπ S.productDifference_comp_limOneπ

/-- For Definition 19.4.1 (3), in the standard exact sequence
`0 ⟶ S.lim ⟶ ∏ A_i ⟶ ∏ A_i ⟶ S.limOne ⟶ 0`, the quotient-side short complex is exact.
-/
theorem quotientShortComplex_exact :
    S.quotientShortComplex.Exact := by
  apply ShortComplex.exact_of_g_is_cokernel
  exact S.limOneIsCokernel

/-- For Definition 19.4.1 (4), in the standard exact sequence
`0 ⟶ S.lim ⟶ ∏ A_i ⟶ ∏ A_i ⟶ S.limOne ⟶ 0`, the quotient map `S.limOneπ` is surjective.
-/
theorem limOneπ_surjective :
    Function.Surjective S.limOneπ :=
  QuotientAddGroup.mk'_surjective _

/-- The quotient map `∏ A_i ⟶ lim¹ A_i` is an epimorphism. -/
instance limOneπ_epi : Epi S.limOneπ := by
  rw [AddCommGrpCat.epi_iff_surjective]
  exact S.limOneπ_surjective

end InverseSequence
