import Mathlib
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.SymmetricExterior

open scoped TensorProduct

noncomputable section

universe u v

namespace Representation

section

-- Mathlib's `SymmetricPower R ι M` now requires the coefficient ring `R` and the index type `ι`
-- to share a universe.  Since the symmetric powers below are indexed by `Fin n : Type 0`, the base
-- field `k` is pinned to `Type 0`; every consumer of this file instantiates `k` at `Type 0`
-- (e.g. `AlgebraicClosure (ZMod p)`), so this loses no needed generality.
variable {k : Type} [Field k]
variable {V : Type v}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Helper for Exercise 9-9.1-3: a linear equivalence of carriers induces a linear equivalence on
their symmetric powers by functoriality of `SymmetricPower.map`. -/
private noncomputable def symmetricPowerLinearEquiv
    {W : Type u} [AddCommGroup W] [Module k W]
    (n : ℕ) (e : V ≃ₗ[k] W) :
    SymmetricPower k (Fin n) V ≃ₗ[k] SymmetricPower k (Fin n) W := by
  let f : SymmetricPower k (Fin n) V →ₗ[k] SymmetricPower k (Fin n) W :=
    SymmetricPower.map n e.toLinearMap
  let g : SymmetricPower k (Fin n) W →ₗ[k] SymmetricPower k (Fin n) V :=
    SymmetricPower.map n e.symm.toLinearMap
  have hleft : g.comp f = LinearMap.id := by
    -- Apply functoriality to the inverse pair `e.symm ∘ e = id`.
    calc
      g.comp f = SymmetricPower.map n (e.symm.toLinearMap.comp e.toLinearMap) := by
        rw [← SymmetricPower.map_comp n e.toLinearMap e.symm.toLinearMap]
      _ = SymmetricPower.map n LinearMap.id := by
        congr
        ext x
        exact e.left_inv x
      _ = LinearMap.id := SymmetricPower.map_id n
  have hright : f.comp g = LinearMap.id := by
    -- Apply the same argument to `e ∘ e.symm = id`.
    calc
      f.comp g = SymmetricPower.map n (e.toLinearMap.comp e.symm.toLinearMap) := by
        rw [← SymmetricPower.map_comp n e.symm.toLinearMap e.toLinearMap]
      _ = SymmetricPower.map n LinearMap.id := by
        congr
        ext x
        exact e.right_inv x
      _ = LinearMap.id := SymmetricPower.map_id n
  exact
    LinearEquiv.ofBijective f
      ⟨by
          intro x y hxy
          calc
            x = g (f x) := by
                  symm
                  exact LinearMap.congr_fun hleft x
            _ = g (f y) := by rw [hxy]
            _ = y := LinearMap.congr_fun hleft y,
        by
          intro y
          refine ⟨g y, ?_⟩
          exact LinearMap.congr_fun hright y⟩

/-- Helper for Exercise 9-9.1-3: choosing a basis of `V` reduces the target finrank comparison to
the coordinate model `ι →₀ k` on the source side. -/
private theorem finrank_symmetricPower_chooseBasisIndex_finsupp
    (n : ℕ) :
    Module.finrank k (SymmetricPower k (Fin (n + 1)) V) =
      Module.finrank k
        (SymmetricPower k (Fin (n + 1))
          (Module.Free.ChooseBasisIndex k V →₀ k)) := by
  let b := Module.Free.chooseBasis k V
  let eV : V ≃ₗ[k] Module.Free.ChooseBasisIndex k V →₀ k := b.repr
  let eSym := symmetricPowerLinearEquiv (k := k) (n := n + 1) eV
  -- Transport the symmetric power along the chosen coordinate equivalence.
  simpa [eSym] using eSym.finrank_eq

/-- Helper for Exercise 9-9.1-3: after choosing coordinates on `V`, scalar extension identifies
`K ⊗ (ι →₀ k)` with `ι →₀ K`, so the target finrank problem becomes a standard coordinate count. -/
private theorem finrank_symmetricPower_baseChange_chooseBasisIndex_finsupp
    (n : ℕ) :
    let ι := Module.Free.ChooseBasisIndex k V
    Module.finrank (AlgebraicClosure k)
      (SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
        (TensorProduct k (AlgebraicClosure k) V)) =
      Module.finrank (AlgebraicClosure k)
        (SymmetricPower (AlgebraicClosure k) (Fin (n + 1)) (ι →₀ AlgebraicClosure k)) := by
  let ι := Module.Free.ChooseBasisIndex k V
  letI : Fintype ι := Module.Free.ChooseBasisIndex.fintype k V
  letI : DecidableEq ι := Classical.decEq ι
  let b := Module.Free.chooseBasis k V
  let eV : V ≃ₗ[k] ι →₀ k := b.repr
  let eBase :
      TensorProduct k (AlgebraicClosure k) V ≃ₗ[AlgebraicClosure k]
        TensorProduct k (AlgebraicClosure k) (ι →₀ k) :=
    eV.baseChange k (AlgebraicClosure k)
  let eTensor :
      TensorProduct k (AlgebraicClosure k) (ι →₀ k) ≃ₗ[AlgebraicClosure k]
        ι →₀ AlgebraicClosure k :=
    TensorProduct.finsuppScalarRight k (AlgebraicClosure k) (AlgebraicClosure k) ι
  let eSym₁ :=
    symmetricPowerLinearEquiv
      (k := AlgebraicClosure k) (V := TensorProduct k (AlgebraicClosure k) V)
      (W := TensorProduct k (AlgebraicClosure k) (ι →₀ k)) (n := n + 1) eBase
  let eSym₂ :=
    symmetricPowerLinearEquiv
      (k := AlgebraicClosure k) (V := TensorProduct k (AlgebraicClosure k) (ι →₀ k))
      (W := ι →₀ AlgebraicClosure k) (n := n + 1) eTensor
  -- First move the base-changed carrier to coordinates, then simplify the tensor product of the
  -- coordinate module by the standard `finsuppScalarRight` equivalence.
  calc
    Module.finrank (AlgebraicClosure k)
        (SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) V)) =
      Module.finrank (AlgebraicClosure k)
        (SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) (ι →₀ k))) := by
            simpa [eSym₁] using eSym₁.finrank_eq
    _ =
      Module.finrank (AlgebraicClosure k)
        (SymmetricPower (AlgebraicClosure k) (Fin (n + 1)) (ι →₀ AlgebraicClosure k)) := by
            simpa [eSym₂] using eSym₂.finrank_eq

/-- Helper for Exercise 9-9.1-3: deleting one chosen coordinate identifies the quotient by the
line `K • single i0 1` with the smaller coordinate module on the complement of `i0`. -/
private noncomputable def finsupp_quotient_span_singleton_equiv_complement
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι] (i0 : ι) :
    ((ι →₀ K) ⧸ (K ∙ Finsupp.single i0 (1 : K))) ≃ₗ[K]
      ({i : ι // i ≠ i0} →₀ K) := by
  let u : {i : ι // i ≠ i0} → ι := Subtype.val
  let v : Unit → ι := fun _ ↦ i0
  let line : Submodule K (ι →₀ K) := K ∙ Finsupp.single i0 (1 : K)
  have huv : IsCompl (Set.range u) (Set.range v) := by
    -- The complement coordinates and the distinguished singleton coordinate partition `ι`.
    rw [isCompl_iff, disjoint_iff, codisjoint_iff]
    constructor
    · ext i
      constructor
      · intro hi
        rcases hi with ⟨hiu, hiv⟩
        rcases hiu with ⟨j, rfl⟩
        rcases hiv with ⟨_, hi'⟩
        exact j.2 hi'.symm
      · intro hi
        cases hi
    · ext i
      constructor
      · intro _
        trivial
      · intro _
        by_cases hi : i = i0
        · right
          subst hi
          exact ⟨(), rfl⟩
        · left
          exact ⟨⟨i, hi⟩, rfl⟩
  have hcompl :
      IsCompl
        (LinearMap.range (Finsupp.lmapDomain K K u))
        line := by
    -- `Finsupp.lmapDomain` realizes the complement coordinates inside the full coordinate module.
    simpa [line, v] using
      (Finsupp.isCompl_range_lmapDomain_span (R := K) (u := u) (v := v) huv)
  let eQuot :
      ((ι →₀ K) ⧸ line) ≃ₗ[K]
        LinearMap.range (Finsupp.lmapDomain K K u) :=
    Submodule.quotientEquivOfIsCompl line
      (LinearMap.range (Finsupp.lmapDomain K K u)) hcompl.symm
  let eRange :
      LinearMap.range (Finsupp.lmapDomain K K u) ≃ₗ[K] ({i : ι // i ≠ i0} →₀ K) :=
    (LinearEquiv.ofInjective (Finsupp.lmapDomain K K u)
      (show Function.Injective (Finsupp.lmapDomain K K u) from
        Finsupp.mapDomain_injective Subtype.val_injective)).symm
  -- Pass from the quotient to the embedded complement range, then forget the range embedding.
  simpa [line] using eQuot.trans eRange

/-- Helper for Exercise 9-9.1-3: degree-`n` exponent vectors on a finite index set are exactly
the multiplicity functions of elements of `Sym ι n`. -/
private noncomputable def finsupp_degree_equiv_sym
    {ι : Type u} [Fintype ι] [DecidableEq ι] (n : ℕ) :
    {d : ι →₀ ℕ // d.degree = n} ≃ Sym ι n := by
  let eDegree :
      {d : ι →₀ ℕ // d.degree = n} ≃
        {d : ι →₀ ℕ // d.sum (fun _ x ↦ x) = n} :=
    { toFun := fun d ↦ by
        refine ⟨d.1, ?_⟩
        -- Rewrite the total degree as the total coefficient sum of the exponent vector.
        simpa [Finsupp.degree_apply, Finsupp.sum] using d.2
      invFun := fun d ↦ by
        refine ⟨d.1, ?_⟩
        -- Conversely, a multiplicity function summing to `n` has total degree `n`.
        simpa [Finsupp.degree_apply, Finsupp.sum] using d.2
      left_inv := by intro d; rfl
      right_inv := by intro d; rfl }
  exact eDegree.trans (Sym.equivNatSum ι n).symm

/-- Helper for Exercise 9-9.1-3: the degree-`n` homogeneous subspace of `MvPolynomial ι K` has the
expected `multichoose` dimension. This is the polynomial-model count underlying the coordinate
proof route. -/
private theorem finrank_mvPolynomial_homogeneousSubmodule_eq_multichoose
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι] (n : ℕ) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule ι K n) =
      (Fintype.card ι).multichoose n := by
  classical
  let s : Set (ι →₀ ℕ) := {d | d.degree = n}
  letI : Fintype s :=
    Fintype.ofEquiv (Sym ι n) (finsupp_degree_equiv_sym (ι := ι) n).symm
  have hs :
      MvPolynomial.homogeneousSubmodule ι K n = MvPolynomial.restrictSupport K s := by
    -- The homogeneous submodule is exactly the submodule supported on degree-`n` monomials.
    simpa [MvPolynomial.restrictSupport, s] using
      (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (σ := ι) (R := K) n)
  have hcard :
      Fintype.card s = (Fintype.card ι).multichoose n := by
    -- Count degree-`n` exponent vectors by transporting to `Sym ι n`.
    calc
      Fintype.card s = Fintype.card (Sym ι n) := by
        exact Fintype.card_congr (finsupp_degree_equiv_sym (ι := ι) n)
      _ = (Fintype.card ι).multichoose n := by
        simpa using (Sym.card_sym_eq_multichoose ι n)
  calc
    Module.finrank K (MvPolynomial.homogeneousSubmodule ι K n) =
        Module.finrank K (MvPolynomial.restrictSupport K s) := by
          rw [hs]
    _ = Fintype.card s := by
          -- The restricted-support monomials form the canonical basis of the homogeneous piece.
          simpa [s] using
            (Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport (R := K) s))
    _ = (Fintype.card ι).multichoose n := hcard

/-- Helper for Exercise 9-9.1-3: the standard coordinate vector `x : ι →₀ K` determines the
corresponding linear form `∑ x i • X i` in `MvPolynomial ι K`. -/
noncomputable def coordinateLinearForm
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι] :
    (ι →₀ K) →ₗ[K] MvPolynomial ι K :=
  Finsupp.linearCombination K fun i ↦ (MvPolynomial.X i : MvPolynomial ι K)

/-- Helper for Exercise 9-9.1-3: the coordinate singleton basis vector maps to the corresponding
polynomial variable. -/
theorem coordinateLinearForm_single
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι] (i : ι) :
    coordinateLinearForm (K := K) (ι := ι) (Finsupp.single i (1 : K)) = MvPolynomial.X i := by
  -- The coordinate linear form specializes to the chosen basis variable on singleton vectors.
  simp [coordinateLinearForm, Finsupp.linearCombination_apply]

/-- Helper for Exercise 9-9.1-3: every coordinate linear form is homogeneous of degree `1`. -/
theorem coordinateLinearForm_mem_homogeneousSubmodule_one
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι] (x : ι →₀ K) :
    coordinateLinearForm (K := K) (ι := ι) x ∈ MvPolynomial.homogeneousSubmodule ι K 1 := by
  classical
  -- Each summand is a scalar multiple of one variable, so the whole linear form is homogeneous.
  rw [coordinateLinearForm, Finsupp.linearCombination_apply]
  refine (MvPolynomial.homogeneousSubmodule ι K 1).sum_mem ?_
  intro i hi
  exact
    Submodule.smul_mem _ _
      ((MvPolynomial.mem_homogeneousSubmodule (σ := ι) (R := K) 1 (MvPolynomial.X i)).2
        (MvPolynomial.isHomogeneous_X K i))

/-- Helper for Exercise 9-9.1-3: multiplying `n + 1` coordinate linear forms produces a degree
`n + 1` homogeneous polynomial. This is the forward tensor-level polynomial model before
descending through the symmetric quotient. -/
theorem coordinateLinearForm_prod_mem_homogeneousSubmodule
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (x : Fin (n + 1) → ι →₀ K) :
    (∏ i, coordinateLinearForm (K := K) (ι := ι) (x i)) ∈
      MvPolynomial.homogeneousSubmodule ι K (n + 1) := by
  classical
  have hprod :
      ∀ s : Finset (Fin (n + 1)),
        Finset.prod s (fun i ↦ coordinateLinearForm (K := K) (ι := ι) (x i)) ∈
          MvPolynomial.homogeneousSubmodule ι K s.card := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · -- The empty product is the constant polynomial `1`, which has degree `0`.
      simpa using
        ((MvPolynomial.mem_homogeneousSubmodule (σ := ι) (R := K) 0 (1 : MvPolynomial ι K)).2
          (MvPolynomial.isHomogeneous_one (σ := ι) (R := K)))
    · intro i s hi hs
      have hiMem :
          coordinateLinearForm (K := K) (ι := ι) (x i) ∈
            MvPolynomial.homogeneousSubmodule ι K 1 :=
        coordinateLinearForm_mem_homogeneousSubmodule_one (K := K) (ι := ι) (x i)
      have hmul :
          (coordinateLinearForm (K := K) (ι := ι) (x i) *
              Finset.prod s (fun j ↦ coordinateLinearForm (K := K) (ι := ι) (x j))) ∈
            MvPolynomial.homogeneousSubmodule ι K (1 + s.card) := by
        -- Each extra factor contributes one more distinguished degree.
        exact
          MvPolynomial.homogeneousSubmodule_mul 1 s.card <|
            Submodule.mul_mem_mul hiMem hs
      -- Reassociate the product over the inserted coordinate and simplify the degree count.
      simpa [Finset.prod_insert, Finset.card_insert_of_notMem hi, hi, Nat.add_comm] using hmul
  -- The full product over `Fin (n + 1)` is the degree-`n + 1` case of the inductive claim.
  simpa using hprod Finset.univ

/-- Helper for Exercise 9-9.1-3: multiplying `n` coordinate linear forms always produces a degree
`n` homogeneous polynomial. This is the uniform version of the tensor-level polynomial model used
for the quotient descent to symmetric powers. -/
theorem coordinateLinearForm_prod_mem_homogeneousSubmodule_fin
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (x : Fin n → ι →₀ K) :
    (∏ i, coordinateLinearForm (K := K) (ι := ι) (x i)) ∈
      MvPolynomial.homogeneousSubmodule ι K n := by
  classical
  have hprod :
      ∀ s : Finset (Fin n),
        Finset.prod s (fun i ↦ coordinateLinearForm (K := K) (ι := ι) (x i)) ∈
          MvPolynomial.homogeneousSubmodule ι K s.card := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · -- The empty product is the constant polynomial `1`, hence homogeneous of degree `0`.
      simpa using
        ((MvPolynomial.mem_homogeneousSubmodule (σ := ι) (R := K) 0 (1 : MvPolynomial ι K)).2
          (MvPolynomial.isHomogeneous_one (σ := ι) (R := K)))
    · intro i s hi hs
      have hiMem :
          coordinateLinearForm (K := K) (ι := ι) (x i) ∈
            MvPolynomial.homogeneousSubmodule ι K 1 :=
        coordinateLinearForm_mem_homogeneousSubmodule_one (K := K) (ι := ι) (x i)
      have hmul :
          (coordinateLinearForm (K := K) (ι := ι) (x i) *
              Finset.prod s (fun j ↦ coordinateLinearForm (K := K) (ι := ι) (x j))) ∈
            MvPolynomial.homogeneousSubmodule ι K (1 + s.card) := by
        -- Each extra factor contributes exactly one more degree.
        exact
          MvPolynomial.homogeneousSubmodule_mul 1 s.card <|
            Submodule.mul_mem_mul hiMem hs
      -- Reassociate the inserted factor and rewrite the degree count.
      simpa [Finset.prod_insert, Finset.card_insert_of_notMem hi, hi, Nat.add_comm] using hmul
  -- The full product over `Fin n` is the target homogeneous polynomial.
  simpa using hprod Finset.univ

/-- Helper for Exercise 9-9.1-3: the tensor-level coordinate product is multilinear before
descending to the symmetric quotient. -/
private noncomputable def coordinateLinearForm_prod_multilinear
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι] (n : ℕ) :
    MultilinearMap K (fun _ : Fin n => ι →₀ K) (MvPolynomial ι K) :=
  (MultilinearMap.mkPiAlgebra K (Fin n) (MvPolynomial ι K)).compLinearMap
    (fun _ ↦ coordinateLinearForm (K := K) (ι := ι))

/-- Helper for Exercise 9-9.1-3: the tensor-level multilinear coordinate product is just the
product of the individual coordinate linear forms. -/
theorem coordinateLinearForm_prod_multilinear_apply
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (x : Fin n → ι →₀ K) :
    coordinateLinearForm_prod_multilinear (K := K) (ι := ι) n x =
      ∏ i, coordinateLinearForm (K := K) (ι := ι) (x i) := by
  simp [coordinateLinearForm_prod_multilinear]

/-- Helper for Exercise 9-9.1-3: the tensor-level coordinate product already lands in the degree
`n` homogeneous submodule. -/
private noncomputable def coordinateLinearForm_prod_homogeneous_multilinear
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι] (n : ℕ) :
    MultilinearMap K (fun _ : Fin n => ι →₀ K)
      (MvPolynomial.homogeneousSubmodule ι K n) :=
  (coordinateLinearForm_prod_multilinear (K := K) (ι := ι) n).codRestrict
    (MvPolynomial.homogeneousSubmodule ι K n)
    (coordinateLinearForm_prod_mem_homogeneousSubmodule_fin (K := K) (ι := ι) n)

/-- Helper for Exercise 9-9.1-3: tensoring the multilinear coordinate product gives the linear
map before quotienting by symmetric relations. -/
private noncomputable def coordinateLinearForm_prod_tensor
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι] (n : ℕ) :
    PiTensorProduct K (fun _ : Fin n => ι →₀ K) →ₗ[K]
      MvPolynomial.homogeneousSubmodule ι K n :=
  PiTensorProduct.lift (coordinateLinearForm_prod_homogeneous_multilinear (K := K) (ι := ι) n)

/-- Helper for Exercise 9-9.1-3: the tensor-level coordinate product respects the permutation
relations defining symmetric powers, because the target product is commutative. -/
private theorem coordinateLinearForm_prod_tensor_wellDefined
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι] (n : ℕ)
    {x y : PiTensorProduct K (fun _ : Fin n ↦ ι →₀ K)}
    (h : addConGen (SymmetricPower.Rel K (Fin n) (ι →₀ K)) x y) :
    coordinateLinearForm_prod_tensor (K := K) (ι := ι) n x =
      coordinateLinearForm_prod_tensor (K := K) (ι := ι) n y := by
  induction h with
  | of x y h =>
      cases h with
      | perm e f =>
          apply Subtype.ext
          simpa [coordinateLinearForm_prod_tensor,
            coordinateLinearForm_prod_homogeneous_multilinear,
            coordinateLinearForm_prod_multilinear_apply] using
            ((e.prod_comp Finset.univ
              (fun i ↦ coordinateLinearForm (K := K) (ι := ι) (f i)))
              (by intro a ha; simp)).symm
  | refl =>
      rfl
  | symm _ ih =>
      exact ih.symm
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂
  | add _ _ ih₁ ih₂ =>
      simpa using congrArg₂ (· + ·) ih₁ ih₂

/-- Helper for Exercise 9-9.1-3: descending the tensor-level coordinate product to the symmetric
quotient gives the shared polynomial-model map from coordinate symmetric powers to homogeneous
polynomials. -/
private def symmetricPower_coordinate_to_homogeneousSubmodule_fun
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι] (n : ℕ) :
    SymmetricPower K (Fin n) (ι →₀ K) →
      MvPolynomial.homogeneousSubmodule ι K n :=
  Quotient.lift (coordinateLinearForm_prod_tensor (K := K) (ι := ι) n)
    (fun _ _ h ↦
      coordinateLinearForm_prod_tensor_wellDefined (K := K) (ι := ι) n h)

/-- Helper for Exercise 9-9.1-3: the descended coordinate product is additive on symmetric
powers. -/
private theorem symmetricPower_coordinate_to_homogeneousSubmodule_fun_add
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (x y : SymmetricPower K (Fin n) (ι →₀ K)) :
    symmetricPower_coordinate_to_homogeneousSubmodule_fun
        (K := K) (ι := ι) n (x + y) =
      symmetricPower_coordinate_to_homogeneousSubmodule_fun
          (K := K) (ι := ι) n x +
        symmetricPower_coordinate_to_homogeneousSubmodule_fun
          (K := K) (ι := ι) n y := by
  refine AddCon.induction_on₂ x y ?_
  intro x y
  change coordinateLinearForm_prod_tensor (K := K) (ι := ι) n (x + y) = _
  rw [LinearMap.map_add]
  rfl

/-- Helper for Exercise 9-9.1-3: the descended coordinate product is `K`-linear on symmetric
powers. -/
private theorem symmetricPower_coordinate_to_homogeneousSubmodule_fun_smul
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (a : K) (x : SymmetricPower K (Fin n) (ι →₀ K)) :
    symmetricPower_coordinate_to_homogeneousSubmodule_fun
        (K := K) (ι := ι) n (a • x) =
      a •
        symmetricPower_coordinate_to_homogeneousSubmodule_fun
          (K := K) (ι := ι) n x := by
  refine AddCon.induction_on x ?_
  intro x
  change coordinateLinearForm_prod_tensor (K := K) (ι := ι) n (a • x) = _
  rw [LinearMap.map_smul]
  rfl

/-- Helper for Exercise 9-9.1-3: the quotient-descended coordinate product is the forward
polynomial-model map from coordinate symmetric powers to degree-`n` homogeneous polynomials. -/
noncomputable def symmetricPower_coordinate_to_homogeneousSubmodule
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι] (n : ℕ) :
    SymmetricPower K (Fin n) (ι →₀ K) →ₗ[K]
      MvPolynomial.homogeneousSubmodule ι K n where
  toFun := symmetricPower_coordinate_to_homogeneousSubmodule_fun (K := K) (ι := ι) n
  map_add' :=
    symmetricPower_coordinate_to_homogeneousSubmodule_fun_add
      (K := K) (ι := ι) n
  map_smul' :=
    symmetricPower_coordinate_to_homogeneousSubmodule_fun_smul
      (K := K) (ι := ι) n

/-- Helper for Exercise 9-9.1-3: on a pure symmetric generator, the descended coordinate-product
map is still the literal product of the corresponding coordinate linear forms. -/
theorem symmetricPower_coordinate_to_homogeneousSubmodule_apply_tprod
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (x : Fin n → ι →₀ K) :
    symmetricPower_coordinate_to_homogeneousSubmodule (K := K) (ι := ι) n
        (SymmetricPower.tprod K x) =
      ⟨∏ i, coordinateLinearForm (K := K) (ι := ι) (x i),
        coordinateLinearForm_prod_mem_homogeneousSubmodule_fin
          (K := K) (ι := ι) n x⟩ := by
  apply Subtype.ext
  change
    ↑((coordinateLinearForm_prod_tensor (K := K) (ι := ι) n)
      ((PiTensorProduct.tprod K) x)) =
      ∏ i, coordinateLinearForm (K := K) (ι := ι) (x i)
  rw [coordinateLinearForm_prod_tensor, PiTensorProduct.lift.tprod,
    coordinateLinearForm_prod_homogeneous_multilinear]
  simpa [coordinateLinearForm_prod_multilinear_apply]

/-- Helper for Exercise 9-9.1-3: the product of the variables indexed by a tuple is the monomial
whose exponent vector counts the occurrences of each index. -/
private theorem prod_X_eq_monomial_sum_single
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι] :
    ∀ n : ℕ, ∀ f : Fin n → ι,
      (∏ i, (MvPolynomial.X (f i) : MvPolynomial ι K)) =
        MvPolynomial.monomial (∑ i, Finsupp.single (f i) 1) (1 : K)
  | 0, f => by
      simp
  | n + 1, f => by
      let g : Fin n → ι := fun i ↦ f i.succ
      have hsum :
          (∑ i : Fin (n + 1), Finsupp.single (f i) 1) =
            Finsupp.single (f 0) 1 + ∑ i : Fin n, Finsupp.single (g i) 1 := by
        simp [g, Fin.sum_univ_succ]
      calc
        (∏ i : Fin (n + 1), (MvPolynomial.X (f i) : MvPolynomial ι K)) =
            MvPolynomial.X (f 0) * ∏ i : Fin n, (MvPolynomial.X (g i) : MvPolynomial ι K) := by
              simp [g, Fin.prod_univ_succ]
        _ =
            MvPolynomial.X (f 0) *
              MvPolynomial.monomial (∑ i : Fin n, Finsupp.single (g i) 1) (1 : K) := by
                rw [prod_X_eq_monomial_sum_single K n g]
        _ =
            MvPolynomial.monomial
              (Finsupp.single (f 0) 1 + ∑ i : Fin n, Finsupp.single (g i) 1) (1 : K) := by
                rw [MvPolynomial.monomial_single_add]
                simp
        _ =
            MvPolynomial.monomial (∑ i : Fin (n + 1), Finsupp.single (f i) 1) (1 : K) := by
                rw [hsum]

/-- Helper for Exercise 9-9.1-3: on coordinate singleton generators, the forward polynomial model
produces the expected degree-`n` monomial. This is the source-faithful generator formula needed
for the later quotient-level polynomial equivalence. -/
theorem symmetricPower_coordinate_to_homogeneousSubmodule_apply_single_tprod
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (f : Fin n → ι) :
    symmetricPower_coordinate_to_homogeneousSubmodule (K := K) (ι := ι) n
        (SymmetricPower.tprod K fun i ↦ Finsupp.single (f i) (1 : K)) =
      ⟨MvPolynomial.monomial (∑ i, Finsupp.single (f i) 1) (1 : K),
        by
          rw [MvPolynomial.mem_homogeneousSubmodule]
          apply MvPolynomial.isHomogeneous_monomial
          rw [Finsupp.degree_eq_sum]
          calc
            ∑ x : ι, (∑ c : Fin n, Finsupp.single (f c) (1 : ℕ)) x =
                (∑ c : Fin n, Finsupp.single (f c) (1 : ℕ)).sum fun _ e ↦ e := by
                  symm
                  exact Finsupp.sum_fintype _ _ (fun _ ↦ rfl)
            _ = ∑ c : Fin n, (Finsupp.single (f c) (1 : ℕ)).sum fun _ e ↦ e := by
                  rw [Finsupp.sum_sum_index' (h0 := fun _ ↦ rfl) (h1 := fun _ _ _ ↦ rfl)]
            _ = ∑ _c : Fin n, (1 : ℕ) := by
                  refine Finset.sum_congr rfl ?_
                  intro c hc
                  simp
            _ = n := by simp⟩ := by
  apply Subtype.ext
  rw [symmetricPower_coordinate_to_homogeneousSubmodule_apply_tprod]
  simp [coordinateLinearForm_single, prod_X_eq_monomial_sum_single]

/-- Helper for Exercise 9-9.1-3: multiplying a degree-`n` homogeneous polynomial by the
distinguished variable `X i0` raises the degree by one. This is the polynomial-model version of
adjoining one copy of the distinguished line factor. -/
theorem mul_X_mem_homogeneousSubmodule_succ
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι]
    (i0 : ι) (n : ℕ) {p : MvPolynomial ι K}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule ι K n) :
    MvPolynomial.X i0 * p ∈ MvPolynomial.homogeneousSubmodule ι K (n + 1) := by
  have hX :
      MvPolynomial.X i0 ∈ MvPolynomial.homogeneousSubmodule ι K 1 := by
    exact
      (MvPolynomial.mem_homogeneousSubmodule (σ := ι) (R := K) 1 (MvPolynomial.X i0)).2
        (MvPolynomial.isHomogeneous_X K i0)
  -- One distinguished variable contributes degree `1`, so multiplication shifts the homogeneous
  -- degree from `n` to `n + 1`.
  simpa [Nat.add_comm] using
    (MvPolynomial.homogeneousSubmodule_mul 1 n <|
      Submodule.mul_mem_mul hX hp)

/-- Helper for Exercise 9-9.1-3: on the homogeneous-polynomial model, adjoining the distinguished
line factor is represented by multiplication by the distinguished variable `X i0`. -/
noncomputable def homogeneousSubmodule_mul_X
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι]
    (i0 : ι) (n : ℕ) :
    MvPolynomial.homogeneousSubmodule ι K n →ₗ[K]
      MvPolynomial.homogeneousSubmodule ι K (n + 1) where
  toFun p :=
    ⟨MvPolynomial.X i0 * p.1,
      mul_X_mem_homogeneousSubmodule_succ (K := K) (ι := ι) i0 n p.2⟩
  map_add' p q := by
    ext
    simp [mul_add]
  map_smul' a p := by
    ext
    simp [mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Exercise 9-9.1-3: multiplication by `X i0` on homogeneous polynomials is injective
because `MvPolynomial ι K` is a domain and `X i0 ≠ 0`. This is the exact injectivity input needed
for the split-model first filtration. -/
theorem homogeneousSubmodule_mul_X_injective
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι]
    (i0 : ι) (n : ℕ) :
    Function.Injective (homogeneousSubmodule_mul_X (K := K) (ι := ι) i0 n) := by
  intro p q hpq
  apply Subtype.ext
  have hval :
      MvPolynomial.X i0 * (p : MvPolynomial ι K) =
        MvPolynomial.X i0 * (q : MvPolynomial ι K) := by
    exact congrArg Subtype.val hpq
  exact mul_left_cancel₀ (MvPolynomial.X_ne_zero i0) hval

/-- Helper for Exercise 9-9.1-3: a length-`n` vector of indices determines the expected exponent
vector obtained by summing the singleton basis functions of its entries. -/
private theorem vector_toMultiset_sum_single
    {ι : Type u} [DecidableEq ι] :
    ∀ {n : ℕ} (v : List.Vector ι n),
      Finsupp.toMultiset (∑ i : Fin n, Finsupp.single (v.get i) 1) =
        ((v : Sym ι n) : Multiset ι)
  | _, v => by
      induction v using List.Vector.inductionOn with
      | nil =>
          -- In degree `0`, both the exponent vector and the multiset of entries are empty.
          simp
      | @cons n x w ih =>
          -- Passing to `x ::ᵥ w` adds one copy of `x` on both the exponent-vector side and the
          -- multiset side.
          simp [Fin.sum_univ_succ, ih, Finsupp.toMultiset_add,
            Finsupp.toMultiset_single, Sym.coe_cons]

/-- Helper for Exercise 9-9.1-3: the representative vector chosen from a multiset class in
`Sym ι n` has exponent vector equal to the `Sym.equivNatSum` image of that class. -/
private theorem vector_sum_single_eq_equivNatSum
    {ι : Type u} [DecidableEq ι] {n : ℕ} (s : Sym ι n) :
    let v : List.Vector ι n := (Sym.symEquivSym' s).out
    (∑ i : Fin n, Finsupp.single (v.get i) 1) =
      (Sym.equivNatSum ι n s : ι →₀ ℕ) := by
  classical
  dsimp
  have hv : (((Sym.symEquivSym' s).out : List.Vector ι n) : Sym ι n) = s := by
    -- `Quotient.out` is a representative of the same symmetric class.
    apply (Sym.symEquivSym' (α := ι) (n := n)).injective
    exact Quotient.out_eq _
  have hmult :
      Finsupp.toMultiset
          (∑ i : Fin n,
            Finsupp.single ((Quotient.out (Sym.symEquivSym' s)).get i) 1) =
        Finsupp.toMultiset (Sym.equivNatSum ι n s : ι →₀ ℕ) := by
    -- Both multisets are the same class `s`, just written through two different models.
    rw [vector_toMultiset_sum_single, hv]
    symm
    exact Multiset.toFinsupp_toMultiset (s : Multiset ι)
  simpa using congrArg Multiset.toFinsupp hmult

/-- Helper for Exercise 9-9.1-3: every degree-`n` monomial of the homogeneous polynomial model
comes from a coordinate symmetric pure tensor. -/
private theorem symmetricPower_coordinate_to_homogeneousSubmodule_monomial_preimage
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (d : ι →₀ ℕ) (hd : d.degree = n) :
    ∃ x,
      symmetricPower_coordinate_to_homogeneousSubmodule (K := K) (ι := ι) n x =
        ⟨MvPolynomial.monomial d (1 : K), by
          rw [MvPolynomial.mem_homogeneousSubmodule]
          exact MvPolynomial.isHomogeneous_monomial (1 : K) hd⟩ := by
  classical
  let s : Sym ι n :=
    (Sym.equivNatSum ι n).symm ⟨d, by
      simpa [Finsupp.degree_apply, Finsupp.sum] using hd⟩
  let v : List.Vector ι n := (Sym.symEquivSym' s).out
  let x : SymmetricPower K (Fin n) (ι →₀ K) :=
    SymmetricPower.tprod K fun i ↦ Finsupp.single (v.get i) (1 : K)
  refine ⟨x, ?_⟩
  have hsum : ∑ i : Fin n, Finsupp.single (v.get i) 1 = d := by
    -- The chosen vector representative has exactly the prescribed multiplicity profile `d`.
    simpa [s, v] using vector_sum_single_eq_equivNatSum (ι := ι) s
  -- The generator formula for the polynomial model now gives the required monomial.
  simpa [x, hsum] using
    symmetricPower_coordinate_to_homogeneousSubmodule_apply_single_tprod
      (K := K) (ι := ι) n (fun i ↦ v.get i)

/-- Helper for Exercise 9-9.1-3: the coordinate polynomial model already hits every homogeneous
polynomial, because it hits each monomial basis vector and the map is linear. -/
private theorem symmetricPower_coordinate_to_homogeneousSubmodule_surjective
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι]
    (n : ℕ) :
    Function.Surjective
      (symmetricPower_coordinate_to_homogeneousSubmodule (K := K) (ι := ι) n) := by
  classical
  let f := symmetricPower_coordinate_to_homogeneousSubmodule (K := K) (ι := ι) n
  intro p
  let preimageOfMonomial : (ι →₀ ℕ) → SymmetricPower K (Fin n) (ι →₀ K) := fun d ↦
    if hd : d.degree = n then
      Classical.choose
        (symmetricPower_coordinate_to_homogeneousSubmodule_monomial_preimage
          (K := K) (ι := ι) n d hd)
    else 0
  let x : SymmetricPower K (Fin n) (ι →₀ K) :=
    Finset.sum p.1.support fun d ↦
      (MvPolynomial.coeff d p.1) • preimageOfMonomial d
  refine ⟨x, ?_⟩
  apply Subtype.ext
  change ↑(f x) = p.1
  calc
    ↑(f x) =
        Finset.sum p.1.support fun d ↦
          MvPolynomial.coeff d p.1 • ↑(f (preimageOfMonomial d)) := by
            -- Expand the linear map through the explicit finite linear combination of preimages.
            simp [x, f, map_sum, map_smul]
    _ =
        Finset.sum p.1.support fun d ↦
          MvPolynomial.coeff d p.1 • MvPolynomial.monomial d (1 : K) := by
            refine Finset.sum_congr rfl ?_
            intro d hd
            have hddeg : d.degree = n := by
              -- Every support monomial of a homogeneous polynomial has the target degree.
              rw [Finsupp.degree_eq_weight_one]
              exact p.2 (by simpa [MvPolynomial.mem_support_iff] using hd)
            have hpre :
                f (preimageOfMonomial d) =
                  ⟨MvPolynomial.monomial d (1 : K), by
                    rw [MvPolynomial.mem_homogeneousSubmodule]
                    exact MvPolynomial.isHomogeneous_monomial (1 : K) hddeg⟩ := by
              simpa [preimageOfMonomial, hddeg] using
                Classical.choose_spec
                  (symmetricPower_coordinate_to_homogeneousSubmodule_monomial_preimage
                    (K := K) (ι := ι) n d hddeg)
            have hpre_val : ↑(f (preimageOfMonomial d)) = MvPolynomial.monomial d (1 : K) := by
              exact congrArg Subtype.val hpre
            rw [hpre_val]
    _ = p.1 := by
          -- Summing the coefficient-scaled monomials reconstructs the polynomial itself.
          simpa [Algebra.smul_def, MvPolynomial.C_mul_monomial] using
            p.1.support_sum_monomial_coeff.symm

/-- Helper for Exercise 9-9.1-3: multilinearity expands every pure symmetric tensor in the
coordinate module into the span of the pure tensors built from singleton basis vectors. This is
the source-faithful precursor to collapsing the tuple index set down to multiset classes. -/
private theorem symmetricPower_tprod_mem_span_singleton_generators
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (x : Fin n → ι →₀ K) :
    SymmetricPower.tprod K x ∈
      Submodule.span K
        (Set.range fun f : Fin n → ι ↦
          SymmetricPower.tprod K
            (fun i ↦ Finsupp.single (f i) (1 : K))) := by
  classical
  have hx :
      ∀ i, x i ∈ Submodule.span K (Set.range fun j : ι ↦ Finsupp.single j (1 : K)) := by
    intro i
    -- Each coordinate vector already lies in the span of the standard singleton basis.
    have hspan :
        Submodule.span K (Set.range fun j : ι ↦ Finsupp.single j (1 : K)) = ⊤ := by
      simpa [Finsupp.coe_basisSingleOne] using
        (Finsupp.basisSingleOne (R := K) (ι := ι)).span_eq
    rw [hspan]
    simp
  choose coeff supp hsubset hsupport hsum using fun i =>
    (Submodule.mem_span_iff_exists_finset_subset).1 (hx i)
  have hx_eq : x = fun i ↦ ∑ y ∈ supp i, coeff i y • y := by
    -- Rewrite every coordinate vector as a finite linear combination of singleton basis vectors.
    funext i
    symm
    exact hsum i
  rw [hx_eq]
  rw [(SymmetricPower.tprod K (ι := Fin n) (M := ι →₀ K)).map_sum_finset
    (g := fun i y ↦ coeff i y • y) (A := supp)]
  refine sum_mem ?_
  intro r hr
  let f : Fin n → ι := fun i ↦
    Classical.choose (hsubset i ((Fintype.mem_piFinset.1 hr) i))
  have hf : ∀ i, r i = Finsupp.single (f i) (1 : K) := by
    intro i
    exact (Classical.choose_spec (hsubset i ((Fintype.mem_piFinset.1 hr) i))).symm
  have hterm :
      (fun i ↦ coeff i (r i) • r i) =
        fun i ↦ coeff i (r i) • Finsupp.single (f i) (1 : K) := by
    -- Each selected summand is now a scalar multiple of a singleton basis vector.
    funext i
    rw [hf i]
  have hsmul :
      SymmetricPower.tprod K
          (fun i ↦ coeff i (r i) • Finsupp.single (f i) (1 : K)) =
        (∏ i, coeff i (r i)) •
          SymmetricPower.tprod K
            (fun i ↦ Finsupp.single (f i) (1 : K)) := by
    -- Pull all scalar factors out of the multilinear symmetric pure tensor at once.
    simpa using
      (SymmetricPower.tprod K (ι := Fin n) (M := ι →₀ K)).map_smul_univ
        (fun i ↦ coeff i (r i))
        (fun i ↦ Finsupp.single (f i) (1 : K))
  have hgen :
      SymmetricPower.tprod K
          (fun i ↦ Finsupp.single (f i) (1 : K)) ∈
        Submodule.span K
          (Set.range fun g : Fin n → ι ↦
            SymmetricPower.tprod K
              (fun i ↦ Finsupp.single (g i) (1 : K))) := by
    -- The chosen tuple of singleton basis vectors is one of the spanning generators.
    exact Submodule.subset_span ⟨f, rfl⟩
  -- After the multilinear expansion, each term is a scalar multiple of one tuple-indexed
  -- singleton generator, hence lies in the target span.
  rw [hterm, hsmul]
  exact Submodule.smul_mem _ _ hgen

/-- Helper for Exercise 9-9.1-3: the coordinate symmetric power is already spanned by the pure
singleton generators indexed by tuples `Fin n → ι`; the only remaining upper-bound step is to
identify generators that differ by permutation and collapse this tuple set to `Sym ι n`. -/
private theorem symmetricPower_span_singleton_generators_eq_top
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι]
    (n : ℕ) :
    Submodule.span K
        (Set.range fun f : Fin n → ι ↦
          SymmetricPower.tprod K
            (fun i ↦ Finsupp.single (f i) (1 : K))) =
      ⊤ := by
  rw [← SymmetricPower.span_tprod_eq_top (R := K) (ι := Fin n) (M := ι →₀ K)]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, rfl⟩
    -- Every singleton generator is already a pure tensor generator.
    exact Submodule.subset_span ⟨fun i ↦ Finsupp.single (f i) (1 : K), rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, rfl⟩
    -- The previous multilinear expansion reduces every pure tensor to the singleton-generator
    -- span.
    exact
      symmetricPower_tprod_mem_span_singleton_generators
        (K := K) (ι := ι) n x

/-- Helper for Exercise 9-9.1-3: a permutation of the entries of a length-`n` vector is realized
by an actual permutation of the index set `Fin n`. This is the bridge from `Sym.symEquivSym'` to
the permutation-invariance theorem `SymmetricPower.tprod_equiv`. -/
private theorem vector_perm_realized_by_fin_perm
    {ι : Type u} [DecidableEq ι] {n : ℕ} {v w : List.Vector ι n}
    (h : List.Perm v.1 w.1) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, w.get i = v.get (σ i) := by
  classical
  let r : Fin n → ι → Prop := fun j a ↦ a = v.get j
  have hv : List.Forall₂ r (List.finRange n) (List.ofFn v.get) := by
    -- Read the source tuple `v` against the standard index list `0, …, n - 1`.
    refine List.forall₂_of_length_eq_of_get ?_ ?_
    · simp
    · intro i _ _
      simp [r]
  have hvList : List.ofFn v.get = v.1 := by
    simpa [List.Vector.get_eq_get_toList] using (List.ofFn_get v.1)
  have hwList : List.ofFn w.get = w.1 := by
    simpa [List.Vector.get_eq_get_toList] using (List.ofFn_get w.1)
  have hlist : List.Perm (List.ofFn v.get) (List.ofFn w.get) := by
    -- Rewrite the vector permutation as a permutation of the corresponding `ofFn` lists.
    rw [hvList, hwList]
    exact h
  have hcomp :
      Relation.Comp (List.Forall₂ r) List.Perm (List.finRange n) (List.ofFn w.get) :=
    ⟨List.ofFn v.get, hv, hlist⟩
  rw [List.forall₂_comp_perm_eq_perm_comp_forall₂] at hcomp
  rcases hcomp with ⟨l, hlperm, hrel⟩
  have hlen : l.length = n := by
    simpa using hlperm.length_eq.symm
  have hnodup : l.Nodup := hlperm.nodup_iff.1 (List.nodup_finRange n)
  let σFun : Fin n → Fin n := fun i ↦
    l.get ⟨i.1, by simpa [hlen] using i.2⟩
  have hσ : ∀ i, w.get i = v.get (σFun i) := by
    intro i
    -- The transported `Forall₂` witness says the `i`th entry of `w` comes from the
    -- `σFun i`th entry of `v`.
    have hiL : i.1 < l.length := by
      simpa [hlen] using i.2
    have hrel_get := List.Forall₂.get hrel hiL (by simpa using i.2)
    simpa [r, σFun, hiL] using hrel_get
  have hσinj : Function.Injective σFun := by
    intro i j hij
    -- Since `l` is a permutation of `finRange n`, its entries are pairwise distinct.
    have hget :
        (⟨i.1, by simpa [hlen] using i.2⟩ : Fin l.length) =
          ⟨j.1, by simpa [hlen] using j.2⟩ :=
      (List.nodup_iff_injective_get.1 hnodup) hij
    exact Fin.ext (by simpa using congrArg Fin.val hget)
  have hσsurj : Function.Surjective σFun := by
    intro x
    -- Every index of `Fin n` still occurs somewhere in the permuted index list `l`.
    have hxmem : x ∈ List.finRange n := by
      simpa using (List.mem_finRange.2 x.2)
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 (hlperm.subset hxmem)
    refine ⟨⟨i.1, by simpa [hlen] using i.2⟩, ?_⟩
    simpa [σFun] using hi
  exact ⟨Equiv.ofBijective σFun ⟨hσinj, hσsurj⟩, hσ⟩

/-- Helper for Exercise 9-9.1-3: the singleton symmetric generator depends only on the
permutation class of the tuple. This is the exact quotient-compatibility needed to descend the
tuple-indexed family to `Sym ι n`. -/
private theorem symmetricPower_singleton_tprod_eq_of_vector_perm
    (K : Type) [Field K] {ι : Type u} [DecidableEq ι] {n : ℕ}
    {v w : List.Vector ι n} (h : List.Perm v.1 w.1) :
    SymmetricPower.tprod K (fun i ↦ Finsupp.single (v.get i) (1 : K)) =
      SymmetricPower.tprod K (fun i ↦ Finsupp.single (w.get i) (1 : K)) := by
  rcases vector_perm_realized_by_fin_perm (v := v) (w := w) h with ⟨σ, hσ⟩
  -- Route correction: instead of choosing one representative per symmetric class, use the
  -- actual permutation of `Fin n` and the permutation-invariance of symmetric pure tensors.
  calc
    SymmetricPower.tprod K (fun i ↦ Finsupp.single (v.get i) (1 : K)) =
        SymmetricPower.tprod K (fun i ↦ Finsupp.single (v.get (σ i)) (1 : K)) := by
          symm
          simpa using
            (SymmetricPower.tprod_equiv (R := K) (M := ι →₀ K) σ
              (fun i ↦ Finsupp.single (v.get i) (1 : K)))
    _ = SymmetricPower.tprod K (fun i ↦ Finsupp.single (w.get i) (1 : K)) := by
          -- Replace the permuted tuple entries by the target vector entries coordinatewise.
          congr
          funext i
          rw [hσ i]

/-- Helper for Exercise 9-9.1-3: descending the tuple-indexed singleton generator through
`Sym.symEquivSym'` gives the source-faithful generator family indexed by `Sym ι n`. -/
private noncomputable def symmetricPower_singleton_generator_of_sym
    (K : Type) [Field K] {ι : Type u} [DecidableEq ι] (n : ℕ) :
    Sym ι n → SymmetricPower K (Fin n) (ι →₀ K) :=
  fun s ↦
    Quotient.lift
      (fun v : List.Vector ι n ↦
        SymmetricPower.tprod K (fun i ↦ Finsupp.single (v.get i) (1 : K)))
      (fun v w h ↦
        symmetricPower_singleton_tprod_eq_of_vector_perm
          (K := K) (v := v) (w := w) h)
      (Sym.symEquivSym' s)

/-- Helper for Exercise 9-9.1-3: for a concrete tuple `f : Fin n → ι`, the descended
`Sym`-indexed generator is exactly the old tuple-indexed singleton generator. -/
private theorem symmetricPower_singleton_generator_of_sym_apply_ofFn
    (K : Type) [Field K] {ι : Type u} [DecidableEq ι] {n : ℕ} (f : Fin n → ι) :
    symmetricPower_singleton_generator_of_sym (K := K) n
        (((List.Vector.ofFn f : List.Vector ι n) : Sym ι n)) =
      SymmetricPower.tprod K (fun i ↦ Finsupp.single (f i) (1 : K)) := by
  -- Evaluate the quotient lift on the explicit tuple representative `List.Vector.ofFn f`.
  change
    Quotient.lift
      (s := List.Vector.Perm.isSetoid ι n)
      (fun v : List.Vector ι n ↦
        SymmetricPower.tprod K (fun i ↦ Finsupp.single (v.get i) (1 : K)))
      (fun v w h ↦
        symmetricPower_singleton_tprod_eq_of_vector_perm
          (K := K) (v := v) (w := w) h)
      (Quotient.mk (List.Vector.Perm.isSetoid ι n) (List.Vector.ofFn f)) =
        SymmetricPower.tprod K (fun i ↦ Finsupp.single (f i) (1 : K))
  rw [Quotient.lift_mk]
  simp

/-- Helper for Exercise 9-9.1-3: the quotient-indexed singleton generators already span the whole
coordinate symmetric power, because every tuple-indexed generator is one of them after passing to
its class in `Sym ι n`. -/
private theorem symmetricPower_span_singleton_sym_generators_eq_top
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι]
    (n : ℕ) :
    Submodule.span K
        (Set.range (symmetricPower_singleton_generator_of_sym (K := K) (ι := ι) n)) =
      ⊤ := by
  rw [eq_top_iff]
  rw [← symmetricPower_span_singleton_generators_eq_top (K := K) (ι := ι) n]
  refine Submodule.span_mono ?_
  rintro _ ⟨f, rfl⟩
  -- The tuple-indexed generator is exactly the generator attached to its symmetric class.
  exact
    ⟨((List.Vector.ofFn f : List.Vector ι n) : Sym ι n),
      symmetricPower_singleton_generator_of_sym_apply_ofFn
        (K := K) (ι := ι) f⟩

/-- Helper for Exercise 9-9.1-3: in the standard coordinate model `ι →₀ K`, the degree-`n + 1`
symmetric power has the expected multichoose dimension. -/
private theorem finrank_symmetricPower_coordinate_finsupp_eq_multichoose
    (K : Type) [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι] (n : ℕ) :
    Module.finrank K (SymmetricPower K (Fin (n + 1)) (ι →₀ K)) =
      (Fintype.card ι).multichoose (n + 1) := by
  apply le_antisymm
  · -- Route correction: the upper bound now follows from the source-faithful quotient by
    -- permutations, namely one singleton generator for each class in `Sym ι (n + 1)`.
    calc
      Module.finrank K (SymmetricPower K (Fin (n + 1)) (ι →₀ K)) ≤
          Fintype.card (Sym ι (n + 1)) := by
            exact
              finrank_le_of_span_eq_top
                (v := symmetricPower_singleton_generator_of_sym
                  (K := K) (ι := ι) (n + 1))
                (symmetricPower_span_singleton_sym_generators_eq_top
                  (K := K) (ι := ι) (n := n + 1))
      _ = (Fintype.card ι).multichoose (n + 1) := by
            simpa using (Sym.card_sym_eq_multichoose ι (n + 1))
  · -- Route correction: we now use the descended polynomial model exactly as the source suggests,
    -- but only for the already-closed surjective direction.
    calc
      (Fintype.card ι).multichoose (n + 1) =
          Module.finrank K (MvPolynomial.homogeneousSubmodule ι K (n + 1)) := by
            symm
            exact
              finrank_mvPolynomial_homogeneousSubmodule_eq_multichoose
                (K := K) (ι := ι) (n := n + 1)
      _ ≤ Module.finrank K (SymmetricPower K (Fin (n + 1)) (ι →₀ K)) := by
            exact
              LinearMap.finrank_le_finrank_of_surjective
                (f := symmetricPower_coordinate_to_homogeneousSubmodule
                  (K := K) (ι := ι) (n := n + 1))
                (symmetricPower_coordinate_to_homogeneousSubmodule_surjective
                  (K := K) (ι := ι) (n := n + 1))

/-- Helper for Exercise 9-9.1-3: every positive-degree symmetric power has the expected
`multichoose` dimension once we choose coordinates on the underlying vector space. -/
theorem finrank_symmetricPower_eq_multichoose
    (n : ℕ) :
    Module.finrank k (SymmetricPower k (Fin (n + 1)) V) =
      (Module.finrank k V).multichoose (n + 1) := by
  let ι := Module.Free.ChooseBasisIndex k V
  letI : Fintype ι := Module.Free.ChooseBasisIndex.fintype k V
  -- Choose a basis, transport to the coordinate model `ι →₀ k`, then count by multisets.
  calc
    Module.finrank k (SymmetricPower k (Fin (n + 1)) V) =
      Module.finrank k (SymmetricPower k (Fin (n + 1)) (ι →₀ k)) := by
        simpa [ι] using
          finrank_symmetricPower_chooseBasisIndex_finsupp
            (k := k) (V := V) n
    _ = (Fintype.card ι).multichoose (n + 1) := by
          simpa using
            finrank_symmetricPower_coordinate_finsupp_eq_multichoose
              (K := k) (ι := ι) n
    _ = (Module.finrank k V).multichoose (n + 1) := by
          rw [Module.finrank_eq_card_chooseBasisIndex]

/-- Helper for Exercise 9-9.1-3: scalar extension preserves the symmetric-power dimension because
both sides are counted by the same multichoose cardinal attached to a basis of `V`. -/
theorem finrank_symmetricPower_baseChange_target_eq
    (n : ℕ) :
    Module.finrank (AlgebraicClosure k)
      (SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
        (TensorProduct k (AlgebraicClosure k) V)) =
      Module.finrank k (SymmetricPower k (Fin (n + 1)) V) := by
  let ι := Module.Free.ChooseBasisIndex k V
  letI : Fintype ι := Module.Free.ChooseBasisIndex.fintype k V
  -- Route correction: the ambient base-change statement is now reduced to the coordinate model
  -- `ι →₀ k`, so the remaining gap is a pure standard-basis counting identity.
  calc
    Module.finrank (AlgebraicClosure k)
        (SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
          (TensorProduct k (AlgebraicClosure k) V)) =
      Module.finrank (AlgebraicClosure k)
        (SymmetricPower (AlgebraicClosure k) (Fin (n + 1))
          (ι →₀ AlgebraicClosure k)) := by
            simpa [ι] using
              finrank_symmetricPower_baseChange_chooseBasisIndex_finsupp
                (k := k) (V := V) n
    _ = (Fintype.card ι).multichoose (n + 1) := by
          -- The positive-degree comparison is now reduced to the pure coordinate count over the
          -- algebraic closure.
          simpa using
            finrank_symmetricPower_coordinate_finsupp_eq_multichoose
              (K := AlgebraicClosure k) (ι := ι) n
    _ =
      Module.finrank k
        (SymmetricPower k (Fin (n + 1))
          (ι →₀ k)) := by
            -- Apply the same coordinate count on the source field and read the equality backwards.
            symm
            simpa using
              finrank_symmetricPower_coordinate_finsupp_eq_multichoose
                (K := k) (ι := ι) n
    _ = Module.finrank k (SymmetricPower k (Fin (n + 1)) V) := by
          simpa [ι] using
            (finrank_symmetricPower_chooseBasisIndex_finsupp
              (k := k) (V := V) n).symm

end

end Representation
