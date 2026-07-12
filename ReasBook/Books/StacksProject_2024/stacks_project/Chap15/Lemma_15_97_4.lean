import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.Localization.AtPrime.Basic
import StacksProject_2024.Chap15.Lemma_15_8_1
import StacksProject_2024.Chap15.Lemma_15_65_15
import StacksProject_2024.Chap15.Lemma_15_96_10
import StacksProject_2024.Chap15.Lemma_15_97_1
import StacksProject_2024.Chap15.Lemma_15_97_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open CategoryTheory
open CategoryTheory.Abelian
open scoped FittingIdeal
open scoped nonZeroDivisors

universe u

section

variable {A : Type u} [CommRing A]

open scoped EtaDeterminantalIdeal

/- Domain-style sampling:
- primary domain: determinantal ideals of cochain-complex presentation maps, localized at a prime
  and compared with powers of a nonzerodivisor;
- sampled owner declarations:
  `etaDeterminantalIdeal`,
  `etaPresentationLinearMap`,
  `fittingIdeal_eq_presentationFittingIdeal`,
  `fittingIdeal_baseChange`;
- best owner abstraction:
  `source-facing`: `etaDeterminantalIdeal`, the degree-`i` ideal attached to `(f, d^i)`;
  `core/canonical`: the intrinsic Fitting-ideal owner from `15.97.1`;
  `bridge/view`: the chosen-basis matrix of `etaPresentationLinearMap f M i`, used only to
    compare the owner with the classical maximal-minors presentation;
- primitive data vs. derived API: the primitive public data already live in `15.97.1` as the map
  `etaPresentationLinearMap f M i` and its quotient. The matrix formula here is derived bridge
  data and should not be a second owner. -/

-- Proof sketch: compute the intrinsic owner `etaDeterminantalIdeal` from the canonical quotient
-- presentation `etaPresentationQuotient f M i`, then identify that quotient with the cokernel of
-- the chosen matrix of `etaPresentationLinearMap f M i`.
/-- Helper for Lemma 15.97.4: reindexing the chosen domain and codomain bases reindexes the matrix
of a linear map in the same way. -/
private theorem linearMap_toMatrix_reindex_eq
    {ι ι' κ κ' : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    {M : Type*} {N : Type*} [AddCommMonoid M] [Module A M] [AddCommMonoid N] [Module A N]
    (bdom : Module.Basis κ A M) (bcod : Module.Basis ι A N) (eDom : κ ≃ κ')
    (eCod : ι ≃ ι') (g : M →ₗ[A] N) :
    LinearMap.toMatrix (bdom.reindex eDom) (bcod.reindex eCod) g =
      Matrix.reindex eCod eDom (LinearMap.toMatrix bdom bcod g) := by
  -- Proof comment: both matrices record the same coordinates after translating indices through the
  -- chosen reindexing equivalences.
  ext i j
  simp [LinearMap.toMatrix_apply, Matrix.reindex_apply, Module.Basis.reindex_apply]

/-- Helper for Lemma 15.97.4: reindexing the rows and columns of a matrix by equivalences does not
change the corresponding minor ideal. -/
private theorem matrix_minorIdeal_reindex_eq
    {ι : Type*} {ι' : Type*} {κ : Type*} {κ' : Type*}
    (r : ℕ) (B : Matrix ι κ A) (e₁ : ι ≃ ι') (e₂ : κ ≃ κ') :
    Matrix.minorIdeal r (Matrix.reindex e₁ e₂ B) = Matrix.minorIdeal r B := by
  refine le_antisymm ?_ ?_
  · -- Proof comment: every minor of the reindexed matrix is the same minor of the original one,
    -- read through the inverse row and column equivalences.
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨f₁, f₂⟩, rfl⟩
    simpa [Matrix.reindex_apply, Matrix.submatrix_submatrix, Function.comp_def] using
      Matrix.det_submatrix_mem_minorIdeal r B
        (f₁.trans e₁.symm.toEmbedding) (f₂.trans e₂.symm.toEmbedding)
  · -- Proof comment: the reverse inclusion is the same argument after reindexing by the inverse
    -- equivalences.
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨f₁, f₂⟩, rfl⟩
    simpa [Matrix.reindex_apply, Matrix.submatrix_submatrix, Function.comp_def] using
      Matrix.det_submatrix_mem_minorIdeal r (Matrix.reindex e₁ e₂ B)
        (f₁.trans e₁.toEmbedding) (f₂.trans e₂.toEmbedding)

/-- Helper for Lemma 15.97.4: transposing a matrix does not change its determinantal ideal. -/
private theorem matrix_minorIdeal_transpose_eq
    {ι : Type*} {κ : Type*} (r : ℕ) (B : Matrix ι κ A) :
    Matrix.minorIdeal r Bᵀ = Matrix.minorIdeal r B := by
  refine le_antisymm ?_ ?_
  · -- Proof comment: each minor of `Bᵀ` is the transpose of the corresponding minor of `B`.
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
    change (Bᵀ.submatrix e₁ e₂).det ∈ Matrix.minorIdeal r B
    have hdet : (Bᵀ.submatrix e₁ e₂).det = (B.submatrix e₂ e₁).det := by
      calc
        (Bᵀ.submatrix e₁ e₂).det = ((B.submatrix e₂ e₁)ᵀ).det := by
          rw [Matrix.transpose_submatrix]
        _ = (B.submatrix e₂ e₁).det := by
          rw [Matrix.det_transpose]
    rw [hdet]
    exact Matrix.det_submatrix_mem_minorIdeal r B e₂ e₁
  · -- Proof comment: applying the same argument to `Bᵀ` gives the reverse inclusion.
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
    change (B.submatrix e₁ e₂).det ∈ Matrix.minorIdeal r Bᵀ
    have hdet : (B.submatrix e₁ e₂).det = (Bᵀ.submatrix e₂ e₁).det := by
      calc
        (B.submatrix e₁ e₂).det = ((B.submatrix e₁ e₂)ᵀ).det := by
          rw [Matrix.det_transpose]
        _ = (Bᵀ.submatrix e₂ e₁).det := by
          rw [Matrix.transpose_submatrix]
    rw [hdet]
    exact Matrix.det_submatrix_mem_minorIdeal r Bᵀ e₂ e₁

/-- Helper for Lemma 15.97.4: a determinant built from any column-selector already belongs to the
corresponding minor ideal; repeated columns force the non-injective cases to vanish. -/
private theorem det_submatrix_mem_minorIdeal_of_colMap
    {ι : Type*} {κ : Type*} (r : ℕ) (B : Matrix ι κ A)
    (e₁ : Fin r ↪ ι) (f : Fin r → κ) :
    (B.submatrix e₁ f).det ∈ Matrix.minorIdeal r B := by
  -- Proof comment: transpose the repeated-column statement into the imported repeated-row lemma.
  have hmem :
      (Bᵀ.submatrix f e₁).det ∈ Matrix.minorIdeal r Bᵀ :=
    Matrix.det_submatrix_mem_minorIdeal_of_rowMap r Bᵀ f e₁
  have hdet : (Bᵀ.submatrix f e₁).det = (B.submatrix e₁ f).det := by
    calc
      (Bᵀ.submatrix f e₁).det = ((B.submatrix e₁ f)ᵀ).det := by
        rw [Matrix.transpose_submatrix]
      _ = (B.submatrix e₁ f).det := by
        rw [Matrix.det_transpose]
  rw [matrix_minorIdeal_transpose_eq (A := A) r B] at hmem
  rwa [hdet] at hmem

/-- Helper for Lemma 15.97.4: right-multiplying a chosen row-restricted matrix only forms an
`A`-linear combination of `r × r` minors of the ambient matrix. -/
private theorem det_submatrix_mul_right_mem_minorIdeal_of_colMap
    {ι : Type*} {κ : Type*} {α : Type*} [Fintype α]
    (r : ℕ) (B : Matrix ι κ A) (e₁ : Fin r ↪ ι) (g : α → κ)
    (T : Matrix α (Fin r) A) :
    (((B.submatrix e₁ g) * T).det) ∈ Matrix.minorIdeal r B := by
  classical
  let M : Matrix (Fin r) α A := B.submatrix e₁ g
  rw [show (((B.submatrix e₁ g) * T).det) = (M * T).det by rfl]
  -- Proof comment: expand the determinant of the product, then factor each summand into a scalar
  -- times a chosen minor of the ambient matrix.
  rw [show (M * T).det =
      ∑ p : Fin r → α, ∑ σ : Equiv.Perm (Fin r),
        ↑(Equiv.Perm.sign σ) * ∏ i, M (σ i) (p i) * T (p i) i by
      simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum,
        Fintype.piFinset_univ]
      rw [Finset.sum_comm]]
  refine (Matrix.minorIdeal r B).sum_mem fun p _ ↦ ?_
  have hp_det :
      ∑ σ : Equiv.Perm (Fin r), ↑(Equiv.Perm.sign σ) * ∏ i, M (σ i) (p i) =
        (M.submatrix id p).det := by
    symm
    exact Matrix.det_apply' (M.submatrix id p)
  have hp_factor :
      (∑ σ : Equiv.Perm (Fin r), ↑(Equiv.Perm.sign σ) * ∏ i, M (σ i) (p i) * T (p i) i) =
        (∏ i, T (p i) i) * (M.submatrix id p).det := by
    -- Proof comment: pull the coefficients from `T` out of the permutation sum and keep the
    -- determinant core as a single chosen minor.
    calc
      (∑ σ : Equiv.Perm (Fin r), ↑(Equiv.Perm.sign σ) * ∏ i, M (σ i) (p i) * T (p i) i) =
          ∑ σ : Equiv.Perm (Fin r),
            (∏ i, T (p i) i) * (↑(Equiv.Perm.sign σ) * ∏ i, M (σ i) (p i)) := by
            refine Finset.sum_congr rfl fun σ _ ↦ ?_
            simp [Finset.prod_mul_distrib, mul_assoc, mul_left_comm, mul_comm]
      _ = (∏ i, T (p i) i) * ∑ σ : Equiv.Perm (Fin r),
            ↑(Equiv.Perm.sign σ) * ∏ i, M (σ i) (p i) := by
            rw [Finset.mul_sum]
      _ = (∏ i, T (p i) i) * (M.submatrix id p).det := by
            rw [hp_det]
  rw [hp_factor]
  have hminor : (M.submatrix id p).det ∈ Matrix.minorIdeal r B := by
    -- Proof comment: the selected columns of `M` are exactly selected columns of the ambient
    -- matrix `B`.
    simpa [M, Matrix.submatrix_submatrix, Function.comp_def] using
      det_submatrix_mem_minorIdeal_of_colMap (A := A) r B e₁ (g ∘ p)
  exact Ideal.mul_mem_left _ _ hminor

/-- Helper for Lemma 15.97.4: passing to a selected submatrix can only decrease the corresponding
minor ideal. -/
private theorem matrix_minorIdeal_submatrix_le
    {ι : Type*} {ι' : Type*} {κ : Type*} {κ' : Type*}
    (r : ℕ) (B : Matrix ι κ A) (e₁ : ι' ↪ ι) (e₂ : κ' ↪ κ) :
    Matrix.minorIdeal r (B.submatrix e₁ e₂) ≤ Matrix.minorIdeal r B := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨⟨f₁, f₂⟩, rfl⟩
  -- Proof comment: each minor of a chosen submatrix is also a minor of the ambient matrix.
  simpa [Matrix.submatrix_submatrix, Function.comp_def] using
    Matrix.det_submatrix_mem_minorIdeal r B (f₁.trans e₁) (f₂.trans e₂)

/-- Helper for Lemma 15.97.4: a surjective finite relation family computes the same presentation
Fitting ideal as the full kernel-column matrix. -/
private theorem presentationFittingIdeal_eq_minorIdeal_of_surjective_fin_family
    {M : Type*} [AddCommGroup M] [Module A M]
    {n m k : ℕ} (π : (Fin n → A) →ₗ[A] M)
    (φ : (Fin m → A) →ₗ[A] LinearMap.ker π) (hφ : Function.Surjective φ) :
    presentationFittingIdeal A M k π =
      Matrix.minorIdeal (n - k)
        (fun i j ↦ ((φ (Pi.single j (1 : A)) : LinearMap.ker π) : Fin n → A) i :
          Matrix (Fin n) (Fin m) A) := by
  classical
  let K : Matrix (Fin n) (LinearMap.ker π) A := fun i x ↦ x.1 i
  let B : Matrix (Fin n) (Fin m) A := fun i j ↦ ((φ (Pi.single j (1 : A)) : LinearMap.ker π) : Fin n → A) i
  rw [presentationFittingIdeal]
  refine le_antisymm ?_ ?_
  · -- Proof comment: any chosen kernel-column minor factors through finitely many preimages under
    -- `φ`, so it is an `A`-linear combination of minors of the finite family matrix `B`.
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
    choose v hv using fun j : Fin (n - k) ↦ hφ (e₂ j)
    let T : Matrix (Fin m) (Fin (n - k)) A := fun l j ↦ v j l
    have hmatrix :
        K.submatrix e₁ e₂ = (B.submatrix e₁ (fun x : Fin m ↦ x)) * T := by
      ext i j
      have hvsum :
          v j = ∑ l : Fin m, v j l • Pi.single l (1 : A) := by
        ext l
        simp [Pi.single_apply]
      have hpreimage :
          φ (v j) = ∑ l : Fin m, v j l • φ (Pi.single l (1 : A)) := by
        calc
          φ (v j) = φ (∑ l : Fin m, v j l • Pi.single l (1 : A)) := by rw [hvsum]
          _ = ∑ l : Fin m, v j l • φ (Pi.single l (1 : A)) := by simp
      have hcoord :=
        congrArg (fun z : LinearMap.ker π ↦ ((z : Fin n → A) (e₁ i))) (hv j)
      rw [hpreimage] at hcoord
      simpa [K, B, T, Matrix.mul_apply, mul_comm, mul_left_comm, mul_assoc] using hcoord.symm
    change (K.submatrix e₁ e₂).det ∈ Matrix.minorIdeal (n - k) B
    rw [hmatrix]
    exact
      det_submatrix_mul_right_mem_minorIdeal_of_colMap
        (A := A) (r := n - k) B e₁ (fun x : Fin m ↦ x) T
  · -- Proof comment: each column of `B` is already a kernel vector of `π`, so every finite-family
    -- minor is one of the generators in the ambient kernel-column presentation ideal.
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
    let g : Fin (n - k) → LinearMap.ker π := fun j ↦ φ (Pi.single (e₂ j) (1 : A))
    have hsub : B.submatrix e₁ e₂ = K.submatrix e₁ g := by
      ext i j
      simp [B, K, g]
    change (B.submatrix e₁ e₂).det ∈ Matrix.minorIdeal (n - k) K
    rw [hsub]
    exact det_submatrix_mem_minorIdeal_of_colMap (A := A) (n - k) K e₁ g

/-- Helper for Lemma 15.97.4: in chosen bases, the coordinate vectors coming from
`etaPresentationLinearMap f M i` span the full kernel of the quotient presentation map. -/
private theorem etaPresentationQuotient_coordinate_kernel_family_surjective
    {ι : Type*} {ι1 : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ι1] [DecidableEq ι1]
    (f : A) (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ)
    (bi : Module.Basis ι A (M.X i)) (bi1 : Module.Basis ι1 A (M.X (i + 1))) :
    let πκ : ((ι ⊕ ι1) → A) →ₗ[A] etaPresentationQuotient f M i :=
      (LinearMap.range (etaPresentationLinearMap f M i)).mkQ.comp
        (bi.prod bi1).equivFun.symm.toLinearMap
    let ψκ : (ι → A) →ₗ[A] LinearMap.ker πκ :=
      LinearMap.codRestrict (LinearMap.ker πκ)
        ((bi.prod bi1).equivFun.toLinearMap.comp
          ((etaPresentationLinearMap f M i).comp bi.equivFun.symm.toLinearMap))
        (by
          intro y
          rw [LinearMap.mem_ker]
          change
            Submodule.mkQ (LinearMap.range (etaPresentationLinearMap f M i))
                (etaPresentationLinearMap f M i (bi.equivFun.symm y)) =
              0
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact ⟨bi.equivFun.symm y, rfl⟩)
    Function.Surjective ψκ := by
  intro πκ ψκ
  intro x
  change
    Submodule.mkQ (LinearMap.range (etaPresentationLinearMap f M i))
        ((bi.prod bi1).equivFun.symm x.1) =
      0 at x.2
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at x.2
  rcases x.2 with ⟨z, hz⟩
  refine ⟨bi.equivFun z, ?_⟩
  apply Subtype.ext
  -- Proof comment: after choosing a preimage in `M.X i`, the basis-coordinate relation family
  -- recovers exactly the original kernel vector.
  exact congrArg (bi.prod bi1).equivFun hz

/-- Helper for Lemma 15.97.4: the Fitting ideal of the eta-presentation quotient is the maximal
minor ideal of the chosen matrix of `(f, d^i)`. -/
private theorem etaPresentationQuotient_fittingIdeal_eq_minorIdeal_toMatrix
    (f : A) (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))] :
    let bi : Module.Basis (Module.Free.ChooseBasisIndex A (M.X i)) A (M.X i) :=
      Module.Free.chooseBasis A (M.X i)
    let bi1 : Module.Basis (Module.Free.ChooseBasisIndex A (M.X (i + 1))) A (M.X (i + 1)) :=
      Module.Free.chooseBasis A (M.X (i + 1))
    Fit[A]_(Module.finrank A (M.X (i + 1)))(etaPresentationQuotient f M i) =
      I_((Module.finrank A (M.X i)))(
        (LinearMap.toMatrix bi (bi.prod bi1) (etaPresentationLinearMap f M i))) := by
  classical
  let bi : Module.Basis (Module.Free.ChooseBasisIndex A (M.X i)) A (M.X i) :=
    Module.Free.chooseBasis A (M.X i)
  let bi1 : Module.Basis (Module.Free.ChooseBasisIndex A (M.X (i + 1))) A (M.X (i + 1)) :=
    Module.Free.chooseBasis A (M.X (i + 1))
  let ι := Module.Free.ChooseBasisIndex A (M.X i)
  let ι1 := Module.Free.ChooseBasisIndex A (M.X (i + 1))
  let r : ℕ := Fintype.card ι
  let s : ℕ := Fintype.card ι1
  let n : ℕ := Fintype.card (ι ⊕ ι1)
  let eDom : ι ≃ Fin r := Fintype.equivFin ι
  let eCod : ι ⊕ ι1 ≃ Fin n := Fintype.equivFin (ι ⊕ ι1)
  let domEquiv : (Fin n → A) ≃ₗ[A] ((ι ⊕ ι1) → A) :=
    LinearEquiv.funCongrLeft (R := A) (M := A) eCod
  let relEquiv : (Fin r → A) ≃ₗ[A] (ι → A) :=
    LinearEquiv.funCongrLeft (R := A) (M := A) eDom
  let πκ : ((ι ⊕ ι1) → A) →ₗ[A] etaPresentationQuotient f M i :=
    (LinearMap.range (etaPresentationLinearMap f M i)).mkQ.comp
      (bi.prod bi1).equivFun.symm.toLinearMap
  let π : (Fin n → A) →ₗ[A] etaPresentationQuotient f M i :=
    πκ.comp domEquiv.toLinearMap
  let coordMap : (ι → A) →ₗ[A] ((ι ⊕ ι1) → A) :=
    (bi.prod bi1).equivFun.toLinearMap.comp
      ((etaPresentationLinearMap f M i).comp bi.equivFun.symm.toLinearMap)
  let φ : (Fin r → A) →ₗ[A] LinearMap.ker π :=
    LinearMap.codRestrict (LinearMap.ker π)
      (domEquiv.symm.toLinearMap.comp (coordMap.comp relEquiv.toLinearMap))
      (by
        intro y
        rw [LinearMap.mem_ker]
        change πκ (coordMap (relEquiv y)) = 0
        change
          Submodule.mkQ (LinearMap.range (etaPresentationLinearMap f M i))
              ((etaPresentationLinearMap f M i) (bi.equivFun.symm (relEquiv y))) =
            0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact ⟨bi.equivFun.symm (relEquiv y), rfl⟩)
  have hφκ :
      Function.Surjective
        (LinearMap.codRestrict (LinearMap.ker πκ) coordMap
          (by
            intro y
            rw [LinearMap.mem_ker]
            change
              Submodule.mkQ (LinearMap.range (etaPresentationLinearMap f M i))
                  ((etaPresentationLinearMap f M i) (bi.equivFun.symm y)) =
                0
            rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
            exact ⟨bi.equivFun.symm y, rfl⟩)) := by
    simpa [πκ, coordMap] using
      etaPresentationQuotient_coordinate_kernel_family_surjective (A := A) f M i bi bi1
  have hφ : Function.Surjective φ := by
    intro x
    let xκ : LinearMap.ker πκ :=
      ⟨domEquiv x.1, by
        have hx : π x.1 = 0 := x.2
        simpa [π, domEquiv, LinearMap.comp_apply] using hx⟩
    rcases hφκ xκ with ⟨y, hy⟩
    refine ⟨relEquiv.symm y, ?_⟩
    apply Subtype.ext
    change domEquiv.symm (coordMap (relEquiv (relEquiv.symm y))) = x.1
    have hy' : coordMap y = xκ.1 := congrArg Subtype.val hy
    simpa [xκ, domEquiv] using congrArg domEquiv.symm hy'
  have hπ : Function.Surjective π := by
    intro x
    rcases Submodule.mkQ_surjective (LinearMap.range (etaPresentationLinearMap f M i)) x with
      ⟨y, rfl⟩
    refine ⟨domEquiv.symm ((bi.prod bi1).equivFun y), ?_⟩
    simp [π, πκ, domEquiv]
  have hfit :
      Fit[A]_(Module.finrank A (M.X (i + 1)))(etaPresentationQuotient f M i) =
        Matrix.minorIdeal (n - Module.finrank A (M.X (i + 1)))
          (fun i' j' ↦ ((φ (Pi.single j' (1 : A)) : LinearMap.ker π) : Fin n → A) i' :
            Matrix (Fin n) (Fin r) A) := by
    rw [fittingIdeal_eq_presentationFittingIdeal
      (R := A) (M := etaPresentationQuotient f M i)
      (k := Module.finrank A (M.X (i + 1))) π hπ]
    exact presentationFittingIdeal_eq_minorIdeal_of_surjective_fin_family
      (A := A) (M := etaPresentationQuotient f M i)
      (n := n) (m := r) (k := Module.finrank A (M.X (i + 1))) π φ hφ
  have hmatrix :
      (fun i' j' ↦ ((φ (Pi.single j' (1 : A)) : LinearMap.ker π) : Fin n → A) i' :
        Matrix (Fin n) (Fin r) A) =
        LinearMap.toMatrix (bi.reindex eDom) ((bi.prod bi1).reindex eCod)
          (etaPresentationLinearMap f M i) := by
    ext i' j'
    simp [φ, coordMap, π, πκ, domEquiv, relEquiv, LinearMap.toMatrix_apply]
  -- Route correction: the kernel-family surjectivity bridge is now isolated in
  -- `etaPresentationQuotient_coordinate_kernel_family_surjective`. The remaining work is the
  -- finite-`Fin` transport that feeds this family into
  -- `presentationFittingIdeal_eq_minorIdeal_of_surjective_fin_family` and then reindexes the
  -- resulting matrix back to `LinearMap.toMatrix bi (bi.prod bi1) (etaPresentationLinearMap f M i)`.
  -- Proof comment: compute the intrinsic Fitting ideal from the explicit finite presentation,
  -- then remove the coordinate transports on rows and columns.
  calc
    Fit[A]_(Module.finrank A (M.X (i + 1)))(etaPresentationQuotient f M i) =
        Matrix.minorIdeal (n - Module.finrank A (M.X (i + 1)))
          (LinearMap.toMatrix (bi.reindex eDom) ((bi.prod bi1).reindex eCod)
            (etaPresentationLinearMap f M i)) := by
      rw [hfit, hmatrix]
    _ = Matrix.minorIdeal r
          (LinearMap.toMatrix (bi.reindex eDom) ((bi.prod bi1).reindex eCod)
            (etaPresentationLinearMap f M i)) := by
      congr 1
      simp [n, r, s, Module.finrank_eq_card_chooseBasisIndex]
    _ = Matrix.minorIdeal r
          (Matrix.reindex eCod eDom
            (LinearMap.toMatrix bi (bi.prod bi1) (etaPresentationLinearMap f M i))) := by
      rw [linearMap_toMatrix_reindex_eq (A := A)
        (bdom := bi) (bcod := bi.prod bi1) (eDom := eDom) (eCod := eCod)
        (g := etaPresentationLinearMap f M i)]
    _ = Matrix.minorIdeal r
          (LinearMap.toMatrix bi (bi.prod bi1) (etaPresentationLinearMap f M i)) := by
      rw [matrix_minorIdeal_reindex_eq (A := A) r
        (LinearMap.toMatrix bi (bi.prod bi1) (etaPresentationLinearMap f M i))
        eCod eDom]
    _ = I_((Module.finrank A (M.X i)))
          (LinearMap.toMatrix bi (bi.prod bi1) (etaPresentationLinearMap f M i)) := by
      simp [r, Module.finrank_eq_card_chooseBasisIndex]

/-- The intrinsic determinantal ideal `I_i(M^\bullet, f)` is computed from the maximal minors of
the chosen matrix of `(f, d^i)`. -/
theorem etaDeterminantalIdeal_def
    (f : A) (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))] :
    let bi := Module.Free.chooseBasis A (M.X i)
    let bi1 := Module.Free.chooseBasis A (M.X (i + 1))
    I[f]_(i)(M) =
      I_((Module.finrank A (M.X i)))(
        (LinearMap.toMatrix bi (bi.prod bi1) (etaPresentationLinearMap f M i))) :=
  by
  -- Proof comment: rewrite the intrinsic owner `I[f]_(i)(M)` as the Fitting ideal of the
  -- quotient presented by `(f, d^i)`, then compute that presentation ideal from the chosen matrix.
  simpa [etaDeterminantalIdeal] using
    etaPresentationQuotient_fittingIdeal_eq_minorIdeal_toMatrix (A := A) f M i

local instance etaDeterminantalIdealTermModuleFree
    {M : CochainComplex (ModuleCat.{u} A) ℤ}
    [hMff : CategoryTheory.CochainComplex.IsTermwiseFiniteFree M] (j : ℤ) :
    Module.Free A (M.X j) :=
  inferInstance

local instance etaDeterminantalIdealTermModuleFinite
    {M : CochainComplex (ModuleCat.{u} A) ℤ}
    [hMff : CategoryTheory.CochainComplex.IsTermwiseFiniteFree M] (j : ℤ) :
    Module.Finite A (M.X j) :=
  inferInstance

/-- Helper for Lemma 15.97.4: the image of scalar multiplication by `a` is the principal-ideal
submodule `aN`. -/
private theorem range_lsmul_eq_principalIdeal_smul_top
    {N : Type*} [AddCommGroup N] [Module A N] (a : A) :
    LinearMap.range (LinearMap.lsmul A N a) =
      principalIdeal a • (⊤ : Submodule A N) := by
  ext x
  constructor
  · intro hx
    rcases LinearMap.mem_range.mp hx with ⟨y, rfl⟩
    -- Proof comment: every visible `a`-multiple lies in the principal-ideal multiple by
    -- construction.
    simpa [principalIdeal, LinearMap.lsmul_apply] using
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a)
        (show y ∈ (⊤ : Submodule A N) by simp))
  · intro hx
    -- Proof comment: every generator of `aN` comes from the corresponding preimage under
    -- multiplication by `a`.
    have hle :
        principalIdeal a • (⊤ : Submodule A N) ≤ LinearMap.range (LinearMap.lsmul A N a) := by
      rw [Submodule.smul_le]
      intro r hr y hy
      rcases Ideal.mem_span_singleton.mp hr with ⟨b, rfl⟩
      refine LinearMap.mem_range.mpr ⟨b • y, ?_⟩
      simp [LinearMap.lsmul_apply, smul_smul, mul_comm]
    exact hle hx

/-- Helper for Lemma 15.97.4: mapping a submodule into the first factor of a product gives the
product of that submodule with `0` in the second factor. -/
private theorem submodule_map_inl_eq_prod_bot
    {N₁ : Type*} [AddCommGroup N₁] [Module A N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module A N₂]
    (P : Submodule A N₁) :
    P.map (LinearMap.inl A N₁ N₂) = Submodule.prod P (⊥ : Submodule A N₂) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    -- Proof comment: the image of `inl` lands in the first-factor copy of `P` with zero tail.
    exact ⟨hy, by simp⟩
  · intro hx
    rcases hx with ⟨hx₁, hx₂⟩
    have hx₂' : x.2 = 0 := by
      simpa using hx₂
    -- Proof comment: an element of `P × {0}` is visibly `inl` of its first coordinate.
    refine ⟨x.1, hx₁, ?_⟩
    ext <;> simp [hx₂']

/-- Helper for Lemma 15.97.4: quotienting a product by a product submodule splits as the product
of the two quotient modules. -/
private theorem quotient_prod_submodule_equiv
    {M₁ : Type*} [AddCommGroup M₁] [Module A M₁]
    {M₂ : Type*} [AddCommGroup M₂] [Module A M₂]
    (P : Submodule A M₁) (Q : Submodule A M₂) :
    ((M₁ × M₂) ⧸ Submodule.prod P Q) ≃ₗ[A] ((M₁ ⧸ P) × (M₂ ⧸ Q)) := by
  let φ : M₁ × M₂ →ₗ[A] ((M₁ ⧸ P) × (M₂ ⧸ Q)) := LinearMap.prod P.mkQ Q.mkQ
  have hker : LinearMap.ker φ = Submodule.prod P Q := by
    -- Proof comment: the product quotient map vanishes exactly on `P × Q`.
    simpa [φ] using (LinearMap.ker_prodMap (f := P.mkQ) (g := Q.mkQ))
  have hsurj : Function.Surjective φ := by
    intro y
    rcases Submodule.mkQ_surjective P y.1 with ⟨x₁, rfl⟩
    rcases Submodule.mkQ_surjective Q y.2 with ⟨x₂, rfl⟩
    exact ⟨(x₁, x₂), rfl⟩
  have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.2 hsurj
  -- Proof comment: transport to the actual kernel and then collapse the full range.
  exact
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      (φ.quotKerEquivRange.trans
        ((LinearEquiv.ofEq _ _ hrange).trans Submodule.topEquiv))

/-- Helper for Lemma 15.97.4: quotienting by the zero submodule recovers the ambient module. -/
private noncomputable def quotient_bot_linearEquiv
    {N : Type*} [AddCommGroup N] [Module A N] :
    (N ⧸ (⊥ : Submodule A N)) ≃ₗ[A] N :=
  Submodule.quotEquivOfEqBot (⊥ : Submodule A N) rfl

/-- Helper for Lemma 15.97.4: functions on `Fin (n + 1)` split as the first coordinate together
with the tail. -/
private noncomputable def finSuccArrowLinearEquiv
    {B : Type*} [AddCommGroup B] [Module A B] (n : ℕ) :
    (Fin (n + 1) → B) ≃ₗ[A] (B × (Fin n → B)) where
  toEquiv := (Fin.consEquiv fun _ : Fin (n + 1) => B).symm
  map_add' f g := by
    -- Proof comment: the standard `Fin.consEquiv` is definitionally coordinatewise.
    rfl
  map_smul' a f := by
    -- Proof comment: scalar multiplication is transported coordinatewise through the same
    -- equivalence.
    rfl

/-- Helper for Lemma 15.97.4: if the differential in degree `i` vanishes, the eta-presentation map
is just multiplication by `g` followed by the first inclusion. -/
lemma etaPresentationLinearMap_zero_differential_factorization
    (g : A) (N : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ)
    (hd : (N.d i (i + 1)).hom = 0) :
    etaPresentationLinearMap g N i =
      (LinearMap.inl A (N.X i) (N.X (i + 1))).comp
        (LinearMap.lsmul A (N.X i) g) := by
  -- Proof comment: after `d^i = 0`, the second coordinate of `(g, d^i)` disappears.
  ext x <;> simp [etaPresentationLinearMap, hd, LinearMap.lsmul_apply]

/-- Helper for Lemma 15.97.4: under the zero-differential hypothesis, the range of the
eta-presentation map is the image of `g : N^i → N^i` under the first inclusion. -/
lemma etaPresentationLinearMap_zero_differential_range
    (g : A) (N : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ)
    (hd : (N.d i (i + 1)).hom = 0) :
    LinearMap.range (etaPresentationLinearMap g N i) =
      (LinearMap.range (LinearMap.lsmul A (N.X i) g)).map
        (LinearMap.inl A (N.X i) (N.X (i + 1))) := by
  -- Proof comment: factor the map through the first summand and apply the standard range formula
  -- for a composite.
  simpa [etaPresentationLinearMap_zero_differential_factorization (A := A) g N i hd]
    using
      LinearMap.range_comp
        (LinearMap.lsmul A (N.X i) g)
        (LinearMap.inl A (N.X i) (N.X (i + 1)))

/-- Helper for Lemma 15.97.4: when `d^i = 0`, the eta-presentation range is exactly
`gN^i × {0}` inside the target product. -/
private theorem etaPresentationLinearMap_zero_differential_range_eq_prod
    (g : A) (N : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ)
    (hd : (N.d i (i + 1)).hom = 0) :
    LinearMap.range (etaPresentationLinearMap g N i) =
      Submodule.prod
        (principalIdeal g • (⊤ : Submodule A (N.X i)))
        (⊥ : Submodule A (N.X (i + 1))) := by
  -- Proof comment: combine the factorization through `inl` with the explicit range of
  -- multiplication by `g`.
  calc
    LinearMap.range (etaPresentationLinearMap g N i) =
        (LinearMap.range (LinearMap.lsmul A (N.X i) g)).map
          (LinearMap.inl A (N.X i) (N.X (i + 1))) := by
      exact etaPresentationLinearMap_zero_differential_range (A := A) g N i hd
    _ = (principalIdeal g • (⊤ : Submodule A (N.X i))).map
          (LinearMap.inl A (N.X i) (N.X (i + 1))) := by
      rw [range_lsmul_eq_principalIdeal_smul_top (A := A) (N := N.X i) g]
    _ = Submodule.prod
          (principalIdeal g • (⊤ : Submodule A (N.X i)))
          (⊥ : Submodule A (N.X (i + 1))) := by
      exact submodule_map_inl_eq_prod_bot
        (A := A) (N₁ := N.X i) (N₂ := N.X (i + 1))
        (principalIdeal g • (⊤ : Submodule A (N.X i)))

/-- Helper for Lemma 15.97.4: when `d^i = 0`, the eta-presentation quotient splits as the
quotient of `N^i` by `gN^i` together with the untouched term `N^{i + 1}`. -/
private noncomputable def etaPresentationQuotient_zero_differential_split
    (g : A) (N : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ)
    (hd : (N.d i (i + 1)).hom = 0) :
    etaPresentationQuotient g N i ≃ₗ[A]
      ((N.X i ⧸ principalIdeal g • (⊤ : Submodule A (N.X i))) × N.X (i + 1)) :=
  (Submodule.quotEquivOfEq _ _
      (etaPresentationLinearMap_zero_differential_range_eq_prod
        (A := A) g N i hd)).trans
    ((quotient_prod_submodule_equiv
        (A := A)
        (P := principalIdeal g • (⊤ : Submodule A (N.X i)))
        (Q := (⊥ : Submodule A (N.X (i + 1))))).trans
      (LinearEquiv.prodCongr
        (LinearEquiv.refl A
          (N.X i ⧸ principalIdeal g • (⊤ : Submodule A (N.X i))))
        (quotient_bot_linearEquiv (A := A) (N := N.X (i + 1)))))

/-- Helper for Lemma 15.97.4: any two integer offsets can be balanced by adding suitable natural
numbers on the left. -/
lemma alternatingRankTail_balance_exists (x y : ℤ) :
    ∃ m n : ℕ, (m : ℤ) + x = (n : ℤ) + y := by
  -- Proof comment: shift the smaller side up by the nonnegative difference between `x` and `y`.
  by_cases hxy : x ≤ y
  · refine ⟨Int.toNat (y - x), 0, ?_⟩
    -- Proof comment: when `x ≤ y`, the difference `y - x` is already a natural number.
    have hnonneg : 0 ≤ y - x := sub_nonneg.mpr hxy
    calc
      ((Int.toNat (y - x) : ℕ) : ℤ) + x = (y - x) + x := by
        rw [Int.toNat_of_nonneg hnonneg]
      _ = y := by omega
      _ = ((0 : ℕ) : ℤ) + y := by simp
  · refine ⟨0, Int.toNat (x - y), ?_⟩
    -- Proof comment: the opposite inequality gives the same balancing formula after swapping.
    have hyx : y ≤ x := le_of_not_ge hxy
    have hnonneg : 0 ≤ x - y := sub_nonneg.mpr hyx
    calc
      ((0 : ℕ) : ℤ) + x = x := by simp
      _ = (x - y) + y := by omega
      _ = ((Int.toNat (x - y) : ℕ) : ℤ) + y := by
        rw [Int.toNat_of_nonneg hnonneg]

/-- Helper for Lemma 15.97.4: the derived homology of the localized strict complex is the
prime-localized ordinary homology module. -/
private noncomputable def localizationAtPrimeComplex_homology_iso_localizedModule
    (p : PrimeSpectrum A) (M : CochainComplex (ModuleCat.{u} A) ℤ) (j : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat (Localization.AtPrime p.asIdeal)) j).obj
        ((DerivedCategory.Q).obj (CategoryTheory.localizationAtPrimeComplex p M)) ≅
      ModuleCat.of (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal (M.homology j)) := by
  let Aₚ := Localization.AtPrime p.asIdeal
  let eQ :
      (DerivedCategory.homologyFunctor (ModuleCat Aₚ) j).obj
          ((DerivedCategory.Q).obj (CategoryTheory.localizationAtPrimeComplex p M)) ≅
        (DerivedCategory.homologyFunctor (ModuleCat Aₚ) j).obj
          (((ModuleCat.extendScalars (algebraMap A Aₚ)).mapDerivedCategory).obj
            ((DerivedCategory.Q).obj M)) :=
    (DerivedCategory.homologyFunctor (ModuleCat Aₚ) j).mapIso
      (CategoryTheory.q_obj_localizationAtPrimeComplex_mapDerived_iso (R := A) (p := p) M)
  let eBase :
      (ModuleCat.extendScalars (algebraMap A Aₚ)).obj
          ((DerivedCategory.homologyFunctor (ModuleCat A) j).obj ((DerivedCategory.Q).obj M)) ≅
        (DerivedCategory.homologyFunctor (ModuleCat Aₚ) j).obj
          (((ModuleCat.extendScalars (algebraMap A Aₚ)).mapDerivedCategory).obj
            ((DerivedCategory.Q).obj M)) :=
    extendScalars_homology_iso_of_flat (R := A) (R' := Aₚ) ((DerivedCategory.Q).obj M) j
  let eHom :
      (DerivedCategory.homologyFunctor (ModuleCat A) j).obj ((DerivedCategory.Q).obj M) ≅
        M.homology j :=
    (DerivedCategory.homologyFunctorFactors (ModuleCat A) j).app M
  let restrictScalarsSelfEquiv :
      ↑((ModuleCat.restrictScalars (algebraMap A Aₚ)).obj (ModuleCat.of Aₚ Aₚ)) ≃ₗ[Aₚ] Aₚ :=
    { __ := AddEquiv.refl Aₚ
      map_smul' := fun _ _ ↦ rfl }
  let eTensor :
      (ModuleCat.extendScalars (algebraMap A Aₚ)).obj (M.homology j) ≅
        ModuleCat.of Aₚ (Aₚ ⊗[A] M.homology j) := by
    -- Proof comment: rewrite exact scalar extension as the canonical tensor-product model.
    simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
      (TensorProduct.AlgebraTensorModule.congr
        restrictScalarsSelfEquiv
        (LinearEquiv.refl A (M.homology j))).toModuleIso
  let eLocal :
      ModuleCat.of Aₚ (Aₚ ⊗[A] M.homology j) ≅
        ModuleCat.of Aₚ (LocalizedModule.AtPrime p.asIdeal (M.homology j)) :=
    ((LocalizedModule.equivTensorProduct p.asIdeal.primeCompl (M.homology j)).symm).toModuleIso
  -- Proof comment: first compare strict localization with derived scalar extension, then commute
  -- homology past exact flat extension, and finally identify the tensor product with the
  -- localized module.
  exact eQ ≪≫ eBase.symm ≪≫ (ModuleCat.extendScalars (algebraMap A Aₚ)).mapIso eHom ≪≫
    eTensor ≪≫ eLocal

/-- Helper for Lemma 15.97.4: freeness of the localized cohomology modules forces all higher
`Ext` groups between the localized derived homology objects to vanish. -/
private theorem localized_homology_ext_vanishing_of_free
    (p : PrimeSpectrum A) (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hcohom :
      ∀ j : ℤ,
        Module.Free (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal (M.homology j))) :
    ∀ (n : ℕ) (_ : 2 ≤ n) (j k : ℤ) (_ : k < j),
      Subsingleton
        (Ext
          ((DerivedCategory.homologyFunctor
              (ModuleCat (Localization.AtPrime p.asIdeal)) j).obj
            ((DerivedCategory.Q).obj (CategoryTheory.localizationAtPrimeComplex p M)))
          ((DerivedCategory.homologyFunctor
              (ModuleCat (Localization.AtPrime p.asIdeal)) k).obj
            ((DerivedCategory.Q).obj (CategoryTheory.localizationAtPrimeComplex p M)))
          n) := by
  intro n hn j k hk
  let Aₚ := Localization.AtPrime p.asIdeal
  let Hj :
      ModuleCat Aₚ :=
    (DerivedCategory.homologyFunctor (ModuleCat Aₚ) j).obj
      ((DerivedCategory.Q).obj (CategoryTheory.localizationAtPrimeComplex p M))
  let Hk :
      ModuleCat Aₚ :=
    (DerivedCategory.homologyFunctor (ModuleCat Aₚ) k).obj
      ((DerivedCategory.Q).obj (CategoryTheory.localizationAtPrimeComplex p M))
  let eHj := localizationAtPrimeComplex_homology_iso_localizedModule (A := A) p M j
  have hprojLocalized :
      Projective
        (ModuleCat.of Aₚ (LocalizedModule.AtPrime p.asIdeal (M.homology j))) := by
    letI : Module.Free Aₚ (LocalizedModule.AtPrime p.asIdeal (M.homology j)) := hcohom j
    simpa using
      (inferInstance :
        Projective (ModuleCat.of Aₚ (LocalizedModule.AtPrime p.asIdeal (M.homology j))))
  have hprojHj : Projective Hj := by
    -- Proof comment: transport projectivity across the homology identification just proved.
    exact Projective.of_iso eHj.symm hprojLocalized
  have hpdHj : HasProjectiveDimensionLE Hj 0 := by
    -- Proof comment: projective objects have projective dimension zero, which kills all higher
    -- `Ext`s out of `H^j`.
    exact (projective_iff_hasProjectiveDimensionLE_zero Hj).1 hprojHj
  letI : HasProjectiveDimensionLT Hj 1 := hpdHj
  refine ⟨fun e₁ e₂ ↦ ?_⟩
  have hz₁ : e₁ = 0 :=
    CategoryTheory.Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT e₁ 1 (by omega)
  have hz₂ : e₂ = 0 :=
    CategoryTheory.Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT e₂ 1 (by omega)
  rw [hz₁, hz₂]

-- Proof sketch: localize at `p`, use the base-change formula for `I_i(M^\bullet, f)` and the
-- invariance under replacing `M^\bullet` by a quasi-isomorphic bounded finite free complex, then
-- apply the splitting result for complexes with free localized cohomology to replace `M^\bullet_p`
-- by the zero-differential complex on its cohomology. For a zero-differential complex, `(f, d^i)`
-- becomes `(f, 0)`, whose maximal minors generate a power of `f`.
/-- Lemma 15.97.4: let `A` be a ring, let `𝔭 ⊂ A` be a prime ideal, and let `f ∈ A` be a
nonzerodivisor. Let `M^\bullet` be a bounded complex of finite free `A`-modules. If
`H^i(M^\bullet)_𝔭` is free for all `i`, then `I_i(M^\bullet, f)_𝔭` is generated by a power of the
image of `f` for every `i`. -/
theorem etaDeterminantalIdeal_atPrime_eq_principalIdeal_pow_of_homology_free
    (p : PrimeSpectrum A) (f : A) (hf : f ∈ nonZeroDivisors A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hboundedBelow : ∃ a : ℤ, M.IsStrictlyGE a)
    (hboundedAbove : ∃ b : ℤ, M.IsStrictlyLE b)
    [CategoryTheory.CochainComplex.IsTermwiseFiniteFree M]
    (hcohom :
      ∀ j : ℤ,
        Module.Free (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal (M.homology j)))
    (i : ℤ) :
    let Aₚ := Localization.AtPrime p.asIdeal
    ∃ n : ℕ,
      Ideal.map (algebraMap A Aₚ) (I[f]_(i)(M)) =
        principalIdeal ((algebraMap A Aₚ f) ^ n) :=
  by
  let Aₚ := Localization.AtPrime p.asIdeal
  let g : Aₚ := algebraMap A Aₚ f
  let Mp : CochainComplex (ModuleCat.{u} Aₚ) ℤ :=
    (((ModuleCat.extendScalars (algebraMap A Aₚ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (M : CochainComplex (ModuleCat.{u} A) ℤ))
  have hmap :=
    (etaDeterminantalIdeal_baseChange
      (A := A) (B := Aₚ) (f := f)
      (M := (M : CochainComplex (ModuleCat.{u} A) ℤ)) (i := i)).symm
  letI : Module.Flat A Aₚ := IsLocalization.flat Aₚ p.asIdeal.primeCompl
  have hg : g ∈ nonZeroDivisors Aₚ := by
    -- Proof comment: localization is flat, so the image of a nonzerodivisor stays regular.
    simpa [Aₚ, g] using
      (algebraMap_mem_nonZeroDivisors_of_flat (A := A) (B := Aₚ) f hf)
  have hgreg : IsRegular g := by
    -- Proof comment: `15.97.1` is stated for `IsRegular`, so convert the localized hypothesis now.
    rwa [isRegular_iff_mem_nonZeroDivisors]
  have hExtLocal :
      ∀ (n : ℕ) (_ : 2 ≤ n) (j k : ℤ) (_ : k < j),
        Subsingleton
          (Ext
            ((DerivedCategory.homologyFunctor (ModuleCat Aₚ) j).obj ((DerivedCategory.Q).obj Mp))
            ((DerivedCategory.homologyFunctor (ModuleCat Aₚ) k).obj ((DerivedCategory.Q).obj Mp))
            n) := by
    -- Proof comment: after identifying localized derived homology with localized ordinary
    -- homology, freeness gives projectivity and therefore vanishing of all higher `Ext`s.
    simpa [Mp, Aₚ] using
      localized_homology_ext_vanishing_of_free (A := A) p M hcohom
  -- Route correction: the proof now follows the source route up to the localized owner provided by
  -- `hmap`, with `Mp` naming the strict scalar-extension complex used in that base-change step.
  -- TODO: transport the localized homology objects to `LocalizedModule.AtPrime p.asIdeal
  -- (M.homology j)` and the higher-`Ext` vanishing are now established. The remaining source-faithful
  -- blocker is to realize the resulting split object as an explicit bounded zero-differential
  -- finite-free complex `N`, compute `I[g]_(i)(N)` as a principal power, and then transport that
  -- equality back along `15.97.1`.
  let _ := hboundedBelow
  let _ := hboundedAbove
  let _ := hcohom
  let _ := hmap
  let _ := hg
  let _ := hgreg
  let _ := hExtLocal
  sorry

end
