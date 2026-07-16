import Mathlib.Data.List.TFAE
import StacksProject_2024.stacks_project.Chap10.Definition_10_78_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_23_1
import Mathlib.RingTheory.Localization.Away.Basic
import StacksProject_2024.stacks_project.Chap15.Definition_15_8_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_4_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_8_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped FittingIdeal TensorProduct

universe u v

section

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

section

variable [Module.Finite R M]

/-- Helper for Lemma 15.8.8: the Fitting ideals of the standard free module `A^n` are `0` below
rank `n` and the unit ideal from rank `n` onward. -/
lemma fittingIdeal_free_eq_zero_or_top_local
    {A : Type*} [CommRing A] (n k : ℕ) :
    Fit[A]_(k)(Fin n → A) = if k < n then ⊥ else ⊤ := by
  let π : (Fin n → A) →ₗ[A] (Fin n → A) := LinearMap.id
  have hπ : Function.Surjective π := fun x ↦ ⟨x, rfl⟩
  rw [fittingIdeal_eq_presentationFittingIdeal (R := A) (M := Fin n → A) k π hπ]
  by_cases hk : k < n
  · have hnk : 0 < n - k := Nat.sub_pos_of_lt hk
    rw [if_pos hk, presentationFittingIdeal, Matrix.minorIdeal, Ideal.span_eq_bot]
    rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
    exact Matrix.det_eq_zero_of_row_eq_zero ⟨0, hnk⟩ fun j ↦ by
      have he₂j : (((e₂ j : LinearMap.ker π) : Fin n → A)) = 0 :=
        LinearMap.mem_ker.mp (e₂ j).property
      have hentry :
          (((e₂ j : LinearMap.ker π) : Fin n → A) (e₁ ⟨0, hnk⟩)) = 0 := by
        simpa using congrArg (fun v : Fin n → A ↦ v (e₁ ⟨0, hnk⟩)) he₂j
      simpa [π] using hentry
  · have hk' : n ≤ k := Nat.le_of_not_gt hk
    rw [if_neg hk, presentationFittingIdeal, Matrix.minorIdeal, Nat.sub_eq_zero_of_le hk']
    refine Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one
    refine Ideal.subset_span ?_
    refine ⟨⟨⟨Fin.elim0, ?_⟩, ⟨Fin.elim0, ?_⟩⟩, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
    · simp [Matrix.det_fin_zero]

/-- Helper for Lemma 15.8.8: after transporting a finite module across a linear equivalence with
the standard free module of rank `r`, its `k`th Fitting ideal is the expected `0`/`R` dichotomy. -/
lemma fittingIdeal_eq_zero_or_top_of_linearEquiv_fin
    {A : Type*} [CommRing A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    {r : ℕ} (e : N ≃ₗ[A] (Fin r → A)) (k : ℕ) :
    Fit[A]_(k)(N) = if k < r then ⊥ else ⊤ := by
  -- Transport the intrinsic Fitting ideal to the standard free module, then use the explicit
  -- free-module computation from Example `15.8.5`.
  calc
    Fit[A]_(k)(N) = Fit[A]_(k)(Fin r → A) := by
      simpa using
        (fittingIdeal_eq_of_linearEquiv
          (R := A) (M := N) (M' := Fin r → A) (k := k) e)
    _ = if k < r then ⊥ else ⊤ := fittingIdeal_free_eq_zero_or_top_local r k

/-- Helper for Lemma 15.8.8: an ideal is zero once all of its prime localizations are zero. -/
lemma ideal_eq_bot_of_localizedAtPrime_map_eq_bot
    {A : Type*} [CommRing A]
    (J : Ideal A)
    (hJ : ∀ q : PrimeSpectrum A,
      Ideal.map (algebraMap A (Localization.AtPrime q.asIdeal)) J = ⊥) :
    J = ⊥ := by
  ext x
  constructor
  · intro hx
    have hx_local :
        ∀ (P : Ideal A) [P.IsPrime],
          LocalizedModule.mkLinearMap P.primeCompl A x = 0 := by
      intro P hP
      let q : PrimeSpectrum A := ⟨P, hP⟩
      have hx_map :
          algebraMap A (Localization.AtPrime P) x ∈
            Ideal.map (algebraMap A (Localization.AtPrime P)) J :=
        Ideal.mem_map_of_mem _ hx
      simpa [q, hJ q] using hx_map
    -- Detect the vanishing of the ring element from all prime localizations.
    exact
      ((element_zero_localization_tfae (R := A) (M := A) x).out 1 0).mp
        hx_local
  · intro hx
    have hx_zero : x = 0 := by
      simpa using hx
    simpa [hx_zero] using J.zero_mem

/-- Helper for Lemma 15.8.8: the canonical basis vectors transported back through a linear
equivalence with `A^r` generate the source module. -/
lemma exists_generators_of_linearEquiv_fin
    {A : Type*} [CommRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    {r : ℕ} (e : N ≃ₗ[A] (Fin r → A)) :
    ∃ v : Fin r → N, Submodule.span A (Set.range v) = ⊤ := by
  let σ : (Fin r → A) →ₗ[A] N := e.symm.toLinearMap
  let v : Fin r → N := fun i ↦ σ (Pi.single i (1 : A))
  have hσ : Function.Surjective σ := e.symm.surjective
  have hlin : Fintype.linearCombination A v = σ := by
    -- The transported standard basis vectors recover the inverse coordinate map `σ`.
    apply LinearMap.ext
    intro x
    calc
      (Fintype.linearCombination A v) x
          = ∑ i, x i • σ (Pi.single i (1 : A)) := by
              simp [v, Fintype.linearCombination_apply]
      _ = ∑ i, σ (x i • (Pi.single i (1 : A) : Fin r → A)) := by
            congr with i
            exact (σ.map_smul (x i) (Pi.single i (1 : A))).symm
      _ = σ (∑ i, x i • (Pi.single i (1 : A) : Fin r → A)) := by
            symm
            simp [map_sum]
      _ = σ x := by
            congr 1
            ext i
            simpa [Pi.single_apply, mul_comm] using
              (Fintype.sum_pi_single (i := i) (f := x))
  refine ⟨v, ?_⟩
  -- Repackage surjectivity of the coordinate map as a spanning statement.
  rw [span_range_eq_top_iff_surjective_fintypeLinearCombination]
  intro x
  rcases hσ x with ⟨c, rfl⟩
  refine ⟨c, ?_⟩
  simpa [hlin]

/-- Helper for Lemma 15.8.8: once `N ≃ A^r`, it is also generated by any larger number `k ≥ r`
of elements by padding the standard basis with zero coordinates. -/
lemma exists_generators_of_linearEquiv_fin_of_le
    {A : Type*} [CommRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    {r k : ℕ} (hrk : r ≤ k) (e : N ≃ₗ[A] (Fin r → A)) :
    ∃ v : Fin k → N, Submodule.span A (Set.range v) = ⊤ := by
  let ρ : (Fin k → A) →ₗ[A] (Fin r → A) :=
    LinearMap.pi fun i : Fin r ↦ LinearMap.proj (Fin.castLE hrk i)
  have hρ : Function.Surjective ρ := by
    -- Extend a coordinate vector on `Fin r` by zero on the remaining coordinates.
    intro y
    refine ⟨fun i ↦ if h : i.1 < r then y ⟨i.1, h⟩ else 0, ?_⟩
    ext i
    simp [ρ, i.2]
  let σ : (Fin k → A) →ₗ[A] N := e.symm.toLinearMap.comp ρ
  have hσ : Function.Surjective σ := e.symm.surjective.comp hρ
  let v : Fin k → N := fun i ↦ σ (Pi.single i (1 : A))
  have hlin : Fintype.linearCombination A v = σ := by
    -- The padded standard basis vectors still recover the coordinate map `σ`.
    apply LinearMap.ext
    intro x
    calc
      (Fintype.linearCombination A v) x
          = ∑ i, x i • σ (Pi.single i (1 : A)) := by
              simp [v, Fintype.linearCombination_apply]
      _ = ∑ i, σ (x i • (Pi.single i (1 : A) : Fin k → A)) := by
            congr with i
            exact (σ.map_smul (x i) (Pi.single i (1 : A))).symm
      _ = σ (∑ i, x i • (Pi.single i (1 : A) : Fin k → A)) := by
            symm
            simp [map_sum]
      _ = σ x := by
            congr 1
            ext i
            simpa [Pi.single_apply, mul_comm] using
              (Fintype.sum_pi_single (i := i) (f := x))
  refine ⟨v, ?_⟩
  -- Repackage surjectivity of the padded coordinate map as a spanning statement.
  rw [span_range_eq_top_iff_surjective_fintypeLinearCombination]
  intro x
  rcases hσ x with ⟨c, rfl⟩
  refine ⟨c, ?_⟩
  simpa [hlin]

/-- Helper for Lemma 15.8.8: after localizing away from `f`, the `k`th Fitting ideal is computed
through the canonical tensor-product model of `LocalizedModule.Away f M`. -/
lemma fittingIdeal_away_eq_tensor
    {f : R} (k : ℕ) :
    Fit[Localization.Away f]_(k)(LocalizedModule.Away f M) =
      Fit[Localization.Away f]_(k)((Localization.Away f) ⊗[R] M) := by
  let hfiniteTensor :
      Module.Finite (Localization.Away f) ((Localization.Away f) ⊗[R] M) :=
    Module.Finite.base_change (R := R) (A := Localization.Away f) (M := M)
  let _ : Module.Finite (Localization.Away f) ((Localization.Away f) ⊗[R] M) := hfiniteTensor
  let _ : Module.Finite (Localization.Away f) (LocalizedModule.Away f M) :=
    Module.Finite.equiv (LocalizedModule.equivTensorProduct (Submonoid.powers f) M).symm
  -- Rewrite the away-local module through the canonical tensor-product model first.
  simpa using
    (fittingIdeal_eq_of_linearEquiv
      (R := Localization.Away f)
      (M := LocalizedModule.Away f M)
      (M' := (Localization.Away f) ⊗[R] M)
      (k := k)
      (LocalizedModule.equivTensorProduct (Submonoid.powers f) M))

/-- Helper for Lemma 15.8.8: forming determinantal ideals commutes with applying the localization
map coefficientwise to a matrix. -/
lemma matrix_minorIdeal_map_eq_local
    {f : R} {ι κ : Type*} (t : ℕ) (A : Matrix ι κ R) :
    Ideal.map (algebraMap R (Localization.Away f)) (Matrix.minorIdeal t A) =
      Matrix.minorIdeal t (A.map (algebraMap R (Localization.Away f))) := by
  classical
  -- Unfold the determinantal ideal and move the localization map across each determinant.
  unfold Matrix.minorIdeal
  rw [Ideal.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨p, rfl⟩, rfl⟩
    refine ⟨p, ?_⟩
    have hsub :
        (algebraMap R (Localization.Away f)).mapMatrix (A.submatrix p.1 p.2) =
          (A.map (algebraMap R (Localization.Away f))).submatrix p.1 p.2 := by
      ext i j
      rfl
    simpa [hsub] using
      (RingHom.map_det (algebraMap R (Localization.Away f)) (A.submatrix p.1 p.2)).symm
  · rintro ⟨p, hp⟩
    refine ⟨(A.submatrix p.1 p.2).det, ?_, ?_⟩
    · exact ⟨p, rfl⟩
    · have hsub :
          (algebraMap R (Localization.Away f)).mapMatrix (A.submatrix p.1 p.2) =
            (A.map (algebraMap R (Localization.Away f))).submatrix p.1 p.2 := by
        ext i j
        rfl
      calc
        algebraMap R (Localization.Away f) (A.submatrix p.1 p.2).det =
            ((A.map (algebraMap R (Localization.Away f))).submatrix p.1 p.2).det := by
              simpa [hsub] using
                RingHom.map_det (algebraMap R (Localization.Away f)) (A.submatrix p.1 p.2)
        _ = y := hp

/-- Helper for Lemma 15.8.8: tensoring the standard free source `R^n` with `R_f` identifies it
with the standard free `R_f`-module on `Fin n`. -/
private noncomputable abbrev away_tensor_free_equiv
    {f : R} (n : ℕ) :
    (Localization.Away f) ⊗[R] (Fin n → R) ≃ₗ[Localization.Away f]
      (Fin n → Localization.Away f) :=
  TensorProduct.piScalarRight R (Localization.Away f) (Localization.Away f) (Fin n)

/-- Helper for Lemma 15.8.8: tensoring a finite free presentation and then transporting the
source through `away_tensor_free_equiv` gives the standard away-local presentation. -/
private noncomputable abbrev away_tensor_presentation
    {f : R} {n : ℕ} (π : (Fin n → R) →ₗ[R] M) :
    (Fin n → Localization.Away f) →ₗ[Localization.Away f]
      ((Localization.Away f) ⊗[R] M) :=
  (π.baseChange (Localization.Away f)).comp
    ((away_tensor_free_equiv (R := R) (f := f) n).symm.toLinearMap)

/-- Helper for Lemma 15.8.8: tensoring preserves surjectivity for the chosen away-local
presentation. -/
private lemma away_tensor_presentation_surjective
    {f : R} {n : ℕ} (π : (Fin n → R) →ₗ[R] M) (hπ : Function.Surjective π) :
    Function.Surjective (away_tensor_presentation (R := R) (M := M) (f := f) π) := by
  -- Proof comment: first tensor the original surjection, then move to the standard free source
  -- `R_f^n` through the canonical tensor/free equivalence.
  exact
    (LinearMap.lTensor_surjective (Localization.Away f) hπ).comp
      ((away_tensor_free_equiv (R := R) (f := f) n).symm.surjective)

/-- Helper for Lemma 15.8.8: the transported pure tensor `1 ⊗ x` lies in the kernel of the
away-local presentation. -/
private lemma away_kernel_vector_mem
    {f : R} {n : ℕ} (π : (Fin n → R) →ₗ[R] M)
    (x : LinearMap.ker π) :
    (away_tensor_free_equiv (R := R) (f := f) n)
        (TensorProduct.tmul R (1 : Localization.Away f) x.1) ∈
      LinearMap.ker (away_tensor_presentation (R := R) (M := M) (f := f) π) := by
  -- Rewrite the away-local presentation as a tensorized map and then cancel the free-source
  -- equivalence on the chosen pure tensor.
  change
    (π.baseChange (Localization.Away f))
        (((away_tensor_free_equiv (R := R) (f := f) n).symm)
          ((away_tensor_free_equiv (R := R) (f := f) n)
            (TensorProduct.tmul R (1 : Localization.Away f) x.1))) = 0
  rw [show
      ((away_tensor_free_equiv (R := R) (f := f) n).symm)
          ((away_tensor_free_equiv (R := R) (f := f) n)
            (TensorProduct.tmul R (1 : Localization.Away f) x.1)) =
        TensorProduct.tmul R (1 : Localization.Away f) x.1 by
          simpa using
            (away_tensor_free_equiv (R := R) (f := f) n).symm_apply_apply
              (TensorProduct.tmul R (1 : Localization.Away f) x.1)]
  simp [LinearMap.baseChange_eq_ltensor, x.2]

/-- Helper for Lemma 15.8.8: a kernel vector of the original presentation gives a kernel vector of
the away-local presentation by tensoring with `1` and transporting across the free-source
equivalence. -/
private noncomputable def away_kernel_vector
    {f : R} {n : ℕ} (π : (Fin n → R) →ₗ[R] M)
    (x : LinearMap.ker π) :
    LinearMap.ker (away_tensor_presentation (R := R) (M := M) (f := f) π) :=
  ⟨(away_tensor_free_equiv (R := R) (f := f) n)
      (TensorProduct.tmul R (1 : Localization.Away f) x.1),
    away_kernel_vector_mem (R := R) (M := M) (f := f) π x⟩

/-- Helper for Lemma 15.8.8: the away-local kernel vector coming from `x` has coordinates given by
localizing the coordinates of `x`. -/
private lemma away_kernel_vector_apply
    {f : R} {n : ℕ} (π : (Fin n → R) →ₗ[R] M)
    (x : LinearMap.ker π) (i : Fin n) :
    (away_kernel_vector (R := R) (M := M) (f := f) π x).1 i =
      algebraMap R (Localization.Away f) (x.1 i) := by
  -- Expand the transported kernel vector and evaluate `TensorProduct.piScalarRight` on the pure
  -- tensor `1 ⊗ x`.
  change
    ((away_tensor_free_equiv (R := R) (f := f) n)
      (TensorProduct.tmul R (1 : Localization.Away f) x.1)) i =
        algebraMap R (Localization.Away f) (x.1 i)
  simpa [away_tensor_free_equiv, Algebra.smul_def]

/-- Helper for Lemma 15.8.8: evaluating the away-local linear combination of transported kernel
vectors is the coefficientwise localized linear combination of the original coordinates. -/
private lemma away_kernel_linearCombination_apply
    {f : R} {n : ℕ} (π : (Fin n → R) →ₗ[R] M)
    (l : LinearMap.ker π →₀ Localization.Away f) (i : Fin n) :
    ((Finsupp.linearCombination (Localization.Away f)
        (away_kernel_vector (R := R) (M := M) (f := f) π) l).1 i) =
      Finset.sum l.support
        (fun x ↦ l x * algebraMap R (Localization.Away f) (x.1 i)) := by
  -- Proof comment: expand the finitely supported linear combination and evaluate the result on the
  -- coordinate `i`.
  classical
  -- Rewrite the linear combination as a support-indexed sum and then evaluate each transported
  -- kernel vector coordinatewise.
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  simp [away_kernel_vector_apply, Algebra.smul_def, mul_comm]

/-- Helper for Lemma 15.8.8: taking minors commutes with transposing the ambient matrix. -/
private lemma minorIdeal_transpose_eq_local
    {A : Type*} [CommRing A] {ι κ : Type*} (t : ℕ) (B : Matrix ι κ A) :
    Matrix.minorIdeal t B.transpose = Matrix.minorIdeal t B := by
  refine le_antisymm ?_ ?_
  · -- Every selected minor of `Bᵀ` is the transpose of a selected minor of `B`.
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
    change (B.transpose.submatrix e₁ e₂).det ∈ Matrix.minorIdeal t B
    have hdet : (B.transpose.submatrix e₁ e₂).det = (B.submatrix e₂ e₁).det := by
      calc
        (B.transpose.submatrix e₁ e₂).det = ((B.submatrix e₂ e₁).transpose).det := by
          rw [Matrix.transpose_submatrix]
        _ = (B.submatrix e₂ e₁).det := by
          rw [Matrix.det_transpose]
    rw [hdet]
    exact Matrix.det_submatrix_mem_minorIdeal t B e₂ e₁
  · -- Apply the same transpose argument in the opposite direction.
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
    change (B.submatrix e₁ e₂).det ∈ Matrix.minorIdeal t B.transpose
    have hdet : (B.submatrix e₁ e₂).det = (B.transpose.submatrix e₂ e₁).det := by
      calc
        (B.submatrix e₁ e₂).det = ((B.submatrix e₁ e₂).transpose).det := by
          rw [Matrix.det_transpose]
        _ = (B.transpose.submatrix e₂ e₁).det := by
          rw [Matrix.transpose_submatrix]
    rw [hdet]
    exact Matrix.det_submatrix_mem_minorIdeal t B.transpose e₂ e₁

/-- Helper for Lemma 15.8.8: allowing repeated chosen columns still produces an element of the
same determinantal ideal. -/
private lemma det_submatrix_mem_minorIdeal_of_colMap_local
    {A : Type*} [CommRing A] {ι κ : Type*}
    (t : ℕ) (B : Matrix ι κ A) (e₁ : Fin t ↪ ι) (g : Fin t → κ) :
    (B.submatrix e₁ g).det ∈ Matrix.minorIdeal t B := by
  -- Proof comment: transpose to the row-map statement and rewrite back with determinant
  -- invariance under transpose.
  have hmem :
      (B.transpose.submatrix g e₁).det ∈ Matrix.minorIdeal t B.transpose :=
    Matrix.det_submatrix_mem_minorIdeal_of_rowMap t B.transpose g e₁
  have hdet : (B.transpose.submatrix g e₁).det = (B.submatrix e₁ g).det := by
    calc
      (B.transpose.submatrix g e₁).det = ((B.submatrix e₁ g).transpose).det := by
        rw [Matrix.transpose_submatrix]
      _ = (B.submatrix e₁ g).det := by
        rw [Matrix.det_transpose]
  rw [minorIdeal_transpose_eq_local (t := t) B] at hmem
  rwa [hdet] at hmem

/-- Helper for Lemma 15.8.8: after localizing away from `f`, the `k`th Fitting ideal of the
tensor-product model is the image of the original `k`th Fitting ideal. -/
lemma fittingIdeal_baseChange_away
    {f : R} (k : ℕ) :
    Fit[Localization.Away f]_(k)((Localization.Away f) ⊗[R] M) =
      Ideal.map (algebraMap R (Localization.Away f)) (Fit[R]_(k)(M)) := by
  -- TODO for Lemma 15.8.8: prove the away-local base-change identity directly in this file by
  -- comparing one finite free presentation of `M` with its tensorized presentation over
  -- `Localization.Away f`, then transporting the resulting determinantal ideal with
  -- `matrix_minorIdeal_map_eq_local`. The earlier owner file `Lemma_15_8_4` cannot currently be
  -- imported here because that file itself fails to build in this workspace.
  sorry

/-- Helper for Lemma 15.8.8: after localizing away from `f`, the `k`th Fitting ideal is computed
by the same `0`/`R_f` dichotomy coming from a free-rank-`r` trivialization of `M_f`. -/
lemma fittingIdeal_map_away_eq_zero_or_top_of_linearEquiv_fin
    {r : ℕ} {f : R}
    (e : LocalizedModule.Away f M ≃ₗ[Localization.Away f]
      (Fin r → Localization.Away f))
    (k : ℕ) :
    Ideal.map (algebraMap R (Localization.Away f)) (Fit[R]_(k)(M)) =
      if k < r then ⊥ else ⊤ := by
  -- Route correction: first rewrite the localized tensor-product model using the new away-local
  -- base-change bridge, then transport the computation across the canonical localization model.
  calc
    Ideal.map (algebraMap R (Localization.Away f)) (Fit[R]_(k)(M)) =
        Fit[Localization.Away f]_(k)((Localization.Away f) ⊗[R] M) := by
          simpa using
            (fittingIdeal_baseChange_away (R := R) (M := M) (f := f) k).symm
    _ = Fit[Localization.Away f]_(k)(LocalizedModule.Away f M) := by
          simpa using (fittingIdeal_away_eq_tensor (R := R) (M := M) (f := f) k).symm
    _ = if k < r then ⊥ else ⊤ :=
          fittingIdeal_eq_zero_or_top_of_linearEquiv_fin e k

/-- Helper for Lemma 15.8.8: vanishing of the predecessor Fitting ideal survives localization on a
standard open because `Fit_{r-1}` commutes with the away tensor-product model. -/
lemma precedingFittingIdeal_away_eq_bot_of_eq_bot
    {r : ℕ} {f : R} (hprev : precedingFittingIdeal R M r = ⊥) :
    precedingFittingIdeal (Localization.Away f) (LocalizedModule.Away f M) r = ⊥ := by
  cases r with
  | zero =>
      -- In rank `0`, the predecessor Fitting ideal is `⊥` by definition on every ring.
      simpa using
        (precedingFittingIdeal_zero
          (R := Localization.Away f) (M := LocalizedModule.Away f M))
  | succ r =>
      -- For positive rank, rewrite `Fit_{r-1}` as an ordinary Fitting ideal and transport it
      -- through the away-local base-change identity.
      rw [precedingFittingIdeal_succ] at hprev ⊢
      calc
        Fit[Localization.Away f]_(r)(LocalizedModule.Away f M) =
            Fit[Localization.Away f]_(r)((Localization.Away f) ⊗[R] M) := by
              simpa using
                (fittingIdeal_away_eq_tensor (R := R) (M := M) (f := f) r)
        _ = Ideal.map (algebraMap R (Localization.Away f)) (Fit[R]_(r)(M)) := by
              simpa using
                (fittingIdeal_baseChange_away (R := R) (M := M) (f := f) r)
        _ = ⊥ := by
              simpa [hprev]

/-- Helper for Lemma 15.8.8: for a surjection `A^r → N`, vanishing of `Fit_{r-1}(N)` forces the
surjection to be an isomorphism, because every kernel coordinate already lies in `Fit_{r-1}(N)`. -/
lemma kernel_coordinate_mem_fittingIdeal_of_surjective
    {A : Type*} [CommRing A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    {r : ℕ} (π : (Fin (r + 1) → A) →ₗ[A] N) (hπ : Function.Surjective π)
    (x : LinearMap.ker π) (i : Fin (r + 1)) :
    x.1 i ∈ Fit[A]_(r)(N) := by
  let row : Fin 1 ↪ Fin (r + 1) :=
    ⟨fun _ ↦ i, fun a b _ ↦ Subsingleton.elim a b⟩
  let col : Fin 1 ↪ LinearMap.ker π :=
    ⟨fun _ ↦ x, fun a b _ ↦ Subsingleton.elim a b⟩
  -- Rewrite the intrinsic Fitting ideal through the chosen presentation and pick the `1 × 1`
  -- minor whose determinant is exactly the chosen coordinate.
  rw [fittingIdeal_eq_presentationFittingIdeal (R := A) (M := N) r π hπ, presentationFittingIdeal]
  have hsize : r + 1 - r = 1 := by
    omega
  rw [hsize]
  have hminor :
      (Matrix.submatrix
          (fun j y ↦ y.1 j : Matrix (Fin (r + 1)) (LinearMap.ker π) A) row col).det ∈
        Matrix.minorIdeal 1 (fun j y ↦ y.1 j : Matrix (Fin (r + 1)) (LinearMap.ker π) A) := by
    exact Matrix.det_submatrix_mem_minorIdeal 1
      (fun j y ↦ y.1 j : Matrix (Fin (r + 1)) (LinearMap.ker π) A) row col
  simpa [row, col, Matrix.minorIdeal, Matrix.det_fin_one] using
    (Ideal.subset_span hminor)

/-- Helper for Lemma 15.8.8: a surjective map `A^r → N` with vanishing preceding Fitting ideal is
already an isomorphism. This is the local presentation step from the source proof. -/
lemma linearEquiv_fin_of_surjective_fin_of_precedingFittingIdeal_eq_bot
    {A : Type*} [CommRing A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    {r : ℕ} (π : (Fin r → A) →ₗ[A] N) (hπ : Function.Surjective π)
    (hprev : precedingFittingIdeal A N r = ⊥) :
    Nonempty (N ≃ₗ[A] (Fin r → A)) := by
  cases r with
  | zero =>
      have hsub : Subsingleton N := by
        refine ⟨fun x y ↦ ?_⟩
        rcases hπ x with ⟨a, rfl⟩
        rcases hπ y with ⟨b, rfl⟩
        exact congrArg π (Subsingleton.elim a b)
      -- In rank `0`, the codomain is forced to be the zero module.
      exact ⟨LinearEquiv.ofSubsingleton N (Fin 0 → A)⟩
  | succ r =>
      have hfit : Fit[A]_(r)(N) = ⊥ := by
        simpa using hprev
      have hker_zero : ∀ x : LinearMap.ker π, x = 0 := by
        intro x
        apply Subtype.ext
        ext i
        have hxi : x.1 i ∈ Fit[A]_(r)(N) :=
          kernel_coordinate_mem_fittingIdeal_of_surjective (A := A) (N := N) π hπ x i
        simpa [hfit] using hxi
      have hker_bot : LinearMap.ker π = ⊥ := by
        ext y
        constructor
        · intro hy
          let x : LinearMap.ker π := ⟨y, hy⟩
          have hx_zero : x = 0 := hker_zero x
          rw [Submodule.mem_bot]
          simpa [x] using congrArg Subtype.val hx_zero
        · intro hy
          rw [Submodule.mem_bot] at hy
          change π y = 0
          simpa [hy]
      have hbij : Function.Bijective π := ⟨LinearMap.ker_eq_bot.mp hker_bot, hπ⟩
      -- Vanishing of the kernel upgrades the surjection to a linear equivalence.
      exact ⟨(LinearEquiv.ofBijective π hbij).symm⟩

/-- Helper for Lemma 15.8.8: if `Fit_{r-1}(M)=0` and `Fit_r(M)=R`, then around every prime there
is a standard-open neighborhood on which `M` becomes free of rank `r`. -/
lemma exists_away_linearEquiv_fin_of_fitting_conditions_at_prime
    (r : ℕ)
    (hprev : precedingFittingIdeal R M r = ⊥)
    (htop : Fit[R]_(r)(M) = ⊤)
    (p : Ideal R) [p.IsPrime] :
    ∃ f : R, f ∉ p ∧
      Nonempty
        ((LocalizedModule.Away f M) ≃ₗ[Localization.Away f]
          (Fin r → Localization.Away f)) := by
  have hnot_le : ¬ Fit[R]_(r)(M) ≤ p := by
    intro hle
    have htop_le : (⊤ : Ideal R) ≤ p := by
      simpa [htop] using hle
    exact (Ideal.IsPrime.ne_top (I := p) inferInstance) (top_le_iff.mp htop_le)
  have hlocal_gen :
      ∃ f : R, f ∉ p ∧ ∃ v : Fin r → LocalizedModule.Away f M,
        Submodule.span (Localization.Away f) (Set.range v) = ⊤ := by
    -- Lemma `15.8.7` gives the away-local generation criterion at the chosen prime.
    exact
      ((fittingIdeal_not_le_prime_tfae_residueField_finrank_and_local_generators
        (R := R) (M := M) r p).out 0 3).mp hnot_le
  rcases hlocal_gen with ⟨f, hf, v, hv⟩
  let πf : (Fin r → Localization.Away f) →ₗ[Localization.Away f] LocalizedModule.Away f M :=
    Fintype.linearCombination (Localization.Away f) v
  have hπf : Function.Surjective πf := by
    -- The spanning family `v` is equivalently a surjective coordinate map from the free module.
    simpa [πf] using
      (span_range_eq_top_iff_surjective_fintypeLinearCombination
        (Localization.Away f) v).1 hv
  have hprevAway :
      precedingFittingIdeal (Localization.Away f) (LocalizedModule.Away f M) r = ⊥ :=
    precedingFittingIdeal_away_eq_bot_of_eq_bot (R := R) (M := M) (r := r) (f := f) hprev
  -- Vanishing of the predecessor Fitting ideal kills the kernel of the local coordinate map.
  exact
    ⟨f, hf,
      linearEquiv_fin_of_surjective_fin_of_precedingFittingIdeal_eq_bot
        (A := Localization.Away f) (N := LocalizedModule.Away f M) πf hπf hprevAway⟩

/-- Helper for Lemma 15.8.8: the Fitting ideals form an increasing sequence in the index. -/
lemma fittingIdeal_mono {k l : ℕ} (hkl : k ≤ l) :
    Fit[R]_(k)(M) ≤ Fit[R]_(l)(M) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  -- Compute both intrinsic Fitting ideals from one presentation and then compare minor sizes.
  rw [fittingIdeal_eq_presentationFittingIdeal (R := R) (M := M) k π hπ,
    fittingIdeal_eq_presentationFittingIdeal (R := R) (M := M) l π hπ,
    presentationFittingIdeal, presentationFittingIdeal]
  exact
    (Matrix.minorIdeal_antitone
      (fun i x ↦ x.1 i : Matrix (Fin n) (LinearMap.ker π) R))
      (Nat.sub_le_sub_left hkl n)

-- Proof sketch: clause (2) is equivalent to clause (3) because Fitting ideals form an increasing
-- sequence. For `(1) → (2)`, localize on a standard-open cover on which `M` is free of rank `r`,
-- use the explicit computation of Fitting ideals for a free module, and descend the equalities by
-- base change. For `(2) → (1)`, use the local generation criterion coming from the previous lemma
-- to reduce locally to a presentation by `r` generators; the vanishing of `Fit_{r-1}(M)` then
-- forces the presentation matrix to vanish, so the localized module is free of rank `r`.
/-- Lemma 15.8.8: for a finite `R`-module `M` and `r : ℕ`, the following are equivalent: `M` is
finite locally free of rank `r`; `Fit_{r-1}(M) = 0` (with the convention `Fit_{-1}(M) = 0`) and
`Fit_r(M) = R`; and `Fit_k(M) = 0` for `k < r` while `Fit_k(M) = R` for `k ≥ r`. -/
theorem finiteLocallyFreeOfRank_tfae_fittingIdeal_conditions (r : ℕ) :
    List.TFAE
      [ Module.FiniteLocallyFreeOfRank R M r
      , precedingFittingIdeal R M r = ⊥ ∧ Fit[R]_(r)(M) = ⊤
      , (∀ k, k < r → Fit[R]_(k)(M) = ⊥) ∧ ∀ k, r ≤ k → Fit[R]_(k)(M) = ⊤
      ] := by
  -- Route correction: use the existing base-change owner theorem for `1 → 2`, the away-local
  -- generation criterion from Lemma `15.8.7` for `2 → 1`, and monotonicity for `2 ↔ 3`.
  tfae_have 1 → 2 := by
    intro hloc
    rcases Module.FiniteLocallyFreeOfRank.exists_standardOpen_cover
        (R := R) (M := M) (r := r) with ⟨s, hs_span, hs_local⟩
    have hprev_map :
        ∀ q : PrimeSpectrum R,
          Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal))
            (precedingFittingIdeal R M r) = ⊥ := by
      intro q
      classical
      have hnot_subset : ¬ s ⊆ q.asIdeal := by
        intro hsq
        have hspan_le : Ideal.span s ≤ q.asIdeal := Ideal.span_le.2 hsq
        have htop_le : (⊤ : Ideal R) ≤ q.asIdeal := by
          simpa [hs_span] using hspan_le
        exact (Ideal.IsPrime.ne_top (I := q.asIdeal) inferInstance) (top_le_iff.mp htop_le)
      obtain ⟨f, hfs, hfq⟩ : ∃ f : R, f ∈ s ∧ f ∉ q.asIdeal := by
        simpa [Set.subset_def] using hnot_subset
      rcases hs_local f hfs with ⟨e⟩
      have hprev_away :
          Ideal.map (algebraMap R (Localization.Away f))
            (precedingFittingIdeal R M r) = ⊥ := by
        cases r with
        | zero =>
            -- In rank `0`, the predecessor ideal is already `⊥` before localizing.
            simp
        | succ r' =>
            -- Below the local free rank, the preceding Fitting ideal vanishes after localizing.
            simpa [precedingFittingIdeal_succ] using
              (fittingIdeal_map_away_eq_zero_or_top_of_linearEquiv_fin
                (R := R) (M := M) (r := r' + 1) (f := f) e r')
      have hfCompl : f ∈ q.asIdeal.primeCompl := by
        simpa using hfq
      let β : Localization.Away f →+* Localization.AtPrime q.asIdeal :=
        Localization.awayLift (algebraMap R (Localization.AtPrime q.asIdeal)) f
          (IsLocalization.map_units (Localization.AtPrime q.asIdeal) ⟨f, hfCompl⟩)
      have hcomp :
          β.comp (algebraMap R (Localization.Away f)) =
            algebraMap R (Localization.AtPrime q.asIdeal) := by
        ext x
        -- The away lift is characterized by agreeing with the original map on `R`.
        simp [β, Localization.awayLift]
      calc
        Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal))
            (precedingFittingIdeal R M r) =
            Ideal.map (β.comp (algebraMap R (Localization.Away f)))
              (precedingFittingIdeal R M r) := by
                rw [hcomp]
        _ = Ideal.map β
              (Ideal.map (algebraMap R (Localization.Away f))
                (precedingFittingIdeal R M r)) := by
                rw [Ideal.map_map]
        _ = ⊥ := by
              simpa [hprev_away]
    have hfit_map :
        ∀ (m : Ideal R) (_ : m.IsMaximal),
          Ideal.map (algebraMap R (Localization.AtPrime m))
            (Fit[R]_(r)(M)) = ⊤ := by
      intro m hm
      classical
      let q : PrimeSpectrum R := ⟨m, hm.isPrime⟩
      have hnot_subset : ¬ s ⊆ m := by
        intro hsm
        have hspan_le : Ideal.span s ≤ m := Ideal.span_le.2 hsm
        have htop_le : (⊤ : Ideal R) ≤ m := by
          simpa [hs_span] using hspan_le
        exact hm.ne_top (top_le_iff.mp htop_le)
      obtain ⟨f, hfs, hfm⟩ : ∃ f : R, f ∈ s ∧ f ∉ m := by
        simpa [Set.subset_def] using hnot_subset
      rcases hs_local f hfs with ⟨e⟩
      have hfit_away :
          Ideal.map (algebraMap R (Localization.Away f)) (Fit[R]_(r)(M)) = ⊤ := by
        -- At the local free rank, the away-local Fitting ideal is the unit ideal.
        simpa using
          (fittingIdeal_map_away_eq_zero_or_top_of_linearEquiv_fin
            (R := R) (M := M) (r := r) (f := f) e r)
      have hfCompl : f ∈ m.primeCompl := by
        simpa using hfm
      let β : Localization.Away f →+* Localization.AtPrime m :=
        Localization.awayLift (algebraMap R (Localization.AtPrime m)) f
          (IsLocalization.map_units (Localization.AtPrime m) ⟨f, hfCompl⟩)
      have hcomp :
          β.comp (algebraMap R (Localization.Away f)) =
            algebraMap R (Localization.AtPrime m) := by
        ext x
        -- The away lift again agrees with the ambient localization map on `R`.
        simp [β, Localization.awayLift]
      calc
        Ideal.map (algebraMap R (Localization.AtPrime m)) (Fit[R]_(r)(M)) =
            Ideal.map (β.comp (algebraMap R (Localization.Away f))) (Fit[R]_(r)(M)) := by
              rw [hcomp]
        _ = Ideal.map β (Ideal.map (algebraMap R (Localization.Away f)) (Fit[R]_(r)(M))) := by
              rw [Ideal.map_map]
        _ = ⊤ := by
              simpa [hfit_away, Ideal.map_top]
    refine
      ⟨ideal_eq_bot_of_localizedAtPrime_map_eq_bot
        (A := R) (J := precedingFittingIdeal R M r) hprev_map, ?_⟩
    -- The unit ideal is detected after localizing at all maximal ideals.
    refine Ideal.eq_of_localization_maximal fun m hm ↦ ?_
    simpa [Ideal.map_top] using hfit_map m hm
  tfae_have 2 → 1 := by
    intro h
    classical
    let s : Set R := {f | Nonempty ((LocalizedModule.Away f M) ≃ₗ[Localization.Away f]
      (Fin r → Localization.Away f))}
    have hs_cover : (⨆ f ∈ s, PrimeSpectrum.basicOpen f) = ⊤ := by
      apply SetLike.ext'
      change (↑(⨆ f ∈ s, PrimeSpectrum.basicOpen f) : Set (PrimeSpectrum R)) = Set.univ
      rw [Set.eq_univ_iff_forall]
      intro p
      letI : p.asIdeal.IsPrime := p.2
      rcases exists_away_linearEquiv_fin_of_fitting_conditions_at_prime
          (R := R) (M := M) r h.1 h.2 p.asIdeal with ⟨f, hfp, he⟩
      have hfs : f ∈ s := he
      have hp_basic : p ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
        simpa [PrimeSpectrum.mem_basicOpen] using hfp
      exact
        (show (PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum R)) ≤
            ⨆ t ∈ s, PrimeSpectrum.basicOpen t from
            le_iSup_of_le f <| le_iSup_of_le hfs le_rfl) hp_basic
    have hs_span : Ideal.span s = ⊤ :=
      PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp hs_cover
    -- Package the primewise away-trivializations into the owner cover for finite local freeness.
    exact ⟨s, hs_span, fun f hf ↦ hf⟩
  tfae_have 2 → 3 := by
    intro h
    refine ⟨?_, ?_⟩
    · intro k hk
      cases r with
      | zero =>
          exact (Nat.not_lt_zero _ hk).elim
      | succ r' =>
          have hprev' : Fit[R]_(r')(M) = ⊥ := by
            simpa [precedingFittingIdeal_succ] using h.1
          have hle : Fit[R]_(k)(M) ≤ Fit[R]_(r')(M) :=
            fittingIdeal_mono (R := R) (M := M) (Nat.le_of_lt_succ hk)
          exact le_antisymm (by simpa [hprev'] using hle) bot_le
    · intro k hk
      have hle : Fit[R]_(r)(M) ≤ Fit[R]_(k)(M) :=
        fittingIdeal_mono (R := R) (M := M) hk
      exact top_le_iff.mp (by simpa [h.2] using hle)
  tfae_have 3 → 2 := by
    intro h
    refine ⟨?_, h.2 r le_rfl⟩
    cases r with
    | zero =>
        simpa using (precedingFittingIdeal_zero (R := R) (M := M))
    | succ r =>
        simpa using h.1 r (Nat.lt_succ_self r)
  tfae_finish

end

end
