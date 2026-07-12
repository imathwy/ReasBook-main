import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap09.Lemma_9_21_5
import StacksProject_2024.Chap11.Definition_11_8_1
import StacksProject_2024.Chap11.Lemma_11_5_1
import StacksProject_2024.Chap11.Lemma_11_4_2
import StacksProject_2024.Chap11.Lemma_11_4_3
import StacksProject_2024.Chap11.Lemma_11_7_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/- Domain-style sampling for Lemma 11.8.6:
- primary domain: finite-dimensional central simple algebras and their splitting criteria;
- sampled owner declarations:
  `CSA.IsSplitBy`,
  `CSA.baseChange`,
  `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`,
  `CSA.finrank_isSquare`;
- best owner abstraction: the numbered TFAE statement is `source-facing` on an arbitrary
  `k`-algebra `A`, while the canonical owner for the splitting clauses is `CSA k`;
- primitive data: for the main TFAE, only the ambient `k`-algebra structure on `A`; for the
  companion statements below, only a representative `A : CSA k`;
- derived API: the algebraic-closure, separable-closure, and finite-Galois splitting statements on
  `CSA`; the degree API belongs upstream with `CSA.finrank_isSquare` rather than in this later
  TFAE file.

Source/core/bridge triage:
- `source-facing`: `finite_central_simple_tfae`;
- `core/canonical`: `CSA k` together with `CSA.IsSplitBy`;
- `bridge/view`: the owner-level companion splitness theorems below, which package the explicit
  matrix-algebra clauses of the TFAE in the canonical `IsSplitBy` language. -/

/-- Helper for Lemma 11.8.6: a matrix splitting witness over `AlgebraicClosure k` makes the
upstairs tensor product finite-dimensional, central, and simple over `AlgebraicClosure k`. -/
lemma split_over_algebraicClosure_implies_upstairs_finite_central_simple
    (h :
      ∃ n : ℕ, n ≠ 0 ∧ Nonempty
        ((A ⊗[k] AlgebraicClosure k) ≃ₐ[AlgebraicClosure k]
          Matrix (Fin n) (Fin n) (AlgebraicClosure k))) :
    FiniteDimensional (AlgebraicClosure k) (A ⊗[k] AlgebraicClosure k) ∧
      Algebra.IsCentral (AlgebraicClosure k) (A ⊗[k] AlgebraicClosure k) ∧
      IsSimpleRing (A ⊗[k] AlgebraicClosure k) := by
  rcases h with ⟨n, hn, ⟨e⟩⟩
  letI : NeZero n := ⟨hn⟩
  -- First transport finite-dimensionality and centrality back from the matrix algebra model.
  have hfinite :
      FiniteDimensional (AlgebraicClosure k) (A ⊗[k] AlgebraicClosure k) := by
    exact e.symm.toLinearEquiv.finiteDimensional
  have hcentral :
      Algebra.IsCentral (AlgebraicClosure k) (A ⊗[k] AlgebraicClosure k) := by
    letI :
        Algebra.IsCentral (AlgebraicClosure k)
          (Matrix (Fin n) (Fin n) (AlgebraicClosure k)) := inferInstance
    exact
      Algebra.IsCentral.of_algEquiv
        (K := AlgebraicClosure k)
        (D := Matrix (Fin n) (Fin n) (AlgebraicClosure k))
        (A := A ⊗[k] AlgebraicClosure k) e.symm
  -- Then transport simplicity along the same algebra equivalence.
  have hsimple :
      IsSimpleRing (A ⊗[k] AlgebraicClosure k) := by
    have hMatrix :
        IsSimpleRing (Matrix (Fin n) (Fin n) (AlgebraicClosure k)) :=
      IsSimpleRing.matrix (Fin n) (AlgebraicClosure k)
    exact IsSimpleRing.of_ringEquiv e.symm.toRingEquiv hMatrix
  exact ⟨hfinite, hcentral, hsimple⟩

/-- Helper for Lemma 11.8.6: a matrix splitting witness over `AlgebraicClosure k` already forces
`A` to be finite-dimensional over `k`; the remaining reverse-direction work is only simplicity and
centrality descent. -/
lemma split_over_algebraicClosure_implies_finiteDimensional
    (h :
      ∃ n : ℕ, n ≠ 0 ∧ Nonempty
        ((A ⊗[k] AlgebraicClosure k) ≃ₐ[AlgebraicClosure k]
          Matrix (Fin n) (Fin n) (AlgebraicClosure k))) :
    FiniteDimensional k A := by
  rcases split_over_algebraicClosure_implies_upstairs_finite_central_simple (k := k) (A := A) h with
    ⟨hfiniteUpstairs, _, _⟩
  letI : FiniteDimensional (AlgebraicClosure k) (A ⊗[k] AlgebraicClosure k) := hfiniteUpstairs
  -- Reorder the tensor factors so the faithful-flat finiteness descent theorem applies directly.
  have hfiniteComm :
      FiniteDimensional (AlgebraicClosure k) ((AlgebraicClosure k) ⊗[k] A) := by
    exact
      (Algebra.TensorProduct.comm k (AlgebraicClosure k) A).toLinearEquiv.finiteDimensional
  letI : FiniteDimensional (AlgebraicClosure k) ((AlgebraicClosure k) ⊗[k] A) := hfiniteComm
  have hff :
      (algebraMap k (AlgebraicClosure k)).FaithfullyFlat := by
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  letI : Module.FaithfullyFlat k (AlgebraicClosure k) :=
    (RingHom.faithfullyFlat_algebraMap_iff :
      (algebraMap k (AlgebraicClosure k)).FaithfullyFlat ↔
        Module.FaithfullyFlat k (AlgebraicClosure k)).mp hff
  letI : Module.Finite (AlgebraicClosure k) ((AlgebraicClosure k) ⊗[k] A) := inferInstance
  letI : Module.Finite k A :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat (AlgebraicClosure k)
  -- Over a field, finite generation is equivalent to finite-dimensionality.
  infer_instance

/-- Helper for Lemma 11.8.6: if a matrix algebra is central over `k`, then its division
coefficients are already central over `k`. -/
lemma matrix_central_implies_division_central (n : ℕ) [NeZero n] (D : Type w)
    [DivisionRing D] [Algebra k D]
    [Algebra.IsCentral k (Matrix (Fin n) (Fin n) D)] :
    Algebra.IsCentral k D := by
  -- Move a central scalar matrix back to a diagonal coefficient.
  refine ⟨fun x hx ↦ ?_⟩
  have hxM :
      Matrix.scalar (Fin n) x ∈
        (Subalgebra.center k D).map (Matrix.scalarAlgHom (Fin n) k) := by
    exact ⟨x, hx, rfl⟩
  rw [← subalgebraCenter_eq_scalarAlgHom_map] at hxM
  obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff k).1 hxM
  rw [Algebra.mem_bot]
  refine ⟨a, ?_⟩
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  simpa [i] using (congrArg (fun M : Matrix (Fin n) (Fin n) D ↦ M i i) ha).symm

/-- Helper for Lemma 11.8.6: the textbook center-and-ideal clause is equivalent to finite
central simplicity. -/
lemma finite_central_simple_iff_center_bot_and_two_sided_ideal_trivial :
    (FiniteDimensional k A ∧ Algebra.IsCentral k A ∧ IsSimpleRing A) ↔
      (FiniteDimensional k A ∧ Subalgebra.center k A = ⊥ ∧
        Nontrivial A ∧ ∀ I : Ideal A, I.IsTwoSided → I = ⊥ ∨ I = ⊤) := by
  constructor
  · rintro ⟨hfinite, hcentral, hsimple⟩
    letI : Algebra.IsCentral k A := hcentral
    letI : IsSimpleRing A := hsimple
    -- Read centrality as equality of the center with the bottom subalgebra, then package the
    -- standard simple-ring ideal dichotomy.
    refine ⟨hfinite, Algebra.IsCentral.center_eq_bot (K := k) (D := A), inferInstance, ?_⟩
    intro I hI
    rcases IsSimpleRing.simple.eq_bot_or_eq_top I.toTwoSided with hIbot | hItop
    · left
      simpa using congrArg TwoSidedIdeal.asIdeal hIbot
    · right
      simpa using congrArg TwoSidedIdeal.asIdeal hItop
  · rintro ⟨hfinite, hcenter, hnontrivial, htrivial⟩
    letI : Nontrivial A := hnontrivial
    have hcentral : Algebra.IsCentral k A := by
      -- Rebuild the centrality instance directly from the center equality.
      refine ⟨fun x hx ↦ ?_⟩
      have hxbot : x ∈ (⊥ : Subalgebra k A) := by
        simpa [hcenter] using hx
      simpa [Algebra.mem_bot] using hxbot
    have hsimple : IsSimpleRing A := by
      -- Convert the source-facing ideal statement into the owner theorem
      -- `IsSimpleRing.of_eq_bot_or_eq_top`.
      refine IsSimpleRing.of_eq_bot_or_eq_top fun I ↦ ?_
      rcases htrivial I.asIdeal inferInstance with hIbot | hItop
      · left
        cases hIbot
        simp
      · right
        cases hItop
        simp
    exact ⟨hfinite, hcentral, hsimple⟩

/-- Helper for Lemma 11.8.6: the matrix-over-division-algebra clause is equivalent to finite
central simplicity. -/
lemma finite_central_simple_iff_matrix_division_form :
    (FiniteDimensional k A ∧ Algebra.IsCentral k A ∧ IsSimpleRing A) ↔
      (∃ (n : ℕ), n ≠ 0 ∧ ∃ (D : Type w) (_ : DivisionRing D) (_ : Algebra k D)
        (_ : FiniteDimensional k D) (_ : Algebra.IsCentral k D),
        Nonempty (A ≃ₐ[k] Matrix (Fin n) (Fin n) D)) := by
  constructor
  · rintro ⟨hfinite, hcentral, hsimple⟩
    letI : FiniteDimensional k A := hfinite
    letI : Algebra.IsCentral k A := hcentral
    letI : IsSimpleRing A := hsimple
    letI : IsArtinianRing A := IsArtinianRing.of_finite k A
    -- Apply the finite-dimensional Wedderburn theorem, then recover centrality of the
    -- coefficient division algebra from the matrix algebra model.
    obtain ⟨n, hn, D, hDdiv, hDalg, hDfinite, ⟨e⟩⟩ :=
      IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k A
    letI : NeZero n := hn
    letI : DivisionRing D := hDdiv
    letI : Algebra k D := hDalg
    letI : Module.Finite k D := hDfinite
    letI : FiniteDimensional k D := inferInstance
    letI : Algebra.IsCentral k (Matrix (Fin n) (Fin n) D) :=
      Algebra.IsCentral.of_algEquiv k A _ e
    letI : Algebra.IsCentral k D := matrix_central_implies_division_central (k := k) n D
    exact ⟨n, hn, D, inferInstance, inferInstance, inferInstance, inferInstance, ⟨e⟩⟩
  · rintro ⟨n, hn, D, hDdiv, hDalg, hDfinite, hDcentral, ⟨e⟩⟩
    letI : DivisionRing D := hDdiv
    letI : Algebra k D := hDalg
    letI : FiniteDimensional k D := hDfinite
    letI : Algebra.IsCentral k D := hDcentral
    letI : NeZero n := ⟨hn⟩
    -- Transport finite-dimensionality, centrality, and simplicity back from the matrix algebra.
    have hfinite : FiniteDimensional k A := by
      exact e.symm.toLinearEquiv.finiteDimensional
    have hcentral : Algebra.IsCentral k A := by
      letI : Algebra.IsCentral k (Matrix (Fin n) (Fin n) D) := inferInstance
      exact Algebra.IsCentral.of_algEquiv k (Matrix (Fin n) (Fin n) D) A e.symm
    have hsimple : IsSimpleRing A := by
      have hmatrix : IsSimpleRing (Matrix (Fin n) (Fin n) D) :=
        IsSimpleRing.matrix (Fin n) D
      exact IsSimpleRing.of_ringEquiv e.symm.toRingEquiv hmatrix
    exact ⟨hfinite, hcentral, hsimple⟩

/-- Helper for Lemma 11.8.6: descending simplicity from a split algebra over
`AlgebraicClosure k` reduces to showing that every downstairs two-sided ideal becomes trivial
after scalar extension. -/
lemma tensor_baseChange_eq_bot_or_eq_top_of_two_sided
    (h :
      ∃ n : ℕ, n ≠ 0 ∧ Nonempty
        ((A ⊗[k] AlgebraicClosure k) ≃ₐ[AlgebraicClosure k]
          Matrix (Fin n) (Fin n) (AlgebraicClosure k)))
    (I : Ideal A) (hI : I.IsTwoSided) :
    (((I.restrictScalars k).baseChange (AlgebraicClosure k) :
      Submodule (AlgebraicClosure k) ((AlgebraicClosure k) ⊗[k] A)) = ⊥) ∨
      (((I.restrictScalars k).baseChange (AlgebraicClosure k) :
        Submodule (AlgebraicClosure k) ((AlgebraicClosure k) ⊗[k] A)) = ⊤) := by
  let K := AlgebraicClosure k
  rcases split_over_algebraicClosure_implies_upstairs_finite_central_simple (k := k) (A := A) h with
    ⟨_, _, hsimpleUpstairs⟩
  letI : IsSimpleRing (K ⊗[k] A) := hsimpleUpstairs
  let W : Submodule (K ⊗[k] Kᵐᵒᵖ) (K ⊗[k] A) :=
    Subbimodule.mk (Ideal.map (includeRight : A →ₐ[k] K ⊗[k] A) I).toAddSubmonoid
      (fun a {x} hx ↦ by
        -- Left multiplication preserves the ideal generated by `includeRight(I)`.
        exact Ideal.mul_mem_left _ _ hx)
      (fun a {x} hx ↦ by
        -- Right multiplication reduces to two-sidedness of the original ideal.
        rcases Ideal.map_includeRight_eq (R := k) (A := K) (B := A) I ▸ hx with hx
        rw [two_sided_submodule_eq_baseChange_comap_one_tmul (k := k) (K := K) (V := A) W] at hx
        rw [Submodule.baseChange_eq_span] at hx
        refine Submodule.span_induction ?hz ?h0 ?hadd ?hsmul hx
        · rintro z ⟨y, hy, rfl⟩
          change op a • ((1 : K) ⊗ₜ[k] y) ∈
            ((I.restrictScalars k).baseChange K : Submodule K (K ⊗[k] A))
          have hy' : a.unop * y ∈ I := hI.mul_mem_left _ hy
          simpa [TensorProduct.smul_tmul'] using
            Submodule.tmul_mem_baseChange_of_mem (p := I.restrictScalars k) (a := (1 : K)) hy'
        · simpa using (show (0 : K ⊗[k] A) ∈
            ((I.restrictScalars k).baseChange K : Submodule K (K ⊗[k] A)) from
            Submodule.zero_mem _)
        · intro x y hx hy
          exact Submodule.add_mem _ hx hy
        · intro r x hx
          exact Submodule.smul_mem _ r hx)
  have hbase :
      ((I.restrictScalars k).baseChange K : Submodule K (K ⊗[k] A)) =
        (Ideal.map (includeRight : A →ₐ[k] K ⊗[k] A) I).restrictScalars K := by
    -- The base-changed submodule is exactly the image ideal generated by `includeRight(I)`.
    simpa [W] using
      (Ideal.map_includeRight_eq (R := k) (A := K) (B := A) I).symm
  rcases IsSimpleRing.simple.eq_bot_or_eq_top
      (Ideal.map (includeRight : A →ₐ[k] K ⊗[k] A) I).toTwoSided with hbot | htop
  · left
    -- Transport the upstairs ideal dichotomy back to the exact base-change spelling used later.
    simpa [hbase] using congrArg TwoSidedIdeal.asIdeal hbot
  · right
    -- Transport the upstairs ideal dichotomy back to the exact base-change spelling used later.
    simpa [hbase] using congrArg TwoSidedIdeal.asIdeal htop

/-- Helper for Chap11 Lemma 11 8 6: the tensor image of the bottom subalgebra is exactly the
left scalar range inside `K ⊗[k] A`. -/
lemma tensorMap_botRange_eq_includeLeftRange
    (K : Type*) [Field K] [Algebra k K] :
    (Algebra.TensorProduct.map (AlgHom.id k K) (⊥ : Subalgebra k A).val).range =
      (Algebra.TensorProduct.includeLeft : K →ₐ[k] K ⊗[k] A).range := by
  -- Rewrite the tensor image of `⊥` using the standard tensor-product range formula.
  rw [Algebra.TensorProduct.map_range]
  have hbot :
      ((Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).comp
          (⊥ : Subalgebra k A).val).range =
        (⊥ : Subalgebra k (K ⊗[k] A)) := by
    rw [AlgHom.range_comp, Subalgebra.range_val, Algebra.map_bot]
  -- The right-factor contribution is trivial, so only the left scalar range remains.
  rw [hbot, sup_bot_eq]
  simp

/-- Helper for Lemma 11.8.6: a split matrix model over `AlgebraicClosure k` collapses the center
of a finite-dimensional simple `k`-algebra to `k`-dimension one. -/
lemma center_finrank_eq_one_of_split_algebraicClosure
    [FiniteDimensional k A] [IsSimpleRing A]
    (h :
      ∃ n : ℕ, n ≠ 0 ∧ Nonempty
        ((A ⊗[k] AlgebraicClosure k) ≃ₐ[AlgebraicClosure k]
          Matrix (Fin n) (Fin n) (AlgebraicClosure k))) :
    Module.finrank k (Subalgebra.center k A) = 1 := by
  let K := AlgebraicClosure k
  let C := Subalgebra.center k A
  rcases split_over_algebraicClosure_implies_upstairs_finite_central_simple (k := k) (A := A) h with
    ⟨_, hcentralUpstairs, _⟩
  letI : Algebra.IsCentral K (K ⊗[k] A) := hcentralUpstairs
  have hcenterField : FiniteDimensional k C ∧ IsField C :=
    center_finiteFieldExtension (k := k) (A := A)
  letI : FiniteDimensional k C := hcenterField.1
  let ι : C →ₐ[k] K ⊗[k] A := Algebra.TensorProduct.map (AlgHom.id k K) C.val
  have hιinj :
      Function.Injective
        (TensorProduct.map (LinearMap.id : K →ₗ[k] K) C.val.toLinearMap) := by
    -- Flatness of both tensor factors makes the tensorized center inclusion injective.
    simpa using TensorProduct.map_injective_of_flat_flat
      (LinearMap.id : K →ₗ[k] K) C.val.toLinearMap (fun _ _ hxy ↦ hxy) Subtype.val_injective
  have hrange :
      ι.range = (Algebra.TensorProduct.includeLeft : K →ₐ[k] K ⊗[k] A).range := by
    -- Compare the tensorized center with the centralizer of the right factor.
    have hmem :
        Subalgebra.centralizer k
          (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).range =
          (Algebra.TensorProduct.includeLeft : K →ₐ[k] K ⊗[k] A).range := by
      rw [Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct k K A]
      rw [Algebra.IsCentral.center_eq_bot, tensorMap_botRange_eq_includeLeftRange (k := k) (A := A)]
    simpa [ι] using hmem
  have hfinrankRange :
      Module.finrank K ι.range = 1 := by
    -- The left scalar range is one-dimensional because `includeLeft` is injective.
    rw [hrange]
    simpa using LinearMap.finrank_range_of_inj
      (Algebra.TensorProduct.includeLeft : K →ₐ[k] K ⊗[k] A).toLinearMap
      (Algebra.TensorProduct.includeLeft : K →ₐ[k] K ⊗[k] A).injective
  have hfinrankTensorCenter :
      Module.finrank K (K ⊗[k] C) = 1 := by
    -- Injectivity identifies `K ⊗[k] C` with its range inside `K ⊗[k] A`.
    simpa [ι] using (LinearMap.finrank_range_of_inj
      (TensorProduct.map (LinearMap.id : K →ₗ[k] K) C.val.toLinearMap) hιinj).trans hfinrankRange
  -- Descend the one-dimensional base change back to the original center over `k`.
  calc
    Module.finrank k C = Module.finrank K (K ⊗[k] C) := by
      simpa using (Module.finrank_baseChange (R := k) (A := K) (M := C)).symm
    _ = 1 := hfinrankTensorCenter

/-- Helper for Lemma 11.8.6: descending simplicity from a split algebra over
`AlgebraicClosure k` reduces to showing that every downstairs two-sided ideal becomes trivial
after scalar extension. -/
lemma split_over_algebraicClosure_implies_two_sided_ideal_trivial
    (h :
      ∃ n : ℕ, n ≠ 0 ∧ Nonempty
        ((A ⊗[k] AlgebraicClosure k) ≃ₐ[AlgebraicClosure k]
          Matrix (Fin n) (Fin n) (AlgebraicClosure k))) :
    ∀ I : Ideal A, I.IsTwoSided → I = ⊥ ∨ I = ⊤ := by
  let K := AlgebraicClosure k
  have hfinite : FiniteDimensional k A :=
    split_over_algebraicClosure_implies_finiteDimensional (k := k) (A := A) h
  letI : FiniteDimensional k A := hfinite
  have hff :
      (algebraMap k K).FaithfullyFlat := by
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  letI : Module.FaithfullyFlat k K :=
    (RingHom.faithfullyFlat_algebraMap_iff :
      (algebraMap k K).FaithfullyFlat ↔ Module.FaithfullyFlat k K).mp hff
  intro I hI
  rcases tensor_baseChange_eq_bot_or_eq_top_of_two_sided (k := k) (A := A) h I hI with
    hBaseBot | hBaseTop
  · left
    ext x
    constructor
    · intro hx
      -- If the base change is zero, faithful flatness forces every generator `1 ⊗ x` to vanish.
      have hxBase :
          (1 : K) ⊗ₜ[k] x ∈ ((I.restrictScalars k).baseChange K :
            Submodule K (K ⊗[k] A)) :=
        Submodule.tmul_mem_baseChange_of_mem (p := I.restrictScalars k) (a := (1 : K)) hx
      rw [hBaseBot] at hxBase
      have hxZero : (1 : K) ⊗ₜ[k] x = 0 := by simpa using hxBase
      have hmk_inj :
          Function.Injective (TensorProduct.mk k K A 1) :=
        Module.FaithfullyFlat.tensorProduct_mk_injective (A := k) (B := K) A
      have hx' : x = 0 := hmk_inj (by simpa using hxZero)
      simpa [Ideal.mem_bot, hx']
    · intro hx
      simpa using hx
  · right
    -- If the base change is all of `K ⊗ A`, then dimension comparison forces `I = ⊤`.
    have hfinI :
        Module.finrank k I = Module.finrank k A := by
      calc
        Module.finrank k I
            = Module.finrank K (K ⊗[k] ↥(I.restrictScalars k)) := by
                simpa using
                  (Module.finrank_baseChange (R := k) (A := K)
                    (M := ↥(I.restrictScalars k))).symm
        _ = Module.finrank K ((I.restrictScalars k).baseChange K) := by
              symm
              exact (Submodule.toBaseChange.toLinearEquiv
                (A := K) (p := I.restrictScalars k)).finrank_eq
        _ = Module.finrank K (K ⊗[k] A) := by simpa [hBaseTop]
        _ = Module.finrank k A := by
              simpa using (Module.finrank_baseChange (R := k) (A := K) (M := A))
    exact Submodule.eq_top_of_finrank_eq (by simpa using hfinI)

/-- Helper for Lemma 11.8.6: a split matrix model over `AlgebraicClosure k` forces `A` to be
simple once two-sided ideals are descended from the scalar extension. -/
lemma split_over_algebraicClosure_implies_isSimpleRing
    (h :
      ∃ n : ℕ, n ≠ 0 ∧ Nonempty
        ((A ⊗[k] AlgebraicClosure k) ≃ₐ[AlgebraicClosure k]
          Matrix (Fin n) (Fin n) (AlgebraicClosure k))) :
    IsSimpleRing A := by
  letI : Nontrivial A := inferInstance
  -- Package the descended ideal-triviality statement in the canonical `IsSimpleRing` API.
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I ↦ ?_
  rcases split_over_algebraicClosure_implies_two_sided_ideal_trivial (k := k) (A := A) h
      I.asIdeal I.isTwoSided with hIbot | hItop
  · left
    simpa using congrArg Ideal.toTwoSided hIbot
  · right
    simpa using congrArg Ideal.toTwoSided hItop

/-- Helper for Lemma 11.8.6: once `A` is known finite-dimensional and simple, the center can be
collapsed from the algebraic-closure splitting witness by a finite-dimensional center comparison.
-/
lemma split_over_algebraicClosure_implies_isCentral
    [FiniteDimensional k A] [IsSimpleRing A]
    (h :
      ∃ n : ℕ, n ≠ 0 ∧ Nonempty
        ((A ⊗[k] AlgebraicClosure k) ≃ₐ[AlgebraicClosure k]
          Matrix (Fin n) (Fin n) (AlgebraicClosure k))) :
    Algebra.IsCentral k A := by
  let C := Subalgebra.center k A
  have hfinrankC : Module.finrank k C = 1 :=
    center_finrank_eq_one_of_split_algebraicClosure (k := k) (A := A) h
  have hbij : Function.Bijective (algebraMap k C) :=
    Module.Free.bijective_algebraMap_of_finrank_eq_one hfinrankC
  -- Every central element comes from the scalar image because the center has `k`-dimension one.
  refine ⟨fun x hx ↦ ?_⟩
  obtain ⟨a, ha⟩ := hbij.2 ⟨x, hx⟩
  rw [Algebra.mem_bot]
  refine ⟨a, ?_⟩
  exact congrArg Subtype.val ha

end

section

open JacobsonNoether
open Subalgebra

variable {k : Type u} [Field k]
variable {D : Type v} [DivisionRing D] [Algebra k D] [FiniteDimensional k D]
  [Algebra.IsCentral k D]

/-- Helper for Chap11 Lemma 11 8 6: inverses stay in the centralizer of a subalgebra. -/
lemma inv_mem_centralizer_of_mem_centralizer (K : Subalgebra k D) {x : D}
    (hx : x ∈ Subalgebra.centralizer k (K : Set D)) :
    x⁻¹ ∈ Subalgebra.centralizer k (K : Set D) := by
  -- The centralizer is closed under inversion because commuting with `x` is equivalent to
  -- commuting with `x⁻¹`.
  rw [Subalgebra.mem_centralizer_iff] at hx ⊢
  intro y hy
  by_cases hx0 : x = 0
  · simp [hx0]
  · calc
      y * x⁻¹ = (x⁻¹ * x) * y * x⁻¹ := by rw [inv_mul_cancel₀ hx0, one_mul]
      _ = x⁻¹ * (x * y) * x⁻¹ := by simp [mul_assoc]
      _ = x⁻¹ * (y * x) * x⁻¹ := by rw [hx y hy]
      _ = x⁻¹ * y * (x * x⁻¹) := by simp [mul_assoc]
      _ = x⁻¹ * y := by rw [mul_inv_cancel₀ hx0, mul_one]

/-- Helper for Chap11 Lemma 11 8 6: choose a separable `k`-subfield of maximal `k`-dimension. -/
lemma exists_finrank_maximal_separable_subfield :
    ∃ K : Subalgebra k D, IsField K ∧ Algebra.IsSeparable k K ∧
      ∀ L : Subalgebra k D, IsField L → Algebra.IsSeparable k L →
        Module.finrank k L ≤ Module.finrank k K := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ K : Subalgebra k D, IsField K ∧ Algebra.IsSeparable k K ∧ Module.finrank k K = n
  have hbotField : IsField (⊥ : Subalgebra k D) := by
    -- The bottom subalgebra is canonically a copy of the base field.
    exact (Algebra.botEquiv k D).symm.toMulEquiv.isField (Field.toIsField k)
  have hbotSep : Algebra.IsSeparable k (⊥ : Subalgebra k D) := by
    -- Separability is preserved across the bottom-field equivalence.
    exact (AlgEquiv.Algebra.isSeparable_iff (Algebra.botEquiv k D)).2 inferInstance
  have hP : P 1 := by
    refine ⟨⊥, hbotField, hbotSep, ?_⟩
    simpa using (Subalgebra.finrank_bot : Module.finrank k (⊥ : Subalgebra k D) = 1)
  let n := Nat.findGreatest P (Module.finrank k D)
  have hnP : P n := by
    exact Nat.findGreatest_spec (Module.finrank_pos : 1 ≤ Module.finrank k D) hP
  rcases hnP with ⟨K, hKfield, hKsep, rfl⟩
  refine ⟨K, hKfield, hKsep, ?_⟩
  intro L hLfield hLsep
  have hbound : Module.finrank k L ≤ Module.finrank k D := by
    simpa using Submodule.finrank_le (Subalgebra.toSubmodule L)
  exact Nat.le_findGreatest hbound ⟨L, hLfield, hLsep, rfl⟩

/-- Helper for Chap11 Lemma 11 8 6: a commutative subfield lies inside its own centralizer. -/
lemma self_le_centralizer_of_isField
    (K : Subalgebra k D) (hKfield : IsField K) :
    K ≤ Subalgebra.centralizer k (K : Set D) := by
  -- Elements of a field subalgebra commute with every other element of that same field.
  intro x hx
  rw [Subalgebra.mem_centralizer_iff]
  intro y hy
  simpa using mul_comm (⟨x, hx⟩ : K) (⟨y, hy⟩ : K)

/-- Helper for Chap11 Lemma 11 8 6: the chosen subfield includes into its centralizer. -/
noncomputable def centralizerSubfieldInclusion
    (K : Subalgebra k D) (hKfield : IsField K) :
    K →ₐ[k] Subalgebra.centralizer k (K : Set D) :=
  Subalgebra.inclusion (self_le_centralizer_of_isField (k := k) (D := D) K hKfield)

/-- Helper for Chap11 Lemma 11 8 6: adjoining a centralizer element over `K` gives a canonical
`k`-algebra map back to the ambient division algebra. -/
noncomputable def adjoinRootToAmbient_of_centralizer_element
    (K : Subalgebra k D) (hKfield : IsField K) :
    let C := Subalgebra.centralizer k (K : Set D)
    letI : Field K := hKfield.toField
    letI : Algebra K C :=
      (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
    (x : C) → AdjoinRoot (minpoly K x) →ₐ[k] D :=
  let C := Subalgebra.centralizer k (K : Set D)
  letI : Field K := hKfield.toField
  letI : Algebra K C :=
    (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
  fun x ↦
    C.val.comp <|
      AlgHom.restrictScalars k <|
        AdjoinRoot.liftAlgHom (minpoly K x) (algebraMap K C) x (minpoly.aeval K x)

/-- Helper for Chap11 Lemma 11 8 6: the distinguished root of the simple extension is sent to the
chosen centralizer element. -/
lemma adjoinRootToAmbient_of_centralizer_element_root
    (K : Subalgebra k D) (hKfield : IsField K) :
    let C := Subalgebra.centralizer k (K : Set D)
    letI : Field K := hKfield.toField
    letI : Algebra K C :=
      (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
    ∀ x : C,
      adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x
          (AdjoinRoot.root (minpoly K x)) = x.1 := by
  let C := Subalgebra.centralizer k (K : Set D)
  letI : Field K := hKfield.toField
  letI : Algebra K C :=
    (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
  intro x
  -- The `AdjoinRoot` lift is defined by sending the distinguished root to `x`.
  simp [adjoinRootToAmbient_of_centralizer_element, AdjoinRoot.liftAlgHom_root]

/-- Helper for Chap11 Lemma 11 8 6: the simple-extension range still contains the original
subfield `K`. -/
lemma subfield_le_adjoinRoot_range_of_centralizer_element
    (K : Subalgebra k D) (hKfield : IsField K) :
    let C := Subalgebra.centralizer k (K : Set D)
    letI : Field K := hKfield.toField
    letI : Algebra K C :=
      (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
    ∀ x : C,
      K ≤ (adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range := by
  let C := Subalgebra.centralizer k (K : Set D)
  letI : Field K := hKfield.toField
  letI : Algebra K C :=
    (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
  intro x a ha
  refine ⟨algebraMap K (AdjoinRoot (minpoly K x)) ⟨a, ha⟩, ?_⟩
  -- Coefficients from `K` lie in the range by the defining formula of the lift.
  simp [adjoinRootToAmbient_of_centralizer_element]

/-- Helper for Chap11 Lemma 11 8 6: the chosen centralizer element itself belongs to the
simple-extension range in `D`. -/
lemma centralizer_element_mem_adjoinRoot_range_of_centralizer_element
    (K : Subalgebra k D) (hKfield : IsField K) :
    let C := Subalgebra.centralizer k (K : Set D)
    letI : Field K := hKfield.toField
    letI : Algebra K C :=
      (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
    ∀ x : C,
      x.1 ∈ (adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range := by
  let C := Subalgebra.centralizer k (K : Set D)
  letI : Field K := hKfield.toField
  letI : Algebra K C :=
    (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
  intro x
  refine ⟨AdjoinRoot.root (minpoly K x), ?_⟩
  -- The generator of the simple extension maps to `x`.
  simpa using
    adjoinRootToAmbient_of_centralizer_element_root (k := k) (D := D) K hKfield x

/-- Helper for Chap11 Lemma 11 8 6: a nonscalar centralizer element generates a strictly larger
subfield over `K`. -/
lemma adjoinRoot_range_strict_of_nontrivial_centralizer_element
    (K : Subalgebra k D) (hKfield : IsField K) :
    let C := Subalgebra.centralizer k (K : Set D)
    letI : Field K := hKfield.toField
    letI : Algebra K C :=
      (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
    ∀ x : C, x ∉ (⊥ : Subalgebra K C) →
      K < (adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range := by
  let C := Subalgebra.centralizer k (K : Set D)
  letI : Field K := hKfield.toField
  letI : Algebra K C :=
    (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
  intro x hx
  refine lt_of_le_of_ne
    (subfield_le_adjoinRoot_range_of_centralizer_element (k := k) (D := D) K hKfield x) ?_
  intro hEq
  have hxrange :
      x.1 ∈ (adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range :=
    centralizer_element_mem_adjoinRoot_range_of_centralizer_element
      (k := k) (D := D) K hKfield x
  have hxK : x.1 ∈ K := by
    simpa [hEq] using hxrange
  apply hx
  rw [Algebra.mem_bot]
  refine ⟨⟨x.1, hxK⟩, ?_⟩
  ext
  rfl

/-- Helper for Chap11 Lemma 11 8 6: the centralizer of a subfield is finite dimensional over that
subfield. -/
lemma finiteDimensional_centralizer_over_subfield
    (K : Subalgebra k D) (hKfield : IsField K) :
    let C := Subalgebra.centralizer k (K : Set D)
    letI : Field K := hKfield.toField
    letI : Algebra K C :=
      (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
    FiniteDimensional K C := by
  let C := Subalgebra.centralizer k (K : Set D)
  letI : Field K := hKfield.toField
  letI : FiniteDimensional k K := FiniteDimensional.of_injective K.val K.val_injective
  letI : Algebra K C :=
    (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
  letI : FiniteDimensional K D := FiniteDimensional.right K k D
  let iCD : C →ₗ[K] D where
    toFun := Subtype.val
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
  -- The centralizer is a `K`-subspace of the finite-dimensional `K`-vector space `D`.
  exact FiniteDimensional.of_injective iCD fun x y hxy ↦ Subtype.ext hxy

/-- Helper for Chap11 Lemma 11 8 6: the simple-extension map onto the ambient range is a
`k`-algebra equivalence. -/
noncomputable lemma adjoinRoot_range_algEquiv_of_centralizer_element
    (K : Subalgebra k D) (hKfield : IsField K) :
    let C := Subalgebra.centralizer k (K : Set D)
    letI : Field K := hKfield.toField
    letI : Algebra K C :=
      (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
    ∀ x : C,
      AdjoinRoot (minpoly K x) ≃ₐ[k]
        (adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range := by
  let C := Subalgebra.centralizer k (K : Set D)
  letI : Field K := hKfield.toField
  letI : Algebra K C :=
    (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
  letI : FiniteDimensional K C :=
    finiteDimensional_centralizer_over_subfield (k := k) (D := D) K hKfield
  letI : Algebra.IsAlgebraic K C := Algebra.IsAlgebraic.of_finite K C
  intro x
  let hxalg : IsAlgebraic K x := Algebra.IsAlgebraic.isAlgebraic (R := K) x
  letI : Fact (Irreducible (minpoly K x)) := ⟨minpoly.irreducible hxalg.isIntegral⟩
  let φx := adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x
  -- The range of an algebra hom from a field into a division ring is canonically equivalent to
  -- the source field.
  exact (Subalgebra.ofInjectiveField φx).restrictScalars k

/-- Helper for Chap11 Lemma 11 8 6: the transported simple-extension range is a field. -/
lemma adjoinRoot_range_isField_of_centralizer_element
    (K : Subalgebra k D) (hKfield : IsField K) :
    let C := Subalgebra.centralizer k (K : Set D)
    letI : Field K := hKfield.toField
    letI : Algebra K C :=
      (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
    ∀ x : C,
      IsField
        ((adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range) := by
  let C := Subalgebra.centralizer k (K : Set D)
  letI : Field K := hKfield.toField
  letI : Algebra K C :=
    (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
  intro x
  letI : FiniteDimensional K C :=
    finiteDimensional_centralizer_over_subfield (k := k) (D := D) K hKfield
  letI : Algebra.IsAlgebraic K C := Algebra.IsAlgebraic.of_finite K C
  let hxalg : IsAlgebraic K x := Algebra.IsAlgebraic.isAlgebraic (R := K) x
  letI : Fact (Irreducible (minpoly K x)) := ⟨minpoly.irreducible hxalg.isIntegral⟩
  let e :=
    adjoinRoot_range_algEquiv_of_centralizer_element (k := k) (D := D) K hKfield x
  -- Fieldness transfers across the range equivalence from the `AdjoinRoot` source.
  exact e.toMulEquiv.isField (Field.toIsField (AdjoinRoot (minpoly K x)))

/-- Helper for Chap11 Lemma 11 8 6: the transported simple-extension range is separable over `k`
once the chosen centralizer element is separable over `K`. -/
lemma adjoinRoot_range_isSeparable_of_centralizer_element
    (K : Subalgebra k D) (hKfield : IsField K) (hKsep : Algebra.IsSeparable k K) :
    let C := Subalgebra.centralizer k (K : Set D)
    letI : Field K := hKfield.toField
    letI : Algebra K C :=
      (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
    ∀ x : C, IsSeparable K x →
      Algebra.IsSeparable k
        ((adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range) := by
  let C := Subalgebra.centralizer k (K : Set D)
  letI : Field K := hKfield.toField
  letI : Algebra K C :=
    (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
  intro x hxsep
  let e :=
    adjoinRoot_range_algEquiv_of_centralizer_element (k := k) (D := D) K hKfield x
  let hxint : IsIntegral K x := IsSeparable.isIntegral hxsep
  letI : Fact (Irreducible (minpoly K x)) := ⟨minpoly.irreducible hxint⟩
  let y : AdjoinRoot (minpoly K x) := AdjoinRoot.root (minpoly K x)
  have hysep : IsSeparable K y := by
    -- The distinguished root has the same minimal polynomial as `x`.
    simpa [IsSeparable, AdjoinRoot.minpoly_root (minpoly.ne_zero hxint), minpoly.monic hxint]
      using hxsep
  have hsimple :
      Algebra.IsSeparable K K⟮y⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
      (F := K) (E := AdjoinRoot (minpoly K x))).2 hysep
  have htop : K⟮y⟯ = ⊤ := IntermediateField.adjoin_root_eq_top (p := minpoly K x)
  have hsourceK :
      Algebra.IsSeparable K (AdjoinRoot (minpoly K x)) := by
    have hsourceTop : Algebra.IsSeparable K (⊤ : IntermediateField K (AdjoinRoot (minpoly K x))) := by
      simpa [htop] using hsimple
    exact AlgEquiv.Algebra.isSeparable (IntermediateField.topEquiv :
      (⊤ : IntermediateField K (AdjoinRoot (minpoly K x))) ≃ₐ[K] AdjoinRoot (minpoly K x))
  let _ : Algebra.IsSeparable K (AdjoinRoot (minpoly K x)) := hsourceK
  let _ : Algebra.IsSeparable k (AdjoinRoot (minpoly K x)) :=
    Algebra.IsSeparable.trans k K (AdjoinRoot (minpoly K x))
  -- Separability transfers from the `AdjoinRoot` owner to the range.
  exact AlgEquiv.Algebra.isSeparable e

/-- Helper for Chap11 Lemma 11 8 6: a proper centralizer produces a strictly larger separable
`k`-subfield. -/
lemma exists_larger_separable_subfield_of_nontrivial_centralizer
    (K : Subalgebra k D) (hKfield : IsField K) (hKsep : Algebra.IsSeparable k K)
    (hCK : Subalgebra.centralizer k (K : Set D) ≠ K) :
    ∃ L : Subalgebra k D, IsField L ∧ Algebra.IsSeparable k L ∧ K < L := by
  let C := Subalgebra.centralizer k (K : Set D)
  have hKC : K ≤ C := self_le_centralizer_of_isField (k := k) (D := D) K hKfield
  let iKC := centralizerSubfieldInclusion (k := k) (D := D) K hKfield
  let C₀ : Subfield D :=
    C.toSubring.toSubfield fun x hx ↦
      inv_mem_centralizer_of_mem_centralizer (k := k) (D := D) K hx
  let iKC₀ : K →ₐ[k] C₀ where
    toFun a := ⟨a.1, hKC a.2⟩
    map_zero' := rfl
    map_one' := rfl
    map_add' _ _ := rfl
    map_mul' _ _ := rfl
    commutes' _ := rfl
  letI : Field K := hKfield.toField
  letI : Algebra K C := iKC.toRingHom.toAlgebra
  letI : Algebra K C₀ := iKC₀.toRingHom.toAlgebra
  letI : FiniteDimensional k K := FiniteDimensional.of_injective K.val K.val_injective
  letI : FiniteDimensional K D := FiniteDimensional.right K k D
  let iC₀D : C₀ →ₗ[K] D where
    toFun := Subtype.val
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
  letI : FiniteDimensional K C₀ := FiniteDimensional.of_injective iC₀D fun x y hxy ↦
    Subtype.ext hxy
  letI : Algebra.IsAlgebraic K C₀ := Algebra.IsAlgebraic.of_finite K C₀
  have hCproper₀ : (⊥ : Subalgebra K C₀) ≠ ⊤ := by
    intro hbot
    have hEq : C = K := by
      apply le_antisymm
      · intro x hx
        have hxbot : (⟨x, hx⟩ : C₀) ∈ (⊥ : Subalgebra K C₀) := by
          simpa [hbot] using (show (⟨x, hx⟩ : C₀) ∈ (⊤ : Subalgebra K C₀) from by simp)
        rw [Algebra.mem_bot] at hxbot
        rcases hxbot with ⟨a, ha⟩
        exact (congrArg Subtype.val ha) ▸ a.2
      · exact hKC
    exact hCK (by simpa [C] using hEq)
  have hCcentral₀ : Algebra.IsCentral K C₀ := by
    let A : CSA.{u, v} k := CSA.mk (AlgCat.of k D)
    have hCC : Subalgebra.centralizer k (C : Set D) = K := by
      -- The double-centralizer theorem identifies the center of the centralizer with `K`.
      simpa [A, C] using
        (Subalgebra.centralizer_centralizer_eq (k := k) (A := A) (B := K))
    refine ⟨fun x hx ↦ ?_⟩
    have hxC :
        x.1 ∈ Subalgebra.centralizer k (C : Set D) := by
      -- A central element of `C₀` commutes with every element of the ambient centralizer `C`.
      rw [Subalgebra.mem_centralizer_iff]
      rw [Subalgebra.mem_center_iff] at hx
      intro y hy
      exact congrArg Subtype.val (hx ⟨y, hy⟩)
    have hxK : x.1 ∈ K := by
      simpa [hCC] using hxC
    rw [Algebra.mem_bot]
    refine ⟨⟨x.1, hxK⟩, ?_⟩
    ext
    rfl
  letI : Algebra.IsCentral K C₀ := hCcentral₀
  -- Route correction: package the centralizer as a proper central `K`-algebra before adjoining
  -- a separable nonscalar element.
  have htransport_strict :
      ∀ x : C, x ∉ (⊥ : Subalgebra K C) →
        K < (adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range :=
    adjoinRoot_range_strict_of_nontrivial_centralizer_element
      (k := k) (D := D) K hKfield
  obtain ⟨x₀, hx₀bot, hx₀sep⟩ :=
    JacobsonNoether.exists_separable_and_not_isCentral' (L := K) (D := C₀) hCproper₀
  let x : C := ⟨x₀.1, x₀.2⟩
  let fCC₀ : C →ₐ[K] C₀ where
    toFun z := ⟨z.1, z.2⟩
    map_zero' := rfl
    map_one' := rfl
    map_add' _ _ := rfl
    map_mul' _ _ := rfl
    commutes' _ := rfl
  have hxbot : x ∉ (⊥ : Subalgebra K C) := by
    intro hx
    apply hx₀bot
    rw [Algebra.mem_bot] at hx ⊢
    rcases hx with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    ext
    exact congrArg Subtype.val ha
  have hxsep : IsSeparable K x := by
    have hfx : fCC₀ x = x₀ := by
      ext
      rfl
    -- Transfer separability back along the identity inclusion between the two centralizer models.
    exact hfx ▸ IsSeparable.of_algHom (f := fCC₀) hx₀sep
  let L :=
    (adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range
  have hLfield : IsField L :=
    adjoinRoot_range_isField_of_centralizer_element (k := k) (D := D) K hKfield x
  have hLsep : Algebra.IsSeparable k L :=
    adjoinRoot_range_isSeparable_of_centralizer_element
      (k := k) (D := D) K hKfield hKsep x hxsep
  have hKL : K < L := htransport_strict x hxbot
  -- Adjoin the nonscalar separable centralizer element and transfer the field and separability
  -- facts along the canonical simple-extension map.
  exact ⟨L, hLfield, hLsep, hKL⟩

/-- Helper for Chap11 Lemma 11 8 6: a finite central skew field contains a maximal subfield that
is separable over `k`. -/
theorem exists_separable_maximal_subfield :
    ∃ K : Subalgebra k D, Algebra.IsSeparable k K ∧ IsMaximalSubfield K := by
  classical
  rcases exists_finrank_maximal_separable_subfield (k := k) (D := D) with
    ⟨K, hKfield, hKsep, hmax⟩
  have hCeq : Subalgebra.centralizer k (K : Set D) = K := by
    by_contra hCK
    rcases exists_larger_separable_subfield_of_nontrivial_centralizer
      (k := k) (D := D) K hKfield hKsep hCK with
      ⟨L, hLfield, hLsep, hKL⟩
    have hfinKL : Module.finrank k K ≤ Module.finrank k L := by
      exact Submodule.finrank_mono hKL.le
    have hfinLK : Module.finrank k L ≤ Module.finrank k K := hmax L hLfield hLsep
    have hEq : K = L := Subalgebra.eq_of_le_of_finrank_eq hKL.le (Nat.le_antisymm hfinLK hfinKL)
    exact hKL.ne hEq
  have hKmax : K.IsMaximalCommutative :=
    (K.centralizer_eq_iff_isMaximalCommutative).1 hCeq
  -- The maximal-finrank separable field becomes maximal once its centralizer collapses.
  exact ⟨K, hKsep, { toIsMaximalCommutative := hKmax }⟩

end

namespace CSA

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k)

/- Layer note: `finite_central_simple_tfae` is the `source-facing` statement for an arbitrary
`k`-algebra. The declarations below move to the `core/canonical` owner abstraction `CSA k` for
representative-level splitness and degree data, rather than keeping parallel ad hoc wrappers. -/

-- Proof sketch: a finite central simple algebra becomes a matrix algebra after scalar extension to
-- an algebraic closure by the splitting criterion.
/-- Companion statement: every finite central simple `k`-algebra splits over `AlgebraicClosure k`.
-/
theorem isSplitBy_algebraicClosure : A.IsSplitBy (AlgebraicClosure k) := by
  -- Apply the algebraically closed Wedderburn theorem to the canonical base change of `A`.
  obtain ⟨n, _, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed (AlgebraicClosure k)
      (A.baseChange (AlgebraicClosure k))
  exact ⟨n, ⟨e⟩⟩

/-- Helper for Chap11 Lemma 11 8 6: left multiplication becomes `K`-linear once `B` is viewed as
right module over an embedded field `K`. -/
private theorem embeddedFieldLeftMulAlgHom
    {K : Type w} [Field K] [Algebra k K] {B : CSA.{u, v} k}
    (ι : K →ₐ[k] B) :
    B →ₐ[k] Module.End K B := by
  letI : Module K B :=
    { smul := fun c x ↦ x * ι c
      one_smul := by
        intro x
        simp
      mul_smul := by
        intro a b x
        rw [show x * ι (a * b) = x * (ι a * ι b) by rw [map_mul]]
        rw [mul_assoc]
        congr 1
        exact mul_comm (ι a) (ι b)
      smul_zero := by
        intro c
        simp
      smul_add := by
        intro c x y
        simp [mul_add]
      zero_smul := by
        intro x
        simp
      add_smul := by
        intro a b x
        simp [add_mul] }
  letI : IsScalarTower k K B :=
    ⟨fun r c x ↦ by
      calc
        (r • c) • x = x * ι ((algebraMap k K r) * c) := rfl
        _ = x * (algebraMap k B r * ι c) := by rw [map_mul, AlgHom.commutes]
        _ = (x * algebraMap k B r) * ι c := by rw [mul_assoc]
        _ = (algebraMap k B r * x) * ι c := by
              rw [Algebra.commutes (R := k) (A := B) r x]
        _ = r • (c • x) := by rw [Algebra.smul_def, mul_assoc]⟩
  -- Package left multiplication into the universal `Module.End` algebra.
  refine
    { toFun := fun b ↦
        { toFun := fun x ↦ b * x
          map_add' := by
            intro x y
            simp [mul_add]
          map_smul' := by
            intro c x
            change b * (x * ι c) = (b * x) * ι c
            rw [mul_assoc] }
      map_zero' := by
        ext x
        simp
      map_one' := by
        ext x
        simp
      map_add' := by
        intro b₁ b₂
        ext x
        simp [add_mul]
      map_mul' := by
        intro b₁ b₂
        ext x
        simp [mul_assoc]
      commutes' := by
        intro r
        ext x
        change algebraMap k B r * x = x * ι (algebraMap k K r)
        rw [AlgHom.commutes]
        exact Algebra.commutes (R := k) (A := B) r x }

/-- Helper for Chap11 Lemma 11 8 6: an embedded field of square degree splits the ambient finite
central simple algebra. -/
theorem isSplitBy_of_self_embedding_finrank_sq
    {K : Type w} [Field K] [Algebra k K] {B : CSA.{u, v} k}
    (hK : Nonempty (K →ₐ[k] B))
    (hdim : Module.finrank k B = Module.finrank k K ^ 2) :
    B.IsSplitBy K := by
  rcases hK with ⟨ι⟩
  letI : Module K B :=
    { smul := fun c x ↦ x * ι c
      one_smul := by
        intro x
        simp
      mul_smul := by
        intro a b x
        rw [show x * ι (a * b) = x * (ι a * ι b) by rw [map_mul]]
        rw [mul_assoc]
        congr 1
        exact mul_comm (ι a) (ι b)
      smul_zero := by
        intro c
        simp
      smul_add := by
        intro c x y
        simp [mul_add]
      zero_smul := by
        intro x
        simp
      add_smul := by
        intro a b x
        simp [add_mul] }
  letI : IsScalarTower k K B :=
    ⟨fun r c x ↦ by
      calc
        (r • c) • x = x * ι ((algebraMap k K r) * c) := rfl
        _ = x * (algebraMap k B r * ι c) := by rw [map_mul, AlgHom.commutes]
        _ = (x * algebraMap k B r) * ι c := by rw [mul_assoc]
        _ = (algebraMap k B r * x) * ι c := by
              rw [Algebra.commutes (R := k) (A := B) r x]
        _ = r • (c • x) := by rw [Algebra.smul_def, mul_assoc]⟩
  letI : FiniteDimensional K B := FiniteDimensional.right k K B
  let φ : B.baseChange K →ₐ[K] Module.End K B :=
    (AlgHom.liftEquiv k K B (Module.End K B))
      (embeddedFieldLeftMulAlgHom (k := k) (ι := ι))
  have hφ_inj : Function.Injective φ := RingHom.injective φ.toRingHom
  have hfinrankB : Module.finrank K B = Module.finrank k K := by
    -- Compare the two ways of computing `[B : k]`.
    apply Nat.eq_of_mul_eq_mul_left Module.finrank_pos
    calc
      Module.finrank k K * Module.finrank K B = Module.finrank k B := by
        simpa using (Module.finrank_mul_finrank k K B)
      _ = Module.finrank k K ^ 2 := by simpa using hdim
      _ = Module.finrank k K * Module.finrank k K := by rw [pow_two]
  have hφ_dim :
      Module.finrank K (B.baseChange K) = Module.finrank K (Module.End K B) := by
    -- Rewrite both sides as the same square dimension over `K`.
    calc
      Module.finrank K (B.baseChange K) = Module.finrank k B := by
        simpa [CSA.baseChange] using
          (Module.finrank_baseChange (R := K) (S := k) (M' := B))
      _ = Module.finrank k K ^ 2 := by simpa using hdim
      _ = Module.finrank K B * Module.finrank K B := by rw [hfinrankB, pow_two]
      _ = Module.finrank K (Module.End K B) := by
            simpa using (Module.finrank_linearMap K K B B).symm
  have hφ_surj : Function.Surjective φ := by
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hφ_dim).mp hφ_inj
  let b : Basis (Fin (Module.finrank K B)) K B := Module.finBasis K B
  -- Identify the base change with the endomorphism algebra and then with matrices.
  refine ⟨Module.finrank K B, ?_⟩
  exact ⟨(AlgEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩).trans (Module.End.algEquivMatrix b)⟩

/-- Helper for Chap11 Lemma 11 8 6: a maximal subfield of a finite central skew field splits the
associated central simple algebra. -/
theorem maximalSubfield_splits
    {D : Type w} [DivisionRing D] [Algebra k D] [FiniteDimensional k D]
    [Algebra.IsCentral k D] (K₀ : Subalgebra k D) [IsMaximalSubfield K₀] :
    (CSA.mk (AlgCat.of k D)).IsSplitBy K₀ := by
  -- Use the direct square-degree split criterion on the canonical inclusion `K₀ ↪ D`.
  refine isSplitBy_of_self_embedding_finrank_sq (k := k) (B := CSA.mk (AlgCat.of k D))
    (K := K₀) ?_ ?_
  · exact ⟨K₀.val⟩
  · simpa using IsMaximalSubfield.finrank_sq K₀

/-- Helper for Lemma 11.8.6: finite central simple algebras admit finite separable splitting
fields in the ambient output universe used by clause `(5)`. -/
theorem finite_separable_splitting_field_exists :
    ∃ (L : Type w) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L)
      (_ : Algebra.IsSeparable k L),
      A.IsSplitBy L := by
  -- Route correction: work through a Brauer-equivalent division representative, build a
  -- separable maximal subfield there, then transport the splitness witness back to `A`.
  rcases A.exists_division_algebra_representative with
    ⟨D, _, _, _, _, hAD⟩
  rcases exists_separable_maximal_subfield (k := k) (D := D) with ⟨L, hLsep, hLmax⟩
  letI : IsMaximalSubfield L := hLmax
  have hsplitD : (CSA.mk (AlgCat.of k D)).IsSplitBy L := maximalSubfield_splits (k := k) L
  exact ⟨L, inferInstance, inferInstance, inferInstance, hLsep,
    (A.isSplitBy_iff_of_isBrauerEquivalent L hAD).2 hsplitD⟩

/-- Helper for Lemma 11.8.6: choose a finite separable splitting field together with its canonical
map into `SeparableClosure k`. -/
theorem finite_separable_splitting_field_to_separableClosure :
    ∃ (L : Type v) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L)
      (_ : Algebra.IsSeparable k L) (_ : Algebra L (SeparableClosure k))
      (_ : IsScalarTower k L (SeparableClosure k)),
      A.IsSplitBy L := by
  have hsplit :
      ∃ (L : Type v) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L)
        (_ : Algebra.IsSeparable k L),
        A.IsSplitBy L := by
    -- Reinterpret the local finite separable splitting-field placeholder in the target universe.
    simpa using A.finite_separable_splitting_field_exists
  rcases hsplit with ⟨L, _, _, _, hLsep, hLsplit⟩
  let ι : L →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  have hRange : ι.fieldRange ≤ separableClosure k (AlgebraicClosure k) := by
    -- The image field of a separable extension is separable over `k`, hence contained in the
    -- canonical separable closure inside `AlgebraicClosure k`.
    letI : Algebra.IsSeparable k ι.fieldRange :=
      AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField ι)
    exact le_separableClosure k (AlgebraicClosure k) ι.fieldRange
  let ιsep : L →ₐ[k] SeparableClosure k :=
    ι.codRestrict (separableClosure k (AlgebraicClosure k)).toSubalgebra fun x ↦
      hRange ⟨x, rfl⟩
  letI : Algebra L (SeparableClosure k) := ιsep.toAlgebra
  letI : IsScalarTower k L (SeparableClosure k) := inferInstance
  -- Package the embedding into the separable closure together with the original split witness.
  exact ⟨L, inferInstance, inferInstance, inferInstance, hLsep, inferInstance, inferInstance,
    hLsplit⟩

/-- Helper for Lemma 11.8.6: scalar extension carries a matrix algebra over `L` to the
corresponding matrix algebra over `K`. -/
noncomputable def matrix_baseChange_algEquiv
    {L : Type*} {K : Type*} [Field L] [Field K] [Algebra k L] [Algebra k K]
    [Algebra L K] [IsScalarTower k L K] (n : ℕ) :
    K ⊗[L] Matrix (Fin n) (Fin n) L ≃ₐ[K] Matrix (Fin n) (Fin n) K :=
  let eK : K ≃ₐ[K] Matrix (Fin 1) (Fin 1) K :=
    ((Matrix.reindexAlgEquiv K K finOneEquiv).trans Matrix.uniqueAlgEquiv).symm
  let eTensor :
      K ⊗[L] Matrix (Fin n) (Fin n) L ≃ₐ[K]
        Matrix (Fin 1) (Fin 1) K ⊗[L] Matrix (Fin n) (Fin n) L :=
    Algebra.TensorProduct.congr eK
      (AlgEquiv.refl : Matrix (Fin n) (Fin n) L ≃ₐ[L] Matrix (Fin n) (Fin n) L)
  let eKronecker :
      Matrix (Fin 1) (Fin 1) K ⊗[L] Matrix (Fin n) (Fin n) L ≃ₐ[K]
        Matrix (Fin 1 × Fin n) (Fin 1 × Fin n) (K ⊗[L] L) :=
    Matrix.kroneckerTMulAlgEquiv (Fin 1) (Fin n) L K K L
  let eCoeff :
      Matrix (Fin 1 × Fin n) (Fin 1 × Fin n) (K ⊗[L] L) ≃ₐ[K]
        Matrix (Fin 1 × Fin n) (Fin 1 × Fin n) K :=
    (Algebra.TensorProduct.rid L K K).mapMatrix
  let eProd : Fin 1 × Fin n ≃ Fin n :=
    finProdFinEquiv.trans (finCongr (show 1 * n = n by simp))
  -- First rewrite the left factor as a `1 × 1` matrix algebra, then apply the Kronecker
  -- tensor equivalence and collapse the coefficient tensor `K ⊗[L] L` back to `K`.
  eTensor.trans <| eKronecker.trans <| eCoeff.trans <| Matrix.reindexAlgEquiv K K eProd

/-- Helper for Lemma 11.8.6: splitness ascends along a tower of field extensions. -/
theorem isSplitBy_of_isScalarTower
    {L : Type*} {K : Type*} [Field L] [Field K] [Algebra k L] [Algebra k K]
    [Algebra L K] [IsScalarTower k L K] (hL : A.IsSplitBy L) :
    A.IsSplitBy K := by
  rcases hL with ⟨n, ⟨e⟩⟩
  refine ⟨n, ?_⟩
  let eTensor :
      K ⊗[L] (L ⊗[k] A) ≃ₐ[K] K ⊗[L] Matrix (Fin n) (Fin n) L :=
    Algebra.TensorProduct.congr (AlgEquiv.refl K) e
  -- Cancel the intermediate base field `L`, transport the split matrix model upstairs, and then
  -- identify the scalar-extended matrix algebra with matrices over `K`.
  exact ⟨(Algebra.TensorProduct.cancelBaseChange k L K K A).symm.trans <|
    eTensor.trans <| A.matrix_baseChange_algEquiv (L := L) (K := K) n⟩

/-- Helper for Lemma 11.8.6: the canonical normal closure of a finite separable extension is
Galois over the base field. -/
theorem normalClosure_isGalois {L : Type w} [Field L] [Algebra k L]
    [Algebra.IsSeparable k L] :
    IsGalois k (IntermediateField.normalClosure k L (AlgebraicClosure L)) := by
  -- Invoke the earlier normal-closure theorem from Chapter 9.
  simpa using (isGalois_normalClosure_of_separable (K := k) (L := L))

-- Proof sketch: a finite central simple algebra splits over the separable closure because the
-- algebraic-closure splitting descends along Lemma 11.4.5.
/-- Companion statement: every finite central simple `k`-algebra splits over `SeparableClosure k`.
-/
theorem isSplitBy_separableClosure : A.IsSplitBy (SeparableClosure k) := by
  rcases A.finite_separable_splitting_field_to_separableClosure with
    ⟨L, _, _, _, _, _, _, hL⟩
  -- Ascend the finite separable splitting-field witness to the canonical separable closure.
  exact A.isSplitBy_of_isScalarTower (L := L) hL

-- Proof sketch: Proposition 11.8.5 gives a finite separable splitting field, and a finite Galois
-- closure of that field yields the Galois form.
/-- Companion statement: every finite central simple `k`-algebra admits a finite Galois splitting
field. -/
theorem exists_finite_galois_splitting_field :
    ∃ (k' : Type w) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k')
      (_ : IsGalois k k'),
      A.IsSplitBy k' := by
  rcases A.finite_separable_splitting_field_exists with ⟨L, _, _, _, _, hL⟩
  refine ⟨IntermediateField.normalClosure k L (AlgebraicClosure L), inferInstance, inferInstance,
    inferInstance, ?_,
    ?_⟩
  · -- The canonical normal closure of a finite separable extension is finite Galois.
    exact normalClosure_isGalois (k := k) (L := L)
  · letI : Algebra L (IntermediateField.normalClosure k L (AlgebraicClosure L)) := inferInstance
    letI : IsScalarTower k L (IntermediateField.normalClosure k L (AlgebraicClosure L)) :=
      inferInstance
    -- Ascend the original splitting witness to its finite Galois normal closure.
    exact A.isSplitBy_of_isScalarTower (L := L) hL

end CSA

section

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]

/-- Lemma 11.8.6: for a `k`-algebra `A`, the following are equivalent: `A` is finite-dimensional,
central, and simple; it has center exactly `k` and only trivial two-sided ideals; it becomes a
matrix algebra after scalar extension to the algebraic closure or to the separable closure; it is
split by a finite Galois extension of `k`; and it is a full matrix algebra over a finite central
division `k`-algebra. -/
@[stacks 0753]
theorem finite_central_simple_tfae :
    List.TFAE
      [ FiniteDimensional k A ∧ Algebra.IsCentral k A ∧ IsSimpleRing A,
        FiniteDimensional k A ∧ Subalgebra.center k A = ⊥ ∧
          Nontrivial A ∧ ∀ I : Ideal A, I.IsTwoSided → I = ⊥ ∨ I = ⊤,
        ∃ n : ℕ, n ≠ 0 ∧ Nonempty
          ((A ⊗[k] AlgebraicClosure k) ≃ₐ[AlgebraicClosure k]
            Matrix (Fin n) (Fin n) (AlgebraicClosure k)),
        ∃ n : ℕ, n ≠ 0 ∧ Nonempty
          ((A ⊗[k] SeparableClosure k) ≃ₐ[SeparableClosure k]
            Matrix (Fin n) (Fin n) (SeparableClosure k)),
        ∃ (k' : Type w) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k')
      (_ : IsGalois k k') (n : ℕ),
          n ≠ 0 ∧ Nonempty ((A ⊗[k] k') ≃ₐ[k'] Matrix (Fin n) (Fin n) k'),
        ∃ (n : ℕ), n ≠ 0 ∧ ∃ (D : Type w) (_ : DivisionRing D) (_ : Algebra k D)
          (_ : FiniteDimensional k D) (_ : Algebra.IsCentral k D),
          Nonempty (A ≃ₐ[k] Matrix (Fin n) (Fin n) D) ] := by
  -- Route correction: the forward source-faithful splitting edges now run through the owner API
  -- on `CSA`, while the reverse edge `(3 → 1)` has been isolated behind the two remaining descent
  -- frontiers `split_over_algebraicClosure_implies_two_sided_ideal_trivial` and
  -- `split_over_algebraicClosure_implies_isCentral`.
  tfae_have 1 ↔ 2 := by
    simpa using
      (finite_central_simple_iff_center_bot_and_two_sided_ideal_trivial
        (k := k) (A := A))
  tfae_have 1 ↔ 6 := by
    simpa using
      (finite_central_simple_iff_matrix_division_form (k := k) (A := A))
  tfae_have 1 → 4 := by
    rintro ⟨hfinite, hcentral, hsimple⟩
    letI : FiniteDimensional k A := hfinite
    letI : Algebra.IsCentral k A := hcentral
    letI : IsSimpleRing A := hsimple
    let ACSA : CSA.{u, v} k := CSA.mk (AlgCat.of k A)
    have hsplit : ACSA.IsSplitBy (SeparableClosure k) := ACSA.isSplitBy_separableClosure
    -- Rewrite the owner splitness witness from `SeparableClosure k ⊗[k] A` to the source-facing
    -- tensor order `A ⊗[k] SeparableClosure k`.
    rcases (ACSA.isSplitBy_iff_exists_pnat_algEquiv_matrix (K := SeparableClosure k)).1 hsplit with
      ⟨n, ⟨e⟩⟩
    exact ⟨n, Nat.ne_of_gt n.2, ⟨(Algebra.TensorProduct.comm k A (SeparableClosure k)).trans e⟩⟩
  tfae_have 4 → 3 := by
    rintro ⟨n, hn, ⟨e⟩⟩
    let ACSA : CSA.{u, v} k := CSA.mk (AlgCat.of k A)
    have hsplitSep : ACSA.IsSplitBy (SeparableClosure k) := by
      -- Convert the source-facing tensor order back to the owner base-change order.
      exact ⟨n, ⟨(Algebra.TensorProduct.comm k A (SeparableClosure k)).symm.trans e⟩⟩
    have hsplitAlg :
        ACSA.IsSplitBy (AlgebraicClosure k) :=
      ACSA.isSplitBy_of_isScalarTower (L := SeparableClosure k) hsplitSep
    -- Return to the source-facing tensor order after ascending to the algebraic closure.
    rcases (ACSA.isSplitBy_iff_exists_pnat_algEquiv_matrix (K := AlgebraicClosure k)).1 hsplitAlg with
      ⟨m, ⟨eAlg⟩⟩
    exact ⟨m, Nat.ne_of_gt m.2,
      ⟨(Algebra.TensorProduct.comm k A (AlgebraicClosure k)).trans eAlg⟩⟩
  tfae_have 1 → 5 := by
    rintro ⟨hfinite, hcentral, hsimple⟩
    letI : FiniteDimensional k A := hfinite
    letI : Algebra.IsCentral k A := hcentral
    letI : IsSimpleRing A := hsimple
    let ACSA : CSA.{u, v} k := CSA.mk (AlgCat.of k A)
    rcases ACSA.exists_finite_galois_splitting_field with
      ⟨k', hk'Field, hk'Alg, hk'Finite, hk'Galois, hsplit⟩
    letI : Field k' := hk'Field
    letI : Algebra k k' := hk'Alg
    letI : FiniteDimensional k k' := hk'Finite
    letI : IsGalois k k' := hk'Galois
    -- Unpack the owner splitness witness and commute the tensor factors back.
    rcases (ACSA.isSplitBy_iff_exists_pnat_algEquiv_matrix (K := k')).1 hsplit with ⟨n, ⟨e⟩⟩
    exact ⟨k', inferInstance, inferInstance, inferInstance, inferInstance, n,
      Nat.ne_of_gt n.2, ⟨(Algebra.TensorProduct.comm k A k').trans e⟩⟩
  tfae_have 5 → 3 := by
    rintro ⟨k', hk'Field, hk'Alg, hk'Finite, hk'Galois, n, hn, ⟨e⟩⟩
    letI : Field k' := hk'Field
    letI : Algebra k k' := hk'Alg
    letI : FiniteDimensional k k' := hk'Finite
    letI : IsGalois k k' := hk'Galois
    let ι : k' →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
    letI : Algebra k' (AlgebraicClosure k) := ι.toAlgebra
    letI : IsScalarTower k k' (AlgebraicClosure k) := inferInstance
    let ACSA : CSA.{u, v} k := CSA.mk (AlgCat.of k A)
    have hsplitk' : ACSA.IsSplitBy k' := by
      -- Convert the clause `(5)` witness into the owner splitness language.
      exact ⟨n, ⟨(Algebra.TensorProduct.comm k A k').symm.trans e⟩⟩
    have hsplitAlg :
        ACSA.IsSplitBy (AlgebraicClosure k) :=
      ACSA.isSplitBy_of_isScalarTower (L := k') hsplitk'
    -- Finally move back to the source-facing tensor order over `AlgebraicClosure k`.
    rcases (ACSA.isSplitBy_iff_exists_pnat_algEquiv_matrix (K := AlgebraicClosure k)).1 hsplitAlg with
      ⟨m, ⟨eAlg⟩⟩
    exact ⟨m, Nat.ne_of_gt m.2,
      ⟨(Algebra.TensorProduct.comm k A (AlgebraicClosure k)).trans eAlg⟩⟩
  tfae_have 3 → 1 := by
    intro hsplit
    have hfinite : FiniteDimensional k A :=
      split_over_algebraicClosure_implies_finiteDimensional (k := k) (A := A) hsplit
    letI : FiniteDimensional k A := hfinite
    have hsimple : IsSimpleRing A :=
      split_over_algebraicClosure_implies_isSimpleRing (k := k) (A := A) hsplit
    letI : IsSimpleRing A := hsimple
    have hcentral : Algebra.IsCentral k A :=
      split_over_algebraicClosure_implies_isCentral (k := k) (A := A) hsplit
    exact ⟨hfinite, hcentral, hsimple⟩
  tfae_finish

end
