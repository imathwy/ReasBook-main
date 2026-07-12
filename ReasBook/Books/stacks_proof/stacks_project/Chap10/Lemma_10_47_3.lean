import Mathlib
import StacksProject_2024.Chap09.Lemma_9_6_9
import StacksProject_2024.Chap09.Lemma_9_26_11
import StacksProject_2024.Chap10.Lemma_10_47_1
import StacksProject_2024.Chap10.Definition_10_47_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct
open AlgebraicGeometry CommRingCat CategoryTheory CategoryTheory.Limits
attribute [local instance] Algebra.TensorProduct.rightAlgebra MvPolynomial.algebraMvPolynomial

universe u

section

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]

/-- Helper for Lemma 10.47.3: irreducibility of prime spectra descends along injective ring
homomorphisms. -/
private theorem irreducibleSpace_primeSpectrum_of_injective {A B : Type u} [CommRing A]
    [CommRing B] (f : A →+* B) (hf : Function.Injective f) :
    IrreducibleSpace (PrimeSpectrum B) → IrreducibleSpace (PrimeSpectrum A) := by
  intro hB
  -- Proof comment: compare nilradicals by injectivity and pull primality back along `f`.
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at hB ⊢
  letI : (nilradical B).IsPrime := hB
  have hcomap : Ideal.comap f (nilradical B) = nilradical A := by
    ext x
    simp [Ideal.mem_comap, mem_nilradical, IsNilpotent.map_iff hf]
  simpa [hcomap] using Ideal.comap_isPrime f (nilradical B)

/-- Helper for Lemma 10.47.3: a concrete witness that the nilradical of a ring is not prime. -/
private structure NonprimeNilradicalWitness (A : Type u) [CommRing A] where
  left : A
  right : A
  mul_isNilpotent : IsNilpotent (left * right)
  left_not_isNilpotent : ¬ IsNilpotent left
  right_not_isNilpotent : ¬ IsNilpotent right

/-- Helper for Lemma 10.47.3: such a witness contradicts irreducibility of the prime spectrum. -/
private theorem not_irreducibleSpace_primeSpectrum_of_nonprime_nilradical_witness
    {A : Type u} [CommRing A] :
    Nonempty (NonprimeNilradicalWitness A) → ¬ IrreducibleSpace (PrimeSpectrum A) := by
  intro h hA
  obtain ⟨w⟩ := h
  -- Proof comment: if the nilradical were prime, one witness factor would already be nilpotent.
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at hA
  have hmul : w.left * w.right ∈ nilradical A := mem_nilradical.mpr w.mul_isNilpotent
  rcases hA.mem_or_mem hmul with hleft | hright
  · exact w.left_not_isNilpotent (mem_nilradical.mp hleft)
  · exact w.right_not_isNilpotent (mem_nilradical.mp hright)

/-- Helper for Lemma 10.47.3: over a nontrivial ring, failure of irreducibility yields a
nonprime-nilradical witness. -/
private theorem exists_nonprime_nilradical_witness_of_not_irreducibleSpace_primeSpectrum
    {A : Type u} [CommRing A] [Nontrivial A] :
    ¬ IrreducibleSpace (PrimeSpectrum A) → Nonempty (NonprimeNilradicalWitness A) := by
  intro hA
  -- Proof comment: rewrite non-irreducibility as non-primeness of the nilradical.
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at hA
  have htop : (nilradical A) ≠ ⊤ := by
    intro htop
    have hnil : IsNilpotent (1 : A) := by
      apply mem_nilradical.mp
      simpa [htop] using (show (1 : A) ∈ (⊤ : Ideal A) from Ideal.mem_top)
    obtain ⟨n, hn⟩ := hnil
    exact (show (1 : A) ≠ 0 from one_ne_zero) (by simpa using hn)
  obtain ⟨x, hx, y, hy, hxy⟩ := (Ideal.not_isPrime_iff.mp hA).resolve_left htop
  exact ⟨{
    left := x
    right := y
    mul_isNilpotent := mem_nilradical.mp hxy
    left_not_isNilpotent := by simpa [mem_nilradical] using hx
    right_not_isNilpotent := by simpa [mem_nilradical] using hy
  }⟩

/-- Helper for Lemma 10.47.3: transporting a tensor from a smaller intermediate field stage into
the ambient field extension does not change its image in the full tensor product. -/
private theorem fieldTensor_map_comp_inclusion
    {L K F : Type u} [Field L] [Field K] [Field F] [Algebra L K] [Algebra L F]
    {K₀ K₁ : IntermediateField L K} (hK : K₀ ≤ K₁) (x : K₀ ⊗[L] F) :
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom L K₁ K) (AlgHom.id L F)
      (Algebra.TensorProduct.map (IntermediateField.inclusion hK) (AlgHom.id L F) x) =
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom L K₀ K) (AlgHom.id L F) x := by
  -- Proof comment: check the transport identity on pure tensors, then extend additively.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro a b
    simp [IntermediateField.coe_inclusion]
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for Lemma 10.47.3: every tensor in `K ⊗[L] F` already comes from a finitely generated
intermediate field of `K / L`. -/
private theorem exists_finitely_generated_intermediate_field_fieldTensor
    {L K F : Type u} [Field L] [Field K] [Field F] [Algebra L K] [Algebra L F]
    (x : K ⊗[L] F) :
    ∃ (K₀ : IntermediateField L K) (_ : K₀.FG) (x₀ : K₀ ⊗[L] F),
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom L K₀ K) (AlgHom.id L F) x₀ = x := by
  classical
  -- Proof comment: build the stage recursively from a tensor decomposition and enlarge stages by
  -- taking suprema in the additive step.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · refine ⟨⊥, IntermediateField.fg_bot, 0, ?_⟩
    simp
  · intro a b
    let K₀ : IntermediateField L K := IntermediateField.adjoin L ({a} : Set K)
    have haK₀ : a ∈ K₀ := IntermediateField.subset_adjoin L ({a} : Set K) (by simp)
    refine
      ⟨K₀,
        IntermediateField.fg_adjoin_of_finite (F := L) (E := K) (Set.finite_singleton a),
        ⟨a, haK₀⟩ ⊗ₜ[L] b, ?_⟩
    simp [K₀]
  · intro x y hx hy
    rcases hx with ⟨Kx, hKx, x₀, hx₀⟩
    rcases hy with ⟨Ky, hKy, y₀, hy₀⟩
    let K₀ : IntermediateField L K := Kx ⊔ Ky
    let x₀' : K₀ ⊗[L] F :=
      Algebra.TensorProduct.map
        (IntermediateField.inclusion (show Kx ≤ K₀ from le_sup_left))
        (AlgHom.id L F) x₀
    let y₀' : K₀ ⊗[L] F :=
      Algebra.TensorProduct.map
        (IntermediateField.inclusion (show Ky ≤ K₀ from le_sup_right))
        (AlgHom.id L F) y₀
    refine ⟨K₀, IntermediateField.fg_sup hKx hKy, x₀' + y₀', ?_⟩
    -- Proof comment: after transporting both stage tensors into the union stage, the ambient
    -- tensor is just the sum of the original ambient images.
    calc
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom L K₀ K) (AlgHom.id L F) (x₀' + y₀') =
          Algebra.TensorProduct.map (IsScalarTower.toAlgHom L K₀ K) (AlgHom.id L F) x₀' +
            Algebra.TensorProduct.map (IsScalarTower.toAlgHom L K₀ K) (AlgHom.id L F) y₀' := by
              simp [x₀', y₀']
      _ =
          Algebra.TensorProduct.map (IsScalarTower.toAlgHom L Kx K) (AlgHom.id L F) x₀ +
            Algebra.TensorProduct.map (IsScalarTower.toAlgHom L Ky K) (AlgHom.id L F) y₀ := by
              rw [fieldTensor_map_comp_inclusion (L := L) (K := K) (F := F)
                    (show Kx ≤ K₀ from le_sup_left) x₀,
                fieldTensor_map_comp_inclusion (L := L) (K := K) (F := F)
                    (show Ky ≤ K₀ from le_sup_right) y₀]
      _ = x + y := by
          simpa [hx₀, hy₀]

/-- Helper for Lemma 10.47.3: two tensors in `K ⊗[L] F` simultaneously descend to one finitely
generated intermediate field of `K / L`. -/
private theorem exists_fg_stage_ringTensor_field_pair
    {L K F : Type u} [Field L] [Field K] [Field F] [Algebra L K] [Algebra L F]
    (x y : K ⊗[L] F) :
    ∃ (K₀ : IntermediateField L K) (_ : K₀.FG) (x₀ y₀ : K₀ ⊗[L] F),
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom L K₀ K) (AlgHom.id L F) x₀ = x ∧
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom L K₀ K) (AlgHom.id L F) y₀ = y := by
  obtain ⟨Kx, hKx, x₀, hx₀⟩ :=
    exists_finitely_generated_intermediate_field_fieldTensor (L := L) (K := K) (F := F) x
  obtain ⟨Ky, hKy, y₀, hy₀⟩ :=
    exists_finitely_generated_intermediate_field_fieldTensor (L := L) (K := K) (F := F) y
  let K₀ : IntermediateField L K := Kx ⊔ Ky
  let x₀' : K₀ ⊗[L] F :=
    Algebra.TensorProduct.map
      (IntermediateField.inclusion (show Kx ≤ K₀ from le_sup_left))
      (AlgHom.id L F) x₀
  let y₀' : K₀ ⊗[L] F :=
    Algebra.TensorProduct.map
      (IntermediateField.inclusion (show Ky ≤ K₀ from le_sup_right))
      (AlgHom.id L F) y₀
  refine ⟨K₀, IntermediateField.fg_sup hKx hKy, x₀', y₀', ?_, ?_⟩
  · -- Proof comment: enlarge the first stage to the common finitely generated intermediate field.
    calc
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom L K₀ K) (AlgHom.id L F) x₀' =
          Algebra.TensorProduct.map (IsScalarTower.toAlgHom L Kx K) (AlgHom.id L F) x₀ := by
            rw [fieldTensor_map_comp_inclusion (L := L) (K := K) (F := F)
              (show Kx ≤ K₀ from le_sup_left) x₀]
      _ = x := hx₀
  · -- Proof comment: the same enlargement works for the second tensor.
    calc
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom L K₀ K) (AlgHom.id L F) y₀' =
          Algebra.TensorProduct.map (IsScalarTower.toAlgHom L Ky K) (AlgHom.id L F) y₀ := by
            rw [fieldTensor_map_comp_inclusion (L := L) (K := K) (F := F)
              (show Ky ≤ K₀ from le_sup_right) y₀]
      _ = y := hy₀

/-- Helper for Lemma 10.47.3: a nonprime-nilradical witness in `K ⊗[L] F` already appears over a
finitely generated intermediate field of `K / L`. -/
private theorem exists_nonprime_nilradical_witness_finitely_generated_field_stage
    {L K F : Type u} [Field L] [Field K] [Field F] [Algebra L K] [Algebra L F]
    (w : NonprimeNilradicalWitness (K ⊗[L] F)) :
    ∃ (K₀ : IntermediateField L K) (_ : K₀.FG) (x₀ y₀ : K₀ ⊗[L] F),
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom L K₀ K) (AlgHom.id L F) x₀ = w.left ∧
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom L K₀ K) (AlgHom.id L F) y₀ = w.right ∧
        IsNilpotent (x₀ * y₀) ∧ ¬ IsNilpotent x₀ ∧ ¬ IsNilpotent y₀ := by
  -- Route correction: descend only the two witness elements to one finitely generated
  -- intermediate field stage, then pull the nilpotence data back by injectivity.
  obtain ⟨K₀, hK₀, x₀, y₀, hx₀, hy₀⟩ :=
    exists_fg_stage_ringTensor_field_pair (L := L) (K := K) (F := F) w.left w.right
  let stageMap : K₀ ⊗[L] F →ₐ[L] K ⊗[L] F :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom L K₀ K) (AlgHom.id L F)
  let stageRing : K₀ ⊗[L] F →+* K ⊗[L] F := stageMap.toRingHom
  have hx₀' : stageRing x₀ = w.left := hx₀
  have hy₀' : stageRing y₀ = w.right := hy₀
  have hstage_inj : Function.Injective stageMap := by
    -- Proof comment: tensoring the injective field inclusion `K₀ ↪ K` with the identity on `F`
    -- preserves injectivity because both tensor factors are flat over the base field.
    simpa [stageMap] using TensorProduct.map_injective_of_flat_flat
      (IsScalarTower.toAlgHom L K₀ K).toLinearMap (AlgHom.id L F).toLinearMap
      (IsScalarTower.toAlgHom L K₀ K).injective Function.injective_id
  have hxy_nilpotent : IsNilpotent (x₀ * y₀) := by
    -- Proof comment: the product becomes the given nilpotent witness after applying the stage
    -- map, and injectivity pulls nilpotence back to the finitely generated stage.
    rcases w.mul_isNilpotent with ⟨n, hn⟩
    refine ⟨n, hstage_inj ?_⟩
    change stageRing ((x₀ * y₀) ^ n) = 0
    calc
      stageRing ((x₀ * y₀) ^ n) = (stageRing (x₀ * y₀)) ^ n := by
        rw [RingHom.map_pow]
      _ = (stageRing x₀ * stageRing y₀) ^ n := by
        rw [RingHom.map_mul]
      _ = (w.left * w.right) ^ n := by
        rw [hx₀', hy₀']
      _ = 0 := hn
  have hx₀_not_nilpotent : ¬ IsNilpotent x₀ := by
    intro hx₀_nilpotent
    apply w.left_not_isNilpotent
    -- Proof comment: nilpotence pushes forward along the stage map and contradicts the ambient
    -- witness.
    rcases hx₀_nilpotent with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    calc
      w.left ^ n = (stageRing x₀) ^ n := by rw [hx₀']
      _ = stageRing (x₀ ^ n) := by rw [← RingHom.map_pow]
      _ = 0 := by rw [hn, RingHom.map_zero]
  have hy₀_not_nilpotent : ¬ IsNilpotent y₀ := by
    intro hy₀_nilpotent
    apply w.right_not_isNilpotent
    -- Proof comment: the same pushforward argument rules out nilpotence of the second factor.
    rcases hy₀_nilpotent with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    calc
      w.right ^ n = (stageRing y₀) ^ n := by rw [hy₀']
      _ = stageRing (y₀ ^ n) := by rw [← RingHom.map_pow]
      _ = 0 := by rw [hn, RingHom.map_zero]
  exact ⟨K₀, hK₀, x₀, y₀, hx₀, hy₀, hxy_nilpotent, hx₀_not_nilpotent, hy₀_not_nilpotent⟩

/-- Helper for Lemma 10.47.3: every tensor in `R ⊗[k] SeparableClosure k` already comes from a
finite separable intermediate field of `SeparableClosure k / k`. -/
private theorem exists_finite_separable_stage_ringTensor_separableClosure
    (x : R ⊗[k] SeparableClosure k) :
    ∃ (L : IntermediateField k (SeparableClosure k)) (_ : FiniteDimensional k L)
      (_ : Algebra.IsSeparable k L) (xL : R ⊗[k] L),
      Algebra.TensorProduct.map (AlgHom.id k R) L.val xL = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · -- Proof comment: the zero tensor already lives over the trivial intermediate field.
    refine ⟨⊥, inferInstance, inferInstance, 0, ?_⟩
    simp
  · intro r a
    let L : IntermediateField k (SeparableClosure k) :=
      IntermediateField.adjoin k ({a} : Set (SeparableClosure k))
    have ha_sep : IsSeparable k a :=
      Algebra.IsSeparable.isSeparable (F := k) (K := SeparableClosure k) (x := a)
    have hLfd : FiniteDimensional k L := by
      apply IntermediateField.finiteDimensional_adjoin
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact ha_sep.isIntegral
    have hLsep : Algebra.IsSeparable k L := by
      rw [IntermediateField.isSeparable_adjoin_iff_isSeparable]
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact ha_sep
    let aL : L := ⟨a, IntermediateField.subset_adjoin k ({a} : Set (SeparableClosure k)) (by simp)⟩
    refine ⟨L, hLfd, hLsep, r ⊗ₜ[k] aL, ?_⟩
    simp [L, aL]
  · intro x y hx hy
    rcases hx with ⟨Lx, hLx_fd, hLx_sep, xL, hxL⟩
    rcases hy with ⟨Ly, hLy_fd, hLy_sep, yL, hyL⟩
    let L : IntermediateField k (SeparableClosure k) := Lx ⊔ Ly
    let ix : Lx →ₐ[k] L := IntermediateField.inclusion le_sup_left
    let iy : Ly →ₐ[k] L := IntermediateField.inclusion le_sup_right
    let xL' : R ⊗[k] L := Algebra.TensorProduct.map (AlgHom.id k R) ix xL
    let yL' : R ⊗[k] L := Algebra.TensorProduct.map (AlgHom.id k R) iy yL
    refine ⟨L, inferInstance, inferInstance, xL' + yL', ?_⟩
    -- Proof comment: enlarge both stage witnesses to the common finite separable compositum.
    have hxL' :
        Algebra.TensorProduct.map (AlgHom.id k R) L.val xL' = x := by
      have hcomp :
          Algebra.TensorProduct.map (AlgHom.id k R) (L.val.comp ix) xL =
            Algebra.TensorProduct.map (AlgHom.id k R) L.val
              ((Algebra.TensorProduct.map (AlgHom.id k R) ix) xL) := by
        simpa using congrArg
          (fun ψ : R ⊗[k] Lx →ₐ[k] R ⊗[k] SeparableClosure k => ψ xL)
          (Algebra.TensorProduct.map_comp (AlgHom.id k R) (AlgHom.id k R) L.val ix)
      calc
        Algebra.TensorProduct.map (AlgHom.id k R) L.val xL'
            = Algebra.TensorProduct.map (AlgHom.id k R) (L.val.comp ix) xL := by
                simpa [xL'] using hcomp.symm
        _ = Algebra.TensorProduct.map (AlgHom.id k R) Lx.val xL := by
              rfl
        _ = x := hxL
    have hyL' :
        Algebra.TensorProduct.map (AlgHom.id k R) L.val yL' = y := by
      have hcomp :
          Algebra.TensorProduct.map (AlgHom.id k R) (L.val.comp iy) yL =
            Algebra.TensorProduct.map (AlgHom.id k R) L.val
              ((Algebra.TensorProduct.map (AlgHom.id k R) iy) yL) := by
        simpa using congrArg
          (fun ψ : R ⊗[k] Ly →ₐ[k] R ⊗[k] SeparableClosure k => ψ yL)
          (Algebra.TensorProduct.map_comp (AlgHom.id k R) (AlgHom.id k R) L.val iy)
      calc
        Algebra.TensorProduct.map (AlgHom.id k R) L.val yL'
            = Algebra.TensorProduct.map (AlgHom.id k R) (L.val.comp iy) yL := by
                simpa [yL'] using hcomp.symm
        _ = Algebra.TensorProduct.map (AlgHom.id k R) Ly.val yL := by
              rfl
        _ = y := hyL
    simp [xL', yL', hxL', hyL']

/-- Helper for Lemma 10.47.3: two tensors in `R ⊗[k] SeparableClosure k` simultaneously descend to
one finite separable intermediate stage. -/
private theorem exists_common_finite_separable_stage_ringTensor_separableClosure
    (x y : R ⊗[k] SeparableClosure k) :
    ∃ (L : IntermediateField k (SeparableClosure k)) (_ : FiniteDimensional k L)
      (_ : Algebra.IsSeparable k L) (xL yL : R ⊗[k] L),
      Algebra.TensorProduct.map (AlgHom.id k R) L.val xL = x ∧
        Algebra.TensorProduct.map (AlgHom.id k R) L.val yL = y := by
  rcases exists_finite_separable_stage_ringTensor_separableClosure (k := k) (R := R) x with
    ⟨Lx, hLx_fd, hLx_sep, xL, hxL⟩
  rcases exists_finite_separable_stage_ringTensor_separableClosure (k := k) (R := R) y with
    ⟨Ly, hLy_fd, hLy_sep, yL, hyL⟩
  let L : IntermediateField k (SeparableClosure k) := Lx ⊔ Ly
  let ix : Lx →ₐ[k] L := IntermediateField.inclusion le_sup_left
  let iy : Ly →ₐ[k] L := IntermediateField.inclusion le_sup_right
  let xL' : R ⊗[k] L := Algebra.TensorProduct.map (AlgHom.id k R) ix xL
  let yL' : R ⊗[k] L := Algebra.TensorProduct.map (AlgHom.id k R) iy yL
  refine ⟨L, inferInstance, inferInstance, xL', yL', ?_, ?_⟩
  · -- Proof comment: enlarge the first stage witness to the common finite separable stage.
    have hcomp :
        Algebra.TensorProduct.map (AlgHom.id k R) (L.val.comp ix) xL =
          Algebra.TensorProduct.map (AlgHom.id k R) L.val
            ((Algebra.TensorProduct.map (AlgHom.id k R) ix) xL) := by
      simpa using congrArg
        (fun ψ : R ⊗[k] Lx →ₐ[k] R ⊗[k] SeparableClosure k => ψ xL)
        (Algebra.TensorProduct.map_comp (AlgHom.id k R) (AlgHom.id k R) L.val ix)
    calc
      Algebra.TensorProduct.map (AlgHom.id k R) L.val xL'
          = Algebra.TensorProduct.map (AlgHom.id k R) (L.val.comp ix) xL := by
              simpa [xL'] using hcomp.symm
      _ = Algebra.TensorProduct.map (AlgHom.id k R) Lx.val xL := by
            rfl
      _ = x := hxL
  · -- Proof comment: the same enlargement works for the second witness.
    have hcomp :
        Algebra.TensorProduct.map (AlgHom.id k R) (L.val.comp iy) yL =
          Algebra.TensorProduct.map (AlgHom.id k R) L.val
            ((Algebra.TensorProduct.map (AlgHom.id k R) iy) yL) := by
      simpa using congrArg
        (fun ψ : R ⊗[k] Ly →ₐ[k] R ⊗[k] SeparableClosure k => ψ yL)
        (Algebra.TensorProduct.map_comp (AlgHom.id k R) (AlgHom.id k R) L.val iy)
    calc
      Algebra.TensorProduct.map (AlgHom.id k R) L.val yL'
          = Algebra.TensorProduct.map (AlgHom.id k R) (L.val.comp iy) yL := by
              simpa [yL'] using hcomp.symm
      _ = Algebra.TensorProduct.map (AlgHom.id k R) Ly.val yL := by
            rfl
      _ = y := hyL

/-- Helper for Lemma 10.47.3: a nonprime-nilradical witness over `SeparableClosure k` descends to
one finite separable intermediate stage. -/
private theorem exists_nonprime_nilradical_witness_finite_separable_stage
    (w : NonprimeNilradicalWitness (R ⊗[k] SeparableClosure k)) :
    ∃ (L : IntermediateField k (SeparableClosure k)) (_ : FiniteDimensional k L)
      (_ : Algebra.IsSeparable k L) (xL yL : R ⊗[k] L),
      Algebra.TensorProduct.map (AlgHom.id k R) L.val xL = w.left ∧
        Algebra.TensorProduct.map (AlgHom.id k R) L.val yL = w.right ∧
        IsNilpotent (xL * yL) ∧ ¬ IsNilpotent xL ∧ ¬ IsNilpotent yL := by
  obtain ⟨L, hLfd, hLsep, xL, yL, hxL, hyL⟩ :=
    exists_common_finite_separable_stage_ringTensor_separableClosure
      (k := k) (R := R) w.left w.right
  let stageMap : R ⊗[k] L →ₐ[k] R ⊗[k] SeparableClosure k :=
    Algebra.TensorProduct.map (AlgHom.id k R) L.val
  have hstage_inj : Function.Injective stageMap := by
    -- Proof comment: tensoring the injective field inclusion `L ↪ SeparableClosure k` preserves
    -- injectivity because both tensor factors are flat over the base field `k`.
    simpa [stageMap] using TensorProduct.map_injective_of_flat_flat
      (AlgHom.id k R).toLinearMap L.val.toLinearMap Function.injective_id L.val.injective
  have hxy_nilpotent : IsNilpotent (xL * yL) := by
    -- Proof comment: the product becomes the given nilpotent witness after applying the stage map,
    -- and injectivity lets us pull nilpotence back to the finite separable stage.
    rcases w.mul_isNilpotent with ⟨n, hn⟩
    refine ⟨n, hstage_inj ?_⟩
    rw [map_zero, map_pow, map_mul, hxL, hyL, hn]
  have hxL_not_nilpotent : ¬ IsNilpotent xL := by
    intro hxL_nilpotent
    apply w.left_not_isNilpotent
    -- Proof comment: nilpotence would push forward along the stage map and contradict the upstairs
    -- witness.
    rcases hxL_nilpotent with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    calc
      w.left ^ n = (stageMap xL) ^ n := by rw [hxL]
      _ = stageMap (xL ^ n) := by rw [map_pow]
      _ = 0 := by rw [hn, map_zero]
  have hyL_not_nilpotent : ¬ IsNilpotent yL := by
    intro hyL_nilpotent
    apply w.right_not_isNilpotent
    -- Proof comment: the same injective pushforward argument rules out nilpotence of `yL`.
    rcases hyL_nilpotent with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    calc
      w.right ^ n = (stageMap yL) ^ n := by rw [hyL]
      _ = stageMap (yL ^ n) := by rw [map_pow]
      _ = 0 := by rw [hn, map_zero]
  exact ⟨L, hLfd, hLsep, xL, yL, hxL, hyL, hxy_nilpotent, hxL_not_nilpotent, hyL_not_nilpotent⟩

/-- Helper for Lemma 10.47.3: if every finite separable stage has irreducible prime spectrum, then
so does the separable-closure tensor product. -/
private theorem irreducibleSpace_primeSpectrum_separableClosure_of_finiteSeparable
    (h :
      ∀ (K : Type u) [Field K] [Algebra k K]
        [FiniteDimensional k K] [Algebra.IsSeparable k K],
        IrreducibleSpace (PrimeSpectrum (R ⊗[k] K))) :
    IrreducibleSpace (PrimeSpectrum (R ⊗[k] SeparableClosure k)) := by
  -- Route correction: descend only the two witness elements to one finite separable stage, then
  -- rebuild the downstairs witness there instead of transporting the whole witness structure.
  by_contra hSep
  have hk : IrreducibleSpace (PrimeSpectrum (R ⊗[k] k)) := h k
  have hk_nonempty : Nonempty (PrimeSpectrum (R ⊗[k] k)) := by
    rw [irreducibleSpace_def] at hk
    rcases hk.1 with ⟨x, hx⟩
    exact ⟨x⟩
  letI : Nontrivial (R ⊗[k] k) := PrimeSpectrum.nonempty_iff_nontrivial.mp hk_nonempty
  let eBase : R ⊗[k] k ≃ₐ[R] R := Algebra.TensorProduct.rid k R R
  letI : Nontrivial R := eBase.injective.nontrivial
  letI : Nontrivial (R ⊗[k] SeparableClosure k) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left
      (R := k) (A := R) (B := SeparableClosure k) (algebraMap k (SeparableClosure k)).injective
  obtain ⟨w⟩ :=
    exists_nonprime_nilradical_witness_of_not_irreducibleSpace_primeSpectrum hSep
  obtain ⟨L, hLfd, hLsep, xL, yL, hxL, hyL, hxy_nilpotent, hxL_not_nilpotent,
    hyL_not_nilpotent⟩ :=
      exists_nonprime_nilradical_witness_finite_separable_stage (k := k) (R := R) w
  have hL : IrreducibleSpace (PrimeSpectrum (R ⊗[k] L)) := h L
  -- Proof comment: the descended pair gives a concrete nonprime-nilradical witness at the finite
  -- separable stage, contradicting the hypothesis there.
  exact
    (not_irreducibleSpace_primeSpectrum_of_nonprime_nilradical_witness
      (A := R ⊗[k] L)
      ⟨{ left := xL
         right := yL
         mul_isNilpotent := hxy_nilpotent
         left_not_isNilpotent := hxL_not_nilpotent
         right_not_isNilpotent := hyL_not_nilpotent }⟩) hL

/-- Helper for Lemma 10.47.3: over an algebraically closed base, the relative algebraic closure in
an essentially finite type field extension is trivial. -/
private theorem algebraicClosure_eq_bot_of_isAlgClosed_of_essFiniteType
    {L K : Type u} [Field L] [Field K] [Algebra L K] [IsAlgClosed L]
    [Algebra.EssFiniteType L K] :
    algebraicClosure L K = ⊥ := by
  -- Proof comment: finite generation makes the relative algebraic closure finite-dimensional over
  -- `L`, hence algebraic over the algebraically closed base, so it must already be `L`.
  letI : FiniteDimensional L (algebraicClosure L K) := finiteDimensional_algebraicClosure L K
  exact IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure L K)

/-- Helper for Lemma 10.47.3: over an algebraically closed base, every field extension has trivial
relative algebraic closure. -/
private theorem algebraicClosure_eq_bot_of_isAlgClosed
    {L K : Type u} [Field L] [Field K] [Algebra L K] [IsAlgClosed L] :
    algebraicClosure L K = ⊥ := by
  -- Proof comment: the relative algebraic closure is algebraic over the base field, so
  -- algebraic closedness collapses it back to `L`.
  exact IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure L K)

/-- Helper for Lemma 10.47.3: over an algebraically closed base, the relative separable closure in
any field extension is trivial. -/
private theorem separableClosure_eq_bot_of_isAlgClosed
    {L K : Type u} [Field L] [Field K] [Algebra L K] [IsAlgClosed L] :
    separableClosure L K = ⊥ := by
  -- Proof comment: an algebraically closed field is separably closed, so a separable algebraic
  -- intermediate field over it must collapse to the base field.
  letI : IsSepClosed L := inferInstance
  exact IntermediateField.eq_bot_of_isSepClosed_of_isSeparable (separableClosure L K)

/-- Helper for Lemma 10.47.3: base changing the rational-function field of a multivariable
polynomial ring along a field extension is again a domain. -/
private theorem isDomain_tensor_fractionRing_of_mvPolynomial
    {L F ι : Type u} [Field L] [Field F] [Algebra L F] :
    IsDomain (FractionRing (MvPolynomial ι L) ⊗[L] F) := by
  let A : Type u := MvPolynomial ι L
  let B : Type u := MvPolynomial ι F
  letI : CommRing A := inferInstance
  letI : CommRing B := inferInstance
  letI : Algebra L A := inferInstance
  letI : Algebra L B := inferInstance
  letI : Algebra F B := inferInstance
  letI : Algebra A B := inferInstance
  letI : IsScalarTower L A B := inferInstance
  letI : Algebra.IsPushout L F A B := inferInstance
  let eCommL : FractionRing A ⊗[L] F ≃+* F ⊗[L] FractionRing A :=
    (Algebra.TensorProduct.comm L (FractionRing A) F).toRingEquiv
  let ePush : B ⊗[A] FractionRing A ≃+* F ⊗[L] FractionRing A :=
    (Algebra.IsPushout.cancelBaseChangeAlg L F A B (FractionRing A)).toRingEquiv
  let eCommA : B ⊗[A] FractionRing A ≃+* FractionRing A ⊗[A] B :=
    (Algebra.TensorProduct.comm A B (FractionRing A)).toRingEquiv
  let eLoc :
      FractionRing A ⊗[A] B ≃+*
        Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) :=
    (Localization.tensorRightAlgEquiv (nonZeroDivisors A) B).toRingEquiv
  let e :
      FractionRing A ⊗[L] F ≃+*
        Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) :=
    eCommL.trans (ePush.symm.trans (eCommA.trans eLoc))
  have hAB_inj : Function.Injective (algebraMap A B) := by
    simpa [A, B] using MvPolynomial.map_injective (algebraMap L F)
      (FaithfulSMul.algebraMap_injective L F)
  have hloc : IsDomain (Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))) := by
    exact IsLocalization.isDomain_localization
      (map_le_nonZeroDivisors_of_injective (algebraMap A B) hAB_inj le_rfl)
  -- Proof comment: identify the tensor with a localization of `F[X_i]` at the image of the
  -- nonzero elements of `L[X_i]`, which is a domain because the coefficient map is injective.
  exact e.isDomain_iff.mpr hloc

/-- Helper for Lemma 10.47.3: after identifying a transcendence-basis stage with a rational
function field, tensoring with any left field still yields a domain. -/
private theorem isDomain_tensorAdjoin_of_isTranscendenceBasis
    {L K F ι : Type u} [Field L] [Field K] [Field F]
    [Algebra L K] [Algebra L F]
    (x : ι → K) (hx : IsTranscendenceBasis L x) :
    IsDomain (F ⊗[L] IntermediateField.adjoin L (Set.range x)) := by
  let eAdjoin :
      F ⊗[L] IntermediateField.adjoin L (Set.range x) ≃+*
        F ⊗[L] FractionRing (MvPolynomial ι L) :=
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : F ≃ₐ[L] F)
      hx.1.aevalEquivField.symm).toRingEquiv
  let eComm :
      F ⊗[L] FractionRing (MvPolynomial ι L) ≃+*
        FractionRing (MvPolynomial ι L) ⊗[L] F :=
    (Algebra.TensorProduct.comm L F (FractionRing (MvPolynomial ι L))).toRingEquiv
  -- Proof comment: move to the rational-function model for the transcendence-basis field and use
  -- the fraction-ring base-change domain computation above.
  exact (eAdjoin.trans eComm).isDomain_iff.mpr
    (isDomain_tensor_fractionRing_of_mvPolynomial (L := L) (F := F) (ι := ι))

/-- Helper for Lemma 10.47.3: every coefficient of a monic divisor of the mapped minimal
polynomial already lies in the base field once the relative algebraic closure is trivial. -/
private theorem coeff_mem_bot_of_monic_dvd_mappedMinpoly
    {k K L : Type u} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    (pb : PowerBasis k L)
    (hclosed : algebraicClosure k K = ⊥)
    {q : Polynomial K} (hq_monic : q.Monic)
    (hq_dvd : q ∣ (minpoly k pb.gen).map (algebraMap k K)) :
    ∀ i : ℕ, q.coeff i ∈ (⊥ : IntermediateField k K) := by
  intro i
  -- Proof comment: coefficients of a monic divisor of the mapped minimal polynomial are integral
  -- over `k`, so the algebraic-closure hypothesis forces them back into the base field.
  have hcoeff_integral : IsIntegral k (q.coeff i) := by
    simpa using
      Polynomial.isIntegral_coeff_of_dvd
        (minpoly k pb.gen) q (minpoly.monic pb.isIntegral_gen) hq_monic hq_dvd i
  have hcoeff_mem : q.coeff i ∈ algebraicClosure k K := by
    exact mem_algebraicClosure_iff'.mpr hcoeff_integral
  simpa [hclosed] using hcoeff_mem

/-- Helper for Lemma 10.47.3: the mapped minimal polynomial of a primitive element stays
irreducible after base change once the relative algebraic closure is trivial. -/
private theorem mappedMinpoly_irreducible_of_algebraicClosure_eq_bot
    {k K L : Type u} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    (pb : PowerBasis k L)
    (hclosed : algebraicClosure k K = ⊥) :
    Irreducible ((minpoly k pb.gen).map (algebraMap k K)) := by
  let pK : Polynomial K := (minpoly k pb.gen).map (algebraMap k K)
  have hpK_monic : pK.Monic := by
    exact (minpoly.monic pb.isIntegral_gen).map (algebraMap k K)
  refine (hpK_monic.irreducible_iff_natDegree).2 ?_
  refine ⟨?_, ?_⟩
  · -- Proof comment: mapping the nonconstant minimal polynomial preserves positive degree.
    intro hpK_one
    have hdeg : 0 < pK.natDegree := by
      change 0 < ((minpoly k pb.gen).map (algebraMap k K)).natDegree
      rw [(minpoly.monic pb.isIntegral_gen).natDegree_map]
      exact minpoly.natDegree_pos pb.isIntegral_gen
    simpa [hpK_one] using hdeg
  · intro q r hq_monic hr_monic hqr
    have hq_dvd : q ∣ pK := ⟨r, hqr.symm⟩
    have hr_dvd : r ∣ pK := ⟨q, by rw [mul_comm, hqr]⟩
    have hq_lifts : q ∈ Polynomial.lifts (algebraMap k K) := by
      refine q.lifts_iff_coeff_lifts.mpr ?_
      intro i
      simpa [Algebra.mem_bot, Set.mem_range] using
        coeff_mem_bot_of_monic_dvd_mappedMinpoly
          (k := k) (K := K) (L := L) pb hclosed hq_monic hq_dvd i
    have hr_lifts : r ∈ Polynomial.lifts (algebraMap k K) := by
      refine r.lifts_iff_coeff_lifts.mpr ?_
      intro i
      simpa [Algebra.mem_bot, Set.mem_range] using
        coeff_mem_bot_of_monic_dvd_mappedMinpoly
          (k := k) (K := K) (L := L) pb hclosed hr_monic hr_dvd i
    obtain ⟨q0, hq0_map, hq0_deg, hq0_monic⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic hq_lifts hq_monic
    obtain ⟨r0, hr0_map, hr0_deg, hr0_monic⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic hr_lifts hr_monic
    have hfactor0 : q0 * r0 = minpoly k pb.gen := by
      -- Proof comment: once both factors descend coefficientwise, injectivity of `map`
      -- transports the factorization back to `k[X]`.
      apply Polynomial.map_injective (algebraMap k K) (FaithfulSMul.algebraMap_injective k K)
      simpa [pK, Polynomial.map_mul, hq0_map, hr0_map] using hqr
    rcases (minpoly.irreducible pb.isIntegral_gen).isUnit_or_isUnit hfactor0.symm with
        hq0_unit | hr0_unit
    · left
      have hq0_one : q0 = 1 := hq0_monic.eq_one_of_isUnit hq0_unit
      have hq0_nat : q0.natDegree = 0 := by simpa [hq0_one]
      simpa [hq0_deg] using hq0_nat
    · right
      have hr0_one : r0 = 1 := hr0_monic.eq_one_of_isUnit hr0_unit
      have hr0_nat : r0.natDegree = 0 := by simpa [hr0_one]
      simpa [hr0_deg] using hr0_nat

/-- Helper for Lemma 10.47.3: after finite separable base change, a primitive element still
generates the whole tensor product algebra. -/
private theorem tensorProduct_oneTmul_adjoin_eq_top_of_powerBasis
    {k K L : Type u} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    (pb : PowerBasis k L) :
    Algebra.adjoin K ({((1 : K) ⊗ₜ[k] pb.gen)} : Set (K ⊗[k] L)) = ⊤ := by
  -- Proof comment: this is the tensor-product companion of the primitive-element statement.
  simpa [Set.image_singleton] using
    (Algebra.TensorProduct.adjoin_one_tmul_image_eq_top
      (R := k) (A := K) ({pb.gen} : Set L) pb.adjoin_gen_eq_top)

/-- Helper for Lemma 10.47.3: if the right field extension is finite separable and the left field
has trivial relative algebraic closure over the base, then the tensor product is a domain. -/
private theorem isDomain_tensorProduct_finiteSeparable_of_algebraicClosure_eq_bot
    {k K L : Type u} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (hclosed : algebraicClosure k K = ⊥) :
    IsDomain (K ⊗[k] L) := by
  let pb : PowerBasis k L := Field.powerBasisOfFiniteOfSeparable k L
  let x : K ⊗[k] L := (1 : K) ⊗ₜ[k] pb.gen
  have hpK_irreducible :
      Irreducible ((minpoly k pb.gen).map (algebraMap k K)) :=
    mappedMinpoly_irreducible_of_algebraicClosure_eq_bot
      (k := k) (K := K) (L := L) pb hclosed
  have hpK_monic : ((minpoly k pb.gen).map (algebraMap k K)).Monic := by
    exact (minpoly.monic pb.isIntegral_gen).map (algebraMap k K)
  have hx_aeval : Polynomial.aeval x ((minpoly k pb.gen).map (algebraMap k K)) = 0 := by
    -- Proof comment: the tensor generator `1 ⊗ pb.gen` is the image of `pb.gen`, so the mapped
    -- minimal polynomial vanishes on it.
    rw [Polynomial.aeval_map_algebraMap (R := k) (A := K) (x := x) (p := minpoly k pb.gen)]
    change Polynomial.aeval
        ((Algebra.TensorProduct.includeRight (R := k) (A := K) (B := L)) pb.gen)
        (minpoly k pb.gen) = 0
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hminpoly :
      minpoly K x = (minpoly k pb.gen).map (algebraMap k K) := by
    -- Proof comment: `irreducible + monic + root` identifies the minimal polynomial upstairs.
    exact (minpoly.eq_of_irreducible_of_monic hpK_irreducible hx_aeval hpK_monic).symm
  have hAdjoinRootDomain : IsDomain (AdjoinRoot (minpoly K x)) := by
    -- Proof comment: irreducibility over a field upgrades to primality of the defining polynomial.
    have hprime : Prime (minpoly K x) := by
      rw [hminpoly]
      exact hpK_irreducible.prime
    exact AdjoinRoot.isDomain_of_prime hprime
  have hAdjoinDomain : IsDomain (Algebra.adjoin K ({x} : Set (K ⊗[k] L))) := by
    have hToAdjoin_injective :
        Function.Injective (AdjoinRoot.Minpoly.toAdjoin (R := K) (x := x)) := by
      -- Proof comment: a class in `AdjoinRoot` is zero as soon as its representing polynomial
      -- vanishes at the tensor generator.
      refine (injective_iff_map_eq_zero _).2 ?_
      intro y hy
      obtain ⟨p, rfl⟩ := (AdjoinRoot.mk_surjective (g := minpoly K x)) y
      rw [AdjoinRoot.Minpoly.coe_toAdjoin, AdjoinRoot.liftAlgHom_mk] at hy
      have hy' : Polynomial.aeval x p = 0 := by
        have hy'' :
            ((Polynomial.aeval ⟨x, Algebra.self_mem_adjoin_singleton (R := K) x⟩ p :
              Algebra.adjoin K ({x} : Set (K ⊗[k] L))) : K ⊗[k] L) = 0 := by
          exact congrArg
            (fun z : Algebra.adjoin K ({x} : Set (K ⊗[k] L)) => (z : K ⊗[k] L))
            hy
        rw [Polynomial.aeval_subalgebra_coe] at hy''
        exact hy''
      exact AdjoinRoot.mk_eq_zero.2 (minpoly.dvd K x hy')
    have hToAdjoin_surjective :
        Function.Surjective (AdjoinRoot.Minpoly.toAdjoin (R := K) (x := x)) :=
      AdjoinRoot.Minpoly.toAdjoin.surjective (R := K) (x := x)
    let eAdjoin :
        AdjoinRoot (minpoly K x) ≃ₐ[K] Algebra.adjoin K ({x} : Set (K ⊗[k] L)) :=
      AlgEquiv.ofBijective (AdjoinRoot.Minpoly.toAdjoin (R := K) (x := x))
        ⟨hToAdjoin_injective, hToAdjoin_surjective⟩
    letI : IsDomain (AdjoinRoot (minpoly K x)) := hAdjoinRootDomain
    exact MulEquiv.isDomain (AdjoinRoot (minpoly K x)) eAdjoin.toMulEquiv.symm
  have hgen : Algebra.adjoin K ({x} : Set (K ⊗[k] L)) = ⊤ := by
    -- Proof comment: the primitive element already generates the whole tensor product algebra.
    simpa [x] using tensorProduct_oneTmul_adjoin_eq_top_of_powerBasis
      (k := k) (K := K) (L := L) pb
  let eTop : Algebra.adjoin K ({x} : Set (K ⊗[k] L)) ≃ₐ[K] K ⊗[k] L :=
    (Subalgebra.equivOfEq _ _ hgen).trans Subalgebra.topEquiv
  -- Proof comment: transport the domain structure from the adjoin-root model to the full tensor
  -- product through the generator-equals-top identification.
  letI : IsDomain (Algebra.adjoin K ({x} : Set (K ⊗[k] L))) := hAdjoinDomain
  exact MulEquiv.isDomain (Algebra.adjoin K ({x} : Set (K ⊗[k] L))) eTop.toMulEquiv.symm

/-- Helper for Chap10 Lemma 10 47 3: over an algebraically closed base, finite separable
field-stage tensor products are domains. -/
private theorem isDomain_tensorProduct_finiteSeparable_of_isAlgClosed
    {L K F : Type u} [Field L] [IsAlgClosed L] [Field K] [Field F]
    [Algebra L K] [Algebra L F] [FiniteDimensional L F] [Algebra.IsSeparable L F] :
    IsDomain (K ⊗[L] F) := by
  -- Proof comment: algebraic closedness collapses the relative algebraic closure, so the
  -- finite-separable domain criterion above applies directly.
  exact
    isDomain_tensorProduct_finiteSeparable_of_algebraicClosure_eq_bot
      (k := L) (K := K) (L := F)
      (algebraicClosure_eq_bot_of_isAlgClosed (L := L) (K := K))

/-- Helper for Chap10 Lemma 10 47 3: a finite separable tensor product over a domain is a domain
when the base field is algebraically closed in the domain's fraction field. -/
private theorem isDomain_tensorProduct_domain_finiteSeparable_of_algebraicClosure_eq_bot
    {k A F : Type u} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Field F] [Algebra k F] [FiniteDimensional k F] [Algebra.IsSeparable k F]
    (hclosed : algebraicClosure k (FractionRing A) = ⊥) :
    IsDomain (A ⊗[k] F) := by
  let fracMap : A ⊗[k] F →ₐ[k] FractionRing A ⊗[k] F :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A (FractionRing A)) (AlgHom.id k F)
  have htarget : IsDomain (FractionRing A ⊗[k] F) :=
    isDomain_tensorProduct_finiteSeparable_of_algebraicClosure_eq_bot
      (k := k) (K := FractionRing A) (L := F) hclosed
  have hfrac_injective : Function.Injective fracMap := by
    -- Proof comment: tensoring the injective fraction map with a field over `k` preserves
    -- injectivity because both modules are flat over the base field.
    simpa [fracMap] using TensorProduct.map_injective_of_flat_flat
      (IsScalarTower.toAlgHom k A (FractionRing A)).toLinearMap
      (AlgHom.id k F).toLinearMap
      (FaithfulSMul.algebraMap_injective A (FractionRing A)) Function.injective_id
  -- Proof comment: pull the domain structure back along the injective map to the fraction-field
  -- tensor product.
  exact Function.Injective.isDomain fracMap.toRingHom hfrac_injective

/-- Helper for Chap10 Lemma 10 47 3: the finite separable field-stage tensor product has
irreducible prime spectrum over an algebraically closed base. -/
private theorem irreducibleSpace_primeSpectrum_ringTensor_finiteSeparable_of_algClosed
    {L K F : Type u} [Field L] [IsAlgClosed L] [Field K] [Field F]
    [Algebra L K] [Algebra L F] [FiniteDimensional L F] [Algebra.IsSeparable L F] :
    IrreducibleSpace (PrimeSpectrum (K ⊗[L] F)) := by
  -- Proof comment: once the tensor product is a domain, the prime spectrum is irreducible by the
  -- standard domain instance.
  letI : IsDomain (K ⊗[L] F) :=
    isDomain_tensorProduct_finiteSeparable_of_isAlgClosed (L := L) (K := K) (F := F)
  infer_instance

/-- Helper for Chap10 Lemma 10 47 3: transporting the right tensor factor from a smaller
intermediate field stage into the ambient field extension is compatible with stage inclusion. -/
private theorem fieldTensor_right_map_comp_inclusion
    {L K F : Type u} [Field L] [Field K] [Field F] [Algebra L K] [Algebra L F]
    {F₀ F₁ : IntermediateField L F} (hF : F₀ ≤ F₁) (x : K ⊗[L] F₀) :
    Algebra.TensorProduct.map (AlgHom.id L K) (IsScalarTower.toAlgHom L F₁ F)
      (Algebra.TensorProduct.map (AlgHom.id L K) (IntermediateField.inclusion hF) x) =
        Algebra.TensorProduct.map (AlgHom.id L K) (IsScalarTower.toAlgHom L F₀ F) x := by
  -- Proof comment: verify the compatibility on pure tensors, then extend across sums.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro a b
    simp [IntermediateField.coe_inclusion]
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for Chap10 Lemma 10 47 3: every tensor in `K ⊗[L] F` already comes from a finitely
generated intermediate field of `F / L` on the right tensor factor. -/
private theorem exists_finitely_generated_intermediate_field_rightTensor
    {L K F : Type u} [Field L] [Field K] [Field F] [Algebra L K] [Algebra L F]
    (x : K ⊗[L] F) :
    ∃ (F₀ : IntermediateField L F) (_ : F₀.FG) (x₀ : K ⊗[L] F₀),
      Algebra.TensorProduct.map (AlgHom.id L K) (IsScalarTower.toAlgHom L F₀ F) x₀ = x := by
  classical
  -- Proof comment: recursively collect the finitely many right-side field elements appearing in a
  -- tensor expression, adjoining them to `L` and taking suprema in the additive step.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · refine ⟨⊥, IntermediateField.fg_bot, 0, ?_⟩
    simp
  · intro a b
    let F₀ : IntermediateField L F := IntermediateField.adjoin L ({b} : Set F)
    have hbF₀ : b ∈ F₀ := IntermediateField.subset_adjoin L ({b} : Set F) (by simp)
    refine
      ⟨F₀,
        IntermediateField.fg_adjoin_of_finite (F := L) (E := F) (Set.finite_singleton b),
        a ⊗ₜ[L] ⟨b, hbF₀⟩, ?_⟩
    simp [F₀]
  · intro x y hx hy
    rcases hx with ⟨Fx, hFx, x₀, hx₀⟩
    rcases hy with ⟨Fy, hFy, y₀, hy₀⟩
    let F₀ : IntermediateField L F := Fx ⊔ Fy
    let x₀' : K ⊗[L] F₀ :=
      Algebra.TensorProduct.map
        (AlgHom.id L K)
        (IntermediateField.inclusion (show Fx ≤ F₀ from le_sup_left)) x₀
    let y₀' : K ⊗[L] F₀ :=
      Algebra.TensorProduct.map
        (AlgHom.id L K)
        (IntermediateField.inclusion (show Fy ≤ F₀ from le_sup_right)) y₀
    refine ⟨F₀, IntermediateField.fg_sup hFx hFy, x₀' + y₀', ?_⟩
    -- Proof comment: after both tensors are moved into the common right stage, the ambient image
    -- is the sum of their original ambient images.
    calc
      Algebra.TensorProduct.map (AlgHom.id L K) (IsScalarTower.toAlgHom L F₀ F) (x₀' + y₀') =
          Algebra.TensorProduct.map (AlgHom.id L K) (IsScalarTower.toAlgHom L F₀ F) x₀' +
            Algebra.TensorProduct.map (AlgHom.id L K) (IsScalarTower.toAlgHom L F₀ F) y₀' := by
              simp [x₀', y₀']
      _ =
          Algebra.TensorProduct.map (AlgHom.id L K) (IsScalarTower.toAlgHom L Fx F) x₀ +
            Algebra.TensorProduct.map (AlgHom.id L K) (IsScalarTower.toAlgHom L Fy F) y₀ := by
              rw [fieldTensor_right_map_comp_inclusion (L := L) (K := K) (F := F)
                    (show Fx ≤ F₀ from le_sup_left) x₀,
                fieldTensor_right_map_comp_inclusion (L := L) (K := K) (F := F)
                    (show Fy ≤ F₀ from le_sup_right) y₀]
      _ = x + y := by
          simpa [hx₀, hy₀]

/-- Helper for Chap10 Lemma 10 47 3: two tensors in `K ⊗[L] F` simultaneously descend to one
finitely generated intermediate field of `F / L` on the right. -/
private theorem exists_fg_stage_fieldTensor_pair_right
    {L K F : Type u} [Field L] [Field K] [Field F] [Algebra L K] [Algebra L F]
    (x y : K ⊗[L] F) :
    ∃ (F₀ : IntermediateField L F) (_ : F₀.FG) (x₀ y₀ : K ⊗[L] F₀),
      Algebra.TensorProduct.map (AlgHom.id L K) (IsScalarTower.toAlgHom L F₀ F) x₀ = x ∧
        Algebra.TensorProduct.map (AlgHom.id L K) (IsScalarTower.toAlgHom L F₀ F) y₀ = y := by
  obtain ⟨Fx, hFx, x₀, hx₀⟩ :=
    exists_finitely_generated_intermediate_field_rightTensor (L := L) (K := K) (F := F) x
  obtain ⟨Fy, hFy, y₀, hy₀⟩ :=
    exists_finitely_generated_intermediate_field_rightTensor (L := L) (K := K) (F := F) y
  let F₀ : IntermediateField L F := Fx ⊔ Fy
  let x₀' : K ⊗[L] F₀ :=
    Algebra.TensorProduct.map
      (AlgHom.id L K)
      (IntermediateField.inclusion (show Fx ≤ F₀ from le_sup_left)) x₀
  let y₀' : K ⊗[L] F₀ :=
    Algebra.TensorProduct.map
      (AlgHom.id L K)
      (IntermediateField.inclusion (show Fy ≤ F₀ from le_sup_right)) y₀
  refine ⟨F₀, IntermediateField.fg_sup hFx hFy, x₀', y₀', ?_, ?_⟩
  · -- Proof comment: enlarge the right stage for the first tensor to the common finitely
    -- generated stage.
    calc
      Algebra.TensorProduct.map (AlgHom.id L K) (IsScalarTower.toAlgHom L F₀ F) x₀' =
          Algebra.TensorProduct.map (AlgHom.id L K) (IsScalarTower.toAlgHom L Fx F) x₀ := by
            rw [fieldTensor_right_map_comp_inclusion (L := L) (K := K) (F := F)
              (show Fx ≤ F₀ from le_sup_left) x₀]
      _ = x := hx₀
  · -- Proof comment: the same enlargement works for the second tensor.
    calc
      Algebra.TensorProduct.map (AlgHom.id L K) (IsScalarTower.toAlgHom L F₀ F) y₀' =
          Algebra.TensorProduct.map (AlgHom.id L K) (IsScalarTower.toAlgHom L Fy F) y₀ := by
            rw [fieldTensor_right_map_comp_inclusion (L := L) (K := K) (F := F)
              (show Fy ≤ F₀ from le_sup_right) y₀]
      _ = y := hy₀

/-- Helper for Chap10 Lemma 10 47 3: a nonzero zero-divisor pair in `K ⊗[L] F` descends to a
finitely generated right-field stage. -/
private theorem exists_zeroDivisor_finitelyGenerated_right_stage
    {L K F : Type u} [Field L] [Field K] [Field F] [Algebra L K] [Algebra L F]
    {x y : K ⊗[L] F} (hxy : x * y = 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ (F₀ : IntermediateField L F) (_ : F₀.FG) (x₀ y₀ : K ⊗[L] F₀),
      Algebra.TensorProduct.map (AlgHom.id L K) (IsScalarTower.toAlgHom L F₀ F) x₀ = x ∧
        Algebra.TensorProduct.map (AlgHom.id L K) (IsScalarTower.toAlgHom L F₀ F) y₀ = y ∧
        x₀ * y₀ = 0 ∧ x₀ ≠ 0 ∧ y₀ ≠ 0 := by
  obtain ⟨F₀, hF₀, x₀, y₀, hx₀, hy₀⟩ :=
    exists_fg_stage_fieldTensor_pair_right (L := L) (K := K) (F := F) x y
  let stageMap : K ⊗[L] F₀ →ₐ[L] K ⊗[L] F :=
    Algebra.TensorProduct.map (AlgHom.id L K) (IsScalarTower.toAlgHom L F₀ F)
  have hstage_inj : Function.Injective stageMap := by
    -- Proof comment: tensoring the identity with the injective intermediate-field inclusion
    -- preserves injectivity because both modules over the base field are flat.
    simpa [stageMap] using TensorProduct.map_injective_of_flat_flat
      (AlgHom.id L K).toLinearMap (IsScalarTower.toAlgHom L F₀ F).toLinearMap
      Function.injective_id (IsScalarTower.toAlgHom L F₀ F).injective
  have hxy₀ : x₀ * y₀ = 0 := by
    -- Proof comment: the descended product maps to the ambient zero product, so injectivity pulls
    -- the equality back to the right finite stage.
    apply hstage_inj
    rw [map_mul, hx₀, hy₀, hxy, map_zero]
  have hx₀_ne : x₀ ≠ 0 := by
    intro hx₀_zero
    apply hx
    rw [← hx₀, hx₀_zero, map_zero]
  have hy₀_ne : y₀ ≠ 0 := by
    intro hy₀_zero
    apply hy
    rw [← hy₀, hy₀_zero, map_zero]
  exact ⟨F₀, hF₀, x₀, y₀, hx₀, hy₀, hxy₀, hx₀_ne, hy₀_ne⟩

/-- Helper for Chap10 Lemma 10 47 3: tensoring an irreducible affine scheme with a geometrically
irreducible affine scheme over the same field preserves irreducibility. -/
private theorem irreducibleSpace_primeSpectrum_tensorProduct_of_geometricallyIrreducible
    {L A B : Type u} [Field L] [CommRing A] [CommRing B] [Algebra L A] [Algebra L B]
    (hA : IrreducibleSpace (PrimeSpectrum A))
    [GeometricallyIrreducible (Spec.map (ofHom (algebraMap L B)))] :
    IrreducibleSpace (PrimeSpectrum (A ⊗[L] B)) := by
  let f : Spec (of (A ⊗[L] B)) ⟶ Spec (of A) :=
    Spec.map (ofHom (algebraMap A (A ⊗[L] B)))
  letI : GeometricallyIrreducible f := by
    -- Proof comment: identify the tensor projection with the affine pullback of
    -- `Spec B -> Spec L`, so geometric irreducibility is stable under base change.
    let e := pullbackSpecIso L A B
    letI : GeometricallyIrreducible (e.inv ≫ pullback.fst _ _) := by
      infer_instance
    simpa [f, e, pullbackSpecIso_inv_fst'] using
      (inferInstance : GeometricallyIrreducible (e.inv ≫ pullback.fst _ _))
  letI : IrreducibleSpace (Spec (of A)) := by
    simpa using hA
  -- Proof comment: the tensor projection is open over a field, so geometric irreducibility of the
  -- fibers and irreducibility of the base imply irreducibility of the total space.
  simpa using
    (GeometricallyIrreducible.irreducibleSpace f
      (by
        simpa using
          (PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field :
            IsOpenMap (PrimeSpectrum.comap (algebraMap A (A ⊗[L] B))))))

/-- Helper for Chap10 Lemma 10 47 3: linearly disjoint images of two field extensions in a common
overfield make their tensor product a domain. -/
private theorem isDomain_tensorProduct_of_linearlyDisjoint_commonField
    {L K F M : Type u} [Field L] [Field K] [Field F] [Field M]
    [Algebra L K] [Algebra L F] [Algebra L M]
    (iK : K →ₐ[L] M) (iF : F →ₐ[L] M)
    (hld : iK.fieldRange.LinearDisjoint iF.fieldRange) :
    IsDomain (K ⊗[L] F) := by
  -- Proof comment: mathlib's field-range linear-disjointness criterion is exactly the domain
  -- statement for tensor products of the two source fields.
  exact IntermediateField.LinearDisjoint.isDomain' hld

/-- Helper for Chap10 Lemma 10 47 3: a geometrically irreducible right field factor makes the
field-field tensor product irreducible. -/
private theorem irreducibleSpace_primeSpectrum_fieldTensor_field_of_geometricallyIrreducible
    {L K F : Type u} [Field L] [Field K] [Field F] [Algebra L K] [Algebra L F]
    [GeometricallyIrreducible (Spec.map (ofHom (algebraMap L F)))] :
    IrreducibleSpace (PrimeSpectrum (K ⊗[L] F)) := by
  -- Proof comment: specialize the affine tensor criterion to the irreducible field `K`.
  exact irreducibleSpace_primeSpectrum_tensorProduct_of_geometricallyIrreducible
    (L := L) (A := K) (B := F) inferInstance

/-- Helper for Chap10 Lemma 10 47 3: over an algebraically closed base, finitely generated
right-field tensor products are domains. -/
private theorem isDomain_tensorProduct_finitelyGeneratedField_of_isAlgClosed
    {L K F : Type u} [Field L] [IsAlgClosed L] [Field K] [Field F]
    [Algebra L K] [Algebra L F] [Algebra.EssFiniteType L F] :
    IsDomain (K ⊗[L] F) := by
  classical
  -- Proof comment: choose a separating transcendence basis for the finitely generated extension
  -- and reduce the target to the finite separable extension over the generated rational field.
  obtain ⟨s, hs, hsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_perfectField L F
  let A : IntermediateField L F :=
    IntermediateField.adjoin L (Set.range (Subtype.val : s → F))
  have hstage_domain : IsDomain (K ⊗[L] A) := by
    simpa [A] using
      isDomain_tensorAdjoin_of_isTranscendenceBasis
        (L := L) (K := F) (F := K) (x := (Subtype.val : s → F)) hs
  haveI : Algebra.IsSeparable A F := by
    have hrange : Set.range (Subtype.val : s → F) = (s : Set F) := Subtype.range_val
    dsimp [A]
    rw [hrange]
    exact hsep
  haveI : Algebra.IsAlgebraic A F := inferInstance
  haveI : Algebra.EssFiniteType A F := Algebra.EssFiniteType.of_comp L A F
  haveI : Module.Finite A F := Algebra.finite_of_essFiniteType_of_isAlgebraic
  haveI : FiniteDimensional A F := inferInstance
  have hclosed_needed :
      algebraicClosure A (FractionRing (K ⊗[L] A)) = ⊥ := by
    -- TODO: prove the regularity bridge by identifying the fraction field of
    -- `K ⊗[L] L(s)` with the rational-function tensor normal form; this is the first remaining
    -- blocker after the finite-separable-over-domain adapter above.
    sorry
  haveI : IsDomain (K ⊗[L] A) := hstage_domain
  have hfinite_stage : IsDomain ((K ⊗[L] A) ⊗[A] F) :=
    isDomain_tensorProduct_domain_finiteSeparable_of_algebraicClosure_eq_bot
      (k := A) (A := K ⊗[L] A) (F := F) hclosed_needed
  -- TODO: transport `hfinite_stage` across the canonical tensor base-change equivalence
  -- `(K ⊗[L] A) ⊗[A] F ≃+* K ⊗[L] F`.
  sorry

/-- Helper for Chap10 Lemma 10 47 3: over an algebraically closed base, tensor products of two
field extensions are domains. -/
private theorem isDomain_tensorProduct_field_of_isAlgClosed
    {L K F : Type u} [Field L] [IsAlgClosed L] [Field K] [Field F]
    [Algebra L K] [Algebra L F] :
    IsDomain (K ⊗[L] F) := by
  -- Proof comment: if a zero-divisor pair existed in the full tensor product, descend the two
  -- factors to one finitely generated right-field stage and contradict the finite-stage domain
  -- theorem.
  rw [isDomain_iff_noZeroDivisors_and_nontrivial]
  constructor
  · constructor
    intro x y hxy
    by_cases hx : x = 0
    · exact Or.inl hx
    by_cases hy : y = 0
    · exact Or.inr hy
    obtain ⟨F₀, hF₀, x₀, y₀, hx₀, hy₀, hxy₀, hx₀_ne, hy₀_ne⟩ :=
      exists_zeroDivisor_finitelyGenerated_right_stage
        (L := L) (K := K) (F := F) hxy hx hy
    haveI : Algebra.EssFiniteType L F₀ := (IntermediateField.essFiniteType_iff).mpr hF₀
    letI : IsDomain (K ⊗[L] F₀) :=
      isDomain_tensorProduct_finitelyGeneratedField_of_isAlgClosed
        (L := L) (K := K) (F := F₀)
    rcases mul_eq_zero.mp hxy₀ with hx₀_zero | hy₀_zero
    · exact False.elim (hx₀_ne hx₀_zero)
    · exact False.elim (hy₀_ne hy₀_zero)
  · exact Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left
      (R := L) (A := K) (B := F) (FaithfulSMul.algebraMap_injective L F)

/-- Helper for Chap10 Lemma 10 47 3: over an algebraically closed base, the prime spectrum of
a tensor product of two field extensions is irreducible. -/
private theorem irreducibleSpace_primeSpectrum_fieldTensor_field_of_isAlgClosed
    {L K F : Type u} [Field L] [IsAlgClosed L] [Field K] [Field F]
    [Algebra L K] [Algebra L F] :
    IrreducibleSpace (PrimeSpectrum (K ⊗[L] F)) := by
  -- Proof comment: the algebraically closed field-tensor theorem gives a domain, hence an
  -- irreducible prime spectrum.
  letI : IsDomain (K ⊗[L] F) :=
    isDomain_tensorProduct_field_of_isAlgClosed (L := L) (K := K) (F := F)
  infer_instance

/-- Helper for Chap10 Lemma 10 47 3: the fiber of a tensor-product projection is identified
with the residue-field tensor product for irreducibility purposes. -/
private theorem irreducibleSpace_primeSpectrum_fiber_tensorProduct_of_residueField
    {L A B : Type u} [Field L] [CommRing A] [CommRing B] [Algebra L A] [Algebra L B]
    (p : PrimeSpectrum A)
    (h : IrreducibleSpace (PrimeSpectrum (p.asIdeal.ResidueField ⊗[L] B))) :
    IrreducibleSpace (PrimeSpectrum (p.asIdeal.Fiber (A ⊗[L] B))) := by
  let e :=
    (Algebra.TensorProduct.cancelBaseChange L A A p.asIdeal.ResidueField B).toRingEquiv
  -- Proof comment: canceling the base change identifies the fiber ring with
  -- `κ(p) ⊗[L] B`, so irreducibility transports along the ring equivalence.
  exact (PrimeSpectrum.homeomorphOfRingEquiv e).irreducibleSpace_iff.2 h

/-- Helper for Chap10 Lemma 10 47 3: over an algebraically closed base, tensoring an irreducible
affine prime spectrum with a field preserves irreducibility. -/
private theorem irreducibleSpace_primeSpectrum_tensorProduct_field_of_isAlgClosed
    {L B K : Type u} [Field L] [IsAlgClosed L] [CommRing B] [Algebra L B]
    [Field K] [Algebra L K]
    (hB : IrreducibleSpace (PrimeSpectrum B)) :
    IrreducibleSpace (PrimeSpectrum (B ⊗[L] K)) := by
  -- Proof comment: apply the open-map criterion; every fiber is a tensor product of two field
  -- extensions over the algebraically closed base.
  refine irreducibleSpace_primeSpectrum_of_isOpenMap_of_dense_irreducible_fibers
    hB PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field ?_
  have hall :
      { p : PrimeSpectrum B |
          IrreducibleSpace (PrimeSpectrum (p.asIdeal.Fiber (B ⊗[L] K))) } = Set.univ := by
    ext p
    constructor
    · intro _
      trivial
    · intro _
      exact irreducibleSpace_primeSpectrum_fiber_tensorProduct_of_residueField p
        (irreducibleSpace_primeSpectrum_fieldTensor_field_of_isAlgClosed
          (L := L) (K := p.asIdeal.ResidueField) (F := K))
  rw [hall]
  exact dense_univ

/-- Helper for Chap10 Lemma 10 47 3: over an algebraically closed base, the same field
base-change theorem with the field factor on the left. -/
private theorem irreducibleSpace_primeSpectrum_field_tensorProduct_of_isAlgClosed
    {L B K : Type u} [Field L] [IsAlgClosed L] [CommRing B] [Algebra L B]
    [Field K] [Algebra L K]
    (hB : IrreducibleSpace (PrimeSpectrum B)) :
    IrreducibleSpace (PrimeSpectrum (K ⊗[L] B)) := by
  let e := (Algebra.TensorProduct.comm L K B).toRingEquiv
  -- Proof comment: commute the tensor factors and use the right-field version.
  exact (PrimeSpectrum.homeomorphOfRingEquiv e).irreducibleSpace_iff.2
    (irreducibleSpace_primeSpectrum_tensorProduct_field_of_isAlgClosed
      (L := L) (B := B) (K := K) hB)

/-- Helper for Chap10 Lemma 10 47 3: over an algebraically closed base, tensoring two algebras
with irreducible prime spectra preserves irreducibility. -/
private theorem irreducibleSpace_primeSpectrum_tensorProduct_of_isAlgClosed_source
    {L A B : Type u} [Field L] [IsAlgClosed L] [CommRing A] [CommRing B]
    [Algebra L A] [Algebra L B]
    (hA : IrreducibleSpace (PrimeSpectrum A))
    (hB : IrreducibleSpace (PrimeSpectrum B)) :
    IrreducibleSpace (PrimeSpectrum (A ⊗[L] B)) := by
  -- Proof comment: the affine open-map criterion reduces the tensor product to residue-field
  -- fibers, and the field-left algebraically closed theorem handles those fibers.
  refine irreducibleSpace_primeSpectrum_of_isOpenMap_of_dense_irreducible_fibers
    hA PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field ?_
  have hall :
      { p : PrimeSpectrum A |
          IrreducibleSpace (PrimeSpectrum (p.asIdeal.Fiber (A ⊗[L] B))) } = Set.univ := by
    ext p
    constructor
    · intro _
      trivial
    · intro _
      exact irreducibleSpace_primeSpectrum_fiber_tensorProduct_of_residueField p
        (irreducibleSpace_primeSpectrum_field_tensorProduct_of_isAlgClosed
          (L := L) (B := B) (K := p.asIdeal.ResidueField) hB)
  rw [hall]
  exact dense_univ

/-- Helper for Chap10 Lemma 10 47 3: irreducibility of prime spectra is invariant under purely
inseparable tensor base change by a field. -/
private theorem irreducibleSpace_primeSpectrum_tensorProduct_of_purelyInseparable_baseChange
    {L Ω A : Type u} [Field L] [Field Ω] [CommRing A] [Algebra L Ω] [Algebra L A]
    [IsPurelyInseparable L Ω] :
    IrreducibleSpace (PrimeSpectrum (Ω ⊗[L] A)) ↔
      IrreducibleSpace (PrimeSpectrum A) := by
  have hHomeo :
      IsHomeomorph
        (PrimeSpectrum.comap
          ((Algebra.TensorProduct.map
            (Algebra.ofId L Ω)
            (AlgHom.id L A)).toRingHom)) :=
    PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable
      (R := L) (K := L) (S := A) (L := Ω)
  let eBase : L ⊗[L] A ≃ₐ[L] A := Algebra.TensorProduct.lid L A
  constructor
  · intro hΩ
    -- Proof comment: descend through the universal homeomorphism, then remove the trivial
    -- `L`-tensor factor.
    have hBase : IrreducibleSpace (PrimeSpectrum (L ⊗[L] A)) :=
      (hHomeo.homeomorph _).irreducibleSpace_iff.1 hΩ
    exact (PrimeSpectrum.homeomorphOfRingEquiv eBase.toRingEquiv).irreducibleSpace_iff.1 hBase
  · intro hA
    -- Proof comment: add the trivial base tensor and lift across the same universal
    -- homeomorphism.
    have hBase : IrreducibleSpace (PrimeSpectrum (L ⊗[L] A)) :=
      (PrimeSpectrum.homeomorphOfRingEquiv eBase.toRingEquiv).irreducibleSpace_iff.2 hA
    exact (hHomeo.homeomorph _).irreducibleSpace_iff.2 hBase

/-- Helper for Chap10 Lemma 10 47 3: over a separably closed base field, the tensor product of
two field extensions has irreducible prime spectrum. -/
private theorem irreducibleSpace_primeSpectrum_fieldTensor_field_of_isSepClosed
    {L K F : Type u} [Field L] [IsSepClosed L] [Field K] [Field F]
    [Algebra L K] [Algebra L F] :
    IrreducibleSpace (PrimeSpectrum (K ⊗[L] F)) := by
  -- Route correction: avoid the circular geometric-irreducibility premise.  Base change to the
  -- algebraic closure, prove irreducibility there by the algebraically closed field-tensor
  -- theorem, then descend across the purely inseparable universal homeomorphism.
  let Ω : Type u := AlgebraicClosure L
  letI : Field Ω := inferInstance
  letI : Algebra L Ω := inferInstance
  haveI : IsPurelyInseparable L Ω :=
    (isSepClosed_iff_isPurelyInseparable_algebraicClosure L Ω).mp inferInstance
  have hHomeo :
      IsHomeomorph
        (PrimeSpectrum.comap
          ((Algebra.TensorProduct.map
            (Algebra.ofId L Ω)
            (AlgHom.id L (K ⊗[L] F))).toRingHom)) :=
    PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable
      (R := L) (K := L) (S := K ⊗[L] F) (L := Ω)
  have hOmega : IrreducibleSpace (PrimeSpectrum (Ω ⊗[L] (K ⊗[L] F))) := by
    let e :
        (Ω ⊗[L] K) ⊗[Ω] (Ω ⊗[L] F) ≃+* Ω ⊗[L] (K ⊗[L] F) :=
      ((Algebra.TensorProduct.cancelBaseChange L Ω Ω (Ω ⊗[L] K) F).trans
        (Algebra.TensorProduct.assoc L L Ω Ω K F)).toRingEquiv
    have hSource :
        IrreducibleSpace (PrimeSpectrum ((Ω ⊗[L] K) ⊗[Ω] (Ω ⊗[L] F))) := by
      have hLeft : IrreducibleSpace (PrimeSpectrum (Ω ⊗[L] K)) :=
        (irreducibleSpace_primeSpectrum_tensorProduct_of_purelyInseparable_baseChange
          (L := L) (Ω := Ω) (A := K)).2 inferInstance
      have hRight : IrreducibleSpace (PrimeSpectrum (Ω ⊗[L] F)) :=
        (irreducibleSpace_primeSpectrum_tensorProduct_of_purelyInseparable_baseChange
          (L := L) (Ω := Ω) (A := F)).2 inferInstance
      -- Proof comment: after both factors have irreducible spectra over `Ω`, the algebraically
      -- closed source theorem gives irreducibility of their tensor over `Ω`.
      exact irreducibleSpace_primeSpectrum_tensorProduct_of_isAlgClosed_source
        (L := Ω) (A := Ω ⊗[L] K) (B := Ω ⊗[L] F) hLeft hRight
    exact (PrimeSpectrum.homeomorphOfRingEquiv e).irreducibleSpace_iff.1 hSource
  have hBaseTensor : IrreducibleSpace (PrimeSpectrum (L ⊗[L] (K ⊗[L] F))) := by
    exact (hHomeo.homeomorph _).irreducibleSpace_iff.1 hOmega
  let eBase : L ⊗[L] (K ⊗[L] F) ≃ₐ[L] K ⊗[L] F :=
    Algebra.TensorProduct.lid L (K ⊗[L] F)
  -- Proof comment: identify the trivial base-change tensor with the original tensor product.
  exact (PrimeSpectrum.homeomorphOfRingEquiv eBase.toRingEquiv).irreducibleSpace_iff.1 hBaseTensor

/-- Helper for Chap10 Lemma 10 47 3: the fiber of the tensor-product projection over a prime is
the corresponding residue-field tensor product, up to irreducibility of prime spectra. -/
private theorem irreducibleSpace_primeSpectrum_fiber_tensorProduct
    {L A B : Type u} [Field L] [CommRing A] [CommRing B] [Algebra L A] [Algebra L B]
    (p : PrimeSpectrum A)
    (h : IrreducibleSpace (PrimeSpectrum (p.asIdeal.ResidueField ⊗[L] B))) :
    IrreducibleSpace (PrimeSpectrum (p.asIdeal.Fiber (A ⊗[L] B))) := by
  let e :=
    (Algebra.TensorProduct.cancelBaseChange L A A p.asIdeal.ResidueField B).toRingEquiv
  -- Proof comment: `Ideal.Fiber` is `κ(p) ⊗[A] (A ⊗[L] B)`, and canceling the base change
  -- identifies it with `κ(p) ⊗[L] B`.
  exact (PrimeSpectrum.homeomorphOfRingEquiv e).irreducibleSpace_iff.2 h

/-- Helper for Chap10 Lemma 10 47 3: over a separably closed base, base change of an irreducible
affine spectrum to a field extension remains irreducible. -/
private theorem irreducibleSpace_primeSpectrum_tensorProduct_field_of_isSepClosed
    {L B K : Type u} [Field L] [IsSepClosed L] [CommRing B] [Algebra L B]
    [Field K] [Algebra L K]
    (hB : IrreducibleSpace (PrimeSpectrum B)) :
    IrreducibleSpace (PrimeSpectrum (B ⊗[L] K)) := by
  -- Proof comment: apply the affine open-map criterion to `Spec (B ⊗ K) -> Spec B`;
  -- every fiber is a field-field tensor product over the separably closed base.
  refine irreducibleSpace_primeSpectrum_of_isOpenMap_of_dense_irreducible_fibers
    hB PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field ?_
  have hall :
      { p : PrimeSpectrum B |
          IrreducibleSpace (PrimeSpectrum (p.asIdeal.Fiber (B ⊗[L] K))) } = Set.univ := by
    ext p
    constructor
    · intro _
      trivial
    · intro _
      exact irreducibleSpace_primeSpectrum_fiber_tensorProduct p
        (irreducibleSpace_primeSpectrum_fieldTensor_field_of_isSepClosed
          (L := L) (K := p.asIdeal.ResidueField) (F := K))
  rw [hall]
  exact dense_univ

/-- Helper for Chap10 Lemma 10 47 3: the same field base-change result with the field factor on
the left of the tensor product. -/
private theorem irreducibleSpace_primeSpectrum_field_tensorProduct_of_isSepClosed
    {L B K : Type u} [Field L] [IsSepClosed L] [CommRing B] [Algebra L B]
    [Field K] [Algebra L K]
    (hB : IrreducibleSpace (PrimeSpectrum B)) :
    IrreducibleSpace (PrimeSpectrum (K ⊗[L] B)) := by
  let e := (Algebra.TensorProduct.comm L K B).toRingEquiv
  -- Proof comment: commute the tensor factors and use the one-sided field base-change theorem.
  exact (PrimeSpectrum.homeomorphOfRingEquiv e).irreducibleSpace_iff.2
    (irreducibleSpace_primeSpectrum_tensorProduct_field_of_isSepClosed
      (L := L) (B := B) (K := K) hB)

/-- Helper for Chap10 Lemma 10 47 3: over a separably closed base, tensoring two algebras
with irreducible prime spectra preserves irreducibility. -/
private theorem irreducibleSpace_primeSpectrum_tensorProduct_of_isSepClosed_source
    {L A B : Type u} [Field L] [IsSepClosed L] [CommRing A] [CommRing B]
    [Algebra L A] [Algebra L B]
    (hA : IrreducibleSpace (PrimeSpectrum A))
    (hB : IrreducibleSpace (PrimeSpectrum B)) :
    IrreducibleSpace (PrimeSpectrum (A ⊗[L] B)) := by
  -- Route correction: avoid the later geometric-irreducibility criterion and use the affine
  -- open-map criterion directly; the fibers are residue-field tensor products with `B`.
  refine irreducibleSpace_primeSpectrum_of_isOpenMap_of_dense_irreducible_fibers
    hA PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field ?_
  have hall :
      { p : PrimeSpectrum A |
          IrreducibleSpace (PrimeSpectrum (p.asIdeal.Fiber (A ⊗[L] B))) } = Set.univ := by
    ext p
    constructor
    · intro _
      trivial
    · intro _
      exact irreducibleSpace_primeSpectrum_fiber_tensorProduct p
        (irreducibleSpace_primeSpectrum_field_tensorProduct_of_isSepClosed
          (L := L) (B := B) (K := p.asIdeal.ResidueField) hB)
  rw [hall]
  exact dense_univ

/-- Helper for Lemma 10.47.3: over an algebraically closed base field, tensoring an algebra with
an arbitrary field extension preserves irreducibility of prime spectra. -/
private theorem irreducibleSpace_primeSpectrum_tensorProduct_of_algClosed_base
    {L A F : Type u} [Field L] [IsAlgClosed L] [CommRing A] [Algebra L A] [Field F] [Algebra L F]
    (hA : IrreducibleSpace (PrimeSpectrum A)) :
    IrreducibleSpace (PrimeSpectrum (A ⊗[L] F)) := by
  -- Route correction: use the source-facing separably-closed tensor theorem rather than the failed
  -- finite-generated zero-divisor specialization route.
  exact irreducibleSpace_primeSpectrum_tensorProduct_of_isSepClosed_source
    (L := L) (A := A) (B := F) hA inferInstance

/-- Helper for Chap10 Lemma 10 47 3: after base change to `AlgebraicClosure k`, tensoring
further with a field extension preserves irreducibility of prime spectra. -/
private theorem irreducibleSpace_iteratedTensor_of_algebraicClosure_base
    {k R F : Type u} [Field k] [CommRing R] [Algebra k R] [Field F] [Algebra k F]
    [Algebra (AlgebraicClosure k) F] [IsScalarTower k (AlgebraicClosure k) F]
    (h : IrreducibleSpace (PrimeSpectrum (R ⊗[k] AlgebraicClosure k))) :
    IrreducibleSpace
      (PrimeSpectrum ((R ⊗[k] AlgebraicClosure k) ⊗[AlgebraicClosure k] F)) := by
  -- Proof comment: view the iterated tensor as base change over the algebraically closed field
  -- `AlgebraicClosure k`, then apply the algebraically closed base-change helper.
  exact irreducibleSpace_primeSpectrum_tensorProduct_of_algClosed_base
    (L := AlgebraicClosure k) (A := R ⊗[k] AlgebraicClosure k) (F := F) h

-- Proof sketch: `(1) → (2)` is immediate. For `(2) → (3)`, write `SeparableClosure k` as the
-- union of its finite separable subextensions and use flat going-down to compare minimal primes.
-- For `(3) → (4)`, the extension from the separable closure to the algebraic closure is purely
-- inseparable, so the induced map on spectra is a homeomorphism. For `(4) → (1)`, embed an
-- arbitrary field extension and `AlgebraicClosure k` into a common overfield and use flat
-- injective base change plus the unique-minimal-prime criterion from Lemma `10.47.2`.
/-- Lemma 10.47.3: for a `k`-algebra `R`, the following are equivalent: every base change to a
field extension of `k` has irreducible prime spectrum, every base change to a finite separable
field extension of `k` has irreducible prime spectrum, the base change to `SeparableClosure k` has
irreducible prime spectrum, and the base change to `AlgebraicClosure k` has irreducible prime
spectrum. -/
@[stacks 037K]
theorem irreducibleSpace_primeSpectrum_baseChange_tfae :
    List.TFAE
      [ (∀ (K : Type u) [Field K] [Algebra k K],
            IrreducibleSpace (PrimeSpectrum (R ⊗[k] K))),
        (∀ (K : Type u) [Field K] [Algebra k K]
            [FiniteDimensional k K] [Algebra.IsSeparable k K],
            IrreducibleSpace (PrimeSpectrum (R ⊗[k] K))),
        IrreducibleSpace (PrimeSpectrum (R ⊗[k] SeparableClosure k)),
        IrreducibleSpace (PrimeSpectrum (R ⊗[k] AlgebraicClosure k)) ] := by
  tfae_have 1 → 2 := by
    intro h1 K _ _ _ _
    -- Proof comment: finite separable extensions are a special case of arbitrary extensions.
    exact h1 K
  tfae_have 2 → 3 := by
    intro h2
    -- Proof comment: any witness to non-irreducibility over the separable closure descends to a
    -- finite separable stage, contradicting the hypothesis.
    exact irreducibleSpace_primeSpectrum_separableClosure_of_finiteSeparable
      (k := k) (R := R) h2
  tfae_have 3 → 4 := by
    intro h3
    -- Proof comment: `AlgebraicClosure k / SeparableClosure k` is purely inseparable, so this
    -- base change induces a homeomorphism on prime spectra after commuting the tensor factors.
    let eSep :
        SeparableClosure k ⊗[k] R ≃ₐ[SeparableClosure k] R ⊗[k] SeparableClosure k :=
      Algebra.TensorProduct.commRight k (SeparableClosure k) R
    have hSepLeft : IrreducibleSpace (PrimeSpectrum (SeparableClosure k ⊗[k] R)) := by
      exact (PrimeSpectrum.homeomorphOfRingEquiv eSep.toRingEquiv).irreducibleSpace_iff.2 h3
    let hHomeo :
        IsHomeomorph
          (PrimeSpectrum.comap
            ((Algebra.TensorProduct.map
              (Algebra.ofId (SeparableClosure k) (AlgebraicClosure k))
              (AlgHom.id k R)).toRingHom)) :=
      PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable
        (R := k) (K := SeparableClosure k) (S := R) (L := AlgebraicClosure k)
    have hAlgLeft : IrreducibleSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] R)) := by
      exact (hHomeo.homeomorph _).irreducibleSpace_iff.2 hSepLeft
    let eAlg :
        AlgebraicClosure k ⊗[k] R ≃ₐ[AlgebraicClosure k] R ⊗[k] AlgebraicClosure k :=
      Algebra.TensorProduct.commRight k (AlgebraicClosure k) R
    exact (PrimeSpectrum.homeomorphOfRingEquiv eAlg.toRingEquiv).irreducibleSpace_iff.1 hAlgLeft
  tfae_have 4 → 1 := by
    intro h4 K _ _
    obtain ⟨F, _, _, iK, iAlg, hiK, hiAlg⟩ :=
      exists_common_field_extension (k := k) (E := K) (F := AlgebraicClosure k)
    letI : Algebra (AlgebraicClosure k) F := iAlg.toAlgebra
    letI : IsScalarTower k (AlgebraicClosure k) F := by
      refine IsScalarTower.of_algebraMap_eq ?_
      intro x
      exact (iAlg.commutes x).symm
    let baseChangeMap : R ⊗[k] K →ₐ[k] R ⊗[k] F :=
      Algebra.TensorProduct.map (AlgHom.id k R) iK
    have hbaseChangeMap_injective : Function.Injective baseChangeMap := by
      -- Proof comment: tensoring the injective field embedding `K ↪ F` with the identity on `R`
      -- preserves injectivity because both tensor factors are flat over `k`.
      simpa [baseChangeMap] using TensorProduct.map_injective_of_flat_flat
        (AlgHom.id k R).toLinearMap iK.toLinearMap Function.injective_id hiK
    have hFalg :
        IrreducibleSpace
          (PrimeSpectrum ((R ⊗[k] AlgebraicClosure k) ⊗[AlgebraicClosure k] F)) := by
      -- Proof comment: after passing to the common overfield, use the isolated iterated
      -- base-change adapter so the transport comparison below stays separate.
      exact irreducibleSpace_iteratedTensor_of_algebraicClosure_base
        (k := k) (R := R) (F := F) h4
    let e1 :
        ((R ⊗[k] AlgebraicClosure k) ⊗[AlgebraicClosure k] F) ≃+*
          F ⊗[AlgebraicClosure k] (R ⊗[k] AlgebraicClosure k) :=
      (Algebra.TensorProduct.commRight (AlgebraicClosure k) F
        (R ⊗[k] AlgebraicClosure k)).symm.toRingEquiv
    let e2 :
        F ⊗[AlgebraicClosure k] (R ⊗[k] AlgebraicClosure k) ≃+*
          F ⊗[AlgebraicClosure k] (AlgebraicClosure k ⊗[k] R) :=
      (Algebra.TensorProduct.congr
        (AlgEquiv.refl : F ≃ₐ[AlgebraicClosure k] F)
        (Algebra.TensorProduct.commRight k (AlgebraicClosure k) R).symm).toRingEquiv
    let e3 :
        F ⊗[AlgebraicClosure k] (AlgebraicClosure k ⊗[k] R) ≃+* F ⊗[k] R :=
      (Algebra.TensorProduct.cancelBaseChange k (AlgebraicClosure k) F F R).toRingEquiv
    let e4 : F ⊗[k] R ≃+* R ⊗[k] F :=
      (Algebra.TensorProduct.comm k R F).symm.toRingEquiv
    let eCompare :
        ((R ⊗[k] AlgebraicClosure k) ⊗[AlgebraicClosure k] F) ≃+* R ⊗[k] F :=
      e1.trans <| e2.trans <| e3.trans e4
    have hRF : IrreducibleSpace (PrimeSpectrum (R ⊗[k] F)) := by
      -- Proof comment: compare the iterated base change with the ambient tensor product by the
      -- standard `commRight + cancelBaseChange` ring equivalence.
      exact (PrimeSpectrum.homeomorphOfRingEquiv eCompare).irreducibleSpace_iff.1 hFalg
    -- Proof comment: irreducibility then descends from the common overfield tensor product to the
    -- original base change along the injective flat map `R ⊗[k] K → R ⊗[k] F`.
    exact irreducibleSpace_primeSpectrum_of_injective baseChangeMap.toRingHom
      hbaseChangeMap_injective hRF
  tfae_finish

private theorem geometricallyIrreducible_tfae :
    List.TFAE
      [ GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))),
        (∀ (K : Type u) [Field K] [Algebra k K]
            [FiniteDimensional k K] [Algebra.IsSeparable k K],
            IrreducibleSpace (PrimeSpectrum (R ⊗[k] K))),
        IrreducibleSpace (PrimeSpectrum (R ⊗[k] SeparableClosure k)),
        IrreducibleSpace (PrimeSpectrum (R ⊗[k] AlgebraicClosure k)) ] := by
  have htfae :
      List.TFAE
        [ (∀ (K : Type u) [Field K] [Algebra k K],
              IrreducibleSpace (PrimeSpectrum (R ⊗[k] K))),
          (∀ (K : Type u) [Field K] [Algebra k K]
              [FiniteDimensional k K] [Algebra.IsSeparable k K],
              IrreducibleSpace (PrimeSpectrum (R ⊗[k] K))),
          IrreducibleSpace (PrimeSpectrum (R ⊗[k] SeparableClosure k)),
          IrreducibleSpace (PrimeSpectrum (R ⊗[k] AlgebraicClosure k)) ] :=
    irreducibleSpace_primeSpectrum_baseChange_tfae
  let hgeom :
      GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))) ↔
        ∀ (K : Type u) [Field K] [Algebra k K],
          IrreducibleSpace (PrimeSpectrum (R ⊗[k] K)) :=
    geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_baseChange
  tfae_have 1 ↔ 2 := by
    exact hgeom.trans <| htfae.out 0 1 (by simp) (by simp)
  tfae_have 1 ↔ 3 := by
    exact hgeom.trans <| htfae.out 0 2 (by simp) (by simp)
  tfae_have 1 ↔ 4 := by
    exact hgeom.trans <| htfae.out 0 3 (by simp) (by simp)
  tfae_finish

/-- Canonical geometric-irreducibility form of Lemma 10.47.3, clauses `(1) ↔ (2)`: it is enough
to test irreducibility of `PrimeSpectrum (R ⊗[k] K)` on finite separable extensions of `k`. -/
theorem geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_finiteSeparable_baseChange :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))) ↔
      ∀ (K : Type u) [Field K] [Algebra k K]
        [FiniteDimensional k K] [Algebra.IsSeparable k K],
        IrreducibleSpace (PrimeSpectrum (R ⊗[k] K)) := by
  have htfae :
      List.TFAE
        [ GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))),
          (∀ (K : Type u) [Field K] [Algebra k K]
              [FiniteDimensional k K] [Algebra.IsSeparable k K],
              IrreducibleSpace (PrimeSpectrum (R ⊗[k] K))),
          IrreducibleSpace (PrimeSpectrum (R ⊗[k] SeparableClosure k)),
          IrreducibleSpace (PrimeSpectrum (R ⊗[k] AlgebraicClosure k)) ] :=
    geometricallyIrreducible_tfae
  simpa using htfae.out 0 1 (by simp) (by simp)

/-- Canonical geometric-irreducibility form of Lemma 10.47.3, clauses `(1) ↔ (3)`: a `k`-algebra
is geometrically irreducible iff its base change to `SeparableClosure k` has irreducible prime
spectrum. -/
theorem geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_separableClosure :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))) ↔
      IrreducibleSpace (PrimeSpectrum (R ⊗[k] SeparableClosure k)) := by
  have htfae :
      List.TFAE
        [ GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))),
          (∀ (K : Type u) [Field K] [Algebra k K]
              [FiniteDimensional k K] [Algebra.IsSeparable k K],
              IrreducibleSpace (PrimeSpectrum (R ⊗[k] K))),
          IrreducibleSpace (PrimeSpectrum (R ⊗[k] SeparableClosure k)),
          IrreducibleSpace (PrimeSpectrum (R ⊗[k] AlgebraicClosure k)) ] :=
    geometricallyIrreducible_tfae
  simpa using htfae.out 0 2 (by simp) (by simp)

/-- Helper for Chap10 Lemma 10 47 3: over a separably closed base, irreducibility of
`PrimeSpectrum B` makes `Spec B ⟶ Spec L` geometrically irreducible. -/
private theorem geometricallyIrreducible_of_irreducibleSpace_primeSpectrum_of_isSepClosed
    {L B : Type u} [Field L] [IsSepClosed L] [CommRing B] [Algebra L B]
    (hB : IrreducibleSpace (PrimeSpectrum B)) :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap L B))) := by
  -- Route correction: prove the separably-closed bridge only after the separable-closure
  -- criterion is available, avoiding the earlier circular tensor theorem.
  let eK : SeparableClosure L ≃ₐ[L] L := IsSepClosure.equiv L (SeparableClosure L) L
  let e : B ⊗[L] SeparableClosure L ≃ₐ[B] B :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B) eK).trans
      (Algebra.TensorProduct.rid L B B)
  exact geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_separableClosure.2 <|
    (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).irreducibleSpace_iff.2 <| by
      simpa using hB

/-- Helper for Chap10 Lemma 10 47 3: source-facing tensor irreducibility over a separably closed
base. This is the canonical Lemma 10.47.2 input recovered after Lemma 10.47.3. -/
private theorem irreducibleSpace_primeSpectrum_tensorProduct_of_isSepClosed
    {L A B : Type u} [Field L] [IsSepClosed L] [CommRing A] [CommRing B]
    [Algebra L A] [Algebra L B]
    (hA : IrreducibleSpace (PrimeSpectrum A))
    (hB : IrreducibleSpace (PrimeSpectrum B)) :
    IrreducibleSpace (PrimeSpectrum (A ⊗[L] B)) := by
  have hgeomB : GeometricallyIrreducible (Spec.map (ofHom (algebraMap L B))) :=
    geometricallyIrreducible_of_irreducibleSpace_primeSpectrum_of_isSepClosed hB
  letI : GeometricallyIrreducible (Spec.map (ofHom (algebraMap L B))) := hgeomB
  -- Proof comment: once `B` is geometrically irreducible over the separably closed base, the
  -- tensor-product projection proves the desired irreducibility.
  exact irreducibleSpace_primeSpectrum_tensorProduct_of_geometricallyIrreducible
    (L := L) (A := A) (B := B) hA

/-- Canonical geometric-irreducibility form of Lemma 10.47.3, clauses `(1) ↔ (4)`: a `k`-algebra
is geometrically irreducible iff its base change to `AlgebraicClosure k` has irreducible prime
spectrum. -/
theorem geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_algebraicClosure :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))) ↔
      IrreducibleSpace (PrimeSpectrum (R ⊗[k] AlgebraicClosure k)) := by
  have htfae :
      List.TFAE
        [ GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))),
          (∀ (K : Type u) [Field K] [Algebra k K]
              [FiniteDimensional k K] [Algebra.IsSeparable k K],
              IrreducibleSpace (PrimeSpectrum (R ⊗[k] K))),
          IrreducibleSpace (PrimeSpectrum (R ⊗[k] SeparableClosure k)),
          IrreducibleSpace (PrimeSpectrum (R ⊗[k] AlgebraicClosure k)) ] :=
    geometricallyIrreducible_tfae
  simpa using htfae.out 0 3 (by simp) (by simp)

end
