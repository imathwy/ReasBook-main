import Mathlib
import stacks_project.Chap09.Lemma_9_6_9
import stacks_project.Chap09.Lemma_9_26_11
import stacks_project.Chap10.Lemma_10_47_1
import stacks_project.Chap10.Definition_10_47_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct
open AlgebraicGeometry CommRingCat
attribute [local instance] Algebra.TensorProduct.rightAlgebra

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

/-- Helper for Lemma 10.47.3: over an algebraically closed base, the relative separable closure in
any field extension is trivial. -/
private theorem separableClosure_eq_bot_of_isAlgClosed
    {L K : Type u} [Field L] [Field K] [Algebra L K] [IsAlgClosed L] :
    separableClosure L K = ⊥ := by
  -- Proof comment: an algebraically closed field is separably closed, so a separable algebraic
  -- intermediate field over it must collapse to the base field.
  letI : IsSepClosed L := inferInstance
  exact IntermediateField.eq_bot_of_isSepClosed_of_isSeparable (separableClosure L K)

/-- Helper for Lemma 10.47.3: over an algebraically closed base field, tensoring two field
extensions still yields an irreducible prime spectrum. -/
private theorem irreducibleSpace_primeSpectrum_ringTensor_field_of_algClosed
    {L K F : Type u} [Field L] [IsAlgClosed L] [Field K] [Field F]
    [Algebra L K] [Algebra L F] :
    IrreducibleSpace (PrimeSpectrum (K ⊗[L] F)) := by
  -- Route correction: isolate the remaining source-faithful blocker at the field level, so the
  -- algebra theorem below can close by the open-map fiber criterion without redoing tensor descent.
  sorry

/-- Helper for Lemma 10.47.3: over an algebraically closed base field, tensoring an algebra with
an arbitrary field extension preserves irreducibility of prime spectra. -/
private theorem irreducibleSpace_primeSpectrum_tensorProduct_of_algClosed_base
    {L A F : Type u} [Field L] [IsAlgClosed L] [CommRing A] [Algebra L A] [Field F] [Algebra L F]
    (hA : IrreducibleSpace (PrimeSpectrum A)) :
    IrreducibleSpace (PrimeSpectrum (A ⊗[L] F)) := by
  -- Route correction: this is the remaining source-faithful substitute for the blocked import of
  -- Lemma `10.47.2`; the main theorem now reduces `4 → 1` to this single algebraically-closed-base
  -- tensor statement.
  have hFiber :
      ∀ p : PrimeSpectrum A,
        IrreducibleSpace (PrimeSpectrum (p.asIdeal.Fiber (A ⊗[L] F))) := by
    intro p
    let e :
        p.asIdeal.Fiber (A ⊗[L] F) ≃ₐ[p.asIdeal.ResidueField]
          p.asIdeal.ResidueField ⊗[L] F :=
      Algebra.TensorProduct.cancelBaseChange L A p.asIdeal.ResidueField p.asIdeal.ResidueField F
    -- Proof comment: cancel the base change through the residue field so that each fiber becomes
    -- the field tensor product handled by the dedicated field-level theorem.
    exact (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).irreducibleSpace_iff.2 <|
      irreducibleSpace_primeSpectrum_ringTensor_field_of_algClosed
        (L := L) (K := p.asIdeal.ResidueField) (F := F)
  have hdense :
      Dense { p : PrimeSpectrum A |
        IrreducibleSpace (PrimeSpectrum (p.asIdeal.Fiber (A ⊗[L] F))) } := by
    have hall :
        { p : PrimeSpectrum A |
            IrreducibleSpace (PrimeSpectrum (p.asIdeal.Fiber (A ⊗[L] F))) } = Set.univ := by
      ext p
      simp [hFiber p]
    rw [hall]
    simpa using (dense_univ : Dense (Set.univ : Set (PrimeSpectrum A)))
  -- Proof comment: the tensor-product projection is open over a field, and every residue-field
  -- fiber is irreducible by the field-level step above, so Lemma `10.47.1` applies directly.
  exact irreducibleSpace_primeSpectrum_of_isOpenMap_of_dense_irreducible_fibers
    (R := A) (S := A ⊗[L] F) hA
    (PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field : IsOpenMap
      (PrimeSpectrum.comap (algebraMap A (A ⊗[L] F))))
    hdense

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
      -- Proof comment: this is the single remaining missing input from the algebraically closed
      -- base-change step.
      exact irreducibleSpace_primeSpectrum_tensorProduct_of_algClosed_base
        (L := AlgebraicClosure k) (A := R ⊗[k] AlgebraicClosure k) (F := F) h4
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
