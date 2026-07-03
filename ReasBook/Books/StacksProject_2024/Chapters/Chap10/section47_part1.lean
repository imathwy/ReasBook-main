import Mathlib
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Spectrum.Prime.Chevalley

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_47_1 (from Chap10) -/
universe u v

open PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling for the affine irreducibility criterion:
* primary domain: irreducibility of prime spectra under an open spectral map, with fibers described
  by fiber rings `κ(p) ⊗[R] S`;
* sampled owner declarations:
  `IsOpenMap.irreducibleSpace_of_dense_irreducible_fiber`,
  `PrimeSpectrum.preimageHomeomorphFiber`,
  `PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation`.

Layer triage:
* `source-facing`: the affine-spectrum form of the Stacks irreducibility criterion;
* `core/canonical`: the topological owner theorem
  `IsOpenMap.irreducibleSpace_of_dense_irreducible_fiber`;
* `bridge/view`: `PrimeSpectrum.preimageHomeomorphFiber`, identifying the set-theoretic fiber of
  `PrimeSpectrum.comap (algebraMap R S)` over `p` with `PrimeSpectrum (p.asIdeal.Fiber S)`.

Primitive data is the open-map hypothesis on `Spec S → Spec R` together with dense irreducibility
of the fiber spectra `Spec(κ(p) ⊗[R] S)`. The irreducibility of `Spec S` is derived API obtained
by transporting the fiber condition across the canonical homeomorphism and applying the owner
theorem.
-/

-- Auxiliary generalization: this is the affine-spectrum specialization of
-- `IsOpenMap.irreducibleSpace_of_dense_irreducible_fiber`. For each
-- `p : PrimeSpectrum R`, identify the set-theoretic fiber of `PrimeSpectrum.comap (algebraMap R S)`
-- over `p` with `PrimeSpectrum (p.asIdeal.Fiber S)` via `PrimeSpectrum.preimageHomeomorphFiber`.
theorem irreducibleSpace_primeSpectrum_of_isOpenMap_of_dense_irreducible_fibers
    (hR : IrreducibleSpace (PrimeSpectrum R))
    (hopen : IsOpenMap (comap (algebraMap R S)))
    (hdense : Dense { p : PrimeSpectrum R | IrreducibleSpace (PrimeSpectrum (p.asIdeal.Fiber S)) }) :
    IrreducibleSpace (PrimeSpectrum S) := by
  refine IsOpenMap.irreducibleSpace_of_dense_irreducible_fiber hopen hR ?_
  refine hdense.mono fun p hp ↦ ?_
  simpa [isIrreducible_iff_irreducibleSpace] using
    (preimageHomeomorphFiber R S p).irreducibleSpace_iff.mpr hp

-- Proof sketch: flat algebras satisfy going down, so
-- `PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation` applies; then use the
-- open-map generalization above.
/-- Lemma 10.47.1: if `Spec R` is irreducible, `R → S` is flat and of finite presentation, and
the fiber spectra `Spec(κ(p) ⊗[R] S)` are irreducible for a dense set of primes `p` of `R`, then
`Spec S` is irreducible. -/
theorem irreducibleSpace_primeSpectrum_of_flat_finitePresentation_of_dense_irreducible_fibers
    (hR : IrreducibleSpace (PrimeSpectrum R))
    [Module.Flat R S] [Algebra.FinitePresentation R S]
    (hdense : Dense { p : PrimeSpectrum R | IrreducibleSpace (PrimeSpectrum (p.asIdeal.Fiber S)) }) :
    IrreducibleSpace (PrimeSpectrum S) := by
  exact irreducibleSpace_primeSpectrum_of_isOpenMap_of_dense_irreducible_fibers
    hR isOpenMap_comap_of_hasGoingDown_of_finitePresentation hdense

end

/-! ### Lemma_10_47_2 (from Chap10) -/
open AlgebraicGeometry CommRingCat
open scoped TensorProduct

universe u

section

variable {k R S : Type u}
variable [Field k] [IsSepClosed k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

private theorem irreducibleSpace_primeSpectrum_of_existsUnique_minimalPrime
    (h : ∃! p : Ideal R, p ∈ minimalPrimes R) :
    IrreducibleSpace (PrimeSpectrum R) := by
  rcases h with ⟨p, hp, hp_unique⟩
  have hminimal : minimalPrimes R = {p} := by
    ext q
    constructor
    · intro hq
      simpa using hp_unique q hq
    · rintro rfl
      exact hp
  have hsInf : sInf (minimalPrimes R) = nilradical R := by
    rw [minimalPrimes, nilradical]
    exact Ideal.sInf_minimalPrimes
  have hnil : nilradical R = p := by
    rw [← hsInf, hminimal]
    simp
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
  simpa [hnil] using Ideal.minimalPrimes_isPrime hp

private theorem existsUnique_minimalPrime_of_irreducibleSpace_primeSpectrum
    (h : IrreducibleSpace (PrimeSpectrum R)) :
    ∃! p : Ideal R, p ∈ minimalPrimes R := by
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at h
  letI : (nilradical R).IsPrime := h
  have hminimal : minimalPrimes R = {nilradical R} := by
    simpa [minimalPrimes, nilradical] using
      (show (nilradical R).minimalPrimes = {nilradical R} from
        Ideal.minimalPrimes_eq_subsingleton_self)
  refine ⟨nilradical R, ?_, ?_⟩
  · rw [hminimal]
    simp
  · intro q hq
    rw [hminimal] at hq
    simpa using hq

-- Proof sketch: over a separably closed field, Lemma `10.47.5` identifies irreducibility of
-- `Spec S` with geometric irreducibility over `k`. Lemma `10.47.7` then upgrades geometric
-- irreducibility of `S` to geometric irreducibility of the tensor-product projection
-- `Spec (R ⊗[k] S) ⟶ Spec R`. Since this projection is open over a field, the owner theorem
-- `GeometricallyIrreducible.irreducibleSpace` yields irreducibility of `Spec (R ⊗[k] S)` from
-- irreducibility of `Spec R`.
/-- Canonical prime-spectrum form of Lemma 10.47.2: over a separably closed field, the tensor
product of two `k`-algebras with irreducible prime spectrum again has irreducible prime spectrum. -/
theorem irreducibleSpace_primeSpectrum_tensorProduct
    (hR : IrreducibleSpace (PrimeSpectrum R))
    (hS : IrreducibleSpace (PrimeSpectrum S)) :
    IrreducibleSpace (PrimeSpectrum (R ⊗[k] S)) := by
  let f : Spec (of (R ⊗[k] S)) ⟶ Spec (of R) :=
    Spec.map (ofHom (algebraMap R (R ⊗[k] S)))
  letI : GeometricallyIrreducible (Spec.map (ofHom (algebraMap k S))) :=
    (Lemma_10_47_5).2 <| by
      simpa using hS
  letI : GeometricallyIrreducible f := by
    simpa [f] using
      (inferInstance :
        GeometricallyIrreducible (Spec.map (ofHom (algebraMap R (R ⊗[k] S)))))
  letI : IrreducibleSpace (Spec (of R)) := by
    simpa using hR
  simpa using
    (GeometricallyIrreducible.irreducibleSpace f
      (by
        simpa using
          (PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field :
            IsOpenMap (PrimeSpectrum.comap (algebraMap R (R ⊗[k] S))))))

/-- Lemma 10.47.2 (Tag 00I7): if `k` is separably closed and the `k`-algebras `R` and `S` each
have a unique minimal prime ideal, then `R ⊗[k] S` also has a unique minimal prime ideal. This is
the textbook formulation of `irreducibleSpace_primeSpectrum_tensorProduct`. -/
@[stacks 00I7]
theorem existsUnique_minimalPrime_tensorProduct
    (hR : ∃! p : Ideal R, p ∈ minimalPrimes R)
    (hS : ∃! p : Ideal S, p ∈ minimalPrimes S) :
    ∃! p : Ideal (R ⊗[k] S), p ∈ minimalPrimes (R ⊗[k] S) := by
  exact existsUnique_minimalPrime_of_irreducibleSpace_primeSpectrum <|
    irreducibleSpace_primeSpectrum_tensorProduct
      (irreducibleSpace_primeSpectrum_of_existsUnique_minimalPrime hR)
      (irreducibleSpace_primeSpectrum_of_existsUnique_minimalPrime hS)

end

/-! ### Lemma_10_47_3 (from Chap10) -/
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

/-! ### Definition_10_47_4 (from Chap10) -/
open AlgebraicGeometry CommRingCat
open scoped TensorProduct

universe u

section

variable {k S : Type u} [Field k] [CommRing S] [Algebra k S]

/- Definition 10.47.4: the canonical scheme-theoretic notion of a geometrically irreducible
`k`-algebra `S` is
`AlgebraicGeometry.GeometricallyIrreducible (Spec.map (ofHom (algebraMap k S)))`.
-/
#check GeometricallyIrreducible (Spec.map (ofHom (algebraMap k S)))

/-- Prime-spectrum form of the affine base-change criterion for Definition 10.47.4. -/
theorem geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_baseChange :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k S))) ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        IrreducibleSpace (PrimeSpectrum (S ⊗[k] K)) := by
  rw [geometricallyIrreducible_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  constructor
  · intro h K _ _
    let e := Scheme.homeoOfIso (pullbackSpecIso k S K).symm
    simpa using e.irreducibleSpace_iff.mpr (h K)
  · intro h K _ _
    let e := Scheme.homeoOfIso (pullbackSpecIso k S K).symm
    simpa using e.irreducibleSpace_iff.mp (h K)

/-- A field is geometrically irreducible over itself. -/
instance : GeometricallyIrreducible (Spec.map (ofHom (algebraMap k k))) := by
  rw [geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_baseChange]
  intro K _ _
  let e : k ⊗[k] K ≃ₐ[k] K := Algebra.TensorProduct.lid k K
  letI : IsDomain (k ⊗[k] K) := MulEquiv.isDomain _ e.toMulEquiv
  infer_instance

end

/-! ### Lemma_10_47_5 (from Chap10) -/
universe u

open scoped TensorProduct
open AlgebraicGeometry CommRingCat

section

variable {k R : Type u} [Field k] [IsSepClosed k] [CommRing R] [Algebra k R]

/-- Lemma 10.47.5 (Tag 037M): over a separably closed field `k`, a `k`-algebra `R` is
geometrically irreducible over `k` if and only if `Spec R` is irreducible. -/
@[stacks 037M]
theorem Lemma_10_47_5
    :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))) ↔
      IrreducibleSpace (Spec (of R)) := by
  constructor
  · intro h
    letI : GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))) := h
    simpa using
      (GeometricallyIrreducible.irreducibleSpace_of_subsingleton
        (Spec.map (ofHom (algebraMap k R))))
  · intro h
    let eK : SeparableClosure k ≃ₐ[k] k := IsSepClosure.equiv k (SeparableClosure k) k
    let e : R ⊗[k] SeparableClosure k ≃ₐ[R] R :=
      (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) eK).trans
        (Algebra.TensorProduct.rid k R R)
    exact geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_separableClosure.2 <|
      (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).irreducibleSpace_iff.2 <| by
        simpa using h

end

/-! ### Lemma_10_47_6 (from Chap10) -/
open CategoryTheory Limits
open scoped TensorProduct
open Algebra.TensorProduct
open AlgebraicGeometry CommRingCat

universe u

namespace Algebra

-- Local shorthand for the canonical geometric-irreducibility owner property from
-- `Definition_10_47_4`.
local notation "GeomIrreducibleOver[" k "] " R =>
  GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R)))

section

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

/-- Helper for Lemma 10.47.6: an irreducible prime spectrum is automatically nonempty, hence the
underlying ring is nontrivial. -/
private theorem nontrivial_of_irreducible_primeSpectrum {R : Type u} [CommRing R]
    (hR : IrreducibleSpace (PrimeSpectrum R)) : Nontrivial R := by
  -- An irreducible space is nonempty, and `Spec R` is nonempty exactly when `R` is nontrivial.
  letI : IrreducibleSpace (PrimeSpectrum R) := hR
  exact PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance

/-- Helper for Lemma 10.47.6: irreducibility of prime spectra descends along injective ring maps. -/
private theorem irreducibleSpace_primeSpectrum_of_injective {R S : Type u} [CommRing R]
    [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    IrreducibleSpace (PrimeSpectrum S) → IrreducibleSpace (PrimeSpectrum R) := by
  intro hS
  -- Compare the nilradicals via injectivity, then pull primeness back along `f`.
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at hS ⊢
  letI : (nilradical S).IsPrime := hS
  have hcomap : Ideal.comap f (nilradical S) = nilradical R := by
    ext x
    simp [Ideal.mem_comap, mem_nilradical, IsNilpotent.map_iff hf]
  simpa [hcomap] using Ideal.comap_isPrime f (nilradical S)

/-- Helper for Lemma 10.47.6: a witness that the nilradical of a ring fails to be prime. -/
private structure NonprimeNilradicalWitness (R : Type u) [CommRing R] where
  left : R
  right : R
  mul_isNilpotent : IsNilpotent (left * right)
  left_not_isNilpotent : ¬ IsNilpotent left
  right_not_isNilpotent : ¬ IsNilpotent right

/-- Helper for Lemma 10.47.6: such a witness forces the prime spectrum to be non-irreducible. -/
private theorem not_irreducibleSpace_primeSpectrum_of_nonprime_nilradical_witness
    {R : Type u} [CommRing R] :
    Nonempty (NonprimeNilradicalWitness R) → ¬ IrreducibleSpace (PrimeSpectrum R) := by
  intro h hR
  obtain ⟨w⟩ := h
  -- Primeness of the nilradical would force one of the two factors to be nilpotent.
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at hR
  have hmul : w.left * w.right ∈ nilradical R := by
    exact mem_nilradical.mpr w.mul_isNilpotent
  rcases hR.mem_or_mem hmul with hleft | hright
  · exact w.left_not_isNilpotent (mem_nilradical.mp hleft)
  · exact w.right_not_isNilpotent (mem_nilradical.mp hright)

/-- Helper for Lemma 10.47.6: in a nontrivial ring, failure of irreducibility of `Spec R`
produces a concrete witness that the nilradical is not prime. -/
private theorem exists_nonprime_nilradical_witness_of_not_irreducibleSpace_primeSpectrum
    {R : Type u} [CommRing R] [Nontrivial R] :
    ¬ IrreducibleSpace (PrimeSpectrum R) → Nonempty (NonprimeNilradicalWitness R) := by
  intro hR
  -- Rewrite non-irreducibility into non-primeness of the nilradical.
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at hR
  have htop : (nilradical R) ≠ ⊤ := by
    intro htop
    have hnil : IsNilpotent (1 : R) := by
      apply mem_nilradical.mp
      simpa [htop] using (show (1 : R) ∈ (⊤ : Ideal R) from Ideal.mem_top)
    obtain ⟨n, hn⟩ := hnil
    exact (show (1 : R) ≠ 0 from one_ne_zero) (by simpa using hn)
  obtain ⟨x, hx, y, hy, hxy⟩ := (Ideal.not_isPrime_iff.mp hR).resolve_left htop
  -- The failed primeness statement is exactly the desired witness.
  exact ⟨{
    left := x
    right := y
    mul_isNilpotent := mem_nilradical.mp hxy
    left_not_isNilpotent := by simpa [mem_nilradical] using hx
    right_not_isNilpotent := by simpa [mem_nilradical] using hy
  }⟩

/-- Helper for Lemma 10.47.6: a nonprime-nilradical witness in a tensor product already appears
in a finitely generated tensor stage on both sides. -/
private theorem exists_fg_subalgebras_tensorProduct_has_nonprime_nilradical_witness
    {K : Type u} [Field K] [Algebra k K]
    (h : Nonempty (NonprimeNilradicalWitness (A ⊗[k] K))) :
    ∃ T : @FGSubalgebraPair k A K _ _ _ _ _,
      Nonempty (NonprimeNilradicalWitness (T.left ⊗[k] T.right)) := by
  obtain ⟨w⟩ := h
  -- Descend the two witness elements to one common finitely generated tensor stage.
  obtain ⟨T, x', y', hx_map, hy_map⟩ :=
    exists_fg_subalgebras_tensorProduct_lift_pair (k := k) (R := A) (S := K) w.left w.right
  have h_inj := tensorProduct_map_injective_of_fgSubalgebraPair (k := k) (R := A) (S := K) T
  have hmul_nilpotent : IsNilpotent (x' * y') := by
    rw [← IsNilpotent.map_iff h_inj]
    simpa [map_mul, hx_map, hy_map] using w.mul_isNilpotent
  have hx_not_nilpotent : ¬ IsNilpotent x' := by
    intro hx_nilpotent
    apply w.left_not_isNilpotent
    simpa [hx_map] using hx_nilpotent.map (Algebra.TensorProduct.map T.left.val T.right.val)
  have hy_not_nilpotent : ¬ IsNilpotent y' := by
    intro hy_nilpotent
    apply w.right_not_isNilpotent
    simpa [hy_map] using hy_nilpotent.map (Algebra.TensorProduct.map T.left.val T.right.val)
  refine ⟨T, ?_⟩
  -- The descended elements give the same obstruction at the finite stage.
  exact ⟨{
    left := x'
    right := y'
    mul_isNilpotent := hmul_nilpotent
    left_not_isNilpotent := hx_not_nilpotent
    right_not_isNilpotent := hy_not_nilpotent
  }⟩

-- Proof sketch: after any field extension of `k`, tensoring with that field preserves injectivity
-- of `f`; irreducibility then descends along the induced map on prime spectra.
private theorem geometricallyIrreducible_of_injective {B : Type u} [CommRing B] [Algebra k B]
    (f : B →ₐ[k] A) (hf : Function.Injective f) :
    (GeomIrreducibleOver[k] A) → GeomIrreducibleOver[k] B := by
  intro hA
  rw [geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_baseChange] at hA ⊢
  intro K _ _
  let g : B ⊗[k] K →ₐ[k] A ⊗[k] K :=
    Algebra.TensorProduct.map f (AlgHom.id k K)
  have hg : Function.Injective g := by
    -- Tensoring with a field preserves injectivity of the algebra map.
    simpa [g] using TensorProduct.map_injective_of_flat_flat
      f.toLinearMap (AlgHom.id k K).toLinearMap hf (AlgHom.id k K).injective
  -- Apply the ring-level irreducibility descent after base change.
  exact irreducibleSpace_primeSpectrum_of_injective g.toRingHom hg (hA K)

/-- Lemma 10.47.6 (1): every `k`-subalgebra of a geometrically irreducible `k`-algebra is
geometrically irreducible over `k`. -/
theorem geometricallyIrreducible_subalgebra (S : Subalgebra k A) :
    (GeomIrreducibleOver[k] A) → GeomIrreducibleOver[k] S :=
  geometricallyIrreducible_of_injective S.val Subtype.val_injective

instance (S : Subalgebra k A) [GeomIrreducibleOver[k] A] : GeomIrreducibleOver[k] S :=
  geometricallyIrreducible_subalgebra S inferInstance

/-- Lemma 10.47.6 (2): if every finitely generated `k`-subalgebra of `A` is geometrically
irreducible over `k`, then `A` is geometrically irreducible over `k`. -/
-- Proof sketch: every field-valued base change of `A` is the directed union of the corresponding
-- base changes of its finitely generated `k`-subalgebras, so irreducibility is detected on those
-- finitely generated stages.
theorem geometricallyIrreducible_of_forall_fg
    (h : ∀ S : Subalgebra k A, S.FG → GeomIrreducibleOver[k] S) :
    GeomIrreducibleOver[k] A := by
  rw [geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_baseChange]
  intro K _ _
  by_contra hK
  have hbot :
      GeomIrreducibleOver[k] (⊥ : Subalgebra k A) :=
    h ⊥ Subalgebra.fg_bot
  rw [geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_baseChange] at hbot
  have hbotk : IrreducibleSpace (PrimeSpectrum ((⊥ : Subalgebra k A) ⊗[k] k)) := hbot k
  letI : Nontrivial ((⊥ : Subalgebra k A) ⊗[k] k) :=
    nontrivial_of_irreducible_primeSpectrum hbotk
  let ebot : ((⊥ : Subalgebra k A) ⊗[k] k) ≃ (⊥ : Subalgebra k A) :=
    (Algebra.TensorProduct.rid k (⊥ : Subalgebra k A) (⊥ : Subalgebra k A)).toEquiv
  letI : Nontrivial (⊥ : Subalgebra k A) := ebot.injective.nontrivial
  have hbot_inj : Function.Injective ((⊥ : Subalgebra k A).val) := Subtype.val_injective
  letI : Nontrivial A := hbot_inj.nontrivial
  letI : Nontrivial (A ⊗[k] K) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left
      (R := k) (A := A) (B := K) (algebraMap k K).injective
  have hwitness : Nonempty (NonprimeNilradicalWitness (A ⊗[k] K)) :=
    exists_nonprime_nilradical_witness_of_not_irreducibleSpace_primeSpectrum hK
  obtain ⟨T, ⟨w⟩⟩ :=
    exists_fg_subalgebras_tensorProduct_has_nonprime_nilradical_witness
      (k := k) (A := A) (K := K) hwitness
  let j : T.right →ₐ[k] K := T.right.val
  let g : T.left ⊗[k] T.right →ₐ[k] T.left ⊗[k] K :=
    Algebra.TensorProduct.map (AlgHom.id k T.left) j
  have hg : Function.Injective g := by
    -- Tensoring with the ambient field preserves injectivity of the right-hand inclusion.
    simpa [g, j] using TensorProduct.map_injective_of_flat_flat
      (AlgHom.id k T.left).toLinearMap j.toLinearMap
      Function.injective_id Subtype.val_injective
  have hTK : IrreducibleSpace (PrimeSpectrum (T.left ⊗[k] K)) := by
    -- The finitely generated left stage is geometrically irreducible by hypothesis.
    have hT : GeomIrreducibleOver[k] T.left := h T.left T.left_fg
    rw [geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_baseChange] at hT
    exact hT K
  have hsmall : IrreducibleSpace (PrimeSpectrum (T.left ⊗[k] T.right)) :=
    irreducibleSpace_primeSpectrum_of_injective g.toRingHom hg hTK
  -- The finite-stage witness contradicts irreducibility of that finite tensor product.
  exact
    (not_irreducibleSpace_primeSpectrum_of_nonprime_nilradical_witness
      (R := T.left ⊗[k] T.right) ⟨w⟩) hsmall

end

section

variable {k I : Type u} [Field k] [Preorder I] [IsDirectedOrder I]

omit [IsDirectedOrder I] in
/-- Helper for Lemma 10.47.6: any finitely generated subalgebra of a filtered colimit of
`k`-algebras factors injectively through one stage. -/
private theorem exists_injective_stage_of_fg_subalgebra_colimit
    (F : I ⥤ CommAlgCat.{u} k) [Nonempty I] [IsFiltered I]
    (T : Subalgebra k (colimit F : CommAlgCat.{u} k)) (hT : T.FG) :
    ∃ (i : I) (φ : T →ₐ[k] F.obj i), Function.Injective φ := by
  let E := commAlgCatEquivUnder (CommRingCat.of k)
  let G : I ⥤ Under (CommRingCat.of k) := F ⋙ E.functor
  let c : Cocone G := E.functor.mapCocone (colimit.cocone F)
  have hc : IsColimit c := isColimitOfPreserves E.functor (colimit.isColimit F)
  have hfp : (algebraMap k T).FinitePresentation := by
    -- A finitely generated algebra over a field is finitely presented.
    simpa [RingHom.finitePresentation_algebraMap] using
      (Algebra.FinitePresentation.of_finiteType).mp ((Subalgebra.fg_iff_finiteType T).mp hT)
  let g : CommRingCat.mkUnder (CommRingCat.of k) T ⟶ c.pt := T.val.toUnder
  letI : IsFinitelyPresentable.{u} (CommRingCat.mkUnder (CommRingCat.of k) T) :=
    CommRingCat.isFinitelyPresentable_under
      (R := CommRingCat.of k) (S := CommRingCat.mkUnder (CommRingCat.of k) T) hfp
  obtain ⟨i, g', hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit
    (X := CommRingCat.mkUnder (CommRingCat.of k) T) hc g
  let g'' :
      CommRingCat.mkUnder (CommRingCat.of k) T ⟶
        CommRingCat.mkUnder (CommRingCat.of k) (F.obj i) := by
    simpa [G, E] using g'
  let ιi : CommRingCat.mkUnder (CommRingCat.of k) (F.obj i) ⟶ c.pt := by
    simpa [G, E] using c.ι.app i
  have hg' : g = g'' ≫ ιi := by
    dsimp [g'', ιi]
    simpa [g, G, E] using hg.symm
  let φ : T →ₐ[k] F.obj i :=
    { __ := g''.right.hom
      commutes' := by
        intro x
        have hw := CommRingCat.hom_ext_iff.mp (Under.w g'')
        change ((CommRingCat.Hom.hom g''.right).comp (algebraMap k T)) x =
          (algebraMap k (F.obj i)) x
        simpa [CommRingCat.mkUnder_hom, CommRingCat.hom_comp] using DFunLike.congr_fun hw x }
  have hfac (x : T) : ιi.right (φ x) = T.val x := by
    -- The stage map factors the subalgebra inclusion into the colimit.
    have hw := CommRingCat.hom_ext_iff.mp (congrArg (fun f ↦ f.right) hg')
    simpa [g, φ, CommRingCat.hom_comp] using (DFunLike.congr_fun hw x).symm
  have hφ : Function.Injective φ := by
    intro x y hxy
    exact Subtype.ext <| by
      change T.val x = T.val y
      rw [← hfac x, ← hfac y, hxy]
  exact ⟨i, φ, hφ⟩

/-- Lemma 10.47.6 (3): a directed colimit of geometrically irreducible `k`-algebras is
geometrically irreducible over `k`. -/
-- Proof sketch: if the index type is empty, the colimit in `CommAlgCat k` is the initial
-- `k`-algebra `k`, which is geometrically irreducible by `Definition_10_47_4`. Otherwise every
-- finitely generated `k`-subalgebra of the colimit is generated by finitely many elements coming
-- from stages of the directed system; directedness moves those generators to a common stage, and
-- part `(2)` finishes.
theorem geometricallyIrreducible_colimit_of_directedSystem
    (F : I ⥤ CommAlgCat.{u} k)
    (hF : ∀ i, GeomIrreducibleOver[k] (F.obj i)) :
    GeomIrreducibleOver[k] (colimit F : CommAlgCat.{u} k) :=
  by
    by_cases hI : Nonempty I
    · letI : Nonempty I := hI
      letI : IsFiltered I := inferInstance
      -- Reduce the colimit statement to finitely generated subalgebras of the colimit.
      apply geometricallyIrreducible_of_forall_fg
      intro T hT
      obtain ⟨i, φ, hφ⟩ :=
        exists_injective_stage_of_fg_subalgebra_colimit (F := F) T hT
      -- Part `(1)` descends geometric irreducibility from that stage to the chosen subalgebra.
      exact geometricallyIrreducible_of_injective φ hφ (hF i)
    · letI : IsEmpty I := not_nonempty_iff.mp hI
      have hcolim : IsInitial (colimit F : CommAlgCat.{u} k) :=
        (isColimitEquivIsInitialOfIsEmpty (CommAlgCat.{u} k) (colimit.cocone F))
          (colimit.isColimit F)
      have hself : IsInitial (CommAlgCat.of k k) := CommAlgCat.isInitialSelf
      let e : (colimit F : CommAlgCat.{u} k) ≅ CommAlgCat.of k k :=
        hcolim.coconePointUniqueUpToIso hself
      let e' : (colimit F : CommAlgCat.{u} k) ≃ₐ[k] CommAlgCat.of k k :=
        CommAlgCat.algEquivOfIso e
      have hk : GeomIrreducibleOver[k] (CommAlgCat.of k k) := inferInstance
      -- The empty filtered colimit is just `k`, and geometric irreducibility descends across the
      -- resulting algebra equivalence.
      exact geometricallyIrreducible_of_injective e'.toAlgHom e'.injective hk

end

end Algebra

/-! ### Lemma_10_47_7 (from Chap10) -/
open AlgebraicGeometry CommRingCat CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

section

variable {k R S : Type u}
variable [Field k] [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]
variable [GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k S)))]

instance : GeometricallyIrreducible (Spec.map (ofHom (algebraMap R (R ⊗[k] S)))) := by
  let e := pullbackSpecIso k R S
  letI : GeometricallyIrreducible (e.inv ≫ pullback.fst _ _) := by
    infer_instance
  simpa [e, pullbackSpecIso_inv_fst'] using
    (inferInstance : GeometricallyIrreducible (e.inv ≫ pullback.fst _ _))

/- Lemma 10.47.7: if `k` is a field, `S` is geometrically irreducible over `k`, and `R` is any
`k`-algebra, then the canonical map `Spec(R ⊗[k] S) → Spec(R)` induces a bijection on irreducible
components.

The owner abstraction is `Scheme.Hom.irreducibleComponentsEquiv`, applied to the tensor-product
projection together with the owner-side base-change instance for
`GeometricallyIrreducible` and the prime-spectrum openness theorem
`PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field`.
-/
#check
  (Spec.map (ofHom (algebraMap R (R ⊗[k] S)))).irreducibleComponentsEquiv
    (by
      simpa using
        (PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field :
          IsOpenMap (PrimeSpectrum.comap (algebraMap R (R ⊗[k] S)))))

end

/-! ### Lemma_10_47_8 (from Chap10) -/
open scoped TensorProduct
open Algebra.TensorProduct
open AlgebraicGeometry CommRingCat
open Polynomial

namespace Algebra

universe u

section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Helper for Lemma 10.47.8: every coefficient of a monic divisor of the mapped minimal
polynomial is already in the base field because it is algebraic over `k`. -/
private theorem coeff_mem_bot_of_monic_dvd_mapped_minpoly
    {L : Type u} [Field L] [Algebra k L] (pb : PowerBasis k L)
    (hclosed : algebraicClosure k K = ⊥) {q : Polynomial K} (hq_monic : q.Monic)
    (hq_dvd : q ∣ (minpoly k pb.gen).map (algebraMap k K)) :
    ∀ i : ℕ, q.coeff i ∈ (⊥ : IntermediateField k K) := by
  intro i
  -- Proof comment: divisors of a monic polynomial with coefficients in `k` have integral
  -- coefficients, hence algebraic coefficients; `hclosed` then collapses them to `k`.
  have hcoeff_integral : IsIntegral k (q.coeff i) := by
    simpa using
      Polynomial.isIntegral_coeff_of_dvd
        (minpoly k pb.gen) q (minpoly.monic pb.isIntegral_gen) hq_monic hq_dvd i
  have hcoeff_mem : q.coeff i ∈ algebraicClosure k K := by
    exact mem_algebraicClosure_iff'.mpr hcoeff_integral
  simpa [hclosed] using hcoeff_mem

/-- Helper for Lemma 10.47.8: the minimal polynomial of a primitive element stays irreducible
after base change from `k` to `K` when `k` is algebraically closed in `K`. -/
private theorem mapped_minpoly_irreducible_of_algebraicClosure_eq_bot
    {L : Type u} [Field L] [Algebra k L] (pb : PowerBasis k L)
    (hclosed : algebraicClosure k K = ⊥) :
    Irreducible ((minpoly k pb.gen).map (algebraMap k K)) := by
  let pK : Polynomial K := (minpoly k pb.gen).map (algebraMap k K)
  have hpK_monic : pK.Monic := by
    exact (minpoly.monic pb.isIntegral_gen).map (algebraMap k K)
  refine (hpK_monic.irreducible_iff_natDegree).2 ?_
  refine ⟨?_, ?_⟩
  · -- Proof comment: mapping the nonconstant minimal polynomial keeps positive degree.
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
        coeff_mem_bot_of_monic_dvd_mapped_minpoly
          (k := k) (K := K) pb hclosed hq_monic hq_dvd i
    have hr_lifts : r ∈ Polynomial.lifts (algebraMap k K) := by
      refine r.lifts_iff_coeff_lifts.mpr ?_
      intro i
      simpa [Algebra.mem_bot, Set.mem_range] using
        coeff_mem_bot_of_monic_dvd_mapped_minpoly
          (k := k) (K := K) pb hclosed hr_monic hr_dvd i
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

/-- Helper for Lemma 10.47.8: a finite separable base change tensor product is generated over `K`
by `1 ⊗ pb.gen`. -/
private theorem tensorProduct_gen_adjoin_eq_top_of_powerBasis
    {L : Type u} [Field L] [Algebra k L] (pb : PowerBasis k L) :
    Algebra.adjoin K ({((1 : K) ⊗ₜ[k] pb.gen)} : Set (K ⊗[k] L)) = ⊤ := by
  -- Proof comment: transport the primitive-element generator across the standard tensor-product
  -- adjoin lemma.
  simpa [Set.image_singleton] using
    (Algebra.TensorProduct.adjoin_one_tmul_image_eq_top
      (R := k) (A := K) ({pb.gen} : Set L) pb.adjoin_gen_eq_top)

/-- Helper for Lemma 10.47.8: after finite separable base change, the tensor product with `K`
is a domain. -/
private theorem isDomain_tensorProduct_finiteSeparable_of_algebraicClosure_eq_bot
    {L : Type u} [Field L] [Algebra k L] [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (hclosed : algebraicClosure k K = ⊥) :
    IsDomain (K ⊗[k] L) := by
  let pb : PowerBasis k L := Field.powerBasisOfFiniteOfSeparable k L
  let x : K ⊗[k] L := (1 : K) ⊗ₜ[k] pb.gen
  have hpK_irreducible :
      Irreducible ((minpoly k pb.gen).map (algebraMap k K)) :=
    mapped_minpoly_irreducible_of_algebraicClosure_eq_bot (k := k) (K := K) pb hclosed
  have hpK_monic : ((minpoly k pb.gen).map (algebraMap k K)).Monic := by
    exact (minpoly.monic pb.isIntegral_gen).map (algebraMap k K)
  have hx_aeval : Polynomial.aeval x ((minpoly k pb.gen).map (algebraMap k K)) = 0 := by
    -- Proof comment: `x = 1 ⊗ pb.gen` is exactly the image of `pb.gen` under
    -- `TensorProduct.includeRight`, so the mapped minimal polynomial vanishes at `x`.
    rw [Polynomial.aeval_map_algebraMap (R := k) (A := K) (x := x) (p := minpoly k pb.gen)]
    change Polynomial.aeval
        ((Algebra.TensorProduct.includeRight (R := k) (A := K) (B := L)) pb.gen)
        (minpoly k pb.gen) = 0
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hx_integral : IsIntegral K x := by
    -- Proof comment: the mapped minimal polynomial is monic and annihilates `x`.
    exact ⟨_, hpK_monic, hx_aeval⟩
  have hminpoly :
      minpoly K x = (minpoly k pb.gen).map (algebraMap k K) := by
    -- Proof comment: identify the `K`-minimal polynomial of the tensor generator by the usual
    -- `irreducible + monic + root` characterization.
    exact (minpoly.eq_of_irreducible_of_monic hpK_irreducible hx_aeval hpK_monic).symm
  have hAdjoinRootDomain : IsDomain (AdjoinRoot (minpoly K x)) := by
    -- Proof comment: the minimal polynomial is prime because it is irreducible over a field.
    have hprime : Prime (minpoly K x) := by
      rw [hminpoly]
      exact hpK_irreducible.prime
    exact AdjoinRoot.isDomain_of_prime hprime
  have hAdjoinDomain : IsDomain (Algebra.adjoin K ({x} : Set (K ⊗[k] L))) := by
    have hToAdjoin_injective :
        Function.Injective (AdjoinRoot.Minpoly.toAdjoin (R := K) (x := x)) := by
      -- Proof comment: if a class in `AdjoinRoot` maps to zero in the adjoin algebra, represent
      -- it by a polynomial `p`; then `p(x) = 0`, so `minpoly K x ∣ p`, hence the class is zero.
      refine (injective_iff_map_eq_zero _).2 ?_
      intro y hy
      obtain ⟨p, rfl⟩ := (AdjoinRoot.mk_surjective (g := minpoly K x)) y
      rw [AdjoinRoot.Minpoly.coe_toAdjoin, AdjoinRoot.liftAlgHom_mk] at hy
      have hy' : Polynomial.aeval x p = 0 := by
        -- Proof comment: forget from the adjoin subalgebra back to the ambient tensor product.
        have hy'' :
            ((Polynomial.aeval ⟨x, self_mem_adjoin_singleton K x⟩ p :
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
    -- Proof comment: the primitive element already generates the whole tensor product.
    simpa [x] using tensorProduct_gen_adjoin_eq_top_of_powerBasis (k := k) (K := K) pb
  let eTop : Algebra.adjoin K ({x} : Set (K ⊗[k] L)) ≃ₐ[K] K ⊗[k] L :=
    (Subalgebra.equivOfEq _ _ hgen).trans Subalgebra.topEquiv
  -- Proof comment: transport the domain structure from the adjoin-root model to the full tensor
  -- product using the generator-equals-top identification.
  letI : IsDomain (Algebra.adjoin K ({x} : Set (K ⊗[k] L))) := hAdjoinDomain
  exact MulEquiv.isDomain (Algebra.adjoin K ({x} : Set (K ⊗[k] L))) eTop.toMulEquiv.symm

/-- Lemma 10.47.8: if `k` is algebraically closed in the field extension `K`, then `K` is
geometrically irreducible over `k`. -/
@[stacks 037P]
theorem isGeometricallyIrreducibleOver_of_algebraicClosure_eq_bot
    (hclosed : algebraicClosure k K = ⊥) :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k K))) := by
  rw [geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_finiteSeparable_baseChange]
  intro L _ _ _ _
  -- Proof comment: by Lemma `10.47.3` it is enough to test finite separable extensions, and the
  -- primitive-element/irreducible-polynomial argument shows each base-change tensor product is a
  -- domain.
  letI : IsDomain (K ⊗[k] L) :=
    isDomain_tensorProduct_finiteSeparable_of_algebraicClosure_eq_bot
      (k := k) (K := K) (L := L) hclosed
  infer_instance

end

end Algebra

/-! ### Lemma_10_47_9 (from Chap10) -/
open AlgebraicGeometry CommRingCat CategoryTheory

namespace Algebra

universe u

section

variable (k K S : Type u)
variable [Field k] [Field K] [CommRing S]
variable [Algebra k K] [Algebra K S] [Algebra k S] [IsScalarTower k K S]

/-- Lemma 10.47.9: if the field extension `K / k` is geometrically irreducible and the
`K`-algebra `S` is geometrically irreducible over `K`, then `S` is geometrically irreducible over
`k`. -/
-- Proof sketch: apply `AlgebraicGeometry.GeometricallyIrreducible.comp` to the structure maps
-- `Spec S ⟶ Spec K ⟶ Spec k` and identify the composite with `Spec.map (ofHom (algebraMap k S))`.
@[stacks 0G30]
theorem geometrically_irreducible_over_base_of_tower
    [GeometricallyIrreducible (Spec.map (ofHom (algebraMap k K)))]
    [GeometricallyIrreducible (Spec.map (ofHom (algebraMap K S)))] :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k S))) := by
  -- Apply geometric irreducibility along the tower `Spec S ⟶ Spec K ⟶ Spec k`.
  simpa [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsScalarTower.algebraMap_eq k K S] using
    (GeometricallyIrreducible.comp
      (Spec.map (ofHom (algebraMap K S)))
      (Spec.map (ofHom (algebraMap k K))))

end

end Algebra
