import Mathlib
import stacks_project.Chap10.Definition_10_32_1
import stacks_project.Chap10.Definition_10_166_2
import stacks_project.Chap10.Lemma_10_164_4
import stacks_project.Chap10.Lemma_10_161_13
import stacks_project.Chap10.Lemma_10_157_5
import stacks_project.Chap10.Lemma_10_46_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Algebra

universe u v w

section

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]

variable {ι : Type w}

/-- Helper for Lemma 10.166.5: a finite set of coefficients in `k` already lies in one stage of a
directed union of subfields. -/
lemma finite_subset_subfield_stage
    [Nonempty ι] (kᵢ : ι → Subfield k) (hdir : Directed (· ≤ ·) kᵢ) (hk : iSup kᵢ = ⊤)
    (s : Finset k) :
    ∃ i, ∀ x ∈ s, x ∈ kᵢ i := by
  classical
  refine s.induction_on ?_ ?_
  · -- Any stage works for the empty finite set.
    refine ⟨Classical.choice inferInstance, ?_⟩
    intro x hx
    cases hx
  · intro a s ha hs
    -- First place the old finite set in one stage and the new coefficient in another stage.
    obtain ⟨i, hi⟩ := hs
    have ha_mem_iSup : a ∈ (iSup kᵢ : Subfield k) := by
      rw [hk]
      simp
    obtain ⟨j, hj⟩ := (Subfield.mem_iSup_of_directed hdir).1 ha_mem_iSup
    -- Directedness moves both pieces of finite data to a common stage.
    obtain ⟨m, him, hjm⟩ := hdir i j
    refine ⟨m, ?_⟩
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx'
    · exact hjm hj
    · exact him (hi x hx')

/-- Helper for Lemma 10.166.5: regularity is invariant under a ring isomorphism. -/
lemma isRegularRing_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    [IsRegularRing R] :
    IsRegularRing S := by
  -- Descend regularity along the inverse isomorphism using faithful-flat descent.
  let f : S →+* R := e.symm.toRingHom
  have hf : RingHom.FaithfullyFlat f := by
    exact RingHom.FaithfullyFlat.of_bijective e.symm.bijective
  exact isRegularRing_of_faithfullyFlat f hf

/-- Helper for Lemma 10.166.5: the stage tensor product `K₀ ⊗[k₀] A` identifies with the tensor
stage `A ⊗[k] (k ⊗[k₀] K₀)` via commutativity and base-change cancellation. -/
noncomputable def tensor_stage_regular_source_compare
    {k₀ : Type u} [Field k₀] [Algebra k₀ k] [Algebra k₀ A] [IsScalarTower k₀ k A]
    {K₀ : Type (max u v)} [Field K₀] [Algebra k₀ K₀] :
    (K₀ ⊗[k₀] A) ≃+* (A ⊗[k] (k ⊗[k₀] K₀)) :=
  let e₁ : K₀ ⊗[k₀] A ≃+* A ⊗[k₀] K₀ :=
    (Algebra.TensorProduct.comm (R := k₀) (A := K₀) (B := A)).toRingEquiv
  let e₂ : A ⊗[k₀] K₀ ≃+* A ⊗[k] (k ⊗[k₀] K₀) :=
    ((Algebra.TensorProduct.cancelBaseChange k₀ k A A K₀).toRingEquiv).symm
  e₁.trans e₂

/-- Helper for Lemma 10.166.5: stagewise geometric regularity already gives regularity after
base change to the tensor stage `k ⊗[k₀] K₀`. -/
lemma stage_tensor_regular_of_descended_purelyInseparable_stage
    {k₀ : Type u} [Field k₀] [Algebra k₀ k] [Algebra k₀ A] [IsScalarTower k₀ k A]
    {K₀ : Type (max u v)} [Field K₀] [Algebra k₀ K₀]
    [IsGeometricallyRegular k₀ A]
    [FiniteDimensional k₀ K₀] [IsPurelyInseparable k₀ K₀] :
    IsRegularRing (A ⊗[k] (k ⊗[k₀] K₀)) := by
  letI : IsRegularRing (K₀ ⊗[k₀] A) :=
    IsGeometricallyRegular.isRegularRing_baseChange (k := k₀) (A := A) K₀
  let eTensor : (K₀ ⊗[k₀] A) ≃+* (A ⊗[k] (k ⊗[k₀] K₀)) :=
    tensor_stage_regular_source_compare (k := k) (A := A) (k₀ := k₀) (K₀ := K₀)
  -- Proof comment: geometric regularity over the stage field gives regularity of `K₀ ⊗ A`,
  -- and the fixed tensor comparison transports that regularity to `A ⊗ (k ⊗ K₀)`.
  exact isRegularRing_of_ringEquiv eTensor

/-- Helper for Lemma 10.166.5: a descended stage model compares the stage tensor product with the
target tensor product by the standard commutation and base-change cancellation isomorphisms. -/
noncomputable def tensor_compare_of_descended_stage_model
    {k₀ : Type u} [Field k₀] [Algebra k₀ k] [Algebra k₀ A] [IsScalarTower k₀ k A]
    (K : Type (max u v)) [CommRing K] [Algebra k K]
    {K₀ : Type (max u v)} [Field K₀] [Algebra k₀ K₀]
    (e : (k ⊗[k₀] K₀) ≃ₐ[k] K) :
    (K₀ ⊗[k₀] A) ≃+* (K ⊗[k] A) :=
  -- Proof comment: first commute the stage tensor product into the order needed by
  -- `cancelBaseChange`, then rewrite the scalar-extension factor via `e`, and finally commute
  -- back to the target tensor order.
  let e₁ : K₀ ⊗[k₀] A ≃+* A ⊗[k₀] K₀ :=
    (Algebra.TensorProduct.comm (R := k₀) (A := K₀) (B := A)).toRingEquiv
  let e₂ : A ⊗[k₀] K₀ ≃+* A ⊗[k] (k ⊗[k₀] K₀) :=
    ((Algebra.TensorProduct.cancelBaseChange k₀ k A A K₀).toRingEquiv).symm
  let e₃ : A ⊗[k] (k ⊗[k₀] K₀) ≃+* A ⊗[k] K :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[k] A) e).toRingEquiv
  let e₄ : A ⊗[k] K ≃+* K ⊗[k] A :=
    (Algebra.TensorProduct.comm (R := k) (A := A) (B := K)).toRingEquiv
  e₁.trans <| e₂.trans <| e₃.trans e₄

/-- Helper for Lemma 10.166.5: once the finite purely inseparable test field has descended to one
stage, stagewise geometric regularity transports regularity back to the original tensor product. -/
lemma isRegularRing_tensorBaseChange_of_descended_stage
    {k₀ : Type u} [Field k₀] [Algebra k₀ k] [Algebra k₀ A] [IsScalarTower k₀ k A]
    (K : Type (max u v)) [Field K] [Algebra k K]
    [IsGeometricallyRegular k₀ A]
    {K₀ : Type (max u v)} [Field K₀] [Algebra k₀ K₀]
    [FiniteDimensional k₀ K₀] [IsPurelyInseparable k₀ K₀]
    (e : (k ⊗[k₀] K₀) ≃ₐ[k] K) :
    IsRegularRing (K ⊗[k] A) := by
  letI : IsRegularRing (K₀ ⊗[k₀] A) :=
    IsGeometricallyRegular.isRegularRing_baseChange (k := k₀) (A := A) K₀
  let eTensor : (K₀ ⊗[k₀] A) ≃+* (K ⊗[k] A) :=
    tensor_compare_of_descended_stage_model (A := A) (K := K) e
  -- Proof comment: the stage hypothesis gives regularity for the descended tensor product, and
  -- the tensor comparison ring isomorphism transports it to the original test ring.
  exact isRegularRing_of_ringEquiv eTensor

/-- Helper for Lemma 10.166.5: in characteristic zero, a finite purely inseparable extension is
already equal to the base field. -/
noncomputable def algEquiv_base_of_charZero_purelyInseparable
    [CharZero k]
    (K : Type (max u v)) [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsPurelyInseparable k K] :
    K ≃ₐ[k] k := by
  letI : PerfectField k := PerfectField.ofCharZero
  letI : Algebra.IsSeparable k K := inferInstance
  have hsurj : Function.Surjective (algebraMap k K) :=
    IsPurelyInseparable.surjective_algebraMap_of_isSeparable k K
  have hbij : Function.Bijective (algebraMap k K) :=
    ⟨(algebraMap k K).injective, hsurj⟩
  -- Proof comment: a purely inseparable extension over a perfect field is trivial, so the
  -- structure map `k → K` is a bijective `k`-algebra hom.
  exact (AlgEquiv.ofBijective (Algebra.ofId k K) hbij).symm

/-- Helper for Lemma 10.166.5: in positive characteristic, a finite purely inseparable extension
admits finitely many generators with one common `p^e`-power relation, and the finitely many
coefficients of those relations already lie in one stage of the directed union. -/
lemma exists_stage_common_qpow_generators_of_finite_purelyInseparable
    [Nonempty ι]
    (kᵢ : ι → Subfield k) (hdir : Directed (· ≤ ·) kᵢ) (hk : iSup kᵢ = ⊤)
    (K : Type (max u v)) [Field K] [Algebra k K]
    [FiniteDimensional k K] {p : ℕ} [Fact p.Prime] [CharP k p]
    [IsPurelyInseparable k K] :
    ∃ (s : Finset K) (e : ℕ) (i : ι),
      IntermediateField.adjoin k (↑s : Set K) = ⊤ ∧
        ∀ a ∈ s, ∃ c : kᵢ i, a ^ (p ^ e) = algebraMap (kᵢ i) K c := by
  classical
  obtain ⟨s, e, hs_top, hs_pow⟩ :=
    generating_finset_with_common_qpow_mem_base (Kx := k) (L := K) (p := p)
  choose b hb using hs_pow
  let coeffs : Finset k := s.attach.image fun a ↦ b a.1 a.2
  obtain ⟨i, hi⟩ := finite_subset_subfield_stage (kᵢ := kᵢ) hdir hk coeffs
  refine ⟨s, e, i, hs_top, ?_⟩
  intro a ha
  have hb_mem : b a ha ∈ kᵢ i := by
    exact hi (b a ha) <| by
      refine Finset.mem_image.mpr ?_
      exact ⟨⟨a, ha⟩, by simp⟩
  refine ⟨⟨b a ha, hb_mem⟩, ?_⟩
  -- Proof comment: the coefficient now lies in the chosen stage, so the original `k`-equation
  -- is literally the desired stage-valued one.
  simpa using hb a ha

/-- Helper for Lemma 10.166.5: reindex the descended common `p^e`-power generators by `Fin n`
so that the Chapter 9 tuple language can drive the positive-characteristic descent. -/
lemma stage_generator_tuple_with_common_qpow
    [Nonempty ι]
    (kᵢ : ι → Subfield k) (hdir : Directed (· ≤ ·) kᵢ) (hk : iSup kᵢ = ⊤)
    (K : Type (max u v)) [Field K] [Algebra k K]
    [FiniteDimensional k K] {p : ℕ} [Fact p.Prime] [CharP k p]
    [IsPurelyInseparable k K] :
    ∃ (n e : ℕ) (i : ι) (α : Fin n → K) (c : Fin n → kᵢ i),
      Situation_9_12_7.stage k α (Fin.last n) = ⊤ ∧
        ∀ j, α j ^ (p ^ e) = algebraMap (kᵢ i) K (c j) := by
  classical
  obtain ⟨s, e, i, hs_top, hs_pow⟩ :=
    exists_stage_common_qpow_generators_of_finite_purelyInseparable
      (kᵢ := kᵢ) (hdir := hdir) (hk := hk) (K := K) (p := p)
  let eι : {a // a ∈ s} ≃ Fin s.card := Finset.equivFin s
  have hs_pow' :
      ∀ a : {a // a ∈ s}, ∃ c : kᵢ i, ((a : K) ^ (p ^ e)) = algebraMap (kᵢ i) K c := by
    intro a
    exact hs_pow a a.2
  choose coeff hcoeff using hs_pow'
  refine ⟨s.card, e, i, fun j ↦ ((eι.symm j : {a // a ∈ s}) : K), fun j ↦ coeff (eι.symm j), ?_, ?_⟩
  · have hrange :
        Set.range (fun j : Fin s.card ↦ ((eι.symm j : {a // a ∈ s}) : K)) = (↑s : Set K) := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact (eι.symm j).2
      · intro hx
        refine ⟨eι ⟨x, hx⟩, ?_⟩
        simp
    have hstage_range :
        Situation_9_12_7.stage k (fun j : Fin s.card ↦ ((eι.symm j : {a // a ∈ s}) : K))
            (Fin.last s.card) =
          IntermediateField.adjoin k
            (Set.range fun j : Fin s.card ↦ ((eι.symm j : {a // a ∈ s}) : K)) := by
      unfold Situation_9_12_7.stage
      congr
      ext x
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨j, j.2, rfl⟩
    -- Proof comment: the last Chapter 9 stage adjoins exactly the full image of the tuple.
    calc
      Situation_9_12_7.stage k (fun j : Fin s.card ↦ ((eι.symm j : {a // a ∈ s}) : K))
          (Fin.last s.card) =
        IntermediateField.adjoin k
          (Set.range fun j : Fin s.card ↦ ((eι.symm j : {a // a ∈ s}) : K)) := hstage_range
      _ = IntermediateField.adjoin k (↑s : Set K) := by
        rw [hrange]
      _ = ⊤ := hs_top
  · intro j
    -- Proof comment: each tuple coordinate inherits its descended common `p^e`-power relation.
    simpa using hcoeff (eι.symm j)

/-- Helper for Lemma 10.166.5: the stage field generated by the descended common `p^e`-power
generators is finite-dimensional over that stage. -/
lemma finiteDimensional_adjoin_of_stage_common_qpow
    [Nonempty ι]
    (kᵢ : ι → Subfield k) (hdir : Directed (· ≤ ·) kᵢ) (hk : iSup kᵢ = ⊤)
    (K : Type (max u v)) [Field K] [Algebra k K]
    [FiniteDimensional k K] {p : ℕ} [Fact p.Prime] [CharP k p]
    [IsPurelyInseparable k K] :
    ∃ (s : Finset K) (i : ι),
      IntermediateField.adjoin k (↑s : Set K) = ⊤ ∧
        FiniteDimensional (kᵢ i) (IntermediateField.adjoin (kᵢ i) (↑s : Set K)) := by
  classical
  obtain ⟨s, e, i, hs_top, hs_pow⟩ :=
    exists_stage_common_qpow_generators_of_finite_purelyInseparable
      (kᵢ := kᵢ) (hdir := hdir) (hk := hk) (K := K) (p := p)
  refine ⟨s, i, hs_top, ?_⟩
  letI : Fintype ((↑s : Set K)) := s.finite_toSet.fintype
  -- Proof comment: each generator satisfies a monic polynomial `X^(p^e) - c` over the chosen
  -- stage, so adjoining finitely many of them stays finite-dimensional.
  exact IntermediateField.finiteDimensional_adjoin (K := ↥(kᵢ i)) (L := K)
    (S := (↑s : Set K)) fun x hx ↦ by
      rcases hs_pow x (by simpa using hx) with ⟨c, hc⟩
      have hxpow : IsIntegral ↥(kᵢ i) ((x : K) ^ (p ^ e)) := by
        rw [hc]
        exact isIntegral_algebraMap
      exact IsIntegral.of_pow (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) _) hxpow

/-- Helper for Lemma 10.166.5: the stage field generated by the descended common `p^e`-power
generators is purely inseparable over that stage. -/
lemma isPurelyInseparable_adjoin_of_stage_common_qpow
    [Nonempty ι]
    (kᵢ : ι → Subfield k) (hdir : Directed (· ≤ ·) kᵢ) (hk : iSup kᵢ = ⊤)
    (K : Type (max u v)) [Field K] [Algebra k K]
    [FiniteDimensional k K] {p : ℕ} [Fact p.Prime] [CharP k p]
    [IsPurelyInseparable k K] :
    ∃ (s : Finset K) (i : ι),
      IntermediateField.adjoin k (↑s : Set K) = ⊤ ∧
        IsPurelyInseparable (kᵢ i) (IntermediateField.adjoin (kᵢ i) (↑s : Set K)) := by
  classical
  obtain ⟨s, e, i, hs_top, hs_pow⟩ :=
    exists_stage_common_qpow_generators_of_finite_purelyInseparable
      (kᵢ := kᵢ) (hdir := hdir) (hk := hk) (K := K) (p := p)
  refine ⟨s, i, hs_top, ?_⟩
  letI : CharP ↥(kᵢ i) p := inferInstance
  letI : ExpChar ↥(kᵢ i) p := inferInstance
  -- Proof comment: the common `p^e`-power witnesses are exactly the input expected by the owner
  -- criterion `IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem`.
  rw [IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem
    (F := ↥(kᵢ i)) (E := K) p]
  intro x hx
  rcases hs_pow x (by simpa using hx) with ⟨c, hc⟩
  exact ⟨e, ⟨c, hc.symm⟩⟩

/-- Helper for Lemma 10.166.5: the last Chapter 9 stage attached to a tuple is exactly the field
obtained by adjoining the tuple range. -/
lemma stage_last_eq_adjoin_range
    {k₀ : Type*} {K : Type*} [Field k₀] [Field K] [Algebra k₀ K]
    {n : ℕ} (α : Fin n → K) :
    Situation_9_12_7.stage k₀ α (Fin.last n) = IntermediateField.adjoin k₀ (Set.range α) := by
  -- Proof comment: at the last stage the defining prefix condition is simply membership in the
  -- full range of the tuple.
  unfold Situation_9_12_7.stage
  congr
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, j.2, rfl⟩

/-- Helper for Lemma 10.166.5: the descended tuple already defines a finite-dimensional last stage
over the chosen source field. -/
lemma finiteDimensional_stage_of_common_qpow
    {k₀ : Type*} {K : Type*} [Field k₀] [Field K] [Algebra k₀ K]
    {n e p : ℕ} [Fact p.Prime] (α : Fin n → K) (c : Fin n → k₀)
    (hαq : ∀ j, α j ^ (p ^ e) = algebraMap k₀ K (c j)) :
    FiniteDimensional k₀ (Situation_9_12_7.stage k₀ α (Fin.last n)) := by
  rw [stage_last_eq_adjoin_range (k₀ := k₀) α]
  letI : Fintype (Set.range α) := (Set.finite_range α).fintype
  -- Proof comment: every generator satisfies a monic polynomial `X^(p^e) - c_j`, so the adjoin
  -- of the finite tuple is finite-dimensional over the base field.
  exact IntermediateField.finiteDimensional_adjoin (K := k₀) (L := K) (S := Set.range α) fun x hx ↦ by
    rcases hx with ⟨j, rfl⟩
    have hxpow : IsIntegral k₀ ((α j : K) ^ (p ^ e)) := by
      rw [hαq j]
      exact isIntegral_algebraMap
    exact IsIntegral.of_pow (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) _) hxpow

/-- Helper for Lemma 10.166.5: the descended tuple already defines a purely inseparable last stage
over the chosen source field. -/
lemma isPurelyInseparable_stage_of_common_qpow
    {k₀ : Type*} {K : Type*} [Field k₀] [Field K] [Algebra k₀ K]
    {n e p : ℕ} [Fact p.Prime] [CharP k₀ p]
    (α : Fin n → K) (c : Fin n → k₀)
    (hαq : ∀ j, α j ^ (p ^ e) = algebraMap k₀ K (c j)) :
    IsPurelyInseparable k₀ (Situation_9_12_7.stage k₀ α (Fin.last n)) := by
  letI : ExpChar k₀ p := inferInstance
  rw [stage_last_eq_adjoin_range (k₀ := k₀) α]
  -- Proof comment: each generator has a displayed `p^e`-power in the base field, which is
  -- exactly the criterion for the adjoined stage to be purely inseparable.
  rw [IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem (F := k₀) (E := K) p]
  intro x hx
  rcases hx with ⟨j, rfl⟩
  exact ⟨e, ⟨c j, (hαq j).symm⟩⟩

/-- Helper for Lemma 10.166.5: if `K₀` is the last Chapter 9 stage of `α`, then the same tuple,
viewed inside `K₀`, already generates all of `K₀`. -/
lemma intrinsic_stage_tuple_top
    {k₀ : Type*} {K : Type*} [Field k₀] [Field K] [Algebra k₀ K]
    {n : ℕ}
    (α : Fin n → K)
    (K₀ : IntermediateField k₀ K)
    (hK₀ : K₀ = Situation_9_12_7.stage k₀ α (Fin.last n))
    (u : Fin n → K₀)
    (hu : ∀ j, ((u j : K₀) : K) = α j) :
    Situation_9_12_7.stage k₀ u (Fin.last n) = ⊤ := by
  have htop_lift :
      IntermediateField.lift (F := K₀) (⊤ : IntermediateField k₀ K₀) = K₀ := by
    ext x
    constructor
    · intro hx
      exact IntermediateField.lift_le (⊤ : IntermediateField k₀ K₀) hx
    · intro hx
      exact (IntermediateField.mem_lift (E := (⊤ : IntermediateField k₀ K₀)) ⟨x, hx⟩).2 (by simp)
  -- Proof comment: lifting the stage generated by `u` back into `K` recovers the original last
  -- stage generated by `α`, so injectivity of `lift` forces the stage over `K₀` to be top.
  apply (IntermediateField.lift_injective K₀)
  calc
    IntermediateField.lift (F := K₀)
        (Situation_9_12_7.stage k₀ u (Fin.last n)) =
      IntermediateField.adjoin k₀ (Subtype.val '' Set.range u) := by
        rw [stage_last_eq_adjoin_range (k₀ := k₀) u, IntermediateField.lift_adjoin]
    _ = IntermediateField.adjoin k₀ (Set.range α) := by
      congr 1
      ext x
      constructor
      · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
        exact ⟨j, (hu j).symm⟩
      · rintro ⟨j, rfl⟩
        exact ⟨u j, ⟨j, rfl⟩, hu j⟩
    _ = K₀ := by
      rw [hK₀, stage_last_eq_adjoin_range (k₀ := k₀) α]
    _ = IntermediateField.lift (F := K₀) (⊤ : IntermediateField k₀ K₀) := htop_lift.symm

/-- Helper for Lemma 10.166.5: after inserting the intrinsic stage tuple into the tensor product,
the same common `p^e`-power relations still hold over the enlarged base field. -/
lemma tensor_intrinsic_tuple_qpow
    {k₀ : Type*} {k : Type*} {K₀ : Type*}
    [Field k₀] [Field k] [Field K₀] [Algebra k₀ k] [Algebra k₀ K₀]
    {n e p : ℕ} [Fact p.Prime]
    (u : Fin n → K₀) (c : Fin n → k₀)
    (huq : ∀ j, u j ^ (p ^ e) = algebraMap k₀ K₀ (c j)) :
    let β : Fin n → k ⊗[k₀] K₀ := fun j ↦
      Algebra.TensorProduct.includeRight (R := k₀) (A := k) (B := K₀) (u j)
    ∀ j, β j ^ (p ^ e) = algebraMap k (k ⊗[k₀] K₀) (algebraMap k₀ k (c j)) := by
  intro β j
  -- Proof comment: `includeRight` preserves powers, and the tensor relation identifies
  -- `1 ⊗ c_j` with `(algebraMap k₀ k c_j) ⊗ 1`.
  calc
    β j ^ (p ^ e) =
      Algebra.TensorProduct.includeRight (R := k₀) (A := k) (B := K₀)
        (u j ^ (p ^ e)) := by
          simp [β, map_pow]
    _ =
      Algebra.TensorProduct.includeRight (R := k₀) (A := k) (B := K₀)
        (algebraMap k₀ K₀ (c j)) := by
          rw [huq j]
    _ = (1 : k) ⊗ₜ[k₀] algebraMap k₀ K₀ (c j) := rfl
    _ = algebraMap k₀ k (c j) ⊗ₜ[k₀] (1 : K₀) := by
          symm
          simpa using
            (Algebra.TensorProduct.tmul_one_eq_one_tmul
              (R := k₀) (A := k) (B := K₀) (c j))
    _ = algebraMap k (k ⊗[k₀] K₀) (algebraMap k₀ k (c j)) := rfl

/-- Helper for Lemma 10.166.5: if the intrinsic tuple already generates the descended stage field
`K₀`, then its tensor-side image generates the whole scalar extension `k ⊗[k₀] K₀` over `k`. -/
lemma tensor_intrinsic_tuple_top
    {k₀ : Type*} {k : Type*} {K₀ : Type*}
    [Field k₀] [Field k] [Field K₀] [Algebra k₀ k] [Algebra k₀ K₀]
    [Algebra.IsAlgebraic k₀ K₀]
    {n : ℕ}
    (u : Fin n → K₀)
    (hu_top : Situation_9_12_7.stage k₀ u (Fin.last n) = ⊤) :
    let β : Fin n → k ⊗[k₀] K₀ := fun j ↦
      Algebra.TensorProduct.includeRight (R := k₀) (A := k) (B := K₀) (u j)
    Algebra.adjoin k (Set.range β) = ⊤ := by
  intro β
  have hu_top_if : IntermediateField.adjoin k₀ (Set.range u) = ⊤ := by
    rw [← stage_last_eq_adjoin_range (k₀ := k₀) u]
    exact hu_top
  have hu_top' : Algebra.adjoin k₀ (Set.range u) = ⊤ := by
    -- Proof comment: the last Chapter 9 stage is exactly the field generated by the tuple range.
    exact
      (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic
        (F := k₀) (E := K₀) (S := Set.range u)
        (fun x _ ↦ Algebra.IsAlgebraic.isAlgebraic x)).mp hu_top_if
  have himage :
      ((fun x : K₀ ↦ (1 : k) ⊗ₜ[k₀] x) '' Set.range u) = Set.range β := by
    ext y
    constructor
    · rintro ⟨x, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨u j, ⟨j, rfl⟩, rfl⟩
  -- Proof comment: after scalar extension, the generators become the literal `1 ⊗ u_j` tuple.
  rw [← himage]
  simpa using
    (Algebra.TensorProduct.adjoin_one_tmul_image_eq_top
      (R := k₀) (A := k) (B := K₀) (s := Set.range u) hu_top')

/-- Helper for Lemma 10.166.5: any element of the algebra generated by a tuple with common
`p^e`-power scalar relations again has a `p^e`-power in the base field. -/
lemma pow_eq_algebraMap_of_mem_adjoin_common_qpow
    {K : Type*} [CommRing K] [Nontrivial K] [Algebra k K]
    {n e p : ℕ} [Fact p.Prime] [CharP k p]
    (α : Fin n → K) (c : Fin n → k)
    {x : K} (hx : x ∈ Algebra.adjoin k (Set.range α))
    (hαq : ∀ j, α j ^ (p ^ e) = algebraMap k K (c j)) :
    ∃ a : k, x ^ (p ^ e) = algebraMap k K a := by
  letI : CharP K p := charP_of_injective_ringHom (algebraMap k K).injective p
  let P : (y : K) → y ∈ Algebra.adjoin k (Set.range α) → Prop :=
    fun y _ ↦ ∃ a : k, y ^ (p ^ e) = algebraMap k K a
  -- Proof comment: the set of elements whose `p^e`-power lands in the base field is closed under
  -- the algebra operations because Frobenius is additive and multiplicative in characteristic `p`.
  change P x hx
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨j, rfl⟩
    exact ⟨c j, hαq j⟩
  · intro r
    exact ⟨r ^ (p ^ e), by simp [map_pow]⟩
  · intro y z _ _ hy hz
    rcases hy with ⟨a, ha⟩
    rcases hz with ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    calc
      (y + z) ^ (p ^ e) = y ^ (p ^ e) + z ^ (p ^ e) := by
        rw [add_pow_char_pow (p := p) (n := e)]
      _ = algebraMap k K a + algebraMap k K b := by rw [ha, hb]
      _ = algebraMap k K (a + b) := by simp
  · intro y z _ _ hy hz
    rcases hy with ⟨a, ha⟩
    rcases hz with ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    calc
      (y * z) ^ (p ^ e) = y ^ (p ^ e) * z ^ (p ^ e) := by rw [mul_pow]
      _ = algebraMap k K a * algebraMap k K b := by rw [ha, hb]
      _ = algebraMap k K (a * b) := by simp

/-- Helper for Lemma 10.166.5: if every prime ideal contains the kernel of an algebra map, then
that kernel is locally nilpotent. -/
lemma ker_isLocallyNilpotent_of_le_all_primes
    {B : Type*} [CommRing B] [Algebra k B]
    {K : Type*} [CommRing K] [Algebra k K]
    (ψ : B →ₐ[k] K)
    (hker : ∀ P : Ideal B, P.IsPrime → RingHom.ker ψ.toRingHom ≤ P) :
    (RingHom.ker ψ.toRingHom).IsLocallyNilpotent := by
  rw [Ideal.isLocallyNilpotent_iff]
  intro x hx
  rw [nilpotent_iff_mem_prime]
  intro P hP
  exact hker P hP hx

/-- Helper for Lemma 10.166.5: the canonical comparison from the descended tensor stage
`k ⊗[k₀] K₀` to the target field `K` multiplies the left scalar with the right-stage image. -/
noncomputable def tensor_stage_compare
    {k₀ : Type*} {k : Type*} {K₀ : Type*} {K : Type*}
    [CommSemiring k₀] [CommSemiring k] [CommSemiring K₀] [CommSemiring K]
    [Algebra k₀ k] [Algebra k₀ K₀] [Algebra k₀ K] [Algebra k K] [IsScalarTower k₀ k K]
    (φ : K₀ →ₐ[k₀] K) :
    (k ⊗[k₀] K₀) →ₐ[k] K :=
  -- Proof comment: use the tensor-product universal property with the identity `k`-algebra map on
  -- the left factor and the given stage inclusion on the right factor.
  Algebra.TensorProduct.lift (Algebra.ofId k K) φ (fun _ _ ↦ Commute.all _ _)

/-- Helper for Lemma 10.166.5: the canonical tensor-stage comparison sends each tensor generator
coming from the intrinsic stage tuple to the original generator in `K`. -/
lemma tensor_stage_compare_apply_tuple
    {k₀ : Type*} {k : Type*} {K₀ : Type*} {K : Type*}
    [CommSemiring k₀] [CommSemiring k] [CommSemiring K₀] [CommSemiring K]
    [Algebra k₀ k] [Algebra k₀ K₀] [Algebra k₀ K] [Algebra k K] [IsScalarTower k₀ k K]
    {n : ℕ}
    (φ : K₀ →ₐ[k₀] K)
    (u : Fin n → K₀) (α : Fin n → K)
    (hu : ∀ j, φ (u j) = α j) :
    ∀ j,
      tensor_stage_compare (k₀ := k₀) (k := k) (K₀ := K₀) (K := K) φ
          (Algebra.TensorProduct.includeRight (R := k₀) (A := k) (B := K₀) (u j)) =
        α j := by
  intro j
  have hcomp :=
    DFunLike.congr_fun
      (Algebra.TensorProduct.lift_comp_includeRight
        (f := Algebra.ofId k K) (g := φ) (hfg := fun _ _ ↦ Commute.all _ _))
      (u j)
  -- Proof comment: `lift_comp_includeRight` computes the comparison map on the right tensor
  -- generators, and `hu` identifies those images with the original tuple.
  simpa [tensor_stage_compare, hu j] using hcomp

/-- Helper for Lemma 10.166.5: if the original tuple generates `K` as a `k`-algebra, then the
canonical tensor-stage comparison is surjective. -/
lemma tensor_stage_compare_surjective
    {k₀ : Type*} {k : Type*} {K₀ : Type*} {K : Type*}
    [Field k₀] [Field k] [Field K₀] [Field K]
    [Algebra k₀ k] [Algebra k₀ K₀] [Algebra k₀ K] [Algebra k K] [IsScalarTower k₀ k K]
    {n : ℕ}
    (φ : K₀ →ₐ[k₀] K)
    (u : Fin n → K₀) (α : Fin n → K)
    (hu : ∀ j, φ (u j) = α j)
    (hα_top_alg : Algebra.adjoin k (Set.range α) = ⊤) :
    Function.Surjective
      (tensor_stage_compare (k₀ := k₀) (k := k) (K₀ := K₀) (K := K) φ) := by
  have hgen :
      Set.range α ⊆
        (tensor_stage_compare (k₀ := k₀) (k := k) (K₀ := K₀) (K := K) φ).range := by
    intro x hx
    rcases hx with ⟨j, rfl⟩
    refine ⟨Algebra.TensorProduct.includeRight (R := k₀) (A := k) (B := K₀) (u j), ?_⟩
    exact tensor_stage_compare_apply_tuple
      (k₀ := k₀) (k := k) (K₀ := K₀) (K := K) φ u α hu j
  have hrange :
      Algebra.adjoin k (Set.range α) ≤
        (tensor_stage_compare (k₀ := k₀) (k := k) (K₀ := K₀) (K := K) φ).range := by
    -- Proof comment: once the generators land in the image, the whole generated `k`-subalgebra
    -- lands in the image as well.
    exact Algebra.adjoin_le hgen
  have htop_range :
      (tensor_stage_compare (k₀ := k₀) (k := k) (K₀ := K₀) (K := K) φ).range = ⊤ := by
    -- Proof comment: the source tuple already generates all of `K`, so the comparison map has
    -- full algebraic range.
    apply top_unique
    rw [← hα_top_alg]
    exact hrange
  exact (AlgHom.range_eq_top
    (f := tensor_stage_compare (k₀ := k₀) (k := k) (K₀ := K₀) (K := K) φ)).mp htop_range

/-- Helper for Lemma 10.166.5: the prime spectrum of a tensor stage over a purely inseparable
field extension is a singleton. -/
lemma tensor_stage_primeSpectrum_subsingleton
    {k₀ : Type*} {k : Type*} {K₀ : Type*}
    [Field k₀] [Field k] [Field K₀]
    [Algebra k₀ k] [Algebra k₀ K₀]
    [IsPurelyInseparable k₀ K₀] :
    Subsingleton (PrimeSpectrum (k ⊗[k₀] K₀)) := by
  letI : Algebra k (k ⊗[k₀] K₀) := Algebra.TensorProduct.leftAlgebra
  have hfield_spec : Subsingleton (PrimeSpectrum k) := by
    -- Proof comment: a field has only the zero prime ideal.
    refine ⟨fun P Q ↦ ?_⟩
    ext x
    simp [Ideal.eq_bot_of_prime (I := P.asIdeal), Ideal.eq_bot_of_prime (I := Q.asIdeal)]
  have hhomeo :
      IsHomeomorph (PrimeSpectrum.comap (algebraMap k (k ⊗[k₀] K₀))) := by
    -- Proof comment: purely inseparable base change is a universal homeomorphism on spectra.
    simpa using
      (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable
        (k := k₀) (K := K₀) (R := k))
  -- Proof comment: injectivity of the spectral map collapses the tensor-stage spectrum to the
  -- unique point of `Spec k`.
  exact ⟨fun P Q ↦ hhomeo.injective (hfield_spec.elim _ _)⟩

/-- Helper for Lemma 10.166.5: if the prime spectrum of the source ring is a singleton, then the
kernel of any map from it to a field is locally nilpotent. -/
lemma kernel_isLocallyNilpotent_of_subsingleton_primeSpectrum
    {B : Type*} [CommRing B] [Algebra k B]
    {K : Type*} [Field K] [Algebra k K]
    (hspec : Subsingleton (PrimeSpectrum B))
    (ψ : B →ₐ[k] K) :
    (RingHom.ker ψ.toRingHom).IsLocallyNilpotent := by
  -- Proof comment: every prime ideal equals the kernel prime, so the kernel lies in every prime.
  apply ker_isLocallyNilpotent_of_le_all_primes (k := k) (K := K) ψ
  intro P hP
  let pSpec : PrimeSpectrum B := ⟨P, hP⟩
  let qSpec : PrimeSpectrum B := ⟨RingHom.ker ψ.toRingHom, RingHom.ker_isPrime _⟩
  have hpq : pSpec = qSpec := hspec.elim pSpec qSpec
  have hEq : P = RingHom.ker ψ.toRingHom := congrArg PrimeSpectrum.asIdeal hpq
  exact hEq ▸ (le_rfl : RingHom.ker ψ.toRingHom ≤ RingHom.ker ψ.toRingHom)

/-- Helper for Lemma 10.166.5: specialize the generic tensor-stage surjectivity statement to the
subfield inclusion `K₀ ↪ K`. -/
lemma tensor_stage_compare_surjective_specialized
    {k₀ : Type*} {k : Type*} {K : Type*}
    [Field k₀] [Field k] [Field K]
    [Algebra k₀ k] [Algebra k₀ K] [Algebra k K] [IsScalarTower k₀ k K]
    (K₀ : IntermediateField k₀ K)
    {n : ℕ}
    (u : Fin n → K₀) (α : Fin n → K)
    (hu : ∀ j, K₀.val (u j) = α j)
    (hα_top_alg : Algebra.adjoin k (Set.range α) = ⊤) :
    Function.Surjective
      (tensor_stage_compare (k₀ := k₀) (k := k) (K₀ := ↥K₀) (K := K) K₀.val) := by
  -- Proof comment: this is the generic surjectivity statement with the stage inclusion frozen.
  exact tensor_stage_compare_surjective
    (k₀ := k₀) (k := k) (K₀ := ↥K₀) (K := K)
    K₀.val u α hu hα_top_alg

/-- Helper for Lemma 10.166.5: after tensoring a surjective comparison map with `A`, reducedness
of the source kills the locally nilpotent tensor kernel, so the tensored map is bijective. -/
lemma tensored_stage_compare_bijective_of_reduced_source
    {B : Type*} [CommRing B] [Algebra k B]
    {K : Type*} [Field K] [Algebra k K]
    (ψ : B →ₐ[k] K)
    (hψsurj : Function.Surjective ψ)
    (hψker : (RingHom.ker ψ.toRingHom).IsLocallyNilpotent)
    [IsReduced (A ⊗[k] B)] :
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id k A) ψ) := by
  let g : A ⊗[k] B →ₐ[k] A ⊗[k] K :=
    Algebra.TensorProduct.map (AlgHom.id k A) ψ
  have hg_surj : Function.Surjective g := by
    -- Proof comment: tensoring the surjective comparison map with the identity on `A` stays
    -- surjective.
    simpa [g] using
      (Algebra.TensorProduct.map_surjective
        (R := k) (S := k) (A := A) (B := A) (C := B) (D := K)
        (f := AlgHom.id k A) (g := ψ)
        (by intro a; exact ⟨a, rfl⟩) hψsurj)
  have hgker : (RingHom.ker g.toRingHom).IsLocallyNilpotent := by
    -- Proof comment: right exactness identifies the tensor kernel with the image of `ker ψ`.
    rw [show RingHom.ker g.toRingHom =
        Ideal.map
          (Algebra.TensorProduct.includeRight
            (R := k) (A := A) (B := B)).toRingHom
          (RingHom.ker ψ.toRingHom) by
        simpa [g] using
          (Algebra.TensorProduct.lTensor_ker (A := A) (g := ψ) hψsurj)]
    simpa using
      Ideal.map_isLocallyNilpotent
        (Algebra.TensorProduct.includeRight
          (R := k) (A := A) (B := B)).toRingHom hψker
  have hgker_eq_bot : RingHom.ker g.toRingHom = ⊥ := by
    apply le_antisymm
    · intro x hx
      exact IsReduced.eq_zero x ((Ideal.isLocallyNilpotent_iff _).mp hgker x hx)
    · exact bot_le
  have hg_inj : Function.Injective g := by
    exact (RingHom.injective_iff_ker_eq_bot (f := g.toRingHom)).2 hgker_eq_bot
  simpa [g] using (show Function.Bijective g from ⟨hg_inj, hg_surj⟩)

/-- Helper for Lemma 10.166.5: if the descended tensor-stage comparison is surjective with
locally nilpotent kernel, then regularity on `A ⊗[k] B` transports to `A ⊗[k] K`. -/
lemma isRegularRing_tensor_target_of_surjective_locallyNilpotent_stage_compare
    {B : Type*} [CommRing B] [Algebra k B]
    {K : Type*} [Field K] [Algebra k K]
    (ψ : B →ₐ[k] K)
    (hψsurj : Function.Surjective ψ)
    (hψker : (RingHom.ker ψ.toRingHom).IsLocallyNilpotent)
    [IsReduced (A ⊗[k] B)] [IsRegularRing (A ⊗[k] B)] :
    IsRegularRing (A ⊗[k] K) := by
  let eTensor : (A ⊗[k] B) ≃ₐ[k] (A ⊗[k] K) :=
    AlgEquiv.ofBijective
      (Algebra.TensorProduct.map (AlgHom.id k A) ψ)
      (tensored_stage_compare_bijective_of_reduced_source
        (k := k) (A := A) ψ hψsurj hψker)
  -- Proof comment: tensoring `ψ` with the identity on `A` becomes bijective on the reduced
  -- regular source ring, so the resulting algebra equivalence transports regularity to the
  -- target tensor product.
  exact isRegularRing_of_ringEquiv eTensor.toRingEquiv

/-- Helper for Lemma 10.166.5: a finite purely inseparable test field over `k` descends to one
stage of the directed union of subfields strongly enough to prove regularity of the corresponding
tensor product with `A`. -/
lemma isRegularRing_tensorBaseChange_of_directed_iSup_subfields
    [Nonempty ι]
    (kᵢ : ι → Subfield k) (hdir : Directed (· ≤ ·) kᵢ) (hk : iSup kᵢ = ⊤)
    (hA : ∀ i, IsGeometricallyRegular (kᵢ i) A)
    (K : Type (max u v)) [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsPurelyInseparable k K] :
    IsRegularRing (K ⊗[k] A) := by
  classical
  obtain hchar0 | ⟨p, hp, hpchar⟩ := CharP.exists' k
  · letI : CharZero k := hchar0
    let i : ι := Classical.choice inferInstance
    letI : IsRegularRing A :=
      Algebra.isRegularRing_of_isGeometricallyRegular (k := ↥(kᵢ i)) (A := A)
    let eK : K ≃ₐ[k] k :=
      algEquiv_base_of_charZero_purelyInseparable (k := k) (K := K)
    let eTensor : (K ⊗[k] A) ≃+* (k ⊗[k] A) :=
      (Algebra.TensorProduct.congr eK (AlgEquiv.refl : A ≃ₐ[k] A)).toRingEquiv
    let eA : (k ⊗[k] A) ≃+* A :=
      (Algebra.TensorProduct.lid (R := k) (A := A)).toRingEquiv
    -- Proof comment: replace the characteristic-zero test field by `k` itself, then collapse the
    -- tensor product over `k`; stagewise geometric regularity already implies `A` is regular.
    exact isRegularRing_of_ringEquiv (R := A) (e := (eTensor.trans eA).symm)
  · letI : Fact p.Prime := hp
    letI : CharP k p := hpchar
    obtain ⟨n, e, i, α, c, hα_top, hαq⟩ :=
      stage_generator_tuple_with_common_qpow
        (kᵢ := kᵢ) (hdir := hdir) (hk := hk) (K := K) (p := p)
    let K₀ := Situation_9_12_7.stage (↥(kᵢ i)) α (Fin.last n)
    letI : Field ↥K₀ := inferInstance
    letI : Algebra (↥(kᵢ i)) ↥K₀ := inferInstance
    letI : FiniteDimensional (↥(kᵢ i)) K₀ :=
      finiteDimensional_stage_of_common_qpow
        (k₀ := ↥(kᵢ i)) (K := K) (p := p) α c hαq
    letI : IsPurelyInseparable (↥(kᵢ i)) K₀ :=
      isPurelyInseparable_stage_of_common_qpow
        (k₀ := ↥(kᵢ i)) (K := K) (p := p) α c hαq
    have hmemK₀ : ∀ j, α j ∈ K₀ := by
      intro j
      change α j ∈ Situation_9_12_7.stage (↥(kᵢ i)) α (Fin.last n)
      rw [stage_last_eq_adjoin_range (k₀ := ↥(kᵢ i)) α]
      exact IntermediateField.mem_adjoin_of_mem (↥(kᵢ i)) ⟨j, rfl⟩
    let u : Fin n → K₀ := fun j ↦ ⟨α j, hmemK₀ j⟩
    have huq : ∀ j, u j ^ (p ^ e) = algebraMap (↥(kᵢ i)) K₀ (c j) := by
      intro j
      apply (algebraMap K₀ K).injective
      change ((u j : K) ^ (p ^ e)) = algebraMap (↥(kᵢ i)) K (c j)
      simpa [u] using hαq j
    have husucc_stage :
        Situation_9_12_7.IsSuccessiveRootTuple (↥(kᵢ i)) u u := by
      -- Proof comment: after passing to the intrinsic tuple of the descended stage field, the
      -- Chapter 9 successive-root package applies without needing finite-dimensionality of `K`
      -- over the source stage.
      exact successive_root_tuple_of_common_qpow_data
        (Kx := ↥(kᵢ i)) (L := K₀) (E := K₀) (p := p) (e := e) u u c huq huq
    have hu_top :
        Situation_9_12_7.stage (↥(kᵢ i)) u (Fin.last n) = ⊤ := by
      -- Proof comment: the intrinsic tuple is just `α` seen inside the descended stage.
      exact intrinsic_stage_tuple_top
        (k₀ := ↥(kᵢ i)) α K₀ rfl u (fun j ↦ rfl)
    have hα_top_alg : Algebra.adjoin k (Set.range α) = ⊤ := by
      have hα_top_if : IntermediateField.adjoin k (Set.range α) = ⊤ := by
        rw [← stage_last_eq_adjoin_range (k₀ := k) α]
        exact hα_top
      -- Proof comment: because `K / k` is algebraic, the subfield and algebra-generation
      -- conditions are equivalent.
      exact
          (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic
          (F := k) (E := K) (S := Set.range α)
          (fun x _ ↦ Algebra.IsAlgebraic.isAlgebraic x)).mp hα_top_if
    let B : Type (max u v) := k ⊗[↥(kᵢ i)] ↥K₀
    letI : Algebra (↥(kᵢ i)) k := Algebra.ofSubsemiring (kᵢ i)
    letI : Algebra (↥(kᵢ i)) ↥K₀ := inferInstance
    letI : CommRing (k ⊗[↥(kᵢ i)] ↥K₀) := TensorProduct.instCommRing
    letI : Algebra k (k ⊗[↥(kᵢ i)] ↥K₀) := Algebra.TensorProduct.leftAlgebra
    letI : Algebra (↥(kᵢ i)) K := Algebra.ofSubsemiring (kᵢ i)
    letI : IsScalarTower (↥(kᵢ i)) k K :=
      inferInstance
    have hu_val : ∀ j, K₀.val (u j) = α j := by
      intro j
      rfl
    let ψ : (k ⊗[↥(kᵢ i)] ↥K₀) →ₐ[k] K :=
      tensor_stage_compare
        (k₀ := ↥(kᵢ i)) (k := k) (K₀ := ↥K₀) (K := K) K₀.val
    have hψsurj : Function.Surjective ψ := by
      -- Proof comment: the descended tensor-stage generators map back to the original tuple
      -- `α`, which already generates all of `K` over `k`.
      exact tensor_stage_compare_surjective_specialized
        (k₀ := ↥(kᵢ i)) (k := k) (K := K) K₀ u α hu_val hα_top_alg
    have hB_spec_subsingleton : Subsingleton (PrimeSpectrum B) := by
      -- Route correction: isolate the universal-homeomorphism argument in a dedicated helper so
      -- the main proof no longer rebuilds the singleton-spectrum argument in place.
      simpa [B] using
        (tensor_stage_primeSpectrum_subsingleton
          (k₀ := ↥(kᵢ i)) (k := k) (K₀ := ↥K₀))
    have hψker : (RingHom.ker ψ.toRingHom).IsLocallyNilpotent := by
      -- Proof comment: once the tensor-stage spectrum is a singleton, every prime contains the
      -- kernel prime, so local nilpotence follows from the kernel helper.
      exact kernel_isLocallyNilpotent_of_subsingleton_primeSpectrum
        (k := k) (B := B) (K := K) hB_spec_subsingleton ψ
    letI : IsGeometricallyRegular (↥(kᵢ i)) A := hA i
    letI : IsRegularRing (A ⊗[k] B) :=
      -- Route correction: package the `comm + cancelBaseChange` transport once so the positive
      -- characteristic branch reuses the descended stage regularity without re-elaborating it.
      by
        -- Proof comment: the stage hypothesis makes `K₀ ⊗[kᵢ i] A` regular, and the dedicated
        -- tensor-stage comparison moves that regularity to `A ⊗[k] B`.
        simpa [B] using
          (stage_tensor_regular_of_descended_purelyInseparable_stage
            (k := k) (A := A) (k₀ := ↥(kᵢ i)) (K₀ := ↥K₀))
    letI : IsNormalRing (A ⊗[k] B) :=
      isNormalRing_of_isRegularRing
    letI : IsReduced (A ⊗[k] B) := inferInstance
    letI : IsRegularRing (A ⊗[k] K) :=
      -- Proof comment: tensoring the stage comparison with `A` kills the locally nilpotent
      -- kernel on the reduced source ring, so regularity pushes forward to `A ⊗[k] K`.
      isRegularRing_tensor_target_of_surjective_locallyNilpotent_stage_compare
        (k := k) (A := A) (B := B) (K := K) ψ hψsurj hψker
    let eKA : (A ⊗[k] K) ≃+* (K ⊗[k] A) :=
      (Algebra.TensorProduct.comm (R := k) (A := A) (B := K)).toRingEquiv
    -- Proof comment: the tensor-stage map becomes an isomorphism after tensoring with `A`
    -- because its locally nilpotent kernel vanishes on the reduced regular source ring.
    exact isRegularRing_of_ringEquiv eKA

/-- Lemma 10.166.5: if `k` is the directed colimit of subfields `kᵢ` and `A` is geometrically
regular over every `kᵢ`, then `A` is geometrically regular over `k`. -/
-- Proof sketch: to prove geometric regularity over `k`, test against a finite purely inseparable
-- extension `K/k`. The finitely many coefficients defining `K` descend to some stage `kᵢ`,
-- producing a finite purely inseparable extension `Kᵢ/kᵢ` with `K ≃ Kᵢ ⊗[kᵢ] k`; then
-- `K ⊗[k] A` identifies with `Kᵢ ⊗[kᵢ] A`, which is regular by the hypothesis on stage `i`.
theorem isGeometricallyRegular_of_directed_iSup_subfields
    [Nonempty ι]
    (kᵢ : ι → Subfield k) (hdir : Directed (· ≤ ·) kᵢ) (hk : iSup kᵢ = ⊤)
    (hA : ∀ i, IsGeometricallyRegular (kᵢ i) A) :
    IsGeometricallyRegular k A := by
  -- Route correction: the source proof works by descending the finite purely inseparable test
  -- field to one stage, not by trying to compare the original test field directly over `kᵢ`.
  -- Proof comment: after constructing the descended stage model `K₀ / kᵢ i`, the formal endgame
  -- is already isolated in `isRegularRing_tensorBaseChange_of_descended_stage`.
  rw [isGeometricallyRegular_iff_forall_finite_purelyInseparable_tensorBaseChange_isRegularRing]
  intro K _ _ _ _
  -- Proof comment: the missing descent package is now isolated in a single helper that directly
  -- produces regularity of the finite purely inseparable test tensor product.
  exact isRegularRing_tensorBaseChange_of_directed_iSup_subfields
    (kᵢ := kᵢ) (hdir := hdir) (hk := hk) (hA := hA) (K := K)

end

end Algebra
