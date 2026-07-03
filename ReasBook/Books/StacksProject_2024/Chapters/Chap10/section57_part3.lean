import Mathlib
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.Data.Finset.Card
import Mathlib.Order.Preorder.Finite
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_57_9 (from Chap10) -/
open scoped BigOperators DirectSum
open HomogeneousLocalization

universe u v w

noncomputable section

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M]
variable (𝒜 : ℕ → Submodule R S) (ℳ : ℕ → Submodule R M)
variable [GradedAlgebra 𝒜]
variable [SetLike.GradedSMul 𝒜 ℳ]

/-- The standard fraction `m / f^n` in the localization `M[f⁻¹]`. -/
private noncomputable abbrev awayPowMk {d : ℕ} (f : 𝒜 d) (n : ℕ) (m : M) :
    LocalizedModule.Away (f : S) M :=
  LocalizedModule.mk m ⟨(f : S) ^ n, by exact ⟨n, rfl⟩⟩

/-- The degree-zero homogeneous localization `S_(f)` inherits an `R`-algebra structure through the
composite map `R → S₀ → S_(f)`. -/
noncomputable instance (f : S) :
    Algebra R (Away 𝒜 f) :=
  Algebra.compHom (Away 𝒜 f) (algebraMap R (𝒜 0))

/-- The canonical algebra structures on `R`, `S₀`, and `S` form a scalar tower. -/
instance : IsScalarTower R (𝒜 0) S := by
  let h : ∀ x : R, algebraMap R S x = algebraMap (𝒜 0) S (algebraMap R (𝒜 0) x) := fun _ ↦ rfl
  exact IsScalarTower.of_algebraMap_eq h

/-- The ordinary localization `M[f⁻¹]` regarded by restriction of scalars as a module over the
degree-zero homogeneous localization `S_(f)`. -/
noncomputable instance (f : S) :
    Module (Away 𝒜 f) (LocalizedModule.Away f M) :=
  Module.compHom (LocalizedModule.Away f M)
    (algebraMap (Away 𝒜 f) (Localization.Away f))

private def awayDegreeZeroPartSet (ℳ : ℕ → Submodule R M) [SetLike.GradedSMul 𝒜 ℳ] {d : ℕ}
    (f : 𝒜 d) : Set (LocalizedModule.Away (f : S) M) :=
  { z | ∃ n, ∃ m : ℳ (n * d), z = awayPowMk 𝒜 f n (m : M) }

omit [GradedAlgebra 𝒜] in
private theorem awayDegreeZeroPartSet_zero_mem (ℳ : ℕ → Submodule R M)
    [SetLike.GradedSMul 𝒜 ℳ] {d : ℕ} (f : 𝒜 d) :
    0 ∈ awayDegreeZeroPartSet 𝒜 ℳ f :=
  ⟨0, 0, by simp [awayPowMk]⟩

private theorem awayDegreeZeroPartSet_add_mem (ℳ : ℕ → Submodule R M)
    [SetLike.GradedSMul 𝒜 ℳ] {d : ℕ} (f : 𝒜 d) {x y : LocalizedModule.Away (f : S) M}
    (hx : x ∈ awayDegreeZeroPartSet 𝒜 ℳ f) (hy : y ∈ awayDegreeZeroPartSet 𝒜 ℳ f) :
    x + y ∈ awayDegreeZeroPartSet 𝒜 ℳ f := by
  rcases hx with ⟨n, m, rfl⟩
  rcases hy with ⟨k, m', rfl⟩
  refine ⟨n + k, ⟨(f : S) ^ k • (m : M) + (f : S) ^ n • (m' : M), ?_⟩, ?_⟩
  · rw [Nat.add_mul]
    refine add_mem ?_ ?_
    · simpa [nsmul_eq_mul, Nat.add_comm] using
        (SetLike.GradedSMul.smul_mem (SetLike.pow_mem_graded k f.2) m.2)
    · simpa [nsmul_eq_mul] using
        (SetLike.GradedSMul.smul_mem (SetLike.pow_mem_graded n f.2) m'.2)
  · rw [LocalizedModule.mk_add_mk]
    congr 1
    ext
    simp [pow_add]

private theorem awayDegreeZeroPartSet_smul_mem (ℳ : ℕ → Submodule R M)
    [SetLike.GradedSMul 𝒜 ℳ] {d : ℕ} (f : 𝒜 d) (z : Away 𝒜 (f : S))
    {x : LocalizedModule.Away (f : S) M} (hx : x ∈ awayDegreeZeroPartSet 𝒜 ℳ f) :
    z • x ∈ awayDegreeZeroPartSet 𝒜 ℳ f := by
  rcases hx with ⟨n, m, rfl⟩
  obtain ⟨k, a, ha, rfl⟩ := Away.mk_surjective 𝒜 f.2 z
  refine ⟨k + n, ⟨a • (m : M), ?_⟩, ?_⟩
  · simpa [Nat.add_mul, nsmul_eq_mul] using SetLike.GradedSMul.smul_mem ha m.2
  · change (algebraMap (Away 𝒜 (f : S)) (Localization.Away (f : S))
        (Away.mk 𝒜 f.2 k a ha)) •
        awayPowMk 𝒜 f n (m : M) = awayPowMk 𝒜 f (k + n) (a • (m : M))
    rw [HomogeneousLocalization.algebraMap_apply, Away.val_mk, LocalizedModule.mk_smul_mk]
    congr 1
    ext
    simp [pow_add, mul_comm]

/-- If the graded ring `S` is finite type over `R`, then its degree-zero part `S₀ = 𝒜 0` is
finite type over `R`. This is the `bridge/view` step from the ambient graded ring to the canonical
owner base ring for homogeneous localization. -/
private theorem degreeZero_finiteType [Algebra.FiniteType R S] :
    Algebra.FiniteType R (𝒜 0) := by
  rw [← RingHom.finiteType_algebraMap]
  let g : S →+* 𝒜 0 := GradedRing.projZeroRingHom' 𝒜
  have hcomp : (g.comp (algebraMap R S)).FiniteType :=
    RingHom.FiniteType.comp_surjective
      (by
        rw [RingHom.finiteType_algebraMap]
        infer_instance)
      (GradedRing.projZeroRingHom'_surjective 𝒜)
  convert hcomp using 1
  ext r
  exact (DirectSum.decompose_of_mem_same 𝒜 (SetLike.algebraMap_mem_graded 𝒜 r)).symm

/-- Lemma 10.57.9 (1): if `S` is of finite type over `R`, then for every homogeneous element
`f : 𝒜 d` the degree-zero homogeneous localization `S_(f)` is of finite type over `R`. The core
owner theorem is `HomogeneousLocalization.Away.finiteType`, and `degreeZero_finiteType` supplies
the bridge from `R` to `S₀`. -/
theorem away_finiteType [Algebra.FiniteType R S] {d : ℕ} (f : 𝒜 d) :
    Algebra.FiniteType R (Away 𝒜 (f : S)) := by
  rw [← RingHom.finiteType_algebraMap]
  have hR0 : (algebraMap R (𝒜 0)).FiniteType := by
    rw [RingHom.finiteType_algebraMap]
    exact degreeZero_finiteType 𝒜
  have h0Away : (algebraMap (𝒜 0) (Away 𝒜 (f : S))).FiniteType := by
    rw [RingHom.finiteType_algebraMap]
    let _ : Algebra.FiniteType (𝒜 0) S :=
      Algebra.FiniteType.of_restrictScalars_finiteType R (𝒜 0) S
    exact HomogeneousLocalization.Away.finiteType _ _ f.2
  convert RingHom.FiniteType.comp h0Away hR0 using 1

/-- For a homogeneous element `f : 𝒜 d`, the degree-zero homogeneous localization `M_(f)` is the
`S_(f)`-submodule of `M[f⁻¹]` consisting of fractions `m / f^n` with `m` homogeneous of degree
`n * d`. -/
noncomputable def awayDegreeZeroPart (ℳ : ℕ → Submodule R M) [SetLike.GradedSMul 𝒜 ℳ] {d : ℕ}
    (f : 𝒜 d) :
    Submodule (Away 𝒜 (f : S)) (LocalizedModule.Away (f : S) M) :=
  { carrier := awayDegreeZeroPartSet 𝒜 ℳ f
    zero_mem' := awayDegreeZeroPartSet_zero_mem 𝒜 ℳ f
    add_mem' := awayDegreeZeroPartSet_add_mem 𝒜 ℳ f
    smul_mem' := awayDegreeZeroPartSet_smul_mem 𝒜 ℳ f }

/-- A fraction of `M[f⁻¹]` lies in `M_(f)` exactly when it is represented by `m / f^n` with
`m` homogeneous of degree `n * d`. -/
theorem mem_awayDegreeZeroPart_iff {d : ℕ} (f : 𝒜 d) {z : LocalizedModule.Away (f : S) M} :
    z ∈ awayDegreeZeroPart 𝒜 ℳ f ↔
      ∃ n, ∃ m : ℳ (n * d),
        z = LocalizedModule.mk (m : M) ⟨(f : S) ^ n, by exact ⟨n, rfl⟩⟩ := by
  constructor
  · rintro ⟨n, m, rfl⟩
    exact ⟨n, m, by simp [awayPowMk]⟩
  · rintro ⟨n, m, rfl⟩
    exact ⟨n, m, by simp [awayPowMk]⟩

/-- The standard homogeneous generators `m / f^n` belong to `M_(f)`. -/
theorem awayDegreeZeroPart_mk_mem {d n : ℕ} (f : 𝒜 d) {m : M} (hm : m ∈ ℳ (n * d)) :
    LocalizedModule.mk m ⟨(f : S) ^ n, by exact ⟨n, rfl⟩⟩ ∈ awayDegreeZeroPart 𝒜 ℳ f :=
  ⟨n, ⟨m, hm⟩, by simp [awayPowMk]⟩

omit [Algebra R S] in
/-- Helper for Lemma 10.57.9: a finite graded module admits a finite homogeneous generating
family obtained by decomposing an arbitrary finite generating family into homogeneous pieces and
reindexing it by `Fin n`. -/
private theorem exists_finite_homogeneous_module_generators_nat
    [Module.Finite S M] [DirectSum.Decomposition ℳ] :
    ∃ n : ℕ, ∃ x : Fin n → M, ∃ η : Fin n → ℕ,
      (∀ j, x j ∈ ℳ (η j)) ∧ Submodule.span S (Set.range x) = ⊤ := by
  classical
  let hfg : (⊤ : Submodule S M).FG := Module.Finite.fg_top (R := S) (M := M)
  obtain ⟨n, g, hg⟩ := (Submodule.fg_iff_exists_fin_generating_family (R := S)
    (M := M) (N := (⊤ : Submodule S M))).mp hfg
  let κ : Type := Σ j : Fin n, { k // k ∈ (DirectSum.decompose ℳ (g j)).support }
  let x : κ → M := fun j => (DirectSum.decompose ℳ (g j.1) j.2.1 : ℳ j.2.1)
  let η : κ → ℕ := fun j => j.2.1
  let _ : Fintype κ := inferInstance
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let x' : Fin (Fintype.card κ) → M := fun j ↦ x (e.symm j)
  let η' : Fin (Fintype.card κ) → ℕ := fun j ↦ η (e.symm j)
  have hx' : ∀ j, x' j ∈ ℳ (η' j) := by
    -- Each reindexed component lies in the same homogeneous degree as before reindexing.
    intro j
    exact (DirectSum.decompose ℳ (g (e.symm j).1) (e.symm j).2.1).2
  have hx'_range : Set.range x' = Set.range x := by
    -- Reindexing by `equivFin` preserves the generating set.
    ext m
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e.symm j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨e j, by simp [x', e]⟩
  have hspan' : Submodule.span S (Set.range x') = ⊤ := by
    -- The original generators lie in the span of all homogeneous components, hence so does `M`.
    rw [hx'_range, ← top_le_iff, ← hg, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [← DirectSum.sum_support_decompose ℳ (g j)]
    exact Submodule.sum_mem _ fun n hn =>
      Submodule.subset_span ⟨⟨j, ⟨n, hn⟩⟩, rfl⟩
  exact ⟨Fintype.card κ, x', η', hx', hspan'⟩

/-- Helper for Lemma 10.57.9: a finite-type graded ring admits finitely many positive-degree
homogeneous algebra generators over its degree-zero part, indexed by `Fin n`. -/
private theorem exists_finite_positive_homogeneous_ring_generators_nat
    [Algebra.FiniteType (𝒜 0) S] :
    ∃ n : ℕ, ∃ v : Fin n → S, ∃ δ : Fin n → ℕ,
      (∀ i, 0 < δ i ∧ v i ∈ 𝒜 (δ i)) ∧ Algebra.adjoin (𝒜 0) (Set.range v) = ⊤ := by
  classical
  obtain ⟨s, hs, hsdeg⟩ := GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero 𝒜
  let e : s ≃ Fin s.card := Finset.equivFin s
  let v : Fin s.card → S := fun i ↦ ((e.symm i : s) : S)
  choose δ hδ_ne hδmem using
    fun i : Fin s.card ↦ hsdeg (v i) ((e.symm i).2)
  have hv_range : Set.range v = (s : Set S) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hx
      refine ⟨e ⟨x, hx⟩, ?_⟩
      simp [v, e]
  -- The finite homogeneous generators are already indexed by `Fin s.card`.
  refine ⟨s.card, v, δ, ?_, ?_⟩
  · intro i
    exact ⟨Nat.pos_of_ne_zero (hδ_ne i), hδmem i⟩
  · simpa [hv_range] using hs

omit [Module R M] in
/-- Helper for Lemma 10.57.9: multiplying the localized fraction `m / f^n` by the degree-zero
element `g^d / f^e` inserts the corresponding homogeneous block into the numerator and shifts the
denominator by `e`. -/
private theorem isLocalizationElem_smul_awayPowMk {d e n : ℕ} (f : 𝒜 d) {g : S}
    (hg : g ∈ 𝒜 e) (m : M) :
    (Away.isLocalizationElem f.2 hg) • awayPowMk 𝒜 f n m =
      awayPowMk 𝒜 f (n + e) ((g ^ d) • m) := by
  -- Compare the two localized module fractions after mapping to the ordinary localization.
  change (algebraMap (Away 𝒜 (f : S)) (Localization.Away (f : S))
      (Away.isLocalizationElem f.2 hg)) • awayPowMk 𝒜 f n m =
    awayPowMk 𝒜 f (n + e) ((g ^ d) • m)
  rw [HomogeneousLocalization.algebraMap_apply, Away.val_mk, LocalizedModule.mk_smul_mk]
  -- The two representatives agree after combining the denominator powers of `f`.
  congr 1
  ext
  simp [pow_add, mul_comm]

omit [Module R M] in
/-- Helper for Lemma 10.57.9: repeated multiplication by `g^d / f^e` produces the expected
power `g^(q * d)` in the numerator and shifts the denominator exponent by `q * e`. -/
private theorem isLocalizationElem_pow_smul_awayPowMk {d e n q : ℕ} (f : 𝒜 d) {g : S}
    (hg : g ∈ 𝒜 e) (m : M) :
    (Away.isLocalizationElem f.2 hg) ^ q • awayPowMk 𝒜 f n m =
      awayPowMk 𝒜 f (n + q * e) ((g ^ (q * d)) • m) := by
  induction q generalizing n m with
  | zero =>
      -- The zeroth power does not change the localized fraction.
      simp [awayPowMk]
  | succ q ih =>
      -- Apply the one-step transport lemma after the induction hypothesis.
      rw [pow_succ, mul_smul, isLocalizationElem_smul_awayPowMk (𝒜 := 𝒜)
        (f := f) (hg := hg) (n := n)]
      rw [ih (n := n + e) (m := (g ^ d) • m)]
      congr 1
      · simp [Nat.succ_mul, add_assoc, add_left_comm, add_comm]
      · calc
          g ^ (q * d) • g ^ d • m = (g ^ (q * d) * g ^ d) • m := by
            simp [smul_smul]
          _ = g ^ (q * d + d) • m := by
            simp [pow_add]
          _ = g ^ ((q + 1) * d) • m := by
            congr 1
            rw [Nat.succ_mul]

omit [Module R M] in
/-- Helper for Lemma 10.57.9: a finite product of degree-zero localization elements transports a
single homogeneous fraction by accumulating both the denominator shift and the numerator blocks. -/
private theorem finset_prod_isLocalizationElem_pow_smul_awayPowMk
    {ι : Type*} {d n : ℕ} (f : 𝒜 d) (s : Finset ι)
    (v : ι → S) (δ q : ι → ℕ) (hv : ∀ i, v i ∈ 𝒜 (δ i)) (m : M) :
    (s.prod fun i => (Away.isLocalizationElem f.2 (hv i)) ^ (q i)) • awayPowMk 𝒜 f n m =
      awayPowMk 𝒜 f (n + s.sum fun i => q i * δ i) (((s.prod fun i => v i ^ (q i * d)) : S) • m) := by
  classical
  induction s using Finset.induction_on generalizing n m with
  | empty =>
      -- The empty product contributes no transport data.
      simp [awayPowMk]
  | @insert i s hi ih =>
      -- Move the first generator block across the fraction, then recurse on the remaining product.
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      calc
        ((Away.isLocalizationElem f.2 (hv i)) ^ (q i) *
            s.prod fun x => (Away.isLocalizationElem f.2 (hv x)) ^ (q x)) •
            awayPowMk 𝒜 f n m =
            (s.prod fun x => (Away.isLocalizationElem f.2 (hv x)) ^ (q x)) •
              ((Away.isLocalizationElem f.2 (hv i)) ^ (q i) • awayPowMk 𝒜 f n m) := by
            simp [smul_smul, mul_comm]
        _ =
            (s.prod fun x => (Away.isLocalizationElem f.2 (hv x)) ^ (q x)) •
              awayPowMk 𝒜 f (n + q i * δ i) ((v i ^ (q i * d)) • m) := by
            rw [isLocalizationElem_pow_smul_awayPowMk (𝒜 := 𝒜) (f := f) (hg := hv i) (n := n)
              (q := q i)]
        _ =
            awayPowMk 𝒜 f ((n + q i * δ i) + s.sum fun x => q x * δ x)
              (((s.prod fun x => v x ^ (q x * d)) : S) • ((v i ^ (q i * d)) • m)) := by
            rw [ih (n := n + q i * δ i) (m := (v i ^ (q i * d)) • m)]
        _ = awayPowMk 𝒜 f (n + (q i * δ i + s.sum fun x => q x * δ x))
              (((insert i s).prod fun x => v x ^ (q x * d) : S) • m) := by
            simp [Finset.prod_insert, hi, smul_smul, add_assoc, mul_comm]

/-- Helper for Lemma 10.57.9: splitting each exponent into quotient and remainder modulo `d`
packages the exact denominator data needed for the source-style bounded reduction. -/
private theorem remainder_degree_data_of_weighted_eq_multiple
    {ι : Type*} [Fintype ι] {d : ℕ} (hd : 0 < d)
    (e δ : ι → ℕ) {η a : ℕ} (ha : (∑ i, e i * δ i) + η = a * d) :
    d ∣ ((∑ i, (e i % d) * δ i) + η) ∧
      (((∑ i, (e i % d) * δ i) + η) / d + ∑ i, (e i / d) * δ i = a) := by
  let r : ℕ := (∑ i, (e i % d) * δ i) + η
  let q : ℕ := ∑ i, (e i / d) * δ i
  have hsplit :
      (∑ i, e i * δ i) = (∑ i, (e i % d) * δ i) + d * q := by
    -- Expand each exponent as quotient plus remainder, then collect the `d`-multiple block.
    calc
      (∑ i, e i * δ i) = ∑ i, (((e i % d) + d * (e i / d)) * δ i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [Nat.mod_add_div]
      _ = ∑ i, ((e i % d) * δ i + d * ((e i / d) * δ i)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [Nat.add_mul, Nat.mul_assoc]
      _ = (∑ i, (e i % d) * δ i) + ∑ i, d * ((e i / d) * δ i) := by
        rw [Finset.sum_add_distrib]
      _ = (∑ i, (e i % d) * δ i) + d * q := by
        rw [← Finset.mul_sum]
  have hmain : r + d * q = a * d := by
    -- The total weighted degree separates into the remainder contribution plus the quotient block.
    calc
      r + d * q = (∑ i, e i * δ i) + η := by
        dsimp [r]
        rw [hsplit]
        ac_rfl
      _ = a * d := ha
  have hq_le : q ≤ a := by
    exact Nat.le_of_mul_le_mul_right
      (by
        calc
          q * d ≤ r + q * d := Nat.le_add_left _ _
          _ = a * d := by
            simpa [r, q, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmain)
      hd
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hq_le
  have hr_eq : r = k * d := by
    -- After factoring `a = q + k`, cancellation isolates the remainder block as a `d`-multiple.
    have hcancel : q * d + r = q * d + k * d := by
      calc
        q * d + r = r + d * q := by ac_rfl
        _ = a * d := hmain
        _ = (q + k) * d := by simpa [hk]
        _ = q * d + k * d := by rw [Nat.add_mul]
    exact Nat.add_left_cancel hcancel
  constructor
  · exact ⟨k, by simpa [r, Nat.mul_comm] using hr_eq⟩
  · -- Dividing the isolated multiple by `d` recovers the remainder denominator exponent.
    calc
      r / d + q = k + q := by
        rw [hr_eq]
        rw [Nat.mul_comm, Nat.mul_div_right _ hd]
      _ = a := by simpa [Nat.add_comm] using hk.symm

/-- Helper for Lemma 10.57.9: a weighted monomial in homogeneous ring generators sends a
homogeneous module generator to the predicted graded piece. -/
private theorem weighted_monomial_smul_mem_degree_piece_nat
    {ι κ : Type*} [Fintype ι]
    (v : ι → S) (δ : ι → ℕ) (x : κ → M) (η : κ → ℕ)
    (hv : ∀ i, v i ∈ 𝒜 (δ i)) (hx : ∀ j, x j ∈ ℳ (η j))
    (e : ι → ℕ) (j : κ) :
    ((∏ i, v i ^ e i : S) • x j) ∈ ℳ ((∑ i, e i * δ i) + η j) := by
  -- The weighted degree of the ring monomial adds to the degree of the chosen module generator.
  have hprod :
      (∏ i, v i ^ e i : S) ∈ 𝒜 (∑ i, e i * δ i) := by
    simpa [nsmul_eq_mul] using
      (SetLike.prod_pow_mem_graded 𝒜 δ v e (fun i _ ↦ hv i))
  simpa [nsmul_eq_mul] using
    (SetLike.GradedSMul.smul_mem hprod (hx j) :
      ((∏ i, v i ^ e i : S) • x j) ∈ ℳ ((∑ i, e i * δ i) + η j))

omit [SetLike.GradedSMul 𝒜 ℳ] in
/-- Helper for Lemma 10.57.9: the source-style quotient/remainder rewrite holds on the module
side, expressing an arbitrary homogeneous monomial fraction as an `Away`-scalar multiple of a
bounded-remainder fraction. -/
private theorem awayPowMk_monomial_mod_div_eq
    {ι κ : Type*} [Fintype ι] {d a : ℕ}
    (f : 𝒜 d) (hd : 0 < d)
    (v : ι → S) (δ : ι → ℕ) (hv : ∀ i, v i ∈ 𝒜 (δ i))
    (x : κ → M) (η : κ → ℕ) (_hx : ∀ j, x j ∈ ℳ (η j))
    (e : ι → ℕ) (j : κ)
    (ha : (∑ i, e i * δ i) + η j = a * d) :
    awayPowMk 𝒜 f a (((∏ i, v i ^ e i : S) • x j)) =
      (∏ i, (Away.isLocalizationElem f.2 (hv i)) ^ (e i / d)) •
        awayPowMk 𝒜 f (((∑ i, (e i % d) * δ i) + η j) / d)
          (((∏ i, v i ^ (e i % d) : S) • x j)) := by
  let q : ι → ℕ := fun i => e i / d
  let r : ι → ℕ := fun i => e i % d
  obtain ⟨-, hdenom⟩ := remainder_degree_data_of_weighted_eq_multiple
    (d := d) hd e δ (η := η j) ha
  have hprod :
      ((∏ i, v i ^ (q i * d) : S) • ((∏ i, v i ^ r i : S) • x j)) =
        ((∏ i, v i ^ e i : S) • x j) := by
    -- The quotient block and remainder block recombine to the original exponent vector.
    calc
      ((∏ i, v i ^ (q i * d) : S) • ((∏ i, v i ^ r i : S) • x j)) =
          (((∏ i, v i ^ (q i * d) : S) * ∏ i, v i ^ r i) • x j) := by
            simp [smul_smul]
      _ = ((∏ i, v i ^ (q i * d + r i) : S) • x j) := by
            congr 1
            rw [← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl ?_
            intro i hi
            rw [← pow_add]
      _ = ((∏ i, v i ^ e i : S) • x j) := by
            congr 1
            refine Finset.prod_congr rfl ?_
            intro i hi
            congr 1
            calc
              q i * d + r i = r i + d * q i := by
                dsimp [q, r]
                ac_rfl
              _ = e i := by
                dsimp [q, r]
                exact Nat.mod_add_div (e i) d
  -- Apply the finite-product transport lemma, then rewrite the denominator and numerator data.
  have htransport :=
    finset_prod_isLocalizationElem_pow_smul_awayPowMk
      (𝒜 := 𝒜) (f := f) (n := (((∑ i, (e i % d) * δ i) + η j) / d))
      (s := Finset.univ) v δ q hv
      (((∏ i, v i ^ r i : S) • x j))
  rw [hdenom] at htransport
  simpa [q, r, hprod] using htransport.symm

/-- Helper for Lemma 10.57.9: the bounded remainder indices record a module generator together
with the remainder data modulo `d` whose weighted degree is still divisible by `d`. -/
private abbrev boundedRemainderIndex
    {ι κ : Type*} [Fintype ι] {d : ℕ} (δ : ι → ℕ) (η : κ → ℕ) : Type _ :=
  { p : κ × (ι → Fin d) // d ∣ ((∑ i, (p.2 i : ℕ) * δ i) + η p.1) }

/-- Helper for Lemma 10.57.9: each bounded remainder numerator lands in the degree prescribed by
its denominator exponent. This isolates the divisibility bookkeeping needed to build the bounded
family inside `awayDegreeZeroPart`. -/
private theorem bounded_remainder_mem_degree_piece
    {ι κ : Type*} [Fintype ι] {d : ℕ}
    (_f : 𝒜 d) (v : ι → S) (δ : ι → ℕ) (x : κ → M) (η : κ → ℕ)
    (hv : ∀ i, v i ∈ 𝒜 (δ i)) (hx : ∀ j, x j ∈ ℳ (η j))
    (p : boundedRemainderIndex (d := d) (δ := δ) η) :
    ((∏ i, v i ^ (p.1.2 i : ℕ) : S) • x p.1.1) ∈
      ℳ ((((∑ i, (p.1.2 i : ℕ) * δ i) + η p.1.1) / d) * d) := by
  -- First place the weighted monomial in its natural graded piece.
  have hm :=
    weighted_monomial_smul_mem_degree_piece_nat
      (𝒜 := 𝒜) (ℳ := ℳ) v δ x η hv hx (fun i ↦ (p.1.2 i : ℕ)) p.1.1
  -- Then rewrite that degree using the divisibility witness stored in the index.
  simpa [Nat.div_mul_cancel p.2] using hm

/-- Helper for Lemma 10.57.9: the source-style bounded remainder family consists of all fractions
whose remainder exponents are strictly less than `d`. -/
private noncomputable def boundedRemainderFamily
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (f : 𝒜 d) (v : ι → S) (δ : ι → ℕ) (x : κ → M) (η : κ → ℕ)
    (hv : ∀ i, v i ∈ 𝒜 (δ i)) (hx : ∀ j, x j ∈ ℳ (η j)) :
    boundedRemainderIndex (d := d) (δ := δ) η → awayDegreeZeroPart 𝒜 ℳ f :=
  fun p ↦
    ⟨LocalizedModule.mk
        (((∏ i, v i ^ (p.1.2 i : ℕ) : S) • x p.1.1) : M)
        ⟨(f : S) ^ (((∑ i, (p.1.2 i : ℕ) * δ i) + η p.1.1) / d),
          ⟨(((∑ i, (p.1.2 i : ℕ) * δ i) + η p.1.1) / d), rfl⟩⟩,
      awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f
        (bounded_remainder_mem_degree_piece
          (𝒜 := 𝒜) (ℳ := ℳ) f v δ x η hv hx p)⟩

/-- Helper for Lemma 10.57.9: every explicit bounded remainder generator belongs to the span of
the finite bounded family. This removes the subtype packaging from the later span induction. -/
private theorem bounded_remainder_generator_mem_span
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (f : 𝒜 d) (v : ι → S) (δ : ι → ℕ) (x : κ → M) (η : κ → ℕ)
    (hv : ∀ i, v i ∈ 𝒜 (δ i)) (hx : ∀ j, x j ∈ ℳ (η j))
    (j : κ) (r : ι → Fin d)
    (hdiv : d ∣ ((∑ i, (r i : ℕ) * δ i) + η j)) :
    boundedRemainderFamily (𝒜 := 𝒜) (ℳ := ℳ) f v δ x η hv hx ⟨(j, r), hdiv⟩ ∈
      Submodule.span (Away 𝒜 (f : S))
        (Set.range (boundedRemainderFamily (𝒜 := 𝒜) (ℳ := ℳ) f v δ x η hv hx)) := by
  -- A spanning family contains each of its chosen generators.
  exact Submodule.subset_span ⟨⟨(j, r), hdiv⟩, rfl⟩

/-- Helper for Lemma 10.57.9: quotient/remainder reduction sends every admissible monomial
fraction into the span of the bounded remainder family. This is the module-side source step that
replaces an arbitrary numerator by its remainder modulo `d`. -/
private theorem awayPowMk_monomial_mem_span_bounded_family
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] {d a : ℕ}
    (f : 𝒜 d) (hd : 0 < d)
    (v : ι → S) (δ : ι → ℕ) (hv : ∀ i, v i ∈ 𝒜 (δ i))
    (x : κ → M) (η : κ → ℕ) (hx : ∀ j, x j ∈ ℳ (η j))
    (e : ι → ℕ) (j : κ)
    (ha : (∑ i, e i * δ i) + η j = a * d) :
    (⟨awayPowMk 𝒜 f a (((∏ i, v i ^ e i : S) • x j)),
      awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f
        (by
          -- The source monomial numerator has exactly degree `a * d`.
          simpa [ha] using
            (weighted_monomial_smul_mem_degree_piece_nat
              (𝒜 := 𝒜) (ℳ := ℳ) v δ x η hv hx e j))⟩ :
      awayDegreeZeroPart 𝒜 ℳ f) ∈
      Submodule.span (Away 𝒜 (f : S))
        (Set.range (boundedRemainderFamily (𝒜 := 𝒜) (ℳ := ℳ) f v δ x η hv hx)) := by
  let r : ι → Fin d := fun i ↦ ⟨e i % d, Nat.mod_lt _ hd⟩
  have hdiv :
      d ∣ ((∑ i, (r i : ℕ) * δ i) + η j) := by
    -- The remainder data is exactly the divisible block produced by the weighted degree equation.
    simpa [r] using
      (remainder_degree_data_of_weighted_eq_multiple
        (d := d) hd e δ (η := η j) ha).1
  have hrewrite :
      (awayPowMk 𝒜 f a (((∏ i, v i ^ e i : S) • x j)) :
          LocalizedModule.Away (f : S) M) =
        (∏ i, (Away.isLocalizationElem f.2 (hv i)) ^ (e i / d)) •
          ((boundedRemainderFamily (𝒜 := 𝒜) (ℳ := ℳ) f v δ x η hv hx
              ⟨(j, r), hdiv⟩ : awayDegreeZeroPart 𝒜 ℳ f) :
            LocalizedModule.Away (f : S) M) := by
    -- Rewrite the arbitrary monomial fraction as an `Away`-scalar multiple of its bounded
    -- remainder representative.
    simpa [boundedRemainderFamily, awayPowMk, r] using
      (awayPowMk_monomial_mod_div_eq
        (𝒜 := 𝒜) (ℳ := ℳ) (f := f) hd v δ hv x η hx e j ha)
  have hz :
      (⟨awayPowMk 𝒜 f a (((∏ i, v i ^ e i : S) • x j)),
        awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f
          (by
            -- Reuse the degree computation for the source monomial numerator.
            simpa [ha] using
              (weighted_monomial_smul_mem_degree_piece_nat
                (𝒜 := 𝒜) (ℳ := ℳ) v δ x η hv hx e j))⟩ :
        awayDegreeZeroPart 𝒜 ℳ f) =
        (∏ i, (Away.isLocalizationElem f.2 (hv i)) ^ (e i / d)) •
          boundedRemainderFamily (𝒜 := 𝒜) (ℳ := ℳ) f v δ x η hv hx ⟨(j, r), hdiv⟩ := by
    -- Equality in the subtype follows from equality of the underlying localized fractions.
    apply Subtype.ext
    simpa using hrewrite
  -- The rewritten monomial lies in the span because the bounded generator already does.
  rw [hz]
  exact Submodule.smul_mem _ _
    (bounded_remainder_generator_mem_span
      (𝒜 := 𝒜) (ℳ := ℳ) f v δ x η hv hx j r hdiv)

/-- Helper for Lemma 10.57.9: if a weighted degree is `0` and every ring generator has positive
degree, then every exponent is `0` and the module generator also has degree `0`. -/
private theorem weighted_degree_eq_zero_forces_trivial_monomial
    {ι : Type*} [Fintype ι] (δ : ι → ℕ) (hδ : ∀ i, 0 < δ i)
    (e : ι → ℕ) {η : ℕ} (ha : (∑ i, e i * δ i) + η = 0) :
    (∀ i, e i = 0) ∧ η = 0 := by
  have hsum : ∑ i, e i * δ i = 0 := Nat.eq_zero_of_add_eq_zero_right ha
  have hη : η = 0 := Nat.eq_zero_of_add_eq_zero_left ha
  refine ⟨?_, hη⟩
  intro i
  have hle : e i * δ i ≤ ∑ j, e j * δ j := by
    simpa using
      (Finset.single_le_sum (f := fun j ↦ e j * δ j)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i))
  have hmul : e i * δ i = 0 := by
    exact Nat.eq_zero_of_le_zero (by simpa [hsum] using hle)
  exact (eq_zero_or_eq_zero_of_mul_eq_zero hmul).resolve_right (Nat.ne_of_gt (hδ i))

omit [Module R M] [GradedAlgebra 𝒜] in
/-- Helper for Lemma 10.57.9: localizing a finite sum with a fixed denominator exponent distributes
over that sum. This is the bookkeeping step used after rewriting a numerator as a finite linear
combination of homogeneous module generators. -/
private theorem awayPowMk_finset_sum
    {d a : ℕ} (f : 𝒜 d) {κ : Type*} (s : Finset κ) (m : κ → M) :
    awayPowMk 𝒜 f a (s.sum m) = s.sum fun k ↦ awayPowMk 𝒜 f a (m k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty sum localizes to zero.
      simp [awayPowMk]
  | @insert i s hi ih =>
      -- Fixed-denominator fractions add by combining the numerators.
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih, awayPowMk]
      rw [awayPowMk, LocalizedModule.mk_add_mk]
      -- The fixed denominator can be cancelled again after one common-denominator addition step.
      apply LocalizedModule.mk_eq.mpr
      refine ⟨1, ?_⟩
      simp [mul_smul, smul_add]

omit [GradedAlgebra 𝒜] in
/-- Helper for Lemma 10.57.9: multiplying a homogeneous module element by a degree-zero scalar
keeps it in the same graded piece. -/
private theorem smul_mem_same_degree_of_zero
    {n : ℕ} (r : 𝒜 0) {m : M} (hm : m ∈ ℳ n) :
    (r : S) • m ∈ ℳ n := by
  -- Degree-zero scalars do not shift the grading index.
  simpa [Nat.zero_add] using
    (SetLike.GradedSMul.smul_mem r.2 hm : (r : S) • m ∈ ℳ (0 + n))

/-- Helper for Lemma 10.57.9: multiplying a fixed-denominator homogeneous fraction by a scalar
from the degree-zero part just multiplies its numerator inside the same homogeneous localization
piece. -/
private theorem awayDegreeZeroPart_algebraMap_smul_mk
    {d a : ℕ} (f : 𝒜 d) (r : 𝒜 0) {m : M} (hm : m ∈ ℳ (a * d)) :
    (algebraMap (𝒜 0) (Away 𝒜 (f : S)) r) •
        (⟨awayPowMk 𝒜 f a m, awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f hm⟩ :
          awayDegreeZeroPart 𝒜 ℳ f) =
      ⟨awayPowMk 𝒜 f a ((r : S) • m),
        awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f
          (smul_mem_same_degree_of_zero (𝒜 := 𝒜) (ℳ := ℳ) r hm)⟩ := by
  -- Compare the two subtype elements by their images in the ordinary localized module.
  apply Subtype.ext
  change (algebraMap (Away 𝒜 (f : S)) (Localization.Away (f : S))
      (algebraMap (𝒜 0) (Away 𝒜 (f : S)) r)) • awayPowMk 𝒜 f a m =
    awayPowMk 𝒜 f a ((r : S) • m)
  rw [HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.algebraMap_eq]
  change Localization.mk (r : S) ⟨1, by exact ⟨0, by simp⟩⟩ •
      LocalizedModule.mk m ⟨(f : S) ^ a, by exact ⟨a, rfl⟩⟩ =
    LocalizedModule.mk ((r : S) • m) ⟨(f : S) ^ a, by exact ⟨a, rfl⟩⟩
  rw [LocalizedModule.mk_smul_mk]
  congr 2
  ext
  simp

/-- Helper for Lemma 10.57.9: when `f` has degree `0`, the general degree-zero localization
scalar `r / f^a` acts on the basic fraction `m / 1` by multiplying the numerator by `r` and
shifting the denominator exponent by `a`. -/
private theorem awayDegreeZeroPart_away_mk_smul_mk_degree_zero
    {a : ℕ} (f : 𝒜 0) (r : 𝒜 0) {m : M} (hm : m ∈ ℳ 0) :
    (Away.mk 𝒜 f.2 a (r : S) r.2) •
        (⟨awayPowMk 𝒜 f 0 m, awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f hm⟩ :
          awayDegreeZeroPart 𝒜 ℳ f) =
      ⟨awayPowMk 𝒜 f a ((r : S) • m),
        awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f
          (smul_mem_same_degree_of_zero (𝒜 := 𝒜) (ℳ := ℳ) r hm)⟩ := by
  let powa : Submonoid.powers (f : S) := ⟨(f : S) ^ a, ⟨a, rfl⟩⟩
  let pow0 : Submonoid.powers (f : S) := ⟨(f : S) ^ 0, ⟨0, rfl⟩⟩
  apply Subtype.ext
  change (algebraMap (Away 𝒜 (f : S)) (Localization.Away (f : S))
      (Away.mk 𝒜 f.2 a (r : S) r.2)) •
      LocalizedModule.mk m pow0 =
    LocalizedModule.mk ((r : S) • m) powa
  rw [HomogeneousLocalization.algebraMap_apply, Away.val_mk, LocalizedModule.mk_smul_mk]
  simpa [powa, pow0]

omit [GradedAlgebra 𝒜] in
/-- Helper for Lemma 10.57.9: a degree-zero scalar preserves each homogeneous component of a
graded module element. This is the component-level transport bridge needed in both the positive
and zero branches of the source proof. -/
private theorem component_smul_by_degree_zero
    [DirectSum.Decomposition ℳ] {r : S} (hr : r ∈ 𝒜 0) (n : ℕ) (m : M) :
    ((DirectSum.decompose ℳ ((r : S) • m) n : ℳ n) : M) =
      (r : S) • ((DirectSum.decompose ℳ m n : ℳ n) : M) := by
  classical
  let s := (DirectSum.decompose ℳ m).support
  let g : ℕ → M := fun i ↦ ((DirectSum.decompose ℳ m i : ℳ i) : M)
  have hdecomp :
      DirectSum.decompose ℳ ((r : S) • m) =
        ∑ i ∈ s, DirectSum.decompose ℳ ((r : S) • g i) := by
    -- Expand `m` into its homogeneous support and decompose the scalar multiple termwise.
    rw [show m = ∑ i ∈ s, g i by
      simp [s, g, DirectSum.sum_support_decompose]]
    rw [Finset.smul_sum, DirectSum.decompose_sum]
  have hcoord :
      ((DirectSum.decompose ℳ ((r : S) • m) n : ℳ n) : M) =
        ∑ i ∈ s, ((DirectSum.decompose ℳ ((r : S) • g i) n : ℳ n) : M) := by
    simpa [DirectSum.sum_apply] using
      congrArg (fun z : ⨁ i, ℳ i ↦ (z n : M)) hdecomp
  have hterm :
      ∀ i ∈ s,
        ((DirectSum.decompose ℳ ((r : S) • g i) n : ℳ n) : M) =
          if h : i = n then (r : S) • ((DirectSum.decompose ℳ m n : ℳ n) : M) else 0 := by
    intro i hi
    by_cases h : i = n
    · subst i
      have hmem : (r : S) • g n ∈ ℳ n := by
        simpa [g] using
          (SetLike.GradedSMul.smul_mem hr (DirectSum.decompose ℳ m n).2 :
            (r : S) • ((DirectSum.decompose ℳ m n : ℳ n) : M) ∈ ℳ (0 + n))
      simpa [g] using (DirectSum.decompose_of_mem_same ℳ hmem)
    · have hmem : (r : S) • g i ∈ ℳ i := by
        simpa [g] using
          (SetLike.GradedSMul.smul_mem hr (DirectSum.decompose ℳ m i).2 :
            (r : S) • ((DirectSum.decompose ℳ m i : ℳ i) : M) ∈ ℳ (0 + i))
      simpa [g, h] using (DirectSum.decompose_of_mem_ne ℳ hmem h)
  rw [Finset.sum_congr rfl hterm] at hcoord
  by_cases hn : n ∈ s
  · rw [Finset.sum_eq_single_of_mem n hn] at hcoord
    · simpa using hcoord
    · intro i hi hin
      simp [hin]
  · have hzero : ((DirectSum.decompose ℳ m n : ℳ n) : M) = 0 := by
      have hzero' : (DirectSum.decompose ℳ m n : ℳ n) = 0 := by
        by_contra hzero'
        exact hn (by simpa [s, DFinsupp.mem_support_iff, hzero'])
      exact congrArg (fun z : ℳ n ↦ (z : M)) hzero'
    rw [Finset.sum_eq_zero] at hcoord
    · simpa [hzero] using hcoord
    · intro i hi
      have hi_ne : i ≠ n := by
        intro hin
        exact hn (hin ▸ hi)
      simp [hi_ne]

omit [GradedAlgebra 𝒜] in
/-- Helper for Lemma 10.57.9: on a homogeneous module element of degree `n`, multiplication by a
degree-zero scalar leaves the `n`-component unchanged except for the scalar itself. -/
private theorem component_smul_homogeneous_by_degree_zero
    [DirectSum.Decomposition ℳ] {r : S} (hr : r ∈ 𝒜 0) {n : ℕ} {m : M} (hm : m ∈ ℳ n) :
    ((DirectSum.decompose ℳ ((r : S) • m) n : ℳ n) : M) = (r : S) • m := by
  -- First move the scalar through the component map, then identify the homogeneous component.
  rw [component_smul_by_degree_zero (𝒜 := 𝒜) (ℳ := ℳ) hr n m]
  simp [DirectSum.decompose_of_mem_same ℳ hm]

omit [GradedAlgebra 𝒜] in
/-- Helper for Lemma 10.57.9: if a homogeneous module element has degree `j ≠ n`, then a
degree-zero scalar still contributes nothing to the `n`-component. -/
private theorem component_smul_homogeneous_by_degree_zero_eq_zero
    [DirectSum.Decomposition ℳ] {r : S} (hr : r ∈ 𝒜 0)
    {j n : ℕ} {m : M} (hm : m ∈ ℳ j) (hjn : j ≠ n) :
    ((DirectSum.decompose ℳ ((r : S) • m) n : ℳ n) : M) = 0 := by
  -- Route correction: the source proof needs the degree component after scalar multiplication,
  -- so reduce it to the component of `m` before multiplying.
  rw [component_smul_by_degree_zero (𝒜 := 𝒜) (ℳ := ℳ) hr n m]
  simp [DirectSum.decompose_of_mem_ne ℳ hm hjn]

omit [GradedAlgebra 𝒜] in
/-- Helper for Lemma 10.57.9: a homogeneous scalar of degree `i` acting on a homogeneous module
generator of degree `j` contributes exactly to degree `i + j`. -/
private theorem component_of_homogeneous_scalar_smul_same
    [DirectSum.Decomposition ℳ] {i j : ℕ} {c : S} (hc : c ∈ 𝒜 i) {m : M} (hm : m ∈ ℳ j) :
    ((DirectSum.decompose ℳ (c • m) (i + j) : ℳ (i + j)) : M) = c • m := by
  simpa using
    (DirectSum.decompose_of_mem_same ℳ
      (SetLike.GradedSMul.smul_mem hc hm : c • m ∈ ℳ (i + j)))

omit [GradedAlgebra 𝒜] in
/-- Helper for Lemma 10.57.9: an off-degree component of a homogeneous scalar acting on a
homogeneous module generator vanishes. -/
private theorem component_of_homogeneous_scalar_smul_ne
    [DirectSum.Decomposition ℳ] {i j n : ℕ} {c : S} (hc : c ∈ 𝒜 i) {m : M} (hm : m ∈ ℳ j)
    (hijn : i + j ≠ n) :
    ((DirectSum.decompose ℳ (c • m) n : ℳ n) : M) = 0 := by
  simpa using
    (DirectSum.decompose_of_mem_ne ℳ
      (SetLike.GradedSMul.smul_mem hc hm : c • m ∈ ℳ (i + j)) hijn)

/-- Helper for Lemma 10.57.9: a homogeneous scalar of degree `i` lies in the span of the weighted
monomials in the chosen positive-degree homogeneous generators whose total degree is `i`. -/
private theorem homogeneous_scalar_mem_span_weighted_monomials_nat
    {ι : Type*} [Fintype ι]
    (v : ι → S) (δ : ι → ℕ) (hδ : ∀ i, 0 < δ i)
    (hv : ∀ i, v i ∈ 𝒜 (δ i))
    (hgen : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤)
    {i : ℕ} {c : S} (hc : c ∈ 𝒜 i) :
    c ∈ Submodule.span (𝒜 0)
      (Set.range fun e : {e : ι → Fin (i + 1) // ∑ k, (e k : ℕ) * δ k = i} ↦
        ∏ k, v k ^ (e.1 k : ℕ)) := by
  classical
  let W : Set S :=
    Set.range fun e : {e : ι → Fin (i + 1) // ∑ k, (e k : ℕ) * δ k = i} ↦
      ∏ k, v k ^ (e.1 k : ℕ)
  have hc_span : c ∈ Submodule.span (𝒜 0) (Submonoid.closure (Set.range v)) := by
    -- Rewrite the algebra-generation hypothesis into the span form used by span induction.
    have hc_adjoin : c ∈ Algebra.adjoin (𝒜 0) (Set.range v) := by
      rw [hgen]
      trivial
    change c ∈ (Algebra.adjoin (𝒜 0) (Set.range v)).toSubmodule at hc_adjoin
    simpa [Algebra.adjoin_eq_span] using hc_adjoin
  have hcomponent : (DirectSum.decompose 𝒜 c i : S) ∈ Submodule.span (𝒜 0) W := by
    clear hc
    induction hc_span using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨a, rfl⟩ := Submonoid.exists_of_mem_closure_range v y hy
        by_cases ha : ∑ k, a k * δ k = i
        · have hprod_mem : (∏ k, v k ^ a k : S) ∈ 𝒜 i := by
            have hmem :
                (∏ k, v k ^ a k : S) ∈ 𝒜 (∑ k, a k * δ k) := by
              simpa [nsmul_eq_mul] using
                (SetLike.prod_pow_mem_graded 𝒜 δ v a (fun k _ ↦ hv k))
            simpa [ha] using hmem
          have hbound : ∀ k, a k ≤ i := by
            intro k
            have hk_le_sum : a k * δ k ≤ ∑ j, a j * δ j := by
              simpa using
                (Finset.single_le_sum
                  (fun j _ ↦ Nat.zero_le (a j * δ j)) (Finset.mem_univ k) :
                  a k * δ k ≤ ∑ j, a j * δ j)
            have hone : 1 ≤ δ k := Nat.succ_le_of_lt (hδ k)
            calc
              a k = a k * 1 := by simp
              _ ≤ a k * δ k := by exact Nat.mul_le_mul_left _ hone
              _ ≤ i := by simpa [ha] using hk_le_sum
          let e : ι → Fin (i + 1) := fun k ↦ ⟨a k, Nat.lt_succ_of_le (hbound k)⟩
          have hw : (∏ k, v k ^ a k : S) ∈ Submodule.span (𝒜 0) W := by
            -- Package the exponent vector into the finite admissible family indexed by `Fin`.
            refine Submodule.subset_span ?_
            refine ⟨⟨e, ?_⟩, ?_⟩
            · simpa [e] using ha
            · simp [e]
          simpa [W, DirectSum.decompose_of_mem_same 𝒜 hprod_mem] using hw
        · have hprod_mem :
            (∏ k, v k ^ a k : S) ∈ 𝒜 (∑ k, a k * δ k) := by
            simpa [nsmul_eq_mul] using
              (SetLike.prod_pow_mem_graded 𝒜 δ v a (fun k _ ↦ hv k))
          simpa [W, DirectSum.decompose_of_mem_ne 𝒜 hprod_mem ha] using
            (show (0 : S) ∈ Submodule.span (𝒜 0) W from
              (Submodule.span (𝒜 0) W).zero_mem)
    | zero =>
        simpa [W] using
          (show (0 : S) ∈ Submodule.span (𝒜 0) W from
            (Submodule.span (𝒜 0) W).zero_mem)
    | add y z hy hz hy' hz' =>
        -- The fixed-degree component map is additive.
        simpa [W, DirectSum.decompose_add, AddMemClass.coe_add] using
          (Submodule.span (𝒜 0) W).add_mem hy' hz'
    | smul r y hy hy' =>
        -- Multiplication by a degree-zero scalar keeps the component inside the target span.
        have hdecomp :
            (DirectSum.decompose 𝒜 ((algebraMap (𝒜 0) S r : S) * y) i : S) =
              r • (DirectSum.decompose 𝒜 y i : S) := by
          calc
            (DirectSum.decompose 𝒜 ((algebraMap (𝒜 0) S r : S) * y) i : S) =
                (algebraMap (𝒜 0) S r : S) * (DirectSum.decompose 𝒜 y i : S) := by
                  simpa using
                    (DirectSum.coe_decompose_mul_of_left_mem_zero (𝒜 := 𝒜)
                      (a := (algebraMap (𝒜 0) S r : S)) (b := y) (j := i) (SetLike.coe_mem r))
            _ = r • (DirectSum.decompose 𝒜 y i : S) := by
                  rw [Algebra.smul_def]
        have hdecomp' :
            (DirectSum.decompose 𝒜 (r • y) i : S) =
              r • (DirectSum.decompose 𝒜 y i : S) := by
          simpa [Algebra.smul_def] using hdecomp
        exact hdecomp' ▸ Submodule.smul_mem (Submodule.span (𝒜 0) W) r hy'
  -- The input scalar is already homogeneous of degree `i`, so its `i`-component is itself.
  simpa [W, DirectSum.decompose_of_mem_same 𝒜 hc] using hcomponent

/-- Helper for Lemma 10.57.9: the degree-`a * d` component of `c • m` is controlled by the
degree-`i` scalar component when `i + j = a * d`. -/
private theorem decompose_smul_homogeneous_generator_eq_nat
    [DirectSum.Decomposition ℳ] {a i j : ℕ} {c : S} {m : M}
    (hm : m ∈ ℳ j) (hij : i + j = a) :
    ((DirectSum.decompose ℳ (c • m) a : ℳ a) : M) =
      (((DirectSum.decompose 𝒜 c i : 𝒜 i) : S) • m) := by
  classical
  have happly :
      (((∑ k ∈ (DirectSum.decompose 𝒜 c).support,
          DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 c) k : 𝒜 k) : S) • m)) a : ℳ a) : M) =
        ∑ k ∈ (DirectSum.decompose 𝒜 c).support,
          ((DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 c) k : 𝒜 k) : S) • m) a : ℳ a) : M) := by
    simpa using
      congrArg (fun z : ℳ a ↦ (z : M))
        (DFinsupp.finset_sum_apply
          ((DirectSum.decompose 𝒜 c).support)
          (fun k ↦ DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 c) k : 𝒜 k) : S) • m))
          a)
  have hsum :
      ∑ k ∈ (DirectSum.decompose 𝒜 c).support,
          ((DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 c) k : 𝒜 k) : S) • m) a : ℳ a) : M) =
        ((DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 c) i : 𝒜 i) : S) • m) a : ℳ a) : M) := by
    by_cases hi : i ∈ (DirectSum.decompose 𝒜 c).support
    · rw [Finset.sum_eq_single_of_mem i hi]
      · intro k hk hki
        have hk_ne : k + j ≠ a := by
          intro hk_eq
          exact hki (Nat.add_right_cancel (hk_eq.trans hij.symm))
        simpa using
          (component_of_homogeneous_scalar_smul_ne
            (𝒜 := 𝒜) (ℳ := ℳ)
            (hc := (DirectSum.decompose 𝒜 c k).2) (hm := hm) hk_ne)
    · have hsum_zero :
          ∑ k ∈ (DirectSum.decompose 𝒜 c).support,
              ((DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 c) k : 𝒜 k) : S) • m) a : ℳ a) : M) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro k hk
        have hk_ne : k + j ≠ a := by
          intro hk_eq
          exact hi (Nat.add_right_cancel (hk_eq.trans hij.symm) ▸ hk)
        simpa using
          (component_of_homogeneous_scalar_smul_ne
            (𝒜 := 𝒜) (ℳ := ℳ)
            (hc := (DirectSum.decompose 𝒜 c k).2) (hm := hm) hk_ne)
      have hizero : DirectSum.decompose 𝒜 c i = 0 := by
        simpa [DFinsupp.mem_support_iff] using hi
      rw [hsum_zero]
      simpa [hizero]
  have hdecomp :
      ((DirectSum.decompose ℳ (c • m) a : ℳ a) : M) =
        ∑ k ∈ (DirectSum.decompose 𝒜 c).support,
          ((DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 c) k : 𝒜 k) : S) • m) a : ℳ a) : M) := by
    have h :=
      congrArg (fun z : M ↦ ((DirectSum.decompose ℳ z a : ℳ a) : M))
        (DirectSum.sum_support_decompose 𝒜 c |> congrArg (fun z : S => z • m))
    simpa [Finset.sum_smul, DirectSum.decompose_sum, happly] using h.symm
  calc
    ((DirectSum.decompose ℳ (c • m) a : ℳ a) : M) =
        ∑ k ∈ (DirectSum.decompose 𝒜 c).support,
          ((DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 c) k : 𝒜 k) : S) • m) a : ℳ a) : M) := hdecomp
    _ = ((DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 c) i : 𝒜 i) : S) • m) a : ℳ a) : M) := hsum
    _ = (((DirectSum.decompose 𝒜 c i : 𝒜 i) : S) • m) := by
          rw [← hij]
          exact component_of_homogeneous_scalar_smul_same
            (𝒜 := 𝒜) (ℳ := ℳ)
            (hc := (DirectSum.decompose 𝒜 c i).2) (hm := hm)

/-- Helper for Lemma 10.57.9: if the target degree `a` is strictly smaller than the degree `j` of
a homogeneous module generator, then the degree-`a` component of `c • m` vanishes. -/
private theorem decompose_smul_homogeneous_generator_eq_zero_of_lt
    (𝒜 : ℕ → Submodule R S) (ℳ : ℕ → Submodule R M)
    [GradedAlgebra 𝒜] [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]
    {a j : ℕ} {c : S} {m : M}
    (hm : m ∈ ℳ j) (haj : a < j) :
    ((DirectSum.decompose ℳ (c • m) a : ℳ a) : M) = 0 := by
  classical
  have happly :
      (((∑ k ∈ (DirectSum.decompose 𝒜 c).support,
          DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 c) k : 𝒜 k) : S) • m)) a : ℳ a) : M) =
        ∑ k ∈ (DirectSum.decompose 𝒜 c).support,
          ((DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 c) k : 𝒜 k) : S) • m) a : ℳ a) : M) := by
    simpa using
      congrArg (fun z : ℳ a ↦ (z : M))
        (DFinsupp.finset_sum_apply
          ((DirectSum.decompose 𝒜 c).support)
          (fun k ↦ DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 c) k : 𝒜 k) : S) • m))
          a)
  have hsum_zero :
      ∑ k ∈ (DirectSum.decompose 𝒜 c).support,
          ((DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 c) k : 𝒜 k) : S) • m) a : ℳ a) : M) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro k hk
    have hk_ne : k + j ≠ a := by
      intro hk_eq
      have hle : j ≤ a := by
        simpa [hk_eq] using (Nat.le_add_left j k)
      exact (Nat.not_le_of_gt haj) hle
    simpa using
      (component_of_homogeneous_scalar_smul_ne
        (𝒜 := 𝒜) (ℳ := ℳ)
        (hc := (DirectSum.decompose 𝒜 c k).2) (hm := hm) hk_ne)
  have hdecomp :
      ((DirectSum.decompose ℳ (c • m) a : ℳ a) : M) =
        ∑ k ∈ (DirectSum.decompose 𝒜 c).support,
          ((DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 c) k : 𝒜 k) : S) • m) a : ℳ a) : M) := by
    have h :=
      congrArg (fun z : M ↦ ((DirectSum.decompose ℳ z a : ℳ a) : M))
        (DirectSum.sum_support_decompose 𝒜 c |> congrArg (fun z : S ↦ z • m))
    simpa [Finset.sum_smul, DirectSum.decompose_sum, happly] using h.symm
  calc
    ((DirectSum.decompose ℳ (c • m) a : ℳ a) : M) =
        ∑ k ∈ (DirectSum.decompose 𝒜 c).support,
          ((DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 c) k : 𝒜 k) : S) • m) a : ℳ a) : M) := hdecomp
    _ = 0 := hsum_zero

/-- Helper for Lemma 10.57.9: a homogeneous scalar in the weighted-monomial span sends a fixed
homogeneous module generator to the span of the bounded remainder localization family. -/
private theorem awayPowMk_smul_homogeneous_generator_mem_span_bounded_family_of_scalar_span
    {κ ι : Type*} [Fintype ι] [DecidableEq ι] {d a : ℕ}
    (f : 𝒜 d) (hd : 0 < d)
    (x : κ → M) (η : κ → ℕ) (hx : ∀ j, x j ∈ ℳ (η j))
    (v : ι → S) (δ : ι → ℕ) (hv : ∀ i, v i ∈ 𝒜 (δ i))
    (j : κ) {i : ℕ} (hij : i + η j = a * d)
    {c : S} (hc : c ∈ 𝒜 i)
    (hc_span : c ∈ Submodule.span (𝒜 0)
      (Set.range fun e : {e : ι → Fin (i + 1) // ∑ k, (e k : ℕ) * δ k = i} ↦
        ∏ k, v k ^ (e.1 k : ℕ))) :
    (⟨awayPowMk 𝒜 f a (c • x j),
      awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f
        (by
          simpa [hij] using
            (SetLike.GradedSMul.smul_mem hc (hx j) :
              c • x j ∈ ℳ (i + η j)))⟩ :
      awayDegreeZeroPart 𝒜 ℳ f) ∈
      Submodule.span (Away 𝒜 (f : S))
        (Set.range (boundedRemainderFamily (𝒜 := 𝒜) (ℳ := ℳ) f v δ x η hv hx)) := by
  classical
  let E : Type _ :=
    {e : ι → Fin (i + 1) // ∑ k, (e k : ℕ) * δ k = i}
  let moduleMon : E → awayDegreeZeroPart 𝒜 ℳ f := fun e ↦
    ⟨awayPowMk 𝒜 f a (((∏ k, v k ^ (e.1 k : ℕ) : S) • x j)),
      awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f
        (by
          have hmem :=
            weighted_monomial_smul_mem_degree_piece_nat
              (𝒜 := 𝒜) (ℳ := ℳ) v δ x η hv hx (fun k ↦ (e.1 k : ℕ)) j
          simpa [e.2, hij] using hmem)⟩
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun (𝒜 0)).mp hc_span
  have hsum_eq :
      (∑ e, (algebraMap (𝒜 0) (Away 𝒜 (f : S)) (r e)) • moduleMon e : awayDegreeZeroPart 𝒜 ℳ f) =
        ⟨awayPowMk 𝒜 f a (c • x j),
          awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f
            (by
              simpa [hij] using
                (SetLike.GradedSMul.smul_mem hc (hx j) :
                  c • x j ∈ ℳ (i + η j)))⟩ := by
    have hsum1 :
        (∑ e, (algebraMap (𝒜 0) (Away 𝒜 (f : S)) (r e)) • moduleMon e :
            awayDegreeZeroPart 𝒜 ℳ f) =
          ∑ e,
            ⟨awayPowMk 𝒜 f a ((r e : S) • (((∏ k, v k ^ (e.1 k : ℕ) : S)) • x j)),
              awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f
                (by
                  have hmon :=
                    weighted_monomial_smul_mem_degree_piece_nat
                      (𝒜 := 𝒜) (ℳ := ℳ) v δ x η hv hx (fun k ↦ (e.1 k : ℕ)) j
                  have hsmul :
                      (r e : S) • (((∏ k, v k ^ (e.1 k : ℕ) : S)) • x j) ∈
                        ℳ (0 + (a * d)) := by
                    simpa [e.2, hij] using
                      (SetLike.GradedSMul.smul_mem (SetLike.coe_mem (r e)) hmon :
                        (r e : S) • (((∏ k, v k ^ (e.1 k : ℕ) : S)) • x j) ∈
                          ℳ (0 + ((∑ k, (e.1 k : ℕ) * δ k) + η j)))
                  simpa using hsmul)⟩ := by
      refine Finset.sum_congr rfl ?_
      intro e he
      exact awayDegreeZeroPart_algebraMap_smul_mk
        (𝒜 := 𝒜) (ℳ := ℳ) (f := f) (r := r e)
        (hm := by
          have hmon :=
            weighted_monomial_smul_mem_degree_piece_nat
              (𝒜 := 𝒜) (ℳ := ℳ) v δ x η hv hx (fun k ↦ (e.1 k : ℕ)) j
          simpa [e.2, hij] using hmon)
    rw [hsum1]
    apply Subtype.ext
    calc
      ((((∑ e,
          ⟨awayPowMk 𝒜 f a ((r e : S) • (((∏ k, v k ^ (e.1 k : ℕ) : S)) • x j)),
            awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f
              (by
                have hmon :=
                  weighted_monomial_smul_mem_degree_piece_nat
                    (𝒜 := 𝒜) (ℳ := ℳ) v δ x η hv hx (fun k ↦ (e.1 k : ℕ)) j
                have hsmul :
                    (r e : S) • (((∏ k, v k ^ (e.1 k : ℕ) : S)) • x j) ∈
                      ℳ (0 + (a * d)) := by
                  simpa [e.2, hij] using
                    (SetLike.GradedSMul.smul_mem (SetLike.coe_mem (r e)) hmon :
                      (r e : S) • (((∏ k, v k ^ (e.1 k : ℕ) : S)) • x j) ∈
                        ℳ (0 + ((∑ k, (e.1 k : ℕ) * δ k) + η j)))
                simpa using hsmul)⟩ :
            awayDegreeZeroPart 𝒜 ℳ f) : awayDegreeZeroPart 𝒜 ℳ f) :
          LocalizedModule.Away (f : S) M)) =
          ∑ e, awayPowMk 𝒜 f a ((r e : S) • (((∏ k, v k ^ (e.1 k : ℕ) : S)) • x j)) := by
            simp
      _ = awayPowMk 𝒜 f a (c • x j) := by
            rw [← awayPowMk_finset_sum (𝒜 := 𝒜) (f := f) (a := a)
              (s := Finset.univ)
              (m := fun e ↦ (r e : S) • (((∏ k, v k ^ (e.1 k : ℕ) : S)) • x j))]
            have hsmul_eq :
                (∑ e, (r e : S) • (((∏ k, v k ^ (e.1 k : ℕ) : S)) • x j)) = c • x j := by
              calc
                (∑ e, (r e : S) • (((∏ k, v k ^ (e.1 k : ℕ) : S)) • x j)) =
                    (∑ e, (r e : S) * (∏ k, v k ^ (e.1 k : ℕ) : S)) • x j := by
                      rw [Finset.sum_smul]
                      refine Finset.sum_congr rfl ?_
                      intro e he
                      rw [smul_smul]
                _ = c • x j := by
                      simpa [Algebra.smul_def] using congrArg (fun z : S ↦ z • x j) hr
            simpa [hsmul_eq]
  have hsum_mem :
      (∑ e, (algebraMap (𝒜 0) (Away 𝒜 (f : S)) (r e)) • moduleMon e :
          awayDegreeZeroPart 𝒜 ℳ f) ∈
        Submodule.span (Away 𝒜 (f : S))
          (Set.range (boundedRemainderFamily (𝒜 := 𝒜) (ℳ := ℳ) f v δ x η hv hx)) := by
    refine Submodule.sum_mem _ ?_
    intro e he
    exact Submodule.smul_mem _ _
      (awayPowMk_monomial_mem_span_bounded_family
        (𝒜 := 𝒜) (ℳ := ℳ) (f := f) (hd := hd)
        v δ hv x η hx (fun k ↦ (e.1 k : ℕ)) j
        (by simpa [e.2] using hij))
  exact hsum_eq.symm ▸ hsum_mem

/-- Helper for Lemma 10.57.9: after decomposing a scalar into homogeneous pieces, the degree
`a * d` numerator component acting on one homogeneous module generator already lies in the span
of the bounded remainder localization family. -/
private theorem degree_ad_component_smul_generator_mem_span_bounded_family
    {κ ι : Type*} [Fintype ι] [DecidableEq ι] {d a : ℕ}
    [DirectSum.Decomposition ℳ] (f : 𝒜 d) (hd : 0 < d)
    (x : κ → M) (η : κ → ℕ) (hx : ∀ j, x j ∈ ℳ (η j))
    (v : ι → S) (δ : ι → ℕ) (hδ : ∀ i, 0 < δ i) (hv : ∀ i, v i ∈ 𝒜 (δ i))
    (hgen : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤)
    (j : κ) (c : S) :
    (⟨awayPowMk 𝒜 f a (((DirectSum.decompose ℳ (c • x j) (a * d) : ℳ (a * d)) : M)),
      awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f
        (DirectSum.decompose ℳ (c • x j) (a * d)).2⟩ :
      awayDegreeZeroPart 𝒜 ℳ f) ∈
      Submodule.span (Away 𝒜 (f : S))
        (Set.range (boundedRemainderFamily (𝒜 := 𝒜) (ℳ := ℳ) f v δ x η hv hx)) := by
  classical
  by_cases hη : η j ≤ a * d
  · let i : ℕ := a * d - η j
    have hij : i + η j = a * d := by
      dsimp [i]
      exact Nat.sub_add_cancel hη
    have hc : (((DirectSum.decompose 𝒜 c i : 𝒜 i) : S)) ∈ 𝒜 i :=
      (DirectSum.decompose 𝒜 c i).2
    have hc_span :
        (((DirectSum.decompose 𝒜 c i : 𝒜 i) : S)) ∈
          Submodule.span (𝒜 0)
            (Set.range fun e : {e : ι → Fin (i + 1) // ∑ k, (e k : ℕ) * δ k = i} ↦
              ∏ k, v k ^ (e.1 k : ℕ)) :=
      homogeneous_scalar_mem_span_weighted_monomials_nat
        (𝒜 := 𝒜) v δ hδ hv hgen hc
    have hterm_eq :
        (⟨awayPowMk 𝒜 f a (((DirectSum.decompose ℳ (c • x j) (a * d) : ℳ (a * d)) : M)),
          awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f
            (DirectSum.decompose ℳ (c • x j) (a * d)).2⟩ :
        awayDegreeZeroPart 𝒜 ℳ f) =
        ⟨awayPowMk 𝒜 f a ((((DirectSum.decompose 𝒜 c i : 𝒜 i) : S) • x j)),
          awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f
            (by
              simpa [hij] using
                (SetLike.GradedSMul.smul_mem hc (hx j) :
                  (((DirectSum.decompose 𝒜 c i : 𝒜 i) : S) • x j) ∈
                    ℳ (i + η j)))⟩ := by
      apply Subtype.ext
      simpa using
        congrArg (awayPowMk 𝒜 f a)
          (decompose_smul_homogeneous_generator_eq_nat
            (𝒜 := 𝒜) (ℳ := ℳ) (a := a * d) (i := i) (j := η j) (hm := hx j) hij)
    exact hterm_eq.symm ▸
      (awayPowMk_smul_homogeneous_generator_mem_span_bounded_family_of_scalar_span
        (𝒜 := 𝒜) (ℳ := ℳ) (f := f) hd x η hx v δ hv j hij hc hc_span)
  · have haj : a * d < η j := lt_of_not_ge hη
    have hzero :
        ((DirectSum.decompose ℳ (c • x j) (a * d) : ℳ (a * d)) : M) = 0 :=
        decompose_smul_homogeneous_generator_eq_zero_of_lt
          𝒜 ℳ (a := a * d) (j := η j) (hm := hx j) haj
    have hterm_zero :
        (⟨awayPowMk 𝒜 f a (((DirectSum.decompose ℳ (c • x j) (a * d) : ℳ (a * d)) : M)),
          awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f
            (DirectSum.decompose ℳ (c • x j) (a * d)).2⟩ :
          awayDegreeZeroPart 𝒜 ℳ f) = 0 := by
      apply Subtype.ext
      simp [hzero, awayPowMk]
    exact hterm_zero.symm ▸ Submodule.zero_mem _

/-- Over the degree-zero base ring `S₀ = 𝒜 0`, finite type of the graded ring `S` and finite
generation of the graded module `M` imply finite generation of the degree-zero homogeneous
localization `M_(f)` over `S_(f)`. -/
-- Proof sketch: choose homogeneous generators of `M` and homogeneous algebra generators of `S`,
-- and then use the same bounded-exponent reduction as in part (1) to obtain finitely many
-- generators for the degree-zero localized module.
private theorem awayDegreeZeroPart_finite_of_finiteType_degreeZeroBase
    [Algebra.FiniteType (𝒜 0) S] [Module.Finite S M] {d : ℕ}
    [DirectSum.Decomposition ℳ] (f : 𝒜 d) :
    Module.Finite (Away 𝒜 (f : S)) (awayDegreeZeroPart 𝒜 ℳ f) := by
  classical
  obtain ⟨n, x, η, hx, hspan⟩ :=
    exists_finite_homogeneous_module_generators_nat (S := S) (M := M) (ℳ := ℳ)
  by_cases hd0 : d = 0
  · subst hd0
    let w0 : {j : Fin n // η j = 0} → awayDegreeZeroPart 𝒜 ℳ f := fun j ↦
      match j with
      | ⟨j, hj⟩ =>
          ⟨awayPowMk 𝒜 f 0 (x j),
            awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f
              (by simpa [hj] using hx j)⟩
    have htop_le :
        (⊤ : Submodule (Away 𝒜 (f : S)) (awayDegreeZeroPart 𝒜 ℳ f)) ≤
          Submodule.span (Away 𝒜 (f : S)) (Set.range w0) := by
      intro z hz
      obtain ⟨a, m, hmz⟩ :=
        (mem_awayDegreeZeroPart_iff (𝒜 := 𝒜) (ℳ := ℳ) f).mp z.2
      have hm_span : ((m : ℳ 0) : M) ∈ Submodule.span S (Set.range x) := by
        rw [hspan]
        trivial
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp hm_span
      let term : Fin n → awayDegreeZeroPart 𝒜 ℳ f := fun j ↦
        ⟨awayPowMk 𝒜 f a (((DirectSum.decompose ℳ (c j • x j) 0 : ℳ 0) : M)),
          awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f
            (DirectSum.decompose ℳ (c j • x j) 0).2⟩
      have hcomp_sum :
          (∑ j, ((DirectSum.decompose ℳ (c j • x j) 0 : ℳ 0) : M)) = (m : M) := by
        have hproj :=
          congrArg (fun y : M ↦ ((DirectSum.decompose ℳ y 0 : ℳ 0) : M)) hc
        simpa [DirectSum.decompose_sum, DirectSum.decompose_of_mem_same ℳ m.2] using hproj
      have hterm_eq :
          (∑ j, term j : awayDegreeZeroPart 𝒜 ℳ f) = z := by
        apply Subtype.ext
        calc
          ((((∑ j, term j : awayDegreeZeroPart 𝒜 ℳ f) : awayDegreeZeroPart 𝒜 ℳ f) :
              LocalizedModule.Away (f : S) M)) =
              ∑ j, awayPowMk 𝒜 f a (((DirectSum.decompose ℳ (c j • x j) 0 : ℳ 0) : M)) := by
                simp [term]
          _ = z.1 := by
                rw [← awayPowMk_finset_sum (𝒜 := 𝒜) (f := f) (a := a)
                  (s := Finset.univ)
                  (m := fun j ↦ ((DirectSum.decompose ℳ (c j • x j) 0 : ℳ 0) : M))]
                simpa [hmz, hcomp_sum]
      have hsum_mem :
          (∑ j, term j : awayDegreeZeroPart 𝒜 ℳ f) ∈
            Submodule.span (Away 𝒜 (f : S)) (Set.range w0) := by
        refine Submodule.sum_mem _ ?_
        intro j hj
        by_cases hη0 : η j = 0
        · have hx0 : x j ∈ ℳ 0 := by
            simpa [hη0] using hx j
          have hcomp :
              ((DirectSum.decompose ℳ (c j • x j) 0 : ℳ 0) : M) =
                (((DirectSum.decompose 𝒜 (c j) 0 : 𝒜 0) : S) • x j) := by
            simpa using
              (decompose_smul_homogeneous_generator_eq_nat
                (𝒜 := 𝒜) (ℳ := ℳ) (a := 0) (i := 0) (j := 0) (hm := hx0)
                (by simp))
          have hscalar_mem :
              (((DirectSum.decompose 𝒜 (c j) 0 : 𝒜 0) : S) • x j) ∈ ℳ 0 := by
            simpa using
              (smul_mem_same_degree_of_zero (𝒜 := 𝒜) (ℳ := ℳ)
                (DirectSum.decompose 𝒜 (c j) 0) hx0)
          have hterm_eq_scalar :
              term j =
                ⟨awayPowMk 𝒜 f a ((((DirectSum.decompose 𝒜 (c j) 0 : 𝒜 0) : S) • x j)),
                  awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f
                    (by simpa using hscalar_mem)⟩ := by
            apply Subtype.ext
            simp [term, hcomp]
          have hterm_eq' :
              term j =
                (Away.mk 𝒜 f.2 a (((DirectSum.decompose 𝒜 (c j) 0 : 𝒜 0) : S))
                    (DirectSum.decompose 𝒜 (c j) 0).2) •
                  w0 ⟨j, hη0⟩ := by
            calc
              term j =
                  ⟨awayPowMk 𝒜 f a ((((DirectSum.decompose 𝒜 (c j) 0 : 𝒜 0) : S) • x j)),
                    awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f
                      (by simpa using hscalar_mem)⟩ := hterm_eq_scalar
              _ =
                  (Away.mk 𝒜 f.2 a (((DirectSum.decompose 𝒜 (c j) 0 : 𝒜 0) : S))
                      (DirectSum.decompose 𝒜 (c j) 0).2) •
                    w0 ⟨j, hη0⟩ := by
                      symm
                      exact awayDegreeZeroPart_away_mk_smul_mk_degree_zero
                        (𝒜 := 𝒜) (ℳ := ℳ) f (DirectSum.decompose 𝒜 (c j) 0) hx0
          rw [hterm_eq']
          exact Submodule.smul_mem _ _
            (Submodule.subset_span ⟨⟨j, hη0⟩, rfl⟩)
        · have hzero :
              ((DirectSum.decompose ℳ (c j • x j) 0 : ℳ 0) : M) = 0 :=
            decompose_smul_homogeneous_generator_eq_zero_of_lt 𝒜 ℳ
              (a := 0) (j := η j) (hm := hx j) (Nat.pos_of_ne_zero hη0)
          have hterm_zero : term j = 0 := by
            apply Subtype.ext
            simp [term, hzero, awayPowMk]
          rw [hterm_zero]
          exact Submodule.zero_mem _
      exact hterm_eq ▸ hsum_mem
    have hspan_top :
        Submodule.span (Away 𝒜 (f : S)) (Set.range w0) = ⊤ := by
      rw [eq_top_iff]
      exact htop_le
    have hspan_finite :
        Module.Finite (Away 𝒜 (f : S))
          (Submodule.span (Away 𝒜 (f : S)) (Set.range w0)) :=
      Module.Finite.span_of_finite (Away 𝒜 (f : S)) (Set.finite_range w0)
    have htop_finite :
        Module.Finite (Away 𝒜 (f : S))
          (⊤ : Submodule (Away 𝒜 (f : S)) (awayDegreeZeroPart 𝒜 ℳ f)) := by
      exact hspan_top ▸ hspan_finite
    letI :
        Module.Finite (Away 𝒜 (f : S))
          (⊤ : Submodule (Away 𝒜 (f : S)) (awayDegreeZeroPart 𝒜 ℳ f)) := htop_finite
    -- Route correction: transfer finite generation from the top submodule via its subtype map,
    -- avoiding the expensive elaboration of `Submodule.topEquiv`.
    refine Module.Finite.of_surjective
      ((⊤ : Submodule (Away 𝒜 (f : S)) (awayDegreeZeroPart 𝒜 ℳ f)).subtype) ?_
    intro z
    exact ⟨⟨z, by trivial⟩, rfl⟩
  · obtain ⟨n', v, δ, hposmem, hgen⟩ :=
      exists_finite_positive_homogeneous_ring_generators_nat (𝒜 := 𝒜)
    have hd : 0 < d := Nat.pos_of_ne_zero hd0
    have hδ : ∀ i, 0 < δ i := fun i ↦ (hposmem i).1
    have hv : ∀ i, v i ∈ 𝒜 (δ i) := fun i ↦ (hposmem i).2
    let w :
        boundedRemainderIndex (ι := Fin n') (κ := Fin n) (d := d) (δ := δ) η →
          awayDegreeZeroPart 𝒜 ℳ f :=
      boundedRemainderFamily (𝒜 := 𝒜) (ℳ := ℳ) f v δ x η hv hx
    have htop_le :
        (⊤ : Submodule (Away 𝒜 (f : S)) (awayDegreeZeroPart 𝒜 ℳ f)) ≤
          Submodule.span (Away 𝒜 (f : S)) (Set.range w) := by
      intro z hz
      obtain ⟨a, m, hmz⟩ :=
        (mem_awayDegreeZeroPart_iff (𝒜 := 𝒜) (ℳ := ℳ) f).mp z.2
      have hm_span : ((m : ℳ (a * d)) : M) ∈ Submodule.span S (Set.range x) := by
        rw [hspan]
        trivial
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp hm_span
      let term : Fin n → awayDegreeZeroPart 𝒜 ℳ f := fun j ↦
        ⟨awayPowMk 𝒜 f a (((DirectSum.decompose ℳ (c j • x j) (a * d) : ℳ (a * d)) : M)),
          awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f
            (DirectSum.decompose ℳ (c j • x j) (a * d)).2⟩
      have hcomp_sum :
          (∑ j, ((DirectSum.decompose ℳ (c j • x j) (a * d) : ℳ (a * d)) : M)) = (m : M) := by
        have hproj :=
          congrArg (fun y : M ↦ ((DirectSum.decompose ℳ y (a * d) : ℳ (a * d)) : M)) hc
        simpa [DirectSum.decompose_sum, DirectSum.decompose_of_mem_same ℳ m.2] using hproj
      have hterm_eq :
          (∑ j, term j : awayDegreeZeroPart 𝒜 ℳ f) = z := by
        apply Subtype.ext
        calc
          ((((∑ j, term j : awayDegreeZeroPart 𝒜 ℳ f) : awayDegreeZeroPart 𝒜 ℳ f) :
              LocalizedModule.Away (f : S) M)) =
              ∑ j, awayPowMk 𝒜 f a (((DirectSum.decompose ℳ (c j • x j) (a * d) : ℳ (a * d)) : M)) := by
                simp [term]
          _ = z.1 := by
                rw [← awayPowMk_finset_sum (𝒜 := 𝒜) (f := f) (a := a)
                  (s := Finset.univ)
                  (m := fun j ↦ ((DirectSum.decompose ℳ (c j • x j) (a * d) : ℳ (a * d)) : M))]
                simpa [hmz, hcomp_sum]
      have hsum_mem :
          (∑ j, term j : awayDegreeZeroPart 𝒜 ℳ f) ∈
            Submodule.span (Away 𝒜 (f : S)) (Set.range w) := by
        refine Submodule.sum_mem _ ?_
        intro j hj
        change
          (⟨awayPowMk 𝒜 f a (((DirectSum.decompose ℳ (c j • x j) (a * d) : ℳ (a * d)) : M)),
            awayDegreeZeroPart_mk_mem (𝒜 := 𝒜) (ℳ := ℳ) f
              (DirectSum.decompose ℳ (c j • x j) (a * d)).2⟩ :
            awayDegreeZeroPart 𝒜 ℳ f) ∈
            Submodule.span (Away 𝒜 (f : S))
              (Set.range (boundedRemainderFamily (𝒜 := 𝒜) (ℳ := ℳ) f v δ x η hv hx))
        exact
          degree_ad_component_smul_generator_mem_span_bounded_family
            (𝒜 := 𝒜) (ℳ := ℳ) (f := f) hd x η hx v δ hδ hv hgen j (c j)
      exact hterm_eq ▸ hsum_mem
    have hspan_top :
        Submodule.span (Away 𝒜 (f : S)) (Set.range w) = ⊤ := by
      rw [eq_top_iff]
      exact htop_le
    have hspan_finite :
        Module.Finite (Away 𝒜 (f : S))
          (Submodule.span (Away 𝒜 (f : S)) (Set.range w)) :=
      Module.Finite.span_of_finite (Away 𝒜 (f : S)) (Set.finite_range w)
    have htop_finite :
        Module.Finite (Away 𝒜 (f : S))
          (⊤ : Submodule (Away 𝒜 (f : S)) (awayDegreeZeroPart 𝒜 ℳ f)) := by
      exact hspan_top ▸ hspan_finite
    let _ :
        Module.Finite (Away 𝒜 (f : S))
          (⊤ : Submodule (Away 𝒜 (f : S)) (awayDegreeZeroPart 𝒜 ℳ f)) := htop_finite
    -- Route correction: transfer finite generation from the top submodule via its subtype map,
    -- avoiding the expensive elaboration of `Submodule.topEquiv`.
    refine Module.Finite.of_surjective
      ((⊤ : Submodule (Away 𝒜 (f : S)) (awayDegreeZeroPart 𝒜 ℳ f)).subtype) ?_
    intro z
    exact ⟨⟨z, by trivial⟩, rfl⟩

/-- Lemma 10.57.9 (2): if `S` is of finite type over `R` and `M = ⨁ M_n` is a finite graded
`S`-module, then `M_(f)` is a finite `S_(f)`-module. For the degree-zero homogeneous localization,
the positivity assumption on the degree of `f` is redundant. -/
theorem awayDegreeZeroPart_finite [Algebra.FiniteType R S] [Module.Finite S M] {d : ℕ}
    [DirectSum.Decomposition ℳ] (f : 𝒜 d) :
    Module.Finite (Away 𝒜 (f : S)) (awayDegreeZeroPart 𝒜 ℳ f) := by
  let _ : Algebra.FiniteType (𝒜 0) S :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (𝒜 0) S
  exact awayDegreeZeroPart_finite_of_finiteType_degreeZeroBase 𝒜 ℳ f

end
