import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DirectSum
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

/-- Over the degree-zero base ring `S₀ = 𝒜 0`, finite type of the graded ring `S` and finite
generation of the graded module `M` imply finite generation of the degree-zero homogeneous
localization `M_(f)` over `S_(f)`. -/
-- Proof sketch: choose homogeneous generators of `M` and homogeneous algebra generators of `S`,
-- and then use the same bounded-exponent reduction as in part (1) to obtain finitely many
-- generators for the degree-zero localized module.
private theorem awayDegreeZeroPart_finite_of_finiteType_degreeZeroBase
    [Algebra.FiniteType (𝒜 0) S] [Module.Finite S M] {d : ℕ}
    [DirectSum.Decomposition ℳ] (f : 𝒜 d) :
    Module.Finite (Away 𝒜 (f : S)) (awayDegreeZeroPart 𝒜 ℳ f) := sorry

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
