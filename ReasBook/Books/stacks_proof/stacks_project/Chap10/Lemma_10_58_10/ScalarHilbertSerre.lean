import StacksProject_2024.Chap10.Example_10_58_9

open Filter
open HomogeneousIdeal
open scoped BigOperators DirectSum

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.decomposition
attribute [local instance] MvPolynomial.HomogeneousSubmodule.gradedMonoid

noncomputable section

universe u v

section

/-- Helper for Chap10 Lemma 10 58 10: the standard grading shifts integer degrees by addition. -/
local instance scalarNatVAddInt : AddAction ℕ ℤ where
  vadd n z := (n : ℤ) + z
  zero_vadd := by
    intro z
    change ((0 : ℕ) : ℤ) + z = z
    simp
  add_vadd := by
    intro m n z
    change (((m + n : ℕ) : ℤ) + z) = ((m : ℤ) + ((n : ℤ) + z))
    simp [Nat.cast_add, add_assoc]

variable {k : Type u} [Field k] {d : ℕ}
variable {M : Type v} [AddCommGroup M] [Module k M]
variable [Module (MvPolynomial (Fin d) k) M]

local notation "S" => MvPolynomial (Fin d) k
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin d) k

/-- Helper for Chap10 Lemma 10 58 10: a finite standard-graded module with scalar degree pieces
admits finitely many homogeneous module generators. -/
lemma scalarFiniteHomogeneousModuleGenerators
    (ℳ : ℤ → Submodule k M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    [Module.Finite S M] :
    ∃ (κ : Type v) (_ : Fintype κ) (m : κ → M) (η : κ → ℤ),
      (∀ j, m j ∈ ℳ (η j)) ∧ Submodule.span S (Set.range m) = ⊤ := by
  classical
  let hfg : (⊤ : Submodule S M).FG := Module.Finite.fg_top (R := S) (M := M)
  obtain ⟨G, _, g, hg⟩ := (Submodule.fg_iff_exists_finite_generating_family (A := S)
    (M := M) (N := (⊤ : Submodule S M))).mp hfg
  let κ : Type v := Σ j : G, { n // n ∈ (DirectSum.decompose ℳ (g j)).support }
  let m : κ → M := fun j ↦ (DirectSum.decompose ℳ (g j.1) j.2.1 : ℳ j.2.1)
  let η : κ → ℤ := fun j ↦ j.2.1
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype κ := inferInstance
  -- Split a finite `S`-generating family into all nonzero scalar homogeneous components.
  refine ⟨κ, inferInstance, m, η, ?_, ?_⟩
  · intro j
    exact (DirectSum.decompose ℳ (g j.1) j.2.1).2
  · rw [← top_le_iff, ← hg, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [← DirectSum.sum_support_decompose ℳ (g j)]
    refine Submodule.sum_mem _ ?_
    intro n hn
    exact Submodule.subset_span ⟨⟨j, ⟨n, hn⟩⟩, rfl⟩

/-- Helper for Chap10 Lemma 10 58 10: a homogeneous scalar term contributes its full scalar
action to the matching scalar graded component. -/
lemma scalar_directsum_component_of_homogeneous_scalar_smul_same
    (ℳ : ℤ → Submodule k M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {η n : ℤ} {e : ℕ} {a_e : S} (ha_e : a_e ∈ 𝒜 e)
    {m_eta : M} (hm_eta : m_eta ∈ ℳ η)
    (hnd : (e : ℤ) + η = n) :
    ((DirectSum.decompose ℳ (a_e • m_eta) n : ℳ n) : M) = a_e • m_eta := by
  -- The graded action puts this term in exactly one degree, so the matching projection is itself.
  have hsmul : a_e • m_eta ∈ ℳ ((e : ℤ) + η) :=
    SetLike.GradedSMul.smul_mem ha_e hm_eta
  subst n
  simpa using (DirectSum.decompose_of_mem_same ℳ hsmul)

/-- Helper for Chap10 Lemma 10 58 10: a homogeneous scalar term contributes nothing to any
off-degree scalar graded component. -/
lemma scalar_directsum_component_of_homogeneous_scalar_smul_ne
    (ℳ : ℤ → Submodule k M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {η n : ℤ} {e : ℕ} {a_e : S} (ha_e : a_e ∈ 𝒜 e)
    {m_eta : M} (hm_eta : m_eta ∈ ℳ η)
    (hnd : (e : ℤ) + η ≠ n) :
    ((DirectSum.decompose ℳ (a_e • m_eta) n : ℳ n) : M) = 0 := by
  -- The same one-degree support statement makes every different projection vanish.
  have hsmul : a_e • m_eta ∈ ℳ ((e : ℤ) + η) :=
    SetLike.GradedSMul.smul_mem ha_e hm_eta
  simpa using (DirectSum.decompose_of_mem_ne ℳ hsmul hnd)

/-- Helper for Chap10 Lemma 10 58 10: for a scalar homogeneous module generator, only the scalar
component in the matching degree contributes to a fixed scalar graded projection. -/
lemma scalar_decompose_smul_homogeneous_generator_eq
    (ℳ : ℤ → Submodule k M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {η n : ℤ} {e : ℕ} {a : S} {m : M}
    (hm : m ∈ ℳ η) (hnd : (e : ℤ) + η = n) :
    ((DirectSum.decompose ℳ (a • m) n : ℳ n) : M) =
      (((DirectSum.decompose 𝒜 a e : 𝒜 e) : S) • m) := by
  classical
  let g : ℕ → M := fun i ↦
    ((DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 a) i : 𝒜 i) : S) • m) n :
      ℳ n) : M)
  have happly :
      ((((∑ i ∈ (DirectSum.decompose 𝒜 a).support,
          DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 a) i : 𝒜 i) : S) • m)) n :
          ℳ n) : M)) =
        ∑ i ∈ (DirectSum.decompose 𝒜 a).support, g i := by
    -- Evaluate the degree-`n` coordinate after pushing decomposition through the finite sum.
    simpa [g] using congrArg (fun z : ℳ n ↦ (z : M))
      (DFinsupp.finset_sum_apply
        ((DirectSum.decompose 𝒜 a).support)
        (fun i ↦ DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 a) i : 𝒜 i) : S) • m))
        n)
  have hsum :
      ∑ i ∈ (DirectSum.decompose 𝒜 a).support, g i = g e := by
    by_cases he : e ∈ (DirectSum.decompose 𝒜 a).support
    · rw [Finset.sum_eq_single_of_mem e he]
      intro i hi hie
      have hi_ne : (i : ℤ) + η ≠ n := by
        intro hi_eq
        have hcast : (i : ℤ) = e := by
          linarith [hi_eq, hnd]
        exact hie (Int.ofNat.inj hcast)
      simpa [g] using
        (scalar_directsum_component_of_homogeneous_scalar_smul_ne
          (ℳ := ℳ) (ha_e := (DirectSum.decompose 𝒜 a i).2)
          (hm_eta := hm) hi_ne)
    · have hsum_zero :
          ∑ i ∈ (DirectSum.decompose 𝒜 a).support, g i = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        have hi_ne : (i : ℤ) + η ≠ n := by
          intro hi_eq
          have hcast : (i : ℤ) = e := by
            linarith [hi_eq, hnd]
          exact he (Int.ofNat.inj hcast ▸ hi)
        simpa [g] using
          (scalar_directsum_component_of_homogeneous_scalar_smul_ne
            (ℳ := ℳ) (ha_e := (DirectSum.decompose 𝒜 a i).2)
            (hm_eta := hm) hi_ne)
      have hezero : DirectSum.decompose 𝒜 a e = 0 := by
        simpa [DFinsupp.mem_support_iff] using he
      have hg_zero : g e = 0 := by
        simp [g, hezero]
      rw [hsum_zero, hg_zero]
  have hdecomp :
      ((DirectSum.decompose ℳ (a • m) n : ℳ n) : M) =
        ∑ i ∈ (DirectSum.decompose 𝒜 a).support, g i := by
    -- Expand the scalar into homogeneous components before acting on the fixed homogeneous vector.
    have h :=
      congrArg (fun z : S ↦ ((DirectSum.decompose ℳ (z • m) n : ℳ n) : M))
        (DirectSum.sum_support_decompose 𝒜 a)
    simpa [g, Finset.sum_smul, DirectSum.decompose_sum, happly] using h.symm
  calc
    ((DirectSum.decompose ℳ (a • m) n : ℳ n) : M) =
        ∑ i ∈ (DirectSum.decompose 𝒜 a).support, g i := hdecomp
    _ = g e := hsum
    _ = (((DirectSum.decompose 𝒜 a e : 𝒜 e) : S) • m) := by
          change
            ((DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 a) e : 𝒜 e) : S) • m) n :
                ℳ n) : M) =
              (((DirectSum.decompose 𝒜 a e : 𝒜 e) : S) • m)
          exact
            scalar_directsum_component_of_homogeneous_scalar_smul_same
              (ℳ := ℳ) (ha_e := (DirectSum.decompose 𝒜 a e).2)
              (hm_eta := hm) hnd

/-- Helper for Chap10 Lemma 10 58 10: if the irrelevant ideal vanishes, then scalar graded
pieces vanish in all sufficiently large degrees. -/
lemma scalarGradedPiece_eq_bot_eventually_of_irrelevant_eq_bot
    (ℳ : ℤ → Submodule k M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    [Module.Finite S M]
    (hbot : 𝒜₊.toIdeal = ⊥) :
    ∃ N : ℤ, ∀ n, N ≤ n → ℳ n = ⊥ := by
  classical
  obtain ⟨κ, _, m, η, hm, hspan⟩ :=
    scalarFiniteHomogeneousModuleGenerators (k := k) (d := d) (ℳ := ℳ)
  let N : ℤ := ((∑ j : κ, Int.natAbs (η j) : ℕ) : ℤ) + 1
  refine ⟨N, ?_⟩
  intro n hn
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hx_span : x ∈ Submodule.span S (Set.range m) := by
    rw [hspan]
    trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp hx_span
  have hx_decompose :
      (∑ j, (DirectSum.decompose ℳ (c j • m j) n : ℳ n)) = ⟨x, hx⟩ := by
    -- Project the chosen finite `S`-linear generator expression to degree `n`.
    calc
      (∑ j, (DirectSum.decompose ℳ (c j • m j) n : ℳ n)) =
          DirectSum.decompose ℳ (∑ j, c j • m j) n := by
            simp [DirectSum.decompose_sum]
      _ = DirectSum.decompose ℳ x n := by
            simpa [hc]
      _ = ⟨x, hx⟩ := by
            ext
            simpa [DirectSum.decompose_of_mem_same ℳ hx]
  have hterm_zero : ∀ j : κ, (DirectSum.decompose ℳ (c j • m j) n : ℳ n) = 0 := by
    intro j
    have hsum_nat : Int.natAbs (η j) ≤ ∑ k : κ, Int.natAbs (η k) := by
      exact
        (Finset.single_le_sum
          (fun k _ ↦ Nat.zero_le (Int.natAbs (η k))) (Finset.mem_univ j) :
          Int.natAbs (η j) ≤ ∑ k : κ, Int.natAbs (η k))
    have hη_le : η j ≤ ((∑ k : κ, Int.natAbs (η k) : ℕ) : ℤ) := by
      have hnatabs_le : (Int.natAbs (η j) : ℤ) ≤
          ((∑ k : κ, Int.natAbs (η k) : ℕ) : ℤ) := by
        exact_mod_cast hsum_nat
      exact le_trans (Int.le_natAbs (a := η j)) hnatabs_le
    have hη_lt : η j < n := by
      dsimp [N] at hn
      linarith
    let e : ℕ := Int.toNat (n - η j)
    have he_nonneg : 0 ≤ n - η j := by
      linarith
    have hne : (e : ℤ) + η j = n := by
      dsimp [e]
      rw [Int.toNat_of_nonneg he_nonneg]
      linarith
    have he_pos : 0 < e := by
      by_contra he_not_pos
      have he_zero : e = 0 := Nat.eq_zero_of_not_pos he_not_pos
      have : n = η j := by
        calc
          n = ((e : ℤ) + η j) := by
                symm
                exact hne
          _ = η j := by simp [he_zero]
      linarith
    have hscalar_zero : ((DirectSum.decompose 𝒜 (c j) e : 𝒜 e) : S) = 0 := by
      -- Positive-degree scalar components vanish when the irrelevant ideal is zero.
      exact
        eq_zero_of_mem_positive_degree_of_irrelevant_eq_bot
          𝒜 he_pos (DirectSum.decompose 𝒜 (c j) e).2 hbot
    apply Subtype.ext
    simpa [hscalar_zero] using
      (scalar_decompose_smul_homogeneous_generator_eq
        (ℳ := ℳ) (hm := hm j) (hnd := hne) (a := c j) (m := m j))
  have hx_subtype_zero : (⟨x, hx⟩ : ℳ n) = 0 := by
    -- Since every projected generator contribution is zero, the original degree-`n` vector is zero.
    calc
      (⟨x, hx⟩ : ℳ n) = ∑ j, (DirectSum.decompose ℳ (c j • m j) n : ℳ n) := by
        symm
        exact hx_decompose
      _ = 0 := by
        refine Finset.sum_eq_zero ?_
        intro j hj
        exact hterm_zero j
  simpa using congrArg (fun y : ℳ n ↦ (y : M)) hx_subtype_zero

/-- Helper for Chap10 Lemma 10 58 10: the irrelevant-ideal-zero base case gives an eventually
zero scalar Hilbert function. -/
lemma scalarGradedPiece_finrank_isNumericalPolynomial_of_irrelevant_eq_bot
    (ℳ : ℤ → Submodule k M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    [Module.Finite S M]
    (hbot : 𝒜₊.toIdeal = ⊥) :
    IsNumericalPolynomial (fun n ↦ (Module.finrank k (ℳ n) : ℤ)) := by
  obtain ⟨N, hN⟩ :=
    scalarGradedPiece_eq_bot_eventually_of_irrelevant_eq_bot
      (k := k) (d := d) (ℳ := ℳ) hbot
  -- Convert eventual vanishing of pieces into the constant-zero binomial expansion.
  exact isNumericalPolynomial_of_eventuallyEq_zero <|
    Filter.eventually_atTop.mpr ⟨N, by
      intro n hn
      change (Module.finrank k (ℳ n) : ℤ) = 0
      rw [hN n hn]
      simp⟩

variable [IsScalarTower k (MvPolynomial (Fin d) k) M]

/-- Helper for Chap10 Lemma 10 58 10: multiplication by a degree-one scalar as a `k`-linear map
between consecutive scalar graded pieces. -/
def scalarDegreeOneMulMap
    (ℳ : ℤ → Submodule k M)
    [SetLike.GradedSMul 𝒜 ℳ]
    {a : S} (ha : a ∈ 𝒜 1) (n : ℤ) :
    ℳ (n - 1) →ₗ[k] ℳ n where
  toFun x :=
    ⟨a • (x : M), by
      have hmem : a • (x : M) ∈ ℳ ((1 : ℕ) +ᵥ (n - 1)) :=
        SetLike.GradedSMul.smul_mem ha x.2
      have hindex : ((1 : ℕ) +ᵥ (n - 1) : ℤ) = n := by
        change ((1 : ℕ) : ℤ) + (n - 1) = n
        ring
      simpa [hindex] using hmem⟩
  map_add' := by
    intro x y
    ext
    simp [smul_add]
  map_smul' := by
    intro c x
    ext
    -- The scalar action is `k`-linear because the `S`-action extends the `k`-action.
    calc
      a • c • (x : M) = a • ((algebraMap k S c) • (x : M)) := by
        rw [algebraMap_smul S c (x : M)]
      _ = (a * algebraMap k S c) • (x : M) := by
        rw [smul_smul]
      _ = (algebraMap k S c * a) • (x : M) := by
        rw [mul_comm]
      _ = (algebraMap k S c) • (a • (x : M)) := by
        rw [smul_smul]
      _ = c • a • (x : M) := by
        rw [algebraMap_smul S c (a • (x : M))]

/-- Helper for Chap10 Lemma 10 58 10: rank-nullity for the degree-one multiplication map at the
scalar graded-piece surface. -/
lemma scalarDegreeOneMulMap_finrankExact
    (ℳ : ℤ → Submodule k M)
    [SetLike.GradedSMul 𝒜 ℳ]
    (hfinite : ∀ n, Module.Finite k (ℳ n))
    {a : S} (ha : a ∈ 𝒜 1) (n : ℤ) :
    Module.finrank k (LinearMap.range (scalarDegreeOneMulMap (ℳ := ℳ) ha n)) +
        Module.finrank k (LinearMap.ker (scalarDegreeOneMulMap (ℳ := ℳ) ha n)) =
      Module.finrank k (ℳ (n - 1)) := by
  let μ : ℳ (n - 1) →ₗ[k] ℳ n := scalarDegreeOneMulMap (ℳ := ℳ) ha n
  let _ : Module.Finite k (ℳ (n - 1)) := hfinite (n - 1)
  let _ : Module.Finite k (LinearMap.ker μ) := inferInstance
  -- Identify the quotient by the kernel with the range, then apply finite-dimensional rank-nullity.
  rw [← LinearEquiv.finrank_eq μ.quotKerEquivRange]
  exact (LinearMap.ker μ).finrank_quotient_add_finrank

end
