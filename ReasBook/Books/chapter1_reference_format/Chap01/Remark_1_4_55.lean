import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ENNReal Topology
open Filter Finset

universe u

namespace lp

variable (K : Type u) [NontriviallyNormedField K]

local notation "ℓ1" => lp (fun _ : ℕ ↦ K) (1 : ℝ≥0∞)

/-- Helper for Remark 1.4.55: the zero vector in `ℓ¹(ℕ, K)` is finitely supported. -/
theorem zero_mem_finitelySupported_carrier :
    Memℓp (fun n ↦ ((0 : ℓ1) n)) 0 := by
  -- The support of the zero sequence is empty.
  simpa using (zero_memℓp : Memℓp (fun n ↦ ((0 : ℓ1) n)) 0)

/-- Helper for Remark 1.4.55: finite support is stable under addition in `ℓ¹(ℕ, K)`. -/
theorem add_mem_finitelySupported_carrier {f g : ℓ1}
    (hf : Memℓp (fun n ↦ (f : ℓ1) n) 0)
    (hg : Memℓp (fun n ↦ (g : ℓ1) n) 0) :
    Memℓp (fun n ↦ ((f + g : ℓ1) n)) 0 := by
  -- The support of a sum sits inside the union of the two finite supports.
  simpa using hf.add hg

/-- Helper for Remark 1.4.55: finite support is stable under scalar multiplication. -/
theorem smul_mem_finitelySupported_carrier (c : K) {f : ℓ1}
    (hf : Memℓp (fun n ↦ (f : ℓ1) n) 0) :
    Memℓp (fun n ↦ ((c • f : ℓ1) n)) 0 := by
  -- Scaling does not create new nonzero coordinates.
  simpa using hf.const_smul c

/-- The subspace of `ℓ¹(ℕ, K)` consisting of finitely supported sequences. -/
def finitelySupported : Submodule K ℓ1 where
  carrier := {f | Memℓp (fun n ↦ (f : ℓ1) n) 0}
  zero_mem' := zero_mem_finitelySupported_carrier K
  add_mem' := add_mem_finitelySupported_carrier K
  smul_mem' := smul_mem_finitelySupported_carrier K

theorem single_mem_finitelySupported (n : ℕ) (x : K) :
    lp.single 1 n x ∈ finitelySupported K := by
  change Memℓp (fun m ↦ (lp.single 1 n x : ℓ1) m) 0
  apply memℓp_zero
  refine Set.Finite.subset (Set.finite_singleton n) ?_
  intro m hm
  by_contra hmn
  simp [lp.single_apply, Pi.single_eq_of_ne hmn] at hm

theorem linearIndependent_single_finitelySupported :
    LinearIndependent K
      (fun n : ℕ ↦
        (⟨lp.single 1 n (1 : K),
          single_mem_finitelySupported K n 1⟩ : finitelySupported K)) := by
  apply LinearIndependent.of_comp (finitelySupported K).subtype
  let Φ : ℓ1 →ₗ[K] (ℕ → K) :=
    { toFun := fun f ↦ (f : ℕ → K)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  apply LinearIndependent.of_comp Φ
  simpa [Φ, lp.single_apply] using
    (Pi.linearIndependent_single_one ℕ K)

theorem not_finiteDimensional_finitelySupported :
    ¬ FiniteDimensional K (finitelySupported K) := by
  intro h
  let v : ℕ → finitelySupported K := fun n ↦
    ⟨lp.single 1 n (1 : K),
      single_mem_finitelySupported K n 1⟩
  let _ : Module.Finite K (finitelySupported K) := h
  exact Module.Finite.not_linearIndependent_of_infinite v
    (by simpa [v] using linearIndependent_single_finitelySupported K)

/-- Helper for Remark 1.4.55: the geometric sequence with ratio of norm less than `1`
belongs to `ℓ¹(ℕ, K)`. -/
theorem memℓp_geometric (r : K) (hr : ‖r‖ < 1) :
    Memℓp (fun n ↦ r ^ n) 1 := by
  -- The absolute values form a summable geometric series.
  refine memℓp_gen ?_
  simpa using summable_norm_geometric_of_norm_lt_one hr

/-- The geometric `ℓ¹` vector associated to a ratio of norm less than `1`. -/
def geometric (r : K) (hr : ‖r‖ < 1) : ℓ1 :=
  ⟨fun n ↦ r ^ n, memℓp_geometric K r hr⟩

/-- Helper for Remark 1.4.55: the exponent `p = 1` satisfies the lower bound required by
`lp.hasSum_single`. -/
theorem one_le_one_ennreal : (1 : ℝ≥0∞) ≤ (1 : ℝ≥0∞) := by
  -- This is the trivial order relation needed to invoke the `lp` singleton summation theorem.
  simp

/-- Helper for Remark 1.4.55: package the previous inequality as a `Fact` instance. -/
instance fact_one_le_one_ennreal : Fact (1 ≤ (1 : ℝ≥0∞)) where
  out := one_le_one_ennreal

theorem geometric_not_mem_finitelySupported {r : K} (hr0 : 0 < ‖r‖) (hr : ‖r‖ < 1) :
    geometric K r hr ∉ finitelySupported K := by
  intro h
  have hr_ne : r ≠ 0 := norm_pos_iff.mp hr0
  have hfinite : Set.Finite {n : ℕ | (geometric K r hr : ℓ1) n ≠ 0} := Memℓp.finite_dsupport h
  have hfinite' : Set.Finite {n : ℕ | r ^ n ≠ 0} := by
    simpa [geometric] using hfinite
  have huniv : {n : ℕ | r ^ n ≠ 0} = Set.univ := by
    ext n
    simp [hr_ne]
  have : Set.Finite (Set.univ : Set ℕ) := huniv ▸ hfinite'
  let _ : Finite ℕ := Finite.of_finite_univ this
  exact not_finite ℕ

theorem geometric_mem_closure_finitelySupported {r : K} (hr : ‖r‖ < 1) :
    geometric K r hr ∈ closure (finitelySupported K : Set ℓ1) := by
  -- The canonical singleton expansion of an `ℓ¹` vector converges back to the vector itself.
  have hsum :
      HasSum
        (fun n : ℕ ↦ lp.single 1 n ((geometric K r hr) n))
        (geometric K r hr) := by
    simpa using lp.hasSum_single ENNReal.one_ne_top (geometric K r hr)
  -- Every finite partial sum is finitely supported because it is a finite sum of singleton vectors.
  refine mem_closure_of_tendsto hsum.tendsto_sum_nat ?_
  refine Eventually.of_forall fun n ↦ ?_
  exact Submodule.sum_mem (finitelySupported K) fun i hi ↦
    single_mem_finitelySupported K i ((geometric K r hr) i)

theorem not_complete_finitelySupported :
    ¬ CompleteSpace (finitelySupported K) := by
  intro h
  have hclosed : IsClosed (finitelySupported K : Set ℓ1) :=
    (completeSpace_coe_iff_isComplete.1 h).isClosed
  obtain ⟨r, hr0, hr1⟩ := NormedField.exists_norm_lt_one K
  have hmem : geometric K r hr1 ∈ (finitelySupported K : Set ℓ1) := by
    rw [← hclosed.closure_eq]
    exact geometric_mem_closure_finitelySupported K hr1
  exact geometric_not_mem_finitelySupported K hr0 hr1 hmem

/-- Remark 1.4.55: Proposition 1.4.54 does not extend to infinite-dimensional `K`-vector spaces;
the finitely supported subspace of `ℓ¹(ℕ, K)` is infinite-dimensional and not complete. -/
theorem finitelySupported_not_finiteDimensional_and_not_complete :
    ¬ FiniteDimensional K (finitelySupported K) ∧ ¬ CompleteSpace (finitelySupported K) := by
  exact ⟨not_finiteDimensional_finitelySupported K, not_complete_finitelySupported K⟩

end lp
