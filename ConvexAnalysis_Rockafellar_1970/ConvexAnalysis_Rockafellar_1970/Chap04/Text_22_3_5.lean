import ConvexAnalysis_Rockafellar_1970.Chap01.Corollary_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_22_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators RealInnerProductSpace Rockafellar
open LinearConstraintRelation

noncomputable section

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 22.3.5 is Rockafellar's mixed alternative in which a chosen subset of a
  finite family of linear constraints is imposed as equalities while the complementary indices
  remain weak inequalities.
- `core/canonical`: the owner layer is `LinearConstraintRelation.feasibleSet` together with
  `LinearConstraintRelation.eqOn`, and the mixed alternative is exposed at the pairing layer
  `a : I → Y` under `[HasLinearPairing E Y ℝ]`.
- `bridge/view`: the pairing-side nonemptiness reformulation of the owner feasible set and the
  linear-functional and inner-product specializations.

Domain-style sampling used here:
- the Chapter 1 owners `LinearConstraintRelation.eqOn` and `LinearConstraintRelation.feasibleSet`;
- the owner-side membership theorem `LinearConstraintRelation.mem_feasibleSet`;
- the Chapter 4 weak-alternative theorems
  `xor_exists_feasible_point_or_weak_pairing_inequality_farkas_certificate` and
  `xor_exists_feasible_point_or_weak_linear_inequality_farkas_certificate`;
- the Fréchet-Riesz bridge `InnerProductSpace.toDual`.

Primitive data vs derived API:
- primitive source data for the main theorem: a finite index type `I`, pairing-side coefficients
  `a : I → Y`, bounds `α : I → ℝ`, and the equality-index set `eqIndices : Set I`;
- owner object: the mixed feasible set `feasibleSet (eqOn eqIndices) a α`;
- derived API: the functional linear-map specialization and the textbook inner-product vector
  restatement.

Layer target: `core/canonical` for the pairing-owner theorem, with `bridge/view` companions for
the linear-functional and inner-product presentations.

Abstraction checks for this item:
- Codomain/owner layer: the source-facing nonemptiness bridge is stated directly on the pairing
  owner `feasibleSet (eqOn eqIndices) a α`, with pointwise pairing notation `⟪x, a i⟫ₚ`.
- Scalar layer: multiplier alternatives remain over `ℝ` in this file because they are reused from
  Theorem 22.1, whose upstream proof route is currently real-linear.
- Ambient structure: no inner-product assumptions appear on the primary mixed owner theorem; the
  inner-product formulation is retained only as a downstream bridge.
-/

section PairingOwner

variable {𝕜 : Type*} [LE 𝕜] [LT 𝕜]
variable {X Y : Type*} [HasPairing X Y 𝕜]
variable {I : Type*}

local notation "solutionSet[" eqIndices "; " a ", " α "]" =>
  (feasibleSet (eqOn eqIndices) a α : Set X)

/-- The owner mixed feasible set is nonempty exactly when the pairing-side mixed
equality/inequality system has a solution. -/
theorem mixed_linear_constraint_solution_set_nonempty_iff
    (a : I → Y) (α : I → 𝕜) (eqIndices : Set I) :
    (solutionSet[eqIndices; a, α]).Nonempty ↔
      ∃ x : X,
        (∀ i : I, i ∉ eqIndices → (⟪x, a i⟫ₚ ≤ α i)) ∧
          (∀ i : I, i ∈ eqIndices → (⟪x, a i⟫ₚ = α i)) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_, ?_⟩
    · intro i hi
      have hxi := (mem_feasibleSet _ _ _ _).1 hx i
      simpa [eqOn, hi] using hxi
    · intro i hi
      have hxi := (mem_feasibleSet _ _ _ _).1 hx i
      simpa [eqOn, hi] using hxi
  · rintro ⟨x, hxle, hxeq⟩
    refine ⟨x, (mem_feasibleSet _ _ _ _).2 ?_⟩
    intro i
    by_cases hi : i ∈ eqIndices
    · simpa [eqOn, hi] using hxeq i hi
    · simpa [eqOn, hi] using hxle i hi

end PairingOwner

section FunctionalOwner

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : Type*} [Fintype I]

local notation "solutionSet[" eqIndices "; " a ", " α "]" =>
  (feasibleSet (eqOn eqIndices) a α : Set E)

private def mixedLinearConstraintFarkasFunctional
    (a : I → E →ₗ[ℝ] ℝ) (eqIndices : Set I) : I ⊕ I → E →ₗ[ℝ] ℝ :=
  let _ : DecidablePred (· ∈ eqIndices) := Classical.decPred eqIndices
  Sum.elim a fun i ↦ if i ∈ eqIndices then -a i else 0

private def mixedLinearConstraintFarkasScalar
    (α : I → ℝ) (eqIndices : Set I) : I ⊕ I → ℝ :=
  let _ : DecidablePred (· ∈ eqIndices) := Classical.decPred eqIndices
  Sum.elim α fun i ↦ if i ∈ eqIndices then -α i else 0

private def mixedLinearConstraintWeakSolutionSet
    (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ) (eqIndices : Set I) : Set E :=
  linearInequalitySolutionSet
    (Set.range fun j : I ⊕ I ↦
      (mixedLinearConstraintFarkasFunctional a eqIndices j,
        mixedLinearConstraintFarkasScalar α eqIndices j))

omit [FiniteDimensional ℝ E] [Fintype I] in
private theorem weakSolutionSet_eq_mixed_linear_constraint_solutionSet
    (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ) (eqIndices : Set I) :
    mixedLinearConstraintWeakSolutionSet a α eqIndices = solutionSet[eqIndices; a, α] := by
  classical
  ext x
  rw [mixedLinearConstraintWeakSolutionSet, mem_linearInequalitySolutionSet_range_iff,
    mem_feasibleSet]
  constructor
  · intro hx i
    by_cases hi : i ∈ eqIndices
    · have hle : a i x ≤ α i := by
        simpa [mixedLinearConstraintFarkasFunctional, mixedLinearConstraintFarkasScalar] using
          hx (Sum.inl i)
      have hge : α i ≤ a i x := by
        have hneg :
            (mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inr i)) x ≤
              mixedLinearConstraintFarkasScalar α eqIndices (Sum.inr i) :=
          hx (Sum.inr i)
        simpa [mixedLinearConstraintFarkasFunctional, mixedLinearConstraintFarkasScalar, hi] using
          hneg
      have heq : a i x = α i := le_antisymm hle hge
      simpa [eqOn, hi] using heq
    · simpa [eqOn, hi, mixedLinearConstraintFarkasFunctional, mixedLinearConstraintFarkasScalar] using
        hx (Sum.inl i)
  · intro hx j
    cases j with
    | inl i =>
        by_cases hi : i ∈ eqIndices
        · have heq : a i x = α i := by
            simpa [eqOn, hi] using hx i
          simpa [mixedLinearConstraintFarkasFunctional, mixedLinearConstraintFarkasScalar, hi] using
            heq.le
        · simpa [eqOn, hi, mixedLinearConstraintFarkasFunctional, mixedLinearConstraintFarkasScalar] using
            hx i
    | inr i =>
        by_cases hi : i ∈ eqIndices
        · have heq : a i x = α i := by
            simpa [eqOn, hi] using hx i
          have hneg : ⟪x, (-a i : E →ₗ[ℝ] ℝ)⟫ₚ ≤ -α i := by
            change (-a i) x ≤ -α i
            simp [heq]
          simpa [mixedLinearConstraintFarkasFunctional, mixedLinearConstraintFarkasScalar, hi] using
            hneg
        · have hzero :
            (mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inr i)) x ≤
              mixedLinearConstraintFarkasScalar α eqIndices (Sum.inr i) := by
            simp [mixedLinearConstraintFarkasFunctional, mixedLinearConstraintFarkasScalar, hi]
          exact hzero

omit [FiniteDimensional ℝ E] in
private theorem exists_mixed_linear_constraint_farkas_certificate_iff
    (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ) (eqIndices : Set I) :
    (∃ u : I ⊕ I → ℝ,
      (∀ j : I ⊕ I, 0 ≤ u j) ∧
        (∑ j : I ⊕ I, u j • mixedLinearConstraintFarkasFunctional a eqIndices j = 0) ∧
          (∑ j : I ⊕ I, u j * mixedLinearConstraintFarkasScalar α eqIndices j) < 0) ↔
      ∃ w : I → ℝ,
        (∀ i : I, i ∉ eqIndices → 0 ≤ w i) ∧
          (∑ i : I, w i • a i = 0) ∧
            (∑ i : I, w i * α i) < 0 := by
  classical
  constructor
  · rintro ⟨u, hu_nonneg, hu_vec, hu_scalar⟩
    let w : I → ℝ := fun i ↦ if hi : i ∈ eqIndices then u (Sum.inl i) - u (Sum.inr i) else u (Sum.inl i)
    refine ⟨w, ?_, ?_, ?_⟩
    · intro i hi
      simpa [w, hi] using hu_nonneg (Sum.inl i)
    · have hu_vec' :
        ∑ i : I, u (Sum.inl i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inl i) +
            ∑ i : I, u (Sum.inr i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inr i) =
          0 := by
        simpa [Fintype.sum_sum_type] using hu_vec
      calc
        ∑ i : I, w i • a i
            = ∑ i : I,
                (u (Sum.inl i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inl i) +
                  u (Sum.inr i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inr i)) := by
                refine Finset.sum_congr rfl ?_
                intro i _
                by_cases hi : i ∈ eqIndices
                · calc
                    w i • a i = (u (Sum.inl i) - u (Sum.inr i)) • a i := by
                      simp [w, hi]
                    _ = u (Sum.inl i) • a i + u (Sum.inr i) • (-a i) := by
                          simp [sub_eq_add_neg, add_smul]
                    _ = u (Sum.inl i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inl i) +
                          u (Sum.inr i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inr i) := by
                          simp [mixedLinearConstraintFarkasFunctional, hi]
                · simp [w, mixedLinearConstraintFarkasFunctional, hi]
        _ = ∑ i : I, u (Sum.inl i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inl i) +
              ∑ i : I, u (Sum.inr i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inr i) := by
                rw [Finset.sum_add_distrib]
        _ = 0 := hu_vec'
    · have hu_scalar' :
        ∑ i : I, u (Sum.inl i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inl i) +
            ∑ i : I, u (Sum.inr i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inr i) <
          0 := by
        simpa [Fintype.sum_sum_type] using hu_scalar
      calc
        ∑ i : I, w i * α i
            = ∑ i : I,
                (u (Sum.inl i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inl i) +
                  u (Sum.inr i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inr i)) := by
                refine Finset.sum_congr rfl ?_
                intro i _
                by_cases hi : i ∈ eqIndices
                · calc
                    w i * α i = (u (Sum.inl i) - u (Sum.inr i)) * α i := by
                      simp [w, hi]
                    _ = u (Sum.inl i) * α i + u (Sum.inr i) * (-α i) := by
                          ring
                    _ = u (Sum.inl i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inl i) +
                          u (Sum.inr i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inr i) := by
                          simp [mixedLinearConstraintFarkasScalar, hi]
                · simp [w, mixedLinearConstraintFarkasScalar, hi]
        _ = ∑ i : I, u (Sum.inl i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inl i) +
              ∑ i : I, u (Sum.inr i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inr i) := by
                rw [Finset.sum_add_distrib]
        _ < 0 := hu_scalar'
  · rintro ⟨w, hw_nonneg, hw_vec, hw_scalar⟩
    let u : I ⊕ I → ℝ :=
      Sum.elim
        (fun i ↦ if hi : i ∈ eqIndices then max (w i) 0 else w i)
        (fun i ↦ if hi : i ∈ eqIndices then max (-w i) 0 else 0)
    refine ⟨u, ?_, ?_, ?_⟩
    · intro j
      cases j with
      | inl i =>
          by_cases hi : i ∈ eqIndices
          · simp [u, hi]
          · simp [u, hi, hw_nonneg i hi]
      | inr i =>
          by_cases hi : i ∈ eqIndices
          · simp [u, hi]
          · simp [u, hi]
    · have hsum :
        ∑ i : I, u (Sum.inl i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inl i) +
            ∑ i : I, u (Sum.inr i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inr i) =
          ∑ i : I, w i • a i := by
        calc
          ∑ i : I, u (Sum.inl i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inl i) +
              ∑ i : I, u (Sum.inr i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inr i)
              = ∑ i : I, u (Sum.inl i) • a i +
                  ∑ i : I, u (Sum.inr i) • (if i ∈ eqIndices then -a i else 0) := by
                    simp [mixedLinearConstraintFarkasFunctional]
          _ = ∑ i : I, (u (Sum.inl i) • a i + u (Sum.inr i) • (if i ∈ eqIndices then -a i else 0)) := by
                rw [← Finset.sum_add_distrib]
          _ = ∑ i : I, w i • a i := by
                refine Finset.sum_congr rfl ?_
                intro i _
                by_cases hi : i ∈ eqIndices
                · calc
                    u (Sum.inl i) • a i + u (Sum.inr i) • (if i ∈ eqIndices then -a i else 0)
                        = max (w i) 0 • a i + max (-w i) 0 • (-a i) := by
                            simp [u, hi]
                    _ = (max (w i) 0 - max (-w i) 0) • a i := by
                          simp [sub_eq_add_neg, add_smul]
                    _ = w i • a i := by rw [max_zero_sub_eq_self]
                · simp [u, hi]
      calc
        ∑ j : I ⊕ I, u j • mixedLinearConstraintFarkasFunctional a eqIndices j
            = ∑ i : I, u (Sum.inl i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inl i) +
                ∑ i : I, u (Sum.inr i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inr i) := by
                  rw [Fintype.sum_sum_type]
        _ = ∑ i : I, w i • a i := hsum
        _ = 0 := hw_vec
    · have hsum :
        ∑ i : I, u (Sum.inl i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inl i) +
            ∑ i : I, u (Sum.inr i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inr i) =
          ∑ i : I, w i * α i := by
        calc
          ∑ i : I, u (Sum.inl i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inl i) +
              ∑ i : I, u (Sum.inr i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inr i)
              = ∑ i : I, u (Sum.inl i) * α i +
                  ∑ i : I, u (Sum.inr i) * (if i ∈ eqIndices then -α i else 0) := by
                    simp [mixedLinearConstraintFarkasScalar]
          _ = ∑ i : I, (u (Sum.inl i) * α i + u (Sum.inr i) * (if i ∈ eqIndices then -α i else 0)) := by
                rw [← Finset.sum_add_distrib]
          _ = ∑ i : I, w i * α i := by
                refine Finset.sum_congr rfl ?_
                intro i _
                by_cases hi : i ∈ eqIndices
                · calc
                    u (Sum.inl i) * α i + u (Sum.inr i) * (if i ∈ eqIndices then -α i else 0)
                        = max (w i) 0 * α i + max (-w i) 0 * (-α i) := by
                            simp [u, hi]
                    _ = (max (w i) 0 - max (-w i) 0) * α i := by
                          ring
                    _ = w i * α i := by rw [max_zero_sub_eq_self]
                · simp [u, hi]
      calc
        ∑ j : I ⊕ I, u j * mixedLinearConstraintFarkasScalar α eqIndices j
            = ∑ i : I, u (Sum.inl i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inl i) +
                ∑ i : I, u (Sum.inr i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inr i) := by
                  rw [Fintype.sum_sum_type]
        _ = ∑ i : I, w i * α i := hsum
        _ < 0 := hw_scalar

-- Proof sketch: rewrite each equality constraint indexed by `eqIndices` as the pair of
-- inequalities `aᵢ x ≤ αᵢ` and `(-aᵢ) x ≤ -αᵢ`, apply Theorem 22.1 to that enlarged family, and
-- then combine the two nonnegative multipliers on each equality index into the signed coefficient
-- `λ i = μ⁺ i - μ⁻ i`.
/-- Text 22.3.5 on the functional-owner layer: for linear functionals `aᵢ`, scalars
`αᵢ`, and an equality-index set `eqIndices`, exactly one of the following holds: either the mixed
owner feasible set `feasibleSet (eqOn eqIndices) a α` is nonempty, or there is a multiplier
family `λ` with `λᵢ ≥ 0` on the inequality indices, `∑ i, λᵢ • aᵢ = 0`, and
`∑ i, λᵢ αᵢ < 0`. -/
theorem xor_mixed_linear_constraint_solution_set_nonempty_or_mixed_linear_constraint_farkas_certificate
    (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ) (eqIndices : Set I) :
    Xor'
      (solutionSet[eqIndices; a, α]).Nonempty
      (∃ w : I → ℝ,
        (∀ i : I, i ∉ eqIndices → 0 ≤ w i) ∧
          (∑ i : I, w i • a i = 0) ∧
            (∑ i : I, w i * α i) < 0) := by
  have hmain :
      Xor'
        (mixedLinearConstraintWeakSolutionSet a α eqIndices).Nonempty
        (∃ u : I ⊕ I → ℝ,
          (∀ j : I ⊕ I, 0 ≤ u j) ∧
            (∑ j : I ⊕ I, u j • mixedLinearConstraintFarkasFunctional a eqIndices j = 0) ∧
              (∑ j : I ⊕ I, u j * mixedLinearConstraintFarkasScalar α eqIndices j) < 0) :=
    xor_linearInequalitySolutionSet_nonempty_or_weak_linear_inequality_farkas_certificate
      (mixedLinearConstraintFarkasFunctional a eqIndices)
      (mixedLinearConstraintFarkasScalar α eqIndices)
  rcases hmain with h | h
  · left
    refine ⟨by
      simpa [weakSolutionSet_eq_mixed_linear_constraint_solutionSet a α eqIndices] using h.1, ?_⟩
    intro hw
    exact h.2 ((exists_mixed_linear_constraint_farkas_certificate_iff a α eqIndices).2 hw)
  · right
    refine ⟨(exists_mixed_linear_constraint_farkas_certificate_iff a α eqIndices).1 h.1, ?_⟩
    intro hs
    exact h.2 (by
      simpa [weakSolutionSet_eq_mixed_linear_constraint_solutionSet a α eqIndices] using hs)

/-- Companion pointwise form of Text 22.3.5 on the functional-owner layer. -/
theorem xor_exists_feasible_point_or_mixed_linear_constraint_farkas_certificate
    (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ) (eqIndices : Set I) :
    Xor'
      (∃ x : E,
        (∀ i : I, i ∉ eqIndices → ⟪x, a i⟫ₚ ≤ α i) ∧
          ∀ i : I, i ∈ eqIndices → ⟪x, a i⟫ₚ = α i)
      (∃ w : I → ℝ,
        (∀ i : I, i ∉ eqIndices → 0 ≤ w i) ∧
          (∑ i : I, w i • a i = 0) ∧
            (∑ i : I, w i * α i) < 0) := by
  simpa [mixed_linear_constraint_solution_set_nonempty_iff] using
    xor_mixed_linear_constraint_solution_set_nonempty_or_mixed_linear_constraint_farkas_certificate
      a α eqIndices

end FunctionalOwner

section PairingFunctionalBridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {Y : Type*} [AddCommMonoid Y] [Module ℝ Y] [HasLinearPairing E Y ℝ]
variable {I : Type*} [Fintype I]

local notation "solutionSet[" eqIndices "; " a ", " α "]" =>
  (feasibleSet (eqOn eqIndices) a α : Set E)

/-- Pairing-owner pointwise formulation of Text 22.3.5, obtained by transporting the
linear-functional mixed alternative through `HasLinearPairing.pairingLinear`. -/
theorem xor_exists_feasible_point_or_mixed_pairing_constraint_farkas_certificate
    (a : I → Y) (α : I → ℝ) (eqIndices : Set I) :
    Xor'
      (∃ x : E,
        (∀ i : I, i ∉ eqIndices → (⟪x, a i⟫ₚ : ℝ) ≤ α i) ∧
          ∀ i : I, i ∈ eqIndices → (⟪x, a i⟫ₚ : ℝ) = α i)
      (∃ w : I → ℝ,
        (∀ i : I, i ∉ eqIndices → 0 ≤ w i) ∧
          (∀ x : E, ∑ i : I, w i * (⟪x, a i⟫ₚ : ℝ) = 0) ∧
            (∑ i : I, w i * α i) < 0) := by
  let aLin : I → E →ₗ[ℝ] ℝ :=
    fun i ↦ (HasLinearPairing.pairingLinear (𝕜 := ℝ) (X := E) (Y := Y)).flip (a i)
  have hmain :
      Xor'
        (∃ x : E,
          (∀ i : I, i ∉ eqIndices → ⟪x, aLin i⟫ₚ ≤ α i) ∧
            ∀ i : I, i ∈ eqIndices → ⟪x, aLin i⟫ₚ = α i)
        (∃ w : I → ℝ,
          (∀ i : I, i ∉ eqIndices → 0 ≤ w i) ∧
            (∑ i : I, w i • aLin i = 0) ∧
              (∑ i : I, w i * α i) < 0) :=
    xor_exists_feasible_point_or_mixed_linear_constraint_farkas_certificate aLin α eqIndices
  have hsolution :
      (∃ x : E,
        (∀ i : I, i ∉ eqIndices → ⟪x, aLin i⟫ₚ ≤ α i) ∧
          ∀ i : I, i ∈ eqIndices → ⟪x, aLin i⟫ₚ = α i) ↔
      (∃ x : E,
        (∀ i : I, i ∉ eqIndices → (⟪x, a i⟫ₚ : ℝ) ≤ α i) ∧
          ∀ i : I, i ∈ eqIndices → (⟪x, a i⟫ₚ : ℝ) = α i) := by
    constructor
    · rintro ⟨x, hxle, hxeq⟩
      refine ⟨x, ?_, ?_⟩
      · intro i hi
        simpa [aLin, HasLinearPairing.pairing_eq_pairingLinear] using hxle i hi
      · intro i hi
        simpa [aLin, HasLinearPairing.pairing_eq_pairingLinear] using hxeq i hi
    · rintro ⟨x, hxle, hxeq⟩
      refine ⟨x, ?_, ?_⟩
      · intro i hi
        simpa [aLin, HasLinearPairing.pairing_eq_pairingLinear] using hxle i hi
      · intro i hi
        simpa [aLin, HasLinearPairing.pairing_eq_pairingLinear] using hxeq i hi
  have hcertificate :
      (∃ w : I → ℝ,
        (∀ i : I, i ∉ eqIndices → 0 ≤ w i) ∧
          (∑ i : I, w i • aLin i = 0) ∧
            (∑ i : I, w i * α i) < 0) ↔
      (∃ w : I → ℝ,
        (∀ i : I, i ∉ eqIndices → 0 ≤ w i) ∧
          (∀ x : E, ∑ i : I, w i * (⟪x, a i⟫ₚ : ℝ) = 0) ∧
            (∑ i : I, w i * α i) < 0) := by
    constructor
    · rintro ⟨w, hw_nonneg, hw_sum, hw_scalar⟩
      refine ⟨w, hw_nonneg, ?_, hw_scalar⟩
      intro x
      have hw_sum_x : (∑ i : I, w i • aLin i) x = 0 := by
        simpa using congrArg (fun b : E →ₗ[ℝ] ℝ ↦ b x) hw_sum
      simpa [aLin, HasLinearPairing.pairing_eq_pairingLinear, smul_eq_mul] using hw_sum_x
    · rintro ⟨w, hw_nonneg, hw_sum, hw_scalar⟩
      refine ⟨w, hw_nonneg, ?_, hw_scalar⟩
      ext x
      have hw_sum_x : ∑ i : I, w i * (⟪x, a i⟫ₚ : ℝ) = 0 := hw_sum x
      simpa [aLin, HasLinearPairing.pairing_eq_pairingLinear, smul_eq_mul] using hw_sum_x
  rcases hmain with h | h
  · left
    refine ⟨(hsolution.mp h.1), ?_⟩
    intro hw
    exact h.2 (hcertificate.mpr hw)
  · right
    refine ⟨(hcertificate.mp h.1), ?_⟩
    intro hs
    exact h.2 (hsolution.mpr hs)

/-- Pairing-owner feasible-set form of Text 22.3.5. -/
theorem xor_mixed_linear_constraint_solution_set_nonempty_or_mixed_pairing_constraint_farkas_certificate
    (a : I → Y) (α : I → ℝ) (eqIndices : Set I) :
    Xor'
      (solutionSet[eqIndices; a, α]).Nonempty
      (∃ w : I → ℝ,
        (∀ i : I, i ∉ eqIndices → 0 ≤ w i) ∧
          (∀ x : E, ∑ i : I, w i * (⟪x, a i⟫ₚ : ℝ) = 0) ∧
            (∑ i : I, w i * α i) < 0) := by
  simpa [mixed_linear_constraint_solution_set_nonempty_iff] using
    xor_exists_feasible_point_or_mixed_pairing_constraint_farkas_certificate a α eqIndices

end PairingFunctionalBridge

section InnerProductSpecialization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : Type*} [Fintype I]

local notation "solutionSet[" eqIndices "; " a ", " α "]" =>
  (feasibleSet (eqOn eqIndices) a α : Set E)

/-- Inner-product specialization of the source-facing mixed alternative, recovered from the
functional-owner theorem via the canonical Fréchet-Riesz bridge `InnerProductSpace.toDual`. -/
theorem xor_exists_feasible_point_or_mixed_linear_constraint_farkas_certificate_innerProduct
    (a : I → E) (α : I → ℝ) (eqIndices : Set I) :
    Xor'
      (∃ x : E,
        (∀ i : I, i ∉ eqIndices → ⟪a i, x⟫ ≤ α i) ∧
          ∀ i : I, i ∈ eqIndices → ⟪a i, x⟫ = α i)
      (∃ w : I → ℝ,
        (∀ i : I, i ∉ eqIndices → 0 ≤ w i) ∧
          (∑ i : I, w i • a i = 0) ∧
            (∑ i : I, w i * α i) < 0) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hcertificate :
      (∃ w : I → ℝ,
        (∀ i : I, i ∉ eqIndices → 0 ≤ w i) ∧
          (∑ i : I, w i • ((InnerProductSpace.toDual ℝ E) (a i)).toLinearMap = 0) ∧
            (∑ i : I, w i * α i) < 0) ↔
      (∃ w : I → ℝ,
        (∀ i : I, i ∉ eqIndices → 0 ≤ w i) ∧
          (∑ i : I, w i • a i = 0) ∧
            (∑ i : I, w i * α i) < 0) := by
    constructor
    · rintro ⟨w, hw_nonneg, hw_sum, hw_α⟩
      refine ⟨w, hw_nonneg, ?_, hw_α⟩
      have hw_sum_cont : ∑ i : I, w i • (InnerProductSpace.toDual ℝ E) (a i) = 0 := by
        ext x
        have hw_sum_x :
            (∑ i : I, w i • ((InnerProductSpace.toDual ℝ E) (a i)).toLinearMap) x = 0 := by
          simpa using congrArg (fun b : E →ₗ[ℝ] ℝ => b x) hw_sum
        simpa using hw_sum_x
      apply (InnerProductSpace.toDual ℝ E).injective
      simpa using hw_sum_cont
    · rintro ⟨w, hw_nonneg, hw_sum, hw_α⟩
      refine ⟨w, hw_nonneg, ?_, hw_α⟩
      have hw_sum_cont : ∑ i : I, w i • (InnerProductSpace.toDual ℝ E) (a i) = 0 := by
        simpa using congrArg (InnerProductSpace.toDual ℝ E) hw_sum
      ext x
      have hw_sum_cont_x :
          (∑ i : I, w i • (InnerProductSpace.toDual ℝ E) (a i)) x = 0 := by
        simpa using congrArg (fun b : E →L[ℝ] ℝ => b x) hw_sum_cont
      simpa using hw_sum_cont_x
  simpa [InnerProductSpace.toDual_apply_apply, Xor', hcertificate] using
    (xor_exists_feasible_point_or_mixed_linear_constraint_farkas_certificate
      (fun i ↦ ((InnerProductSpace.toDual ℝ E) (a i)).toLinearMap) α eqIndices)

/-- Inner-product owner-form specialization of Text 22.3.5, obtained from the functional-owner
theorem through `InnerProductSpace.toDual`. -/
theorem xor_mixed_linear_constraint_solution_set_nonempty_or_mixed_linear_constraint_farkas_certificate_innerProduct
    (a : I → E) (α : I → ℝ) (eqIndices : Set I) :
    Xor'
      (solutionSet[eqIndices; a, α]).Nonempty
      (∃ w : I → ℝ,
        (∀ i : I, i ∉ eqIndices → 0 ≤ w i) ∧
          (∑ i : I, w i • a i = 0) ∧
            (∑ i : I, w i * α i) < 0) := by
  simpa [mixed_linear_constraint_solution_set_nonempty_iff, real_inner_comm] using
    xor_exists_feasible_point_or_mixed_linear_constraint_farkas_certificate_innerProduct
      a α eqIndices

end InnerProductSpecialization
