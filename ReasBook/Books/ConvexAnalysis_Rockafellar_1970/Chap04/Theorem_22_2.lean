import ConvexAnalysis_Rockafellar_1970.Chap01.Corollary_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_5_0
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_21_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Rockafellar
open LinearConstraintRelation

set_option linter.style.emptyLine false
set_option linter.style.longLine false

private def strictCutIndices {m : ℕ} (k : ℕ) : Set (Fin m) := {i : Fin m | i.1 < k}

private abbrev StrictSubtype (I : Type*) (S : Set I) := {i : I // i ∈ S}
private abbrev WeakSubtype (I : Type*) (S : Set I) := {i : I // i ∉ S}

private lemma withBotTop_coe_add (a b : ℝ) :
    ((a : WithBotTop ℝ) + (b : WithBotTop ℝ)) = ((a + b : ℝ) : WithBotTop ℝ) := by
  change (WithBot.some (WithTop.some a) + WithBot.some (WithTop.some b) : WithBot (WithTop ℝ)) =
    WithBot.some (WithTop.some (a + b))
  simp [WithTop.coe_add, WithBot.coe_add]

private lemma withBotTop_coe_mul (a b : ℝ) :
    ((a : WithBotTop ℝ) * (b : WithBotTop ℝ)) = ((a * b : ℝ) : WithBotTop ℝ) := by
  change (WithBot.some (WithTop.some a) * WithBot.some (WithTop.some b) : WithBot (WithTop ℝ)) =
    WithBot.some (WithTop.some (a * b))
  simp [WithTop.coe_mul, WithBot.coe_mul]

private lemma withBotTop_sum_coe {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ i, ((f i : ℝ) : WithBotTop ℝ)) = ((∑ i, f i : ℝ) : WithBotTop ℝ) := by
  let φ : ℝ →+ WithBotTop ℝ :=
    { toFun := fun x ↦ (x : WithBotTop ℝ)
      map_zero' := rfl
      map_add' := by
        intro x y
        simpa using withBotTop_coe_add x y }
  change ∑ i, φ (f i) = φ (∑ i, f i)
  exact (map_sum φ f Finset.univ).symm

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 22.2 is the finite mixed strict/weak linear-inequality alternative
  with strict block `i < k` and weak block `k ≤ i`, expressed on the pairing owner
  `a : I → Y`; the functional case `a : I → E →ₗ[ℝ] ℝ` is a bridge specialization.
- `core/canonical`: the owner abstraction for feasibility is the mixed set-index owner
  `LinearConstraintRelation.feasibleSet (LinearConstraintRelation.ltOn S) a α`
  indexed by `S : Set I` at the pairing layer `a : I → Y`, and the multiplier side is the
  intrinsic scalar condition
  `∀ x, ∑ i, w i * ⟪x, a i⟫ₚ = 0` together with nonnegativity/strict-support and
  `∑ i, w i * α i ≤ 0`.
- `bridge/view`: the functional specialization `a : I → E →ₗ[ℝ] ℝ` with
  `∑ i, w i • a i = 0` is retained as the direct downstream bridge to Theorem 22.1.
- `bridge/index`: the textbook indexing `i = 1, …, k` and `i = k + 1, …, m` is represented using
  zero-based `Fin m` indices by the set `{i : Fin m | i.1 < k}`; the theorem is the direct linear
  specialization of the mixed convex-affine alternative in Theorem 21.2 obtained from affine maps
  `x ↦ aᵢ x - αᵢ`.

Domain-style sampling used here:
- the Chapter 1 owners `LinearConstraintRelation.ltOn` and
  `LinearConstraintRelation.feasibleSet`;
- the Chapter 22 canonical algebraic-functional owner theorem
  `xor_linearInequalitySolutionSet_nonempty_or_weak_linear_inequality_farkas_certificate`;
- the Chapter 21 mixed convex-affine owner theorem
  `xor_mixed_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate`;
- the Chapter 22 continuous-dual bridge theorem
  `xor_linearInequalitySolutionSet_nonempty_or_weak_linear_inequality_farkas_certificate_contDual`.

Primitive data vs derived API:
- primitive inputs: a strict-index set `S : Set I`, a finite family
  `a : I → Y`, and bounds `α : I → ℝ`;
- owner data: the mixed feasible set
  `LinearConstraintRelation.feasibleSet (LinearConstraintRelation.ltOn S) a α : Set E`;
- derived API: the textbook pointwise feasibility clause and the exclusive alternative between
  feasibility of that owner set and direct existence of a nonnegative multiplier family whose
  weighted pairing sum vanishes pointwise, whose weighted scalar sum is nonpositive, and whose
  strict block `S` contains a positive coefficient.

Layer target: `bridge/view`; the canonical owner-side feasible set is kept explicit, and the
textbook pointwise wording is recovered immediately below as a thin companion rather than as a
parallel root API.

Abstraction checks for this item:
- scalar/codomain layer: the public owner remains over `ℝ` because Theorem 22.2 is an
  order-and-separation alternative with real nonnegative multipliers and a real affine-separation
  certificate; the reused Chapter 21 owner theorem is exactly the real
  `WithBotTop ℝ` mixed alternative, and this file adds no extra scalar specialization;
- ambient structure: no `InnerProductSpace` owner assumptions are used; the theorem stays on the
  weaker pairing/linear-functional layer;
- owner naming/surface: the main theorem is set-indexed by `strictIndices : Set I`; linear-map and
  cut-index textbook forms are retained as downstream specializations.
-/

section PairingOwner

variable {E : Type*} {Y : Type*} {R : Type*} {I : Type*}
variable [LE R] [LT R] [HasPairing E Y R]

local notation "solutionSet[" strictIndices "; " a ", " α "]" =>
  (feasibleSet (ltOn strictIndices) a α : Set E)
local notation "weakSet[" strictIndices "; " a ", " α "]" =>
  (LinearConstraintRelation.leFeasible
    (X := E)
    (fun i : {i : I // i ∉ strictIndices} ↦ a i)
    (fun i : {i : I // i ∉ strictIndices} ↦ α i) : Set E)

/- The mixed owner feasible set for `ltOn` is nonempty exactly when there is a point satisfying
the strict constraints on `strictIndices` and weak constraints on the complement. -/
theorem ltOn_pairing_constraint_solution_set_nonempty_iff
    (strictIndices : Set I) (a : I → Y) (α : I → R) :
    (solutionSet[strictIndices; a, α]).Nonempty ↔
      ∃ x : E,
        (∀ i : I, i ∈ strictIndices → ⟪x, a i⟫ₚ < α i) ∧
          ∀ i : I, i ∉ strictIndices → ⟪x, a i⟫ₚ ≤ α i := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_, ?_⟩
    · intro i hi
      have hxi := (mem_feasibleSet _ _ _ _).1 hx i
      simpa [ltOn, hi] using hxi
    · intro i hi
      have hxi := (mem_feasibleSet _ _ _ _).1 hx i
      simpa [ltOn, hi] using hxi
  · rintro ⟨x, hxstrict, hxweak⟩
    refine ⟨x, (mem_feasibleSet _ _ _ _).2 ?_⟩
    intro i
    by_cases hi : i ∈ strictIndices
    · simpa [ltOn, hi] using hxstrict i hi
    · simpa [ltOn, hi] using hxweak i hi

/- The weak block on the complement of `strictIndices` is exactly the canonical weak owner
`leFeasible` on the weak-index subtype. -/
theorem weak_pairing_constraint_complement_solution_set_nonempty_iff
    (strictIndices : Set I) (a : I → Y) (α : I → R) :
    (weakSet[strictIndices; a, α]).Nonempty ↔
      ∃ x : E, ∀ i : I, i ∉ strictIndices → ⟪x, a i⟫ₚ ≤ α i := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro i hi
    have hxi : ∀ j : {j : I // j ∉ strictIndices}, ⟪x, a j⟫ₚ ≤ α j :=
      (LinearConstraintRelation.mem_leFeasible
        (X := E)
        (b := fun j : {j : I // j ∉ strictIndices} ↦ a j)
        (β := fun j : {j : I // j ∉ strictIndices} ↦ α j)
        (x := x)).1 hx
    simpa using hxi ⟨i, hi⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, (LinearConstraintRelation.mem_leFeasible
      (X := E)
      (b := fun j : {j : I // j ∉ strictIndices} ↦ a j)
      (β := fun j : {j : I // j ∉ strictIndices} ↦ α j)
      (x := x)).2 ?_⟩
    intro i
    exact hx i i.2

end PairingOwner

section CutIndexPairingBridge

variable {E : Type*} {Y : Type*} {R : Type*}
variable [LE R] [LT R] [HasPairing E Y R]
variable {m : ℕ}

local notation "solutionSet[" k "; " a ", " α "]" =>
  (feasibleSet (ltOn (strictCutIndices (m := m) k)) a α : Set E)

/- The textbook cut-index strict/weak system is a direct specialization of the `ltOn` owner
bridge theorem. -/
theorem strict_weak_pairing_constraint_solution_set_nonempty_iff
    (k : ℕ) (a : Fin m → Y) (α : Fin m → R) :
    (solutionSet[k; a, α]).Nonempty ↔
      ∃ x : E,
        (∀ i : Fin m, i.1 < k → ⟪x, a i⟫ₚ < α i) ∧
          ∀ i : Fin m, k ≤ i.1 → ⟪x, a i⟫ₚ ≤ α i := by
  simpa [strictCutIndices, Set.mem_setOf_eq, not_lt] using
    (ltOn_pairing_constraint_solution_set_nonempty_iff
      (E := E) (Y := Y) (R := R) (I := Fin m) (strictCutIndices (m := m) k) a α)

end CutIndexPairingBridge

section LinearFunctionalCore

variable {E : Type*}
variable [TopologicalSpace E] [AddCommGroup E] [TopologicalAddGroup E]
variable [Module ℝ E] [ContinuousSMul ℝ E] [FiniteDimensional ℝ E]
variable {I : Type*} [Fintype I]

local notation "solutionSet[" strictIndices "; " a ", " α "]" =>
  (feasibleSet (ltOn strictIndices) a α : Set E)

/- Abstraction audit: this section provides the linear-functional bridge
`a : I → E →ₗ[ℝ] ℝ`; the pairing-owner theorem is stated below in
`PairingFunctionalBridge`. Continuous-dual forms remain downstream bridge
specializations. The ambient assumptions stay at the weaker topological-module layer
`[TopologicalSpace E] [AddCommGroup E] [TopologicalAddGroup E] [Module ℝ E]
[ContinuousSMul ℝ E] [FiniteDimensional ℝ E]`, matching the upstream
certificate/separation owner reused from Theorem 21.2. -/
set_option linter.style.emptyLine false in
set_option linter.style.longLine false in
/-- Internal linear-functional core used to prove the public pairing-owner theorem and its
functional bridge specialization. -/
private theorem
    xor_ltOn_linear_constraint_solution_set_nonempty_or_nonnegative_multiplier_certificate_core
    (strictIndices : Set I) (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ)
    (hconsistent : ∃ x : E, ∀ i : I, i ∉ strictIndices → a i x ≤ α i) :
    Xor'
      (solutionSet[strictIndices; a, α]).Nonempty
      (∃ w : I → ℝ,
        (∀ i : I, 0 ≤ w i) ∧
        (∃ i : I, i ∈ strictIndices ∧ 0 < w i) ∧
        (∑ i : I, w i • a i = 0) ∧
        (∑ i : I, w i * α i ≤ 0)) := by
  classical
  let _ : DecidablePred (fun i : I ↦ i ∈ strictIndices) := Classical.decPred strictIndices
  let strictType := StrictSubtype I strictIndices
  let weakType := WeakSubtype I strictIndices
  let eStrict : strictType ≃ Fin (Fintype.card strictType) := Fintype.equivFin strictType
  let eWeak : weakType ≃ Fin (Fintype.card weakType) := Fintype.equivFin weakType
  let strictAffine : Fin (Fintype.card strictType) → E →ᵃ[ℝ] ℝ :=
    fun i ↦
      (a (eStrict.symm i)).toAffineMap +
        AffineMap.const ℝ E (-α (eStrict.symm i))
  let weakAffine : Fin (Fintype.card weakType) → E →ᵃ[ℝ] ℝ :=
    fun j ↦
      (a (eWeak.symm j)).toAffineMap +
        AffineMap.const ℝ E (-α (eWeak.symm j))
  let strictFun : Fin (Fintype.card strictType) → E → WithBotTop ℝ :=
    fun i ↦ Function.toWithBotTop (strictAffine i)

  have hfeasible_not_certificate :
      (∃ x : E,
        (∀ i : I, i ∈ strictIndices → a i x < α i) ∧
          (∀ i : I, i ∉ strictIndices → a i x ≤ α i)) →
      ¬ (∃ w : I → ℝ,
        (∀ i : I, 0 ≤ w i) ∧
        (∃ i : I, i ∈ strictIndices ∧ 0 < w i) ∧
        (∑ i : I, w i • a i = 0) ∧
        (∑ i : I, w i * α i ≤ 0)) := by
    rintro ⟨x, hxstrict, hxweak⟩ ⟨w, hw_nonneg, hw_pos, hw_sum, hw_α⟩
    rcases hw_pos with ⟨i0, hi0, hi0_pos⟩
    have hw_sum_x : (∑ i : I, w i • a i) x = 0 := by
      simpa using congrArg (fun b : E →ₗ[ℝ] ℝ ↦ b x) hw_sum
    have hle : ∀ i : I, w i * a i x ≤ w i * α i := by
      intro i
      by_cases hi : i ∈ strictIndices
      · exact mul_le_mul_of_nonneg_left (le_of_lt (hxstrict i hi)) (hw_nonneg i)
      · exact mul_le_mul_of_nonneg_left (hxweak i hi) (hw_nonneg i)
    have hlt_i0 : w i0 * a i0 x < w i0 * α i0 :=
      mul_lt_mul_of_pos_left (hxstrict i0 hi0) hi0_pos
    have hsum_lt : ∑ i : I, w i * a i x < ∑ i : I, w i * α i := by
      simpa using
        (Finset.sum_lt_sum (s := (Finset.univ : Finset I))
          (f := fun i ↦ w i * a i x)
          (g := fun i ↦ w i * α i)
          (fun i _ ↦ hle i)
          ⟨i0, by simp, hlt_i0⟩)
    have hsum_eval : (∑ i : I, w i * a i x) = 0 := by
      simpa [smul_eq_mul] using hw_sum_x
    have hα_pos : 0 < ∑ i : I, w i * α i := by
      simpa [hsum_eval] using hsum_lt
    linarith

  have hmain :
    Xor'
      (∃ x : E,
        x ∈ (Set.univ : Set E) ∧
          (∀ i : Fin (Fintype.card strictType), strictFun i x < 0) ∧
            ∀ j : Fin (Fintype.card weakType), weakAffine j x ≤ 0)
      (∃ wf : Fin (Fintype.card strictType) → ℝ,
        ∃ wg : Fin (Fintype.card weakType) → ℝ,
          (∀ i : Fin (Fintype.card strictType), 0 ≤ wf i) ∧
          (∀ j : Fin (Fintype.card weakType), 0 ≤ wg j) ∧
          (∃ i : Fin (Fintype.card strictType), wf i ≠ 0) ∧
            (∀ x : (Set.univ : Set E),
              (0 : WithBotTop ℝ) ≤
                ∑ i : Fin (Fintype.card strictType),
                    (wf i : WithBotTop ℝ) * strictFun i x +
                  ∑ j : Fin (Fintype.card weakType),
                    (wg j : WithBotTop ℝ) * Function.toWithBotTop (weakAffine j) x)) :=
    xor_strict_feasible_or_nonnegative_multiplier_certificate
      (C := (Set.univ : Set E))
      convex_univ
      strictFun
      weakAffine
      (by
        intro i
        simpa [strictFun] using
          (Function.isConvex_coe_of_convexOn_univ (strictAffine i).convexOn_univ).isConvexOn
            (convex_univ : Convex ℝ (Set.univ : Set E)))
      (by
        intro i x
        exact lt_of_le_of_ne bot_le (Ne.symm (WithBotTop.coe_ne_bot ((strictAffine i) x))))
      (by
        intro i x hx
        exact lt_top_iff_ne_top.mpr (WithBotTop.coe_ne_top ((strictAffine i) x)))
      (by
        rcases hconsistent with ⟨x0, hx0⟩
        refine ⟨x0, by simp, ?_⟩
        intro j
        have hj : a (eWeak.symm j) x0 ≤ α (eWeak.symm j) :=
          hx0 (eWeak.symm j) (eWeak.symm j).2
        have hj' : a (eWeak.symm j) x0 - α (eWeak.symm j) ≤ 0 := sub_nonpos.mpr hj
        simpa [weakAffine, sub_eq_add_neg] using hj')

  rcases hmain with hmain | hmain
  · left
    rcases hmain with ⟨hfeas, hnotcert⟩
    rcases hfeas with ⟨x, _, hxstrict, hxweak⟩
    have hxstrict' : ∀ i : I, i ∈ strictIndices → a i x < α i := by
      intro i hi
      have hxi : strictFun (eStrict ⟨i, hi⟩) x < 0 := hxstrict (eStrict ⟨i, hi⟩)
      have hxi' : ((a i x - α i : ℝ) : WithBotTop ℝ) < 0 := by
        simpa [strictFun, strictAffine, sub_eq_add_neg] using hxi
      have hxi'' : a i x - α i < 0 := (WithBotTop.coe_lt_coe).1 hxi'
      linarith
    have hxweak' : ∀ i : I, i ∉ strictIndices → a i x ≤ α i := by
      intro i hi
      have hxi : weakAffine (eWeak ⟨i, hi⟩) x ≤ 0 := hxweak (eWeak ⟨i, hi⟩)
      have hxi' : a i x - α i ≤ 0 := by
        simpa [weakAffine, sub_eq_add_neg] using hxi
      exact sub_nonpos.mp hxi'
    refine ⟨?_, ?_⟩
    · exact (ltOn_pairing_constraint_solution_set_nonempty_iff
        (E := E) (Y := E →ₗ[ℝ] ℝ) (R := ℝ) (I := I) strictIndices a α).2
        ⟨x, hxstrict', hxweak'⟩
    · intro hcert
      exact hfeasible_not_certificate ⟨x, hxstrict', hxweak'⟩ hcert
  · right
    rcases hmain with ⟨hcert, hnotfeas⟩
    rcases hcert with ⟨wf, wg, hwf_nonneg, hwg_nonneg, hwf_nonzero, hineq⟩
    let wfStrict : strictType → ℝ := fun s ↦ wf (eStrict s)
    let wgWeak : weakType → ℝ := fun t ↦ wg (eWeak t)
    let w : I → ℝ :=
      fun i ↦ if hi : i ∈ strictIndices then wfStrict ⟨i, hi⟩ else wgWeak ⟨i, hi⟩
    let sFun : E →ₗ[ℝ] ℝ :=
      (∑ i : Fin (Fintype.card strictType), wf i • a (eStrict.symm i)) +
        ∑ j : Fin (Fintype.card weakType), wg j • a (eWeak.symm j)
    let c : ℝ :=
      (∑ i : Fin (Fintype.card strictType), wf i * α (eStrict.symm i)) +
        ∑ j : Fin (Fintype.card weakType), wg j * α (eWeak.symm j)

    have hbound : ∀ x : E, 0 ≤ sFun x - c := by
      intro x
      have hxWithBotTop := hineq ⟨x, by simp⟩
      have hstrict_term :
          ∀ i : Fin (Fintype.card strictType),
            (wf i : WithBotTop ℝ) * strictFun i x =
              ((wf i * strictAffine i x : ℝ) : WithBotTop ℝ) := by
        intro i
        simpa [strictFun, Function.toWithBotTop] using withBotTop_coe_mul (wf i) (strictAffine i x)
      have hweak_term :
          ∀ j : Fin (Fintype.card weakType),
            (wg j : WithBotTop ℝ) * Function.toWithBotTop (weakAffine j) x =
              ((wg j * weakAffine j x : ℝ) : WithBotTop ℝ) := by
        intro j
        simpa [Function.toWithBotTop] using withBotTop_coe_mul (wg j) (weakAffine j x)
      have hstrict_sum_coe :
          (∑ i : Fin (Fintype.card strictType), (wf i : WithBotTop ℝ) * strictFun i x) =
            ((∑ i : Fin (Fintype.card strictType), wf i * strictAffine i x : ℝ) : WithBotTop ℝ) := by
        calc
          (∑ i : Fin (Fintype.card strictType), (wf i : WithBotTop ℝ) * strictFun i x)
              = ∑ i : Fin (Fintype.card strictType), ((wf i * strictAffine i x : ℝ) : WithBotTop ℝ) := by
                  refine Finset.sum_congr rfl ?_
                  intro i _
                  exact hstrict_term i
          _ = ((∑ i : Fin (Fintype.card strictType), wf i * strictAffine i x : ℝ) : WithBotTop ℝ) := by
                simpa using withBotTop_sum_coe (f := fun i : Fin (Fintype.card strictType) ↦
                  wf i * strictAffine i x)
      have hweak_sum_coe :
          (∑ j : Fin (Fintype.card weakType), (wg j : WithBotTop ℝ) * Function.toWithBotTop (weakAffine j) x) =
            ((∑ j : Fin (Fintype.card weakType), wg j * weakAffine j x : ℝ) : WithBotTop ℝ) := by
        calc
          (∑ j : Fin (Fintype.card weakType), (wg j : WithBotTop ℝ) * Function.toWithBotTop (weakAffine j) x)
              = ∑ j : Fin (Fintype.card weakType), ((wg j * weakAffine j x : ℝ) : WithBotTop ℝ) := by
                  refine Finset.sum_congr rfl ?_
                  intro j _
                  exact hweak_term j
          _ = ((∑ j : Fin (Fintype.card weakType), wg j * weakAffine j x : ℝ) : WithBotTop ℝ) := by
                simpa using withBotTop_sum_coe (f := fun j : Fin (Fintype.card weakType) ↦
                  wg j * weakAffine j x)
      have hxWithBotTop' :
          ((0 : ℝ) : WithBotTop ℝ) ≤
            (((∑ i : Fin (Fintype.card strictType), wf i * strictAffine i x) +
              ∑ j : Fin (Fintype.card weakType), wg j * weakAffine j x : ℝ) : WithBotTop ℝ) := by
        calc
          ((0 : ℝ) : WithBotTop ℝ)
              ≤ (∑ i : Fin (Fintype.card strictType), (wf i : WithBotTop ℝ) * strictFun i x) +
                ∑ j : Fin (Fintype.card weakType), (wg j : WithBotTop ℝ) *
                  Function.toWithBotTop (weakAffine j) x := by
                  simpa using hxWithBotTop
          _ = ((∑ i : Fin (Fintype.card strictType), wf i * strictAffine i x : ℝ) : WithBotTop ℝ) +
                ((∑ j : Fin (Fintype.card weakType), wg j * weakAffine j x : ℝ) : WithBotTop ℝ) := by
                  rw [hstrict_sum_coe, hweak_sum_coe]
          _ = (((∑ i : Fin (Fintype.card strictType), wf i * strictAffine i x) +
                ∑ j : Fin (Fintype.card weakType), wg j * weakAffine j x : ℝ) : WithBotTop ℝ) := by
                  simpa using withBotTop_coe_add
                    (∑ i : Fin (Fintype.card strictType), wf i * strictAffine i x)
                    (∑ j : Fin (Fintype.card weakType), wg j * weakAffine j x)
      have hxReal :
          (0 : ℝ) ≤
            ∑ i : Fin (Fintype.card strictType), wf i * strictAffine i x +
              ∑ j : Fin (Fintype.card weakType), wg j * weakAffine j x := by
        exact (WithBotTop.coe_le_coe).1 hxWithBotTop'
      have hstrict_sum :
          ∑ i : Fin (Fintype.card strictType), wf i * strictAffine i x =
            (∑ i : Fin (Fintype.card strictType), wf i • a (eStrict.symm i)) x -
              ∑ i : Fin (Fintype.card strictType), wf i * α (eStrict.symm i) := by
        calc
          ∑ i : Fin (Fintype.card strictType), wf i * strictAffine i x
              = ∑ i : Fin (Fintype.card strictType), wf i * (a (eStrict.symm i) x - α (eStrict.symm i)) := by
                  refine Finset.sum_congr rfl ?_
                  intro i _
                  have hi : strictAffine i x = a (eStrict.symm i) x - α (eStrict.symm i) := by
                    simp [strictAffine, sub_eq_add_neg]
                  rw [hi]
          _ = ∑ i : Fin (Fintype.card strictType),
                (wf i * a (eStrict.symm i) x - wf i * α (eStrict.symm i)) := by
                  refine Finset.sum_congr rfl ?_
                  intro i _
                  ring
          _ = (∑ i : Fin (Fintype.card strictType), wf i * a (eStrict.symm i) x) -
                ∑ i : Fin (Fintype.card strictType), wf i * α (eStrict.symm i) := by
                  rw [Finset.sum_sub_distrib]
          _ = (∑ i : Fin (Fintype.card strictType), (wf i • a (eStrict.symm i)) x) -
                ∑ i : Fin (Fintype.card strictType), wf i * α (eStrict.symm i) := by
                  simp
          _ = (∑ i : Fin (Fintype.card strictType), wf i • a (eStrict.symm i)) x -
                ∑ i : Fin (Fintype.card strictType), wf i * α (eStrict.symm i) := by
                  simp
      have hweak_sum :
          ∑ j : Fin (Fintype.card weakType), wg j * weakAffine j x =
            (∑ j : Fin (Fintype.card weakType), wg j • a (eWeak.symm j)) x -
              ∑ j : Fin (Fintype.card weakType), wg j * α (eWeak.symm j) := by
        calc
          ∑ j : Fin (Fintype.card weakType), wg j * weakAffine j x
              = ∑ j : Fin (Fintype.card weakType), wg j * (a (eWeak.symm j) x - α (eWeak.symm j)) := by
                  refine Finset.sum_congr rfl ?_
                  intro j _
                  have hj : weakAffine j x = a (eWeak.symm j) x - α (eWeak.symm j) := by
                    simp [weakAffine, sub_eq_add_neg]
                  rw [hj]
          _ = ∑ j : Fin (Fintype.card weakType),
                (wg j * a (eWeak.symm j) x - wg j * α (eWeak.symm j)) := by
                  refine Finset.sum_congr rfl ?_
                  intro j _
                  ring
          _ = (∑ j : Fin (Fintype.card weakType), wg j * a (eWeak.symm j) x) -
                ∑ j : Fin (Fintype.card weakType), wg j * α (eWeak.symm j) := by
                  rw [Finset.sum_sub_distrib]
          _ = (∑ j : Fin (Fintype.card weakType), (wg j • a (eWeak.symm j)) x) -
                ∑ j : Fin (Fintype.card weakType), wg j * α (eWeak.symm j) := by
                  simp
          _ = (∑ j : Fin (Fintype.card weakType), wg j • a (eWeak.symm j)) x -
                ∑ j : Fin (Fintype.card weakType), wg j * α (eWeak.symm j) := by
                  simp
      have hxRewrite :
          (∑ i : Fin (Fintype.card strictType), wf i * strictAffine i x +
            ∑ j : Fin (Fintype.card weakType), wg j * weakAffine j x) = sFun x - c := by
        rw [hstrict_sum, hweak_sum]
        simp [sFun, c]
        ring
      simpa [hxRewrite] using hxReal

    have hsFun : sFun = 0 := by
      by_contra hsFun
      have hs_eval : ∃ x0 : E, sFun x0 ≠ 0 := by
        by_contra hs_eval
        apply hsFun
        ext x
        have hxzero : sFun x = 0 := by
          by_contra hx
          exact hs_eval ⟨x, hx⟩
        exact hxzero
      rcases hs_eval with ⟨x0, hx0⟩
      let t : ℝ := (c - 1) / sFun x0
      have hbad := hbound (t • x0)
      have ht : sFun (t • x0) - c = -1 := by
        calc
          sFun (t • x0) - c = t * sFun x0 - c := by simp
          _ = ((c - 1) / sFun x0) * sFun x0 - c := by simp [t]
          _ = -1 := by
                field_simp [hx0]
                ring
      rw [ht] at hbad
      linarith

    have hc : c ≤ 0 := by
      have h0 := hbound (0 : E)
      have h0' : 0 ≤ -c := by
        simpa [sFun, hsFun] using h0
      exact neg_nonneg.mp h0'

    have hstrict_lin_equiv :
        (∑ s : strictType, wfStrict s • a s) =
          ∑ i : Fin (Fintype.card strictType), wf i • a (eStrict.symm i) := by
      refine Fintype.sum_equiv eStrict
        (fun s : strictType ↦ wfStrict s • a s)
        (fun i : Fin (Fintype.card strictType) ↦ wf i • a (eStrict.symm i))
        ?_
      intro s
      dsimp [wfStrict]
      exact congrArg (fun t : strictType ↦ wf (eStrict s) • a t.1) (eStrict.left_inv s).symm
    have hweak_lin_equiv :
        (∑ t : weakType, wgWeak t • a t) =
          ∑ j : Fin (Fintype.card weakType), wg j • a (eWeak.symm j) := by
      refine Fintype.sum_equiv eWeak
        (fun t : weakType ↦ wgWeak t • a t)
        (fun j : Fin (Fintype.card weakType) ↦ wg j • a (eWeak.symm j))
        ?_
      intro t
      dsimp [wgWeak]
      exact congrArg (fun u : weakType ↦ wg (eWeak t) • a u.1) (eWeak.left_inv t).symm
    have hstrict_scalar_equiv :
        (∑ s : strictType, wfStrict s * α s) =
          ∑ i : Fin (Fintype.card strictType), wf i * α (eStrict.symm i) := by
      refine Fintype.sum_equiv eStrict
        (fun s : strictType ↦ wfStrict s * α s)
        (fun i : Fin (Fintype.card strictType) ↦ wf i * α (eStrict.symm i))
        ?_
      intro s
      dsimp [wfStrict]
      exact congrArg (fun t : strictType ↦ wf (eStrict s) * α t.1) (eStrict.left_inv s).symm
    have hweak_scalar_equiv :
        (∑ t : weakType, wgWeak t * α t) =
          ∑ j : Fin (Fintype.card weakType), wg j * α (eWeak.symm j) := by
      refine Fintype.sum_equiv eWeak
        (fun t : weakType ↦ wgWeak t * α t)
        (fun j : Fin (Fintype.card weakType) ↦ wg j * α (eWeak.symm j))
        ?_
      intro t
      dsimp [wgWeak]
      exact congrArg (fun u : weakType ↦ wg (eWeak t) * α u.1) (eWeak.left_inv t).symm

    have hsSubtype :
        (∑ s : strictType, wfStrict s • a s) +
            ∑ t : weakType, wgWeak t • a t = 0 := by
      have hsFin :
          (∑ i : Fin (Fintype.card strictType), wf i • a (eStrict.symm i)) +
              ∑ j : Fin (Fintype.card weakType), wg j • a (eWeak.symm j) = 0 := by
        change sFun = 0
        exact hsFun
      calc
        (∑ s : strictType, wfStrict s • a s) +
            ∑ t : weakType, wgWeak t • a t
            = (∑ i : Fin (Fintype.card strictType), wf i • a (eStrict.symm i)) +
                ∑ j : Fin (Fintype.card weakType), wg j • a (eWeak.symm j) := by
                  rw [hstrict_lin_equiv, hweak_lin_equiv]
        _ = 0 := hsFin
    have hcSubtype :
        (∑ s : strictType, wfStrict s * α s) +
            ∑ t : weakType, wgWeak t * α t ≤ 0 := by
      calc
        (∑ s : strictType, wfStrict s * α s) +
            ∑ t : weakType, wgWeak t * α t
            = (∑ i : Fin (Fintype.card strictType), wf i * α (eStrict.symm i)) +
                ∑ j : Fin (Fintype.card weakType), wg j * α (eWeak.symm j) := by
                  rw [hstrict_scalar_equiv, hweak_scalar_equiv]
        _ = c := by rfl
        _ ≤ 0 := hc

    have hw_nonneg : ∀ i : I, 0 ≤ w i := by
      intro i
      by_cases hi : i ∈ strictIndices
      · have hwi : w i = wf (eStrict ⟨i, hi⟩) := by
          simp [w, wfStrict, hi]
        rw [hwi]
        exact hwf_nonneg (eStrict ⟨i, hi⟩)
      · have hwi : w i = wg (eWeak ⟨i, hi⟩) := by
          simp [w, wgWeak, hi]
        rw [hwi]
        exact hwg_nonneg (eWeak ⟨i, hi⟩)
    have hw_pos : ∃ i : I, i ∈ strictIndices ∧ 0 < w i := by
      rcases hwf_nonzero with ⟨i0, hi0⟩
      have hnonneg0 : 0 ≤ wf i0 := hwf_nonneg i0
      have hpos0 : 0 < wf i0 := lt_of_le_of_ne hnonneg0 (Ne.symm hi0)
      refine ⟨(eStrict.symm i0).1, (eStrict.symm i0).2, ?_⟩
      simp [w, wfStrict, hpos0]

    let eSplit : I ≃ (strictType ⊕ weakType) :=
      (Equiv.sumCompl (fun i : I ↦ i ∈ strictIndices)).symm
    have hw_sum_decomp :
        (∑ i : I, w i • a i) =
          (∑ s : strictType, wfStrict s • a s) +
            ∑ t : weakType, wgWeak t • a t := by
      have htmp :
          (∑ i : I, w i • a i) =
            (∑ u : strictType ⊕ weakType,
              (Sum.elim wfStrict wgWeak u) • a (eSplit.symm u)) := by
        exact Fintype.sum_equiv eSplit
          (fun i : I ↦ w i • a i)
          (fun u : strictType ⊕ weakType ↦ (Sum.elim wfStrict wgWeak u) • a (eSplit.symm u))
          (by
            intro i
            have hcoeff : w i = Sum.elim wfStrict wgWeak (eSplit i) := by
              by_cases hi : i ∈ strictIndices
              · have hsplit : eSplit i = Sum.inl ⟨i, hi⟩ := by
                  simpa [eSplit] using
                    (Equiv.sumCompl_symm_apply_of_pos
                      (p := fun i : I ↦ i ∈ strictIndices) hi)
                calc
                  w i = wfStrict ⟨i, hi⟩ := by simp [w, hi]
                  _ = Sum.elim wfStrict wgWeak (Sum.inl ⟨i, hi⟩) := rfl
                  _ = Sum.elim wfStrict wgWeak (eSplit i) := by rw [hsplit]
              · have hsplit : eSplit i = Sum.inr ⟨i, hi⟩ := by
                  simpa [eSplit] using
                    (Equiv.sumCompl_symm_apply_of_neg
                      (p := fun i : I ↦ i ∈ strictIndices) hi)
                calc
                  w i = wgWeak ⟨i, hi⟩ := by simp [w, hi]
                  _ = Sum.elim wfStrict wgWeak (Sum.inr ⟨i, hi⟩) := rfl
                  _ = Sum.elim wfStrict wgWeak (eSplit i) := by rw [hsplit]
            calc
              w i • a i = (Sum.elim wfStrict wgWeak (eSplit i)) • a i := by rw [hcoeff]
              _ = (Sum.elim wfStrict wgWeak (eSplit i)) • a (eSplit.symm (eSplit i)) := by
                    rw [eSplit.symm_apply_apply])
      calc
        (∑ i : I, w i • a i)
            = (∑ u : strictType ⊕ weakType,
                (Sum.elim wfStrict wgWeak u) • a (eSplit.symm u)) := htmp
        _ = (∑ s : strictType, wfStrict s • a s) +
              ∑ t : weakType, wgWeak t • a t := by
              rw [Fintype.sum_sum_type]
              have hsumStrict :
                  (∑ x : strictType,
                    (Sum.elim wfStrict wgWeak (Sum.inl x)) • a (eSplit.symm (Sum.inl x))) =
                    ∑ s : strictType, wfStrict s • a s := by
                refine Finset.sum_congr rfl ?_
                intro s hs
                have hs' : eSplit.symm (Sum.inl s) = s := by
                  change (Equiv.sumCompl (fun i : I ↦ i ∈ strictIndices)) (Sum.inl s) = (s : I)
                  exact Equiv.sumCompl_apply_inl (p := fun i : I ↦ i ∈ strictIndices) s
                rw [hs']
                rfl
              have hsumWeak :
                  (∑ x : weakType,
                    (Sum.elim wfStrict wgWeak (Sum.inr x)) • a (eSplit.symm (Sum.inr x))) =
                    ∑ t : weakType, wgWeak t • a t := by
                refine Finset.sum_congr rfl ?_
                intro t ht
                have ht' : eSplit.symm (Sum.inr t) = t := by
                  change (Equiv.sumCompl (fun i : I ↦ i ∈ strictIndices)) (Sum.inr t) = (t : I)
                  exact Equiv.sumCompl_apply_inr (p := fun i : I ↦ i ∈ strictIndices) t
                rw [ht']
                rfl
              rw [hsumStrict, hsumWeak]

    have hw_scalar_decomp :
        (∑ i : I, w i * α i) =
          (∑ s : strictType, wfStrict s * α s) +
            ∑ t : weakType, wgWeak t * α t := by
      have htmp :
          (∑ i : I, w i * α i) =
            (∑ u : strictType ⊕ weakType,
              (Sum.elim wfStrict wgWeak u) * α (eSplit.symm u)) := by
        exact Fintype.sum_equiv eSplit
          (fun i : I ↦ w i * α i)
          (fun u : strictType ⊕ weakType ↦ (Sum.elim wfStrict wgWeak u) * α (eSplit.symm u))
          (by
            intro i
            have hcoeff : w i = Sum.elim wfStrict wgWeak (eSplit i) := by
              by_cases hi : i ∈ strictIndices
              · have hsplit : eSplit i = Sum.inl ⟨i, hi⟩ := by
                  simpa [eSplit] using
                    (Equiv.sumCompl_symm_apply_of_pos
                      (p := fun i : I ↦ i ∈ strictIndices) hi)
                calc
                  w i = wfStrict ⟨i, hi⟩ := by simp [w, hi]
                  _ = Sum.elim wfStrict wgWeak (Sum.inl ⟨i, hi⟩) := rfl
                  _ = Sum.elim wfStrict wgWeak (eSplit i) := by rw [hsplit]
              · have hsplit : eSplit i = Sum.inr ⟨i, hi⟩ := by
                  simpa [eSplit] using
                    (Equiv.sumCompl_symm_apply_of_neg
                      (p := fun i : I ↦ i ∈ strictIndices) hi)
                calc
                  w i = wgWeak ⟨i, hi⟩ := by simp [w, hi]
                  _ = Sum.elim wfStrict wgWeak (Sum.inr ⟨i, hi⟩) := rfl
                  _ = Sum.elim wfStrict wgWeak (eSplit i) := by rw [hsplit]
            calc
              w i * α i = (Sum.elim wfStrict wgWeak (eSplit i)) * α i := by rw [hcoeff]
              _ = (Sum.elim wfStrict wgWeak (eSplit i)) * α (eSplit.symm (eSplit i)) := by
                    rw [eSplit.symm_apply_apply])
      calc
        (∑ i : I, w i * α i)
            = (∑ u : strictType ⊕ weakType,
                (Sum.elim wfStrict wgWeak u) * α (eSplit.symm u)) := htmp
        _ = (∑ s : strictType, wfStrict s * α s) +
              ∑ t : weakType, wgWeak t * α t := by
              rw [Fintype.sum_sum_type]
              have hsumStrict :
                  (∑ x : strictType,
                    (Sum.elim wfStrict wgWeak (Sum.inl x)) * α (eSplit.symm (Sum.inl x))) =
                    ∑ s : strictType, wfStrict s * α s := by
                refine Finset.sum_congr rfl ?_
                intro s hs
                have hs' : eSplit.symm (Sum.inl s) = s := by
                  change (Equiv.sumCompl (fun i : I ↦ i ∈ strictIndices)) (Sum.inl s) = (s : I)
                  exact Equiv.sumCompl_apply_inl (p := fun i : I ↦ i ∈ strictIndices) s
                rw [hs']
                rfl
              have hsumWeak :
                  (∑ x : weakType,
                    (Sum.elim wfStrict wgWeak (Sum.inr x)) * α (eSplit.symm (Sum.inr x))) =
                    ∑ t : weakType, wgWeak t * α t := by
                refine Finset.sum_congr rfl ?_
                intro t ht
                have ht' : eSplit.symm (Sum.inr t) = t := by
                  change (Equiv.sumCompl (fun i : I ↦ i ∈ strictIndices)) (Sum.inr t) = (t : I)
                  exact Equiv.sumCompl_apply_inr (p := fun i : I ↦ i ∈ strictIndices) t
                rw [ht']
                rfl
              rw [hsumStrict, hsumWeak]

    have hw_sum_zero : ∑ i : I, w i • a i = 0 := by
      rw [hw_sum_decomp]
      exact hsSubtype
    have hw_scalar_le : ∑ i : I, w i * α i ≤ 0 := by
      rw [hw_scalar_decomp]
      exact hcSubtype

    refine ⟨?_, ?_⟩
    · refine ⟨w, hw_nonneg, hw_pos, ?_, ?_⟩
      · exact hw_sum_zero
      · exact hw_scalar_le
    · intro hfeas
      have hfeas' :
          ∃ x : E,
            (∀ i : I, i ∈ strictIndices → a i x < α i) ∧
              (∀ i : I, i ∉ strictIndices → a i x ≤ α i) :=
        (ltOn_pairing_constraint_solution_set_nonempty_iff
          (E := E) (Y := E →ₗ[ℝ] ℝ) (R := ℝ) (I := I) strictIndices a α).1 hfeas
      exact hfeasible_not_certificate hfeas' ⟨w, hw_nonneg, hw_pos, hw_sum_zero, hw_scalar_le⟩

end LinearFunctionalCore

section PairingFunctionalBridge

variable {E : Type*} {Y : Type*}
variable [TopologicalSpace E] [AddCommGroup E] [TopologicalAddGroup E]
variable [Module ℝ E] [ContinuousSMul ℝ E] [FiniteDimensional ℝ E]
variable [AddCommMonoid Y] [Module ℝ Y] [HasLinearPairing E Y ℝ]
variable {I : Type*} [Fintype I]

local notation "solutionSet[" strictIndices "; " a ", " α "]" =>
  (feasibleSet (ltOn strictIndices) a α : Set E)
local notation "weakSet[" strictIndices "; " a ", " α "]" =>
  (LinearConstraintRelation.leFeasible
    (X := E)
    (fun i : {i : I // i ∉ strictIndices} ↦ a i)
    (fun i : {i : I // i ∉ strictIndices} ↦ α i) : Set E)

/-- Pairing-owner form of Theorem 22.2 with owner-side weak-block consistency:
if `weakSet[strictIndices; a, α]` is nonempty, then exactly one of the following alternatives
holds: either the mixed owner feasible set `solutionSet[strictIndices; a, α]` is nonempty, or
there is a
nonnegative multiplier family with a positive coefficient on `strictIndices`, whose weighted
pairing sum vanishes pointwise and whose weighted scalar sum is nonpositive. -/
theorem
    xor_ltOn_pairing_constraint_solution_set_nonempty_or_nonnegative_multiplier_certificate_of_weakFeasible
    (strictIndices : Set I) (a : I → Y) (α : I → ℝ)
    (hweak : (weakSet[strictIndices; a, α]).Nonempty) :
    Xor'
      (solutionSet[strictIndices; a, α]).Nonempty
      (∃ w : I → ℝ,
        (∀ i : I, 0 ≤ w i) ∧
        (∃ i : I, i ∈ strictIndices ∧ 0 < w i) ∧
        (∀ x : E, ∑ i : I, w i * ⟪x, a i⟫ₚ = 0) ∧
        (∑ i : I, w i * α i ≤ 0)) := by
  have hconsistent : ∃ x : E, ∀ i : I, i ∉ strictIndices → ⟪x, a i⟫ₚ ≤ α i :=
    (weak_pairing_constraint_complement_solution_set_nonempty_iff
      (E := E) (Y := Y) (R := ℝ) (I := I) strictIndices a α).1 hweak
  let aLin : I → E →ₗ[ℝ] ℝ :=
    fun i ↦ (HasLinearPairing.pairingLinear (𝕜 := ℝ) (X := E) (Y := Y)).flip (a i)
  have hconsistentLin : ∃ x : E, ∀ i : I, i ∉ strictIndices → aLin i x ≤ α i := by
    rcases hconsistent with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro i hi
    simpa [aLin, HasLinearPairing.pairing_eq_pairingLinear] using hx i hi
  have hmain :
      Xor'
        (solutionSet[strictIndices; aLin, α]).Nonempty
        (∃ w : I → ℝ,
          (∀ i : I, 0 ≤ w i) ∧
          (∃ i : I, i ∈ strictIndices ∧ 0 < w i) ∧
          (∑ i : I, w i • aLin i = 0) ∧
          (∑ i : I, w i * α i ≤ 0)) :=
    xor_ltOn_linear_constraint_solution_set_nonempty_or_nonnegative_multiplier_certificate_core
      (E := E) (I := I) strictIndices aLin α hconsistentLin
  have hsolution :
      (solutionSet[strictIndices; aLin, α]).Nonempty ↔
        (solutionSet[strictIndices; a, α]).Nonempty := by
    constructor
    · intro h
      rcases (ltOn_pairing_constraint_solution_set_nonempty_iff
        (E := E) (Y := E →ₗ[ℝ] ℝ) (R := ℝ) (I := I) strictIndices aLin α).1 h with
        ⟨x, hxstrict, hxweak⟩
      refine (ltOn_pairing_constraint_solution_set_nonempty_iff
        (E := E) (Y := Y) (R := ℝ) (I := I) strictIndices a α).2 ?_
      refine ⟨x, ?_, ?_⟩
      · intro i hi
        simpa [aLin, HasLinearPairing.pairing_eq_pairingLinear] using hxstrict i hi
      · intro i hi
        simpa [aLin, HasLinearPairing.pairing_eq_pairingLinear] using hxweak i hi
    · intro h
      rcases (ltOn_pairing_constraint_solution_set_nonempty_iff
        (E := E) (Y := Y) (R := ℝ) (I := I) strictIndices a α).1 h with
        ⟨x, hxstrict, hxweak⟩
      refine (ltOn_pairing_constraint_solution_set_nonempty_iff
        (E := E) (Y := E →ₗ[ℝ] ℝ) (R := ℝ) (I := I) strictIndices aLin α).2 ?_
      refine ⟨x, ?_, ?_⟩
      · intro i hi
        simpa [aLin, HasLinearPairing.pairing_eq_pairingLinear] using hxstrict i hi
      · intro i hi
        simpa [aLin, HasLinearPairing.pairing_eq_pairingLinear] using hxweak i hi
  have hcertificate :
      (∃ w : I → ℝ,
        (∀ i : I, 0 ≤ w i) ∧
        (∃ i : I, i ∈ strictIndices ∧ 0 < w i) ∧
        (∑ i : I, w i • aLin i = 0) ∧
        (∑ i : I, w i * α i ≤ 0)) ↔
      (∃ w : I → ℝ,
        (∀ i : I, 0 ≤ w i) ∧
        (∃ i : I, i ∈ strictIndices ∧ 0 < w i) ∧
        (∀ x : E, ∑ i : I, w i * ⟪x, a i⟫ₚ = 0) ∧
        (∑ i : I, w i * α i ≤ 0)) := by
    constructor
    · rintro ⟨w, hw_nonneg, hw_pos, hw_sum, hw_scalar⟩
      refine ⟨w, hw_nonneg, hw_pos, ?_, hw_scalar⟩
      intro x
      have hw_sum_x : (∑ i : I, w i • aLin i) x = 0 := by
        simpa using congrArg (fun b : E →ₗ[ℝ] ℝ ↦ b x) hw_sum
      simpa [aLin, HasLinearPairing.pairing_eq_pairingLinear, smul_eq_mul] using hw_sum_x
    · rintro ⟨w, hw_nonneg, hw_pos, hw_sum, hw_scalar⟩
      refine ⟨w, hw_nonneg, hw_pos, ?_, hw_scalar⟩
      ext x
      have hw_sum_x : ∑ i : I, w i * ⟪x, a i⟫ₚ = 0 := hw_sum x
      simpa [aLin, HasLinearPairing.pairing_eq_pairingLinear, smul_eq_mul] using hw_sum_x
  simpa [Xor', hsolution, hcertificate] using hmain

/-- Source-facing restatement of the pairing-owner theorem:
the weak-block pointwise consistency hypothesis is exactly the owner nonemptiness of
`weakSet[strictIndices; a, α]`. -/
theorem
    xor_ltOn_pairing_constraint_solution_set_nonempty_or_nonnegative_multiplier_certificate
    (strictIndices : Set I) (a : I → Y) (α : I → ℝ)
    (hconsistent : ∃ x : E, ∀ i : I, i ∉ strictIndices → ⟪x, a i⟫ₚ ≤ α i) :
    Xor'
      (solutionSet[strictIndices; a, α]).Nonempty
      (∃ w : I → ℝ,
        (∀ i : I, 0 ≤ w i) ∧
        (∃ i : I, i ∈ strictIndices ∧ 0 < w i) ∧
        (∀ x : E, ∑ i : I, w i * ⟪x, a i⟫ₚ = 0) ∧
        (∑ i : I, w i * α i ≤ 0)) := by
  exact xor_ltOn_pairing_constraint_solution_set_nonempty_or_nonnegative_multiplier_certificate_of_weakFeasible
    (E := E) (Y := Y) (I := I) strictIndices a α
    ((weak_pairing_constraint_complement_solution_set_nonempty_iff
      (E := E) (Y := Y) (R := ℝ) (I := I) strictIndices a α).2 hconsistent)

end PairingFunctionalBridge

section FunctionalBridge

variable {E : Type*}
variable [TopologicalSpace E] [AddCommGroup E] [TopologicalAddGroup E]
variable [Module ℝ E] [ContinuousSMul ℝ E] [FiniteDimensional ℝ E]
variable {I : Type*} [Fintype I]

local notation "solutionSet[" strictIndices "; " a ", " α "]" =>
  (feasibleSet (ltOn strictIndices) a α : Set E)
local notation "weakSet[" strictIndices "; " a ", " α "]" =>
  (LinearConstraintRelation.leFeasible
    (X := E)
    (fun i : {i : I // i ∉ strictIndices} ↦ a i)
    (fun i : {i : I // i ∉ strictIndices} ↦ α i) : Set E)

/-- Linear-functional owner-side bridge specialization of Theorem 22.2:
the weak-block owner `weakSet[strictIndices; a, α]` is the canonical consistency hypothesis. -/
theorem
    xor_ltOn_linear_constraint_solution_set_nonempty_or_nonnegative_multiplier_certificate_of_weakFeasible
    (strictIndices : Set I) (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ)
    (hweak : (weakSet[strictIndices; a, α]).Nonempty) :
    Xor'
      (solutionSet[strictIndices; a, α]).Nonempty
      (∃ w : I → ℝ,
        (∀ i : I, 0 ≤ w i) ∧
        (∃ i : I, i ∈ strictIndices ∧ 0 < w i) ∧
        (∑ i : I, w i • a i = 0) ∧
        (∑ i : I, w i * α i ≤ 0)) := by
  let qPair : Prop :=
    ∃ w : I → ℝ,
      (∀ i : I, 0 ≤ w i) ∧
      (∃ i : I, i ∈ strictIndices ∧ 0 < w i) ∧
      (∀ x : E, ∑ i : I, w i * ⟪x, a i⟫ₚ = 0) ∧
      (∑ i : I, w i * α i ≤ 0)
  let qLin : Prop :=
    ∃ w : I → ℝ,
      (∀ i : I, 0 ≤ w i) ∧
      (∃ i : I, i ∈ strictIndices ∧ 0 < w i) ∧
      (∑ i : I, w i • a i = 0) ∧
      (∑ i : I, w i * α i ≤ 0)
  have hmain : Xor' (solutionSet[strictIndices; a, α]).Nonempty qPair := by
    simpa [qPair] using
      (xor_ltOn_pairing_constraint_solution_set_nonempty_or_nonnegative_multiplier_certificate_of_weakFeasible
        (E := E) (Y := E →ₗ[ℝ] ℝ) (I := I) strictIndices a α hweak)
  have hcertificate : qPair ↔ qLin := by
    dsimp [qPair, qLin]
    constructor
    · rintro ⟨w, hw_nonneg, hw_pos, hw_sum, hw_scalar⟩
      refine ⟨w, hw_nonneg, hw_pos, ?_, hw_scalar⟩
      ext x
      have hw_sum_x : ∑ i : I, w i * ⟪x, a i⟫ₚ = 0 := hw_sum x
      simpa [smul_eq_mul] using hw_sum_x
    · rintro ⟨w, hw_nonneg, hw_pos, hw_sum, hw_scalar⟩
      refine ⟨w, hw_nonneg, hw_pos, ?_, hw_scalar⟩
      intro x
      have hw_sum_x : (∑ i : I, w i • a i) x = 0 := by
        simpa using congrArg (fun b : E →ₗ[ℝ] ℝ ↦ b x) hw_sum
      simpa [smul_eq_mul] using hw_sum_x
  have hnotiff : ¬ ((solutionSet[strictIndices; a, α]).Nonempty ↔ qLin) := by
    intro hiff
    have hnotPair : ¬ ((solutionSet[strictIndices; a, α]).Nonempty ↔ qPair) :=
      (xor_iff_not_iff _ _).1 hmain
    exact hnotPair (hiff.trans hcertificate.symm)
  exact (xor_iff_not_iff _ _).2 hnotiff

/-- Linear-functional bridge specialization of the pairing-owner Theorem 22.2 alternative. -/
theorem
    xor_ltOn_linear_constraint_solution_set_nonempty_or_nonnegative_multiplier_certificate
    (strictIndices : Set I) (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ)
    (hconsistent : ∃ x : E, ∀ i : I, i ∉ strictIndices → a i x ≤ α i) :
    Xor'
      (solutionSet[strictIndices; a, α]).Nonempty
      (∃ w : I → ℝ,
        (∀ i : I, 0 ≤ w i) ∧
        (∃ i : I, i ∈ strictIndices ∧ 0 < w i) ∧
        (∑ i : I, w i • a i = 0) ∧
        (∑ i : I, w i * α i ≤ 0)) := by
  have hconsistentPair : ∃ x : E, ∀ i : I, i ∉ strictIndices → ⟪x, a i⟫ₚ ≤ α i := by
    rcases hconsistent with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro i hi
    simpa using hx i hi
  have hweak :
      (weakSet[strictIndices; a, α]).Nonempty :=
    (weak_pairing_constraint_complement_solution_set_nonempty_iff
      (E := E) (Y := E →ₗ[ℝ] ℝ) (R := ℝ) (I := I) strictIndices a α).2 hconsistentPair
  exact
    xor_ltOn_linear_constraint_solution_set_nonempty_or_nonnegative_multiplier_certificate_of_weakFeasible
      (E := E) (I := I) strictIndices a α hweak

end FunctionalBridge

section CutIndexPairingOwner

variable {E : Type*} {Y : Type*}
variable [TopologicalSpace E] [AddCommGroup E] [TopologicalAddGroup E]
variable [Module ℝ E] [ContinuousSMul ℝ E] [FiniteDimensional ℝ E]
variable [AddCommMonoid Y] [Module ℝ Y] [HasLinearPairing E Y ℝ]
variable {m : ℕ}

local notation "solutionSet[" k "; " a ", " α "]" =>
  (feasibleSet (ltOn (strictCutIndices (m := m) k)) a α : Set E)

/-- Cut-index pairing-owner specialization of Theorem 22.2. -/
theorem
    xor_strict_weak_pairing_constraint_solution_set_nonempty_or_nonnegative_multiplier_certificate
    (k : ℕ) (a : Fin m → Y) (α : Fin m → ℝ)
    (hconsistent : ∃ x : E, ∀ i : Fin m, k ≤ i.1 → ⟪x, a i⟫ₚ ≤ α i) :
    Xor'
      (solutionSet[k; a, α]).Nonempty
      (∃ w : Fin m → ℝ,
        (∀ i : Fin m, 0 ≤ w i) ∧
        (∃ i : Fin m, i.1 < k ∧ 0 < w i) ∧
        (∀ x : E, ∑ i : Fin m, w i * ⟪x, a i⟫ₚ = 0) ∧
        (∑ i : Fin m, w i * α i ≤ 0)) := by
  rcases hconsistent with ⟨x, hx⟩
  have hconsistent_ltOn :
      ∃ x : E, ∀ i : Fin m, i ∉ strictCutIndices (m := m) k → ⟪x, a i⟫ₚ ≤ α i := by
    refine ⟨x, ?_⟩
    intro i hi
    exact hx i (by simpa [strictCutIndices, Set.mem_setOf_eq, not_lt] using hi)
  have hweak_ltOn :
      (LinearConstraintRelation.leFeasible
        (X := E)
        (fun i : {i : Fin m // i ∉ strictCutIndices (m := m) k} ↦ a i)
        (fun i : {i : Fin m // i ∉ strictCutIndices (m := m) k} ↦ α i) : Set E).Nonempty :=
    (weak_pairing_constraint_complement_solution_set_nonempty_iff
      (E := E) (Y := Y) (R := ℝ) (I := Fin m) (strictCutIndices (m := m) k) a α).2
      hconsistent_ltOn
  simpa [strictCutIndices, Set.mem_setOf_eq, not_lt] using
    (xor_ltOn_pairing_constraint_solution_set_nonempty_or_nonnegative_multiplier_certificate_of_weakFeasible
      (E := E) (Y := Y) (I := Fin m) (strictCutIndices (m := m) k) a α hweak_ltOn)

/-- Source-facing pairing restatement of Theorem 22.2 in cut-index form. -/
theorem xor_exists_strict_pairing_feasible_point_or_nonnegative_multiplier_certificate
    (k : ℕ) (a : Fin m → Y) (α : Fin m → ℝ)
    (hconsistent : ∃ x : E, ∀ i : Fin m, k ≤ i.1 → ⟪x, a i⟫ₚ ≤ α i) :
    Xor'
      (∃ x : E,
        (∀ i : Fin m, i.1 < k → ⟪x, a i⟫ₚ < α i) ∧
          ∀ i : Fin m, k ≤ i.1 → ⟪x, a i⟫ₚ ≤ α i)
      (∃ w : Fin m → ℝ,
        (∀ i : Fin m, 0 ≤ w i) ∧
        (∃ i : Fin m, i.1 < k ∧ 0 < w i) ∧
        (∀ x : E, ∑ i : Fin m, w i * ⟪x, a i⟫ₚ = 0) ∧
        (∑ i : Fin m, w i * α i ≤ 0)) := by
  simpa [strict_weak_pairing_constraint_solution_set_nonempty_iff k a α] using
    xor_strict_weak_pairing_constraint_solution_set_nonempty_or_nonnegative_multiplier_certificate
      k a α hconsistent

end CutIndexPairingOwner

section CutIndexFunctionalBridge

variable {E : Type*}
variable [TopologicalSpace E] [AddCommGroup E] [TopologicalAddGroup E]
variable [Module ℝ E] [ContinuousSMul ℝ E] [FiniteDimensional ℝ E]
variable {m : ℕ}

local notation "solutionSet[" k "; " a ", " α "]" =>
  (feasibleSet (ltOn (strictCutIndices (m := m) k)) a α : Set E)
local notation "weakSet[" k "; " a ", " α "]" =>
  (LinearConstraintRelation.leFeasible
    (X := E)
    (fun i : {i : Fin m // i ∉ strictCutIndices (m := m) k} ↦ a i)
    (fun i : {i : Fin m // i ∉ strictCutIndices (m := m) k} ↦ α i) : Set E)

/-- Theorem 22.2 linear-functional cut-index specialization with owner-side weak feasibility
hypothesis. -/
theorem
    xor_strict_weak_linear_constraint_solution_set_nonempty_or_nonnegative_multiplier_certificate_of_weakFeasible
    (k : ℕ) (a : Fin m → E →ₗ[ℝ] ℝ) (α : Fin m → ℝ)
    (hweak : (weakSet[k; a, α]).Nonempty) :
    Xor'
      (solutionSet[k; a, α]).Nonempty
      (∃ w : Fin m → ℝ,
        (∀ i : Fin m, 0 ≤ w i) ∧
        (∃ i : Fin m, i.1 < k ∧ 0 < w i) ∧
        (∑ i : Fin m, w i • a i = 0) ∧
        (∑ i : Fin m, w i * α i ≤ 0)) := by
  simpa [strictCutIndices, Set.mem_setOf_eq, not_lt] using
    (xor_ltOn_linear_constraint_solution_set_nonempty_or_nonnegative_multiplier_certificate_of_weakFeasible
      (E := E) (I := Fin m) (strictCutIndices (m := m) k) a α hweak)

/-- Theorem 22.2 in textbook cut-index owner form, recovered as a specialization of the
set-index owner theorem. -/
theorem
    xor_strict_weak_linear_constraint_solution_set_nonempty_or_nonnegative_multiplier_certificate
    (k : ℕ) (a : Fin m → E →ₗ[ℝ] ℝ) (α : Fin m → ℝ)
    (hconsistent : ∃ x : E, ∀ i : Fin m, k ≤ i.1 → a i x ≤ α i) :
    Xor'
      (solutionSet[k; a, α]).Nonempty
      (∃ w : Fin m → ℝ,
        (∀ i : Fin m, 0 ≤ w i) ∧
        (∃ i : Fin m, i.1 < k ∧ 0 < w i) ∧
        (∑ i : Fin m, w i • a i = 0) ∧
        (∑ i : Fin m, w i * α i ≤ 0)) := by
  have hconsistent_ltOn :
      ∃ x : E, ∀ i : Fin m, i ∉ strictCutIndices (m := m) k → ⟪x, a i⟫ₚ ≤ α i := by
    rcases hconsistent with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro i hi
    exact hx i (by simpa [strictCutIndices, Set.mem_setOf_eq, not_lt] using hi)
  have hweak : (weakSet[k; a, α]).Nonempty :=
    (weak_pairing_constraint_complement_solution_set_nonempty_iff
      (E := E) (Y := E →ₗ[ℝ] ℝ) (R := ℝ) (I := Fin m)
      (strictCutIndices (m := m) k) a α).2 hconsistent_ltOn
  exact
    xor_strict_weak_linear_constraint_solution_set_nonempty_or_nonnegative_multiplier_certificate_of_weakFeasible
      (E := E) (m := m) k a α hweak

/-- Source-facing pointwise restatement of Theorem 22.2. The owner feasible-set alternative is
equivalent to existence of a point satisfying the displayed mixed strict/weak linear system. -/
theorem xor_exists_strict_linear_feasible_point_or_nonnegative_multiplier_certificate
    (k : ℕ) (a : Fin m → E →ₗ[ℝ] ℝ) (α : Fin m → ℝ)
    (hconsistent : ∃ x : E, ∀ i : Fin m, k ≤ i.1 → a i x ≤ α i) :
    Xor'
      (∃ x : E,
        (∀ i : Fin m, i.1 < k → a i x < α i) ∧
          ∀ i : Fin m, k ≤ i.1 → a i x ≤ α i)
      (∃ w : Fin m → ℝ,
        (∀ i : Fin m, 0 ≤ w i) ∧
        (∃ i : Fin m, i.1 < k ∧ 0 < w i) ∧
        (∑ i : Fin m, w i • a i = 0) ∧
        (∑ i : Fin m, w i * α i ≤ 0)) := by
  have hconsistentPair : ∃ x : E, ∀ i : Fin m, k ≤ i.1 → ⟪x, a i⟫ₚ ≤ α i := by
    rcases hconsistent with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro i hi
    simpa using hx i hi
  let pPair : Prop :=
    ∃ x : E,
      (∀ i : Fin m, i.1 < k → ⟪x, a i⟫ₚ < α i) ∧
        ∀ i : Fin m, k ≤ i.1 → ⟪x, a i⟫ₚ ≤ α i
  let pLin : Prop :=
    ∃ x : E,
      (∀ i : Fin m, i.1 < k → a i x < α i) ∧
        ∀ i : Fin m, k ≤ i.1 → a i x ≤ α i
  let qPair : Prop :=
    ∃ w : Fin m → ℝ,
      (∀ i : Fin m, 0 ≤ w i) ∧
      (∃ i : Fin m, i.1 < k ∧ 0 < w i) ∧
      (∀ x : E, ∑ i : Fin m, w i * ⟪x, a i⟫ₚ = 0) ∧
      (∑ i : Fin m, w i * α i ≤ 0)
  let qLin : Prop :=
    ∃ w : Fin m → ℝ,
      (∀ i : Fin m, 0 ≤ w i) ∧
      (∃ i : Fin m, i.1 < k ∧ 0 < w i) ∧
      (∑ i : Fin m, w i • a i = 0) ∧
      (∑ i : Fin m, w i * α i ≤ 0)
  have hmain : Xor' pPair qPair := by
    simpa [pPair, qPair] using
      (xor_exists_strict_pairing_feasible_point_or_nonnegative_multiplier_certificate
        (E := E) (Y := E →ₗ[ℝ] ℝ) k a α hconsistentPair)
  have hp : pPair ↔ pLin := by
    dsimp [pPair, pLin]
    constructor
    · rintro ⟨x, hxstrict, hxweak⟩
      refine ⟨x, ?_, ?_⟩
      · intro i hi
        simpa using hxstrict i hi
      · intro i hi
        simpa using hxweak i hi
    · rintro ⟨x, hxstrict, hxweak⟩
      refine ⟨x, ?_, ?_⟩
      · intro i hi
        simpa using hxstrict i hi
      · intro i hi
        simpa using hxweak i hi
  have hq : qPair ↔ qLin := by
    dsimp [qPair, qLin]
    constructor
    · rintro ⟨w, hw_nonneg, hw_pos, hw_sum, hw_scalar⟩
      refine ⟨w, hw_nonneg, hw_pos, ?_, hw_scalar⟩
      ext x
      have hw_sum_x : ∑ i : Fin m, w i * ⟪x, a i⟫ₚ = 0 := hw_sum x
      simpa [smul_eq_mul] using hw_sum_x
    · rintro ⟨w, hw_nonneg, hw_pos, hw_sum, hw_scalar⟩
      refine ⟨w, hw_nonneg, hw_pos, ?_, hw_scalar⟩
      intro x
      have hw_sum_x : (∑ i : Fin m, w i • a i) x = 0 := by
        simpa using congrArg (fun b : E →ₗ[ℝ] ℝ ↦ b x) hw_sum
      simpa [smul_eq_mul] using hw_sum_x
  have hnotiff : ¬ (pLin ↔ qLin) := by
    intro hiff
    have hnotPair : ¬ (pPair ↔ qPair) := (xor_iff_not_iff _ _).1 hmain
    exact hnotPair ((hp.trans hiff).trans hq.symm)
  exact (xor_iff_not_iff _ _).2 hnotiff

end CutIndexFunctionalBridge
