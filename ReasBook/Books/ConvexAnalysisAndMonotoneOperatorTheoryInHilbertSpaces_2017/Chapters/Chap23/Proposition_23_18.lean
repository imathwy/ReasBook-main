import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap21.Theorem_21_1
import BauschkeLean.Chap23.Definition_23_1

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain-style sampling:
-- - primary domain: maximally monotone set-valued operators on finite Hilbert direct sums
-- - inspected owners:
--   `Maximal` from `Chap20/Definition_20_20.lean`
--   `J[...]` / `resolvent` from `Chap23/Definition_23_1.lean`
--   `ContinuousLinearMap.toLpOperator` from `Chap19/Example_19_3.lean` as the chapter's
--   analogous direct-sum owner for linear data
--   downstream Chapter 26 files, which already reuse `SetValuedOperator.familyOperator` as the
--   owner abstraction
-- Source/core/bridge triage:
-- - `source-facing`: the coordinatewise operator on `lp K 2` and Proposition 23.18's maximality
--   and resolvent formulas
-- - `core/canonical`: `SetValuedOperator.familyOperator` together with `Maximal IsMonotone` and
--   `J[...]`
-- - `bridge/view`: the membership equivalence `mem_familyOperator_iff`

open scoped BigOperators InnerProductSpace Pointwise SetValuedOperator

noncomputable section

universe u v

namespace SetValuedOperator

section FamilyOperator

variable {I : Type v}
variable {K : I → Type u}
variable [∀ i, NormedAddCommGroup (K i)]

/-- The coordinatewise set-valued operator on the finite Hilbert direct sum `lp K 2` attached to
the family `Aᵢ : K i → 2^(K i)`. -/
def familyOperator (A : ∀ i, SetValuedOperator (K i) (K i)) :
    SetValuedOperator (lp K 2) (lp K 2) :=
  fun x ↦ {u | ∀ i, u i ∈ A i (x i)}

/-- Membership in `familyOperator A x` is equivalent to coordinatewise membership in the values
`A i (x i)`. -/
@[simp] theorem mem_familyOperator_iff
    (A : ∀ i, SetValuedOperator (K i) (K i)) (x u : lp K 2) :
    u ∈ familyOperator A x ↔ ∀ i, u i ∈ A i (x i) :=
  Iff.rfl

end FamilyOperator

section Proposition2318

variable {I : Type v} [Finite I]
variable {K : I → Type u}
variable [∀ i, NormedAddCommGroup (K i)]
variable [∀ i, InnerProductSpace ℝ (K i)]
variable [∀ i, CompleteSpace (K i)]

section FiniteFamilyHelpers

variable [Fintype I]

/-- Helper for Proposition 23.18: package a coordinate family `w : ∀ i, K i` as an element of the
finite Hilbert direct sum `lp K 2`. -/
private def lpFamily
    (w : ∀ i, K i) : lp K 2 :=
  (lpPiLpₗᵢ K ℝ).symm (WithLp.toLp 2 w)

/-- Helper for Proposition 23.18: the `i`th coordinate of `lpFamily w` is exactly `w i`. -/
@[simp] private theorem lpFamily_apply
    (w : ∀ i, K i) (i : I) :
    lpFamily w i = w i := by
  -- Unfold the canonical `lp`/`PiLp` bridge once so later coordinate computations are definitionally
  -- stable.
  change ((lpPiLpₗᵢ K ℝ).symm (WithLp.toLp 2 w)) i = w i
  rw [coe_lpPiLpₗᵢ_symm]

/-- Helper for Proposition 23.18: coordinatewise monotonicity of the family `A i` implies
monotonicity of the product-space operator `familyOperator A`. -/
private theorem familyOperator_isMonotone_of_isMonotone
    (A : ∀ i, SetValuedOperator (K i) (K i))
    (hA : ∀ i, (A i).IsMonotone) :
    (familyOperator A).IsMonotone := by
  -- Sum the coordinatewise monotonicity inequalities after transporting the `lp` inner product to
  -- the canonical `PiLp` coordinates.
  rw [SetValuedOperator.isMonotone_iff]
  intro x u y v hu hv
  have hcoord : ∀ i, 0 ≤ ⟪x i - y i, u i - v i⟫_ℝ := by
    intro i
    exact (SetValuedOperator.isMonotone_iff (A i)).1 (hA i) (hu i) (hv i)
  calc
    0 ≤ ∑ i, ⟪(lpPiLpₗᵢ K ℝ (x - y)) i, (lpPiLpₗᵢ K ℝ (u - v)) i⟫_ℝ := by
      refine Finset.sum_nonneg ?_
      intro i hi
      simpa [coe_lpPiLpₗᵢ] using hcoord i
    _ = ⟪lpPiLpₗᵢ K ℝ (x - y), lpPiLpₗᵢ K ℝ (u - v)⟫_ℝ := by
      symm
      rw [PiLp.inner_apply]
    _ = ⟪x - y, u - v⟫_ℝ := by
      exact (lpPiLpₗᵢ K ℝ).inner_map_map (x - y) (u - v)

/-- Helper for Proposition 23.18: if every coordinate operator `A i` is maximally monotone, then
`Id + familyOperator A` has full range. -/
private theorem range_id_add_familyOperator_eq_univ_of_maximal
    (A : ∀ i, SetValuedOperator (K i) (K i))
    (hA : ∀ i, Maximal IsMonotone (A i)) :
    (((id : lp K 2 → lp K 2).toSetValuedOperator) + familyOperator A).range = Set.univ := by
  -- Apply Minty's range characterization coordinatewise, then package the chosen witnesses into a
  -- single `lp` point.
  ext x
  constructor
  · intro hx
    simp
  · intro _
    have hrangeCoord :
        ∀ i, ((id : K i → K i).toSetValuedOperator + A i).range = Set.univ := by
      intro i
      exact (maximal_iff_range_id_add_eq_univ (A i) (Maximal.isMonotone (hA i))).1 (hA i)
    have hcoord :
        ∀ i, ∃ p u : K i, u ∈ A i p ∧ x i = p + u := by
      intro i
      have hxrange : x i ∈ (((id : K i → K i).toSetValuedOperator + A i).range) := by
        simpa [hrangeCoord i]
      rcases
          (SetValuedOperator.mem_range_iff
            (((id : K i → K i).toSetValuedOperator + A i)) (x i)).1 hxrange with
        ⟨p, hp⟩
      change x i ∈ ((id : K i → K i).toSetValuedOperator p + A i p) at hp
      rw [Function.toSetValuedOperator_apply, Set.mem_add] at hp
      rcases hp with ⟨y, hy, u, hu, hyu⟩
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact ⟨p, u, hu, hyu.symm⟩
    classical
    choose p u hu hxu using hcoord
    let pLp : lp K 2 := lpFamily p
    let uLp : lp K 2 := lpFamily u
    refine
      (SetValuedOperator.mem_range_iff
        (((id : lp K 2 → lp K 2).toSetValuedOperator + familyOperator A)) x).2 ?_
    refine ⟨pLp, ?_⟩
    change x ∈ ((id : lp K 2 → lp K 2).toSetValuedOperator pLp + familyOperator A pLp)
    rw [Function.toSetValuedOperator_apply, Set.mem_add]
    refine ⟨pLp, by simp, uLp, ?_, ?_⟩
    · rw [mem_familyOperator_iff]
      intro i
      simpa [uLp, pLp] using hu i
    · ext i
      simpa [pLp, uLp] using (hxu i).symm

end FiniteFamilyHelpers

/-- Proposition 23.18 (1): for a finite family of real Hilbert spaces `K i` and maximally
monotone operators `A i : K i → 2^(K i)`, the coordinatewise operator on the finite Hilbert direct
sum `lp K 2` is maximally monotone. -/
theorem familyOperator_maximal_of_maximal
    (A : ∀ i, SetValuedOperator (K i) (K i))
    (hA : ∀ i, Maximal IsMonotone (A i)) :
    Maximal IsMonotone (familyOperator A) := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  -- Prove maximality through Minty's range criterion for `Id + familyOperator A`.
  refine
    (maximal_iff_range_id_add_eq_univ (familyOperator A) ?_).2
      (range_id_add_familyOperator_eq_univ_of_maximal A hA)
  exact familyOperator_isMonotone_of_isMonotone A (fun i ↦ Maximal.isMonotone (hA i))

end Proposition2318

section ResolventFamilyOperator

variable {I : Type v}
variable {K : I → Type u}
variable [∀ i, NormedAddCommGroup (K i)]

/-- Helper for Proposition 23.18: membership in the resolvent of `familyOperator A` is equivalent
to coordinatewise membership in the resolvents `J[A i]`. -/
private theorem mem_resolvent_familyOperator_iff
    (A : ∀ i, SetValuedOperator (K i) (K i)) (x p : lp K 2) :
    p ∈ J[(familyOperator A)] x ↔ ∀ i, p i ∈ J[(A i)] (x i) := by
  constructor
  · intro hp
    -- Read the `Id + familyOperator A` witness and project it coordinatewise.
    rw [resolvent_def, mem_inverse_iff] at hp
    change x ∈ ((id : lp K 2 → lp K 2).toSetValuedOperator p + familyOperator A p) at hp
    rw [Function.toSetValuedOperator_apply, Set.mem_add] at hp
    rcases hp with ⟨y, hy, u, hu, hyu⟩
    rw [Set.mem_singleton_iff] at hy
    subst y
    intro i
    rw [resolvent_def, mem_inverse_iff]
    change x i ∈ ((id : K i → K i).toSetValuedOperator (p i) + A i (p i))
    rw [Function.toSetValuedOperator_apply, Set.mem_add]
    refine ⟨p i, by simp, u i, hu i, ?_⟩
    exact congrArg (fun z : lp K 2 ↦ z i) hyu
  · intro hp
    -- Assemble the resolvent witness in the product space from the coordinatewise residuals
    -- `x i - p i ∈ A i (p i)`.
    rw [resolvent_def, mem_inverse_iff]
    change x ∈ ((id : lp K 2 → lp K 2).toSetValuedOperator p + familyOperator A p)
    rw [Function.toSetValuedOperator_apply, Set.mem_add]
    refine ⟨p, by simp, x - p, ?_, ?_⟩
    · rw [mem_familyOperator_iff]
      intro i
      have hpi : p i ∈ J[(A i)] (x i) := hp i
      rw [resolvent_def, mem_inverse_iff] at hpi
      change x i ∈ ((id : K i → K i).toSetValuedOperator (p i) + A i (p i)) at hpi
      rw [Function.toSetValuedOperator_apply, Set.mem_add] at hpi
      rcases hpi with ⟨y, hy, u, hu, hyu⟩
      rw [Set.mem_singleton_iff] at hy
      subst y
      have hyu' : p i + u = x i := by
        simpa using hyu
      have hxpu : x i - p i = u := by
        calc
          x i - p i = (p i + u) - p i := by rw [← hyu']
          _ = u := by abel_nf
      have hmem : x i - p i ∈ A i (p i) := by
        simpa [hxpu] using hu
      simpa using hmem
    · ext i
      change p i + (x i - p i) = x i
      abel_nf

/-- Proposition 23.18 (2): the resolvent of the coordinatewise family operator is the
coordinatewise family of the resolvents. This identity is coordinatewise and only uses the
`lp`/`familyOperator` owner together with the Chapter 23 resolvent owner `J[...]`. -/
theorem resolvent_familyOperator_eq_familyOperator_resolvent
    (A : ∀ i, SetValuedOperator (K i) (K i)) :
    J[(familyOperator A)] = familyOperator (fun i ↦ J[(A i)]) := by
  -- Reduce operator equality to the coordinatewise resolvent-membership criterion.
  ext x p
  rw [mem_resolvent_familyOperator_iff A x p, mem_familyOperator_iff]

end ResolventFamilyOperator

end SetValuedOperator
