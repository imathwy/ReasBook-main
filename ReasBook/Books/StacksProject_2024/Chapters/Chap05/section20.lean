import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_20_1 (from Chap05) -/
universe u

open Specialization TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for dimension functions on topological spaces:
- source-facing specialization relation: `Specializes`
- core order owner for immediate steps: `CovBy` on `Specialization X`
- core graded-order owner: `GradeOrder ℤ (Specialization X)`

Layer triage:
- `source-facing`: `IsImmediateSpecialization` and `IsDimensionFunction`
- `core/canonical`: `CovBy` and `GradeOrder` on the specialization order
- `bridge/view`: under `T₀`, immediate specializations are exactly covers in `Specialization X`;
  a dimension function forces `T₀` and canonically grades `Specialization X`

Primitive data is only the strict-decrease and unit-drop axioms. The induced `T₀` separation and
the order-theoretic cover interface are derived API, so they should not be stored as primitive
fields.
-/

/-- A point `y` is an immediate specialization of `x` if `y` is a proper specialization of `x`
and there is no third point strictly between them in the specialization relation. -/
def IsImmediateSpecialization (x y : X) : Prop :=
  x ⤳ y ∧ x ≠ y ∧ ∀ ⦃z : X⦄, x ⤳ z → z ⤳ y → z = x ∨ z = y

theorem IsImmediateSpecialization.specializes {x y : X} (h : IsImmediateSpecialization x y) :
    x ⤳ y :=
  h.1

theorem IsImmediateSpecialization.ne {x y : X} (h : IsImmediateSpecialization x y) :
    x ≠ y :=
  h.2.1

theorem IsImmediateSpecialization.eq_or_eq {x y z : X} (h : IsImmediateSpecialization x y)
    (hxz : x ⤳ z) (hzy : z ⤳ y) : z = x ∨ z = y :=
  h.2.2 hxz hzy

/-- On a `T₀` space, immediate specializations are exactly cover relations in the canonical
specialization order. -/
theorem isImmediateSpecialization_iff_covBy [T0Space X] {x y : X} :
    IsImmediateSpecialization x y ↔ toEquiv y ⋖ toEquiv x := by
  rw [covBy_iff_lt_and_eq_or_eq]
  constructor
  · intro h
    rcases h with ⟨hxy, hne, hmid⟩
    refine ⟨?_, ?_⟩
    · refine ⟨hxy, ?_⟩
      intro hyx
      exact hne ((hxy.antisymm hyx).eq)
    · intro z hyz hzx
      have hxz : x ⤳ ofEquiv z := by
        simpa using hzx
      have hzy : ofEquiv z ⤳ y := by
        simpa using hyz
      simpa [toEquiv_inj, or_comm] using hmid hxz hzy
  · intro h
    refine ⟨h.1.1, ?_, ?_⟩
    · intro hxy
      exact h.1.2 (by simpa [hxy] using (specializes_rfl : x ⤳ x))
    · intro z hxz hzy
      have hyz : toEquiv y ≤ toEquiv z := by
        simpa using hzy
      have hzx : toEquiv z ≤ toEquiv x := by
        simpa using hxz
      simpa [toEquiv_inj, or_comm] using h.2 (toEquiv z) hyz hzx

/-- Definition 5.20.1: a dimension function on a topological space is an integer-valued function
that is strictly decreasing under proper specialization and drops by exactly one along immediate
specializations. -/
class IsDimensionFunction (δ : X → ℤ) : Prop where
  /-- A dimension function strictly decreases along proper specializations. -/
  strict_of_specializes {x y : X} : x ⤳ y → x ≠ y → δ x > δ y
  /-- A dimension function drops by exactly one along immediate specializations. -/
  eq_add_one_of_immediateSpecialization {x y : X} :
    IsImmediateSpecialization x y → δ x = δ y + 1

/-- A dimension function forces the ambient space to be `T₀`: distinct inseparable points would
make the strict specialization inequality run in both directions. -/
theorem IsDimensionFunction.t0Space {δ : X → ℤ} (hδ : IsDimensionFunction δ) : T0Space X := by
  refine ⟨?_⟩
  intro x y hxy
  by_contra hne
  have hgt : δ x > δ y := hδ.strict_of_specializes hxy.specializes hne
  have hlt : δ y > δ x := hδ.strict_of_specializes hxy.specializes' (fun h ↦ hne h.symm)
  exact lt_irrefl _ (lt_trans hgt hlt)

/-- A dimension function canonically upgrades the specialization order to a graded order. -/
@[reducible] protected noncomputable def IsDimensionFunction.gradeOrder {δ : X → ℤ}
    (hδ : IsDimensionFunction δ) : GradeOrder ℤ (Specialization X) :=
  letI : GradeBoundedOrder ℤ ℤ := Preorder.toGradeBoundedOrder
  GradeOrder.liftRight (δ ∘ ofEquiv)
    (by
      intro a b hab
      exact hδ.strict_of_specializes (by simpa using hab.le) (by
        intro h
        exact hab.ne <| by simpa [eq_comm] using h))
    (by
      intro a b hab
      letI : T0Space X := hδ.t0Space
      have himm : IsImmediateSpecialization (ofEquiv b) (ofEquiv a) :=
        (isImmediateSpecialization_iff_covBy).2 <| by simpa using hab
      rw [Order.covBy_iff_add_one_eq]
      simpa [eq_comm] using hδ.eq_add_one_of_immediateSpecialization himm)

/-- On a `T1` space, the constant zero function is a dimension function because there are no
proper specializations. -/
instance [T1Space X] : IsDimensionFunction (fun _ : X ↦ (0 : ℤ)) where
  strict_of_specializes := by
    intro x y hxy hne
    exact (hne (Specializes.eq hxy)).elim
  eq_add_one_of_immediateSpecialization := by
    intro x y hxy
    exact (hxy.ne (Specializes.eq hxy.specializes)).elim

/-! ### Lemma_5_20_2 (from Chap05) -/
universe u

open TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for Lemma 5.20.2:
- project owner for dimension functions: `IsDimensionFunction` in `Definition_5_20_1`
- derived graded-order owner: `IsDimensionFunction.gradeOrder` on `Specialization X`
- project owner for catenarity and relative codimension: `CatenarySpace` and `codimBetween` in
  `Definition_5_11_4`
- project soberification bridge: `toIrreducibleCloseds` in `Lemma_5_8_16`
- mathlib specialization owner: `Specializes.closure_subset`

Layer triage:
- `source-facing`: Lemma 5.20.2, pairing catenarity with the codimension formula for closures of
  specialized points
- `core/canonical`: `IsDimensionFunction`, its induced `gradeOrder`, `CatenarySpace`, and
  sobriety encoded by
  `[QuasiSober X]` together with the derived instance `hδ.t0Space`
- `bridge/view`: the order comparison on `IrreducibleCloseds X` induced by a specialization

Primitive data already belongs to the upstream owners, so this file keeps the combined textbook
statement primary and derives the individual consequences from it.
-/

namespace IsDimensionFunction

section

variable [QuasiSober X] {δ : X → ℤ}

/-- Helper for Lemma 5.20.2: on a sober `T₀` space, irreducible closed subsets identify with
points in the specialization order. -/
private noncomputable def irreducible_closeds_equiv_specialization_points [T0Space X] :
    IrreducibleCloseds X ≃o Specialization X := by
  letI : PartialOrder X := specializationOrder X
  let eX : IrreducibleCloseds X ≃o X := irreducibleSetEquivPoints (α := X)
  let eS : X ≃o Specialization X :=
    { toEquiv := Specialization.toEquiv
      map_rel_iff' := by
        intro x y
        rfl }
  exact eX.trans eS

/-- Helper for Lemma 5.20.2: the sober-space generic-point equivalence restricts to the
corresponding interval of specialization-ordered points. -/
private noncomputable def irreducible_closeds_interval_equiv_generic_points [T0Space X]
    {T T' : IrreducibleCloseds X} :
    Set.Icc T T' ≃o
      Set.Icc ((irreducible_closeds_equiv_specialization_points (X := X)) T)
        ((irreducible_closeds_equiv_specialization_points (X := X)) T') where
  toFun x := ⟨(irreducible_closeds_equiv_specialization_points (X := X)) x.1,
    (irreducible_closeds_equiv_specialization_points (X := X)).monotone x.2.1,
    (irreducible_closeds_equiv_specialization_points (X := X)).monotone x.2.2⟩
  invFun y := ⟨(irreducible_closeds_equiv_specialization_points (X := X)).symm y.1,
    by
      simpa using
        (irreducible_closeds_equiv_specialization_points (X := X)).symm.monotone y.2.1,
    by
      simpa using
        (irreducible_closeds_equiv_specialization_points (X := X)).symm.monotone y.2.2⟩
  left_inv x := by
    ext
    simp [irreducible_closeds_equiv_specialization_points]
  right_inv y := by
    ext
    simp [irreducible_closeds_equiv_specialization_points]
  map_rel_iff' := by
    intro x y
    simpa using (irreducible_closeds_equiv_specialization_points (X := X)).le_iff_le

/-- Helper for Lemma 5.20.2: a dimension function is strictly monotone on the specialization
order. -/
private theorem strictMono_specialization_of_dimensionFunction [T0Space X]
    (hδ : IsDimensionFunction δ) :
    StrictMono fun x : Specialization X ↦ δ (Specialization.ofEquiv x) := by
  -- A strict increase in specialization order means the upper point specializes to the lower one,
  -- so the dimension function strictly increases when viewed on the ordered type
  -- `Specialization X`.
  intro x y hxy
  have hspecializes : Specialization.ofEquiv y ⤳ Specialization.ofEquiv x := by
    simpa using hxy.le
  simpa using hδ.strict_of_specializes hspecializes hxy.ne.symm

/-- Helper for Lemma 5.20.2: finite chains of length `n + 1` have Krull dimension `n`. -/
private theorem krullDim_fin_succ (n : ℕ) :
    Order.krullDim (Fin (n + 1)) = n := by
  -- Compare `Fin (n + 1)` with the initial interval `{0, ..., n}` in `ℕ`.
  let e : Fin (n + 1) ≃o Set.Iic n := by
    refine
      { toFun := fun i ↦ ⟨i.1, by simpa using i.is_le⟩
        invFun := fun i ↦ ⟨i.1, Nat.lt_succ_of_le i.2⟩
        left_inv := ?_
        right_inv := ?_
        map_rel_iff' := ?_ }
    · intro i
      rfl
    · intro i
      ext
      rfl
    · intro i j
      rfl
  rw [Order.krullDim_eq_of_orderIso e]
  simpa using (Order.height_eq_krullDim_Iic n).symm

/-- Helper for Lemma 5.20.2: the finite integer interval `[m, n]` has Krull dimension `n - m`. -/
private theorem krullDim_int_interval {m n : ℤ} (hmn : m ≤ n) :
    Order.krullDim (Set.Icc m n) = Int.toNat (n - m) := by
  -- Count the interval, then identify it with the corresponding finite chain.
  have hcard : Fintype.card (Set.Icc m n) = Int.toNat (n - m) + 1 := by
    have hcard' : (Fintype.card (Set.Icc m n) : ℤ) = n + 1 - m := by
      exact Int.card_fintype_Icc_of_le (a := m) (b := n) (by omega)
    have hcard'' : ((Int.toNat (n - m) + 1 : ℕ) : ℤ) = n + 1 - m := by
      norm_num [Int.toNat_of_nonneg (sub_nonneg.mpr hmn)]
      omega
    exact Int.ofNat.inj (hcard'.trans hcard''.symm)
  let e : Fin (Int.toNat (n - m) + 1) ≃o Set.Icc m n :=
    Fintype.orderIsoFinOfCardEq (Set.Icc m n) hcard
  calc
    Order.krullDim (Set.Icc m n)
        = Order.krullDim (Fin (Int.toNat (n - m) + 1)) := by
          simpa using (Order.krullDim_eq_of_orderIso e).symm
    _ = Int.toNat (n - m) := krullDim_fin_succ (Int.toNat (n - m))

/-- Helper for Lemma 5.20.2: in a bounded `ℤ`-graded order, the Krull dimension is the grade
difference between top and bottom. -/
private theorem krullDim_eq_toNat_sub_of_grade_order {α : Type*} [PartialOrder α]
    [BoundedOrder α] [GradeOrder ℤ α] :
    Order.krullDim α = Int.toNat (grade ℤ (⊤ : α) - grade ℤ (⊥ : α)) := by
  classical
  let N : ℕ := Int.toNat (grade ℤ (⊤ : α) - grade ℤ (⊥ : α))
  have hbot_top :
      grade ℤ (⊥ : α) ≤ grade ℤ (⊤ : α) := by
    exact grade_mono (bot_le : (⊥ : α) ≤ ⊤)
  apply le_antisymm
  · -- Map the graded order into the corresponding integer interval to get the upper bound.
    let g : α → Set.Icc (grade ℤ (⊥ : α)) (grade ℤ (⊤ : α)) :=
      fun x ↦ ⟨grade ℤ x, grade_mono (bot_le : (⊥ : α) ≤ x),
        grade_mono (le_top : x ≤ (⊤ : α))⟩
    have hg : StrictMono g := by
      intro x y hxy
      show grade ℤ x < grade ℤ y
      exact grade_strictMono hxy
    exact (Order.krullDim_le_of_strictMono g hg).trans (by
      simpa [N] using (krullDim_int_interval hbot_top).le)
  · -- A flag from bottom to top already has exactly one point in each integer grade.
    let s : Flag α := Classical.choice (show Nonempty (Flag α) from inferInstance)
    let gradeNat : s → ℕ :=
      fun x ↦ Int.toNat (grade ℤ x - grade ℤ (⊥ : s))
    have hgrade_strict : StrictMono gradeNat := by
      intro x y hxy
      have hxy_grade : grade ℤ x < grade ℤ y := grade_strictMono hxy
      have hbot_x : grade ℤ (⊥ : s) ≤ grade ℤ x := by
        exact grade_mono (bot_le : (⊥ : s) ≤ x)
      have hbot_y : grade ℤ (⊥ : s) ≤ grade ℤ y := by
        exact grade_mono (bot_le : (⊥ : s) ≤ y)
      dsimp [gradeNat]
      omega
    have hgrade_le : ∀ x : s, gradeNat x ≤ N := by
      intro x
      have hxtop : grade ℤ x ≤ grade ℤ (⊤ : s) := by
        exact grade_mono (le_top : x ≤ (⊤ : s))
      have hbot_x : grade ℤ (⊥ : s) ≤ grade ℤ x := by
        exact grade_mono (bot_le : (⊥ : s) ≤ x)
      dsimp [gradeNat, N]
      have htop_coe : grade ℤ (⊤ : s) = grade ℤ (⊤ : α) := by
        change grade ℤ ((⊤ : s) : α) = grade ℤ (⊤ : α)
        rfl
      have hbot_coe : grade ℤ (⊥ : s) = grade ℤ (⊥ : α) := by
        change grade ℤ ((⊥ : s) : α) = grade ℤ (⊥ : α)
        rfl
      omega
    let gradeFin : s → Fin (N + 1) :=
      fun x ↦ ⟨gradeNat x, Nat.lt_succ_of_le (hgrade_le x)⟩
    have hgrade_injective : Function.Injective gradeFin := by
      intro x y hxy
      exact hgrade_strict.injective (congrArg Fin.val hxy)
    letI : Finite s := Finite.of_injective gradeFin hgrade_injective
    letI : Fintype s := Fintype.ofFinite s
    have hcard_pos : 0 < Fintype.card s := Fintype.card_pos_iff.mpr ⟨⊥⟩
    let m : ℕ := Fintype.card s - 1
    have hm_card : Fintype.card s = m + 1 := by
      dsimp [m]
      exact (Nat.succ_pred_eq_of_pos hcard_pos).symm
    have huniv : (Finset.univ : Finset s).card = m + 1 := by
      simpa using hm_card
    let e₀ : Fin (m + 1) ≃o { x : s // x ∈ (Finset.univ : Finset s) } :=
      (Finset.univ : Finset s).orderIsoOfFin huniv
    let e₁ : { x : s // x ∈ (Finset.univ : Finset s) } ≃o s := by
      refine
        { toFun := fun x ↦ x.1
          invFun := fun x ↦ ⟨x, by simp⟩
          left_inv := ?_
          right_inv := ?_
          map_rel_iff' := ?_ }
      · intro x
        cases x
        rfl
      · intro x
        rfl
      · intro a b
        rfl
    let e : Fin (m + 1) ≃o s := e₀.trans e₁
    have hbot : e 0 = ⊥ := by
      exact e.map_bot
    have htop : e (Fin.last m) = ⊤ := by
      exact e.map_top
    have hstep :
        ∀ i : Fin m, gradeNat (e (Fin.succ i)) = gradeNat (e (Fin.castSucc i)) + 1 := by
      intro i
      have hcov_fin : (Fin.castSucc i : Fin (m + 1)) ⋖ Fin.succ i := by
        have hnat : ((i : ℕ) ⋖ i + 1) := by
          simp
        exact (Fin.covBy_iff).2 hnat
      have hcov_flag : e (Fin.castSucc i) ⋖ e (Fin.succ i) :=
        (apply_covBy_apply_iff e).2 hcov_fin
      have hcov : ((e (Fin.castSucc i) : s) : α) ⋖ ((e (Fin.succ i) : s) : α) := by
        exact (Flag.coe_covBy_coe).2 hcov_flag
      have hcov_grade :
          grade ℤ (e (Fin.castSucc i)) ⋖ grade ℤ (e (Fin.succ i)) := hcov_flag.grade ℤ
      have hbot_left :
          grade ℤ (⊥ : s) ≤ grade ℤ (e (Fin.castSucc i)) := by
        exact grade_mono (bot_le : (⊥ : s) ≤ e (Fin.castSucc i))
      have hbot_right :
          grade ℤ (⊥ : s) ≤ grade ℤ (e (Fin.succ i)) := by
        exact grade_mono (bot_le : (⊥ : s) ≤ e (Fin.succ i))
      rw [Order.covBy_iff_add_one_eq] at hcov_grade
      dsimp [gradeNat]
      omega
    have hindex : ∀ n (hn : n ≤ m), gradeNat (e ⟨n, Nat.lt_succ_of_le hn⟩) = n := by
      intro n hn
      induction n with
      | zero =>
          have hzero : gradeNat (e 0) = 0 := by
            dsimp [gradeNat]
            rw [hbot]
            omega
          simpa using hzero
      | succ n ih =>
          have hn' : n ≤ m := Nat.le_of_succ_le hn
          have hstep' := hstep ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
          simpa [ih hn'] using hstep'
    have htop_grade : gradeNat (e (Fin.last m)) = N := by
      dsimp [gradeNat, N]
      rw [htop]
      have htop_coe : grade ℤ (⊤ : s) = grade ℤ (⊤ : α) := by
        change grade ℤ ((⊤ : s) : α) = grade ℤ (⊤ : α)
        rfl
      have hbot_coe : grade ℤ (⊥ : s) = grade ℤ (⊥ : α) := by
        change grade ℤ ((⊥ : s) : α) = grade ℤ (⊥ : α)
        rfl
      omega
    have hm_eq_N : m = N := by
      calc
        m = gradeNat (e (Fin.last m)) := by simpa using (hindex m le_rfl).symm
        _ = N := htop_grade
    let p : LTSeries α :=
      { length := m
        toFun := fun i ↦ ((e i : s) : α)
        step := fun i ↦ by
          have : (Fin.castSucc i : Fin (m + 1)) < Fin.succ i := by
            simp
          exact e.strictMono this }
    have hp : (p.length : ℕ) = N := hm_eq_N
    have hdim' : (m : WithBot ℕ∞) ≤ Order.krullDim α := by
      simpa [p] using (Order.LTSeries.length_le_krullDim p)
    have hdim : (N : WithBot ℕ∞) ≤ Order.krullDim α := by
      simpa [hm_eq_N] using hdim'
    simpa [N] using hdim

/-- Helper for Lemma 5.20.2: for comparable irreducible closed subsets, relative codimension is
the difference of the dimension function at their generic points. -/
private theorem codimBetween_eq_toNat_sub_of_irreducible_closeds_le
    [T0Space X] (hδ : IsDimensionFunction δ) {T T' : IrreducibleCloseds X} (hTT' : T ≤ T') :
    codimBetween T T' hTT' =
      Int.toNat
        (δ (Specialization.ofEquiv
            ((irreducible_closeds_equiv_specialization_points (X := X)) T')) -
          δ (Specialization.ofEquiv
            ((irreducible_closeds_equiv_specialization_points (X := X)) T))) := by
  -- Transport the interval of irreducible closed subsets to the generic-point interval and use the
  -- induced integer grading coming from the dimension function.
  letI : GradeOrder ℤ (Specialization X) := hδ.gradeOrder
  let e : IrreducibleCloseds X ≃o Specialization X :=
    irreducible_closeds_equiv_specialization_points (X := X)
  let _ : Fact (e T ≤ e T') := ⟨e.monotone hTT'⟩
  have hconn :
      (Set.range (OrderEmbedding.subtype (Set.Icc (e T) (e T')))).OrdConnected := by
    simpa only [OrderEmbedding.coe_subtype, Subtype.range_coe_subtype] using
      (Set.ordConnected_Icc : (Set.Icc (e T) (e T')).OrdConnected)
  letI : GradeOrder ℤ (Set.Icc (e T) (e T')) :=
    GradeOrder.liftRight (Subtype.val : Set.Icc (e T) (e T') → Specialization X)
      (Subtype.strictMono_coe _)
      (fun x y hxy ↦ by
        exact
          ((Set.OrdConnected.apply_covBy_apply_iff
              (OrderEmbedding.subtype (Set.Icc (e T) (e T'))) hconn).2 hxy))
  apply WithBot.coe_inj.mp
  calc
    (codimBetween T T' hTT' : WithBot ℕ∞) = Order.krullDim (Set.Icc T T') := codimBetween_eq_krullDim hTT'
    _ = Order.krullDim (Set.Icc (e T) (e T')) := by
      exact Order.krullDim_eq_of_orderIso
        (irreducible_closeds_interval_equiv_generic_points (X := X) (T := T) (T' := T'))
    _ = Int.toNat
          (grade ℤ (⊤ : Set.Icc (e T) (e T')) -
            grade ℤ (⊥ : Set.Icc (e T) (e T'))) := by
          exact krullDim_eq_toNat_sub_of_grade_order
    _ = Int.toNat
          (δ (Specialization.ofEquiv (e T')) - δ (Specialization.ofEquiv (e T))) := by
          rfl

-- Proof sketch: use quasi-sobriety together with the derived instance `hδ.t0Space` to identify
-- irreducible closed subsets with closures of their generic points. The dimension-function axioms
-- then compute the common length of maximal chains by telescoping along immediate specializations.
/-- Lemma 5.20.2: if `X` is sober and `δ` is a dimension function on `X`, then `X` is catenary.
Moreover, for any specialization `x ⤳ y`, the difference `δ x - δ y` equals the codimension of
`closure {y}` inside `closure {x}`. Quasi-sobriety is an ambient hypothesis, and `T₀` is derived
canonically from the dimension function. -/
theorem catenarySpace_and_sub_eq_codimBetween_pointClosure
    (hδ : IsDimensionFunction δ)
    :
    CatenarySpace X ∧
      ∀ (x y : X) (hxy : x ⤳ y),
        δ x - δ y =
          (ENat.toNat
            (codimBetween (toIrreducibleCloseds y) (toIrreducibleCloseds x)
              hxy.toIrreducibleCloseds_le) : ℤ) := by
  letI : T0Space X := hδ.t0Space
  let e : IrreducibleCloseds X ≃o Specialization X :=
    irreducible_closeds_equiv_specialization_points (X := X)
  have hδ_strict :
      StrictMono fun z : Specialization X ↦ δ (Specialization.ofEquiv z) :=
    strictMono_specialization_of_dimensionFunction (δ := δ) hδ
  have hδ_mono :
      Monotone fun z : Specialization X ↦ δ (Specialization.ofEquiv z) := hδ_strict.monotone
  constructor
  · -- The codimension criterion from Lemma 5.11.6 reduces catenarity to finiteness and
    -- additivity of `codimBetween`, both of which follow from the generic-point formula above.
    rw [catenarySpace_iff_finite_codimBetween_and_codimBetween_additive]
    refine ⟨?_, ?_⟩
    · intro T T' hTT'
      rw [codimBetween_eq_toNat_sub_of_irreducible_closeds_le (δ := δ) hδ hTT']
      exact ENat.coe_lt_top _
    · intro T T' T'' hTT' hT'T''
      rw [codimBetween_eq_toNat_sub_of_irreducible_closeds_le (δ := δ) hδ (hTT'.trans hT'T''),
        codimBetween_eq_toNat_sub_of_irreducible_closeds_le (δ := δ) hδ hTT',
        codimBetween_eq_toNat_sub_of_irreducible_closeds_le (δ := δ) hδ hT'T'']
      have h01 :
          0 ≤ δ (Specialization.ofEquiv (e T')) - δ (Specialization.ofEquiv (e T)) := by
        exact sub_nonneg.mpr (hδ_mono (e.monotone hTT'))
      have h12 :
          0 ≤ δ (Specialization.ofEquiv (e T'')) - δ (Specialization.ofEquiv (e T')) := by
        exact sub_nonneg.mpr (hδ_mono (e.monotone hT'T''))
      have h02 :
          0 ≤ δ (Specialization.ofEquiv (e T'')) - δ (Specialization.ofEquiv (e T)) := by
        exact sub_nonneg.mpr (hδ_mono (e.monotone (hTT'.trans hT'T'')))
      have hsumInt :
          (Int.toNat
            (δ (Specialization.ofEquiv (e T'')) -
              δ (Specialization.ofEquiv (e T))) : ℤ) =
            Int.toNat
              (δ (Specialization.ofEquiv (e T')) -
                δ (Specialization.ofEquiv (e T))) +
              Int.toNat
                (δ (Specialization.ofEquiv (e T'')) -
                  δ (Specialization.ofEquiv (e T'))) := by
        rw [Int.toNat_of_nonneg h02, Int.toNat_of_nonneg h01, Int.toNat_of_nonneg h12]
        omega
      have hsum :
          Int.toNat
            (δ (Specialization.ofEquiv (e T'')) -
              δ (Specialization.ofEquiv (e T))) =
            Int.toNat
              (δ (Specialization.ofEquiv (e T')) -
                δ (Specialization.ofEquiv (e T))) +
              Int.toNat
                (δ (Specialization.ofEquiv (e T'')) -
                  δ (Specialization.ofEquiv (e T'))) := by
        exact_mod_cast hsumInt
      exact congrArg (fun n : ℕ ↦ (n : ℕ∞)) hsum
  · intro x y hxy
    -- Specialize the generic-point computation to the interval of point closures.
    have hcodim :
        codimBetween (toIrreducibleCloseds y) (toIrreducibleCloseds x)
            hxy.toIrreducibleCloseds_le =
          Int.toNat (δ x - δ y) := by
      have hx :
          Specialization.ofEquiv
              ((irreducible_closeds_equiv_specialization_points (X := X))
                (toIrreducibleCloseds x)) = x := by
        letI : PartialOrder X := specializationOrder X
        change (irreducibleSetEquivPoints (α := X)) (toIrreducibleCloseds x) = x
        exact (irreducibleSetEquivPoints (α := X)).right_inv x
      have hy :
          Specialization.ofEquiv
              ((irreducible_closeds_equiv_specialization_points (X := X))
                (toIrreducibleCloseds y)) = y := by
        letI : PartialOrder X := specializationOrder X
        change (irreducibleSetEquivPoints (α := X)) (toIrreducibleCloseds y) = y
        exact (irreducibleSetEquivPoints (α := X)).right_inv y
      simpa [hx, hy] using
        (codimBetween_eq_toNat_sub_of_irreducible_closeds_le (δ := δ) hδ
          hxy.toIrreducibleCloseds_le : _)
    have hnonneg : 0 ≤ δ x - δ y := by
      by_cases hEq : x = y
      · simp [hEq]
      · exact sub_nonneg.mpr (le_of_lt (hδ.strict_of_specializes hxy hEq))
    calc
      δ x - δ y = (Int.toNat (δ x - δ y) : ℤ) := by
        rw [Int.toNat_of_nonneg hnonneg]
      _ = (ENat.toNat
          (codimBetween (toIrreducibleCloseds y) (toIrreducibleCloseds x)
            hxy.toIrreducibleCloseds_le) : ℤ) := by
        rw [hcodim]
        simp

/-- A quasi-sober topological space with a dimension function is catenary; the ambient `T₀`
structure is derived canonically from the dimension function. -/
theorem catenarySpace (hδ : IsDimensionFunction δ) :
    CatenarySpace X :=
  hδ.catenarySpace_and_sub_eq_codimBetween_pointClosure.1

-- Proof sketch: this is the codimension component of Lemma 5.20.2, applied to the irreducible
-- closed interval `[closure {y}, closure {x}]`.
/-- On a sober space, a dimension function computes the codimension between point closures along a
specialization. Here quasi-sobriety is ambient, and `T₀` is supplied canonically by the
dimension function. -/
theorem sub_eq_codimBetween_pointClosure (hδ : IsDimensionFunction δ)
    (x y : X) (hxy : x ⤳ y) :
    δ x - δ y =
      (ENat.toNat
        (codimBetween (toIrreducibleCloseds y) (toIrreducibleCloseds x)
          hxy.toIrreducibleCloseds_le) : ℤ) :=
  hδ.catenarySpace_and_sub_eq_codimBetween_pointClosure.2 x y hxy

end

end IsDimensionFunction

/-! ### Lemma_5_20_3 (from Chap05) -/
open TopologicalSpace

universe u

/- Domain-style sampling for Lemma 5.20.3:
- project owner for dimension functions: `IsDimensionFunction`
- derived codimension comparison owner: `IsDimensionFunction.sub_eq_codimBetween_pointClosure`
- local Noetherian neighborhood bridge: `LocallyNoetherianSpace.exists_mem_nhds_subset`
- canonical irreducible-component owner on Noetherian neighborhoods: `irreducibleComponents`

Layer triage:
- `source-facing`: the difference of two dimension functions is locally constant
- `core/canonical`: `IsDimensionFunction`, `IsLocallyConstant`, `LocallyNoetherianSpace`,
  `QuasiSober`
- `bridge/view`: shrink to a Noetherian open neighborhood, then compare both functions on each
  irreducible component through the common codimension formula from Lemma `5.20.2`

Primitive data versus derived API:
- primitive data already lives upstream in `IsDimensionFunction` and `LocallyNoetherianSpace`
- this file should contribute only the derived locally constant theorem under the owner namespace,
  not a new wrapper around local dimension data
-/

namespace IsDimensionFunction

section

variable {X : Type u} [TopologicalSpace X] [LocallyNoetherianSpace X] [QuasiSober X]
  {δ δ' : X → ℤ}

/-- Helper for Lemma 5.20.3: restricting a dimension function to an open subspace preserves the
dimension-function axioms. -/
lemma restrict_open (U : Opens X) (hδ : IsDimensionFunction δ) :
    IsDimensionFunction (fun u : U ↦ δ u) where
  strict_of_specializes := by
    intro x y hxy hne
    -- Pass the specialization relation to the ambient space and reuse the ambient strict decrease.
    exact hδ.strict_of_specializes ((subtype_specializes_iff x y).mp hxy) fun h =>
      hne (Subtype.ext h)
  eq_add_one_of_immediateSpecialization := by
    intro x y hxy
    -- Lift the immediate-specialization relation from the open subtype to the ambient space.
    have hxy_ambient : IsImmediateSpecialization (x : X) y := by
      refine ⟨(subtype_specializes_iff x y).mp hxy.specializes, ?_, ?_⟩
      · intro h
        exact hxy.ne (Subtype.ext h)
      · intro z hxz hzy
        have hzU : z ∈ (U : Set X) := hzy.mem_open U.2 y.2
        let zU : U := ⟨z, hzU⟩
        have hxzU : x ⤳ zU := (subtype_specializes_iff x zU).2 hxz
        have hzUy : zU ⤳ y := (subtype_specializes_iff zU y).2 hzy
        rcases hxy.eq_or_eq hxzU hzUy with hzx | hzy'
        · left
          exact congrArg Subtype.val hzx
        · right
          exact congrArg Subtype.val hzy'
    -- The unit-drop identity now follows from the ambient dimension function.
    simpa using hδ.eq_add_one_of_immediateSpecialization hxy_ambient

section Noetherian

variable [NoetherianSpace X]

/-- Helper for Lemma 5.20.3: the difference of two dimension functions is constant on each
irreducible component. -/
lemma sub_eq_sub_of_mem_irreducible_component (hδ : IsDimensionFunction δ)
    (hδ' : IsDimensionFunction δ') {Z : Set X} (hZ : Z ∈ irreducibleComponents X) {x y : X}
    (hx : x ∈ Z) (hy : y ∈ Z) :
    δ x - δ' x = δ y - δ' y := by
  let ξ : X := hZ.1.genericPoint
  have hξ : IsGenericPoint ξ Z := by
    simpa [ξ] using
      hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
  have hξx : ξ ⤳ x := hξ.specializes hx
  have hξy : ξ ⤳ y := hξ.specializes hy
  -- Compare both functions to the same generic point of the component.
  have hx_eq : δ ξ - δ x = δ' ξ - δ' x := by
    rw [hδ.sub_eq_codimBetween_pointClosure ξ x hξx,
      hδ'.sub_eq_codimBetween_pointClosure ξ x hξx]
  have hy_eq : δ ξ - δ y = δ' ξ - δ' y := by
    rw [hδ.sub_eq_codimBetween_pointClosure ξ y hξy,
      hδ'.sub_eq_codimBetween_pointClosure ξ y hξy]
  -- Cancelling the common codimension terms gives the claimed equality of differences.
  linarith

/-- Helper for Lemma 5.20.3: in a Noetherian space, the union of irreducible components not
containing a fixed point has open complement. -/
lemma isOpen_component_neighborhood (x : X) :
    IsOpen (((⋃₀ {Z : Set X | Z ∈ irreducibleComponents X ∧ x ∉ Z})ᶜ : Set X)) := by
  let bad : Set (Set X) := {Z | Z ∈ irreducibleComponents X ∧ x ∉ Z}
  have hbad_finite : bad.Finite := NoetherianSpace.finite_irreducibleComponents.subset fun _ h ↦ h.1
  have hbad_closed : IsClosed (⋃₀ bad) := by
    rw [Set.sUnion_eq_biUnion]
    exact hbad_finite.isClosed_biUnion fun W hW ↦
      isClosed_of_mem_irreducibleComponents W hW.1
  -- The desired neighborhood is the complement of this closed union.
  simpa [bad] using hbad_closed.isOpen_compl

/-- Helper for Lemma 5.20.3: on a Noetherian quasi-sober space, the difference of two dimension
functions is locally constant. -/
theorem isLocallyConstant_sub_of_noetherian (hδ : IsDimensionFunction δ)
    (hδ' : IsDimensionFunction δ') :
    IsLocallyConstant (δ - δ') := by
  refine (IsLocallyConstant.iff_exists_open _).2 ?_
  intro x
  let V : Set X :=
    (((⋃₀ {Z : Set X | Z ∈ irreducibleComponents X ∧ x ∉ Z})ᶜ : Set X))
  have hV_open : IsOpen V := by
    simpa [V] using isOpen_component_neighborhood (X := X) x
  have hxV : x ∈ V := by
    -- By construction, `x` lies in no irreducible component excluded from the neighborhood.
    intro hx_bad
    rcases Set.mem_sUnion.1 hx_bad with ⟨B, hBbad, hxB⟩
    exact hBbad.2 hxB
  refine ⟨V, hV_open, hxV, ?_⟩
  intro y hyV
  have hy_components : y ∈ ⋃₀ irreducibleComponents X := by
    simp [sUnion_irreducibleComponents]
  rcases Set.mem_sUnion.1 hy_components with ⟨Z, hZ, hyZ⟩
  have hxZ : x ∈ Z := by
    -- Any irreducible component meeting the neighborhood must also contain `x`.
    by_contra hxZ
    have hy_bad : y ∈ ⋃₀ {Z : Set X | Z ∈ irreducibleComponents X ∧ x ∉ Z} := by
      exact Set.mem_sUnion.2 ⟨Z, ⟨hZ, hxZ⟩, hyZ⟩
    exact hyV hy_bad
  simpa using
    (sub_eq_sub_of_mem_irreducible_component (X := X) (x := x) (y := y) hδ hδ' hZ hxZ hyZ).symm

end Noetherian

-- Proof sketch: around each point, choose a Noetherian open neighbourhood using local
-- Noetherianity. In that neighbourhood, the finitely many irreducible components through the
-- point have generic points by sobriety, and Lemma 5.20.2 identifies both dimension functions
-- with the same codimension formula on each component, forcing `δ - δ'` to be constant there.
/-- Lemma 5.20.3: on a locally Noetherian sober topological space, the difference `δ - δ'` of two
dimension functions is locally constant; `T₀` is derived canonically from either dimension
function, so only quasi-sobriety remains ambient. -/
theorem isLocallyConstant_sub (hδ : IsDimensionFunction δ)
    (hδ' : IsDimensionFunction δ') :
    IsLocallyConstant (δ - δ') := by
  refine (IsLocallyConstant.iff_exists_open _).2 ?_
  intro x
  rcases LocallyNoetherianSpace.exists_open x with ⟨U, hxU, hU_noetherian⟩
  letI : NoetherianSpace U := hU_noetherian
  letI : QuasiSober U := U.isOpenEmbedding'.quasiSober
  have hδU : IsDimensionFunction (fun u : U ↦ δ u) := restrict_open U hδ
  have hδU' : IsDimensionFunction (fun u : U ↦ δ' u) := restrict_open U hδ'
  have hlocU : IsLocallyConstant (fun u : U ↦ δ u - δ' u) :=
    isLocallyConstant_sub_of_noetherian (X := U) hδU hδU'
  obtain ⟨V, hV_open, hxV, hconstV⟩ := (IsLocallyConstant.iff_exists_open _).1 hlocU ⟨x, hxU⟩
  let W : Set X := Subtype.val '' V
  have hW_open : IsOpen W := by
    simpa [W] using U.2.isOpenMap_subtype_val V hV_open
  have hxW : x ∈ W := by
    exact ⟨⟨x, hxU⟩, hxV, rfl⟩
  refine ⟨W, hW_open, hxW, ?_⟩
  intro y hyW
  rcases hyW with ⟨yU, hyV, rfl⟩
  -- The locally constant neighborhood in the open subtype pushes forward to one in `X`.
  simpa using hconstV yU hyV

end

end IsDimensionFunction

/-! ### Lemma_5_20_4 (from Chap05) -/
universe u

open TopologicalSpace Order Specialization

variable {X : Type u} [TopologicalSpace X] [TopologicalSpace.LocallyNoetherianSpace X]
  [QuasiSober X] [T0Space X] [CatenarySpace X]

/- Domain-style sampling for local existence of dimension functions:
- project owner for dimension functions: `IsDimensionFunction` in `Definition_5_20_1`
- derived codimension owner: `IsDimensionFunction.sub_eq_codimBetween_pointClosure`
- local Noetherian neighborhood owner: `TopologicalSpace.LocallyNoetherianSpace.exists_open`
- open-subspace locality owners: `IsLocallyClosed.sober` and `IsLocallyClosed.catenarySpace`

Layer triage:
- `source-facing`: Lemma 5.20.4, asserting existence of a local dimension function near a point
- `core/canonical`: `IsDimensionFunction`, `LocallyNoetherianSpace`, `QuasiSober`, and
  `CatenarySpace`
- `bridge/view`: restriction to a suitable open neighborhood, then construction of an
  integer-valued function on that open subspace

Primitive data versus derived API:
- primitive data already belongs to the owner abstractions `IsDimensionFunction`,
  `LocallyNoetherianSpace`, and `CatenarySpace`
- this file should therefore keep only the source-facing existential theorem on an open subspace,
  rather than introducing a local wrapper for a neighborhood together with its function
-/

omit [TopologicalSpace.LocallyNoetherianSpace X] [QuasiSober X] [T0Space X] [CatenarySpace X] in
/-- Helper for Lemma 5.20.4: transporting a dimension function across a homeomorphism preserves
the dimension-function axioms. -/
theorem Homeomorph.isDimensionFunction_comp_symm {Y : Type*} [TopologicalSpace Y]
    (e : X ≃ₜ Y) {δ : X → ℤ} (hδ : IsDimensionFunction δ) :
    IsDimensionFunction (fun y : Y ↦ δ (e.symm y)) where
  strict_of_specializes := by
    intro y z hyz hyz_ne
    -- Pull the specialization relation back along the inverse homeomorphism.
    exact hδ.strict_of_specializes (hyz.map e.symm.continuous) fun h =>
      hyz_ne <| by
        simpa using congrArg e h
  eq_add_one_of_immediateSpecialization := by
    intro y z hyz
    -- Immediate specializations are preserved because both directions of the homeomorphism are
    -- continuous.
    have hyz_pullback : IsImmediateSpecialization (e.symm y) (e.symm z) := by
      refine ⟨hyz.specializes.map e.symm.continuous, ?_, ?_⟩
      · intro h
        exact hyz.ne <| by
          simpa using congrArg e h
      · intro w hyw hwz
        have hyw' : y ⤳ e w := by
          simpa using hyw.map e.continuous
        have hwz' : e w ⤳ z := by
          simpa using hwz.map e.continuous
        rcases hyz.eq_or_eq hyw' hwz' with h | h
        · left
          simpa using congrArg e.symm h
        · right
          simpa using congrArg e.symm h
    simpa using hδ.eq_add_one_of_immediateSpecialization hyz_pullback

/-- Helper for Lemma 5.20.4: on a sober `T₀` space, irreducible closed subsets identify with
points in the specialization order. -/
private noncomputable def irreducible_closeds_equiv_specialization_points :
    IrreducibleCloseds X ≃o Specialization X := by
  letI : PartialOrder X := specializationOrder X
  let eX : IrreducibleCloseds X ≃o X := irreducibleSetEquivPoints (α := X)
  let eS : X ≃o Specialization X :=
    { toEquiv := toEquiv
      map_rel_iff' := by
        intro x y
        rfl }
  exact eX.trans eS

/-- Helper for Lemma 5.20.4: the irreducible-closed/point equivalence sends a point closure to the
original point. -/
@[simp] private theorem irreducible_closeds_equiv_specialization_points_apply_pointClosure
    (x : X) :
    irreducible_closeds_equiv_specialization_points (X := X) (toIrreducibleCloseds x) =
      toEquiv x := by
  letI : PartialOrder X := specializationOrder X
  change toEquiv ((irreducibleSetEquivPoints (α := X)) (toIrreducibleCloseds x)) = toEquiv x
  exact congrArg toEquiv ((irreducibleSetEquivPoints (α := X)).right_inv x)

/-- Helper for Lemma 5.20.4: strict containment of irreducible closed subsets gives positive
relative codimension. -/
private theorem codimBetween_pos_of_lt {T T' : IrreducibleCloseds X} (hTT' : T < T') :
    0 < codimBetween T T' hTT'.le := by
  -- Rewrite relative codimension as the coheight of the bottom element in `[T, T']`.
  let _ : Fact (T ≤ T') := ⟨hTT'.le⟩
  change 0 < coheight (⊥ : Set.Icc T T')
  exact coheight_pos_of_lt_top hTT'

/-- Helper for Lemma 5.20.4: a cover relation contributes exactly one unit of relative
codimension once relative codimension is finite. -/
private theorem codimBetween_eq_one_of_covBy
    (hfinite : ∀ ⦃A B : IrreducibleCloseds X⦄ (hAB : A ≤ B), codimBetween A B hAB < ⊤)
    {T T' : IrreducibleCloseds X} (hTT' : T ⋖ T') :
    codimBetween T T' hTT'.le = 1 := by
  -- Route correction: exclude codimension `≥ 2` by producing an intermediate irreducible closed
  -- subset, which contradicts that `T ⋖ T'`.
  have hfin : codimBetween T T' hTT'.le < ⊤ := hfinite hTT'.le
  have hpos : 0 < codimBetween T T' hTT'.le := codimBetween_pos_of_lt hTT'.1
  by_contra hne
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hfin.ne
  have hone_lt : (1 : ℕ∞) < codimBetween T T' hTT'.le := by
    cases n with
    | zero =>
        exfalso
        rw [← hn] at hpos
        exact (lt_irrefl _ hpos).elim
    | succ n =>
        cases n with
        | zero =>
            exfalso
            have hone : codimBetween T T' hTT'.le = 1 := by
              simpa using hn.symm
            exact hne hone
        | succ n =>
            rw [← hn]
            exact_mod_cast Nat.succ_lt_succ (Nat.succ_pos n)
  let _ : Fact (T ≤ T') := ⟨hTT'.le⟩
  obtain ⟨U, hTU, hUcoh⟩ :=
    (coe_lt_coheight_iff hfin).1 <| by
      simpa using hone_lt
  have hU_ne_top : U ≠ (⊤ : Set.Icc T T') := by
    intro hU
    simp [hU] at hUcoh
  have hU_lt_top : U < (⊤ : Set.Icc T T') := lt_of_le_of_ne le_top hU_ne_top
  exact ((not_covBy_iff hTT'.1).2 ⟨U.1, by simpa using hTU, by simpa using hU_lt_top⟩) hTT'

/-- Helper for Lemma 5.20.4: a proper specialization induces strict containment of the associated
point closures. -/
private theorem pointClosure_lt_of_proper_specializes {x y : X} (hxy : x ⤳ y) (hxy_ne : x ≠ y) :
    toIrreducibleCloseds y < toIrreducibleCloseds x := by
  refine lt_of_le_of_ne hxy.toIrreducibleCloseds_le ?_
  intro hEq
  exact hxy_ne ((inseparable_iff_eq).1 <| (toIrreducibleCloseds_eq_iff_inseparable).1 hEq.symm)

/-- Helper for Lemma 5.20.4: the relative codimension between point closures is positive for a
proper specialization. -/
theorem pointClosure_codim_pos_of_proper_specializes {x y : X} (hxy : x ⤳ y) (hxy_ne : x ≠ y) :
    0 <
      codimBetween (toIrreducibleCloseds y) (toIrreducibleCloseds x)
        hxy.toIrreducibleCloseds_le := by
  -- Proper specialization makes the target point closure strictly smaller.
  exact codimBetween_pos_of_lt (pointClosure_lt_of_proper_specializes hxy hxy_ne)

/-- Helper for Lemma 5.20.4: the relative codimension between point closures is exactly one for an
immediate specialization. -/
theorem pointClosure_codim_eq_one_of_immediateSpecialization {x y : X}
    (hxy : IsImmediateSpecialization x y) :
    codimBetween (toIrreducibleCloseds y) (toIrreducibleCloseds x)
      hxy.specializes.toIrreducibleCloseds_le = 1 := by
  let e : IrreducibleCloseds X ≃o Specialization X :=
    irreducible_closeds_equiv_specialization_points (X := X)
  have hcov_points : toEquiv y ⋖ toEquiv x := (isImmediateSpecialization_iff_covBy).1 hxy
  have hcov :
      toIrreducibleCloseds y ⋖ toIrreducibleCloseds x := by
    have hy : e (toIrreducibleCloseds y) = toEquiv y := by
      simp [e]
    have hx : e (toIrreducibleCloseds x) = toEquiv x := by
      simp [e]
    refine (apply_covBy_apply_iff e).1 ?_
    rw [hy, hx]
    exact hcov_points
  -- A cover relation in the irreducible-closed poset contributes one unit of codimension.
  exact codimBetween_eq_one_of_covBy
    (fun _ _ hAB ↦ CatenarySpace.finite_codimBetween (X := X) hAB) hcov

/-- Helper for Lemma 5.20.4: mapping an irreducible closed subset of a closed subtype back to the
ambient space stays inside that closed subset of the ambient space. -/
private theorem irreducibleClosed_map_subtype_subset {S : Set X} (hS : IsClosed S)
    (T : IrreducibleCloseds S) :
    ((IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T :
        IrreducibleCloseds X) : Set X) ⊆ S := by
  -- The mapped subset is the closure of an image already contained in `S`.
  rw [IrreducibleCloseds.coe_map]
  refine closure_minimal ?_ hS
  rintro z ⟨y, hy, rfl⟩
  exact y.2

/-- Helper for Lemma 5.20.4: bundle the ambient irreducible component through a point as an
irreducible closed subset. -/
private noncomputable def ambientIrreducibleComponent (x : X) : IrreducibleCloseds X :=
  ⟨irreducibleComponent x, (irreducibleComponent_mem_irreducibleComponents x).1,
    isClosed_irreducibleComponent⟩

/-- Helper for Lemma 5.20.4: a point belongs to its ambient irreducible component. -/
private theorem ambientIrreducibleComponent_mem (x : X) :
    x ∈ (ambientIrreducibleComponent x : Set X) :=
  mem_irreducibleComponent

/-- Helper for Lemma 5.20.4: a point closure is contained in any irreducible closed subset that
contains the point. -/
private theorem pointClosure_le_of_mem {T : IrreducibleCloseds X} {x : X}
    (hx : x ∈ (T : Set X)) : toIrreducibleCloseds x ≤ T := by
  -- Specializations out of `x` stay inside every closed subset containing `x`.
  intro z hz
  exact (specializes_iff_mem_closure.mpr hz).mem_closed T.isClosed hx

/-- Helper for Lemma 5.20.4: on an irreducible catenary space, shifting codimension to the top
irreducible closed subset gives an integer-valued candidate for a dimension function. -/
private noncomputable def topIrreducibleClosed [IrreducibleSpace X] : IrreducibleCloseds X :=
  ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩

/-- Helper for Lemma 5.20.4: every point closure lies in the top irreducible closed subset of an
irreducible space. -/
private theorem pointClosure_le_topIrreducibleClosed [IrreducibleSpace X] (x : X) :
    toIrreducibleCloseds x ≤ topIrreducibleClosed (X := X) :=
  pointClosure_le_of_mem (by simp [topIrreducibleClosed])

/-- Helper for Lemma 5.20.4: the codimension shift inside a fixed irreducible closed subset,
normalized to vanish at the base point `x`. -/
private noncomputable def codimShiftIn (x : X) (T : IrreducibleCloseds X) (hxT : x ∈ (T : Set X))
    (y : X) (hyT : y ∈ (T : Set X)) : ℤ :=
  -(ENat.toNat
      (codimBetween (toIrreducibleCloseds y) T (pointClosure_le_of_mem hyT)) : ℤ) +
    (ENat.toNat
      (codimBetween (toIrreducibleCloseds x) T (pointClosure_le_of_mem hxT)) : ℤ)

/-- Helper for Lemma 5.20.4: on an irreducible catenary space, shifting codimension to the top
irreducible closed subset gives an integer-valued candidate for a dimension function. -/
private noncomputable def codim_shift_to_top [IrreducibleSpace X] (x : X) : X → ℤ :=
  fun y ↦
    -(ENat.toNat
        (codimBetween (toIrreducibleCloseds y) (topIrreducibleClosed (X := X))
          (pointClosure_le_topIrreducibleClosed (X := X) y)) : ℤ) +
      (ENat.toNat
        (codimBetween (toIrreducibleCloseds x) (topIrreducibleClosed (X := X))
          (pointClosure_le_topIrreducibleClosed (X := X) x)) : ℤ)

/-- Helper for Lemma 5.20.4: the codimension shift to the top irreducible closed subset is a
dimension function on an irreducible catenary space. -/
private theorem codim_shift_to_top_isDimensionFunction [IrreducibleSpace X] (x : X) :
    IsDimensionFunction (codim_shift_to_top (X := X) x) where
  strict_of_specializes := by
    intro y z hyz hyz_ne
    -- Additivity in the chain `closure {z} ⊆ closure {y} ⊆ ⊤` isolates the positive codimension
    -- between the point closures.
    have hyz_add :
        codimBetween (toIrreducibleCloseds z) (topIrreducibleClosed (X := X))
            (pointClosure_le_topIrreducibleClosed (X := X) z) =
          codimBetween (toIrreducibleCloseds z) (toIrreducibleCloseds y)
              hyz.toIrreducibleCloseds_le +
            codimBetween (toIrreducibleCloseds y) (topIrreducibleClosed (X := X))
              (pointClosure_le_topIrreducibleClosed (X := X) y) := by
      simpa using
        (CatenarySpace.codimBetween_additive (X := X) hyz.toIrreducibleCloseds_le
          (pointClosure_le_topIrreducibleClosed (X := X) y))
    have hpos :
        0 < codimBetween (toIrreducibleCloseds z) (toIrreducibleCloseds y)
          hyz.toIrreducibleCloseds_le :=
      pointClosure_codim_pos_of_proper_specializes hyz hyz_ne
    have hfinite :
        codimBetween (toIrreducibleCloseds z) (toIrreducibleCloseds y)
            hyz.toIrreducibleCloseds_le <
          ⊤ :=
      CatenarySpace.finite_codimBetween hyz.toIrreducibleCloseds_le
    have htop_finite :
        codimBetween (toIrreducibleCloseds y) (topIrreducibleClosed (X := X))
            (pointClosure_le_topIrreducibleClosed (X := X) y) <
          ⊤ :=
      CatenarySpace.finite_codimBetween
        (pointClosure_le_topIrreducibleClosed (X := X) y)
    have hnat :
        0 <
          ENat.toNat
            (codimBetween (toIrreducibleCloseds z) (toIrreducibleCloseds y)
              hyz.toIrreducibleCloseds_le) := by
      exact Nat.pos_of_ne_zero fun hzero ↦
        hpos.ne' <| by
          rw [← ENat.coe_toNat hfinite.ne, hzero]
          rfl
    dsimp [codim_shift_to_top]
    rw [hyz_add, ENat.toNat_add hfinite.ne htop_finite.ne]
    have hnat_int :
        (0 : ℤ) <
          ENat.toNat
            (codimBetween (toIrreducibleCloseds z) (toIrreducibleCloseds y)
              hyz.toIrreducibleCloseds_le) := by
      exact_mod_cast hnat
    omega
  eq_add_one_of_immediateSpecialization := by
    intro y z hyz
    -- Along an immediate specialization, the isolated point-closure codimension is exactly one.
    have hyz_add :
        codimBetween (toIrreducibleCloseds z) (topIrreducibleClosed (X := X))
            (pointClosure_le_topIrreducibleClosed (X := X) z) =
          codimBetween (toIrreducibleCloseds z) (toIrreducibleCloseds y)
              hyz.specializes.toIrreducibleCloseds_le +
            codimBetween (toIrreducibleCloseds y) (topIrreducibleClosed (X := X))
              (pointClosure_le_topIrreducibleClosed (X := X) y) := by
      simpa using
        (CatenarySpace.codimBetween_additive (X := X) hyz.specializes.toIrreducibleCloseds_le
          (pointClosure_le_topIrreducibleClosed (X := X) y))
    have hone :
        codimBetween (toIrreducibleCloseds z) (toIrreducibleCloseds y)
          hyz.specializes.toIrreducibleCloseds_le = 1 :=
      pointClosure_codim_eq_one_of_immediateSpecialization hyz
    have htop_finite :
        codimBetween (toIrreducibleCloseds y) (topIrreducibleClosed (X := X))
            (pointClosure_le_topIrreducibleClosed (X := X) y) <
          ⊤ :=
      CatenarySpace.finite_codimBetween
        (pointClosure_le_topIrreducibleClosed (X := X) y)
    dsimp [codim_shift_to_top]
    rw [hyz_add, hone, ENat.toNat_add (by simp) htop_finite.ne, ENat.toNat_one]
    omega

/-- Helper for Lemma 5.20.4: shrink around `x` so that every ambient irreducible component and
every relevant component of a pairwise overlap through a point of the neighborhood also contains
`x`. -/
private theorem exists_component_overlap_neighborhood [NoetherianSpace X] (x : X) :
    ∃ U : Opens X, x ∈ U ∧
      (∀ {y Z}, y ∈ U → Z ∈ irreducibleComponents X → y ∈ Z → x ∈ Z) ∧
      (∀ {y Z Z'}, y ∈ U → Z ∈ irreducibleComponents X → Z' ∈ irreducibleComponents X →
        y ∈ Z → y ∈ Z' →
        ∃ C : IrreducibleCloseds X, (C : Set X) ⊆ Z ∩ Z' ∧ x ∈ (C : Set X) ∧
          y ∈ (C : Set X)) := by
  classical
  let _ : Finite (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  let overlapSet (i j : irreducibleComponents X) : Set X := (i : Set X) ∩ (j : Set X)
  let overlapComponent (i j : irreducibleComponents X) (k : irreducibleComponents (overlapSet i j)) :
      IrreducibleCloseds X :=
    IrreducibleCloseds.map (Subtype.val : overlapSet i j → X) continuous_subtype_val
      ⟨(k : Set (overlapSet i j)), k.2.1,
        isClosed_of_mem_irreducibleComponents (k : Set (overlapSet i j)) k.2⟩
  let Uset : Set X :=
    (⋂ i : irreducibleComponents X,
      if x ∈ (i : Set X) then (Set.univ : Set X) else ((i : Set X)ᶜ)) ∩
    ⋂ i : irreducibleComponents X,
      ⋂ j : irreducibleComponents X,
        ⋂ k : irreducibleComponents (overlapSet i j),
          if x ∈ (overlapComponent i j k : Set X) then (Set.univ : Set X)
          else ((overlapComponent i j k : Set X)ᶜ)
  have hUset_open : IsOpen Uset := by
    refine IsOpen.inter ?_ ?_
    · -- Delete ambient irreducible components that miss `x`.
      refine isOpen_iInter_of_finite ?_
      intro i
      by_cases hxI : x ∈ (i : Set X)
      · simp [hxI]
      · simpa [hxI] using
          (isClosed_of_mem_irreducibleComponents (i : Set X) i.2).isOpen_compl
    · -- For each pair of ambient components, also delete overlap components missing `x`.
      refine isOpen_iInter_of_finite ?_
      intro i
      refine isOpen_iInter_of_finite ?_
      intro j
      let _ : Finite (irreducibleComponents (overlapSet i j)) :=
        NoetherianSpace.finite_irreducibleComponents.to_subtype
      refine isOpen_iInter_of_finite ?_
      intro k
      by_cases hxK : x ∈ (overlapComponent i j k : Set X)
      · simp [hxK]
      · simpa [hxK] using (overlapComponent i j k).isClosed.isOpen_compl
  let U : Opens X := ⟨Uset, hUset_open⟩
  have hxU : x ∈ U := by
    change x ∈ Uset
    constructor
    · refine Set.mem_iInter.2 ?_
      intro i
      by_cases hxI : x ∈ (i : Set X)
      · simp [hxI]
      · simp [hxI]
    · refine Set.mem_iInter.2 ?_
      intro i
      refine Set.mem_iInter.2 ?_
      intro j
      let _ : Finite (irreducibleComponents (overlapSet i j)) :=
        NoetherianSpace.finite_irreducibleComponents.to_subtype
      refine Set.mem_iInter.2 ?_
      intro k
      by_cases hxK : x ∈ (overlapComponent i j k : Set X)
      · simp [hxK]
      · simp [hxK]
  refine ⟨U, hxU, ?_⟩
  refine ⟨?_, ?_⟩
  · intro y Z hyU hZ hyZ
    let i : irreducibleComponents X := ⟨Z, hZ⟩
    have hyi : y ∈ if x ∈ (i : Set X) then (Set.univ : Set X) else ((i : Set X)ᶜ) := by
      exact Set.mem_iInter.mp hyU.1 i
    by_cases hxZ : x ∈ Z
    · exact hxZ
    · have hy_not : y ∈ (Z : Set X)ᶜ := by
        simpa [i, hxZ] using hyi
      exact False.elim (hy_not hyZ)
  · intro y Z Z' hyU hZ hZ' hyZ hyZ'
    let i : irreducibleComponents X := ⟨Z, hZ⟩
    let j : irreducibleComponents X := ⟨Z', hZ'⟩
    let S : Set X := overlapSet i j
    let yS : S := ⟨y, ⟨hyZ, hyZ'⟩⟩
    let k : irreducibleComponents S :=
      ⟨irreducibleComponent yS, irreducibleComponent_mem_irreducibleComponents yS⟩
    let C : IrreducibleCloseds X := overlapComponent i j k
    have hyC : y ∈ (C : Set X) := by
      -- The chosen overlap component contains the point `y`.
      change y ∈ closure ((Subtype.val : S → X) '' ((k : Set S) : Set S))
      exact subset_closure ⟨yS, mem_irreducibleComponent, rfl⟩
    have hfactor :
        y ∈ if x ∈ (C : Set X) then (Set.univ : Set X) else ((C : Set X)ᶜ) := by
      exact Set.mem_iInter.mp (Set.mem_iInter.mp (Set.mem_iInter.mp hyU.2 i) j) k
    have hxC : x ∈ (C : Set X) := by
      by_cases hxC : x ∈ (C : Set X)
      · exact hxC
      · have hy_not : y ∈ ((C : Set X)ᶜ) := by
          simpa [hxC] using hfactor
        exact False.elim (hy_not hyC)
    have hCsub : (C : Set X) ⊆ Z ∩ Z' := by
      -- The mapped overlap component still lives inside the ambient pairwise intersection.
      have hSclosed : IsClosed S := by
        exact (isClosed_of_mem_irreducibleComponents (i : Set X) i.2).inter
          (isClosed_of_mem_irreducibleComponents (j : Set X) j.2)
      have hsubset : (C : Set X) ⊆ S := irreducibleClosed_map_subtype_subset hSclosed _
      simpa [S, overlapSet, i, j] using hsubset
    exact ⟨C, hCsub, hxC, hyC⟩

/-- Helper for Lemma 5.20.4: on the overlap of two ambient irreducible components through `y`, the
codimension-shift expression does not depend on which component is chosen, provided both components
contain the distinguished base point `x` and a common overlap component through `x` and `y`. -/
private theorem codim_shift_eq_of_overlap_component {x y : X} {Z Z' : Set X}
    (hZ : Z ∈ irreducibleComponents X) (hZ' : Z' ∈ irreducibleComponents X)
    (hxZ : x ∈ Z) (hyZ : y ∈ Z) (hxZ' : x ∈ Z') (hyZ' : y ∈ Z')
    {C : IrreducibleCloseds X} (hCZ : (C : Set X) ⊆ Z ∩ Z') (hxC : x ∈ (C : Set X))
    (hyC : y ∈ (C : Set X)) :
    codimShiftIn x ⟨Z, hZ.1, isClosed_of_mem_irreducibleComponents _ hZ⟩ hxZ y hyZ =
      codimShiftIn x ⟨Z', hZ'.1, isClosed_of_mem_irreducibleComponents _ hZ'⟩ hxZ' y hyZ' := by
  let TZ : IrreducibleCloseds X := ⟨Z, hZ.1, isClosed_of_mem_irreducibleComponents _ hZ⟩
  let TZ' : IrreducibleCloseds X := ⟨Z', hZ'.1, isClosed_of_mem_irreducibleComponents _ hZ'⟩
  have hCy : toIrreducibleCloseds y ≤ C := pointClosure_le_of_mem hyC
  have hCx : toIrreducibleCloseds x ≤ C := pointClosure_le_of_mem hxC
  -- Additivity along `closure {y} ⊆ C ⊆ Z` and `closure {x} ⊆ C ⊆ Z` exposes the same middle
  -- codimension term, which cancels.
  have hy_add_Z :
      codimBetween (toIrreducibleCloseds y) TZ (pointClosure_le_of_mem hyZ) =
        codimBetween (toIrreducibleCloseds y) C hCy +
          codimBetween C TZ (fun z hz ↦ (hCZ hz).1) := by
    simpa [TZ] using
      (CatenarySpace.codimBetween_additive (X := X) hCy (fun z hz ↦ (hCZ hz).1))
  have hx_add_Z :
      codimBetween (toIrreducibleCloseds x) TZ (pointClosure_le_of_mem hxZ) =
        codimBetween (toIrreducibleCloseds x) C hCx +
          codimBetween C TZ (fun z hz ↦ (hCZ hz).1) := by
    simpa [TZ] using
      (CatenarySpace.codimBetween_additive (X := X) hCx (fun z hz ↦ (hCZ hz).1))
  have hy_add_Z' :
      codimBetween (toIrreducibleCloseds y) TZ' (pointClosure_le_of_mem hyZ') =
        codimBetween (toIrreducibleCloseds y) C hCy +
          codimBetween C TZ' (fun z hz ↦ (hCZ hz).2) := by
    simpa [TZ'] using
      (CatenarySpace.codimBetween_additive (X := X) hCy (fun z hz ↦ (hCZ hz).2))
  have hx_add_Z' :
      codimBetween (toIrreducibleCloseds x) TZ' (pointClosure_le_of_mem hxZ') =
        codimBetween (toIrreducibleCloseds x) C hCx +
          codimBetween C TZ' (fun z hz ↦ (hCZ hz).2) := by
    simpa [TZ'] using
      (CatenarySpace.codimBetween_additive (X := X) hCx (fun z hz ↦ (hCZ hz).2))
  have hCy_finite : codimBetween (toIrreducibleCloseds y) C hCy < ⊤ :=
    CatenarySpace.finite_codimBetween hCy
  have hCx_finite : codimBetween (toIrreducibleCloseds x) C hCx < ⊤ :=
    CatenarySpace.finite_codimBetween hCx
  have hCZT_finite : codimBetween C TZ (fun z hz ↦ (hCZ hz).1) < ⊤ :=
    CatenarySpace.finite_codimBetween _
  have hCZ'T_finite : codimBetween C TZ' (fun z hz ↦ (hCZ hz).2) < ⊤ :=
    CatenarySpace.finite_codimBetween _
  dsimp [codimShiftIn]
  rw [hy_add_Z, hx_add_Z, hy_add_Z', hx_add_Z']
  rw [ENat.toNat_add hCy_finite.ne hCZT_finite.ne, ENat.toNat_add hCx_finite.ne hCZT_finite.ne,
    ENat.toNat_add hCy_finite.ne hCZ'T_finite.ne,
    ENat.toNat_add hCx_finite.ne hCZ'T_finite.ne]
  omega

/-- Helper for Lemma 5.20.4: on a neighborhood satisfying the ambient-component condition, define
the codimension shift using the ambient irreducible component of each point. -/
private noncomputable def componentCodimShift {U : Opens X} (x : X)
    (hcomponent : ∀ {y Z}, y ∈ U → Z ∈ irreducibleComponents X → y ∈ Z → x ∈ Z) :
    U → ℤ :=
  fun u ↦
    codimShiftIn x (ambientIrreducibleComponent (u : X))
      (hcomponent u.2 (irreducibleComponent_mem_irreducibleComponents (u : X))
        (ambientIrreducibleComponent_mem (u : X)))
      (u : X) (ambientIrreducibleComponent_mem (u : X))

/-- Helper for Lemma 5.20.4: once the neighborhood has the overlap property, the ambient
componentwise codimension-shift function computes specialization differences by the codimension
between point closures. -/
private theorem codim_shift_sub_eq_pointClosure_codim {U : Opens X} (x : X)
    (hcomponent : ∀ {y Z}, y ∈ U → Z ∈ irreducibleComponents X → y ∈ Z → x ∈ Z)
    (hoverlap : ∀ {y Z Z'}, y ∈ U → Z ∈ irreducibleComponents X → Z' ∈ irreducibleComponents X →
      y ∈ Z → y ∈ Z' →
      ∃ C : IrreducibleCloseds X, (C : Set X) ⊆ Z ∩ Z' ∧ x ∈ (C : Set X) ∧
        y ∈ (C : Set X)) :
    ∀ {u v : U} (huv : u ⤳ v),
      componentCodimShift (X := X) x hcomponent u -
          componentCodimShift (X := X) x hcomponent v =
      (ENat.toNat
        (codimBetween (toIrreducibleCloseds (v : X)) (toIrreducibleCloseds (u : X))
          ((subtype_specializes_iff u v).1 huv).toIrreducibleCloseds_le) : ℤ) := by
  intro u v huv
  have huvX : (u : X) ⤳ v := (subtype_specializes_iff u v).1 huv
  have hxComp_u : x ∈ (ambientIrreducibleComponent (u : X) : Set X) :=
    hcomponent u.2 (irreducibleComponent_mem_irreducibleComponents (u : X))
      (ambientIrreducibleComponent_mem (u : X))
  have hvComp_u : (v : X) ∈ (ambientIrreducibleComponent (u : X) : Set X) :=
    huvX.mem_closed (ambientIrreducibleComponent (u : X)).isClosed
      (ambientIrreducibleComponent_mem (u : X))
  have hvComp_v : (v : X) ∈ (ambientIrreducibleComponent (v : X) : Set X) :=
    ambientIrreducibleComponent_mem (v : X)
  -- Rewrite the `v`-term so both codimension shifts are computed in the same ambient component.
  obtain ⟨C, hCsub, hxC, hvC⟩ :=
    hoverlap v.2 (irreducibleComponent_mem_irreducibleComponents (u : X))
      (irreducibleComponent_mem_irreducibleComponents (v : X)) hvComp_u hvComp_v
  have hrewrite :
      codimShiftIn x (ambientIrreducibleComponent (v : X))
          (hcomponent v.2 (irreducibleComponent_mem_irreducibleComponents (v : X))
            (ambientIrreducibleComponent_mem (v : X)))
          (v : X) (ambientIrreducibleComponent_mem (v : X)) =
        codimShiftIn x (ambientIrreducibleComponent (u : X)) hxComp_u (v : X) hvComp_u := by
    simpa [ambientIrreducibleComponent] using
      (codim_shift_eq_of_overlap_component
        (X := X)
        (hZ := irreducibleComponent_mem_irreducibleComponents (v : X))
        (hZ' := irreducibleComponent_mem_irreducibleComponents (u : X))
        (hxZ := hcomponent v.2 (irreducibleComponent_mem_irreducibleComponents (v : X))
          (ambientIrreducibleComponent_mem (v : X)))
        (hyZ := ambientIrreducibleComponent_mem (v : X))
        (hxZ' := hxComp_u)
        (hyZ' := hvComp_u)
        (hCZ := by simpa [Set.inter_comm] using hCsub)
        (hxC := hxC)
        (hyC := hvC))
  have huv_add :
      codimBetween (toIrreducibleCloseds (v : X)) (ambientIrreducibleComponent (u : X))
          (pointClosure_le_of_mem hvComp_u) =
        codimBetween (toIrreducibleCloseds (v : X)) (toIrreducibleCloseds (u : X))
            huvX.toIrreducibleCloseds_le +
          codimBetween (toIrreducibleCloseds (u : X)) (ambientIrreducibleComponent (u : X))
            (pointClosure_le_of_mem (ambientIrreducibleComponent_mem (u : X))) := by
    -- Additivity in the chain `closure {v} ⊆ closure {u} ⊆ IrrComp(u)` gives the claimed
    -- difference formula.
    simpa [ambientIrreducibleComponent] using
      (CatenarySpace.codimBetween_additive (X := X) huvX.toIrreducibleCloseds_le
        (pointClosure_le_of_mem (ambientIrreducibleComponent_mem (u : X))))
  have huv_finite :
      codimBetween (toIrreducibleCloseds (v : X)) (toIrreducibleCloseds (u : X))
          huvX.toIrreducibleCloseds_le <
        ⊤ :=
    CatenarySpace.finite_codimBetween huvX.toIrreducibleCloseds_le
  have huComp_finite :
      codimBetween (toIrreducibleCloseds (u : X)) (ambientIrreducibleComponent (u : X))
          (pointClosure_le_of_mem (ambientIrreducibleComponent_mem (u : X))) <
        ⊤ :=
    CatenarySpace.finite_codimBetween _
  dsimp [componentCodimShift]
  rw [hrewrite]
  dsimp [codimShiftIn]
  rw [huv_add, ENat.toNat_add huv_finite.ne huComp_finite.ne]
  omega

/-- Helper for Lemma 5.20.4: an immediate specialization inside an open subset is still immediate
after forgetting the subtype. -/
private theorem ambient_immediate_specialization {U : Opens X} {u v : U}
    (huv : IsImmediateSpecialization u v) : IsImmediateSpecialization (u : X) v := by
  refine ⟨(subtype_specializes_iff u v).1 huv.specializes, ?_, ?_⟩
  · intro h
    exact huv.ne (Subtype.ext h)
  · intro z huz hzv
    have hzU : z ∈ (U : Set X) := hzv.mem_open U.2 v.2
    let zU : U := ⟨z, hzU⟩
    have huzU : u ⤳ zU := (subtype_specializes_iff u zU).2 huz
    have hzUv : zU ⤳ v := (subtype_specializes_iff zU v).2 hzv
    rcases huv.eq_or_eq huzU hzUv with h | h
    · left
      exact congrArg Subtype.val h
    · right
      exact congrArg Subtype.val h

/-- Helper for Lemma 5.20.4: the ambient codimension-shift function on the chosen neighborhood
satisfies the dimension-function axioms. -/
private theorem codim_shift_isDimensionFunction {U : Opens X} (δ : U → ℤ)
    (hsub : ∀ {u v : U} (huv : u ⤳ v), δ u - δ v =
      (ENat.toNat
        (codimBetween (toIrreducibleCloseds (v : X)) (toIrreducibleCloseds (u : X))
          ((subtype_specializes_iff u v).1 huv).toIrreducibleCloseds_le) : ℤ)) :
    IsDimensionFunction δ where
  strict_of_specializes := by
    intro u v huv huv_ne
    have huvX : (u : X) ⤳ v := (subtype_specializes_iff u v).1 huv
    -- Proper specialization gives positive point-closure codimension, so the difference is
    -- positive.
    have hpos :=
      pointClosure_codim_pos_of_proper_specializes huvX fun h ↦ huv_ne (Subtype.ext h)
    have hfinite :=
      CatenarySpace.finite_codimBetween huvX.toIrreducibleCloseds_le
    have hnat :
        0 <
          ENat.toNat
            (codimBetween (toIrreducibleCloseds (v : X)) (toIrreducibleCloseds (u : X))
              huvX.toIrreducibleCloseds_le) := by
      exact Nat.pos_of_ne_zero fun hzero ↦
        hpos.ne' <| by
          rw [← ENat.coe_toNat hfinite.ne, hzero]
          rfl
    have hnat_int :
        (0 : ℤ) <
          ENat.toNat
            (codimBetween (toIrreducibleCloseds (v : X)) (toIrreducibleCloseds (u : X))
              huvX.toIrreducibleCloseds_le) := by
      exact_mod_cast hnat
    have hsub_uv := hsub huv
    linarith
  eq_add_one_of_immediateSpecialization := by
    intro u v huv
    -- Immediate specializations in the open subtype remain immediate in the ambient space.
    have huvX : IsImmediateSpecialization (u : X) v := ambient_immediate_specialization huv
    have hsub_uv : δ u - δ v = 1 := by
      have hsub_uv := hsub huv.specializes
      rw [pointClosure_codim_eq_one_of_immediateSpecialization huvX] at hsub_uv
      simpa using hsub_uv
    linarith

/-- Helper for Lemma 5.20.4: in the Noetherian case, the source proof shrinks around `x` so that a
componentwise codimension shift defines a dimension function. -/
private theorem exists_open_neighborhood_with_dimensionFunction_of_noetherian
    [NoetherianSpace X] (x : X) :
    ∃ U : Opens X, x ∈ U ∧ ∃ δ : U → ℤ, IsDimensionFunction δ := by
  classical
  -- Route correction: the proof stays in ambient irreducible components of `X`, then shrinks the
  -- open neighborhood until the componentwise codimension shifts agree on every overlap.
  obtain ⟨U, hxU, hcomponent, hoverlap⟩ :=
    exists_component_overlap_neighborhood (X := X) x
  let δ : U → ℤ := componentCodimShift (X := X) x hcomponent
  have hsub :
      ∀ {u v : U} (huv : u ⤳ v), δ u - δ v =
        (ENat.toNat
          (codimBetween (toIrreducibleCloseds (v : X)) (toIrreducibleCloseds (u : X))
            ((subtype_specializes_iff u v).1 huv).toIrreducibleCloseds_le) : ℤ) :=
    codim_shift_sub_eq_pointClosure_codim (X := X) x hcomponent hoverlap
  have hδ : IsDimensionFunction δ := codim_shift_isDimensionFunction δ hsub
  exact ⟨U, hxU, δ, hδ⟩

-- Proof sketch: choose a Noetherian open neighbourhood of `x` using local Noetherianity, solve the
-- problem inside that open subspace, and then transport the resulting dimension function back to
-- the corresponding ambient open subset through the canonical open embedding.
/-- Lemma 5.20.4: in a locally Noetherian, sober, catenary space, every point has an open
neighbourhood whose induced topology admits a dimension function. -/
theorem exists_open_neighborhood_with_dimensionFunction (x : X) :
    ∃ U : Opens X, x ∈ U ∧ ∃ δ : U → ℤ, IsDimensionFunction δ := by
  rcases LocallyNoetherianSpace.exists_open x with ⟨N, hxN, hN_noetherian⟩
  let xN : N := ⟨x, hxN⟩
  letI : NoetherianSpace N := hN_noetherian
  letI : QuasiSober N := N.2.isLocallyClosed.quasiSober
  letI : CatenarySpace N := N.2.isLocallyClosed.catenarySpace
  obtain ⟨V, hxV, δ, hδ⟩ :=
    exists_open_neighborhood_with_dimensionFunction_of_noetherian (X := N) xN
  let f : V → X := fun v ↦ v.1.1
  have hfV : Topology.IsOpenEmbedding (fun v : V ↦ (v : N)) := V.isOpenEmbedding'
  have hfN : Topology.IsOpenEmbedding (fun n : N ↦ (n : X)) := N.isOpenEmbedding'
  have hf : Topology.IsOpenEmbedding f := by
    simpa [f] using hfN.comp hfV
  let W : Opens X := ⟨Set.range f, hf.isOpen_range⟩
  have hxW : x ∈ W := by
    exact ⟨⟨xN, hxV⟩, rfl⟩
  let e0 : (Set.univ : Set V) ≃ₜ (f '' (Set.univ : Set V)) :=
    hf.isEmbedding.homeomorphImage Set.univ
  let e1 : V ≃ₜ (Set.univ : Set V) := (Homeomorph.Set.univ V).symm
  let e2 : (f '' (Set.univ : Set V)) ≃ₜ W := Homeomorph.setCongr (by
    ext z
    constructor
    · intro hz
      simpa [W] using hz
    · intro hz
      simpa [W] using hz)
  let e : V ≃ₜ W := e1.trans (e0.trans e2)
  let δW : W → ℤ := fun w ↦ δ (e.symm w)
  have hδW : IsDimensionFunction δW := e.isDimensionFunction_comp_symm hδ
  -- The open subset produced inside the Noetherian neighbourhood pushes forward to an ambient
  -- open neighbourhood of `x`.
  exact ⟨W, hxW, δW, hδW⟩

/-! ### Remark_5_20_5 (from Chap05) -/
open CategoryTheory TopologicalSpace

universe u

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for Remark 5.20.5:
- primary domain: dimension functions on topological spaces and first sheaf cohomology of the
  constant integer sheaf
- same-domain declarations inspected:
  `IsDimensionFunction` in `Definition_5_20_1`
  `IsDimensionFunction.isLocallyConstant_sub` in `Lemma_5_20_3`
  `exists_open_neighborhood_with_dimensionFunction` in `Lemma_5_20_4`
  direct `H 1` owner usage in `TopologicalSpace.SheafCohomology.squareZeroBoundaryClass`

Owner-abstraction choice:
- `source-facing`: the obstruction-class existence statement of the remark
- `core/canonical`: `IsDimensionFunction` and the canonical cohomology object
  `((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (AddCommGrpCat.of (ULift ℤ))).H 1`
- `bridge/view`: the vanishing criterion relating a cohomology class to a global dimension
  function

Primitive data versus derived API:
- primitive data already lives in the upstream owner `IsDimensionFunction` and in the local
  existence/difference lemmas `Lemma_5_20_3` and `Lemma_5_20_4`
- this file should therefore contribute only the derived cohomological existence statement, not a
  parallel local alias for the canonical `H^1` type or for its vanishing specification
-/

-- Proof sketch: Lemma 5.20.4 gives local dimension functions on a catenary locally Noetherian
-- sober space, and Lemma 5.20.3 identifies the differences of two such local functions on overlaps
-- with locally constant integer-valued functions. These transition functions define a Cech
-- 1-cocycle for the constant integer sheaf, hence an obstruction class in `H^1(X, \underline Z)`;
-- its vanishing is equivalent to gluing the local dimension functions to a global one.
/-- Remark 5.20.5, formalized at the level currently available in the imported API: on a catenary,
locally Noetherian, sober topological space, local dimension functions exist around every point.
The Stacks remark packages the gluing obstruction for these local functions as an `H^1` class; the
corresponding boundary/obstruction-class construction is not available in the current mathlib
interface, so this statement records the dependency-closed local data from which that class would
be built. -/
theorem exists_dimensionFunction_obstruction_class
    [LocallyNoetherianSpace X] [T0Space X] [QuasiSober X] [CatenarySpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
    [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)] :
    ∀ x : X, ∃ U : Opens X, x ∈ U ∧ ∃ δ : U → ℤ, IsDimensionFunction δ := by
  intro x
  exact exists_open_neighborhood_with_dimensionFunction x
