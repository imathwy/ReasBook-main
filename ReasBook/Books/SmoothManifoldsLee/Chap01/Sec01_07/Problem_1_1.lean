import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- The subset `X ⊆ ℝ²` consisting of the two horizontal lines `y = 1` and `y = -1`. -/
def problem1LineWithTwoOriginsPoints : Set (ℝ × ℝ) :=
  { p | p.2 = 1 ∨ p.2 = -1 }

/-- The point space `X` before taking the quotient in the line-with-two-origins construction. -/
abbrev problem1LineWithTwoOriginsPoint : Type :=
  ↥problem1LineWithTwoOriginsPoints

/-- The upper point `(0, 1)` in the two-line model `X`. -/
def problem1LineWithTwoOriginsUpperPoint : problem1LineWithTwoOriginsPoint :=
  ⟨(0, 1), Or.inl rfl⟩

/-- The lower point `(0, -1)` in the two-line model `X`. -/
def problem1LineWithTwoOriginsLowerPoint : problem1LineWithTwoOriginsPoint :=
  ⟨(0, -1), Or.inr rfl⟩

/-- Two points of `X` are equivalent when they have the same `x`-coordinate, and the
`y`-coordinate is remembered only over `x = 0`. This is the quotient relation that identifies
`(x, -1)` with `(x, 1)` for every nonzero `x`. -/
def problem1LineWithTwoOriginsRel (p q : problem1LineWithTwoOriginsPoint) : Prop :=
  p.1.1 = q.1.1 ∧ (p.1.1 ≠ 0 ∨ p.1.2 = q.1.2)

/- The next three lemmas provide the equivalence-relation axioms for the quotient relation. -/

/-- The line-with-two-origins relation is reflexive. -/
-- Proof sketch: the `x`-coordinates agree by reflexivity, and the `y`-coordinates agree
-- tautologically.
theorem problem1LineWithTwoOriginsRel_refl (p : problem1LineWithTwoOriginsPoint) :
    problem1LineWithTwoOriginsRel p p := by
  -- Both coordinates agree with themselves, so the remembered `y`-coordinate matches trivially.
  exact ⟨rfl, Or.inr rfl⟩

/-- The line-with-two-origins relation is symmetric. -/
-- Proof sketch: symmetry preserves equality of `x`-coordinates, and the second clause is symmetric
-- because either the common `x`-coordinate is nonzero or the `y`-coordinates are equal.
theorem problem1LineWithTwoOriginsRel_symm {p q : problem1LineWithTwoOriginsPoint}
    (hpq : problem1LineWithTwoOriginsRel p q) : problem1LineWithTwoOriginsRel q p := by
  rcases hpq with ⟨hxy, hbranch⟩
  -- Reversing the pair keeps the common `x`-coordinate and flips the `y`-equality.
  refine ⟨hxy.symm, ?_⟩
  rcases hbranch with hx | hy
  · exact Or.inl fun hq => hx (hxy.trans hq)
  · exact Or.inr hy.symm

/-- The line-with-two-origins relation is transitive. -/
-- Proof sketch: equality of `x`-coordinates is transitive. If the common `x`-coordinate is
-- nonzero, the second clause is automatic; if it is `0`, the intermediate equalities of
-- `y`-coordinates force the endpoints to have the same `y`-coordinate.
theorem problem1LineWithTwoOriginsRel_trans {p q r : problem1LineWithTwoOriginsPoint}
    (hpq : problem1LineWithTwoOriginsRel p q) (hqr : problem1LineWithTwoOriginsRel q r) :
    problem1LineWithTwoOriginsRel p r := by
  rcases hpq with ⟨hpq_x, hpq_branch⟩
  rcases hqr with ⟨hqr_x, hqr_branch⟩
  -- The `x`-coordinate is the global invariant carried through the quotient.
  refine ⟨hpq_x.trans hqr_x, ?_⟩
  by_cases hx : p.1.1 = 0
  · -- Over `x = 0`, both relation hypotheses must come from equal `y`-coordinates.
    right
    have hq0 : q.1.1 = 0 := by exact hpq_x ▸ hx
    have hr0 : r.1.1 = 0 := by exact hqr_x ▸ hq0
    have hpq_y : p.1.2 = q.1.2 := by
      rcases hpq_branch with hp0 | hy
      · exact False.elim (hp0 hx)
      · exact hy
    have hqr_y : q.1.2 = r.1.2 := by
      rcases hqr_branch with hq0' | hy
      · exact False.elim (hq0' hq0)
      · exact hy
    exact hpq_y.trans hqr_y
  · -- Away from `x = 0`, the quotient forgets the `y`-coordinate entirely.
    exact Or.inl hx

/-- The setoid on `X` defining Lee's line with two origins. -/
def problem1LineWithTwoOriginsSetoid : Setoid problem1LineWithTwoOriginsPoint where
  r := problem1LineWithTwoOriginsRel
  iseqv :=
    ⟨problem1LineWithTwoOriginsRel_refl, problem1LineWithTwoOriginsRel_symm,
      problem1LineWithTwoOriginsRel_trans⟩

/-- Helper for Problem 1-1: expose the quotient relation as the ambient setoid on `X`. -/
instance : Setoid problem1LineWithTwoOriginsPoint :=
  problem1LineWithTwoOriginsSetoid

/-- The quotient space `M` obtained from the two horizontal lines by identifying the points with
the same nonzero `x`-coordinate. -/
abbrev problem1LineWithTwoOrigins : Type :=
  Quotient problem1LineWithTwoOriginsSetoid

/-- The upper origin of the line with two origins. -/
def problem1LineWithTwoOriginsUpperOrigin : problem1LineWithTwoOrigins :=
  ⟦problem1LineWithTwoOriginsUpperPoint⟧

/-- The lower origin of the line with two origins. -/
def problem1LineWithTwoOriginsLowerOrigin : problem1LineWithTwoOrigins :=
  ⟦problem1LineWithTwoOriginsLowerPoint⟧

/-- Helper for Problem 1-1: the quotient remembers only the `x`-coordinate of a class. -/
def problem1LineWithTwoOriginsXCoord : problem1LineWithTwoOrigins → ℝ :=
  Quotient.lift (fun p => p.1.1) fun _ _ h => h.1

/-- Helper for Problem 1-1: the upper branch parametrizes the quotient by classes of `(x, 1)`. -/
def problem1LineWithTwoOriginsUpperBranch (x : ℝ) : problem1LineWithTwoOrigins :=
  ⟦⟨(x, 1), Or.inl rfl⟩⟧

/-- Helper for Problem 1-1: the lower branch parametrizes the quotient by classes of `(x, -1)`. -/
def problem1LineWithTwoOriginsLowerBranch (x : ℝ) : problem1LineWithTwoOrigins :=
  ⟦⟨(x, -1), Or.inr rfl⟩⟧

/-- Helper for Problem 1-1: the quotient `x`-coordinate of the upper branch is the parameter. -/
lemma problem1LineWithTwoOrigins_xCoord_upper_branch (x : ℝ) :
    problem1LineWithTwoOriginsXCoord (problem1LineWithTwoOriginsUpperBranch x) = x := by
  rfl

/-- Helper for Problem 1-1: the quotient `x`-coordinate of the lower branch is the parameter. -/
lemma problem1LineWithTwoOrigins_xCoord_lower_branch (x : ℝ) :
    problem1LineWithTwoOriginsXCoord (problem1LineWithTwoOriginsLowerBranch x) = x := by
  rfl

/-- Helper for Problem 1-1: the two branches are identified away from `x = 0`. -/
lemma problem1LineWithTwoOrigins_upper_eq_lower_branch {x : ℝ} (hx : x ≠ 0) :
    problem1LineWithTwoOriginsUpperBranch x = problem1LineWithTwoOriginsLowerBranch x := by
  -- The quotient relation identifies the two points with the same nonzero `x`-coordinate.
  exact Quotient.sound ⟨rfl, Or.inl hx⟩

/-- Helper for Problem 1-1: the two origins represent distinct quotient classes. -/
lemma problem1LineWithTwoOriginsUpperOrigin_ne_lowerOrigin :
    problem1LineWithTwoOriginsUpperOrigin ≠ problem1LineWithTwoOriginsLowerOrigin := by
  intro h
  -- If the origins were equal, the quotient relation would force `1 = -1`.
  have hrel :
      problem1LineWithTwoOriginsRel problem1LineWithTwoOriginsUpperPoint
        problem1LineWithTwoOriginsLowerPoint :=
    Quotient.exact h
  rcases hrel with ⟨_, hbranch⟩
  rcases hbranch with hzero | hy
  · exact hzero rfl
  · have hy' : (1 : ℝ) = -1 := by
        simpa [problem1LineWithTwoOriginsUpperPoint, problem1LineWithTwoOriginsLowerPoint] using hy
    norm_num at hy'

/-- Helper for Problem 1-1: every upper-branch point avoids the lower origin. -/
lemma problem1LineWithTwoOrigins_upper_branch_ne_lower_origin (x : ℝ) :
    problem1LineWithTwoOriginsUpperBranch x ≠ problem1LineWithTwoOriginsLowerOrigin := by
  intro h
  -- Equality with the lower origin would force the representative `(x, 1)` to have `y = -1`.
  have hrel :
      problem1LineWithTwoOriginsRel ⟨(x, 1), Or.inl rfl⟩ problem1LineWithTwoOriginsLowerPoint :=
    Quotient.exact h
  rcases hrel with ⟨hx, hbranch⟩
  rcases hbranch with hne | hy
  · exact hne hx
  · have hy' : (1 : ℝ) = -1 := by
        simpa [problem1LineWithTwoOriginsLowerPoint] using hy
    norm_num at hy'

/-- Helper for Problem 1-1: every lower-branch point avoids the upper origin. -/
lemma problem1LineWithTwoOrigins_lower_branch_ne_upper_origin (x : ℝ) :
    problem1LineWithTwoOriginsLowerBranch x ≠ problem1LineWithTwoOriginsUpperOrigin := by
  intro h
  -- Equality with the upper origin would force the representative `(x, -1)` to have `y = 1`.
  have hrel :
      problem1LineWithTwoOriginsRel ⟨(x, -1), Or.inr rfl⟩ problem1LineWithTwoOriginsUpperPoint :=
    Quotient.exact h
  rcases hrel with ⟨hx, hbranch⟩
  rcases hbranch with hne | hy
  · exact hne hx
  · have hy' : (-1 : ℝ) = 1 := by
        simpa [problem1LineWithTwoOriginsUpperPoint] using hy
    norm_num at hy'

/-- Helper for Problem 1-1: a class different from the lower origin is represented on the upper
branch by its common `x`-coordinate. -/
lemma problem1LineWithTwoOrigins_upper_branch_eq_of_ne_lower_origin
    (p : problem1LineWithTwoOriginsPoint)
    (hp : ⟦p⟧ ≠ problem1LineWithTwoOriginsLowerOrigin) :
    problem1LineWithTwoOriginsUpperBranch p.1.1 = ⟦p⟧ := by
  rcases p.2 with hp_y | hp_y
  · -- On the upper branch the representative already has the desired form.
    exact Quotient.sound ⟨rfl, Or.inr hp_y.symm⟩
  · -- On the lower branch, being different from the lower origin forces `x ≠ 0`.
    have hx : p.1.1 ≠ 0 := by
      intro hx0
      apply hp
      exact Quotient.sound ⟨hx0, Or.inr hp_y⟩
    calc
      problem1LineWithTwoOriginsUpperBranch p.1.1 =
          problem1LineWithTwoOriginsLowerBranch p.1.1 :=
        problem1LineWithTwoOrigins_upper_eq_lower_branch hx
      _ = ⟦p⟧ := by
        exact Quotient.sound ⟨rfl, Or.inr hp_y.symm⟩

/-- Helper for Problem 1-1: a class different from the upper origin is represented on the lower
branch by its common `x`-coordinate. -/
lemma problem1LineWithTwoOrigins_lower_branch_eq_of_ne_upper_origin
    (p : problem1LineWithTwoOriginsPoint)
    (hp : ⟦p⟧ ≠ problem1LineWithTwoOriginsUpperOrigin) :
    problem1LineWithTwoOriginsLowerBranch p.1.1 = ⟦p⟧ := by
  rcases p.2 with hp_y | hp_y
  · -- On the upper branch, being different from the upper origin forces `x ≠ 0`.
    have hx : p.1.1 ≠ 0 := by
      intro hx0
      apply hp
      exact Quotient.sound ⟨hx0, Or.inr hp_y⟩
    calc
      problem1LineWithTwoOriginsLowerBranch p.1.1 =
          problem1LineWithTwoOriginsUpperBranch p.1.1 := by
        symm
        exact problem1LineWithTwoOrigins_upper_eq_lower_branch hx
      _ = ⟦p⟧ := by
        exact Quotient.sound ⟨rfl, Or.inr hp_y.symm⟩
  · -- On the lower branch the representative already has the desired form.
    exact Quotient.sound ⟨rfl, Or.inr hp_y.symm⟩

/-- Helper for Problem 1-1: the upper branch recovers every class except the lower origin. -/
lemma problem1LineWithTwoOrigins_upper_branch_xCoord
    {q : problem1LineWithTwoOrigins} (hq : q ≠ problem1LineWithTwoOriginsLowerOrigin) :
    problem1LineWithTwoOriginsUpperBranch (problem1LineWithTwoOriginsXCoord q) = q := by
  -- Prove the statement by quotient induction, carrying the non-lower-origin hypothesis along.
  refine Quotient.inductionOn q ?_ hq
  intro p hp
  simpa [problem1LineWithTwoOriginsXCoord] using
    problem1LineWithTwoOrigins_upper_branch_eq_of_ne_lower_origin p hp

/-- Helper for Problem 1-1: the lower branch recovers every class except the upper origin. -/
lemma problem1LineWithTwoOrigins_lower_branch_xCoord
    {q : problem1LineWithTwoOrigins} (hq : q ≠ problem1LineWithTwoOriginsUpperOrigin) :
    problem1LineWithTwoOriginsLowerBranch (problem1LineWithTwoOriginsXCoord q) = q := by
  -- Prove the statement by quotient induction, carrying the non-upper-origin hypothesis along.
  refine Quotient.inductionOn q ?_ hq
  intro p hp
  simpa [problem1LineWithTwoOriginsXCoord] using
    problem1LineWithTwoOrigins_lower_branch_eq_of_ne_upper_origin p hp

/-- Helper for Problem 1-1: the quotient coordinate descends continuously to the quotient. -/
lemma problem1LineWithTwoOrigins_continuous_xCoord :
    Continuous problem1LineWithTwoOriginsXCoord := by
  -- The prequotient coordinate map is continuous and constant on equivalence classes.
  have hf : Continuous (fun p : problem1LineWithTwoOriginsPoint => p.1.1) := by
    simpa using (continuous_fst.comp continuous_subtype_val)
  simpa [problem1LineWithTwoOriginsXCoord] using
    (Continuous.quotient_liftOn' (s := problem1LineWithTwoOriginsSetoid)
      (f := fun p : problem1LineWithTwoOriginsPoint => p.1.1) hf fun _ _ h => h.1)

/-- Helper for Problem 1-1: the upper branch is a continuous map into the quotient. -/
lemma problem1LineWithTwoOrigins_continuous_upper_branch :
    Continuous problem1LineWithTwoOriginsUpperBranch := by
  -- The upper branch is the quotient projection composed with the continuous inclusion
  -- `x ↦ (x, 1)`.
  have hinc :
      Continuous
        (fun x : ℝ => (⟨((x, 1) : ℝ × ℝ), Or.inl rfl⟩ : problem1LineWithTwoOriginsPoint)) := by
    exact
      (show Continuous fun x : ℝ => ((x, (1 : ℝ)) : ℝ × ℝ) by continuity).subtype_mk
        fun _ => Or.inl rfl
  simpa [problem1LineWithTwoOriginsUpperBranch] using continuous_quotient_mk'.comp hinc

/-- Helper for Problem 1-1: the lower branch is a continuous map into the quotient. -/
lemma problem1LineWithTwoOrigins_continuous_lower_branch :
    Continuous problem1LineWithTwoOriginsLowerBranch := by
  -- The lower branch is the quotient projection composed with the continuous inclusion
  -- `x ↦ (x, -1)`.
  have hinc :
      Continuous
        (fun x : ℝ => (⟨((x, -1) : ℝ × ℝ), Or.inr rfl⟩ : problem1LineWithTwoOriginsPoint)) := by
    exact
      (show Continuous fun x : ℝ => ((x, (-1 : ℝ)) : ℝ × ℝ) by continuity).subtype_mk
        fun _ => Or.inr rfl
  simpa [problem1LineWithTwoOriginsLowerBranch] using continuous_quotient_mk'.comp hinc

/-- Helper for Problem 1-1: the quotient preimage of the upper chart domain is an elementary
open subset of the two-line model. -/
lemma problem1LineWithTwoOrigins_preimage_upper_chart_domain :
    (Quotient.mk' : problem1LineWithTwoOriginsPoint → problem1LineWithTwoOrigins) ⁻¹'
        {q : problem1LineWithTwoOrigins | q ≠ problem1LineWithTwoOriginsLowerOrigin} =
      {p : problem1LineWithTwoOriginsPoint | 0 < p.1.2 ∨ p.1.1 ≠ 0} := by
  ext p
  rcases p.2 with hp_y | hp_y
  · -- Points on the upper branch never map to the lower origin.
    constructor
    · intro _
      left
      simp [hp_y]
    · intro _ hq
      apply problem1LineWithTwoOrigins_upper_branch_ne_lower_origin p.1.1
      have hp_eq : problem1LineWithTwoOriginsUpperBranch p.1.1 = ⟦p⟧ := by
        exact Quotient.sound ⟨rfl, Or.inr hp_y.symm⟩
      exact hp_eq.trans hq
  · -- Points on the lower branch avoid the lower origin exactly when `x ≠ 0`.
    constructor
    · intro hp
      right
      intro hx
      apply hp
      exact Quotient.sound ⟨hx, Or.inr hp_y⟩
    · intro hp
      rcases hp with hp_pos | hx
      · linarith [hp_y]
      · intro hq
        have hrel :
            problem1LineWithTwoOriginsRel p problem1LineWithTwoOriginsLowerPoint :=
          Quotient.exact hq
        exact hx hrel.1

/-- Helper for Problem 1-1: the quotient preimage of the lower chart domain is an elementary
open subset of the two-line model. -/
lemma problem1LineWithTwoOrigins_preimage_lower_chart_domain :
    (Quotient.mk' : problem1LineWithTwoOriginsPoint → problem1LineWithTwoOrigins) ⁻¹'
        {q : problem1LineWithTwoOrigins | q ≠ problem1LineWithTwoOriginsUpperOrigin} =
      {p : problem1LineWithTwoOriginsPoint | p.1.2 < 0 ∨ p.1.1 ≠ 0} := by
  ext p
  rcases p.2 with hp_y | hp_y
  · -- Points on the upper branch avoid the upper origin exactly when `x ≠ 0`.
    constructor
    · intro hp
      right
      intro hx
      apply hp
      exact Quotient.sound ⟨hx, Or.inr hp_y⟩
    · intro hp
      rcases hp with hp_neg | hx
      · linarith [hp_y]
      · intro hq
        have hrel :
            problem1LineWithTwoOriginsRel p problem1LineWithTwoOriginsUpperPoint :=
          Quotient.exact hq
        exact hx hrel.1
  · -- Points on the lower branch never map to the upper origin.
    constructor
    · intro _
      left
      simp [hp_y]
    · intro _ hq
      apply problem1LineWithTwoOrigins_lower_branch_ne_upper_origin p.1.1
      have hp_eq : problem1LineWithTwoOriginsLowerBranch p.1.1 = ⟦p⟧ := by
        exact Quotient.sound ⟨rfl, Or.inr hp_y.symm⟩
      exact hp_eq.trans hq

/-- Helper for Problem 1-1: the complement of the lower origin is open. -/
lemma problem1LineWithTwoOrigins_upper_chart_domain_isOpen :
    IsOpen {q : problem1LineWithTwoOrigins | q ≠ problem1LineWithTwoOriginsLowerOrigin} := by
  -- Route correction: prove openness through the quotient preimage, where the set becomes a
  -- simple union of open branch conditions.
  change
    IsOpen
      ((Quotient.mk' : problem1LineWithTwoOriginsPoint → problem1LineWithTwoOrigins) ⁻¹'
        {q : problem1LineWithTwoOrigins | q ≠ problem1LineWithTwoOriginsLowerOrigin})
  rw [problem1LineWithTwoOrigins_preimage_upper_chart_domain]
  have hy :
      IsOpen {p : problem1LineWithTwoOriginsPoint | 0 < p.1.2} := by
    simpa using
      isOpen_lt continuous_const (continuous_snd.comp continuous_subtype_val)
  have hx :
      IsOpen {p : problem1LineWithTwoOriginsPoint | p.1.1 ≠ 0} := by
    simpa using isOpen_ne.preimage (continuous_fst.comp continuous_subtype_val)
  exact hy.union hx

/-- Helper for Problem 1-1: the complement of the upper origin is open. -/
lemma problem1LineWithTwoOrigins_lower_chart_domain_isOpen :
    IsOpen {q : problem1LineWithTwoOrigins | q ≠ problem1LineWithTwoOriginsUpperOrigin} := by
  -- Route correction: as above, the quotient preimage is a union of open half-branch conditions.
  change
    IsOpen
      ((Quotient.mk' : problem1LineWithTwoOriginsPoint → problem1LineWithTwoOrigins) ⁻¹'
        {q : problem1LineWithTwoOrigins | q ≠ problem1LineWithTwoOriginsUpperOrigin})
  rw [problem1LineWithTwoOrigins_preimage_lower_chart_domain]
  have hy :
      IsOpen {p : problem1LineWithTwoOriginsPoint | p.1.2 < 0} := by
    simpa using
      isOpen_lt (continuous_snd.comp continuous_subtype_val) continuous_const
  have hx :
      IsOpen {p : problem1LineWithTwoOriginsPoint | p.1.1 ≠ 0} := by
    simpa using isOpen_ne.preimage (continuous_fst.comp continuous_subtype_val)
  exact hy.union hx

/-- Helper for Problem 1-1: the complement of the lower origin is globally parameterized by the
upper branch. -/
lemma problem1LineWithTwoOrigins_upper_chart_homeomorph :
    Nonempty ({q : problem1LineWithTwoOrigins | q ≠ problem1LineWithTwoOriginsLowerOrigin} ≃ₜ
      (Set.univ : Set ℝ)) := by
  refine ⟨
    { toFun := fun q => ⟨problem1LineWithTwoOriginsXCoord q.1, by simp⟩
      invFun := fun x =>
        ⟨problem1LineWithTwoOriginsUpperBranch x.1,
          problem1LineWithTwoOrigins_upper_branch_ne_lower_origin x.1⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }⟩
  · intro q
    -- Every class in the upper chart is recovered by following its `x`-coordinate back up
    -- the upper branch.
    apply Subtype.ext
    exact problem1LineWithTwoOrigins_upper_branch_xCoord q.2
  · intro x
    -- On the upper branch the quotient coordinate is visibly the original parameter.
    apply Subtype.ext
    simp [problem1LineWithTwoOrigins_xCoord_upper_branch]
  · -- Continuity of the chart map is continuity of `xCoord`, with a trivial subtype target.
    exact
      (problem1LineWithTwoOrigins_continuous_xCoord.comp continuous_subtype_val).subtype_mk
        fun _ => by simp
  · -- Continuity of the inverse is continuity of the upper branch, again with a trivial subtype
    -- target.
    exact
      (problem1LineWithTwoOrigins_continuous_upper_branch.comp continuous_subtype_val).subtype_mk
        fun x => problem1LineWithTwoOrigins_upper_branch_ne_lower_origin x.1

/-- Helper for Problem 1-1: the complement of the upper origin is globally parameterized by the
lower branch. -/
lemma problem1LineWithTwoOrigins_lower_chart_homeomorph :
    Nonempty ({q : problem1LineWithTwoOrigins | q ≠ problem1LineWithTwoOriginsUpperOrigin} ≃ₜ
      (Set.univ : Set ℝ)) := by
  refine ⟨
    { toFun := fun q => ⟨problem1LineWithTwoOriginsXCoord q.1, by simp⟩
      invFun := fun x =>
        ⟨problem1LineWithTwoOriginsLowerBranch x.1,
          problem1LineWithTwoOrigins_lower_branch_ne_upper_origin x.1⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }⟩
  · intro q
    -- Every class in the lower chart is recovered by following its `x`-coordinate back down
    -- the lower branch.
    apply Subtype.ext
    exact problem1LineWithTwoOrigins_lower_branch_xCoord q.2
  · intro x
    -- On the lower branch the quotient coordinate is the original parameter.
    apply Subtype.ext
    rfl
  · -- Continuity of the chart map is continuity of `xCoord`, with a trivial subtype target.
    exact
      (problem1LineWithTwoOrigins_continuous_xCoord.comp continuous_subtype_val).subtype_mk
        fun _ => by simp
  · -- Continuity of the inverse is continuity of the lower branch.
    exact
      (problem1LineWithTwoOrigins_continuous_lower_branch.comp continuous_subtype_val).subtype_mk
        fun x => problem1LineWithTwoOrigins_lower_branch_ne_upper_origin x.1

/-- Problem 1-1 (1): every point of the line with two origins has an open neighborhood
homeomorphic to an open subset of `ℝ`, so the quotient is locally Euclidean of dimension `1`. -/
-- Proof sketch: away from the two origins, the quotient map is locally a homeomorphism onto an
-- open interval in one of the two copies of `ℝ`. At either origin, take a small interval around
-- `0` in the chosen branch; its image in the quotient is still homeomorphic to an open interval.
theorem problem1LineWithTwoOrigins_exists_open_homeomorph (x : problem1LineWithTwoOrigins) :
    ∃ (U : Set problem1LineWithTwoOrigins) (hU : IsOpen U) (hx : x ∈ U) (V : Set ℝ)
      (hV : IsOpen V), Nonempty (U ≃ₜ V) := by
  by_cases hx : x = problem1LineWithTwoOriginsLowerOrigin
  · -- At the lower origin, use the lower chart.
    refine ⟨{q : problem1LineWithTwoOrigins | q ≠ problem1LineWithTwoOriginsUpperOrigin},
      problem1LineWithTwoOrigins_lower_chart_domain_isOpen, ?_,
      Set.univ, isOpen_univ, problem1LineWithTwoOrigins_lower_chart_homeomorph⟩
    simpa [hx] using problem1LineWithTwoOriginsUpperOrigin_ne_lowerOrigin.symm
  · -- Every other point lies in the upper chart.
    refine ⟨{q : problem1LineWithTwoOrigins | q ≠ problem1LineWithTwoOriginsLowerOrigin},
      problem1LineWithTwoOrigins_upper_chart_domain_isOpen, hx,
      Set.univ, isOpen_univ, problem1LineWithTwoOrigins_upper_chart_homeomorph⟩

/-- Problem 1-1 (2): the line with two origins is second-countable. -/
-- Proof sketch: the prequotient `X` is a subspace of `ℝ²`, hence second-countable. Show that the
-- quotient map `X → M` is an open quotient map, then transfer second countability to the
-- quotient.
theorem problem1LineWithTwoOrigins_secondCountableTopology :
    SecondCountableTopology problem1LineWithTwoOrigins := by
  -- The quotient is covered by the two open global charts, each homeomorphic to `ℝ`.
  let U : Bool → Set problem1LineWithTwoOrigins := fun b =>
    cond b
      {q : problem1LineWithTwoOrigins | q ≠ problem1LineWithTwoOriginsUpperOrigin}
      {q : problem1LineWithTwoOrigins | q ≠ problem1LineWithTwoOriginsLowerOrigin}
  have hU_sc : ∀ b, SecondCountableTopology (U b) := by
    intro b
    cases b
    · rcases problem1LineWithTwoOrigins_upper_chart_homeomorph with ⟨e⟩
      simpa [U] using e.secondCountableTopology
    · rcases problem1LineWithTwoOrigins_lower_chart_homeomorph with ⟨e⟩
      simpa [U] using e.secondCountableTopology
  letI : ∀ b, SecondCountableTopology (U b) := hU_sc
  have hU_open : ∀ b, IsOpen (U b) := by
    intro b
    cases b
    · simpa [U] using problem1LineWithTwoOrigins_upper_chart_domain_isOpen
    · simpa [U] using problem1LineWithTwoOrigins_lower_chart_domain_isOpen
  have hcover : ⋃ b, U b = Set.univ := by
    ext q
    constructor
    · intro _
      simp
    · intro _
      by_cases hq : q = problem1LineWithTwoOriginsLowerOrigin
      · refine Set.mem_iUnion.2 ?_
        refine ⟨true, ?_⟩
        simpa [U, hq] using problem1LineWithTwoOriginsUpperOrigin_ne_lowerOrigin.symm
      · refine Set.mem_iUnion.2 ?_
        exact ⟨false, hq⟩
  exact TopologicalSpace.secondCountableTopology_of_countable_cover hU_open hcover

/-- Helper for Problem 1-1: any open neighborhoods of the two origins contain a common nonzero
branch parameter, so they meet in the quotient. -/
lemma problem1LineWithTwoOrigins_origins_nhds_inter
    (U V : Set problem1LineWithTwoOrigins) (hU : IsOpen U) (hV : IsOpen V)
    (hUpper : problem1LineWithTwoOriginsUpperOrigin ∈ U)
    (hLower : problem1LineWithTwoOriginsLowerOrigin ∈ V) :
    (U ∩ V).Nonempty := by
  let U' : Set ℝ := problem1LineWithTwoOriginsUpperBranch ⁻¹' U
  let V' : Set ℝ := problem1LineWithTwoOriginsLowerBranch ⁻¹' V
  have hU' : IsOpen U' := by
    simpa [U'] using hU.preimage problem1LineWithTwoOrigins_continuous_upper_branch
  have hV' : IsOpen V' := by
    simpa [V'] using hV.preimage problem1LineWithTwoOrigins_continuous_lower_branch
  have h0U : (0 : ℝ) ∈ U' := by
    simpa [U', problem1LineWithTwoOriginsUpperBranch, problem1LineWithTwoOriginsUpperOrigin]
      using hUpper
  have h0V : (0 : ℝ) ∈ V' := by
    simpa [V', problem1LineWithTwoOriginsLowerBranch, problem1LineWithTwoOriginsLowerOrigin]
      using hLower
  -- Open neighborhoods of `0` contain metric balls around `0`.
  obtain ⟨εU, hεU_pos, hεU⟩ := Metric.mem_nhds_iff.1 (hU'.mem_nhds h0U)
  obtain ⟨εV, hεV_pos, hεV⟩ := Metric.mem_nhds_iff.1 (hV'.mem_nhds h0V)
  let t : ℝ := min εU εV / 2
  have ht_pos : 0 < t := by
    dsimp [t]
    have hmin_pos : 0 < min εU εV := lt_min hεU_pos hεV_pos
    linarith
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  have htU : t ∈ U' := by
    apply hεU
    dsimp [t]
    have hnonneg : 0 ≤ min εU εV / 2 := by
      have hmin_nonneg : 0 ≤ min εU εV := le_of_lt (lt_min hεU_pos hεV_pos)
      nlinarith
    have hlt : min εU εV / 2 < εU := by
      have hmin_le : min εU εV ≤ εU := min_le_left _ _
      nlinarith [hεU_pos]
    simpa [Metric.ball, Real.dist_eq, abs_of_nonneg hnonneg] using hlt
  have htV : t ∈ V' := by
    apply hεV
    dsimp [t]
    have hnonneg : 0 ≤ min εU εV / 2 := by
      have hmin_nonneg : 0 ≤ min εU εV := le_of_lt (lt_min hεU_pos hεV_pos)
      nlinarith
    have hlt : min εU εV / 2 < εV := by
      have hmin_le : min εU εV ≤ εV := min_le_right _ _
      nlinarith [hεV_pos]
    simpa [Metric.ball, Real.dist_eq, abs_of_nonneg hnonneg] using hlt
  -- The same nonzero parameter gives the same quotient point on the two branches.
  refine ⟨problem1LineWithTwoOriginsUpperBranch t, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [U'] using htU
  · have hLowerMem : problem1LineWithTwoOriginsLowerBranch t ∈ V := by
      simpa [V'] using htV
    exact problem1LineWithTwoOrigins_upper_eq_lower_branch ht_ne ▸ hLowerMem

/-- Problem 1-1 (3): the line with two origins is not Hausdorff. -/
-- Proof sketch: the upper and lower origins are distinct quotient classes, but every open
-- neighborhood of one meets every open neighborhood of the other because both contain the image of
-- some punctured interval around `0`, whose nonzero points have been identified in the quotient.
theorem problem1LineWithTwoOrigins_not_t2Space :
    ¬ T2Space problem1LineWithTwoOrigins := by
  intro hT2
  letI : T2Space problem1LineWithTwoOrigins := hT2
  -- In a Hausdorff space, distinct points admit disjoint open neighborhoods.
  rcases t2_separation problem1LineWithTwoOriginsUpperOrigin_ne_lowerOrigin with
    ⟨U, V, hU, hV, hUpper, hLower, hDisj⟩
  rcases
      problem1LineWithTwoOrigins_origins_nhds_inter U V hU hV hUpper hLower with
    ⟨x, hxU, hxV⟩
  exact Set.disjoint_left.1 hDisj hxU hxV
