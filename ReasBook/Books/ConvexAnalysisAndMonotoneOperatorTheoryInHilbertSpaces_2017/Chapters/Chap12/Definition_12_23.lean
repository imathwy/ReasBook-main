import Mathlib
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.Definition_12_20

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H]

/-- The unit proximal objective at `x`, whose minimizers are the proximal points of `f` at `x`. -/
noncomputable def proximalObjective (f : H → Set.Ioi (⊥ : EReal)) (x : H) : H → EReal :=
  fun y ↦ (f y : EReal) + ((((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal))

/-- Definition 12 23: the proximal points of `f` at `x` are the minimizers of the regularized
objective `y ↦ f y + (1 / 2) ‖x - y‖^2`. -/
def proximalPoints (f : H → Set.Ioi (⊥ : EReal)) (x : H) : Set H :=
  Argmin (proximalObjective f x)

/-- Predicate form of Definition 12 23: `p` is a proximal point of `f` at `x` when it belongs to
the argmin set of the regularized objective at `x`. -/
abbrev IsProxPoint (f : H → Set.Ioi (⊥ : EReal)) (x p : H) : Prop :=
  p ∈ proximalPoints f x

-- Proof sketch: unfold `IsProxPoint`, then rewrite the unit Moreau envelope with
-- `moreauEnvelope_apply` at the parameter `γ = 1`.
/-- A point is proximal exactly when it realizes the value of the unit Moreau envelope. -/
theorem isProxPoint_iff_moreauEnvelope_eq (f : H → Set.Ioi (⊥ : EReal)) (x p : H) :
    IsProxPoint f x p ↔
      ({}^[⟨(1 : ℝ), by simp [Set.mem_Ioi]⟩] f) x =
        (f p : EReal) + ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal)) := by
  have hunit : (0 : ℝ) < 1 := by
    norm_num
  let γ : Set.Ioi (0 : ℝ) := ⟨(1 : ℝ), hunit⟩
  have hmoreau :
      ({}^[γ] f) x =
        ⨅ y : H, (f y : EReal) + ((((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal)) := by
    -- Rewrite the unit Moreau envelope as the infimum of the proximal objective.
    simpa [γ] using
      (moreauEnvelope_apply (f := f) (γ := γ) (x := x))
  have hobjective_iInf :
      iInf (proximalObjective f x) =
        ⨅ y : H, (f y : EReal) + ((((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal)) := by
    rfl
  have hiff :
      IsProxPoint f x p ↔
        ({}^[γ] f) x =
          (f p : EReal) + ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal)) := by
    -- Both sides now identify the proximal objective value at `p` with the same infimum.
    rw [IsProxPoint, proximalPoints, mem_argmin_iff_eq_sInf, sInf_range]
    constructor
    · intro hp
      rw [hmoreau, ← hobjective_iInf]
      simpa [proximalObjective] using hp.symm
    · intro hp
      rw [hmoreau, ← hobjective_iInf] at hp
      simpa [proximalObjective] using hp.symm
  simpa [γ] using hiff

/-- A function has a unique proximal point at every base point when the regularized objective
`y ↦ f y + (1 / 2) ‖x - y‖^2` admits a unique minimizer for every `x`. -/
def HasUniqueProxPoint (f : H → Set.Ioi (⊥ : EReal)) : Prop :=
  ∀ x : H, ∃! p : H, p ∈ proximalPoints f x

/-- The proximity operator attached to a function with unique proximal points sends `x` to its
unique proximal point. -/
noncomputable def proximityOperator (f : H → Set.Ioi (⊥ : EReal)) (hf : HasUniqueProxPoint f) :
    H → H :=
  fun x ↦ (hf x).choose

-- Proof sketch: unfold `proximityOperator` and use the defining `ExistsUnique` witness from
-- `HasUniqueProxPoint`.
/-- The value of the proximity operator is a proximal point. -/
theorem proximityOperator_isProxPoint (f : H → Set.Ioi (⊥ : EReal))
    (hf : HasUniqueProxPoint f) (x : H) :
    IsProxPoint f x (proximityOperator f hf x) := by
  -- The chosen point is exactly the witness supplied by the unique-existence hypothesis.
  exact (hf x).choose_spec.1

-- Proof sketch: apply the uniqueness clause in `hf x` to the given proximal point and to
-- `proximityOperator f hf x`.
/-- Any proximal point at `x` coincides with the value of the proximity operator at `x`. -/
theorem eq_proximityOperator_of_isProxPoint (f : H → Set.Ioi (⊥ : EReal))
    (hf : HasUniqueProxPoint f) {x p : H} (hp : IsProxPoint f x p) :
    p = proximityOperator f hf x := by
  -- Uniqueness identifies any proximal point with the chosen witness.
  exact ExistsUnique.unique (hf x) hp (proximityOperator_isProxPoint f hf x)

end ERealFunction
