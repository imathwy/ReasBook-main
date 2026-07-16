import Mathlib.Data.EReal.Inv
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Definition 4.4.6 fixes arithmetic conventions on the extended line `[-∞, ∞]`,
  including empty `sInf`/`sSup` and admissible-domain rules around mixed infinities.
- `core/canonical`: mathlib's owner for the extended real line is `EReal`.
- `bridge/view`: Rockafellar's "forbidden" mixed-infinite formulas are represented by admissibility
  side conditions (`x ≠ ⊥`, `x ≠ ⊤`, sign hypotheses), while arithmetic remains total on `EReal`.
- Layer target: keep the textbook arithmetic source-facing by recalling the canonical `EReal`
  lemmas directly, without routing through the chapter's deprecated wrapper modules.
- Domain-style sampling used here:
  `EReal.top_add_of_ne_bot`, `EReal.top_add_iff_ne_bot`, `EReal.top_sub`,
  `EReal.add_eq_bot_iff`, `EReal.mul_top_of_pos`, `EReal.top_mul_of_pos`,
  `EReal.left_distrib_of_nonneg_of_ne_top`, and `EReal.right_distrib_of_nonneg`.
  The empty `sInf`/`sSup` conventions and admissibility side conditions are derived API.
-/

/-!  The chapter's extended-real arithmetic owner is the canonical mathlib type `EReal`. -/
/-- Defintion 4.4.6: Rockafellar's extended real line with the stated arithmetic conventions is
the canonical mathlib type `EReal`. -/
abbrev extendedRealLine := EReal

/- Definition 4.4.6 codomain owner name: `EReal`. -/
recall EReal

/- For any extended real number different from `⊥`, adding `⊤` yields `⊤`, matching the textbook
rule `α + ∞ = ∞ + α = ∞` on its stated domain. -/
section AdditiveBoundary

recall EReal.top_add_of_ne_bot

/- The domain condition for the previous rule is exactly that the other summand is not `⊥`. -/
recall EReal.top_add_iff_ne_bot

/- The symmetric form of the previous rule is `EReal.add_top_of_ne_bot`. -/
recall EReal.add_top_of_ne_bot

/- The symmetric domain condition is `WithTopBot.add_top_iff_ne_bot`. -/
recall EReal.add_top_iff_ne_bot

/- The totalized `⊥`-valued failure mode for sums is canonically identified by
`EReal.add_eq_bot_iff`; in particular, the forbidden mixed sums land at `⊥` in the owner
totalization. -/
recall EReal.add_eq_bot_iff

/- Rockafellar's rule `x + (-∞) = -∞` is recalled through `EReal.add_bot`. -/
recall EReal.add_bot

/- Rockafellar's symmetric rule `(-∞) + x = -∞` is recalled through `EReal.bot_add`. -/
recall EReal.bot_add

end AdditiveBoundary

section AdditiveAdmissibility

/-- Helper for Defintion 4.4.6: Rockafellar's order-style admissibility conditions are exactly the
canonical `EReal` exclusions of `⊥` and `⊤`. -/
theorem admissible_addition_side_conditions :
    ∀ x : EReal, (⊥ < x ↔ x ≠ (⊥ : EReal)) ∧ (x < ⊤ ↔ x ≠ (⊤ : EReal)) := by
  intro x
  constructor
  · -- The lower boundary is admissible precisely when the summand is not `⊥`.
    constructor
    · -- Any element strictly above `⊥` is automatically different from `⊥`.
      intro hx
      exact ne_of_gt hx
    · -- Every owner value other than `⊥` lies strictly above the lower boundary.
      intro hx
      exact bot_lt_iff_ne_bot.mpr hx
  · -- The upper boundary is admissible precisely when the summand is not `⊤`.
    constructor
    · -- Strictly lying below `⊤` rules out equality with `⊤`.
      intro hx
      exact ne_of_lt hx
    · -- Every owner value other than `⊤` lies strictly below the upper boundary.
      intro hx
      exact lt_top_iff_ne_top.mpr hx

end AdditiveAdmissibility

/- The symmetric admissible subtraction rule `∞ - α = ∞` for `α ≠ ∞` is recalled through
`EReal.top_sub`. -/
section SubtractionBoundary

recall EReal.top_sub

/- Rockafellar's rule `x - ∞ = -∞` is recalled through `EReal.sub_top`. -/
recall EReal.sub_top

end SubtractionBoundary

section NegationBoundary

/- Negating `⊥` gives `⊤`, i.e. `-(-∞) = ∞`. -/
recall EReal.neg_bot

/- Negating `⊤` gives `⊥`. -/
recall EReal.neg_top

end NegationBoundary

/- Addition on the owner is associative. -/
section AdditiveAssociativity

variable {α : Type*} [AddSemigroup α]

recall add_assoc

end AdditiveAssociativity

/- Addition on the owner is commutative (when the base addition is commutative). -/
section AdditiveCommutativity

variable {α : Type*} [AddCommMagma α]

recall add_comm

end AdditiveCommutativity

/- Right multiplication by `⊤` with a positive factor yields `⊤`. -/
section MultiplicativeBoundary

recall EReal.mul_top_of_pos

/- Left multiplication by `⊤` with a positive factor yields `⊤`. -/
recall EReal.top_mul_of_pos

/- Right multiplication by `⊥` with a positive factor yields `⊥`. -/
recall EReal.mul_bot_of_pos

/- Left multiplication by `⊥` with a positive factor yields `⊥`. -/
recall EReal.bot_mul_of_pos

/- Right multiplication by `⊤` with a negative factor yields `⊥`. -/
recall EReal.mul_top_of_neg

/- Left multiplication by `⊤` with a negative factor yields `⊥`. -/
recall EReal.top_mul_of_neg

/- Right multiplication by `⊥` with a negative factor yields `⊤`. -/
recall EReal.mul_bot_of_neg

/- Left multiplication by `⊥` with a negative factor yields `⊤`. -/
recall EReal.bot_mul_of_neg

end MultiplicativeBoundary

section ZeroMultiplication

variable {β : Type*} [MulZeroClass β]

/- Zero annihilates multiplication on the left in any `MulZeroClass`; for the chapter's extended
codomain owner naming this specializes to `β = WithTopBot α` (implemented by the bridge API). -/
recall zero_mul

/- Right multiplication by zero in the owner yields zero. -/
recall mul_zero

/-- Helper for Defintion 4.4.6: zero is a two-sided annihilator in any `MulZeroClass`, so the
textbook boundary values follow by specializing to `⊤` and `⊥` in the owner codomain. -/
theorem zero_mul_two_sided (x : β) : (0 : β) * x = 0 ∧ x * (0 : β) = 0 := by
  constructor
  · -- The left annihilation law is one of the primitive `MulZeroClass` axioms.
    exact zero_mul x
  · -- The right annihilation law is the symmetric primitive axiom.
    exact mul_zero x

end ZeroMultiplication

section EmptySupInf

variable {β : Type*} [CompleteLattice β]

/- In any complete lattice, the infimum of the empty set is `⊤`; for `WithTopBot α` this is the
textbook `+∞` convention. -/
recall sInf_empty

/- In any complete lattice, the supremum of the empty set is `⊥`; for `WithTopBot α` this is the
textbook `-∞` convention. -/
recall sSup_empty

/-- Helper for Defintion 4.4.6: the empty infimum and supremum boundary conventions are the
canonical complete-lattice ones. -/
theorem empty_bounds_in_complete_lattice :
    sInf (∅ : Set β) = ⊤ ∧ sSup (∅ : Set β) = ⊥ := by
  constructor
  · -- The empty infimum is the top element in every complete lattice.
    exact (sInf_empty : sInf (∅ : Set β) = (⊤ : β))
  · -- The empty supremum is the bottom element in every complete lattice.
    exact (sSup_empty : sSup (∅ : Set β) = (⊥ : β))

end EmptySupInf

section MultiplicativeCommutativity

/- Multiplication on `EReal` is commutative. -/
recall EReal.mul_comm

end MultiplicativeCommutativity

/- A canonical safe left-distributivity law on the chapter arithmetic owner holds when the
coefficient is nonnegative and finite. -/
section OrderedDistributivity

recall EReal.left_distrib_of_nonneg_of_ne_top

/- A canonical safe right-distributivity law on the chapter arithmetic owner holds when the
coefficient is nonnegative and finite. -/
recall EReal.right_distrib_of_nonneg_of_ne_top

/- A canonical safe left-distributivity law on the chapter arithmetic owner also holds when the
addends are nonnegative. -/
recall EReal.left_distrib_of_nonneg

/- A canonical safe right-distributivity law on the chapter arithmetic owner holds when the
addends are nonnegative. -/
recall EReal.right_distrib_of_nonneg

/-- Helper for Defintion 4.4.6: safe distributivity on `EReal` holds in both left and right forms
whenever the scalar is nonnegative and finite, matching the textbook admissibility clause. -/
theorem safe_ereal_distrib {x y z : EReal} (hx_nonneg : 0 ≤ x) (hx_ne_top : x ≠ ⊤) :
    x * (y + z) = x * y + x * z ∧ (y + z) * x = y * x + z * x := by
  constructor
  · -- The left-distributive safe case is exactly the recalled `EReal` lemma.
    exact EReal.left_distrib_of_nonneg_of_ne_top hx_nonneg hx_ne_top y z
  · -- The right-distributive safe case is the symmetric recalled lemma.
    exact EReal.right_distrib_of_nonneg_of_ne_top hx_nonneg hx_ne_top y z

end OrderedDistributivity
