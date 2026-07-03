import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_1 (from Chap10) -/
universe u

/- Definition 10.1: positive homogeneity is the canonical owner `PositivelyHomogeneous`; for
`EReal`-valued functions, the codomain scalar action is the real multiplication action on
`EReal` recalled in Chapter 1. -/
recall PositivelyHomogeneous

namespace ERealFunction

section Additive

variable {H : Type u} [Add H]

/-- Definition 10.1 (1): an extended-real-valued function is subadditive when the value at a sum
is bounded above by the sum of the values for all pairs of points in the effective domain. -/
def Subadditive (f : H → EReal) : Prop :=
  ∀ ⦃x y : H⦄, x ∈ dom f → y ∈ dom f → f (x + y) ≤ f x + f y

-- Proof sketch: unfold `Subadditive` and apply the defining inequality to the chosen domain
-- points `x` and `y`.
/-- A subadditive function satisfies the textbook inequality at every two points of its domain. -/
theorem Subadditive.map_add_le {f : H → EReal} (hf : Subadditive f) {x y : H}
    (hx : x ∈ dom f) (hy : y ∈ dom f) :
    f (x + y) ≤ f x + f y :=
  hf hx hy

end Additive

section RealScalarAction

variable {H : Type u} [Add H] [SMul ℝ H]

/-- Definition 10.1 (2): an extended-real-valued function is sublinear when it is positively
homogeneous and subadditive. -/
def Sublinear (f : H → EReal) : Prop :=
  PositivelyHomogeneous f ∧ Subadditive f

-- Proof sketch: unfold `Sublinear` and extract the positive-homogeneity conjunct.
/-- A sublinear function is positively homogeneous. -/
theorem Sublinear.positivelyHomogeneous {f : H → EReal} (hf : Sublinear f) :
    PositivelyHomogeneous f :=
  hf.1

-- Proof sketch: unfold `Sublinear` and extract the subadditivity conjunct.
/-- A sublinear function is subadditive. -/
theorem Sublinear.subadditive {f : H → EReal} (hf : Sublinear f) :
    Subadditive f :=
  hf.2

end RealScalarAction

end ERealFunction
