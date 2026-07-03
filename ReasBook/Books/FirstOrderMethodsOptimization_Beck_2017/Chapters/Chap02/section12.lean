import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_12 (from Chap02) -/
universe u

open Pointwise

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- Definition 2.12: the polar cone of a set `K ⊆ E` is the set of dual vectors `y` whose
pairing with every `x ∈ K` is nonpositive. -/
def polar_cone (K : Set E) : Set (Module.Dual ℝ E) :=
  (-PointedCone.dual (Module.Dual.eval ℝ E) K : Set (Module.Dual ℝ E))

-- Proof sketch: rewrite membership in the negative of the dual cone as membership of `-y` in the
-- dual cone, unfold `PointedCone.mem_dual` for the evaluation pairing, and simplify.
/-- Membership in the polar cone means being nonpositive on every point of `K`. -/
lemma mem_polar_cone (K : Set E) (y : Module.Dual ℝ E) :
    y ∈ polar_cone K ↔ ∀ x ∈ K, y x ≤ 0 := sorry

/-- The polar cone is the negative of the dual cone for the evaluation pairing. -/
lemma polar_cone_eq_neg_dual (K : Set E) :
    polar_cone K = (-PointedCone.dual (Module.Dual.eval ℝ E) K : Set (Module.Dual ℝ E)) := rfl

end
