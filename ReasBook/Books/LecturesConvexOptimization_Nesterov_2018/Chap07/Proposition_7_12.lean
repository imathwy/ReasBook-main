import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap02.Lemma_2_18
import LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_9
import LecturesConvexOptimization_Nesterov_2018.Chap07.Definition_7_29

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped EllipsoidNotation PositiveDefMatrixNorm SupportFunction

universe u v

section Family

variable {ι : Type u}

/- Proposition 7.12 lies in the chapter's symmetric-hull / support-function / finite
max-absolute-linear domain.

Sampled owner-style declarations:
- mathlib `absConvexHull` and `convexHull_union_neg_eq_absConvexHull`;
- `maxTypeObjective` and `maxTypeObjective_apply` in `Chap02/Lemma_2_18`;
- `ξ[Q]` and `supportFunction_convexHull_eq` in `Chap03/Definition_3_9`.

Best owner abstraction:
- source-facing: the symmetric hull `conv {±aᵢ}` and the finite objective `x ↦ maxᵢ |⟪aᵢ, x⟫|`;
- core/canonical: `absConvexHull ℝ (Set.range a)`, `maxTypeObjective`, and the Chapter 3 support
  function `ξ[Q]`;
- bridge/view: the theorem identifying `conv {±aᵢ}` with `absConvexHull ℝ (Set.range a)` and the
  support-function identity relating the finite max to that canonical hull.

Primitive data:
- a family `a : ι → E`;
- a finite nonempty index type `[Fintype ι] [Nonempty ι]` for the finite max owner.

Derived API:
- the source-facing specialization of mathlib's canonical symmetric-hull bridge
  `convexHull ℝ (Set.range a ∪ Set.range (fun i ↦ -a i)) = absConvexHull ℝ (Set.range a)`;
- the canonical owner evaluation theorem `maxTypeObjective_apply`, specialized to
  `fun i x ↦ |⟪aᵢ, x⟫|`;
- the support-function bridge below.
-/

section Hull

variable {E : Type v} [AddCommGroup E] [Module ℝ E]

/-- The textbook symmetric hull `conv {±aᵢ}` of a family `a` is exactly the canonical absolutely
convex hull of its range. This is the `Set.range` specialization of mathlib's owner theorem
`convexHull_union_neg_eq_absConvexHull`. -/
theorem convexHull_range_union_neg_eq_absConvexHull_range (a : ι → E) :
    convexHull ℝ (Set.range a ∪ Set.range (fun i ↦ -a i)) =
      absConvexHull ℝ (Set.range a) := by
  simpa [Set.neg_range] using
    (convexHull_union_neg_eq_absConvexHull :
      convexHull ℝ (Set.range a ∪ -Set.range a) = absConvexHull ℝ (Set.range a))

end Hull

section Support

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section FiniteFamily

variable [Fintype ι] [Nonempty ι]

/-- Companion bridge: the Chapter 3 support function of the canonical absolutely convex hull
`absConvexHull ℝ (Set.range a)` is exactly the finite max of the absolute pairings. -/
theorem supportFunction_absConvexHull_range_toReal_eq_maxTypeObjective_absInner
    (a : ι → E) (x : E) :
    (ξ[absConvexHull ℝ (Set.range a)] x).toReal =
      maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x := sorry

/-- Proposition 7.12 (2): the support function of the symmetric hull `conv {±aᵢ}` is exactly the
finite maximum of the absolute pairings `maxᵢ |⟪aᵢ, x⟫|`. -/
theorem supportFunction_convexHull_range_union_neg_toReal_eq_maxTypeObjective_absInner
    (a : ι → E) (x : E) :
    (ξ[convexHull ℝ (Set.range a ∪ Set.range fun i : ι ↦ -a i)] x).toReal =
      maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x := by
  simpa [convexHull_range_union_neg_eq_absConvexHull_range] using
    supportFunction_absConvexHull_range_toReal_eq_maxTypeObjective_absInner a x

end FiniteFamily

end Support

end Family

section Ellipsoid

variable {m : ℕ+} {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

-- Proof sketch: Proposition 7.12 is the support-function sandwich induced by the centered
-- ellipsoidal-rounding owner, then rewritten through the symmetric-hull bridge
-- `convexHull_range_union_neg_eq_absConvexHull_range`.
/-- Companion bridge: the lower ellipsoidal bound written for the canonical absolutely convex hull
`absConvexHull ℝ (Set.range a)`. -/
theorem ellipsoidalNorm_le_maxTypeObjective_absInner_of_ellipsoidal_rounding_absConvexHull
    (a : Fin (m : ℕ) → E) {G : Mat} {γ : ℝ} (x : E)
    (hrounding : IsEllipsoidalRounding (absConvexHull ℝ (Set.range a)) γ G) :
    ‖x‖[⟨G, hrounding.posDef⟩] ≤ maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x := by
  sorry

/-- Proposition 7.12 (1): if the symmetric hull `conv {±aᵢ}` admits a `γ √n`-ellipsoidal
rounding with shape matrix `G`, then `maxᵢ |⟪aᵢ, x⟫|` bounds the `G`-norm of `x` from below. -/
theorem ellipsoidalNorm_le_maxTypeObjective_absInner_of_ellipsoidal_rounding
    (a : Fin (m : ℕ) → E) {G : Mat} {γ : ℝ} (x : E)
    (hrounding :
      IsEllipsoidalRounding
        (convexHull ℝ (Set.range a ∪ Set.range fun i : Fin (m : ℕ) ↦ -a i)) γ G) :
    ‖x‖[⟨G, hrounding.posDef⟩] ≤ maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x := by
  have hrounding' : IsEllipsoidalRounding (absConvexHull ℝ (Set.range a)) γ G := by
    simpa [convexHull_range_union_neg_eq_absConvexHull_range] using hrounding
  simpa using
    ellipsoidalNorm_le_maxTypeObjective_absInner_of_ellipsoidal_rounding_absConvexHull a x
      hrounding'

/- Proposition 7.12 (2) is exactly
`supportFunction_convexHull_range_union_neg_toReal_eq_maxTypeObjective_absInner`. -/

-- Proof sketch: combine the support-function identity
-- `supportFunction_absConvexHull_range_toReal_eq_maxTypeObjective_absInner` with the outer
-- inclusion from `hrounding`, then evaluate the support function of the centered ellipsoid
-- `W[(γ * √n)](G)` via the dual norm `‖·‖[⟨G, hrounding.posDef⟩]`.
/-- Companion bridge: the upper ellipsoidal bound written for the canonical absolutely convex hull
`absConvexHull ℝ (Set.range a)`. -/
theorem maxTypeObjective_absInner_le_of_ellipsoidal_rounding_absConvexHull
    (a : Fin (m : ℕ) → E) {G : Mat} {γ : ℝ} (x : E)
    (hrounding : IsEllipsoidalRounding (absConvexHull ℝ (Set.range a)) γ G) :
    maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x ≤
      γ * Real.sqrt (n : ℝ) * ‖x‖[⟨G, hrounding.posDef⟩] := by
  sorry

/-- Proposition 7.12 (3): if the symmetric hull `conv {±aᵢ}` admits a `γ √n`-ellipsoidal
rounding with shape matrix `G`, then `maxᵢ |⟪aᵢ, x⟫|` is bounded above by `γ √n ‖x‖_G`. -/
theorem maxTypeObjective_absInner_le_of_ellipsoidal_rounding
    (a : Fin (m : ℕ) → E) {G : Mat} {γ : ℝ} (x : E)
    (hrounding :
      IsEllipsoidalRounding
        (convexHull ℝ (Set.range a ∪ Set.range fun i : Fin (m : ℕ) ↦ -a i)) γ G) :
    maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x ≤
      γ * Real.sqrt (n : ℝ) * ‖x‖[⟨G, hrounding.posDef⟩] := by
  have hrounding' : IsEllipsoidalRounding (absConvexHull ℝ (Set.range a)) γ G := by
    simpa [convexHull_range_union_neg_eq_absConvexHull_range] using hrounding
  simpa using
    maxTypeObjective_absInner_le_of_ellipsoidal_rounding_absConvexHull a x hrounding'

/-- Companion bridge: the support function of `absConvexHull ℝ (Set.range a)` satisfies the same
upper bound because it is exactly the finite max of the absolute pairings in real form. -/
theorem supportFunction_absConvexHull_range_le_of_ellipsoidal_rounding
    (a : Fin (m : ℕ) → E) {G : Mat} {γ : ℝ} (x : E)
    (hrounding : IsEllipsoidalRounding (absConvexHull ℝ (Set.range a)) γ G) :
    (ξ[absConvexHull ℝ (Set.range a)] x).toReal ≤
      γ * Real.sqrt (n : ℝ) * ‖x‖[⟨G, hrounding.posDef⟩] := by
  rw [supportFunction_absConvexHull_range_toReal_eq_maxTypeObjective_absInner]
  exact maxTypeObjective_absInner_le_of_ellipsoidal_rounding_absConvexHull a x hrounding

-- Proof sketch: each generator `a_i` belongs to the symmetric hull `conv {±aᵢ}`, so the outer
-- inclusion from `hrounding` places `a_i` inside `W[(γ * √n)](G)`. Rewriting membership in this
-- centered ellipsoid by `mem_centeredMatrixEllipsoid_iff_dualNorm_le` gives the claimed
-- dual-norm bound.
/-- Each generator `a_i` lies in the outer centered ellipsoid coming from the rounding
hypothesis. Equivalently, its `G`-dual norm is at most `γ √n`. -/
theorem generator_ellipsoidalDualNorm_le_of_ellipsoidal_rounding
    (a : Fin (m : ℕ) → E) {G : Mat} {γ : ℝ} (i : Fin (m : ℕ))
    (hrounding :
      IsEllipsoidalRounding
        (convexHull ℝ (Set.range a ∪ Set.range fun j : Fin (m : ℕ) ↦ -a j)) γ G) :
    ‖a i‖[⟨G, hrounding.posDef⟩,*] ≤ γ * Real.sqrt (n : ℝ) := by
  sorry

end Ellipsoid

end
