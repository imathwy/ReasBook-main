import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Definition_3_1_1_2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Definition_3_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped ConvexAnalysis WithTopConvexAnalysis

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 5.0.27 lies in the chapter's Fenchel-conjugacy domain.

Sampled owner-style declarations:
- `extendedRealEffectiveDomain` / `dom` in `Chap03/Definition_3_1_1_2`, the chapter owner for the
  effective domain of an `EReal`-valued function;
- `fenchelDual` in `Chap03/Definition_3_1_2_1`, the source-facing owner for the Fenchel conjugate
  of a `WithTop ℝ`-valued function on a real inner-product space;
- `fenchelDual_apply_eq_sSup_image_dom` in `Chap03/Definition_3_8`, the canonical bridge that
  restricts the defining supremum to `dom f`;
- `fenchelConjugate` in `Chap06/Definition_6_1`, the core dual-space owner underlying
  `fenchelDual`.

Best owner abstraction:
- source-facing: `fenchelDual`, written on the theorem surface as `f⋆`;
- core/canonical: `fenchelConjugate`;
- bridge/view: the `dom`-restricted supremum formula and the finite real part `withTopRealPart`.

Primitive data:
- `f : E → WithTop ℝ`.

Derived API:
- the recalled owner `f⋆`;
- the recalled dual effective domain `dom (f⋆)`;
- the recalled `dom`-restricted supremum formula `fenchelDual_apply_eq_sSup_image_dom`;
- the textbook bounded-below characterization of `dom (f⋆)` under `dom f` nonempty.

Source/core/bridge triage:
- source-facing: Definition 5.0.27, the Fenchel conjugate and its textbook dual domain on `ℝⁿ`;
- core/canonical: `fenchelConjugate`;
- bridge/view: the Euclidean specialization via `innerₗ E`.

This file is recall-first for the conjugate itself: the Chapter 3 owner already supplies the exact
source-facing Fenchel-dual construction and the canonical `dom`-restricted supremum formula, so
the previous local duplicate definitions are deleted. The dual effective domain is likewise
recalled directly as `dom (f⋆)`; only the textbook bounded-below condition remains as a companion
bridge theorem, because it is not the owner and it needs a nonempty-domain hypothesis to match the
canonical effective domain.
-/

/- Definition 5.0.27 recalls the source-facing Fenchel-dual owner on `ℝⁿ`. -/
recall fenchelDual

section

variable (f : E → WithTop ℝ)

/- Definition 5.0.27 also recalls the canonical dual effective domain surface `dom (f⋆)`. -/
#check dom (f⋆)

end

section

variable (f : E → WithTop ℝ) (s : E)

/- Restricting the recalled Fenchel-dual supremum to `dom f` gives the textbook formula. -/
#check fenchelDual_apply_eq_sSup_image_dom f s

end

section

variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- On a real inner-product space, under the nonempty-domain hypothesis needed to exclude the
empty-image edge case, membership in the canonical dual effective domain `dom (f⋆)` is equivalent
to the textbook condition that `x ↦ f(x) - ⟪s, x⟫` is bounded below on `dom f`. -/
-- Proof sketch: rewrite `(f⋆) s` with `fenchelDual_apply_eq_sSup_image_dom`; under
-- `(dom f).Nonempty`, the displayed image set is nonempty and consists of finite real values, so
-- finiteness of the supremum is equivalent to boundedness above of
-- `x ↦ inner ℝ s x - withTopRealPart f x`, equivalently to boundedness below of
-- `x ↦ withTopRealPart f x - inner ℝ s x`.
theorem mem_dom_fenchelDual_iff {f : F → WithTop ℝ} (hdom : (dom f).Nonempty) {s : F} :
    s ∈ dom (f⋆) ↔
      BddBelow ((fun x : F ↦ withTopRealPart f x - inner ℝ s x) '' dom f) := sorry

end

end
