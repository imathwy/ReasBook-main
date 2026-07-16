import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_17_1
import StacksProject_2024.stacks_project.Chap29.Lemma_29_10_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

noncomputable section

-- Semantic recall / local precedent check:
-- `lean_leansearch` did not surface a scheme-level dimension-formula owner for this statement.
-- The nearby files `29_52_1_1` and `29_52_2_1`, together with the canonical owners
-- `Scheme.functionField`, `IsDominant`, `LocallyOfFiniteType`, `IsLocallyNoetherian`, and
-- `UniversallyCatenary`,
-- determine the source-facing scheme statement used here.

section

variable {X S : Scheme.{u}} (f : X ⟶ S)

local notation "functionFieldTrdeg" =>
  Cardinal.toNat (Algebra.trdeg S.functionField X.functionField)

local notation "residueFieldTrdegAt" =>
  fun x : X ↦
    Cardinal.toNat
      (Algebra.trdeg (S.residueField (f x)) (X.residueField x))

/-- Lemma 29.52.1 (1): let `f : X ⟶ S` be a dominant morphism of integral schemes, with `S`
locally Noetherian and `f` locally of finite type. Then for every `x : X`, writing `s = f x`, the
Krull dimension of `𝒪_{X, x}` is at most the Krull dimension of `𝒪_{S, s}` plus the
transcendence degree of the function-field extension `R(X) / R(S)`, minus the transcendence degree
of the residue-field extension `κ(x) / κ(s)`. -/
@[stacks 02JU]
theorem ringKrullDim_stalk_le_ringKrullDim_stalk_image_add_functionFieldTrdeg_sub_residueFieldTrdeg
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] [IsIntegral X] [IsIntegral S]
    [IsDominant f] [Algebra S.functionField X.functionField] (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤
      ringKrullDim (S.presheaf.stalk (f x)) +
        ((functionFieldTrdeg - residueFieldTrdegAt x) : WithBot ℕ∞) := sorry

/-- Companion additive form of Lemma 29.52.1 (1), aligned with the chapter's local-dimension
arithmetic surfaces. -/
theorem ringKrullDim_stalk_add_residueFieldTrdeg_le_ringKrullDim_stalk_image_add_functionFieldTrdeg
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] [IsIntegral X] [IsIntegral S]
    [IsDominant f] [Algebra S.functionField X.functionField] (x : X) :
    ringKrullDim (X.presheaf.stalk x) + (residueFieldTrdegAt x : WithBot ℕ∞) ≤
      ringKrullDim (S.presheaf.stalk (f x)) + (functionFieldTrdeg : WithBot ℕ∞) := sorry

/-- Lemma 29.52.1 (2): under the same hypotheses, if `S` is universally catenary then the
dimension formula at `x` is an equality. -/
@[stacks 02JU]
theorem ringKrullDim_stalk_eq_ringKrullDim_stalk_image_add_functionFieldTrdeg_sub_residueFieldTrdeg_of_universallyCatenary
    [LocallyOfFiniteType f] [UniversallyCatenary S] [IsIntegral X] [IsIntegral S]
    [IsDominant f] [Algebra S.functionField X.functionField] (x : X) :
    ringKrullDim (X.presheaf.stalk x) =
      ringKrullDim (S.presheaf.stalk (f x)) +
        ((functionFieldTrdeg - residueFieldTrdegAt x) : WithBot ℕ∞) := sorry

/-- Companion additive form of Lemma 29.52.1 (2), avoiding subtraction in the public equality. -/
theorem ringKrullDim_stalk_add_residueFieldTrdeg_eq_ringKrullDim_stalk_image_add_functionFieldTrdeg_of_universallyCatenary
    [LocallyOfFiniteType f] [UniversallyCatenary S] [IsIntegral X] [IsIntegral S]
    [IsDominant f] [Algebra S.functionField X.functionField] (x : X) :
    ringKrullDim (X.presheaf.stalk x) + (residueFieldTrdegAt x : WithBot ℕ∞) =
      ringKrullDim (S.presheaf.stalk (f x)) + (functionFieldTrdeg : WithBot ℕ∞) := sorry

end

end

end AlgebraicGeometry
