import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace CategoryTheory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {Λ : Type u} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{u} Λ)]

/-- The `n`th quotient `Λ / I^n`, viewed as an object of `ModuleCat Λ`. -/
abbrev idealPowerQuotientSequence (I : Ideal Λ) (n : ℕ) : ModuleCat.{u} Λ :=
  ModuleCat.of Λ (Λ ⧸ I ^ n)

/-- The transition map `Λ / I^(n + 1) → Λ / I^n` in the `I`-adic quotient tower. -/
abbrev idealPowerQuotientTransition (I : Ideal Λ) (n : ℕ) :
    idealPowerQuotientSequence I (n + 1) ⟶ idealPowerQuotientSequence I n :=
  ModuleCat.ofHom
    (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right (Nat.le_succ n))).toLinearMap

/-- The inverse system `n ↦ Λ / I^n` in `ModuleCat Λ`. -/
abbrev idealPowerQuotientSystem (I : Ideal Λ) : ℕᵒᵖ ⥤ ModuleCat.{u} Λ :=
  Functor.ofOpSequence (idealPowerQuotientTransition I)

/-- The inverse system of constant sheaves with values `Λ / I^n`. -/
abbrev constantIdealPowerQuotientSheafSystem
    (J : GrothendieckTopology C) (I : Ideal Λ) :
    ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{u} Λ) :=
  idealPowerQuotientSystem I ⋙ constantSheaf J (ModuleCat.{u} Λ)

/-- The completed constant sheaf `\underline Λ^∧ = lim_n \underline{Λ / I^n}`. -/
abbrev constantIadicCompletionSheaf
    (J : GrothendieckTopology C) (I : Ideal Λ) :
    Sheaf J (ModuleCat.{u} Λ) :=
  limit (constantIdealPowerQuotientSheafSystem J I)

/-- The constant sheaf with value `Λ / I`. -/
abbrev constantIdealQuotientSheaf
    (J : GrothendieckTopology C) (I : Ideal Λ) :
    Sheaf J (ModuleCat.{u} Λ) :=
  (constantIdealPowerQuotientSheafSystem J I).obj (op 1)

/-- The sections of the completed constant sheaf over `U`. -/
abbrev constantIadicCompletionSections
    (J : GrothendieckTopology C) (I : Ideal Λ) (U : C) :
    ModuleCat.{u} Λ :=
  (constantIadicCompletionSheaf J I).1.obj (op U)

/-- The sections of the constant quotient sheaf `\underline{Λ / I}` over `U`. -/
abbrev constantIdealQuotientSections
    (J : GrothendieckTopology C) (I : Ideal Λ) (U : C) :
    ModuleCat.{u} Λ :=
  (constantIdealQuotientSheaf J I).1.obj (op U)

/-- The canonical map from the sections of the completed constant sheaf to the sections of
`\underline{Λ / I}`, induced by the projection to the first quotient in the inverse system. -/
abbrev constantIadicCompletionSectionsToConstantIdealQuotient
    (J : GrothendieckTopology C) (I : Ideal Λ) (U : C) :
    constantIadicCompletionSections J I U →ₗ[Λ] constantIdealQuotientSections J I U :=
  (((limit.π (constantIdealPowerQuotientSheafSystem J I) (op 1)).hom.app (op U)).hom)

-- Proof sketch: the target is a `Λ / I`-module, so multiplication by any element of `I` is zero;
-- hence the projection to the first quotient annihilates `I · \underline{Λ}^∧(U)`.
/-- The projection from completed sections to `\underline{Λ / I}(U)` kills the submodule generated
by `I`. -/
theorem smul_top_le_constantIadicCompletionSectionsToConstantIdealQuotient_ker
    (J : GrothendieckTopology C) (I : Ideal Λ) (U : C) :
    I • (⊤ : Submodule Λ (constantIadicCompletionSections J I U)) ≤
      LinearMap.ker
        (constantIadicCompletionSectionsToConstantIdealQuotient J I U) := sorry

/-- The canonical map from the quotient of completed sections modulo `I` to
`\underline{Λ / I}(U)`. -/
abbrev constantIadicCompletionSectionsModIComparison
    (J : GrothendieckTopology C) (I : Ideal Λ) (U : C) :
    ((constantIadicCompletionSections J I U) ⧸
      (I • (⊤ : Submodule Λ (constantIadicCompletionSections J I U)))) →ₗ[Λ]
      constantIdealQuotientSections J I U :=
  (I • (⊤ : Submodule Λ (constantIadicCompletionSections J I U))).liftQ
    (constantIadicCompletionSectionsToConstantIdealQuotient J I U)
    (smul_top_le_constantIadicCompletionSectionsToConstantIdealQuotient_ker
      J I U)

-- Proof sketch: evaluate the inverse-limit sheaf at `U`, identify the result with the limit of the
-- system `Λ / I^n` of flat `Λ / I^n`-modules with surjective transition maps, and then apply the
-- flatness criterion for inverse limits over a Noetherian base.
/-- Lemma 18.42.4 (1): for a Noetherian ring `Λ`, the sections of the completed constant sheaf
`\underline Λ^∧ = lim_n \underline{Λ / I^n}` are flat over `Λ`. -/
theorem constantIadicCompletionSheaf_app_flat
    [IsNoetherianRing Λ] (I : Ideal Λ) (U : C) :
    Module.Flat Λ (constantIadicCompletionSections J I U) := sorry

-- Proof sketch: compare the inverse system `Λ / I^n` with its reduction modulo `I`, use exactness
-- of inverse limits with surjective transition maps, and identify the resulting quotient with the
-- constant sheaf on `Λ / I`.
/-- Lemma 18.42.4 (2): the quotient of the completed constant sheaf by `I` identifies with the
constant sheaf `\underline{Λ / I}` on sections. -/
theorem constantIadicCompletionSectionsModIComparison_bijective
    [IsNoetherianRing Λ] (I : Ideal Λ) (U : C) :
    Function.Bijective (constantIadicCompletionSectionsModIComparison J I U) := sorry

end CategoryTheory
