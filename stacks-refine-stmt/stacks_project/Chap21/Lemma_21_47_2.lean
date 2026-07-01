import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable (Mod : Type w) [Category.{v} Mod] [Abelian Mod]
variable (ModLoc : C → Type w)
variable [∀ U : C, Category.{v} (ModLoc U)]
variable [∀ U : C, Abelian (ModLoc U)]

/- The parameter `strictlyPerfect U` stands for the strict-perfectness predicate on complexes of
`\mathcal O_U`-modules. -/
variable (strictlyPerfect : ∀ U : C, CochainComplex (ModLoc U) ℤ → Prop)

/- The parameter `localizedRestrictionDerived U` stands for the derived restriction functor
`D(\mathcal O) → D(\mathcal O_U)`. -/
variable (localizedRestrictionDerived :
  ∀ U : C, DerivedCategory Mod ⥤ DerivedCategory (ModLoc U))

/- The parameter `complexIsPerfect` stands for perfectness on complexes of `\mathcal O`-modules. -/
variable (complexIsPerfect : CochainComplex Mod ℤ → Prop)

/- The parameter `derivedIsPerfect` stands for perfectness on `D(\mathcal O)`. -/
variable (derivedIsPerfect : DerivedCategory Mod → Prop)

section

variable {J : GrothendieckTopology C}
variable {Mod : Type w} [Category.{v} Mod] [Abelian Mod]
variable {ModLoc : C → Type w}
variable [∀ U : C, Category.{v} (ModLoc U)]
variable [∀ U : C, Abelian (ModLoc U)]
variable {strictlyPerfect : ∀ U : C, CochainComplex (ModLoc U) ℤ → Prop}
variable {localizedRestrictionDerived :
  ∀ U : C, DerivedCategory Mod ⥤ DerivedCategory (ModLoc U)}
variable {complexIsPerfect : CochainComplex Mod ℤ → Prop}
variable {derivedIsPerfect : DerivedCategory Mod → Prop}

-- Proof sketch: because `X` is final, any object of the site admits a cover obtained by pulling
-- back the chosen cover of `X`. The given strictly perfect local models on that cover then yield
-- the local strictly perfect representatives required by the definition of perfectness.
/-- Lemma 21.47.2 (1): if a derived `\mathcal O`-module becomes on a covering of a final object
isomorphic in the localized derived categories to strictly perfect complexes, then it is perfect.
-/
theorem isPerfect_of_exists_cover_on_finalObject
    (E : DerivedCategory Mod) (X : C) (_hX : IsTerminal X)
    (hcover :
      ∃ T : J.Cover X, ∀ I : T.Arrow,
        ∃ E' : CochainComplex (ModLoc I.Y) ℤ,
          strictlyPerfect I.Y E' ∧
            ∃ α :
              ((DerivedCategory.Q :
                  CochainComplex (ModLoc I.Y) ℤ ⥤
                    DerivedCategory (ModLoc I.Y)).obj E') ⟶
                (localizedRestrictionDerived I.Y).obj E,
              IsIso α) :
    derivedIsPerfect E := sorry

-- Proof sketch: unfold the definition of derived perfectness to choose one perfect representative
-- of `E`. Any other complex representing `E` is isomorphic to that representative in the derived
-- category, so the local strictly perfect models transport across the representing isomorphism.
/-- Lemma 21.47.2 (2): if `E` is perfect, then every complex representing `E` is perfect. -/
theorem cochainComplex_isPerfect_of_represents_isPerfect
    (E : DerivedCategory Mod) (K : CochainComplex Mod ℤ)
    (e : ((DerivedCategory.Q : CochainComplex Mod ℤ ⥤ DerivedCategory Mod).obj K) ≅ E)
    (hE : derivedIsPerfect E) :
    complexIsPerfect K := sorry

end

end

end SheafOfModules.RingedSite
