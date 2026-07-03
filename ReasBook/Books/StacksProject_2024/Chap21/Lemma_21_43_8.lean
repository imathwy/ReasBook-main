import StacksProject_2024.Chap21.Definition_21_43_1
import StacksProject_2024.Chap21.Lemma_21_43_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open Opposite

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory.ModulesOnCategory

section

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
variable
  (RGamma :
    ∀ U : C,
      DerivedCategory (PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) ⥤
        DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (derivedRestrict :
    ∀ {U V : C},
      (U ⟶ V) →
        DerivedCategory (ModuleCat (𝒪.obj (op V))) ⥤
          DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)

local notation "Ring𝒪" => 𝒪 ⋙ forget₂ CommRingCat RingCat
local notation "DModO" => DerivedCategory (PresheafOfModules Ring𝒪)

local notation "QCoh" => QC 𝒪 RGamma derivedRestrict comparison

/-- A cardinal `κ` controls small nonzero sources in `QC(\mathcal O)` and countable direct-sum
factorizations from `κ`-bounded objects. -/
class IsBoundForSmallSourcesAndCountableCoproductFactorizations
    (κ : Cardinal) : Prop where
  /-- Every nonzero quasi-coherent object receives a nonzero map from a `κ`-bounded
  quasi-coherent object. -/
  nonzero_morphism_from_bounded_object :
    ∀ (K : QCoh), ¬ IsZero K →
      ∃ (E : QCoh) (f : E ⟶ K),
        f ≠ 0 ∧ derivedObjectCardinal 𝒪 E.obj ≤ κ
  /-- Every map from a `κ`-bounded quasi-coherent object into a countable direct sum factors
  through a countable direct sum of `κ`-bounded source objects. -/
  countable_coproduct_factorization :
    ∀ (E : QCoh) (K : ℕ → QCoh) [HasCoproduct K] (α : E ⟶ ∐ K),
      derivedObjectCardinal 𝒪 E.obj ≤ κ →
        ∃ (E' : ℕ → QCoh) (_hE' : HasCoproduct E')
          (φ : ∀ n : ℕ, E' n ⟶ K n) (β : E ⟶ ∐ E'),
          (∀ n : ℕ, derivedObjectCardinal 𝒪 (E' n).obj ≤ κ) ∧
            α = β ≫ Limits.Sigma.desc (fun n : ℕ ↦ φ n ≫ Limits.Sigma.ι K n)

-- Proof sketch: choose `κ` dominating the bounds from Lemmas `21.43.6`, `21.43.7`, and
-- `15.103.5`. For a nonzero `K`, represent a nonzero cohomology class by a small image subcomplex
-- and enlarge it using the quasi-coherent closure construction to obtain a nonzero bounded source.
-- For a map into a countable coproduct, represent it on complexes, factor each component through a
-- bounded quasi-coherent subcomplex, and reassemble these componentwise factorizations into a map
-- through the coproduct of the bounded sources.
/-- Lemma 21.43.8: there exists a cardinal `\kappa` such that every nonzero object of
`QC(\mathcal O)` receives a nonzero morphism from a `\kappa`-bounded object, and every morphism
from a `\kappa`-bounded object into a countable direct sum factors through a countable direct sum
of `\kappa`-bounded source objects. -/
theorem exists_cardinal_for_small_sources_and_countable_coproduct_factorizations :
    ∃ κ : Cardinal,
      IsBoundForSmallSourcesAndCountableCoproductFactorizations
        𝒪 RGamma derivedRestrict comparison κ := sorry

end

end CategoryTheory.ModulesOnCategory
