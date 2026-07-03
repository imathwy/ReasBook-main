import Mathlib
import StacksProject_2024.Chap13.Definition_13_18_1
import StacksProject_2024.Chap13.Remark_13_18_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape HomotopyCategory

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {K L : CochainComplex 𝒜 ℤ}

/- Domain-style sampling:
- primary domain: homotopy-category uniqueness of lifts along quasi-isomorphisms into
  bounded-below injective cochain complexes;
- sampled owner declarations:
  `CochainComplex.InjectivePlus`,
  `CochainComplex.PlusWithTermsIn.plus`,
  `CochainComplex.PlusWithTermsIn.term_mem`,
  `CochainComplex.IsKInjective.Qh_map_bijective`,
  `homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective`,
  `HomotopyCategory.eq_of_homotopy`,
  `HomotopyCategory.homotopyOfEq`;
- best owner abstraction: `CochainComplex.InjectivePlus`, the chapter owner for bounded-below
  cochain complexes with injective terms; the bridge theorem
  `homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective` is derived API whose
  canonical core owner is `CochainComplex.IsKInjective.Qh_map_bijective`;
- primitive data: a quasi-isomorphism `α : K ⟶ L`, a bounded-below injective target
  `I : InjectivePlus 𝒜`, and maps `γ : K ⟶ I`, `β₁, β₂ : L ⟶ I`;
- derived API: uniqueness of the lift up to homotopy.

Source/core/bridge triage:
- `source-facing`: the uniqueness-up-to-homotopy statement below;
- `core/canonical`: `CochainComplex.InjectivePlus` and
  `CochainComplex.IsKInjective.Qh_map_bijective`;
- `bridge/view`: the chapter bijectivity theorem on homotopy-category precomposition, instantiated
  from the `InjectivePlus` owner.
-/

-- Proof sketch: pass to the homotopy category. The hypotheses `α ≫ β₁ ∼ γ` and `α ≫ β₂ ∼ γ`
-- say that precomposition by `α` sends the classes of `β₁` and `β₂` to the same morphism
-- `K^• ⟶ I^•`. By Remark 13.18.5, instantiated with the bounded-below injective owner `I`,
-- precomposition with the quasi-isomorphism `α` is bijective on maps into `I^•`, so those
-- classes are equal; then
-- `HomotopyCategory.homotopyOfEq` yields a homotopy `β₁ ∼ β₂`.
/-- Lemma 13.18.7: if `α : K^• ⟶ L^•` is a quasi-isomorphism, `I^•` is bounded below with
injective terms, and two morphisms `β₁, β₂ : L^• ⟶ I^•` both make the triangle with
`γ : K^• ⟶ I^•` commute up to homotopy, then `β₁` and `β₂` are homotopic. -/
theorem homotopic_lifts_of_quasiIso_to_boundedBelow_injective
    (α : K ⟶ L) [QuasiIso α] (I : InjectivePlus 𝒜) (γ : K ⟶ I) (β₁ β₂ : L ⟶ I)
    (hβ₁ : Nonempty (Homotopy (α ≫ β₁) γ))
    (hβ₂ : Nonempty (Homotopy (α ≫ β₂) γ)) :
    Nonempty (Homotopy β₁ β₂) := by
  let Q := HomotopyCategory.quotient 𝒜 (up ℤ)
  obtain ⟨hβ₁⟩ := hβ₁
  obtain ⟨hβ₂⟩ := hβ₂
  refine ⟨homotopyOfEq _ _ ?_⟩
  apply (homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective α I).injective
  simpa [Q, Functor.map_comp] using
    (eq_of_homotopy _ _ hβ₁).trans (eq_of_homotopy _ _ hβ₂).symm

end CochainComplex
