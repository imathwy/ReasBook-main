import Mathlib
import stacks_project.Chap13.Definition_13_19_1
import stacks_project.Chap13.Remark_13_19_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape HomotopyCategory

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {K L : CochainComplex 𝒜 ℤ}

/- Domain-style sampling:
- primary domain: uniqueness of homotopy lifts from bounded-above projective cochain complexes
  along quasi-isomorphisms;
- sampled owner declarations:
  `CochainComplex.ProjectiveMinus`,
  `CochainComplex.MinusWithTermsIn.minus`,
  `CochainComplex.MinusWithTermsIn.term_mem`,
  `homotopyCategory_postcomp_bijective_of_quasiIso_from_boundedAbove_projective`,
  `HomotopyCategory.eq_of_homotopy`,
  `HomotopyCategory.homotopyOfEq`;
- best owner abstraction: `ProjectiveMinus 𝒜` is the chapter owner for a bounded-above complex of
  projective objects, so this lemma should take that owner directly
  instead of separate boundedness and termwise-projective hypotheses;
- primitive data: a projective-minus source complex `P`, a quasi-isomorphism `α : L ⟶ K`, and
  maps `γ : P ⟶ K`, `β₁, β₂ : P ⟶ L`;
- derived API: uniqueness of lifts up to homotopy, obtained from the owner-level bijectivity of
  postcomposition in the homotopy category.

Source/core/bridge triage:
- `source-facing`: the uniqueness-up-to-homotopy statement below;
- `core/canonical`: `ProjectiveMinus 𝒜` and the homotopy-category postcomposition bijection for
  K-projective sources;
- `bridge/view`: the passage from commuting-up-to-homotopy triangles to equality in the homotopy
  category, then back to a homotopy via `homotopyOfEq`.
-/

-- Proof sketch: pass to the homotopy category. The hypotheses `β₁ ≫ α ∼ γ` and `β₂ ≫ α ∼ γ`
-- say that postcomposition by `α` sends the classes of `β₁` and `β₂` to the same morphism
-- `P^• ⟶ K^•`. By Remark 13.19.5, instantiated with the owner
-- `ProjectiveMinus 𝒜`,
-- postcomposition with the quasi-isomorphism `α` is bijective on maps out of `P^•`, so those
-- classes are equal; then
-- `HomotopyCategory.homotopyOfEq` yields a homotopy `β₁ ∼ β₂`.
/-- Lemma 13.19.7: if `α : L^• ⟶ K^•` is a quasi-isomorphism, `P^•` is bounded above with
projective terms, and two morphisms `β₁, β₂ : P^• ⟶ L^•` both make the triangle with
`γ : P^• ⟶ K^•` commute up to homotopy, then `β₁` and `β₂` are homotopic. -/
theorem homotopic_lifts_along_quasiIso_from_boundedAbove_projective
    (P : ProjectiveMinus 𝒜) (α : L ⟶ K) [QuasiIso α]
    (γ : (P : CochainComplex 𝒜 ℤ) ⟶ K)
    (β₁ β₂ : (P : CochainComplex 𝒜 ℤ) ⟶ L)
    (hβ₁ : Nonempty (Homotopy (β₁ ≫ α) γ))
    (hβ₂ : Nonempty (Homotopy (β₂ ≫ α) γ)) :
    Nonempty (Homotopy β₁ β₂) := by
  let Q := HomotopyCategory.quotient 𝒜 (up ℤ)
  obtain ⟨hβ₁⟩ := hβ₁
  obtain ⟨hβ₂⟩ := hβ₂
  refine ⟨homotopyOfEq _ _ ?_⟩
  apply (homotopyCategory_postcomp_bijective_of_quasiIso_from_boundedAbove_projective α P).injective
  simpa [Q, Functor.map_comp] using
    (eq_of_homotopy _ _ hβ₁).trans (eq_of_homotopy _ _ hβ₂).symm

end CochainComplex
