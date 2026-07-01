import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

/- Domain-style sampling for Lemma 19.7.1:
- primary domain: injective objects in a category, specialized here to abelian sheaves on a site;
- sampled owner API:
  `Injective`,
  `Injective.factors`,
  `Injective.factorThru`,
  `Injective.comp_factorThru`;
- best owner abstraction: the canonical extension morphism
  `Injective.factorThru (φ ≫ jSucc ℱ α) i`;
- primitive data: the monomorphism `i`, the successor-stage map
  `J_[α](ℱ) ⟶ J_[Order.succ α](ℱ)`, and the morphism `φ`;
- derived API: the resulting commuting square, expressed canonically as `CommSq`.

Source/core/bridge triage:
- `source-facing`: the successor-stage extension square for the transfinite system `J_[α](ℱ)`;
- `core/canonical`: `Injective.factorThru`;
- `bridge/view`: this lemma, which specializes the canonical lift to the source-facing recursive
  stage notation `J_[α](ℱ)`.

The file should expose the square using the canonical lift and the source-facing stage notation,
rather than a generic family wrapper or an existential reformulation of `Injective.factors`. -/

section

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)

variable (J : Sheaf K AddCommGrpCat.{max u v} → Ordinal → Sheaf K AddCommGrpCat.{max u v})
variable (jSucc : ∀ (ℱ : Sheaf K AddCommGrpCat.{max u v}) (α : Ordinal),
  J ℱ α ⟶ J ℱ (Order.succ α))

local notation "J_[" α "](" ℱ ")" => J ℱ α

-- Proof sketch: compose `φ` with the source-facing successor-stage map
-- `J_[α](ℱ) ⟶ J_[Order.succ α](ℱ)` and apply the canonical injective lift across `i`.
/-- Lemma 19.7.1: for an injective morphism `i : 𝒢₁ ⟶ 𝒢₂` of abelian sheaves on a site, the
canonical extension of a map `φ : 𝒢₁ ⟶ J_[α](ℱ)` to the successor stage
`J_[Order.succ α](ℱ)` gives a commuting square. -/
theorem abelianSheaf_extend_to_successor_injective_stage
    {𝒢₁ 𝒢₂ : Sheaf K AddCommGrpCat.{max u v}}
    (i : 𝒢₁ ⟶ 𝒢₂) [Mono i]
    (ℱ : Sheaf K AddCommGrpCat.{max u v}) (α : Ordinal) (φ : 𝒢₁ ⟶ J_[α](ℱ))
    [Injective (J_[Order.succ α](ℱ))] :
    CommSq φ i (jSucc ℱ α) (Injective.factorThru (φ ≫ jSucc ℱ α) i) := by
  refine ⟨?_⟩
  exact (Injective.comp_factorThru (φ ≫ jSucc ℱ α) i).symm

end
