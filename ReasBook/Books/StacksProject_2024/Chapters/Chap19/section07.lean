import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_19_7_1 (from Chap19) -/
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

/-! ### Lemma_19_7_2 (from Chap19) -/
open CategoryTheory MorphismProperty

universe w v u

section

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)
variable {I : Type w} (𝒢 : I → Sheaf K AddCommGrpCat.{max u v})

-- Proof sketch: replace the family `(𝒢 i)` by its coproduct, consider the underlying set of all
-- sections of that coproduct, and choose an ordinal whose cofinality is strictly larger than that
-- cardinal. Then apply the canonical Grothendieck-abelian smallness criterion for monomorphisms
-- to each `𝒢 i`; the single regular cardinal dominates all relevant subobject cardinals at once,
-- so every member of the family is small for the same ordinal bound.
/-- Lemma 19.7.2: for a family of abelian sheaves on a site, there is a single ordinal `β` such
that every member of the family is `β`-small with respect to monomorphisms; equivalently, maps
from any `𝒢 i` into a `β`-stage transfinite composition of monomorphisms factor through some
earlier stage. -/
theorem abelianSheaf_family_exists_uniform_smallness_bound_wrt_monomorphisms
    : ∃ β : Ordinal, ∀ i : I, is_alpha_small_wrt (𝒢 i) (monomorphisms _) β := sorry

end

/-! ### Lemma_19_7_3 (from Chap19) -/
open CategoryTheory
open scoped CategoryTheory.FreeAbelianSheaf

universe u v

noncomputable section

/- Domain-style sampling for Lemma 19.7.3:
- primary domain: injective objects in the category of abelian sheaves on a site, tested on the
  source-facing family of free abelian sheaves on representables;
- sampled owner declarations:
  `Injective`,
  `Injective.factors`,
  `freeAbelianSheaf`,
  `(ℤ_ (yoneda.obj X))^#[K]`;
- best owner abstraction: the canonical class `Injective`; the free abelian sheaves on
  representables are the source-facing test objects, not a second owner abstraction;
- primitive data: an object `X`, a monomorphism `i : 𝒮 ⟶ (ℤ_ (yoneda.obj X))^#`, and a morphism
  `φ : 𝒮 ⟶ 𝒥`;
- derived API: the extension morphism `ψ` across `i`.

Source/core/bridge triage:
- `source-facing`: the Stacks-project test family `(ℤ_ (yoneda.obj X))^#`;
- `core/canonical`: `Injective` and its extension owner `Injective.factors`;
- `bridge/view`: this theorem, which proves injectivity from the source-facing extension test. -/

-- Proof sketch: argue by Baer's criterion as in More on Algebra, Lemma 15.54.1. For a strict
-- monomorphism of abelian sheaves and a map into `𝒥`, choose an object `X` and a section of the
-- larger sheaf not coming from the smaller one; the associated map from `Z_X^#`, formalized as
-- the free abelian sheaf on `yoneda.obj X`, and the assumed extension property produce a strictly
-- larger intermediate subsheaf to which the map extends, contradicting maximality.
/-- Lemma 19.7.3: if every morphism from an abelian subsheaf of `Z_X^#`, formalized as a
monomorphism into `(ℤ_ (yoneda.obj X))^#[K]`,
extends to `𝒥`, then `𝒥` is an injective abelian sheaf on `(C, K)`. -/
theorem injective_of_representable_free_abelian_extension_property
    {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)
    [HasWeakSheafify K AddCommGrpCat]
    (𝒥 : Sheaf K AddCommGrpCat)
    (h𝒥 : ∀ (X : C) (𝒮 : Sheaf K AddCommGrpCat)
      (i : 𝒮 ⟶ (ℤ_ (yoneda.obj X))^#[K]) [Mono i]
      (φ : 𝒮 ⟶ 𝒥),
        ∃ ψ : (ℤ_ (yoneda.obj X))^#[K] ⟶ 𝒥,
          i ≫ ψ = φ) :
    Injective 𝒥 := by
  sorry

/-! ### Theorem_19_7_4 (from Chap19) -/
open CategoryTheory

universe u v

noncomputable section

/-
Domain-style sampling for Theorem 19.7.4:
- primary domain: enough injectives and functorial injective embeddings for abelian sheaves on a
  site;
- sampled owner declarations:
  `EnoughInjectives`,
  `HasFunctorialInjectiveEmbeddings`,
  the Chapter 12 instance `HasFunctorialInjectiveEmbeddings C → EnoughInjectives C`,
  `hasFunctorialInjectiveEmbeddings_of_enoughInjectives`;
- best owner abstraction: the source-facing statement in this file is
  `EnoughInjectives (Sheaf K AddCommGrpCat)`, while
  `HasFunctorialInjectiveEmbeddings (Sheaf K AddCommGrpCat)` is the canonical owner-level derived
  API used downstream;
- primitive data: enough injectives for the category of abelian sheaves on the site;
- derived API: the owner-level `HasFunctorialInjectiveEmbeddings` instance supplied by the Chapter
  12 bridge.

Source/core/bridge triage:
- `source-facing`: Theorem 19.7.4, asserting enough injectives for abelian sheaves on a site;
- `core/canonical`: `EnoughInjectives` and `HasFunctorialInjectiveEmbeddings`;
- `bridge/view`: the canonical Chapter 12 passage from enough injectives to functorial injective
  embeddings.
-/

-- Proof sketch: choose the uniform ordinal bound from Lemma 19.7.2 for the family of all
-- subsheaves of free abelian sheaves on representables, build the transfinite system `J_α(ℱ)`,
-- and use Lemma 19.7.3 together with Lemma 19.7.1 to obtain functorial injective embeddings of
-- abelian sheaves; the Chapter 12 bridge then yields enough injectives.
/-- Theorem 19.7.4: the category of sheaves of abelian groups on a site has enough injectives. -/
theorem siteAbelianSheaf_hasEnoughInjectives
    {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) :
    EnoughInjectives (Sheaf K AddCommGrpCat.{max u v}) := sorry

/-- Canonical owner-level form of Theorem 19.7.4 for abelian sheaves on a site. -/
instance siteAbelianSheaf_hasFunctorialInjectiveEmbeddings
    {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) :
    HasFunctorialInjectiveEmbeddings (Sheaf K AddCommGrpCat.{max u v}) := by
  exact hasFunctorialInjectiveEmbeddings_of_isGrothendieckAbelian
