import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_13_31_1 (from Chap13) -/
open CategoryTheory
open ComplexShape
open HomotopyCategory

/- Definition 13.31.1: in an abelian category, the textbook notion of a K-injective complex is the
canonical mathlib class `CochainComplex.IsKInjective`. It encodes that every morphism from an
acyclic cochain complex to the given complex is null-homotopic, equivalently zero in the homotopy
category `K(\mathcal A)`. -/
recall CochainComplex.IsKInjective

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "Q" => quotient 𝒜 (up ℤ)

-- Domain-style sampling:
-- * primary domain: K-injective cochain complexes in the homotopy category `K(𝒜)`;
-- * sampled owner declarations:
--   `CochainComplex.IsKInjective`,
--   `CochainComplex.isKInjective_iff_rightOrthogonal`,
--   `CochainComplex.IsKInjective.rightOrthogonal`,
--   `HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic`;
-- * best owner abstraction: the canonical owner is the complex `I` with property `I.IsKInjective`;
-- * source/core/bridge triage:
--   `core/canonical`: `I.IsKInjective`;
--   `bridge/view`: the vanishing criterion in `K(𝒜)` for morphisms from acyclic complexes;
-- * primitive data: only the complex `I`;
-- * derived API: the source-facing vanishing characterization below.

-- Proof sketch: combine `isKInjective_iff_rightOrthogonal` with
-- `HomotopyCategory.subcategoryAcyclic C` and rewrite acyclicity using
-- `HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic`.
/-- A cochain complex is K-injective exactly when every morphism to it from an acyclic complex
vanishes in the homotopy category. -/
theorem isKInjective_iff_homotopyCategory_from_acyclic_eq_zero
    (I : CochainComplex 𝒜 ℤ) :
    I.IsKInjective ↔
      ∀ (M : CochainComplex 𝒜 ℤ) (_ : M.Acyclic)
        (f : (Q).obj M ⟶ (Q).obj I), f = 0 := by
  rw [isKInjective_iff_rightOrthogonal]
  constructor
  · intro h M hM f
    exact h f ((quotient_obj_mem_subcategoryAcyclic_iff_acyclic M).2 hM)
  · intro h X f hX
    obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    exact h M ((quotient_obj_mem_subcategoryAcyclic_iff_acyclic M).1 hX) f

end CochainComplex

/-! ### Lemma_13_31_2 (from Chap13) -/
open CategoryTheory DerivedCategory ComplexShape HomotopyCategory

universe w v u

namespace CochainComplex

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "KHom" => HomotopyCategory 𝒜 (up ℤ)
local notation "Qis" => quasiIso 𝒜 (up ℤ)

-- Domain-style sampling:
-- * primary domain: K-injective cochain complexes and the localization
--   `K(𝒜) ⥤ D(𝒜)` at quasi-isomorphisms.
-- * inspected owner declarations:
--   `CochainComplex.IsKInjective`,
--   `CochainComplex.isKInjective_iff_rightOrthogonal`,
--   `CochainComplex.IsKInjective.rightOrthogonal`,
--   `CochainComplex.IsKInjective.Qh_map_bijective`,
--   `DerivedCategory.isIso_Qh_map_iff`.
-- * layer: `source-facing`; Lemma 13.31.2 is genuinely a three-way equivalence, so the main entry
--   should remain a local `List.TFAE`, but the owner abstraction must stay `I.IsKInjective`.
-- * core/canonical owner abstraction: `I.IsKInjective`.
-- * primitive data: only the cochain complex `I`.
-- * derived API: bijectivity of precomposition by quasi-isomorphisms into `I`, and bijectivity of
--   the canonical localization map `Qh.map` on morphisms with target `I`.
-- * abstraction check: there is no coordinate bookkeeping here; the correct ambient owner is the
--   homotopy/derived-category localization API, not a local wrapper around Hom-sets.

-- Proof sketch: clause `(2)` is exactly the `Qis.isLocal` formulation of the acyclic
-- right-orthogonality criterion `isKInjective_iff_rightOrthogonal`, while clause `(3)` is the
-- canonical owner theorem `IsKInjective.Qh_map_bijective`; conversely, bijectivity of `Qh.map`
-- transports the derived-category bijection induced by any quasi-isomorphism back to the
-- homotopy category.
/-- A cochain complex is K-injective exactly when precomposition by every quasi-isomorphism in the
homotopy category induces a bijection on morphisms into it. -/
theorem isKInjective_iff_precomp_bijective_of_quasiIso (I : CochainComplex 𝒜 ℤ) :
    I.IsKInjective ↔
      ∀ ⦃M N : KHom⦄ (f : M ⟶ N), Qis f →
        Function.Bijective
          (fun g : N ⟶ (quotient 𝒜 (up ℤ)).obj I ↦ f ≫ g) := by
  simpa only [MorphismProperty.isLocal_iff,
    HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W 𝒜] using
    (show I.IsKInjective ↔
        (HomotopyCategory.subcategoryAcyclic 𝒜).trW.isLocal
          ((quotient 𝒜 (up ℤ)).obj I) by
      rw [CochainComplex.isKInjective_iff_rightOrthogonal,
        ← ObjectProperty.isLocal_trW (HomotopyCategory.subcategoryAcyclic 𝒜)])

/-- Lemma 13.31.2: for a complex `I^•` in an abelian category, the following are equivalent:
`I^•` is K-injective; precomposition with any quasi-isomorphism in the homotopy category induces a
bijection on morphisms into `I^•`; and for every complex, the canonical map from morphisms in the
homotopy category to morphisms in the derived category with target `I^•` is bijective. -/
theorem isKInjective_tfae [HasDerivedCategory.{w} 𝒜] (I : CochainComplex 𝒜 ℤ) :
    List.TFAE
      [ I.IsKInjective
      , ∀ ⦃M N : KHom⦄ (f : M ⟶ N), Qis f →
          Function.Bijective
            (fun g : N ⟶ (quotient 𝒜 (up ℤ)).obj I ↦ f ≫ g)
      , ∀ N : KHom,
          Function.Bijective
            (Qh.map : (N ⟶ (quotient 𝒜 (up ℤ)).obj I) → _)
      ] := by
  tfae_have 1 ↔ 2 := isKInjective_iff_precomp_bijective_of_quasiIso I
  tfae_have 1 ↔ 3 := by
    let J : KHom := (quotient 𝒜 (up ℤ)).obj I
    constructor
    · intro hI N
      let _ : I.IsKInjective := hI
      simpa [J] using IsKInjective.Qh_map_bijective N I
    · intro hI
      refine (isKInjective_iff_precomp_bijective_of_quasiIso I).2 ?_
      intro M N f hf
      have hM :
          Function.Bijective
            (Qh.map : (M ⟶ J) → (Qh.obj M ⟶ Qh.obj J)) := by
        simpa [J] using hI M
      have hN :
          Function.Bijective
            (Qh.map : (N ⟶ J) → (Qh.obj N ⟶ Qh.obj J)) := by
        simpa [J] using hI N
      have : IsIso (Qh.map f) := (isIso_Qh_map_iff f).2 hf
      have hpre :
          Function.Bijective
            (fun g : Qh.obj N ⟶ Qh.obj J ↦ Qh.map f ≫ g) := by
        refine ⟨?_, ?_⟩
        · intro g₁ g₂ h
          exact (cancel_epi (Qh.map f)).1 h
        · intro g
          exact ⟨inv (Qh.map f) ≫ g, by simp⟩
      have hcomp :
          ((Qh.map :
              (M ⟶ J) →
                (Qh.obj M ⟶ Qh.obj J)) ∘
            fun g : N ⟶ J ↦ f ≫ g) =
          (fun g : Qh.obj N ⟶ Qh.obj J ↦ Qh.map f ≫ g) ∘
            (Qh.map :
              (N ⟶ J) →
                (Qh.obj N ⟶ Qh.obj J)) := by
        funext g
        simp [Functor.map_comp]
      have hcompBij :
          Function.Bijective
            (((Qh.map :
                (M ⟶ J) →
                  (Qh.obj M ⟶ Qh.obj J)) ∘
              fun g : N ⟶ J ↦ f ≫ g)) := by
        rw [hcomp]
        exact hpre.comp hN
      exact (Function.Bijective.of_comp_iff' hM _).mp hcompBij
  tfae_finish

end

end CochainComplex

/-! ### Lemma_13_31_3 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Pretriangulated
open ComplexShape

universe v u

namespace CochainComplex

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "KHom" => HomotopyCategory 𝒜 (up ℤ)
local notation "AcycOrth" =>
  ObjectProperty.rightOrthogonal (HomotopyCategory.subcategoryAcyclic 𝒜)

-- Domain-style sampling for Lemma 13.31.3:
-- * primary domain: K-injective cochain complexes inside the triangulated homotopy category
--   `K(𝒜)`;
-- * sampled owner declarations:
--   `CochainComplex.isKInjective_iff_rightOrthogonal`,
--   `HomotopyCategory.subcategoryAcyclic`,
--   `ObjectProperty.rightOrthogonal`,
--   `ObjectProperty.ext_of_isTriangulatedClosed₁/₂/₃`;
-- * source/core/bridge triage:
--   `source-facing`: the three two-out-of-three statements below;
--   `core/canonical`: the object property
--   `(HomotopyCategory.subcategoryAcyclic 𝒜).rightOrthogonal`;
--   `bridge/view`: the equivalence `isKInjective_iff_rightOrthogonal`;
-- * primitive data: only the distinguished triangle `T` and the K-injectivity hypotheses on its
--   vertices;
-- * derived API: two-out-of-three for membership in the canonical right orthogonal.

-- Proof sketch: identify K-injective complexes with the right orthogonal to the acyclic
-- subcategory via `CochainComplex.isKInjective_iff_rightOrthogonal`. Right orthogonals are
-- triangulated, and `K(\mathcal A)` is triangulated, so `ObjectProperty.ext_of_isTriangulatedClosed₃`
-- gives the third vertex from the first two.
/-- Lemma 13.31.3: if `T` is a distinguished triangle in `K(\mathcal A)` and the first two
vertices are represented by K-injective cochain complexes, then the third vertex is represented by
a K-injective cochain complex. Together with the rotated companion lemmas below, this is the
two-out-of-three property for K-injective complexes in distinguished triangles. -/
theorem isKInjective_obj₃_of_distinguished_triangle
    (T : Triangle KHom) (hT : T ∈ distTriang KHom)
    (h₁ : CochainComplex.IsKInjective T.obj₁.as) (h₂ : CochainComplex.IsKInjective T.obj₂.as) :
    CochainComplex.IsKInjective T.obj₃.as := by
  rw [CochainComplex.isKInjective_iff_rightOrthogonal] at h₁ h₂ ⊢
  exact (AcycOrth).ext_of_isTriangulatedClosed₃ T hT h₁ h₂

-- Proof sketch: rewrite K-injectivity as right orthogonality to acyclic complexes and use the
-- triangulated closure of right orthogonals together with
-- `ObjectProperty.ext_of_isTriangulatedClosed₂`.
/-- The `obj₁`-`obj₃` case of the K-injective two-out-of-three property in a distinguished
triangle of `K(\mathcal A)`. -/
theorem isKInjective_obj₂_of_distinguished_triangle
    (T : Triangle KHom) (hT : T ∈ distTriang KHom)
    (h₁ : CochainComplex.IsKInjective T.obj₁.as) (h₃ : CochainComplex.IsKInjective T.obj₃.as) :
    CochainComplex.IsKInjective T.obj₂.as := by
  rw [CochainComplex.isKInjective_iff_rightOrthogonal] at h₁ h₃ ⊢
  exact (AcycOrth).ext_of_isTriangulatedClosed₂ T hT h₁ h₃

-- Proof sketch: after the same identification with a right orthogonal, apply
-- `ObjectProperty.ext_of_isTriangulatedClosed₁` to the distinguished triangle `T`.
/-- The `obj₂`-`obj₃` case of the K-injective two-out-of-three property in a distinguished
triangle of `K(\mathcal A)`. -/
theorem isKInjective_obj₁_of_distinguished_triangle
    (T : Triangle KHom) (hT : T ∈ distTriang KHom)
    (h₂ : CochainComplex.IsKInjective T.obj₂.as) (h₃ : CochainComplex.IsKInjective T.obj₃.as) :
    CochainComplex.IsKInjective T.obj₁.as := by
  rw [CochainComplex.isKInjective_iff_rightOrthogonal] at h₂ h₃ ⊢
  exact (AcycOrth).ext_of_isTriangulatedClosed₁ T hT h₂ h₃

end

end CochainComplex

/-! ### Lemma_13_31_4 (from Chap13) -/
open CategoryTheory

universe v u

namespace CochainComplex

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Lemma 13.31.4:
- primary domain: bounded-below injective cochain complexes and their K-injectivity;
- sampled owner declarations:
  `CochainComplex.InjectivePlus`,
  `CochainComplex.plus_iff`,
  `CochainComplex.isKInjective_of_injective`,
  `CochainComplex.PlusWithTermsIn.instIsKInjective`;
- best owner abstraction: the chapter owner `CochainComplex.InjectivePlus 𝒜` for bounded-below
  cochain complexes with injective terms;
- primitive data: an owner object `I : CochainComplex.InjectivePlus 𝒜`;
- derived API: the canonical `IsKInjective` instance recalled below.

Source/core/bridge triage:
- `source-facing`: the textbook formulation below for an arbitrary bounded-below cochain complex of
  injectives;
- `core/canonical`: `CochainComplex.InjectivePlus 𝒜` together with its `IsKInjective` instance;
- `bridge/view`: the source wording is already subsumed by the owner-level instance built from
  `CochainComplex.plus_iff` and `CochainComplex.isKInjective_of_injective`, so no separate bridge
  declaration is needed here.
-/

/- Lemma 13.31.4: in an abelian category, a bounded below cochain complex of injective objects is
K-injective. This is the canonical owner instance on `CochainComplex.InjectivePlus 𝒜`, recalled
here rather than redeclared under a parallel theorem name. -/
recall PlusWithTermsIn.instIsKInjective

end

end CochainComplex

/-! ### Lemma_13_31_5 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open DerivedCategory
open HomologicalComplex

universe t w v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {T : Type t}
variable {I : T → CochainComplex 𝒜 ℤ} {P : CochainComplex 𝒜 ℤ}

local notation "Q" => DerivedCategory.Q

/-
Domain-style sampling for Lemma 13.31.5:
- primary domain: K-injective cochain complexes and products in the derived category;
- inspected owner declarations:
  * `CochainComplex.IsKInjective`
  * `CochainComplex.IsKInjective.Qh_map_bijective`
  * `CategoryTheory.Limits.PreservesLimit`
  * `HomologicalComplex.isLimitOfEval`
  * `CategoryTheory.Limits.Fan.IsLimit.lift`
  * `CategoryTheory.Limits.Fan.IsLimit.hom_ext`
  `IsLimit (Fan.mk P π)`; for the concrete termwise product family the canonical derived-category
  owner is the preservation statement `PreservesLimit (Discrete.functor I) Q`; the `Q.obj`-level
  universal morphisms are only a private bridge from an arbitrary chosen product cone to that
  owner;
- primitive data:
  * a family of complexes `I t`
  * a comparison family `π : ∀ t, P ⟶ I t`
- derived API:
  * the complex-level product witness `IsLimit (Fan.mk P π)`
  * the ambient instances `∀ t, (I t).IsKInjective`
  * `P.IsKInjective`
  * for a termwise product family `I`, the preservation witness
    `PreservesLimit (Discrete.functor I) Q`
  * the recoverable `IsLimit` witness in `DerivedCategory 𝒜` via
    `isLimitOfHasProductOfPreservesLimit`
  * the unique lift in `DerivedCategory 𝒜` for source objects of the form `Q.obj K`, together
    with the localization representative bridge from an arbitrary derived object via
    `Q.objPreimage`.

Source/core/bridge triage:
- source-facing: `isKInjective_of_product`, expressing the lemma through the complex-level product
  cone `Fan.mk P π`;
- core/canonical: `Fan.IsLimit` for the cochain-complex product cone `Fan.mk P π`, and for
  concrete termwise products the preservation owner `PreservesLimit (Discrete.functor I) Q`;
- bridge/view: `HomologicalComplex.isLimitOfEval` upgrades internal termwise product cones to
  `Fan.mk P π`, while `Q.objPreimage` and `Q.objObjPreimageIso` transport the `Q.obj`-level
  lift/uniqueness statement to an arbitrary derived object; this bridge stays private because the
  public owner is the preservation theorem.
-/

-- Proof sketch: for any acyclic complex `K`, the source proof studies the Hom-complex
-- `HomComplex K P`; we record the postcomposition map here because that is the canonical bridge
-- from the product cone on complexes to a product cone on Hom-complexes.
/-- Helper for Lemma 13.31.5: postcomposition by a morphism of complexes induces an additive map
on cochains of fixed degree in the Hom-complex. -/
private theorem homComplex_postcomp_map_zero
    {K L M : CochainComplex 𝒜 ℤ}
    (σ : L ⟶ M) (n : ℤ) :
    (0 : CochainComplex.HomComplex.Cochain K L n).comp
        (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero n) = 0 := by
  simpa only using
    (CochainComplex.HomComplex.Cochain.zero_comp
      (n₁ := n) (n₂ := 0) (n₁₂ := n) (h := add_zero n)
      (CochainComplex.HomComplex.Cochain.ofHom σ))

/-- Helper for Lemma 13.31.5: postcomposition on cochains is additive. -/
private theorem homComplex_postcomp_map_add
    {K L M : CochainComplex 𝒜 ℤ}
    (σ : L ⟶ M) (n : ℤ)
    (z z' : CochainComplex.HomComplex.Cochain K L n) :
    (z + z').comp (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero n) =
      z.comp (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero n) +
        z'.comp (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero n) := by
  simpa only using
    (CochainComplex.HomComplex.Cochain.add_comp
      (n₁ := n) (n₂ := 0) (n₁₂ := n) (h := add_zero n) z z'
      (CochainComplex.HomComplex.Cochain.ofHom σ))

/-- Helper for Lemma 13.31.5: postcomposition by a morphism of complexes gives an additive
endomorphism on each Hom-complex degree. -/
private def homComplex_postcompAddMonoidHom
    {K L M : CochainComplex 𝒜 ℤ}
    (σ : L ⟶ M) (n : ℤ) :
    CochainComplex.HomComplex.Cochain K L n →+ CochainComplex.HomComplex.Cochain K M n :=
  { toFun := fun z ↦ z.comp (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero n)
    map_zero' := homComplex_postcomp_map_zero σ n
    map_add' := homComplex_postcomp_map_add σ n }

/-- Helper for Lemma 13.31.5: the postcomposition maps on cochains commute with the Hom-complex
differential. -/
private theorem homComplex_postcomp_comm
    {K L M : CochainComplex 𝒜 ℤ}
    (σ : L ⟶ M) (i j : ℤ) (_hij : (ComplexShape.up ℤ).Rel i j) :
    AddCommGrpCat.ofHom (homComplex_postcompAddMonoidHom σ i) ≫
        (CochainComplex.HomComplex K M).d i j =
      (CochainComplex.HomComplex K L).d i j ≫
        AddCommGrpCat.ofHom (homComplex_postcompAddMonoidHom σ j) := by
  -- This is the chain-level compatibility needed for the Hom-complex product cone.
  ext z
  change
    CochainComplex.HomComplex.δ i j
        (z.comp (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero i)) =
      (CochainComplex.HomComplex.δ i j z).comp
        (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero j)
  simpa only using
    (CochainComplex.HomComplex.δ_comp_ofHom (n := i) z σ j)

/-- Helper for Lemma 13.31.5: postcomposition by a morphism of complexes induces a morphism of
Hom-complexes. -/
private def homComplex_postcomp
    {K L M : CochainComplex 𝒜 ℤ}
    (σ : L ⟶ M) :
    CochainComplex.HomComplex K L ⟶ CochainComplex.HomComplex K M :=
  { f := fun n ↦ AddCommGrpCat.ofHom (homComplex_postcompAddMonoidHom σ n)
    comm' := homComplex_postcomp_comm σ }

/-- Helper for Lemma 13.31.5: after evaluating a product cone of complexes in a fixed degree and
applying coyoneda, the resulting cone of types still admits a limiting structure. -/
private theorem evaluated_product_coyoneda_nonempty
    (π : ∀ t, P ⟶ I t)
    (hP : IsLimit (Fan.mk P π))
    (n : ℤ) (X : 𝒜) :
    Nonempty
      (IsLimit
      ((HomologicalComplex.eval 𝒜 (up ℤ) n ⋙ coyoneda.obj (Opposite.op X)).mapCone
        (Fan.mk P π))) := by
  let F := HomologicalComplex.eval 𝒜 (up ℤ) n ⋙ coyoneda.obj (Opposite.op X)
  haveI : F.IsCorepresentable :=
    (HomologicalComplex.evalCompCoyonedaCorepresentable (C := 𝒜) (c := up ℤ) X n).isCorepresentable
  exact ⟨by simpa [F] using isLimitOfPreserves F hP⟩

/-- Helper for Lemma 13.31.5: a product cone of cochain complexes gives products in each
degree. -/
private theorem degreewise_product_isLimit_nonempty
    (π : ∀ t, P ⟶ I t)
    (hP : IsLimit (Fan.mk P π))
    (n : ℤ) :
    Nonempty (IsLimit (Fan.mk (P.X n) fun t ↦ (π t).f n)) := by
  classical
  let c : Fan fun t ↦ (I t).X n := Fan.mk (P.X n) fun t ↦ (π t).f n
  refine ⟨((Limits.Cone.isLimitCoyonedaEquiv c).symm ?_)⟩
  intro X
  let hX := Classical.choice (evaluated_product_coyoneda_nonempty π hP n X.unop)
  -- The coyoneda image of the degreewise fan is the same mapped product cone seen through
  -- evaluation and then `coyoneda`.
  exact
    (Fan.isLimitMapConeEquiv (coyoneda.obj X) (fun t ↦ (I t).X n) c).symm
      ((CategoryTheory.Limits.isLimitMapConeFanMkEquiv
        (HomologicalComplex.eval 𝒜 (up ℤ) n ⋙ coyoneda.obj X) I π) hX)

/-- Helper for Lemma 13.31.5: a chosen degreewise product structure induced by the product cone of
complexes. -/
private noncomputable def degreewise_product_isLimit
    (π : ∀ t, P ⟶ I t)
    (hP : IsLimit (Fan.mk P π))
    (n : ℤ) :
    IsLimit (Fan.mk (P.X n) fun t ↦ (π t).f n) :=
  Classical.choice (degreewise_product_isLimit_nonempty π hP n)

/-- Helper for Lemma 13.31.5: if all projections of a morphism to a product complex are
null-homotopic, then the morphism itself is null-homotopic. -/
private theorem null_homotopy_of_factorwise_null_homotopy
    {K : CochainComplex 𝒜 ℤ}
    (π : ∀ t, P ⟶ I t)
    (hP : IsLimit (Fan.mk P π))
    (f : K ⟶ P)
    (hf : ∀ t, Nonempty (Homotopy (f ≫ π t) 0)) :
    Nonempty (Homotopy f 0) := by
  classical
  let αt : ∀ t, CochainComplex.HomComplex.Cochain K (I t) (-1) := fun t ↦
    ((CochainComplex.HomComplex.Cochain.equivHomotopy (f ≫ π t) 0)
      (Classical.choice (hf t))).1
  have hαt :
      ∀ t,
        CochainComplex.HomComplex.Cochain.ofHom (f ≫ π t) =
          CochainComplex.HomComplex.δ (-1) 0 (αt t) := by
    intro t
    -- Each chosen factorwise homotopy identifies `f ≫ π t` with a coboundary in degree `-1`.
    simpa only [αt, CochainComplex.HomComplex.Cochain.ofHom_zero, add_zero] using
      ((CochainComplex.HomComplex.Cochain.equivHomotopy (f ≫ π t) 0)
        (Classical.choice (hf t))).2
  let α : CochainComplex.HomComplex.Cochain K P (-1) :=
    CochainComplex.HomComplex.Cochain.mk fun p q hpq ↦
      (degreewise_product_isLimit π hP q).lift
        (Fan.mk (K.X p) fun t ↦ (αt t).v p q hpq)
  have hα_fac (t : T) :
      α.comp (CochainComplex.HomComplex.Cochain.ofHom (π t)) (add_zero (-1)) = αt t := by
    ext p q hpq
    -- The assembled cochain has the prescribed factorwise components by the degreewise product
    -- universal property.
    simpa [α] using
      (Fan.IsLimit.fac (degreewise_product_isLimit π hP q)
        (fun s ↦ (αt s).v p q hpq) t)
  have hα_eq :
      CochainComplex.HomComplex.Cochain.ofHom f =
        CochainComplex.HomComplex.δ (-1) 0 α := by
    apply CochainComplex.HomComplex.Cochain.ext₀
    intro p
    -- Equality of degreewise components is checked after composing with every product projection.
    apply Fan.IsLimit.hom_ext (degreewise_product_isLimit π hP p)
    intro t
    have hcomp :
        (CochainComplex.HomComplex.Cochain.ofHom f).comp
            (CochainComplex.HomComplex.Cochain.ofHom (π t)) (add_zero 0) =
          (CochainComplex.HomComplex.δ (-1) 0 α).comp
            (CochainComplex.HomComplex.Cochain.ofHom (π t)) (add_zero 0) := by
      calc
        (CochainComplex.HomComplex.Cochain.ofHom f).comp
            (CochainComplex.HomComplex.Cochain.ofHom (π t)) (add_zero 0) =
          CochainComplex.HomComplex.Cochain.ofHom (f ≫ π t) := by
            simpa only using (CochainComplex.HomComplex.Cochain.ofHom_comp f (π t)).symm
        _ = CochainComplex.HomComplex.δ (-1) 0 (αt t) := hαt t
        _ = CochainComplex.HomComplex.δ (-1) 0
              (α.comp (CochainComplex.HomComplex.Cochain.ofHom (π t)) (add_zero (-1))) := by
            rw [hα_fac t]
        _ = (CochainComplex.HomComplex.δ (-1) 0 α).comp
              (CochainComplex.HomComplex.Cochain.ofHom (π t)) (add_zero 0) := by
            symm
            simpa only using
              (CochainComplex.HomComplex.δ_comp_ofHom (n := -1) α (π t) 0).symm
    have hcomp_v :=
      CochainComplex.HomComplex.Cochain.congr_v hcomp p p (add_zero p)
    simpa using hcomp_v
  -- The assembled `-1`-cochain is exactly the datum of a null-homotopy of `f`.
  refine ⟨(CochainComplex.HomComplex.Cochain.equivHomotopy f 0).symm ?_⟩
  refine ⟨α, ?_⟩
  rw [hα_eq, CochainComplex.HomComplex.Cochain.ofHom_zero, add_zero]

/-- Helper for Lemma 13.31.5: a product cone of complexes induces the corresponding product cone
in the homotopy category. -/
private theorem homotopyCategory_product_existsUnique_of_product_cone
    (π : ∀ t, P ⟶ I t)
    (hP : IsLimit (Fan.mk P π))
    (K : CochainComplex 𝒜 ℤ)
    (u : ∀ t,
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
        (HomotopyCategory.quotient 𝒜 (up ℤ)).obj (I t)) :
    ∃! v : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
        (HomotopyCategory.quotient 𝒜 (up ℤ)).obj P,
      ∀ t, v ≫ (HomotopyCategory.quotient 𝒜 (up ℤ)).map (π t) = u t := by
  classical
  let KQ := HomotopyCategory.quotient 𝒜 (up ℤ)
  let u' : ∀ t, K ⟶ I t := fun t ↦ (KQ.map_surjective (u t)).choose
  have hu' : ∀ t, KQ.map (u' t) = u t := fun t ↦ (KQ.map_surjective (u t)).choose_spec
  let v' : K ⟶ P := hP.lift (Fan.mk K u')
  have hv' : ∀ t, KQ.map v' ≫ KQ.map (π t) = u t := by
    intro t
    -- The chosen lift in complexes already has the correct projections in the homotopy category.
    simpa [v', hu' t, Functor.map_comp] using
      congrArg (fun m ↦ KQ.map m) (Fan.IsLimit.fac hP u' t)
  refine ⟨KQ.map v', hv', ?_⟩
  intro m hm
  obtain ⟨m', hm'⟩ := KQ.map_surjective m
  have hfactor :
      ∀ t, Nonempty (Homotopy ((m' - v') ≫ π t) 0) := by
    intro t
    -- Equality of projections in the homotopy category means each factor of the difference is
    -- null-homotopic.
    apply (HomotopyCategory.quotient_map_eq_zero_iff ((m' - v') ≫ π t)).1
    rw [Functor.map_comp, Functor.map_sub, Preadditive.sub_comp, hm', hm t, hv' t, sub_self]
  have hnull :
      Nonempty (Homotopy (m' - v') 0) :=
    null_homotopy_of_factorwise_null_homotopy π hP (m' - v') hfactor
  have hzero : KQ.map (m' - v') = 0 :=
    (HomotopyCategory.quotient_map_eq_zero_iff (m' - v')).2 hnull
  have hm_eq : KQ.map m' = KQ.map v' := by
    apply sub_eq_zero.mp
    simpa using hzero
  calc
    m = KQ.map m' := hm'.symm
    _ = KQ.map v' := hm_eq

/-- Core product form of Lemma 13.31.5: a product of K-injective cochain complexes is
K-injective. -/
theorem isKInjective_of_product
    (π : ∀ t, P ⟶ I t)
    [∀ t, (I t).IsKInjective]
    (hP : IsLimit (Fan.mk P π)) :
    P.IsKInjective := by
  -- Route correction: instead of a bespoke cone isomorphism, use evaluation to get degreewise
  -- products and then assemble the factorwise null-homotopies into one homotopy on the product.
  refine ⟨fun {K} f hK ↦ ?_⟩
  exact null_homotopy_of_factorwise_null_homotopy π hP f fun t ↦
    CochainComplex.IsKInjective.nonempty_homotopy_zero (f ≫ π t) hK

section

variable [HasDerivedCategory.{w} 𝒜]

/-- Helper for Lemma 13.31.5: conjugating a `Qh`-image along `quotientCompQhIso` recovers the
corresponding `Q`-image. -/
private theorem quotientCompQhIso_homCongr_map
    {K L : CochainComplex 𝒜 ℤ}
    (f : K ⟶ L) :
    (Iso.homCongr ((quotientCompQhIso 𝒜).app K) ((quotientCompQhIso 𝒜).app L))
      (Qh.map ((HomotopyCategory.quotient 𝒜 (up ℤ)).map f)) = Q.map f := by
  -- This is the naturality square for the comparison isomorphism `quotient ⋙ Qh ≅ Q`.
  change
    (quotientCompQhIso 𝒜).inv.app K ≫
        Qh.map ((HomotopyCategory.quotient 𝒜 (up ℤ)).map f) ≫
          (quotientCompQhIso 𝒜).hom.app L =
      Q.map f
  have hnat :
      Qh.map ((HomotopyCategory.quotient 𝒜 (up ℤ)).map f) ≫
          (quotientCompQhIso 𝒜).hom.app L =
        (quotientCompQhIso 𝒜).hom.app K ≫ Q.map f := by
    simpa [Functor.comp_map] using (quotientCompQhIso 𝒜).hom.naturality f
  calc
    (quotientCompQhIso 𝒜).inv.app K ≫
        Qh.map ((HomotopyCategory.quotient 𝒜 (up ℤ)).map f) ≫
          (quotientCompQhIso 𝒜).hom.app L =
      (quotientCompQhIso 𝒜).inv.app K ≫
        ((quotientCompQhIso 𝒜).hom.app K ≫ Q.map f) := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ (quotientCompQhIso 𝒜).inv.app K ≫ k) hnat
    _ = Q.map f := by
          simpa using
            (Iso.inv_hom_id_assoc ((quotientCompQhIso 𝒜).app K) (Q.map f))

-- Proof sketch: use the previous K-injectivity statement together with the characterization of
-- morphisms into a K-injective complex in the derived category, first for source objects of the
-- form `Q.obj K`; the intermediate owner-level statement is existence and uniqueness of the lift
-- to `Q.obj P` against the product fan. The final product cone in `DerivedCategory 𝒜` is then
-- obtained for an arbitrary source object by transporting along `Q.objObjPreimageIso`.
private theorem qObjProduct_existsUnique
    (π : ∀ t, P ⟶ I t)
    [∀ t, (I t).IsKInjective]
    (hP : IsLimit (Fan.mk P π))
    (K : CochainComplex 𝒜 ℤ)
    (f : ∀ t, Q.obj K ⟶ Q.obj (I t)) :
    ∃! g : Q.obj K ⟶ Q.obj P, ∀ t, g ≫ Q.map (π t) = f t := by
  classical
  let KQ := HomotopyCategory.quotient 𝒜 (up ℤ)
  let eP := Iso.homCongr ((quotientCompQhIso 𝒜).app K) ((quotientCompQhIso 𝒜).app P)
  let eI : ∀ t, (Qh.obj (KQ.obj K) ⟶ Qh.obj (KQ.obj (I t))) ≃ (Q.obj K ⟶ Q.obj (I t)) := fun t ↦
    Iso.homCongr ((quotientCompQhIso 𝒜).app K) ((quotientCompQhIso 𝒜).app (I t))
  haveI : P.IsKInjective := isKInjective_of_product π hP
  let u : ∀ t, KQ.obj K ⟶ KQ.obj (I t) := fun t ↦
    ((CochainComplex.IsKInjective.Qh_map_bijective (KQ.obj K) (I t)).surjective
      ((eI t).symm (f t))).choose
  have hu : ∀ t, Qh.map (u t) = (eI t).symm (f t) := by
    intro t
    exact
      ((CochainComplex.IsKInjective.Qh_map_bijective (KQ.obj K) (I t)).surjective
        ((eI t).symm (f t))).choose_spec
  obtain ⟨v, hv, hvuniq⟩ := homotopyCategory_product_existsUnique_of_product_cone π hP K u
  have huQ : ∀ t, eI t (Qh.map (u t)) = f t := by
    intro t
    rw [hu t]
    exact (eI t).apply_symm_apply (f t)
  have htransport (g : KQ.obj K ⟶ KQ.obj P) (t : T) :
      eP (Qh.map g) ≫ Q.map (π t) = eI t (Qh.map (g ≫ KQ.map (π t))) := by
    -- This is the naturality square of `quotientCompQhIso`, written after conjugating the
    -- homotopy-category morphism.
    have hnat :
        (quotientCompQhIso 𝒜).hom.app P ≫ Q.map (π t) =
          Qh.map (KQ.map (π t)) ≫ (quotientCompQhIso 𝒜).hom.app (I t) := by
      simpa [Functor.comp_map] using ((quotientCompQhIso 𝒜).hom.naturality (π t)).symm
    calc
      eP (Qh.map g) ≫ Q.map (π t) =
          (quotientCompQhIso 𝒜).inv.app K ≫ Qh.map g ≫
            (quotientCompQhIso 𝒜).hom.app P ≫ Q.map (π t) := by
              show
                (((quotientCompQhIso 𝒜).app K).inv ≫ Qh.map g ≫ ((quotientCompQhIso 𝒜).app P).hom) ≫
                    Q.map (π t) =
                  (quotientCompQhIso 𝒜).inv.app K ≫ Qh.map g ≫
                    (quotientCompQhIso 𝒜).hom.app P ≫ Q.map (π t)
              simp [Category.assoc]
      _ =
          (quotientCompQhIso 𝒜).inv.app K ≫ Qh.map g ≫
            (Qh.map (KQ.map (π t)) ≫ (quotientCompQhIso 𝒜).hom.app (I t)) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ (quotientCompQhIso 𝒜).inv.app K ≫ Qh.map g ≫ k)
                  hnat
      _ =
          (quotientCompQhIso 𝒜).inv.app K ≫
            (Qh.map g ≫ Qh.map (KQ.map (π t))) ≫ (quotientCompQhIso 𝒜).hom.app (I t) := by
              simp [Category.assoc]
      _ =
          (quotientCompQhIso 𝒜).inv.app K ≫
            Qh.map (g ≫ KQ.map (π t)) ≫ (quotientCompQhIso 𝒜).hom.app (I t) := by
              simp [Functor.map_comp, Category.assoc]
      _ = eI t (Qh.map (g ≫ KQ.map (π t))) := by
            show
              (quotientCompQhIso 𝒜).inv.app K ≫
                  Qh.map (g ≫ KQ.map (π t)) ≫ (quotientCompQhIso 𝒜).hom.app (I t) =
                (((quotientCompQhIso 𝒜).app K).homCongr ((quotientCompQhIso 𝒜).app (I t)))
                  (Qh.map (g ≫ KQ.map (π t)))
            rfl
  refine ⟨eP (Qh.map v), ?_, ?_⟩
  · intro t
    -- The homotopy-category lift transports to the required derived-category projection formula.
    have hvQh : Qh.map (v ≫ KQ.map (π t)) = Qh.map (u t) := by
      simpa [Functor.map_comp] using congrArg (fun m ↦ Qh.map m) (hv t)
    calc
      eP (Qh.map v) ≫ Q.map (π t) =
        eI t (Qh.map (v ≫ KQ.map (π t))) := htransport v t
      _ = eI t (Qh.map (u t)) := by
          rw [hvQh]
      _ = f t := huQ t
  · intro m hm
    obtain ⟨m', hm'⟩ :=
      (CochainComplex.IsKInjective.Qh_map_bijective (KQ.obj K) P).surjective ((eP).symm m)
    have hmQ : eP (Qh.map m') = m := by
      rw [hm']
      exact eP.apply_symm_apply m
    have hm'fac : ∀ t, m' ≫ KQ.map (π t) = u t := by
      intro t
      have hderived :
          eI t (Qh.map (m' ≫ KQ.map (π t))) = eI t (Qh.map (u t)) := by
        calc
          eI t (Qh.map (m' ≫ KQ.map (π t))) =
              eP (Qh.map m') ≫ Q.map (π t) := by
                simpa using (htransport m' t).symm
          _ = m ≫ Q.map (π t) := by rw [hmQ]
          _ = f t := hm t
          _ = eI t (Qh.map (u t)) := by symm; exact huQ t
      have hQh :
          Qh.map (m' ≫ KQ.map (π t)) = Qh.map (u t) :=
        (eI t).injective hderived
      exact (CochainComplex.IsKInjective.Qh_map_bijective (KQ.obj K) (I t)).injective hQh
    have hmv : m' = v := hvuniq _ hm'fac
    calc
      m = eP (Qh.map m') := hmQ.symm
      _ = eP (Qh.map v) := by rw [hmv]

private noncomputable def qObjProductLift
    (π : ∀ t, P ⟶ I t)
    [∀ t, (I t).IsKInjective]
    (hP : IsLimit (Fan.mk P π))
    (K : CochainComplex 𝒜 ℤ)
    (f : ∀ t, Q.obj K ⟶ Q.obj (I t)) :
    Q.obj K ⟶ Q.obj P :=
  Classical.choose (ExistsUnique.exists (qObjProduct_existsUnique π hP K f))

private theorem qObjProductLift_fac
    (π : ∀ t, P ⟶ I t)
    [∀ t, (I t).IsKInjective]
    (hP : IsLimit (Fan.mk P π))
    (K : CochainComplex 𝒜 ℤ)
    (f : ∀ t, Q.obj K ⟶ Q.obj (I t))
    (t : T) :
    qObjProductLift π hP K f ≫ Q.map (π t) = f t :=
  (Classical.choose_spec (ExistsUnique.exists (qObjProduct_existsUnique π hP K f))) t

private theorem qObjProductLift_uniq
    (π : ∀ t, P ⟶ I t)
    [∀ t, (I t).IsKInjective]
    (hP : IsLimit (Fan.mk P π))
    (K : CochainComplex 𝒜 ℤ)
    (f : ∀ t, Q.obj K ⟶ Q.obj (I t))
    (m : Q.obj K ⟶ Q.obj P)
    (hm : ∀ t, m ≫ Q.map (π t) = f t) :
    m = qObjProductLift π hP K f :=
  (qObjProduct_existsUnique π hP K f).unique hm (qObjProductLift_fac π hP K f)

-- Proof sketch: specialize the source-facing product theorem to the canonical product cone
-- `Fan.mk (∏ᶜ I) (Pi.π I)`, build the mapped fan from the private unique-lift API above, and
-- package the result with `preservesLimit_of_preserves_limit_cone`.
/-- The localization functor `DerivedCategory.Q` preserves the product of any family of
K-injective cochain complexes. -/
theorem derivedCategory_Q_preserves_product_of_kInjective
    (I : T → CochainComplex 𝒜 ℤ)
    [HasProduct I]
    [∀ t, (I t).IsKInjective] :
    PreservesLimit (Discrete.functor I) Q := by
  classical
  let π : ∀ t, ∏ᶜ I ⟶ I t := fun t ↦ Pi.π I t
  let hπ : IsLimit (Fan.mk (∏ᶜ I) π) := by
    simpa [π] using productIsProduct I
  let hQ' : IsLimit (Fan.mk (Q.obj (∏ᶜ I)) fun t ↦ Q.map (π t)) := by
    refine mkFanLimit (Fan.mk (Q.obj (∏ᶜ I)) fun t ↦ Q.map (π t)) (fun s ↦ ?_) ?_ ?_
    · let e := Q.objObjPreimageIso s.pt
      exact e.inv ≫ qObjProductLift π hπ (Q.objPreimage s.pt) (fun t ↦ e.hom ≫ s.proj t)
    · intro s t
      let e := Q.objObjPreimageIso s.pt
      simpa [Category.assoc] using
        congrArg (fun k ↦ e.inv ≫ k)
          (qObjProductLift_fac π hπ (Q.objPreimage s.pt) (fun j ↦ e.hom ≫ s.proj j) t)
    · intro s m hm
      let e := Q.objObjPreimageIso s.pt
      have hm' :
          e.hom ≫ m =
            qObjProductLift π hπ (Q.objPreimage s.pt) (fun t ↦ e.hom ≫ s.proj t) :=
        qObjProductLift_uniq π hπ (Q.objPreimage s.pt) (fun t ↦ e.hom ≫ s.proj t) (e.hom ≫ m)
          fun t ↦ by
            simpa [Category.assoc] using congrArg (fun k ↦ e.hom ≫ k) (hm t)
      simpa [Category.assoc] using congrArg (fun k ↦ e.inv ≫ k) hm'
  let hQ : IsLimit (Q.mapCone (Fan.mk (∏ᶜ I) π)) :=
    (isLimitMapConeFanMkEquiv Q I π).symm hQ'
  exact preservesLimit_of_preserves_limit_cone hπ hQ

/-- Lemma 13.31.5: if the termwise product of a family of K-injective cochain complexes exists,
then the product complex is K-injective, and its image in the derived category represents the
product of the family. -/
theorem product_of_kInjective_isKInjective_and_preserves_limit
    (I : T → CochainComplex 𝒜 ℤ)
    [HasProduct I]
    [∀ t, (I t).IsKInjective] :
    (∏ᶜ I).IsKInjective ∧ PreservesLimit (Discrete.functor I) Q := by
  let π : ∀ t, ∏ᶜ I ⟶ I t := fun t ↦ Pi.π I t
  have hπ : IsLimit (Fan.mk (∏ᶜ I) π) := by
    simpa [π] using productIsProduct I
  constructor
  · exact isKInjective_of_product π hπ
  · exact derivedCategory_Q_preserves_product_of_kInjective I

end

end

end CategoryTheory

/-! ### Lemma_13_31_6 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

universe v₁ v₂ u₁ u₂

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒜] [Abelian 𝒜]
  [Category.{v₂} 𝒟']

/- Domain-style sampling for Lemma 13.31.6:
- primary domain: pointwise right derived functors on the homotopy category `K(\mathcal A)`,
  computed on K-injective complexes and transported along quasi-isomorphisms;
- sampled owner declarations:
  `Functor.ComputesRightDerivedAt`,
  `Functor.HasPointwiseRightDerivedFunctorAt`,
  `Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem`,
  `DerivedCategory.Qh`,
  `CochainComplex.IsKInjective.Qh_map_bijective`;
- best owner abstractions:
  `source-facing`: the statement that a K-injective complex computes the right derived functor;
  `core/canonical`: `Functor.ComputesRightDerivedAt` and the transport owner
    `Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem`;
  `bridge/view`: the downstream use of the canonical transport theorem for objects
    quasi-isomorphic to a K-injective one.
- primitive data: the functor `F` and the K-injective complex `I`.
- derived API: downstream pointwise-definedness statements are obtained by transporting the
  computation theorem at `(HomotopyCategory.quotient 𝒜 (up ℤ)).obj I` along a quasi-isomorphism
  using `Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem`.

The main owner-level theorem here is therefore the computation statement at a K-injective object.
The pointwise-existence statement for an arbitrary quasi-isomorphic object should therefore be
handled downstream by the canonical transport API, not by a separate local wrapper theorem.
-/

variable (F : HomotopyCategory 𝒜 (up ℤ) ⥤ 𝒟')

local notation "KQ" => HomotopyCategory.quotient 𝒜 (up ℤ)
local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)

-- Proof sketch: `IsKInjective.Qh_map_bijective` says every arrow into a K-injective complex is
-- uniquely determined by its image in the derived category. Applied to the costructured-arrow
-- category over `DerivedCategory.Qh.obj ((KQ).obj I)`, this makes the identity denominator
-- terminal, so the
-- pointwise right derived value is just `F.obj ((KQ).obj I)` and the canonical unit is an
-- isomorphism.
/-- Lemma 13.31.6: every K-injective complex computes the right derived functor of
`F : K(\mathcal A) ⥤ \mathcal D'` with respect to quasi-isomorphisms. -/
theorem kInjective_computesRightDerivedFunctorAt
    (I : CochainComplex 𝒜 ℤ) [I.IsKInjective] :
    F.ComputesRightDerivedAt Qis ((KQ).obj I) := by
  sorry

end

end CategoryTheory

/-! ### Lemma_13_31_7 (from Chap13) -/
open ComplexShape

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} 𝒟']
  [Abelian 𝒜]

local notation "KHom" => HomotopyCategory 𝒜 (up ℤ)
local notation "W" => HomotopyCategory.quasiIso 𝒜 (up ℤ)

/- Domain-style sampling for Lemma 13.31.7:
- primary domain: right derived functors on the unbounded homotopy category `K(\mathcal A)`,
  obtained from K-injective replacements;
- sampled owner declarations:
  `kInjective_computesRightDerivedFunctorAt`,
  `Functor.hasPointwiseRightDerivedFunctor_of_exists_computesRightDerivedAt`,
  `Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor`,
  `Functor.ComputesRightDerivedAt`,
  `Functor.HasPointwiseRightDerivedFunctor`;
- best owner abstractions:
  `source-facing`: the existence of right derived functors on `K(\mathcal A)` under
    K-injective replacements;
  `core/canonical`: `Functor.ComputesRightDerivedAt`,
    `Functor.HasPointwiseRightDerivedFunctor`, the Chapter `13` owner bridge
    `Functor.hasPointwiseRightDerivedFunctor_of_exists_computesRightDerivedAt`, and the
    globalization owner theorem `Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor`;
  `bridge/view`: the K-injective computation theorem
    `kInjective_computesRightDerivedFunctorAt`, which supplies the pointwise computation input
    required by the Chapter `13` existence bridge.
- primitive data: the functor `F` and, for each cochain complex `K`, a quasi-isomorphism
  `K ⟶ I` to a K-injective complex `I`;
- derived API: first pointwise right-derived existence for `F`, obtained from the K-injective
  replacements via `kInjective_computesRightDerivedFunctorAt` and
  `Functor.hasPointwiseRightDerivedFunctor_of_exists_computesRightDerivedAt`, and then global
  right-derived existence via
  `Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor`.

This file should therefore keep only the global existence statement as its source-facing API and
reuse the existing owner path for K-injective computation, pointwise existence, and global
existence, rather than rebuilding the costructured-arrow localization argument locally.
-/ 
/-- Lemma 13.31.7: if every cochain complex in an abelian category admits a quasi-isomorphism to
a K-injective complex, then any functor `K(\mathcal A) ⥤ \mathcal D'` has a right derived
functor with respect to quasi-isomorphisms. The statement is organized around the canonical owner
predicates `Functor.HasPointwiseRightDerivedFunctor` and `Functor.HasRightDerivedFunctor`, with the
K-injective replacement hypothesis supplying the source-facing existence data. -/
theorem hasRightDerivedFunctor_of_kInjective_resolutions
    (F : KHom ⥤ 𝒟')
    (hKI :
      ∀ K : CochainComplex 𝒜 ℤ,
        ∃ (I : CochainComplex 𝒜 ℤ) (_ : I.IsKInjective) (s : K ⟶ I), QuasiIso s) :
    F.HasRightDerivedFunctor W := sorry

end

end CategoryTheory

/-! ### Lemma_13_31_8 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open Opposite

universe v u

namespace CategoryTheory

namespace SequentialInverseSystem

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Lemma 13.31.8 in the homological-complex / sequential-limit domain:
- sampled owner declarations:
  * `CochainComplex.IsKInjective`
  * `CategoryTheory.isKInjective_of_product`
  * `HomologicalComplex.isLimitConeOfHasLimitEval`
  * `SequentialInverseSystem.transitionMap`
- best owner abstractions:
  * `CochainComplex.IsKInjective` for the target property on the inverse-limit complex
  * `SequentialInverseSystem` for the sequential tower itself, with `transitionMap` as derived API
- primitive data:
  * the sequential inverse system `I`
  * termwise split-epimorphism hypotheses on the successor transition maps
  * degreewise existence of limits, which canonically induces `HasLimit I` via
    `HomologicalComplex.isLimitConeOfHasLimitEval`
- derived API:
  * the owner instances `∀ n : ℕ, (I.obj (op n)).IsKInjective`
- source/core/bridge triage:
  * `source-facing`: the K-injectivity statement for the inverse-limit complex
  * `core/canonical`: `CochainComplex.IsKInjective`, the chapter product theorem
    `isKInjective_of_product`, and the homological-complex limit owner
  * `bridge/view`: `SequentialInverseSystem.transitionMap`, which replaces the raw
    `I.map ((homOfLE _).op)` spelling

This item should therefore keep the source-facing limit theorem, but express the tower through the
chapter owner `SequentialInverseSystem` and its derived `transitionMap` API rather than by a
parallel coordinate-level map expression. -/

/-- Lemma 13.31.8: for a sequential inverse system of K-injective cochain complexes in an abelian
category, if every successor transition map is termwise split epic and each degreewise
inverse limit exists, then the inverse-limit complex is K-injective. -/
-- Proof sketch: identify the inverse limit degreewise with the kernel of the Milnor difference
-- map on the product of the tower, use `isKInjective_of_product` for the two product complexes,
-- and then apply `CochainComplex.isKInjective_obj₁_of_distinguished_triangle` to the
-- distinguished triangle coming from the resulting degreewise split short exact sequence.
theorem isKInjective_limit_of_termwiseSplitEpi
    (I : SequentialInverseSystem (CochainComplex 𝒜 ℤ))
    [∀ n : ℕ, (I.obj (op n)).IsKInjective]
    [∀ m : ℤ, HasLimit (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) m)]
    (hTermwiseSplitEpi : ∀ n : ℕ, ∀ m : ℤ, IsSplitEpi ((I.transitionMap (Nat.le_succ n)).f m)) :
    (limit I).IsKInjective := sorry

end

end SequentialInverseSystem

end CategoryTheory

/-! ### Lemma_13_31_9 (from Chap13) -/
open CategoryTheory
open ComplexShape
open CochainComplex
open HomologicalComplex

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

noncomputable section

section

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜]
variable {ℬ : Type u₂} [Category.{v₂} ℬ] [Abelian ℬ]

-- Domain-style sampling:
-- * primary domain: K-injective cochain complexes and their behavior under exact additive
--   functors between abelian categories.
-- * inspected owner declarations:
--   `CochainComplex.IsKInjective`,
--   `CochainComplex.IsKInjective.rightOrthogonal`,
--   `CochainComplex.IsKInjective.homotopyZero`,
--   `Adjunction.homotopy_mapHomologicalComplex_homEquiv`,
--   `Functor.mapHomologicalComplex`,
--   `Adjunction.mapHomologicalComplex`.
-- * layer: `source-facing`; the statement is genuinely about preservation of K-injectivity under a
--   right adjoint, not about introducing a new wrapper around complexes.
-- * core/canonical owner abstraction: `I.IsKInjective` for the mapped complex
--   `((u.mapHomologicalComplex (up ℤ)).obj I)`.
-- * primitive data: the adjunction `v ⊣ u` and exactness of `v`; additivity is derived from
--   these owner hypotheses and should not remain as redundant public input.
-- * derived API: K-injectivity of the image of `I` under `u.mapHomologicalComplex`.

private theorem mapHomologicalComplex_acyclic_of_exact
    (v : ℬ ⥤ 𝒜) (hv : exactFunctor ℬ 𝒜 v)
    (M : CochainComplex ℬ ℤ) (hM : M.Acyclic) :
    by
      letI : v.Additive := (exactFunctor_le_additiveFunctor ℬ 𝒜) v hv
      exact ((v.mapHomologicalComplex (up ℤ)).obj M).Acyclic := by
  letI : v.Additive := (exactFunctor_le_additiveFunctor ℬ 𝒜) v hv
  let hExact := (exactFunctor_iff v).1 hv
  letI : Limits.PreservesFiniteLimits v := hExact.1
  letI : Limits.PreservesFiniteColimits v := hExact.2
  letI : v.PreservesHomology := inferInstance
  rw [HomologicalComplex.acyclic_iff] at hM ⊢
  intro n
  rw [HomologicalComplex.exactAt_iff]
  have hMn : (M.sc n).Exact := by
    simpa [HomologicalComplex.exactAt_iff] using hM n
  simpa [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor] using
    hMn.map v

-- Proof sketch: let `M` be an acyclic complex of `ℬ`. Exactness of the left adjoint `v` sends
-- `M` to an acyclic complex of `𝒜`. The adjunction `v ⊣ u` induces an identification
-- `Hom_K(v(M), I) ≃ Hom_K(M, u(I))`, and the left-hand side vanishes because `I` is
-- K-injective.
/-- Lemma 13.31.9: if `u : \mathcal A ⥤ \mathcal B` is right adjoint to an exact functor
`v : \mathcal B ⥤ \mathcal A`, then the image of a K-injective cochain complex under `u`
is again K-injective. In abelian categories, the needed additivity of `u` and `v` is derived
internally from exactness and the adjunction. -/
theorem right_adjoint_preserves_isKInjective_of_exact_left_adjoint
    (u : 𝒜 ⥤ ℬ) (v : ℬ ⥤ 𝒜) (adj : v ⊣ u) (hv : exactFunctor ℬ 𝒜 v)
    (I : CochainComplex 𝒜 ℤ) [I.IsKInjective] :
    by
      letI : v.Additive := (exactFunctor_le_additiveFunctor ℬ 𝒜) v hv
      letI : u.Additive := adj.right_adjoint_additive
      exact CochainComplex.IsKInjective ((u.mapHomologicalComplex (up ℤ)).obj I) := by
  letI : v.Additive := (exactFunctor_le_additiveFunctor ℬ 𝒜) v hv
  letI : u.Additive := adj.right_adjoint_additive
  let uC := u.mapHomologicalComplex (up ℤ)
  let vC := v.mapHomologicalComplex (up ℤ)
  let adjC := adj.mapHomologicalComplex (up ℤ)
  refine ⟨fun {M} f hM ↦ ?_⟩
  let f' := (adjC.homEquiv M I).symm f
  have hM' : (vC.obj M).Acyclic :=
    mapHomologicalComplex_acyclic_of_exact v hv M hM
  refine ⟨?_⟩
  simpa [uC, vC, adjC, f'] using
    adj.homotopy_mapHomologicalComplex_homEquiv (up ℤ) (IsKInjective.homotopyZero f' hM')

end

end

end CategoryTheory
