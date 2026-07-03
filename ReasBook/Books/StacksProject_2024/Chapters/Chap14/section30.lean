import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_14_30_1 (from Chap14) -/
open CategoryTheory Opposite Simplicial
open SSet.modelCategoryQuillen

universe u

variable {X Y : SSet.{u}} (f : X ⟶ Y)

/- Domain-style sampling for Definition 14.30.1:
- primary domain: simplicial-set lifting properties in the Quillen model structure.
- inspected owner declarations:
  `SSet.modelCategoryQuillen.I`,
  `CategoryTheory.MorphismProperty.rlp`,
  `SSet.modelCategoryQuillen.fibration_iff`,
  `HomotopicalAlgebra.Fibration`.
- owner abstraction: `SSet.modelCategoryQuillen.I.rlp`.
- primitive data: the right lifting property against the boundary inclusions `∂Δ[n].ι`.
- derived API: the textbook split into surjectivity on `0`-simplices and positive-dimensional
  boundary filling.

Source/core/bridge triage:
- `source-facing`: the textbook split into degree-zero surjectivity and positive-dimensional
  boundary filling;
- `core/canonical`: `I.rlp`;
- `bridge/view`: thin source-facing consequences and reconstruction lemmas relating the textbook
  split description to `I.rlp`.

This item should therefore expose `I.rlp` as the main owner and keep the textbook formulation only
through thin companion theorems, rather than a large conjunction-shaped wrapper. -/

/- Definition 14.30.1: a map of simplicial sets is a trivial Kan fibration precisely when it has
the right lifting property with respect to the boundary inclusions `∂Δ[n].ι`, i.e. when it
belongs to `SSet.modelCategoryQuillen.I.rlp`. -/
#check (I.rlp f : Prop)

/-- Every morphism in `I.rlp` lifts against each boundary inclusion `∂Δ[n].ι`. -/
theorem boundaryInclusions_rlp_hasLiftingProperty (n : ℕ) (hf : I.rlp f) :
    HasLiftingProperty (∂Δ[n].ι) f :=
  hf _ (boundary_ι_mem_I n)

/-- Bridge/view companion to Definition 14.30.1: a morphism in `I.rlp` is surjective on
`0`-simplices. This is the source-facing reformulation of lifting against `∂Δ[0].ι`. -/
theorem boundaryInclusions_rlp_zero_surjective
    (hf : I.rlp f) :
    Function.Surjective (f.app (op ⦋0⦌)) := sorry

/-- Source-facing reconstruction of `I.rlp` from surjectivity on `0`-simplices and fillers for
all positive-dimensional boundaries. -/
theorem boundaryInclusions_rlp_of_zero_surjective_and_boundary_lifting
    (h0 : Function.Surjective (f.app (op ⦋0⦌)))
    (hboundary : ∀ n : ℕ, HasLiftingProperty (∂Δ[n + 1].ι) f) :
    I.rlp f := sorry

/-- Bundled source-facing restatement of Definition 14.30.1. The owner-level predicate `I.rlp f`
is equivalent to the textbook split into surjectivity on `0`-simplices and fillers for all
positive-dimensional boundaries. -/
theorem boundaryInclusions_rlp_iff_zero_surjective_and_boundary_lifting :
    I.rlp f ↔
      Function.Surjective (f.app (op ⦋0⦌)) ∧
        ∀ n : ℕ, HasLiftingProperty (∂Δ[n + 1].ι) f := sorry

/- Companion recall: every isomorphism of simplicial sets has the boundary-inclusion right lifting
property, via the canonical owner theorem `I.rlp_of_isIso`. -/
#check I.rlp_of_isIso

/-! ### Lemma_14_30_2 (from Chap14) -/
open CategoryTheory MorphismProperty
open SSet.modelCategoryQuillen

universe u

section

variable {X Y : SSet.{u}} {f : X ⟶ Y}

/- Domain-style sampling for Lemma 14.30.2:
- primary domain: simplicial-set lifting properties and monomorphisms in the Quillen model
  structure;
- sampled owner declarations:
  `SSet.modelCategoryQuillen.I.rlp`,
  `CategoryTheory.MorphismProperty.monomorphisms`,
  `CategoryTheory.MorphismProperty.rlp`,
  `CategoryTheory.HasLiftingProperty`;
- best owner abstraction: `(monomorphisms SSet).rlp`;
- primitive data: the morphism `f` together with the owner property `I.rlp f` from
  Definition 14.30.1;
- derived API: the pointwise lifting statement `HasLiftingProperty i f` for a chosen monomorphism
  `i`.

Source/core/bridge triage:
- `source-facing`: a trivial Kan fibration lifts against every monomorphism of simplicial sets;
- `core/canonical`: `(monomorphisms SSet).rlp f`;
- `bridge/view`: evaluation of that owner property on a particular monomorphism `i`. -/

-- Proof sketch: reinterpret a trivial Kan fibration via
-- `I.rlp`, identify termwise injective maps of
-- simplicial sets with monomorphisms, and then use the standard closure argument to upgrade the
-- owner property from the generating boundary inclusions to all monomorphisms.
/-- Lemma 14.30.2: a trivial Kan fibration of simplicial sets has the right lifting property with
respect to any monomorphism of simplicial sets, i.e. canonically with respect to any termwise
injective map. -/
theorem boundaryInclusions_rlp_monomorphisms (hf : I.rlp f) :
    (monomorphisms SSet).rlp f := sorry

/-- Companion owner-level reformulation of Lemma 14.30.2: for simplicial sets, lifting against the
boundary inclusions is equivalent to lifting against all monomorphisms. The forward implication is
the source-facing content of the lemma; the reverse implication is the generic monotonicity of
`MorphismProperty.rlp` applied to `I_le_monomorphisms`. -/
theorem boundaryInclusions_rlp_iff_monomorphisms_rlp :
    I.rlp f ↔ (monomorphisms SSet).rlp f :=
  ⟨boundaryInclusions_rlp_monomorphisms,
    fun hmono ↦
      (show (monomorphisms SSet).rlp ≤ I.rlp from antitone_rlp I_le_monomorphisms) f hmono⟩

end

/-! ### Lemma_14_30_3 (from Chap14) -/
open CategoryTheory Limits MorphismProperty
open SSet.modelCategoryQuillen

universe u

section

variable {X Y Y' : SSet.{u}}
variable {f : X ⟶ Y} {g : Y' ⟶ Y}

/-
Domain-style sampling for Lemma 14.30.3:
- primary domain: lifting properties of simplicial-set morphisms under pullback.
- inspected owner declarations:
  `SSet.modelCategoryQuillen.I.rlp`,
  `CategoryTheory.MorphismProperty.pullback_snd`,
  `MorphismProperty.rlp_isStableUnderBaseChange`.
- best owner abstraction: the morphism property `SSet.modelCategoryQuillen.I.rlp`;
  the relevant canonical derived theorem is `CategoryTheory.MorphismProperty.pullback_snd`,
  specialized here as `I.rlp.pullback_snd`.
- primitive-vs-derived split:
  primitive data: the morphisms `f`, `g`, and the owner property `I.rlp f`.
  derived API: the textbook statement that a trivial Kan fibration stays trivial after pullback;
  the specialized consequence `I.rlp (pullback.snd f g)` is derived by the canonical owner theorem
  `MorphismProperty.pullback_snd`,
  and the pullback existence needed for `pullback.snd f g` is already supplied canonically in
  `SSet`. -/

/- Source/core/bridge triage for Lemma 14.30.3:
- source-facing: trivial Kan fibrations of simplicial sets.
- core/canonical: the owner property `I.rlp` together with its canonical base-change theorem
  `I.rlp.pullback_snd`.
- bridge/view: the source wording "trivial Kan fibration" for the owner-level property `I.rlp`.

This item adds no simplicial-specific data beyond the owner property `I.rlp`, and mathlib already
provides the exact base-change theorem for that owner. The correct refinement is therefore direct
canonical use of `I.rlp.pullback_snd f g`, rather than a renamed local theorem shell. -/

/- Lemma 14.30.3: for a trivial Kan fibration `f : X ⟶ Y` of simplicial sets and any morphism
`g : Y' ⟶ Y`, the pullback projection `X ×[Y] Y' ⟶ Y'` is again a trivial Kan fibration.
Canonically, this is `I.rlp.pullback_snd f g`, the owner-prefixed specialization of the generic
base-change theorem to the boundary-inclusion right lifting
property `I.rlp`. -/
recall MorphismProperty.pullback_snd

#check (I.rlp.pullback_snd f g : I.rlp f → I.rlp (pullback.snd f g))

end

/-! ### Lemma_14_30_4 (from Chap14) -/
open CategoryTheory
open SSet.modelCategoryQuillen

universe u

variable {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}

/- Domain-style sampling for Lemma 14.30.4:
- primary domain: simplicial-set lifting properties in the Quillen model structure;
- sampled owner declarations:
  `SSet.modelCategoryQuillen.I`,
  `CategoryTheory.MorphismProperty.rlp`,
  `CategoryTheory.MorphismProperty.comp_mem`,
  `MorphismProperty.comp_mem`;
- best owner abstraction: `I.rlp`;
- primitive-vs-derived split:
  primitive data: only the morphisms `f`, `g` together with the owner-property proofs
    `I.rlp f` and `I.rlp g`;
  derived API: closure of that owner property under composition via the canonical owner theorem
    `MorphismProperty.comp_mem I.rlp f g`.

Source/core/bridge triage:
- `source-facing`: the statement that a composite of trivial Kan fibrations is again a trivial Kan
  fibration;
- `core/canonical`: `MorphismProperty.comp_mem I.rlp f g`;
- `bridge/view`: the textbook phrase “trivial Kan fibration” for the owner-level predicate `I.rlp`.

This item introduces no simplicial-specific primitive data beyond `I.rlp`, so the correct
refinement is to reuse the canonical composition theorem directly rather than keep a parallel
chapter-local lemma. -/

/- Lemma 14.30.4: the composition of two trivial Kan fibrations is again a trivial Kan fibration.
Canonically, this is the specialization `MorphismProperty.comp_mem I.rlp f g` of the generic owner
theorem `CategoryTheory.MorphismProperty.comp_mem`. -/
recall MorphismProperty.comp_mem

#check (MorphismProperty.comp_mem I.rlp f g : I.rlp f → I.rlp g → I.rlp (f ≫ g))

/-! ### Lemma_14_30_5 (from Chap14) -/
open CategoryTheory Limits Opposite
open SSet.modelCategoryQuillen

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

private theorem limitProjection_ofSequence_hasLiftingProperty
    {X : ℕ → C} (f : ∀ n : ℕ, X (n + 1) ⟶ X n)
    [HasLimit (Functor.ofOpSequence f)] {A B : C} (g : A ⟶ B)
    (hf : ∀ n : ℕ, HasLiftingProperty g (f n)) :
    HasLiftingProperty g (limit.π (Functor.ofOpSequence f) (op 0)) := by
  let F := Functor.ofOpSequence f
  refine ⟨fun {u v} sq ↦ ?_⟩
  let successorSq (n : ℕ) (prev : B ⟶ X n)
      (hprev : u ≫ limit.π F (op n) = g ≫ prev) :
      CommSq (u ≫ limit.π F (op (n + 1))) g (f n) prev := by
    have hπ :
        limit.π F (op (n + 1)) ≫ f n = limit.π F (op n) := by
      simpa [F] using limit.w F (homOfLE (Nat.le_add_right n 1)).op
    have hsucc :
        u ≫ limit.π F (op (n + 1)) ≫ f n = u ≫ limit.π F (op n) := by
      exact congrArg (fun k ↦ u ≫ k) hπ
    exact CommSq.mk (by simpa [Category.assoc] using hsucc.trans hprev)
  let stage₀ : { l : B ⟶ X 0 // u ≫ limit.π F (op 0) = g ≫ l } :=
    ⟨v, sq.w⟩
  let succStage (n : ℕ)
      (prev : { l : B ⟶ X n // u ≫ limit.π F (op n) = g ≫ l }) :
      { l : B ⟶ X (n + 1) // u ≫ limit.π F (op (n + 1)) = g ≫ l } := by
    let hsq := successorSq n prev.1 prev.2
    let _ : hsq.HasLift := (hf n).sq_hasLift hsq
    exact ⟨hsq.lift, (CommSq.fac_left hsq).symm⟩
  have succStage_w (n : ℕ)
      (prev : { l : B ⟶ X n // u ≫ limit.π F (op n) = g ≫ l }) :
      prev.1 = (succStage n prev).1 ≫ f n := by
    let hsq := successorSq n prev.1 prev.2
    let _ : hsq.HasLift := (hf n).sq_hasLift hsq
    simpa only [succStage] using (CommSq.fac_right hsq).symm
  let stage : (n : ℕ) → { l : B ⟶ X n // u ≫ limit.π F (op n) = g ≫ l } :=
    Nat.rec stage₀ (fun n prev ↦ succStage n prev)
  let c : Cone F := {
    pt := B
    π := NatTrans.ofOpSequence (fun n ↦ (stage n).1) (fun n ↦ by
      simpa [stage, F] using succStage_w n (stage n))
  }
  refine CommSq.HasLift.mk' ?_
  refine ⟨limit.lift F c, ?_, ?_⟩
  · apply limit.hom_ext
    intro n
    rw [Category.assoc, limit.lift_π]
    simpa [c] using (stage n.unop).2.symm
  · rw [limit.lift_π]
    rfl

namespace MorphismProperty

/-- The projection from the inverse limit of a countable tower of morphisms in `T.rlp` again lies
in `T.rlp`. -/
theorem rlp_limitProjection_ofSequence (T : MorphismProperty C)
    {X : ℕ → C} (f : ∀ n : ℕ, X (n + 1) ⟶ X n)
    [HasLimit (Functor.ofOpSequence f)] (hf : ∀ n : ℕ, T.rlp (f n)) :
    T.rlp (limit.π (Functor.ofOpSequence f) (Opposite.op 0)) :=
  fun _ _ g hg ↦ limitProjection_ofSequence_hasLiftingProperty f g (fun n ↦ hf n g hg)

end MorphismProperty

end CategoryTheory

variable {X : ℕ → SSet.{u}} (f : ∀ n : ℕ, X (n + 1) ⟶ X n)

/- Domain-style sampling for Lemma 14.30.5:
- primary domain: lifting properties of inverse-limit projections for sequential diagrams,
  specialized to simplicial sets.
- inspected owner declarations:
  `CategoryTheory.MorphismProperty.rlp`,
  `CategoryTheory.MorphismProperty.rlp_limitProjection_ofSequence`,
  `CategoryTheory.Functor.ofOpSequence`,
  `boundaryInclusions_rlp_hasLiftingProperty`.
- best owner abstraction: the morphism-property theorem
  `CategoryTheory.MorphismProperty.rlp_limitProjection_ofSequence`, specialized here to the
  Chapter 14 owner property `I.rlp`.
- primitive-vs-derived split:
  primitive data: the inverse sequence `f` and the stagewise owner property `I.rlp (f n)`;
  derived API: the source-facing specialized interface for trivial Kan fibrations.

Source/core/bridge triage:
- `source-facing`: the textbook statement about inverse limits of trivial Kan fibrations.
- `core/canonical`: the owner theorem
  `CategoryTheory.MorphismProperty.rlp_limitProjection_ofSequence`.
- `bridge/view`: Definition 14.30.1, which identifies the textbook notion with `I.rlp`. -/

/- Lemma 14.30.5: for a countable inverse sequence of trivial Kan fibrations of simplicial sets,
equivalently of morphisms having the right lifting property with respect to all boundary
inclusions, the canonical projection from the inverse limit to the initial term again has that
right lifting property. In the refined API this source-facing statement is used directly as the
owner specialization `I.rlp_limitProjection_ofSequence f`. -/
#check (I.rlp_limitProjection_ofSequence f :
  ∀ [HasLimit (Functor.ofOpSequence f)],
    (∀ n : ℕ, I.rlp (f n)) → I.rlp (limit.π (Functor.ofOpSequence f) (Opposite.op 0)))

/-! ### Lemma_14_30_6 (from Chap14) -/
open CategoryTheory Limits
open SSet.modelCategoryQuillen

universe w u

section

variable {J : Type w} {X Y : J → SSet.{u}}
variable [HasProduct X] [HasProduct Y]

/-
Domain-style sampling for Lemma 14.30.6:
- primary domain: lifting properties of simplicial-set morphisms under products.
- inspected owner declarations:
  `SSet.modelCategoryQuillen.I.rlp`,
  `CategoryTheory.HasLiftingProperty`,
  `CategoryTheory.MorphismProperty.limMap`,
  `CategoryTheory.MorphismProperty.rlp_isStableUnderProductsOfShape`.
- best owner abstraction: `I.rlp`.
- primitive-vs-derived split:
  primitive data: the family `f` and the componentwise owner property `I.rlp (f j)`.
  derived API: the source-facing product conclusion `I.rlp (Limits.Pi.map f)`. -/

/- Source/core/bridge triage for Lemma 14.30.6:
- source-facing: products of trivial Kan fibrations of simplicial sets.
- core/canonical: `MorphismProperty.limMap`, specialized to the owner morphism property `I.rlp`.
- bridge/view: the textbook phrase "trivial Kan fibration" for the owner-level property
  `I.rlp`. -/

/- Lemma 14.30.6: a family of trivial Kan fibrations of simplicial sets has product map again a
trivial Kan fibration. Since Definition 14.30.1 already identifies “trivial Kan fibration” with
the owner property `I.rlp`, this source-facing statement is a thin bridge from the canonical owner
theorem `MorphismProperty.limMap`, whose native interface is formulated on the corresponding
natural transformation in the discrete functor category. -/
theorem boundaryInclusions_rlp_piMap (f : ∀ j, X j ⟶ Y j) (hf : ∀ j, I.rlp (f j)) :
    I.rlp (Limits.Pi.map f) := by
  exact MorphismProperty.limMap _ (fun ⟨j⟩ ↦ hf j)

end

/-! ### Lemma_14_30_7 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Arrow
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open Simplicial
open SSet.modelCategoryQuillen

universe u v₁ v₂

attribute [local instance] Cardinal.fact_isRegular_aleph0

section

/-
Domain-style sampling for Lemma 14.30.7:
- primary domain: filtered colimits of simplicial-set morphisms carrying a right lifting property;
- inspected owner declarations:
  `SSet.modelCategoryQuillen.I.rlp`,
  `CategoryTheory.MorphismProperty.IsStableUnderFilteredColimits`,
  `CategoryTheory.MorphismProperty.colimitsOfShape.mk'`,
  `CategoryTheory.MorphismProperty.colimitsOfShape_le`,
  `CategoryTheory.Arrow.preservesColimitsOfShape_leftFunc`,
  `CategoryTheory.Arrow.preservesColimitsOfShape_rightFunc`.
- best owner abstraction: the morphism property `I.rlp`;
- primitive-vs-derived split:
  primitive data: an arbitrary filtered arrow diagram `F` and the stagewise owner property
    `I.rlp ((F.obj j).hom)`;
  derived API: the cocone-point conclusion for an arbitrary colimit cocone in `Arrow SSet`.

Source/core/bridge triage:
- `source-facing`: filtered colimits of trivial Kan fibrations of simplicial sets;
- `core/canonical`: the owner property `I.rlp`;
- `bridge/view`: the cocone-point theorem below. -/

-- Proof sketch: rewrite trivial Kan fibrations as the morphisms in `I.rlp`, i.e. the maps with
-- the right lifting property against all boundary inclusions. Filtered colimits in `SSet` are
-- computed degreewise in `Type`, and filtered colimits of sets commute with the finite limits that
-- describe the simplices of boundaries, so any compatible family of stagewise lifts produces a
-- lift for the colimit arrow.
/-- Helper for Lemma 14.30.7: every simplicial boundary is finitely presentable. -/
lemma boundary_isFinitelyPresentable (n : ℕ) :
    IsFinitelyPresentable.{u} (∂Δ[n] : SSet.{u}) := by
  infer_instance

/-- Helper for Lemma 14.30.7: every standard simplex is finitely presentable. -/
lemma simplex_isFinitelyPresentable (n : ℕ) :
    IsFinitelyPresentable.{u} (Δ[n] : SSet.{u}) := by
  infer_instance

/-- Helper for Lemma 14.30.7: a standard simplex is finitely presentable at the larger universe
needed for the filtered small-model descent. -/
lemma simplex_isFinitelyPresentable_large (n : ℕ) :
    IsFinitelyPresentable.{max u v₁ v₂} (Δ[n] : SSet.{u}) := by
  -- View `Δ[n]` through the lifted Yoneda embedding so the evaluation functor computes the
  -- relevant hom-sets in a universe where the filtered colimit shape is allowed.
  change IsCardinalPresentable.{max u v₁ v₂} (Δ[n] : SSet.{u}) Cardinal.aleph0
  rw [isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj.{max v₁ v₂}]
  constructor
  intro J _ _
  let e :
      uliftCoyoneda.{max v₁ v₂}.obj (op (Δ[n] : SSet.{u})) ≅
        (evaluation _ (Type u)).obj (op (SimplexCategory.mk n)) ⋙
          uliftFunctor.{max v₁ v₂, u} :=
    NatIso.ofComponents
      (fun P ↦
        Equiv.toIso ((Equiv.ulift.trans SSet.yonedaEquiv).trans Equiv.ulift.symm))
      (by
        intro P Q f
        ext x
        rfl)
  exact CategoryTheory.Limits.preservesColimitsOfShape_of_natIso e.symm

/-- Helper for Lemma 14.30.7: a lifting square against a boundary inclusion and a filtered-colimit
arrow already comes from one stage of the diagram. -/
lemma boundary_stagewise_square_of_filtered_colimit_square
    {J : Type v₁} [Category.{v₂} J] [IsFiltered J]
    (X₁ X₂ : J ⥤ SSet.{u}) (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂)
    (f : X₁ ⟶ X₂) (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j)
    (n : ℕ) {t : (∂Δ[n] : SSet.{u}) ⟶ c₁.pt} {b : Δ[n] ⟶ c₂.pt}
    (hsq : t ≫ φ =
      (((∂Δ[n]).ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n]) ≫ b)) :
    ∃ (j : J) (u : (∂Δ[n] : SSet.{u}) ⟶ X₁.obj j) (v : Δ[n] ⟶ X₂.obj j),
      u ≫ c₁.ι.app j = t ∧
      v ≫ c₂.ι.app j = b ∧
      u ≫ f.app j =
        (((∂Δ[n]).ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n]) ≫ v) := by
  -- Route correction: the intended proof descends the square through a small model of `J`.
  -- The remaining blocker is the boundary analogue of `simplex_isFinitelyPresentable_large`.
  -- Once `∂Δ[n]` is available as `IsFinitelyPresentable.{max u v₁ v₂}`, the stagewise factorization
  -- and equalization can follow the existing essentially-small filtered-colimit API.
  sorry

/-- Helper for Lemma 14.30.7: the structure map of an arrow-valued cocone commutes with each stage
arrow after projecting to source and target simplicial sets. -/
lemma arrow_cocone_hom_naturality
    {J : Type v₁} [Category.{v₂} J]
    (F : J ⥤ Arrow SSet.{u}) (c : Cocone F) (j : J) :
    (Arrow.leftFunc.mapCocone c).ι.app j ≫ c.pt.hom =
      (F.obj j).hom ≫ (Arrow.rightFunc.mapCocone c).ι.app j := by
  -- Read the cocone component in `Arrow SSet` as a commutative square in `SSet`.
  simpa using Arrow.w (c.ι.app j)

instance : IsStableUnderFilteredColimits (I.rlp : MorphismProperty SSet.{u}) := by
  constructor
  intro J _ _
  constructor
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ
  intro A B g hg
  have hg' :
      ∃ n, Arrow.mk g =
        Arrow.mk (((∂Δ[n]).ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n])) := by
    simpa [I, MorphismProperty.ofHoms_iff] using hg
  obtain ⟨n, hg'⟩ := hg'
  let p : (∂Δ[n] : SSet.{u}) ⟶ Δ[n] := (∂Δ[n]).ι
  have hp : HasLiftingProperty p φ := by
    -- Route correction: instead of reconstructing the colimit degreewise, descend the lifting
    -- square to one finite stage and lift there.
    rw [Arrow.hasLiftingProperty_iff]
    intro ψ
    obtain ⟨j, u, v, hu, hv, hsquare⟩ :=
      boundary_stagewise_square_of_filtered_colimit_square X₁ X₂ c₁ c₂ hc₁ hc₂ f φ hφ n ψ.w
    have hj : HasLiftingProperty p (f.app j) :=
      hf j _ (boundary_ι_mem_I n)
    let sqStage : CommSq u p (f.app j) v := CommSq.mk hsquare
    let liftStage : Δ[n] ⟶ X₁.obj j := sqStage.lift
    have hright_stage : liftStage ≫ f.app j = v := by
      simpa [liftStage] using sqStage.fac_right
    have hfac_right : (liftStage ≫ c₁.ι.app j) ≫ φ = v ≫ c₂.ι.app j := by
      -- The stagewise filler remains a filler after composing into the colimit cocone.
      calc
        (liftStage ≫ c₁.ι.app j) ≫ φ = liftStage ≫ (c₁.ι.app j ≫ φ) := by
          simp [Category.assoc]
        _ = liftStage ≫ (f.app j ≫ c₂.ι.app j) := by
          exact congrArg (fun k ↦ liftStage ≫ k) (hφ j)
        _ = (liftStage ≫ f.app j) ≫ c₂.ι.app j := by
          simp [Category.assoc]
        _ = v ≫ c₂.ι.app j := by
          exact congrArg (fun k ↦ k ≫ c₂.ι.app j) hright_stage
    -- Lift at stage `j`, then compose with the colimit cocone to obtain a lift upstairs.
    refine ⟨{ l := liftStage ≫ c₁.ι.app j, fac_left := ?_, fac_right := ?_ }⟩
    · calc
        p ≫ (liftStage ≫ c₁.ι.app j) = (p ≫ liftStage) ≫ c₁.ι.app j := by
          simp [Category.assoc]
        _ = u ≫ c₁.ι.app j := by
          simpa [liftStage, Category.assoc] using
            congrArg (fun k ↦ k ≫ c₁.ι.app j) sqStage.fac_left
        _ = ψ.left := hu
    · exact hfac_right.trans (by simpa using hv)
  -- Finally transport the lifting property back from the identified boundary inclusion.
  letI : HasLiftingProperty p φ := hp
  exact HasLiftingProperty.of_arrow_iso_left (eqToIso hg'.symm) φ

theorem boundaryInclusions_rlp_colimit_of_filtered_diagram
    {J : Type v₁} [Category.{v₂} J] [IsFiltered J]
    (F : J ⥤ Arrow SSet.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, I.rlp ((F.obj j).hom)) :
    I.rlp (c.pt.hom) := by
  let X₁ : J ⥤ SSet.{u} := F ⋙ Arrow.leftFunc
  let X₂ : J ⥤ SSet.{u} := F ⋙ Arrow.rightFunc
  let c₁ : Cocone X₁ := Arrow.leftFunc.mapCocone c
  let c₂ : Cocone X₂ := Arrow.rightFunc.mapCocone c
  let η : X₁ ⟶ X₂ :=
    Functor.whiskerLeft F (Comma.natTrans (𝟭 SSet.{u}) (𝟭 SSet.{u}))
  -- Package the stagewise trivial-Kan-fibration hypotheses as a morphism-property statement
  -- on the natural transformation between the source and target diagrams.
  have hη : (I.rlp : MorphismProperty SSet.{u}).functorCategory J η := by
    intro j
    simpa [η] using hF j
  -- The cocone equations in `Arrow SSet` give the compatibility needed by `colimitsOfShape.mk'`.
  have hφ : ∀ j, c₁.ι.app j ≫ c.pt.hom = η.app j ≫ c₂.ι.app j := by
    intro j
    simpa [X₁, X₂, c₁, c₂, η] using arrow_cocone_hom_naturality F c j
  have hcolims : IsColimit c₁ × IsColimit c₂ := by
    -- TODO: project the arrow-valued colimit cocone to source and target cocones without assuming
    -- ambient `HasColimitsOfShape J SSet`; this is the remaining wrapper-level blocker.
    sorry
  let W : MorphismProperty SSet.{u} := I.rlp
  have hW : W.IsStableUnderColimitsOfShape J := inferInstance
  exact hW.condition X₁ X₂ c₁ c₂ hcolims.1 hcolims.2 η hη c.pt.hom hφ

end

/-! ### Lemma_14_30_8 (from Chap14) -/
open CategoryTheory MorphismProperty
open CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.SimplicialObject
open CategoryTheory.Limits.Types
open SSet (ι₀ ι₁)
open SSet.modelCategoryQuillen
open scoped MonoidalCategory Simplicial

universe u

noncomputable section

variable {X Y : SSet.{u}} {f : X ⟶ Y}

private theorem mono_coprod_desc_endpoints (X : SSet.{u}) :
    Mono (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  let c : BinaryCofan (X.obj n) (X.obj n) :=
    BinaryCofan.mk ((coprod.inl : X ⟶ X ⨿ X).app n) ((coprod.inr : X ⟶ X ⨿ X).app n)
  have hc : IsColimit c :=
    mapIsColimitOfPreservesOfIsColimit ((evaluation _ _).obj n)
      (coprod.inl : X ⟶ X ⨿ X) (coprod.inr : X ⟶ X ⨿ X) (coprodIsCoprod X X)
  let e : c.pt ≅ Sum (X.obj n) (X.obj n) :=
    hc.coconePointUniqueUpToIso (binaryCoproductColimit (X.obj n) (X.obj n))
  have hinl : c.inl ≫ e.hom = Sum.inl := by
    simpa [c] using
      IsColimit.comp_coconePointUniqueUpToIso_hom hc
        (binaryCoproductColimit (X.obj n) (X.obj n)) ⟨WalkingPair.left⟩
  have hinr : c.inr ≫ e.hom = Sum.inr := by
    simpa [c] using
      IsColimit.comp_coconePointUniqueUpToIso_hom hc
        (binaryCoproductColimit (X.obj n) (X.obj n)) ⟨WalkingPair.right⟩
  have hinl' : Sum.inl ≫ e.inv = c.inl := by
    simpa using congrArg (fun k ↦ k ≫ e.inv) hinl.symm
  have hinr' : Sum.inr ≫ e.inv = c.inr := by
    simpa using congrArg (fun k ↦ k ≫ e.inv) hinr.symm
  have hinl_app (a : X.obj n) : e.inv (.inl a) = c.inl a := by
    simpa using congrFun hinl' a
  have hinr_app (a : X.obj n) : e.inv (.inr a) = c.inr a := by
    simpa using congrFun hinr' a
  have hcomp_inl (a : X.obj n) :
      (e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) (.inl a) = ι₀.app n a := by
    calc
      (e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) (.inl a) =
          (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n (e.inv (.inl a)) := rfl
      _ = (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n (c.inl a) := by rw [hinl_app]
      _ =
          ((coprod.inl : X ⟶ X ⨿ X) ≫
            coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n a := rfl
      _ = ι₀.app n a := by
          simpa using congrFun
            (congr_app (coprod.inl_desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) n) a
  have hcomp_inr (a : X.obj n) :
      (e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) (.inr a) = ι₁.app n a := by
    calc
      (e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) (.inr a) =
          (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n (e.inv (.inr a)) := rfl
      _ = (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n (c.inr a) := by rw [hinr_app]
      _ =
          ((coprod.inr : X ⟶ X ⨿ X) ≫
            coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n a := rfl
      _ = ι₁.app n a := by
          simpa using congrFun
            (congr_app (coprod.inr_desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) n) a
  have hsum :
      Function.Injective
        ((e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) :
          Sum (X.obj n) (X.obj n) → (X ⊗ Δ[1]).obj n) := by
    intro a b hab
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            have hfst : (ι₀.app n a).1 = (ι₀.app n b).1 := by
              have hfst := congrArg Prod.fst hab
              rw [hcomp_inl a, hcomp_inl b] at hfst
              exact hfst
            simpa using hfst
        | inr b =>
            exfalso
            have hsnd :
                ((e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) (.inl a)).2 =
                  ((e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) (.inr b)).2 := by
              simpa using congrArg Prod.snd hab
            have hsnd0 :
                SSet.stdSimplex.asOrderHom
                    ((e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) (.inl a)).2 0 =
                  SSet.stdSimplex.asOrderHom
                    ((e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) (.inr b)).2 0 := by
              simpa [SSet.stdSimplex.asOrderHom] using
                congrArg (fun t : Δ[1].obj n ↦ SSet.stdSimplex.asOrderHom t 0) hsnd
            rw [hcomp_inl a, hcomp_inr b] at hsnd0
            have hzero :
                SSet.stdSimplex.asOrderHom ((ι₀.app n a).2) 0 = (0 : Fin 2) := by
              simpa [SSet.stdSimplex.asOrderHom] using
                (SSet.ι₀_app_snd_apply a 0)
            have hone :
                SSet.stdSimplex.asOrderHom ((ι₁.app n b).2) 0 = (1 : Fin 2) := by
              simpa [SSet.stdSimplex.asOrderHom] using
                (SSet.ι₁_app_snd_apply b 0)
            have hsnd01 : (0 : Fin 2) = 1 := hzero.symm.trans (hsnd0.trans hone)
            exact Fin.zero_ne_one hsnd01
    | inr a =>
        cases b with
        | inl b =>
            exfalso
            have hsnd :
                ((e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) (.inr a)).2 =
                  ((e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) (.inl b)).2 := by
              simpa using congrArg Prod.snd hab
            have hsnd0 :
                SSet.stdSimplex.asOrderHom
                    ((e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) (.inr a)).2 0 =
                  SSet.stdSimplex.asOrderHom
                    ((e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) (.inl b)).2 0 := by
              simpa [SSet.stdSimplex.asOrderHom] using
                congrArg (fun t : Δ[1].obj n ↦ SSet.stdSimplex.asOrderHom t 0) hsnd
            rw [hcomp_inr a, hcomp_inl b] at hsnd0
            have hone :
                SSet.stdSimplex.asOrderHom ((ι₁.app n a).2) 0 = (1 : Fin 2) := by
              simpa [SSet.stdSimplex.asOrderHom] using
                (SSet.ι₁_app_snd_apply a 0)
            have hzero :
                SSet.stdSimplex.asOrderHom ((ι₀.app n b).2) 0 = (0 : Fin 2) := by
              simpa [SSet.stdSimplex.asOrderHom] using
                (SSet.ι₀_app_snd_apply b 0)
            have hsnd01 : (1 : Fin 2) = 0 := hone.symm.trans (hsnd0.trans hzero)
            exact Fin.zero_ne_one hsnd01.symm
        | inr b =>
            have hfst : (ι₁.app n a).1 = (ι₁.app n b).1 := by
              have hfst := congrArg Prod.fst hab
              rw [hcomp_inr a, hcomp_inr b] at hfst
              exact hfst
            simpa using hfst
  intro a b hab
  apply e.toEquiv.injective
  apply hsum
  simpa using hab

/- Domain-style sampling for Lemma 14.30.8:
- primary domain: simplicial-set lifting properties and simplicial homotopy equivalences.
- sampled owner declarations:
  `SSet.modelCategoryQuillen.I.rlp`,
  `boundaryInclusions_rlp_monomorphisms`,
  `CategoryTheory.SimplicialObject.HomotopyEquiv`,
  `CategoryTheory.SimplicialObject.IsHomotopyEquivalence`,
  `SSet.Homotopy`.
- best owner abstractions:
  the source hypothesis is already canonically expressed by `I.rlp f`, and the target owner is
  `HomotopyEquiv X Y`/`IsHomotopyEquivalence f`.
- primitive data:
  the morphism `f` together with the owner property `I.rlp f`;
  the section of `f`, the endpoint subcomplex of `X ⊗ Δ[1]`, and the filler map are derived proof
  data, not new public API.
- derived API:
  the induced simplicial homotopy `f ≫ g ∼ 𝟙 X`, transported from an `SSet.Homotopy`.

Source/core/bridge triage:
- `source-facing`: a trivial Kan fibration of simplicial sets is a simplicial homotopy
  equivalence;
- `core/canonical`: the owners `I.rlp` and `HomotopyEquiv`;
- `bridge/view`: the conversion from the simplicial-set homotopy filler to the simplicial-object
  relation `Homotopic` via `SSet.Homotopy.toSimplicialObjectHomotopy`. -/

-- Proof sketch: use Lemma 14.30.2 to upgrade `hf : I.rlp f` to the right lifting property against
-- all monomorphisms. Apply this first to the initial-object inclusion to obtain a section
-- `g : Y ⟶ X` of `f`, and then to the canonical endpoint map `X ⨿ X ⟶ X ⊗ Δ[1]` induced by
-- `ι₀, ι₁`, with endpoint values `f ≫ g` and `𝟙 X`. The resulting filler is an `SSet.Homotopy`
-- from `f ≫ g` to `𝟙 X`, which yields the desired simplicial homotopy equivalence together with
-- `g ≫ f = 𝟙 Y`.
/-- Helper for Lemma 14.30.8: a morphism with the right lifting property against all
monomorphisms admits a section. -/
private theorem section_of_monomorphism_rlp (hmono : (monomorphisms SSet).rlp f) :
    ∃ g : Y ⟶ X, g ≫ f = 𝟙 Y := by
  -- Lift against the initial map to extract the right inverse promised by the source proof.
  have hSection : HasLiftingProperty (initial.to Y) f := hmono (initial.to Y) (by infer_instance)
  have sqSection : CommSq (initial.to X) (initial.to Y) f (𝟙 Y) := by
    -- The unique map out of the initial simplicial set makes the square commute tautologically.
    refine CommSq.mk ?_
    simp
  let _ : sqSection.HasLift := hSection.sq_hasLift sqSection
  refine ⟨CommSq.lift sqSection, ?_⟩
  exact CommSq.fac_right sqSection

/-- Helper for Lemma 14.30.8: the endpoint data `f ≫ g` and `𝟙 X` define the lifting square used
to produce the simplicial homotopy. -/
private theorem endpoint_square_commutes (g : Y ⟶ X) (hg : g ≫ f = 𝟙 Y) :
    CommSq (coprod.desc (f ≫ g) (𝟙 X))
      (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) f (fst X Δ[1] ≫ f) := by
  -- Check commutativity on the two coproduct summands separately.
  refine CommSq.mk ?_
  apply coprod.hom_ext
  · simp [hg, Category.assoc]
  · simp [hg, Category.assoc]

/-- Helper for Lemma 14.30.8: the lift of the endpoint square restricts to `f ≫ g` at the
`0`-endpoint. -/
private theorem endpoint_lift_h_zero (g : Y ⟶ X)
    (sqHomotopy : CommSq (coprod.desc (f ≫ g) (𝟙 X))
      (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) f (fst X Δ[1] ≫ f))
    [sqHomotopy.HasLift] :
    ι₀ ≫ CommSq.lift sqHomotopy = f ≫ g := by
  -- Compose the left factorization identity with the left coproduct injection.
  calc
    ι₀ ≫ CommSq.lift sqHomotopy =
        ((coprod.inl : X ⟶ X ⨿ X) ≫ coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) ≫
          CommSq.lift sqHomotopy := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ k ≫ CommSq.lift sqHomotopy)
              (coprod.inl_desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).symm
    _ = (coprod.inl : X ⟶ X ⨿ X) ≫ coprod.desc (f ≫ g) (𝟙 X) := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ (coprod.inl : X ⟶ X ⨿ X) ≫ k) (CommSq.fac_left sqHomotopy)
    _ = f ≫ g := by
          simpa using (coprod.inl_desc (f ≫ g) (𝟙 X))

/-- Helper for Lemma 14.30.8: the lift of the endpoint square restricts to the identity at the
`1`-endpoint. -/
private theorem endpoint_lift_h_one (g : Y ⟶ X)
    (sqHomotopy : CommSq (coprod.desc (f ≫ g) (𝟙 X))
      (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) f (fst X Δ[1] ≫ f))
    [sqHomotopy.HasLift] :
    ι₁ ≫ CommSq.lift sqHomotopy = 𝟙 X := by
  -- Compose the left factorization identity with the right coproduct injection.
  calc
    ι₁ ≫ CommSq.lift sqHomotopy =
        ((coprod.inr : X ⟶ X ⨿ X) ≫ coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) ≫
          CommSq.lift sqHomotopy := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ k ≫ CommSq.lift sqHomotopy)
              (coprod.inr_desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).symm
    _ = (coprod.inr : X ⟶ X ⨿ X) ≫ coprod.desc (f ≫ g) (𝟙 X) := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ (coprod.inr : X ⟶ X ⨿ X) ≫ k) (CommSq.fac_left sqHomotopy)
    _ = 𝟙 X := by
          simpa using (coprod.inr_desc (f ≫ g) (𝟙 X))

/-- Helper for Lemma 14.30.8: the relative condition for the bottom subcomplex is vacuous, so the
endpoint lift automatically satisfies it. -/
private theorem endpoint_lift_bot_relative (g : Y ⟶ X)
    (sqHomotopy : CommSq (coprod.desc (f ≫ g) (𝟙 X))
      (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) f (fst X Δ[1] ≫ f))
    [sqHomotopy.HasLift] :
    (⊥ : X.Subcomplex).ι ▷ Δ[1] ≫ CommSq.lift sqHomotopy =
      fst (⊥ : X.Subcomplex).toSSet Δ[1] ≫
        SSet.Subcomplex.isInitialBot.to (⊥ : X.Subcomplex).toSSet ≫
        (⊥ : X.Subcomplex).ι := by
  -- There are no simplices in the bottom subcomplex, so extensionality closes the goal.
  ext Δ z
  exact False.elim z.1.2

/-- Helper for Lemma 14.30.8: the endpoint lift packages into a simplicial-set homotopy from
`f ≫ g` to `𝟙 X`. -/
private noncomputable def endpoint_filler_homotopy (g : Y ⟶ X)
    (sqHomotopy : CommSq (coprod.desc (f ≫ g) (𝟙 X))
      (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) f (fst X Δ[1] ≫ f))
    [sqHomotopy.HasLift] :
    SSet.Homotopy (f ≫ g) (𝟙 X) where
  h := CommSq.lift sqHomotopy
  h₀ := endpoint_lift_h_zero (f := f) g sqHomotopy
  h₁ := endpoint_lift_h_one (f := f) g sqHomotopy
  rel := endpoint_lift_bot_relative (f := f) g sqHomotopy

/-- Helper for Lemma 14.30.8: the filler map yields the Chapter 14 homotopy relation
`f ≫ g ∼ 𝟙 X`. -/
private theorem endpoint_filler_homotopic (g : Y ⟶ X)
    (sqHomotopy : CommSq (coprod.desc (f ≫ g) (𝟙 X))
      (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) f (fst X Δ[1] ≫ f))
    [sqHomotopy.HasLift] :
    Homotopic (f ≫ g) (𝟙 X) := by
  -- Convert the simplicial-set homotopy furnished by the lift into the simplicial-object one.
  exact Homotopic.of_homotopy (endpoint_filler_homotopy (f := f) g sqHomotopy).toSimplicialObjectHomotopy

/-- Helper for Lemma 14.30.8: a strict section equation already gives the second homotopy
required for a simplicial homotopy equivalence. -/
private theorem section_comp_homotopic_id (g : Y ⟶ X) (hg : g ≫ f = 𝟙 Y) :
    Homotopic (g ≫ f) (𝟙 Y) := by
  -- Rewrite the composite to the identity and use reflexivity of the homotopy relation.
  simpa [hg] using (Homotopic.refl (𝟙 Y : Y ⟶ Y))

/-- Helper for Lemma 14.30.8: the section and endpoint filler assemble into the canonical
homotopy-equivalence data. -/
private noncomputable def filler_homotopy_equiv_data (g : Y ⟶ X) (hg : g ≫ f = 𝟙 Y)
    (sqHomotopy : CommSq (coprod.desc (f ≫ g) (𝟙 X))
      (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) f (fst X Δ[1] ≫ f))
    [sqHomotopy.HasLift] :
    HomotopyEquiv X Y where
  hom := f
  inv := g
  homotopyHomInvId := endpoint_filler_homotopic (f := f) g sqHomotopy
  homotopyInvHomId := section_comp_homotopic_id (f := f) g hg

/-- Lemma 14.30.8: every trivial Kan fibration of simplicial sets is a simplicial homotopy
equivalence. -/
lemma trivialKanFibration_isHomotopyEquivalence (hf : I.rlp f) :
    IsHomotopyEquivalence f := by
  -- First upgrade the trivial Kan fibration hypothesis to lifting against all monomorphisms.
  have hmono : (monomorphisms SSet).rlp f :=
    boundaryInclusions_rlp_monomorphisms hf
  rcases section_of_monomorphism_rlp (f := f) hmono with ⟨g, hg⟩
  -- Then apply the same lifting property to the endpoint inclusion in `X ⊗ Δ[1]`.
  have hEndpoint :
      HasLiftingProperty (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) f :=
    hmono (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) (mono_coprod_desc_endpoints X)
  have sqHomotopy :
      CommSq (coprod.desc (f ≫ g) (𝟙 X))
        (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) f (fst X Δ[1] ≫ f) :=
    endpoint_square_commutes (f := f) g hg
  let _ : sqHomotopy.HasLift := hEndpoint.sq_hasLift sqHomotopy
  -- The extracted section and the endpoint lift give the required homotopy-equivalence witness.
  exact (filler_homotopy_equiv_data (f := f) g hg sqHomotopy).isHomotopyEquivalence

end
