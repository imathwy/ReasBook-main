import Mathlib
import Mathlib.Algebra.Module.Injective
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_19_2_1 (from Chap19) -/
open CategoryTheory Limits Opposite

noncomputable section

/-- The transition map between consecutive finite initial segments of `ℕ`, modeled by
`Fin (n + 1) ⟶ Fin (n + 2)`. -/
def nat_initial_segment_map (n : ℕ) : Fin (n + 1) ⟶ Fin (n + 2) :=
  Fin.castSucc

/-- The sequential diagram of finite initial segments of `ℕ` in the category of sets. -/
def nat_initial_segment_diagram : ℕ ⥤ Type :=
  Functor.ofSequence nat_initial_segment_map

/-- The map `ℕ → colimit nat_initial_segment_diagram` sending `n` to the class of the top element
of the `n`-th finite initial segment. -/
def nat_initial_segment_colimit_map : ℕ → colimit nat_initial_segment_diagram :=
  fun n ↦ colimit.ι nat_initial_segment_diagram n (Fin.last n)

/-- The canonical map from `ℕ` to the colimit of the finite initial segments does not factor
through any single stage `Fin (m + 1)`. -/
-- Proof sketch: if such a factorization through `Fin (m + 1)` existed, the image of every natural
-- number in the colimit would already come from that finite stage, contradicting the fact that the
-- elements represented by `Fin.last n` require arbitrarily large stages.
theorem nat_initial_segment_colimit_map_not_factor_through_stage (m : ℕ) :
    ¬ ∃ f : ℕ → Fin (m + 1),
        nat_initial_segment_colimit_map = fun n ↦ colimit.ι nat_initial_segment_diagram m (f n) :=
  sorry

/-- Example 19.2.1: in the category of sets, for the sequential system of finite initial
segments of `ℕ` modeled by `Fin (n + 1)`, the canonical comparison map from the colimit of the
stagewise Hom-sets `ℕ → Fin (n + 1)` to the Hom-set `ℕ → colimit nat_initial_segment_diagram` is
not surjective. -/
-- Proof sketch: apply `nat_initial_segment_colimit_map_not_factor_through_stage` to the map
-- `nat_initial_segment_colimit_map`. Any element in the image of the comparison map comes from a
-- single stage, so this specific map cannot lie in the image.
theorem nat_initial_segment_hom_colimit_comparison_not_surjective :
    ¬ Function.Surjective
      (colimit.post nat_initial_segment_diagram (coyoneda.obj (op ℕ))) := sorry

/-! ### Example_19_2_2 (from Chap19) -/
open CategoryTheory Limits Opposite
open scoped CategoryTheory

/- Domain-style sampling for Example 19.2.2:
- primary domain: quotient sets in `Type`, sequential colimits, and the represented-Hom
  comparison `colimit.post B (coyoneda.obj (op A))`;
- sampled owner declarations:
  `Quotient.map`,
  `Functor.ofSequence`,
  `colimit.post`,
  `colimit_post_coyoneda_ι_app`;
- best owner abstractions:
  the source-facing quotient stage `collapsedInitialSegment n` and the canonical comparison map
  `colimit.post collapsedInitialSegmentDiagram (coyoneda.obj (op ℕ))`;
- primitive data: the quotient relation collapsing the initial segment `{0, …, n}`;
- derived API: the quotient projection, the collapsed class, the transition maps induced by
  monotonicity of the collapsed segment, and the comparison map from `19.2.0.1`.

Source/core/bridge triage:
- `source-facing`: the sequential quotient system `B_{n + 1}` and the noninjectivity example;
- `core/canonical`: `colimit.post`;
- `bridge/view`: the quotient projection `ℕ → B_{n + 1}` and the constant map at the collapsed
  class.

The raw owner name `collapsedInitialSegment` is already short and stable on this small local API
surface, so no extra `B_n` notation is introduced here.
-/

/-- The equivalence relation on `ℕ` that identifies all elements of the initial segment
`{0, …, n}` and leaves larger elements distinct. -/
def collapsedInitialSegmentSetoid (n : ℕ) : Setoid ℕ where
  r a b := a = b ∨ a ≤ n ∧ b ≤ n
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact Or.inl rfl
    · intro a b h
      rcases h with rfl | ⟨ha, hb⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hb, ha⟩
    · intro a b c hab hbc
      rcases hab with rfl | ⟨ha, hb⟩
      · exact hbc
      · rcases hbc with rfl | ⟨_, hc⟩
        · exact Or.inr ⟨ha, hb⟩
        · exact Or.inr ⟨ha, hc⟩

/-- The quotient set obtained by collapsing the first `n + 1` natural numbers to a single point.
This is the Lean stage indexed by `n`, corresponding to the textbook family `B_{n + 1}`. -/
abbrev collapsedInitialSegment (n : ℕ) : Type :=
  Quotient (collapsedInitialSegmentSetoid n)

/-- The natural quotient projection `ℕ → B_{n + 1}`. -/
def collapsedInitialSegmentProjection (n : ℕ) : ℕ → collapsedInitialSegment n :=
  Quotient.mk _

/-- The collapsed class of the initial segment `{0, …, n}` in `B_{n + 1}`. -/
def collapsedInitialSegmentCollapsedPoint (n : ℕ) : collapsedInitialSegment n :=
  collapsedInitialSegmentProjection n 0

/-- The constant map to the collapsed class in `B_{n + 1}`. -/
def collapsedInitialSegmentCollapsedMap (n : ℕ) : ℕ → collapsedInitialSegment n :=
  fun _ ↦ collapsedInitialSegmentCollapsedPoint n

/-- For `n ≤ m`, the quotient map `B_{n + 1} → B_{m + 1}` induced by collapsing a larger initial
segment. -/
def collapsedInitialSegmentMap {n m : ℕ} (h : n ≤ m) :
    collapsedInitialSegment n → collapsedInitialSegment m :=
  Quotient.map id <| by
    intro a b hab
    rcases hab with rfl | ⟨ha, hb⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨Nat.le_trans ha h, Nat.le_trans hb h⟩

/-- The successor transition `B_{n + 1} → B_{n + 2}` in the collapsed-initial-segment system. -/
def collapsedInitialSegmentStep (n : ℕ) :
    collapsedInitialSegment n → collapsedInitialSegment (n + 1) :=
  collapsedInitialSegmentMap (Nat.le_succ n)

/-- The sequential system `B_{n + 1}` of collapsed initial segments of the natural numbers. -/
def collapsedInitialSegmentDiagram : ℕ ⥤ Type :=
  Functor.ofSequence collapsedInitialSegmentStep

-- Proof sketch: every class in some stage eventually maps to the collapsed point, so in the
-- filtered colimit all representatives become equal to that distinguished class.
/-- Any two points in the colimit of the collapsed-initial-segment system are equal. -/
theorem collapsedInitialSegmentDiagram_colimit_subsingleton :
    Subsingleton (colimit collapsedInitialSegmentDiagram) := sorry

-- Proof sketch: compare the classes in `colim_n Mor(ℕ, B_{n + 1})` represented by the quotient
-- projections `ℕ → B_{n + 1}` and by the constant maps to the collapsed class. They remain
-- distinct in the Hom-colimit, but after composing with the colimit cocone they both become the
-- unique map from `ℕ` to the one-point colimit of the `B_{n + 1}`.
/-- Example 19.2.2: for the sequential system `B_{n + 1}` obtained by collapsing the first
`n + 1` natural numbers, the canonical comparison map
`colim_n Mor(ℕ, B_{n + 1}) → Mor(ℕ, colim_n B_{n + 1})` is not injective. -/
theorem collapsedInitialSegment_hom_colimit_comparison_not_injective :
    ¬ Function.Injective
      (colimit.post collapsedInitialSegmentDiagram (coyoneda.obj (op ℕ))) := sorry

/-! ### Lemma_19_2_3 (from Chap19) -/
open CategoryTheory CategoryTheory.Limits Opposite

universe v u

section

variable {J : Type v} [SmallCategory J]

/- Domain-style sampling for Lemma 19.2.3:
- primary domain: filtered colimits in `Type` and represented Hom-functors `Hom(A, -)`;
- sampled owner declarations:
  `colimit.post`,
  `CategoryTheory.Types.isCardinalPresentable_iff`,
  `CategoryTheory.isFinitelyPresentable_iff_preservesFilteredColimits`,
  `CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink`;
- best owner abstraction: the source-facing comparison map is the canonical owner
  `colimit.post B (coyoneda.obj (op A))`, while the core/canonical input controlling its
  bijectivity is `IsFinitelyPresentable A`;
- primitive data: the finite type `A` and the filtered diagram `B`;
- derived API: preservation of the colimit of `B` by `coyoneda.obj (op A)`, hence the bijectivity
  of `colimit.post B (coyoneda.obj (op A))`.

Source/core/bridge triage:
- `source-facing`: the displayed bijection
  `colim_j Hom(A, B_j) → Hom(A, colim_j B_j)` for finite `A`;
- `core/canonical`: `IsFinitelyPresentable A`;
- `bridge/view`: the `Type`-specific cardinal characterization of finite presentability and the
  specialization of preservation to the fixed comparison map `colimit.post`.
-/

-- Proof sketch: use that finite sets are finitely presentable in `Type`, so `coyoneda.obj (op A)`
-- preserves filtered colimits; then the displayed comparison map is the comparison morphism from
-- the preserved colimit cocone and hence is bijective.
/-- Lemma 19.2.3: for a filtered diagram of sets and a finite set `A`, the canonical map
`colim_j Hom(A, B_j) → Hom(A, colim_j B_j)` is bijective. -/
theorem finite_hom_to_colimit_comparison_bijective [IsFiltered J] (A : Type (max u v))
    [Finite A] (B : J ⥤ Type (max u v)) :
    Function.Bijective (colimit.post B (coyoneda.obj (op A))) := by
  letI : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  letI : IsFinitelyPresentable.{max u v} A := by
    exact (CategoryTheory.Types.isCardinalPresentable_iff Cardinal.aleph0).2 <| by
      rw [hasCardinalLT_aleph0_iff]
      infer_instance
  letI : PreservesFilteredColimitsOfSize.{v, v} (coyoneda.obj (op A)) :=
    preservesFilteredColimitsOfSize_shrink (coyoneda.obj (op A))
  letI : PreservesColimit B (coyoneda.obj (op A)) := by
    infer_instance
  exact (isIso_iff_bijective (colimit.post B (coyoneda.obj (op A)))).1 inferInstance

end

/-! ### Definition_19_2_4 (from Chap19) -/
open CategoryTheory Limits Opposite

universe w v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for 19.2.4:
- primary domain: transfinite smallness conditions expressed by preservation of colimits of
  `α`-indexed diagrams under the represented functor `Hom(A, -) = coyoneda.obj (op A)`;
- sampled owner declarations:
  `PreservesColimit`,
  `colimit.post`,
  `preservesColimit_of_isIso_post`,
  `MorphismProperty.IsCardinalForSmallObjectArgument.preservesColimit`;
- best owner abstraction: for a fixed system `B`, the canonical owner is
  `PreservesColimit B (coyoneda.obj (op A))`; the extra restriction that every transition map of
  `B` lie in `I` is source-facing data of Definition 19.2.4, not a separate owner already present
  in mathlib/project;
- primitive data: an object `A`, a morphism property `I`, an ordinal `α`, an `α`-indexed diagram
  `B`, and the hypothesis that each structure map of `B` lies in `I`;
- derived API: the equivalent comparison-map formulation via
  `colimit.post B (coyoneda.obj (op A))`.

Source/core/bridge triage:
- `source-facing`: `is_alpha_small_wrt A I α`;
- `core/canonical`: `PreservesColimit B (coyoneda.obj (op A))` for each admissible system `B`;
- `bridge/view`: the comparison morphism `colimit.post B (coyoneda.obj (op A))`.

The deleted helper predicate and elimination theorem were only local packaging around this
canonical preservation condition.
-/

/-- Definition 19.2.4: an object `A` is `α`-small with respect to `I` if for every system
`B : α.ToType ⥤ C` whose transition maps lie in `I`, the functor `Hom(A, -)` preserves the
colimit of `B`; equivalently, the comparison map of `19.2.0.1` is an isomorphism for every such
system. -/
def is_alpha_small_wrt (A : C) (I : MorphismProperty C) (α : Ordinal) : Prop :=
  ∀ (B : α.ToType ⥤ C)
    (_ : ∀ ⦃j j' : α.ToType⦄ (f : j ⟶ j'), I (B.map f)),
      PreservesColimit B (coyoneda.obj (op A))

end

end CategoryTheory

/-! ### Proposition_19_2_5 (from Chap19) -/
open CategoryTheory
open ModuleCat

universe u v

namespace CategoryTheory

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-
Domain-style sampling for 19.2.5:
- primary domain: transfinite smallness in `ModuleCat R`, with the source-specific size bound
  expressed by the lattice of `R`-submodules of `M`;
- sampled owner declarations:
  `is_alpha_small_wrt`,
  `ModuleCat.subobjectModule`,
  `ConcreteCategory.injective_eq_monomorphisms`,
  `is_alpha_small_wrt_monomorphisms_of_subobject_cardinal_lt_cof`;
- best owner abstraction: the conclusion should use the canonical morphism-property owner
  `MorphismProperty.monomorphisms (ModuleCat R)`, while the source-facing cardinal bound may remain
  on `Submodule R M`;
- primitive data: the module `M`, the ordinal `α`, and the cardinal inequality
  `Cardinal.mk (Submodule R M) < α.cof`;
- derived API: the categorical smallness statement `is_alpha_small_wrt (of R M) ... α`.

Source/core/bridge triage:
- `source-facing`: the module-theoretic cardinal bound on `Submodule R M`;
- `core/canonical`: `is_alpha_small_wrt (of R M) (MorphismProperty.monomorphisms (ModuleCat R)) α`;
- `bridge/view`: the order isomorphism `ModuleCat.subobjectModule` and the concrete-category
  identification of injective maps with monomorphisms.
-/

-- Proof sketch: for an `α`-indexed transfinite system of injective module maps and a morphism
-- `M ⟶ colimit B`, consider the `R`-submodules `f ⁻¹(B_β) ⊆ M`. There are at most
-- `Cardinal.mk (Submodule R M)` distinct such submodules, so when this cardinal is strictly below
-- `α.cof`, the corresponding indices are bounded in `α`; then the map factors through one stage,
-- which is exactly the required smallness criterion.
/-- Proposition 19.2.5: if the cofinality of `α` is strictly larger than the cardinality of the
set of `R`-submodules of `M`, then `M` is `α`-small with respect to injections, i.e. with
respect to monomorphisms in `ModuleCat R`. -/
theorem moduleCat_is_alpha_small_wrt_monomorphisms_of_submodule_cardinal_lt_cof
    (α : Ordinal) (hα : Cardinal.mk (Submodule R M) < α.cof) :
    is_alpha_small_wrt (of R M) (MorphismProperty.monomorphisms (ModuleCat R)) α := sorry

end

end CategoryTheory

/-! ### Lemma_19_2_6_Baers_criterion (from Chap19) -/
/- Lemma 19.2.6 (Baer's criterion): for a ring `R` and an `R`-module `Q`, the module `Q` is
injective if and only if every `R`-linear map from an ideal `I : Ideal R` to `Q` extends along the
inclusion `I → R`. This is the canonical mathlib theorem `Module.Baer.iff_injective`, because
`Module.Baer R Q` is exactly the extension property for all ideals of `R`. -/
recall Module.Baer.iff_injective

/-! ### Lemma_19_2_7 (from Chap19) -/
open CategoryTheory Limits
open scoped DirectSum

universe u

/- Domain-style sampling for Lemma 19.2.7:
- primary domain: functoriality of pushouts and commutative squares in `ModuleCat R`;
- sampled owner API:
  `CategoryTheory.CommSq`,
  `pushout.map`,
  `baerModuleStep_square_commutes`,
  `𝐌(M)`,
  `𝟭 (ModuleCat R) ⟶ baerModuleStepFunctor R`;
- best owner abstraction: the natural transformation from the identity functor to the Baer
  one-step functor `M ↦ 𝐌(M)`, with source-facing square statements expressed as `CommSq`;
- primitive data: the Baer pushout span, its induced pushout maps, and the functorial
  `pushout.map`;
- derived API: the naturality squares and the resulting natural transformation.

Source/core/bridge triage:
- `source-facing`: the functoriality square for `M ⟶ \mathbf{M}(M)` and the extension square for
  ideal maps;
- `core/canonical`: `CommSq` for commuting squares and the natural transformation
  `𝟭 (ModuleCat R) ⟶ baerModuleStepFunctor R`;
- `bridge/view`: the explicit Baer pushout maps whose commutativity witnesses are packaged by
  those owner abstractions. -/

section

variable (R : Type u) [Ring R]

local notation "𝐌(" M ")" => baerModuleStep R M

/-- The map on Baer indices induced by an `R`-linear map of modules. -/
abbrev baerModuleIndexMap {M N : ModuleCat R} (f : M ⟶ N) :
    baerModuleIndex R M → baerModuleIndex R N :=
  fun j ↦ ⟨j.1, f.hom.comp j.2⟩

/-- The map on the direct sum of ideals induced by an `R`-linear map of modules. -/
noncomputable abbrev baerModuleIdealDirectSumMap {M N : ModuleCat R} (f : M ⟶ N) :
    baerModuleIdealDirectSum R M ⟶ baerModuleIdealDirectSum R N :=
  ModuleCat.ofHom <|
    DirectSum.toModule R (baerModuleIndex R M)
      (⨁ j : baerModuleIndex R N, baerModuleIdealSummand R N j)
      (fun j ↦
        DirectSum.lof R (baerModuleIndex R N) (baerModuleIdealSummand R N)
          (baerModuleIndexMap R f j))

/-- The map on the direct sum of copies of `R` induced by an `R`-linear map of modules. -/
noncomputable abbrev baerModuleRingDirectSumMap {M N : ModuleCat R} (f : M ⟶ N) :
    baerModuleRingDirectSum R M ⟶ baerModuleRingDirectSum R N :=
  ModuleCat.ofHom <|
    DirectSum.toModule R (baerModuleIndex R M)
      (⨁ _j : baerModuleIndex R N, R)
      (fun j ↦
        DirectSum.lof R (baerModuleIndex R N) (fun _j ↦ R)
          (baerModuleIndexMap R f j))

/-- The left side of the Baer pushout square is natural in the module. -/
-- Proof sketch: both composites send the summand indexed by `(𝔞, φ)` to the copy of `R`
-- indexed by `(𝔞, f ∘ φ)` using the same inclusion `𝔞 ↪ R`, so they agree by extensionality of
-- maps out of a direct sum.
theorem baerModuleLeftVertical_natural {M N : ModuleCat R} (f : M ⟶ N) :
    CommSq (baerModuleLeftVertical R M) (baerModuleIdealDirectSumMap R f)
      (baerModuleRingDirectSumMap R f) (baerModuleLeftVertical R N) := sorry

/-- The top map in the Baer pushout square is natural in the module. -/
-- Proof sketch: on the summand indexed by `(𝔞, φ)`, the top map followed by `f` is exactly the
-- composite `f ∘ φ`, which is also the map defining the target summand indexed by `(𝔞, f ∘ φ)`.
theorem baerModuleTopMap_natural {M N : ModuleCat R} (f : M ⟶ N) :
    CommSq (baerModuleTopMap R M) (baerModuleIdealDirectSumMap R f) f
      (baerModuleTopMap R N) := sorry

/-- The map `\mathbf{M}(M) → \mathbf{M}(N)` induced by a morphism `M ⟶ N`. -/
noncomputable abbrev baerModuleStepMap {M N : ModuleCat R} (f : M ⟶ N) :
    𝐌(M) ⟶ 𝐌(N) :=
  pushout.map (baerModuleLeftVertical R M) (baerModuleTopMap R M)
    (baerModuleLeftVertical R N) (baerModuleTopMap R N)
    (baerModuleRingDirectSumMap R f) f (baerModuleIdealDirectSumMap R f)
    (baerModuleLeftVertical_natural R f).w (baerModuleTopMap_natural R f).w

/-- The canonical map on Baer pushouts acts as the identity on identity morphisms. -/
-- Proof sketch: this is the identity case of `pushout.map`, using the identity maps on all three
-- corners of the defining span.
theorem baerModuleStepMap_id (M : ModuleCat R) :
    baerModuleStepMap R (𝟙 M) = 𝟙 (𝐌(M)) := sorry

/-- The canonical map on Baer pushouts respects composition. -/
-- Proof sketch: functoriality of `pushout.map` gives the compatibility with composition once the
-- naturality relations for the two sides of the defining span are inserted.
theorem baerModuleStepMap_comp {M N P : ModuleCat R} (f : M ⟶ N) (g : N ⟶ P) :
    baerModuleStepMap R (f ≫ g) =
      baerModuleStepMap R f ≫ baerModuleStepMap R g := sorry

/-- The Baer construction `M ↦ \mathbf{M}(M)` as an endofunctor on `ModuleCat R`. -/
noncomputable def baerModuleStepFunctor : ModuleCat R ⥤ ModuleCat R where
  obj := baerModuleStep R
  map := baerModuleStepMap R
  map_id := baerModuleStepMap_id R
  map_comp := baerModuleStepMap_comp R

/-- The canonical extension map `R ⟶ \mathbf{M}(M)` attached to an ideal map `𝔞 → M`. -/
noncomputable abbrev baerModuleIdealLift (M : ModuleCat R) (I : Ideal R) (φ : I →ₗ[R] M) :
    ModuleCat.of R R ⟶ 𝐌(M) :=
  ModuleCat.ofHom
      (DirectSum.lof R (baerModuleIndex R M) (fun _j ↦ R) ⟨I, φ⟩) ≫
    baerModuleStepFromRingDirectSum R M

-- Proof sketch: the morphisms `baerModuleStepMap R f` assemble the one-step Baer construction
-- into an endofunctor, and the canonical inclusions from `M` into the pushouts commute with these
-- induced maps by the universal property of `pushout.map`.
/-- Lemma 19.2.7 (1): the canonical maps `M ⟶ \mathbf{M}(M)` are functorial in `M`. -/
theorem baerModuleStepInclusion_natural {M N : ModuleCat R} (f : M ⟶ N) :
    CommSq f (baerModuleStepInclusion R M) (baerModuleStepInclusion R N)
      ((baerModuleStepFunctor R).map f) := sorry

/-- The natural transformation from the identity functor on `R`-modules to the one-step Baer
functor. -/
noncomputable def baerModuleStepInclusionNatTrans :
    𝟭 (ModuleCat R) ⟶ baerModuleStepFunctor R where
  app M := baerModuleStepInclusion R M
  naturality := fun {_ _} f ↦ (baerModuleStepInclusion_natural R f).w

-- Proof sketch: in the Baer pushout construction one adjoins copies of `R` to force extensions of
-- maps from ideals into `M`, but no relation identifies two distinct elements already lying in
-- `M`; this yields injectivity of the canonical inclusion.
/-- Lemma 19.2.7 (2): the canonical map `M ⟶ \mathbf{M}(M)` is injective. -/
theorem baerModuleStepInclusion_injective (M : ModuleCat R) :
    Function.Injective (baerModuleStepInclusion R M).hom := sorry

-- Proof sketch: the pair `(I, φ)` indexing the chosen ideal map contributes a distinguished `R`
-- summand to the left side of the pushout, and composing its coprojection with the pushout map
-- produces the required extension square.
/-- Lemma 19.2.7 (3): every `R`-linear map from an ideal `I ⊆ R` to `M` extends to a map
`R ⟶ \mathbf{M}(M)` compatible with the canonical inclusion `M ⟶ \mathbf{M}(M)`. -/
theorem baerModuleIdealLift_comp_subtype (M : ModuleCat R) (I : Ideal R) (φ : I →ₗ[R] M) :
    CommSq (ModuleCat.ofHom I.subtype) (ModuleCat.ofHom φ)
      (baerModuleIdealLift R M I φ) (baerModuleStepInclusion R M) := sorry

end

/-! ### Theorem_19_2_8 (from Chap19) -/
open CategoryTheory
open CategoryTheory.SmallObject
open CategoryTheory.SmallObject.SuccStruct

universe u

section

variable (R : Type u) [Ring R]

/-- The successor structure on `ModuleCat R ⥤ ModuleCat R` determined by the one-step Baer
construction `M ↦ 𝐌(M)`. -/
private noncomputable abbrev baerModuleTransfiniteSuccStruct :
    SuccStruct (ModuleCat R ⥤ ModuleCat R) :=
  SuccStruct.ofNatTrans (baerModuleStepInclusionNatTrans R)

/-- The zeroth object of the transfinite Baer successor structure is the identity functor on
`ModuleCat R`. -/
@[simp]
private theorem baerModuleTransfiniteSuccStruct_X₀ :
    (baerModuleTransfiniteSuccStruct R).X₀ = 𝟭 (ModuleCat R) :=
  rfl

/-- The transfinite Baer functor `N ↦ \mathbf{M}_α(N)`. -/
noncomputable def baerModuleTransfiniteFunctor (α : Ordinal.{u}) :
    ModuleCat R ⥤ ModuleCat R :=
  if hα : α = 0 then
    𝟭 (ModuleCat R)
  else
    letI := Ordinal.toTypeOrderBot hα
    (baerModuleTransfiniteSuccStruct R).iteration α.ToType

notation:max "𝐌_[" α "](" N ")" => Functor.obj (baerModuleTransfiniteFunctor _ α) N

-- Proof sketch: unfold `baerModuleTransfiniteFunctor`; when `α = 0`, the defining `if` chooses the
-- identity functor branch.
/-- At ordinal `0`, the transfinite Baer functor is the identity functor on `ModuleCat R`. -/
private theorem baerModuleTransfiniteFunctor_eq_id (α : Ordinal.{u}) (hα : α = 0) :
    baerModuleTransfiniteFunctor R α = 𝟭 (ModuleCat R) := sorry

-- Proof sketch: unfold `baerModuleTransfiniteFunctor`; when `α ≠ 0`, the defining `if` chooses the
-- branch given by the transfinite iteration of the one-step Baer successor structure over
-- `α.ToType`.
/-- For `α ≠ 0`, the transfinite Baer functor is the standard transfinite iteration of the
one-step Baer successor structure over `α.ToType`. -/
private theorem baerModuleTransfiniteFunctor_eq_iteration (α : Ordinal.{u}) (hα : α ≠ 0) :
    baerModuleTransfiniteFunctor R α =
      letI := Ordinal.toTypeOrderBot hα
      (baerModuleTransfiniteSuccStruct R).iteration α.ToType := sorry

/-- The canonical natural transformation `N ⟶ \mathbf{M}_α(N)`. -/
noncomputable def baerModuleTransfiniteInclusion (α : Ordinal.{u}) :
    𝟭 (ModuleCat R) ⟶ baerModuleTransfiniteFunctor R α :=
  if hα : α = 0 then
    eqToHom (baerModuleTransfiniteFunctor_eq_id R α hα).symm
  else
    letI := Ordinal.toTypeOrderBot hα
    eqToHom (baerModuleTransfiniteSuccStruct_X₀ R).symm ≫
      (baerModuleTransfiniteSuccStruct R).ιIteration α.ToType ≫
        eqToHom (baerModuleTransfiniteFunctor_eq_iteration R α hα).symm

notation:max "ι_𝐌[" α "](" N ")" => NatTrans.app (baerModuleTransfiniteInclusion _ α) N

private noncomputable def baerModuleTransfiniteArrowFunctor (α : Ordinal.{u}) :
    ModuleCat R ⥤ Arrow (ModuleCat R) :=
  (baerModuleTransfiniteInclusion R α).arrowFunctor

-- Proof sketch: each successor map `\mathbf{M}_β(N) ⟶ \mathbf{M}_{β + 1}(N)` is injective by
-- Lemma `19.2.7 (2)`, and the transfinite stage `N ⟶ \mathbf{M}_α(N)` is obtained by composing
-- these injections and taking the canonical maps into limit-stage colimits.
/-- For every `R`-module `N`, the canonical map `N ⟶ \mathbf{M}_α(N)` is injective. -/
theorem baerModuleTransfiniteInclusion_app_injective
    (α : Ordinal.{u}) (N : ModuleCat R) :
    Function.Injective (ι_𝐌[α](N)).hom := sorry

-- Proof sketch: use Baer's criterion. Given an ideal map `I ⟶ \mathbf{M}_α(N)`, apply
-- Proposition `19.2.5` to the module `I` to factor it through some earlier stage
-- `\mathbf{M}_β(N)` with `β < α`, then use Lemma `19.2.7 (3)` to extend it across
-- `I ↪ R` into `\mathbf{M}_{β + 1}(N) ⟶ \mathbf{M}_α(N)`.
/-- If the cofinality of `α` is larger than the cardinality of the set of ideals of `R`, then
`\mathbf{M}_α(N)` is an injective `R`-module. -/
theorem baerModuleTransfiniteFunctor_obj_injective
    (α : Ordinal.{u}) (hα : Cardinal.mk (Ideal R) < α.cof) (N : ModuleCat R) :
    Injective (𝐌_[α](N)) := sorry

/-- Theorem 19.2.8: if the cofinality of `α` is strictly larger than the cardinality of the set of
ideals of `R`, then the transfinite Baer construction `N ↦ \mathbf{M}_α(N)` together with the
canonical maps `N ⟶ \mathbf{M}_α(N)` yields functorial injective embeddings of `R`-modules. -/
@[reducible]
noncomputable def baerModule_hasFunctorialInjectiveEmbeddings
    (α : Ordinal.{u}) (hα : Cardinal.mk (Ideal R) < α.cof) :
    HasFunctorialInjectiveEmbeddings (ModuleCat R) where
  J := baerModuleTransfiniteArrowFunctor R α
  leftFunc_comp_J := NatTrans.arrowFunctor_leftFunc_comp _
  mono_obj N := (ModuleCat.mono_iff_injective _).mpr
    (baerModuleTransfiniteInclusion_app_injective R α N)
  injective_obj N := baerModuleTransfiniteFunctor_obj_injective R α hα N

end
