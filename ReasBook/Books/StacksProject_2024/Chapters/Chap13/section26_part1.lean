import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_13_26_1 (from Chap13) -/
universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Definition 13.26.1:
- primary domain: filtered objects in an abelian category, specialized to the full subcategory of
  finite filtered objects;
- sampled owner declarations:
  `Injective`,
  `CochainComplex.IsKInjective`,
  `IsFilteredInjective`,
  `gr^{p}`,
  `finiteFilteredObjectCat`;
- owner abstraction: the source-facing owner is the class `IsFilteredInjective` on `Fil^f(𝒜)`,
  not a new wrapper on ambient filtered objects;
- source/core/bridge triage:
  `source-facing`: filtered injective objects of `Fil^f(𝒜)`;
  `core/canonical`: the existing chapter class owner `IsFilteredInjective`;
  `bridge/view`: the graded-piece characterization built into that owner.

This item is therefore a pure canonical-recall entry: the textbook definition already matches the
existing chapter owner exactly, so the file should recall that owner directly rather than
reintroducing a duplicate alias or `_iff` wrapper. -/

/- Definition 13.26.1: for an abelian category `𝒜`, an object `I` of `Fil^f(𝒜)` is filtered
injective when each graded piece `gr^p(I)` is an injective object of `𝒜`. The chapter owner is
the class `IsFilteredInjective`. -/
recall IsFilteredInjective

end CategoryTheory

/-! ### Lemma_13_26_2 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory

/- Domain-style sampling for Lemma `13.26.2`.
- primary domain: finite filtered objects in an abelian category and their interval-indexed split
  biproduct presentations;
- sampled owner declarations:
  `DecreasingFiltration`,
  `FilteredObject`,
  `FilteredObject.IsFinite`,
  `finiteFilteredObjectCat`,
  `Set.Icc`,
  `biproduct.fromSubtype`;
- best owner abstraction: the Chapter `12` owner `FilteredObject 𝒜`, with the tail stages first
  assembled as a `DecreasingFiltration`;
- primitive data: an interval-indexed family `J : Set.Icc a b → 𝒜`;
- derived API: the tail filtration, the associated finite filtered object, and the filtered-
  injective decomposition theorem.

Source/core/bridge triage:
- `source-facing`: the characterization of filtered injective finite filtered objects by an
  interval-indexed split model;
- `core/canonical`: `DecreasingFiltration`, `FilteredObject`, `FilteredObject.IsFinite`, and
  `Fil^f(𝒜)`;
- `bridge/view`: the interval-tail filtration and the resulting bridge object
  `intervalSplitFilteredObject`. -/

section IntervalSplit

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜] [HasZeroObject 𝒜]
  [HasFiniteBiproducts 𝒜]
variable (a b : ℤ) (J : Set.Icc a b → 𝒜)

/-- The tail direct sum stage inside the interval-indexed biproduct. -/
private noncomputable def intervalTailSubobject (p : ℤ) :
    Subobject (⨁ J) :=
  by
    letI : IsSplitMono (biproduct.fromSubtype J fun i ↦ p ≤ i.1) :=
      IsSplitMono.mk'
        { retraction := biproduct.toSubtype J fun i ↦ p ≤ i.1
          id := biproduct.fromSubtype_toSubtype J fun i ↦ p ≤ i.1 }
    exact Subobject.mk (biproduct.fromSubtype J fun i ↦ p ≤ i.1)

-- Proof sketch: if `p ≤ q`, then every summand with index at least `q` also has index at least
-- `p`, so the tail direct sums define a decreasing filtration. Equivalently, the assignment is
-- monotone on the order-dual integers.
/-- The tail filtration on the biproduct indexed by the interval `[a, b]` is monotone on `ℤᵒᵈ`.
-/
private theorem intervalTailFiltration_monotone :
    Monotone (fun p : ℤᵒᵈ ↦ intervalTailSubobject a b J p) := sorry

/-- The decreasing filtration on the interval biproduct whose `p`-th stage is the tail direct sum
over indices `q ≥ p`. -/
noncomputable def intervalTailFiltration :
    DecreasingFiltration (⨁ J) :=
  { toFun := fun p ↦ intervalTailSubobject a b J p
    monotone' := intervalTailFiltration_monotone a b J }

-- Proof sketch: the stage at `b + 1` is the empty tail direct sum, hence zero, while the stage at
-- `a` contains every summand in the interval and hence is the whole biproduct.
/-- The interval-split filtered object has finite filtration. -/
private theorem intervalSplitFilteredObject_isFinite :
    ({ obj := ⨁ J
       filtration := intervalTailFiltration a b J } : FilteredObject 𝒜).IsFinite := sorry

/-- The finite filtered object attached to an interval-indexed family of summands. -/
noncomputable def intervalSplitFilteredObject :
    Fil^f(𝒜) :=
  ⟨{ obj := ⨁ J
     filtration := intervalTailFiltration a b J },
    intervalSplitFilteredObject_isFinite a b J⟩

-- Proof sketch: this is the defining formula of `intervalSplitFilteredObject`.
/-- The stage `F^{p}` of `intervalSplitFilteredObject` is the tail direct sum over the summands
with index at least `p`. -/
@[simp]
theorem intervalSplitFilteredObject_filtration_obj (a b p : ℤ) (J : Set.Icc a b → 𝒜) :
    F^{p} ((intervalSplitFilteredObject a b J).obj) = intervalTailFiltration a b J p := rfl

end IntervalSplit

section FilteredInjective

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local instance : HasFiniteBiproducts 𝒜 := Abelian.hasFiniteBiproducts

-- Proof sketch: if `I` is filtered injective, each graded piece is injective, and the finite
-- filtration splits into interval-indexed injective graded summands. Conversely, the graded pieces
-- of the interval-split model are exactly those injective summands.
/-- Lemma 13.26.2: a finite filtered object is filtered injective if and only if it is
isomorphic to a finite direct sum of injective objects indexed by an interval, equipped with the
tail filtration.
-/
theorem isFilteredInjective_iff_exists_iso_intervalSplitFilteredObject
    (I : Fil^f(𝒜)) :
    IsFilteredInjective I ↔
      ∃ a b : ℤ,
        ∃ J : Set.Icc a b → 𝒜,
          ∃ e : I ≅ intervalSplitFilteredObject a b J, ∀ n, Injective (J n) := sorry

end FilteredInjective

end CategoryTheory

/-! ### Lemma_13_26_3 (from Chap13) -/
open CategoryTheory
open FilteredObject.Hom
open scoped CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "FilF" => Fil^f(𝒜)

/- Domain-style sampling for Lemma `13.26.3`.
- primary domain: finite filtered objects and strict monomorphisms in an abelian category;
- sampled owner declarations:
  `finiteFilteredObjectCat`,
  `Injective`,
  `CochainComplex.PlusWithTermsIn`,
  `CochainComplex.FilteredInjectivePlus`,
  `CochainComplex.IsKInjective`,
  `FilteredObject.Hom.Strict`,
  `gr^{p}`;
- best owner abstraction: the source-facing chapter owner is `finiteFilteredObjectCat 𝒜` with
  notation `Fil^f(𝒜)` for finite filtered objects, and filtered injectivity should be owned by a
  reusable class parallel to `Injective` and `CochainComplex.IsKInjective`; the bounded-below
  filtered-injective cochain complexes are then canonically owned by
  `CochainComplex.FilteredInjectivePlus 𝒜`;
- primitive data: a finite filtered object `I : FilF`;
- derived API: the split-mono theorem for strict monomorphisms out of a filtered-injective source;
- source/core/bridge triage:
  `source-facing`: filtered injectivity on `FilF` and the split-mono theorem;
  `core/canonical`: the class owner `IsFilteredInjective`, together with
    `FilteredObject.Hom.Strict`;
  `bridge/view`: the graded-piece characterization built directly into `IsFilteredInjective`. -/

/-- A finite filtered object is filtered injective if each of its graded pieces is injective in
the ambient abelian category. -/
class IsFilteredInjective (I : FilF) : Prop where
  injective (p : ℤ) : Injective (gr^{p} I.obj)

attribute [instance] IsFilteredInjective.injective

namespace CochainComplex

/-- The bounded-below cochain complexes of finite filtered objects whose terms are filtered
injective. -/
abbrev FilteredInjectivePlus (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :=
  CochainComplex.PlusWithTermsIn
    (IsFilteredInjective : ObjectProperty FilF)

end CochainComplex

namespace IsFilteredInjective

-- Proof sketch: choose the largest filtration index with nonzero graded piece, use strictness and
-- Lemma 12.19.13 to obtain a monomorphism on the top graded piece, split that monomorphism by
-- injectivity of the graded piece, decompose source and target into that top piece and its kernel,
-- and conclude by induction on the finite filtration length of `I`.
/-- Lemma 13.26.3: if `u : I.obj ⟶ A` is a strict monomorphism in `Fil(𝒜)` with finite filtered-
injective source `I : Fil^f(𝒜)`, then `u` is a split injection. -/
theorem isSplitMono_of_strict
    {I : FilF} {A : FilteredObject 𝒜} (u : I.obj ⟶ A) [IsFilteredInjective I] [Mono u]
    (hu : Strict u) :
    IsSplitMono u := sorry

end IsFilteredInjective

end CategoryTheory

/-! ### Lemma_13_26_4 (from Chap13) -/
noncomputable section

universe u v

namespace CategoryTheory

open FilteredObject.Hom
open scoped CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Lemma `13.26.4`.
- primary domain: strict monomorphisms of finite filtered objects and extension into filtered
  injectives;
- sampled owner declarations:
  `FilteredObject.Hom.Strict`,
  `IsFilteredInjective`,
  `Injective.factors`,
  `Injective.factorThru`,
  `Injective.comp_factorThru`;
- best owner abstraction: the chapter owner `IsFilteredInjective`, with the source-facing
  extension theorem modeled on the theorem-level owner `Injective.factors`; unlike ordinary
  injective objects, no canonical filtered factorization morphism is available here, so the public
  API should stay existential rather than introducing a chosen witness;
- primitive data: a strict monomorphism `u : A ⟶ B` in `Fil^f(𝒜)`, a map `f : A ⟶ I`, and a
  filtered-injective target `I`;
- derived API: only the theorem-level factorization statement below;
- source/core/bridge triage:
  `source-facing`: extension of a morphism across a strict monomorphism in `Fil^f(𝒜)`;
  `core/canonical`: `Strict` and `IsFilteredInjective`;
  `bridge/view`: the theorem below, which is the filtered analogue of `Injective.factors`.
-/

namespace IsFilteredInjective

/-- Lemma 13.26.4: a morphism from the source of a strict monomorphism in `Fil^f(𝒜)` to a
filtered injective object factors through that strict monomorphism. -/
theorem factors
    {A B I : Fil^f(𝒜)} [IsFilteredInjective I] (f : A ⟶ I) (u : A ⟶ B) [Mono u]
    (hu : Strict u.hom) :
    ∃ g : B ⟶ I, u ≫ g = f := by
  sorry

end IsFilteredInjective

end CategoryTheory

/-! ### Lemma_13_26_5 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open FilteredObject.Hom
open scoped CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]

section FilteredInjectives

/-- The strictly full subcategory `𝓘^f ⊂ Fil^f(𝒜)` of filtered injective objects. -/
abbrev filteredInjectiveSubcategory (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :=
  ObjectProperty.FullSubcategory (IsFilteredInjective : ObjectProperty (Fil^f(𝒜)))

/- The Stacks Project writes the full subcategory of filtered injective finite filtered objects as
`𝓘^f(𝒜)`. This is notation for the chapter owner `filteredInjectiveSubcategory 𝒜`. -/
scoped notation "𝓘^f(" C:arg ")" => filteredInjectiveSubcategory C

instance (I : 𝓘^f(𝒜)) : IsFilteredInjective I.obj :=
  I.property

/-- The inclusion `𝓘^f(𝒜) ⥤ Fil^f(𝒜)` forgetting that an object is filtered injective. -/
abbrev filteredInjectiveInclusion (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    𝓘^f(𝒜) ⥤ Fil^f(𝒜) :=
  ObjectProperty.ι (IsFilteredInjective : ObjectProperty (Fil^f(𝒜)))

end FilteredInjectives

/- Domain-style sampling for Lemma `13.26.5`.
- primary domain: finite filtered objects, strict monomorphisms, and filtered-injective targets in
  an abelian category with enough injectives;
- sampled owner declarations:
  `FilteredObject.Hom.Strict`,
  `IsFilteredInjective`,
  `filteredInjectiveSubcategory`,
  `IsFilteredInjective.isSplitMono_of_strict`,
  `EnoughInjectives.presentation`;
- best owner abstraction: the source-facing category owners `Fil^f(𝒜)` and `𝓘^f(𝒜)` together
  with the canonical inclusion `filteredInjectiveInclusion 𝒜`; the ambient
  monomorphism-into-injective data comes from the canonical mathlib owner
  `EnoughInjectives.presentation`;
- primitive data: a finite filtered object `A`;
- derived API: a strict monomorphism from `A` into an object of `𝓘^f(𝒜)`;
- source/core/bridge triage:
  `source-facing`: the existence of a strict monomorphism in `Fil^f(𝒜)` into a filtered
    injective object;
  `core/canonical`: `Fil^f(𝒜)`, `𝓘^f(𝒜)`, `filteredInjectiveInclusion`, `Strict`,
    `IsFilteredInjective`, and `EnoughInjectives.presentation`;
  `bridge/view`: the existence theorem below, which upgrades enough injectives in `𝒜` to a
    strict filtered embedding in `Fil^f(𝒜)`.

The target theorem should therefore stay a source-facing existence statement, but its surface
should reuse the chapter notations `Fil^f(𝒜)` and `𝓘^f(𝒜)` and the owner predicate `Strict`
directly rather than spelling parallel long forms or exposing the filtered-injective witness as a
separate proof argument. -/

-- Proof sketch: choose bounds for the finite filtration of `A`, embed each quotient
-- `A.obj.obj / F^{n + 1}A` into an injective object of `𝒜`, and assemble these maps into a
-- morphism from `A` to the finite direct sum equipped with the tail filtration. The resulting
-- codomain is filtered injective, and the componentwise construction makes the map a strict
-- monomorphism.
/-- Lemma 13.26.5: every object of `Fil^f(𝒜)` admits a strict monomorphism into a filtered
injective object. -/
theorem exists_strictMono_to_filteredInjective
    (A : Fil^f(𝒜)) :
    ∃ (I : 𝓘^f(𝒜)) (u : A ⟶ I.obj), Mono u ∧ Strict u.hom := sorry

end CategoryTheory

/-! ### Lemma_13_26_6 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.CochainComplex
open CochainComplex
open scoped CategoryTheory ZeroObject

noncomputable section

universe u v

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "FilF" => Fil^f(𝒜)

/-- A cochain complex in `Fil^f(𝒜)` has finite filtrations in every degree after forgetting to a
filtered complex. -/
theorem hasFiniteFiltrations (K : CochainComplex FilF ℤ) :
    CategoryTheory.FilteredComplex.HasFiniteFiltrations
      (((ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜)))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) := by
  intro n
  simpa using (K.X n).property

variable [Abelian (finiteFilteredObjectCat 𝒜)]

/-- A morphism from a cochain complex in `Fil^f(𝒜)` to a bounded-below filtered-injective complex
is a filtered quasi-isomorphism with termwise strict monomorphisms if it is bounded below, each
component is monic, the induced map on associated graded complexes is a quasi-isomorphism, and
each degree component is strict in `Fil(𝒜)`. -/
structure IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso
    (a : ℤ) {K : CochainComplex FilF ℤ}
    (I : CategoryTheory.CochainComplex.FilteredInjectivePlus 𝒜)
    (α : K ⟶ ((_root_.CochainComplex.PlusWithTermsIn.ι
      (IsFilteredInjective : ObjectProperty FilF)).obj I)) : Prop
    extends IsTermwiseMonoStrictlyGEWithTermsIn
      (IsFilteredInjective : ObjectProperty FilF) a
      (show _root_.CochainComplex.PlusWithTermsIn
        (IsFilteredInjective : ObjectProperty FilF) from I) α where
  quasiIso :
    QuasiIso ((finiteFilteredObjectAssociatedGradedCochainFunctor 𝒜).map α)
  term_strict (n : ℤ) : FilteredObject.Hom.Strict (α.f n).hom

namespace IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso

-- Proof sketch: forget the filtration to the associated graded complexes, where `hα.quasiIso`
-- makes `α` a quasi-isomorphism and `hα.term_mono` gives termwise monomorphy. Apply the ordinary
-- bounded-below injective lifting theorem degreewise on graded pieces and then reassemble the
-- lift using the strictness hypotheses `hα.term_strict`.
/-- A filtered quasi-isomorphism with termwise strict monomorphisms into a bounded-below complex of
filtered injectives admits strict lifts against any bounded-below filtered-injective target. -/
theorem exists_strict_lift_to_boundedBelow_filteredInjective
    {a : ℤ} {K : CochainComplex FilF ℤ}
    {I J : CategoryTheory.CochainComplex.FilteredInjectivePlus 𝒜}
    {α : K ⟶ ((_root_.CochainComplex.PlusWithTermsIn.ι
      (IsFilteredInjective : ObjectProperty FilF)).obj I)}
    (hα : IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso a I α)
    (γ : K ⟶ ((_root_.CochainComplex.PlusWithTermsIn.ι
      (IsFilteredInjective : ObjectProperty FilF)).obj J)) :
    ∃ β :
      ((_root_.CochainComplex.PlusWithTermsIn.ι
        (IsFilteredInjective : ObjectProperty FilF)).obj I) ⟶
        ((_root_.CochainComplex.PlusWithTermsIn.ι
          (IsFilteredInjective : ObjectProperty FilF)).obj J),
      α ≫ β = γ := by
  sorry

end IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso

end CochainComplex

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]

namespace CochainComplex.FilteredInjectivePlus

/- Domain-style sampling for Lemma `13.26.6`.
- primary domain: filtered cochain complexes in an abelian category, with the degree-zero
  embedding of finite filtered objects and bounded-below filtered-injective replacements;
- sampled owner declarations:
  `CochainComplex.FilteredInjectivePlus`,
  `CochainComplex.singleFunctor`,
  `IsTermwiseMonoStrictlyGEWithTermsIn`,
  `CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso`,
  `finiteFilteredObjectAssociatedGradedCochainFunctor`,
  `FilteredObject.Hom.Strict`;
- best owner abstraction: the bounded-below filtered-injective target is owned by
  `CochainComplex.FilteredInjectivePlus 𝒜`, while the primitive comparison-map owner is the
  generic bounded-below termwise-monomorphic datum
  `IsTermwiseMonoStrictlyGEWithTermsIn (IsFilteredInjective : ObjectProperty FilF)`; the
  source-facing filtered enhancement is canonically owned by
  `CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso`, which extends that primitive
  owner by the associated-graded quasi-isomorphism and degreewise strictness;
- primitive data: a finite filtered object `A : Fil^f(𝒜)`;
- derived API: the degree-zero cochain complex `(singleFunctor FilF (0 : ℤ)).obj A`, the generic
  forgetful bridge
  `((ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜)))).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj` from cochain complexes in `Fil^f(𝒜)` to `FilteredComplex 𝒜`, the
  induced theorem `CochainComplex.hasFiniteFiltrations`, and the source-facing existence theorem
  below, exposed on `CochainComplex.FilteredInjectivePlus`;
- source/core/bridge triage:
    `source-facing`: the source object `(singleFunctor FilF (0 : ℤ)).obj A` and the existence
      theorem below;
  `core/canonical`: `CochainComplex.FilteredInjectivePlus`,
    `CochainComplex.singleFunctor`,
    `IsTermwiseMonoStrictlyGEWithTermsIn`,
    `CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso`,
    `((ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜)))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj`,
    `CochainComplex.hasFiniteFiltrations`,
    `finiteFilteredObjectAssociatedGradedCochainFunctor`, and `FilteredObject.Hom.Strict`;
  `bridge/view`: the canonical coercion from `CochainComplex.FilteredInjectivePlus 𝒜` to
    `CochainComplex (Fil^f(𝒜)) ℤ`, and the generic forgetful bridge
    `((ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜)))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj`. -/

local notation "FilF" => Fil^f(𝒜)
local notation "FiltInjPlus" => CochainComplex.FilteredInjectivePlus 𝒜
variable (A : FilF)

/-- Helper for Lemma 13.26.6: the zero finite filtered object is filtered injective. -/
private instance filteredInjective_zero : IsFilteredInjective (0 : FilF) where
  injective p := by
    let G : FilF ⥤ 𝒜 := finiteFilteredObjectAssociatedGradedFunctor 𝒜 ⋙ GradedObject.eval p
    simpa [G] using (Functor.map_isZero G (Limits.isZero_zero FilF)).injective

/-- Helper for Lemma 13.26.6: filtered injectivity is preserved under isomorphism in
`Fil^f(𝒜)`. -/
private theorem isFilteredInjective_of_iso {X Y : FilF} (e : X ≅ Y) [IsFilteredInjective X] :
    IsFilteredInjective Y where
  injective p := by
    let G : FilF ⥤ 𝒜 := finiteFilteredObjectAssociatedGradedFunctor 𝒜 ⋙ GradedObject.eval p
    simpa [G] using Injective.of_iso (Functor.mapIso G e)
      (inferInstance : Injective (gr^{p} X.obj))

/-- Helper for Lemma 13.26.6: the object property of filtered injectives contains the zero object
of `Fil^f(𝒜)`. -/
private instance filteredInjective_containsZero :
    ObjectProperty.ContainsZero (IsFilteredInjective : ObjectProperty FilF) where
  exists_zero := by
    -- The zero filtered object is already known to be filtered injective degreewise.
    exact ⟨(0 : FilF), Limits.isZero_zero _, inferInstance⟩

/-- Helper for Lemma 13.26.6: every finite filtered object admits a monomorphism into a filtered
injective object. -/
private instance filteredInjective_hasMonoEmbedding :
    ObjectProperty.HasMonoEmbedding (IsFilteredInjective : ObjectProperty FilF) where
  exists_mono X := by
    -- Forget the strictness witness from Lemma `13.26.5`; the generic resolution theorem only
    -- needs an ambient monomorphism into the object property.
    obtain ⟨I, u, hu_mono, _hu_strict⟩ :=
      exists_strictMono_to_filteredInjective (𝒜 := 𝒜) X
    exact ⟨I.obj, I.property, u, hu_mono⟩

/-- Helper for Lemma 13.26.6: package a chosen strict embedding of the cokernel of a morphism
into a filtered injective object. -/
private structure StrictCokernelEmbedding {X Y : FilF} (f : X ⟶ Y) where
  next : FilF
  next_injective : IsFilteredInjective next
  lift : cokernel f ⟶ next
  lift_mono : Mono lift
  lift_strict : FilteredObject.Hom.Strict lift.hom

attribute [instance] StrictCokernelEmbedding.next_injective

/-- Helper for Lemma 13.26.6: every cokernel in `Fil^f(𝒜)` admits a strict monomorphism into a
filtered injective object. -/
private theorem exists_strictCokernelEmbedding {X Y : FilF} (f : X ⟶ Y) :
    Nonempty (StrictCokernelEmbedding f) := by
  -- Reapply Lemma `13.26.5` to the next cokernel in the recursive construction.
  obtain ⟨I, u, hu_mono, hu_strict⟩ :=
    exists_strictMono_to_filteredInjective (𝒜 := 𝒜) (cokernel f)
  exact ⟨⟨I.obj, I.property, u, hu_mono, hu_strict⟩⟩

/-- Helper for Lemma 13.26.6: fix a filtered-injective target for the cokernel of a morphism. -/
private noncomputable def strictCokernelEmbedding {X Y : FilF} (f : X ⟶ Y) :
    StrictCokernelEmbedding f :=
  Classical.choice (exists_strictCokernelEmbedding (𝒜 := 𝒜) f)

/-- Helper for Lemma 13.26.6: the next differential is obtained by composing the cokernel map
with the chosen strict cokernel embedding. -/
private noncomputable def strictCokernelDifferential {X Y : FilF} (f : X ⟶ Y) :
    Y ⟶ (strictCokernelEmbedding f).next :=
  cokernel.π f ≫ (strictCokernelEmbedding f).lift

/-- Helper for Lemma 13.26.6: the recursive differential still composes to zero with the previous
morphism. -/
private theorem strictCokernelDifferential_comp_zero {X Y : FilF} (f : X ⟶ Y) :
    f ≫ strictCokernelDifferential (𝒜 := 𝒜) f = 0 := by
  -- The cokernel relation is exactly the recursion invariant for the next differential.
  simp [strictCokernelDifferential]

/-- Helper for Lemma 13.26.6: the explicit quotient-filtered cokernel of a morphism in `Fil^f(𝒜)`
again has finite filtration. -/
private theorem finite_cokernelFilteredObject_isFinite {X Y : FilF} (f : X ⟶ Y) :
    FilteredObject.IsFinite (FilteredObject.Hom.cokernelFilteredObject f.hom) := by
  -- TODO: prove finite filtration stagewise by rewriting the quotient filtration to the image of
  -- `cokernel.π f.hom.hom`, then use the eventual `⊤`/`⊥` bounds coming from `Y.property`.
  sorry

/-- Helper for Lemma 13.26.6: the explicit quotient-filtered cokernel can be viewed as an object of
`Fil^f(𝒜)`. -/
private noncomputable def finiteCokernelObject {X Y : FilF} (f : X ⟶ Y) : FilF :=
  ⟨FilteredObject.Hom.cokernelFilteredObject f.hom,
    finite_cokernelFilteredObject_isFinite (𝒜 := 𝒜) f⟩

/-- Helper for Lemma 13.26.6: the canonical quotient-filtered projection into the explicit finite
cokernel object. -/
private noncomputable def toFiniteCokernel {X Y : FilF} (f : X ⟶ Y) :
    Y ⟶ finiteCokernelObject (𝒜 := 𝒜) f :=
  ObjectProperty.homMk (FilteredObject.Hom.toCokernel f.hom)

/-- Helper for Lemma 13.26.6: the explicit quotient-filtered projection is a cokernel cofork. -/
private theorem toFiniteCokernel_comp_zero {X Y : FilF} (f : X ⟶ Y) :
    f ≫ toFiniteCokernel (𝒜 := 𝒜) f = 0 := by
  -- Forgetting to `Fil(𝒜)` reduces this to the ambient cokernel relation.
  ext
  simpa [toFiniteCokernel] using FilteredObject.Hom.comp_toCokernel f.hom

/-- Helper for Lemma 13.26.6: isomorphisms of filtered objects are strict. -/
private theorem strict_of_iso {X Y : FilteredObject 𝒜} (e : X ≅ Y) :
    FilteredObject.Hom.Strict e.hom := by
  -- TODO: rewrite the stagewise image through the isomorphism and use that `e.hom.hom` has image
  -- `⊤`; the previous direct `imageSubobject_le_mk` proof was not type-correct.
  sorry

/-- Helper for Lemma 13.26.6: the quotient-filtered cokernel projection is strict in the ambient
filtered-object category. -/
private theorem strict_toFiniteCokernel {X Y : FilF} (f : X ⟶ Y) :
    FilteredObject.Hom.Strict (toFiniteCokernel (𝒜 := 𝒜) f).hom := by
  -- TODO: after identifying the target filtration with the quotient filtration coming from
  -- `FilteredObject.Hom.toCokernel`, apply `strict_iff_quotient_eq_inf` directly.
  sorry

/-- Helper for Lemma 13.26.6: the explicit quotient-filtered cokernel satisfies the cokernel
universal property already inside `Fil^f(𝒜)`. -/
private noncomputable def finiteCokernel_isColimit {X Y : FilF} (f : X ⟶ Y) :
    IsColimit
      (CokernelCofork.ofπ (toFiniteCokernel (𝒜 := 𝒜) f)
        (toFiniteCokernel_comp_zero (𝒜 := 𝒜) f)) :=
  sorry

/-- Helper for Lemma 13.26.6: the categorical cokernel in `Fil^f(𝒜)` is canonically isomorphic to
the explicit quotient-filtered cokernel object. -/
private noncomputable def cokernel_iso_finiteCokernelObject {X Y : FilF} (f : X ⟶ Y) :
    cokernel f ≅ finiteCokernelObject (𝒜 := 𝒜) f :=
  sorry

/-- Helper for Lemma 13.26.6: the comparison isomorphism identifies the categorical cokernel
projection with the explicit quotient-filtered projection. -/
private theorem cokernel_π_comp_cokernel_iso_hom {X Y : FilF} (f : X ⟶ Y) :
    cokernel.π f ≫ (cokernel_iso_finiteCokernelObject (𝒜 := 𝒜) f).hom =
      toFiniteCokernel (𝒜 := 𝒜) f := by
  -- TODO: this is the projection-compatibility equation coming from the cokernel comparison iso.
  sorry

/-- Helper for Lemma 13.26.6: the cokernel projection in `Fil^f(𝒜)` is strict. -/
private theorem cokernel_π_hom_epi {X Y : FilF} (f : X ⟶ Y) :
    Epi ((cokernel.π f).hom.hom) := by
  -- TODO: transport the ambient epi fact for `FilteredObject.Hom.toCokernel f.hom` back along the
  -- comparison isomorphism from `cokernel_π_comp_cokernel_iso_hom`.
  sorry

/-- Helper for Lemma 13.26.6: the image of a composite with an epimorphism is the image of the
second morphism. -/
private theorem imageSubobject_comp_eq_of_epi {X Y Z : 𝒜} (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z) :
    imageSubobject (f ≫ g) = imageSubobject g := by
  calc
    imageSubobject (f ≫ g) = imageSubobject ((imageSubobject f).arrow ≫ g) := by
      rw [CategoryTheory.Limits.imageSubobject_comp_eq_imageSubobject_restriction f g]
    _ = imageSubobject (((⊤ : Subobject Y)).arrow ≫ g) := by
      simpa using congrArg (fun S : Subobject Y ↦ imageSubobject (S.arrow ≫ g))
        (Limits.imageSubobject_eq_top_of_epi f)
    _ = imageSubobject g := by
      simpa using
        (CategoryTheory.Limits.imageSubobject_iso_comp ((⊤ : Subobject Y).arrow) g)

/-- Helper for Lemma 13.26.6: quotient filtrations compose through an epimorphism. -/
private theorem quotient_comp_eq_quotient_of_quotient
    {X Y Z : FilteredObject 𝒜} (f : X ⟶ Y) (g : Y ⟶ Z) (i : ℤ) :
    X.filtration.quotient (f.hom ≫ g.hom) i =
      (X.filtration.quotient f.hom).quotient g.hom i := by
  -- Both sides are computed by the image of the same composite through the cokernel tower.
  rw [DecreasingFiltration.quotient_eq_imageSubobject_comp,
    DecreasingFiltration.quotient_eq_imageSubobject_comp]
  rw [DecreasingFiltration.quotient_eq_imageSubobject_comp]
  simpa [Category.assoc] using
    (CategoryTheory.Limits.imageSubobject_comp_eq_imageSubobject_restriction
      ((X.filtration i).arrow ≫ f.hom) g.hom)

/-- Helper for Lemma 13.26.6: a strict epimorphism identifies the quotient filtration with the
target filtration. -/
private theorem quotient_filtration_eq_of_strict_epi {X Y : FilteredObject 𝒜}
    (f : X ⟶ Y) [Epi f.hom] (hf : FilteredObject.Hom.Strict f) :
    X.filtration.quotient f.hom = Y.filtration := by
  apply OrderHom.ext
  funext i
  calc
    X.filtration.quotient f.hom i = imageSubobject f.hom ⊓ Y.filtration i := by
      exact (FilteredObject.Hom.strict_iff_quotient_eq_inf f).1 hf i
    _ = (⊤ : Subobject Y.obj) ⊓ Y.filtration i := by
      rw [Limits.imageSubobject_eq_top_of_epi f.hom]
    _ = Y.filtration i := by simp

/-- Helper for Lemma 13.26.6: the composite of a strict epimorphism with a strict morphism is
strict. -/
private theorem strict_comp_of_epi {X Y Z : FilteredObject 𝒜}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Epi f.hom] (hf : FilteredObject.Hom.Strict f)
    (hg : FilteredObject.Hom.Strict g) :
    FilteredObject.Hom.Strict (f ≫ g) := by
  refine (FilteredObject.Hom.strict_iff_quotient_eq_inf (f ≫ g)).2 ?_
  intro i
  calc
    X.filtration.quotient (f.hom ≫ g.hom) i
        = (X.filtration.quotient f.hom).quotient g.hom i :=
            quotient_comp_eq_quotient_of_quotient f g i
    _ = Y.filtration.quotient g.hom i := by
          rw [quotient_filtration_eq_of_strict_epi f hf]
    _ = imageSubobject g.hom ⊓ Z.filtration i := by
          exact (FilteredObject.Hom.strict_iff_quotient_eq_inf g).1 hg i
    _ = imageSubobject (f.hom ≫ g.hom) ⊓ Z.filtration i := by
          rw [imageSubobject_comp_eq_of_epi f.hom g.hom]

/-- Helper for Lemma 13.26.6: the cokernel projection in `Fil^f(𝒜)` is strict. -/
private theorem strict_cokernel_π {X Y : FilF} (f : X ⟶ Y) :
    FilteredObject.Hom.Strict (cokernel.π f).hom := by
  -- TODO: after the cokernel comparison iso is proved, rewrite `(cokernel f).obj.filtration`
  -- through that iso and transport `strict_toFiniteCokernel` back to `(cokernel.π f).hom`.
  sorry

/-- Helper for Lemma 13.26.6: the recursive cokernel differential is strict. -/
private theorem strict_strictCokernelDifferential {X Y : FilF} (f : X ⟶ Y) :
    FilteredObject.Hom.Strict (strictCokernelDifferential (𝒜 := 𝒜) f).hom := by
  letI : Epi ((cokernel.π f).hom.hom) := cokernel_π_hom_epi (𝒜 := 𝒜) f
  -- The recursive differential is the composite of the strict ambient cokernel projection with the
  -- chosen strict monomorphism from that cokernel.
  exact
    strict_comp_of_epi (cokernel.π f).hom (strictCokernelEmbedding f).lift.hom
      (strict_cokernel_π (𝒜 := 𝒜) f) (strictCokernelEmbedding f).lift_strict

/-- Helper for Lemma 13.26.6: the nat-indexed recursive resolution built from successive strict
cokernel embeddings. -/
private noncomputable def recursiveResolutionNat {A I₀ : FilF} [IsFilteredInjective I₀]
    (u₀ : A ⟶ I₀) : CochainComplex FilF ℕ :=
  CochainComplex.mk' I₀ (strictCokernelEmbedding u₀).next
    (strictCokernelDifferential (𝒜 := 𝒜) u₀)
    (fun {_ _} f ↦
      ⟨(strictCokernelEmbedding f).next,
        strictCokernelDifferential (𝒜 := 𝒜) f,
        strictCokernelDifferential_comp_zero (𝒜 := 𝒜) f⟩)

/-- Helper for Lemma 13.26.6: the chosen degree-zero embedding annihilates the first recursive
differential. -/
private theorem recursiveResolutionNatAugmentation_comp_zero {A I₀ : FilF}
    [IsFilteredInjective I₀] (u₀ : A ⟶ I₀) :
    u₀ ≫ (recursiveResolutionNat (𝒜 := 𝒜) u₀).d 0 1 = 0 := by
  -- The first differential was defined from the cokernel of `u₀`.
  simpa [recursiveResolutionNat] using
    strictCokernelDifferential_comp_zero (𝒜 := 𝒜) u₀

/-- Helper for Lemma 13.26.6: the augmentation into the nat-indexed recursive resolution is the
chosen strict degree-zero embedding. -/
private noncomputable def recursiveResolutionNatAugmentation {A I₀ : FilF} [IsFilteredInjective I₀]
    (u₀ : A ⟶ I₀) :
    (CochainComplex.single₀ FilF).obj A ⟶ recursiveResolutionNat (𝒜 := 𝒜) u₀ :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨u₀, recursiveResolutionNatAugmentation_comp_zero (𝒜 := 𝒜) u₀⟩

/-- Helper for Lemma 13.26.6: the nat-indexed augmentation has component `u₀` in degree `0`. -/
private theorem recursiveResolutionNatAugmentation_f_zero {A I₀ : FilF} [IsFilteredInjective I₀]
    (u₀ : A ⟶ I₀) :
    (recursiveResolutionNatAugmentation (𝒜 := 𝒜) u₀).f 0 = u₀ := by
  -- `fromSingle₀Equiv` is normalized so that the degree-zero component is the chosen map.
  simp [recursiveResolutionNatAugmentation]

/-- Helper for Lemma 13.26.6: the recursive nat-indexed resolution is extended to an
`ℤ`-indexed bounded-below complex by `embeddingUpNat`. -/
private noncomputable def recursiveResolution {A I₀ : FilF} [IsFilteredInjective I₀]
    (u₀ : A ⟶ I₀) : CochainComplex FilF ℤ :=
  (recursiveResolutionNat (𝒜 := 𝒜) u₀).extend ComplexShape.embeddingUpNat

/-- Helper for Lemma 13.26.6: the recursive nat-resolution identifies its successor term with the
chosen filtered-injective target for the preceding differential. -/
private theorem recursiveResolutionNat_X_succ_succ {A I₀ : FilF} [IsFilteredInjective I₀]
    (u₀ : A ⟶ I₀) (n : ℕ) :
    ((recursiveResolutionNat (𝒜 := 𝒜) u₀).X (n + 2)) =
      (strictCokernelEmbedding
        ((recursiveResolutionNat (𝒜 := 𝒜) u₀).d n (n + 1))).next := by
  -- Unfold the recursive `mk'` constructor until the successor object appears explicitly.
  rw [recursiveResolutionNat, CochainComplex.mk']
  cases n with
  | zero =>
      rw [CochainComplex.mk_d_1_0]
      rfl
  | succ n =>
      rw [CochainComplex.mk, CochainComplex.of_d]
      simp [CochainComplex.mkAux]

/-- Helper for Lemma 13.26.6: every term of the nat-indexed recursive resolution is filtered
injective. -/
private theorem recursiveResolutionNat_term_filteredInjective {A I₀ : FilF}
    [IsFilteredInjective I₀] (u₀ : A ⟶ I₀) (n : ℕ) :
    IsFilteredInjective ((recursiveResolutionNat (𝒜 := 𝒜) u₀).X n) := by
  -- Split the recursive complex into the initial two terms and the inductive successor terms.
  obtain _ | _ | n := n
  · simpa [recursiveResolutionNat]
  · exact (strictCokernelEmbedding (𝒜 := 𝒜) u₀).next_injective
  · rw [recursiveResolutionNat_X_succ_succ (𝒜 := 𝒜) u₀ n]
    exact
      (strictCokernelEmbedding
        ((recursiveResolutionNat (𝒜 := 𝒜) u₀).d n (n + 1))).next_injective

/-- Helper for Lemma 13.26.6: the extended recursive resolution is zero in negative degrees. -/
private theorem recursiveResolution_strictlyGE {A I₀ : FilF} [IsFilteredInjective I₀]
    (u₀ : A ⟶ I₀) :
    (recursiveResolution (𝒜 := 𝒜) u₀).IsStrictlyGE 0 := by
  -- Extending an `ℕ`-indexed cochain complex by `embeddingUpNat` gives the standard lower bound.
  show CochainComplex.IsStrictlyGE
    ((recursiveResolutionNat (𝒜 := 𝒜) u₀).extend ComplexShape.embeddingUpNat) 0
  infer_instance

/-- Helper for Lemma 13.26.6: every term of the extended recursive resolution is filtered
injective. -/
private theorem recursiveResolution_term_filteredInjective {A I₀ : FilF}
    [IsFilteredInjective I₀] (u₀ : A ⟶ I₀) (n : ℤ) :
    IsFilteredInjective ((recursiveResolution (𝒜 := 𝒜) u₀).X n) := by
  by_cases hn : 0 ≤ n
  · -- In nonnegative degree, compare with the corresponding nat-indexed term.
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    letI : IsFilteredInjective ((recursiveResolutionNat (𝒜 := 𝒜) u₀).X k) :=
      recursiveResolutionNat_term_filteredInjective (𝒜 := 𝒜) u₀ k
    exact isFilteredInjective_of_iso (𝒜 := 𝒜)
      (HomologicalComplex.extendXIso (recursiveResolutionNat (𝒜 := 𝒜) u₀)
        ComplexShape.embeddingUpNat rfl).symm
  · -- In negative degree, the extension is zero, hence filtered injective.
    letI : (recursiveResolution (𝒜 := 𝒜) u₀).IsStrictlyGE 0 :=
      recursiveResolution_strictlyGE (𝒜 := 𝒜) u₀
    exact isFilteredInjective_of_iso (𝒜 := 𝒜)
      (CochainComplex.isZero_of_isStrictlyGE
        (recursiveResolution (𝒜 := 𝒜) u₀) 0 n (by linarith)).isoZero.symm

/-- Helper for Lemma 13.26.6: the recursive resolution determines a bounded-below complex in
`Fil^f(𝒜)`. -/
private noncomputable def recursiveResolutionPlus {A I₀ : FilF}
    [IsFilteredInjective I₀] (u₀ : A ⟶ I₀) : CochainComplex.Plus FilF :=
  ⟨recursiveResolution (𝒜 := 𝒜) u₀,
    (CochainComplex.plus_iff (C := FilF) (recursiveResolution (𝒜 := 𝒜) u₀)).2
      ⟨0, recursiveResolution_strictlyGE (𝒜 := 𝒜) u₀⟩⟩

/-- Helper for Lemma 13.26.6: the recursive resolution is bounded below and has filtered-injective
terms, so it defines an object of `FilteredInjectivePlus 𝒜`. -/
private noncomputable def recursiveResolutionFilteredInjectivePlus {A I₀ : FilF}
    [IsFilteredInjective I₀] (u₀ : A ⟶ I₀) :
    CochainComplex.PlusWithTermsIn (IsFilteredInjective : ObjectProperty FilF) :=
  show CochainComplex.PlusWithTermsIn (IsFilteredInjective : ObjectProperty FilF) from
    ⟨recursiveResolutionPlus (𝒜 := 𝒜) u₀,
      fun n ↦ recursiveResolution_term_filteredInjective (𝒜 := 𝒜) u₀ n⟩

/-- Helper for Lemma 13.26.6: the final `ℤ`-indexed augmentation is obtained by extending the
nat-indexed one and identifying the source single complexes. -/
private noncomputable def recursiveResolutionAugmentation {A I₀ : FilF} [IsFilteredInjective I₀]
    (u₀ : A ⟶ I₀) :
    (singleFunctor FilF (0 : ℤ)).obj A ⟶ recursiveResolution (𝒜 := 𝒜) u₀ :=
  (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat A 0 0 rfl).inv ≫
    HomologicalComplex.extendMap (recursiveResolutionNatAugmentation (𝒜 := 𝒜) u₀)
      ComplexShape.embeddingUpNat

/-- Helper for Lemma 13.26.6: any morphism whose source filtered object is zero is strict. -/
private theorem strict_of_isZero_source {X Y : FilteredObject 𝒜} (hX : IsZero X) (f : X ⟶ Y) :
    FilteredObject.Hom.Strict f := by
  -- A morphism out of the zero filtered object has zero image in every filtration step.
  have hf : f = 0 := hX.eq_of_src f 0
  subst hf
  intro i
  simp

-- Proof sketch: starting from `A`, iterate Lemma `13.26.5` on successive cokernels to build a
-- nonnegative cochain complex of filtered injective objects. Lemma `12.19.13` gives exactness on
-- associated graded pieces, so the augmentation `A[0] ⟶ I^•` is a bounded-below filtered
-- quasi-isomorphism whose degree maps are strict monomorphisms.
/-- Lemma 13.26.6: every finite filtered object `A` admits a bounded-below filtered quasi-
isomorphism `A[0] ⟶ I^•` to a filtered-injective complex, and each degree component of the
comparison map is a strict monomorphism in `Fil^f(𝒜)`. -/
theorem exists_filteredQuasiIso_from_single (A : FilF) :
    ∃ (I : FiltInjPlus) (f : (singleFunctor FilF (0 : ℤ)).obj A ⟶ I),
      _root_.CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso 0 I f := by
  classical
  -- Start the source-proof recursion by choosing the strict embedding `u₀ : A ⟶ I⁰`.
  obtain ⟨I₀, u₀, hu₀_mono, hu₀_strict⟩ :=
    exists_strictMono_to_filteredInjective (𝒜 := 𝒜) A
  let I : FiltInjPlus :=
    recursiveResolutionFilteredInjectivePlus (𝒜 := 𝒜) (I₀ := I₀.obj) u₀
  let f :
      (singleFunctor FilF (0 : ℤ)).obj A ⟶ I :=
    recursiveResolutionAugmentation (𝒜 := 𝒜) (I₀ := I₀.obj) u₀
  have _ : Mono u₀ := hu₀_mono
  have _ : FilteredObject.Hom.Strict u₀.hom := hu₀_strict
  -- Route correction: the source-faithful recursive resolution object and augmentation are now
  -- packaged as an object of `FilteredInjectivePlus 𝒜`; the only remaining step is the source-
  -- faithful graded exactness argument proving that the augmentation is a filtered quasi-
  -- isomorphism.
  --
  -- TODO: after evaluating each graded piece, use Lemma `12.19.13` on the strict recursive
  -- differentials `strict_strictCokernelDifferential` to prove exactness in positive degrees, then
  -- conclude that the graded augmentation is a quasi-isomorphism and transfer it back along
  -- `extendMap`.
  sorry

end CochainComplex.FilteredInjectivePlus

end CategoryTheory

/-! ### Lemma_13_26_7 (from Chap13) -/
open CategoryTheory
open CategoryTheory.ObjectProperty
open CochainComplex
open FilteredObject.Hom

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]

local notation "FilF" => Fil^f(𝒜)
local notation "single₀" => CochainComplex.singleFunctor FilF (0 : ℤ)

/- Domain-style sampling for Lemma `13.26.7`.
- primary domain: strict lifting of morphisms along filtered quasi-isomorphisms into bounded-below
  filtered-injective cochain complexes in `Fil^f(𝒜)`;
- sampled owner declarations:
  `CochainComplex.FilteredInjectivePlus`,
  `CochainComplex.IsTermwiseMonoStrictlyGEWithTermsIn`,
  `CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso`,
  `CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso
    .exists_strict_lift_to_boundedBelow_filteredInjective`,
  `finiteFilteredObjectAssociatedGradedCochainFunctor`,
  `FilteredObject.Hom.Strict`,
  `CategoryTheory.CommSq`;
- best owner abstraction: the bounded-below filtered-injective complexes are canonically owned by
  `CochainComplex.FilteredInjectivePlus 𝒜`; the source comparison map
  `K ⟶ I^•` together with its associated-graded quasi-isomorphism and degreewise strictness is
  canonically owned by the chapter declaration
  `CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso`; its primitive bounded-below
  termwise-monomorphic part is the generic Chapter 13 owner
  `CochainComplex.IsTermwiseMonoStrictlyGEWithTermsIn`; the degree-zero square-shaped formulation
  is a source-facing bridge owned by `CategoryTheory.CommSq`;
- primitive data: a cochain complex `K`, owner objects `I J` in
  `CochainComplex.FilteredInjectivePlus 𝒜`, a source comparison morphism `α : K ⟶ I^•` carrying
  the owner data
  `CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso 0 I α`, together with a target
  comparison map `γ : K ⟶ J^•`;
- derived API: the degree-zero commutative square corollary on the underlying cochain complexes
  via the canonical coercion, with the source hypotheses kept in the same primitive owner/data
  split as in `Lemma_13_26_6`, and obtained directly from the owner theorem
  `CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso
    .exists_strict_lift_to_boundedBelow_filteredInjective`;
- source/core/bridge triage:
  `source-facing`: the degree-zero square corollary below;
  `core/canonical`: `CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso`,
    `CochainComplex.IsTermwiseMonoStrictlyGEWithTermsIn`,
    `CochainComplex.FilteredInjectivePlus`,
    `finiteFilteredObjectAssociatedGradedCochainFunctor`, and `FilteredObject.Hom.Strict`;
  `bridge/view`: the canonical coercion from `CochainComplex.FilteredInjectivePlus 𝒜` to
    `CochainComplex (Fil^f(𝒜)) ℤ`, and the source-facing `CommSq` wrapper for the single-degree
    statement.

The public surface therefore keeps the bounded-below filtered-injective complexes on the canonical
owner `CochainComplex.FilteredInjectivePlus 𝒜` and reuses the primitive comparison-map owner
`CochainComplex.IsTermwiseMonoStrictlyGEWithTermsIn`, but takes the full filtered comparison datum
through the existing chapter owner
`CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso` instead of restating its derived
fields as parallel arguments. -/

variable {A B : FilF}

-- Proof sketch: argue by the filtered comparison theorem for bounded-below filtered-injective
-- complexes, using the full comparison datum `ha` supplied by Lemma `13.26.6`. Specialize to
-- `K = A[0]` and `γ = (single₀).map f ≫ b`, then package the resulting equality as a commutative
-- square.
/-- Lemma 13.26.7: a morphism in `Fil^f(𝒜)` extends from a bounded-below filtered-injective
resolution `A[0] ⟶ I^•` with termwise strict degree maps to a bounded-below filtered-injective
complex `J^•` equipped with a comparison map `B[0] ⟶ J^•`. -/
theorem exists_cochainMap_of_filteredQuasiIso_to_termwise_filteredInjective
    {I J : CochainComplex.FilteredInjectivePlus 𝒜}
    (f : A ⟶ B) (a : (single₀).obj A ⟶ I)
    (_ha : CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso 0 I a)
    (b : (single₀).obj B ⟶ J) :
    ∃ g : I ⟶ J, CommSq a ((single₀).map f) g b :=
  let ha := _ha
  -- Apply the comparison theorem from Lemma `13.26.6` to the morphism `A[0] ⟶ J`.
  match
      CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso
        .exists_strict_lift_to_boundedBelow_filteredInjective ha ((single₀).map f ≫ b) with
  | ⟨g, hg⟩ =>
      -- Package the resulting equality as the required commutative square.
      ⟨g, hg⟩

end CategoryTheory

/-! ### Lemma_13_26_8 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CochainComplex
open scoped CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]
  [Abelian (finiteFilteredObjectCat 𝒜)]

local instance instCategoryWithHomologyGradedObjectInt_13_26_8 :
    CategoryWithHomology (GradedObject ℤ 𝒜) := by
  have hzero : (Preadditive.preadditiveHasZeroMorphisms :
      HasZeroMorphisms (GradedObject ℤ 𝒜)) = GradedObject.hasZeroMorphisms ℤ :=
    HasZeroMorphisms.ext _ _
  exact hzero ▸
    (@_root_.CategoryTheory.categoryWithHomology_of_abelian (GradedObject ℤ 𝒜) _ _)

namespace CochainComplex

local notation "FilF" => Fil^f(𝒜)
local notation "FiltInjPlus" => FilteredInjectivePlus 𝒜
local notation "single₀" => CochainComplex.singleFunctor FilF (0 : ℤ)
local notation "ιFiltInjPlus" => CochainComplex.PlusWithTermsIn.ι IsFilteredInjective
private abbrev assocGraded := finiteFilteredObjectAssociatedGradedCochainFunctor 𝒜

/- Domain-style sampling for Lemma `13.26.8`.
- primary domain: horseshoe diagrams in the bounded-below filtered-complex category
  `CochainComplex.Plus (Fil^f(𝒜))`, with filtered-injective rows and filtered quasi-isomorphism
  comparison maps;
- sampled owner declarations:
  `CochainComplex.FilteredInjectivePlus`,
  `CochainComplex.PlusWithTermsIn.ι`,
  `CategoryTheory.ShortComplex`,
  `ShortComplex.Hom`,
  `ShortComplex.ShortExact`,
  `finiteFilteredObjectAssociatedGradedCochainFunctor`;
- best owner abstraction: the lower row is canonically owned by
  `ShortComplex (CochainComplex.FilteredInjectivePlus 𝒜)`, its comparison with the degree-zero
  short exact sequence is owned by `ShortComplex.Hom`, and short exactness is owned by
  `ShortComplex.ShortExact`, while the source-facing termwise-split conclusion is owned by the
  degreewise family `∀ n, (T.map (HomologicalComplex.eval FilF (ComplexShape.up ℤ) n)).Splitting`
  on the underlying short complex `T`;
- primitive data: the prescribed outer filtered-injective complexes and outer vertical maps, a
  lower short complex in `CochainComplex.FilteredInjectivePlus 𝒜`, and the comparison morphism
  from `S.map single₀` to its image after applying the canonical inclusion
  `CochainComplex.PlusWithTermsIn.ι`, together with the
  degreewise splitting of the lower row;
- derived API: the lower-row short exactness deduced from the degreewise splitting family, and the
  middle filtered quasi-isomorphism deduced from that short exactness plus the outer filtered
  quasi-isomorphisms;
- source/core/bridge triage:
  `source-facing`: the existence theorem below, stated with prescribed outer filtered
    quasi-isomorphisms and an explicit degreewise-splitting conclusion;
  `core/canonical`: `CochainComplex.FilteredInjectivePlus`,
    `CochainComplex.PlusWithTermsIn.ι`,
    `ShortComplex`, `ShortComplex.Hom`, `ShortComplex.ShortExact`, and the associated-graded
    functor on `CochainComplex (Fil^f(𝒜)) ℤ`;
  `bridge/view`: the canonical bounded-below inclusion
    `CochainComplex.PlusWithTermsIn.ι`. -/

omit [EnoughInjectives 𝒜] in
/-- For a morphism between two short exact rows, if the outer vertical components are filtered
quasi-isomorphisms, then so is the middle component. -/
theorem quasiIso_middle {S : ShortComplex FilF} (hS : S.ShortExact)
    {T : ShortComplex FiltInjPlus} (φ : S.map single₀ ⟶ T.map ιFiltInjPlus)
    (hrow : (T.map ιFiltInjPlus).ShortExact)
    (hτ₁ : QuasiIso (assocGraded.map φ.τ₁))
    (hτ₃ : QuasiIso (assocGraded.map φ.τ₃)) :
    QuasiIso (assocGraded.map φ.τ₂) := by
  sorry

-- Proof sketch: starting from the prescribed filtered quasi-isomorphisms on the outer terms, lift
-- the outer objects into bounded-below filtered-injective complexes, build the middle
-- filtered-injective complex degreewise by extension, and assemble the lower row directly as a
-- short complex in `CochainComplex.FilteredInjectivePlus 𝒜` together with a single comparison
-- morphism from the degree-zero short exact sequence. The lower row is recorded by the canonical
-- degreewise splitting family, which is the source-facing termwise-split conclusion.
/-- Lemma 13.26.8: given a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` in `Fil^f(𝒜)` and prescribed
filtered quasi-isomorphisms from `A[0]` and `C[0]` into bounded-below complexes of filtered
injective objects, there exists a filtered horseshoe diagram whose lower row is termwise split
and whose outer comparison maps are exactly the prescribed maps. -/
theorem exists_filtered_horseshoe_diagram
    (S : ShortComplex FilF) (hS : S.ShortExact)
    {I J : FiltInjPlus} (a : (single₀).obj S.X₁ ⟶ I)
    (c : (single₀).obj S.X₃ ⟶ J)
    (hτ₁ : QuasiIso (assocGraded.map a))
    (hτ₃ : QuasiIso (assocGraded.map c)) :
    ∃ (K : FiltInjPlus) (i : I ⟶ K) (p : K ⟶ J) (hip : i ≫ p = 0)
      (φ : S.map single₀ ⟶ (ShortComplex.mk i p hip).map ιFiltInjPlus)
      (σ : ∀ n : ℤ,
        ((ShortComplex.mk i p hip).map
          (ιFiltInjPlus ⋙ HomologicalComplex.eval FilF (ComplexShape.up ℤ) n)).Splitting),
        φ.τ₁ = a ∧
          φ.τ₃ = c := by
  sorry

-- Proof sketch: first build the horseshoe diagram from `exists_filtered_horseshoe_diagram`.
-- The degreewise splitting family implies short exactness of the lower row, so
-- `quasiIso_middle` applies to the resulting short-complex morphism and the prescribed outer
-- filtered quasi-isomorphisms.
/-- Companion consequence to Lemma 13.26.8: if the prescribed outer comparison maps are filtered
quasi-isomorphisms, then the horseshoe diagram can be chosen so that the middle comparison map is
also a filtered quasi-isomorphism. -/
theorem exists_filtered_horseshoe_diagram_of_outer_quasiIso
    (S : ShortComplex FilF) (hS : S.ShortExact)
    {I J : FiltInjPlus} (a : (single₀).obj S.X₁ ⟶ I)
    (c : (single₀).obj S.X₃ ⟶ J)
    (hτ₁ : QuasiIso (assocGraded.map a))
    (hτ₃ : QuasiIso (assocGraded.map c)) :
    ∃ (K : FiltInjPlus) (i : I ⟶ K) (p : K ⟶ J) (hip : i ≫ p = 0)
      (φ : S.map single₀ ⟶ (ShortComplex.mk i p hip).map ιFiltInjPlus)
      (σ : ∀ n : ℤ,
        ((ShortComplex.mk i p hip).map
          (ιFiltInjPlus ⋙ HomologicalComplex.eval FilF (ComplexShape.up ℤ) n)).Splitting),
        φ.τ₁ = a ∧
          φ.τ₃ = c ∧
          QuasiIso (assocGraded.map φ.τ₂) := by
  sorry

end CochainComplex

end CategoryTheory

/-! ### Lemma_13_26_9 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CochainComplex
open CategoryTheory.ObjectProperty

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]

local instance instCategoryWithHomologyGradedObjectInt_13_26_9 :
    CategoryWithHomology (GradedObject ℤ 𝒜) := by
  have hzero : (Preadditive.preadditiveHasZeroMorphisms :
      HasZeroMorphisms (GradedObject ℤ 𝒜)) = GradedObject.hasZeroMorphisms ℤ :=
    HasZeroMorphisms.ext _ _
  exact hzero ▸
    (@_root_.CategoryTheory.categoryWithHomology_of_abelian (GradedObject ℤ 𝒜) _ _)

namespace FilteredComplex

local notation "FilF" => Fil^f(𝒜)
local notation "FiltInjPlus" => CochainComplex.FilteredInjectivePlus 𝒜
local notation "ιFilF" =>
  Functor.mapHomologicalComplex
    (ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))))
    (ComplexShape.up ℤ)

/- Domain-style sampling for Lemma `13.26.9`.
- primary domain: bounded-below filtered complexes with finite filtrations and their filtered
  quasi-isomorphisms into bounded-below complexes of filtered injective objects;
- sampled owner declarations:
  `FilteredComplex`,
  `FilteredComplex.HasFiniteFiltrations`,
  `FilteredComplex.toFiniteCochain`,
  `FilteredComplex.toFiniteCochainMap`,
  `FilteredComplex.associatedGradedMap`,
  `CochainComplex.FilteredInjectivePlus`,
  `CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso`,
  `((ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜)))).mapHomologicalComplex
    (ComplexShape.up ℤ))`;
- best owner abstraction: the source object remains the intrinsic Chapter `12` owner
  `FilteredComplex 𝒜`, while the target bounded-below filtered-injective complex is canonically
  owned by `CochainComplex.FilteredInjectivePlus 𝒜`; the comparison map data should be expressed
  by the chapter owner `CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso` after the
  canonical bridge `FilteredComplex.toFiniteCochain` from a finite filtered complex to a cochain
  complex in `Fil^f(𝒜)`;
- primitive data: a filtered complex `K : FilteredComplex 𝒜` together with a lower bound
  `hKge : K.underlying.IsStrictlyGE a` and the finiteness witness `hKfin : K.HasFiniteFiltrations`;
- derived API: the bridge declarations `toFiniteCochain` and `toFiniteCochainMap`, and the
  existence theorem below, whose public comparison datum is the intrinsic filtered-complex
  morphism `f : K ⟶ (ιFilF).obj I`;
- source/core/bridge triage:
  `source-facing`: the existence theorem below, formulated on `FilteredComplex 𝒜`;
  `core/canonical`: `CochainComplex.FilteredInjectivePlus` and
    `CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso`;
  `bridge/view`: `FilteredComplex.toFiniteCochain`, `FilteredComplex.toFiniteCochainMap`, and
    the canonical inclusion
    `((ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))))
      .mapHomologicalComplex (ComplexShape.up ℤ))`, which translates the intrinsic
    finite-filtration hypothesis into the canonical full-subcategory owner `Fil^f(𝒜)`. -/

/-- Bridge/view layer: a filtered complex with finite filtrations is canonically a cochain complex
in `Fil^f(𝒜)`. -/
abbrev toFiniteCochain (K : FilteredComplex 𝒜) (hKfin : K.HasFiniteFiltrations) :
    CochainComplex FilF ℤ :=
  { X n := ⟨K.X n, hKfin n⟩
    d i j := ObjectProperty.homMk (K.d i j)
    shape i j hij := by
      simp [K.shape i j hij]
    d_comp_d' i j k hij hjk := by
      ext
      simp [K.d_comp_d' i j k hij hjk] }

/-- Bridge/view layer: a morphism from a filtered complex with finite filtrations into the
canonical image of a cochain complex in `Fil^f(𝒜)` lifts to a morphism in
`CochainComplex (Fil^f(𝒜)) ℤ`. -/
abbrev toFiniteCochainMap {K : FilteredComplex 𝒜} (hKfin : K.HasFiniteFiltrations)
    {I : CochainComplex FilF ℤ} (f : K ⟶ (ιFilF).obj I) :
    K.toFiniteCochain hKfin ⟶ I :=
  { f n := ObjectProperty.homMk (f.f n)
    comm' i j hij := by
      ext
      simpa using f.comm' i j hij }

-- Proof sketch: shift a bounded-below filtered complex so that it is concentrated in degrees
-- `≥ 0`, and resolve the kernels and coimages of the differentials
-- termwise by Lemma
-- `13.26.6`. Use Lemma `13.26.7` to lift the connecting morphisms and Lemma `13.26.8` to splice
-- the resulting resolutions into a double complex whose total complex gives the desired target.
-- The degreewise maps are strict monomorphisms by construction, and the total map is a filtered
-- quasi-isomorphism because associated graded commutes with totalization and Lemma `12.25.4`
-- applies to the graded double complex.
/-- Lemma 13.26.9: a bounded-below filtered complex with finite filtrations admits a filtered
quasi-isomorphism to a bounded-below filtered complex of filtered injective objects such that each
degree map is a strict monomorphism in `Fil^f(𝒜)`. -/
theorem exists_filteredQuasiIso_to_termwiseStrictMono_termwiseFilteredInjective_of_boundedBelow
    (a : ℤ) (K : FilteredComplex 𝒜) (hKge : K.underlying.IsStrictlyGE a)
    (hKfin : K.HasFiniteFiltrations) :
    ∃ (I : FiltInjPlus) (f : K ⟶ (ιFilF).obj I),
      CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso a I
        (toFiniteCochainMap hKfin f) := sorry

end FilteredComplex

end CategoryTheory

/-! ### Lemma_13_26_10 (from Chap13) -/
open CategoryTheory
open CochainComplex
open scoped CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]

local notation "FilF" => finiteFilteredObjectCat 𝒜
local notation "QhFilt" => HomotopyCategory.quotient FilF (ComplexShape.up ℤ)
local notation "ιFiltInjPlus" =>
  CochainComplex.PlusWithTermsIn.ι (IsFilteredInjective : ObjectProperty FilF)
local notation "FAcOrth" => ObjectProperty.rightOrthogonal (FAc(𝒜))

variable {K : CochainComplex FilF ℤ}

/- Domain-style sampling for Lemma `13.26.10`.
- primary domain: filtered acyclic objects in the homotopy category `K(Fil^f(𝒜))`, bounded-below
  filtered-injective complexes, and right orthogonality against `FAc(𝒜)`;
- sampled owner declarations:
  `FAc(𝒜)`,
  `ObjectProperty.rightOrthogonal`,
  `HomotopyCategory.quotient_map_eq_zero_iff`,
  `CochainComplex.FilteredInjectivePlus`,
  `IsFilteredInjective`;
- best owner abstraction: the canonical owner is the right orthogonal
  `FAcOrth` in the filtered homotopy category, with the bounded-below filtered-injective target
  owned by the chapter abbreviation `CochainComplex.FilteredInjectivePlus 𝒜`;
- primitive data: a bounded-below filtered-injective complex
  `I : CochainComplex.FilteredInjectivePlus 𝒜`;
- derived API: membership of `((ιFiltInjPlus ⋙ QhFilt).obj I)` in `FAcOrth`, and the
  source-facing homotopy-to-zero statement obtained by
  `HomotopyCategory.quotient_map_eq_zero_iff`.

Source/core/bridge triage:
- `source-facing`: the textbook null-homotopy statement below;
- `core/canonical`: `ObjectProperty.rightOrthogonal` applied to `FAc(𝒜)`;
- `bridge/view`: `HomotopyCategory.quotient_map_eq_zero_iff`, which translates vanishing in the
  homotopy category into existence of a homotopy to zero.

This file therefore keeps the textbook statement as a thin bridge, while exposing the owner-level
orthogonality theorem directly on the filtered homotopy category. -/
namespace CochainComplex.FilteredInjectivePlus

-- Proof sketch: pass to the homotopy category of `Fil^f(𝒜)` and argue degreewise on associated
-- graded pieces as in the ordinary injective case. Filtered acyclicity kills the source, while
-- bounded-belowness and termwise filtered injectivity place the target in the right orthogonal of
-- `FAc(𝒜)`.
/-- A bounded-below complex of filtered injectives lies in the right orthogonal of the filtered
acyclic subcategory of `K(Fil^f(𝒜))`. -/
theorem rightOrthogonal (I : CochainComplex.FilteredInjectivePlus 𝒜) :
    FAcOrth ((ιFiltInjPlus ⋙ QhFilt).obj I) := by
  sorry

end CochainComplex.FilteredInjectivePlus

-- Proof sketch: apply the owner theorem
-- `CochainComplex.FilteredInjectivePlus.rightOrthogonal` in the filtered homotopy
-- category and translate the resulting vanishing statement back to a homotopy by
-- `HomotopyCategory.quotient_map_eq_zero_iff`.
/-- Lemma 13.26.10: if `K^•` is filtered acyclic and `I^•` is bounded below with filtered
injective terms, then every morphism `K^• ⟶ I^•` is homotopic to zero. -/
theorem homotopic_to_zero_of_filteredAcyclic_to_boundedBelow_termwiseFilteredInjective
    (I : CochainComplex.FilteredInjectivePlus 𝒜) (α : K ⟶ I)
    (hK : FAc(𝒜) ((QhFilt).obj K)) :
    Nonempty (Homotopy α 0) :=
  let hI : FAcOrth ((ιFiltInjPlus ⋙ QhFilt).obj I) := I.rightOrthogonal
  exact (HomotopyCategory.quotient_map_eq_zero_iff α).1 <|
    hI ((QhFilt).map α) hK

end CategoryTheory

/-! ### Lemma_13_26_11 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open ComplexShape
open FilteredObject
open scoped CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]

local notation "FilF" => finiteFilteredObjectCat 𝒜
local notation "QhFilt" => HomotopyCategory.quotient FilF (up ℤ)
local notation "KFilt" => HomotopyCategory FilF (up ℤ)
local notation "QhFiltInj" =>
  CochainComplex.PlusWithTermsIn.ι (IsFilteredInjective : ObjectProperty FilF) ⋙ QhFilt

local instance finiteFiltered_hasFiniteBiproducts_13_26_11 : HasFiniteBiproducts FilF :=
  HasFiniteBiproducts.of_hasFiniteProducts

local instance finiteFiltered_hasBinaryBiproducts_13_26_11 : HasBinaryBiproducts FilF :=
  CategoryTheory.Limits.hasBinaryBiproducts_of_finite_biproducts _

local instance pretriangulated_filtered_homotopy_13_26_11 :
    Pretriangulated KFilt := by
  exact HomotopyCategory.instPretriangulatedIntUp FilF

local instance isTriangulated_filtered_homotopy_13_26_11 : IsTriangulated KFilt := inferInstance

/- Domain-style sampling for Lemma `13.26.11`.
- primary domain: Verdier localization of the filtered homotopy category at filtered
  quasi-isomorphisms, together with the filtered analogue of bounded-below injective cochain
  complexes and right orthogonality against filtered acyclic objects;
- sampled owner declarations in this domain:
  `CochainComplex.FilteredInjectivePlus`,
  `CochainComplex.PlusWithTermsIn.plus`,
  `CochainComplex.PlusWithTermsIn.term_mem`,
  `CochainComplex.FilteredInjectivePlus.rightOrthogonal`,
  `ObjectProperty.rightOrthogonal.map_bijective_of_isTriangulated`,
  `((FAc(𝒜) : ObjectProperty KFilt).trW.Q : KFilt ⥤ DF(𝒜))`,
  `DF(𝒜)`;
- best owner abstraction: the filtered analogue
  `CochainComplex.FilteredInjectivePlus 𝒜` of `CochainComplex.InjectivePlus 𝒜`, which packages
  bounded-belowness together with termwise filtered injectivity, while the canonical quotient
  functor `((FAc(𝒜) : ObjectProperty KFilt).trW.Q : KFilt ⥤ DF(𝒜))` remains the localization
  bridge;
- primitive data: a filtered quasi-isomorphism `α` in `KFilt`, together with a bounded-below
  filtered-injective target `I : CochainComplex.FilteredInjectivePlus 𝒜`;
- derived API: bijectivity of precomposition in `KFilt` and bijectivity of the localization map on
  morphisms into that target;
- source/core/bridge triage:
  `source-facing`: the two bijectivity statements below;
  `core/canonical`: `CochainComplex.FilteredInjectivePlus`, `ObjectProperty.rightOrthogonal`,
    `DF(𝒜)`, and `((FAc(𝒜) : ObjectProperty KFilt).trW.Q : KFilt ⥤ DF(𝒜))`;
  `bridge/view`: the textbook null-homotopy statement of Lemma `13.26.10`, derived from the owner
  theorem `CochainComplex.FilteredInjectivePlus.rightOrthogonal`.

This file therefore keeps the source-facing statements, but refines the target hypothesis from a
raw bounded-below cochain complex with separate termwise filtered-injectivity hypotheses to the
owner `CochainComplex.FilteredInjectivePlus 𝒜`, and writes theorem `(2)` directly with the
canonical quotient functor `((FAc(𝒜) : ObjectProperty KFilt).trW.Q : KFilt ⥤ DF(𝒜))`. -/

-- Proof sketch: the owner theorem
-- `CochainComplex.FilteredInjectivePlus.rightOrthogonal` places the target object
-- in the right orthogonal of `FAc(𝒜)`. Since `FQis(𝒜) = (FAc(𝒜)).trW` by Lemma `13.13.4`, the
-- canonical theorem
-- `ObjectProperty.rightOrthogonal.map_bijective_of_isTriangulated` applied to the chapter owner
-- functor `((FAc(𝒜) : ObjectProperty KFilt).trW.Q : KFilt ⥤ DF(𝒜))` gives bijectivity of
-- precomposition with `α`.
/-- Lemma 13.26.11 (1): precomposition with a filtered quasi-isomorphism induces a bijection on
morphisms into a bounded-below complex whose terms are filtered injective. -/
theorem precomp_bijective_of_filteredQuasiIso_to_boundedBelow_termwiseFilteredInjective
    {K L : KFilt} (I : CochainComplex.FilteredInjectivePlus 𝒜) (α : K ⟶ L)
    (hα : (FQis(𝒜) : MorphismProperty KFilt) α) :
    Function.Bijective
      (fun β : L ⟶ (QhFiltInj).obj I ↦ α ≫ β) := by
  have hY : (FQis(𝒜) : MorphismProperty KFilt).isLocal ((QhFiltInj).obj I) := by
    rw [← filteredAcyclic_trW_eq_filteredQuasiIso, ObjectProperty.isLocal_trW (FAc(𝒜))]
    exact I.rightOrthogonal
  exact hY α hα

-- Proof sketch: any morphism in the localization is represented by a right fraction whose
-- denominator is a filtered quasi-isomorphism. Part (1) lets one descend the numerator to a map
-- from `L` to `I`, giving surjectivity; applying part (1) again to a denominator that kills a map
-- in the localization gives injectivity.
/-- Lemma 13.26.11 (2): for a bounded-below complex whose terms are filtered injective, the
canonical map from the filtered homotopy category to the filtered derived category identifies
morphisms into it in `K(Fil^f(𝒜))` with morphisms into it in `DF(𝒜)`. -/
theorem homotopyCategory_to_filteredDerived_bijective_of_boundedBelow_termwiseFilteredInjective
    (L : KFilt) (I : CochainComplex.FilteredInjectivePlus 𝒜) :
    Function.Bijective
      ((((FAc(𝒜) : ObjectProperty KFilt).trW.Q) : KFilt ⥤ DF(𝒜)).map :
        (L ⟶ (QhFiltInj).obj I) → _) := by
  letI :
      Functor.IsLocalization
        (((FAc(𝒜) : ObjectProperty KFilt).trW.Q) : KFilt ⥤ DF(𝒜))
        ((FAc(𝒜) : ObjectProperty KFilt).trW) := by
    exact Functor.q_isLocalization ((FAc(𝒜) : ObjectProperty KFilt).trW)
  simpa using
    (I.rightOrthogonal).map_bijective_of_isTriangulated
      (((FAc(𝒜) : ObjectProperty KFilt).trW.Q) : KFilt ⥤ DF(𝒜)) L

end CategoryTheory
