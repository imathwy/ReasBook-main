import Mathlib
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.Abelian.Opposite
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Balanced
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.Transfer
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_5_1 (from Chap12) -/
namespace CategoryTheory

/- Source/core/bridge triage for Definition 12.5.1:
- source-facing: the source notion of an abelian category
- core/canonical owner: `Abelian`
- bridge/view: `Abelian.ofCoimageImageComparisonIsIso`, whose additive input reuses the earlier
  chapter owner `HasFiniteProducts` from Definition 12.3.8 together with `Preadditive` -/
/- Definition 12.5.1: the source notion of an abelian category is represented canonically by the
mathlib owner class `Abelian`. -/
recall Abelian

/- Source-facing bridge: the textbook criterion "additive, kernels, cokernels, and
`Coim(f) ⟶ Im(f)` an isomorphism for every morphism `f`" is implemented by the constructor
`Abelian.ofCoimageImageComparisonIsIso`, with the additive hypothesis represented in mathlib by
`Preadditive` together with finite products. -/
recall Abelian.ofCoimageImageComparisonIsIso

end CategoryTheory

/-! ### Lemma_12_5_2 (from Chap12) -/
universe v u

namespace CategoryTheory

open Limits

variable (A : Type u) [Category.{v} A]

/-
Source/core/bridge triage for Lemma 12.5.2:
- source-facing: opposite and unop preserve the preadditive/additive/abelian structures in the
  Stacks sense
- core/canonical owners: `instPreadditiveOpposite`, `HasFiniteProducts`, and the abelian opposite
  instance from mathlib
- bridge/view: `Preadditive.ofFullyFaithful`, `hasFiniteProducts_of_opposite`, and
  `abelianOfEquivalence`
-/

section

variable [Preadditive A]

/- Lemma 12.5.2 (1): the opposite of a preadditive category is canonically preadditive. -/
recall instPreadditiveOpposite (A : Type u) [Category.{v} A] [Preadditive A] : Preadditive Aᵒᵖ

/-
Lemma 12.5.2 (1): if `A` is additive, then `Aᵒᵖ` is additive. In the canonical owner language of
Definition 12.3.8, the remaining additive structure is the finite-product instance below.
-/
@[reducible] noncomputable def instHasFiniteProductsOpposite
    [HasFiniteProducts A] :
    HasFiniteProducts Aᵒᵖ := by
  let _ : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts
  let _ : HasFiniteCoproducts A := inferInstance
  infer_instance

end

section

variable [Preadditive Aᵒᵖ]

/- Lemma 12.5.2 (1): if `Aᵒᵖ` is preadditive, then `A` is canonically preadditive. -/
@[reducible] noncomputable def instPreadditiveUnop : Preadditive A :=
  Preadditive.ofFullyFaithful (Functor.FullyFaithful.ofFullyFaithful (opOp A))

/-
Lemma 12.5.2 (1): if `Aᵒᵖ` is additive, then `A` is additive. In the canonical owner language of
Definition 12.3.8, the remaining additive structure is the finite-product instance below.
-/
@[reducible] noncomputable def instHasFiniteProductsUnop
    [HasFiniteProducts Aᵒᵖ] :
    HasFiniteProducts A := by
  let _ : HasFiniteBiproducts Aᵒᵖ := HasFiniteBiproducts.of_hasFiniteProducts
  let _ : HasFiniteCoproducts Aᵒᵖ := inferInstance
  exact hasFiniteProducts_of_opposite

end

section

variable [Abelian A]

/- Lemma 12.5.2 (2): the opposite of an abelian category is canonically abelian. -/
recall instAbelianOpposite (A : Type u) [Category.{v} A] [Abelian A] : Abelian Aᵒᵖ

end

section

variable [Abelian Aᵒᵖ]

/- Lemma 12.5.2 (2): if the opposite category `Aᵒᵖ` is abelian, then `A` is abelian. -/
@[reducible] noncomputable def instAbelianUnop : Abelian A :=
  let _ : Preadditive A := instPreadditiveUnop A
  let _ : HasFiniteProducts A := instHasFiniteProductsUnop A
  let _ : Abelian Aᵒᵖᵒᵖ := instAbelianOpposite Aᵒᵖ
  abelianOfEquivalence (opOpEquivalence A).symm.functor

attribute [instance] instHasFiniteProductsOpposite
attribute [instance] instPreadditiveUnop
attribute [instance] instHasFiniteProductsUnop
attribute [instance] instAbelianUnop

end

end CategoryTheory

/-! ### Definition_12_5_3 (from Chap12) -/
universe v u

namespace CategoryTheory

open Limits Opposite Preadditive

variable {C : Type u} [Category.{v} C]
variable {X Y : C}

/- Domain-style sampling for Definition 12.5.3:
- primary domain: kernel/cokernel criteria for morphisms, together with subobjects and quotient
  objects in an abelian category;
- inspected canonical declarations:
  `mono_iff_isZero_kernel`,
  `epi_iff_isZero_cokernel`,
  `Subobject`,
  `Abelian.subobjectIsoSubobjectOp`;
- best owner abstraction:
  source-facing `IsInjective f`, `IsSurjective f`, and `IsSubobject X Y`;
  core/canonical `Mono f`, `Epi f`, and `Subobject Y`;
  bridge/view `IsQuotient Y X := IsSubobject (op Y) (op X)`.

Primitive-vs-derived split:
- primitive data for the source-facing morphism notions: the kernel and cokernel objects of `f`;
- derived API: the canonical bridge theorems `isInjective_iff_mono` and
  `isSurjective_iff_epi`;
- primitive data for subobjects: a canonical subobject `P : Subobject Y`;
- derived API: the source-facing relation “`X` is a subobject of `Y`”, expressed by asking for an
  isomorphism from `X` to the underlying object of some `P`, and the opposite-category bridge
  `IsQuotient`.
-/

abbrev IsInjective (f : X ⟶ Y) [HasZeroMorphisms C] [HasKernel f] : Prop :=
  IsZero (kernel f)

abbrev IsSurjective (f : X ⟶ Y) [HasZeroMorphisms C] [HasCokernel f] : Prop :=
  IsZero (cokernel f)

/- Companion canonical owner for Definition 12.5.3 (injective). -/
recall CategoryTheory.Mono

/- Companion canonical owner for Definition 12.5.3 (surjective). -/
recall CategoryTheory.Epi

section

variable [Preadditive C] (f : X ⟶ Y)

/-- Definition 12.5.3, canonical bridge: the source-facing injective condition is equivalent to
the owner predicate `Mono f`. -/
theorem isInjective_iff_mono [HasKernel f] :
    IsInjective f ↔ Mono f := by
  simpa [IsInjective] using (mono_iff_isZero_kernel f).symm

/-- Definition 12.5.3, canonical bridge: the source-facing surjective condition is equivalent to
the owner predicate `Epi f`. -/
theorem isSurjective_iff_epi [HasCokernel f] :
    IsSurjective f ↔ Epi f := by
  simpa [IsSurjective] using (epi_iff_isZero_cokernel f).symm

end

/- Definition 12.5.3 (subobjects): the owner notion of subobjects of `Y` is `Subobject Y`. -/
recall CategoryTheory.Subobject
recall CategoryTheory.Subobject.mk
recall CategoryTheory.Subobject.underlyingIso

section

variable [Abelian C]

/- Definition 12.5.3 (quotient objects): mathlib represents quotient objects of `Y` by
`Subobject (op Y)`, and in an abelian category `Abelian.subobjectIsoSubobjectOp Y` identifies
them with the ordinary subobjects of `Y`. -/
recall CategoryTheory.Abelian.subobjectIsoSubobjectOp

end

/-- Source-facing bridge/view: `X` is a subobject of `Y` when it is isomorphic to the underlying
object of some canonical subobject of `Y`. -/
def IsSubobject (X Y : C) : Prop :=
  ∃ P : Subobject Y, Nonempty (X ≅ P)

infix:50 " ⊂ " => IsSubobject

/-- Source-facing dual bridge/view: `Y` is a quotient of `X` when `op Y` is a subobject of
`op X`. -/
abbrev IsQuotient (Y X : C) : Prop :=
  IsSubobject (op Y) (op X)

namespace ObjectProperty

/-- An object property has epi covers if every object receives an epimorphism from an object
satisfying the property. -/
class HasEpiCover (P : ObjectProperty C) : Prop where
  exists_epi : ∀ X : C, ∃ Y : C, P Y ∧ ∃ f : Y ⟶ X, Epi f

/-- The maximal object property has epi covers, using the identity epimorphism of each object. -/
instance instHasEpiCoverTop : HasEpiCover (⊤ : ObjectProperty C) := sorry

end ObjectProperty

/-- Companion canonical bridge: `X` is a subobject of `Y` exactly when there exists a
monomorphism `X ⟶ Y`. -/
theorem isSubobject_iff_exists_mono :
    X ⊂ Y ↔ ∃ f : X ⟶ Y, Mono f := by
  constructor
  · rintro ⟨P, ⟨e⟩⟩
    exact ⟨e.hom ≫ P.arrow, inferInstance⟩
  · rintro ⟨f, hf⟩
    letI : Mono f := hf
    exact ⟨Subobject.mk f, ⟨(Subobject.underlyingIso f).symm⟩⟩

/-- Source-facing bridge to the textbook wording: `X` is a subobject of `Y` exactly when there
exists an injective morphism `X ⟶ Y`, with injective understood as `IsZero (kernel f)`. -/
theorem isSubobject_iff_exists_isInjective [Preadditive C] [HasKernels C] :
    X ⊂ Y ↔ ∃ f : X ⟶ Y, IsInjective f := by
  rw [isSubobject_iff_exists_mono]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, (isInjective_iff_mono f).2 hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, (isInjective_iff_mono f).1 hf⟩

/-- Companion canonical bridge: `Y` is a quotient of `X` exactly when there exists an
epimorphism `X ⟶ Y`. -/
theorem isQuotient_iff_exists_epi :
    IsQuotient Y X ↔ ∃ f : X ⟶ Y, Epi f := by
  rw [IsQuotient, isSubobject_iff_exists_mono]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f.unop, by
      letI : Mono f := hf
      infer_instance⟩
  · rintro ⟨f, hf⟩
    exact ⟨f.op, by
      letI : Epi f := hf
      infer_instance⟩

/-- Source-facing dual bridge to the textbook wording: `Y` is a quotient of `X` exactly when there
exists a surjective morphism `X ⟶ Y`, with surjective understood as `IsZero (cokernel f)`. -/
theorem isQuotient_iff_exists_isSurjective [Preadditive C] [HasCokernels C] :
    IsQuotient Y X ↔ ∃ f : X ⟶ Y, IsSurjective f := by
  rw [isQuotient_iff_exists_epi]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, (isSurjective_iff_epi f).2 hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, (isSurjective_iff_epi f).1 hf⟩

end CategoryTheory

/-! ### Lemma_12_5_4 (from Chap12) -/
universe v u

namespace CategoryTheory

open Limits

/- 
Domain-style sampling for Lemma 12.5.4:
- primary domain: the source-facing injective/surjective/isomorphism criteria for morphisms in a
  preadditive balanced category;
- inspected owner declarations:
  `IsInjective`,
  `IsSurjective`,
  `isInjective_iff_mono`,
  `isSurjective_iff_epi`,
  `isIso_iff_mono_and_epi`,
  together with the source-facing vocabulary from Definition `12.5.3`;
- best owner abstraction: the chapter owner predicates `IsInjective f` and `IsSurjective f`,
  bridged to the categorical predicates `Mono f`, `Epi f`, and `IsIso f`;
- primitive data: a morphism `f : X ⟶ Y`;
- derived API: the equivalences `isInjective_iff_mono` and `isSurjective_iff_epi`, together with
  the source-facing criterion combining them for isomorphisms.

Source/core/bridge triage:
- `source-facing`: the textbook predicates `IsInjective f` and `IsSurjective f` from Definition
  `12.5.3`, and the criterion that an isomorphism is exactly a morphism that is both injective and
  surjective;
- `core/canonical`: `Mono f`, `Epi f`, and `IsIso f`;
- `bridge/view`: `isInjective_iff_mono`, `isSurjective_iff_epi`, and `isIso_iff_mono_and_epi`.
-/

section MonoCriterion

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {X Y : C} (f : X ⟶ Y) [HasKernel f]

/- Lemma 12.5.4 (1): the source-facing injective condition from Definition `12.5.3` is equivalent
to the owner predicate `Mono f`. -/
recall isInjective_iff_mono

end MonoCriterion

section EpiCriterion

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {X Y : C} (f : X ⟶ Y) [HasCokernel f]

/- Lemma 12.5.4 (2): dually, the source-facing surjective condition from Definition `12.5.3` is
equivalent to the owner predicate `Epi f`. -/
recall isSurjective_iff_epi

end EpiCriterion

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [Balanced C]
variable {X Y : C} (f : X ⟶ Y) [HasKernel f] [HasCokernel f]

/-
Lemma 12.5.4 (3): the canonical owner theorem for the isomorphism criterion in a balanced
category is `isIso_iff_mono_and_epi`.
-/
recall isIso_iff_mono_and_epi

/-- Lemma 12.5.4 (3): a morphism is an isomorphism exactly when it is both injective and
surjective, in the source-facing sense of Definition `12.5.3`. -/
theorem isIso_iff_isInjective_and_isSurjective :
    IsIso f ↔ IsInjective f ∧ IsSurjective f := by
  rw [isIso_iff_mono_and_epi, ← isInjective_iff_mono f, ← isSurjective_iff_epi f]

end

end CategoryTheory

/-! ### Lemma_12_5_5 (from Chap12) -/
namespace CategoryTheory

/- Lemma 12.5.5: the source sentence "all finite limits and all finite colimits exist" splits
canonically into the owner instances `Abelian.hasFiniteLimits` and
`Abelian.hasFiniteColimits`. -/
recall Abelian.hasFiniteLimits

/- Companion recall for the finite-colimit half of Lemma 12.5.5. -/
recall Abelian.hasFiniteColimits

end CategoryTheory

/-! ### Example_12_5_6 (from Chap12) -/
universe v u

namespace CategoryTheory

/- Domain-style sampling for Example 12.5.6:
- primary domain: pullbacks and pushouts in an abelian category, expressed as kernels and cokernels
  of the canonical biproduct comparison maps;
- inspected owner declarations:
  `Abelian.PullbackToBiproductIsKernel.pullbackToBiproduct`,
  `Abelian.PullbackToBiproductIsKernel.pullbackToBiproductFork`,
  `Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct`,
  `Abelian.BiproductToPushoutIsCokernel.isColimitBiproductToPushout`;
- best owner abstraction: the universal-property owners `KernelFork` / `CokernelCofork` together
  with `IsLimit` / `IsColimit`, specialized to the canonical pullback-to-biproduct and
  biproduct-to-pushout maps already provided by mathlib;
- primitive data: the canonical comparison maps `pullback a b ⟶ x ⊞ z` and
  `x' ⊞ z' ⟶ pushout f g`;
- derived API: the induced kernel fork and cokernel cofork, and the statements that they are
  limiting/colimiting.

Source/core/bridge triage:
- `source-facing`: the two textbook example statements identifying the fibre product with the
  kernel of `(a, -b)` and the pushout with the cokernel of `(f, -g)`;
- `core/canonical`: `KernelFork`, `CokernelCofork`, `IsLimit`, and `IsColimit`;
- `bridge/view`: the specialized owner declarations
  `Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct` and
  `Abelian.BiproductToPushoutIsCokernel.isColimitBiproductToPushout`, which package the
  source-facing constructions into the canonical kernel/cokernel interface.
-/

section

variable {C : Type u} [Category.{v} C] [Abelian C]

/- Example 12.5.6 (1): in an abelian category, for morphisms `a : x ⟶ y` and `b : z ⟶ y`,
the canonical map `pullback a b ⟶ x ⊞ z` exhibits the fibre product as the kernel of
`(a, -b) : x ⊞ z ⟶ y`. The owner declaration is the kernel-fork statement
`Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct`. -/
recall Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct

/- Example 12.5.6 (2): dually, for morphisms `f : y' ⟶ x'` and `g : y' ⟶ z'`, the canonical map
`x' ⊞ z' ⟶ pushout f g` exhibits the pushout as the cokernel of
`(f, -g) : y' ⟶ x' ⊞ z'`. The owner declaration is the cokernel-cofork statement
`Abelian.BiproductToPushoutIsCokernel.isColimitBiproductToPushout`. -/
recall Abelian.BiproductToPushoutIsCokernel.isColimitBiproductToPushout

end

end CategoryTheory

/-! ### Definition_12_5_7 (from Chap12) -/
universe v u

namespace CategoryTheory

/- Domain-style sampling for Definition 12.5.7:
- primary domain: exactness of finite sequences, homological complexes, and short exact sequences
  in categorical homological algebra;
- sampled canonical owner declarations:
  `ComposableArrows.IsComplex`,
  `ComposableArrows.Exact`,
  `ShortComplex.Exact`,
  `ShortComplex.toComposableArrows`,
  `ShortComplex.exact_iff_exact_toComposableArrows`,
  `HomologicalComplex.ExactAt`,
  `HomologicalComplex.Acyclic`,
  `ShortComplex.ShortExact`;
- best owner abstractions:
  `ComposableArrows C n` for finite sequences,
  `ShortComplex C` with the owner predicate `S.Exact` for three-term exact sequences,
  `HomologicalComplex C c` for complexes,
  `ShortComplex C` with the owner predicate `S.ShortExact` for short exact sequences;
- primitive data:
  the underlying finite diagram of composable arrows, the underlying homological complex, and the
  underlying short complex;
- derived API:
  the owner predicates for consecutive-zero compositions, exactness at a spot, acyclicity, and the
  bridge from a three-term short complex to `ComposableArrows C 2`;
- source/core/bridge triage:
  `source-facing`: the textbook notions of finite exact sequences, complexes exact at a term,
    acyclic complexes, exactness of a three-term sequence, and short exact sequences;
  `core/canonical`: `ComposableArrows.Exact`, `ShortComplex.Exact`,
    `HomologicalComplex.ExactAt`, `HomologicalComplex.Acyclic`, and `ShortComplex.ShortExact`;
  `bridge/view`: `ShortComplex.toComposableArrows` and
    `ShortComplex.exact_iff_exact_toComposableArrows`.

No local wrapper should be introduced here: the source notions are already owned by the canonical
mathlib declarations above. For three-term exact sequences, the main owner is `ShortComplex.Exact`,
and the comparison with finite exact sequences is already provided by the owner-side bridge from
`ShortComplex` to `ComposableArrows`.
-/

/- Definition 12.5.7 (finite sequences): for a finite sequence of composable arrows, the owner
predicate for "the composite of any two consecutive arrows is zero" is
`ComposableArrows.IsComplex`, and exactness of the whole finite sequence is
`ComposableArrows.Exact`. -/
recall ComposableArrows.IsComplex
recall ComposableArrows.Exact

/- Definition 12.5.7 (three-term sequences): for a composable pair `X₁ ⟶ X₂ ⟶ X₃` with zero
composite, the canonical owner predicate for exactness is `ShortComplex.Exact`. -/
recall ShortComplex.Exact

/- Companion bridge: for a three-term sequence `X₁ ⟶ X₂ ⟶ X₃`, exactness of the associated short
complex is transported to finite-sequence exactness by `ShortComplex.toComposableArrows`, and
`ShortComplex.exact_iff_exact_toComposableArrows` identifies it with exactness of the
corresponding object of `ComposableArrows C 2`. -/
recall ShortComplex.toComposableArrows
recall ShortComplex.exact_iff_exact_toComposableArrows

/- Definition 12.5.7 (complexes): the owner object for a complex in an additive category is
`HomologicalComplex`, with `ChainComplex` and `CochainComplex` as the standard one-sided
specializations. -/
recall HomologicalComplex
recall ChainComplex
recall CochainComplex

/- Definition 12.5.7 (exactness in a complex): exactness at a chosen object of a homological
complex is defined from the canonical associated short complex `HomologicalComplex.sc`; the owner
predicate `HomologicalComplex.ExactAt` is by definition exactness of that short complex in the
chosen degree. -/
recall HomologicalComplex.sc
recall HomologicalComplex.ExactAt
recall HomologicalComplex.exactAt_iff

/- Definition 12.5.7 (acyclicity): exactness in every degree of a homological complex is the
owner predicate `HomologicalComplex.Acyclic`. -/
recall HomologicalComplex.Acyclic
recall HomologicalComplex.acyclic_iff

/- Definition 12.5.7 (short exact sequences): the owner predicate for a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is `S.ShortExact`. -/
recall ShortComplex.ShortExact

/- The constructor `ShortComplex.ShortExact.mk'` gives the textbook formulation directly:
to build short exactness, it suffices to provide exactness together with `Mono S.f`
and `Epi S.g`. -/
recall ShortComplex.ShortExact.mk'

end CategoryTheory

/-! ### Lemma_12_5_8 (from Chap12) -/
open CategoryTheory Limits
open Opposite

universe v u

section

variable {A : Type u} [Category.{v} A] [Abelian A]

/- Domain-style sampling for Lemma 12.5.8:
- primary domain: exactness detection in abelian categories via preadditive Yoneda/coyoneda and
  pointwise exactness in functor categories;
- sampled owner declarations:
  `Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono`,
  `JointlyReflectIsomorphisms.exact_iff`,
  `NatTrans.mono_iff_mono_app`,
  `ShortComplex.exact_and_mono_f_iff_f_is_kernel`;
- best owner abstraction: the public statements remain source-facing assertions about a short
  complex `S : ShortComplex A`, while the proof layer should use the canonical functor-category
  exactness and mono owners rather than a bespoke evaluation-to-kernel wrapper;
- primitive data: `S : ShortComplex A` and the Hom functors `preadditiveYoneda.obj N` and
  `preadditiveCoyoneda.obj (op N)`;
- derived API: the pointwise exactness/mono families and the reflected kernel witnesses obtained
  from them;
- source/core/bridge triage:
  `source-facing`: the two iff-theorems below;
  `core/canonical`: the sampled owner declarations above;
  `bridge/view`: the functor-valued short complexes `S.op.map preadditiveCoyoneda` and
  `S.map preadditiveYoneda`. -/

private theorem evaluation_jointlyReflectsIsomorphisms
    (J : Type*) [Category J] (C : Type*) [Category C] :
    JointlyReflectIsomorphisms ((evaluation J C).obj : J → (J ⥤ C) ⥤ C) := by
  refine ⟨fun {X Y} f _ ↦ ?_⟩
  rw [NatTrans.isIso_iff_isIso_app]
  intro j
  simpa using (inferInstance : IsIso (((evaluation J C).obj j).map f))

/-- Lemma 12.5.8 (1): in an abelian category, a complex `M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` is exact iff for every
object `N`, the induced sequence `0 ⟶ Hom(M₃, N) ⟶ Hom(M₂, N) ⟶ Hom(M₁, N)` is exact in abelian
groups. -/
-- Proof sketch: rewrite the source condition as `S.op.Exact ∧ Mono S.op.f`, then apply the
-- canonical left-exactness criterion for `preadditiveYoneda.obj N` and reflect back through the
-- Yoneda formalism.
theorem epi_exact_iff_hom_into_exact
    (S : ShortComplex A) :
    (S.Exact ∧ Epi S.g) ↔
      ∀ N : A,
        let T := S.op.map (preadditiveYoneda.obj N)
        T.Exact ∧ Mono T.f := by
  constructor
  · rintro ⟨hS, hg⟩ N
    have hmap := ((Functor.preservesFiniteLimits_tfae (preadditiveYoneda.obj N)).out 3 1).1
      (show PreservesFiniteLimits (preadditiveYoneda.obj N) from inferInstance)
    simpa using hmap S.op ⟨hS.op, by simpa using hg⟩
  · intro h
    let T : ShortComplex (A ⥤ AddCommGrpCat.{v}) := S.op.map preadditiveCoyoneda
    let c : KernelFork S.op.g := KernelFork.ofι S.op.f S.op.zero
    have hT_exact : T.Exact := by
      exact ((evaluation_jointlyReflectsIsomorphisms A AddCommGrpCat.{v}).exact_iff T).2
        fun N ↦ by simpa [T] using (h N).1
    have hT_mono : Mono T.f := by
      rw [NatTrans.mono_iff_mono_app]
      intro N
      simpa [T] using (h N).2
    have hc : IsLimit c := by
      refine isLimitOfReflects preadditiveCoyoneda ?_
      simpa [T, c] using
        (KernelFork.isLimitMapConeEquiv c preadditiveCoyoneda).symm
          ((T.exact_and_mono_f_iff_f_is_kernel).1 ⟨hT_exact, hT_mono⟩).some
    have hSop : S.op.Exact ∧ Mono S.op.f :=
      (S.op.exact_and_mono_f_iff_f_is_kernel).2 ⟨hc⟩
    exact ⟨(S.exact_op_iff).1 hSop.1, by simpa using hSop.2⟩

/-- Lemma 12.5.8 (2): in an abelian category, a complex `0 ⟶ M₁ ⟶ M₂ ⟶ M₃` is exact iff for every
object `N`, the induced sequence `0 ⟶ Hom(N, M₁) ⟶ Hom(N, M₂) ⟶ Hom(N, M₃)` is exact in abelian
groups. -/
-- Proof sketch: apply the canonical left-exactness criterion to `preadditiveCoyoneda.obj (op N)`,
-- then jointly reflect kernels through the functor-valued Yoneda embedding `preadditiveYoneda`.
theorem mono_exact_iff_hom_from_exact
    (S : ShortComplex A) :
    (S.Exact ∧ Mono S.f) ↔
      ∀ N : A,
        let T := S.map (preadditiveCoyoneda.obj (op N))
        T.Exact ∧ Mono T.f := by
  constructor
  · rintro ⟨hS, hf⟩ N
    have hmap := ((Functor.preservesFiniteLimits_tfae (preadditiveCoyoneda.obj (op N))).out 3 1).1
      (show PreservesFiniteLimits (preadditiveCoyoneda.obj (op N)) from inferInstance)
    simpa using hmap S ⟨hS, hf⟩
  · intro h
    let T : ShortComplex (Aᵒᵖ ⥤ AddCommGrpCat.{v}) := S.map preadditiveYoneda
    let c : KernelFork S.g := KernelFork.ofι S.f S.zero
    have hT_exact : T.Exact := by
      exact ((evaluation_jointlyReflectsIsomorphisms Aᵒᵖ AddCommGrpCat.{v}).exact_iff T).2
        fun N ↦ by simpa [T] using (h N.unop).1
    have hT_mono : Mono T.f := by
      rw [NatTrans.mono_iff_mono_app]
      intro N
      simpa [T] using (h N.unop).2
    have hc : IsLimit c := by
      refine isLimitOfReflects preadditiveYoneda ?_
      simpa [T, c] using
        (KernelFork.isLimitMapConeEquiv c preadditiveYoneda).symm
          ((T.exact_and_mono_f_iff_f_is_kernel).1 ⟨hT_exact, hT_mono⟩).some
    exact (S.exact_and_mono_f_iff_f_is_kernel).2 ⟨hc⟩

end

/-! ### Definition_12_5_9 (from Chap12) -/
open CategoryTheory

universe v u

namespace CategoryTheory
namespace ShortComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (S : ShortComplex C)

/- Domain-style sampling for Definition 12.5.9:
- primary domain: split short complexes in a preadditive category;
- sampled owner API:
  `ShortComplex.Splitting`,
  `ShortComplex.Splitting.splitMono_f`,
  `ShortComplex.Splitting.splitEpi_g`,
  `ShortComplex.Splitting.isoBinaryBiproduct`;
- source/core/bridge triage:
  `source-facing`: the textbook proposition that a short complex is split, formalized as
    `Nonempty S.Splitting`;
  `core/canonical`: the owner structure `S.Splitting`;
  `bridge/view`: the existence-style reformulation below in terms of a retraction and a section.

Primitive data are exactly the retraction `r`, the section `s`, and the direct-sum identity on
`S.X₂`. The split monomorphism/epimorphism consequences and biproduct comparison are derived API
already provided upstream by the owner structure, so this file should not introduce a parallel
wrapper for that data.
-/

/- Definition 12.5.9: a short complex is split in the textbook sense exactly when the proposition
`Nonempty S.Splitting` holds. -/
#check (Nonempty S.Splitting)

/- Companion recall: `S.Splitting` is the canonical owner for chosen splitting data. Its primitive
data are a retraction of `S.f`, a section of `S.g`, and the direct-sum identity on `S.X₂`. -/
recall Splitting

/-- Source-facing bridge for the textbook formulation of a split short complex. -/
theorem nonempty_splitting_iff :
    Nonempty S.Splitting ↔
      ∃ (r : S.X₂ ⟶ S.X₁) (s : S.X₃ ⟶ S.X₂),
        S.f ≫ r = 𝟙 S.X₁ ∧ s ≫ S.g = 𝟙 S.X₃ ∧ r ≫ S.f + S.g ≫ s = 𝟙 S.X₂ := by
  constructor
  · rintro ⟨σ⟩
    exact ⟨σ.r, σ.s, σ.f_r, σ.s_g, σ.id⟩
  · rintro ⟨r, s, hr, hs, hid⟩
    exact ⟨⟨r, s, hr, hs, hid⟩⟩

end ShortComplex
end CategoryTheory

/-! ### Lemma_12_5_10 (from Chap12) -/
open CategoryTheory Limits

universe v u

namespace CategoryTheory
namespace ShortComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [Balanced C]
variable {S : ShortComplex C}

/- Domain-style sampling for Lemma 12.5.10:
- primary domain: splittings of exact short complexes in a preadditive balanced category;
- sampled owner API:
  `ShortComplex.Splitting`,
  `ShortComplex.Splitting.ext_r`,
  `ShortComplex.Splitting.ext_s`,
  `ShortComplex.Splitting.ofExactOfSection`,
  `ShortComplex.Splitting.ofExactOfRetraction`;
- source/core/bridge triage:
  `source-facing`: the two complementary existence-and-uniqueness statements from the source;
  `core/canonical`: the owner structure `S.Splitting`;
  `bridge/view`: extracting the complementary retraction or section from a chosen splitting.

Primitive data already live in the owner `S.Splitting`: a retraction, a section, and the splitting
identity. The local uniqueness package for splittings is therefore derived API, so this file
should state only the source-facing complementary-map lemmas and prove them directly from the
canonical owner constructors and extensionality lemmas.
-/

open Splitting

/-- Lemma 12.5.10 (1): in a short exact sequence, a chosen section of the quotient map determines
uniquely the complementary retraction on the subobject map making the sequence split. -/
theorem existsUnique_retraction_of_shortExact_of_section
    (hS : S.Exact) [Mono S.f] (s : S.X₃ ⟶ S.X₂) (hs : s ≫ S.g = 𝟙 S.X₃) :
    ∃! r : S.X₂ ⟶ S.X₁, S.f ≫ r = 𝟙 S.X₁ ∧ r ≫ S.f + S.g ≫ s = 𝟙 S.X₂ := by
  let σ : S.Splitting := ofExactOfSection S hS s hs inferInstance
  refine ⟨σ.r, ⟨σ.f_r, by simpa [σ] using σ.id⟩, ?_⟩
  intro r hr
  let τ : S.Splitting := { r := r, s := s, f_r := hr.1, s_g := hs, id := hr.2 }
  have hτ : τ = σ := ext_s τ σ rfl
  simpa [τ, σ] using congrArg Splitting.r hτ

/-- Lemma 12.5.10 (2): in a short exact sequence, a chosen retraction of the subobject map
determines uniquely the complementary section of the quotient map making the sequence split. -/
theorem existsUnique_section_of_shortExact_of_retraction
    (hS : S.Exact) [Epi S.g] (r : S.X₂ ⟶ S.X₁) (hr : S.f ≫ r = 𝟙 S.X₁) :
    ∃! s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 S.X₃ ∧ r ≫ S.f + S.g ≫ s = 𝟙 S.X₂ := by
  let σ : S.Splitting := ofExactOfRetraction S hS r hr inferInstance
  refine ⟨σ.s, ⟨σ.s_g, by simpa [σ] using σ.id⟩, ?_⟩
  intro s hs
  let τ : S.Splitting := { r := r, s := s, f_r := hr, s_g := hs.1, id := hs.2 }
  have hτ : τ = σ := ext_r τ σ rfl
  simpa [τ, σ] using congrArg Splitting.s hτ

end ShortComplex
end CategoryTheory

/-! ### Lemma_12_5_11 (from Chap12) -/
noncomputable section

open CategoryTheory Limits ZeroObject ComposableArrows

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {W X Y Z : C} {f : W ⟶ Y} {g : W ⟶ X} {h : Y ⟶ Z} {k : X ⟶ Z}

/-- Lemma 12.5.11 (1): a commutative square in an abelian category is cartesian if and only if
the sequence `0 ⟶ W ⟶ X ⊞ Y ⟶ Z` with maps `(g, f)` and `(k, -h)` is exact. -/
theorem isPullback_iff_exact_biproduct_sequence
    (sq : CommSq g f k h) :
    IsPullback g f k h ↔ (mk₃ (0 : 0 ⟶ W) sq.shortComplex'.f sq.shortComplex'.g).Exact := by
  constructor
  · intro hsq
    let S : ShortComplex C := .mk (0 : 0 ⟶ W) sq.shortComplex'.f
      (by simpa using (show (0 : 0 ⟶ W) ≫ sq.shortComplex'.f = 0 from zero_comp))
    have h₀ : (mk₂ (0 : 0 ⟶ W) sq.shortComplex'.f).Exact := by
      change S.toComposableArrows.Exact
      rw [← S.exact_iff_exact_toComposableArrows]
      exact (S.exact_iff_mono (by rfl)).2 hsq.mono_shortComplex'_f
    have hδ₀ : (mk₃ (0 : 0 ⟶ W) sq.shortComplex'.f sq.shortComplex'.g).δ₀.Exact := by
      simpa [ComposableArrows.δ₀, ShortComplex.toComposableArrows] using
        hsq.exact_shortComplex'.exact_toComposableArrows
    exact ComposableArrows.exact_of_δ₀ h₀ hδ₀
  · intro hExact
    have hsplit := (ComposableArrows.exact_iff_δ₀
      (mk₃ (0 : 0 ⟶ W) sq.shortComplex'.f sq.shortComplex'.g)).1 hExact
    let S : ShortComplex C := .mk (0 : 0 ⟶ W) sq.shortComplex'.f
      (by simpa using (show (0 : 0 ⟶ W) ≫ sq.shortComplex'.f = 0 from zero_comp))
    have hmono' : Mono sq.shortComplex'.f := by
      exact (S.exact_iff_mono (by rfl)).1 <| by
        rw [S.exact_iff_exact_toComposableArrows]
        change (mk₂ (0 : 0 ⟶ W) sq.shortComplex'.f).Exact
        exact hsplit.1
    have hexact' : sq.shortComplex'.Exact := by
      rw [sq.shortComplex'.exact_iff_exact_toComposableArrows]
      simpa [ComposableArrows.δ₀, ShortComplex.toComposableArrows] using hsplit.2
    refine IsPullback.of_isLimit ((sq.isLimitEquivIsLimitKernelFork).symm ?_)
    exact ((sq.shortComplex').exact_and_mono_f_iff_f_is_kernel.mp ⟨hexact', hmono'⟩).some
/-- Lemma 12.5.11 (2): a commutative square in an abelian category is cocartesian if and only if
the sequence `W ⟶ X ⊞ Y ⟶ Z ⟶ 0` with maps `(g, -f)` and `(k, h)` is exact. -/
theorem isPushout_iff_exact_biproduct_sequence
    (sq : CommSq g f k h) :
    IsPushout g f k h ↔ (mk₃ sq.shortComplex.f sq.shortComplex.g (0 : Z ⟶ 0)).Exact := by
  let zToZero := (0 : Z ⟶ 0)
  constructor
  · intro hsq
    have hδlast :
        (mk₃ sq.shortComplex.f sq.shortComplex.g zToZero).δlast.Exact := by
      refine ComposableArrows.exact₂_mk _ ?_ ?_
      · change sq.shortComplex.f ≫ sq.shortComplex.g = 0
        exact sq.shortComplex.zero
      simpa [ComposableArrows.δlast, zToZero, ShortComplex.toComposableArrows] using
        hsq.exact_shortComplex
    let S : ShortComplex C := .mk sq.shortComplex.g zToZero
      (by simpa [zToZero] using (show sq.shortComplex.g ≫ (0 : Z ⟶ 0) = 0 from comp_zero))
    have h₂ : (mk₂ sq.shortComplex.g zToZero).Exact := by
      change S.toComposableArrows.Exact
      rw [← S.exact_iff_exact_toComposableArrows]
      exact (S.exact_iff_epi (by rfl)).2 hsq.epi_shortComplex_g
    exact ComposableArrows.exact_of_δlast (mk₃ sq.shortComplex.f sq.shortComplex.g zToZero)
      hδlast h₂
  · intro hExact
    have hsplit := (ComposableArrows.exact_iff_δlast
      (mk₃ sq.shortComplex.f sq.shortComplex.g zToZero)).1 hExact
    let S : ShortComplex C := .mk sq.shortComplex.g zToZero
      (by simpa [zToZero] using (show sq.shortComplex.g ≫ (0 : Z ⟶ 0) = 0 from comp_zero))
    have hexact : sq.shortComplex.Exact := by
      simpa [ComposableArrows.δlast, zToZero, ShortComplex.toComposableArrows] using
        (ComposableArrows.exact₂_iff
          ((mk₃ sq.shortComplex.f sq.shortComplex.g zToZero).δlast) hsplit.1.toIsComplex).1
          hsplit.1
    have hepι : Epi sq.shortComplex.g := by
      exact (S.exact_iff_epi (by rfl)).1 <| by
        rw [S.exact_iff_exact_toComposableArrows]
        change (mk₂ sq.shortComplex.g zToZero).Exact
        exact hsplit.2
    refine IsPushout.of_isColimit ((sq.isColimitEquivIsColimitCokernelCofork).symm ?_)
    exact ((sq.shortComplex).exact_and_epi_g_iff_g_is_cokernel.mp ⟨hexact, hepι⟩).some

end CategoryTheory

/-! ### Lemma_12_5_12 (from Chap12) -/
namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {W X Y Z : C} {f : W ⟶ Y} {g : W ⟶ X} {h : Y ⟶ Z} {k : X ⟶ Z}

/-
Domain-style sampling for Lemma 12.5.12:
- primary domain: kernel and cokernel comparison morphisms associated to pullback and pushout
  squares in a category with zero morphisms;
- sampled owner declarations:
  `kernel.map`,
  `cokernel.map`,
  `isIso_kernel_map_of_isPullback`,
  `isIso_cokernel_map_of_isPushout`;
- best owner abstraction: the mathlib owner theorems
  `isIso_kernel_map_of_isPullback` and `isIso_cokernel_map_of_isPushout`;
- primitive data: a pullback or pushout square together with the existing kernel or cokernel
  objects on the relevant vertical morphisms;
- derived API: the vertical comparison statements obtained canonically from those owner theorems by
  flipping the square.

Source/core/bridge triage:
- `source-facing`: the Stacks formulation comparing the kernels or cokernels of the vertical maps;
- `core/canonical`: the owner theorems for the horizontal comparison maps;
- `bridge/view`: the source-facing vertical specialization theorems below, derived from `sq.flip`.

This numbered item is therefore bridge-only: the canonical owner theorems already exist upstream,
so the refined file should recall them directly and keep only thin named companion theorems for
the vertical Stacks formulations.
-/

/- Lemma 12.5.12, core/canonical recall: in a pullback square, the canonical horizontal kernel map
is an isomorphism. -/
recall isIso_kernel_map_of_isPullback

/- Lemma 12.5.12 (1), source-facing specialization: for a cartesian square, the induced morphism
`kernel f ⟶ kernel k` between the kernels of the vertical maps is the canonical isomorphism
obtained by applying `isIso_kernel_map_of_isPullback` to the flipped square. -/
theorem isIso_kernel_map_vertical_of_isPullback [HasKernel f] [HasKernel k]
    (sq : IsPullback g f k h) :
    IsIso (kernel.map f k g h sq.w.symm) := by
  simpa using isIso_kernel_map_of_isPullback sq.flip

/- Lemma 12.5.12, core/canonical recall: in a pushout square, the canonical horizontal cokernel
map is an isomorphism. -/
recall isIso_cokernel_map_of_isPushout

/- Lemma 12.5.12 (2), source-facing specialization: for a cocartesian square, the induced
morphism `cokernel f ⟶ cokernel k` between the cokernels of the vertical maps is the canonical
isomorphism obtained by applying `isIso_cokernel_map_of_isPushout` to the flipped square. -/
theorem isIso_cokernel_map_vertical_of_isPushout [HasCokernel f] [HasCokernel k]
    (sq : IsPushout g f k h) :
    IsIso (cokernel.map f k g h sq.w.symm) := by
  simpa using isIso_cokernel_map_of_isPushout sq.flip

end CategoryTheory.Limits

/-! ### Lemma_12_5_13 (from Chap12) -/
open CategoryTheory Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {W X Y Z : C} {f : W ⟶ Y} {g : W ⟶ X} {h : Y ⟶ Z} {k : X ⟶ Z}

/-- Lemma 12.5.13 (1): in an abelian category, a cartesian square whose right morphism is an
epimorphism is cocartesian. -/
theorem isPushout_of_isPullback_of_epi_right [Epi k] (sq : IsPullback g f k h) :
    IsPushout g f k h := by
  let S := sq.toCommSq
  let e : S.shortComplex' ≅ S.shortComplex :=
    ShortComplex.isoMk (Iso.refl _) (biprod.mapIso (Iso.refl X) (-Iso.refl Y)) (Iso.refl _)
      (by
        apply biprod.hom_ext <;> simp)
      (by
        apply biprod.hom_ext' <;> simp)
  let T := S.shortComplex
  have hExact : T.Exact :=
    ShortComplex.exact_of_iso e sq.exact_shortComplex'
  letI : Epi T.g := by
    change Epi (biprod.desc k h)
    infer_instance
  obtain ⟨hT⟩ := T.exact_and_epi_g_iff_g_is_cokernel.1 ⟨hExact, inferInstance⟩
  exact IsPushout.of_isColimit (S.isColimitEquivIsColimitCokernelCofork.symm hT)

/-- Lemma 12.5.13 (2): in an abelian category, in a cartesian square, if the right morphism is
an epimorphism, then the left morphism is an epimorphism. -/
theorem epi_left_of_isPullback_of_epi_right [Epi k] (sq : IsPullback g f k h) :
    Epi f := by
  simpa using Abelian.epi_snd_of_isLimit k h sq.isLimit

/-- Lemma 12.5.13 (3): in an abelian category, a cocartesian square whose top morphism is a
monomorphism is cartesian. -/
theorem isPullback_of_isPushout_of_mono_top [Mono g] (sq : IsPushout g f k h) :
    IsPullback g f k h := by
  let sqOp : IsPullback k.op h.op g.op f.op := sq.flip.op
  exact (isPushout_of_isPullback_of_epi_right sqOp).unop.flip

/-- Lemma 12.5.13 (4): in an abelian category, in a cocartesian square, if the top morphism is a
monomorphism, then the bottom morphism is a monomorphism. -/
theorem mono_bottom_of_isPushout_of_mono_top [Mono g] (sq : IsPushout g f k h) :
    Mono h := by
  simpa using Abelian.mono_inr_of_isColimit g f sq.isColimit

end CategoryTheory

/-! ### Lemma_12_5_14 (from Chap12) -/
namespace CategoryTheory

/- Domain-style sampling for Lemma 12.5.14:
- primary domain: stability of epimorphisms and monomorphisms under pullback and pushout in an
  abelian category;
- inspected owner declarations:
  `Abelian.epi_pullback_of_epi_f`,
  `Abelian.epi_pullback_of_epi_g`,
  `Abelian.mono_pushout_of_mono_f`,
  `Abelian.mono_pushout_of_mono_g`;
- best owner abstraction: the categorical owner predicates `Epi` and `Mono`, with the canonical
  stability results already owned by `CategoryTheory.Abelian`;
- primitive data: a pullback or pushout square together with an epic or monic edge;
- derived API: the induced epic or monic structure on the opposite projection or inclusion.

Source/core/bridge triage:
- `source-facing`: the textbook statements that surjections stay surjective after pullback and
  injections stay injective after pushout;
- `core/canonical`: the owner instances `Epi (pullback.snd f g)` and
  `Mono (pushout.inr f g : Z ⟶ pushout f g)`;
- `bridge/view`: this file is recall-only, so it should use the upstream owners directly rather
  than restating their full interfaces locally.
-/

/- Lemma 12.5.14 (1): in an abelian category, if `x ⟶ y` is surjective, then for every
`z ⟶ y` the projection `x ×_y z ⟶ z` is surjective. This is the canonical abelian-category
statement that pullbacks preserve epimorphisms. -/
recall Abelian.epi_pullback_of_epi_f

/- Lemma 12.5.14 (2): in an abelian category, if `x ⟶ y` is injective, then for every
`x ⟶ z` the canonical morphism `z ⟶ z ⨿_x y` is injective. This is the canonical
abelian-category statement that pushouts preserve monomorphisms. -/
recall Abelian.mono_pushout_of_mono_f

end CategoryTheory

/-! ### Lemma_12_5_15 (from Chap12) -/
universe v u

namespace CategoryTheory

/- Domain-style sampling for Lemma 12.5.15:
- primary domain: exactness criteria for short complexes in abelian categories, expressed by
  lifting morphisms after refinement by an epimorphism;
- inspected owner declarations:
  `ShortComplex.Exact`,
  `ShortComplex.exact_iff_exact_toComposableArrows`,
  `ShortComplex.exact_iff_exact_up_to_refinements`,
  `ShortComplex.Exact.exact_up_to_refinements`;
- best owner abstraction: `ShortComplex C` with the owner predicate `S.Exact`; the refinement
  criterion is derived API already owned upstream by
  `ShortComplex.exact_iff_exact_up_to_refinements`, and the pointwise lifting form is the
  theorem-level view rather than new primitive data;
- primitive data: the short complex `S`;
- derived API: the refinement-lifting characterization of `S.Exact` and the forward lifting
  operation exposed by `ShortComplex.Exact.exact_up_to_refinements`.

Source/core/bridge triage:
- `source-facing`: the textbook criterion that `x₁ ⟶ x₂ ⟶ x₃` is exact iff every morphism into the
  middle term killed by the second map lifts through the first map after refining the source by an
  epimorphism;
- `core/canonical`: the owner predicate `ShortComplex.Exact`;
- `bridge/view`: `ShortComplex.exact_iff_exact_up_to_refinements`, which is already the exact
  canonical bridge theorem for this criterion.

This file should stay recall-only: the source statement is already owned upstream with the correct
short-complex abstraction, so a local restatement or wrapper would only duplicate the API.
-/

variable {C : Type u} [Category.{v} C] [Abelian C]

/- Lemma 12.5.15: in an abelian category, a short complex is exact if and only if every morphism
into the middle object that is killed by the second map lifts through the first map after
precomposition by some epimorphism. Applied to `ShortComplex.mk f g h`, this is exactly the
textbook criterion for the exactness of `x ⟶ y ⟶ z`. -/
recall ShortComplex.exact_iff_exact_up_to_refinements (S : ShortComplex C) :
    S.Exact ↔
      ∀ ⦃A : C⦄ (x₂ : A ⟶ S.X₂) (_ : x₂ ≫ S.g = 0),
        ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = x₁ ≫ S.f

end CategoryTheory

/-! ### Lemma_12_5_16 (from Chap12) -/
universe v u

namespace CategoryTheory

open Category Limits
open ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)

/- Domain-style sampling for Lemma 12.5.16:
- primary domain: exactness of the kernel and cokernel rows induced by a morphism of short
  complexes in an abelian category;
- inspected owner declarations:
  `ShortComplex.exact_iff_exact_up_to_refinements`,
  `ShortComplex.Exact.exact_up_to_refinements`,
  `ShortComplex.exact_unop_iff`,
  `CategoryTheory.kernelOpUnop`;
- best owner abstraction: `ShortComplex.Exact`, accessed through the refinement criterion
  `exact_up_to_refinements`, is the core exactness owner matching the textbook assumptions, while
  the induced kernel and cokernel rows themselves are built canonically from `kernel.map` and
  `cokernel.map`; the stronger snake-lemma owner `ShortComplex.SnakeInput` packages extra endpoint
  exactness hypotheses that this lemma does not assume;
- primitive data: a morphism `φ : S₁ ⟶ S₂`, exactness of one horizontal row, and one endpoint
  mono/epi hypothesis;
- derived API: exactness of the induced row on kernels or cokernels.

Source/core/bridge triage:
- `source-facing`: the two exactness statements for the kernel row and cokernel row of `φ`;
- `core/canonical`: `ShortComplex.Exact.exact_up_to_refinements`, `kernel.map`, `cokernel.map`,
  and the opposite-category comparison isomorphisms;
- `bridge/view`: this file keeps the source-facing theorem names, but rewrites them directly in
  terms of the core owner API instead of introducing parallel local row definitions.
-/

private noncomputable abbrev kernelRow (φ : S₁ ⟶ S₂) : ShortComplex C :=
  ShortComplex.mk
    (kernel.map φ.τ₁ φ.τ₂ S₁.f S₂.f φ.comm₁₂)
    (kernel.map φ.τ₂ φ.τ₃ S₁.g S₂.g φ.comm₂₃)

private noncomputable abbrev cokernelRow (φ : S₁ ⟶ S₂) : ShortComplex C :=
  ShortComplex.mk
    (cokernel.map φ.τ₁ φ.τ₂ S₁.f S₂.f φ.comm₁₂)
    (cokernel.map φ.τ₂ φ.τ₃ S₁.g S₂.g φ.comm₂₃)

private noncomputable def cokernelRowIsoUnopKernelRowOpMap (φ : S₁ ⟶ S₂) :
    cokernelRow φ ≅ (kernelRow (opMap φ)).unop :=
  ShortComplex.isoMk
    (kernelOpUnop φ.τ₁).symm
    (kernelOpUnop φ.τ₂).symm
    (kernelOpUnop φ.τ₃).symm
    (by
      have hπ₁ :
          cokernel.π φ.τ₁ ≫ (kernelOpUnop φ.τ₁).symm.hom =
            (kernel.ι (φ.τ₁.op)).unop := by
        simpa using (kernel.ι_op φ.τ₁).symm
      have hπ₂ :
          cokernel.π φ.τ₂ ≫ (kernelOpUnop φ.τ₂).symm.hom =
            (kernel.ι (φ.τ₂.op)).unop := by
        simpa using (kernel.ι_op φ.τ₂).symm
      have hK :
          (kernelRow (opMap φ)).g ≫ kernel.ι (φ.τ₁.op) =
            kernel.ι (φ.τ₂.op) ≫ S₂.f.op := by
        change
          kernel.map (opMap φ).τ₂ (opMap φ).τ₃ (S₂.op).g (S₁.op).g (opMap φ).comm₂₃ ≫
              kernel.ι (φ.τ₁.op) =
            kernel.ι (φ.τ₂.op) ≫ S₂.f.op
        simp [kernel.map]
      apply (cancel_epi (cokernel.π φ.τ₁)).1
      calc
        cokernel.π φ.τ₁ ≫ (kernelOpUnop φ.τ₁).symm.hom ≫ (kernelRow (opMap φ)).unop.f =
            (kernel.ι (φ.τ₁.op)).unop ≫ (kernelRow (opMap φ)).unop.f := by
          simpa [assoc] using congrArg (fun k ↦ k ≫ (kernelRow (opMap φ)).unop.f) hπ₁
        _ = S₂.f ≫ (kernel.ι (φ.τ₂.op)).unop := by
          change ((kernelRow (opMap φ)).g ≫ kernel.ι (φ.τ₁.op)).unop =
            (kernel.ι (φ.τ₂.op) ≫ S₂.f.op).unop
          exact congrArg Quiver.Hom.unop hK
        _ = S₂.f ≫ cokernel.π φ.τ₂ ≫ (kernelOpUnop φ.τ₂).symm.hom := by
          simpa [assoc] using congrArg (fun k ↦ S₂.f ≫ k) hπ₂.symm
        _ = cokernel.π φ.τ₁ ≫ cokernel.map φ.τ₁ φ.τ₂ S₁.f S₂.f φ.comm₁₂ ≫
              (kernelOpUnop φ.τ₂).symm.hom := by
          simp [cokernel.map, assoc])
    (by
      have hπ₂ :
          cokernel.π φ.τ₂ ≫ (kernelOpUnop φ.τ₂).symm.hom =
            (kernel.ι (φ.τ₂.op)).unop := by
        simpa using (kernel.ι_op φ.τ₂).symm
      have hπ₃ :
          cokernel.π φ.τ₃ ≫ (kernelOpUnop φ.τ₃).symm.hom =
            (kernel.ι (φ.τ₃.op)).unop := by
        simpa using (kernel.ι_op φ.τ₃).symm
      have hK :
          (kernelRow (opMap φ)).f ≫ kernel.ι (φ.τ₂.op) =
            kernel.ι (φ.τ₃.op) ≫ S₂.g.op := by
        change
          kernel.map (opMap φ).τ₁ (opMap φ).τ₂ (S₂.op).f (S₁.op).f (opMap φ).comm₁₂ ≫
              kernel.ι (φ.τ₂.op) =
            kernel.ι (φ.τ₃.op) ≫ S₂.g.op
        simp [kernel.map]
      apply (cancel_epi (cokernel.π φ.τ₂)).1
      calc
        cokernel.π φ.τ₂ ≫ (kernelOpUnop φ.τ₂).symm.hom ≫ (kernelRow (opMap φ)).unop.g =
            (kernel.ι (φ.τ₂.op)).unop ≫ (kernelRow (opMap φ)).unop.g := by
          simpa [assoc] using congrArg (fun k ↦ k ≫ (kernelRow (opMap φ)).unop.g) hπ₂
        _ = S₂.g ≫ (kernel.ι (φ.τ₃.op)).unop := by
          change ((kernelRow (opMap φ)).f ≫ kernel.ι (φ.τ₂.op)).unop =
            (kernel.ι (φ.τ₃.op) ≫ S₂.g.op).unop
          exact congrArg Quiver.Hom.unop hK
        _ = S₂.g ≫ cokernel.π φ.τ₃ ≫ (kernelOpUnop φ.τ₃).symm.hom := by
          simpa [assoc] using congrArg (fun k ↦ S₂.g ≫ k) hπ₃.symm
        _ = cokernel.π φ.τ₂ ≫ cokernel.map φ.τ₂ φ.τ₃ S₁.g S₂.g φ.comm₂₃ ≫
              (kernelOpUnop φ.τ₃).symm.hom := by
          simp [cokernel.map, assoc])

/-- Lemma 12.5.16 (1): for a morphism of short complexes in an abelian category, if the source row
is exact and the first map in the target row is a monomorphism, then the induced sequence on the
kernels of the vertical morphisms is exact. -/
-- Proof sketch: apply the canonical lifting operation for exact short complexes to
-- `x₂ ≫ kernel.ι φ.τ₂`. Exactness of `S₁` and monicity of `S₂.f` give the needed lift to
-- `kernel φ.τ₁`, and the result is exactly the kernel row built from `kernel.map`.
theorem kernel_sequence_exact_of_exact_of_mono (hS₁ : S₁.Exact) [Mono S₂.f] :
    (ShortComplex.mk
      (kernel.map φ.τ₁ φ.τ₂ S₁.f S₂.f φ.comm₁₂)
      (kernel.map φ.τ₂ φ.τ₃ S₁.g S₂.g φ.comm₂₃)).Exact := by
  let K := kernelRow φ
  change K.Exact
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  obtain ⟨A₁, π₁, hπ₁, y₁, hy₁⟩ := hS₁.exact_up_to_refinements (x₂ ≫ kernel.ι φ.τ₂) (by
    have hx₂' : x₂ ≫ K.g ≫ kernel.ι φ.τ₃ = 0 := by
      simpa [assoc] using hx₂ =≫ kernel.ι φ.τ₃
    simpa [K, kernel.map, assoc] using hx₂')
  have hy₁' : y₁ ≫ φ.τ₁ = 0 := by
    have hx₂' : x₂ ≫ kernel.ι φ.τ₂ ≫ φ.τ₂ = 0 := by
      simpa [assoc] using congrArg (fun t ↦ x₂ ≫ t) (kernel.condition φ.τ₂)
    have hy₁'' : y₁ ≫ S₁.f ≫ φ.τ₂ = 0 := by
      have hcomp : π₁ ≫ x₂ ≫ kernel.ι φ.τ₂ ≫ φ.τ₂ = 0 := by
        simpa [assoc] using congrArg (fun t ↦ π₁ ≫ t) hx₂'
      calc
        y₁ ≫ S₁.f ≫ φ.τ₂ = π₁ ≫ x₂ ≫ kernel.ι φ.τ₂ ≫ φ.τ₂ := by
          simpa [assoc] using congrArg (fun t ↦ t ≫ φ.τ₂) hy₁.symm
        _ = 0 := hcomp
    apply (cancel_mono S₂.f).1
    simpa [assoc, φ.comm₁₂] using hy₁''
  refine ⟨A₁, π₁, hπ₁, kernel.lift φ.τ₁ y₁ hy₁', ?_⟩
  apply (cancel_mono (kernel.ι φ.τ₂)).1
  simpa [K, kernel.map, assoc] using hy₁

/-- Lemma 12.5.16 (2): for a morphism of short complexes in an abelian category, if the target row
is exact and the second map in the source row is an epimorphism, then the induced sequence on the
cokernels of the vertical morphisms is exact. -/
-- Proof sketch: apply part (1) in the opposite category to `ShortComplex.opMap φ`, then transport
-- the resulting exactness statement to the canonical cokernel row using the standard
-- abelian-opposite comparison isomorphisms.
theorem cokernel_sequence_exact_of_exact_of_epi (hS₂ : S₂.Exact) [Epi S₁.g] :
    (ShortComplex.mk
      (cokernel.map φ.τ₁ φ.τ₂ S₁.f S₂.f φ.comm₁₂)
      (cokernel.map φ.τ₂ φ.τ₃ S₁.g S₂.g φ.comm₂₃)).Exact := by
  let K := kernelRow (opMap φ)
  change (cokernelRow φ).Exact
  letI : Mono (S₁.op).f := by
    dsimp [ShortComplex.op]
    infer_instance
  have hK : K.Exact := by
    simpa [K] using kernel_sequence_exact_of_exact_of_mono (opMap φ) hS₂.op
  exact (ShortComplex.exact_iff_of_iso (cokernelRowIsoUnopKernelRowOpMap φ)).2
    ((ShortComplex.exact_unop_iff K).2 hK)

end CategoryTheory

/-! ### Lemma_12_5_17 (from Chap12) -/
universe v u

namespace CategoryTheory

/- Domain-style sampling for Lemma 12.5.17:
- primary domain: the snake lemma in an abelian category, packaged as a commutative diagram of
  short complexes with exact rows and kernel/cokernel endpoint data;
- sampled owner declarations:
  `ShortComplex.SnakeInput.δ`,
  `ShortComplex.SnakeInput.snd_δ_inr`,
  `ShortComplex.SnakeInput.snake_lemma`,
  `ShortComplex.SnakeInput.mono_L₀_f`,
  `ShortComplex.SnakeInput.epi_L₃_g`;
- best owner abstraction:
  `source-facing`: the connecting morphism, its characteristic square, the exact six-term snake
    sequence, and the endpoint mono/epi consequences stated in Lemma 12.5.17;
  `core/canonical`: the owner `ShortComplex.SnakeInput`;
  `bridge/view`: none is needed here, because the textbook kernel-cokernel sequence already
    appears as owner-derived API;
- primitive data vs derived API: the primitive data are the four short complexes, the vertical
  comparison morphisms, exactness of the middle rows, and the kernel/cokernel endpoint data
  bundled by `ShortComplex.SnakeInput`; the connecting morphism `δ`, the pullback-pushout square
  `snd_δ_inr`, the exact snake sequence `snake_lemma`, and the induced mono/epi results are all
  derived API, so this file should recall those canonical declarations directly rather than
  repackage them through local aliases or wrapper statements.
-/

/- Lemma 12.5.17 (1): for a snake input encoding a commutative diagram with exact rows in an
abelian category, the connecting morphism `ker γ ⟶ coker α` is the canonical boundary map
`S.δ : S.L₀.X₃ ⟶ S.L₃.X₁` provided by the snake-lemma owner abstraction. -/
recall ShortComplex.SnakeInput.δ

/- Companion recall: the canonical connecting morphism `S.δ` satisfies the textbook
pullback-pushout commutative square that characterizes the snake-lemma boundary map. -/
recall ShortComplex.SnakeInput.snd_δ_inr

/- Lemma 12.5.17 (2): the induced sequence on kernels, the connecting morphism, and cokernels is
exact. In the `SnakeInput` notation this is exactly the six-term snake-lemma sequence
`S.L₀.X₁ ⟶ S.L₀.X₂ ⟶ S.L₀.X₃ ⟶ S.L₃.X₁ ⟶ S.L₃.X₂ ⟶ S.L₃.X₃`. -/
recall ShortComplex.SnakeInput.snake_lemma

/- Lemma 12.5.17 (3): if the left map in the top exact row is injective, then the induced map on
kernels `ker α ⟶ ker β` is injective. In `SnakeInput` notation this is the monomorphism
`S.L₀.f`. -/
recall ShortComplex.SnakeInput.mono_L₀_f

/- Lemma 12.5.17 (4): if the right map in the bottom exact row is surjective, then the induced map
on cokernels `coker β ⟶ coker γ` is surjective. In `SnakeInput` notation this is the epimorphism
`S.L₃.g`. -/
recall ShortComplex.SnakeInput.epi_L₃_g

end CategoryTheory

/-! ### Lemma_12_5_18 (from Chap12) -/
namespace CategoryTheory

/- Lemma 12.5.18: for a morphism of snake inputs coming from a commutative diagram with exact
rows in an abelian category, the induced morphisms on kernels, connecting morphisms, and
cokernels assemble into a morphism between the associated six-term snake-lemma diagrams.
Equivalently, the induced kernel-cokernel diagram commutes. -/
recall ShortComplex.SnakeInput.composableArrowsFunctor

/- Companion recall: the central square in the induced diagram commutes, i.e. the connecting
morphisms are natural with respect to morphisms of snake inputs. -/
recall ShortComplex.SnakeInput.naturality_δ

end CategoryTheory

/-! ### Lemma_12_5_19 (from Chap12) -/
namespace CategoryTheory

/- Domain-style sampling for Lemma 12.5.19:
- primary domain: the four lemma in an abelian category, expressed for a morphism of exact
  four-term diagrams, i.e. a morphism `φ : R₁ ⟶ R₂` in `ComposableArrows C 3`;
- sampled owner declarations:
  `Abelian.mono_of_epi_of_mono_of_mono`,
  `Abelian.epi_of_epi_of_epi_of_mono`,
  `Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`,
  `ComposableArrows.Exact`;
- best owner abstraction:
  `source-facing`: the mono and epi forms of the four lemma stated in the source;
  `core/canonical`: the owner theorems
    `Abelian.mono_of_epi_of_mono_of_mono` and `Abelian.epi_of_epi_of_epi_of_mono` for exact
    morphisms of `ComposableArrows C 3`;
  `bridge/view`: none is needed here, because the source statements already coincide with the
    upstream owner-level theorems;
- primitive data vs derived API: the primitive data are the morphism of four-term diagrams and the
  exactness of the two rows, encoded by `φ : R₁ ⟶ R₂` with `R₁.Exact` and `R₂.Exact`; the mono and
  epi conclusions are derived API owned upstream, so any local restatement would only duplicate
  the canonical chapter/mathlib interface.

This file should stay recall-only: the source mathematics is already represented by the correct
owner abstraction, so the refined public surface is direct canonical recall rather than a local
wrapper or compatibility theorem.
-/

/- Lemma 12.5.19 (1): for a commutative diagram of four-term complexes with exact rows in an
abelian category, if the first and third vertical maps are epimorphisms and the fourth vertical
map is a monomorphism, then the second vertical map is an epimorphism. -/
recall Abelian.epi_of_epi_of_epi_of_mono

/- Lemma 12.5.19 (2): for a commutative diagram of four-term complexes with exact rows in an
abelian category, if the first vertical map is an epimorphism and the second and fourth vertical
maps are monomorphisms, then the third vertical map is a monomorphism. -/
recall Abelian.mono_of_epi_of_mono_of_mono

end CategoryTheory

/-! ### Lemma_12_5_20 (from Chap12) -/
namespace CategoryTheory

/- Domain-style sampling for Lemma 12.5.20:
- primary domain: abelian-category diagram lemmas for morphisms between exact rows;
- inspected owner declarations:
  `Abelian.mono_of_epi_of_mono_of_mono`,
  `Abelian.epi_of_epi_of_epi_of_mono`,
  `Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`;
- best owner abstraction: the canonical mathlib five-lemma owner
  `Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`;
- primitive data: a morphism `φ : R₁ ⟶ R₂` of length-`5` composable-arrow diagrams together with
  exactness of the two rows and the endpoint epi/mono hypotheses;
- derived API: the conclusion that the middle vertical morphism is an isomorphism.

Source/core/bridge triage:
- `source-facing`: the Stacks five-lemma statement for a commutative diagram with exact rows in an
  abelian category;
- `core/canonical`: `Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`;
- `bridge/view`: none needed here, because the textbook statement already matches the owner theorem.

This item is recall-only: there is no local source-facing wrapper to preserve, and adding one would
only duplicate the upstream owner theorem. -/
/- Lemma 12.5.20: in a commutative diagram with exact rows in an abelian category, if the
second and fourth vertical morphisms are isomorphisms, the fifth vertical morphism is a
monomorphism, and the first vertical morphism is an epimorphism, then the middle vertical
morphism is an isomorphism. -/
recall Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono

end CategoryTheory
