import Mathlib
import stacks_project.Chap12.Definition_12_19_3
import stacks_project.Chap13.Lemma_13_13_8
import stacks_project.Chap13.Lemma_13_15_5
import stacks_project.Chap13.Lemma_13_26_5

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
