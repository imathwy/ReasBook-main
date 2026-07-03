import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_24_1 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/- Domain-style sampling for Definition 4.24.1:
- `Adjunction` is the owner object for the notion that `u : C ⥤ D` is left adjoint to
  `v : D ⥤ C`.
- `Adjunction.CoreHomEquiv` is the canonical bridge packaging the textbook's natural family of
  hom-set bijections.
- `Adjunction.mkOfHomEquiv` is the canonical constructor from the textbook hom-set bijections.
- `Adjunction.homEquiv` is the derived hom-set equivalence attached to an adjunction.
- `Adjunction.homEquiv_naturality_left` and `Adjunction.homEquiv_naturality_right` are the
  canonical naturality laws for that derived equivalence.

Primitive-vs-derived split:
- primitive data: the adjunction owner `u ⊣ v`.
- derived API: the source-style family of hom-set bijections and its naturality in both
  variables. -/

/- Source/core/bridge triage for Definition 4.24.1:
- `source-facing`: the textbook statement that `u` is left adjoint to `v`, equivalently that
  there is a natural family of bijections
  `(u.obj X ⟶ Y) ≃ (X ⟶ v.obj Y)`.
- `core/canonical`: `Adjunction u v`, written `u ⊣ v`.
- `bridge/view`: `Adjunction.CoreHomEquiv`, `Adjunction.mkOfHomEquiv`, `Adjunction.homEquiv`, and
  the two naturality lemmas expressing the textbook hom-set formulation from the owner
  abstraction.
-/

/- Definition 4.24.1: for functors `u : C ⥤ D` and `v : D ⥤ C`, saying that `u` is a left
adjoint of `v`, or equivalently that `v` is a right adjoint to `u`, is the canonical owner notion
`Adjunction u v`, written `u ⊣ v`. The source-style hom-set bijections are derived from this owner
via `Adjunction.homEquiv`, and conversely a natural family of such bijections gives an adjunction
via `Adjunction.mkOfHomEquiv`. -/
recall Adjunction

/- The textbook's natural family of hom-set bijections is packaged by the canonical bridge object
`Adjunction.CoreHomEquiv`; it is auxiliary data for constructing the owner object `u ⊣ v`, not a
second owner notion. -/
recall Adjunction.CoreHomEquiv

/- The textbook's natural family of hom-set bijections canonically determines an adjunction via
`Adjunction.mkOfHomEquiv`. -/
recall Adjunction.mkOfHomEquiv

/- The textbook's bijections of morphism sets are the canonical equivalences attached to an
adjunction. -/
recall Adjunction.homEquiv

/- The hom-set bijections of an adjunction are natural in the source object. -/
recall Adjunction.homEquiv_naturality_left

/- The hom-set bijections of an adjunction are natural in the target object. -/
recall Adjunction.homEquiv_naturality_right

end CategoryTheory

/-! ### Lemma_4_24_2 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/- Domain-style sampling for Lemma 4.24.2:
- primary domain: representability criteria for adjoints, owned by
  `Mathlib/CategoryTheory/Adjunction/PartialAdjoint`.
- sampled owner API:
  `Functor.rightAdjointObjIsDefined`,
  `Functor.rightAdjointObjIsDefined_iff`,
  `Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top`,
  `Functor.isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top`.
- best owner abstraction: `u.rightAdjointObjIsDefined : ObjectProperty D`.
- source-facing layer: the hypothesis that each presheaf `X ↦ (u.obj X ⟶ Y)` is representable.
- core/canonical layer: the owner criterion that `u.rightAdjointObjIsDefined = ⊤`.
- bridge/view: the theorem below turns the source hypothesis into that owner criterion and then
  reuses the owner theorem for left adjoints.
- primitive data: only the functor `u`.
- derived API: objectwise representability is the pointwise description of
  `u.rightAdjointObjIsDefined`, and `u.IsLeftAdjoint` is then derived from the owner theorem.
-/

/-- Helper for Lemma 4.24.2: objectwise representability of the presheaves
`X ↦ (u.obj X ⟶ Y)` is exactly the condition that the right-adjoint object property of `u`
is the top object property. -/
lemma rightAdjointObjIsDefined_eq_top_of_objwise_hom_isRepresentable (u : C ⥤ D)
    (h : ∀ Y : D, (u.op ⋙ yoneda.obj Y).IsRepresentable) : u.rightAdjointObjIsDefined = ⊤ := by
  -- Convert equality of object properties into the corresponding pointwise representability claim.
  ext Y
  -- The owner API identifies the fiber over `Y` with representability of the presheaf
  -- `u.op ⋙ yoneda.obj Y`, so the hypothesis closes the pointwise goal immediately.
  simpa [u.rightAdjointObjIsDefined_iff Y] using h Y

/-- Lemma 4.24.2: if for every object `Y : D` the presheaf
`X ↦ (u.obj X ⟶ Y)` is representable, then `u` is a left adjoint, so it has a right adjoint. -/
theorem isLeftAdjoint_of_objwise_hom_isRepresentable (u : C ⥤ D)
    (h : ∀ Y : D, (u.op ⋙ yoneda.obj Y).IsRepresentable) : u.IsLeftAdjoint := by
  -- The partial-adjoint criterion reduces existence of a right adjoint to the owner property
  -- that every target object admits a representing object for the hom-presheaf along `u`.
  rw [u.isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top]
  -- Apply the objectwise representability hypothesis through the bridge lemma above.
  exact rightAdjointObjIsDefined_eq_top_of_objwise_hom_isRepresentable u h

end Functor
end CategoryTheory

/-! ### Lemma_4_24_3 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

/- Domain-style sampling for Lemma 4.24.3:
- primary domain: adjunction criteria for full, faithful, and fully faithful functors;
- sampled owner API:
  `Functor.FullyFaithful`,
  `Functor.FullyFaithful.ofCompFaithful`,
  `Adjunction.fullyFaithfulLOfIsIsoUnit`,
  `Adjunction.fullyFaithfulROfIsIsoCounit`,
  `Adjunction.homEquiv`;
- source-facing layer: the Stacks criterion that if the composite endofunctor `u ⋙ v` or `v ⋙ u`
  is fully faithful, then the corresponding adjoint `u` or `v` is fully faithful;
- core/canonical owner: `CategoryTheory.Adjunction`;
- bridge/view: this file upgrades fully faithfulness of the composite endofunctor to the owner
  criteria on the adjunction hom-set equivalence. The nearest upstream composition theorem is
  `Functor.FullyFaithful.ofCompFaithful`, but it needs an independent faithfulness hypothesis on
  the second functor, so it does not subsume the adjunction-specific Stacks lemma here.

Primitive data are the adjunction `adj : u ⊣ v` and the bundled `FullyFaithful` structure on the
composite endofunctor. The final `FullyFaithful` structures on `u` and `v` are derived API and
should be built directly from the adjunction owner `homEquiv`, rather than by introducing
intermediate local `Full`, `Faithful`, or `IsIso` wrappers.
-/

/- Source/core/bridge triage for Lemma 4.24.3:
- `source-facing`: the Stacks lemma is stated for a chosen adjunction `u ⊣ v` and a chosen
  fully faithful composite endofunctor `u ⋙ v` or `v ⋙ u`;
- `core/canonical`: the owner abstractions `Adjunction.homEquiv`,
  `Adjunction.fullyFaithfulLOfIsIsoUnit`, and `Adjunction.fullyFaithfulROfIsIsoCounit`;
- `bridge/view`: the two declarations below are thin source-facing bridges from full faithfulness
  of the composite endofunctor to full faithfulness of the corresponding adjoint. This file
  cannot be reduced to a pure `recall`: the nearest generic composition theorem
  `Functor.FullyFaithful.ofCompFaithful` still needs an independent faithfulness hypothesis on the
  second functor, so the adjunction-specific argument remains necessary here.
-/

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {u : C ⥤ D} {v : D ⥤ C}

attribute [local simp] Adjunction.homEquiv_unit Adjunction.homEquiv_counit

/-- Lemma 4.24.3 (1): source-facing bridge from full faithfulness of `u ⋙ v` to full faithfulness
of the left adjoint `u`. -/
noncomputable def fullyFaithfulLOfCompFullyFaithful
    (adj : u ⊣ v) (hcomp : (u ⋙ v).FullyFaithful) : u.FullyFaithful where
  preimage f := hcomp.preimage (v.map f)
  map_preimage {X Y} f := by
    apply (adj.homEquiv X (u.obj Y)).injective
    simpa [Functor.comp_map] using
      congrArg (fun k ↦ adj.unit.app X ≫ k) (hcomp.map_preimage (v.map f))
  preimage_map f := by
    simpa [Functor.comp_map] using hcomp.preimage_map f

/-- Full faithfulness of `u ⋙ v` makes the map on `Hom`-sets induced by the left adjoint `u`
bijective. -/
theorem fullyFaithfulLOfCompFullyFaithful_map_bijective
    (adj : u ⊣ v) (hcomp : (u ⋙ v).FullyFaithful) (X Y : C) :
    Function.Bijective (u.map : (X ⟶ Y) → (u.obj X ⟶ u.obj Y)) := by
  simpa using (fullyFaithfulLOfCompFullyFaithful adj hcomp).map_bijective X Y

/-- Lemma 4.24.3 (2): source-facing bridge from full faithfulness of `v ⋙ u` to full faithfulness
of the right adjoint `v`. -/
noncomputable def fullyFaithfulROfCompFullyFaithful
    (adj : u ⊣ v) (hcomp : (v ⋙ u).FullyFaithful) : v.FullyFaithful where
  preimage f := hcomp.preimage (u.map f)
  map_preimage {X Y} f := by
    apply (adj.homEquiv (v.obj X) Y).symm.injective
    simpa [Functor.comp_map, Category.assoc] using
      congrArg (fun k ↦ k ≫ adj.counit.app Y) (hcomp.map_preimage (u.map f))
  preimage_map f := by
    simpa [Functor.comp_map] using hcomp.preimage_map f

/-- Full faithfulness of `v ⋙ u` makes the map on `Hom`-sets induced by the right adjoint `v`
bijective. -/
theorem fullyFaithfulROfCompFullyFaithful_map_bijective
    (adj : u ⊣ v) (hcomp : (v ⋙ u).FullyFaithful) (X Y : D) :
    Function.Bijective (v.map : (X ⟶ Y) → (v.obj X ⟶ v.obj Y)) := by
  simpa using (fullyFaithfulROfCompFullyFaithful adj hcomp).map_bijective X Y

end

end CategoryTheory.Adjunction

/-! ### Lemma_4_24_4 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {u : C ⥤ D} {v : D ⥤ C}

/- Domain-style sampling for Lemma 4.24.4:
- primary domain: adjunction criteria for fully faithful functors;
- sampled owner API:
  `Adjunction.unit_isIso_of_L_fully_faithful`,
  `Adjunction.fullyFaithfulLOfIsIsoUnit`,
  `Adjunction.counit_isIso_of_R_fully_faithful`,
  `Adjunction.fullyFaithfulROfIsIsoCounit`;
- sampled bridge API:
  `Adjunction.isIso_unit_of_iso`,
  `Adjunction.fullyFaithfulLOfCompIsoId`,
  `Adjunction.isIso_counit_of_iso`,
  `Adjunction.fullyFaithfulROfCompIsoId`;
- source-facing layer: the Stacks criterion that, for an adjunction `u ⊣ v`, full faithfulness of
  `u` is equivalent to invertibility of the unit, and full faithfulness of `v` is equivalent to
  invertibility of the counit;
- core/canonical owner: `CategoryTheory.Adjunction`;
- bridge/view: passage between the natural-transformation isomorphism criteria and the explicit
  functor isomorphisms `𝟭 C ≅ u ⋙ v` and `v ⋙ u ≅ 𝟭 D`.

Primitive data are just the adjunction `u ⊣ v`. The full-faithfulness criteria, the `IsIso`
structures on the unit and counit, and the functor-isomorphism reformulations are all derived API
already owned upstream by `CategoryTheory.Adjunction`, so this file should remain a pure canonical
recall rather than introducing local wrappers.
-/

/- Lemma 4.24.4: for an adjunction `u ⊣ v`, the fully faithful criterion is already owned by the
canonical mathlib adjunction API. The source-facing equivalence

* `u` fully faithful `↔` the unit `𝟭 C ⟶ u ⋙ v` is an isomorphism, and
* `v` fully faithful `↔` the counit `v ⋙ u ⟶ 𝟭 D` is an isomorphism

is exactly the pair of owner constructions below. -/
recall Adjunction.unit_isIso_of_L_fully_faithful
recall Adjunction.fullyFaithfulLOfIsIsoUnit
recall Adjunction.counit_isIso_of_R_fully_faithful
recall Adjunction.fullyFaithfulROfIsIsoCounit

/- The source restatement using explicit isomorphisms `𝟭 C ≅ u ⋙ v` and `v ⋙ u ≅ 𝟭 D` is the
canonical bridge between those owner theorems and abstract functor isomorphisms. -/
recall Adjunction.isIso_unit_of_iso
recall Adjunction.fullyFaithfulLOfCompIsoId
recall Adjunction.isIso_counit_of_iso
recall Adjunction.fullyFaithfulROfCompIsoId

end CategoryTheory

/-! ### Lemma_4_24_5 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {u : C ⥤ D} {v : D ⥤ C}

/- Domain-style sampling for Lemma 4.24.5:
- primary domain: adjunctions and preservation of (co)limits;
- sampled owner API:
  `Adjunction.leftAdjoint_preservesColimits`,
  `Adjunction.rightAdjoint_preservesLimits`,
  `Adjunction.functorialityAdjunction`,
  `Adjunction.functorialityAdjunction'`;
- source-facing layer: the Stacks statement that an adjoint pair `u ⊣ v` has `u` preserving
  colimits and `v` preserving limits;
- core/canonical owner: `CategoryTheory.Adjunction`;
- bridge/view: the cocone and cone functoriality adjunctions used upstream to prove the owner
  theorems.

Primitive-vs-derived split:
- primitive data: an adjunction `u ⊣ v`;
- derived API: the preservation-of-colimits and preservation-of-limits instances attached to that
  adjunction. No local wrapper or reformulation is needed here.
-/

/- Source/core/bridge triage for Lemma 4.24.5:
- `source-facing`: the textbook assertion that left adjoints preserve colimits and right adjoints
  preserve limits;
- `core/canonical`: the owner theorems
  `Adjunction.leftAdjoint_preservesColimits` and
  `Adjunction.rightAdjoint_preservesLimits`;
- `bridge/view`: the explicit finite-exactness consequences are handled downstream in
  `Lemma_4_24_6`, so this file should remain a pure recall of the owner API.
-/

/- Lemma 4.24.5: for an adjunction `u ⊣ v`, the left adjoint `u` preserves colimits and the right
adjoint `v` preserves limits. These are exactly the canonical mathlib theorems
`Adjunction.leftAdjoint_preservesColimits` and `Adjunction.rightAdjoint_preservesLimits`. -/
recall Adjunction.leftAdjoint_preservesColimits
recall Adjunction.rightAdjoint_preservesLimits

end CategoryTheory

/-! ### Lemma_4_24_6 (from Chap04) -/
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {u : C ⥤ D} {v : D ⥤ C}

/- Domain-style sampling for Lemma 4.24.6:
- primary domain: adjunctions and exactness properties of functors;
- inspected owner declarations:
  `Adjunction.leftAdjoint_preservesColimits`,
  `Adjunction.rightAdjoint_preservesLimits`,
  `PreservesColimits.preservesFiniteColimits`,
  `PreservesLimits.preservesFiniteLimits`;
- best owner abstraction: the adjunction owner theorems, with the chapter's exactness predicates
  as the canonical finite-(co)limit view;
- primitive data: a chosen adjunction `u ⊣ v`;
- derived API: the right-exactness of `u` and the left-exactness of `v`, obtained from the owner
  theorems through the canonical finite-(co)limit upgrade lemmas and the exactness predicates. -/

/- Source/core/bridge triage for Lemma 4.24.6:
- source-facing: the Stacks lemma is stated for a chosen adjunction `u ⊣ v`.
- core/canonical: mathlib owns the preservation statements through
  `Adjunction.leftAdjoint_preservesColimits` and `Adjunction.rightAdjoint_preservesLimits`.
- bridge/view: the explicit-adjunction statements below are thin companions from a chosen
  adjunction to the chapter's finite-exactness predicates. -/

/-- Lemma 4.24.6 (1): if `u` is left adjoint to `v`, then `u` is right exact. This is the
source-facing bridge from a chosen adjunction to the owner theorem
`Adjunction.leftAdjoint_preservesColimits`. -/
theorem left_adjoint_is_rightExact_of_adjunction (adj : u ⊣ v) :
    rightExactFunctor C D u := by
  -- First upgrade the chosen adjunction to preservation of all colimits.
  letI : PreservesColimits u := adj.leftAdjoint_preservesColimits
  -- Then restrict from all colimits to finite colimits, which is right exactness.
  exact PreservesColimits.preservesFiniteColimits u

/-- Lemma 4.24.6 (2): if `u` is left adjoint to `v`, then `v` is left exact. This is the
source-facing bridge from a chosen adjunction to the owner theorem
`Adjunction.rightAdjoint_preservesLimits`. -/
theorem right_adjoint_is_leftExact_of_adjunction (adj : u ⊣ v) :
    leftExactFunctor D C v := by
  -- First upgrade the chosen adjunction to preservation of all limits.
  letI : PreservesLimits v := adj.rightAdjoint_preservesLimits
  -- Then restrict from all limits to finite limits, which is left exactness.
  exact PreservesLimits.preservesFiniteLimits v

end CategoryTheory

/-! ### Lemma_4_24_7 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {u : C ⥤ D} {v : D ⥤ C}

/- Domain-style sampling for Lemma 4.24.7:
- primary domain: adjunctions in category theory;
- sampled owner API:
  `Adjunction`,
  `Adjunction.left_triangle`,
  `Adjunction.right_triangle`,
  `Adjunction.left_triangle_components`;
- best owner abstraction: the owner object `CategoryTheory.Adjunction`, whose canonical public
  triangle-identity API is given by the natural-transformation theorems
  `Adjunction.left_triangle` and `Adjunction.right_triangle`. The componentwise formulas are
  lower-level owner data used to derive these theorems.

Primitive-vs-derived split:
- primitive data: for `adj : u ⊣ v`, the unit, counit, and the objectwise triangle identities
  `Adjunction.left_triangle_components` / `Adjunction.right_triangle_components` are fields of the
  owner structure itself;
- derived API: the natural-transformation identities `Adjunction.left_triangle` and
  `Adjunction.right_triangle`, along with `Adjunction.homEquiv` and its consequences. This lemma
  is a pure recall item and should reuse the canonical owner theorems directly, without a parallel
  local wrapper or a replacement by unpacked component formulas.
-/

/- Source/core/bridge triage for Lemma 4.24.7:
- source-facing: the two triangle identities for a chosen adjunction `u ⊣ v`;
- core/canonical: the natural-transformation theorems `Adjunction.left_triangle` and
  `Adjunction.right_triangle`;
- bridge/view: none needed here, since the source statement is already exactly the owner API.
-/

/- Lemma 4.24.7: the two triangle identities of a chosen adjunction are exactly the canonical
owner theorems `Adjunction.left_triangle` and `Adjunction.right_triangle`. -/
recall Adjunction.left_triangle
recall Adjunction.right_triangle

end CategoryTheory

/-! ### Lemma_4_24_8 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {U₁ U₂ : C ⥤ D} {V₁ V₂ : D ⥤ C}
variable (adj₁ : U₁ ⊣ V₁) (adj₂ : U₂ ⊣ V₂)

/- Domain-style sampling for Lemma 4.24.8:
- primary domain: adjunction mates/conjugation in category theory;
- sampled owner API:
  `Adjunction`,
  `conjugateEquiv`,
  `conjugateEquiv_counit`,
  `unit_conjugateEquiv`;
- best owner abstraction: the adjunction-mates API in
  `Mathlib.CategoryTheory.Adjunction.Mates`.

Primitive-vs-derived split:
- primitive data: the two adjunctions `adj₁ : U₁ ⊣ V₁` and `adj₂ : U₂ ⊣ V₂`;
- derived API: the conjugation equivalence between natural transformations of left and right
  adjoints, and its unit/counit compatibility lemmas. This item is purely derived API, so it
  should be a direct recall of the owner theorem rather than a parallel local wrapper.
-/

/- Source/core/bridge triage for Lemma 4.24.8:
- source-facing: the textbook counit square comparing a natural transformation of left adjoints
  with its conjugate transformation of right adjoints;
- core/canonical: `conjugateEquiv_counit`;
- bridge/view: `conjugateEquiv` supplies the corresponding mate on right adjoints, but no extra
  local bridge declaration is needed here.
-/

/- Lemma 4.24.8: if `β : U₂ ⟶ U₁` is a natural transformation between left adjoints and
`conjugateEquiv adj₁ adj₂ β : V₁ ⟶ V₂` is the corresponding transformation of right adjoints,
then for each `d : D` the counit square commutes. This is exactly the canonical mathlib theorem
`conjugateEquiv_counit`. -/
recall conjugateEquiv_counit

end CategoryTheory

/-! ### Lemma_4_24_9 (from Chap04) -/
universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {u : B ⥤ A} {v : A ⥤ B}
variable {u' : C ⥤ B} {v' : B ⥤ C}

/- Domain-style sampling for Lemma 4.24.9:
- primary domain: adjunctions in category theory;
- sampled owner API:
  `Adjunction`,
  `Adjunction.comp`,
  `Adjunction.comp_unit_app`,
  `Adjunction.comp_counit_app`;
- best owner abstraction: `CategoryTheory.Adjunction`.

Primitive-vs-derived split:
- primitive data: the chosen adjunctions `u ⊣ v` and `u' ⊣ v'`;
- derived API: their composite adjunction `u' ⋙ u ⊣ v ⋙ v'` and the corresponding unit/counit
  formulas. Since this item is just the composite adjunction itself, it should be a direct recall
  of the owner construction rather than a parallel local wrapper.
-/

/- Source/core/bridge triage for Lemma 4.24.9:
- source-facing: the textbook composes two chosen adjunctions `u ⊣ v` and `u' ⊣ v'`.
- core/canonical: mathlib already owns this construction as `Adjunction.comp`.
- bridge/view: the explicit counit formula is the separate companion recall `4_24_9_1`. -/

/- Lemma 4.24.9 (1): if `v : A ⥤ B` and `v' : B ⥤ C` have left adjoints `u` and `u'`
respectively, then the composite `v ⋙ v'` has left adjoint `u' ⋙ u`. This is exactly the canonical
mathlib construction `Adjunction.comp`. The counit formula in part (2) is the separate item
`4.24.9.1`. -/
recall Adjunction.comp

end CategoryTheory
