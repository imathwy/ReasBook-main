import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_17_11_1 (from Chap17) -/
/- Domain-style sampling for Definition 17.11.1:
- primary domain: sheaves of modules on ringed spaces and the finite-presentation predicate on
  `\mathcal O_X`-modules;
- sampled canonical owner declarations:
  `SheafOfModules.QuasicoherentData`,
  `SheafOfModules.QuasicoherentData.IsFinitePresentation`,
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.isFinitePresentation`;
- best owner abstraction: the mathlib owner class `SheafOfModules.IsFinitePresentation`;
- primitive data: local presentation data on a covering family, packaged upstream by
  `SheafOfModules.QuasicoherentData` and its finite-presentation predicate;
- derived API: the object-property form `SheafOfModules.isFinitePresentation` and the canonical
  instances from finite presentation to quasi-coherence and finite type;
- source/core/bridge triage:
  `core/canonical`: `SheafOfModules.IsFinitePresentation`,
  `bridge/view`: `SheafOfModules.isFinitePresentation`.

This item is a canonical recall item: the source-facing notion is already owned upstream, so this
file should reuse that owner directly rather than introducing a ringed-space-local wrapper around
the local finite-presentation data.
-/

/- Definition 17.11.1: for a sheaf of `\mathcal O_X`-modules on a ringed space, being of finite
presentation is the canonical predicate `SheafOfModules.IsFinitePresentation`, defined upstream by
local finite presentations on a covering family of opens and matching the neighbourhood
formulation in the text. -/
recall SheafOfModules.IsFinitePresentation

/-! ### Lemma_17_11_2 (from Chap17) -/
open AlgebraicGeometry

universe u

/- 
Domain-style sampling for Lemma 17.11.2:
- primary domain: finite-presentation and quasi-coherence predicates for sheaves of modules on a
  ringed space;
- sampled owner declarations:
  `RingedSpace.Modules`,
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.IsQuasicoherent`,
  the canonical mathlib instance
  `(M : SheafOfModules R) [M.IsFinitePresentation] : M.IsQuasicoherent`;
- best owner abstraction: the upstream owner class `SheafOfModules.IsFinitePresentation`, with
  quasi-coherence as derived API supplied by the canonical instance;
- primitive data: a sheaf of modules on `X` together with its finite-presentation instance;
- derived API: the resulting quasi-coherence instance;

Source/core/bridge triage:
- `source-facing`: the ringed-space specialization of Stacks Project Lemma 17.11.2;
- `core/canonical`: the upstream instance `[M.IsFinitePresentation] → M.IsQuasicoherent`;
- `bridge/view`: the chapter owner alias `RingedSpace.Modules X`.

This item is a canonical-use item: the mathematical content is already owned upstream, so the
file should reuse that owner directly instead of introducing a parallel local theorem wrapper.
-/

variable {X : RingedSpace.{u}}
variable (𝒢 : RingedSpace.Modules X) [𝒢.IsFinitePresentation]

/- Lemma 17.11.2: any `\mathcal O_X`-module of finite presentation on a ringed space
`(X, \mathcal O_X)` is quasi-coherent. This is the canonical instance from
`SheafOfModules.IsFinitePresentation` to `SheafOfModules.IsQuasicoherent`. -/
#check (inferInstance : 𝒢.IsQuasicoherent)

/-! ### Lemma_17_11_3 (from Chap17) -/
/-
Domain-style sampling for Lemma 17.11.3:
- primary domain: finite type and finite presentation for sheaves of modules, specialized in the
  source to `\mathcal O_X`-modules on a ringed space;
- inspected owner declarations:
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.isFiniteType_kernel_of_epi_of_finitePresentation`,
  `SheafOfModules.isFinitePresentation_cokernel`,
  `RingedSpace.ringCatSheaf`;
- best owner abstraction: the generic owner theorem
  `SheafOfModules.isFinitePresentation_cokernel`;
- primitive data: a morphism of sheaves of modules over an ambient sheaf of rings together with
  finite-type and finite-presentation instances on source and target;
- derived API: the finite-presentation instance on the cokernel.

Source/core/bridge triage:
- `source-facing`: the ringed-space formulation of Stacks Project Lemma 17.11.3;
- `core/canonical`: `SheafOfModules.isFinitePresentation_cokernel`;
- `bridge/view`: the ringed-space specialization obtained by instantiating the ambient sheaf of
  rings to `(RingedSpace.ringCatSheaf X)`.
-/

/- Lemma 17.11.3: for a morphism `φ : 𝒢 ⟶ ℱ` of `\mathcal O_X`-modules on a ringed space, if
`𝒢` is of finite type and `ℱ` is finitely presented, then `cokernel φ` is finitely presented.
This is exactly the canonical owner theorem
`SheafOfModules.isFinitePresentation_cokernel`, whose ambient sheaf of rings specializes to
`(RingedSpace.ringCatSheaf X)`.
-/
recall SheafOfModules.isFinitePresentation_cokernel

/-! ### Lemma_17_11_4 (from Chap17) -/
open CategoryTheory Limits

noncomputable section

universe u v u'

/- Domain-style sampling for Lemma 17.11.4:
- primary domain: finitely presented sheaves of modules over a sheaf of rings on a site, and
  finite-type control of kernels of epimorphisms;
- inspected owner declarations:
  `SheafOfModules.IsFiniteType`,
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.free`,
  `CategoryTheory.ObjectProperty.prop_of_epi`;
- best owner abstraction:
  the ambient owner category `SheafOfModules R`, with finite type / finite presentation as the
  canonical owner predicates and `kernel` as derived abelian-category data, so the generic
  epimorphism theorem is the owner result and the finite-free case is a source-facing
  specialization;
- primitive data:
  the ambient sheaf of rings `R`, a finitely presented target sheaf, and either an epimorphism
  from a finite free sheaf or an epimorphism from a finite-type sheaf;
- derived API:
  the source-facing finite-type conclusions for the corresponding kernels.

Source/core/bridge triage:
- `source-facing`: the finite-free kernel statement in part `(1)` of Stacks Project Lemma
  `17.11.4`;
- `core/canonical`: the generic owner theorem for kernels of epimorphisms from finite-type
  sheaves into finitely presented sheaves, inside `SheafOfModules R`;
- `bridge/view`: ringed spaces are only the specialization `R = (RingedSpace.ringCatSheaf X)`.

As in Lemma 17.9.3, the public statements are best kept at the generic `SheafOfModules` owner
layer rather than as ringed-space-specific wrappers. Accordingly, the generic finite-type source
theorem is kept as the owner result below, and the finite-free source statement is retained only
as the source-facing specialization. -/

namespace SheafOfModules

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{u}}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
variable [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ X : C, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

-- Proof sketch: locally choose a surjection from a finite free sheaf onto `𝒢`; the composite with
-- `θ` is still epi, so the finite-free case gives finite type for its kernel. The canonical exact
-- sequence comparing `kernel (ψη)` and `kernel θ` then shows that `kernel θ` is an image of a
-- finite type sheaf, hence is itself of finite type.
omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- Lemma 17.11.4 (2): if `θ : 𝒢 \to ℱ` is surjective, `𝒢` is of finite type, and `ℱ` is of finite
presentation, then `kernel θ` is of finite type. -/
theorem isFiniteType_kernel_of_epi_of_finitePresentation
    {𝒢 ℱ : SheafOfModules R} (θ : 𝒢 ⟶ ℱ)
    [Epi θ] [𝒢.IsFiniteType] [ℱ.IsFinitePresentation] :
    (kernel θ).IsFiniteType := sorry

-- Proof sketch: this is the finite-free specialization of the owner theorem above, stated with
-- the source's rank-`r` free sheaf surface.
/-- Lemma 17.11.4 (1): if `ℱ` is a finitely presented `\mathcal O`-module and
`ψ : \mathcal O^{\oplus r} \to ℱ` is surjective, then `kernel ψ` is of finite type. -/
theorem isFiniteType_kernel_of_epi_free_of_finitePresentation
    {ℱ : SheafOfModules R} [ℱ.IsFinitePresentation] (r : ℕ)
    (ψ : free (ULift.{u} (Fin r)) ⟶ ℱ) [Epi ψ] :
    (kernel ψ).IsFiniteType := sorry

end SheafOfModules

/-! ### Lemma_17_11_5 (from Chap17) -/
noncomputable section

universe u

open AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 17.11.5:
- primary domain: finitely presented sheaves of modules on ringed spaces and their behavior under
  the canonical pullback functor;
- inspected owner declarations:
  `(RingedSpace.Modules AlgebraicGeometry.RingedSpace)`,
  `SheafOfModules.IsFinitePresentation`,
  `RingedSpace.Hom.pullback`,
  `SheafOfModules.RingedSite.pullback_isFinitePresentation`;
- best owner abstraction: the Chapter 18 owner theorem
  `SheafOfModules.RingedSite.pullback_isFinitePresentation`, specialized to the ringed site of
  opens of a ringed space and exposed at the pullback owner
  `AlgebraicGeometry.RingedSpace.Hom.pullback_isFinitePresentation`, with the owner predicate
  `SheafOfModules.IsFinitePresentation` on `Y.Modules`;
- primitive data: a ringed-space morphism `f : X ⟶ Y` and a module sheaf
  `𝒢 : Y.Modules`;
- derived API: the source-facing ringed-space specialization asserting that pullback carries
  finitely presented modules to finitely presented modules.

Source/core/bridge triage:
- `source-facing`: the Stacks assertion that pullback along a morphism of ringed spaces preserves
  finite presentation;
- `core/canonical`: `SheafOfModules.RingedSite.pullback_isFinitePresentation`,
  `SheafOfModules.IsFinitePresentation`, and the pullback owner `f^*`;
- `bridge/view`: the specialization along `TopologicalSpace.Opens.map f.hom.base` and
  `RingedSpace.Hom.toRingCatSheafHom f`, exposed at the pullback-owner namespace rather than as a
  separate global compatibility theorem. -/

variable {X Y : RingedSpace.{u}}

namespace RingedSpace.Hom

private theorem pullback_isFinitePresentation_aux
    (f : X ⟶ Y) (𝒢 : Y.Modules) [𝒢.IsFinitePresentation] :
    ((f^*).obj 𝒢).IsFinitePresentation := by
  simpa using
    (SheafOfModules.RingedSite.pullback_isFinitePresentation.{u, u, u, u, u, u, u, u, u, u, u, u, u}
      (TopologicalSpace.Opens.map f.hom.base) (toRingCatSheafHom f) 𝒢)

-- Proof sketch: this is the ringed-space specialization of the Chapter 18 owner theorem on
-- pullback preserving finite presentation for sheaves of modules on ringed sites, applied to the
-- site of opens of `Y` and `X` and the canonical structure-sheaf map `toRingCatSheafHom f`.
/-- Lemma 17.11.5: for a morphism of ringed spaces
`f : (X, \mathcal{O}_X) \to (Y, \mathcal{O}_Y)`, the pullback of an
`\mathcal{O}_Y`-module of finite presentation is an `\mathcal{O}_X`-module of finite
presentation. -/
theorem pullback_isFinitePresentation
    (f : X ⟶ Y) (𝒢 : Y.Modules) [𝒢.IsFinitePresentation] :
    ((f^*).obj 𝒢).IsFinitePresentation :=
  pullback_isFinitePresentation_aux f 𝒢

end RingedSpace.Hom

end AlgebraicGeometry

/-! ### Lemma_17_11_6 (from Chap17) -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 17.11.6:
- primary domain: filtered-colimit presentations of `\mathcal O_X`-modules associated to modules
  over the global-sections ring;
- inspected owner declarations:
  `CategoryTheory.ObjectProperty.ind`,
  `SheafOfModules.isFinitePresentation`,
  `associatedModuleSheaf`,
  `globalSectionsModuleFunctor_preservesColimits`;
- best owner abstraction: the filtered-colimit conclusion should be stated directly in the
  canonical owner form `ind (SheafOfModules.isFinitePresentation (RingedSpace.ringCatSheaf X))`
  on `X.Modules`, rather than by a parallel local predicate that unpacks the same witness data;
- primitive data: the ringed space `X`, the global-sections module `M`, and the source-facing
  isomorphism witness `ℱ ≅ 𝓕_ M`;
- derived API: the `ind` packaging of the filtered-colimit presentation by finitely presented
  module sheaves.

Source/core/bridge triage:
- `source-facing`: the Stacks statement that a module sheaf associated to a global-sections module
  is a filtered colimit of finitely presented `\mathcal O_X`-modules;
- `core/canonical`: `CategoryTheory.ObjectProperty.ind` and
  `SheafOfModules.isFinitePresentation`;
- `bridge/view`: the associated-module-sheaf owner `𝓕_ M`, together with the ambient isomorphism
  witness identifying `ℱ` with that owner.
-/

-- Proof sketch: choose an associated-module-sheaf presentation of `ℱ` from Definition `17.10.6`,
-- then recover a functor realizing that presentation from Lemma `17.10.5`. Apply Lemma
-- `10.11.3` to write `M` as a filtered colimit of finitely presented `R`-modules, then use that
-- the associated-sheaf functor preserves colimits and carries finitely presented modules to
-- finitely presented `\mathcal O_X`-modules.
/-- Lemma 17.11.6: if `ℱ` is an `\mathcal O_X`-module associated to an
`R = \Gamma(X, \mathcal O_X)`-module `M`, then `ℱ` is a directed colimit of finitely presented
`\mathcal O_X`-modules. -/
theorem associatedGlobalSectionsModuleSheaf_isFilteredColimitOfFinitePresentation
    {X : RingedSpace.{u}} (M : ModuleCat (X.presheaf.obj (op ⊤))) (ℱ : X.Modules)
    (hℱ : Nonempty (ℱ ≅ 𝓕_ M)) :
    ind (SheafOfModules.isFinitePresentation (RingedSpace.ringCatSheaf X)) ℱ := sorry

end AlgebraicGeometry

/-! ### Lemma_17_11_7 (from Chap17) -/
open CategoryTheory TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 17.11.7:
- primary domain: finitely presented sheaves of modules on ringed spaces and local freeness from a
  stalkwise finite free model;
- inspected owner declarations:
  `AlgebraicGeometry.RingedSpace.Modules`,
  `AlgebraicGeometry.RingedSpace.stalkModuleCat`,
  `ModuleCat.free`,
  `SheafOfModules.IsFiniteLocallyFreeOfRank`;
- best owner abstraction: the ambient owner category `RingedSpace.Modules X`, with the stalk
  bundled by `RingedSpace.stalkModuleCat` and the canonical finite free stalk model supplied by
  `ModuleCat.free (X.presheaf.stalk x)`;
- primitive data: a finitely presented module sheaf `ℱ`, a point `x`, a rank `r`, and a stalk
  isomorphism from `RingedSpace.stalkModuleCat ℱ x` to the free `X.presheaf.stalk x`-module on
  `ULift (Fin r)`;
- derived API: after shrinking around `x`, the restricted sheaf `ℱ.over U` becomes isomorphic to
  the free sheaf `SheafOfModules.free (ULift (Fin r))`.

Source/core/bridge triage:
- `source-facing`: the local trivialization statement around a point with free stalk;
- `core/canonical`: `RingedSpace.Modules`, `RingedSpace.stalkModuleCat`, and `ModuleCat.free`;
- `bridge/view`: the restriction `ℱ.over U` and the local free sheaf `SheafOfModules.free`. -/

-- Proof sketch: choose lifts on some neighbourhood of a basis of the free stalk module, obtaining
-- a morphism from the finite free sheaf to `ℱ|_U`. Lemma `17.9.4` makes this morphism surjective
-- after shrinking, Lemma `17.11.4` gives finite type for its kernel, and Lemma `17.9.5` kills the
-- kernel after another shrinking because its stalk at `x` is zero.
/-- Lemma 17.11.7: if a finitely presented `\mathcal O_X`-module has stalk at `x` isomorphic to
the free rank-`r` `\mathcal O_{X, x}`-module, then on some open neighbourhood `U` of `x` its
restriction `ℱ|_U` is isomorphic to the free sheaf `\mathcal O_U^{\oplus r}`. -/
theorem exists_open_neighborhood_free_over_of_stalk_free
    {X : RingedSpace.{u}} (ℱ : RingedSpace.Modules X)
    [ℱ.IsFinitePresentation] (x : X) (r : ℕ)
    (hℱx : Nonempty
      (RingedSpace.stalkModuleCat ℱ x ≅
        (ModuleCat.free (X.presheaf.stalk x)).obj (ULift.{u} (Fin r)))) :
    ∃ (U : Opens X) (_ : x ∈ U),
      Nonempty (ℱ.over U ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r))) := sorry

end AlgebraicGeometry
