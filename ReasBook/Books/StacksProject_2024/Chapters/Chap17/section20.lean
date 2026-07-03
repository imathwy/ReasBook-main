import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_17_20_1 (from Chap17) -/
open AlgebraicGeometry

universe u

namespace RingedSpace.Hom

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/- Domain-style sampling for Definition 17.20.1:
- primary domain: flatness of morphisms of ringed spaces, expressed stalkwise;
- sampled owner declarations:
  `AlgebraicGeometry.Flat`,
  `AlgebraicGeometry.Flat.stalkMap`,
  `AlgebraicGeometry.Flat.iff_flat_stalkMap`;
- owner abstraction: the project-level owner for ringed-space morphisms is the global predicate
  `RingedSpace.Hom.IsFlat`, while the scheme specialization is already owned upstream by
  `AlgebraicGeometry.Flat`;
- primitive data: the family of flat stalk maps;
- derived API: the pointwise source-facing predicate `FlatAt` and the scheme bridge
  `Scheme.Hom.isFlat_iff_flat`.

Source/core/bridge triage:
- `source-facing`: `FlatAt`;
- `core/canonical`: `IsFlat`;
- `bridge/view`: `Scheme.Hom.isFlat_iff_flat`.

The public owner should therefore be `IsFlat`, with `FlatAt` retained only as the pointwise view
named in the source, and the scheme specialization connected directly to the mathlib owner
`AlgebraicGeometry.Flat`. -/

/-- Definition 17.20.1: a morphism of ringed spaces is flat at `x` when the induced stalk map
`\mathcal O_{Y, f(x)} \to \mathcal O_{X, x}` is a flat ring homomorphism. -/
abbrev FlatAt (x : X) : Prop :=
  (f.hom.stalkMap x).hom.Flat

/-- A morphism of ringed spaces is flat when it is flat at every point of the source. -/
@[mk_iff]
class IsFlat : Prop where
  flatAt : ∀ x : X, FlatAt f x

end RingedSpace.Hom

namespace Scheme.Hom

open RingedSpace.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Under the scheme specialization, the ringed-space flatness owner agrees with mathlib's
canonical scheme-theoretic flatness predicate. -/
theorem isFlat_iff_flat :
    IsFlat f.toLRSHom.toShHom ↔ Flat f := by
  rw [Flat.iff_flat_stalkMap]
  constructor
  · intro hf x
    simpa [RingedSpace.Hom.FlatAt] using hf.flatAt x
  · intro hf
    exact ⟨fun x ↦ by simpa [RingedSpace.Hom.FlatAt] using hf x⟩

instance instIsFlat [Flat f] : IsFlat f.toLRSHom.toShHom :=
  (isFlat_iff_flat f).2 inferInstance

instance instFlat [IsFlat f.toLRSHom.toShHom] : Flat f :=
  (isFlat_iff_flat f).1 inferInstance

end Scheme.Hom

/-! ### Lemma_17_20_2 (from Chap17) -/
open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

variable {X Y : RingedSpace.{u}}

namespace AlgebraicGeometry.RingedSpace.Hom

/- Domain-style sampling for Lemma 17.20.2:
- primary domain: exactness of inverse-image on module sheaves under a flat morphism of ringed
  spaces;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.Hom.pullback`,
  `RingedSpace.Modules`,
  `SheafOfModules.pullback`,
  `exactFunctor`,
  `RingedSite.Hom.IsFlat.pullback_exact`;
- best owner abstraction: this file is a `bridge/view` item whose primitive hypothesis is still
  the source-facing flatness class `RingedSpace.Hom.IsFlat`, but whose exactness conclusion is
  about the canonical Chapter 6 pullback owner `AlgebraicGeometry.RingedSpace.Hom.pullback`;
  the theorem should therefore be exposed in the `AlgebraicGeometry.RingedSpace.Hom` family,
  while its proof route reuses the site-level exactness owner
  `RingedSite.Hom.IsFlat.pullback_exact`;
- primitive data: a morphism `f : X ⟶ Y` together with `[RingedSpace.Hom.IsFlat f]`;
- derived API: exactness of the canonical pullback functor on the owner categories `Y.Modules` and
  `X.Modules`.

Source/core/bridge triage:
- `source-facing`: flat morphisms of ringed spaces, expressed stalkwise;
- `core/canonical`: `RingedSpace.Modules`, `SheafOfModules.pullback`, and `exactFunctor`;
- `bridge/view`: `AlgebraicGeometry.RingedSpace.Hom.IsFlat.pullback_exact`, which upgrades the
  source-facing flatness owner to exactness of the canonical pullback functor.

Primitive-vs-derived decision:
- the module categories should be taken from the existing owner `RingedSpace.Modules`, not rebuilt
  locally as `SheafOfModules (RingedSpace.ringCatSheaf _)`;
- the theorem itself remains necessary as the ringed-space bridge from stalkwise flatness to the
  exactness owner, so the refinement here is to reuse the canonical category owner rather than
  keep a parallel local category spelling.
-/

/-- Lemma 17.20.2: if `f : (X, \mathcal O_X) \to (Y, \mathcal O_Y)` is a flat morphism of ringed
spaces, then the pullback functor `f^* : \mathit{Mod}(\mathcal O_Y) \to \mathit{Mod}(\mathcal O_X)`
is exact. -/
-- Proof sketch: write `f^*` as the composite of the exact inverse-image functor on abelian sheaves
-- with extension of scalars along `f^{-1} \mathcal O_Y ⟶ \mathcal O_X`; stalkwise flatness makes
-- this tensor-extension functor left exact, and pullback is already right exact by adjointness.
theorem IsFlat.pullback_exact
    (f : X ⟶ Y) [RingedSpace.Hom.IsFlat f] :
    exactFunctor Y.Modules X.Modules (f^*) := sorry

end AlgebraicGeometry.RingedSpace.Hom

/-! ### Definition_17_20_3 (from Chap17) -/
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules

variable {X Y : RingedSpace.{u}}

/-
Domain-style sampling for Definition 17.20.3:
- primary domain: relative flatness of an `\mathcal O_X`-module, expressed by restricting scalars
  along the inverse-image structure-sheaf map `f^{-1}\mathcal O_Y \to \mathcal O_X`;
- sampled owner declarations:
  `RingedSpace.Hom.inverseImageStructureSheafHomComm`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.isFlat_stalk`,
  `Module.Flat`;
- owner abstraction: the canonical global owner is
  `SheafOfModules.RingedSite.IsFlat` for the restricted `f^{-1}\mathcal O_Y`-module obtained from
  `ℱ`; the stalkwise condition is companion bridge API;
- primitive data: the sheaf `ℱ`, the morphism `f`, and the restricted `f^{-1}\mathcal O_Y`-module
  structure on `ℱ`;
- derived API: the source-facing predicates `flat_over` and `flat_over_at`, with the latter
  recording the stalkwise view.

Source/core/bridge triage:
- `source-facing`: `flat_over`;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlat`;
- `bridge/view`: the restricted module below and the stalkwise predicate `flat_over_at`.

This file should therefore organize relative flatness around the canonical exact-tensor owner on the
restricted `f^{-1}\mathcal O_Y`-module, and keep the stalkwise formulation only as a companion
bridge.
-/

private abbrev relativeModule
    (ℱ : X.Modules) (f : X ⟶ Y) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat)).map
      (RingedSpace.Hom.inverseImageStructureSheafHomComm f))).obj ℱ

private abbrev relativeStalk
    (ℱ : X.Modules) (f : X ⟶ Y) (x : X) :
    ModuleCat (Y.presheaf.stalk (f.hom.base x)) :=
  (ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj (stalkModuleCat ℱ x)

/-- Definition 17.20.3: an `\mathcal O_X`-module `\mathcal F` is flat over `Y` when, after
restricting scalars along `f^{-1}\mathcal O_Y \to \mathcal O_X`, it is a flat
`f^{-1}\mathcal O_Y`-module in the canonical exact-tensor sense. -/
abbrev flat_over
    (ℱ : X.Modules) (f : X ⟶ Y) : Prop :=
  SheafOfModules.RingedSite.IsFlat
    ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj Y.sheaf)
    (relativeModule ℱ f)

/-- Flatness of `\mathcal F` over `Y` at a point means that the stalk `\mathcal F_x` is flat over
the target stalk `\mathcal O_{Y, f(x)}`. -/
abbrev flat_over_at
    (ℱ : X.Modules) (f : X ⟶ Y) (x : X) : Prop :=
  Module.Flat (Y.presheaf.stalk (f.hom.base x)) ↑(relativeStalk ℱ f x)

/-- Companion bridge: a sheaf is flat over `Y` exactly when its stalks are flat over the target
stalk rings. -/
theorem flat_over_iff_pointwise (ℱ : X.Modules) (f : X ⟶ Y) :
    flat_over ℱ f ↔ ∀ x : X, flat_over_at ℱ f x :=
  sorry

end SheafOfModules

/-! ### Lemma_17_20_4 (from Chap17) -/
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.20.4:
- primary domain: exactness of pullback followed by tensoring with a sheaf that is flat over the
  target ringed space in the canonical relative-flatness sense;
- sampled owner declarations:
  `SheafOfModules.flat_over`,
  `SheafOfModules.RingedSite.IsFlat`,
  `f^*`,
  `sheafModuleTensorRightFunctor`,
  `exactFunctor`;
- owner abstraction: the source-facing flatness hypothesis should reuse
  `SheafOfModules.flat_over ℱ f` as the canonical relative-flatness owner on the restricted
  `f^{-1}\mathcal O_Y`-module, while the functor part should reuse the canonical pullback owner
  `f^*` and the existing tensor owner `sheafModuleTensorRightFunctor`;
- primitive data: a morphism `f : X ⟶ Y` and a sheaf `ℱ : (RingedSpace.Modules X)`;
- derived API: the exactness theorem for the canonical composite functor
  `f^* ⋙ sheafModuleTensorRightFunctor ℱ`.

Source/core/bridge triage:
- `source-facing`: exactness of `𝒢 ↦ f^*𝒢 ⊗ ℱ` under the hypothesis that `ℱ` is flat over `Y`;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlat`, `f^*`,
  `sheafModuleTensorRightFunctor`, and `exactFunctor`;
- `bridge/view`: `SheafOfModules.flat_over` and the composite pullback-then-tensor functor used
  directly in the theorem.
-/

variable {X Y : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

local notation "ModX" => X.Modules
local notation "ModY" => Y.Modules

-- Proof sketch: rewrite the textbook functor as
-- `𝒢 ↦ f^{-1}𝒢 ⊗_{f^{-1}\mathcal O_Y} ℱ`. The inverse-image functor on abelian sheaves is exact,
-- and the relative-flatness instance on `ℱ` is exactly the flatness needed for tensoring with
-- `ℱ` over `f^{-1}\mathcal O_Y` to preserve short exact sequences; combining these gives exactness of the
-- composite functor.
/-- Lemma 17.20.4: if `f : (X, \mathcal O_X) \to (Y, \mathcal O_Y)` is a morphism of ringed
spaces and `\mathcal F` is an `\mathcal O_X`-module flat over `Y`, then the functor
`\mathcal G \mapsto f^* \mathcal G \otimes_{\mathcal O_X} \mathcal F` from
`Mod(\mathcal O_Y)` to `Mod(\mathcal O_X)` is exact. -/
theorem ringedSpaceModulePullbackTensor_exact_of_flatOverTarget
    (f : X ⟶ Y) (ℱ : ModX) [SheafOfModules.flat_over ℱ f] :
    exactFunctor ModY ModX (f^* ⋙ sheafModuleTensorRightFunctor ℱ) := sorry

end AlgebraicGeometry.RingedSpace
