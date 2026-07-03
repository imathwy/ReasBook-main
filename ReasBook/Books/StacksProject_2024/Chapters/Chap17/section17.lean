import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_17_17_1 (from Chap17) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}

/- Domain-style sampling for Definition 17.17.1:
- primary domain: flat sheaves of modules on a ringed space, defined by exactness of tensoring on
  the right;
- inspected owner declarations:
  `X.Modules`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.RingedSite.unit_isFlat`,
  `Module.Flat`;
- best owner abstraction: the canonical owner is the site-level predicate
  `SheafOfModules.RingedSite.IsFlat`, specialized to the opens-site of `X` and hence to the
  ambient category `X.Modules`;
- primitive data: a sheaf `ℱ : X.Modules`;
- derived API: the stalkwise bridge theorems `isFlat_stalk` and `isFlat_of_stalkwise`, together
  with the unit instance.

Source/core/bridge triage:
- `source-facing`: global flatness of an `\mathcal O_X`-module sheaf, defined by exactness of
  tensoring with it;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlat`;
- `bridge/view`: the later stalkwise characterization, exposed here only through companion bridge
  theorems rather than as primitive public data.

This file should therefore recall the site-level owner specialized to `X` and treat stalkwise
flatness as derived bridge API. -/

/- Definition 17.17.1: for a ringed space `(X, \mathcal O_X)`, flatness of an
`\mathcal O_X`-module is exactly the opens-site specialization of the canonical site-level owner
`SheafOfModules.RingedSite.IsFlat`. -/
recall SheafOfModules.RingedSite.IsFlat

/-- Companion bridge: a flat sheaf of modules has flat stalks. -/
theorem isFlat_stalk {ℱ : X.Modules}
    [SheafOfModules.RingedSite.IsFlat X.sheaf ℱ] (x : X) :
    Module.Flat (X.presheaf.stalk x) ↑(stalkModuleCat ℱ x) := sorry

/-- Companion bridge: stalkwise flatness implies flatness of the sheaf. -/
theorem isFlat_of_stalkwise (ℱ : X.Modules)
    (hℱ : ∀ x : X, Module.Flat (X.presheaf.stalk x) ↑(stalkModuleCat ℱ x)) :
    SheafOfModules.RingedSite.IsFlat X.sheaf ℱ := sorry

/-- The structure sheaf, viewed as a module over itself, is flat. -/
theorem unit_isFlat :
    SheafOfModules.RingedSite.IsFlat X.sheaf
      (SheafOfModules.unit (ringCatSheaf X)) := by
  simpa using SheafOfModules.RingedSite.unit_isFlat X.sheaf

/-- The structure sheaf carries its canonical flatness instance. -/
instance :
    SheafOfModules.RingedSite.IsFlat X.sheaf
      (SheafOfModules.unit (ringCatSheaf X)) :=
  unit_isFlat

end SheafOfModules

/-! ### Lemma_17_17_2 (from Chap17) -/
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}

/- Domain-style sampling for Lemma 17.17.2:
- primary domain: flat sheaves of modules on a ringed space, expressed through stalkwise
  flatness;
- sampled owner declarations:
  `RingedSpace.Modules`,
  `AlgebraicGeometry.RingedSpace.stalkModuleCat`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.flat_at`;
- best owner abstraction: `SheafOfModules.RingedSite.IsFlat X.sheaf` is the canonical owner on
  the opens-site of `X`, while `flat_at` is the source-facing pointwise view;
- primitive data: a module sheaf `ℱ : X.Modules`, with flatness owned globally by exactness of
  tensoring on the right;
- derived API: the stalkwise characterization theorem below.

Source/core/bridge triage:
- `source-facing`: the stalkwise reformulation of flatness;
- `core/canonical`: `X.Modules`, `RingedSpace.stalkModuleCat`, and
  `SheafOfModules.RingedSite.IsFlat X.sheaf`;
- `bridge/view`: `flat_at`.

This file should therefore state only the source-facing equivalence and reuse the canonical owner
from `Definition_17_17_1`, rather than redeclaring a parallel `IsFlat` API.
-/

-- Proof sketch: one direction is exactly the stalk projection theorem for the canonical owner.
-- Conversely, the stalkwise hypotheses are precisely the data required to build the owner class.
/-- Lemma 17.17.2: an `\mathcal O_X`-module `ℱ` on a ringed space is flat if and only if, for
every point `x : X`, the stalk `ℱ_x` is a flat module over the local ring `\mathcal O_{X, x}`. -/
theorem isFlat_iff_stalkwise (ℱ : X.Modules) :
    SheafOfModules.RingedSite.IsFlat X.sheaf ℱ ↔ ∀ x : X, ℱ.flat_at x :=
  ⟨fun _ x ↦ isFlat_stalk x, isFlat_of_stalkwise ℱ⟩

end SheafOfModules

/-! ### Definition_17_17_3 (from Chap17) -/
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}

/- Domain-style sampling for Definition 17.17.3:
- primary domain: stalkwise flatness of sheaves of modules on a ringed space;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.stalkModuleCat`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.isFlat_stalk`,
  `Module.Flat`;
- owner abstractions:
  the canonical stalk owner is `AlgebraicGeometry.RingedSpace.stalkModuleCat`, and the chapter-level
  flatness owner is `SheafOfModules.RingedSite.IsFlat X.sheaf`;
- primitive data: a sheaf `ℱ : X.Modules` and a point `x : X`;
- derived API: the source-facing pointwise predicate `flat_at` and its specialization
  `unit_flat_at`.

Source/core/bridge triage:
- `source-facing`: flatness of an `\mathcal O_X`-module at a single point;
- `core/canonical`: `RingedSpace.stalkModuleCat`,
  `SheafOfModules.RingedSite.IsFlat X.sheaf`, and `Module.Flat`;
- `bridge/view`: the pointwise predicate `flat_at`, obtained by evaluating the canonical stalk
  flatness owner at one point.

This file should therefore keep only the source-facing pointwise view and reuse the existing
canonical stalk and flatness owners, rather than redeclaring a parallel public stalk-module
bridge. -/

/-- Definition 17.17.3: an `\mathcal O_X`-module `ℱ` is flat at `x` if its stalk `ℱ_x` is a flat
module over the local ring `\mathcal O_{X, x}`. -/
abbrev flat_at (ℱ : X.Modules) (x : X) : Prop :=
  Module.Flat (X.presheaf.stalk x) ↑(stalkModuleCat ℱ x)

/-- The structure sheaf is flat at every point. -/
theorem unit_flat_at (x : X) :
    flat_at (SheafOfModules.unit (ringCatSheaf X)) x :=
  isFlat_stalk x

end SheafOfModules

/-! ### Lemma_17_17_4 (from Chap17) -/
open AlgebraicGeometry.RingedSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 17.17.4:
- primary domain: pullback of module sheaves on a morphism of ringed spaces and preservation of
  flatness;
- sampled owner declarations:
  `RingedSpace.Hom.pullback`,
  `RingedSpace.Hom.pullbackStalkIso`,
  `SheafOfModules.isFlat_of_stalkwise`,
  `SheafOfModules.isFlat_stalk`,
  `Module.Flat.baseChange`;
- best owner abstraction: the canonical pullback functor `f^*` acts on `Y.Modules`, while
  flatness is owned by the canonical site-level predicate
  `SheafOfModules.RingedSite.IsFlat`;
- primitive data: a morphism `f : X ⟶ Y` and a module sheaf `𝒢 : Y.Modules`;
- derived API: the flatness-preservation theorem and instance below.

Source/core/bridge triage:
- `source-facing`: pullback preserves flatness;
- `core/canonical`: `Y.Modules`, `f^*`, and `SheafOfModules.RingedSite.IsFlat`;
- `bridge/view`: the stalkwise flatness argument from Lemma `6.26.4`.

This file should therefore reuse the canonical Chapter 6 pullback owner `f^*` together with the
chapter flatness owner from `Definition_17_17_1`, rather than restating pullback through an
explicit bridge decomposition or depending on a separate characterization wrapper.
-/

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

-- Proof sketch: by Lemma `17.17.2`, flatness is stalkwise. For `x : X`, identify the stalk of
-- `f^* 𝒢` with the base change of the stalk of `𝒢` along `\mathcal O_{Y,f(x)} → \mathcal O_{X,x}`
-- using Lemma `6.26.4`, then apply the module-theoretic base-change stability of flatness.
/-- Lemma 17.17.4: for a morphism of ringed spaces `f : (X, \mathcal O_X) ⟶ (Y, \mathcal O_Y)`,
if `𝒢` is a flat `\mathcal O_Y`-module, then its pullback `f^* 𝒢` is a flat
`\mathcal O_X`-module. -/
theorem pullback_isFlat (𝒢 : Y.Modules)
    [SheafOfModules.RingedSite.IsFlat Y.sheaf 𝒢] :
    SheafOfModules.RingedSite.IsFlat X.sheaf ((f^*).obj 𝒢) := by
  refine SheafOfModules.isFlat_of_stalkwise ((f^*).obj 𝒢) ?_
  intro x
  let _ : Module.Flat (X.presheaf.stalk x)
      ↑((ModuleCat.extendScalars (f.hom.stalkMap x).hom).obj
        (stalkModuleCat 𝒢 (f.hom.base x))) := by
    let _ : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    let _ : Module.Flat (Y.presheaf.stalk (f.hom.base x))
        ↑(stalkModuleCat 𝒢 (f.hom.base x)) :=
      by
        simpa using
          (SheafOfModules.isFlat_stalk (f.hom.base x) :
            Module.Flat (Y.presheaf.stalk (f.hom.base x))
              ↑(stalkModuleCat 𝒢 (f.hom.base x)))
    change Module.Flat (X.presheaf.stalk x)
      (TensorProduct (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x)
        ↑(stalkModuleCat 𝒢 (f.hom.base x)))
    infer_instance
  exact Module.Flat.of_linearEquiv ((RingedSpace.Hom.pullbackStalkIso f 𝒢 x).symm.toLinearEquiv)

/-- Pullback along a morphism of ringed spaces preserves flat module sheaves. -/
instance (𝒢 : Y.Modules) [SheafOfModules.RingedSite.IsFlat Y.sheaf 𝒢] :
    SheafOfModules.RingedSite.IsFlat X.sheaf ((f^*).obj 𝒢) :=
  pullback_isFlat f 𝒢

end AlgebraicGeometry

/-! ### Lemma_17_17_5 (from Chap17) -/
/- Domain-style sampling for Lemma 17.17.5:
- primary domain: closure of flat module sheaves under filtered colimits and coproducts;
- sampled owner declarations:
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.RingedSite.isFlat_colimit_of_isFiltered`,
  `SheafOfModules.RingedSite.isFlat_coproduct`,
  `SheafOfModules.isFlat_stalk`,
  `RingedSpace.Modules`;
- best owner abstraction: flatness is owned by
  `SheafOfModules.RingedSite.IsFlat X.sheaf` on `X.Modules`, and the closure results are already
  owned upstream by the Chapter 18 site-level theorems specialized to `X.sheaf`;
- primitive data: a diagram of sheaves of modules on `X` whose objects are all flat;
- derived API: the filtered-colimit and coproduct closure theorems below.

Source/core/bridge triage:
- `source-facing`: flatness is preserved by filtered colimits and direct sums;
- `core/canonical`: `X.Modules`, `SheafOfModules.RingedSite.IsFlat X.sheaf`, and the Chapter 18
  owner theorems `SheafOfModules.RingedSite.isFlat_colimit_of_isFiltered` and
  `SheafOfModules.RingedSite.isFlat_coproduct`;
- `bridge/view`: the ringed-space specialization of those site-level closure results.

This file should therefore be recall-only: the ringed-space case is obtained by specializing the
canonical Chapter 18 owner theorems, so no parallel Chapter 17 theorem names should remain.
-/

/- Lemma 17.17.5 (1): a filtered colimit of flat `\mathcal O_X`-modules is flat. This is exactly
the ringed-space specialization of the canonical owner theorem
`SheafOfModules.RingedSite.isFlat_colimit_of_isFiltered`. -/
recall SheafOfModules.RingedSite.isFlat_colimit_of_isFiltered

/- Lemma 17.17.5 (2): a direct sum of flat `\mathcal O_X`-modules is flat. This is exactly the
ringed-space specialization of the canonical owner theorem
`SheafOfModules.RingedSite.isFlat_coproduct`. -/
recall SheafOfModules.RingedSite.isFlat_coproduct

/-! ### Lemma_17_17_6 (from Chap17) -/
open AlgebraicGeometry
open TopCat
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleSheaf

/- Domain-style sampling for Lemma 17.17.6:
- primary domain: extension by zero for sheaves of modules on a ringed space, specialized to the
  structure sheaf on an open subspace, together with flatness of the resulting `\mathcal O_X`-module;
- sampled owner declarations:
  `moduleSheafExtensionByZeroFromOpen`,
  `openSubsetModuleSheafExtensionByZero`,
  `openSubsetModuleSheafExtensionByZero_eq_moduleSheafExtensionByZeroFromOpen`,
  `SheafOfModules.RingedSite.IsFlat`;
- best owner abstraction: the chapter-level owner for module-valued extension by zero is the
  canonical left adjoint `moduleSheafExtensionByZeroFromOpen`; the explicit
  `openSubsetModuleSheafExtensionByZero` construction is a source-facing bridge already identified
  with that owner in Chapter 6;
- primitive data: an open subset `U ⊆ X`;
- derived API: the specific lower-shriek structure module `structureSheafLowerShriek U =
  j_{U!}\mathcal O_U` and its flatness statement.

Source/core/bridge triage:
- `source-facing`: the module sheaf `j_{U!}\mathcal O_U` and the claim that it is flat;
- `core/canonical`: `moduleSheafExtensionByZeroFromOpen` and
  `SheafOfModules.RingedSite.IsFlat`;
- `bridge/view`: the explicit Chapter-6 `openSubsetModuleSheafExtensionByZero` model.

This file should therefore keep the source-facing owner `j_{U!}\mathcal O_U` as the short public
surface `structureSheafLowerShriek U`, defined using the canonical extension-by-zero owner rather
than by repeating the explicit Chapter-6 bridge term.
-/

/-- The lower-shriek structure sheaf `j_{U!}\mathcal O_U` attached to an open subspace
`U ⊆ X`, viewed as an `\mathcal O_X`-module sheaf. -/
noncomputable abbrev structureSheafLowerShriek
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    SheafOfModules (ringCatSheaf X) :=
  (moduleSheafExtensionByZeroFromOpen U (ringCatSheaf X)).obj
    (SheafOfModules.unit
      ((Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
        (ringCatSheaf X)))

-- Proof sketch: by Lemma 17.17.2 it is enough to check flatness stalkwise. If `x ∈ U`, the
-- stalk of `j_{U!}\mathcal O_U` identifies with `\mathcal O_{U,x} \cong \mathcal O_{X,x}` by the
-- extension-by-zero stalk description on `U`, hence is flat over `\mathcal O_{X,x}`. If
-- `x ∉ U`, the stalk is zero by the extension-by-zero stalk description outside `U`, and the zero
-- module is flat.
/-- Lemma 17.17.6: for an open subset `U ⊆ X`, the extension by zero `j_{U!}\mathcal O_U` is a
flat sheaf of `\mathcal O_X`-modules. -/
theorem structureSheafLowerShriek_isFlat
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    SheafOfModules.RingedSite.IsFlat X.sheaf (structureSheafLowerShriek U) := sorry

end AlgebraicGeometry.RingedSpace.ModuleSheaf

/-! ### Lemma_17_17_7 (from Chap17) -/
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open TopCat
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleSheaf

variable {X : RingedSpace.{u}}

/-
Domain-style sampling for Lemma 17.17.7:
- primary domain: epimorphic generators of `X.Modules` by the lower-shriek structure modules
  `j_{U!}\mathcal O_U`, together with the resulting `ObjectProperty` package used in the Chapter 13
  truncation-resolution formalism;
- sampled owner declarations:
  `RingedSpace.Modules`,
  `structureSheafLowerShriek`,
  `CategoryTheory.ObjectProperty.HasEpiCover`,
  `CategoryTheory.exists_upperTruncationResolutionTower`;
- best owner abstraction: the ambient owner is the canonical module category `X.Modules`; the
  source-facing summands are the already-defined objects `structureSheafLowerShriek U`, and the
  closure/cover statements should be expressed directly as an `ObjectProperty` on `X.Modules`
  rather than via a parallel wrapper category;
- primitive data: an index type `I`, a family of opens `U : I → Opens X.carrier`, and an
  epimorphism from the coproduct of the corresponding modules `j_{U_i!}\mathcal O_{U_i}`;
- derived API: the object property of being such a coproduct, its `ContainsZero` /
  `IsClosedUnderFiniteCoproducts` / `HasEpiCover` instances, and the flat quotient corollary.

Source/core/bridge triage:
- `source-facing`: the coproduct and flat epimorphic presentations of an `\mathcal O_X`-module;
- `core/canonical`: `X.Modules`, `structureSheafLowerShriek`, and the generic
  `CategoryTheory.ObjectProperty` closure classes;
- `bridge/view`: none beyond the source-facing `structureSheafLowerShriek` owner from
  `Lemma_17_17_6`.
-/

local notation "ModX" => X.Modules

-- Proof sketch: for every open `U ⊆ X` and section `s ∈ ℱ(U)`, the adjunction between
-- restriction to `U` and extension by zero gives a morphism `j_{U!}\mathcal O_U ⟶ ℱ` sending `1`
-- to `s`. Taking the coproduct over all pairs `(U, s)` yields a morphism whose stalk maps are
-- surjective, hence the morphism is epimorphic.
/-- Lemma 17.17.7 (1): any sheaf of `\mathcal O_X`-modules is the quotient of a direct sum of
lower-shriek structure sheaves `j_{U_i!}\mathcal O_{U_i}`. -/
theorem exists_epi_from_coproduct_openSubsetStructureSheafLowerShriek
    (ℱ : ModX) :
    ∃ (I : Type u) (U : I → Opens X.carrier)
      (φ : (∐ fun i : I ↦ structureSheafLowerShriek (U i)) ⟶ ℱ), Epi φ := sorry

/-- The object property on `\mathrm{Mod}(\mathcal O_X)` saying that a module is a direct sum,
equivalently a categorical coproduct, of lower-shriek structure sheaves `j_{U!}\mathcal O_U`. -/
def isCoproductOfOpenSubsetStructureSheafLowerShrieks
    (X : RingedSpace.{u}) : CategoryTheory.ObjectProperty X.Modules :=
  fun ℱ ↦
    ∃ (I : Type u) (U : I → Opens X.carrier),
      Nonempty (ℱ ≅ ∐ fun i : I ↦ structureSheafLowerShriek (U i))

/-- The zero `\mathcal O_X`-module is the empty coproduct of lower-shriek structure sheaves. -/
instance isCoproductOfOpenSubsetStructureSheafLowerShrieks_containsZero :
    (isCoproductOfOpenSubsetStructureSheafLowerShrieks X).ContainsZero := sorry

/-- Finite coproducts of coproducts of lower-shriek structure sheaves are again coproducts of
lower-shriek structure sheaves. -/
instance isCoproductOfOpenSubsetStructureSheafLowerShrieks_isClosedUnderFiniteCoproducts :
    (isCoproductOfOpenSubsetStructureSheafLowerShrieks X).IsClosedUnderFiniteCoproducts := sorry

/-- Every `\mathcal O_X`-module admits an epimorphism from a coproduct of lower-shriek structure
sheaves `j_{U!}\mathcal O_U`. -/
instance isCoproductOfOpenSubsetStructureSheafLowerShrieks_hasEpiCover :
    CategoryTheory.ObjectProperty.HasEpiCover
      (isCoproductOfOpenSubsetStructureSheafLowerShrieks X) := sorry

-- Proof sketch: apply the epimorphic coproduct presentation from `(1)` and use that each summand
-- `j_{U_i!}\mathcal O_{U_i}` is flat by `structureSheafLowerShriek_isFlat`. Then apply
-- the earlier direct-sum flatness result to conclude that the source coproduct is flat.
/-- Lemma 17.17.7 (2): any sheaf of `\mathcal O_X`-modules is the quotient of a flat
`\mathcal O_X`-module. -/
theorem exists_epi_from_flat
    (ℱ : ModX) :
    ∃ (𝒢 : ModX)
      (h𝒢 : SheafOfModules.RingedSite.IsFlat X.sheaf 𝒢) (φ : 𝒢 ⟶ ℱ), Epi φ := sorry

end AlgebraicGeometry.RingedSpace.ModuleSheaf

/-! ### Lemma_17_17_8 (from Chap17) -/
open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

/- Domain-style sampling for Lemma 17.17.8:
- primary domain: tensor products of sheaves of modules on a ringed space and preservation of
  short exact sequences under tensoring on the right;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `sheafModuleTensorRightFunctor`,
  `SheafOfModules.IsFlat`,
  `SheafOfModules.RingedSite.shortExact_tensor_right_of_flat_quotient`;
- best owner abstraction: the canonical owner is the site-level theorem
  `SheafOfModules.RingedSite.shortExact_tensor_right_of_flat_quotient`, whose ringed-space case is
  obtained by specializing to the opens-site of `X`;
- primitive data: a short exact sequence in `RingedSpace.Modules X`, a right tensor factor, and a
  flat quotient term;
- derived API: the ringed-space wording of the same tensor-preservation result.

Source/core/bridge triage:
- `source-facing`: the Stacks-project ringed-space formulation of preservation of short exactness
  under tensoring by a fixed sheaf;
- `core/canonical`: `SheafOfModules.RingedSite.shortExact_tensor_right_of_flat_quotient`;
- `bridge/view`: the specialization from a ringed site `(Opens X, Opens.grothendieckTopology X,
  ringCatSheaf X)` to the ambient category `RingedSpace.Modules X`.

Primitive-vs-derived check:
- the deleted local theorem `CategoryTheory.ShortComplex.ShortExact.moduleTensorRight_of_isFlat`
  was only a ringed-space wrapper around the Chapter 18 owner theorem, differing by namespace and
  by passing flatness explicitly instead of through the owner instance;
- this file should therefore be a recall/use file rather than maintain a parallel theorem name.
-/

/- Lemma 17.17.8: for a ringed space `(X, 𝒪_X)`, tensoring a short exact sequence of
`𝒪_X`-modules on the right by any `𝒪_X`-module preserves short exactness when the quotient term is
flat. This is exactly the ringed-space specialization of the canonical site-level owner theorem
`SheafOfModules.RingedSite.shortExact_tensor_right_of_flat_quotient`. -/
recall SheafOfModules.RingedSite.shortExact_tensor_right_of_flat_quotient

/-! ### Lemma_17_17_9 (from Chap17) -/
open CategoryTheory
open CategoryTheory.ShortComplex.ShortExact
open AlgebraicGeometry

universe u

/- Domain-style sampling for Lemma 17.17.9:
- primary domain: flatness propagation in short exact sequences of sheaves of modules on a ringed
  space;
- inspected owner declarations:
  `SheafOfModules.RingedSite.IsFlat`,
  `CategoryTheory.ShortComplex.ShortExact.flat_X₂`,
  `CategoryTheory.ShortComplex.ShortExact.flat_X₁`,
  `SheafOfModules.isFlat_of_stalkwise`,
  `SheafOfModules.isFlat_stalk`,
  `SheafOfModules.flat_at`;
  `S : ShortComplex (RingedSpace.Modules X)`, with the Chapter 10 owner theorems applied to the
  canonical stalk short complex `RingedSpace.stalkShortComplex S x`;
- primitive data: the short complex `S` and its short exactness proof `hS`;
- derived API: the stalkwise companion lemmas `flat_at_X₂` and `flat_at_X₁`.

Source/core/bridge triage:
- `source-facing`: Lemma 17.17.9 asserts global flatness propagation for a short exact sequence of
  `\mathcal O_X`-modules;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlat X.sheaf` together with the module-theoretic
  owners `CategoryTheory.ShortComplex.ShortExact.flat_X₂` and `flat_X₁`;
- `bridge/view`: stalkwise flatness, used only to pass between the global owner and the stalk short
  complexes. -/

namespace SheafOfModules

variable {X : RingedSpace.{u}}
variable {S : ShortComplex (RingedSpace.Modules X)}

-- Proof sketch: use the canonical global owner `SheafOfModules.RingedSite.IsFlat X.sheaf` and
-- prove stalkwise flatness of `S.X₂`. For each `x : X`, the stalk short complex is short exact;
-- apply the module-theoretic owner theorem `CategoryTheory.ShortComplex.ShortExact.flat_X₂` to the
-- stalk modules of `S.X₁`, `S.X₂`, and `S.X₃`.
/-- Lemma 17.17.9 (1): in a short exact sequence of `\mathcal O_X`-modules on a ringed space, if
the left and right terms are flat, then the middle term is flat. -/
theorem isFlat_X₂ (hS : S.ShortExact)
    (h₁ : SheafOfModules.RingedSite.IsFlat X.sheaf S.X₁)
    (h₃ : SheafOfModules.RingedSite.IsFlat X.sheaf S.X₃) :
    SheafOfModules.RingedSite.IsFlat X.sheaf S.X₂ := by
  letI := h₁
  letI := h₃
  refine isFlat_of_stalkwise S.X₂ ?_
  intro x
  letI : Module.Flat (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat S.X₁ x) := isFlat_stalk x
  letI : Module.Flat (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat S.X₃ x) := isFlat_stalk x
  simpa [RingedSpace.stalkShortComplex] using flat_X₂ (hS.stalkShortComplex x)

-- Proof sketch: apply `isFlat_X₂` stalkwise to the short exact stalk complex induced by `hS`, then
-- project back to the pointwise source-facing predicate `flat_at`.
/-- Companion bridge: under the hypotheses of `isFlat_X₂`, the middle term is flat at every
point. -/
theorem flat_at_X₂ (hS : S.ShortExact)
    (h₁ : SheafOfModules.RingedSite.IsFlat X.sheaf S.X₁)
    (h₃ : SheafOfModules.RingedSite.IsFlat X.sheaf S.X₃) :
    ∀ x : X, S.X₂.flat_at x := by
  letI := isFlat_X₂ hS h₁ h₃
  intro x
  simpa [flat_at] using isFlat_stalk x

-- Proof sketch: again use the global flatness owner and check stalkwise flatness. For each point,
-- pass to the induced short exact sequence on stalks and apply the module-theoretic owner theorem
-- `CategoryTheory.ShortComplex.ShortExact.flat_X₁`.
/-- Lemma 17.17.9 (2): in a short exact sequence of `\mathcal O_X`-modules on a ringed space, if
the middle and right terms are flat, then the left term is flat. -/
theorem isFlat_X₁ (hS : S.ShortExact)
    (h₂ : SheafOfModules.RingedSite.IsFlat X.sheaf S.X₂)
    (h₃ : SheafOfModules.RingedSite.IsFlat X.sheaf S.X₃) :
    SheafOfModules.RingedSite.IsFlat X.sheaf S.X₁ := by
  letI := h₂
  letI := h₃
  refine isFlat_of_stalkwise S.X₁ ?_
  intro x
  letI : Module.Flat (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat S.X₂ x) := isFlat_stalk x
  letI : Module.Flat (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat S.X₃ x) := isFlat_stalk x
  simpa [RingedSpace.stalkShortComplex] using flat_X₁ (hS.stalkShortComplex x)

-- Proof sketch: derive the stalkwise statement from the global owner theorem `isFlat_X₁` via the
-- canonical projection `isFlat_stalk`.
/-- Companion bridge: under the hypotheses of `isFlat_X₁`, the left term is flat at every point. -/
theorem flat_at_X₁ (hS : S.ShortExact)
    (h₂ : SheafOfModules.RingedSite.IsFlat X.sheaf S.X₂)
    (h₃ : SheafOfModules.RingedSite.IsFlat X.sheaf S.X₃) :
    ∀ x : X, S.X₁.flat_at x := by
  letI := isFlat_X₁ hS h₂ h₃
  intro x
  simpa [flat_at] using isFlat_stalk x

end SheafOfModules

/-! ### Lemma_17_17_10 (from Chap17) -/
open CategoryTheory
open AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.17.10:
- primary domain: exact right-augmented sequences of `\mathcal O_X`-modules on a ringed space and
  preservation of that exactness under tensoring on the right;
- sampled owner declarations:
  `SheafOfModules.RingedSite.RightAugmentedExact`,
  `SheafOfModules.RingedSite.rightAugmentedExact_tensor_right_of_flat`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.isFlat_iff_stalkwise`;
- best owner abstraction: the ambient exactness package is already owned by
  `RightAugmentedExact`, while flatness remains owned by `IsFlat X.sheaf`; the target lemma should
  therefore be the ringed-space specialization of the owner theorem
  `rightAugmentedExact_tensor_right_of_flat`, not a second conjunction-shaped API;
- primitive data: the family `ℱ`, the differentials `d`, the augmentation `q`, and the single
  owner hypothesis `hExact : RightAugmentedExact ℱ d 𝒬 q`;
- derived API: the ringed-space recall/use of the owner theorem, plus the stalkwise flatness
  bridge theorem below.

Source/core/bridge triage:
- `source-facing`: the right-augmented exact sequence
  `\cdots \to \mathcal F_2 \to \mathcal F_1 \to \mathcal F_0 \to \mathcal Q \to 0`;
- `core/canonical`: `RightAugmentedExact`, `rightAugmentedExact_tensor_right_of_flat`,
  `sheafModuleTensorRightFunctor`, and `IsFlat X.sheaf`;
- `bridge/view`: the stalkwise flatness reformulation used only in the companion theorem.
-/

variable {X : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

variable (ℱ : ℕ → X.Modules)
variable (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
variable {𝒬 𝒢 : X.Modules}
variable (q : ℱ 0 ⟶ 𝒬)

-- Proof sketch: this is the ringed-space specialization of the site-level owner theorem
-- `rightAugmentedExact_tensor_right_of_flat`.
/-- Lemma 17.17.10: if
`\cdots \to \mathcal F_2 \to \mathcal F_1 \to \mathcal F_0 \to \mathcal Q \to 0`
is an exact right-augmented sequence of flat `\mathcal O_X`-modules on a ringed space, then
tensoring on the right with any `\mathcal O_X`-module again yields an exact right-augmented
sequence. -/
theorem rightAugmentedExact_moduleTensorRight_of_isFlat
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    (hflat𝒬 : IsFlat X.sheaf 𝒬)
    (hflatℱ : ∀ n : ℕ, IsFlat X.sheaf (ℱ n)) :
    RightAugmentedExact
      (fun n ↦ (sheafModuleTensorRightFunctor 𝒢).obj (ℱ n))
      (fun n ↦ (sheafModuleTensorRightFunctor 𝒢).map (d n))
      ((sheafModuleTensorRightFunctor 𝒢).obj 𝒬)
      ((sheafModuleTensorRightFunctor 𝒢).map q) := by
  letI : IsFlat X.sheaf 𝒬 := hflat𝒬
  letI : ∀ n : ℕ, IsFlat X.sheaf (ℱ n) := hflatℱ
  simpa using rightAugmentedExact_tensor_right_of_flat ℱ d q hExact

/-- Companion bridge: the stalkwise flatness hypotheses from the textbook formulation imply the
canonical flatness-owner hypotheses used by
`rightAugmentedExact_moduleTensorRight_of_isFlat`. -/
theorem rightAugmentedExact_moduleTensor_right_of_flat_stalkwise
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    (hflat𝒬 : ∀ x : X, 𝒬.flat_at x)
    (hflatℱ : ∀ n : ℕ, ∀ x : X, (ℱ n).flat_at x) :
    RightAugmentedExact
      (fun n ↦ (sheafModuleTensorRightFunctor 𝒢).obj (ℱ n))
      (fun n ↦ (sheafModuleTensorRightFunctor 𝒢).map (d n))
      ((sheafModuleTensorRightFunctor 𝒢).obj 𝒬)
      ((sheafModuleTensorRightFunctor 𝒢).map q) := by
  simpa using
    rightAugmentedExact_moduleTensorRight_of_isFlat ℱ d q hExact
      ((SheafOfModules.isFlat_iff_stalkwise 𝒬).2 hflat𝒬)
      (fun n ↦ (SheafOfModules.isFlat_iff_stalkwise (ℱ n)).2 (hflatℱ n))

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_17_11 (from Chap17) -/
open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.17.11:
- primary domain: local factorization of two-step complexes of sheaves of modules on a ringed
  space with flat target, together with the matrix description of maps between finite free
  restrictions;
- sampled owner declarations:
  `SheafOfModules.flat_at`,
  `AlgebraicGeometry.RingedSpace.moduleRestrictionMap`,
  `AlgebraicGeometry.RingedSpace.moduleRestrictionMapLE`,
  `SheafOfModules.freeHomEquiv`;
- best owner abstraction: the core theorem should use the pointwise flatness owner
  `SheafOfModules.flat_at ℱ x` and the restriction-map owners, while the matrix theorem remains a
  source-facing bridge obtained by unwinding `SheafOfModules.freeHomEquiv`;
- primitive data: an open `U`, a point `x ∈ U`, morphisms `α` and `β` with `α ≫ β = 0`, and the
  flat stalk `ℱ_x`;
- derived API: the restricted complex on a neighbourhood `V` and the matrix-family reformulation.

Source/core/bridge triage:
- `source-facing`: the local finite-free factorization statement and its matrix form;
- `core/canonical`: `SheafOfModules.flat_at`, the restriction-map owners, and `freeHomEquiv`;
- `bridge/view`: the matrix-family translation of the factorization statement. -/

variable {X : RingedSpace.{u}} {ℱ : SheafOfModules (RingedSpace.ringCatSheaf X)}

-- Proof sketch: let `I ⊂ \mathcal O_U` be the image of the map
-- `\mathcal O_U \to \mathcal O_U^{\oplus n}`. The relation `\alpha ≫ \beta = 0` says exactly that
-- the induced map `I ⊗_{\mathcal O_U} \mathcal F|_U \to \mathcal F|_U` kills the corresponding
-- finite family of generators. Flatness of `\mathcal F_x` over `\mathcal O_{X, x}` lets one
-- shrink around `x` so that this tensor relation already vanishes on some neighbourhood `V`. Since
-- the source is finite free, this vanishing can be rewritten as a factorization of the restricted
-- map `\beta|_V` through another finite free module with zero composite from `\alpha|_V`.
/-- Lemma 17.17.11: if a two-step complex
`\mathcal O_U \xrightarrow{\alpha} \mathcal O_U^{\oplus n} \xrightarrow{\beta} \mathcal F|_U`
has stalkwise flat target at `x`, then near `x` the restricted map `\beta` factors through a
finite free module in such a way that the restricted `\alpha` maps to zero. -/
theorem exists_local_finite_free_factorization_of_complex_of_flat
    {U : Opens X} {I : Type u} [Finite I]
    (α : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
      (SheafOfModules.free.{u} I : SheafOfModules _))
    (β : (SheafOfModules.free.{u} I : SheafOfModules _) ⟶ ℱ.over U)
    (hcomplex : α ≫ β = 0)
    (x : X) (hx : x ∈ U) (hflat : ℱ.flat_at x) :
    ∃ (V : Opens X) (_ : x ∈ V) (hVU : V ≤ U) (J : Type u) (_ : Finite J)
      (A :
        ((SheafOfModules.free.{u} I : SheafOfModules _).over
            (Over.mk (homOfLE hVU))) ⟶
          (SheafOfModules.free.{u} J : SheafOfModules _))
      (γ :
        (SheafOfModules.free.{u} J : SheafOfModules _) ⟶
          (ℱ.over U).over (Over.mk (homOfLE hVU))),
        moduleRestrictionMapLE hVU α ≫ A = 0 ∧
          A ≫ γ = moduleRestrictionMapLE hVU β := sorry

-- Proof sketch: apply the owner theorem to the morphisms corresponding under
-- `SheafOfModules.freeHomEquiv` to the families `(f_i)` and `(s_i)`. Unwinding those morphisms on
-- a shrunken neighbourhood gives the matrix coefficients `a_{ij}` and local sections `t_j`.
/-- Source-facing matrix form of Lemma 17.17.11: if families `f_i` and `s_i` define a complex
`\mathcal O_U \to \mathcal O_U^{\oplus n} \to \mathcal F|_U` with `\mathcal F_x` flat, then near
`x` the restricted family `s_i` factors through finitely many local sections `t_j` with matrix
coefficients annihilating the restricted `f_i`. -/
theorem exists_local_matrix_factorization_of_complex_of_flat
    {U : Opens X} {n : ℕ}
    (f : Fin n → X.presheaf.obj (op U))
    (s : Fin n → ℱ.val.obj (op U))
    (hcomplex : ∑ i, f i • s i = 0)
    (x : X) (hx : x ∈ U) (hflat : ℱ.flat_at x) :
    ∃ (V : Opens X) (_ : x ∈ V) (hVU : V ≤ U) (m : ℕ)
      (A : Fin n → Fin m → X.presheaf.obj (op V))
      (t : Fin m → ℱ.val.obj (op V)),
        (∀ i, ℱ.val.map (homOfLE hVU).op (s i) = ∑ j, A i j • t j) ∧
          ∀ j, ∑ i, X.presheaf.map (homOfLE hVU).op (f i) * A i j = 0 := sorry

end AlgebraicGeometry.RingedSpace
