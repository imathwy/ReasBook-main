import StacksProject_2024.stacks_project.Chap05.Definition_5_17_2
import StacksProject_2024.stacks_project.Chap06.Definition_6_7_1
import StacksProject_2024.stacks_project.Chap06.Lemma_6_21_6
import StacksProject_2024.stacks_project.Chap07.Definition_7_15_1_Topoi

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open TopologicalSpace.Opens
open TopCat
open scoped TopCat
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace TopCat.Hom

variable {X Y : TopCat.{u}}

/-- The morphism of topoi on set-valued sheaves induced by a continuous map of topological spaces.
This is the canonical Chapter 7 site-to-topos bridge specialized to `Opens.map f`. -/
noncomputable abbrev toMorphismOfTopoi (f : X ⟶ Y)
    [PreservesFiniteLimits
      ((Opens.map f).sheafPullback
        (Type u)
        (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X))] :
    CategoryTheory.MorphismOfTopoiIn
      (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) :=
  (Opens.map f).morphismOfTopoiInOfContinuous
    (Opens.grothendieckTopology Y)
    (Opens.grothendieckTopology X)

@[simp] theorem toMorphismOfTopoi_inverseImage (f : X ⟶ Y)
    [PreservesFiniteLimits
      ((Opens.map f).sheafPullback
        (Type u)
        (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X))] :
    f.toMorphismOfTopoi⁻¹ =
      (Opens.map f).sheafPullback
        (Type u)
        (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X) :=
  rfl

@[simp] theorem toMorphismOfTopoi_pushforward (f : X ⟶ Y)
    [PreservesFiniteLimits
      ((Opens.map f).sheafPullback
        (Type u)
        (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X))] :
    f.toMorphismOfTopoi _* =
      (Opens.map f).sheafPushforwardContinuous
        (Type u)
        (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X) :=
  rfl

end TopCat.Hom

namespace TopCat.Sheaf

variable {X Y Y' : TopCat.{u}}

/-- The pullback space `X' = Y' ×[Y] X` in the proper base change square. -/
noncomputable def properBaseChangePullback (f : X ⟶ Y) (g : Y' ⟶ Y) : TopCat :=
  Limits.pullback f g

/-- The projection `g' : X' ⟶ X` from the proper base change pullback. -/
noncomputable def properBaseChangeFst (f : X ⟶ Y) (g : Y' ⟶ Y) :
    properBaseChangePullback f g ⟶ X :=
  Limits.pullback.fst f g

/-- The projection `f' : X' ⟶ Y'` from the proper base change pullback. -/
noncomputable def properBaseChangeSnd (f : X ⟶ Y) (g : Y' ⟶ Y) :
    properBaseChangePullback f g ⟶ Y' :=
  Limits.pullback.snd f g

section ProperBaseChangeForSheavesOfSets

variable (f : X ⟶ Y) (g : Y' ⟶ Y)

local notation "X'" => properBaseChangePullback f g
local notation "g'" => properBaseChangeFst f g
local notation "f'" => properBaseChangeSnd f g

local instance preservesFiniteLimits_sheafPullback_f :
    PreservesFiniteLimits
      ((Opens.map f).sheafPullback
        (Type u)
        (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)) :=
  Functor.sheafPullbackConstruction.preservesFiniteLimits
    (Opens.map f)
    (Type u)
    (Opens.grothendieckTopology Y)
    (Opens.grothendieckTopology X)

local instance preservesFiniteLimits_sheafPullback_g :
    PreservesFiniteLimits
      ((Opens.map g).sheafPullback
        (Type u)
        (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology Y')) :=
  Functor.sheafPullbackConstruction.preservesFiniteLimits
    (Opens.map g)
    (Type u)
    (Opens.grothendieckTopology Y)
    (Opens.grothendieckTopology Y')

local instance preservesFiniteLimits_sheafPullback_f' :
    PreservesFiniteLimits
      ((Opens.map f').sheafPullback
        (Type u)
        (Opens.grothendieckTopology Y')
        (Opens.grothendieckTopology X')) :=
  Functor.sheafPullbackConstruction.preservesFiniteLimits
    (Opens.map f')
    (Type u)
    (Opens.grothendieckTopology Y')
    (Opens.grothendieckTopology X')

local instance preservesFiniteLimits_sheafPullback_g' :
    PreservesFiniteLimits
      ((Opens.map g').sheafPullback
        (Type u)
        (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology X')) :=
  Functor.sheafPullbackConstruction.preservesFiniteLimits
    (Opens.map g')
    (Type u)
    (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology X')

/- Domain-style sampling for Lemma 20.18.3:
- primary domain: proper base change for sheaves of sets on topological spaces, expressed through
  the canonical base-change morphism of the associated topoi;
- sampled owner API:
  `MorphismOfTopoiIn.baseChange`,
  `Functor.morphismOfTopoiInOfContinuous`,
  `TopCat.Sheaf.pullbackPushforwardAdjunction`,
  `TopCat.Sheaf.pullbackComp`,
  `Sh(X)`,
  `pullback.condition`;
- best owner abstraction: `MorphismOfTopoiIn.baseChange`, specialized to the morphisms of topoi
  induced by the continuous maps of the pullback square via `Functor.morphismOfTopoiInOfContinuous`;
- primitive data: the continuous maps `f : X ⟶ Y`, `g : Y' ⟶ Y`, and the pullback commutativity
  relation `pullback.condition`;
- derived API: the inverse-image `TwoSquare` bridge from the pullback square of spaces to the
  canonical owner `MorphismOfTopoiIn.baseChange`.

Source/core/bridge triage:
- `source-facing`: the proper-base-change statement for a sheaf of sets on `X`;
- `core/canonical`: `MorphismOfTopoiIn.baseChange`;
- `bridge/view`: the inverse-image `TwoSquare` induced by the pullback square of spaces. -/

/-- The pullback square of spaces underlying proper base change induces the canonical inverse-image
square on the associated morphisms of topoi of set-valued sheaves. This is bridge data for the
owner morphism `MorphismOfTopoiIn.baseChange`. -/
noncomputable def properBaseChangeInverseImageSquare :
    CategoryTheory.TwoSquare
      (g.toMorphismOfTopoi⁻¹)
      (f.toMorphismOfTopoi⁻¹)
      ((properBaseChangeSnd f g).toMorphismOfTopoi⁻¹)
      ((properBaseChangeFst f g).toMorphismOfTopoi⁻¹) := by
  change
    TopCat.Sheaf.pullback (Type u) g ⋙
        TopCat.Sheaf.pullback (Type u) (properBaseChangeSnd f g) ⟶
      TopCat.Sheaf.pullback (Type u) f ⋙
        TopCat.Sheaf.pullback (Type u) (properBaseChangeFst f g)
  exact
    (TopCat.Sheaf.pullbackComp (properBaseChangeSnd f g) g).hom ≫
      eqToHom
        ((congrArg
            (TopCat.Sheaf.pullback (Type u))
            (show properBaseChangeFst f g ≫ f = properBaseChangeSnd f g ≫ g from
              Limits.pullback.condition)).symm) ≫
      (TopCat.Sheaf.pullbackComp (properBaseChangeFst f g) f).inv

/-- The canonical proper-base-change morphism
`g⁻¹ f_* ℱ ⟶ f'_* (g')⁻¹ ℱ` on set-valued sheaves for the pullback square of `f` along `g`. -/
noncomputable def properBaseChangeSetSheafBaseChange (ℱ : Sh(X)) :=
  ((MorphismOfTopoiIn.baseChange
      (properBaseChangeFst f g).toMorphismOfTopoi
      (properBaseChangeSnd f g).toMorphismOfTopoi
      f.toMorphismOfTopoi
      g.toMorphismOfTopoi
      (properBaseChangeInverseImageSquare f g)).app ℱ)

-- Proof sketch: specialize the Chapter 7 owner `MorphismOfTopoiIn.baseChange` to the pullback
-- square of topological spaces via `properBaseChangeInverseImageSquare`. Properness of `f`
-- identifies this canonical comparison with the set-valued proper-base-change map, which is an
-- isomorphism.
/-- Lemma 20.18.3 (Proper base change for sheaves of sets): for a cartesian square of topological
spaces with `X' = Y' ×[Y] X`, a proper map `f : X ⟶ Y`, and a sheaf of sets `ℱ` on `X`,
the canonical proper-base-change morphism
`g⁻¹ f_* ℱ ⟶ f'_* (g')⁻¹ ℱ` is an isomorphism, where
`g' : X' ⟶ X` and `f' : X' ⟶ Y'` are the pullback projections. -/
@[stacks 0D90]
theorem proper_base_change_set_sheaf_baseChange_isIso
    (hf : IsProperMap f) (ℱ : Sh(X)) :
    IsIso (properBaseChangeSetSheafBaseChange f g ℱ) :=
  sorry

instance instIsIso_proper_base_change_set_sheaf_baseChange
    [hf : Fact (IsProperMap f)] {ℱ : Sh(X)} :
    IsIso (properBaseChangeSetSheafBaseChange f g ℱ) :=
  proper_base_change_set_sheaf_baseChange_isIso f g hf.out ℱ

end ProperBaseChangeForSheavesOfSets

end TopCat.Sheaf
