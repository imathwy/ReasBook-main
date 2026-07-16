import StacksProject_2024.stacks_project.Chap07.Lemma_7_25_8
import StacksProject_2024.stacks_project.Chap07.Lemma_7_21_7
import StacksProject_2024.stacks_project.Chap21.«21_30_0_1»
import StacksProject_2024.stacks_project.Chap21.«21_31_0_1»
import StacksProject_2024.stacks_project.Chap21.Lemma_21_31_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.GrothendieckTopology CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.GrothendieckTopology

noncomputable section

universe u

/- Domain-style sampling for Lemma 21.31.8:
- primary domain: comparison morphisms between the localized qc and Zariski topologies on
  `Over X`, together with their compatibility with pullback and pushforward along
  `f : X ⟶ Y` in `LC`;
- inspected owner declarations:
  `Functor.sheafPullback`,
  `comparisonOver_le`,
  `comparisonTopologyPullback`,
  `GrothendieckTopology.overMapPullback`,
  `GrothendieckTopology.overMapPushforward`;
- best owner abstraction: the qc/Zariski comparison is already organized in Chapter `21.30`
  around the topology-comparison owner layer `τzar ≤ τqc`, while the small-to-big Zariski part
  already lives upstream as the canonical owner `Functor.sheafPullback` with notation
  `π[_, _]⁻¹`, and the qc direct image along `f` should use the localized owner
  `τqc.overMapPushforward (Type u) f`;
- primitive vs derived: the primitive data are the global topologies `τzar`, `τqc`, the
  comparison `hle : τzar ≤ τqc`, and the small-to-big Zariski functors `π_X`, `π_Y`; the
  source-facing composites `ε_X⁻¹`, `ε_Y⁻¹`, `a_X⁻¹`, `a_Y⁻¹` are derived API and are written
  below via the owner-level notations `ε[hle]_(X)⁻¹`, `ε[hle]_(Y)⁻¹`, `a[hle, πX]⁻¹`, and
  `a[hle, πY]⁻¹` exported by the canonical bridge owners `comparisonTopologyPullback` and
  `aInverse`.

Source/core/bridge triage:
- `source-facing`: the three comparison isomorphisms of Lemma 21.31.8;
- `core/canonical`: `Functor.sheafPullback`, `comparisonTopologyPullback`, and
  `GrothendieckTopology.overMapPullback`, `GrothendieckTopology.overMapPushforward`;
- `bridge/view`: the source notation `ε_X⁻¹`, `ε_Y⁻¹`, `a_X⁻¹`, `a_Y⁻¹`, realized below by the
  exported owner-level notations `ε[hle]_(_)⁻¹` and `a[hle, _]⁻¹` over the canonical owners
  `comparisonTopologyPullback` and `aInverse`, not by new local owner declarations.
-/

section

variable (τzar τqc : GrothendieckTopology LCCat.{u}) (hle : τzar ≤ τqc)
variable {X Y : LCCat.{u}}

local notation "εX⁻¹" => ε[hle]_(X)⁻¹
local notation "εY⁻¹" => ε[hle]_(Y)⁻¹

-- Proof sketch: the qc/Zariski comparison is the Chapter `21.30` topology-comparison owner for
-- `τzar ≤ τqc`, specialized to the localized slice sites. The localized pullbacks on
-- `LC_{Zar}` and `LC_{qc}` are both induced by `Over.map f`, and the comparison square is the
-- inverse-image form of the same canonical topology-comparison compatibility.
/-- Lemma 21.31.8 (1): for a morphism `f : X ⟶ Y` in `LC`, the inverse-image functors
`ε_X⁻¹ : Sh(LC_{Zar}/X) ⥤ Sh(LC_{qc}/X)` and `ε_Y⁻¹ : Sh(LC_{Zar}/Y) ⥤ Sh(LC_{qc}/Y)` fit into the
canonical comparison isomorphism between the two composites with horizontal arrows given by the
localized morphisms `f_{qc}` and `f_{Zar}`. -/
@[stacks 0D92]
theorem lcQc_lcZar_topoi_square_isomorphic
    (f : X ⟶ Y)
    [HasWeakSheafify (τqc.over X) (Type u)]
    [HasWeakSheafify (τqc.over Y) (Type u)] :
    IsIsomorphic
      (τzar.overMapPullback (Type u) f ⋙ εX⁻¹)
      (εY⁻¹ ⋙ τqc.overMapPullback (Type u) f) := by
  sorry

section SmallToQc

variable (πX : Opens X.obj ⥤ Over X) (πY : Opens Y.obj ⥤ Over Y)
variable [Functor.IsContinuous πX (Opens.grothendieckTopology X.obj) (τzar.over X)]
variable [Functor.IsContinuous πY (Opens.grothendieckTopology Y.obj) (τzar.over Y)]
variable [(πX.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X.obj)
  (τzar.over X)).IsRightAdjoint]
variable [(πY.sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology Y.obj)
  (τzar.over Y)).IsRightAdjoint]
variable [HasWeakSheafify (τqc.over X) (Type u)]
variable [HasWeakSheafify (τqc.over Y) (Type u)]

local notation "aX⁻¹" => a[hle, πX]⁻¹
local notation "aY⁻¹" => a[hle, πY]⁻¹

-- Proof sketch: compose the inverse-image identification for the small/big Zariski square from
-- Lemma `21.31.7 (5)` with the qc/Zariski comparison square from clause `(1)`. The source
-- notation `a_X⁻¹` and `a_Y⁻¹` is realized here by the reusable owner notation
-- `a[hle, πX]⁻¹` and `a[hle, πY]⁻¹` for the composites `π_X⁻¹ ≫ ε_X⁻¹` and
-- `π_Y⁻¹ ≫ ε_Y⁻¹`, with no separate owner declaration.
/-- Lemma 21.31.8 (2): with `a_X = π_X ∘ ε_X` and `a_Y = π_Y ∘ ε_Y`, the localized qc topoi and
the small topoi fit into the canonical comparison isomorphism over a morphism `f : X ⟶ Y` in
`LC`. -/
@[stacks 0D92]
theorem lcQc_small_topoi_square_isomorphic
    (f : X ⟶ Y) :
    IsIsomorphic
      (TopCat.Sheaf.pullback (Type u) f.hom ⋙ aX⁻¹)
      (aY⁻¹ ⋙ τqc.overMapPullback (Type u) f) := by
  sorry

-- Proof sketch: first apply the proper base-change comparison from Lemma `21.31.7 (7)` to the
-- composite `π_Y⁻¹ ∘ f_*`. Then compose with the qc/Zariski comparison pullbacks on the two
-- localized sites, keeping the source notation `a_X⁻¹`, `a_Y⁻¹` only through the reusable owner
-- notation `a[hle, πX]⁻¹`, `a[hle, πY]⁻¹`.
/-- Lemma 21.31.8 (3): if `f : X ⟶ Y` is proper, then the inverse image `a_Y⁻¹` composed with
small direct image along `f` is canonically isomorphic to the qc direct image along `f_{qc}`
composed with `a_X⁻¹`, formalized by the localized direct-image owner
`τqc.overMapPushforward (Type u) f`. -/
@[stacks 0D92]
theorem proper_smallPushforward_aInverse_isomorphic_lcQcPushforward_aInverse
    (f : X ⟶ Y)
    (hf : IsProperMap f.hom) :
    IsIsomorphic
      (TopCat.Sheaf.pushforward (Type u) f.hom ⋙ aY⁻¹)
      (aX⁻¹ ⋙ τqc.overMapPushforward (Type u) f) := by
  sorry

end SmallToQc

end
