import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Lemma_17_28_12

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y S : RingedSpace.{u}}

/- Domain-style sampling for Lemma 17.28.14:
- primary domain: the transitivity sequence for relative differentials of composable morphisms of
  ringed spaces;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.Ω[_]`,
  `AlgebraicGeometry.RingedSpace.pullbackDifferentialsComparison`,
  `SheafOfModules.pullbackId`,
  `CategoryTheory.ShortComplex`;
- best owner abstraction:
  the source-facing short complex
  `f^*Ω[g] → Ω[f ≫ g] → Ω[f] → 0`, built from the canonical base-change comparison
  `pullbackDifferentialsComparison` together with the canonical identity-pullback isomorphism
  `SheafOfModules.pullbackId`;
- primitive data:
  only the composable morphisms `f : X ⟶ Y` and `g : Y ⟶ S`;
- derived API:
  the two transitivity morphisms, the named short complex they define, and its exactness and
  epimorphy.

Source/core/bridge triage:
- `source-facing`: the transitivity short complex together with its two companion morphisms;
- `core/canonical`: `Ω[_]`, `pullbackDifferentialsComparison`, `SheafOfModules.pullbackId`, and
  `ShortComplex`;
- `bridge/view`: the identity-base-change square and the stalkwise exactness criterion used in the
  proof sketch.

The former theorem `modulePullback_id_obj_differentials_eq` was duplicate bridge data: the
identity pullback is already canonically owned by `SheafOfModules.pullbackId`, so the public
surface should use that owner directly. The source-facing owner in this file is therefore the
transitivity short complex itself, with the individual comparison maps as companion data. -/

/-- The canonical map `f^*Ω_{Y/S} → Ω_{X/S}` in the transitivity sequence for relative
differentials. -/
noncomputable def relativeDifferentialsTransitivityLeft
    (f : X ⟶ Y) (g : Y ⟶ S) :
    (f^*).obj Ω[g] ⟶ Ω[f ≫ g] :=
  pullbackDifferentialsComparison f (𝟙 S) g (f ≫ g) ⟨by simp⟩

/-- The canonical map `Ω_{X/S} → Ω_{X/Y}` in the transitivity sequence for relative differentials.
-/
noncomputable def relativeDifferentialsTransitivityRight
    (f : X ⟶ Y) (g : Y ⟶ S) :
    Ω[f ≫ g] ⟶ Ω[f] :=
  (SheafOfModules.pullbackId X.ringCatSheaf).inv.app Ω[f ≫ g] ≫
    pullbackDifferentialsComparison (𝟙 X) g (f ≫ g) f ⟨by simp⟩

-- Proof sketch: pass to stalks, where Lemma `17.28.12` identifies the two displayed sheaf maps
-- with the standard maps between Kähler differentials of local rings. The algebraic transitivity
-- sequence has zero composite, so the sheaf-level composite vanishes.
/-- The canonical transitivity morphisms on relative differentials compose to zero. -/
theorem relativeDifferentialsTransitivity_comp_zero
    (f : X ⟶ Y) (g : Y ⟶ S) :
    relativeDifferentialsTransitivityLeft f g ≫
      relativeDifferentialsTransitivityRight f g = 0 := sorry

/-- The canonical short complex
`f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y}`
in the transitivity sequence for relative differentials. -/
noncomputable def relativeDifferentialsTransitivity
    (f : X ⟶ Y) (g : Y ⟶ S) :
    ShortComplex (RingedSpace.Modules X) :=
  ShortComplex.mk
    (relativeDifferentialsTransitivityLeft f g)
    (relativeDifferentialsTransitivityRight f g)
    (relativeDifferentialsTransitivity_comp_zero f g)

-- Proof sketch: check the statement on stalks. Lemma `17.28.12` identifies the stalk maps with
-- the usual transitivity maps for Kähler differentials of the local ring maps
-- `𝒪_{S,g(f(x))} → 𝒪_{Y,f(x)} → 𝒪_{X,x}`, and Algebra, Lemma `10.131.7` gives exactness and
-- surjectivity there. Then use the stalkwise criterion for exactness of sheaves of modules and for
-- epimorphy.
/-- Lemma 17.28.14: for composable morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ S`, the
canonical transitivity short complex
`f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y}`
is exact. -/
theorem relativeDifferentialsTransitivity_exact
    (f : X ⟶ Y) (g : Y ⟶ S) :
    (relativeDifferentialsTransitivity f g).Exact := sorry

/-- The right map in the transitivity short complex for relative differentials is an epimorphism.
-/
theorem relativeDifferentialsTransitivity_epi
    (f : X ⟶ Y) (g : Y ⟶ S) :
    Epi ((relativeDifferentialsTransitivity f g).g) := sorry

end AlgebraicGeometry.RingedSpace
