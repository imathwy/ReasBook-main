import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_4_1

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)

-- Semantic recall via `lean_leansearch`: the visible hits were abstract model-categorical
-- cofibration and retract APIs, while the verified local owners for this construction are
-- `basedMappingCylinder`, `basedMappingCylinderTopInclusion`, and
-- `basedMappingCylinderTargetInclusion`. The source-faithful statement is therefore the explicit
-- mapping-cylinder factorization together with the unbased cofibration and retraction clauses.

/-- The constant homotopy on a based map `f : X ⟶ Y` fixes the basepoint track
`{underTopBasepoint X} × I`. -/
theorem basedMapConstantHomotopy_map_basepoint {X Y : BasedSpace} (f : X ⟶ Y) (t : I) :
    (ContinuousMap.comp f.right.hom ContinuousMap.fst) (underTopBasepoint X, t) =
      underTopBasepoint Y := sorry

/-- The constant based homotopy on a based map `f : X ⟶ Y`. -/
def basedMapConstantHomotopy {X Y : BasedSpace} (f : X ⟶ Y) : BasedHomotopy X Y where
  toContinuousMap := ContinuousMap.comp f.right.hom ContinuousMap.fst
  map_basepoint' := basedMapConstantHomotopy_map_basepoint f

/-- The reduced-cylinder map `X ∧ I₊ ⟶ Y` induced by the constant homotopy on `f`. -/
def basedMappingCylinderRetractionCylinderMap {X Y : BasedSpace} (f : X ⟶ Y) :
    reducedCylinder X ⟶ Y :=
  basedHomotopyToReducedCylinderMap (basedMapConstantHomotopy f)

/-- The identity on `Y` and the constant cylinder map agree along the attaching map that defines
`M_f`. -/
theorem basedMappingCylinderRetraction_condition {X Y : BasedSpace} (f : X ⟶ Y) :
    f = reducedCylinderBaseInclusion X ≫ basedMappingCylinderRetractionCylinderMap f := sorry

/-- The maps used to descend the mapping-cylinder retraction form a commuting square over the
attaching map for `M_f`. -/
theorem basedMappingCylinderRetraction_commSq {X Y : BasedSpace} (f : X ⟶ Y) :
    CommSq f (reducedCylinderBaseInclusion X) (𝟙 Y)
      (basedMappingCylinderRetractionCylinderMap f) := by
  refine ⟨?_⟩
  simpa [Category.id_comp] using basedMappingCylinderRetraction_condition f

/-- The evident retraction `M_f ⟶ Y`, given by the identity on the target summand and the constant
homotopy at `f` on the reduced-cylinder summand. -/
def basedMappingCylinderRetraction {X Y : BasedSpace} (f : X ⟶ Y) :
    basedMappingCylinder f ⟶ Y :=
  pushout.desc
    (𝟙 Y)
    (basedMappingCylinderRetractionCylinderMap f)
    (basedMappingCylinderRetraction_commSq f).w

/-- Restricting the mapping-cylinder retraction to the cylinder summand recovers the constant map
induced by the constant homotopy on `f`. -/
@[simp] theorem basedMappingCylinderCylinderInclusion_comp_retraction {X Y : BasedSpace}
    (f : X ⟶ Y) :
    basedMappingCylinderCylinderInclusion f ≫ basedMappingCylinderRetraction f =
      basedMappingCylinderRetractionCylinderMap f := by
  simpa [basedMappingCylinderRetraction] using
    (pushout.inr_desc (𝟙 Y) (basedMappingCylinderRetractionCylinderMap f)
      (basedMappingCylinderRetraction_commSq f).w)

/-- Construction 8.4.2 (1). The original based map `f` factors through its based mapping cylinder
as `X ⟶ M_f ⟶ Y`. -/
theorem basedMappingCylinderFactorization {X Y : BasedSpace} (f : X ⟶ Y) :
    basedMappingCylinderTopInclusion f ≫ basedMappingCylinderRetraction f = f := by
  ext x
  change (basedMappingCylinderRetraction f).right.hom
      ((basedMappingCylinderTopInclusion f).right.hom x) =
    f.right.hom x
  rw [basedMappingCylinderTopInclusion_apply]
  have hcomp :
      (basedMappingCylinderRetraction f).right.hom
          ((basedMappingCylinderCylinderInclusion f).right.hom
            ((reducedCylinderTopInclusion X).right.hom x)) =
        (basedMappingCylinderRetractionCylinderMap f).right.hom
          ((reducedCylinderTopInclusion X).right.hom x) := by
    exact
      congrArg
        (fun k ↦ k.right.hom ((reducedCylinderTopInclusion X).right.hom x))
        (basedMappingCylinderCylinderInclusion_comp_retraction f)
  rw [hcomp, reducedCylinderTopInclusion_apply]
  simpa [basedMappingCylinderRetractionCylinderMap, basedMapConstantHomotopy] using
    (basedHomotopyToReducedCylinderMap_apply_mk (basedMapConstantHomotopy f) x (1 : I))

/-- Construction 8.4.2 (2). The inclusion `X ⟶ M_f` appearing in the mapping-cylinder
factorization is an unbased cofibration on underlying spaces. -/
theorem basedMappingCylinderTopInclusion_isCofibration {X Y : BasedSpace} (f : X ⟶ Y) :
    IsCofibration (basedMappingCylinderTopInclusion f).right.hom := sorry

/-- Construction 8.4.2 (3). The map `M_f ⟶ Y` is a retraction of the canonical inclusion
`Y ⟶ M_f`. -/
@[simp] theorem basedMappingCylinderTargetInclusion_comp_retraction {X Y : BasedSpace}
    (f : X ⟶ Y) :
    basedMappingCylinderTargetInclusion f ≫ basedMappingCylinderRetraction f = 𝟙 Y := by
  simpa [basedMappingCylinderRetraction] using
    (pushout.inl_desc (𝟙 Y) (basedMappingCylinderRetractionCylinderMap f)
      (basedMappingCylinderRetraction_commSq f).w)
