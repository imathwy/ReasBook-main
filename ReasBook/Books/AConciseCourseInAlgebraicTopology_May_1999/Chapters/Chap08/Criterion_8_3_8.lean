import Mathlib.CategoryTheory.EpiMono
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Adjunction_8_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_3_7

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)
local notation "I₊" => adjoinBasepoint (TopCat.of I)

-- Semantic recall: `lean_leansearch` again surfaced only model-categorical cofibration APIs, so
-- this file follows the verified Chapter 6 mapping-cylinder criterion and the local Chapter 8
-- owners `IsBasedCofibration`, `reducedCylinder`, and `basedMappingCylinder`.

/-- The canonical map `A ∧ I₊ ⟶ X ∧ I₊` induced by a based map `i : A ⟶ X`. -/
abbrev basedMappingCylinderCylinderMap {A X : BasedSpace} (i : A ⟶ X) :
    reducedCylinder A ⟶ reducedCylinder X :=
  smashProductMap i (𝟙 I₊)

/-- The two maps `X ⟶ X ∧ I₊` and `A ∧ I₊ ⟶ X ∧ I₊` agree on `A` along the time-`0` inclusion, so
they descend to the based mapping cylinder `M_i`. -/
theorem basedMappingCylinderCanonicalMap_condition
    {A X : BasedSpace} (i : A ⟶ X) :
    i ≫ reducedCylinderBaseInclusion X =
      reducedCylinderBaseInclusion A ≫ basedMappingCylinderCylinderMap i := sorry

/-- The square comparing `i : A ⟶ X` with the endpoint inclusions into the reduced cylinders
commutes. -/
theorem basedMappingCylinderCanonicalMap_commSq
    {A X : BasedSpace} (i : A ⟶ X) :
    CommSq i (reducedCylinderBaseInclusion A)
      (reducedCylinderBaseInclusion X) (basedMappingCylinderCylinderMap i) := by
  refine ⟨?_⟩
  simpa using basedMappingCylinderCanonicalMap_condition i

/-- The canonical map `M_i ⟶ X ∧ I₊` from the based mapping cylinder of `i` to the reduced
cylinder on `X`. -/
def basedMappingCylinderCanonicalMap {A X : BasedSpace} (i : A ⟶ X) :
    basedMappingCylinder i ⟶ reducedCylinder X :=
  pushout.desc
    (reducedCylinderBaseInclusion X)
    (basedMappingCylinderCylinderMap i)
    (basedMappingCylinderCanonicalMap_condition i)

/-- Criterion 8.3.8. A based map `i : A ⟶ X` is a based cofibration if and only if its based
mapping cylinder `M_i` is a retract of `X ∧ I₊`, formalized by requiring the canonical map
`basedMappingCylinderCanonicalMap i : M_i ⟶ X ∧ I₊` to admit a left inverse whose restrictions to
`X` and `A ∧ I₊` are the canonical inclusions into `M_i`. -/
theorem isBasedCofibration_iff_exists_basedMappingCylinderRetract
    {A X : BasedSpace} {i : A ⟶ X} :
    IsBasedCofibration i ↔
      ∃ r : reducedCylinder X ⟶ basedMappingCylinder i,
        basedMappingCylinderCanonicalMap i ≫ r = 𝟙 (basedMappingCylinder i) ∧
        reducedCylinderBaseInclusion X ≫ r = basedMappingCylinderTargetInclusion i ∧
        basedMappingCylinderCylinderMap i ≫ r = basedMappingCylinderCylinderInclusion i := sorry

/-- Criterion 8.3.8, expressed with the canonical categorical owner `SplitMono` for the retract of
`basedMappingCylinderCanonicalMap i`. The two displayed equalities record the source-specific
restriction conditions on the retraction. -/
theorem isBasedCofibration_iff_exists_basedMappingCylinderSplitMono
    {A X : BasedSpace} {i : A ⟶ X} :
    IsBasedCofibration i ↔
      ∃ s : SplitMono (basedMappingCylinderCanonicalMap i),
        reducedCylinderBaseInclusion X ≫ s.retraction = basedMappingCylinderTargetInclusion i ∧
        basedMappingCylinderCylinderMap i ≫ s.retraction =
          basedMappingCylinderCylinderInclusion i := by
  constructor
  · intro hi
    rcases isBasedCofibration_iff_exists_basedMappingCylinderRetract.mp hi with
      ⟨r, hr, h_endpoint, h_cylinder⟩
    exact ⟨⟨r, hr⟩, h_endpoint, h_cylinder⟩
  · intro hi
    rcases hi with ⟨s, h_endpoint, h_cylinder⟩
    exact isBasedCofibration_iff_exists_basedMappingCylinderRetract.mpr
      ⟨s.retraction, s.id, h_endpoint, h_cylinder⟩
