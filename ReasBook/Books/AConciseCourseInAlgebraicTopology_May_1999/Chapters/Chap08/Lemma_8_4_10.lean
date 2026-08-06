import Mathlib.CategoryTheory.CommSq
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_5_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_4_5

open CategoryTheory Limits

noncomputable section

universe u

local notation "BasedSpace" => Under (⊤_ TopCat)

-- Semantic recall via `lean_leansearch`: the visible hits were unrelated homological-complex
-- homotopy-cofiber lemmas, while the verified Chapter 8 owners here are `homotopyCofiber`,
-- `homotopyCofiberTargetInclusion`, `cofiberStructureMap`, `signedBasedSuspensionMap`,
-- `CommSq`, and `HomotopicUnder`.

/-- The target inclusion `i(f)` followed by `π(f) : C_f ⟶ ΣX` agrees with the constant map from
the cone on `Y`, so the cofiber universal property for `C_{i(f)}` applies. -/
private theorem iteratedCofiberToSuspensionComparison_w {X Y : BasedSpace} (f : X ⟶ Y) :
    homotopyCofiberTargetInclusion f ≫ cofiberStructureMap f =
      basedConeBaseInclusion Y ≫ constantBasedMap (basedCone Y) (basedSuspension X) := by
  calc
    homotopyCofiberTargetInclusion f ≫ cofiberStructureMap f =
        constantBasedMap Y (basedSuspension X) := by
          exact cofiberStructureMap_targetInclusion f
    _ = basedConeBaseInclusion Y ≫ constantBasedMap (basedCone Y) (basedSuspension X) := by
      ext y
      rfl

/-- The comparison map `C_{i(f)} ⟶ ΣX` obtained by collapsing the cone on `Y` inside the cofiber
of the target inclusion `i(f) = homotopyCofiberTargetInclusion f : Y ⟶ C_f`. -/
def iteratedCofiberToSuspensionComparison {X Y : BasedSpace} (f : X ⟶ Y) :
    homotopyCofiber (homotopyCofiberTargetInclusion f) ⟶ basedSuspension X :=
  pushout.desc
    (cofiberStructureMap f)
    (constantBasedMap (basedCone Y) (basedSuspension X))
    (iteratedCofiberToSuspensionComparison_w f)

/-- The comparison map `C_{i(f)} ⟶ ΣX` is the pushout descent of `π(f) : C_f ⟶ ΣX` on the target
summand and the constant map on the cone summand `CY`. -/
theorem iteratedCofiberToSuspensionComparison_def {X Y : BasedSpace} (f : X ⟶ Y) :
    iteratedCofiberToSuspensionComparison f =
      pushout.desc
        (cofiberStructureMap f)
        (constantBasedMap (basedCone Y) (basedSuspension X))
        (iteratedCofiberToSuspensionComparison_w f) := rfl

/-- Lemma 8.4.10 (1): in the comparison diagram built from `i(f) : Y ⟶ C_f`, the triangle with
vertex `ΣX` commutes strictly. Equivalently, the target inclusion `C_f ⟶ C_{i(f)}` followed by
the comparison map `C_{i(f)} ⟶ ΣX` is exactly `π(f) : C_f ⟶ ΣX`. -/
@[simp] theorem cofiberTargetInclusion_comp_iteratedCofiberToSuspensionComparison
    {X Y : BasedSpace} (f : X ⟶ Y) :
    homotopyCofiberTargetInclusion (homotopyCofiberTargetInclusion f) ≫
        iteratedCofiberToSuspensionComparison f =
      cofiberStructureMap f := by
  simpa [iteratedCofiberToSuspensionComparison_def, homotopyCofiberTargetInclusion] using
    (pushout.inl_desc
      (cofiberStructureMap f)
      (constantBasedMap (basedCone Y) (basedSuspension X))
      (iteratedCofiberToSuspensionComparison_w f))

/-- The comparison map `C_{i(f)} ⟶ ΣX` restricts to the constant map on the cone summand
`CY ⟶ C_{i(f)}`. -/
@[simp] theorem iteratedCofiberToSuspensionComparison_coneInclusion
    {X Y : BasedSpace} (f : X ⟶ Y) :
    homotopyCofiberConeInclusion (homotopyCofiberTargetInclusion f) ≫
        iteratedCofiberToSuspensionComparison f =
      constantBasedMap (basedCone Y) (basedSuspension X) := by
  simpa [iteratedCofiberToSuspensionComparison_def, homotopyCofiberConeInclusion] using
    (pushout.inr_desc
      (cofiberStructureMap f)
      (constantBasedMap (basedCone Y) (basedSuspension X))
      (iteratedCofiberToSuspensionComparison_w f))

/-- Lemma 8.4.10 (1), expressed through the canonical commutative-square owner `CommSq`. -/
theorem cofiberTargetInclusion_iteratedCofiberToSuspensionComparison_commSq
    {X Y : BasedSpace} (f : X ⟶ Y) :
    CommSq
      (homotopyCofiberTargetInclusion (homotopyCofiberTargetInclusion f))
      (cofiberStructureMap f)
      (iteratedCofiberToSuspensionComparison f)
      (𝟙 (basedSuspension X)) := by
  refine ⟨?_⟩
  simpa only [Category.comp_id] using
    cofiberTargetInclusion_comp_iteratedCofiberToSuspensionComparison f

/-- Lemma 8.4.10 (2): the other triangle in the comparison diagram commutes up to homotopy. In
the sign convention of Definition 8.4.5, the comparison map `C_{i(f)} ⟶ ΣX` followed by
`signedBasedSuspensionMap f : ΣX ⟶ ΣY` is homotopic under the basepoint to
`π(i(f)) : C_{i(f)} ⟶ ΣY`. -/
theorem iteratedCofiberToSuspensionComparison_comp_signedBasedSuspensionMap_homotopic
    {X Y : BasedSpace} (f : X ⟶ Y) :
    HomotopicUnder
      (iteratedCofiberToSuspensionComparison f ≫ signedBasedSuspensionMap f)
      (cofiberStructureMap (homotopyCofiberTargetInclusion f)) := sorry
