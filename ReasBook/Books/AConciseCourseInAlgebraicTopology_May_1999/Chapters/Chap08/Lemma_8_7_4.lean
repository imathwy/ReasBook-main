import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_5_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Construction_8_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Construction_8_7_2

open CategoryTheory
open scoped Topology.Homotopy

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)

-- Semantic recall via `lean_leansearch`: no dedicated based-space owner surfaced for this
-- mapping-cylinder comparison square, while the verified local Chapter 8 owners are
-- `mappingCylinderRetractionComparison`, `mappingCylinderQuotientComparison`,
-- `homotopyFiberToLoopHomotopyCofiber`, and `HomotopicUnder`. The auxiliary `F_j ⟶ F_r` map is
-- kept explicitly, but the labeled entry is the homotopy-commutative triangle involving `η`.

/-- Evaluating the mapping-cylinder factorization `X ⟶ M_f ⟶ Y` at a point of `X` recovers
`f`. -/
@[simp] theorem basedMappingCylinderFactorization_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (x : X.right) :
    f.right.hom x =
      (basedMappingCylinderRetraction f).right.hom
        ((basedMappingCylinderTopInclusion f).right.hom x) := by
  simpa using
    congrArg (fun g : X ⟶ Y ↦ g.right.hom x) (basedMappingCylinderFactorization f).symm

/-- The quotient map `M_f ⟶ C_f` sends the top copy of `X` in the reduced mapping cylinder to the
distinguished basepoint of `C_f`. -/
theorem basedMappingCylinderToHomotopyCofiber_topInclusion_target
    {X Y : BasedSpace} (f : X ⟶ Y) (x : X.right) :
    underTopBasepoint (homotopyCofiber f) =
      (basedMappingCylinderToHomotopyCofiber f).right.hom
        ((basedMappingCylinderTopInclusion f).right.hom x) := sorry

/-- The path in `Y` obtained from a point of `F_j` by applying the retraction `r : M_f ⟶ Y` to its
path coordinate. This is the path-space part of the comparison map `id × P r : F_j ⟶ F_f`. -/
theorem mappingCylinderRetractionComparison_target {X Y : BasedSpace} (f : X ⟶ Y)
    (z : HomotopyFiber (basedMappingCylinderTopInclusion f)) :
    f.right.hom z.point = (basedMappingCylinderRetraction f).right.hom z.path.endpoint := by
  calc
    f.right.hom z.point =
      (basedMappingCylinderRetraction f).right.hom
        ((basedMappingCylinderTopInclusion f).right.hom z.point) :=
      basedMappingCylinderFactorization_apply f z.point
    _ = (basedMappingCylinderRetraction f).right.hom z.path.endpoint := by
      rw [HomotopyFiber.endpoint_eq z]

/-- The path in `Y` obtained from a point of `F_j` by applying the retraction `r : M_f ⟶ Y` to its
path coordinate. This is the path-space part of the comparison map `id × P r : F_j ⟶ F_f`. -/
def mappingCylinderRetractionComparisonPath {X Y : BasedSpace} (f : X ⟶ Y)
    (z : HomotopyFiber (basedMappingCylinderTopInclusion f)) :
    PathSpace (underTopBasepoint Y) :=
  let χ : Path (underTopBasepoint Y) (f.right.hom z.point) :=
    ((PathSpace.toPath z.path).map (basedMappingCylinderRetraction f).right.hom.continuous).cast
      (fundamentalGroupFunctorMap_basepoint (basedMappingCylinderRetraction f)).symm
      (mappingCylinderRetractionComparison_target f z)
  PathSpace.mk χ.toContinuousMap χ.source'

/-- The retraction-comparison path ends at `f(z.point)`. -/
@[simp] theorem mappingCylinderRetractionComparisonPath_endpoint {X Y : BasedSpace} (f : X ⟶ Y)
    (z : HomotopyFiber (basedMappingCylinderTopInclusion f)) :
    (mappingCylinderRetractionComparisonPath f z).endpoint = f.right.hom z.point := sorry

/-- Applying the top inclusion to the point of `F_j` and applying `r : M_f ⟶ Y` to the path
coordinate gives a point of the homotopy fiber `F_r`. This is the source-facing `F_j ⟶ F_r`
comparison map in the diagram of Lemma 8.7.4. -/
theorem mappingCylinderRetractionFiberComparison_condition {X Y : BasedSpace} (f : X ⟶ Y)
    (z : HomotopyFiber (basedMappingCylinderTopInclusion f)) :
    (basedMappingCylinderRetraction f).right.hom
        ((basedMappingCylinderTopInclusion f).right.hom z.point) =
      (mappingCylinderRetractionComparisonPath f z).endpoint := by
  calc
    (basedMappingCylinderRetraction f).right.hom
        ((basedMappingCylinderTopInclusion f).right.hom z.point)
      = f.right.hom z.point := (basedMappingCylinderFactorization_apply f z.point).symm
    _ = (mappingCylinderRetractionComparisonPath f z).endpoint :=
      (mappingCylinderRetractionComparisonPath_endpoint f z).symm

/-- The comparison function `F_j → F_r` obtained by keeping the point in `M_f` and applying the
retraction `r` to the path coordinate. -/
def mappingCylinderRetractionFiberComparisonFun {X Y : BasedSpace} (f : X ⟶ Y) :
    HomotopyFiber (basedMappingCylinderTopInclusion f) →
      HomotopyFiber (basedMappingCylinderRetraction f) :=
  fun z ↦
    HomotopyFiber.mk
      ((basedMappingCylinderTopInclusion f).right.hom z.point)
      (mappingCylinderRetractionComparisonPath f z)
      (mappingCylinderRetractionFiberComparison_condition f z)

/-- The comparison function `F_j → F_r` is continuous. -/
theorem mappingCylinderRetractionFiberComparisonContinuous {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous (mappingCylinderRetractionFiberComparisonFun f) := sorry

/-- The comparison map `F_j → F_r` as a continuous map. -/
def mappingCylinderRetractionFiberComparisonContinuousMap {X Y : BasedSpace} (f : X ⟶ Y) :
    C(HomotopyFiber (basedMappingCylinderTopInclusion f),
      HomotopyFiber (basedMappingCylinderRetraction f)) :=
  { toFun := mappingCylinderRetractionFiberComparisonFun f
    continuous_toFun := mappingCylinderRetractionFiberComparisonContinuous f }

/-- The source-facing comparison map `F_j → F_r` preserves the chosen basepoints. -/
theorem mappingCylinderRetractionFiberComparison_w {X Y : BasedSpace} (f : X ⟶ Y) :
    (homotopyFiber (basedMappingCylinderTopInclusion f)).hom ≫
        TopCat.ofHom (mappingCylinderRetractionFiberComparisonContinuousMap f) =
      (homotopyFiber (basedMappingCylinderRetraction f)).hom := sorry

/-- The based comparison morphism `F_j ⟶ F_r` in the quotient-map diagram,
obtained by applying the top inclusion `j : X ⟶ M_f` to the point coordinate and the retraction
`r : M_f ⟶ Y` to the path coordinate. -/
def mappingCylinderRetractionFiberComparison {X Y : BasedSpace} (f : X ⟶ Y) :
    homotopyFiber (basedMappingCylinderTopInclusion f) ⟶
      homotopyFiber (basedMappingCylinderRetraction f) :=
  Under.homMk
    (TopCat.ofHom (mappingCylinderRetractionFiberComparisonContinuousMap f))
    (mappingCylinderRetractionFiberComparison_w f)

/-- Evaluating the based comparison morphism `F_j ⟶ F_r` recovers the source-facing comparison on
homotopy fibers. -/
@[simp] theorem mappingCylinderRetractionFiberComparison_hom_apply {X Y : BasedSpace}
    (f : X ⟶ Y) (z : HomotopyFiber (basedMappingCylinderTopInclusion f)) :
    (mappingCylinderRetractionFiberComparison f).right.hom z =
      mappingCylinderRetractionFiberComparisonFun f z := rfl

/-- The comparison function `F_j → F_f` induced by `id × P r`, where
`j : X ⟶ M_f` is the top inclusion and `r : M_f ⟶ Y` is the mapping-cylinder retraction. -/
def mappingCylinderRetractionComparisonFun {X Y : BasedSpace} (f : X ⟶ Y) :
    HomotopyFiber (basedMappingCylinderTopInclusion f) → HomotopyFiber f :=
  fun z ↦
    HomotopyFiber.mk z.point (mappingCylinderRetractionComparisonPath f z)
      (mappingCylinderRetractionComparisonPath_endpoint f z).symm

/-- The comparison function `F_j → F_f` induced by `id × P r` is continuous. -/
theorem mappingCylinderRetractionComparisonContinuous {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous (mappingCylinderRetractionComparisonFun f) := sorry

/-- The comparison map `F_j → F_f` as a continuous map. -/
def mappingCylinderRetractionComparisonContinuousMap {X Y : BasedSpace} (f : X ⟶ Y) :
    C(HomotopyFiber (basedMappingCylinderTopInclusion f), HomotopyFiber f) :=
  { toFun := mappingCylinderRetractionComparisonFun f
    continuous_toFun := mappingCylinderRetractionComparisonContinuous f }

/-- The comparison map `F_j → F_f` preserves the chosen basepoints. -/
theorem mappingCylinderRetractionComparison_w {X Y : BasedSpace} (f : X ⟶ Y) :
    (homotopyFiber (basedMappingCylinderTopInclusion f)).hom ≫
        TopCat.ofHom (mappingCylinderRetractionComparisonContinuousMap f) =
      (homotopyFiber f).hom := sorry

/-- The based comparison morphism `F_j ⟶ F_f` induced by `id × P r`. -/
def mappingCylinderRetractionComparison {X Y : BasedSpace} (f : X ⟶ Y) :
    homotopyFiber (basedMappingCylinderTopInclusion f) ⟶ homotopyFiber f :=
  Under.homMk
    (TopCat.ofHom (mappingCylinderRetractionComparisonContinuousMap f))
    (mappingCylinderRetractionComparison_w f)

/-- Evaluating the based comparison morphism `F_j ⟶ F_f` recovers the comparison induced by
`id × P r`. -/
@[simp] theorem mappingCylinderRetractionComparison_hom_apply {X Y : BasedSpace}
    (f : X ⟶ Y) (z : HomotopyFiber (basedMappingCylinderTopInclusion f)) :
    (mappingCylinderRetractionComparison f).right.hom z =
      mappingCylinderRetractionComparisonFun f z := rfl

/-- The loop in `C_f` obtained by applying the quotient map `M_f ⟶ C_f` to the path coordinate of
a point of `F_j`. Since the endpoint of that path lies in the collapsed top copy of `X`, the
image path is a loop at the basepoint of `C_f`. -/
theorem mappingCylinderQuotientComparison_target {X Y : BasedSpace} (f : X ⟶ Y)
    (z : HomotopyFiber (basedMappingCylinderTopInclusion f)) :
    underTopBasepoint (homotopyCofiber f) =
      (basedMappingCylinderToHomotopyCofiber f).right.hom z.path.endpoint := sorry

/-- The loop in `C_f` obtained by applying the quotient map `M_f ⟶ C_f` to the path coordinate of
a point of `F_j`. Since the endpoint of that path lies in the collapsed top copy of `X`, the
image path is a loop at the basepoint of `C_f`. -/
def mappingCylinderQuotientComparisonPath {X Y : BasedSpace} (f : X ⟶ Y)
    (z : HomotopyFiber (basedMappingCylinderTopInclusion f)) :
    Path (underTopBasepoint (homotopyCofiber f)) (underTopBasepoint (homotopyCofiber f)) :=
  let χ : Path (underTopBasepoint (homotopyCofiber f))
      (underTopBasepoint (homotopyCofiber f)) :=
    ((PathSpace.toPath z.path).map
      (basedMappingCylinderToHomotopyCofiber f).right.hom.continuous).cast
      (fundamentalGroupFunctorMap_basepoint (basedMappingCylinderToHomotopyCofiber f)).symm
      (mappingCylinderQuotientComparison_target f z)
  χ

/-- The quotient-induced loop comparison `F_j → ΩC_f` is continuous. -/
theorem mappingCylinderQuotientComparisonContinuous {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous (mappingCylinderQuotientComparisonPath f) := sorry

/-- The quotient-induced comparison map `F_j → ΩC_f` as a continuous map. -/
def mappingCylinderQuotientComparisonContinuousMap {X Y : BasedSpace} (f : X ⟶ Y) :
    C(HomotopyFiber (basedMappingCylinderTopInclusion f),
      Path (underTopBasepoint (homotopyCofiber f)) (underTopBasepoint (homotopyCofiber f))) :=
  { toFun := fun z ↦ mappingCylinderQuotientComparisonPath f z
    continuous_toFun := mappingCylinderQuotientComparisonContinuous f }

/-- The quotient-induced comparison map `F_j → ΩC_f` preserves the chosen basepoints. -/
theorem mappingCylinderQuotientComparison_w {X Y : BasedSpace} (f : X ⟶ Y) :
    (homotopyFiber (basedMappingCylinderTopInclusion f)).hom ≫
        TopCat.ofHom (mappingCylinderQuotientComparisonContinuousMap f) =
      (Ωᵇ (homotopyCofiber f)).hom := sorry

/-- The based comparison morphism `F_j ⟶ ΩC_f` induced by the quotient map
`M_f ⟶ C_f`. -/
def mappingCylinderQuotientComparison {X Y : BasedSpace} (f : X ⟶ Y) :
    homotopyFiber (basedMappingCylinderTopInclusion f) ⟶ Ωᵇ (homotopyCofiber f) :=
  Under.homMk
    (TopCat.ofHom (mappingCylinderQuotientComparisonContinuousMap f))
    (mappingCylinderQuotientComparison_w f)

/-- Evaluating the quotient-induced based comparison morphism `F_j ⟶ ΩC_f` recovers the loop
obtained by applying the quotient map to the path coordinate. -/
@[simp] theorem mappingCylinderQuotientComparison_hom_apply {X Y : BasedSpace}
    (f : X ⟶ Y) (z : HomotopyFiber (basedMappingCylinderTopInclusion f)) :
    (mappingCylinderQuotientComparison f).right.hom z =
      mappingCylinderQuotientComparisonPath f z := rfl

/-- Lemma 8.7.4. The quotient-induced map `F_j ⟶ ΩC_f` is homotopic under the basepoint to the
comparison obtained by first sending `F_j` to `F_f` via `id × P r` and then applying
`η : F_f ⟶ ΩC_f`. -/
theorem mappingCylinderRetractionComparison_comp_homotopyFiberToLoopHomotopyCofiber_homotopic
    {X Y : BasedSpace} (f : X ⟶ Y) :
    HomotopicUnder
      (mappingCylinderRetractionComparison f ≫ homotopyFiberToLoopHomotopyCofiber f)
      (mappingCylinderQuotientComparison f) := sorry
