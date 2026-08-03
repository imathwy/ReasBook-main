module

public import Topology_Munkres_2000.Book.Definition_53_5.FigureEight
public import Topology_Munkres_2000.Book.Example_53_4.Covering
import all Topology_Munkres_2000.Book.Example_53_4.Covering

public section

namespace CoordinateAxes

/-- The union of the coordinate axes in `ℝ × ℝ`. -/
def carrier : Set (ℝ × ℝ) :=
  {x | x.2 = 0 ∨ x.1 = 0}

end CoordinateAxes

/-- The coordinate-axis subspace of `ℝ × ℝ`. -/
abbrev CoordinateAxes := CoordinateAxes.carrier

namespace CoordinateAxes

/-- A point lies in the coordinate axes exactly when one coordinate is zero. -/
theorem mem_iff (x : ℝ × ℝ) :
    x ∈ carrier ↔ x.2 = 0 ∨ x.1 = 0 := Iff.rfl

/-- Helper for Exercise 60.3: `Torus.cover` acts coordinatewise by `Circle.turnExp`. -/
private theorem torusCover_apply (x : ℝ × ℝ) :
    Torus.cover x = (Circle.turnExp x.1, Circle.turnExp x.2) := by
  -- Expose the coordinate formula once, keeping later geometric arguments at this interface.
  rfl

/-- The coordinatewise circle parametrization sends the coordinate axes into the figure eight. -/
theorem mapsToFigureEight :
    Set.MapsTo Torus.cover carrier FigureEight.carrier := by
  -- On either source axis, the corresponding circle coordinate is the basepoint.
  intro x hx
  rcases (mem_iff x).mp hx with hxSecond | hxFirst
  · rw [FigureEight.mem_iff, torusCover_apply]
    exact Or.inl (congrArg Circle.turnExp hxSecond |>.trans Circle.turnExp_zero)
  · rw [FigureEight.mem_iff, torusCover_apply]
    exact Or.inr (congrArg Circle.turnExp hxFirst |>.trans Circle.turnExp_zero)

/-- The restriction of the coordinatewise circle parametrization to the coordinate axes. -/
noncomputable def toFigureEight : CoordinateAxes → FigureEight :=
  Set.MapsTo.restrict Torus.cover carrier FigureEight.carrier mapsToFigureEight

/-- The restricted map is given by the coordinatewise one-turn circle parametrization. -/
theorem toFigureEight_apply (x : CoordinateAxes) :
    (toFigureEight x : Torus) = Torus.cover x := by
  -- Restricting the codomain changes only the membership proof, not the underlying value.
  exact Set.MapsTo.val_restrict_apply mapsToFigureEight x

/-- Helper for Exercise 60.3: the punctured horizontal axis omits points with first
coordinate zero. -/
private def puncturedHorizontal : Set CoordinateAxes :=
  {x | (x : ℝ × ℝ).1 ≠ 0}

/-- Helper for Exercise 60.3: the punctured horizontal axis is open in the axes subspace. -/
private theorem isOpen_puncturedHorizontal : IsOpen puncturedHorizontal := by
  -- It is the inverse image of the complement of zero under the first-coordinate map.
  exact isOpen_ne.preimage (continuous_fst.comp continuous_subtype_val)

/-- Helper for Exercise 60.3: the second coordinate circle lies in `FigureEight`. -/
private theorem verticalCircle_mem (z : Circle) :
    ((1 : Circle), z) ∈ FigureEight.carrier := by
  -- Its first coordinate is the figure-eight basepoint.
  exact (FigureEight.mem_iff _).mpr (Or.inr rfl)

/-- Helper for Exercise 60.3: inclusion of the second coordinate circle into `FigureEight`. -/
noncomputable def verticalCircle (z : Circle) : FigureEight :=
  ⟨(1, z), verticalCircle_mem z⟩

/-- Helper for Exercise 60.3: coercing the vertical-circle inclusion recovers its coordinate
pair. -/
private theorem coe_verticalCircle (z : Circle) :
    (verticalCircle z : Torus) = (1, z) := by
  -- The membership proof does not alter the underlying pair.
  rfl

/-- Helper for Exercise 60.3: the second coordinate-circle inclusion is continuous. -/
private theorem continuous_verticalCircle : Continuous verticalCircle := by
  -- The inclusion is a constant first coordinate paired with the identity map.
  exact (continuous_const.prodMk continuous_id).subtype_mk _

/-- Helper for Exercise 60.3: `(1, 0)` belongs to the union of the coordinate axes. -/
private theorem unitHorizontal_mem : ((1, 0) : ℝ × ℝ) ∈ carrier := by
  -- The second coordinate vanishes.
  exact (mem_iff _).mpr (Or.inl rfl)

/-- Helper for Exercise 60.3: the distinguished nonzero point on the horizontal axis. -/
private def unitHorizontal : CoordinateAxes :=
  ⟨(1, 0), unitHorizontal_mem⟩

/-- Helper for Exercise 60.3: coercing the distinguished horizontal point gives `(1, 0)`. -/
private theorem coe_unitHorizontal :
    (unitHorizontal : ℝ × ℝ) = (1, 0) := by
  -- The subtype stores precisely this coordinate pair.
  rfl

/-- Helper for Exercise 60.3: the vertical-circle pullback of the image of the punctured
horizontal axis is only the figure-eight basepoint. -/
private theorem verticalCircle_preimage_image_puncturedHorizontal :
    verticalCircle ⁻¹' (toFigureEight '' puncturedHorizontal) = {(1 : Circle)} := by
  -- Compare the two sets pointwise and use the axis equation to control the source witness.
  ext z
  constructor
  · intro hz
    rcases hz with ⟨x, hxPunctured, hxImage⟩
    have hxSecond : (x : ℝ × ℝ).2 = 0 := by
      rcases (mem_iff x).mp x.property with hxSecond | hxFirst
      · exact hxSecond
      · exact False.elim (hxPunctured hxFirst)
    have hsecond :=
      congrArg (fun w : FigureEight ↦ (w : Torus).2) hxImage
    have hzOne : z = 1 := by
      simpa only [toFigureEight_apply, torusCover_apply, hxSecond,
        Circle.turnExp_zero, coe_verticalCircle] using hsecond.symm
    exact Set.mem_singleton_iff.mpr hzOne
  · intro hz
    have hzOne : z = 1 := Set.mem_singleton_iff.mp hz
    subst z
    refine ⟨unitHorizontal, ?_, ?_⟩
    · -- The first coordinate of the chosen horizontal point is nonzero.
      norm_num [puncturedHorizontal, coe_unitHorizontal]
    · -- Both images have underlying torus coordinate `(1, 1)`.
      apply Subtype.ext
      rw [toFigureEight_apply, torusCover_apply, coe_unitHorizontal,
        Circle.turnExp_one, Circle.turnExp_zero, coe_verticalCircle]

/-- Exercise 60.3: the restriction of the map from Lemma 60.5 to the union of the
coordinate axes is not a covering map. -/
theorem not_isCoveringMap : ¬ IsCoveringMap toFigureEight := by
  -- A covering map would send the open punctured horizontal axis to an open subset.
  intro hcover
  have himageOpen : IsOpen (toFigureEight '' puncturedHorizontal) :=
    hcover.isOpenMap puncturedHorizontal isOpen_puncturedHorizontal
  -- Pulling that image back to the vertical circle would make its singleton basepoint open.
  have hpreimageOpen :
      IsOpen (verticalCircle ⁻¹' (toFigureEight '' puncturedHorizontal)) :=
    himageOpen.preimage continuous_verticalCircle
  rw [verticalCircle_preimage_image_puncturedHorizontal] at hpreimageOpen
  have hclopen : IsClopen ({(1 : Circle)} : Set Circle) :=
    ⟨isClosed_singleton, hpreimageOpen⟩
  have huniv : ({(1 : Circle)} : Set Circle) = Set.univ :=
    IsClopen.eq_univ hclopen (Set.singleton_nonempty 1)
  have hneg : (-1 : Circle) ∈ ({(1 : Circle)} : Set Circle) := by
    rw [huniv]
    exact Set.mem_univ (-1)
  have hne : (-1 : Circle) ≠ 1 := by
    intro h
    have hval := congrArg Subtype.val h
    norm_num at hval
  exact hne (Set.mem_singleton_iff.mp hneg)

end CoordinateAxes
