module

public import Topology_Munkres_2000.Book.Definition_22_2.Saturation
public import Topology_Munkres_2000.Book.Example_22_2
public import Mathlib.Topology.Maps.Basic

public section

namespace ReciprocalHyperbola

/-- The reciprocal hyperbola together with the origin in `ℝ × ℝ`. -/
def withOrigin : Set (ℝ × ℝ) :=
  set ∪ {((0, 0) : ℝ × ℝ)}

/-- The subspace of `ℝ × ℝ` formed by the reciprocal hyperbola and the origin. -/
abbrev WithOrigin := withOrigin

/-- The origin belongs to `withOrigin`. -/
theorem origin_mem : ((0, 0) : ℝ × ℝ) ∈ withOrigin := by
  simp [withOrigin]

/-- The origin regarded as a point of `WithOrigin`. -/
def origin : WithOrigin :=
  ⟨(0, 0), origin_mem⟩

/-- The restriction of the first-coordinate projection to `WithOrigin`. -/
abbrev restrictedFst : WithOrigin → ℝ :=
  withOrigin.restrict Prod.fst

/-- Evaluation of the restricted first-coordinate projection. -/
@[simp]
theorem restrictedFst_apply (point : WithOrigin) :
    restrictedFst point = point.1.1 := rfl

/-- The zero fiber of `restrictedFst` consists exactly of the origin. -/
theorem preimage_zero :
    restrictedFst ⁻¹' ({0} : Set ℝ) = ({origin} : Set WithOrigin) := by
  -- Split a point of `withOrigin` between the hyperbola and the adjoined origin.
  ext point
  constructor
  · intro hpoint
    have hzero : point.1.1 = 0 := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff, restrictedFst_apply] using hpoint
    have hwithOrigin := point.property
    rcases hwithOrigin with hhyperbola | horigin
    · exact (fst_ne_zero_of_mem hhyperbola hzero).elim
    · have hvalue : point.1 = (0, 0) := Set.mem_singleton_iff.mp horigin
      have hpointOrigin : point = origin := by
        apply Subtype.ext
        simpa only [origin] using hvalue
      exact Set.mem_singleton_iff.mpr hpointOrigin
  · intro hpoint
    have hpointOrigin : point = origin := Set.mem_singleton_iff.mp hpoint
    subst point
    simp only [Set.mem_preimage, Set.mem_singleton_iff, restrictedFst_apply, origin]

/-- Helper for Example 22.9: The restricted first-coordinate projection is continuous. -/
theorem restrictedFst_continuous :
    Continuous restrictedFst := by
  -- Restrict the continuous ambient first-coordinate projection to the subspace.
  exact continuous_fst.comp continuous_subtype_val

/-- Helper for Example 22.9: The restricted first-coordinate projection is surjective. -/
theorem restrictedFst_surjective :
    Function.Surjective restrictedFst := by
  intro x
  by_cases hx : x = 0
  · subst x
    -- The adjoined origin lies over zero.
    have horigin : restrictedFst origin = 0 := by
      rfl
    exact ⟨origin, horigin⟩
  · -- Every nonzero real is the first coordinate of its reciprocal pair.
    have hpointMem : (x, x⁻¹) ∈ withOrigin := by
      rw [withOrigin]
      exact Or.inl (reciprocalPair_mem hx)
    let point : WithOrigin := ⟨(x, x⁻¹), hpointMem⟩
    have hpoint : restrictedFst point = x := by
      rfl
    exact ⟨point, hpoint⟩

/-- Helper for Example 22.9: The origin singleton is open in `WithOrigin`. -/
theorem origin_isOpen :
    IsOpen ({origin} : Set WithOrigin) := by
  -- Inside `withOrigin`, the complement of the closed hyperbola is exactly the origin.
  have hpreimage :
      (Subtype.val : WithOrigin → ℝ × ℝ) ⁻¹' setᶜ =
        ({origin} : Set WithOrigin) := by
    ext point
    constructor
    · intro hpoint
      have hwithOrigin := point.property
      rcases hwithOrigin with hhyperbola | horigin
      · exact (hpoint hhyperbola).elim
      · have hvalue : point.1 = (0, 0) := Set.mem_singleton_iff.mp horigin
        have hpointOrigin : point = origin := by
          apply Subtype.ext
          simpa only [origin] using hvalue
        exact Set.mem_singleton_iff.mpr hpointOrigin
    · intro hpoint
      have hpointOrigin : point = origin := Set.mem_singleton_iff.mp hpoint
      subst point
      intro horiginHyperbola
      exact fst_ne_zero_of_mem horiginHyperbola rfl
  -- Pull back the open ambient complement along the subtype inclusion.
  rw [← hpreimage]
  exact isClosed.isOpen_compl.preimage continuous_subtype_val

/-- Helper for Example 22.9: The origin singleton is saturated with respect to `restrictedFst`. -/
theorem origin_isSaturated :
    Set.IsSaturated restrictedFst ({origin} : Set WithOrigin) := by
  -- The origin singleton is the complete preimage of the codomain singleton zero.
  rw [Set.isSaturated_iff_exists_preimage]
  exact ⟨{0}, preimage_zero.symm⟩

/-- Helper for Example 22.9: The image of the origin singleton under `restrictedFst` is `{0}`. -/
theorem origin_image :
    restrictedFst '' ({origin} : Set WithOrigin) = ({0} : Set ℝ) := by
  -- Images of singletons reduce the claim to evaluating the projection at the origin.
  simp only [Set.image_singleton, restrictedFst_apply, origin]

/-- Helper for Example 22.9: The image of the origin singleton is not open in `ℝ`. -/
theorem origin_image_not_isOpen :
    ¬ IsOpen (restrictedFst '' ({origin} : Set WithOrigin)) := by
  -- Normalize the image to the non-open singleton in the real line.
  rw [origin_image]
  exact not_isOpen_singleton 0

/-- Example 22.9: The restricted first-coordinate projection is not a quotient map. -/
theorem restrictedFst_not_isQuotientMap :
    ¬ Topology.IsQuotientMap restrictedFst := by
  intro hquotient
  -- A quotient map would reflect openness from the saturated origin fiber to its image.
  apply origin_image_not_isOpen
  apply hquotient.isCoinducing.isOpen_preimage.mp
  rw [Set.isSaturated_iff_preimage_image.mp origin_isSaturated]
  exact origin_isOpen


end ReciprocalHyperbola

end
