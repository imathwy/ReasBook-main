module

public import Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
import all Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
public import Topology_Munkres_2000.Book.Exercise_72_1.RadialDeformation
public import Topology_Munkres_2000.Book.Theorem_22_1
public import Topology_Munkres_2000.Book.Corollary_70_4
public import Topology_Munkres_2000.Book.Theorem_59_3
public import Topology_Munkres_2000.Book.Exercise_54_7.Product
public import Topology_Munkres_2000.Book.Theorem_58_3.HomotopyEquiv
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Analysis.Convex.Contractible

public section

universe u

open scoped ContinuousMap

/-- Helper for Exercise 72.1: the center of the closed unit ball lies off its boundary. -/
lemma closedUnitBall_center_mem_boundary_compl (m : ℕ) :
    closedUnitBallCenter m ∈ (StandardSphere.boundary m)ᶜ := by
  -- Boundary membership would force the norm of the center to equal one.
  intro hcenter
  have hnorm := (StandardSphere.mem_boundary_iff_norm_eq m (closedUnitBallCenter m)).1 hcenter
  simp [closedUnitBallCenter] at hnorm

/-- Helper for Exercise 72.1: the image of the cell center lies outside the attached
subspace when the cell interior maps into its complement. -/
lemma higherCell_center_image_mem_compl {X : Type u} [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    h (closedUnitBallCenter m) ∈ Aᶜ := by
  -- Apply the maps-to part of the interior bijection to the center.
  exact h_interior.1 (closedUnitBall_center_mem_boundary_compl m)

/-- Helper for Exercise 72.1: the attached subspace avoids the image of the cell center. -/
lemma higherCell_subset_puncturedCenter {X : Type u} [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    A ⊆ ({h (closedUnitBallCenter m)} : Set X)ᶜ := by
  -- A point of `A` cannot equal the center image, which lies in `Aᶜ`.
  have hcenter := higherCell_center_image_mem_compl m A h h_interior
  intro x hxA hxcenter
  exact hcenter (hxcenter ▸ hxA)

/-- Helper for Exercise 72.1: every attaching-sphere image differs from the image of
 the cell center. -/
lemma higherCell_boundary_image_ne_center {X : Type u} [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ)
    (p : StandardSphere.boundary m) :
    h p ≠ h (closedUnitBallCenter m) := by
  -- The boundary image lies in `A`, while the center image lies in `Aᶜ`.
  exact higherCell_subset_puncturedCenter m A h h_interior (h_boundary p.property)

/-- Helper for Exercise 72.1: the canonical map from the closed cell onto its image is
a quotient map. -/
lemma higherCell_rangeFactorization_isQuotientMap {X : Type u} [TopologicalSpace X]
    [T2Space X] (m : ℕ) (h : C(ClosedUnitBall m, X)) :
    Topology.IsQuotientMap (Set.rangeFactorization h) := by
  -- Compactness of the closed ball and Hausdorffness of the image give the quotient map.
  exact Topology.IsQuotientMap.of_surjective_continuous
    Set.rangeFactorization_surjective h.continuous.rangeFactorization

/-- Helper for Exercise 72.1: the cell center is the unique point mapping to its image. -/
lemma higherCell_eq_center_of_image_eq_center {X : Type u} [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ)
    (x : ClosedUnitBall m)
    (hx : h x = h (closedUnitBallCenter m)) :
    x = closedUnitBallCenter m := by
  -- A boundary point cannot share the center image: their images lie on opposite sides of `A`.
  by_cases hx_boundary : x ∈ StandardSphere.boundary m
  · have hcenter_compl := higherCell_center_image_mem_compl m A h h_interior
    exfalso
    exact hcenter_compl (hx ▸ h_boundary hx_boundary)
  · -- Away from the boundary, injectivity of the interior restriction identifies the point.
    exact h_interior.2.1 hx_boundary (closedUnitBall_center_mem_boundary_compl m) hx

/-- Helper for Exercise 72.1: the punctured cell maps onto precisely the punctured
image of the cell. -/
lemma higherCell_range_puncturedRestriction {X : Type u} [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    Set.range
        (({closedUnitBallCenter m} : Set (ClosedUnitBall m))ᶜ.restrict
          (Set.rangeFactorization h)) =
      ({Set.rangeFactorization h (closedUnitBallCenter m)} : Set (Set.range h))ᶜ := by
  -- Surjectivity onto the complement follows by choosing the underlying cell preimage.
  ext y
  constructor
  · rintro ⟨x, rfl⟩ hxcenter
    exact x.property (higherCell_eq_center_of_image_eq_center m A h h_boundary h_interior
      x (congrArg Subtype.val hxcenter))
  · intro hy
    obtain ⟨x, hx_image⟩ := y.property
    have hx : x ∈ ({closedUnitBallCenter m} : Set (ClosedUnitBall m))ᶜ := by
      intro hxcenter
      apply hy
      apply Subtype.ext
      have hx_eq : x = closedUnitBallCenter m := by
        simpa using hxcenter
      calc
        (y : X) = h x := hx_image.symm
        _ = h (closedUnitBallCenter m) := congrArg h hx_eq
        _ = (Set.rangeFactorization h (closedUnitBallCenter m) : X) := rfl
    refine ⟨⟨x, hx⟩, ?_⟩
    exact Subtype.ext hx_image

/-- Helper for Exercise 72.1: deleting the cell center gives a saturated subset for
the canonical map onto the cell image. -/
lemma higherCell_punctured_isSaturated {X : Type u} [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    Set.IsSaturated (Set.rangeFactorization h)
      ({closedUnitBallCenter m} : Set (ClosedUnitBall m))ᶜ := by
  -- Fiberwise uniqueness of the center makes its complement a union of complete fibers.
  rw [Set.isSaturated_iff_mem_of_eq]
  intro x x' hx hxx' hx'_center
  apply hx
  have himage : h x = h (closedUnitBallCenter m) := by
    rw [← hx'_center]
    exact congrArg Subtype.val hxx'.symm
  exact higherCell_eq_center_of_image_eq_center m A h h_boundary h_interior x himage

/-- Helper for Exercise 72.1: restricting the cell-image quotient map away from the
center remains a strict map onto its punctured image. -/
lemma higherCell_puncturedRestriction_isStrictMap {X : Type u} [TopologicalSpace X]
    [T2Space X] (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    Topology.IsStrictMap
      (({closedUnitBallCenter m} : Set (ClosedUnitBall m))ᶜ.restrict
        (Set.rangeFactorization h)) := by
  -- Apply the restriction theorem to the open saturated complement of the center.
  exact Topology.IsQuotientMap.restrictImage_of_isOpen_or_isClosed
    (higherCell_rangeFactorization_isQuotientMap m h)
    (higherCell_punctured_isSaturated m A h h_boundary h_interior)
    (Or.inl (isClosed_singleton.isOpen_compl))

/-- Helper for Exercise 72.1: equal cell images come either from the same point or from two
boundary points. -/
lemma higherCell_puncturedFiber_boundary_or_eq {X : Type u} [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ)
    (x y : PuncturedClosedUnitBall m) (hxy : h x.1 = h y.1) :
    x = y ∨ (x.1 ∈ StandardSphere.boundary m ∧ y.1 ∈ StandardSphere.boundary m) := by
  -- If one point is interior, its image lies outside `A`, so the other point is interior too.
  by_cases hx_boundary : x.1 ∈ StandardSphere.boundary m
  · by_cases hy_boundary : y.1 ∈ StandardSphere.boundary m
    · exact Or.inr ⟨hx_boundary, hy_boundary⟩
    · exfalso
      exact h_interior.1 hy_boundary (hxy ▸ h_boundary hx_boundary)
  · by_cases hy_boundary : y.1 ∈ StandardSphere.boundary m
    · exfalso
      exact h_interior.1 hx_boundary (hxy.symm ▸ h_boundary hy_boundary)
    · left
      apply Subtype.ext
      exact h_interior.2.1 hx_boundary hy_boundary hxy

/-- Helper for Exercise 72.1: applying the attaching map to the radial homotopy gives a
continuous path-valued map on the punctured cell. -/
noncomputable def higherCell_radialImagePaths {X : Type u} [TopologicalSpace X]
    (m : ℕ) (h : C(ClosedUnitBall m, X)) : C(PuncturedClosedUnitBall m, C(unitInterval, X)) :=
  ContinuousMap.curry
    (h.comp ((⟨fun z : PuncturedClosedUnitBall m × unitInterval ↦
      (puncturedClosedUnitBall_radialMap m (z.2, z.1) : PuncturedClosedUnitBall m).1,
      continuous_subtype_val.comp ((puncturedClosedUnitBall_radialMap m).continuous.comp
        continuous_swap)⟩ : C(PuncturedClosedUnitBall m × unitInterval, ClosedUnitBall m))))

/-- Helper for Exercise 72.1: the path-valued radial image is constant on fibers of the
punctured range factorization. -/
lemma higherCell_radialImage_factorsThrough {X : Type u} [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ)
    (x y : PuncturedClosedUnitBall m)
    (hxy : (({closedUnitBallCenter m} : Set (ClosedUnitBall m))ᶜ.restrict
      (Set.rangeFactorization h)) x =
      (({closedUnitBallCenter m} : Set (ClosedUnitBall m))ᶜ.restrict
        (Set.rangeFactorization h)) y) :
    higherCell_radialImagePaths m h x = higherCell_radialImagePaths m h y := by
  -- Classify the fiber; equal points rewrite, while boundary points give constant paths.
  have hxy_image : h x.1 = h y.1 := congrArg Subtype.val hxy
  rcases higherCell_puncturedFiber_boundary_or_eq m A h h_boundary h_interior x y hxy_image with
    rfl | ⟨hx_boundary, hy_boundary⟩
  · rfl
  · apply ContinuousMap.ext
    intro t
    change h (puncturedClosedUnitBall_radialMap m (t, x)).1 =
      h (puncturedClosedUnitBall_radialMap m (t, y)).1
    rw [puncturedClosedUnitBall_radialMap_of_boundary m t x hx_boundary,
      puncturedClosedUnitBall_radialMap_of_boundary m t y hy_boundary]
    exact hxy_image

/-- Helper for Exercise 72.1: every point of a radial image path avoids the image of
 the removed cell center. -/
lemma higherCell_radialImage_ne_center {X : Type u} [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ)
    (x : PuncturedClosedUnitBall m) (t : unitInterval) :
    h (puncturedClosedUnitBall_radialMap m (t, x)).1 ≠
      h (closedUnitBallCenter m) := by
  -- Equality of images would force the radial point to be the deleted center.
  intro himage
  have hcenter := higherCell_eq_center_of_image_eq_center m A h h_boundary h_interior
    (puncturedClosedUnitBall_radialMap m (t, x)).1 himage
  -- The radial map remains in the punctured closed ball, contradicting that equality.
  exact (puncturedClosedUnitBall_radialMap m (t, x)).property hcenter

/-- Helper for Exercise 72.1: the radial image formula is continuous when restricted to
 the punctured ambient space. -/
lemma continuous_higherCell_radialImagePunctured {X : Type u} [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    Continuous (fun z : PuncturedClosedUnitBall m × unitInterval ↦
      (⟨h (puncturedClosedUnitBall_radialMap m (z.2, z.1)).1,
        higherCell_radialImage_ne_center m A h h_boundary h_interior z.1 z.2⟩ :
        ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ))) := by
  -- Continuity follows from the compiled radial map and the attaching map.
  exact Continuous.subtype_mk
    (h.continuous.comp (continuous_subtype_val.comp
      ((puncturedClosedUnitBall_radialMap m).continuous.comp continuous_swap))) _

/-- Helper for Exercise 72.1: the radial image paths regarded as paths in the ambient
 space punctured at the cell-center image. -/
noncomputable def higherCell_radialImagePathsPunctured {X : Type u} [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    C(PuncturedClosedUnitBall m,
      C(unitInterval, ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ))) :=
  ContinuousMap.curry
    ⟨fun z ↦ ⟨h (puncturedClosedUnitBall_radialMap m (z.2, z.1)).1,
      higherCell_radialImage_ne_center m A h h_boundary h_interior z.1 z.2⟩,
      continuous_higherCell_radialImagePunctured m A h h_boundary h_interior⟩

/-- Helper for Exercise 72.1: the attaching map to its image, restricted away from the
 cell center and bundled as a continuous map. -/
noncomputable def higherCell_puncturedRestriction {X : Type u} [TopologicalSpace X]
    (m : ℕ) (h : C(ClosedUnitBall m, X)) :
    C(PuncturedClosedUnitBall m, Set.range h) :=
  ⟨({closedUnitBallCenter m} : Set (ClosedUnitBall m))ᶜ.restrict
      (Set.rangeFactorization h),
    h.continuous.rangeFactorization.comp continuous_subtype_val⟩

/-- Helper for Exercise 72.1: the range factorization of the punctured cell-image map,
 bundled as a continuous map for the quotient-lift API. -/
noncomputable def higherCell_puncturedRangeFactorization {X : Type u} [TopologicalSpace X]
    (m : ℕ) (h : C(ClosedUnitBall m, X)) :
    C(PuncturedClosedUnitBall m, Set.range (higherCell_puncturedRestriction m h)) :=
  ⟨Set.rangeFactorization (higherCell_puncturedRestriction m h),
    (higherCell_puncturedRestriction m h).continuous.rangeFactorization⟩

/-- Helper for Exercise 72.1: the punctured radial path map is constant on fibers of
 the punctured cell-image map. -/
lemma higherCell_radialImagePunctured_factorsThrough {X : Type u} [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    Function.FactorsThrough
      (higherCell_radialImagePathsPunctured m A h h_boundary h_interior)
      (higherCell_puncturedRangeFactorization m h) := by
  -- Forgetting both range subtypes reduces fiber equality to the established X-valued result.
  intro x y hxy
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  exact congrArg (fun path : C(unitInterval, X) ↦ path t)
    (higherCell_radialImage_factorsThrough m A h h_boundary h_interior x y
      (congrArg Subtype.val hxy))

/-- Helper for Exercise 72.1: strictness of the punctured cell-image map supplies the
 quotient map used for path descent. -/
lemma higherCell_puncturedRangeFactorization_isQuotientMap {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    Topology.IsQuotientMap (higherCell_puncturedRangeFactorization m h) := by
  -- Unfold the bundled wrappers to recover the established strict-map theorem.
  exact higherCell_puncturedRestriction_isStrictMap m A h h_boundary h_interior

/-- Helper for Exercise 72.1: descend the punctured radial paths to the nested range of
 the punctured cell-image map. -/
noncomputable def higherCell_puncturedRadialPathsRangeLift {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    C(Set.range (higherCell_puncturedRestriction m h),
      C(unitInterval, ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ))) :=
  Topology.IsQuotientMap.lift
    (f := higherCell_puncturedRangeFactorization m h)
    (higherCell_puncturedRangeFactorization_isQuotientMap
      m A h h_boundary h_interior)
    (higherCell_radialImagePathsPunctured m A h h_boundary h_interior)
    (higherCell_radialImagePunctured_factorsThrough m A h h_boundary h_interior)

/-- Helper for Exercise 72.1: the descended radial paths compute by the original radial
 formula on every punctured-cell representative. -/
lemma higherCell_puncturedRadialPathsRangeLift_apply {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ)
    (x : PuncturedClosedUnitBall m) :
    higherCell_puncturedRadialPathsRangeLift m A h h_boundary h_interior
        (higherCell_puncturedRangeFactorization m h x) =
      higherCell_radialImagePathsPunctured m A h h_boundary h_interior x := by
  -- Apply the quotient-lift computation theorem before exposing any nested subtype values.
  exact DFunLike.congr_fun
    (Topology.IsQuotientMap.lift_comp
      (f := higherCell_puncturedRangeFactorization m h)
      (higherCell_puncturedRangeFactorization_isQuotientMap
        m A h h_boundary h_interior)
      (higherCell_radialImagePathsPunctured m A h h_boundary h_interior)
      (higherCell_radialImagePunctured_factorsThrough m A h h_boundary h_interior)) x

/-- Helper for Exercise 72.1: a punctured cell representative mapping into the attached
 subspace must lie on the boundary sphere. -/
lemma higherCell_preimage_mem_boundary_of_image_mem {X : Type u} [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ)
    (x : PuncturedClosedUnitBall m) (hxA : h x.1 ∈ A) :
    x.1 ∈ StandardSphere.boundary m := by
  -- An interior representative would map to the complement of `A`.
  by_contra hx_boundary
  exact h_interior.1 hx_boundary hxA

/-- Helper for Exercise 72.1: the punctured cell image as a concrete subset of the
punctured ambient space. -/
abbrev HigherCellPuncturedImage {X : Type u} [TopologicalSpace X]
    (m : ℕ) (h : C(ClosedUnitBall m, X)) :
    Set ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ) :=
  Subtype.val ⁻¹' Set.range h

/-- Helper for Exercise 72.1: the image of a punctured-cell point avoids the removed
center image. -/
lemma higherCell_puncturedValue_ne_center {X : Type u} [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ)
    (x : PuncturedClosedUnitBall m) :
    h x.1 ≠ h (closedUnitBallCenter m) := by
  -- Equality with the center image would contradict membership in the punctured ball.
  intro hx
  exact x.property
    (higherCell_eq_center_of_image_eq_center m A h h_boundary h_interior x.1 hx)

/-- Helper for Exercise 72.1: a punctured-cell value belongs to the concrete punctured
cell image. -/
lemma higherCell_puncturedValue_mem_image {X : Type u} [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ)
    (x : PuncturedClosedUnitBall m) :
    (⟨h x.1, higherCell_puncturedValue_ne_center
      m A h h_boundary h_interior x⟩ :
      ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ)) ∈
        HigherCellPuncturedImage m h := by
  -- The original cell point witnesses membership in the range of the attaching map.
  exact ⟨x.1, rfl⟩

/-- Helper for Exercise 72.1: the punctured attaching map is continuous with codomain
the concrete punctured cell image. -/
lemma continuous_higherCell_puncturedImageRestriction {X : Type u}
    [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    Continuous (fun x : PuncturedClosedUnitBall m ↦
      (⟨⟨h x.1, higherCell_puncturedValue_ne_center
          m A h h_boundary h_interior x⟩,
        higherCell_puncturedValue_mem_image
          m A h h_boundary h_interior x⟩ : HigherCellPuncturedImage m h)) := by
  -- Both subtype layers inherit continuity from the attaching map.
  exact Continuous.subtype_mk
    (Continuous.subtype_mk (h.continuous.comp continuous_subtype_val) _) _

/-- Helper for Exercise 72.1: the punctured attaching map with codomain the concrete
punctured cell image. -/
noncomputable def higherCell_puncturedImageRestriction {X : Type u}
    [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    C(PuncturedClosedUnitBall m, HigherCellPuncturedImage m h) :=
  ⟨fun x ↦ ⟨⟨h x.1, higherCell_puncturedValue_ne_center
      m A h h_boundary h_interior x⟩,
    higherCell_puncturedValue_mem_image m A h h_boundary h_interior x⟩,
    continuous_higherCell_puncturedImageRestriction
      m A h h_boundary h_interior⟩

/-- Helper for Exercise 72.1: the concrete punctured-image restriction is surjective. -/
lemma higherCell_puncturedImageRestriction_surjective {X : Type u}
    [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    Function.Surjective
      (higherCell_puncturedImageRestriction m A h h_boundary h_interior) := by
  -- Choose a cell preimage and use avoidance of the center to make it punctured.
  intro y
  obtain ⟨x, hx⟩ := y.property
  have hx_punctured : x ∈ ({closedUnitBallCenter m} : Set (ClosedUnitBall m))ᶜ := by
    intro hx_center
    apply y.1.property
    rw [← hx]
    exact congrArg h hx_center
  refine ⟨⟨x, hx_punctured⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hx

/-- Helper for Exercise 72.1: the concrete punctured-image restriction is a quotient
map. -/
lemma higherCell_puncturedRestriction_isQuotientMap {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    Topology.IsQuotientMap
      (higherCell_puncturedImageRestriction m A h h_boundary h_interior) := by
  -- Forgetting the two concrete subtype layers is an embedding into the full cell image.
  let j : HigherCellPuncturedImage m h → Set.range h :=
    fun y ↦ ⟨y.1.1, y.property⟩
  have hj : Topology.IsEmbedding j :=
    (Topology.IsEmbedding.subtypeVal.comp
      Topology.IsEmbedding.subtypeVal).codRestrict _ _
  rw [Topology.isQuotientMap_iff_isStrictMap_surjective]
  constructor
  · -- Strictness is exactly the previously proved strictness after this embedding.
    rw [hj.isStrictMap_iff]
    have hj_comp :
        j ∘ higherCell_puncturedImageRestriction m A h h_boundary h_interior =
          ({closedUnitBallCenter m} : Set (ClosedUnitBall m))ᶜ.restrict
            (Set.rangeFactorization h) := by
      funext x
      apply Subtype.ext
      rfl
    rw [hj_comp]
    exact higherCell_puncturedRestriction_isStrictMap
      m A h h_boundary h_interior
  · exact higherCell_puncturedImageRestriction_surjective
      m A h h_boundary h_interior

/-- Helper for Exercise 72.1: the punctured radial paths are constant on fibers of the
concrete punctured-image restriction. -/
lemma higherCell_radialImagePunctured_factorsThroughImage {X : Type u}
    [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    Function.FactorsThrough
      (higherCell_radialImagePathsPunctured m A h h_boundary h_interior)
      (higherCell_puncturedImageRestriction m A h h_boundary h_interior) := by
  -- Equality in the concrete image implies equality under the old range-valued map.
  intro x y hxy
  have hxy_range :
      higherCell_puncturedRestriction m h x =
        higherCell_puncturedRestriction m h y := by
    apply Subtype.ext
    exact congrArg (fun z : HigherCellPuncturedImage m h ↦ (z.1.1 : X)) hxy
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  exact congrArg (fun path : C(unitInterval, X) ↦ path t)
    (higherCell_radialImage_factorsThrough
      m A h h_boundary h_interior x y hxy_range)

/-- Helper for Exercise 72.1: the radial paths descended directly to the concrete
punctured cell image. -/
noncomputable def higherCell_puncturedRadialPathsLift {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    C(HigherCellPuncturedImage m h,
      C(unitInterval, ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ))) :=
  Topology.IsQuotientMap.lift
    (higherCell_puncturedRestriction_isQuotientMap
      m A h h_boundary h_interior)
    (higherCell_radialImagePathsPunctured m A h h_boundary h_interior)
    (higherCell_radialImagePunctured_factorsThroughImage
      m A h h_boundary h_interior)

/-- Helper for Exercise 72.1: the concrete descended radial paths compute on every
punctured-cell representative. -/
lemma higherCell_puncturedRadialPathsLift_apply {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ)
    (x : PuncturedClosedUnitBall m) :
    higherCell_puncturedRadialPathsLift m A h h_boundary h_interior
        (higherCell_puncturedImageRestriction m A h h_boundary h_interior x) =
      higherCell_radialImagePathsPunctured m A h h_boundary h_interior x := by
  -- Use the quotient-lift computation rule at the chosen representative.
  exact DFunLike.congr_fun
    (Topology.IsQuotientMap.lift_comp
      (higherCell_puncturedRestriction_isQuotientMap
        m A h h_boundary h_interior)
      (higherCell_radialImagePathsPunctured m A h h_boundary h_interior)
      (higherCell_radialImagePunctured_factorsThroughImage
        m A h h_boundary h_interior)) x

/-- Helper for Exercise 72.1: the boundary sphere is closed in the closed unit ball. -/
lemma closedUnitBall_boundary_isClosed (m : ℕ) :
    IsClosed (StandardSphere.boundary m) := by
  -- The boundary is the inverse image of the closed singleton `{1}` under the norm.
  have hnorm : Continuous (fun x : ClosedUnitBall m ↦
      ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖) :=
    continuous_norm.comp continuous_subtype_val
  have hboundary : StandardSphere.boundary m =
      (fun x : ClosedUnitBall m ↦
        ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖) ⁻¹' {(1 : ℝ)} := by
    ext x
    exact StandardSphere.mem_boundary_iff_norm_eq m x
  rw [hboundary]
  exact isClosed_singleton.preimage hnorm

/-- Helper for Exercise 72.1: the open cell is saturated for the canonical quotient
onto the full cell image. -/
lemma higherCell_interior_isSaturated {X : Type u} [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    Set.IsSaturated (Set.rangeFactorization h)
      (StandardSphere.boundary m)ᶜ := by
  -- A fiber meeting the interior cannot also meet the boundary, since their images
  -- lie respectively in `Aᶜ` and `A`.
  rw [Set.isSaturated_iff_mem_of_eq]
  intro x y hx hxy hy_boundary
  have hxy_image : h x = h y := (congrArg Subtype.val hxy).symm
  apply h_interior.1 hx
  exact hxy_image.symm ▸ h_boundary hy_boundary

/-- Helper for Exercise 72.1: restricting the cell-image quotient to the open cell is
a strict map. -/
lemma higherCell_interiorRestriction_isStrictMap {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    Topology.IsStrictMap
      ((StandardSphere.boundary m)ᶜ.restrict (Set.rangeFactorization h)) := by
  -- Restrict the quotient map to the open saturated interior.
  exact Topology.IsQuotientMap.restrictImage_of_isOpen_or_isClosed
    (higherCell_rangeFactorization_isQuotientMap m h)
    (higherCell_interior_isSaturated m A h h_boundary h_interior)
    (Or.inl (closedUnitBall_boundary_isClosed m).isOpen_compl)

/-- Helper for Exercise 72.1: every point of `Aᶜ` lies in the range of the attaching
map. -/
lemma higherCell_complValue_mem_range {X : Type u} [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ)
    (y : ↥(Aᶜ)) : (y : X) ∈ Set.range h := by
  -- Surjectivity of the interior restriction supplies a cell preimage.
  obtain ⟨x, _, hx⟩ := h_interior.2.2 y.property
  exact ⟨x, hx⟩

/-- Helper for Exercise 72.1: the attaching map restricted from the open cell to `Aᶜ`
is continuous. -/
lemma continuous_higherCell_interiorRestriction {X : Type u}
    [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    Continuous (fun x : ↥((StandardSphere.boundary m)ᶜ) ↦
      (⟨h x.1, h_interior.1 x.property⟩ : ↥(Aᶜ))) := by
  -- The restriction inherits continuity from `h` through its two subtype maps.
  exact Continuous.subtype_mk (h.continuous.comp continuous_subtype_val) _

/-- Helper for Exercise 72.1: the attaching map from the open cell to `Aᶜ`. -/
noncomputable def higherCell_interiorRestriction {X : Type u}
    [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    C(↥((StandardSphere.boundary m)ᶜ), ↥(Aᶜ)) :=
  ⟨fun x ↦ ⟨h x.1, h_interior.1 x.property⟩,
    continuous_higherCell_interiorRestriction m A h h_interior⟩

/-- Helper for Exercise 72.1: the open-cell restriction is bijective. -/
lemma higherCell_interiorRestriction_bijective {X : Type u}
    [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    Function.Bijective (higherCell_interiorRestriction m A h h_interior) := by
  -- Injectivity and surjectivity are exactly the two pointwise clauses of `BijOn`.
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact h_interior.2.1 x.property y.property (congrArg Subtype.val hxy)
  · intro y
    obtain ⟨x, hx, hxy⟩ := h_interior.2.2 y.property
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy

/-- Helper for Exercise 72.1: the open-cell restriction is a homeomorphism. -/
lemma higherCell_interiorRestriction_isHomeomorph {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    IsHomeomorph (higherCell_interiorRestriction m A h h_interior) := by
  -- Embed `Aᶜ` into the full cell image and reuse strictness of the saturated restriction.
  let j : ↥(Aᶜ) → Set.range h :=
    fun y ↦ ⟨y.1, higherCell_complValue_mem_range m A h h_interior y⟩
  have hj : Topology.IsEmbedding j :=
    Topology.IsEmbedding.subtypeVal.codRestrict _ _
  rw [Topology.isHomeomorph_iff_isStrictMap_bijective]
  constructor
  · rw [hj.isStrictMap_iff]
    have hj_comp :
        j ∘ higherCell_interiorRestriction m A h h_interior =
          (StandardSphere.boundary m)ᶜ.restrict (Set.rangeFactorization h) := by
      funext x
      apply Subtype.ext
      rfl
    rw [hj_comp]
    exact higherCell_interiorRestriction_isStrictMap
      m A h h_boundary h_interior
  · exact higherCell_interiorRestriction_bijective m A h h_interior

/-- Helper for Exercise 72.1: the open cell is homeomorphic to the complement of the
attached subspace, compatibly with the attaching map. -/
theorem exists_higherCell_interiorHomeomorphCompl {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    ∃ e : ↥((StandardSphere.boundary m)ᶜ) ≃ₜ ↥(Aᶜ),
      ∀ x, ((e x : ↥(Aᶜ)) : X) = h x.1 := by
  -- Package the preceding homeomorphism predicate and expose its pointwise formula.
  refine ⟨(higherCell_interiorRestriction_isHomeomorph
    m A h h_boundary h_interior).homeomorph, ?_⟩
  intro x
  rfl

/-- Helper for Exercise 72.1: every descended radial path starts at its punctured-image
input. -/
lemma higherCell_puncturedRadialPathsLift_zero {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ)
    (y : HigherCellPuncturedImage m h) :
    higherCell_puncturedRadialPathsLift m A h h_boundary h_interior y 0 = y.1 := by
  -- Compute after choosing a punctured-cell representative of the image point.
  obtain ⟨x, hx⟩ := higherCell_puncturedImageRestriction_surjective
    m A h h_boundary h_interior y
  rw [← hx, higherCell_puncturedRadialPathsLift_apply]
  apply Subtype.ext
  change h (puncturedClosedUnitBall_radialMap m (0, x)).1 = h x.1
  rw [puncturedClosedUnitBall_radialMap_zero]

/-- Helper for Exercise 72.1: the endpoint of every descended radial path lies in the
attached subspace. -/
lemma higherCell_puncturedRadialPathsLift_one_mem {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ)
    (y : HigherCellPuncturedImage m h) :
    ((higherCell_puncturedRadialPathsLift
      m A h h_boundary h_interior y 1 :
      ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ)) : X) ∈ A := by
  -- Compute at a representative and use that radial normalization lands on the boundary.
  obtain ⟨x, hx⟩ := higherCell_puncturedImageRestriction_surjective
    m A h h_boundary h_interior y
  rw [← hx, higherCell_puncturedRadialPathsLift_apply]
  exact h_boundary (puncturedClosedUnitBall_radialMap_one_mem m x)

/-- Helper for Exercise 72.1: descended radial paths fix cell-image points that already
belong to the attached subspace. -/
lemma higherCell_puncturedRadialPathsLift_of_mem_attached {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ)
    (y : HigherCellPuncturedImage m h) (hy : (y.1.1 : X) ∈ A)
    (t : unitInterval) :
    higherCell_puncturedRadialPathsLift m A h h_boundary h_interior y t = y.1 := by
  -- Any representative of an overlap point lies on the boundary and is fixed radially.
  obtain ⟨x, hx⟩ := higherCell_puncturedImageRestriction_surjective
    m A h h_boundary h_interior y
  have hxA : h x.1 ∈ A := by
    have hx_value : h x.1 = (y.1.1 : X) :=
      congrArg (fun z : HigherCellPuncturedImage m h ↦ (z.1.1 : X)) hx
    rw [hx_value]
    exact hy
  have hx_boundary := higherCell_preimage_mem_boundary_of_image_mem
    m A h h_interior x hxA
  rw [← hx, higherCell_puncturedRadialPathsLift_apply]
  apply Subtype.ext
  change h (puncturedClosedUnitBall_radialMap m (t, x)).1 = h x.1
  rw [puncturedClosedUnitBall_radialMap_of_boundary m t x hx_boundary]

/-- Helper for Exercise 72.1: the copy of the attached subspace inside the punctured
ambient space. -/
abbrev HigherCellPuncturedAttached {X : Type u} [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X)) :
    Set ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ) :=
  Subtype.val ⁻¹' A

/-- Helper for Exercise 72.1: the two closed pieces covering the punctured ambient
space. -/
def higherCell_puncturedCover {X : Type u} [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X)) :
    Bool → Set ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ)
  | false => HigherCellPuncturedAttached m A h
  | true => HigherCellPuncturedImage m h

/-- Helper for Exercise 72.1: the constant path family on the attached part of the
punctured ambient space. -/
noncomputable def higherCell_puncturedAttachedConstantPaths {X : Type u}
    [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X)) :
    C(HigherCellPuncturedAttached m A h,
      C(unitInterval, ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ))) :=
  (ContinuousMap.const' :
    C(↥(({h (closedUnitBallCenter m)} : Set X)ᶜ),
      C(unitInterval, ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ)))).comp
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(HigherCellPuncturedAttached m A h,
            ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ)))

/-- Helper for Exercise 72.1: the local path family on each of the two punctured-space
cover pieces. -/
noncomputable def higherCell_puncturedLocalPaths {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    ∀ b : Bool, C(higherCell_puncturedCover m A h b,
      C(unitInterval, ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ)))
  | false => higherCell_puncturedAttachedConstantPaths m A h
  | true => higherCell_puncturedRadialPathsLift m A h h_boundary h_interior

/-- Helper for Exercise 72.1: the two local path families agree on overlaps. -/
lemma higherCell_puncturedLocalPaths_compatible {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    ∀ (i j : Bool) (x : ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ))
      (hxi : x ∈ higherCell_puncturedCover m A h i)
      (hxj : x ∈ higherCell_puncturedCover m A h j),
      higherCell_puncturedLocalPaths m A h h_boundary h_interior i ⟨x, hxi⟩ =
        higherCell_puncturedLocalPaths m A h h_boundary h_interior j ⟨x, hxj⟩ := by
  -- The only nontrivial overlap is `A` with the cell image, where radial paths are fixed.
  intro i j x hxi hxj
  cases i <;> cases j
  · rfl
  · apply ContinuousMap.ext
    intro t
    exact (higherCell_puncturedRadialPathsLift_of_mem_attached
      m A h h_boundary h_interior ⟨x, hxj⟩ hxi t).symm
  · apply ContinuousMap.ext
    intro t
    exact higherCell_puncturedRadialPathsLift_of_mem_attached
      m A h h_boundary h_interior ⟨x, hxi⟩ hxj t
  · rfl

/-- Helper for Exercise 72.1: the attached part and punctured cell image cover the
punctured ambient space. -/
lemma higherCell_puncturedCover_iUnion {X : Type u} [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    ⋃ b, higherCell_puncturedCover m A h b = Set.univ := by
  -- Points outside `A` have an interior cell preimage; all other points use the `A` piece.
  apply Set.iUnion_eq_univ_iff.2
  intro x
  by_cases hxA : (x.1 : X) ∈ A
  · exact ⟨false, hxA⟩
  · have hx_compl : (x.1 : X) ∈ Aᶜ := hxA
    obtain ⟨y, _, hy⟩ := h_interior.2.2 hx_compl
    exact ⟨true, ⟨y, hy⟩⟩

/-- Helper for Exercise 72.1: both pieces of the punctured-space cover are closed. -/
lemma higherCell_puncturedCover_isClosed {X : Type u} [TopologicalSpace X]
    [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (hA_closed : IsClosed A) :
    ∀ b, IsClosed (higherCell_puncturedCover m A h b) := by
  -- Closedness comes from `A` and from compactness of the full cell image.
  intro b
  cases b
  · exact hA_closed.preimage continuous_subtype_val
  · exact (isCompact_range h.continuous).isClosed.preimage continuous_subtype_val

/-- Helper for Exercise 72.1: paste the constant and radial path families over the
closed punctured-space cover. -/
noncomputable def higherCell_puncturedPastedPathsRaw {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ) →
      C(unitInterval, ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ)) :=
  Set.liftCover (higherCell_puncturedCover m A h)
    (fun b x ↦ higherCell_puncturedLocalPaths
      m A h h_boundary h_interior b x)
    (higherCell_puncturedLocalPaths_compatible m A h h_boundary h_interior)
    (higherCell_puncturedCover_iUnion m A h h_interior)

/-- Helper for Exercise 72.1: the pasted punctured-space path family is continuous. -/
lemma continuous_higherCell_puncturedPastedPathsRaw {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (hA_closed : IsClosed A)
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    Continuous (higherCell_puncturedPastedPathsRaw
      m A h h_boundary h_interior) := by
  -- Finite closed pasting reduces continuity to each already continuous local family.
  refine (locallyFinite_of_finite (higherCell_puncturedCover m A h)).continuous
    (higherCell_puncturedCover_iUnion m A h h_interior)
    (higherCell_puncturedCover_isClosed m A h hA_closed) ?_
  intro b
  rw [continuousOn_iff_continuous_restrict]
  have hrestrict :
      (higherCell_puncturedCover m A h b).restrict
          (higherCell_puncturedPastedPathsRaw m A h h_boundary h_interior) =
        higherCell_puncturedLocalPaths m A h h_boundary h_interior b := by
    funext z
    unfold higherCell_puncturedPastedPathsRaw
    exact Set.liftCover_coe z
  rw [hrestrict]
  exact map_continuous _

/-- Helper for Exercise 72.1: the continuous pasted path family on the punctured
ambient space. -/
noncomputable def higherCell_puncturedPastedPaths {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (hA_closed : IsClosed A)
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    C(↥(({h (closedUnitBallCenter m)} : Set X)ᶜ),
      C(unitInterval, ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ))) :=
  ⟨higherCell_puncturedPastedPathsRaw m A h h_boundary h_interior,
    continuous_higherCell_puncturedPastedPathsRaw
      m A h hA_closed h_boundary h_interior⟩

/-- Helper for Exercise 72.1: the pasted path family computes as either local family
on its corresponding cover piece. -/
lemma higherCell_puncturedPastedPaths_of_mem {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (hA_closed : IsClosed A)
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ)
    (b : Bool) (x : ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ))
    (hx : x ∈ higherCell_puncturedCover m A h b) :
    higherCell_puncturedPastedPaths m A h hA_closed h_boundary h_interior x =
      higherCell_puncturedLocalPaths m A h h_boundary h_interior b ⟨x, hx⟩ := by
  -- This is the computation rule for the closed-cover lift.
  change higherCell_puncturedPastedPathsRaw
    m A h h_boundary h_interior x = _
  unfold higherCell_puncturedPastedPathsRaw
  exact Set.liftCover_of_mem hx

/-- Helper for Exercise 72.1: every pasted path starts at its input. -/
lemma higherCell_puncturedPastedPaths_zero {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (hA_closed : IsClosed A)
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ)
    (x : ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ)) :
    higherCell_puncturedPastedPaths m A h hA_closed h_boundary h_interior x 0 = x := by
  -- Compute on whichever of the two cover pieces contains the input.
  by_cases hxA : (x.1 : X) ∈ A
  · rw [higherCell_puncturedPastedPaths_of_mem
      m A h hA_closed h_boundary h_interior false x hxA]
    rfl
  · have hx_compl : (x.1 : X) ∈ Aᶜ := hxA
    obtain ⟨y, _, hy⟩ := h_interior.2.2 hx_compl
    have hx_image : x ∈ higherCell_puncturedCover m A h true := ⟨y, hy⟩
    rw [higherCell_puncturedPastedPaths_of_mem
      m A h hA_closed h_boundary h_interior true x hx_image]
    exact higherCell_puncturedRadialPathsLift_zero
      m A h h_boundary h_interior ⟨x, hx_image⟩

/-- Helper for Exercise 72.1: every pasted path ends in the attached subspace. -/
lemma higherCell_puncturedPastedPaths_one_mem {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (hA_closed : IsClosed A)
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ)
    (x : ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ)) :
    ((higherCell_puncturedPastedPaths
      m A h hA_closed h_boundary h_interior x 1 :
      ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ)) : X) ∈ A := by
  -- On `A` the path is constant; on the cell image use the radial endpoint law.
  by_cases hxA : (x.1 : X) ∈ A
  · rw [higherCell_puncturedPastedPaths_of_mem
      m A h hA_closed h_boundary h_interior false x hxA]
    exact hxA
  · have hx_compl : (x.1 : X) ∈ Aᶜ := hxA
    obtain ⟨y, _, hy⟩ := h_interior.2.2 hx_compl
    have hx_image : x ∈ higherCell_puncturedCover m A h true := ⟨y, hy⟩
    rw [higherCell_puncturedPastedPaths_of_mem
      m A h hA_closed h_boundary h_interior true x hx_image]
    exact higherCell_puncturedRadialPathsLift_one_mem
      m A h h_boundary h_interior ⟨x, hx_image⟩

/-- Helper for Exercise 72.1: the pasted path family fixes the attached subspace. -/
lemma higherCell_puncturedPastedPaths_of_mem_attached {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (hA_closed : IsClosed A)
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ)
    (x : ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ))
    (hxA : (x.1 : X) ∈ A) (t : unitInterval) :
    higherCell_puncturedPastedPaths m A h hA_closed h_boundary h_interior x t = x := by
  -- The pasted map computes as the constant local path on the attached piece.
  rw [higherCell_puncturedPastedPaths_of_mem
    m A h hA_closed h_boundary h_interior false x hxA]
  rfl

/-- Helper for Exercise 72.1: inclusion of the attached subspace into the punctured
ambient space is continuous. -/
lemma continuous_higherCell_attachedInclusionPuncture {X : Type u}
    [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    Continuous (fun a : A ↦
      (⟨a.1, higherCell_subset_puncturedCenter m A h h_interior a.property⟩ :
        ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ))) := by
  -- The map is the subtype inclusion through one additional subtype layer.
  exact Continuous.subtype_mk continuous_subtype_val _

/-- Helper for Exercise 72.1: inclusion of the attached subspace into the punctured
ambient space. -/
noncomputable def higherCell_attachedInclusionPuncture {X : Type u}
    [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    C(A, ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ)) :=
  ⟨fun a ↦ ⟨a.1,
      higherCell_subset_puncturedCenter m A h h_interior a.property⟩,
    continuous_higherCell_attachedInclusionPuncture m A h h_interior⟩

/-- Helper for Exercise 72.1: the radial-pasting endpoint is a continuous map to the
attached subspace. -/
lemma continuous_higherCell_puncturedRetraction {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (hA_closed : IsClosed A)
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    Continuous (fun x : ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ) ↦
      (⟨((higherCell_puncturedPastedPaths
          m A h hA_closed h_boundary h_interior x 1 :
          ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ)) : X),
        higherCell_puncturedPastedPaths_one_mem
          m A h hA_closed h_boundary h_interior x⟩ : A)) := by
  -- Evaluate the continuous path family at one, forget the punctured subtype, and
  -- restrict the codomain using the endpoint-membership theorem.
  exact Continuous.subtype_mk
    (continuous_subtype_val.comp
      ((continuous_eval_const (1 : unitInterval)).comp
        (higherCell_puncturedPastedPaths
          m A h hA_closed h_boundary h_interior).continuous)) _

/-- Helper for Exercise 72.1: the endpoint retraction from the punctured ambient space
to the attached subspace. -/
noncomputable def higherCell_puncturedRetraction {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (hA_closed : IsClosed A)
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    C(↥(({h (closedUnitBallCenter m)} : Set X)ᶜ), A) :=
  ⟨fun x ↦ ⟨((higherCell_puncturedPastedPaths
        m A h hA_closed h_boundary h_interior x 1 :
        ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ)) : X),
      higherCell_puncturedPastedPaths_one_mem
        m A h hA_closed h_boundary h_interior x⟩,
    continuous_higherCell_puncturedRetraction
      m A h hA_closed h_boundary h_interior⟩

/-- Helper for Exercise 72.1: the pasted path family as an uncurried homotopy map. -/
noncomputable def higherCell_puncturedPastedHomotopyMap {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (hA_closed : IsClosed A)
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    C(unitInterval × ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ),
      ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ)) :=
  (higherCell_puncturedPastedPaths
    m A h hA_closed h_boundary h_interior).uncurry.comp ContinuousMap.prodSwap

/-- Helper for Exercise 72.1: the uncurried pasted homotopy starts at the identity. -/
lemma higherCell_puncturedPastedHomotopyMap_zero {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (hA_closed : IsClosed A)
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ)
    (x : ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ)) :
    higherCell_puncturedPastedHomotopyMap
      m A h hA_closed h_boundary h_interior (0, x) = x := by
  -- Uncurrying reduces this to the path-family start computation.
  exact higherCell_puncturedPastedPaths_zero
    m A h hA_closed h_boundary h_interior x

/-- Helper for Exercise 72.1: the uncurried pasted homotopy ends at inclusion after
the endpoint retraction. -/
lemma higherCell_puncturedPastedHomotopyMap_one {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (hA_closed : IsClosed A)
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ)
    (x : ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ)) :
    higherCell_puncturedPastedHomotopyMap
        m A h hA_closed h_boundary h_interior (1, x) =
      higherCell_attachedInclusionPuncture m A h h_interior
        (higherCell_puncturedRetraction
          m A h hA_closed h_boundary h_interior x) := by
  -- Both sides are the time-one value of the pasted path, with different subtype packaging.
  rfl

/-- Helper for Exercise 72.1: the pasted paths form a homotopy from the punctured-space
identity to inclusion after retraction. -/
noncomputable def higherCell_puncturedPastedHomotopy {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (hA_closed : IsClosed A)
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    ContinuousMap.Homotopy
      (ContinuousMap.id ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ))
      ((higherCell_attachedInclusionPuncture m A h h_interior).comp
        (higherCell_puncturedRetraction
          m A h hA_closed h_boundary h_interior)) :=
  { toContinuousMap := higherCell_puncturedPastedHomotopyMap
      m A h hA_closed h_boundary h_interior
    map_zero_left := higherCell_puncturedPastedHomotopyMap_zero
      m A h hA_closed h_boundary h_interior
    map_one_left := higherCell_puncturedPastedHomotopyMap_one
      m A h hA_closed h_boundary h_interior }

/-- Helper for Exercise 72.1: the endpoint retraction is a left inverse to inclusion. -/
lemma higherCell_puncturedRetraction_comp_inclusion {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (hA_closed : IsClosed A)
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    (higherCell_puncturedRetraction
        m A h hA_closed h_boundary h_interior).comp
      (higherCell_attachedInclusionPuncture m A h h_interior) =
        ContinuousMap.id A := by
  -- The pasted deformation is constant on every point of `A`.
  ext a
  change ((higherCell_puncturedPastedPaths
      m A h hA_closed h_boundary h_interior
      (higherCell_attachedInclusionPuncture m A h h_interior a) 1 :
      ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ)) : X) = (a : X)
  exact congrArg
    (fun z : ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ) ↦ (z : X))
    (higherCell_puncturedPastedPaths_of_mem_attached
      m A h hA_closed h_boundary h_interior
      (higherCell_attachedInclusionPuncture m A h h_interior a) a.property 1)

/-- Helper for Exercise 72.1: retraction after inclusion is homotopic to the identity. -/
lemma higherCell_puncturedRetraction_comp_inclusion_homotopic {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (hA_closed : IsClosed A)
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    ((higherCell_puncturedRetraction
        m A h hA_closed h_boundary h_interior).comp
      (higherCell_attachedInclusionPuncture m A h h_interior)).Homotopic
        (ContinuousMap.id A) := by
  -- Rewrite the composite to the identity and use the reflexive homotopy.
  rw [higherCell_puncturedRetraction_comp_inclusion
    m A h hA_closed h_boundary h_interior]

/-- Helper for Exercise 72.1: inclusion after retraction is homotopic to the punctured
space identity. -/
lemma higherCell_attachedInclusion_comp_retraction_homotopic {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (hA_closed : IsClosed A)
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    ((higherCell_attachedInclusionPuncture m A h h_interior).comp
      (higherCell_puncturedRetraction
        m A h hA_closed h_boundary h_interior)).Homotopic
      (ContinuousMap.id ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ)) := by
  -- Reverse the pasted homotopy from the identity to inclusion after retraction.
  exact ⟨(higherCell_puncturedPastedHomotopy
    m A h hA_closed h_boundary h_interior).symm⟩

/-- Helper for Exercise 72.1: inclusion identifies the attached subspace up to homotopy
with the punctured ambient space. -/
noncomputable def higherCell_attachedSubspaceHomotopyEquivPuncture {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (hA_closed : IsClosed A)
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    A ≃ₕ ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ) :=
  { toFun := higherCell_attachedInclusionPuncture m A h h_interior
    invFun := higherCell_puncturedRetraction
      m A h hA_closed h_boundary h_interior
    left_inv := higherCell_puncturedRetraction_comp_inclusion_homotopic
      m A h hA_closed h_boundary h_interior
    right_inv := higherCell_attachedInclusion_comp_retraction_homotopic
      m A h hA_closed h_boundary h_interior }

/-- Helper for Exercise 72.1: the forward map of the punctured-space homotopy
equivalence is the canonical inclusion. -/
lemma higherCell_attachedSubspaceHomotopyEquivPuncture_toFun {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (hA_closed : IsClosed A)
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    (higherCell_attachedSubspaceHomotopyEquivPuncture
      m A h hA_closed h_boundary h_interior).toFun =
        higherCell_attachedInclusionPuncture m A h h_interior := by
  -- This is the exposed forward field of the packaged equivalence.
  rfl

/-- Helper for Exercise 72.1: the forward map into the punctured ambient space is the
canonical inclusion associated to the center-avoidance subset relation. -/
lemma higherCell_attachedInclusionPuncture_eq_inclusion {X : Type u}
    [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    higherCell_attachedInclusionPuncture m A h h_interior =
      ContinuousMap.inclusion
        (higherCell_subset_puncturedCenter m A h h_interior) := by
  -- Both maps retain the same ambient point and use the same center-avoidance proof.
  ext a
  rfl

/-- Helper for Exercise 72.1: a subset inside a containing subspace is homeomorphic to
its direct ambient subtype. -/
def nestedSubsetHomeomorphForHigherCell {Y : Type*} [TopologicalSpace Y]
    (P S : Set Y) (hSP : S ⊆ P) :
    (Subtype.val ⁻¹' S : Set P) ≃ₜ S :=
  { toFun := fun x ↦ ⟨x.1.1, x.2⟩
    invFun := fun x ↦ ⟨⟨x.1, hSP x.2⟩, x.2⟩
    left_inv := fun x ↦ Subtype.ext (Subtype.coe_eta x.1 _)
    right_inv := fun x ↦ Subtype.coe_eta x _
    continuous_toFun :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk fun x ↦ x.2
    continuous_invFun :=
      (continuous_subtype_val.subtype_mk fun x ↦ hSP x.2).subtype_mk fun x ↦ x.2 }

/-- Helper for Exercise 72.1: interior points of the closed unit ball are exactly those
of norm strictly less than one. -/
lemma closedUnitBall_mem_boundary_compl_iff_norm_lt (m : ℕ) (x : ClosedUnitBall m) :
    x ∈ (StandardSphere.boundary m)ᶜ ↔
      ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ < 1 := by
  -- Combine the closed-ball upper bound with exclusion of the norm-one boundary.
  rw [Set.mem_compl_iff, StandardSphere.mem_boundary_iff_norm_eq]
  have hx_le : ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 := by
    have hx_dist := Metric.mem_closedBall.mp x.property
    rwa [dist_zero_right] at hx_dist
  exact ⟨fun hx_ne ↦ lt_of_le_of_ne hx_le hx_ne,
    fun hx_lt hx_eq ↦ hx_lt.ne hx_eq⟩

/-- Helper for Exercise 72.1: an interior closed-ball point belongs to the ambient open
unit ball. -/
lemma closedUnitBallInterior_mem_openBall (m : ℕ)
    (x : ↥((StandardSphere.boundary m)ᶜ)) :
    (x.1.1 : EuclideanSpace ℝ (Fin (m + 1))) ∈ Metric.ball 0 1 := by
  -- Convert the interior characterization into metric-ball membership.
  rw [Metric.mem_ball, dist_zero_right]
  exact (closedUnitBall_mem_boundary_compl_iff_norm_lt m x.1).1 x.property

/-- Helper for Exercise 72.1: an ambient open-unit-ball point belongs to the closed
unit ball. -/
lemma openUnitBall_mem_closedBall (m : ℕ)
    (x : Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    (x.1 : EuclideanSpace ℝ (Fin (m + 1))) ∈ Metric.closedBall 0 1 := by
  -- A strict metric-ball inequality implies the weak closed-ball inequality.
  rw [Metric.mem_closedBall, dist_zero_right]
  have hx_lt : ‖(x.1 : EuclideanSpace ℝ (Fin (m + 1)))‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using x.property
  exact hx_lt.le

/-- Helper for Exercise 72.1: an ambient open-unit-ball point lies off the closed-ball
boundary. -/
lemma openUnitBall_mem_boundary_compl (m : ℕ)
    (x : Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    (⟨x.1, openUnitBall_mem_closedBall m x⟩ : ClosedUnitBall m) ∈
      (StandardSphere.boundary m)ᶜ := by
  -- Convert metric-ball membership back to the norm characterization of the interior.
  apply (closedUnitBall_mem_boundary_compl_iff_norm_lt m _).2
  simpa only [Metric.mem_ball, dist_zero_right] using x.property

/-- Helper for Exercise 72.1: the interior of the closed unit ball is homeomorphic to
the ambient open unit ball. -/
noncomputable def closedUnitBallInteriorHomeomorphOpenBall (m : ℕ) :
    ↥((StandardSphere.boundary m)ᶜ) ≃ₜ
      Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
  { toFun := fun x ↦ ⟨x.1.1, closedUnitBallInterior_mem_openBall m x⟩
    invFun := fun x ↦ ⟨⟨x.1, openUnitBall_mem_closedBall m x⟩,
      openUnitBall_mem_boundary_compl m x⟩
    left_inv := fun _x ↦ Subtype.ext (Subtype.ext rfl)
    right_inv := fun _x ↦ Subtype.ext rfl
    continuous_toFun :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    continuous_invFun :=
      (continuous_subtype_val.subtype_mk _).subtype_mk _ }

/-- Helper for Exercise 72.1: the open cell is contractible. -/
lemma closedUnitBall_interior_contractibleSpace (m : ℕ) :
    ContractibleSpace ↥((StandardSphere.boundary m)ᶜ) := by
  -- Transfer contractibility of the convex ambient open ball across the identity homeomorphism.
  letI : ContractibleSpace
      (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :=
    Metric.contractibleSpace_ball one_pos
  exact (closedUnitBallInteriorHomeomorphOpenBall m).contractibleSpace

/-- Helper for Exercise 72.1: the complement of the attached subspace is simply
connected because it is homeomorphic to the open cell. -/
lemma higherCell_compl_simplyConnectedSpace {X : Type u} [TopologicalSpace X]
    [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    SimplyConnectedSpace ↥(Aᶜ) := by
  -- The source open cell is contractible, hence simply connected, and homeomorphism
  -- transports this property to `Aᶜ`.
  letI : ContractibleSpace ↥((StandardSphere.boundary m)ᶜ) :=
    closedUnitBall_interior_contractibleSpace m
  letI : SimplyConnectedSpace ↥((StandardSphere.boundary m)ᶜ) := inferInstance
  exact (higherCell_interiorRestriction_isHomeomorph
    m A h h_boundary h_interior).homeomorph.symm.toHomotopyEquiv.simplyConnectedSpace

/-- Helper for Exercise 72.1: the cell center regarded as an interior point. -/
def closedUnitBallCenterInterior (m : ℕ) :
    ↥((StandardSphere.boundary m)ᶜ) :=
  ⟨closedUnitBallCenter m, closedUnitBall_center_mem_boundary_compl m⟩

/-- Helper for Exercise 72.1: the punctured open cell in its closed-ball coordinates. -/
abbrev PuncturedOpenCell (m : ℕ) :=
  ({closedUnitBallCenterInterior m}ᶜ : Set ↥((StandardSphere.boundary m)ᶜ))

/-- Helper for Exercise 72.1: the punctured ambient open unit ball in polar-friendly
coordinates. -/
abbrev PuncturedOpenUnitBall (m : ℕ) :=
  {x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (m + 1)))) //
    ‖(x.1 : EuclideanSpace ℝ (Fin (m + 1)))‖ < 1}

/-- Helper for Exercise 72.1: a punctured open-cell point has nonzero ambient value. -/
lemma puncturedOpenCell_ne_zero (m : ℕ) (x : PuncturedOpenCell m) :
    (x.1.1.1 : EuclideanSpace ℝ (Fin (m + 1))) ≠ 0 := by
  -- Zero ambient value would identify the closed-ball point with its center.
  intro hx
  apply x.property
  apply Subtype.ext
  apply Subtype.ext
  exact hx

/-- Helper for Exercise 72.1: a punctured open-cell point has norm below one. -/
lemma puncturedOpenCell_norm_lt (m : ℕ) (x : PuncturedOpenCell m) :
    ‖(x.1.1.1 : EuclideanSpace ℝ (Fin (m + 1)))‖ < 1 := by
  -- This is precisely the boundary-complement membership of the underlying point.
  exact (closedUnitBall_mem_boundary_compl_iff_norm_lt m x.1.1).1 x.1.property

/-- Helper for Exercise 72.1: a polar punctured-open-ball point belongs to the closed
unit ball. -/
lemma puncturedOpenUnitBall_mem_closedBall (m : ℕ) (x : PuncturedOpenUnitBall m) :
    (x.1.1 : EuclideanSpace ℝ (Fin (m + 1))) ∈ Metric.closedBall 0 1 := by
  -- Its strict norm bound implies the closed-ball bound.
  rw [Metric.mem_closedBall, dist_zero_right]
  exact x.property.le

/-- Helper for Exercise 72.1: a polar punctured-open-ball point lies off the boundary. -/
lemma puncturedOpenUnitBall_mem_boundary_compl (m : ℕ) (x : PuncturedOpenUnitBall m) :
    (⟨x.1.1, puncturedOpenUnitBall_mem_closedBall m x⟩ : ClosedUnitBall m) ∈
      (StandardSphere.boundary m)ᶜ := by
  -- Apply the norm characterization of the open cell.
  exact (closedUnitBall_mem_boundary_compl_iff_norm_lt m _).2 x.property

/-- Helper for Exercise 72.1: a polar punctured-open-ball point differs from the cell
center. -/
lemma puncturedOpenUnitBall_ne_center (m : ℕ) (x : PuncturedOpenUnitBall m) :
    (⟨⟨x.1.1, puncturedOpenUnitBall_mem_closedBall m x⟩,
      puncturedOpenUnitBall_mem_boundary_compl m x⟩ :
      ↥((StandardSphere.boundary m)ᶜ)) ≠ closedUnitBallCenterInterior m := by
  -- Equality with the center would force the nonzero ambient point to vanish.
  intro hx
  have hx_zero : (x.1.1 : EuclideanSpace ℝ (Fin (m + 1))) = 0 := by
    have hx_value := congrArg
      (fun y : ↥((StandardSphere.boundary m)ᶜ) ↦
        (y.1.1 : EuclideanSpace ℝ (Fin (m + 1)))) hx
    simpa [closedUnitBallCenterInterior, closedUnitBallCenter] using hx_value
  have hx_ne : (x.1.1 : EuclideanSpace ℝ (Fin (m + 1))) ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.1.property
  exact hx_ne hx_zero

/-- Helper for Exercise 72.1: punctured open-cell coordinates agree with the standard
punctured ambient open ball. -/
noncomputable def puncturedOpenCellHomeomorphUnitBall (m : ℕ) :
    PuncturedOpenCell m ≃ₜ PuncturedOpenUnitBall m :=
  { toFun := fun x ↦ ⟨⟨x.1.1.1, puncturedOpenCell_ne_zero m x⟩,
      puncturedOpenCell_norm_lt m x⟩
    invFun := fun x ↦ ⟨⟨⟨x.1.1, puncturedOpenUnitBall_mem_closedBall m x⟩,
      puncturedOpenUnitBall_mem_boundary_compl m x⟩,
      puncturedOpenUnitBall_ne_center m x⟩
    left_inv := fun _x ↦ Subtype.ext (Subtype.ext (Subtype.ext rfl))
    right_inv := fun _x ↦ Subtype.ext (Subtype.ext rfl)
    continuous_toFun :=
      ((continuous_subtype_val.comp continuous_subtype_val).comp
        continuous_subtype_val).subtype_mk _ |>.subtype_mk _
    continuous_invFun :=
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
        |>.subtype_mk _ }

/-- Helper for Exercise 72.1: polar radius below one is exactly the open-cell radial
condition. -/
lemma puncturedOpenUnitBall_polarRadius_lt_one_iff (m : ℕ)
    (x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (m + 1))))) :
    ‖(x.1 : EuclideanSpace ℝ (Fin (m + 1)))‖ < 1 ↔
      ((homeomorphUnitSphereProd
        (EuclideanSpace ℝ (Fin (m + 1))) x).2.1 : ℝ) < 1 := by
  -- The second polar coordinate is the norm.
  rw [homeomorphUnitSphereProd_apply_snd_coe]

/-- Helper for Exercise 72.1: a restricted positive polar radius belongs to `(0, 1)`. -/
lemma polarRadiusLtOne_to_mem (m : ℕ)
    (z : {z : StandardSphere m × Set.Ioi (0 : ℝ) // z.2.1 < 1}) :
    z.1.2.1 ∈ Set.Ioo (0 : ℝ) 1 := by
  -- Positivity comes from `Ioi`; the upper bound is the restriction predicate.
  exact ⟨z.1.2.2, z.2⟩

/-- Helper for Exercise 72.1: a radius in `(0, 1)` belongs to the positive-radius
coordinate space. -/
lemma polarRadiusLtOne_inv_positive (m : ℕ)
    (z : StandardSphere m × Set.Ioo (0 : ℝ) 1) :
    z.2.1 ∈ Set.Ioi (0 : ℝ) := by
  -- Use the lower endpoint inequality of `Ioo`.
  exact z.2.2.1

/-- Helper for Exercise 72.1: the inverse polar radius satisfies the upper-bound
restriction. -/
lemma polarRadiusLtOne_inv_mem (m : ℕ)
    (z : StandardSphere m × Set.Ioo (0 : ℝ) 1) :
    (z.2.1 : ℝ) < 1 := by
  -- Use the upper endpoint inequality of `Ioo`.
  exact z.2.2.2

/-- Helper for Exercise 72.1: imposing radius below one on positive polar coordinates
gives the interval `(0, 1)`. -/
def polarRadiusLtOneHomeomorph (m : ℕ) :
    {z : StandardSphere m × Set.Ioi (0 : ℝ) // z.2.1 < 1} ≃ₜ
      StandardSphere m × Set.Ioo (0 : ℝ) 1 :=
  { toFun := fun z ↦ (z.1.1, ⟨z.1.2.1, polarRadiusLtOne_to_mem m z⟩)
    invFun := fun z ↦ ⟨(z.1, ⟨z.2.1, polarRadiusLtOne_inv_positive m z⟩),
      polarRadiusLtOne_inv_mem m z⟩
    left_inv := fun z ↦ Subtype.ext (Prod.ext rfl (Subtype.coe_eta z.1.2 _))
    right_inv := fun z ↦ Prod.ext rfl (Subtype.coe_eta z.2 _)
    continuous_toFun :=
      (continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_subtype_val.comp
          (continuous_snd.comp continuous_subtype_val)).subtype_mk
            (polarRadiusLtOne_to_mem m))
    continuous_invFun :=
      (continuous_fst.prodMk
        ((continuous_subtype_val.comp continuous_snd).subtype_mk
          (polarRadiusLtOne_inv_positive m))).subtype_mk
            (polarRadiusLtOne_inv_mem m) }

/-- Helper for Exercise 72.1: polar coordinates identify the punctured open unit ball
with a sphere times `(0, 1)`. -/
noncomputable def puncturedOpenUnitBallPolarHomeomorph (m : ℕ) :
    PuncturedOpenUnitBall m ≃ₜ StandardSphere m × Set.Ioo (0 : ℝ) 1 :=
  ((homeomorphUnitSphereProd
    (EuclideanSpace ℝ (Fin (m + 1)))).subtype
      (puncturedOpenUnitBall_polarRadius_lt_one_iff m)).trans
        (polarRadiusLtOneHomeomorph m)

/-- Helper for Exercise 72.1: a punctured open cell is simply connected in dimensions
at least three. -/
lemma puncturedOpenCell_simplyConnectedSpace (m : ℕ) (hm : 2 ≤ m) :
    SimplyConnectedSpace (PuncturedOpenCell m) := by
  -- Polar coordinates reduce to a simply connected sphere times a contractible interval.
  letI : SimplyConnectedSpace (StandardSphere m) :=
    simplyConnectedSpace_standardSphere m hm
  have hhalf : (2⁻¹ : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    norm_num
  letI : ContractibleSpace (Set.Ioo (0 : ℝ) 1) :=
    (convex_Ioo (0 : ℝ) 1).contractibleSpace ⟨2⁻¹, hhalf⟩
  let intervalEquiv := (ContractibleSpace.hequiv_unit (Set.Ioo (0 : ℝ) 1)).some
  let productEquiv : StandardSphere m × Set.Ioo (0 : ℝ) 1 ≃ₕ StandardSphere m :=
    ((ContinuousMap.HomotopyEquiv.refl (StandardSphere m)).prodCongr
      intervalEquiv).trans (Homeomorph.prodUnique (StandardSphere m) Unit).toHomotopyEquiv
  letI : SimplyConnectedSpace (StandardSphere m × Set.Ioo (0 : ℝ) 1) :=
    productEquiv.simplyConnectedSpace
  exact ((puncturedOpenCellHomeomorphUnitBall m).trans
    (puncturedOpenUnitBallPolarHomeomorph m)).toHomotopyEquiv.simplyConnectedSpace

/-- Helper for Exercise 72.1: the canonical homeomorphism from the open cell to `Aᶜ`. -/
noncomputable def higherCell_interiorHomeomorphCompl {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    ↥((StandardSphere.boundary m)ᶜ) ≃ₜ ↥(Aᶜ) :=
  (higherCell_interiorRestriction_isHomeomorph
    m A h h_boundary h_interior).homeomorph

/-- Helper for Exercise 72.1: deleting the cell center corresponds under the interior
homeomorphism to deleting its image. -/
lemma higherCell_interiorHomeomorph_mem_puncture_iff {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ)
    (x : ↥((StandardSphere.boundary m)ᶜ)) :
    x ∈ ({closedUnitBallCenterInterior m}ᶜ :
        Set ↥((StandardSphere.boundary m)ᶜ)) ↔
      higherCell_interiorHomeomorphCompl m A h h_boundary h_interior x ∈
        (Subtype.val ⁻¹' ({h (closedUnitBallCenter m)} : Set X)ᶜ : Set ↥(Aᶜ)) := by
  -- Fiberwise uniqueness of the center makes deletion commute with the homeomorphism.
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_preimage]
  constructor
  · intro hx himage
    apply hx
    apply Subtype.ext
    exact higherCell_eq_center_of_image_eq_center
      m A h h_boundary h_interior x.1 himage
  · intro himage hx
    apply himage
    have hx_value := congrArg Subtype.val hx
    exact congrArg h hx_value

/-- Helper for Exercise 72.1: a punctured subspace of `Aᶜ` is canonically the overlap
of `Aᶜ` with the punctured ambient space. -/
def higherCell_complPunctureHomeomorphOverlap {X : Type u} [TopologicalSpace X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X)) :
    ↥(Subtype.val ⁻¹' ({h (closedUnitBallCenter m)} : Set X)ᶜ : Set ↥(Aᶜ)) ≃ₜ
      ↥((({h (closedUnitBallCenter m)} : Set X)ᶜ) ∩ Aᶜ) :=
  { toFun := fun x ↦ ⟨x.1.1, ⟨x.2, x.1.2⟩⟩
    invFun := fun x ↦ ⟨⟨x.1, x.2.2⟩, x.2.1⟩
    left_inv := fun _x ↦ rfl
    right_inv := fun _x ↦ rfl
    continuous_toFun :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    continuous_invFun :=
      (continuous_subtype_val.subtype_mk _).subtype_mk _ }

/-- Helper for Exercise 72.1: the punctured open cell is homeomorphic to the van Kampen
overlap. -/
noncomputable def higherCell_puncturedInteriorHomeomorphOverlap {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (m : ℕ) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    PuncturedOpenCell m ≃ₜ
      ↥((({h (closedUnitBallCenter m)} : Set X)ᶜ) ∩ Aᶜ) :=
  ((higherCell_interiorHomeomorphCompl
    m A h h_boundary h_interior).subtype
      (higherCell_interiorHomeomorph_mem_puncture_iff
        m A h h_boundary h_interior)).trans
    (higherCell_complPunctureHomeomorphOverlap m A h)

/-- Helper for Exercise 72.1: the overlap of the punctured ambient space and `Aᶜ` is
simply connected in the required dimensions. -/
lemma higherCell_overlap_simplyConnectedSpace {X : Type u} [TopologicalSpace X]
    [T2Space X]
    (m : ℕ) (hm : 2 ≤ m) (A : Set X) (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ) :
    SimplyConnectedSpace
      ↥((({h (closedUnitBallCenter m)} : Set X)ᶜ) ∩ Aᶜ) := by
  -- Transport simple connectedness of the polar punctured open cell across the overlap map.
  letI : SimplyConnectedSpace (PuncturedOpenCell m) :=
    puncturedOpenCell_simplyConnectedSpace m hm
  exact (higherCell_puncturedInteriorHomeomorphOverlap
    m A h h_boundary h_interior).symm.toHomotopyEquiv.simplyConnectedSpace

/-- Helper for Exercise 72.1: path-connectedness is transported along a homotopy
equivalence. -/
lemma pathConnectedSpace_of_homotopyEquiv {Y Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] [PathConnectedSpace Y]
    (e : Y ≃ₕ Z) : PathConnectedSpace Z := by
  -- Join target points through chosen inverse images, using the right-inverse homotopy
  -- at the two ends and a path in the source in the middle.
  obtain ⟨H⟩ := e.right_inv
  refine ⟨⟨e (Classical.choice (inferInstance : Nonempty Y))⟩, ?_⟩
  intro z₀ z₁
  let middle := (PathConnectedSpace.somePath (e.symm z₀) (e.symm z₁)).map e.continuous
  exact ⟨(H.evalAt z₀).symm |>.trans middle |>.trans (H.evalAt z₁)⟩

/-- Helper for Exercise 72.1: an induced fundamental-group map commutes with
basepoint change along a path. -/
lemma FundamentalGroup.map_comp_basepointChange {Y Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) {y₀ y₁ : Y} (γ : Path y₀ y₁) :
    (fundamentalGroupMulEquivOfPath (γ.map f.continuous)).toMonoidHom.comp
        (map f y₀) =
      (map f y₁).comp (fundamentalGroupMulEquivOfPath γ).toMonoidHom := by
  -- Expand both conjugations; functoriality carries the three path composites
  -- through the induced fundamental-groupoid functor.
  ext p
  let F := FundamentalGroupoid.map f
  let α : FundamentalGroupoid.mk y₀ ≅ FundamentalGroupoid.mk y₁ :=
    (CategoryTheory.Groupoid.isoEquivHom _ _).symm ⟦γ⟧
  let β : FundamentalGroupoid.mk (f y₀) ≅ FundamentalGroupoid.mk (f y₁) :=
    (CategoryTheory.Groupoid.isoEquivHom _ _).symm ⟦γ.map f.continuous⟧
  have hβ : F.mapIso α = β := by
    apply CategoryTheory.Iso.ext
    rfl
  change β.conj (F.map p) = F.map (α.conj p)
  rw [← hβ]
  simp only [CategoryTheory.Iso.conj_apply, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.mapIso_inv, CategoryTheory.Functor.map_comp]
  rfl

/-- Helper for Exercise 72.1: bijectivity of an induced fundamental-group map is
independent of the basepoint along a chosen path. -/
lemma FundamentalGroup.map_bijective_iff_of_path {Y Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) {y₀ y₁ : Y} (γ : Path y₀ y₁) :
    Function.Bijective (map f y₀) ↔ Function.Bijective (map f y₁) := by
  -- The naturality square has bijective horizontal basepoint-change maps, so either
  -- vertical induced map is bijective exactly when the other is.
  have hcomm := map_comp_basepointChange f γ
  have hsource : Function.Bijective
      (fundamentalGroupMulEquivOfPath γ).toMonoidHom :=
    (fundamentalGroupMulEquivOfPath γ).bijective
  have htarget : Function.Bijective
      (fundamentalGroupMulEquivOfPath (γ.map f.continuous)).toMonoidHom :=
    (fundamentalGroupMulEquivOfPath (γ.map f.continuous)).bijective
  have hcomm_fun :
      (fundamentalGroupMulEquivOfPath (γ.map f.continuous)).toMonoidHom ∘
          map f y₀ =
        map f y₁ ∘ (fundamentalGroupMulEquivOfPath γ).toMonoidHom :=
    congrArg DFunLike.coe hcomm
  rw [← (Function.Bijective.of_comp_iff _ hsource)]
  rw [← hcomm_fun]
  exact (Function.Bijective.of_comp_iff' htarget _).symm

/-- Helper for Exercise 72.1: fundamental-group maps respect composition of
continuous maps. -/
lemma fundamentalGroupMap_comp {Y Z W : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
    (g : C(Z, W)) (f : C(Y, Z)) (y : Y) :
    (FundamentalGroup.map g (f y)).comp (FundamentalGroup.map f y) =
      FundamentalGroup.map (g.comp f) y := by
  -- Compute each induced map on a loop class and use functoriality of quotient mapping.
  ext q
  simp only [MonoidHom.comp_apply]
  have innerMap :
      FundamentalGroup.map f y q = Path.Homotopic.Quotient.map q f :=
    FundamentalGroup.map_apply f y q
  have nestedMap :
      Path.Homotopic.Quotient.map
          (Path.Homotopic.Quotient.map q f) g =
        Path.Homotopic.Quotient.map q (g.comp f) :=
    (Path.Homotopic.Quotient.map_comp (p := q) (f := f) (g := g)).symm
  have outerMap :
      FundamentalGroup.map g (f y) (Path.Homotopic.Quotient.map q f) =
        FundamentalGroup.map (g.comp f) y q := by
    rw [FundamentalGroup.map_apply, FundamentalGroup.map_apply]
    exact nestedMap
  exact (congrArg (fun z ↦ FundamentalGroup.map g (f y) z) innerMap).trans outerMap

/-- Helper for Exercise 72.1: the ambient subtype map is the fundamental-group map of
the bundled subtype inclusion. -/
lemma FundamentalGroup.mapOfSubtype_eq_map {Y : Type*} [TopologicalSpace Y]
    (S : Set Y) (s : S) :
    mapOfSubtype S s =
      map (⟨Subtype.val, continuous_subtype_val⟩ : C(S, Y)) s := by
  -- This exposes the defining computation rule needed for basepoint transport.
  unfold mapOfSubtype
  ext q
  rw [map_apply]

/-- Helper for Exercise 72.1: inclusion through a subspace and then into the ambient
space induces the direct ambient inclusion on fundamental groups. -/
lemma FundamentalGroup.mapOfSubtype_comp_mapOfSubset
    {Y : Type*} [TopologicalSpace Y] {S T : Set Y}
    (hST : S ⊆ T) (s : S) :
    (mapOfSubtype T ⟨s, hST s.property⟩).comp (mapOfSubset hST s) =
      mapOfSubtype S s := by
  -- Expose the three inclusion maps, then collapse their composite by functoriality.
  rw [mapOfSubset_eq_map_inclusion]
  rw [mapOfSubtype_eq_map, mapOfSubtype_eq_map]
  calc
    _ = map
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(T, Y)).comp
          (ContinuousMap.inclusion hST)) s :=
      fundamentalGroupMap_comp _ _ s
    _ = map (⟨Subtype.val, continuous_subtype_val⟩ : C(S, Y)) s := by
      congr 1

/-- Helper for Exercise 72.1: restoring the deleted cell center induces a bijection on
fundamental groups. -/
lemma higherCell_punctureInclusion_bijective {X : Type u} [TopologicalSpace X]
    [T2Space X]
    (m : ℕ) (hm : 2 ≤ m) (A : Set X) (hA_closed : IsClosed A)
    (hA_pathConnected : IsPathConnected A)
    (h : C(ClosedUnitBall m, X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary m) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary m)ᶜ Aᶜ)
    (a : ↥(({h (closedUnitBallCenter m)} : Set X)ᶜ)) :
    Function.Bijective
      (FundamentalGroup.mapOfSubtype
        ({h (closedUnitBallCenter m)} : Set X)ᶜ a) := by
  -- Use the punctured space and the open cell complement as the van Kampen cover.
  let U : Set X := ({h (closedUnitBallCenter m)} : Set X)ᶜ
  let V : Set X := Aᶜ
  letI : PathConnectedSpace A :=
    isPathConnected_iff_pathConnectedSpace.mp hA_pathConnected
  let puncturedEquiv := higherCell_attachedSubspaceHomotopyEquivPuncture
    m A h hA_closed h_boundary h_interior
  letI : PathConnectedSpace U :=
    pathConnectedSpace_of_homotopyEquiv puncturedEquiv
  letI : SimplyConnectedSpace V :=
    higherCell_compl_simplyConnectedSpace m A h h_boundary h_interior
  letI : SimplyConnectedSpace (U ∩ V : Set X) :=
    higherCell_overlap_simplyConnectedSpace
      m hm A h h_boundary h_interior
  let x₀ : (U ∩ V : Set X) :=
    Classical.choice (inferInstance : Nonempty (U ∩ V : Set X))
  have hx₀ : (x₀ : X) ∈ U ∩ V := x₀.property
  have hU_open : IsOpen U := isClosed_singleton.isOpen_compl
  have hV_open : IsOpen V := hA_closed.isOpen_compl
  have hcover : U ∪ V = Set.univ := by
    ext x
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      by_cases hx : x = h (closedUnitBallCenter m)
      · right
        rw [hx]
        exact higherCell_center_image_mem_compl m A h h_interior
      · left
        exact hx
  -- Van Kampen gives surjectivity; simple connectedness of the overlap kills its kernel.
  have hsurjective := vanKampenLeftInclusion_surjective
    U V (x₀ : X) hx₀ hU_open hV_open hcover
  have hnormal : vanKampenLeftNormalClosure U V (x₀ : X) hx₀ = ⊥ := by
    rw [Subgroup.normalClosure_eq_bot_iff]
    rintro g ⟨q, rfl⟩
    have hq : q = 1 := Subsingleton.elim q 1
    rw [hq, map_one]
    exact Set.mem_singleton 1
  have hkernel :
      (FundamentalGroup.mapOfSubtype U ⟨(x₀ : X), hx₀.1⟩).ker = ⊥ :=
    (vanKampenLeftInclusion_ker
      U V (x₀ : X) hx₀ hU_open hV_open hcover).trans hnormal
  have hinjective : Function.Injective
      (FundamentalGroup.mapOfSubtype U ⟨(x₀ : X), hx₀.1⟩) :=
    (MonoidHom.ker_eq_bot_iff _).mp hkernel
  have hbase : Function.Bijective
      (FundamentalGroup.mapOfSubtype U ⟨(x₀ : X), hx₀.1⟩) :=
    ⟨hinjective, hsurjective⟩
  -- Transport bijectivity from the overlap basepoint to the requested punctured point.
  let inclusion : C(U, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let γ := PathConnectedSpace.somePath (⟨(x₀ : X), hx₀.1⟩ : U) a
  have hbase_map : Function.Bijective
      (FundamentalGroup.map inclusion (⟨(x₀ : X), hx₀.1⟩ : U)) := by
    rw [← FundamentalGroup.mapOfSubtype_eq_map]
    exact hbase
  rw [FundamentalGroup.mapOfSubtype_eq_map]
  exact (FundamentalGroup.map_bijective_iff_of_path inclusion γ).mp hbase_map

/-- Exercise 72.1: If a Hausdorff space `X` is obtained from a closed path-connected
subspace `A` by adjoining an open `n`-cell with `2 < n`, then inclusion induces a
bijective homomorphism from `π₁(A, a)` to `π₁(X, a)` for every basepoint `a` in the
image of the attaching sphere. -/
theorem fundamentalGroupMap_inclusion_bijective {X : Type u} [TopologicalSpace X]
    [T2Space X] (n : ℕ) (hn : 2 < n) (A : Set X) (hA_closed : IsClosed A)
    (hA_pathConnected : IsPathConnected A)
    (h : C(ClosedUnitBall (n - 1), X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary (n - 1)) A)
    (h_interior : Set.BijOn h (StandardSphere.boundary (n - 1))ᶜ Aᶜ)
    (p : StandardSphere.boundary (n - 1)) :
    Function.Bijective (FundamentalGroup.mapOfSubtype A ⟨h p, h_boundary p.property⟩) := by
  -- Route correction: the radial homotopy was descended directly to the concrete
  -- punctured cell image, avoiding the former nested-range coercion obstruction.
  have hm : 2 ≤ n - 1 := by
    omega
  -- The pasted radial deformation makes inclusion of `A` into the punctured space
  -- a homotopy equivalence, hence its induced map is bijective.
  have hattached : Function.Bijective
      (FundamentalGroup.mapOfSubset
        (higherCell_subset_puncturedCenter (n - 1) A h h_interior)
        ⟨h p, h_boundary p.property⟩) := by
    have hequiv :=
      (higherCell_attachedSubspaceHomotopyEquivPuncture
        (n - 1) A h hA_closed h_boundary h_interior).fundamentalGroupMap_bijective
          ⟨h p, h_boundary p.property⟩
    rw [higherCell_attachedSubspaceHomotopyEquivPuncture_toFun,
      higherCell_attachedInclusionPuncture_eq_inclusion] at hequiv
    rw [FundamentalGroup.mapOfSubset_eq_map_inclusion]
    exact hequiv
  -- Van Kampen restores the deleted center because the overlap is simply connected
  -- in dimension at least three.
  have hrestore : Function.Bijective
      (FundamentalGroup.mapOfSubtype
        ({h (closedUnitBallCenter (n - 1))} : Set X)ᶜ
        ⟨h p, higherCell_subset_puncturedCenter
          (n - 1) A h h_interior (h_boundary p.property)⟩) :=
    higherCell_punctureInclusion_bijective
      (n - 1) hm A hA_closed hA_pathConnected h h_boundary h_interior _
  -- Compose the two bijections and collapse the nested inclusions to the ambient one.
  have hcomposition := hrestore.comp hattached
  change Function.Bijective
    ⇑((FundamentalGroup.mapOfSubtype
      ({h (closedUnitBallCenter (n - 1))} : Set X)ᶜ
      ⟨h p, higherCell_subset_puncturedCenter
        (n - 1) A h h_interior (h_boundary p.property)⟩).comp
      (FundamentalGroup.mapOfSubset
        (higherCell_subset_puncturedCenter (n - 1) A h h_interior)
        ⟨h p, h_boundary p.property⟩)) at hcomposition
  have hinclusionComposition :
      (FundamentalGroup.mapOfSubtype
        ({h (closedUnitBallCenter (n - 1))} : Set X)ᶜ
        ⟨h p, higherCell_subset_puncturedCenter
          (n - 1) A h h_interior (h_boundary p.property)⟩).comp
        (FundamentalGroup.mapOfSubset
          (higherCell_subset_puncturedCenter (n - 1) A h h_interior)
          ⟨h p, h_boundary p.property⟩) =
      FundamentalGroup.mapOfSubtype A ⟨h p, h_boundary p.property⟩ :=
    FundamentalGroup.mapOfSubtype_comp_mapOfSubset
      (higherCell_subset_puncturedCenter (n - 1) A h h_interior)
      ⟨h p, h_boundary p.property⟩
  exact hinclusionComposition ▸ hcomposition

end
