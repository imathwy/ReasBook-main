import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Construction_24_6_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Definition_13_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_2_1

open CategoryTheory
open scoped TopCat Topology Topology.Homotopy

noncomputable section

-- Semantic recall via `lean_leansearch`: no canonical mathlib owner for the bidegree of a
-- multiplication-like sphere map surfaced. This file therefore keeps the source-facing Chapter 24
-- owner `SphereMultiplicationLike.HasBidegree`, but reads each coordinate degree through the
-- existing Chapter 13 owner `SphereSelfMap.HasDegree` after transporting the sphere pointed
-- at `μ.unit` to the canonical suspension-sphere owner.

/-- A comparison between the Chapter 13 suspension sphere `suspensionSphere m` and the
standard sphere `TopCat.sphere m` pointed at `x`. -/
abbrev PointedSphereComparison (m : ℕ+) (x : TopCat.sphere (m : ℕ)) :=
  (suspensionSphere (m : ℕ)).toBasedSpace ≅ underTopOfPoint (TopCat.sphere (m : ℕ)) x

/-- Transport a self-map of `TopCat.sphere m` to the Chapter 13 continuous self-map owner on
`suspensionSphere m` along a pointed comparison. -/
abbrev pointedSphereSelfMapOnSuspensionSphere
    (m : ℕ+) (x : TopCat.sphere (m : ℕ))
    (sphereIso : PointedSphereComparison m x)
    (f : C(TopCat.sphere (m : ℕ), TopCat.sphere (m : ℕ))) :
    SphereSelfMap m :=
  let h :
      (suspensionSphere (m : ℕ)).toCompactlyGenerated ≃ₜ TopCat.sphere (m : ℕ) :=
    TopCat.homeoOfIso ((Under.forget (⊤_ TopCat)).mapIso sphereIso)
  let hMap :
      C((suspensionSphere (m : ℕ)).toCompactlyGenerated, TopCat.sphere (m : ℕ)) :=
    ⟨h, h.continuous_toFun⟩
  let hInv :
      C(TopCat.sphere (m : ℕ), (suspensionSphere (m : ℕ)).toCompactlyGenerated) :=
    ⟨h.symm, h.continuous_invFun⟩
  hInv.comp (f.comp hMap)

namespace SphereMultiplicationLike

/-- The first-coordinate self-map `x ↦ φ(x, e)` attached to `μ`. -/
abbrev firstCoordinateMap {m : ℕ+} (μ : SphereMultiplicationLike (m + 1)) :
    C(TopCat.sphere (m : ℕ), TopCat.sphere (m : ℕ)) :=
  μ.map.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ μ.unit))

/-- The second-coordinate self-map `x ↦ φ(e, x)` attached to `μ`. -/
abbrev secondCoordinateMap {m : ℕ+} (μ : SphereMultiplicationLike (m + 1)) :
    C(TopCat.sphere (m : ℕ), TopCat.sphere (m : ℕ)) :=
  μ.map.comp ((ContinuousMap.const _ μ.unit).prodMk (ContinuousMap.id _))

/-- The first-coordinate self-map of a multiplication-like datum fixes the distinguished unit. -/
@[simp] theorem firstCoordinateMap_unit {m : ℕ+} (μ : SphereMultiplicationLike (m + 1)) :
    μ.firstCoordinateMap μ.unit = μ.unit := by
  simpa [firstCoordinateMap] using μ.map_unit_unit

/-- The second-coordinate self-map of a multiplication-like datum fixes the distinguished unit. -/
@[simp] theorem secondCoordinateMap_unit {m : ℕ+} (μ : SphereMultiplicationLike (m + 1)) :
    μ.secondCoordinateMap μ.unit = μ.unit := by
  simpa [secondCoordinateMap] using μ.map_unit_unit

/-- A multiplication-like map on `S^(n - 1)` has bidegree `(d₁, d₂)` when the first-coordinate
and second-coordinate self-maps obtained by fixing the distinguished unit have degrees `d₁` and
`d₂`, respectively, after transporting the sphere pointed at `μ.unit` to the Chapter 13
canonical sphere owner. -/
class HasBidegree {m : ℕ+} (μ : SphereMultiplicationLike (m + 1)) (d₁ d₂ : ℤ) : Prop where
  /-- The first-coordinate self-map `x ↦ φ(x, e)` has degree `d₁`. -/
  first_degree :
    ∃ sphereIso : PointedSphereComparison m μ.unit,
      SphereSelfMap.HasDegree m
        (pointedSphereSelfMapOnSuspensionSphere m μ.unit sphereIso
          μ.firstCoordinateMap) d₁
  /-- The second-coordinate self-map `x ↦ φ(e, x)` has degree `d₂`. -/
  second_degree :
    ∃ sphereIso : PointedSphereComparison m μ.unit,
      SphereSelfMap.HasDegree m
        (pointedSphereSelfMapOnSuspensionSphere m μ.unit sphereIso
          μ.secondCoordinateMap) d₂

/-- `μ.HasBidegree d₁ d₂` means that the two coordinate self-maps determined by `μ` have
degrees `d₁` and `d₂`. -/
theorem hasBidegree_iff {m : ℕ+} {μ : SphereMultiplicationLike (m + 1)} {d₁ d₂ : ℤ} :
    μ.HasBidegree d₁ d₂ ↔
      (∃ sphereIso : PointedSphereComparison m μ.unit,
        SphereSelfMap.HasDegree m
          (pointedSphereSelfMapOnSuspensionSphere m μ.unit sphereIso
            μ.firstCoordinateMap) d₁) ∧
        ∃ sphereIso : PointedSphereComparison m μ.unit,
          SphereSelfMap.HasDegree m
            (pointedSphereSelfMapOnSuspensionSphere m μ.unit sphereIso
              μ.secondCoordinateMap) d₂ := by
  constructor
  · intro hμ
    exact ⟨hμ.first_degree, hμ.second_degree⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, h₂⟩

/-- Expanding `μ.HasBidegree d₁ d₂` recovers the degree conditions on the first- and
second-coordinate self-maps determined by `μ`. -/
theorem HasBidegree.spec {m : ℕ+} {μ : SphereMultiplicationLike (m + 1)} {d₁ d₂ : ℤ}
    (hμ : μ.HasBidegree d₁ d₂) :
    (∃ sphereIso : PointedSphereComparison m μ.unit,
      SphereSelfMap.HasDegree m
        (pointedSphereSelfMapOnSuspensionSphere m μ.unit sphereIso
          μ.firstCoordinateMap) d₁) ∧
      ∃ sphereIso : PointedSphereComparison m μ.unit,
        SphereSelfMap.HasDegree m
          (pointedSphereSelfMapOnSuspensionSphere m μ.unit sphereIso
            μ.secondCoordinateMap) d₂ :=
  hasBidegree_iff.mp hμ

end SphereMultiplicationLike

/-- Lemma 24.6.4. If `μ : SphereMultiplicationLike (m + 1)` has bidegree `(d₁, d₂)`, then the Hopf
invariant of its Hopf construction is `± d₁ d₂`, recorded here as the alternative that
`hopfConstructionMap (m + 1) μ` has Hopf invariant `d₁ * d₂` or `-(d₁ * d₂)`. -/
theorem hopfConstruction_isHopfInvariant_of_hasBidegree
    {m : ℕ+} {μ : SphereMultiplicationLike (m + 1)} {d₁ d₂ : ℤ}
    (hμ : μ.HasBidegree d₁ d₂) :
    IsHopfInvariant (hopfConstructionMap (m + 1) μ) (d₁ * d₂) ∨
      IsHopfInvariant (hopfConstructionMap (m + 1) μ) (-(d₁ * d₂)) := sorry
