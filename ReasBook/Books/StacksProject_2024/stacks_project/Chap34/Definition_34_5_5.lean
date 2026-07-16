import Mathlib
import StacksProject_2024.stacks_project.Chap07.Definition_7_6_1
import StacksProject_2024.stacks_project.Chap34.Definition_34_5_1

open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.SemiRepresentableFamily.Over

universe u

namespace AlgebraicGeometry

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `lean_leansearch` surfaced `Scheme.Hom.appTop`,
-- `Scheme.OpenCover.isOpenCover_opensRange`, and `targetAffineLocally`. This source item is not a
-- canonical recall because it keeps explicit finite family data on affine source schemes together
-- with global standard-smooth ring maps and only asks that the set-theoretic images cover `T`.

/-- Definition 34.5.5: for an affine scheme `T`, a standard smooth covering of `T` is a finite
family of morphisms `f_j : U_j ⟶ T` with each `U_j` affine, each induced global-sections map
`\Gamma(T, \mathcal O_T) → \Gamma(U_j, \mathcal O_{U_j})` standard smooth, and whose images cover
all points of `T`. -/
structure StandardSmoothCovering (T : Scheme.{u}) [IsAffine T] where
  /-- The number of affine standard smooth charts in the covering family. -/
  n : ℕ
  /-- The source affine schemes of the covering family. -/
  U : Fin n → Scheme.{u}
  /-- The morphisms from the source affine schemes to the affine target `T`. -/
  map : ∀ j, U j ⟶ T
  /-- Each source chart in the family is affine. -/
  isAffine : ∀ j, IsAffine (U j)
  /-- Each induced map on global sections is standard smooth. -/
  isStandardSmooth :
    ∀ j, RingHom.IsStandardSmooth (CommRingCat.Hom.hom (Scheme.Hom.appTop (map j)))
  /-- The set-theoretic images of the family cover all points of `T`. -/
  cover : ∀ t : T, ∃ j, t ∈ Set.range (map j)

/-- A standard smooth covering of an affine scheme can be used as its underlying finite family of
source schemes. -/
instance {T : Scheme.{u}} [IsAffine T] :
    CoeFun (StandardSmoothCovering T) (fun 𝒰 ↦ Fin 𝒰.n → Scheme.{u}) where
  coe 𝒰 := 𝒰.U

/-- Source-facing specification for Definition 34.5.5: a standard smooth covering supplies affine
sources, the standard-smooth affine ring condition, and a jointly covering finite family of
images. -/
theorem StandardSmoothCovering.source_spec
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSmoothCovering T) :
    (∀ j, IsAffine (𝒰.U j)) ∧
      (∀ j, RingHom.IsStandardSmooth (CommRingCat.Hom.hom (Scheme.Hom.appTop (𝒰.map j)))) ∧
        (∀ t : T, ∃ j, t ∈ Set.range (𝒰.map j)) := by
  exact ⟨𝒰.isAffine, 𝒰.isStandardSmooth, 𝒰.cover⟩

/-- For each member of a standard smooth covering, the induced map on global sections is standard
smooth. -/
theorem StandardSmoothCovering.appTop_isStandardSmooth
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSmoothCovering T) (j : Fin 𝒰.n) :
    RingHom.IsStandardSmooth (CommRingCat.Hom.hom (Scheme.Hom.appTop (𝒰.map j))) :=
  𝒰.isStandardSmooth j

/-- The underlying fixed-target family of a standard smooth covering, viewed in `Over T`. -/
abbrev StandardSmoothCovering.toOverFamily
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSmoothCovering T) :
    SemiRepresentableFamily.Over T :=
  ofArrows 𝒰.U 𝒰.map

/-- Every member of a standard smooth covering is a smooth morphism. -/
theorem StandardSmoothCovering.smooth_map
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSmoothCovering T) (j : Fin 𝒰.n) :
    Smooth (𝒰.map j) := sorry

/-- A standard smooth covering of an affine scheme covers all points of the target by the union of
the set-theoretic images of its members. -/
theorem StandardSmoothCovering.iUnion_range_eq_univ
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSmoothCovering T) :
    (⋃ j, Set.range (𝒰.map j)) = Set.univ := by
  ext t
  constructor
  · intro _
    simp
  · intro _
    simpa [Set.mem_iUnion] using 𝒰.cover t

/-- A standard smooth covering presents a finite smooth covering family in the canonical smooth
precoverage on schemes. -/
theorem StandardSmoothCovering.mem_smooth_precoverage
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSmoothCovering T) :
    Presieve.ofArrows 𝒰.U 𝒰.map ∈ (Scheme.precoverage @Smooth).coverings T := sorry

/-- A standard smooth covering induces a smooth covering in the canonical Chapter 34 fixed-target
family owner. -/
theorem StandardSmoothCovering.smoothCovering
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSmoothCovering T) :
    Scheme.SmoothCovering (𝒰.toOverFamily.obj) := sorry

end AlgebraicGeometry
