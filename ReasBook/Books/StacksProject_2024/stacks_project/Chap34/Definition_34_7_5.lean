import Mathlib
import StacksProject_2024.Chap34.Definition_34_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical morphism properties `Flat` and
-- `LocallyOfFinitePresentation`, while nearby Chapter 34 precedents `FppfCover` and
-- `StandardFpqcCover` fix the public owner shape for a finite affine family of covering morphisms.
-- The source item is therefore formalized as the finite affine refinement of an fppf covering.

/-- Definition 34.7.5: a standard fppf covering of an affine scheme `T` is a finite family
`fⱼ : Uⱼ ⟶ T` with each `Uⱼ` affine, each `fⱼ` flat and locally of finite presentation, and whose
images cover all points of `T`. -/
structure StandardFppfCover (T : Scheme.{u}) [IsAffine T] where
  /-- The number of morphisms in the covering family. -/
  n : ℕ
  /-- The affine schemes in the covering family. -/
  U : Fin n → Scheme.{u}
  /-- The morphisms of the covering family. -/
  map : (j : Fin n) → U j ⟶ T
  /-- Each source scheme in the family is affine. -/
  isAffine : ∀ j, IsAffine (U j)
  /-- Each morphism in the family is flat. -/
  flat : ∀ j, Flat (map j)
  /-- Each morphism in the family is locally of finite presentation. -/
  locallyOfFinitePresentation : ∀ j, LocallyOfFinitePresentation (map j)
  /-- The images of the covering morphisms cover all points of `T`. -/
  cover : ∀ t : T, ∃ j, t ∈ Set.range (map j)

/-- A standard fppf covering can be used as its underlying finite family of morphisms into `T`. -/
instance {T : Scheme.{u}} [IsAffine T] :
    CoeFun (StandardFppfCover T) (fun 𝒰 ↦ (j : Fin 𝒰.n) → 𝒰.U j ⟶ T) where
  coe 𝒰 := 𝒰.map

/-- Source-facing specification for Definition 34.7.5: a standard fppf cover supplies affine
sources, flatness, local finite presentation, and a jointly covering finite family of images. -/
theorem StandardFppfCover.source_spec {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardFppfCover T) :
    (∀ j, IsAffine (𝒰.U j)) ∧
      (∀ j, Flat (𝒰.map j)) ∧
        (∀ j, LocallyOfFinitePresentation (𝒰.map j)) ∧
          (∀ t : T, ∃ j, t ∈ Set.range (𝒰.map j)) := by
  exact ⟨𝒰.isAffine, 𝒰.flat, 𝒰.locallyOfFinitePresentation, 𝒰.cover⟩

/-- The underlying finite standard fppf covering family, viewed as an ordinary fppf covering of
`T`. -/
def StandardFppfCover.toFppfCover {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardFppfCover T) :
    FppfCover T :=
  Scheme.Cover.mkOfCovers (Fin 𝒰.n) 𝒰.U 𝒰.map
    (fun t ↦ by
      simpa [Set.mem_range] using 𝒰.cover t)
    (fun j ↦ ⟨𝒰.flat j, 𝒰.locallyOfFinitePresentation j⟩)

/-- Companion bridge for Definition 34.7.5: forgetting local finite presentation, the arrows of a
standard fppf covering form a covering family for the flat precoverage on schemes. -/
theorem StandardFppfCover.mem_flat_precoverage {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardFppfCover T) :
    Presieve.ofArrows 𝒰.U 𝒰 ∈
      (Scheme.precoverage (fun {_ _} f ↦ Flat f)).coverings T := by
  simpa [StandardFppfCover.toFppfCover] using
    𝒰.toFppfCover.mem_flat_precoverage

end AlgebraicGeometry
