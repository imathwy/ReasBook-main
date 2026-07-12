import Mathlib
import StacksProject_2024.Chap07.Definition_7_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u

namespace AlgebraicGeometry

section

variable {T : Scheme.{u}} [IsAffine T]

-- Semantic recall: `lean_leansearch` surfaced `Scheme.precoverage` and the flat morphism
-- predicate, so the canonical owner is the flat precoverage on schemes. Local precedent in
-- `Chap26/Definition_26_5_2.lean` records the
-- "standard" adjective by keeping the finite indexing data explicit in a structure.

/-- Definition 34.9.10: a standard fpqc covering of an affine scheme `T` is a finite family
`Uⱼ ⟶ T` with each `Uⱼ` affine, each morphism flat, and whose images cover all points of `T`. -/
@[stacks 022F]
structure StandardFpqcCover (T : Scheme.{u}) [IsAffine T] where
  /-- The number of morphisms in the covering family. -/
  n : ℕ
  /-- The affine schemes occurring in the covering family. -/
  U : Fin n → Scheme.{u}
  /-- The morphisms of the covering family. -/
  map : (j : Fin n) → U j ⟶ T
  /-- Each source scheme in the covering family is affine. -/
  isAffine : ∀ j, IsAffine (U j)
  /-- Each morphism in the covering family is flat. -/
  flat : ∀ j, Flat (map j)
  /-- The images of the morphisms in the covering family cover all points of `T`. -/
  cover : ∀ t : T, ∃ j, t ∈ Set.range (map j)

/-- A standard fpqc covering can be used as its underlying finite family of morphisms to `T`. -/
instance : CoeFun (StandardFpqcCover T) (fun 𝒰 ↦ (j : Fin 𝒰.n) → 𝒰.U j ⟶ T) where
  coe 𝒰 := 𝒰.map

/-- Source-facing specification for Definition 34.9.10: a standard fpqc cover supplies affine
sources, flatness, and a jointly covering finite family of images. -/
theorem StandardFpqcCover.source_spec (𝒰 : StandardFpqcCover T) :
    (∀ j, IsAffine (𝒰.U j)) ∧
      (∀ j, Flat (𝒰.map j)) ∧
        (∀ t : T, ∃ j, t ∈ Set.range (𝒰.map j)) := by
  exact ⟨𝒰.isAffine, 𝒰.flat, 𝒰.cover⟩

/-- The underlying finite standard fpqc covering family, viewed as an ordinary covering for the
flat precoverage on schemes. -/
def StandardFpqcCover.toFlatCover (𝒰 : StandardFpqcCover T) :
    Scheme.Cover (Scheme.precoverage (fun {_ _} f ↦ Flat f)) T :=
  Scheme.Cover.mkOfCovers (Fin 𝒰.n) 𝒰.U 𝒰.map
    (fun t ↦ by
      simpa [Set.mem_range] using 𝒰.cover t)
    𝒰.flat

@[simp] theorem StandardFpqcCover.toFlatCover_X (𝒰 : StandardFpqcCover T) (j : Fin 𝒰.n) :
    𝒰.toFlatCover.X j = 𝒰.U j := rfl

@[simp] theorem StandardFpqcCover.toFlatCover_f (𝒰 : StandardFpqcCover T) (j : Fin 𝒰.n) :
    𝒰.toFlatCover.f j = 𝒰.map j := rfl

/-- The underlying fixed-target family of a standard fpqc covering, viewed in `Over T`. -/
abbrev StandardFpqcCover.toOverFamily (𝒰 : StandardFpqcCover T) :
    SemiRepresentableFamily.Over T :=
  ofArrows 𝒰.U 𝒰.map

@[simp] theorem StandardFpqcCover.toOverFamily_obj (𝒰 : StandardFpqcCover T) (j : Fin 𝒰.n) :
    𝒰.toOverFamily.obj j = Over.mk (𝒰.map j) := rfl

/-- A standard fpqc covering covers all points of `T` by the union of the set-theoretic images of
its members. -/
theorem StandardFpqcCover.iUnion_range_eq_univ (𝒰 : StandardFpqcCover T) :
    (⋃ j, Set.range (𝒰.map j)) = Set.univ := by
  ext t
  constructor
  · intro _
    simp
  · intro _
    simpa [Set.mem_iUnion] using 𝒰.cover t

/-- Companion bridge for Definition 34.9.10: a standard fpqc covering presents a finite family in
`Scheme.precoverage (fun {_ _} f ↦ Flat f)`, i.e. a jointly surjective family of flat
morphisms. -/
theorem StandardFpqcCover.mem_flat_precoverage (𝒰 : StandardFpqcCover T) :
    Presieve.ofArrows 𝒰.U 𝒰 ∈
      (Scheme.precoverage (fun {_ _} f ↦ Flat f)).coverings T := by
  simpa [StandardFpqcCover.toFlatCover] using 𝒰.toFlatCover.mem₀

end

end AlgebraicGeometry
