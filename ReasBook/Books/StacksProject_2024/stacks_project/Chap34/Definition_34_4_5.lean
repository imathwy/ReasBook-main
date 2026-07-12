import Mathlib
import StacksProject_2024.Chap07.Definition_7_8_1
import StacksProject_2024.Chap34.Definition_34_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u

namespace AlgebraicGeometry

section

variable {T : Scheme.{u}}

-- Semantic recall unavailable: `lean_leansearch` timed out in this environment. Local precedent in
-- `Chap34/Definition_34_9_10.lean` shows that the source's "standard" finite-family adjective is
-- best represented by explicit `Fin n` data, while `Chap34/Lemma_34_4_4.lean` verifies the
-- canonical precoverage owner for jointly surjective étale families as `Scheme.precoverage
-- (@Etale)`.

/-- Definition 34.4.5: a standard étale covering of an affine scheme `T` is a finite family
`Uⱼ ⟶ T` with each `Uⱼ` affine, each morphism étale, and whose images cover all points of `T`. -/
@[stacks 03WU]
structure StandardEtaleCover (T : Scheme.{u}) [IsAffine T] where
  /-- The number of morphisms in the covering family. -/
  n : ℕ
  /-- The affine schemes occurring in the covering family. -/
  U : Fin n → Scheme.{u}
  /-- The morphisms of the covering family. -/
  map : (j : Fin n) → U j ⟶ T
  /-- Each source scheme in the covering family is affine. -/
  isAffine : ∀ j, IsAffine (U j)
  /-- Each morphism in the covering family is étale. -/
  etale : ∀ j, Etale (map j)
  /-- The images of the morphisms in the covering family cover all points of `T`. -/
  cover : ∀ t : T, ∃ j, t ∈ Set.range (map j)

/-- A standard étale covering can be used as its underlying finite family of morphisms to `T`. -/
instance [IsAffine T] : CoeFun (StandardEtaleCover T) (fun 𝒰 ↦ (j : Fin 𝒰.n) → 𝒰.U j ⟶ T) where
  coe 𝒰 := 𝒰.map

/-- Source-facing specification for Definition 34.4.5: a standard étale cover supplies affine
sources, étale morphisms, and a jointly covering finite family of images. -/
theorem StandardEtaleCover.source_spec [IsAffine T] (𝒰 : StandardEtaleCover T) :
    (∀ j, IsAffine (𝒰.U j)) ∧
      (∀ j, Etale (𝒰.map j)) ∧
        (∀ t : T, ∃ j, t ∈ Set.range (𝒰.map j)) := by
  exact ⟨𝒰.isAffine, 𝒰.etale, 𝒰.cover⟩

/-- The underlying finite standard étale covering family, viewed as an ordinary étale covering of
`T`. -/
def StandardEtaleCover.toEtaleCovering [IsAffine T] (𝒰 : StandardEtaleCover T) :
    Scheme.Cover Scheme.etalePrecoverage T :=
  Scheme.Cover.mkOfCovers (Fin 𝒰.n) 𝒰.U 𝒰.map
    (fun t ↦ by
      simpa [Set.mem_range] using 𝒰.cover t)
    𝒰.etale

@[simp] theorem StandardEtaleCover.toEtaleCovering_X [IsAffine T]
    (𝒰 : StandardEtaleCover T) (j : Fin 𝒰.n) :
    𝒰.toEtaleCovering.X j = 𝒰.U j := rfl

@[simp] theorem StandardEtaleCover.toEtaleCovering_f [IsAffine T]
    (𝒰 : StandardEtaleCover T) (j : Fin 𝒰.n) :
    𝒰.toEtaleCovering.f j = 𝒰.map j := rfl

/-- A standard étale covering covers all points of `T` by the union of the set-theoretic images of
its members. -/
theorem StandardEtaleCover.iUnion_range_eq_univ [IsAffine T] (𝒰 : StandardEtaleCover T) :
    (⋃ j, Set.range (𝒰.map j)) = Set.univ := by
  ext t
  constructor
  · intro _
    simp
  · intro _
    simpa [Set.mem_iUnion] using 𝒰.cover t

/-- Companion bridge for Definition 34.4.5: a standard étale covering presents a finite family in
`Scheme.precoverage (@Etale)`, i.e. a jointly surjective family of étale morphisms. -/
theorem StandardEtaleCover.mem_etale_precoverage [IsAffine T] (𝒰 : StandardEtaleCover T) :
    Presieve.ofArrows 𝒰.U 𝒰.map ∈ Scheme.etalePrecoverage.coverings T := by
  simpa using 𝒰.toEtaleCovering.mem₀

/-- The underlying finite family of a standard étale covering, viewed as a semi-representable
family over `T`. -/
def StandardEtaleCover.toFamilyOver [IsAffine T] (𝒰 : StandardEtaleCover T) :
    SemiRepresentableFamily.Over T :=
  ofArrows 𝒰.U 𝒰.map

@[simp] theorem StandardEtaleCover.toFamilyOver_obj [IsAffine T]
    (𝒰 : StandardEtaleCover T) (j : Fin 𝒰.n) :
    𝒰.toFamilyOver.obj j = Over.mk (𝒰.map j) := rfl

end

end AlgebraicGeometry
