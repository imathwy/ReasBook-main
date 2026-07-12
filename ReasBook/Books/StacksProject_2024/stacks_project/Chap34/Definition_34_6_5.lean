import Mathlib
import StacksProject_2024.Chap07.Definition_7_8_2
import StacksProject_2024.Chap10.Lemma_10_136_13
import StacksProject_2024.Chap10.Definition_10_136_5
import StacksProject_2024.Chap29.Definition_29_30_1_Standard
import StacksProject_2024.Chap34.Definition_34_6_1
import StacksProject_2024.Chap34.Definition_34_6_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u

namespace AlgebraicGeometry

section

variable (T : Scheme.{u}) [IsAffine T]

-- Semantic recall / analogue check:
-- `lean_leansearch` was rate-limited for this item, so the owner choice is verified locally
-- against the smooth analogue `Definition_34_5_5`: the source item keeps explicit finite affine
-- family data together with the standard affine syntomic condition and joint surjectivity on
-- points, so this file owns that source-facing affine covering object.

/-- Definition 34.6.5: for an affine scheme `T`, a standard syntomic covering of `T` is a finite
family of morphisms `f_j : U_j ⟶ T` with each `U_j` affine, each induced global-sections map
\Gamma(T, \mathcal O_T) \to \Gamma(U_j, \mathcal O_{U_j}) a relative global complete
intersection, and whose images cover all points of `T`. -/
@[stacks 0229]
structure StandardSyntomicCovering where
  /-- The number of affine standard syntomic charts in the covering family. -/
  n : ℕ
  /-- The source affine schemes of the covering family. -/
  U : Fin n → Scheme.{u}
  /-- The morphisms from the source affine schemes to the affine target `T`. -/
  map : ∀ j, U j ⟶ T
  /-- Each source chart in the family is affine. -/
  isAffine : ∀ j, IsAffine (U j)
  /-- Each induced global-sections map is a relative global complete intersection. -/
  isRelativeGlobalCompleteIntersection : ∀ j,
    let R := Scheme.Γ.obj (Opposite.op T)
    let A := Scheme.Γ.obj (Opposite.op (U j))
    let φ : R →+* A := CommRingCat.Hom.hom (Scheme.Hom.appTop (map j))
    let _ : Algebra R A := φ.toAlgebra
    Algebra.IsRelativeGlobalCompleteIntersection R A
  /-- The set-theoretic images of the family cover all points of `T`. -/
  cover : ∀ t : T, ∃ j, t ∈ Set.range (map j)

/-- A standard syntomic covering of an affine scheme can be used as its underlying finite family
of source schemes. -/
instance : CoeFun (StandardSyntomicCovering T) (fun 𝒰 ↦ Fin 𝒰.n → Scheme.{u}) where
  coe 𝒰 := 𝒰.U

/-- Each chart of a standard syntomic covering is canonically affine. -/
instance (𝒰 : StandardSyntomicCovering T) (j : Fin 𝒰.n) : IsAffine (𝒰.U j) :=
  𝒰.isAffine j

/-- Source-facing specification for Definition 34.6.5: a standard syntomic covering supplies
affine sources, the standard syntomic ring condition, and a jointly covering finite family of
images. -/
theorem StandardSyntomicCovering.source_spec
    {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardSyntomicCovering T) :
    (∀ j, IsAffine (𝒰.U j)) ∧
      (∀ j, StandardSyntomic (𝒰.map j)) ∧
      (∀ t : T, ∃ j, t ∈ Set.range (𝒰.map j)) := by
  refine ⟨𝒰.isAffine, ?_, 𝒰.cover⟩
  intro j
  let _ := 𝒰.isAffine j
  exact 𝒰.isRelativeGlobalCompleteIntersection j

/-- Each member of a standard syntomic covering is standard syntomic. -/
theorem StandardSyntomicCovering.standardSyntomic
    {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardSyntomicCovering T) (j : Fin 𝒰.n) :
    StandardSyntomic (𝒰.map j) := by
  let _ := 𝒰.isAffine j
  exact 𝒰.isRelativeGlobalCompleteIntersection j

/-- For each member of a standard syntomic covering, the induced map on global sections is a
relative global complete intersection. -/
theorem StandardSyntomicCovering.appTop_isRelativeGlobalCompleteIntersection
    {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardSyntomicCovering T) (j : Fin 𝒰.n) :
    let R := Scheme.Γ.obj (Opposite.op T)
    let A := Scheme.Γ.obj (Opposite.op (𝒰.U j))
    let φ : R →+* A := CommRingCat.Hom.hom (Scheme.Hom.appTop (𝒰.map j))
    let _ : Algebra R A := φ.toAlgebra
    Algebra.IsRelativeGlobalCompleteIntersection R A :=
  𝒰.isRelativeGlobalCompleteIntersection j

/-- Every member of a standard syntomic covering is syntomic. -/
theorem StandardSyntomicCovering.syntomic_map
    {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardSyntomicCovering T) (j : Fin 𝒰.n) :
    Syntomic (𝒰.map j) := by
  exact standardSyntomic_syntomic (𝒰.map j) (𝒰.standardSyntomic j)

/-- The underlying finite standard syntomic covering family, viewed as an ordinary syntomic
covering of `T`. -/
def StandardSyntomicCovering.toSyntomicCover
    {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardSyntomicCovering T) :
    SyntomicCover T :=
  Scheme.Cover.mkOfCovers (Fin 𝒰.n) 𝒰.U 𝒰.map
    (fun t ↦ by
      simpa [Set.mem_range] using 𝒰.cover t)
    𝒰.syntomic_map

@[simp] theorem StandardSyntomicCovering.toSyntomicCover_X
    {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardSyntomicCovering T) (j : Fin 𝒰.n) :
    𝒰.toSyntomicCover.X j = 𝒰.U j := rfl

@[simp] theorem StandardSyntomicCovering.toSyntomicCover_f
    {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardSyntomicCovering T) (j : Fin 𝒰.n) :
    𝒰.toSyntomicCover.f j = 𝒰.map j := rfl

/-- The underlying fixed-target family of a standard syntomic covering, viewed in `Over T`. -/
abbrev StandardSyntomicCovering.toOverFamily
    {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardSyntomicCovering T) :
    SemiRepresentableFamily.Over T :=
  ofArrows 𝒰.U 𝒰.map

@[simp] theorem StandardSyntomicCovering.toOverFamily_obj
    {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardSyntomicCovering T) (j : Fin 𝒰.n) :
    𝒰.toOverFamily.obj j = Over.mk (𝒰.map j) := rfl

/-- A standard syntomic covering of an affine scheme covers all points of the target by the union
of the set-theoretic images of its members. -/
theorem StandardSyntomicCovering.iUnion_range_eq_univ
    {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardSyntomicCovering T) :
    (⋃ j, Set.range (𝒰.map j)) = Set.univ := by
  ext t
  constructor
  · intro _
    simp
  · intro _
    simpa [Set.mem_iUnion] using 𝒰.cover t

/-- A standard syntomic covering presents a finite syntomic covering family in the canonical
syntomic precoverage on schemes. -/
theorem StandardSyntomicCovering.mem_syntomic_precoverage
    {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardSyntomicCovering T) :
    Presieve.ofArrows 𝒰.U 𝒰.map ∈ Scheme.bigSyntomicPrecoverage.coverings T :=
  by simpa using 𝒰.toSyntomicCover.mem_syntomic_precoverage

end

end AlgebraicGeometry
