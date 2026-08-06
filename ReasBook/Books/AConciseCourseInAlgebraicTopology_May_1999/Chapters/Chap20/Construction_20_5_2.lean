import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Theorem_20_3_3
import Mathlib.Algebra.Group.Shrink

open CategoryTheory Limits
open scoped Manifold Topology

noncomputable section

universe u v

-- Semantic recall via `lean_leansearch` only surfaced generic colimit APIs, while local Chapter 20
-- precedent fixes `compactlySupportedCohomology`, the degreewise coefficient-homology owner
-- `singularHomologyWithCoefficients`, and
-- `exists_fundamentalClassAtSubspace_of_rOrientedManifold` as the
-- relevant owners. The current repository still lacks a canonical relative cap-product owner on
-- `H^p(M, M \ K)` and `H_n(M, M \ K)`, so this file formalizes Construction 20.5.2 from the
-- source-facing ingredients it actually uses: a compatible family of compact fundamental classes
-- together with the local cap-product maps evaluated on those classes.

section

variable {R : Type u} [CommRing R]
variable {π : Type u} [AddCommGroup π]
variable (Hcoh : PairCohomologyTheory π)
variable {n : ℕ}
variable {p : ℕ}
variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ V H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [Fact (Module.finrank ℝ V = n)]

/-- The relative top homology group of `M` supported at the compact subset `K`. -/
abbrev relativeTopHomologyAtCompact
    (R : Type u) [CommRing R] (n : ℕ) (M : Type u) [TopologicalSpace M]
    (K : TopologicalSpace.Compacts M) :=
  relativeTopHomologyGroup R n M (K : Set M)

/-- `η` is a fundamental class of `M` at the compact subset `K`. -/
abbrev isFundamentalClassAtCompact
    (R : Type u) [CommRing R] (n : ℕ) (M : Type u) [TopologicalSpace M]
    (K : TopologicalSpace.Compacts M) (η : relativeTopHomologyAtCompact R n M K) : Prop :=
  isFundamentalClassAtSubspace R n M (K : Set M) η

/-- Restriction in relative top homology along an inclusion of compact subsets. -/
abbrev relativeTopHomologyRestrictCompact
    (R : Type u) [CommRing R] (n : ℕ) (M : Type u) [TopologicalSpace M]
    {K L : TopologicalSpace.Compacts M} (h : K ⟶ L) :
    relativeTopHomologyAtCompact R n M L → relativeTopHomologyAtCompact R n M K :=
  relativeTopHomologyRestrict R n M (K : Set M) (L : Set M) h.le

/-- Theorem 20.3.3 supplies an `R`-fundamental class at each compact subset `K` of an oriented
manifold `M`. -/
theorem exists_orientedCompactFundamentalClass
    (o : ROrientedManifold R I n M) (K : TopologicalSpace.Compacts M) :
    ∃ η : relativeTopHomologyAtCompact R n M K,
      isFundamentalClassAtCompact R n M K η :=
  exists_fundamentalClassAtSubspace_of_rOrientedManifold o (K : Set M) K.isCompact

/-- The canonical `AddCommGrpCat` view of the global target `H_(n - p)(M; R)`, obtained by
forgetting the `R`-module structure on
`singularHomologyWithCoefficients R (TopCat.of M) (ModuleCat.of R R) (n - p)` and shrinking
universes to match the ambient cohomology category. -/
abbrev compactlySupportedPoincareDualityTarget
    (R : Type u) [CommRing R] [UnivLE.{u, v}]
    (M : Type u) [TopologicalSpace M] (n p : ℕ) : AddCommGrpCat.{v} :=
  AddCommGrpCat.of
    (Shrink.{v}
      (singularHomologyWithCoefficients R (TopCat.of.{u} M) (ModuleCat.of.{u} R R) (n - p)))

/-- A compatible family of compact fundamental classes for Construction 20.5.2. For each compact
subset `K ⊆ M`, the class `classAt K` is fundamental on `K`, and these classes agree under the
restriction maps for inclusions `K ⊆ L`. -/
structure CompactFundamentalClassFamily
    (o : ROrientedManifold R I n M) where
  classAt : (K : TopologicalSpace.Compacts M) → relativeTopHomologyAtCompact R n M K
  isFundamentalClassAt :
    ∀ K : TopologicalSpace.Compacts M,
      isFundamentalClassAtCompact R n M K (classAt K)
  restrict_eq :
    ∀ {K L : TopologicalSpace.Compacts M} (h : K ⟶ L),
      relativeTopHomologyRestrictCompact R n M h (classAt L) = classAt K

@[simp] theorem CompactFundamentalClassFamily.restrict
    {o : ROrientedManifold R I n M} (fundamentalClass : CompactFundamentalClassFamily o)
    {K L : TopologicalSpace.Compacts M} (h : K ⟶ L) :
    relativeTopHomologyRestrictCompact R n M h (fundamentalClass.classAt L) =
      fundamentalClass.classAt K :=
  fundamentalClass.restrict_eq h

/-- Construction 20.5.2 uses the local cap-with-fundamental-class maps
`D_K(-) = - ∩ [M]_K : H^p(M, M \ K; π) ⟶ H_(n - p)(M; R)`. In the current repository the
relative cap-product owner is still upstream, so this structure records the source-facing local
construction as a function of the compact fundamental class together with the required
restriction-compatibility. -/
structure CompactlySupportedLocalCapWithFundamentalClass
    {π : Type u} [AddCommGroup π]
    (Hcoh : PairCohomologyTheory π)
    (R : Type u) [CommRing R] [UnivLE.{u, v}]
    (M : Type u) [TopologicalSpace M] (n p : ℕ) where
  capWith :
    (K : TopologicalSpace.Compacts M) →
      relativeTopHomologyAtCompact R n M K →
        ((compactlySupportedCohomologyDiagram Hcoh (TopCat.of.{u} M) (p : ℤ)).obj K ⟶
          compactlySupportedPoincareDualityTarget R M n p)
  naturality :
    ∀ {K L : TopologicalSpace.Compacts M} (h : K ⟶ L)
      (ηK : relativeTopHomologyAtCompact R n M K)
      (ηL : relativeTopHomologyAtCompact R n M L),
        relativeTopHomologyRestrictCompact R n M h ηL = ηK →
          (compactlySupportedCohomologyDiagram Hcoh (TopCat.of.{u} M) (p : ℤ)).map h ≫
              capWith L ηL =
            capWith K ηK

/-- Specializing `naturality` to a compatible family of compact fundamental classes gives the
source-facing restriction identity for the local maps `D_K(-) = - ∩ [M]_K`. -/
theorem CompactlySupportedLocalCapWithFundamentalClass.naturality_compactFundamentalClass
    {π : Type u} [AddCommGroup π]
    {Hcoh : PairCohomologyTheory π}
    {R : Type u} [CommRing R] [UnivLE.{u, v}]
    {n p : ℕ}
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ V H} [I.Boundaryless]
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [Fact (Module.finrank ℝ V = n)]
    {o : ROrientedManifold R I n M}
    (localCap : CompactlySupportedLocalCapWithFundamentalClass Hcoh R M n p)
    (fundamentalClass : CompactFundamentalClassFamily o)
    {K L : TopologicalSpace.Compacts M} (h : K ⟶ L) :
    (compactlySupportedCohomologyDiagram Hcoh (TopCat.of.{u} M) (p : ℤ)).map h ≫
        localCap.capWith L (fundamentalClass.classAt L) =
      localCap.capWith K (fundamentalClass.classAt K) := by
  simpa using
    localCap.naturality h
      (fundamentalClass.classAt K)
      (fundamentalClass.classAt L)
      (fundamentalClass.restrict h)

/-- A compatible family of local compact-support duality morphisms for Construction 20.5.2 is a
natural transformation whose `K`-component is the local cap-with-`[M]_K` map
`D_K : H^p(M, M \ K; π) ⟶ H_(n - p)(M; R)`. -/
abbrev CompactlySupportedPoincareDualityFamily
    {π : Type u} [AddCommGroup π]
    (Hcoh : PairCohomologyTheory π)
    (R : Type u) [CommRing R] [UnivLE.{u, v}]
    (M : Type u) [TopologicalSpace M] (n p : ℕ) :=
  compactlySupportedCohomologyDiagram Hcoh (TopCat.of.{u} M) (p : ℤ) ⟶
    ((Functor.const (TopologicalSpace.Compacts M)).obj
      (compactlySupportedPoincareDualityTarget R M n p))

/-- The components of a compact-support duality family commute with the restriction maps coming
from inclusions `K ⊆ L`. -/
@[simp] theorem compactlySupportedPoincareDualityFamily_naturality
    {π : Type u} [AddCommGroup π]
    {Hcoh : PairCohomologyTheory π}
    {R : Type u} [CommRing R] [UnivLE.{u, v}]
    {M : Type u} [TopologicalSpace M] {n p : ℕ}
    (localMap : CompactlySupportedPoincareDualityFamily Hcoh R M n p)
    {K L : TopologicalSpace.Compacts M} (h : K ⟶ L) :
    (compactlySupportedCohomologyDiagram Hcoh (TopCat.of.{u} M) (p : ℤ)).map h ≫ localMap.app L =
      localMap.app K := by
  simpa using localMap.naturality h

/-- Evaluating the source-facing local cap-with-fundamental-class construction at a compatible
family of compact fundamental classes produces the natural family `K ↦ D_K` used in
Construction 20.5.2. -/
def compactlySupportedPoincareDualityFamily
    {π : Type u} [AddCommGroup π]
    (Hcoh : PairCohomologyTheory π)
    (R : Type u) [CommRing R] [UnivLE.{u, v}]
    (o : ROrientedManifold R I n M) (p : ℕ)
    (localCap : CompactlySupportedLocalCapWithFundamentalClass Hcoh R M n p)
    (fundamentalClass : CompactFundamentalClassFamily o) :
    CompactlySupportedPoincareDualityFamily Hcoh R M n p where
  app K := localCap.capWith K (fundamentalClass.classAt K)
  naturality := by
    intro K L h
    simpa using localCap.naturality_compactFundamentalClass fundamentalClass h

/-- Helper cocone for a preassembled family `K ↦ D_K`. This is the colimit-assembly step used by
Construction 20.5.2 after the local cap-product maps have been evaluated on compact fundamental
classes. -/
def compactlySupportedPoincareDualityCoconeOfFamily
    {π : Type u} [AddCommGroup π]
    (Hcoh : PairCohomologyTheory π)
    (R : Type u) [CommRing R] [UnivLE.{u, v}]
    (M : Type u) [TopologicalSpace M] (n p : ℕ)
    (localMap : CompactlySupportedPoincareDualityFamily Hcoh R M n p) :
    Cocone (compactlySupportedCohomologyDiagram Hcoh (TopCat.of.{u} M) (p : ℤ)) where
  pt := compactlySupportedPoincareDualityTarget R M n p
  ι := localMap

/-- Helper assembly for a preassembled family `K ↦ D_K`. -/
def compactlySupportedPoincareDualityMapOfFamily
    {π : Type u} [AddCommGroup π]
    (Hcoh : PairCohomologyTheory π)
    (R : Type u) [CommRing R] [UnivLE.{u, v}]
    (M : Type u) [TopologicalSpace M] (n p : ℕ)
    (localMap : CompactlySupportedPoincareDualityFamily Hcoh R M n p) :
    H_c^(p : ℤ)(TopCat.of.{u} M; Hcoh) ⟶
      compactlySupportedPoincareDualityTarget R M n p :=
  colimit.desc _ <|
    compactlySupportedPoincareDualityCoconeOfFamily Hcoh R M n p localMap

/-- The `K`-component of `compactlySupportedPoincareDualityMapOfFamily` is the chosen local
duality map `D_K`. -/
theorem colimit_ι_compactlySupportedPoincareDualityMapOfFamily
    {π : Type u} [AddCommGroup π]
    (Hcoh : PairCohomologyTheory π)
    (R : Type u) [CommRing R] [UnivLE.{u, v}]
    (M : Type u) [TopologicalSpace M] (n p : ℕ)
    (localMap : CompactlySupportedPoincareDualityFamily Hcoh R M n p)
    (K : TopologicalSpace.Compacts M) :
    colimit.ι (compactlySupportedCohomologyDiagram Hcoh (TopCat.of.{u} M) (p : ℤ)) K ≫
        compactlySupportedPoincareDualityMapOfFamily Hcoh R M n p localMap =
      localMap.app K := by
  simpa
      [compactlySupportedPoincareDualityMapOfFamily,
        compactlySupportedPoincareDualityCoconeOfFamily]
    using
      colimit.ι_desc
        (compactlySupportedPoincareDualityCoconeOfFamily Hcoh R M n p localMap) K

/-- Construction 20.5.2 packages the local cap-with-`[M]_K` maps `D_K(-) = - ∩ [M]_K` and a
compatible family of compact fundamental classes into a cocone over the compact-support
cohomology diagram. This is the source-facing cocone, while
`compactlySupportedPoincareDualityCoconeOfFamily` remains the bridge from a preassembled natural
family. -/
def compactlySupportedPoincareDualityCocone
    {π : Type u} [AddCommGroup π]
    (Hcoh : PairCohomologyTheory π)
    (R : Type u) [CommRing R] [UnivLE.{u, v}]
    (o : ROrientedManifold R I n M) (p : ℕ)
    (localCap : CompactlySupportedLocalCapWithFundamentalClass Hcoh R M n p)
    (fundamentalClass : CompactFundamentalClassFamily o) :
    Cocone (compactlySupportedCohomologyDiagram Hcoh (TopCat.of.{u} M) (p : ℤ)) where
  pt := compactlySupportedPoincareDualityTarget R M n p
  ι :=
    { app := fun K ↦ localCap.capWith K (fundamentalClass.classAt K)
      naturality := by
        intro K L h
        simpa using localCap.naturality_compactFundamentalClass fundamentalClass h }

/-- The `K`-component of `compactlySupportedPoincareDualityCocone` is the local cap-product map
evaluated on the chosen compact fundamental class `[M]_K`. -/
@[simp] theorem compactlySupportedPoincareDualityCocone_ι_app
    {π : Type u} [AddCommGroup π]
    (Hcoh : PairCohomologyTheory π)
    (R : Type u) [CommRing R] [UnivLE.{u, v}]
    (o : ROrientedManifold R I n M) (p : ℕ)
    (localCap : CompactlySupportedLocalCapWithFundamentalClass Hcoh R M n p)
    (fundamentalClass : CompactFundamentalClassFamily o)
    (K : TopologicalSpace.Compacts M) :
    (compactlySupportedPoincareDualityCocone Hcoh R o p localCap fundamentalClass).ι.app K =
      localCap.capWith K (fundamentalClass.classAt K) :=
  rfl

/-- Construction 20.5.2. Given the local cap-with-`[M]_K` maps and a compatible family of compact
fundamental classes, the compact-support duality map
`H_c^p(M; Hcoh) ⟶ H_(n - p)(M; R)` is obtained by the universal property of the colimit
defining compactly supported cohomology. -/
def compactlySupportedPoincareDualityMap
    {π : Type u} [AddCommGroup π]
    (Hcoh : PairCohomologyTheory π)
    (R : Type u) [CommRing R] [UnivLE.{u, v}]
    (o : ROrientedManifold R I n M) (p : ℕ)
    (localCap : CompactlySupportedLocalCapWithFundamentalClass Hcoh R M n p)
    (fundamentalClass : CompactFundamentalClassFamily o) :
    H_c^(p : ℤ)(TopCat.of.{u} M; Hcoh) ⟶
      compactlySupportedPoincareDualityTarget R M n p :=
  colimit.desc _ (compactlySupportedPoincareDualityCocone Hcoh R o p localCap fundamentalClass)

/-- The `K`-component of `compactlySupportedPoincareDualityMap` is the local cap-product map
evaluated on the chosen compact fundamental class `[M]_K`. -/
theorem colimit_ι_compactlySupportedPoincareDualityMap
    {π : Type u} [AddCommGroup π]
    (Hcoh : PairCohomologyTheory π)
    (R : Type u) [CommRing R] [UnivLE.{u, v}]
    (o : ROrientedManifold R I n M) (p : ℕ)
    (localCap : CompactlySupportedLocalCapWithFundamentalClass Hcoh R M n p)
    (fundamentalClass : CompactFundamentalClassFamily o)
    (K : TopologicalSpace.Compacts M) :
    colimit.ι (compactlySupportedCohomologyDiagram Hcoh (TopCat.of.{u} M) (p : ℤ)) K ≫
        compactlySupportedPoincareDualityMap Hcoh R o p localCap fundamentalClass =
      localCap.capWith K (fundamentalClass.classAt K) := by
  simpa [compactlySupportedPoincareDualityMap, compactlySupportedPoincareDualityCocone] using
    colimit.ι_desc (compactlySupportedPoincareDualityCocone Hcoh R o p localCap fundamentalClass)
      K

end
