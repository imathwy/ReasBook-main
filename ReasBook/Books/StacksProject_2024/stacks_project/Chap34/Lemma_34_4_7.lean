import Mathlib
import StacksProject_2024.stacks_project.Chap07.Definition_7_8_2
import StacksProject_2024.stacks_project.Chap34.Definition_34_4_1
import StacksProject_2024.stacks_project.Chap34.Definition_34_4_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` returned the canonical site owners
-- `Scheme.etalePretopology` and `Scheme.zariskiTopology_le_etaleTopology`. Local Chapter 7
-- precedent packages source-facing covering-family comparisons by `SemiRepresentableFamily.Over`
-- together with `Refines` and `TautologicallyEquivalent`, while Definition 34.4.1 already fixes
-- the site-side owner as `Scheme.Cover Scheme.etalePrecoverage`.

/-- Lemma 34.4.7 (1): every étale covering of `T` admits a refinement by a covering family in the
canonical big étale site `Scheme.etalePretopology`. -/
@[stacks 03WW]
theorem exists_etaleCoveringFamily_refining_etaleCovering
    {T : Scheme.{u}} (𝒰 : Scheme.Cover Scheme.etalePrecoverage T) :
    ∃ 𝒱 : Scheme.Cover Scheme.etalePrecoverage T,
      Refines 𝒱.toFamilyOver 𝒰.toFamilyOver := sorry

/-- Lemma 34.4.7 (2): a standard étale covering is tautologically equivalent to a covering family
in the canonical big étale site `Scheme.etalePretopology`. -/
@[stacks 03WW]
theorem exists_etaleCoveringFamily_tautologicallyEquivalent_standardEtaleCover
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardEtaleCover T) :
    ∃ 𝒱 : Scheme.Cover Scheme.etalePrecoverage T,
      TautologicallyEquivalent 𝒰.toFamilyOver 𝒱.toFamilyOver := sorry

/-- Lemma 34.4.7 (3): a Zariski covering family of `T` is tautologically equivalent to a covering
family in the canonical big étale site `Scheme.etalePretopology`. -/
@[stacks 03WW]
theorem exists_etaleCoveringFamily_tautologicallyEquivalent_zariskiCovering
    {T : Scheme.{u}} (𝒰 : Scheme.Cover Scheme.zariskiPrecoverage T) :
    ∃ 𝒱 : Scheme.Cover Scheme.etalePrecoverage T,
      TautologicallyEquivalent 𝒰.toFamilyOver 𝒱.toFamilyOver := sorry

end AlgebraicGeometry
