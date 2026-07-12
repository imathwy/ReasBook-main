import Mathlib
import StacksProject_2024.Chap07.Definition_7_8_2
import StacksProject_2024.Chap34.Definition_34_4_1
import StacksProject_2024.Chap34.Definition_34_5_1
import StacksProject_2024.Chap34.Definition_34_5_6
import StacksProject_2024.Chap34.Definition_34_5_5

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall / owner check:
- `lean_leansearch` surfaced the canonical cover constructor `Scheme.Cover.mkOfCovers` and the
  precoverage bridge `Scheme.ofArrows_mem_precoverage_iff`.
- The local Chapter 34 source-facing owners are `Scheme.SmoothCovering` for arbitrary indexed
  smooth coverings and `StandardSmoothCovering` for affine standard smooth coverings.
- The set-theoretic choice of a small site from Definition 34.5.6 is therefore expressed through
  the canonical smooth-cover owner `T.Cover Scheme.bigSmoothPrecoverage`; the generic bridge
  `Scheme.Cover.toFamilyOver` gives the Chapter 7 fixed-target family owner
  `SemiRepresentableFamily.Over T` for refinement and tautological equivalence.
-/

variable {T : Scheme.{u}}

/-- Lemma 34.5.7 (1): an arbitrary smooth covering of `T` admits a refinement by a canonical
smooth-site covering of `T`. -/
@[stacks 03WZ]
theorem exists_siteCover_refining_smoothCovering
    (𝒰₀ : SemiRepresentableFamily.Over T) (h𝒰₀ : Scheme.SmoothCovering 𝒰₀.obj) :
    ∃ 𝒰 : Scheme.Cover Scheme.bigSmoothPrecoverage T,
      Refines (Scheme.Cover.toFamilyOver 𝒰) 𝒰₀ :=
  sorry

/-- Lemma 34.5.7 (2): a standard smooth covering of an affine scheme is tautologically equivalent
to a canonical smooth-site covering of that scheme. -/
@[stacks 03WZ]
theorem exists_siteCover_tautologicallyEquivalent_of_standardSmoothCovering
    {T : Scheme.{u}} [IsAffine T] (𝒰₀ : StandardSmoothCovering T) :
    ∃ 𝒰 : Scheme.Cover Scheme.bigSmoothPrecoverage T,
      TautologicallyEquivalent 𝒰₀.toOverFamily (Scheme.Cover.toFamilyOver 𝒰) :=
  sorry

/-- Lemma 34.5.7 (3): a Zariski covering of `T` is tautologically equivalent to a canonical
smooth-site covering of `T`. -/
@[stacks 03WZ]
theorem exists_siteCover_tautologicallyEquivalent_of_zariskiCover
    (𝒰₀ : Scheme.Cover Scheme.zariskiPrecoverage T) :
    ∃ 𝒰 : Scheme.Cover Scheme.bigSmoothPrecoverage T,
      TautologicallyEquivalent (Scheme.Cover.toFamilyOver 𝒰₀) (Scheme.Cover.toFamilyOver 𝒰) :=
  sorry

end AlgebraicGeometry
