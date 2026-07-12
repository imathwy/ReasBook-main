import Mathlib
import StacksProject_2024.Chap07.Definition_7_8_2
import StacksProject_2024.Chap34.Definition_34_7_1
import StacksProject_2024.Chap34.Definition_34_7_5
import StacksProject_2024.Chap34.Definition_34_7_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/- Semantic recall:
`lean_leansearch` surfaced the canonical fppf owners `Scheme.fppfPrecoverage` and
`Scheme.fppfTopology`; local Chapter 34 precedent now recalls Definition 34.7.6 directly through
those canonical owners, while Chapter 7 supplies the fixed-target family relations `Refines` and
`TautologicallyEquivalent`.
-/

variable {T : Scheme.{u}}

/-- Lemma 34.7.7 (1): every fppf covering of `T` admits a refinement by a covering family in the
big fppf site `Sch_fppf`. -/
@[stacks 03WX]
theorem exists_fppfSiteCover_refining_fppfCover
    (𝒰₀ : FppfCover.{u, v} T) :
    ∃ 𝒰 : SemiRepresentableFamily.Over T,
      IsCovering Scheme.fppfPrecoverage 𝒰 ∧
        Refines 𝒰 (SemiRepresentableFamily.Over.ofArrows 𝒰₀.X 𝒰₀.f) := sorry

/-- Lemma 34.7.7 (2): a standard fppf covering of an affine scheme `T` is tautologically
equivalent to a covering family in the big fppf site `Sch_fppf`. -/
@[stacks 03WX]
theorem exists_fppfSiteCover_tautologicallyEquivalent_standardFppfCover
    [IsAffine T] (𝒰₀ : StandardFppfCover T) :
    ∃ 𝒰 : SemiRepresentableFamily.Over T,
      IsCovering Scheme.fppfPrecoverage 𝒰 ∧
        TautologicallyEquivalent
          (SemiRepresentableFamily.Over.ofArrows (fun j : Fin 𝒰₀.n ↦ 𝒰₀.U j)
            fun j ↦ 𝒰₀.map j)
          𝒰 := sorry

/-- Lemma 34.7.7 (3): a Zariski covering of `T` is tautologically equivalent to a covering family
in the big fppf site `Sch_fppf`. -/
@[stacks 03WX]
theorem exists_fppfSiteCover_tautologicallyEquivalent_zariskiCover
    (𝒰₀ : T.Cover Scheme.zariskiPrecoverage) :
    ∃ 𝒰 : SemiRepresentableFamily.Over T,
      IsCovering Scheme.fppfPrecoverage 𝒰 ∧
        TautologicallyEquivalent
          (SemiRepresentableFamily.Over.ofArrows 𝒰₀.X 𝒰₀.f)
          𝒰 := sorry

end AlgebraicGeometry
