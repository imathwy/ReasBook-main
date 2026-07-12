import Mathlib
import StacksProject_2024.Chap07.Definition_7_8_2
import StacksProject_2024.Chap34.Definition_34_6_1
import StacksProject_2024.Chap34.Definition_34_6_6
import StacksProject_2024.Chap34.Definition_34_6_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/- Semantic recall / owner check:
- `lean_leansearch` recalled the canonical scheme-site owners
  `Scheme.grothendieckTopology`, `Scheme.zariskiPrecoverage`, and `Scheme.Cover`.
- The nearby smooth analogue `Lemma_34_5_7` fixes the source-facing shape here: arbitrary indexed
  source coverings use the local owner `SyntomicCover T`, while coverings in the big syntomic site
  use the canonical owner `T.Cover Scheme.bigSyntomicPrecoverage`.
-/

variable {T : Scheme.{u}}

/-- Lemma 34.6.7 (1): an arbitrary syntomic covering of `T` admits a refinement by a covering in
the big syntomic site `Sch_{syntomic}`. -/
@[stacks 03X2]
theorem exists_siteCover_refining_syntomicCover
    (𝒰₀ : SyntomicCover.{v, u} T) :
    ∃ 𝒰 : T.Cover Scheme.bigSyntomicPrecoverage,
      Refines
        (SemiRepresentableFamily.Over.ofArrows 𝒰.X 𝒰.f)
        (SemiRepresentableFamily.Over.ofArrows 𝒰₀.X 𝒰₀.f) :=
  sorry

/-- Lemma 34.6.7 (2): a standard syntomic covering of an affine scheme `T` is tautologically
equivalent to a covering in the big syntomic site `Sch_{syntomic}`. -/
@[stacks 03X2]
theorem exists_siteCover_tautologicallyEquivalent_of_standardSyntomicCovering
    [IsAffine T] (𝒰₀ : StandardSyntomicCovering T) :
    ∃ 𝒰 : T.Cover Scheme.bigSyntomicPrecoverage,
      TautologicallyEquivalent
        (SemiRepresentableFamily.Over.ofArrows (fun j : Fin 𝒰₀.n ↦ 𝒰₀.U j) fun j ↦ 𝒰₀.map j)
        (SemiRepresentableFamily.Over.ofArrows 𝒰.X 𝒰.f) :=
  sorry

/-- Lemma 34.6.7 (3): a Zariski covering of `T` is tautologically equivalent to a covering in the
big syntomic site `Sch_{syntomic}`. -/
@[stacks 03X2]
theorem exists_siteCover_tautologicallyEquivalent_of_zariskiCover
    (𝒰₀ : T.Cover Scheme.zariskiPrecoverage) :
    ∃ 𝒰 : T.Cover Scheme.bigSyntomicPrecoverage,
      TautologicallyEquivalent
        (SemiRepresentableFamily.Over.ofArrows 𝒰₀.X 𝒰₀.f)
        (SemiRepresentableFamily.Over.ofArrows 𝒰.X 𝒰.f) :=
  sorry

end AlgebraicGeometry
