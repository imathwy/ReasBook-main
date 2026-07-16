import StacksProject_2024.stacks_project.Chap07.Definition_7_8_2
import StacksProject_2024.stacks_project.Chap34.Definition_34_8_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry
namespace BigPhSite

-- Semantic recall: `lean_leansearch` surfaced `GrothendieckTopology.toPrecoverage` and
-- `Scheme.Cover` as site-cover owners; local Chapter 34 precedent uses
-- `SemiRepresentableFamily.Over` with `IsCovering`, `Refines`, and
-- `TautologicallyEquivalent` for source-facing comparisons of covering families.

variable (Schph : BigPhSite.{u, v}) {T : Schph}

/-- Lemma 34.8.10 (1): every ph covering of the scheme underlying an object `T` of a big ph
site admits a refinement by a covering family of `T` in the site. -/
@[stacks 0DBK]
theorem exists_siteCover_refining_phCovering
    {ι : Type u} (X : ι → Scheme.{u}) (π : ∀ i, X i ⟶ Schph.toScheme.obj T)
    (hπ : PhCovering X π) :
    ∃ 𝒱 : SemiRepresentableFamily.Over T,
      IsCovering Schph.pretopology.toPrecoverage 𝒱 ∧
        Refines
          ((SemiRepresentableFamily.map (Over.post Schph.toScheme)).obj 𝒱)
          (ofArrows X π) := sorry

/-- Lemma 34.8.10 (2): a standard ph covering of the scheme underlying an object `T` of a big ph
site is tautologically equivalent to a covering family of `T` in the site. -/
@[stacks 0DBK]
theorem exists_siteCover_tautologicallyEquivalent_standardPhCovering
    [IsAffine (Schph.toScheme.obj T)] (𝒰₀ : StandardPhCovering (Schph.toScheme.obj T)) :
    ∃ 𝒱 : SemiRepresentableFamily.Over T,
      IsCovering Schph.pretopology.toPrecoverage 𝒱 ∧
        TautologicallyEquivalent
          (ofArrows (fun j : Fin 𝒰₀.m ↦ 𝒰₀.obj j) (fun j ↦ 𝒰₀.map j))
          ((SemiRepresentableFamily.map (Over.post Schph.toScheme)).obj 𝒱) := sorry

/-- Lemma 34.8.10 (3): a Zariski covering of the scheme underlying an object `T` of a big ph
site is tautologically equivalent to a covering family of `T` in the site. -/
@[stacks 0DBK]
theorem exists_siteCover_tautologicallyEquivalent_zariskiCovering
    (𝒰₀ : (Schph.toScheme.obj T).OpenCover) :
    ∃ 𝒱 : SemiRepresentableFamily.Over T,
      IsCovering Schph.pretopology.toPrecoverage 𝒱 ∧
        TautologicallyEquivalent
          (ofArrows 𝒰₀.X 𝒰₀.f)
          ((SemiRepresentableFamily.map (Over.post Schph.toScheme)).obj 𝒱) := sorry

end BigPhSite
end AlgebraicGeometry
