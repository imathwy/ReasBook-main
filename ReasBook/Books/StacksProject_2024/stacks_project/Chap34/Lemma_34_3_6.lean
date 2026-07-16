import Mathlib
import StacksProject_2024.stacks_project.Chap07.Definition_7_8_2
import StacksProject_2024.stacks_project.Chap34.Definition_34_3_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` returned the canonical Zariski-site owners
-- `Scheme.zariskiPretopology` and `Scheme.zariskiPrecoverage`; local Chapter 7 precedent packages
-- fixed-target covering families by `SemiRepresentableFamily.Over` together with `IsCovering` and
-- `TautologicallyEquivalent`, while `Over.post` and `SemiRepresentableFamily.map` provide the
-- canonical bridge from a site covering family to its image in `Scheme`.

namespace BigZariskiSite

variable (X : BigZariskiSite.{u, v}) {T : X}

/-- Lemma 34.3.6: every Zariski covering of the scheme underlying an object `T` of a big Zariski
site is tautologically equivalent to the image under `toScheme` of some covering family of `T`
in the site. -/
@[stacks 03WV]
theorem exists_siteCoveringFamily_tautologicallyEquivalent_zariskiCovering
    (𝒰 : (X.toScheme.obj T).OpenCover) :
    ∃ 𝒱 : SemiRepresentableFamily.Over T,
      IsCovering X.pretopology.toPrecoverage 𝒱 ∧
        TautologicallyEquivalent
          (ofArrows 𝒰.X 𝒰.f)
          ((SemiRepresentableFamily.map (Over.post X.toScheme)).obj 𝒱) := sorry

end BigZariskiSite

end AlgebraicGeometry
