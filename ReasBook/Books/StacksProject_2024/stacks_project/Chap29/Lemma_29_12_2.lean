import Mathlib
import Mathlib.AlgebraicGeometry.Morphisms.Constructors
import StacksProject_2024.stacks_project.Chap29.Definition_29_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical morphism owner `IsAffineHom` and
-- the relative diagonal `pullback.diagonal`; Definition 29.12.1 already provides the source-facing
-- nonvanishing-open and family surfaces used here.

section

variable {X : Scheme.{u}} {ι : Type v}

local notation "ModX" => X.Modules

/-- If a fixed family of invertible `\mathcal O_X`-modules provides affine nonvanishing opens at
every point, then the diagonal of `X` is affine. -/
theorem isAffineHom_diagonal_of_affineNonvanishingFamily
    (L : ι → ModX)
    [∀ i : ι, Scheme.Modules.Invertible (L i)]
    [AffineNonvanishingFamily L] :
    IsAffineHom (pullback.diagonal (terminal.from X)) := sorry

/-- Lemma 29.12.2: if every point of a scheme lies in an affine nonvanishing open `X_s`
attached to a global section of an invertible `\mathcal O_X`-module, then the diagonal of `X`
is an affine morphism. -/
@[stacks 0FXS]
theorem isAffineHom_diagonal_of_exists_affine_nonvanishing_open
    (hX : ∀ x : X,
      ∃ (L : ModX) (_ : Scheme.Modules.Invertible L) (s : L.sections) (U : X.Opens),
        x ∈ U ∧ IsAffineOpen U ∧
          U = RingedSpace.sectionNonvanishingOpen X.toRingedSpace L s) :
    IsAffineHom (pullback.diagonal (terminal.from X)) := sorry

end

end AlgebraicGeometry
