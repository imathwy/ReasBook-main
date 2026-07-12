import Mathlib
import StacksProject_2024.Chap17.Definition_17_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced `AlgebraicGeometry.IsFinite.toIsAffineHom`,
-- matching the source proof that finite morphisms are affine before applying affine higher
-- direct-image vanishing.

/-- Lemma 30.9.9 (1): let `f : X ⟶ Y` be a finite morphism of schemes, with `Y` locally
Noetherian, and let `\mathcal F` be a quasi-coherent `\mathcal O_X`-module. Then
`R^p f_* \mathcal F = 0` for every `p > 0`. -/
@[stacks 01Y6]
theorem finiteHigherDirectImageModule_isZero
    (f : X ⟶ Y) [IsFinite f] [IsLocallyNoetherian Y]
    [HasInjectiveResolutions X.Modules]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (p : ℕ) (hp : 0 < p) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived p).obj ℱ) := sorry

/-- Lemma 30.9.9 (2): let `f : X ⟶ Y` be a finite morphism of schemes, with `Y` locally
Noetherian, and let `\mathcal F` be a quasi-coherent coherent `\mathcal O_X`-module. Then
`f_* \mathcal F` is coherent. -/
@[stacks 01Y6]
theorem pushforward_obj_isCoherent_of_isFinite
    (f : X ⟶ Y) [IsFinite f] [IsLocallyNoetherian Y]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsCoherent] :
    ((Scheme.Modules.pushforward f).obj ℱ).IsCoherent := sorry

end AlgebraicGeometry.Scheme.Modules
