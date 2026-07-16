import StacksProject_2024.stacks_project.Chap29.Definition_29_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.Modules

section

variable {S X S' : Scheme} (f : X ⟶ S) (g : S' ⟶ S)

local notation "X'" => pullback f g
local notation "g'" => pullback.fst f g
local notation "f'" => pullback.snd f g

/-- Lemma 29.25.7 (1): let `f : X ⟶ S` be a morphism of schemes, let `ℱ` be a quasi-coherent
`\mathcal O_X`-module, let `g : S' ⟶ S` be a morphism of schemes, and write
`g' : pullback f g ⟶ X` for `pullback.fst f g`. If `ℱ` is flat over `S` at the image of
`x' : pullback f g`, then `g'^* ℱ` is flat over `S'` at `x'`. -/
@[stacks 01U8]
theorem pullback_flat_over_at_of_flat_over_at
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (x' : X')
    (hflat : flatOverAt ℱ f (g'.base x')) :
    flatOverAt (((g')^*).obj ℱ) f' x' := sorry

/-- Lemma 29.25.7 (2): in the same setup, if `ℱ` is flat over `S`, then the pullback
`g'^* ℱ` is flat over `S'`. -/
@[stacks 01U8]
theorem pullback_flat_over_of_flat_over
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (hflat : flatOver ℱ f) :
    flatOver (((g')^*).obj ℱ) f' := sorry

end

end Scheme.Modules

end AlgebraicGeometry
