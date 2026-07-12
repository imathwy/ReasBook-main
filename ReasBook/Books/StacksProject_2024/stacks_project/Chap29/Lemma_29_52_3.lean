import Mathlib
import StacksProject_2024.Chap05.Definition_5_20_1
import StacksProject_2024.Chap29.Definition_29_17_1
import StacksProject_2024.Chap29.Lemma_29_10_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

noncomputable section

-- Semantic recall / local precedent check:
-- `lean_leansearch` surfaced the scheme-morphism owner `LocallyOfFiniteType`.
-- Local files provide the dimension-function owner `IsDimensionFunction`, the scheme owner
-- `UniversallyCatenary`, and the residue-field algebra instance used by `Algebra.trdeg`.

/-- Lemma 29.52.3: let `S` be a locally Noetherian and universally catenary scheme, let
`δ : S → ℤ` be a dimension function, and let `f : X ⟶ S` be locally of finite type. Then the
function `x ↦ δ (f x) + trdeg_{κ(f x)} κ(x)` is a dimension function on `X`. -/
@[stacks 02JW]
theorem isDimensionFunction_relativeDimensionFunction
    {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [UniversallyCatenary S]
    [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ] :
    IsDimensionFunction
      (fun x : X ↦
        δ (f x) +
          (Cardinal.toNat
            (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) : ℤ)) := sorry

end

end AlgebraicGeometry
