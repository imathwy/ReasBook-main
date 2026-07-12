import StacksProject_2024.Chap31.Definition_31_11_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

-- Semantic recall: the source-facing owner remains `Scheme.Modules.IsTorsionFree`, while the
-- supporting canonical pullback API is `Scheme.Modules.pullback`.

namespace IsTorsionFree

/-- Lemma 31.11.6: let `f : X ⟶ Y` be a flat morphism of integral schemes, and let `ℱ` be a
torsion free quasi-coherent `\mathcal O_Y`-module. Then `f^* ℱ` is a torsion free
quasi-coherent `\mathcal O_X`-module. -/
@[stacks 0AXV]
theorem pullback
    (f : X ⟶ Y) [Flat f] {ℱ : Y.Modules} [ℱ.IsQuasicoherent]
    (hℱ : IsTorsionFree ℱ) :
    IsTorsionFree ((f^*).obj ℱ) := by
  sorry

/-- Pullback along a flat morphism of integral schemes preserves torsion-free quasi-coherent
modules. -/
instance instIsTorsionFree_pullback
    (f : X ⟶ Y) [Flat f] {ℱ : Y.Modules} [ℱ.IsQuasicoherent] [hℱ : IsTorsionFree ℱ] :
    IsTorsionFree ((f^*).obj ℱ) :=
  hℱ.pullback f

end IsTorsionFree

end AlgebraicGeometry.Scheme.Modules
