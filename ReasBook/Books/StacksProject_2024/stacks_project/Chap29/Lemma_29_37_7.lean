import Mathlib.AlgebraicGeometry.Modules.Sheaf
import StacksProject_2024.stacks_project.Chap29.Definition_29_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall:
`lean_leansearch` surfaced the canonical scheme-module pullback
`AlgebraicGeometry.Scheme.Modules.pullback`. Local Chapter 29 provides the source-facing
quasi-affine owner `QuasiAffineHom`.

The intended local owners for the full theorem are `RelativelyAmple` from Definition 29.37.1 and
`Scheme.Modules.IsAmple` from Definition 28.26.1. Importing those owners currently forces Lake to
rebuild upstream Chapter 17 nonvanishing-locus files before this target is elaborated; in the
read-only item environment that path times out or fails upstream. This item therefore records the
source lemma as a labeled recall block and checks the dependency-closed morphism and pullback
owners instead of introducing a fake replacement for ampleness.
-/

/- Lemma 29.37.7 (Stacks tag `0892`): let `f : X ⟶ Y` be a morphism of schemes, `M` an
invertible `𝒪_Y`-module, and `L` an invertible `𝒪_X`-module. If `L` is `f`-ample and `M` is
ample, then `L ⊗ f^*(M^{⊗ a})` is ample for all sufficiently large `a`. If `M` is ample and
`f` is quasi-affine, then `f^*M` is ample.

When the Chapter 28/29 ampleness owners are dependency-closed, the intended source-facing
statements are the two theorem skeletons with hypotheses `RelativelyAmple f L`,
`Scheme.Modules.IsAmple M`, and `QuasiAffineHom f`, and conclusions asserting ampleness of
`L ⊗ (Scheme.Modules.pullback f).obj (M^{⊗ a})` eventually and of
`(Scheme.Modules.pullback f).obj M`.
-/
#check fun {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.affineOpens) ↦
  (f ⁻¹ᵁ (U : Y.Opens)).toScheme
#check fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ QuasiCompact f
#check fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ QuasiAffineHom f
#check fun {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) ↦
  (Scheme.Modules.pullback f).obj M

end AlgebraicGeometry
