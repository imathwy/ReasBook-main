import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_20_3
import StacksProject_2024.stacks_project.Chap29.RelativeProjPresentation

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

-- Semantic recall: `lean_leansearch` surfaced the canonical absolute `AlgebraicGeometry.Proj`
-- owner and the scheme-morphism flatness owner `AlgebraicGeometry.Flat`; local project inspection
-- then verified the available relative-module flatness owner
-- `AlgebraicGeometry.Scheme.Modules.flatOver`. The current environment still does not
-- expose a scheme-side relative `Proj_S` construction or a packaged twist family `\mathcal O_X(d)`,
-- so Chapter 29 owns the minimal source-faithful presentation data for a fixed morphism
-- `p : X ⟶ S`, and this file adds the eventual-flatness hypothesis and its flatness
-- consequences.

variable {S X : Scheme.{u}} {p : X ⟶ S}

/-- The source hypothesis in Lemma 31.30.6 that the positive-degree pieces of the graded algebra
attached to a chosen relative `Proj` presentation are flat over `\mathcal O_S` in all
sufficiently large degrees. -/
@[stacks 0D4C]
class RelativeProjEventuallyFlatDegreePieces
    (P : RelativeProjPresentation p) : Prop where
  /-- A degree bound after which every graded piece is flat over `\mathcal O_S`. -/
  bound : ℕ
  /-- Every graded piece above the bound is flat over `\mathcal O_S`. -/
  isFlat_degreePiece (d : ℕ) (hd : bound ≤ d) : (P.degreePiece d).IsFlat

/-- A relative `Proj` eventual-flatness hypothesis exposes flatness of every sufficiently large
degree piece. -/
@[stacks 0D4C]
theorem RelativeProjEventuallyFlatDegreePieces.isFlat_degreePiece
    {P : RelativeProjPresentation p}
    (h : RelativeProjEventuallyFlatDegreePieces P) {d : ℕ} (hd : h.bound ≤ d) :
    (P.degreePiece d).IsFlat :=
  h.isFlat_degreePiece d hd

/-- Lemma 31.30.6 (1): let `S` be a scheme, let `\mathcal A` be a quasi-coherent graded
`\mathcal O_S`-algebra, and let `p : X = \underline{\mathrm{Proj}}_S(\mathcal A) ⟶ S` be the
relative `Proj` morphism. If the positive-degree pieces `\mathcal A_d` are flat over
`\mathcal O_S` for all sufficiently large `d`, then `p` is flat. -/
@[stacks 0D4C]
theorem relativeProj_flat_of_eventuallyFlatDegreePieces
    (P : RelativeProjPresentation p)
    (hflat : RelativeProjEventuallyFlatDegreePieces P) :
    Flat p := sorry

/-- A relative `Proj` eventual-flatness hypothesis exposes flatness of the structural morphism. -/
@[stacks 0D4C]
theorem RelativeProjEventuallyFlatDegreePieces.flat
    {P : RelativeProjPresentation p}
    (h : RelativeProjEventuallyFlatDegreePieces P) :
    Flat p :=
  relativeProj_flat_of_eventuallyFlatDegreePieces P h

/-- Lemma 31.30.6 (2): under the same hypotheses, every twist `\mathcal O_X(d)` of the relative
`Proj` presentation is flat over `S`. -/
@[stacks 0D4C]
theorem relativeProj_twistFlatOver_of_eventuallyFlatDegreePieces
    (P : RelativeProjPresentation p)
    (hflat : RelativeProjEventuallyFlatDegreePieces P)
    (d : ℤ) :
    (SheafOfModules.relativeModule (P.twist d) p.toShHom).IsFlat := sorry

/-- A relative `Proj` eventual-flatness hypothesis makes every twist in the chosen presentation
flat over the base. -/
@[stacks 0D4C]
theorem RelativeProjEventuallyFlatDegreePieces.flatOver_twist
    {P : RelativeProjPresentation p}
    (h : RelativeProjEventuallyFlatDegreePieces P) (d : ℤ) :
    (SheafOfModules.relativeModule (P.twist d) p.toShHom).IsFlat :=
  relativeProj_twistFlatOver_of_eventuallyFlatDegreePieces P h d

end AlgebraicGeometry.Scheme.Hom
