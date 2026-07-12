import StacksProject_2024.Chap30.Lemma_30_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Semantic recall: `lean_leansearch` surfaced the canonical morphism owners `IsFinite`,
`Surjective`, `IsProper`, and the scheme-module pullback functor. Local Chapter 28/30 precedent
uses `Scheme.Modules.Invertible` and `Scheme.Modules.IsAmple` for ample invertible sheaves, and
`X.Over (Spec (CommRingCat.of R))` with `X ↘ Spec (CommRingCat.of R)` for schemes proper over
`R`. The Stacks tag evidence is consistent for tag `0B5V`. -/

variable {X Y : Scheme.{u}}
variable [MonoidalCategory X.Modules] [MonoidalCategory Y.Modules]

/-- Pullback of an invertible scheme module along a morphism of schemes is invertible. -/
instance instInvertibleSchemeModulePullback
    (f : Y ⟶ X) (L : X.Modules) [Invertible L] :
    Invertible ((Scheme.Modules.pullback f).obj L) := sorry

/-- Lemma 30.17.2: let `R` be a Noetherian ring, let `f : Y ⟶ X` be a finite surjective
morphism of schemes proper over `R`, and let `L` be an invertible `\mathcal O_X`-module. Then
`L` is ample if and only if `f^* L` is ample. -/
@[stacks 0B5V]
theorem isAmple_iff_pullback_isAmple_of_isFinite_surjective_properOver
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [X.Over (Spec (CommRingCat.of R))] [Y.Over (Spec (CommRingCat.of R))]
    [IsProper (X ↘ Spec (CommRingCat.of R))] [IsProper (Y ↘ Spec (CommRingCat.of R))]
    (f : Y ⟶ X) [f.IsOver (Spec (CommRingCat.of R))] [IsFinite f] [Surjective f]
    (L : X.Modules) [Invertible L] :
    IsAmple L ↔ IsAmple ((Scheme.Modules.pullback f).obj L) := sorry

end AlgebraicGeometry.Scheme.Modules
