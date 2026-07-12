import Mathlib
import StacksProject_2024.Chap10.Proposition_10_162_15_Nagata
import StacksProject_2024.Chap28.Definition_28_13_1
import StacksProject_2024.Chap28.Lemma_28_13_3
import StacksProject_2024.Chap28.Lemma_28_5_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check:
-- `AlgebraicGeometry.IsLocallyNoetherian` is the canonical scheme-side Noetherian owner, while
-- Definition `28.13.1` already introduced the source-facing affine-local owners
-- `UniversallyJapanese` and `Nagata`. This item therefore uses those owners directly rather than
-- reintroducing local aliases.

/-- Lemma 28.13.8: a scheme is Nagata exactly when it is locally Noetherian and universally
Japanese. -/
@[stacks 033Z]
theorem nagata_iff_isLocallyNoetherian_and_universallyJapanese (X : Scheme.{u}) :
    Nagata X ↔ IsLocallyNoetherian X ∧ UniversallyJapanese X := by
  constructor
  · intro hX
    refine ⟨isLocallyNoetherian_of_nagata X hX, ?_⟩
    rw [universallyJapanese_iff]
    intro x
    rcases (nagata_iff X).1 hX x with ⟨U, hxU, hU⟩
    refine ⟨U, hxU, ?_⟩
    exact (nagataRing_iff_universallyJapaneseRing_and_isNoetherianRing.1 hU).1
  · rintro ⟨hX_noetherian, hX_universallyJapanese⟩
    have hX_noetherian' :
        ∀ U : X.affineOpens, IsNoetherianRing (Γ(X, U)) :=
      (AlgebraicGeometry.isLocallyNoetherian_iff_forall_isNoetherianRing_sections_affineOpen X).1
        hX_noetherian
    rw [nagata_iff]
    intro x
    rcases (universallyJapanese_iff X).1 hX_universallyJapanese x with ⟨U, hxU, hU⟩
    refine ⟨U, hxU, ?_⟩
    exact
      (nagataRing_iff_universallyJapaneseRing_and_isNoetherianRing).2 ⟨hU, hX_noetherian' U⟩

/-- A Nagata scheme is universally Japanese. -/
theorem universallyJapanese_of_nagata (X : Scheme.{u}) (hX : Nagata X) :
    UniversallyJapanese X :=
  (nagata_iff_isLocallyNoetherian_and_universallyJapanese X).1 hX |>.2

/-- A Nagata scheme is locally Noetherian. -/
instance instIsLocallyNoetherianOfNagata (X : Scheme.{u}) [Nagata X] :
    IsLocallyNoetherian X :=
  isLocallyNoetherian_of_nagata X inferInstance

/-- A Nagata scheme is universally Japanese. -/
instance instUniversallyJapaneseOfNagata (X : Scheme.{u}) [Nagata X] :
    UniversallyJapanese X :=
  universallyJapanese_of_nagata X inferInstance

end AlgebraicGeometry.Scheme
