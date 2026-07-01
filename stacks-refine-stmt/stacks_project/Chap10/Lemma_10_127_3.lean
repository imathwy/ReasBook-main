import Mathlib
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

universe u vJ uJ

section

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

-- Source/core/bridge triage:
-- * source-facing: the TFAE between finite presentation, preservation of filtered colimits by
--   `Hom_R(S, -)`, and stagewise factorization through a filtered colimit.
-- * core/canonical: `CommRingCat.preservesFilteredColimits_coyoneda` for
--   `Under.mk (CommRingCat.ofHom f)`.
-- * bridge/view: the factorization clause, which is the surjectivity part of the canonical
--   filtered-colimit comparison for the represented functor.

-- Proof sketch: the forward implication is the mathlib owner theorem
-- `CommRingCat.preservesFilteredColimits_coyoneda`. For the converse, preservation of filtered
-- colimits makes `Under.mk (CommRingCat.ofHom f)` finitely presentable; then apply the standard
-- finite-presentation recognition in `Under (CommRingCat.of R)`.
/-- A ring map `R → S` is of finite presentation if and only if the represented functor
`Hom_R(S, -)` preserves filtered colimits. -/
theorem finitePresentation_iff_preservesFilteredColimits_coyoneda :
    f.FinitePresentation ↔
      PreservesFilteredColimits (coyoneda.obj (.op (Under.mk (CommRingCat.ofHom f)))) := by
  constructor
  · intro hf
    simpa using
      (CommRingCat.preservesFilteredColimits_coyoneda
        (CommRingCat.of R) (Under.mk (CommRingCat.ofHom f)) hf)
  · sorry

-- Proof sketch: if `Hom_R(S, -)` preserves filtered colimits, then the canonical comparison map
-- from the colimit of the stagewise hom-sets to the hom-set into the colimit is bijective.
-- Surjectivity of that comparison map is exactly the assertion that every map into the colimit
-- comes from some stage.
/-- Preservation of filtered colimits by `Hom_R(S, -)` implies the filtered-colimit factorization
property. -/
theorem factorsThroughStage_of_preservesFilteredColimits_coyoneda
    (h :
      PreservesFilteredColimits (coyoneda.obj (.op (Under.mk (CommRingCat.ofHom f))))) :
    ∀ {J : Type uJ} [Category.{vJ} J] [IsFiltered J] (F : J ⥤ Under (CommRingCat.of R))
      (c : Cocone F) (_hc : IsColimit c) (g : Under.mk (CommRingCat.ofHom f) ⟶ c.pt),
        ∃ (j : J) (g' : Under.mk (CommRingCat.ofHom f) ⟶ F.obj j), g = g' ≫ c.ι.app j := sorry

-- Proof sketch: `(1) → (2)` is the canonical mathlib theorem that a finitely presented
-- `R`-algebra is finitely presentable in `Under R`, equivalently preservation of filtered
-- colimits by `Hom_R(S, -)`. `(2) → (3)` is surjectivity of the comparison map for filtered
-- colimits. For `(3) → (1)`, write `S` as a filtered colimit of finitely
-- presented `R`-algebras using Lemma `10.127.2`; apply the factorization hypothesis to the
-- identity of `S`, deduce that `S` is finitely presented over some finitely presented stage by
-- Lemma `10.6.2`, and then compose finite presentation back over `R`.
/-- Lemma 10.127.3: for a ring map `R → S`, the following are equivalent: `R → S` is of finite
presentation, `Hom_R(S, -)` preserves filtered colimits, and every morphism from `S` to a filtered
colimit of `R`-algebras factors through some stage. -/
theorem finitePresentation_tfae :
    List.TFAE
      [f.FinitePresentation,
        PreservesFilteredColimits (coyoneda.obj (.op (Under.mk (CommRingCat.ofHom f)))),
        ∀ {J : Type uJ} [Category.{vJ} J] [IsFiltered J] (F : J ⥤ Under (CommRingCat.of R))
          (c : Cocone F) (_hc : IsColimit c) (g : Under.mk (CommRingCat.ofHom f) ⟶ c.pt),
            ∃ (j : J) (g' : Under.mk (CommRingCat.ofHom f) ⟶ F.obj j), g = g' ≫ c.ι.app j] := sorry

end
