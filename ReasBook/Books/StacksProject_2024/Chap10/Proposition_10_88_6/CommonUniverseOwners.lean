import Mathlib
import StacksProject_2024.Chap10.Lemma_10_11_1
import StacksProject_2024.Chap10.Lemma_10_11_4

-- Proof rescue support owners for Proposition 10.88.6.

open CategoryTheory
open CategoryTheory.Limits

universe u v w

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {M : Type (max v w)} [AddCommGroup M] [Module R M]

/-- Helper for Proposition 10.88.6: reindex the directed system along `ULift` so the index lives
in the same universe as the module stages. -/
noncomputable def lifted_index_diagram
    (F : I ⥤ ModuleCat.{max v w} R) :
    ULift.{max v w} I ⥤ ModuleCat.{max v w} R where
  obj i := F.obj i.down
  map {X Y} h :=
    F.map (homOfLE (show X.down ≤ Y.down from h.down.down))
  map_id X := by
    simpa using F.map_id X.down
  map_comp {X Y Z} h₁ h₂ := by
    let h₁' : X.down ≤ Y.down := show X.down ≤ Y.down from h₁.down.down
    let h₂' : Y.down ≤ Z.down := show Y.down ≤ Z.down from h₂.down.down
    simpa using
      F.map_comp (homOfLE h₁') (homOfLE h₂')

/-- Helper for Proposition 10.88.6: the chosen colimit cocone for `F` induces a cocone on the
lifted-index diagram with the same colimit point. -/
noncomputable def lifted_index_cocone
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M) :
    Cocone (lifted_index_diagram (R := R) F) where
  pt := ModuleCat.of R M
  ι :=
    { app := fun i ↦ colimit.ι F i.down ≫ c.hom
      naturality := by
        intro i j h
        let hij : i.down ≤ j.down := show i.down ≤ j.down from h.down.down
        -- Proof comment: naturality is exactly the original colimit cocone naturality, with the
        -- lifted index forgotten by `ULift.down`.
        apply ModuleCat.hom_ext
        ext x
        have hw :
            (colimit.ι F j.down).hom ((F.map (homOfLE hij)).hom x) =
              (colimit.ι F i.down).hom x := by
          simpa using
            LinearMap.congr_fun
              (congrArg ModuleCat.Hom.hom (colimit.w F (homOfLE hij))) x
        simpa [lifted_index_diagram, Category.assoc] using congrArg (c.hom.hom) hw }

/-- Helper for Proposition 10.88.6: the cocone on the lifted-index diagram is still colimiting
after descending cocones back along `ULift.down`. -/
noncomputable def common_universe_lifted_index_isColimit
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M) :
    IsColimit (lifted_index_cocone (R := R) (M := M) F c) := by
  let descendedCocone : Cocone (lifted_index_diagram (R := R) F) → Cocone F :=
    fun s ↦
      { pt := s.pt
        ι :=
          { app := fun i ↦ s.ι.app (ULift.up i)
            naturality := by
              intro i j h
              let hij : (ULift.up i : ULift.{max v w} I) ≤ ULift.up j := h.down.down
              -- Proof comment: forgetting the `ULift` index turns cocone naturality on the lifted
              -- diagram back into cocone naturality on `F`.
              simpa [lifted_index_diagram] using s.w (homOfLE hij) } }
  let hc := colimit.isColimit F
  refine
    { desc := fun s ↦ c.inv ≫ hc.desc (descendedCocone s)
      fac := ?_
      uniq := ?_ }
  · intro s i
    -- Proof comment: the lifted cocone leg is just the original colimit leg followed by `c.hom`,
    -- so the universal factorization descends after cancelling the isomorphism `c`.
    simpa [lifted_index_cocone, descendedCocone, Category.assoc] using
      hc.fac (descendedCocone s) i.down
  · intro s m hm
    have hm' : c.hom ≫ m = hc.desc (descendedCocone s) := by
      apply hc.hom_ext
      intro i
      -- Proof comment: both maps out of `colimit F` agree on every colimit leg, once we rewrite
      -- the lifted cocone condition at `ULift.up i`.
      have hs : colimit.ι F i ≫ c.hom ≫ m = s.ι.app (ULift.up i) := by
        simpa [lifted_index_cocone, Category.assoc] using hm (ULift.up i)
      have hfac : colimit.ι F i ≫ hc.desc (descendedCocone s) = s.ι.app (ULift.up i) := by
        simpa [descendedCocone] using hc.fac (descendedCocone s) i
      exact hs.trans hfac.symm
    calc
      m = c.inv ≫ c.hom ≫ m := by
        simpa [Category.assoc] using (c.inv_hom_id_assoc m).symm
      _ = c.inv ≫ hc.desc (descendedCocone s) := by rw [hm']
      _ = c.inv ≫ hc.desc (descendedCocone s) := rfl

/-- Helper for Proposition 10.88.6: after lifting the preorder index to the common universe,
any map from a finitely presented module into the chosen colimit cocone factors through one stage.
-/
theorem ulifted_factor_through_given_filtered_cocone_stage_of_finitePresentation
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    (P : ModuleCat.{max v w} R)
    [Module.FinitePresentation R P]
    (f : P ⟶ ModuleCat.of R M) :
    ∃ (i : I) (g : P ⟶ F.obj i), g ≫ (colimit.ι F i ≫ c.hom) = f := by
  -- Route correction: the colimit owner above is now explicit; the remaining blocker is only the
  -- universe alignment between `Module.FinitePresentation` and `IsFinitelyPresentable` for the
  -- source object `P`.
  -- TODO: package `P` in the exact common universe expected by
  -- `IsFinitelyPresentable.exists_hom_of_isColimit`, then descend the returned lifted stage.
  sorry

/-- Helper for Proposition 10.88.6: after lifting the preorder index to the common universe,
equality of two maps in the colimit descends to equality after one later transition map.
-/
theorem ulift_index_eventually_equal_of_hom_to_colimit_of_finite_module
    (F : I ⥤ ModuleCat.{max v w} R)
    {N : Type (max v w)} [AddCommGroup N] [Module R N] [Module.Finite R N]
    {i : I}
    (a b : ModuleCat.of R N ⟶ F.obj i)
    (h : a ≫ colimit.ι F i = b ≫ colimit.ι F i) :
    ∃ (j : I) (hij : i ≤ j), a ≫ F.map (homOfLE hij) = b ≫ F.map (homOfLE hij) := by
  -- Route correction: the remaining blocker is no longer the colimit owner itself, but the
  -- universe-safe handoff from the explicit lifted colimit cocone to the `colimit.ι`-based API of
  -- Lemma `10.11.1`.
  -- TODO: instantiate the lifted diagram as a common-universe `HasColimit`, compare its colimit
  -- legs to the original `colimit.ι F i`, and then descend the later lifted stage returned by
  -- `eventually_equal_of_hom_to_colimit_of_finite_module`.
  sorry

end
