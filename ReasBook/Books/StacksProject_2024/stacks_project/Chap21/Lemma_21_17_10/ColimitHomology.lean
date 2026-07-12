import Mathlib.Algebra.Homology.GrothendieckAbelian
import StacksProject_2024.Chap18.Lemma_18_14_2
import StacksProject_2024.Chap18.RingedSiteModuleCategory

open CategoryTheory CategoryTheory.Limits
open CochainComplex

noncomputable section

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J CommRingCat.{u})
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]

local notation "Mod" => ringedSiteModuleCategory J 𝒪

/-- Helper for Lemma 21.17.10: the module category `Mod(𝒪)` on a ringed site has exact
filtered colimits, so the sequential colimit functor preserves homology. -/
local instance ringedSiteModule_ab5 : AB5 Mod := by
  infer_instance

/-- Helper for Lemma 21.17.10: AB5 on `Mod(𝒪)` supplies exact sequential colimits. -/
local instance ringedSiteModule_hasExactSequentialColimits :
    HasExactColimitsOfShape ℕ Mod := by
  let _ : AB5OfSize.{0, 0} Mod := AB5OfSize_shrink (C := Mod)
  infer_instance

/-- Helper for Lemma 21.17.10: the sequential colimit functor on `Mod(𝒪)` preserves
homology because sequential colimits are exact. -/
local instance ringedSiteModule_sequentialColim_preservesHomology :
    ((colim : (ℕ ⥤ Mod) ⥤ Mod).PreservesHomology) := by
  let F : (ℕ ⥤ Mod) ⥤ Mod := colim
  letI : PreservesFiniteLimits F := inferInstance
  letI : PreservesFiniteColimits F := inferInstance
  exact CategoryTheory.Functor.preservesHomologyOfExact F

/-- Helper for Lemma 21.17.10: the previous differential in a sequential diagram of cochain
complexes forms a natural transformation on the degreewise module diagrams. -/
private def prev_d_natTrans
    (F : ℕ ⥤ CochainComplex Mod ℤ) (i : ℤ) :
    F ⋙ HomologicalComplex.eval Mod (ComplexShape.up ℤ) (i - 1) ⟶
      F ⋙ HomologicalComplex.eval Mod (ComplexShape.up ℤ) i where
  app n := (F.obj n).d (i - 1) i
  naturality _ _ f := by
    -- Naturality is exactly commutativity of the differential with a chain map.
    simpa using (F.map f).comm (i - 1) i

/-- Helper for Lemma 21.17.10: the next differential in a sequential diagram of cochain
complexes forms a natural transformation on the degreewise module diagrams. -/
private def next_d_natTrans
    (F : ℕ ⥤ CochainComplex Mod ℤ) (i : ℤ) :
    F ⋙ HomologicalComplex.eval Mod (ComplexShape.up ℤ) i ⟶
      F ⋙ HomologicalComplex.eval Mod (ComplexShape.up ℤ) (i + 1) where
  app n := (F.obj n).d i (i + 1)
  naturality _ _ f := by
    -- This is the same naturality statement for the adjacent differential.
    simpa using (F.map f).comm i (i + 1)

/-- Helper for Lemma 21.17.10: the consecutive degree differentials in the functor category still
compose to zero. -/
private theorem degree_d_comp_eq_zero
    (F : ℕ ⥤ CochainComplex Mod ℤ) (i : ℤ) :
    prev_d_natTrans (𝒪 := 𝒪) F i ≫ next_d_natTrans (𝒪 := 𝒪) F i = 0 := by
  sorry

/-- Helper for Lemma 21.17.10: the degree-`i` short complex attached to a sequential diagram of
cochain complexes, formed inside the functor category of module diagrams. -/
private def degree_shortComplex
    (F : ℕ ⥤ CochainComplex Mod ℤ) (i : ℤ) :
    ShortComplex (ℕ ⥤ Mod) :=
  ShortComplex.mk
    (prev_d_natTrans (𝒪 := 𝒪) F i)
    (next_d_natTrans (𝒪 := 𝒪) F i)
    (degree_d_comp_eq_zero (𝒪 := 𝒪) F i)

/-- Helper for Lemma 21.17.10: evaluating the functor-category degree-`i` short complex at a
stage recovers the ordinary degree-`i` short complex of that stage. -/
private def degree_shortComplex_app_iso
    (F : ℕ ⥤ CochainComplex Mod ℤ) (i : ℤ) (n : ℕ) :
    (degree_shortComplex (𝒪 := 𝒪) F i).map ((_root_.CategoryTheory.evaluation ℕ Mod).obj n) ≅
      (F.obj n).sc i :=
  (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)) ≪≫
    ((F.obj n).isoSc' (i := i - 1) (j := i) (k := i + 1)
      (CochainComplex.prev ℤ i) (CochainComplex.next ℤ i)).symm

/-- Helper for Lemma 21.17.10: the first `mapShortComplex` compatibility condition for the
sequential degree-`i` short complex is the canonical colimit relation for the previous
differential. -/
private theorem degree_shortComplex_colimit_map_prev
    (F : ℕ ⥤ CochainComplex Mod ℤ) (i : ℤ) (n : ℕ) :
    colimit.ι (degree_shortComplex (𝒪 := 𝒪) F i).X₁ n ≫
        colim.map (prev_d_natTrans (𝒪 := 𝒪) F i) =
      (degree_shortComplex (𝒪 := 𝒪) F i).f.app n ≫
        colimit.ι (degree_shortComplex (𝒪 := 𝒪) F i).X₂ n := by
  -- This is exactly `colimit.ι_map` after unfolding the chosen short-complex structure map.
  simpa [degree_shortComplex] using (colimit.ι_map (prev_d_natTrans (𝒪 := 𝒪) F i) n)

/-- Helper for Lemma 21.17.10: the second `mapShortComplex` compatibility condition for the
sequential degree-`i` short complex is the canonical colimit relation for the next differential. -/
private theorem degree_shortComplex_colimit_map_next
    (F : ℕ ⥤ CochainComplex Mod ℤ) (i : ℤ) (n : ℕ) :
    colimit.ι (degree_shortComplex (𝒪 := 𝒪) F i).X₂ n ≫
        colim.map (next_d_natTrans (𝒪 := 𝒪) F i) =
      (degree_shortComplex (𝒪 := 𝒪) F i).g.app n ≫
        colimit.ι (degree_shortComplex (𝒪 := 𝒪) F i).X₃ n := by
  -- This is the same `ι_map` identity for the second short-complex morphism.
  simpa [degree_shortComplex] using (colimit.ι_map (next_d_natTrans (𝒪 := 𝒪) F i) n)

/-- Helper for Lemma 21.17.10: evaluating the chosen sequential colimit cocone at degree `i`
gives the canonical cocone on the degree-`i` module diagram. -/
private def colimit_degree_term_cocone
    (F : ℕ ⥤ CochainComplex Mod ℤ) [HasColimit F] (i : ℤ) :
    Cocone (F ⋙ HomologicalComplex.eval Mod (ComplexShape.up ℤ) i) :=
  (HomologicalComplex.eval Mod (ComplexShape.up ℤ) i).mapCocone (colimit.cocone F)

/-- Helper for Lemma 21.17.10: evaluation preserves the chosen sequential colimit, so the
degree-`i` evaluated cocone is colimiting. -/
private def colimit_degree_term_isColimit
    (F : ℕ ⥤ CochainComplex Mod ℤ) [HasColimit F] (i : ℤ) :
    IsColimit (colimit_degree_term_cocone (𝒪 := 𝒪) F i) :=
  Limits.isColimitOfPreserves
    (HomologicalComplex.eval Mod (ComplexShape.up ℤ) i)
    (colimit.isColimit F)

/-- Helper for Lemma 21.17.10: the colimit of the degree-`i` terms is canonically the degree-`i`
term of the colimit complex. -/
private noncomputable def colimit_degree_term_iso
    (F : ℕ ⥤ CochainComplex Mod ℤ) [HasColimit F] (i : ℤ) :
    colimit (F ⋙ HomologicalComplex.eval Mod (ComplexShape.up ℤ) i) ≅
      (colimit F).X i :=
  ((colimit_degree_term_isColimit (𝒪 := 𝒪) F i).coconePointUniqueUpToIso
    (colimit.isColimit (F ⋙ HomologicalComplex.eval Mod (ComplexShape.up ℤ) i))).symm

/- Helper for Lemma 21.17.10: on each cocone leg, the degreewise colimit comparison is the
canonical degree-`i` map into the colimit complex. -/
omit [HasBinaryProducts C] [HasSheafify J AddCommGrpCat]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)] in
private theorem colimit_degree_term_iso_hom_ι
    (F : ℕ ⥤ CochainComplex Mod ℤ) [HasColimit F] (i : ℤ) (n : ℕ) :
    colimit.ι (F ⋙ HomologicalComplex.eval Mod (ComplexShape.up ℤ) i) n ≫
        (colimit_degree_term_iso (𝒪 := 𝒪) F i).hom =
      (colimit.ι F n).f i := by
  let e :
      (colimit F).X i ≅
        colimit (F ⋙ HomologicalComplex.eval Mod (ComplexShape.up ℤ) i) :=
    (colimit_degree_term_isColimit (𝒪 := 𝒪) F i).coconePointUniqueUpToIso
      (colimit.isColimit (F ⋙ HomologicalComplex.eval Mod (ComplexShape.up ℤ) i))
  have h :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit_degree_term_isColimit (𝒪 := 𝒪) F i)
      (colimit.isColimit (F ⋙ HomologicalComplex.eval Mod (ComplexShape.up ℤ) i)) n
  -- Compose the cocone-leg identity with the inverse comparison to recover the chosen direction.
  simpa [colimit_degree_term_iso, colimit_degree_term_cocone, e] using
    (congrArg (fun f ↦ f ≫ e.inv) h).symm

/-- Helper for Lemma 21.17.10: the degreewise colimit comparison intertwines the previous
differential with the colimit of the previous-differential natural transformation. -/
private theorem colimit_degree_term_iso_prev_comm
    (F : ℕ ⥤ CochainComplex Mod ℤ) [HasColimit F] (i : ℤ) :
    (colimit_degree_term_iso (𝒪 := 𝒪) F (i - 1)).hom ≫ (colimit F).d (i - 1) i =
      colim.map (prev_d_natTrans (𝒪 := 𝒪) F i) ≫
        (colimit_degree_term_iso (𝒪 := 𝒪) F i).hom := by
  sorry

/-- Helper for Lemma 21.17.10: the degreewise colimit comparison intertwines the next
differential with the colimit of the next-differential natural transformation. -/
private theorem colimit_degree_term_iso_next_comm
    (F : ℕ ⥤ CochainComplex Mod ℤ) [HasColimit F] (i : ℤ) :
    (colimit_degree_term_iso (𝒪 := 𝒪) F i).hom ≫ (colimit F).d i (i + 1) =
      colim.map (next_d_natTrans (𝒪 := 𝒪) F i) ≫
        (colimit_degree_term_iso (𝒪 := 𝒪) F (i + 1)).hom := by
  sorry

/-- Helper for Lemma 21.17.10: the canonical colimit short complex of the sequential degree-`i`
surface identifies with the degree-`i` short complex of the colimit complex. -/
private noncomputable def colimit_degree_shortComplex_iso
    (F : ℕ ⥤ CochainComplex Mod ℤ) [HasColimit F] (i : ℤ) :
    colim.mapShortComplex (degree_shortComplex (𝒪 := 𝒪) F i)
      (colimit.isColimit _)
      (colimit.cocone _)
      (colimit.cocone _)
      (colim.map (prev_d_natTrans (𝒪 := 𝒪) F i))
      (colim.map (next_d_natTrans (𝒪 := 𝒪) F i))
      (degree_shortComplex_colimit_map_prev (𝒪 := 𝒪) F i)
      (degree_shortComplex_colimit_map_next (𝒪 := 𝒪) F i) ≅
        (colimit F).sc i :=
  (ShortComplex.isoMk
      (colimit_degree_term_iso (𝒪 := 𝒪) F (i - 1))
      (colimit_degree_term_iso (𝒪 := 𝒪) F i)
      (colimit_degree_term_iso (𝒪 := 𝒪) F (i + 1))
      (colimit_degree_term_iso_prev_comm (𝒪 := 𝒪) F i)
      (colimit_degree_term_iso_next_comm (𝒪 := 𝒪) F i)) ≪≫
    ((colimit F).isoSc' (i := i - 1) (j := i) (k := i + 1)
      (CochainComplex.prev ℤ i) (CochainComplex.next ℤ i)).symm

/-- Helper for Lemma 21.17.10: evaluating the functor-category degree-`i` short complex at each
stage defines the corresponding sequential diagram of ordinary short complexes. -/
private def degree_shortComplex_evalFunctor
    (F : ℕ ⥤ CochainComplex Mod ℤ) (i : ℤ) :
    ℕ ⥤ ShortComplex Mod where
  obj n := (degree_shortComplex (𝒪 := 𝒪) F i).map ((_root_.CategoryTheory.evaluation ℕ Mod).obj n)
  map f := (degree_shortComplex (𝒪 := 𝒪) F i).mapNatTrans ((_root_.CategoryTheory.evaluation ℕ Mod).map f)
  map_id n := by
    -- Each component of the identity map is definitionally the identity on the evaluated terms.
    ext <;> simp
  map_comp f g := by
    -- Evaluation of a composite morphism agrees componentwise with successive evaluations.
    ext <;> simp

/-- Helper for Lemma 21.17.10: the evaluated degree-`i` short complex is naturally the ordinary
degree-`i` short-complex diagram of the stages. -/
private noncomputable def degree_shortComplex_app_natIso
    (F : ℕ ⥤ CochainComplex Mod ℤ) (i : ℤ) :
    degree_shortComplex_evalFunctor (𝒪 := 𝒪) F i ≅
      F ⋙ HomologicalComplex.shortComplexFunctor Mod (ComplexShape.up ℤ) i :=
  NatIso.ofComponents
    (fun n ↦ degree_shortComplex_app_iso (𝒪 := 𝒪) F i n)
    (by
      sorry)

/-- Helper for Lemma 21.17.10: functor-category homology agrees with stagewise homology after
evaluation. -/
private noncomputable def degree_shortComplex_homology_eval_iso
    (F : ℕ ⥤ CochainComplex Mod ℤ) (i : ℤ) :
    (degree_shortComplex (𝒪 := 𝒪) F i).homology ≅
      degree_shortComplex_evalFunctor (𝒪 := 𝒪) F i ⋙ ShortComplex.homologyFunctor Mod :=
  NatIso.ofComponents
    (fun n ↦
      ((degree_shortComplex (𝒪 := 𝒪) F i).mapHomologyIso
        ((_root_.CategoryTheory.evaluation ℕ Mod).obj n)).symm)
    (by
      intro n m f
      -- Route correction: isolate the functor-category-to-stagewise transport first, so the
      -- colimit comparison below does not have to reconstruct it implicitly.
      have h :=
        NatTrans.app_homology
          (τ := (_root_.CategoryTheory.evaluation ℕ Mod).map f)
          (S := degree_shortComplex (𝒪 := 𝒪) F i)
      simpa [degree_shortComplex_evalFunctor, Category.assoc] using
        congrArg
          (fun k ↦
            k ≫ (((degree_shortComplex (𝒪 := 𝒪) F i).mapHomologyIso
              ((_root_.CategoryTheory.evaluation ℕ Mod).obj m)).symm).hom)
          h)

/-- Helper for Lemma 21.17.10: the homology of the functor-category degree-`i` short complex is
the actual degree-`i` homology diagram of the sequential complex diagram. -/
private noncomputable def degree_shortComplex_homology_iso
    (F : ℕ ⥤ CochainComplex Mod ℤ) (i : ℤ) :
    (degree_shortComplex (𝒪 := 𝒪) F i).homology ≅
      F ⋙ HomologicalComplex.homologyFunctor Mod (ComplexShape.up ℤ) i :=
  let e₁ := degree_shortComplex_homology_eval_iso (𝒪 := 𝒪) F i
  let e₂ :=
    Functor.isoWhiskerRight
      (degree_shortComplex_app_natIso (𝒪 := 𝒪) F i)
      (ShortComplex.homologyFunctor Mod)
  let e₃ :
      (F ⋙ HomologicalComplex.shortComplexFunctor Mod (ComplexShape.up ℤ) i) ⋙
          ShortComplex.homologyFunctor Mod ≅
        F ⋙ HomologicalComplex.homologyFunctor Mod (ComplexShape.up ℤ) i :=
    NatIso.ofComponents
      (fun n ↦ Iso.refl _)
      (by
        intro n m f
        -- On each stage, homology of the standard short complex is definitionally `H^i`.
        rfl)
  e₁ ≪≫ e₂ ≪≫ e₃

/- Helper for Lemma 21.17.10: the universal sequential colimit cocone defines a natural
transformation from evaluation at stage `n` to the colimit functor on module diagrams. -/
omit [HasBinaryProducts C] [HasSheafify J AddCommGrpCat]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)] in
private theorem evaluationToColimit_naturality
    (n : ℕ) {A B : ℕ ⥤ Mod} (τ : A ⟶ B) :
    ((_root_.CategoryTheory.evaluation ℕ Mod).obj n).map τ ≫ colimit.ι B n =
      colimit.ι A n ≫ (colim : (ℕ ⥤ Mod) ⥤ Mod).map τ := by
  -- This is exactly the compatibility of the universal colimit cocone with the map `τ`.
  simpa using (colimit.ι_map τ n).symm

/-- Helper for Lemma 21.17.10: evaluation at a fixed stage maps naturally to the sequential
colimit functor on module diagrams. -/
private def evaluationToColimitNatTrans
    (n : ℕ) :
    (_root_.CategoryTheory.evaluation ℕ Mod).obj n ⟶ (colim : (ℕ ⥤ Mod) ⥤ Mod) where
  app A := colimit.ι A n
  naturality _ _ τ := evaluationToColimit_naturality (𝒪 := 𝒪) (n := n) τ

/-- Helper for Lemma 21.17.10: the component of the homology-diagram identification at stage `n`
collapses the evaluation-side `mapHomologyIso` transport to the ordinary stage short-complex
comparison. -/
private theorem degree_shortComplex_homology_iso_inv_app_comp_eval_inv
    (F : ℕ ⥤ CochainComplex Mod ℤ) (i : ℤ) (n : ℕ) :
    (degree_shortComplex_homology_iso (𝒪 := 𝒪) F i).inv.app n ≫
        ((degree_shortComplex (𝒪 := 𝒪) F i).mapHomologyIso
          ((_root_.CategoryTheory.evaluation ℕ Mod).obj n)).inv =
      ShortComplex.homologyMap
        (degree_shortComplex_app_iso (𝒪 := 𝒪) F i n).inv := by
  sorry

/-- Helper for Lemma 21.17.10: after rewriting both endpoints of the universal stage leg through
the chosen short-complex identifications, the resulting short-complex morphism is the one induced
by the chain-map cocone leg `colimit.ι F n`. -/
private theorem degree_shortComplex_transport_to_colimit_leg
    (F : ℕ ⥤ CochainComplex Mod ℤ) (i : ℤ) (n : ℕ) :
    (degree_shortComplex_app_iso (𝒪 := 𝒪) F i n).inv ≫
        (degree_shortComplex (𝒪 := 𝒪) F i).mapNatTrans
          (evaluationToColimitNatTrans (𝒪 := 𝒪) n) ≫
        (colimit_degree_shortComplex_iso (𝒪 := 𝒪) F i).hom =
      (HomologicalComplex.shortComplexFunctor Mod (ComplexShape.up ℤ) i).map (colimit.ι F n) := by
  sorry

/-- Helper for Lemma 21.17.10: exact sequential colimits identify the `i`th homology of the
colimit complex with the colimit of the `i`th homology diagram. -/
private noncomputable def homology_of_sequential_colimit_iso_colimit_homology
    (F : ℕ ⥤ CochainComplex Mod ℤ) (i : ℤ) :
    ((HomologicalComplex.homologyFunctor Mod (ComplexShape.up ℤ) i).obj (colimit F)) ≅
      colimit (F ⋙ HomologicalComplex.homologyFunctor Mod (ComplexShape.up ℤ) i) := by
  -- Route correction: package exactness on the degree-short-complex surface first, then transport
  -- to the actual homology diagram of the sequential tower.
  simpa [HomologicalComplex.homologyFunctor_obj] using
    ((ShortComplex.homologyMapIso (colimit_degree_shortComplex_iso (𝒪 := 𝒪) F i)).symm ≪≫
      (degree_shortComplex (𝒪 := 𝒪) F i).mapHomologyIso (colim : (ℕ ⥤ Mod) ⥤ Mod) ≪≫
      colim.mapIso (degree_shortComplex_homology_iso (𝒪 := 𝒪) F i))

/-- Helper for Lemma 21.17.10: exact sequential colimits in `Mod(𝒪)` identify the
colimit of the degreewise homology diagram with the homology of the colimit complex. -/
noncomputable def colimit_homology_iso_of_exact_sequential
    (F : ℕ ⥤ CochainComplex Mod ℤ) (i : ℤ) :
    colimit (F ⋙ HomologicalComplex.homologyFunctor Mod (ComplexShape.up ℤ) i) ≅
      (colimit F).homology i :=
  (homology_of_sequential_colimit_iso_colimit_homology (𝒪 := 𝒪) F i).symm

/-- Helper for Lemma 21.17.10: on each stage leg, the exact-colimit homology comparison is
exactly the homology map induced by the universal cocone map `F_n ⟶ colim F`. -/
lemma colimit_homology_iso_of_exact_sequential_hom_ι
    (F : ℕ ⥤ CochainComplex Mod ℤ) (i : ℤ) (n : ℕ) :
    colimit.ι (F ⋙ HomologicalComplex.homologyFunctor Mod (ComplexShape.up ℤ) i) n ≫
        (colimit_homology_iso_of_exact_sequential (𝒪 := 𝒪) F i).hom =
      HomologicalComplex.homologyMap (colimit.ι F n) i := by
  sorry

end

end SheafOfModules.RingedSite
