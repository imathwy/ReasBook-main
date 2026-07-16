import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.EpiMono
import StacksProject_2024.stacks_project.Chap04.Lemma_4_19_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.FunctorToTypes

universe u v

namespace CategoryTheory.Limits

variable {I : Type u} [Category.{v} I]
variable (M : I ⥤ AddCommGrpCat.{max u v})

/-
Domain-style sampling for Lemma 4.19.5:
- primary domain: comparison maps between `Type`-colimits and additive colimits
- inspected owner declarations:
  - `colimit.post`
  - `prodComparison_colim_surjective_of_commonSuccessor`
  - `AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits`
  - `CategoryTheory.epi_iff_surjective`
- source-facing hypotheses: nonemptiness of the index category and common successors for pairs of
  objects
- best owner abstraction: the canonical comparison morphism
  `colimit.post M (forget AddCommGrpCat)`; under the stronger hypothesis `[IsFiltered I]`, the
  filtered-colimit owner `AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits` upgrades
  this comparison map to an isomorphism
- canonical bridge reused in the proof: `prodComparison_colim_surjective_of_commonSuccessor`
- primitive data: the additive diagram `M`, the source-level nonemptiness hypothesis `hI`, and
  the source-level common-successor hypothesis
- derived API: the surjectivity and epimorphism consequences for
  `colimit.post M (forget AddCommGrpCat)`
- target layer here: `bridge/view`, namely the surjectivity and epimorphism consequences for the
  comparison map from the `Type`-colimit to the underlying set of the additive colimit; the
  theorem stays at this layer because the source hypotheses are weaker than filteredness
-/

/-- Lemma 4.19.5: if the index category is nonempty and every pair of its objects admits a common
successor, then the canonical comparison map from the colimit of `M` in sets to the underlying set
of the colimit of `M` in abelian groups is surjective. The nonemptiness hypothesis is necessary:
for the empty index category, the source colimit in `Type` is empty while the target is the
underlying singleton set of the zero abelian group. -/
-- Proof sketch: every element of the abelian-group colimit is represented by a finite sum of
-- images from objects of the diagram. The common-successor hypothesis lets us move finitely many
-- representatives to a single stage, where their sum is represented by one element, and that
-- element defines a preimage in the `Type`-colimit.
theorem addCommGrpColimitComparison_surjective_of_commonSuccessor
    (hObj : ∀ i j : I, ∃ k : I, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
    (hI : Nonempty I) :
    Function.Surjective (colimit.post M (forget AddCommGrpCat)) := by
  classical
  let A : AddCommGrpCat.{max u v} := colimit M
  let i0 : I := Classical.choice hI
  let F : I ⥤ Type (max u v) := M ⋙ forget AddCommGrpCat
  let post : colimit F ⟶ A := colimit.post M (forget AddCommGrpCat)
  have hprodSurj : Function.Surjective (prodComparison colim F F) :=
    prodComparison_colim_surjective_of_commonSuccessor hObj F F
  have post_ι (i : I) (x : F.obj i) : post (colimit.ι F i x) = colimit.ι M i x := by
    simpa [post] using congrFun (colimit.ι_post M (forget AddCommGrpCat) i) x
  let representedSubgroup : AddSubgroup A :=
    { toAddSubmonoid :=
        { carrier := fun z ↦ ∃ i : I, ∃ y : M.obj i, colimit.ι M i y = z
          zero_mem' := by
            refine ⟨i0, 0, ?_⟩
            simp
          add_mem' := by
            intro a b ha hb
            rcases ha with ⟨i, x, rfl⟩
            rcases hb with ⟨j, y, rfl⟩
            let e := Types.binaryProductIso (colimit F) (colimit F)
            obtain ⟨w, hw⟩ := hprodSurj (e.inv (colimit.ι F i x, colimit.ι F j y))
            obtain ⟨k, xy, hxy⟩ := Types.jointly_surjective' w
            let xk : M.obj k := (prod.fst : F ⨯ F ⟶ F).app k xy
            let yk : M.obj k := (prod.snd : F ⨯ F ⟶ F).app k xy
            refine ⟨k, xk + yk, ?_⟩
            have hpair :
                prodComparison colim F F (colimit.ι (F ⨯ F) k xy) =
                  e.inv (colimit.ι F i x, colimit.ι F j y) := by
              rw [hxy]
              exact hw
            have hxk : colimit.ι F k xk = colimit.ι F i x := by
              have hpair' := congrArg (fun p ↦ p.1) (congrArg e.hom hpair)
              exact (CategoryTheory.Limits.prodComparison_colim_ι_fst F F k xy).symm.trans <| by
                simpa [e, xk] using hpair'
            have hyk : colimit.ι F k yk = colimit.ι F j y := by
              have hpair' := congrArg (fun p ↦ p.2) (congrArg e.hom hpair)
              exact (CategoryTheory.Limits.prodComparison_colim_ι_snd F F k xy).symm.trans <| by
                simpa [e, yk] using hpair'
            have hxk' : colimit.ι M k xk = colimit.ι M i x := by
              exact (post_ι k xk).symm.trans <| (congrArg post hxk).trans (post_ι i x)
            have hyk' : colimit.ι M k yk = colimit.ι M j y := by
              exact (post_ι k yk).symm.trans <| (congrArg post hyk).trans (post_ι j y)
            calc
              colimit.ι M k (xk + yk) = colimit.ι M k xk + colimit.ι M k yk := by
                exact (colimit.ι M k).hom.map_add xk yk
              _ = colimit.ι M i x + colimit.ι M j y := by
                exact congrArg₂ (fun a b : A ↦ a + b) hxk' hyk' }
      neg_mem' := by
        intro a ha
        rcases ha with ⟨i, x, rfl⟩
        exact ⟨i, -x, by simp⟩ }
  let representedCocone : Cocone M :=
    { pt := AddCommGrpCat.of ↥representedSubgroup
      ι :=
        { app := fun i ↦
            AddCommGrpCat.ofHom
              { toFun := fun x ↦ ⟨colimit.ι M i x, ⟨i, x, rfl⟩⟩
                map_zero' := by
                  ext
                  simp
                map_add' := fun x y ↦ by
                  ext
                  simp }
          naturality := by
            intro i j f
            ext x
            change (⟨colimit.ι M j (M.map f x), ⟨j, M.map f x, rfl⟩⟩ : representedSubgroup) =
                ⟨colimit.ι M i x, ⟨i, x, rfl⟩⟩
            exact Subtype.ext <| by
              change (M.map f ≫ colimit.ι M j) x = colimit.ι M i x
              exact DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (colimit.w M f)) x } }
  let representedIncl : AddCommGrpCat.of representedSubgroup ⟶ A :=
    AddCommGrpCat.ofHom representedSubgroup.subtype
  let descRepresented : A ⟶ AddCommGrpCat.of representedSubgroup :=
    colimit.desc M representedCocone
  have hdescRepresented : descRepresented ≫ representedIncl = 𝟙 A := by
    apply colimit.hom_ext
    intro i
    ext x
    change (((descRepresented ((colimit.ι M i) x) : representedSubgroup) : A)) = colimit.ι M i x
    have hx :
        descRepresented (colimit.ι M i x) = ⟨colimit.ι M i x, ⟨i, x, rfl⟩⟩ := by
      simp [descRepresented, representedCocone]
    rw [hx]
  have hmem : ∀ z : A, z ∈ representedSubgroup := by
    intro z
    let y : representedSubgroup := descRepresented z
    have hy : (y : A) = z := by
      simpa [y] using DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom hdescRepresented) z
    exact hy.symm ▸ y.2
  intro z
  rcases hmem z with ⟨i, x, hx⟩
  refine ⟨colimit.ι F i x, ?_⟩
  exact (post_ι i x).trans hx

/-- Categorical reformulation of Lemma 4.19.5 via the canonical `epi_iff_surjective` bridge. -/
theorem addCommGrpColimitComparison_epi_of_commonSuccessor
    (hObj : ∀ i j : I, ∃ k : I, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
    (hI : Nonempty I) :
    Epi (colimit.post M (forget AddCommGrpCat)) := by
  simpa using
    (epi_iff_surjective (colimit.post M (forget AddCommGrpCat))).mpr <|
      addCommGrpColimitComparison_surjective_of_commonSuccessor M hObj hI

end CategoryTheory.Limits
