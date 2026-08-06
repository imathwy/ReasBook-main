import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Lemma_1_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Theorem_2_7_5

universe u v

open TopologicalSpace.IsOpenCover
open CategoryTheory CategoryTheory.Limits TopologicalSpace.Opens
open scoped IntersectionClosedSubcover

noncomputable section

variable {ι : Type v} {X : Type u} [TopologicalSpace X]

namespace IntersectionClosedSubcover.FundamentalGroupCocone

/-- The source-facing index category of finite intersection-closed subcovers maps to the
canonical open-cover index category of the derived cover `S ↦ U[O, S]`. -/
def toCoverIndex
    (O : ι → TopologicalSpace.Opens X) :
    IntersectionClosedSubcover O ⥤
      TopologicalSpace.IsOpenCover.Index (fun S ↦ U[O, S]) where
  obj S := S
  map hST := InducedCategory.homMk (homOfLE (finite_intersection_closed_union_mono O hST.le))
  map_id S := by
    ext
    rfl
  map_comp hST hTU := by
    ext
    rfl

/-- The diagram sending a finite intersection-closed subcollection `S` to the group `π₁(U_S, x)`.
-/
abbrev diagram
    (O : ι → TopologicalSpace.Opens X)
    (x : X) (hx : ∀ i, x ∈ O i) :
    IntersectionClosedSubcover O ⥤ GrpCat :=
  toCoverIndex O ⋙
    fundamental_group_cover_diagram
      (fun S ↦ U[O, S]) x
      (basepoint_mem_finite_intersection_closed_union O x hx)

/-- The canonical cocone from the groups `π₁(U_S, x)` to the ambient fundamental group
`π₁(X, x)`. -/
abbrev cocone
    (O : ι → TopologicalSpace.Opens X)
    (x : X) (hx : ∀ i, x ∈ O i) :
    Cocone (diagram O x hx) :=
  (fundamental_group_cover_cocone
      (fun S ↦ U[O, S]) x
      (basepoint_mem_finite_intersection_closed_union O x hx)).whisker
    (toCoverIndex O)

/-- The common basepoint of `X` determines a canonical basepoint of each finite stage `U_S`. -/
abbrev stageBasepoint
    (O : ι → TopologicalSpace.Opens X)
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : IntersectionClosedSubcover O) :
    U[O, S] :=
  ⟨x, basepoint_mem_finite_intersection_closed_union O x hx S⟩

/-- Enlarging a finite stage preserves the canonical stage basepoint induced by `x`. -/
theorem stageInclusionBasepoint
    (O : ι → TopologicalSpace.Opens X)
    (x : X) (hx : ∀ i, x ∈ O i)
    {S T : IntersectionClosedSubcover O}
    (hST : S ≤ T) :
    (((toTopCat (TopCat.of X)).map
        (homOfLE (finite_intersection_closed_union_mono O hST))).hom)
        (stageBasepoint O x hx S) =
      stageBasepoint O x hx T := by
  apply Subtype.ext
  rfl

/-- Enlarging a finite stage induces the canonical map on its fundamental groups. -/
abbrev stageInclusionHom
    (O : ι → TopologicalSpace.Opens X)
    (x : X) (hx : ∀ i, x ∈ O i)
    {S T : IntersectionClosedSubcover O}
    (hST : S ≤ T) :
    GrpCat.of (FundamentalGroup U[O, S] (stageBasepoint O x hx S)) ⟶
      GrpCat.of (FundamentalGroup U[O, T] (stageBasepoint O x hx T)) :=
  GrpCat.ofHom <|
    FundamentalGroup.mapOfEq
      (((toTopCat (TopCat.of X)).map
          (homOfLE (finite_intersection_closed_union_mono O hST))).hom)
      (stageInclusionBasepoint O x hx hST)

/-- Each map in the finite-stage diagram is the canonical map induced by enlarging the chosen
finite intersection-closed stage. -/
theorem diagram_map_eq
    (O : ι → TopologicalSpace.Opens X)
    (x : X) (hx : ∀ i, x ∈ O i)
    {S T : IntersectionClosedSubcover O}
    (hST : S ⟶ T) :
    (diagram O x hx).map hST =
      stageInclusionHom O x hx hST.le := by
  rfl

/-- Including a finite stage union into `X` preserves the chosen stage basepoint. -/
theorem stage_union_to_ambient_basepoint
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : IntersectionClosedSubcover O) :
    (inclusion' U[O, S]).hom (stageBasepoint O x hx S) = x := by
  rfl

/-- The inclusion of a finite stage union into `X` induces the canonical map on fundamental
groups. -/
abbrev stage_union_to_ambient_hom
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : IntersectionClosedSubcover O) :
    GrpCat.of (FundamentalGroup U[O, S] (stageBasepoint O x hx S)) ⟶
      GrpCat.of (FundamentalGroup X x) :=
  GrpCat.ofHom <|
    FundamentalGroup.mapOfEq (inclusion' U[O, S]).hom
      (stage_union_to_ambient_basepoint O x hx S)

/-- The `S`-leg of the canonical finite-stage cocone is definitionally the stage-union inclusion
map on fundamental groups. -/
theorem cocone_app_eq_stage_union_to_ambient_hom
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : IntersectionClosedSubcover O) :
    (cocone O x hx).ι.app S =
      stage_union_to_ambient_hom O x hx S := by
  ext g
  change
    ((fundamental_group_cover_cocone
          (fun T ↦ U[O, T]) x
          (basepoint_mem_finite_intersection_closed_union O x hx)).ι.app
        ((toCoverIndex O).obj S)).hom g =
      (GrpCat.ofHom
          (FundamentalGroup.mapOfEq (inclusion' U[O, S]).hom
            (stage_union_to_ambient_basepoint O x hx S))).hom g
  have hleg :
      ((fundamental_group_cover_cocone
            (fun T ↦ U[O, T]) x
            (basepoint_mem_finite_intersection_closed_union O x hx)).ι.app
          ((toCoverIndex O).obj S)).hom g =
        (FundamentalGroup.map (inclusion' U[O, S]).hom (stageBasepoint O x hx S)) g := by
    simpa [toCoverIndex] using
      congrArg (fun f ↦ f g)
        (fundamental_group_cover_cocone_app_eq_map_inclusion
          (fun T ↦ U[O, T]) x
          (basepoint_mem_finite_intersection_closed_union O x hx) S)
  have hmap :
      (FundamentalGroup.map (inclusion' U[O, S]).hom (stageBasepoint O x hx S)) g =
        (FundamentalGroup.mapOfEq (inclusion' U[O, S]).hom
          (stage_union_to_ambient_basepoint O x hx S)) g := by
    have hmapEq :
        FundamentalGroup.map (inclusion' U[O, S]).hom (stageBasepoint O x hx S) =
          FundamentalGroup.mapOfEq (inclusion' U[O, S]).hom rfl := by
      simpa using FundamentalGroup.map_eq_mapOfEq_rfl (stageBasepoint O x hx S)
    simpa [stage_union_to_ambient_basepoint] using
      congrArg (fun f ↦ f g) hmapEq
  exact hleg.trans hmap

end IntersectionClosedSubcover.FundamentalGroupCocone
