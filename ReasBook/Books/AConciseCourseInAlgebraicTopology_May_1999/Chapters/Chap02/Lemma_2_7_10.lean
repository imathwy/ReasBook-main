import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.ProofStep_2_7_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Lemma_2_7_10.Comparison

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Path
open TopologicalSpace.IsOpenCover
open CategoryTheory CategoryTheory.Limits TopologicalSpace.Opens unitInterval
open scoped IntersectionClosedSubcover

noncomputable section

variable {ι : Type v} {X : Type u} [TopologicalSpace X]

open IntersectionClosedSubcover.FundamentalGroupCocone

/-- Helper for Lemma 2.7.10: a nonempty finite family of stage indices admits an
intersection-closed common refinement. -/
private theorem exists_common_refinement_stage
    (O : ι → TopologicalSpace.Opens X)
    (hinter : ClosedUnderNonemptyFiniteIntersections O)
    (T : Finset ι) (hT : T.Nonempty) :
    ∃ S : IntersectionClosedSubcover O, ∀ ⦃i : ι⦄, i ∈ T → i ∈ S := by
  exact exists_nonempty_intersection_closed_finset_superset O hinter T hT

/-- Helper for Lemma 2.7.10: the literal stage lift of an ambient loop starts at the chosen stage
basepoint. -/
private theorem ambient_loop_in_stage_source
    (O : ι → TopologicalSpace.Opens X)
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : IntersectionClosedSubcover O)
    (γ : Path x x)
    (hγ : Set.range γ ⊆ U[O, S]) :
    (⟨γ 0, hγ ⟨0, rfl⟩⟩ : U[O, S]) = stageBasepoint O x hx S := by
  -- At time `0`, the ambient loop is at `x`, so the lifted stage point is the chosen basepoint.
  apply Subtype.ext
  simp [γ.source]

/-- Helper for Lemma 2.7.10: the literal stage lift of an ambient loop ends at the chosen stage
basepoint. -/
private theorem ambient_loop_in_stage_target
    (O : ι → TopologicalSpace.Opens X)
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : IntersectionClosedSubcover O)
    (γ : Path x x)
    (hγ : Set.range γ ⊆ U[O, S]) :
    (⟨γ 1, hγ ⟨1, rfl⟩⟩ : U[O, S]) = stageBasepoint O x hx S := by
  -- At time `1`, the ambient loop again returns to `x`.
  apply Subtype.ext
  simp [γ.target]

/-- Helper for Lemma 2.7.10: an ambient loop whose image lies in a finite stage can be regarded as
a loop in that stage union. -/
private noncomputable def ambient_loop_in_stage
    (O : ι → TopologicalSpace.Opens X)
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : IntersectionClosedSubcover O)
    (γ : Path x x)
    (hγ : Set.range γ ⊆ U[O, S]) :
    Path (stageBasepoint O x hx S) (stageBasepoint O x hx S) :=
  { toContinuousMap :=
      { toFun := fun t ↦ ⟨γ t, hγ ⟨t, rfl⟩⟩
        continuous_toFun := Continuous.subtype_mk γ.continuous fun t ↦ hγ ⟨t, rfl⟩ }
    source' := ambient_loop_in_stage_source O x hx S γ hγ
    target' := ambient_loop_in_stage_target O x hx S γ hγ }

/-- Helper for Lemma 2.7.10: after enlarging a finite stage, the lifted ambient loop becomes the
same literal loop in the larger stage. -/
private theorem ambient_loop_in_stage_map_stage_union_inclusion
    (O : ι → TopologicalSpace.Opens X)
    (x : X) (hx : ∀ i, x ∈ O i)
    {S T : IntersectionClosedSubcover O}
    (hST : S ≤ T)
    (γ : Path x x)
    (hγS : Set.range γ ⊆ U[O, S])
    (hγT : Set.range γ ⊆ U[O, T]) :
    ((ambient_loop_in_stage O x hx S γ hγS).map
          (((toTopCat (TopCat.of X)).map
              (homOfLE (finite_intersection_closed_union_mono O hST))).hom.continuous)).cast
        (stageInclusionBasepoint O x hx hST).symm
        (stageInclusionBasepoint O x hx hST).symm =
      ambient_loop_in_stage O x hx T γ hγT := by
  -- Both paths have the same ambient coordinate at every time, so extensionality suffices.
  ext t
  apply Subtype.ext
  rfl

/-- Helper for Lemma 2.7.10: enlarging a finite stage sends the lifted ambient loop class to the
same ambient loop class viewed in the larger stage. -/
private theorem stage_union_inclusion_hom_apply_ambient_loop
    (O : ι → TopologicalSpace.Opens X)
    (x : X) (hx : ∀ i, x ∈ O i)
    {S T : IntersectionClosedSubcover O}
    (hST : S ≤ T)
    (γ : Path x x)
    (hγS : Set.range γ ⊆ U[O, S])
    (hγT : Set.range γ ⊆ U[O, T]) :
    (stageInclusionHom O x hx hST).hom
        (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγS⟧) =
      FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγT⟧ := by
  let f :
      C(U[O, S], U[O, T]) :=
    ((toTopCat (TopCat.of X)).map
      (homOfLE (finite_intersection_closed_union_mono O hST))).hom
  have hraw :=
    FundamentalGroup.mapOfEq_apply
      f
      (stageInclusionBasepoint O x hx hST)
      (ambient_loop_in_stage O x hx S γ hγS)
  have hnorm :
      FundamentalGroup.fromPath
          ⟦((ambient_loop_in_stage O x hx S γ hγS).map f.continuous).cast
              (stageInclusionBasepoint O x hx hST).symm
              (stageInclusionBasepoint O x hx hST).symm⟧ =
        FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγT⟧ := by
    -- Normalize the mapped lifted loop to the literal lift in the larger stage.
    exact congrArg FundamentalGroup.fromPath <|
      congrArg Homotopic.Quotient.mk <|
        ambient_loop_in_stage_map_stage_union_inclusion O x hx hST γ hγS hγT
  -- Apply `mapOfEq_apply`, then rewrite the mapped loop into the larger-stage lift.
  simpa [stageInclusionHom, f] using hraw.trans hnorm

/-- Helper for Lemma 2.7.10: evaluating one ambient loop in two finite stages gives the same
result after passing to a common refinement. -/
private theorem ambient_stage_value_eq_of_common_refinement
    (O : ι → TopologicalSpace.Opens X)
    (x : X) (hx : ∀ i, x ∈ O i)
    (hinter : ClosedUnderNonemptyFiniteIntersections O)
    (C : Cocone (diagram O x hx))
    (γ : Path x x)
    {S T : IntersectionClosedSubcover O}
    (hγS : Set.range γ ⊆ U[O, S])
    (hγT : Set.range γ ⊆ U[O, T]) :
    (C.ι.app S).hom (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγS⟧) =
      (C.ι.app T).hom (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγT⟧) := by
  classical
  have hST_nonempty : (S.carrier ∪ T.carrier).Nonempty := by
    rcases S.nonempty with ⟨i, hi⟩
    exact ⟨i, Finset.mem_union.mpr (Or.inl hi)⟩
  obtain ⟨R, hR⟩ :=
    exists_common_refinement_stage O hinter (S.carrier ∪ T.carrier)
      hST_nonempty
  have hSR : S ≤ R := fun i hi ↦ hR (Finset.mem_union.mpr (Or.inl hi))
  have hTR : T ≤ R := fun i hi ↦ hR (Finset.mem_union.mpr (Or.inr hi))
  have hγR_fromS : Set.range γ ⊆ U[O, R] := by
    -- Enlarging the stage preserves containment of the loop image.
    intro y hy
    exact finite_intersection_closed_union_mono O hSR (hγS hy)
  have hγR_fromT : Set.range γ ⊆ U[O, R] := by
    -- The same enlargement argument applies from `T` to `R`.
    intro y hy
    exact finite_intersection_closed_union_mono O hTR (hγT hy)
  have hS_to_R :
      (C.ι.app S).hom (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγS⟧) =
        (C.ι.app R).hom
          (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx R γ hγR_fromS⟧) := by
    have hnat :=
      congrArg
        (fun k ↦
          k.hom (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγS⟧))
        (C.w (homOfLE hSR))
    calc
      (C.ι.app S).hom (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγS⟧) =
        (C.ι.app R).hom
          (((diagram O x hx).map
              (homOfLE hSR)).hom
            (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγS⟧)) := by
              simpa [GrpCat.comp_apply] using hnat.symm
      _ = (C.ι.app R).hom
            (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx R γ hγR_fromS⟧) := by
            rw [diagram_map_eq O x hx]
            exact congrArg (fun z ↦ (C.ι.app R).hom z) <|
              stage_union_inclusion_hom_apply_ambient_loop O x hx hSR γ hγS hγR_fromS
  have hT_to_R :
      (C.ι.app T).hom (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγT⟧) =
        (C.ι.app R).hom
          (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx R γ hγR_fromT⟧) := by
    have hnat :=
      congrArg
        (fun k ↦
          k.hom (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγT⟧))
        (C.w (homOfLE hTR))
    calc
      (C.ι.app T).hom (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγT⟧) =
        (C.ι.app R).hom
          (((diagram O x hx).map
              (homOfLE hTR)).hom
            (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγT⟧)) := by
              simpa [GrpCat.comp_apply] using hnat.symm
      _ = (C.ι.app R).hom
            (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx R γ hγR_fromT⟧) := by
            rw [diagram_map_eq O x hx]
            exact congrArg (fun z ↦ (C.ι.app R).hom z) <|
              stage_union_inclusion_hom_apply_ambient_loop O x hx hTR γ hγT hγR_fromT
  -- Both stage evaluations agree with the common-refinement evaluation.
  exact hS_to_R.trans hT_to_R.symm

/-- Helper for Lemma 2.7.10: if a loop homotopy stays inside one finite stage, then the source
loop already stays inside that stage. -/
private theorem path_range_subset_of_homotopy_source
    (O : ι → TopologicalSpace.Opens X)
    (S : IntersectionClosedSubcover O)
    {x : X} {γ₀ γ₁ : Path x x} (H : Path.Homotopy γ₀ γ₁)
    (hH : Set.range H ⊆ U[O, S]) :
    Set.range γ₀ ⊆ U[O, S] := by
  -- Evaluate the homotopy on the left edge to recover the source loop.
  intro y hy
  rcases hy with ⟨t, rfl⟩
  exact hH ⟨(0, t), by simp⟩

/-- Helper for Lemma 2.7.10: if a loop homotopy stays inside one finite stage, then the target
loop already stays inside that stage. -/
private theorem path_range_subset_of_homotopy_target
    (O : ι → TopologicalSpace.Opens X)
    (S : IntersectionClosedSubcover O)
    {x : X} {γ₀ γ₁ : Path x x} (H : Path.Homotopy γ₀ γ₁)
    (hH : Set.range H ⊆ U[O, S]) :
    Set.range γ₁ ⊆ U[O, S] := by
  -- Evaluate the homotopy on the right edge to recover the target loop.
  intro y hy
  rcases hy with ⟨t, rfl⟩
  exact hH ⟨(1, t), by simp⟩

/-- Helper for Lemma 2.7.10: if two loops both stay inside one finite stage, then their
concatenation stays inside that stage as well. -/
private theorem path_trans_range_subset
    (O : ι → TopologicalSpace.Opens X)
    (S : IntersectionClosedSubcover O)
    {x : X} {γ δ : Path x x}
    (hδ : Set.range δ ⊆ U[O, S])
    (hγ : Set.range γ ⊆ U[O, S]) :
    Set.range (δ.trans γ) ⊆ U[O, S] := by
  -- Split the concatenated path at time `1/2` and use the corresponding factor.
  intro y hy
  rcases hy with ⟨t, rfl⟩
  rw [Path.trans_apply]
  split_ifs with ht
  · exact hδ ⟨⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, rfl⟩
  · exact hγ
      ⟨⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩, rfl⟩

/-- Helper for Lemma 2.7.10: a loop homotopy that stays in one finite stage yields homotopic
stage lifts of its endpoints. -/
private theorem ambient_loop_in_stage_homotopic
    (O : ι → TopologicalSpace.Opens X)
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : IntersectionClosedSubcover O)
    {γ₀ γ₁ : Path x x} (H : Path.Homotopy γ₀ γ₁)
    (hH : Set.range H ⊆ U[O, S]) :
    (ambient_loop_in_stage O x hx S γ₀
        (path_range_subset_of_homotopy_source O S H hH)).Homotopic
      (ambient_loop_in_stage O x hx S γ₁
        (path_range_subset_of_homotopy_target O S H hH)) := by
  -- Lift the ambient homotopy pointwise into the stage subtype.
  refine ⟨
    { toContinuousMap :=
        { toFun := fun p ↦ ⟨H p, hH ⟨p, rfl⟩⟩
          continuous_toFun := Continuous.subtype_mk H.continuous fun p ↦ hH ⟨p, rfl⟩ }
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
  · intro t
    -- On the left edge we recover the lifted source loop.
    apply Subtype.ext
    simp [ambient_loop_in_stage]
  · intro t
    -- On the right edge we recover the lifted target loop.
    apply Subtype.ext
    simp [ambient_loop_in_stage]
  · intro t y hy
    -- Along the top and bottom edges the homotopy stays at the common basepoint.
    apply Subtype.ext
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using H.prop t y hy

/-- Helper for Lemma 2.7.10: lifting an ambient concatenation into one finite stage agrees with
concatenating the two lifted stage loops. -/
private theorem ambient_loop_in_stage_trans
    (O : ι → TopologicalSpace.Opens X)
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : IntersectionClosedSubcover O)
    (γ δ : Path x x)
    (hγ : Set.range γ ⊆ U[O, S])
    (hδ : Set.range δ ⊆ U[O, S]) :
    ambient_loop_in_stage O x hx S (δ.trans γ) (path_trans_range_subset O S hδ hγ) =
      (ambient_loop_in_stage O x hx S δ hδ).trans
        (ambient_loop_in_stage O x hx S γ hγ) := by
  -- Both paths have the same ambient coordinate at every time after expanding concatenation.
  ext t
  change
    (δ.trans γ) t =
      (((ambient_loop_in_stage O x hx S δ hδ).trans
          (ambient_loop_in_stage O x hx S γ hγ)) t).1
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs <;> rfl

/-- Helper for Lemma 2.7.10: once two ambient loops already live in one finite stage, the cocone
value of their product is computed inside that single stage. -/
private theorem ambient_stage_value_mul_of_common_stage
    (O : ι → TopologicalSpace.Opens X)
    (x : X) (hx : ∀ i, x ∈ O i)
    (C : Cocone (diagram O x hx))
    (S : IntersectionClosedSubcover O)
    (γ δ : Path x x)
    (hγ : Set.range γ ⊆ U[O, S])
    (hδ : Set.range δ ⊆ U[O, S]) :
    (C.ι.app S).hom
        (FundamentalGroup.fromPath
          ⟦ambient_loop_in_stage O x hx S (δ.trans γ) (path_trans_range_subset O S hδ hγ)⟧) =
      ((C.ι.app S).hom
          (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγ⟧)) *
        ((C.ι.app S).hom
          (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S δ hδ⟧)) := by
  have hloop :
      FundamentalGroup.fromPath
          ⟦ambient_loop_in_stage O x hx S (δ.trans γ) (path_trans_range_subset O S hδ hγ)⟧ =
        FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγ⟧ *
          FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S δ hδ⟧ := by
    -- Normalize the lifted concatenation to the product in the stage fundamental group.
    rw [ambient_loop_in_stage_trans O x hx S γ δ hγ hδ]
    change FundamentalGroup.fromPath
        (Homotopic.Quotient.trans
          ⟦ambient_loop_in_stage O x hx S δ hδ⟧
          ⟦ambient_loop_in_stage O x hx S γ hγ⟧) =
      _
    change FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγ⟧ *
        FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S δ hδ⟧ =
      _
    rfl
  -- After rewriting the source loop class, multiplicativity of the cocone leg finishes.
  exact (congrArg (fun q ↦ (C.ι.app S).hom q) hloop).trans (MonoidHom.map_mul _ _ _)

/-- Helper for Lemma 2.7.10: the ambient image of a loop in a finite stage still lies in that
same stage union. -/
private theorem stage_loop_range_subset
    (O : ι → TopologicalSpace.Opens X)
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : IntersectionClosedSubcover O)
    (γ : Path (stageBasepoint O x hx S) (stageBasepoint O x hx S)) :
    Set.range (γ.map continuous_subtype_val) ⊆ U[O, S] := by
  -- Every point of the mapped loop comes from the stage subtype itself.
  intro y hy
  rcases hy with ⟨t, rfl⟩
  exact (γ t).2

/-- Helper for Lemma 2.7.10: lifting the ambient image of a literal stage loop back into the same
stage recovers the original stage loop. -/
private theorem ambient_loop_in_stage_of_stage_loop
    (O : ι → TopologicalSpace.Opens X)
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : IntersectionClosedSubcover O)
    (γ : Path (stageBasepoint O x hx S) (stageBasepoint O x hx S)) :
    ambient_loop_in_stage O x hx S
        (γ.map continuous_subtype_val)
        (stage_loop_range_subset O x hx S γ) =
      γ := by
  -- Both loops have the same stage-valued coordinate at every time.
  ext t
  rfl

/-- Helper for Lemma 2.7.10: the finite-stage inclusion sends a literal stage loop class to the
class of the same loop viewed in `X`. -/
private theorem stage_union_to_ambient_hom_apply_stage_loop
    (O : ι → TopologicalSpace.Opens X)
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : IntersectionClosedSubcover O)
    (γ : Path (stageBasepoint O x hx S) (stageBasepoint O x hx S)) :
    (stage_union_to_ambient_hom O x hx S).hom (FundamentalGroup.fromPath ⟦γ⟧) =
      FundamentalGroup.fromPath ⟦γ.map continuous_subtype_val⟧ := by
  let f : C(U[O, S], X) :=
    (inclusion' (U[O, S] : TopologicalSpace.Opens (TopCat.of X))).hom
  have hbase : f (stageBasepoint O x hx S) = x := by
    rfl
  have hraw :=
    FundamentalGroup.mapOfEq_apply
      f
      hbase
      γ
  have hnorm :
      FundamentalGroup.fromPath
          ⟦((γ.map f.continuous).cast
              hbase.symm
              hbase.symm)⟧ =
        FundamentalGroup.fromPath ⟦γ.map continuous_subtype_val⟧ := by
    -- Mapping the literal stage loop to `X` just forgets the subtype proof.
    exact congrArg FundamentalGroup.fromPath <|
      congrArg Homotopic.Quotient.mk <| by
        ext t
        rfl
  -- Apply `mapOfEq_apply`, then normalize the mapped stage loop.
  simpa [stage_union_to_ambient_hom, f] using hraw.trans hnorm

/-- Helper for Lemma 2.7.10: the finite-stage inclusion sends the lifted ambient loop class back
to the original ambient loop class. -/
private theorem stage_union_to_ambient_hom_apply_ambient_loop
    (O : ι → TopologicalSpace.Opens X)
    (x : X) (hx : ∀ i, x ∈ O i)
    (S : IntersectionClosedSubcover O)
    (γ : Path x x)
    (hγ : Set.range γ ⊆ U[O, S]) :
    (stage_union_to_ambient_hom O x hx S).hom
        (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx S γ hγ⟧) =
      FundamentalGroup.fromPath ⟦γ⟧ := by
  let f : C(U[O, S], X) :=
    (inclusion' (U[O, S] : TopologicalSpace.Opens (TopCat.of X))).hom
  have hbase : f (stageBasepoint O x hx S) = x := by
    rfl
  have hraw :=
    FundamentalGroup.mapOfEq_apply
      f
      hbase
      (ambient_loop_in_stage O x hx S γ hγ)
  have hnorm :
      FundamentalGroup.fromPath
          ⟦(((ambient_loop_in_stage O x hx S γ hγ).map
                f.continuous).cast
              hbase.symm
              hbase.symm)⟧ =
        FundamentalGroup.fromPath ⟦γ⟧ := by
    -- Forgetting the stage subtype recovers the original ambient loop.
    exact congrArg FundamentalGroup.fromPath <|
      congrArg Homotopic.Quotient.mk <| by
        ext t
        rfl
  -- Apply `mapOfEq_apply`, then collapse back to the original ambient loop.
  simpa [stage_union_to_ambient_hom, f] using hraw.trans hnorm

-- Internal universal-property formulation used to build the public `IsColimit` datum via the
-- canonical `IsColimit.ofExistsUnique` owner API.
private theorem finite_intersection_closed_subcover_fundamental_group_existsUnique
    (O : ι → TopologicalSpace.Opens X)
    (hO : TopologicalSpace.IsOpenCover O)
    (x : X) (hx : ∀ i, x ∈ O i)
    (hinter : ClosedUnderNonemptyFiniteIntersections O) :
    ∀ S : Cocone (diagram O x hx),
      ∃! d :
        (cocone O x hx).pt ⟶ S.pt,
        ∀ T,
          (cocone O x hx).ι.app T ≫ d =
            S.ι.app T := by
  intro C
  classical
  let chosen_stage : Path x x → IntersectionClosedSubcover O := fun γ ↦
    Classical.choose (loop_image_subset_finite_union_of_intersection_closed_subcover O hO hinter γ)
  let chosen_stage_mem : ∀ γ : Path x x, Set.range γ ⊆ (U[O, chosen_stage γ] : Set X) := fun γ ↦
    Classical.choose_spec
      (loop_image_subset_finite_union_of_intersection_closed_subcover O hO hinter γ)
  let stage_value :
      (γ : Path x x) →
        (T : IntersectionClosedSubcover O) →
          Set.range γ ⊆ U[O, T] → C.pt := fun γ T hγ ↦
    (C.ι.app T).hom (FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγ⟧)
  let raw_value : Path x x → C.pt := fun γ ↦
    stage_value γ (chosen_stage γ) (chosen_stage_mem γ)
  have raw_value_spec :
      ∀ (γ : Path x x) (T : IntersectionClosedSubcover O)
        (hγ : Set.range γ ⊆ U[O, T]),
        raw_value γ = stage_value γ T hγ := by
    -- The common-refinement comparison makes the chosen stage irrelevant.
    intro γ T hγ
    exact ambient_stage_value_eq_of_common_refinement O x hx hinter C γ (chosen_stage_mem γ) hγ
  have raw_value_respects :
      ∀ {γ₀ γ₁ : Path x x}, γ₀.Homotopic γ₁ → raw_value γ₀ = raw_value γ₁ := by
    intro γ₀ γ₁ hγ
    rcases hγ with ⟨H⟩
    obtain ⟨T, hH⟩ :=
      homotopy_image_subset_finite_union_of_intersection_closed_subcover O hO hinter H
    have hγ₀ : Set.range γ₀ ⊆ U[O, T] :=
      path_range_subset_of_homotopy_source O T H hH
    have hγ₁ : Set.range γ₁ ⊆ U[O, T] :=
      path_range_subset_of_homotopy_target O T H hH
    have hquot :
        FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ₀ hγ₀⟧ =
          FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ₁ hγ₁⟧ := by
      -- Lift the ambient homotopy to the chosen common stage and descend it to the quotient.
      apply congrArg FundamentalGroup.fromPath
      exact Quotient.sound (ambient_loop_in_stage_homotopic O x hx T H hH)
    calc
      raw_value γ₀ = stage_value γ₀ T hγ₀ := raw_value_spec γ₀ T hγ₀
      _ = stage_value γ₁ T hγ₁ := by
            simpa [stage_value] using congrArg (fun q ↦ (C.ι.app T).hom q) hquot
      _ = raw_value γ₁ := (raw_value_spec γ₁ T hγ₁).symm
  let dMonoid : FundamentalGroup X x →* C.pt :=
    { toFun := fun q ↦ Quotient.liftOn q raw_value fun _ _ h ↦ raw_value_respects h
      map_one' := by
        -- Evaluate the ambient descendant on the constant loop inside any stage containing it.
        obtain ⟨T, hT⟩ :=
          loop_image_subset_finite_union_of_intersection_closed_subcover O hO hinter (Path.refl x)
        have href :
            ambient_loop_in_stage O x hx T (Path.refl x) hT =
              Path.refl (stageBasepoint O x hx T) := by
          ext t
          rfl
        calc
          Quotient.liftOn (1 : FundamentalGroup X x) raw_value
              (fun _ _ h ↦ raw_value_respects h) =
            raw_value (Path.refl x) := by
                rfl
          _ = stage_value (Path.refl x) T hT := raw_value_spec (Path.refl x) T hT
          _ = 1 := by
                change
                  (C.ι.app T).hom
                      (FundamentalGroup.fromPath ⟦Path.refl (stageBasepoint O x hx T)⟧) =
                    1
                change (C.ι.app T).hom 1 = 1
                simpa using (C.ι.app T).hom.map_one
      map_mul' := by
        intro a b
        induction a using Homotopic.Quotient.ind with
        | mk γ =>
            induction b using Homotopic.Quotient.ind with
            | mk δ =>
                -- Put both representative loops in one common stage and compute there.
                obtain ⟨Sγ, hγ⟩ :=
                  loop_image_subset_finite_union_of_intersection_closed_subcover O hO hinter γ
                obtain ⟨Sδ, hδ⟩ :=
                  loop_image_subset_finite_union_of_intersection_closed_subcover O hO hinter δ
                have hS_nonempty : (Sγ.carrier ∪ Sδ.carrier).Nonempty := by
                  rcases Sγ.nonempty with ⟨i, hi⟩
                  exact ⟨i, Finset.mem_union.mpr (Or.inl hi)⟩
                obtain ⟨R, hR⟩ :=
                  exists_common_refinement_stage O hinter
                    (Sγ.carrier ∪ Sδ.carrier) hS_nonempty
                have hγR : Set.range γ ⊆ U[O, R] := by
                  intro y hy
                  exact finite_intersection_closed_union_mono O
                    (fun i hi ↦ hR (Finset.mem_union.mpr (Or.inl hi))) (hγ hy)
                have hδR : Set.range δ ⊆ U[O, R] := by
                  intro y hy
                  exact finite_intersection_closed_union_mono O
                    (fun i hi ↦ hR (Finset.mem_union.mpr (Or.inr hi))) (hδ hy)
                change raw_value (δ.trans γ) = raw_value γ * raw_value δ
                calc
                  raw_value (δ.trans γ) =
                      stage_value (δ.trans γ) R (path_trans_range_subset O R hδR hγR) :=
                    raw_value_spec (δ.trans γ) R (path_trans_range_subset O R hδR hγR)
                  _ = stage_value γ R hγR * stage_value δ R hδR := by
                        simpa [stage_value] using
                          ambient_stage_value_mul_of_common_stage O x hx C R γ δ hγR hδR
                  _ = raw_value γ * raw_value δ := by
                        rw [raw_value_spec γ R hγR, raw_value_spec δ R hδR] }
  let d :
      (cocone O x hx).pt ⟶ C.pt :=
    GrpCat.ofHom dMonoid
  refine ⟨d, ?_, ?_⟩
  · intro T
    ext g
    induction g using Homotopic.Quotient.ind with
    | mk γ =>
        calc
          dMonoid
              (((cocone O x hx).ι.app T).hom
                (FundamentalGroup.fromPath ⟦γ⟧)) =
            dMonoid (FundamentalGroup.fromPath ⟦γ.map continuous_subtype_val⟧) := by
              rw [cocone_app_eq_stage_union_to_ambient_hom O x hx]
              exact congrArg dMonoid (stage_union_to_ambient_hom_apply_stage_loop O x hx T γ)
          _ =
              stage_value (γ.map continuous_subtype_val) T
                (stage_loop_range_subset O x hx T γ) := by
                exact raw_value_spec (γ.map continuous_subtype_val) T
                  (stage_loop_range_subset O x hx T γ)
          _ = (C.ι.app T).hom (FundamentalGroup.fromPath ⟦γ⟧) := by
                simpa [stage_value] using congrArg
                  (fun q ↦ (C.ι.app T).hom (FundamentalGroup.fromPath q))
                  (congrArg Homotopic.Quotient.mk <|
                    ambient_loop_in_stage_of_stage_loop O x hx T γ)
  · intro ψ hψ
    ext g
    induction g using Homotopic.Quotient.ind with
    | mk γ =>
        obtain ⟨T, hγ⟩ :=
          loop_image_subset_finite_union_of_intersection_closed_subcover
            O hO hinter γ
        let loopClass :
            FundamentalGroup U[O, T] (stageBasepoint O x hx T) :=
          FundamentalGroup.fromPath ⟦ambient_loop_in_stage O x hx T γ hγ⟧
        have hrestrict_apply :
            (((cocone
                O x hx).ι.app T) ≫ ψ).hom loopClass =
              (C.ι.app T).hom loopClass := by
          -- Apply the assumed factorization equality at the stage containing `γ`.
          simpa [loopClass, GrpCat.comp_apply] using congrArg
            (fun k ↦ k.hom loopClass) (hψ T)
        have hraw :
            (C.ι.app T).hom loopClass =
              dMonoid (FundamentalGroup.fromPath ⟦γ⟧) := by
          -- The definition of `dMonoid` evaluates an ambient loop by any containing stage.
          simpa [loopClass, stage_value, raw_value, dMonoid] using (raw_value_spec γ T hγ).symm
        have hleft :
            ψ.hom (FundamentalGroup.fromPath ⟦γ⟧) =
              (((cocone
                  O x hx).ι.app T) ≫ ψ).hom loopClass := by
          rw [cocone_app_eq_stage_union_to_ambient_hom O x hx]
          simpa [loopClass, GrpCat.comp_apply] using
            (congrArg ψ.hom
              (stage_union_to_ambient_hom_apply_ambient_loop O x hx T γ hγ)).symm
        exact hleft.trans (hrestrict_apply.trans hraw)

namespace IntersectionClosedSubcover.FundamentalGroupCocone

/-- Lemma 2.7.10: the colimit of the groups `π₁(U_S, x)` over nonempty finite
intersection-closed subcollections `S` of the cover is the ambient fundamental group
`π₁(X, x)`. -/
-- Proof sketch: by ProofStep 2.7.9, every loop in `X` and every homotopy between loops is
-- contained in some finite union `U_S` coming from a finite subcollection closed under nonempty
-- finite intersections. This lets one define the universal map out of `π₁(X, x)` by choosing a
-- sufficiently large `S` for each loop class, while the homotopy statement guarantees
-- well-definedness and compatibility with the transition maps, giving the colimit universal
-- property.
def isColimit
    (O : ι → TopologicalSpace.Opens X)
    (hO : TopologicalSpace.IsOpenCover O)
    (x : X) (hx : ∀ i, x ∈ O i)
    (hinter : ClosedUnderNonemptyFiniteIntersections O) :
    IsColimit (cocone O x hx) :=
  IsColimit.ofExistsUnique
    (finite_intersection_closed_subcover_fundamental_group_existsUnique O hO x hx hinter)

/-- The colimit cocone from the finite-intersection-closed van Kampen lemma induces the canonical
comparison morphism from `π₁(X, x)` to any other cocone over the finite-subcover diagram, and this
morphism is compatible with the cocone legs. -/
-- Proof sketch: apply the universal property packaged by
-- `IntersectionClosedSubcover.FundamentalGroupCocone.isColimit`; its `fac` field
-- gives the stated compatibility for each finite intersection-closed subcover.
theorem desc_fac
    (O : ι → TopologicalSpace.Opens X)
    (hO : TopologicalSpace.IsOpenCover O)
    (x : X) (hx : ∀ i, x ∈ O i)
    (hinter : ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (diagram O x hx))
    (T : IntersectionClosedSubcover O) :
    (cocone O x hx).ι.app T ≫
        (isColimit O hO x hx hinter).desc S =
      S.ι.app T := by
  simpa using
    (isColimit O hO x hx hinter).fac S T

end IntersectionClosedSubcover.FundamentalGroupCocone
