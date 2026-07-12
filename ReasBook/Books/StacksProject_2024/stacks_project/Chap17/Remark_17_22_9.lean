import Mathlib
import Mathlib.CategoryTheory.Sites.Limits
import StacksProject_2024.Chap06.Example_6_29_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

local notation "JX" => Opens.grothendieckTopology twoClosedPointsSpace

/- Domain-style sampling for Remark 17.22.9:
- primary domain: filtered-colimit comparison morphisms for global sections of abelian sheaves on a
  topological space;
- sampled owner abstractions:
  `twoClosedPointsSpace`,
  `tailPushforwardIntegerSheafFunctor`,
  `sheafSections`,
  `colimit.post`,
  `ConcreteCategory.isIso_iff_bijective`,
  `tailPushforwardIntegerSheaf_exists_global_sections_colimit`,
  `tailPushforwardColimit_global_sections_comparison_isIso`;
- best owner abstraction: the explicit comparison morphism
  `colimit.post tailPushforwardIntegerSheafFunctor
    ((sheafSections JX AddCommGrpCat).obj (op ⊤))`;
- primitive data: the imported witness space `twoClosedPointsSpace` and filtered diagram
  `tailPushforwardIntegerSheafFunctor`;
- derived API: the class-level statement
  `PreservesColimit tailPushforwardIntegerSheafFunctor
    ((sheafSections JX AddCommGrpCat).obj (op ⊤))`
  and its negation, which are bridge consequences of the comparison-map failure;
- layer triage:
  `source-facing`: the explicit map
    `colim Γ(X, j_{n,*}\underline{Z}) → Γ(X, colim j_{n,*}\underline{Z})`;
  `core/canonical`: `colimit.post`;
  `bridge/view`: the explicit Chapter 6 witness
    `twoClosedPointsSpace`, `tailPushforwardIntegerSheafFunctor`, together with the derived
    `PreservesColimit` reformulation.
-/

-- Proof sketch: Example `6.29.2` identifies the colimit of the global sections of the system
-- `j_{n,*}\underline{\mathbf Z}` on a quasi-compact space with an object of sections `M`, while
-- the global sections of the colimit sheaf are `M ⊞ M`; hence global sections need not preserve a
-- filtered colimit on a quasi-compact space. The internal bridge proof uses `IsCompact univ`, but
-- the public witness is the owner-level class `CompactSpace`.
/-- Helper for Remark 17.22.9: the explicit subbasis generating the topology on the
two-closed-points space. -/
private def twoClosedPointsSubbasis : Set (Set twoClosedPointsSpace) :=
  {U | (∃ n : ℕ, U = ({TwoClosedPointsPoint.xi n} : Set twoClosedPointsSpace)) ∨
      U = twoClosedPointsS1BasicOpen ∨ U = twoClosedPointsS2BasicOpen}

/-- Helper for Remark 17.22.9: any cover of the two-closed-points space by members of the explicit
subbasis already contains the two distinguished basic opens, so those two opens give a finite
subcover. -/
private theorem twoClosedPoints_subbasis_cover_has_pair_subcover
    {P : Set (Set twoClosedPointsSpace)} (hP : P ⊆ twoClosedPointsSubbasis)
    (hcover : ⋃₀ P = (Set.univ : Set twoClosedPointsSpace)) :
    ∃ Q ⊆ P, Q.Finite ∧ ⋃₀ Q = (Set.univ : Set twoClosedPointsSpace) := by
  -- Covering the closed point `s1` forces the basic neighborhood of `s1` to appear in the cover.
  have hs1mem : twoClosedPointsS1BasicOpen ∈ P := by
    have hs1 : (TwoClosedPointsPoint.s1 : twoClosedPointsSpace) ∈ ⋃₀ P := by
      simpa [hcover]
    rcases Set.mem_sUnion.mp hs1 with ⟨U, hUP, hs1U⟩
    rcases hP hUP with hxi | hS1 | hS2
    · rcases hxi with ⟨n, rfl⟩
      simp at hs1U
    · simpa [hS1] using hUP
    · exfalso
      subst hS2
      simpa [twoClosedPointsS2BasicOpen, twoClosedPointsXiSet] using hs1U
  -- The same argument at `s2` forces the second distinguished basic open into the cover.
  have hs2mem : twoClosedPointsS2BasicOpen ∈ P := by
    have hs2 : (TwoClosedPointsPoint.s2 : twoClosedPointsSpace) ∈ ⋃₀ P := by
      simpa [hcover]
    rcases Set.mem_sUnion.mp hs2 with ⟨U, hUP, hs2U⟩
    rcases hP hUP with hxi | hS1 | hS2
    · rcases hxi with ⟨n, rfl⟩
      simp at hs2U
    · exfalso
      subst hS1
      simpa [twoClosedPointsS1BasicOpen, twoClosedPointsXiSet] using hs2U
    · simpa [hS2] using hUP
  refine ⟨{twoClosedPointsS1BasicOpen, twoClosedPointsS2BasicOpen}, ?_, ?_, ?_⟩
  · intro U hU
    have hU' : U = twoClosedPointsS1BasicOpen ∨ U = twoClosedPointsS2BasicOpen := by
      simpa using hU
    rcases hU' with rfl | rfl
    · exact hs1mem
    · exact hs2mem
  · simp
  · -- The two distinguished opens already cover both closed points and every generic point.
    ext x
    constructor
    · intro hx
      simp
    · intro hx
      cases x with
      | s1 =>
          simp [twoClosedPointsS1BasicOpen]
      | s2 =>
          simp [twoClosedPointsS2BasicOpen]
      | xi n =>
          simp [twoClosedPointsS1BasicOpen, twoClosedPointsS2BasicOpen, twoClosedPointsXiSet]

private theorem isCompact_univ_twoClosedPointsSpace :
    IsCompact (Set.univ : Set twoClosedPointsSpace) := by
  -- The topology is definitionally `generateFrom` the explicit Chapter 6 subbasis.
  have hcompact : CompactSpace twoClosedPointsSpace := by
    refine compactSpace_generateFrom rfl ?_
    intro P hP hcover
    exact twoClosedPoints_subbasis_cover_has_pair_subcover hP hcover
  -- Whole-space compactness is the `IsCompact univ` form of `CompactSpace`.
  exact isCompact_univ_iff.mpr hcompact

/-- The two-closed-points space from Example 6.29.2 is quasi-compact. -/
theorem compactSpace_twoClosedPointsSpace : CompactSpace twoClosedPointsSpace :=
  isCompact_univ_iff.mp isCompact_univ_twoClosedPointsSpace

/-- Helper for Remark 17.22.9: the Chapter 6 comparison from the colimit of global sections to the
eventual-sequence colimit is computed on each colimit leg by the stagewise product map. -/
private theorem tail_pushforward_integer_sheaf_global_sections_colimit_comparison_comp_ι (n : ℕ) :
    colimit.ι tailPushforwardIntegerSheafGlobalSectionsFunctor n ≫
      tailPushforwardIntegerSheafGlobalSectionsColimitComparison =
    tailPushforwardIntegerSheafGlobalSectionsToProduct n ≫
      colimit.ι tailIntegerProductFunctor n := by
  -- Unfold the public comparison map so `colimit.ι_desc` can read off the defining cocone leg.
  unfold tailPushforwardIntegerSheafGlobalSectionsColimitComparison
  simpa using colimit.ι_desc (c := _) (j := n)

/-- Helper for Remark 17.22.9: after transporting the colimit of global sections across the Chapter
6 comparison isomorphism, the `n`th colimit leg becomes the `n`th product injection followed by the
inverse comparison. -/
private theorem tail_pushforward_integer_sheaf_global_sections_leg_transport (n : ℕ)
    [IsIso tailPushforwardIntegerSheafGlobalSectionsColimitComparison] :
    colimit.ι tailPushforwardIntegerSheafGlobalSectionsFunctor n =
      tailPushforwardIntegerSheafGlobalSectionsToProduct n ≫
        colimit.ι tailIntegerProductFunctor n ≫
          inv tailPushforwardIntegerSheafGlobalSectionsColimitComparison := by
  -- Transport the colimit leg across the Chapter 6 comparison isomorphism.
  calc
    colimit.ι tailPushforwardIntegerSheafGlobalSectionsFunctor n =
        colimit.ι tailPushforwardIntegerSheafGlobalSectionsFunctor n ≫
          tailPushforwardIntegerSheafGlobalSectionsColimitComparison ≫
            inv tailPushforwardIntegerSheafGlobalSectionsColimitComparison := by
      simp
    _ =
        tailPushforwardIntegerSheafGlobalSectionsToProduct n ≫
          colimit.ι tailIntegerProductFunctor n ≫
            inv tailPushforwardIntegerSheafGlobalSectionsColimitComparison := by
      simpa [Category.assoc] using
        congrArg
          (fun f ↦ f ≫ inv tailPushforwardIntegerSheafGlobalSectionsColimitComparison)
          (tail_pushforward_integer_sheaf_global_sections_colimit_comparison_comp_ι n)

/-- Helper for Remark 17.22.9: after transporting the Chapter 6 comparison to a map
`M ⟶ M ⊞ M`, the first projection is the identity on `M`. -/
private theorem transported_globalSections_comparison_fst_eq_id
    [IsIso tailPushforwardIntegerSheafGlobalSectionsColimitComparison]
    [IsIso tailPushforwardColimitGlobalSectionsComparison] :
    (inv tailPushforwardIntegerSheafGlobalSectionsColimitComparison ≫
        colimit.post tailPushforwardIntegerSheafFunctor
          ((sheafSections JX AddCommGrpCat).obj (op ⊤)) ≫
        tailPushforwardColimitGlobalSectionsComparison) ≫
      biprod.fst =
    𝟙 eventualIntegerSequenceColimit := by
  -- First compute the untransported first projection by comparing on each colimit leg.
  have hfst :
      colimit.post tailPushforwardIntegerSheafFunctor
          ((sheafSections JX AddCommGrpCat).obj (op ⊤)) ≫
        tailPushforwardColimitGlobalSectionsComparison ≫
          biprod.fst =
        tailPushforwardIntegerSheafGlobalSectionsColimitComparison := by
    apply colimit.hom_ext
    intro n
    -- Each stage is the diagonal pair map, and the first projection reads off the left component.
    rw [← Category.assoc, ← Category.assoc, colimit.ι_post]
    have hstage :=
      congrArg
        (fun f ↦ f ≫ biprod.fst)
        (tailPushforwardColimitGlobalSectionsComparison_comp_ι_diagonal n)
    change
      (((sheafSections JX AddCommGrpCat).obj (op ⊤)).map
            (colimit.ι tailPushforwardIntegerSheafFunctor n) ≫
          tailPushforwardColimitGlobalSectionsComparison) ≫
        biprod.fst =
      (biprod.lift
            (tailPushforwardIntegerSheafGlobalSectionsToProduct n ≫
              colimit.ι tailIntegerProductFunctor n)
            (tailPushforwardIntegerSheafGlobalSectionsToProduct n ≫
              colimit.ι tailIntegerProductFunctor n)) ≫
        biprod.fst at hstage
    have hstage' :
        (((sheafSections JX AddCommGrpCat).obj (op ⊤)).map
              (colimit.ι tailPushforwardIntegerSheafFunctor n) ≫
            tailPushforwardColimitGlobalSectionsComparison) ≫
          biprod.fst =
        tailPushforwardIntegerSheafGlobalSectionsToProduct n ≫
          colimit.ι tailIntegerProductFunctor n := by
      simpa [biprod.lift_fst] using hstage
    exact hstage'.trans
      (tail_pushforward_integer_sheaf_global_sections_colimit_comparison_comp_ι n).symm
  -- Precompose with the inverse of the left comparison isomorphism to transport back to `M`.
  calc
    (inv tailPushforwardIntegerSheafGlobalSectionsColimitComparison ≫
          colimit.post tailPushforwardIntegerSheafFunctor
            ((sheafSections JX AddCommGrpCat).obj (op ⊤)) ≫
          tailPushforwardColimitGlobalSectionsComparison) ≫
        biprod.fst =
      inv tailPushforwardIntegerSheafGlobalSectionsColimitComparison ≫
        tailPushforwardIntegerSheafGlobalSectionsColimitComparison := by
        simpa [Category.assoc] using
          congrArg
            (fun f ↦ inv tailPushforwardIntegerSheafGlobalSectionsColimitComparison ≫ f)
            hfst
    _ = 𝟙 eventualIntegerSequenceColimit := by
      simp

/-- Helper for Remark 17.22.9: after the same transport, the second projection is also the
identity on `M`. -/
private theorem transported_globalSections_comparison_snd_eq_id
    [IsIso tailPushforwardIntegerSheafGlobalSectionsColimitComparison]
    [IsIso tailPushforwardColimitGlobalSectionsComparison] :
    (inv tailPushforwardIntegerSheafGlobalSectionsColimitComparison ≫
        colimit.post tailPushforwardIntegerSheafFunctor
          ((sheafSections JX AddCommGrpCat).obj (op ⊤)) ≫
        tailPushforwardColimitGlobalSectionsComparison) ≫
      biprod.snd =
    𝟙 eventualIntegerSequenceColimit := by
  -- The second projection is computed by the same stagewise diagonal formula.
  have hsnd :
      colimit.post tailPushforwardIntegerSheafFunctor
          ((sheafSections JX AddCommGrpCat).obj (op ⊤)) ≫
        tailPushforwardColimitGlobalSectionsComparison ≫
          biprod.snd =
        tailPushforwardIntegerSheafGlobalSectionsColimitComparison := by
    apply colimit.hom_ext
    intro n
    -- Each stage is diagonal, so the second projection again recovers the same component.
    rw [← Category.assoc, ← Category.assoc, colimit.ι_post]
    have hstage :=
      congrArg
        (fun f ↦ f ≫ biprod.snd)
        (tailPushforwardColimitGlobalSectionsComparison_comp_ι_diagonal n)
    change
      (((sheafSections JX AddCommGrpCat).obj (op ⊤)).map
            (colimit.ι tailPushforwardIntegerSheafFunctor n) ≫
          tailPushforwardColimitGlobalSectionsComparison) ≫
        biprod.snd =
      (biprod.lift
            (tailPushforwardIntegerSheafGlobalSectionsToProduct n ≫
              colimit.ι tailIntegerProductFunctor n)
            (tailPushforwardIntegerSheafGlobalSectionsToProduct n ≫
              colimit.ι tailIntegerProductFunctor n)) ≫
        biprod.snd at hstage
    have hstage' :
        (((sheafSections JX AddCommGrpCat).obj (op ⊤)).map
              (colimit.ι tailPushforwardIntegerSheafFunctor n) ≫
            tailPushforwardColimitGlobalSectionsComparison) ≫
          biprod.snd =
        tailPushforwardIntegerSheafGlobalSectionsToProduct n ≫
          colimit.ι tailIntegerProductFunctor n := by
      simpa [biprod.lift_snd] using hstage
    exact hstage'.trans
      (tail_pushforward_integer_sheaf_global_sections_colimit_comparison_comp_ι n).symm
  -- Transport the second projection back across the left comparison isomorphism.
  calc
    (inv tailPushforwardIntegerSheafGlobalSectionsColimitComparison ≫
          colimit.post tailPushforwardIntegerSheafFunctor
            ((sheafSections JX AddCommGrpCat).obj (op ⊤)) ≫
          tailPushforwardColimitGlobalSectionsComparison) ≫
        biprod.snd =
      inv tailPushforwardIntegerSheafGlobalSectionsColimitComparison ≫
        tailPushforwardIntegerSheafGlobalSectionsColimitComparison := by
        simpa [Category.assoc] using
          congrArg
            (fun f ↦ inv tailPushforwardIntegerSheafGlobalSectionsColimitComparison ≫ f)
            hsnd
    _ = 𝟙 eventualIntegerSequenceColimit := by
      simp

/-- Helper for Remark 17.22.9: the transported comparison is the diagonal map
`M ⟶ M ⊞ M`. -/
private theorem transported_globalSections_comparison_eq_diagonal
    [IsIso tailPushforwardIntegerSheafGlobalSectionsColimitComparison]
    [IsIso tailPushforwardColimitGlobalSectionsComparison] :
    inv tailPushforwardIntegerSheafGlobalSectionsColimitComparison ≫
        colimit.post tailPushforwardIntegerSheafFunctor
          ((sheafSections JX AddCommGrpCat).obj (op ⊤)) ≫
        tailPushforwardColimitGlobalSectionsComparison =
      biprod.lift (𝟙 eventualIntegerSequenceColimit) (𝟙 eventualIntegerSequenceColimit) := by
  -- Identify the transported comparison by its two projections.
  apply biprod.hom_ext
  · simpa using transported_globalSections_comparison_fst_eq_id
  · simpa using transported_globalSections_comparison_snd_eq_id

/-- Helper for Remark 17.22.9: the class of the constant-one tail sequence is nonzero in the
eventual-sequence colimit `M`. -/
private theorem constant_one_eventualIntegerSequenceColimit_ne_zero :
    colimit.ι tailIntegerProductFunctor 0 (fun _ => (1 : ℤ)) ≠
      (0 : eventualIntegerSequenceColimit) := by
  letI : PreservesFilteredColimits (forget AddCommGrpCat) :=
    AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
  letI : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat) :=
    preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat)
  letI : PreservesColimit tailIntegerProductFunctor (forget AddCommGrpCat) := by
    infer_instance
  have hforget :
      Function.Bijective
        (colimit.post tailIntegerProductFunctor (forget AddCommGrpCat)) := by
    exact (CategoryTheory.isIso_iff_bijective _).1 inferInstance
  intro hzero
  -- Compare the two representatives after applying the forgetful colimit comparison isomorphism.
  have hleft :
      colimit.post tailIntegerProductFunctor (forget AddCommGrpCat)
          (colimit.ι (tailIntegerProductFunctor ⋙ forget AddCommGrpCat) 0
            (fun _ => (1 : ℤ))) =
        colimit.ι tailIntegerProductFunctor 0 (fun _ => (1 : ℤ)) := by
    simpa using
      congrFun (colimit.ι_post tailIntegerProductFunctor (forget AddCommGrpCat) 0)
        (fun _ => (1 : ℤ))
  have hright :
      colimit.post tailIntegerProductFunctor (forget AddCommGrpCat)
          (colimit.ι (tailIntegerProductFunctor ⋙ forget AddCommGrpCat) 0
            (0 : tailIntegerProduct 0)) =
        colimit.ι tailIntegerProductFunctor 0 (0 : tailIntegerProduct 0) := by
    simpa using
      congrFun (colimit.ι_post tailIntegerProductFunctor (forget AddCommGrpCat) 0)
        (0 : tailIntegerProduct 0)
  have hright' :
      colimit.ι tailIntegerProductFunctor 0 (0 : tailIntegerProduct 0) =
        colimit.post tailIntegerProductFunctor (forget AddCommGrpCat)
          (colimit.ι (tailIntegerProductFunctor ⋙ forget AddCommGrpCat) 0
            (0 : tailIntegerProduct 0)) := by
    simpa using hright.symm
  have hzeroStage :
      (0 : eventualIntegerSequenceColimit) =
        colimit.ι tailIntegerProductFunctor 0 (0 : tailIntegerProduct 0) := by
    change 0 = (colimit.ι tailIntegerProductFunctor 0).hom 0
    exact ((colimit.ι tailIntegerProductFunctor 0).hom.map_zero).symm
  have himage :
      colimit.post tailIntegerProductFunctor (forget AddCommGrpCat)
          (colimit.ι (tailIntegerProductFunctor ⋙ forget AddCommGrpCat) 0
            (fun _ => (1 : ℤ))) =
        colimit.post tailIntegerProductFunctor (forget AddCommGrpCat)
          (colimit.ι (tailIntegerProductFunctor ⋙ forget AddCommGrpCat) 0
            (0 : tailIntegerProduct 0)) := by
    exact hleft.trans (hzero.trans (hzeroStage.trans hright'))
  have hsame :
      colimit.ι (tailIntegerProductFunctor ⋙ forget AddCommGrpCat) 0
          (fun _ => (1 : ℤ)) =
        colimit.ι (tailIntegerProductFunctor ⋙ forget AddCommGrpCat) 0
          (0 : tailIntegerProduct 0) :=
    hforget.1 himage
  rcases (Types.FilteredColimit.colimit_eq_iff
      (F := tailIntegerProductFunctor ⋙ forget AddCommGrpCat)).1 hsame with ⟨k, f, g, hfg⟩
  -- Evaluating the common-stage equality at the index `k` forces `1 = 0`, contradiction.
  have hEval := congrFun hfg ⟨k, le_rfl⟩
  have hEq0 : (1 : ℤ) = 0 := by
    simpa only [tailIntegerProduct, tailIntegerProductFunctor, tailIntegerProductMap] using hEval
  exact one_ne_zero hEq0

/-- Helper for Remark 17.22.9: once one exhibits a nonzero element of `M`, the diagonal map
`M ⟶ M ⊞ M` cannot be an isomorphism. -/
private theorem eventualIntegerSequenceColimit_diagonal_not_isIso :
    ¬ IsIso (biprod.lift (𝟙 eventualIntegerSequenceColimit) (𝟙 eventualIntegerSequenceColimit)) := by
  intro hdiag
  let m : eventualIntegerSequenceColimit :=
    colimit.ι tailIntegerProductFunctor 0 (fun _ => (1 : ℤ))
  have hm : m ≠ 0 := constant_one_eventualIntegerSequenceColimit_ne_zero
  have hsurj :
      Function.Surjective
        (biprod.lift (𝟙 eventualIntegerSequenceColimit) (𝟙 eventualIntegerSequenceColimit) :
          eventualIntegerSequenceColimit ⟶
            eventualIntegerSequenceColimit ⊞ eventualIntegerSequenceColimit) := by
    exact (ConcreteCategory.isIso_iff_bijective _).1 hdiag |>.2
  -- The off-diagonal point `(m, 0)` is represented by `biprod.inl m` and cannot lie on the diagonal.
  rcases hsurj
      ((biprod.inl :
          eventualIntegerSequenceColimit ⟶
            eventualIntegerSequenceColimit ⊞ eventualIntegerSequenceColimit) m) with ⟨x, hx⟩
  have hx_fst : x = m := by
    have := congrArg
      (fun z ↦
        (biprod.fst :
          eventualIntegerSequenceColimit ⊞ eventualIntegerSequenceColimit ⟶
            eventualIntegerSequenceColimit) z)
      hx
    change
      ((biprod.lift (𝟙 eventualIntegerSequenceColimit) (𝟙 eventualIntegerSequenceColimit) ≫
            biprod.fst :
          eventualIntegerSequenceColimit ⟶ eventualIntegerSequenceColimit) x) =
        (((biprod.inl :
              eventualIntegerSequenceColimit ⟶
                eventualIntegerSequenceColimit ⊞ eventualIntegerSequenceColimit) ≫
            biprod.fst :
          eventualIntegerSequenceColimit ⟶ eventualIntegerSequenceColimit) m) at this
    simpa using this
  have hx_snd : x = 0 := by
    have := congrArg
      (fun z ↦
        (biprod.snd :
          eventualIntegerSequenceColimit ⊞ eventualIntegerSequenceColimit ⟶
            eventualIntegerSequenceColimit) z)
      hx
    change
      ((biprod.lift (𝟙 eventualIntegerSequenceColimit) (𝟙 eventualIntegerSequenceColimit) ≫
            biprod.snd :
          eventualIntegerSequenceColimit ⟶ eventualIntegerSequenceColimit) x) =
        (((biprod.inl :
              eventualIntegerSequenceColimit ⟶
                eventualIntegerSequenceColimit ⊞ eventualIntegerSequenceColimit) ≫
            biprod.snd :
          eventualIntegerSequenceColimit ⟶ eventualIntegerSequenceColimit) m) at this
    simpa using this
  have hmzero : m = 0 := by
    calc
      m = x := hx_fst.symm
      _ = 0 := hx_snd
  exact hm hmzero

/-- Remark 17.22.9: on the Chapter 6 two-closed-points space, the canonical comparison map
`colim Γ(X, j_{n,*}\underline{Z}) → Γ(X, colim j_{n,*}\underline{Z})` is not an isomorphism. -/
theorem twoClosedPoints_globalSections_colimitComparison_not_isIso :
    ¬ IsIso
      (colimit.post tailPushforwardIntegerSheafFunctor
        ((sheafSections JX AddCommGrpCat).obj (op ⊤))) := by
  intro hcomparison
  let _ : IsIso tailPushforwardIntegerSheafGlobalSectionsColimitComparison :=
    tailPushforwardIntegerSheaf_exists_global_sections_colimit
  let _ : IsIso tailPushforwardColimitGlobalSectionsComparison :=
    tailPushforwardColimit_global_sections_comparison_isIso
  let _ : IsIso
      (colimit.post tailPushforwardIntegerSheafFunctor
        ((sheafSections JX AddCommGrpCat).obj (op ⊤))) := hcomparison
  let δ : eventualIntegerSequenceColimit ⟶
      eventualIntegerSequenceColimit ⊞ eventualIntegerSequenceColimit :=
    inv tailPushforwardIntegerSheafGlobalSectionsColimitComparison ≫
      colimit.post tailPushforwardIntegerSheafFunctor
        ((sheafSections JX AddCommGrpCat).obj (op ⊤)) ≫
      tailPushforwardColimitGlobalSectionsComparison
  -- Route correction: the owner-level Chapter 6 leg formula now lets the source proof identify the
  -- transported comparison with the diagonal on `M`.
  have hδ :
      δ =
        biprod.lift (𝟙 eventualIntegerSequenceColimit) (𝟙 eventualIntegerSequenceColimit) := by
    simpa [δ] using transported_globalSections_comparison_eq_diagonal
  -- Any isomorphism of the original comparison would transport to an isomorphism of the diagonal.
  have hdiag :
      IsIso (biprod.lift (𝟙 eventualIntegerSequenceColimit) (𝟙 eventualIntegerSequenceColimit)) := by
    rw [← hδ]
    let eδ : eventualIntegerSequenceColimit ≅
        eventualIntegerSequenceColimit ⊞ eventualIntegerSequenceColimit :=
      (asIso tailPushforwardIntegerSheafGlobalSectionsColimitComparison).symm ≪≫
        asIso
          (colimit.post tailPushforwardIntegerSheafFunctor
            ((sheafSections JX AddCommGrpCat).obj (op ⊤))) ≪≫
        asIso tailPushforwardColimitGlobalSectionsComparison
    change IsIso eδ.hom
    infer_instance
  exact eventualIntegerSequenceColimit_diagonal_not_isIso hdiag

/-- Remark 17.22.9: the failure of the canonical comparison map implies that the global-sections
functor does not preserve this filtered colimit. -/
theorem twoClosedPoints_globalSections_not_preserves_filteredColimit :
    ¬ PreservesColimit tailPushforwardIntegerSheafFunctor
      ((sheafSections JX AddCommGrpCat).obj (op ⊤)) := by
  intro hpres
  let _ : PreservesColimit tailPushforwardIntegerSheafFunctor
      ((sheafSections JX AddCommGrpCat).obj (op ⊤)) := hpres
  exact twoClosedPoints_globalSections_colimitComparison_not_isIso inferInstance

/-- Remark 17.22.9: Example 6.29.2 gives a quasi-compact space for which the canonical comparison
map from the colimit of global sections of a filtered system of sheaves of abelian groups to the
global sections of the colimit sheaf is not an isomorphism. Thus some hypothesis beyond
quasi-compactness of `X` is necessary in Lemma 17.22.8. -/
theorem quasiCompact_does_not_force_globalSections_colimitComparison_isIso :
    ∃ X : TopCat.{0}, CompactSpace X ∧
      ∃ 𝓕 : ℕ ⥤ X.Sheaf AddCommGrpCat.{0},
        ¬ IsIso
          (colimit.post 𝓕
            ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op ⊤))) := by
  refine ⟨twoClosedPointsSpace, compactSpace_twoClosedPointsSpace, tailPushforwardIntegerSheafFunctor,
    ?_⟩
  simpa using twoClosedPoints_globalSections_colimitComparison_not_isIso

/-- Remark 17.22.9: in particular, quasi-compactness does not force the global-sections functor to
preserve filtered colimits. -/
theorem quasiCompact_does_not_force_globalSections_preserve_filteredColimits :
    ∃ X : TopCat.{0}, CompactSpace X ∧
      ∃ 𝓕 : ℕ ⥤ X.Sheaf AddCommGrpCat.{0},
        ¬ PreservesColimit 𝓕
          ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op ⊤)) := by
  refine ⟨twoClosedPointsSpace, compactSpace_twoClosedPointsSpace, tailPushforwardIntegerSheafFunctor,
    ?_⟩
  simpa using twoClosedPoints_globalSections_not_preserves_filteredColimit
