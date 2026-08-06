import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.CategoryTheory.WithTerminal.Cone
import Mathlib.Tactic.FunProp
import Mathlib.Topology.Algebra.Affine
import Mathlib.Topology.Instances.AddCircle.Defs
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Theorem_1_5_11
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Definition_2_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Proposition_2_8_1

open CategoryTheory Limits
open AddCircle
open unitInterval
open scoped unitInterval

noncomputable section

/-- The circle with its usual basepoint `1`, viewed as an object of the category of based spaces. -/
noncomputable abbrev based_circle : BasedSpace :=
  Under.mk (TopCat.terminalIsoPUnit.hom ≫ TopCat.ofHom (ContinuousMap.const PUnit (1 : Circle)))

/-- The chosen basepoint of `based_circle` is the unit point of `Circle`. -/
@[simp] theorem underTopBasepoint_based_circle :
    underTopBasepoint based_circle = (1 : Circle) := by
  rfl

/- `BasedSpace` currently supplies coproducts for small (`Type`-indexed) families. A genuinely
large-index version would require a separate smallness/shrinking construction, so the index below
is deliberately small rather than accidentally universe-specialized. -/
/-- The wedge sum of `ι` copies of the based circle. -/
noncomputable abbrev wedge_of_circles (ι : Type) : BasedSpace :=
  ∐ (fun _ : ι ↦ based_circle)

/-- The wedge of circles is the coproduct of the constant family of based circles. -/
theorem wedge_of_circles_def (ι : Type) :
    wedge_of_circles ι = ∐ (fun _ : ι ↦ based_circle) :=
  rfl

/-- Helper for Corollary 2.8.2: the standard `AddCircle (2π)` chart uses the canonical positive
period instance. -/
private instance two_pi_pos_fact : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Helper for Corollary 2.8.2: the based circle inherits the ambient `T1` separation property of
`Circle`. -/
private instance based_circle_t1Space : T1Space based_circle.right := by
  simpa [based_circle] using (inferInstance : T1Space Circle)

/-- Helper for Corollary 2.8.2: the circle itself is path connected via the additive-circle
parameterization. -/
private instance circle_pathConnectedSpace : PathConnectedSpace Circle :=
  let e : AddCircle (2 * Real.pi) ≃ₜ Circle := homeomorphCircle'
  let hsurj := e.surjective
  hsurj.pathConnectedSpace e.continuous

/-- Helper for Corollary 2.8.2: the based circle inherits path connectedness from `Circle`. -/
private instance based_circle_pathConnectedSpace : PathConnectedSpace based_circle.right := by
  simpa [based_circle] using (inferInstance : PathConnectedSpace Circle)

/-- Helper for Corollary 2.8.2: the open interval chart used to cut the circle at one point. -/
private abbrev circle_chart_domain : Set ℝ :=
  Set.Ioo (-Real.pi) (-Real.pi + 2 * Real.pi)

/-- Helper for Corollary 2.8.2: the interval chart contains the angle `0`. -/
private theorem zero_mem_circle_chart_domain :
    (0 : ℝ) ∈ circle_chart_domain := by
  constructor
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

/-- Helper for Corollary 2.8.2: the interval chart basepoint corresponding to the circle point
`1`. -/
private def circle_chart_basepoint : circle_chart_domain :=
  ⟨0, zero_mem_circle_chart_domain⟩

/-- Helper for Corollary 2.8.2: the missing point in the circle chart is the image of `-π`. -/
private abbrev circle_chart_removed_point : Circle :=
  AddCircle.homeomorphCircle' (-Real.pi : AddCircle (2 * Real.pi))

/-- Helper for Corollary 2.8.2: the removed chart point is also `exp π`, so it is not the basepoint
`1`. -/
private theorem circle_chart_removed_point_eq_exp_pi :
    circle_chart_removed_point = Circle.exp Real.pi := by
  change Circle.exp (-Real.pi) = Circle.exp Real.pi
  exact Circle.exp_eq_exp.mpr ⟨-1, by ring_nf⟩

/-- Helper for Corollary 2.8.2: the circle basepoint `1` is not the chart cut point. -/
private theorem one_ne_circle_chart_removed_point :
    (1 : Circle) ≠ circle_chart_removed_point := by
  rw [circle_chart_removed_point_eq_exp_pi]
  intro h
  have hpi_lt : -Real.pi < Real.pi := by
    linarith [Real.pi_pos]
  have harg_exp : ((↑(Circle.exp Real.pi) : ℂ).arg) = Real.pi := by
    exact Circle.arg_exp hpi_lt le_rfl
  have hcoe : ((↑(Circle.exp Real.pi) : ℂ)) = 1 := by
    simpa using (congrArg (fun z : Circle ↦ (z : ℂ)) h).symm
  have harg_one : ((↑(Circle.exp Real.pi) : ℂ).arg) = 0 := by
    simp [hcoe]
  linarith [Real.pi_pos, harg_exp, harg_one]

/-- Helper for Corollary 2.8.2: the circle punctured at the chart cut point, based at `1`. -/
private def circle_cut_basepoint : {z : Circle | z ≠ circle_chart_removed_point} :=
  ⟨1, one_ne_circle_chart_removed_point⟩

/-- Helper for Corollary 2.8.2: the additive-circle chart is a homeomorphism from the interval to
the punctured additive circle. -/
private noncomputable def circle_chart_addCircle_homeomorph :
    circle_chart_domain ≃ₜ
      {x : AddCircle (2 * Real.pi) | x ≠ (-Real.pi : AddCircle (2 * Real.pi))} :=
  (openPartialHomeomorphCoe (2 * Real.pi) (-Real.pi)).toHomeomorphSourceTarget

/-- Helper for Corollary 2.8.2: the circle homeomorphism preserves the puncture condition. -/
private theorem circle_cut_membership_iff
    (x : AddCircle (2 * Real.pi)) :
    x ≠ (-Real.pi : AddCircle (2 * Real.pi)) ↔
      AddCircle.homeomorphCircle' x ≠ circle_chart_removed_point := by
  constructor <;> intro hx hEq
  · apply hx
    exact AddCircle.homeomorphCircle'.injective (by simpa [circle_chart_removed_point] using hEq)
  · apply hx
    simpa [circle_chart_removed_point] using congrArg AddCircle.homeomorphCircle' hEq

/-- Helper for Corollary 2.8.2: the additive-circle puncture identifies with the corresponding
punctured circle. -/
private noncomputable def circle_cut_homeomorph :
    {x : AddCircle (2 * Real.pi) | x ≠ (-Real.pi : AddCircle (2 * Real.pi))} ≃ₜ
      {z : Circle | z ≠ circle_chart_removed_point} :=
  (AddCircle.homeomorphCircle').subtype circle_cut_membership_iff

/-- Helper for Corollary 2.8.2: the interval chart identifies the punctured circle with an open
interval. -/
private noncomputable def circle_chart_to_circle_cut :
    circle_chart_domain ≃ₜ {z : Circle | z ≠ circle_chart_removed_point} :=
  circle_chart_addCircle_homeomorph.trans circle_cut_homeomorph

/-- Helper for Corollary 2.8.2: the angle `0` maps to the circle basepoint `1`. -/
private theorem circle_chart_to_circle_cut_basepoint :
    circle_chart_to_circle_cut circle_chart_basepoint = circle_cut_basepoint := by
  apply Subtype.ext
  change AddCircle.homeomorphCircle'
      ((circle_chart_addCircle_homeomorph circle_chart_basepoint : AddCircle (2 * Real.pi))) = 1
  rw [show
      (circle_chart_addCircle_homeomorph circle_chart_basepoint : AddCircle (2 * Real.pi)) = 0 by
        rfl]
  simpa using (AddCircle.homeomorphCircle'_apply_mk (0 : ℝ)).trans Circle.exp_zero

/-- Helper for Corollary 2.8.2: the inverse chart sends the punctured-circle basepoint back to
angle `0`. -/
private theorem circle_chart_to_circle_cut_symm_basepoint :
    circle_chart_to_circle_cut.symm circle_cut_basepoint = circle_chart_basepoint := by
  apply circle_chart_to_circle_cut.injective
  rw [circle_chart_to_circle_cut.apply_symm_apply, circle_chart_to_circle_cut_basepoint]

/-- Helper for Corollary 2.8.2: the open interval contracts linearly to the angle `0`, fixing that
point throughout the homotopy. -/
private theorem circle_chart_contraction :
    (ContinuousMap.id circle_chart_domain).HomotopicRel
      (ContinuousMap.const circle_chart_domain circle_chart_basepoint)
      {circle_chart_basepoint} := by
  refine ⟨{
    toHomotopy := {
      toFun := fun p ↦
        ⟨AffineMap.lineMap p.2.1 0 p.1.1,
          (convex_Ioo (-Real.pi) (-Real.pi + 2 * Real.pi)).lineMap_mem
            p.2.2 zero_mem_circle_chart_domain p.1.2⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ fun p ↦
          (convex_Ioo (-Real.pi) (-Real.pi + 2 * Real.pi)).lineMap_mem
            p.2.2 zero_mem_circle_chart_domain p.1.2
        simpa [AffineMap.lineMap_apply] using
          (by
            fun_prop :
              Continuous fun q : I × circle_chart_domain ↦
                (AffineMap.lineMap q.2.1 0 q.1.1 : ℝ))
      map_zero_left := by
        intro x
        ext
        simp [AffineMap.lineMap_apply_zero]
      map_one_left := by
        intro x
        ext
        simp [circle_chart_basepoint, AffineMap.lineMap_apply_one]
    }
    prop' := by
      intro t x hx
      have hx' : x = circle_chart_basepoint := by
        simpa only [Set.mem_singleton_iff] using hx
      subst hx'
      ext
      simp [circle_chart_basepoint, AffineMap.lineMap_apply]
  }⟩

/-- Helper for Corollary 2.8.2: transport the interval contraction across the chart to contract
the punctured circle to the basepoint `1`, fixing that basepoint. -/
private theorem circle_cut_contraction :
    (ContinuousMap.id {z : Circle | z ≠ circle_chart_removed_point}).HomotopicRel
      (ContinuousMap.const {z : Circle | z ≠ circle_chart_removed_point} circle_cut_basepoint)
      {circle_cut_basepoint} := by
  obtain ⟨H⟩ := circle_chart_contraction
  refine ⟨{
    toHomotopy := {
      toFun := fun p ↦
        circle_chart_to_circle_cut (H.toHomotopy (p.1, circle_chart_to_circle_cut.symm p.2))
      continuous_toFun := by
        have hpre :
            Continuous fun p : I × {z : Circle | z ≠ circle_chart_removed_point} ↦
              (p.1, circle_chart_to_circle_cut.symm p.2) := by
          fun_prop
        have hHcont : Continuous H.toHomotopy := H.toHomotopy.continuous
        exact circle_chart_to_circle_cut.continuous.comp (hHcont.comp hpre)
      map_zero_left := by
        intro x
        have hzero := congrArg circle_chart_to_circle_cut
          (H.toHomotopy.map_zero_left (circle_chart_to_circle_cut.symm x))
        exact hzero.trans (circle_chart_to_circle_cut.apply_symm_apply x)
      map_one_left := by
        intro x
        have hone := congrArg circle_chart_to_circle_cut
          (H.toHomotopy.map_one_left (circle_chart_to_circle_cut.symm x))
        exact hone.trans circle_chart_to_circle_cut_basepoint
    }
    prop' := by
      intro t x hx
      have hx' : x = circle_cut_basepoint := by
        simpa only [Set.mem_singleton_iff] using hx
      subst hx'
      have hfix :
          H.toHomotopy (t, circle_chart_to_circle_cut.symm circle_cut_basepoint) =
            circle_chart_basepoint := by
        rw [circle_chart_to_circle_cut_symm_basepoint]
        exact H.eq_fst t (by simp : circle_chart_basepoint ∈ ({circle_chart_basepoint} :
          Set circle_chart_domain))
      exact congrArg circle_chart_to_circle_cut hfix |>.trans circle_chart_to_circle_cut_basepoint
  }⟩

/-- Helper for Corollary 2.8.2: the based circle has a contractible punctured neighborhood of the
basepoint `1`. -/
private theorem based_circle_has_contractible_base_neighborhood :
    has_contractible_base_neighborhood based_circle := by
  refine ⟨⟨{z : Circle | z ≠ circle_chart_removed_point}, isOpen_compl_singleton⟩,
    one_ne_circle_chart_removed_point, ?_, circle_cut_contraction⟩
  let _ : ContractibleSpace circle_chart_domain :=
    (convex_Ioo (-Real.pi) (-Real.pi + 2 * Real.pi)).contractibleSpace
      ⟨0, zero_mem_circle_chart_domain⟩
  exact circle_chart_to_circle_cut.symm.contractibleSpace

private abbrev based_circle_pi1 : Type :=
  FundamentalGroup based_circle.right (underTopBasepoint based_circle)

private abbrev based_circle_pi1_family (ι : Type) : ι → Type :=
  fun _ ↦ based_circle_pi1

private noncomputable abbrev based_circle_freeGroupUnit_to_pi1 :
    FreeGroup Unit →* based_circle_pi1 :=
  (FundamentalGroup.mapOfEq (ContinuousMap.id based_circle.right)
      underTopBasepoint_based_circle.symm).comp
    (circleFundamentalGroupMulEquivInt.toMonoidHom.comp
      ((FreeGroup.mulEquivIntOfUnique : FreeGroup Unit ≃* Multiplicative ℤ).toMonoidHom))

private noncomputable abbrev wedge_of_circles_freeGroup_to_coprod (ι : Type) :
    FreeGroup ι →*
      Monoid.CoprodI (based_circle_pi1_family ι) :=
  (Monoid.CoprodI.lift fun i ↦
      let ofi :
          based_circle_pi1 →* Monoid.CoprodI (based_circle_pi1_family ι) :=
          @Monoid.CoprodI.of ι (based_circle_pi1_family ι) _ i
      ofi.comp based_circle_freeGroupUnit_to_pi1).comp
    freeGroupEquivCoprodI.toMonoidHom

/-- The canonical homomorphism from the free group on `ι` to the fundamental group of the wedge of
`ι` circles sends each generator to the standard loop in the corresponding circle summand. -/
noncomputable abbrev wedge_of_circles_fundamental_group_comparison (ι : Type) :
    FreeGroup ι →*
      FundamentalGroup (wedge_of_circles ι).right (underTopBasepoint (wedge_of_circles ι)) :=
  (wedge_fundamental_group_comparison fun _ : ι ↦ based_circle).comp
    (wedge_of_circles_freeGroup_to_coprod ι)

/-- Helper for Corollary 2.8.2: changing the circle basepoint along the defining equality gives a
group equivalence. -/
private theorem mapOfEq_comp_symm :
    (FundamentalGroup.mapOfEq (ContinuousMap.id based_circle.right)
        underTopBasepoint_based_circle).comp
      (FundamentalGroup.mapOfEq (ContinuousMap.id based_circle.right)
        underTopBasepoint_based_circle.symm) =
      MonoidHom.id (FundamentalGroup Circle (1 : Circle)) := by
  ext u
  induction u using Quotient.ind
  rename_i p
  change (FundamentalGroup.mapOfEq (ContinuousMap.id Circle)
      underTopBasepoint_based_circle)
      ((FundamentalGroup.mapOfEq (ContinuousMap.id Circle)
        underTopBasepoint_based_circle.symm)
        (FundamentalGroup.fromPath (.mk p))) = FundamentalGroup.fromPath (.mk p)
  rw [FundamentalGroup.mapOfEq_apply (ContinuousMap.id Circle)
    underTopBasepoint_based_circle.symm p]
  simpa using
    (FundamentalGroup.mapOfEq_apply (ContinuousMap.id Circle)
      underTopBasepoint_based_circle
      ((p.map (ContinuousMap.continuous (ContinuousMap.id Circle))).cast
        underTopBasepoint_based_circle underTopBasepoint_based_circle))

/-- Helper for Corollary 2.8.2: the inverse basepoint transport is the opposite transport. -/
private theorem mapOfEq_symm_comp :
    (FundamentalGroup.mapOfEq (ContinuousMap.id based_circle.right)
        underTopBasepoint_based_circle.symm).comp
      (FundamentalGroup.mapOfEq (ContinuousMap.id based_circle.right)
        underTopBasepoint_based_circle) =
      MonoidHom.id based_circle_pi1 := by
  ext u
  induction u using Quotient.ind
  rename_i p
  change (FundamentalGroup.mapOfEq (ContinuousMap.id Circle)
      underTopBasepoint_based_circle.symm)
      ((FundamentalGroup.mapOfEq (ContinuousMap.id Circle)
        underTopBasepoint_based_circle)
        (FundamentalGroup.fromPath (.mk p))) = FundamentalGroup.fromPath (.mk p)
  rw [FundamentalGroup.mapOfEq_apply (ContinuousMap.id Circle)
    underTopBasepoint_based_circle p]
  simpa using
    (FundamentalGroup.mapOfEq_apply (ContinuousMap.id Circle)
      underTopBasepoint_based_circle.symm
      ((p.map (ContinuousMap.continuous (ContinuousMap.id Circle))).cast
        underTopBasepoint_based_circle.symm underTopBasepoint_based_circle.symm))

/-- Helper for Corollary 2.8.2: transport between the two circle basepoints is a group
equivalence. -/
private noncomputable def circle_basepoint_equiv :
    FundamentalGroup Circle (1 : Circle) ≃*
      based_circle_pi1 :=
  MonoidHom.toMulEquiv
    (FundamentalGroup.mapOfEq (ContinuousMap.id based_circle.right)
      underTopBasepoint_based_circle.symm)
    (FundamentalGroup.mapOfEq (ContinuousMap.id based_circle.right)
      underTopBasepoint_based_circle)
    mapOfEq_comp_symm
    mapOfEq_symm_comp

/-- Helper for Corollary 2.8.2: one circle contributes one free-group generator. -/
private noncomputable def based_circle_freeGroupUnit_equiv :
    FreeGroup Unit ≃* based_circle_pi1 :=
  FreeGroup.mulEquivIntOfUnique.trans
    (circleFundamentalGroupMulEquivInt.trans circle_basepoint_equiv)

/-- Helper for Corollary 2.8.2: the single-circle comparison map is an isomorphism. -/
private noncomputable instance based_circle_freeGroupUnit_to_pi1_isIso :
    IsIso (GrpCat.ofHom based_circle_freeGroupUnit_to_pi1) := by
  change IsIso (GrpCat.ofHom based_circle_freeGroupUnit_equiv.toMonoidHom)
  let X : GrpCat := GrpCat.of (FreeGroup Unit)
  let Y : GrpCat := GrpCat.of based_circle_pi1
  let e : X ≃* Y := based_circle_freeGroupUnit_equiv
  exact e.toGrpIso.isIso_hom

private noncomputable abbrev based_circle_freeGroupUnit_equiv_inv :
    based_circle_pi1 →* FreeGroup Unit :=
  based_circle_freeGroupUnit_equiv.symm.toMonoidHom

private noncomputable abbrev based_circle_freeGroupUnit_equiv_hom :
    FreeGroup Unit →* based_circle_pi1 :=
  based_circle_freeGroupUnit_equiv.toMonoidHom

/-- Helper for Corollary 2.8.2: the single-circle equivalence composed with its inverse is the
identity on `FreeGroup Unit`. -/
private theorem based_circle_freeGroupUnit_symm_comp :
    based_circle_freeGroupUnit_equiv_inv.comp based_circle_freeGroupUnit_equiv_hom =
      MonoidHom.id (FreeGroup Unit) := by
  ext u
  exact based_circle_freeGroupUnit_equiv.left_inv (FreeGroup.of u)

/-- Helper for Corollary 2.8.2: the single-circle equivalence inverse composed with the forward map
is the identity on the circle fundamental group. -/
private theorem based_circle_freeGroupUnit_comp_symm :
    based_circle_freeGroupUnit_equiv_hom.comp based_circle_freeGroupUnit_equiv_inv =
      MonoidHom.id based_circle_pi1 := by
  ext u
  exact based_circle_freeGroupUnit_equiv.right_inv u

/-- Helper for Corollary 2.8.2: lift the single-circle equivalence into the indexed free product. -/
private noncomputable def wedge_of_circles_coprod_map (ι : Type) :
    Monoid.CoprodI (fun _ : ι ↦ FreeGroup Unit) →*
      Monoid.CoprodI (based_circle_pi1_family ι) :=
  Monoid.CoprodI.lift fun i ↦
    let ofi :
        based_circle_pi1 →* Monoid.CoprodI (based_circle_pi1_family ι) :=
      @Monoid.CoprodI.of ι (based_circle_pi1_family ι) _ i
    ofi.comp based_circle_freeGroupUnit_equiv.toMonoidHom

/-- Helper for Corollary 2.8.2: the inverse lift from the indexed free product back to the free
group on the indexing type. -/
private noncomputable def wedge_of_circles_coprod_inv (ι : Type) :
    Monoid.CoprodI (based_circle_pi1_family ι) →*
      Monoid.CoprodI (fun _ : ι ↦ FreeGroup Unit) :=
  Monoid.CoprodI.lift fun i ↦
    let ofi :
        FreeGroup Unit →* Monoid.CoprodI (fun _ : ι ↦ FreeGroup Unit) :=
      @Monoid.CoprodI.of ι (fun _ : ι ↦ FreeGroup Unit) _ i
    ofi.comp based_circle_freeGroupUnit_equiv.symm.toMonoidHom

/-- Helper for Corollary 2.8.2: the lifted inverse really inverts the lifted forward map on the
free product of the circle factors. -/
private theorem wedge_of_circles_coprod_inv_comp_map (ι : Type) :
    (wedge_of_circles_coprod_inv ι).comp (wedge_of_circles_coprod_map ι) =
      MonoidHom.id (Monoid.CoprodI (fun _ : ι ↦ FreeGroup Unit)) := by
  apply Monoid.CoprodI.ext_hom
  intro i
  ext u
  dsimp [wedge_of_circles_coprod_map, wedge_of_circles_coprod_inv]
  change
    (@Monoid.CoprodI.of ι (fun _ : ι ↦ FreeGroup Unit) _ i)
        (based_circle_freeGroupUnit_equiv.symm
          (based_circle_freeGroupUnit_equiv (FreeGroup.of u))) =
      (@Monoid.CoprodI.of ι (fun _ : ι ↦ FreeGroup Unit) _ i) (FreeGroup.of u)
  exact congrArg
    (@Monoid.CoprodI.of ι (fun _ : ι ↦ FreeGroup Unit) _ i)
    (based_circle_freeGroupUnit_equiv.left_inv (FreeGroup.of u))

/-- Helper for Corollary 2.8.2: the lifted forward map also inverts the lifted inverse. -/
private theorem wedge_of_circles_coprod_map_comp_inv (ι : Type) :
    (wedge_of_circles_coprod_map ι).comp (wedge_of_circles_coprod_inv ι) =
      MonoidHom.id (Monoid.CoprodI (based_circle_pi1_family ι)) := by
  apply Monoid.CoprodI.ext_hom
  intro i
  ext u
  dsimp [wedge_of_circles_coprod_map, wedge_of_circles_coprod_inv]
  change
    (@Monoid.CoprodI.of ι (based_circle_pi1_family ι) _ i)
        (based_circle_freeGroupUnit_equiv (based_circle_freeGroupUnit_equiv.symm u)) =
      (@Monoid.CoprodI.of ι (based_circle_pi1_family ι) _ i) u
  exact congrArg
    (@Monoid.CoprodI.of ι (based_circle_pi1_family ι) _ i)
    (based_circle_freeGroupUnit_equiv.right_inv u)

/-- Helper for Corollary 2.8.2: identify the free group on `ι` with the free product of the
individual circle groups. -/
private noncomputable def wedge_of_circles_freeGroup_equiv (ι : Type) :
    FreeGroup ι ≃*
      Monoid.CoprodI (based_circle_pi1_family ι) :=
  freeGroupEquivCoprodI.trans
    (MonoidHom.toMulEquiv
      (wedge_of_circles_coprod_map ι)
      (wedge_of_circles_coprod_inv ι)
      (wedge_of_circles_coprod_inv_comp_map ι)
      (wedge_of_circles_coprod_map_comp_inv ι))

/-- Helper for Corollary 2.8.2: the algebraic bridge from `FreeGroup ι` to the free product of
circle groups is an isomorphism. -/
private noncomputable instance wedge_of_circles_freeGroup_to_coprod_isIso (ι : Type) :
    IsIso (GrpCat.ofHom (wedge_of_circles_freeGroup_to_coprod ι)) := by
  change IsIso (GrpCat.ofHom (wedge_of_circles_freeGroup_equiv ι).toMonoidHom)
  let X : GrpCat := GrpCat.of (FreeGroup ι)
  let Y : GrpCat := GrpCat.of (Monoid.CoprodI (based_circle_pi1_family ι))
  let e : X ≃* Y := wedge_of_circles_freeGroup_equiv ι
  exact e.toGrpIso.isIso_hom

/-- Helper for Corollary 2.8.2: Proposition 2.8.1 specializes to the constant family of based
circles. -/
private noncomputable instance wedge_fundamental_group_comparison_based_circle_isIso (ι : Type) :
    IsIso (GrpCat.ofHom (wedge_fundamental_group_comparison fun _ : ι ↦ based_circle)) :=
  wedgeFundamentalGroupComparison_isIso
    (fun _ : ι ↦ based_circle)
    (fun _ ↦ based_circle_has_contractible_base_neighborhood)

/-- The canonical comparison map from `FreeGroup ι` to the fundamental group of the wedge of `ι`
circles is an isomorphism. -/
noncomputable instance wedge_of_circles_fundamental_group_comparison_isIso (ι : Type) :
    IsIso (GrpCat.ofHom (wedge_of_circles_fundamental_group_comparison ι)) := by
  change IsIso
    (GrpCat.ofHom
      ((wedge_fundamental_group_comparison fun _ : ι ↦ based_circle).comp
        (wedge_of_circles_freeGroup_to_coprod ι)))
  simpa using
    (show
      IsIso
        (GrpCat.ofHom (wedge_of_circles_freeGroup_to_coprod ι) ≫
          GrpCat.ofHom (wedge_fundamental_group_comparison fun _ : ι ↦ based_circle))
      from inferInstance)
