module

public import Topology_Munkres_2000.Book.Definition_79_2.Conjugacy
public import Topology_Munkres_2000.Book.Theorem_54_6.Monodromy

public section

open Path
open scoped Pointwise

universe u v

namespace IsCoveringMap

/-- Helper for Lemma 79.3: conjugating after transport by a functor agrees with
transporting a conjugated endomorphism across a pasted square of isomorphisms. -/
private lemma mapConjPaste {C : Type*} {D : Type*} [CategoryTheory.Groupoid C]
    [CategoryTheory.Groupoid D] (F : CategoryTheory.Functor C D) {x₀ x₁ : C} {y : D}
    (α : x₀ ≅ x₁) (β₀ : F.obj x₀ ≅ y) (β₁ : F.obj x₁ ≅ y)
    (a : CategoryTheory.End x₁) :
    ((β₀.symm ≪≫ F.mapIso α ≪≫ β₁).symm.conj (β₁.conj (F.map a))) =
      β₀.conj (F.map (α.symm.conj a)) := by
  -- Expand the pasted isomorphisms; functoriality and inverse cancellation close the square.
  simp only [CategoryTheory.Iso.conj_apply, CategoryTheory.Iso.trans_hom,
    CategoryTheory.Iso.trans_inv, CategoryTheory.Iso.symm_hom,
    CategoryTheory.Iso.symm_inv, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.mapIso_inv, CategoryTheory.Functor.map_comp]
  simp only [CategoryTheory.Category.assoc, CategoryTheory.Iso.hom_inv_id_assoc]

/-- Helper for Lemma 79.3: conjugation in a fundamental group is categorical
conjugation by the inverse of the isomorphism represented by the same loop. -/
private lemma fundamentalGroup_conj_inv_eq_isoOfHom_symm_conj
    {X : Type u} [TopologicalSpace X] {x : X} (c a : FundamentalGroup X x) :
    MulAut.conj c⁻¹ a =
      ((CategoryTheory.Groupoid.isoEquivHom _ _).symm c).symm.conj a := by
  -- Reverse composition in the endomorphism group gives the categorical conjugation order.
  rw [MulAut.conj_apply, CategoryTheory.Iso.conj_apply]
  simp only [FundamentalGroup.mul_def, FundamentalGroup.inv_def]
  have hsymm : (Homotopic.Quotient.symm c).symm = c :=
    (CategoryTheory.Groupoid.invEquiv (C := FundamentalGroupoid X)
      (X := FundamentalGroupoid.mk x) (Y := FundamentalGroupoid.mk x)).right_inv c
  rw [hsymm]
  rfl

/-- Helper for Lemma 79.3: casting the image of a connecting path to a common
basepoint is the morphism of the corresponding pasted isomorphism. -/
private lemma fromPath_cast_mk_map_eq_pastedIso_hom
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x₀ x₁ : X} {y₀ : Y} (h₀ : f x₀ = y₀) (h₁ : f x₁ = y₀)
    (γ : Path x₀ x₁) :
    FundamentalGroup.fromPath
        (Homotopic.Quotient.cast (.mk (γ.map f.continuous)) h₀.symm h₁.symm) =
      ((CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk h₀)).symm ≪≫
          (FundamentalGroupoid.map f).mapIso
            ((CategoryTheory.Groupoid.isoEquivHom _ _).symm (.mk γ)) ≪≫
        CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk h₁)).hom := by
  -- The fundamental-groupoid endpoint-cast formula identifies the two morphisms.
  rw [← FundamentalGroupoid.conj_eqToHom h₀.symm h₁.symm]
  simp only [CategoryTheory.Iso.trans_hom, CategoryTheory.Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom]
  rfl

/-- Helper for Lemma 79.3: an induced fundamental-group map intertwines basepoint
change with conjugation by the mapped connecting path. -/
private lemma conj_comp_mapOfEq_eq_mapOfEq_comp_basepointChange
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x₀ x₁ : X} {y₀ : Y} (h₀ : f x₀ = y₀) (h₁ : f x₁ = y₀)
    (γ : Path x₀ x₁) :
    (MulAut.conj
        (FundamentalGroup.fromPath
          (Homotopic.Quotient.cast (.mk (γ.map f.continuous)) h₀.symm h₁.symm))⁻¹).toMonoidHom.comp
        (FundamentalGroup.mapOfEq f h₁) =
      (FundamentalGroup.mapOfEq f h₀).comp
        (FundamentalGroup.fundamentalGroupMulEquivOfPath γ.symm).toMonoidHom := by
  -- Name the path and endpoint isomorphisms so all subsequent rewrites use one spelling.
  ext a
  let α := (CategoryTheory.Groupoid.isoEquivHom
    (FundamentalGroupoid.mk x₀) (FundamentalGroupoid.mk x₁)).symm (.mk γ)
  let β₀ := CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk h₀)
  let β₁ := CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk h₁)
  let δ := (CategoryTheory.Groupoid.isoEquivHom
    (FundamentalGroupoid.mk y₀) (FundamentalGroupoid.mk y₀)).symm
      (FundamentalGroup.fromPath
        (Homotopic.Quotient.cast (.mk (γ.map f.continuous)) h₀.symm h₁.symm))
  have hδ : δ = β₀.symm ≪≫ (FundamentalGroupoid.map f).mapIso α ≪≫ β₁ := by
    apply CategoryTheory.Iso.ext
    apply eq_of_heq
    exact heq_of_eq (fromPath_cast_mk_map_eq_pastedIso_hom f h₀ h₁ γ)
  have hα : α.symm = (CategoryTheory.Groupoid.isoEquivHom
      (FundamentalGroupoid.mk x₁) (FundamentalGroupoid.mk x₀)).symm (.mk γ.symm) := by
    apply CategoryTheory.Iso.ext
    rfl
  -- Expose the three conjugations, replacing the loop conjugator by its pasted isomorphism.
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  simp only [MulEquiv.coe_toMonoidHom]
  rw [fundamentalGroup_conj_inv_eq_isoOfHom_symm_conj]
  dsimp only [δ] at hδ
  rw [hδ]
  unfold FundamentalGroup.mapOfEq
  unfold FundamentalGroup.fundamentalGroupMulEquivOfPath
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  -- The abstract groupoid pasting identity is exactly the normalized goal.
  have hpaste := mapConjPaste (FundamentalGroupoid.map f) α β₀ β₁ a
  simp only [α, β₀, β₁, hα] at hpaste
  apply eq_of_heq
  exact heq_of_eq hpaste

/-- Helper for Lemma 79.3: a path-homotopy class between two points in a
covering fiber conjugates the ranges of the induced fundamental-group maps. -/
private lemma fundamentalGroupMapRange_map_conj_eq_of_pathClass
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (hp : IsCoveringMap p) {b₀ : B} {e₀ e₁ : E}
    (h₀ : p e₀ = b₀) (h₁ : p e₁ = b₀) (Γ : Path.Homotopic.Quotient e₀ e₁) :
    (hp.fundamentalGroupMapRange h₁).map
        (MulAut.conj
          (FundamentalGroup.fromPath
            ((Γ.map ⟨p, hp.continuous⟩).cast h₀.symm h₁.symm))⁻¹) =
      hp.fundamentalGroupMapRange h₀ := by
  -- Choose a representative only to invoke the path-level naturality bridge.
  induction Γ using Path.Homotopic.Quotient.ind with
  | mk γ =>
      rw [← Path.Homotopic.Quotient.mk_map]
      unfold fundamentalGroupMapRange
      rw [MonoidHom.map_range, ← MulEquiv.toMonoidHom_eq_coe,
        conj_comp_mapOfEq_eq_mapOfEq_comp_basepointChange ⟨p, hp.continuous⟩ h₀ h₁ γ,
        MonoidHom.range_comp, MulEquiv.toMonoidHom_eq_coe, MulEquiv.range_eq_top,
        ← MonoidHom.range_eq_map]

/-- Helper for Lemma 79.3: the pointwise action of a group automorphism on a
subgroup is its ordinary subgroup map. -/
private lemma mulAut_smul_subgroup_eq_map {G : Type*} [Group G]
    (e : MulAut G) (H : Subgroup G) : e • H = H.map e.toMonoidHom := by
  -- Both constructions use the monoid homomorphism underlying `e`.
  rfl

/-- Helper for Lemma 79.3: casting both endpoints of a path class and then
casting them back leaves the path class unchanged. -/
private lemma pathClassCastSymmCast {X : Type*} [TopologicalSpace X]
    {x y x' y' : X} (Γ : Path.Homotopic.Quotient x y)
    (hx : x' = x) (hy : y' = y) :
    (Γ.cast hx hy).cast hx.symm hy.symm = Γ := by
  -- Compose the endpoint transports, then use proof irrelevance to make both reflexive.
  rw [Path.Homotopic.Quotient.cast_cast]
  have hx_rfl : hx.symm.trans hx = rfl := Subsingleton.elim _ _
  have hy_rfl : hy.symm.trans hy = rfl := Subsingleton.elim _ _
  rw [hx_rfl, hy_rfl, Path.Homotopic.Quotient.cast_rfl_rfl]

/-- Lemma 79.3 (1): a path between two points in one fiber of a covering conjugates
the images of their fundamental groups. The inverse on the conjugating element accounts
for mathlib's convention that multiplication in `FundamentalGroup` reverses path order. -/
theorem fundamentalGroupMapRange_map_conj_eq_of_path {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : E → B} (hp : IsCoveringMap p)
    {b₀ : B} {e₀ e₁ : E} (h₀ : p e₀ = b₀) (h₁ : p e₁ = b₀) (γ : Path e₀ e₁) :
    (hp.fundamentalGroupMapRange h₁).map
        (MulAut.conj
          (FundamentalGroup.fromPath
            (Homotopic.Quotient.cast (.mk (γ.map hp.continuous)) h₀.symm h₁.symm))⁻¹) =
      hp.fundamentalGroupMapRange h₀ := by
  -- Pass to the path-homotopy class and normalize the image of its representative.
  have h := fundamentalGroupMapRange_map_conj_eq_of_pathClass hp h₀ h₁ (.mk γ)
  apply eq_of_heq
  exact heq_of_eq h

/-- The fundamental-group images at points joined within one covering fiber are conjugate
subgroups. -/
theorem fundamentalGroupMapRange_isConj_of_path {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : E → B} (hp : IsCoveringMap p)
    {b₀ : B} {e₀ e₁ : E} (h₀ : p e₀ = b₀) (h₁ : p e₁ = b₀) (γ : Path e₀ e₁) :
    (hp.fundamentalGroupMapRange h₁).IsConj (hp.fundamentalGroupMapRange h₀) := by
  -- Use the mapped connecting loop as the explicit conjugacy witness.
  apply Subgroup.isConj_iff_exists.mpr
  use (FundamentalGroup.fromPath
    (Homotopic.Quotient.cast (.mk (γ.map hp.continuous)) h₀.symm h₁.symm))⁻¹
  rw [mulAut_smul_subgroup_eq_map]
  exact hp.fundamentalGroupMapRange_map_conj_eq_of_path h₀ h₁ γ

/-- Lemma 79.3 (2): every subgroup conjugate to the fundamental-group image at one
point of a covering fiber occurs as the image at another point of that fiber. -/
theorem exists_fiberPoint_fundamentalGroupMapRange_eq_of_isConj {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : E → B} (hp : IsCoveringMap p)
    {b₀ : B} (e₀ : E) (h₀ : p e₀ = b₀) (H : Subgroup (FundamentalGroup B b₀))
    (hH : H.IsConj (hp.fundamentalGroupMapRange h₀)) :
    ∃ (e₁ : E) (h₁ : p e₁ = b₀), hp.fundamentalGroupMapRange h₁ = H := by
  -- Choose a conjugating loop and lift its inverse from the prescribed fiber point.
  obtain ⟨g, hg⟩ := Subgroup.isConj_iff_exists.mp hH
  rw [mulAut_smul_subgroup_eq_map] at hg
  let α : Path.Homotopic.Quotient b₀ b₀ := FundamentalGroup.toPath g⁻¹
  let e : p ⁻¹' {b₀} := ⟨e₀, h₀⟩
  let e₁ := hp.monodromy α e
  use e₁.1, e₁.2
  -- Projecting the canonical lifted path back to `B` recovers `α` after cancelling casts.
  have hproject : FundamentalGroup.fromPath
      (((hp.liftPathQuotient α e).map ⟨p, hp.continuous⟩).cast h₀.symm e₁.2.symm) = g⁻¹ := by
    rw [hp.map_liftPathQuotient]
    dsimp only [e, e₁]
    rw [pathClassCastSymmCast]
  have hlift := fundamentalGroupMapRange_map_conj_eq_of_pathClass hp h₀ e₁.2
    (hp.liftPathQuotient α e)
  rw [hproject, inv_inv] at hlift
  -- Both candidate subgroups have the same image under an injective conjugation automorphism.
  apply Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [MulEquiv.toMonoidHom_eq_coe] at hg ⊢
  exact hlift.trans hg.symm

end IsCoveringMap
