module

public import Topology_Munkres_2000.Book.Definition_81_3.CoveringTransformation
public import Topology_Munkres_2000.Book.Theorem_54_6.Monodromy
public import Mathlib.Algebra.Group.Subgroup.Basic
import Topology_Munkres_2000.Book.Lemma_79_1
import Topology_Munkres_2000.Book.Lemma_79_3
import all Topology_Munkres_2000.Book.Definition_54_2.LiftingCorrespondence
import all Topology_Munkres_2000.Book.Definition_81_5.HomeomorphGroup
import all Topology_Munkres_2000.Book.Theorem_54_6.Monodromy

public section

universe u v

namespace FundamentalGroup

/-- Helper for Lemma 81.1: a reflexive target identification in `mapOfEq` gives the
ordinary induced fundamental-group map. -/
private lemma mapOfEq_refl {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    mapOfEq f (rfl : f x = f x) = map f x := by
  -- Compare loop classes and remove the reflexive endpoint transport.
  ext γ
  simp only [mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl, map_apply]

end FundamentalGroup

namespace IsCoveringMap

/-- Helper for Lemma 81.1: pointed self-lifts of a covering are classified by inclusion
of the corresponding induced fundamental-group ranges. -/
private lemma exists_pointedSelfLift_iff_fundamentalGroupMapRange_le
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    {p : E → B} (hp : IsCoveringMap p) (e₀ e₁ : E) (b₀ : B)
    (h₀ : p e₀ = b₀) (h₁ : p e₁ = b₀) :
    (∃ f : C(E, E), f e₀ = e₁ ∧ p ∘ f = p) ↔
      hp.fundamentalGroupMapRange h₀ ≤ hp.fundamentalGroupMapRange h₁ := by
  -- Move to a literal common basepoint, where Lemma 79.1 has the required range statement.
  subst b₀
  have hcriterion :
      (∃! f : C(E, E), f e₀ = e₁ ∧ p ∘ f = p) ↔
        hp.fundamentalGroupMapRange (rfl : p e₀ = p e₀) ≤
          hp.fundamentalGroupMapRange h₁ := by
    simpa only [fundamentalGroupMapRange, FundamentalGroup.mapOfEq_refl,
      ContinuousMap.coe_mk] using
      (existsUnique_continuousMap_lifts_iff_range_le
        p hp ⟨p, hp.continuous⟩ e₀ e₁ h₁)
  constructor
  · rintro ⟨f, f_base, f_lifts⟩
    -- Covering-lift uniqueness upgrades the supplied lift to the unique lift in the criterion.
    have f_spec : f e₀ = e₁ ∧ p ∘ f = p := ⟨f_base, f_lifts⟩
    have f_unique : ∀ g : C(E, E), g e₀ = e₁ ∧ p ∘ g = p → g = f := by
      intro g g_spec
      apply ContinuousMap.ext
      exact congrFun (hp.eq_of_comp_eq g.continuous f.continuous
        (g_spec.2.trans f_lifts.symm) e₀ (g_spec.1.trans f_base.symm))
    exact hcriterion.mp (ExistsUnique.intro f f_spec f_unique)
  · intro h_range
    -- Discard uniqueness after Lemma 79.1 constructs the pointed lift.
    obtain ⟨f, f_spec, -⟩ := hcriterion.mpr h_range
    exact ⟨f, f_spec⟩

/-- Helper for Lemma 81.1: mutually pointed self-lifts over one covering map are inverse
functions. -/
private lemma mutualPointedSelfLifts_inverse
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    [PreconnectedSpace E] {p : E → B} (hp : IsCoveringMap p)
    (e₀ e₁ : E) (f g : C(E, E))
    (f_base : f e₀ = e₁) (g_base : g e₁ = e₀)
    (f_lifts : p ∘ f = p) (g_lifts : p ∘ g = p) :
    Function.LeftInverse g f ∧ Function.RightInverse g f := by
  -- Uniqueness first identifies `g ∘ f` with the identity lift.
  have gf_projection : p ∘ (g ∘ f) = p ∘ id := by
    funext e
    exact congrFun g_lifts (f e) |>.trans (congrFun f_lifts e)
  have gf_base : (g ∘ f) e₀ = id e₀ := by
    simp only [Function.comp_apply, id_eq, f_base, g_base]
  have gf_eq : g ∘ f = id :=
    hp.eq_of_comp_eq (g.continuous.comp f.continuous) continuous_id
      gf_projection e₀ gf_base
  -- The symmetric uniqueness argument identifies `f ∘ g` with the identity lift.
  have fg_projection : p ∘ (f ∘ g) = p ∘ id := by
    funext e
    exact congrFun f_lifts (g e) |>.trans (congrFun g_lifts e)
  have fg_base : (f ∘ g) e₁ = id e₁ := by
    simp only [Function.comp_apply, id_eq, g_base, f_base]
  have fg_eq : f ∘ g = id :=
    hp.eq_of_comp_eq (f.continuous.comp g.continuous) continuous_id
      fg_projection e₁ fg_base
  constructor
  · intro e
    exact congrFun gf_eq e
  · intro e
    exact congrFun fg_eq e

/-- Helper for Lemma 81.1: a fiber point lies in the evaluation orbit of the covering
transformation group exactly when its induced subgroup equals the subgroup at `e₀`. -/
private lemma exists_coveringTransformation_evalInFiber_eq_iff_fundamentalGroupMapRange_eq
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    {p : E → B} (hp : IsCoveringMap p) (e₀ e₁ : E) (b₀ : B)
    (h₀ : p e₀ = b₀) (h₁ : p e₁ = b₀) :
    (∃ h : CoveringTransformation.group p,
        CoveringTransformation.evalInFiber b₀ e₀ h₀ h = ⟨e₁, h₁⟩) ↔
      hp.fundamentalGroupMapRange h₁ = hp.fundamentalGroupMapRange h₀ := by
  constructor
  · rintro ⟨h, h_eval⟩
    -- The transformation and its inverse supply the two subgroup inclusions.
    let f : C(E, E) := ⟨fun e ↦ h • e, continuous_const_smul h⟩
    let g : C(E, E) := ⟨fun e ↦ h⁻¹ • e, continuous_const_smul h⁻¹⟩
    have f_base : f e₀ = e₁ := by
      have f_apply : f e₀ = h • e₀ := rfl
      exact f_apply.trans (congrArg Subtype.val h_eval)
    have f_lifts : p ∘ f = p := by
      funext e
      exact CoveringTransformation.map_smul p h e
    have g_base : g e₁ = e₀ := by
      rw [← f_base]
      exact inv_smul_smul h e₀
    have g_lifts : p ∘ g = p := by
      funext e
      exact CoveringTransformation.map_smul p h⁻¹ e
    have h_forward :=
      (exists_pointedSelfLift_iff_fundamentalGroupMapRange_le
        hp e₀ e₁ b₀ h₀ h₁).mp ⟨f, f_base, f_lifts⟩
    have h_reverse :=
      (exists_pointedSelfLift_iff_fundamentalGroupMapRange_le
        hp e₁ e₀ b₀ h₁ h₀).mp ⟨g, g_base, g_lifts⟩
    exact le_antisymm h_reverse h_forward
  · intro h_range
    -- Equality of subgroups constructs pointed lifts in both directions.
    obtain ⟨f, f_base, f_lifts⟩ :=
      (exists_pointedSelfLift_iff_fundamentalGroupMapRange_le
        hp e₀ e₁ b₀ h₀ h₁).mpr h_range.ge
    obtain ⟨g, g_base, g_lifts⟩ :=
      (exists_pointedSelfLift_iff_fundamentalGroupMapRange_le
        hp e₁ e₀ b₀ h₁ h₀).mpr h_range.le
    obtain ⟨f_left, f_right⟩ := mutualPointedSelfLifts_inverse
      hp e₀ e₁ f g f_base g_base f_lifts g_lifts
    -- Package the already-named inverse laws and continuity facts as a homeomorphism.
    let fEquiv : E ≃ E :=
      { toFun := f
        invFun := g
        left_inv := f_left
        right_inv := f_right }
    let fHomeomorph : E ≃ₜ E :=
      { fEquiv with
        continuous_toFun := f.continuous
        continuous_invFun := g.continuous }
    have fHomeomorph_lifts : p ∘ fHomeomorph = p := f_lifts
    have fHomeomorph_base : fHomeomorph e₀ = e₁ := f_base
    have f_mem : fHomeomorph ∈ CoveringTransformation.group p := by
      exact (CoveringTransformation.mem_group p fHomeomorph).mpr fHomeomorph_lifts
    let h : CoveringTransformation.group p := ⟨fHomeomorph, f_mem⟩
    have h_base : h.1 e₀ = e₁ := fHomeomorph_base
    refine ⟨h, ?_⟩
    apply Subtype.ext
    rw [CoveringTransformation.evalInFiber_apply]
    have h_action : h • e₀ = h.1 e₀ := rfl
    exact h_action.trans h_base

/-- Helper for Lemma 81.1: a path-homotopy class between two points of one fiber
conjugates their induced fundamental-group ranges. -/
private lemma fundamentalGroupMapRange_map_conj_eq_of_pathClass
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (hp : IsCoveringMap p) {b₀ : B} {e₀ e₁ : E}
    (h₀ : p e₀ = b₀) (h₁ : p e₁ = b₀) (Γ : Path.Homotopic.Quotient e₀ e₁) :
    (hp.fundamentalGroupMapRange h₁).map
        (MulAut.conj
          (FundamentalGroup.fromPath
            ((Γ.map ⟨p, hp.continuous⟩).cast h₀.symm h₁.symm))⁻¹) =
      hp.fundamentalGroupMapRange h₀ := by
  -- Choose a path representative and invoke the path-level statement of Lemma 79.3.
  induction Γ using Path.Homotopic.Quotient.ind with
  | mk γ =>
      rw [← Path.Homotopic.Quotient.mk_map]
      exact hp.fundamentalGroupMapRange_map_conj_eq_of_path h₀ h₁ γ

/-- Helper for Lemma 81.1: casting both endpoints of a path class and then casting
them back leaves the path class unchanged. -/
private lemma pathClassCastSymmCast {X : Type*} [TopologicalSpace X]
    {x y x' y' : X} (Γ : Path.Homotopic.Quotient x y)
    (hx : x' = x) (hy : y' = y) :
    (Γ.cast hx hy).cast hx.symm hy.symm = Γ := by
  -- Compose the endpoint transports and use proof irrelevance to make them reflexive.
  rw [Path.Homotopic.Quotient.cast_cast]
  have hx_rfl : hx.symm.trans hx = rfl := Subsingleton.elim _ _
  have hy_rfl : hy.symm.trans hy = rfl := Subsingleton.elim _ _
  rw [hx_rfl, hy_rfl, Path.Homotopic.Quotient.cast_rfl_rfl]

/-- Helper for Lemma 81.1: the subgroup at the monodromy endpoint of `γ⁻¹` maps
under conjugation by `γ` to the subgroup at the starting point. -/
private lemma fundamentalGroupMapRange_map_conj_eq_of_monodromy
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (hp : IsCoveringMap p) {e₀ : E} {b₀ : B}
    (h₀ : p e₀ = b₀) (γ : FundamentalGroup B b₀) :
    (hp.fundamentalGroupMapRange
        (hp.monodromy (FundamentalGroup.toPath γ⁻¹)
          (basepointInFiber p h₀)).2).map (MulAut.conj γ) =
      hp.fundamentalGroupMapRange h₀ := by
  let α : Path.Homotopic.Quotient b₀ b₀ := FundamentalGroup.toPath γ⁻¹
  let e : p ⁻¹' {b₀} := basepointInFiber p h₀
  let e₁ := hp.monodromy α e
  let δ := FundamentalGroup.fromPath
    (((hp.liftPathQuotient α e).map ⟨p, hp.continuous⟩).cast h₀.symm e₁.2.symm)
  -- Project the canonical lifted class and cancel its two successive endpoint transports.
  have h_project : δ = γ⁻¹ := by
    dsimp only [δ]
    rw [hp.map_liftPathQuotient]
    dsimp only [e, e₁]
    rw [pathClassCastSymmCast]
  -- Lemma 79.3 now has conjugator `γ` because the lifted representative was `γ⁻¹`.
  have h_lift :
      (hp.fundamentalGroupMapRange e₁.2).map (MulAut.conj δ⁻¹) =
        hp.fundamentalGroupMapRange h₀ := by
    dsimp only [δ]
    apply eq_of_heq
    exact heq_of_eq (fundamentalGroupMapRange_map_conj_eq_of_pathClass
      hp h₀ e₁.2 (hp.liftPathQuotient α e))
  have h_conjugator : δ⁻¹ = γ := by
    calc
      δ⁻¹ = (γ⁻¹)⁻¹ := congrArg Inv.inv h_project
      _ = γ := inv_inv γ
  rw [h_conjugator] at h_lift
  simpa only [α, e, e₁] using h_lift

/-- Lemma 81.1: The image of evaluation at `e₀` on covering transformations is the
monodromy image of the right cosets represented by the normalizer of the induced subgroup. -/
theorem range_evalInFiber_eq_image_normalizer {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] [PathConnectedSpace E]
    [LocallyPathConnectedSpace E]
    (p : E → B) (hp : IsCoveringMap p) (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) :
    Set.range (CoveringTransformation.evalInFiber b₀ e₀ he₀) =
      hp.monodromyRightCosetMap he₀ ''
        (Quotient.mk'' ''
          Subgroup.normalizer
            (hp.fundamentalGroupMapRange he₀ : Set (FundamentalGroup B b₀))) := by
  -- Compare the two sets pointwise, using induced subgroups as the controlling invariant.
  ext e
  constructor
  · rintro ⟨h, rfl⟩
    -- Choose a right-coset representative for the evaluated fiber point.
    obtain ⟨q, hq⟩ :=
      (hp.monodromyRightCosetMap_bijective he₀).2
        (CoveringTransformation.evalInFiber b₀ e₀ he₀ h)
    obtain ⟨γ, hγ⟩ := Quotient.exists_rep q
    subst q
    refine ⟨Quotient.mk'' γ, ?_, hq⟩
    refine ⟨γ, ?_, rfl⟩
    let eγ := hp.monodromy (FundamentalGroup.toPath γ⁻¹)
      (basepointInFiber p he₀)
    have heγ_eval : eγ = CoveringTransformation.evalInFiber b₀ e₀ he₀ h := by
      simpa only [eγ, hp.monodromyRightCosetMap_mk, liftingCorrespondence] using hq
    -- Lemma 79.1 identifies the subgroup at this endpoint with the base subgroup.
    have h_range :
        hp.fundamentalGroupMapRange eγ.2 = hp.fundamentalGroupMapRange he₀ :=
      (exists_coveringTransformation_evalInFiber_eq_iff_fundamentalGroupMapRange_eq
        hp e₀ eγ.1 b₀ he₀ eγ.2).mp ⟨h, heγ_eval.symm⟩
    have h_conj :
        (hp.fundamentalGroupMapRange eγ.2).map (MulAut.conj γ) =
          hp.fundamentalGroupMapRange he₀ := by
      simpa only [eγ] using
        fundamentalGroupMapRange_map_conj_eq_of_monodromy hp he₀ γ
    rw [h_range] at h_conj
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h_conj
  · rintro ⟨q, ⟨γ, hγ_normalizer, hγq⟩, hqe⟩
    let eγ := hp.monodromy (FundamentalGroup.toPath γ⁻¹)
      (basepointInFiber p he₀)
    -- Compare Lemma 79.3 with the normalizer equation through injectivity of conjugation.
    have h_normalizer :
        (hp.fundamentalGroupMapRange he₀).map (MulAut.conj γ) =
          hp.fundamentalGroupMapRange he₀ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hγ_normalizer
    have h_conj :
        (hp.fundamentalGroupMapRange eγ.2).map (MulAut.conj γ) =
          hp.fundamentalGroupMapRange he₀ := by
      simpa only [eγ] using
        fundamentalGroupMapRange_map_conj_eq_of_monodromy hp he₀ γ
    have h_range :
        hp.fundamentalGroupMapRange eγ.2 = hp.fundamentalGroupMapRange he₀ := by
      apply Subgroup.map_injective
        (f := (MulAut.conj γ).toMonoidHom) (MulAut.conj γ).injective
      rw [MulEquiv.toMonoidHom_eq_coe]
      exact h_conj.trans h_normalizer.symm
    obtain ⟨h, h_eval⟩ :=
      (exists_coveringTransformation_evalInFiber_eq_iff_fundamentalGroupMapRange_eq
        hp e₀ eγ.1 b₀ he₀ eγ.2).mpr h_range
    refine ⟨h, ?_⟩
    calc
      CoveringTransformation.evalInFiber b₀ e₀ he₀ h = eγ := h_eval
      _ = hp.monodromyRightCosetMap he₀ (Quotient.mk'' γ) := by
        symm
        simp only [hp.monodromyRightCosetMap_mk, liftingCorrespondence, eγ]
      _ = hp.monodromyRightCosetMap he₀ q :=
        congrArg (hp.monodromyRightCosetMap he₀) hγq
      _ = e := hqe

end IsCoveringMap
