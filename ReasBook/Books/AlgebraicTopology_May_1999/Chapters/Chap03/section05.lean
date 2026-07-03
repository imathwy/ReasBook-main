import Mathlib
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Endomorphism

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_3_5_1 (from Chap03) -/
universe u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {X : Type u₁} {E : Type u₂} {B : Type u₃}
variable [Groupoid.{v₁} X] [Groupoid.{v₂} E] [Groupoid.{v₃} B]

/-- Helper for Theorem 3.5.1: the chosen endpoint associated to an object `x` is obtained by
lifting the image of the chosen path `a x : x₀ ⟶ x` from the basepoint `e₀`. -/
noncomputable def chosen_lift_obj {p : E ⥤ B} (hp : Functor.IsCovering p) {f : X ⥤ B}
    {x₀ : X} (e₀ : p.Fiber (f.obj x₀)) (a : ∀ x : X, x₀ ⟶ x) (x : X) : p.Fiber (f.obj x) :=
  fiberTranslationMap hp (f.map (a x)) e₀

/-- Helper for Theorem 3.5.1: translating along an equality morphism just transports the fiber
point across the corresponding equality of base objects. -/
lemma fiberTranslationMap_eqToHom {p : E ⥤ B} (hp : Functor.IsCovering p) {b b' : B}
    (h : b = b') (x : p.Fiber b) :
    fiberTranslationMap hp (eqToHom h) x = h ▸ x := by
  cases h
  exact congrFun (fiberTranslationMap_id hp b) x

/-- Helper for Theorem 3.5.1: a fiber translation from a general fiber point can be normalized to
the literal basepoint `⟨e, rfl⟩` by precomposing the base arrow with the equality witness. -/
lemma fiberTranslationMap_normalize_basepoint {p : E ⥤ B} (hp : Functor.IsCovering p)
    {e : E} {b b' : B} (h : p.obj e = b) (γ : b ⟶ b') :
    fiberTranslationMap hp γ ⟨e, h⟩ =
      fiberTranslationMap hp (eqToHom h ≫ γ) ⟨e, rfl⟩ := by
  cases h
  simp [Category.id_comp]

/-- Helper for Theorem 3.5.1: membership in the transported image subgroup is equivalent to
membership of the conjugated loop in the untransported subgroup at the literal basepoint. -/
lemma mapVertexGroup_range_transport_iff {p : E ⥤ B} {e : E} {b : B}
    (h : p.obj e = b) (δ : b ⟶ b) :
    δ ∈ h ▸ (Functor.mapVertexGroup p e).range ↔
      eqToHom h ≫ δ ≫ eqToHom h.symm ∈ (Functor.mapVertexGroup p e).range := by
  -- After eliminating the equality witness, both subgroup-membership conditions are identical.
  cases h
  simp

/-- Helper for Theorem 3.5.1: any loop whose class lies in the transported image subgroup fixes
the chosen fiber point under fiber translation. -/
lemma fiberTranslationMap_eq_self_of_mem_transport_range {p : E ⥤ B} (hp : Functor.IsCovering p)
    {e : E} {b : B} (h : p.obj e = b) (δ : b ⟶ b)
    (hδ : δ ∈ h ▸ (Functor.mapVertexGroup p e).range) :
    fiberTranslationMap hp δ ⟨e, h⟩ = ⟨e, h⟩ := by
  -- First convert the transported membership statement to the literal-basepoint loop subgroup.
  have hδ' : eqToHom h ≫ δ ≫ eqToHom h.symm ∈ (Functor.mapVertexGroup p e).range := by
    exact (mapVertexGroup_range_transport_iff h δ).1 hδ
  -- At the literal basepoint, Remark 3.3.13 shows that loops in the subgroup act trivially.
  have hbase :
      fiberTranslationMap hp (eqToHom h ≫ δ ≫ eqToHom h.symm) ⟨e, rfl⟩ = ⟨e, rfl⟩ := by
    have hmemInv :
        𝟙 (p.obj e) * (eqToHom h ≫ δ ≫ eqToHom h.symm)⁻¹ ∈
          (Functor.mapVertexGroup p e).range := by
      simpa using Subgroup.inv_mem (Functor.mapVertexGroup p e).range hδ'
    have := fiberTranslation_basepoint_eq_of_mem_mapVertexGroup_range hp e
        (eqToHom h ≫ δ ≫ eqToHom h.symm) (𝟙 (p.obj e)) hmemInv
    rw [congrFun (fiberTranslationMap_id hp (p.obj e)) ⟨e, rfl⟩] at this
    exact this
  -- Transport the literal-basepoint fixed-point statement back to the original fiber point.
  calc
    fiberTranslationMap hp δ ⟨e, h⟩ =
        fiberTranslationMap hp (eqToHom h ≫ δ) ⟨e, rfl⟩ := by
      simpa using fiberTranslationMap_normalize_basepoint hp h δ
    _ = fiberTranslationMap hp
          ((eqToHom h ≫ δ ≫ eqToHom h.symm) ≫ eqToHom h) ⟨e, rfl⟩ := by
      simp [Category.assoc]
    _ = fiberTranslationMap hp (eqToHom h)
          (fiberTranslationMap hp (eqToHom h ≫ δ ≫ eqToHom h.symm) ⟨e, rfl⟩) := by
      symm
      change
        (fiberTranslationMap hp (eqToHom h) ∘
            fiberTranslationMap hp (eqToHom h ≫ δ ≫ eqToHom h.symm)) ⟨e, rfl⟩ =
          fiberTranslationMap hp ((eqToHom h ≫ δ ≫ eqToHom h.symm) ≫ eqToHom h) ⟨e, rfl⟩
      exact (congrArg (fun m => m ⟨e, rfl⟩)
        (fiberTranslationMap_comp hp (eqToHom h ≫ δ ≫ eqToHom h.symm) (eqToHom h))).symm
    _ = fiberTranslationMap hp (eqToHom h) ⟨e, rfl⟩ := by
      rw [hbase]
    _ = h ▸ (⟨e, rfl⟩ : p.Fiber (p.obj e)) := by
      rw [fiberTranslationMap_eqToHom hp]
    _ = ⟨e, h⟩ := by
      cases h
      rfl

/-- Helper for Theorem 3.5.1: under the subgroup hypothesis, the endpoint of the lifted image of a
path `x₀ ⟶ x` is independent of the chosen path. -/
lemma lift_endpoint_eq_of_subgroup_inclusion {p : E ⥤ B} (hp : Functor.IsCovering p)
    {f : X ⥤ B} (x₀ : X) (e₀ : p.Fiber (f.obj x₀))
    (hsub : (Functor.mapVertexGroup f x₀).range ≤
      e₀.2 ▸ (Functor.mapVertexGroup p e₀.1).range)
    {x : X} (α₁ α₂ : x₀ ⟶ x) :
    fiberTranslationMap hp (f.map α₁) e₀ =
      fiberTranslationMap hp (f.map α₂) e₀ := by
  symm
  -- The loop comparing the two chosen paths is based at `x₀`, so the subgroup hypothesis applies.
  have hloop :
      f.map (α₂ ≫ CategoryTheory.Groupoid.inv α₁) ∈
        e₀.2 ▸ (Functor.mapVertexGroup p e₀.1).range := by
    apply hsub
    refine ⟨α₂ ≫ CategoryTheory.Groupoid.inv α₁, ?_⟩
    simp [Functor.map_comp]
  -- Once that loop fixes `e₀`, composing with `α₁` reproduces the lift along `α₂`.
  have hfix :
      fiberTranslationMap hp (f.map (α₂ ≫ CategoryTheory.Groupoid.inv α₁)) e₀ = e₀ := by
    exact fiberTranslationMap_eq_self_of_mem_transport_range hp e₀.2
      (f.map (α₂ ≫ CategoryTheory.Groupoid.inv α₁)) hloop
  calc
    fiberTranslationMap hp (f.map α₂) e₀ =
        fiberTranslationMap hp (f.map ((α₂ ≫ CategoryTheory.Groupoid.inv α₁) ≫ α₁)) e₀ := by
      simp
    _ = fiberTranslationMap hp (f.map α₁)
          (fiberTranslationMap hp (f.map (α₂ ≫ CategoryTheory.Groupoid.inv α₁)) e₀) := by
      simpa [Functor.map_comp] using
        congrArg (fun m => m e₀)
          (fiberTranslationMap_comp hp
            (f.map (α₂ ≫ CategoryTheory.Groupoid.inv α₁)) (f.map α₁))
    _ = fiberTranslationMap hp (f.map α₁) e₀ := by
      rw [hfix]

/-- Helper for Theorem 3.5.1: the chosen lifted object is compatible with transport along a
source morphism `β : x ⟶ y`. -/
lemma chosen_lift_obj_comp {p : E ⥤ B} (hp : Functor.IsCovering p) {f : X ⥤ B} (x₀ : X)
    (e₀ : p.Fiber (f.obj x₀))
    (hsub : (Functor.mapVertexGroup f x₀).range ≤
      e₀.2 ▸ (Functor.mapVertexGroup p e₀.1).range)
    (a : ∀ x : X, x₀ ⟶ x) {x y : X} (β : x ⟶ y) :
    fiberTranslationMap hp (f.map β) (chosen_lift_obj (x₀ := x₀) hp e₀ a x) =
        chosen_lift_obj (x₀ := x₀) hp e₀ a y := by
  -- First concatenate the chosen path to `x` with `β`, then invoke path independence.
  calc
    fiberTranslationMap hp (f.map β) (chosen_lift_obj (x₀ := x₀) hp e₀ a x) =
        fiberTranslationMap hp (f.map (a x ≫ β)) e₀ := by
      rw [chosen_lift_obj, Functor.map_comp]
      change
        (fiberTranslationMap hp (f.map β) ∘ fiberTranslationMap hp (f.map (a x))) e₀ =
          fiberTranslationMap hp (f.map (a x) ≫ f.map β) e₀
      exact (congrArg (fun m => m e₀)
        (fiberTranslationMap_comp hp (f.map (a x)) (f.map β))).symm
    _ = chosen_lift_obj (x₀ := x₀) hp e₀ a y := by
      rw [chosen_lift_obj]
      exact lift_endpoint_eq_of_subgroup_inclusion hp x₀ e₀ hsub (a x ≫ β) (a y)

variable [CategoryTheory.IsConnected X]

/-- Theorem 3.5.1: for a covering functor `p : E ⥤ B`, a functor `f : X ⥤ B` from a connected
groupoid `X`, and a chosen point `e₀` of the fiber over `f.obj x₀`, there is a unique lift
`g : X ⥤ E` with
`g.obj x₀ = e₀.1` exactly when the image of the vertex group at `x₀` under `f` is contained in
the image of the vertex group at `e₀.1` under `p`, after identifying both as subgroups of the
vertex group at `f.obj x₀`. -/
-- Proof sketch: the forward implication is `Functor.mapVertexGroup_range_le_of_lift`. For the
-- converse, choose for each object `x : X` a morphism `α : x₀ ⟶ x`, lift `f.map α` through the
-- covering functor starting at `e₀`, and use the subgroup inclusion hypothesis to show that the
-- resulting endpoint is independent of the chosen `α`; the same lifting prescription on morphisms
-- then defines the unique functor lift.
theorem existsUnique_lift_iff_mapVertexGroup_range_le {p : E ⥤ B} (hp : Functor.IsCovering p)
    {f : X ⥤ B} (x₀ : X) (e₀ : p.Fiber (f.obj x₀)) :
    (∃! g : X ⥤ E, g ⋙ p = f ∧ g.obj x₀ = e₀.1) ↔
      (Functor.mapVertexGroup f x₀).range ≤
        e₀.2 ▸ (Functor.mapVertexGroup p e₀.1).range := by
  constructor
  · rintro ⟨g, hg, _⟩
    exact Functor.mapVertexGroup_range_le_of_lift x₀ e₀ hg.1 hg.2
  · intro hsub
    classical
    have hVertexInjective : ∀ e : E, Function.Injective (Functor.mapVertexGroup p e) := by
      intro e γ δ hγδ
      have hUnder :
          (Under.post p).obj (Under.mk γ) = (Under.post p).obj (Under.mk δ) :=
        congrArg Under.mk hγδ
      have hEq : Under.mk γ = Under.mk δ := (hp.star_bijective e).injective hUnder
      cases hEq
      rfl
    -- Follow the source proof: choose one path from `x₀` to each object and lift it from `e₀`.
    let a : ∀ x : X, x₀ ⟶ x := fun x ↦
      Classical.choice (show Nonempty (x₀ ⟶ x) from inferInstance)
    let gObj : ∀ x : X, p.Fiber (f.obj x) := fun x ↦
      chosen_lift_obj (x₀ := x₀) hp e₀ a x
    have hgObj_comp : ∀ {x y : X} (β : x ⟶ y),
        fiberTranslationMap hp (f.map β) (gObj x) = gObj y := by
      intro x y β
      exact chosen_lift_obj_comp hp x₀ e₀ hsub a β
    have hgObj₀ : gObj x₀ = e₀ := by
      have h := lift_endpoint_eq_of_subgroup_inclusion hp x₀ e₀ hsub (a x₀) (𝟙 x₀)
      simp [Functor.map_id] at h
      have hid : fiberTranslationMap hp (𝟙 (f.obj x₀)) e₀ = e₀ :=
        congrFun (fiberTranslationMap_id hp (f.obj x₀)) e₀
      simp [gObj, chosen_lift_obj, h, hid]
    have hgObj_val_comp : ∀ {x y : X} (β : x ⟶ y),
        (fiberTranslationMap hp (f.map β) (gObj x)).1 = (gObj y).1 := by
      intro x y β
      exact congrArg Subtype.val (hgObj_comp β)
    let gMap : ∀ {x y : X}, (x ⟶ y) → ((gObj x).1 ⟶ (gObj y).1) := fun {x y} β ↦
      (starLift hp (f.map β) (gObj x)).hom ≫ eqToHom (hgObj_val_comp β)
    have hgMap_transport : ∀ {x y : X} (β : x ⟶ y),
        eqToHom (starLift_obj hp (f.map β) (gObj x)).symm ≫ p.map (eqToHom (hgObj_val_comp β)) =
          eqToHom (gObj y).2.symm := by
      intro x y β
      -- The two endpoint identifications are proofs of the same equality, so proof irrelevance
      -- collapses the remaining transport.
      have hEq :
          (starLift_obj hp (f.map β) (gObj x)).symm.trans (congrArg p.obj (hgObj_val_comp β)) =
            (gObj y).2.symm := by
        apply Subsingleton.elim
      calc
        eqToHom (starLift_obj hp (f.map β) (gObj x)).symm ≫ p.map (eqToHom (hgObj_val_comp β)) =
            eqToHom (starLift_obj hp (f.map β) (gObj x)).symm ≫
              eqToHom (congrArg p.obj (hgObj_val_comp β)) := by
          rw [eqToHom_map]
        _ =
            eqToHom
              ((starLift_obj hp (f.map β) (gObj x)).symm.trans
                (congrArg p.obj (hgObj_val_comp β))) := by
          rw [eqToHom_trans]
        _ = eqToHom (gObj y).2.symm := by
          rw [hEq]
    have hgMap_over : ∀ {x y : X} (β : x ⟶ y),
        p.map (gMap β) =
          eqToHom (gObj x).2 ≫ f.map β ≫ eqToHom (gObj y).2.symm := by
      intro x y β
      -- Route correction: keep the codomain-adjustment explicit and cancel it with one transport
      -- identity, instead of repeatedly destructing dependent equalities of fiber points.
      have htransport := hgMap_transport β
      have hstar :
          p.map (gMap β) =
            ((eqToHom (gObj x).2 ≫ f.map β ≫ eqToHom (starLift_obj hp (f.map β) (gObj x)).symm) ≫
              p.map (eqToHom (hgObj_val_comp β))) := by
        have h₁ :
            p.map (gMap β) =
              p.map (starLift hp (f.map β) (gObj x)).hom ≫ p.map (eqToHom (hgObj_val_comp β)) := by
          simp [gMap]
        have h₂raw :=
          congrArg (fun k ↦ k ≫ p.map (eqToHom (hgObj_val_comp β)))
            (starLift_hom_over hp (f.map β) (gObj x))
        exact h₁.trans h₂raw
      calc
        p.map (gMap β) =
            eqToHom (gObj x).2 ≫ f.map β ≫ eqToHom (starLift_obj hp (f.map β) (gObj x)).symm ≫
              p.map (eqToHom (hgObj_val_comp β)) := by
          simpa [Category.assoc] using hstar
        _ =
            eqToHom (gObj x).2 ≫ f.map β ≫ eqToHom (gObj y).2.symm := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ eqToHom (gObj x).2 ≫ f.map β ≫ k) htransport
    have hgMap_id : ∀ x : X, gMap (𝟙 x) = 𝟙 ((gObj x).1) := by
      intro x
      -- Since both candidates are loops at `(gObj x).1`, injectivity on the vertex group
      -- upgrades equality after applying `p` to equality in `E`.
      have hmap : p.map (gMap (𝟙 x)) = 𝟙 (p.obj ((gObj x).1)) := by
        simpa using hgMap_over (𝟙 x)
      exact (hVertexInjective ((gObj x).1)) (by simpa using hmap)
    have hgMap_comp : ∀ {x y z : X} (β : x ⟶ y) (γ : y ⟶ z),
        gMap (β ≫ γ) = gMap β ≫ gMap γ := by
      intro x y z β γ
      -- Compare the two arrows by forming the loop obtained from their quotient.
      have hmap :
          p.map (gMap (β ≫ γ)) = p.map (gMap β ≫ gMap γ) := by
        calc
          p.map (gMap (β ≫ γ)) =
              eqToHom (gObj x).2 ≫ f.map (β ≫ γ) ≫ eqToHom (gObj z).2.symm := by
            rw [hgMap_over]
          _ =
              (eqToHom (gObj x).2 ≫ f.map β ≫ eqToHom (gObj y).2.symm) ≫
                (eqToHom (gObj y).2 ≫ f.map γ ≫ eqToHom (gObj z).2.symm) := by
            simp [Functor.map_comp, Category.assoc]
          _ = p.map (gMap β) ≫ p.map (gMap γ) := by
            rw [hgMap_over, hgMap_over]
          _ = p.map (gMap β ≫ gMap γ) := by
            simp [Functor.map_comp]
      let rhsComp : (gObj x).1 ⟶ (gObj z).1 := gMap β ≫ gMap γ
      have hloop :
          gMap (β ≫ γ) ≫ CategoryTheory.Groupoid.inv rhsComp = 𝟙 ((gObj x).1) := by
        apply (hVertexInjective ((gObj x).1))
        calc
          p.map (gMap (β ≫ γ) ≫ CategoryTheory.Groupoid.inv rhsComp) =
              p.map (gMap (β ≫ γ)) ≫ CategoryTheory.Groupoid.inv (p.map rhsComp) := by
            simp [Functor.map_comp]
          _ = p.map rhsComp ≫ CategoryTheory.Groupoid.inv (p.map rhsComp) := by
            rw [hmap]
          _ = (Functor.mapVertexGroup p ((gObj x).1)) (𝟙 ((gObj x).1)) := by
            simp
      have hcancel := congrArg (fun k ↦ k ≫ rhsComp) hloop
      simpa [rhsComp, Category.assoc] using hcancel
    let g : X ⥤ E := {
      obj := fun x ↦ (gObj x).1
      map := fun {x y} β ↦ gMap β
      map_id := fun x ↦ hgMap_id x
      map_comp := fun {x y z} β γ ↦ hgMap_comp β γ
    }
    have hg : g ⋙ p = f := by
      -- On objects the chosen lift lands over `f.obj x`, and on morphisms `hgMap_over` gives the
      -- required transported equality in the base.
      refine CategoryTheory.Functor.ext (fun x ↦ by simpa [g] using (gObj x).2) ?_
      intro x y β
      simpa [g, Functor.comp_map] using hgMap_over β
    have hg₀ : g.obj x₀ = e₀.1 := by
      -- The chosen lifted object at the basepoint is exactly the prescribed fiber point `e₀`.
      simpa [g] using congrArg Subtype.val hgObj₀
    refine ⟨g, ⟨hg, hg₀⟩, ?_⟩
    intro g' hg'
    let e₀' : p.Fiber (f.obj x₀) := ⟨g'.obj x₀, by
      simpa [Functor.comp_obj] using congrArg (fun k : X ⥤ B ↦ k.obj x₀) hg'.1⟩
    have he₀' : e₀' = e₀ := by
      apply Subtype.ext
      exact hg'.2
    have hpath : ∀ x : X, Under.mk (g'.map (a x)) = starLift hp (f.map (a x)) e₀' := by
      intro x
      -- Both arrows start at `g'.obj x₀`, so compare them before identifying that source with `e₀`.
      apply (hp.star_bijective (g'.obj x₀)).injective
      calc
        (Under.post p).obj (Under.mk (g'.map (a x))) = Under.mk (p.map (g'.map (a x))) := by
          simp [Under.post]
        _ =
            Under.mk
              (eqToHom e₀'.2 ≫ f.map (a x) ≫
                eqToHom (congrArg (fun k : X ⥤ B ↦ k.obj x) hg'.1).symm) := by
          simpa [e₀', Functor.comp_obj, Functor.comp_map] using
            congrArg Under.mk (Functor.congr_hom hg'.1 (a x))
        _ = Under.mk (eqToHom e₀'.2 ≫ f.map (a x)) := by
          simpa [Category.assoc] using
            under_mk_comp_eqToHom
              (eqToHom e₀'.2 ≫ f.map (a x))
              (congrArg (fun k : X ⥤ B ↦ k.obj x) hg'.1).symm
        _ = (Under.post p).obj (starLift hp (f.map (a x)) e₀') := by
          have hstar := starLift_post_eq hp (f.map (a x)) e₀'
          rw [fiber_transport_under_mk] at hstar
          exact hstar.symm
    have hobj : ∀ x : X, g'.obj x = g.obj x := by
      intro x
      -- Project the chosen-path comparison to the right endpoint of the lifted arrow.
      have hright : g'.obj x = (starLift hp (f.map (a x)) e₀').right := by
        exact congrArg Comma.right (hpath x)
      rw [he₀'] at hright
      simpa [g, gObj, chosen_lift_obj] using hright
    -- With the source and target objects identified, star-map injectivity upgrades equality after
    -- composing with `p` to equality of the lifted arrows themselves.
    refine CategoryTheory.Functor.ext hobj ?_
    intro x y β
    have hcomp : g' ⋙ p = g ⋙ p := hg'.1.trans hg.symm
    let rhs : g'.obj x ⟶ g'.obj y := eqToHom (hobj x) ≫ g.map β ≫ eqToHom (hobj y).symm
    let rhsInv : g'.obj y ⟶ g'.obj x :=
      eqToHom (hobj y) ≫ CategoryTheory.Groupoid.inv (g.map β) ≫ eqToHom (hobj x).symm
    have hmap : p.map (g'.map β) = p.map rhs := by
      simpa [rhs, Functor.comp_map, eqToHom_map, Category.assoc] using Functor.congr_hom hcomp β
    have hloop : g'.map β ≫ rhsInv = 𝟙 (g'.obj x) := by
      apply (hVertexInjective (g'.obj x))
      calc
        p.map (g'.map β ≫ rhsInv) = p.map (g'.map β) ≫ p.map rhsInv := by
          simp [rhsInv, Functor.map_comp]
        _ = p.map rhs ≫ p.map rhsInv := by
          rw [hmap]
        _ = (Functor.mapVertexGroup p (g'.obj x)) (𝟙 (g'.obj x)) := by
          simp [rhs, rhsInv, eqToHom_map, Category.assoc]
    have hcancel := congrArg (fun k ↦ k ≫ rhs) hloop
    simpa [rhs, rhsInv, Category.assoc] using hcancel

end CategoryTheory.Functor.IsCovering

/-! ### ProofStep_3_5_2 (from Chap03) -/
universe u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor

variable {X : Type u₁} {E : Type u₂} {B : Type u₃}
variable [Groupoid.{v₁} X] [Groupoid.{v₂} E] [Groupoid.{v₃} B]

/-- ProofStep 3.5.2: if `g : X ⥤ E` lifts `f : X ⥤ B` through `p : E ⥤ B` and sends the chosen
base object `x₀` to the chosen point `e₀` of the fiber over `f.obj x₀`, then the image of the
vertex group at `x₀` under `f` is contained in the image of the vertex group at `e₀.1` under
`p`, viewed inside the vertex group at `f.obj x₀`. -/
-- Proof sketch: for any loop `γ : x₀ ⟶ x₀`, the morphism `g.map γ` is a loop at `g.obj x₀`, hence
-- after transporting along `g.obj x₀ = e₀.1` it becomes a loop at `e₀.1` whose image under `p`
-- is exactly `f.map γ` because `g ⋙ p = f`.
theorem mapVertexGroup_range_le_of_lift {p : E ⥤ B} {f : X ⥤ B} {g : X ⥤ E} (x₀ : X)
    (e₀ : p.Fiber (f.obj x₀)) (hg : g ⋙ p = f) (hg₀ : g.obj x₀ = e₀.1) :
    (Functor.mapVertexGroup f x₀).range ≤
      e₀.2 ▸ (Functor.mapVertexGroup p e₀.1).range := by
  have he₀ : e₀ = ⟨g.obj x₀, congrArg (fun k : X ⥤ B ↦ k.obj x₀) hg⟩ := by
    apply Subtype.ext
    exact hg₀.symm
  cases he₀
  cases hg
  intro γ hγ
  rcases hγ with ⟨δ, rfl⟩
  exact ⟨g.map δ, rfl⟩

end CategoryTheory.Functor

/-! ### ProofStep_3_5_3 (from Chap03) -/
universe u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {X : Type u₁} {E : Type u₂} {B : Type u₃}
variable [Groupoid.{v₁} X] [Groupoid.{v₂} E] [Groupoid.{v₃} B]

/-- Helper for ProofStep 3.5.3: transporting along an equality morphism acts on the fiber by
transporting the chosen point across that equality. -/
lemma fiberTranslationMap_eqToHom {p : E ⥤ B} (hp : Functor.IsCovering p) {b b' : B}
    (h : b = b') (x : p.Fiber b) :
    fiberTranslationMap hp (eqToHom h) x = h ▸ x := by
  cases h
  exact congrFun (fiberTranslationMap_id hp b) x

/-- Helper for ProofStep 3.5.3: a fiber translation from a general fiber point can be normalized
to the literal basepoint `⟨e, rfl⟩` by precomposing with the equality witness. -/
lemma fiberTranslationMap_normalize_basepoint {p : E ⥤ B} (hp : Functor.IsCovering p)
    {e : E} {b b' : B} (h : p.obj e = b) (γ : b ⟶ b') :
    fiberTranslationMap hp γ ⟨e, h⟩ =
      fiberTranslationMap hp (eqToHom h ≫ γ) ⟨e, rfl⟩ := by
  cases h
  simp [Category.id_comp]

/-- Helper for ProofStep 3.5.3: membership in the transported image subgroup is equivalent to
membership of the corresponding conjugated loop in the untransported subgroup. -/
lemma mapVertexGroup_range_transport_iff {p : E ⥤ B} {e : E} {b : B}
    (h : p.obj e = b) (δ : b ⟶ b) :
    δ ∈ h ▸ (Functor.mapVertexGroup p e).range ↔
      eqToHom h ≫ δ ≫ eqToHom h.symm ∈ (Functor.mapVertexGroup p e).range := by
  -- Once the equality witness is removed, both subgroup-membership conditions are identical.
  cases h
  simp

/-- Helper for ProofStep 3.5.3: a loop in the vertex-group image fixes the literal basepoint in
the fiber under direct fiber translation. -/
private theorem mem_mapVertexGroup_range_iff_fiberTranslationMap_basepoint_eq
    {p : E ⥤ B} (hp : Functor.IsCovering p) (e : E) (γ : p.obj e ⟶ p.obj e) :
    γ ∈ (Functor.mapVertexGroup p e).range ↔
      fiberTranslationMap hp γ ⟨e, rfl⟩ = ⟨e, rfl⟩ := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  constructor
  · intro hγ
    have hstab : γ ∈ MulAction.stabilizer (p.obj e ⟶ p.obj e) x₀ := by
      rwa [fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e]
    change fiberTranslationMap hp γ⁻¹ x₀ = x₀ at hstab
    calc
      fiberTranslationMap hp γ x₀ = fiberTranslationMap hp γ (fiberTranslationMap hp γ⁻¹ x₀) := by
        rw [hstab]
      _ = x₀ := by
        change (fiberTranslationFunctor hp).map γ ((fiberTranslationFunctor hp).map γ⁻¹ x₀) = x₀
        rw [← Functor.map_comp_apply]
        simp [show γ⁻¹ ≫ γ = 𝟙 _ from Groupoid.inv_comp γ]
        rfl
  · intro hγ
    have hinv : fiberTranslationMap hp γ⁻¹ x₀ = x₀ := by
      calc
        fiberTranslationMap hp γ⁻¹ x₀ =
            fiberTranslationMap hp γ⁻¹ (fiberTranslationMap hp γ x₀) := by
          rw [hγ]
        _ = x₀ := by
          change (fiberTranslationFunctor hp).map γ⁻¹ ((fiberTranslationFunctor hp).map γ x₀) = x₀
          rw [← Functor.map_comp_apply]
          simp [show γ ≫ γ⁻¹ = 𝟙 _ from Groupoid.comp_inv γ]
          rfl
    have hstab : γ ∈ MulAction.stabilizer (p.obj e ⟶ p.obj e) x₀ := by
      change fiberTranslationMap hp γ⁻¹ x₀ = x₀
      exact hinv
    rwa [fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e] at hstab

/-- Helper for ProofStep 3.5.3: any loop whose class lies in the transported image subgroup fixes
the chosen fiber point under fiber translation. -/
lemma fiberTranslationMap_eq_self_of_mem_transport_range {p : E ⥤ B} (hp : Functor.IsCovering p)
    {e : E} {b : B} (h : p.obj e = b) (δ : b ⟶ b)
    (hδ : δ ∈ h ▸ (Functor.mapVertexGroup p e).range) :
    fiberTranslationMap hp δ ⟨e, h⟩ = ⟨e, h⟩ := by
  -- First move the subgroup-membership statement to the literal basepoint `⟨e, rfl⟩`.
  have hδ' : eqToHom h ≫ δ ≫ eqToHom h.symm ∈ (Functor.mapVertexGroup p e).range := by
    exact (mapVertexGroup_range_transport_iff h δ).1 hδ
  have hbase :
      fiberTranslationMap hp (eqToHom h ≫ δ ≫ eqToHom h.symm) ⟨e, rfl⟩ = ⟨e, rfl⟩ := by
    exact (mem_mapVertexGroup_range_iff_fiberTranslationMap_basepoint_eq hp e
      (eqToHom h ≫ δ ≫ eqToHom h.symm)).mp hδ'
  -- Then transport that fixed-point statement back along the equality witness.
  calc
    fiberTranslationMap hp δ ⟨e, h⟩ =
        fiberTranslationMap hp (eqToHom h ≫ δ) ⟨e, rfl⟩ := by
      simpa using fiberTranslationMap_normalize_basepoint hp h δ
    _ = fiberTranslationMap hp
          ((eqToHom h ≫ δ ≫ eqToHom h.symm) ≫ eqToHom h) ⟨e, rfl⟩ := by
      simp [Category.assoc]
    _ = fiberTranslationMap hp (eqToHom h)
          (fiberTranslationMap hp (eqToHom h ≫ δ ≫ eqToHom h.symm) ⟨e, rfl⟩) := by
      rw [fiberTranslationMap_comp]
      rfl
    _ = fiberTranslationMap hp (eqToHom h) ⟨e, rfl⟩ := by
      rw [hbase]
    _ = h ▸ (⟨e, rfl⟩ : p.Fiber (p.obj e)) := by
      rw [fiberTranslationMap_eqToHom hp]
    _ = ⟨e, h⟩ := by
      cases h
      rfl

/-- ProofStep 3.5.3: under the subgroup condition from Theorem 3.5.1, the candidate value
`fiberTranslationMap hp (f.map α) e₀` used to define the lifted functor at an object `x` is
independent of the chosen morphism `α : x₀ ⟶ x`. -/
-- Proof sketch: the loop `α₂ * α₁⁻¹` at `x₀` maps under `f` to
-- `f.map α₂ * (f.map α₁)⁻¹`. The subgroup inclusion hypothesis puts this loop in the image of
-- `π(E, e₀.1)` under `p`, so the basepoint-independence lemma
-- `fiberTranslation_basepoint_eq_of_mem_mapVertexGroup_range` shows that this loop fixes `e₀`.
-- Composing with the lift of `f.map α₁` then identifies the endpoints of the lifts of
-- `f.map α₁` and `f.map α₂`.
theorem fiberTranslationMap_eq_of_mapVertexGroup_range_le {p : E ⥤ B}
    (hp : Functor.IsCovering p) {f : X ⥤ B} (x₀ : X) (e₀ : p.Fiber (f.obj x₀))
    (hsub : (Functor.mapVertexGroup f x₀).range ≤
      e₀.2 ▸ (Functor.mapVertexGroup p e₀.1).range)
    {x : X} (α₁ α₂ : x₀ ⟶ x) :
    fiberTranslationMap hp (f.map α₁) e₀ = fiberTranslationMap hp (f.map α₂) e₀ := by
  symm
  -- Compare the two candidate lifts by the loop based at `x₀` obtained from `α₂` and `α₁`.
  have hloop :
      f.map (α₂ ≫ CategoryTheory.Groupoid.inv α₁) ∈
        e₀.2 ▸ (Functor.mapVertexGroup p e₀.1).range := by
    apply hsub
    refine ⟨α₂ ≫ CategoryTheory.Groupoid.inv α₁, ?_⟩
    simp [Functor.map_comp]
  -- The subgroup condition forces that comparison loop to fix the chosen basepoint in the fiber.
  have hfix :
      fiberTranslationMap hp (f.map (α₂ ≫ CategoryTheory.Groupoid.inv α₁)) e₀ = e₀ := by
    exact fiberTranslationMap_eq_self_of_mem_transport_range hp e₀.2
      (f.map (α₂ ≫ CategoryTheory.Groupoid.inv α₁)) hloop
  -- Rewrite the lift along `α₂` as the comparison loop followed by the lift along `α₁`.
  calc
    fiberTranslationMap hp (f.map α₂) e₀ =
        fiberTranslationMap hp (f.map ((α₂ ≫ CategoryTheory.Groupoid.inv α₁) ≫ α₁)) e₀ := by
      simp
    _ = fiberTranslationMap hp (f.map α₁)
          (fiberTranslationMap hp (f.map (α₂ ≫ CategoryTheory.Groupoid.inv α₁)) e₀) := by
      simpa [Functor.map_comp] using
        congrArg (fun m => m e₀)
          (fiberTranslationMap_comp hp
            (f.map (α₂ ≫ CategoryTheory.Groupoid.inv α₁)) (f.map α₁))
    _ = fiberTranslationMap hp (f.map α₁) e₀ := by
      rw [hfix]

end CategoryTheory.Functor.IsCovering

/-! ### Definition_3_5_4 (from Chap03) -/
open CategoryTheory

universe u v

variable {E E' B : Type u} [Groupoid.{v} E] [Groupoid.{v} E'] [Groupoid.{v} B]
  (p : E ⥤ B) (p' : E' ⥤ B)

/- Definition 3.5.4: a map of coverings of `B`, from `p : E ⥤ B` to `p' : E' ⥤ B`, is a
morphism in the over-category `Over (Cat.of B)`. Equivalently, it is a functor `g : E ⥤ E'`
such that `g ⋙ p' = p`. -/
#check (Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom)

/-! ### Lemma_3_5_5 (from Chap03) -/
universe u v

open CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {E E' B : Type u} [Groupoid.{v} E] [Groupoid.{v} E'] [Groupoid.{v} B]
variable [CategoryTheory.IsPreconnected E']
variable {p : E ⥤ B} {p' : E' ⥤ B}

/-- Lemma 3.5.5: if the target total groupoid is preconnected, then a functor between two covering
functors over the same base groupoid is itself a covering functor. -/
-- Proof sketch: surjectivity on objects follows from the commutative triangle
-- `g ⋙ p' = p`, using surjectivity of `p` on objects and then lifting the resulting base
-- isomorphism through the covering `p'`. Bijectivity on each star follows because the square of
-- star maps induced by `g`, `p`, and `p'` commutes, and the star maps for `p` and `p'` are
-- bijections.
theorem of_map_of_coverings (hp : Functor.IsCovering p) (hp' : Functor.IsCovering p')
    (g : E ⥤ E') (hg : g ⋙ p' = p) :
    Functor.IsCovering g := by
  cases hg
  refine ⟨?_, ?_⟩
  · intro e'
    obtain ⟨e, he⟩ := hp.obj_surjective (p'.obj e')
    let α : g.obj e ⟶ e' :=
      Classical.choice (CategoryTheory.nonempty_hom_of_preconnected_groupoid (g.obj e) e')
    obtain ⟨x, hx⟩ := (hp.star_bijective e).surjective (Under.mk (p'.map α))
    have hxg : (Under.post g).obj x = Under.mk α := by
      apply (hp'.star_bijective (g.obj e)).injective
      simpa [Functor.comp_map] using hx
    refine ⟨x.right, ?_⟩
    simpa using congrArg (fun u : Under (g.obj e) ↦ u.right) hxg
  · intro e
    refine ⟨?_, ?_⟩
    · intro u v h
      obtain ⟨_, fu, rfl⟩ := Under.mk_surjective u
      obtain ⟨_, fv, rfl⟩ := Under.mk_surjective v
      apply (hp.star_bijective e).injective
      have h' := congrArg (fun x ↦ (Under.post p').obj x) h
      simpa [Functor.comp_map] using h'
    · intro y
      obtain ⟨_, fy, rfl⟩ := Under.mk_surjective y
      obtain ⟨x, hx⟩ := (hp.star_bijective e).surjective (Under.mk (p'.map fy))
      refine ⟨x, ?_⟩
      apply (hp'.star_bijective (g.obj e)).injective
      simpa [Functor.comp_map] using hx

end CategoryTheory.Functor.IsCovering

/-! ### Theorem_3_5_6 (from Chap03) -/
universe u v

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {E E' B : Type u} [Groupoid.{v} E] [Groupoid.{v} E'] [Groupoid.{v} B]
variable {p : E ⥤ B} {p' : E' ⥤ B}

/-- Theorem 3.5.6: for a connected groupoid `E`, a functor `p : E ⥤ B`, a covering functor
`p' : E' ⥤ B`, and chosen points `e` and `e'` of the fibers over the same base object `b`, there
exists a unique map of coverings
`h : Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom` with `h.left.toFunctor.obj e.1 = e'.1` exactly
when the image of the vertex group at `e.1` under `p` is contained in the image of the vertex
group at `e'.1` under `p'`, both viewed as subgroups of `π(B,b)`. -/
-- Proof sketch: specialize `existsUnique_lift_iff_mapVertexGroup_range_le` to the functor
-- `f := p` and the base object `e.1`, then package the resulting lift functor as a morphism in
-- `Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom`. The chosen point `e'` lies over `p.obj e.1 = b`,
-- so the subgroup condition is exactly the inclusion of `p(π(E,e.1))` into
-- `p'(π(E',e'.1))` inside `π(B,b)`.
theorem existsUnique_map_iff_mapVertexGroup_range_le
    [IsConnected E] (hp' : Functor.IsCovering p') (b : B)
    (e : p.Fiber b) (e' : p'.Fiber b) :
    (∃! h : Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom,
      let g : E ⥤ E' := h.left.toFunctor
      g.obj e.1 = e'.1) ↔
      e.2 ▸ (Functor.mapVertexGroup p e.1).range ≤
        e'.2 ▸ (Functor.mapVertexGroup p' e'.1).range := by
  rcases e with ⟨e, rfl⟩
  constructor
  · rintro ⟨h, hh, huniq⟩
    refine (existsUnique_lift_iff_mapVertexGroup_range_le hp' e e').mp ?_
    refine ⟨h.left.toFunctor, ?_, ?_⟩
    · refine ⟨?_, by simpa using hh⟩
      simpa using congrArg (fun F ↦ F.toFunctor) (Over.w h)
    · intro g hg
      have hhg :
          Over.homMk g.toCatHom (by simpa using congrArg Functor.toCatHom hg.1) = h :=
        huniq (Over.homMk g.toCatHom (by simpa using congrArg Functor.toCatHom hg.1))
          (by simpa using hg.2)
      simpa using congrArg (fun k ↦ k.left.toFunctor) hhg
  · intro hsub
    rcases (existsUnique_lift_iff_mapVertexGroup_range_le hp' e e').mpr hsub with
      ⟨g, hg, huniq⟩
    refine ⟨Over.homMk g.toCatHom (by simpa using congrArg Functor.toCatHom hg.1), ?_, ?_⟩
    · simpa using hg.2
    · intro h hh
      apply Over.OverMorphism.ext
      simpa using congrArg Functor.toCatHom <|
        huniq h.left.toFunctor
          ⟨by simpa using congrArg (fun F ↦ F.toFunctor) (Over.w h), by simpa using hh⟩

/-- Companion for Theorem 3.5.6: for connected total groupoids `E` and `E'`, a map of coverings
`h : Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom` over `B` sending `e` to `e'` is an isomorphism of
coverings exactly when the image subgroups `p(π(E,e.1))` and `p'(π(E',e'.1))` coincide inside
`π(B,b)`. -/
-- Proof sketch: if `h` is an isomorphism, use the induced inverse map of coverings and
-- part (1) in both directions to obtain the two subgroup inclusions. Conversely,
-- equality gives a reverse map of coverings from part (1). Here `E'` is connected
-- because it is preconnected and `e'.1` provides an object of `E'`.
-- Uniqueness of lifts then shows that the two composites are
-- identities, so `h` is an isomorphism in the over-category.
theorem isIso_map_iff_mapVertexGroup_range_eq
    [IsConnected E] [IsPreconnected E']
    (hp : Functor.IsCovering p) (hp' : Functor.IsCovering p') (b : B)
    (e : p.Fiber b) (e' : p'.Fiber b)
    (h : Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom)
    (hh : let g : E ⥤ E' := h.left.toFunctor
      g.obj e.1 = e'.1) :
    IsIso h ↔
      e.2 ▸ (Functor.mapVertexGroup p e.1).range =
        e'.2 ▸ (Functor.mapVertexGroup p' e'.1).range := by
  rcases e with ⟨e, rfl⟩
  constructor
  · intro hIso
    letI := hIso
    letI : Nonempty E' := ⟨e'.1⟩
    letI : IsConnected E' := { toIsPreconnected := inferInstance }
    let hF : E ⥤ E' := h.left.toFunctor
    let gF : E' ⥤ E := (CategoryTheory.inv h).left.toFunctor
    have hhF : hF.obj e = e'.1 := by
      simpa [hF] using hh
    -- The inverse over-morphism sends the chosen target point back to the chosen source point.
    have hgF : gF.obj e'.1 = e := by
      have hcomp : h ≫ CategoryTheory.inv h = 𝟙 _ := by
        simp
      have hpoint : gF.obj (hF.obj e) = e := by
        exact congrArg
          (fun k : Over.mk p.toCatHom ⟶ Over.mk p.toCatHom ↦
            k.left.toFunctor.obj e) hcomp
      simpa [hF, gF, hhF] using hpoint
    -- Apply the lifting criterion to `h`.
    have hhOver : hF ⋙ p' = p := by
      simpa [hF] using congrArg (fun F ↦ F.toFunctor) (Over.w h)
    have hle :
        (Functor.mapVertexGroup p e).range ≤
          e'.2 ▸ (Functor.mapVertexGroup p' e'.1).range :=
      Functor.mapVertexGroup_range_le_of_lift
        (p := p') (f := p) (g := hF) e e' hhOver hhF
    -- Apply the same criterion to the inverse morphism.
    have hgOver : gF ⋙ p = p' := by
      simpa [gF] using congrArg (fun F ↦ F.toFunctor) (Over.w (CategoryTheory.inv h))
    have hle'₀ :
        (Functor.mapVertexGroup p' e'.1).range ≤
          e'.2.symm ▸ (Functor.mapVertexGroup p e).range :=
      Functor.mapVertexGroup_range_le_of_lift
        (p := p) (f := p') (g := gF) e'.1 ⟨e, e'.2.symm⟩ hgOver hgF
    have hle' :
        e'.2 ▸ (Functor.mapVertexGroup p' e'.1).range ≤
          (Functor.mapVertexGroup p e).range := by
      intro γ hγ
      have hγ' :
          eqToHom e'.2 ≫ γ ≫ eqToHom e'.2.symm ∈
            (Functor.mapVertexGroup p' e'.1).range := by
        exact (mapVertexGroup_range_transport_iff e'.2 γ).1 hγ
      have hγ'' :
          eqToHom e'.2 ≫ γ ≫ eqToHom e'.2.symm ∈
            e'.2.symm ▸ (Functor.mapVertexGroup p e).range :=
        hle'₀ hγ'
      have hγ''' :
          eqToHom e'.2.symm ≫
              (eqToHom e'.2 ≫ γ ≫ eqToHom e'.2.symm) ≫
              eqToHom e'.2 ∈
            (Functor.mapVertexGroup p e).range := by
        exact
          (mapVertexGroup_range_transport_iff e'.2.symm
            (eqToHom e'.2 ≫ γ ≫ eqToHom e'.2.symm)).1 hγ''
      simpa [Category.assoc] using hγ'''
    exact le_antisymm hle hle'
  · intro hEq
    letI : Nonempty E' := ⟨e'.1⟩
    letI : IsConnected E' := { toIsPreconnected := inferInstance }
    obtain ⟨g, hg, _huniqg⟩ :=
      (existsUnique_map_iff_mapVertexGroup_range_le
        (p := p') (p' := p) hp (p.obj e) e' ⟨e, rfl⟩).2 hEq.symm.le
    let hF : E ⥤ E' := h.left.toFunctor
    let gF : E' ⥤ E := g.left.toFunctor
    have hhF : hF.obj e = e'.1 := by
      simpa [hF] using hh
    have hgF : gF.obj e'.1 = e := by
      simpa [gF] using hg
    -- The source-side composite fixes the chosen source point, so uniqueness forces identity.
    let hgFcomp : E ⥤ E := (h ≫ g).left.toFunctor
    have hhg : hgFcomp.obj e = e := by
      change gF.obj (hF.obj e) = e
      simpa [hhF] using hgF
    obtain ⟨_, _, huniqk⟩ :=
      (existsUnique_map_iff_mapVertexGroup_range_le
        (p := p) (p' := p) hp (p.obj e) ⟨e, rfl⟩ ⟨e, rfl⟩).2 le_rfl
    have h_comp_g : h ≫ g = 𝟙 _ :=
      (huniqk (h ≫ g) (by simpa [hgFcomp] using hhg)).trans (huniqk (𝟙 _) rfl).symm
    -- The target-side composite fixes the chosen target point, so uniqueness gives the other identity.
    let ghFcomp : E' ⥤ E' := (g ≫ h).left.toFunctor
    have hgh : ghFcomp.obj e'.1 = e'.1 := by
      change hF.obj (gF.obj e'.1) = e'.1
      simpa [hgF] using hhF
    obtain ⟨_, _, huniqk'⟩ :=
      (existsUnique_map_iff_mapVertexGroup_range_le
        (p := p') (p' := p') hp' (p.obj e) e' e').2 le_rfl
    have g_comp_h : g ≫ h = 𝟙 _ :=
      (huniqk' (g ≫ h) (by simpa [ghFcomp] using hgh)).trans (huniqk' (𝟙 _) rfl).symm
    exact ⟨⟨g, h_comp_g, g_comp_h⟩⟩

end CategoryTheory.Functor.IsCovering

/-! ### Corollary_3_5_7 (from Chap03) -/
universe u v

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {E E' B : Type u} [Groupoid.{v} E] [Groupoid.{v} E'] [Groupoid.{v} B]
variable {p : E ⥤ B} {p' : E' ⥤ B} {e : E}
variable [IsConnected E]

/-- Corollary 3.5.7 (1): a connected universal covering functor over the base object `p.obj e`
maps uniquely to every covering functor over `B` once a point of the target fiber over `p.obj e`
is chosen. -/
-- Proof sketch: apply `existsUnique_map_iff_mapVertexGroup_range_le` with
-- `(Functor.mapVertexGroup p e).range = ⊥`; the needed subgroup inclusion is `⊥ ≤ H` for any
-- target subgroup `H`.
theorem universalCovering_existsUnique_map_to_covering
    (hp : Functor.IsUniversalCovering p e) (hp' : Functor.IsCovering p')
    (e' : p'.Fiber (p.obj e)) :
    ∃! h : Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom,
      let g : E ⥤ E' := h.left.toFunctor
      g.obj e = e'.1 := by
  simpa using
    (existsUnique_map_iff_mapVertexGroup_range_le
      hp' (p.obj e) ⟨e, rfl⟩ e').2 <|
      by
        rw [hp.mapVertexGroup_range_eq_bot]
        exact bot_le

/- Corollary 3.5.7 (2): if the target covering is also universal at the chosen fiber point, then
every point-preserving map of coverings over `B` is an isomorphism of coverings, provided the
target total groupoid is preconnected. -/
-- Proof sketch: if `p'` is also universal at `e'.1`, then both image subgroups in
-- `isIso_map_iff_mapVertexGroup_range_eq` are trivial, so the subgroup equality criterion
-- implies that any point-preserving map of coverings is an isomorphism.
theorem universalCovering_map_isIso_of_target_isUniversal
    [IsPreconnected E']
    (hp : Functor.IsUniversalCovering p e)
    (e' : p'.Fiber (p.obj e)) (hp'univ : Functor.IsUniversalCovering p' e'.1)
    (h : Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom)
    (hh : let g : E ⥤ E' := h.left.toFunctor
      g.obj e = e'.1) :
    IsIso h := by
  letI : Nonempty E' := ⟨e'.1⟩
  letI : IsConnected E' := { toIsPreconnected := inferInstance }
  obtain ⟨g, hg, _huniqg⟩ :=
    universalCovering_existsUnique_map_to_covering
      hp'univ hp.isCovering ⟨e, e'.2.symm⟩
  let hF : E ⥤ E' := h.left.toFunctor
  let gF : E' ⥤ E := g.left.toFunctor
  have hhF : hF.obj e = e'.1 := by
    simpa [hF] using hh
  have hgF : gF.obj e'.1 = e := by
    simpa [gF] using hg
  let hgFcomp : E ⥤ E := (h ≫ g).left.toFunctor
  have hhg : hgFcomp.obj e = e := by
    change gF.obj (hF.obj e) = e
    simpa [hhF] using hgF
  let ghFcomp : E' ⥤ E' := (g ≫ h).left.toFunctor
  have hgh : ghFcomp.obj e'.1 = e'.1 := by
    change hF.obj (gF.obj e'.1) = e'.1
    simpa [hgF] using hhF
  obtain ⟨_, _, huniqk⟩ :=
    universalCovering_existsUnique_map_to_covering hp hp.isCovering ⟨e, rfl⟩
  have h_comp_g : h ≫ g = 𝟙 _ :=
    (huniqk (h ≫ g) (by simpa [hgFcomp] using hhg)).trans (huniqk (𝟙 _) rfl).symm
  obtain ⟨_, _, huniqk'⟩ :=
    universalCovering_existsUnique_map_to_covering hp'univ hp'univ.isCovering ⟨e'.1, rfl⟩
  have g_comp_h : g ≫ h = 𝟙 _ :=
    (huniqk' (g ≫ h) (by simpa [ghFcomp] using hgh)).trans (huniqk' (𝟙 _) rfl).symm
  exact ⟨⟨g, h_comp_g, g_comp_h⟩⟩

end CategoryTheory.Functor.IsCovering

/-! ### Theorem_3_5_8 (from Chap03) -/
universe u v

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {E E' B : Type u} [Groupoid.{v} E] [Groupoid.{v} E'] [Groupoid.{v} B]
variable {p : E ⥤ B} {p' : E' ⥤ B}

/-- A morphism of coverings over `B` sends the fiber of `p` over `b` into the fiber of `p'`
over `b`. -/
-- Proof sketch: evaluate the commutative triangle relation `Over.w h` at the chosen point of the
-- fiber and rewrite the result using the defining equality of that fiber point.
theorem mapOfCoverings_obj_mem_fiber {b : B}
    (h : Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom) (e : p.Fiber b) :
    let g : E ⥤ E' := h.left.toFunctor
    p'.obj (g.obj e.1) = b := by
  let g : E ⥤ E' := h.left.toFunctor
  have hgOver : g ⋙ p' = p := by
    -- Unpack the over-category commutativity relation into an equality of functors.
    simpa [g] using congrArg (fun F ↦ F.toFunctor) (Over.w h)
  have hObj : p'.obj (g.obj e.1) = p.obj e.1 := by
    -- Evaluating that functor equality at `e.1` identifies the two base objects.
    simpa [g] using congrArg (fun F : E ⥤ B ↦ F.obj e.1) hgOver
  exact hObj.trans e.2

/-- Restriction of a map of coverings over `B` to the fiber over `b`. -/
def mapOfCoveringsToFiberFun (b : B)
    (h : Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom) :
    p.Fiber b → p'.Fiber b :=
  let g : E ⥤ E' := h.left.toFunctor
  fun e ↦ ⟨g.obj e.1, mapOfCoverings_obj_mem_fiber h e⟩

/-- Restriction of a map of coverings to the fiber over `b` commutes with fiber translation by
loops at `b`. -/
-- Proof sketch: a map of coverings sends the chosen lift of a loop starting at `e` to the chosen
-- lift of the same loop starting at the image point, because both arrows project to the same base
-- loop and have the same source. Comparing endpoints gives the equivariance identity.
theorem mapOfCoveringsToFiberFun_comm
    (hp : Functor.IsCovering p) (hp' : Functor.IsCovering p') (b : B)
    (h : Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom) (γ : b ⟶ b)
    (e : p.Fiber b) :
    letI := fiberTranslationMulAction hp b
    letI := fiberTranslationMulAction hp' b
    mapOfCoveringsToFiberFun b h (γ • e) = γ • mapOfCoveringsToFiberFun b h e := by
  rcases e with ⟨e, rfl⟩
  let g : E ⥤ E' := h.left.toFunctor
  have hgOver : g ⋙ p' = p := by
    -- Convert the over-category triangle into an equality of total-space functors.
    simpa [g] using congrArg (fun F ↦ F.toFunctor) (Over.w h)
  have hbase : p'.obj (g.obj e) = p.obj e := by
    -- The image of the chosen source point still lies over the same base object.
    simpa [g] using congrArg (fun F : E ⥤ B ↦ F.obj e) hgOver
  let x : p'.Fiber (p.obj e) := ⟨g.obj e, hbase⟩
  have hx : mapOfCoveringsToFiberFun (p.obj e) h ⟨e, rfl⟩ = x := by
    -- The restricted map is the obvious image point in the target fiber.
    apply Subtype.ext
    rfl
  -- Rewrite both actions in terms of fiber translation along `γ⁻¹`.
  change mapOfCoveringsToFiberFun (p.obj e) h (fiberTranslationMap hp γ⁻¹ ⟨e, rfl⟩) =
    fiberTranslationMap hp' γ⁻¹ (mapOfCoveringsToFiberFun (p.obj e) h ⟨e, rfl⟩)
  rw [hx]
  apply Subtype.ext
  let u : Under e := starLift hp γ⁻¹ ⟨e, rfl⟩
  let v : Under (g.obj e) := starLift hp' γ⁻¹ x
  have hright : p'.obj (g.obj u.right) = p.obj u.right := by
    -- The commuting triangle also identifies the basepoint of the lifted endpoint.
    simpa [g, u] using congrArg (fun F : E ⥤ B ↦ F.obj u.right) hgOver
  have hu : p.map u.hom = γ⁻¹ ≫ eqToHom (starLift_obj hp γ⁻¹ ⟨e, rfl⟩).symm := by
    -- Normalize the chosen lift of `γ⁻¹` in the source covering.
    simpa [u] using starLift_hom_over hp γ⁻¹ ⟨e, rfl⟩
  have hmor : (g ⋙ p').map u.hom = eqToHom hbase ≫ p.map u.hom ≫ eqToHom hright.symm := by
    -- Mapping the chosen lift through `g` changes only the source and target transports.
    simpa [u] using CategoryTheory.Functor.congr_hom hgOver u.hom
  have hpostv : (Under.post p').obj v = Under.mk (eqToHom hbase ≫ γ⁻¹) := by
    -- The target chosen lift is characterized by the transported loop `γ⁻¹`.
    rw [show (Under.post p').obj v = x.2.symm ▸ (Under.mk γ⁻¹ : Under (p.obj e)) by
      simpa [v, x] using starLift_post_eq hp' γ⁻¹ x]
    simpa [x] using fiber_transport_under_mk (p := p') γ⁻¹ x
  have hpostu : (Under.post p').obj ((Under.post g).obj u) = Under.mk (eqToHom hbase ≫ γ⁻¹) := by
    -- The image under `g` of the source chosen lift projects to the same transported loop.
    change Under.mk (p'.map (g.map u.hom)) = Under.mk (eqToHom hbase ≫ γ⁻¹)
    rw [show p'.map (g.map u.hom) = (g ⋙ p').map u.hom by rfl]
    rw [hmor]
    have hmiddle :
        eqToHom hbase ≫ p.map u.hom ≫ eqToHom hright.symm =
          eqToHom hbase ≫
            (γ⁻¹ ≫ eqToHom (starLift_obj hp γ⁻¹ ⟨e, rfl⟩).symm) ≫
            eqToHom hright.symm := by
      exact congrArg (fun k ↦ eqToHom hbase ≫ k ≫ eqToHom hright.symm) hu
    calc
      Under.mk (eqToHom hbase ≫ p.map u.hom ≫ eqToHom hright.symm) =
          Under.mk
            (eqToHom hbase ≫
              (γ⁻¹ ≫ eqToHom (starLift_obj hp γ⁻¹ ⟨e, rfl⟩).symm) ≫
              eqToHom hright.symm) := by
            exact congrArg Under.mk hmiddle
      _ = Under.mk
            (eqToHom hbase ≫ γ⁻¹ ≫
              eqToHom ((starLift_obj hp γ⁻¹ ⟨e, rfl⟩).symm.trans hright.symm)) := by
            simp [Category.assoc, eqToHom_trans]
      _ = Under.mk (eqToHom hbase ≫ γ⁻¹) := by
            simpa [Category.assoc] using
              under_mk_comp_eqToHom
                (eqToHom hbase ≫ γ⁻¹)
                ((starLift_obj hp γ⁻¹ ⟨e, rfl⟩).symm.trans hright.symm)
  have hstar : v = (Under.post g).obj u := by
    -- Uniqueness of lifts in the target covering identifies the two candidate lifts of `γ⁻¹`.
    apply (hp'.star_bijective (g.obj e)).injective
    exact hpostv.trans hpostu.symm
  change g.obj u.right = v.right
  -- Reading off endpoints gives the desired equality on fibers.
  simpa [mapOfCoveringsToFiberFun, u, v, x] using congrArg Comma.right hstar.symm

/-- Restriction to the fiber over `b` as a bundled equivariant map. -/
def mapOfCoveringsToFiber (hp : Functor.IsCovering p) (hp' : Functor.IsCovering p')
    (b : B) (h : Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom) :
    letI := fiberTranslationMulAction hp b
    letI := fiberTranslationMulAction hp' b
    p.Fiber b →[(b ⟶ b)] p'.Fiber b :=
  letI := fiberTranslationMulAction hp b
  letI := fiberTranslationMulAction hp' b
  { toFun := mapOfCoveringsToFiberFun b h
    map_smul' := mapOfCoveringsToFiberFun_comm hp hp' b h }

/-- Helper for Theorem 3.5.8: the subgroup attached to a fiber point is its stabilizer under the
fiber-translation action. -/
lemma fiberPoint_stabilizer_eq_mapVertexGroup_range
    (hp : Functor.IsCovering p) {b : B} (e : p.Fiber b) :
    letI : MulAction (b ⟶ b) (p.Fiber b) := fiberTranslationMulAction hp b
    MulAction.stabilizer (b ⟶ b) e = e.2 ▸ (Functor.mapVertexGroup p e.1).range := by
  rcases e with ⟨e, rfl⟩
  -- Reduce to the distinguished basepoint case computed in Lemma 3.4.11.
  simpa [fiberTranslationMulAction] using
    (fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e)

/-- Helper for Theorem 3.5.8: an equivariant map sends stabilizers into stabilizers. -/
lemma stabilizer_le_of_equivariant
    {G : Type v} {X Y : Type u} [Group G] [MulAction G X] [MulAction G Y]
    (φ : X →[G] Y) (x : X) :
    MulAction.stabilizer G x ≤ MulAction.stabilizer G (φ x) := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  -- Push the fixed-point relation forward using equivariance of `φ`.
  calc
    g • φ x = φ (g • x) := by
      simpa using (φ.map_smul' g x).symm
    _ = φ x := by rw [hg]

/-- Theorem 3.5.8: if `E` is connected, restriction to the fiber over `b` gives a bijection
between maps of coverings `E ⥤ E'` over `B` and `(b ⟶ b)`-equivariant maps
`p.Fiber b → p'.Fiber b`, where `b ⟶ b = π(B,b)`. -/
-- Proof sketch: a map of coverings commutes with fiber translation, so restriction gives an
-- equivariant map on the fiber. For surjectivity, connectedness of `E` makes the
-- `(b ⟶ b)`-action on `p.Fiber b` pretransitive. An equivariant fiber map sends the isotropy
-- subgroup of any chosen `e : p.Fiber b` into the isotropy subgroup of its image, so
-- `fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range` and
-- `existsUnique_map_iff_mapVertexGroup_range_le` produce a unique map of coverings with the
-- prescribed value at `e`; pretransitivity then upgrades agreement at `e` to agreement on the
-- whole fiber.
theorem mapOfCoveringsToFiber_bijective [CategoryTheory.IsConnected E]
    (hp : Functor.IsCovering p) (hp' : Functor.IsCovering p') (b : B) :
    letI := fiberTranslationMulAction hp b
    letI := fiberTranslationMulAction hp' b
    Function.Bijective (mapOfCoveringsToFiber hp hp' b) := by
  letI := fiberTranslationMulAction hp b
  letI := fiberTranslationMulAction hp' b
  constructor
  · intro h₁ h₂ hEq
    obtain ⟨e, rfl⟩ := hp.obj_surjective b
    let x : p.Fiber (p.obj e) := ⟨e, rfl⟩
    let x' : p'.Fiber (p.obj e) := mapOfCoveringsToFiber hp hp' (p.obj e) h₁ x
    have hxEq : mapOfCoveringsToFiber hp hp' (p.obj e) h₂ x = x' := by
      -- Equality of restricted equivariant maps gives equality on the chosen fiber point.
      simpa [x'] using congrArg (fun ψ ↦ ψ x) hEq.symm
    let g₁ : E ⥤ E' := h₁.left.toFunctor
    have hg₁ : g₁ ⋙ p' = p := by
      -- Reinterpret the first covering morphism as a lift of `p` through `p'`.
      simpa [g₁] using congrArg (fun F ↦ F.toFunctor) (Over.w h₁)
    have hh₁ : g₁.obj x.1 = x'.1 := by
      -- By definition, `x'` is the image of `x` under the restricted fiber map.
      rfl
    have hle : (Functor.mapVertexGroup p x.1).range ≤
        x'.2 ▸ (Functor.mapVertexGroup p' x'.1).range := by
      -- The first covering morphism supplies the subgroup inclusion from Theorem 3.5.6.
      simpa using Functor.mapVertexGroup_range_le_of_lift x.1 x' hg₁ hh₁
    obtain ⟨_, _, huniq⟩ :=
      (existsUnique_map_iff_mapVertexGroup_range_le
        (p := p) (p' := p') hp' (p.obj e) x x').2 hle
    have hh₂ : let g₂ : E ⥤ E' := h₂.left.toFunctor; g₂.obj x.1 = x'.1 := by
      -- The second covering morphism sends `x` to the same target point because the restrictions
      -- agree on `x`.
      simpa [x', mapOfCoveringsToFiber, mapOfCoveringsToFiberFun] using congrArg Subtype.val hxEq
    exact (huniq h₁ (by simpa [g₁] using hh₁)).trans (huniq h₂ hh₂).symm
  · intro φ
    obtain ⟨e, rfl⟩ := hp.obj_surjective b
    let x : p.Fiber (p.obj e) := ⟨e, rfl⟩
    let x' : p'.Fiber (p.obj e) := φ x
    have hsub : (Functor.mapVertexGroup p x.1).range ≤
        x'.2 ▸ (Functor.mapVertexGroup p' x'.1).range := by
      have hstab : MulAction.stabilizer (p.obj e ⟶ p.obj e) x ≤
          MulAction.stabilizer (p.obj e ⟶ p.obj e) x' := by
        simpa [x'] using (stabilizer_le_of_equivariant φ x)
      -- Translate the isotropy inclusion into the subgroup inclusion required by Theorem 3.5.6.
      simpa [x', fiberPoint_stabilizer_eq_mapVertexGroup_range hp x,
        fiberPoint_stabilizer_eq_mapVertexGroup_range hp' x'] using hstab
    obtain ⟨hcov, hhcov, _⟩ :=
      (existsUnique_map_iff_mapVertexGroup_range_le
        (p := p) (p' := p') hp' (p.obj e) x x').2 hsub
    refine ⟨hcov, ?_⟩
    apply MulActionHom.ext
    intro y
    have hhx : mapOfCoveringsToFiber hp hp' (p.obj e) hcov x = x' := by
      -- The reconstructed covering morphism has the prescribed value on the chosen base fiber
      -- point.
      apply Subtype.ext
      simpa [mapOfCoveringsToFiber, mapOfCoveringsToFiberFun] using hhcov
    letI : MulAction.IsPretransitive (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
      fiberTranslationMulAction_isTransitive hp (p.obj e) |>.2
    have hy : y ∈ MulAction.orbit (p.obj e ⟶ p.obj e) x := by
      -- Connectedness makes every fiber point a translate of the chosen basepoint `x`.
      simpa [MulAction.orbit_eq_univ (p.obj e ⟶ p.obj e) x]
    rcases hy with ⟨γ, rfl⟩
    calc
      mapOfCoveringsToFiber hp hp' (p.obj e) hcov (γ • x) =
          γ • mapOfCoveringsToFiber hp hp' (p.obj e) hcov x := by
        -- The restricted map of coverings is equivariant for the fiber action.
        simpa using (mapOfCoveringsToFiber hp hp' (p.obj e) hcov).map_smul' γ x
      _ = γ • x' := by rw [hhx]
      _ = γ • φ x := by rfl
      _ = φ (γ • x) := by
        -- Equivariance of `φ` propagates equality from the chosen basepoint to all of the fiber.
        symm
        exact φ.map_smul' γ x

end CategoryTheory.Functor.IsCovering

/-! ### Definition_3_5_9 (from Chap03) -/
open CategoryTheory

universe u v

variable {E B : Type u} [Groupoid.{v} E] [Groupoid.{v} B] (p : E ⥤ B)

/- Definition 3.5.9: for a cover of the base groupoid `B` represented by a functor `p : E ⥤ B`,
its automorphism group is the categorical automorphism group of the corresponding object
`Over.mk p.toCatHom` in the over-category `Over (Cat.of B)`. Equivalently, its elements are
invertible maps of coverings from `p` to itself. -/
#check (Aut (Over.mk p.toCatHom))

/-! ### Corollary_3_5_10 (from Chap03) -/
universe u v u₁ u₂

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory
open scoped QuotientGroup

namespace CategoryTheory.Functor.IsCovering

variable {E B : Type u} [Groupoid.{v} E] [Groupoid.{v} B]
variable {p : E ⥤ B}

noncomputable section

/-- Helper for Corollary 3.5.10: restricting the identity over-morphism of `p` to a fiber gives
the identity map. -/
theorem mapOfCoveringsToFiberFun_id (b : B) :
    mapOfCoveringsToFiberFun (p := p) b (𝟙 (Over.mk p.toCatHom)) = id := by
  funext x
  -- The identity over-morphism acts trivially on the chosen fiber point.
  apply Subtype.ext
  rfl

/-- Helper for Corollary 3.5.10: restricting a composite over-morphism to a fiber composes the
restricted fiber maps in the same order. -/
theorem mapOfCoveringsToFiberFun_comp (b : B)
    (h₁ h₂ : Over.mk p.toCatHom ⟶ Over.mk p.toCatHom) :
    mapOfCoveringsToFiberFun (p := p) b (h₁ ≫ h₂) =
      mapOfCoveringsToFiberFun (p := p) b h₂ ∘ mapOfCoveringsToFiberFun (p := p) b h₁ := by
  funext x
  -- Composition in the over-category composes the underlying functors on fiber points.
  apply Subtype.ext
  rfl

/-- The induced map on the fiber over `p.obj e` coming from a covering automorphism is bijective. -/
-- Proof sketch: the inverse automorphism of `α` induces the inverse fiber map, and the two
-- composites are identities because `α.hom ≫ α.inv = 𝟙 _` and `α.inv ≫ α.hom = 𝟙 _`.
theorem coveringAutFiberMap_bijective (hp : Functor.IsCovering p) (e : E)
    (α : Aut (Over.mk p.toCatHom)) :
    Function.Bijective
      (mapOfCoveringsToFiberFun (p.obj e) α.hom) := by
  let f := mapOfCoveringsToFiberFun (p := p) (p.obj e) α.hom
  let g := mapOfCoveringsToFiberFun (p := p) (p.obj e) α.inv
  have hleft : Function.LeftInverse g f := by
    intro x
    have hcomp : g ∘ f = id := by
      -- Restricting `α.hom ≫ α.inv = 𝟙` to the fiber gives a left inverse.
      calc
        g ∘ f = mapOfCoveringsToFiberFun (p := p) (p.obj e) (α.hom ≫ α.inv) := by
          symm
          exact mapOfCoveringsToFiberFun_comp (p := p) (p.obj e) α.hom α.inv
        _ = id := by
          simpa [mapOfCoveringsToFiberFun_id (p := p)] using
            congrArg (mapOfCoveringsToFiberFun (p := p) (p.obj e)) α.hom_inv_id
    simpa [f, g] using congrFun hcomp x
  have hright : Function.RightInverse g f := by
    intro x
    have hcomp : f ∘ g = id := by
      -- Restricting `α.inv ≫ α.hom = 𝟙` to the fiber gives a right inverse.
      calc
        f ∘ g = mapOfCoveringsToFiberFun (p := p) (p.obj e) (α.inv ≫ α.hom) := by
          symm
          exact mapOfCoveringsToFiberFun_comp (p := p) (p.obj e) α.inv α.hom
        _ = id := by
          simpa [mapOfCoveringsToFiberFun_id (p := p)] using
            congrArg (mapOfCoveringsToFiberFun (p := p) (p.obj e)) α.inv_hom_id
    simpa [f, g] using congrFun hcomp x
  exact ⟨hleft.injective, hright.surjective⟩

/-- The permutation of the fiber over `p.obj e` induced by a covering automorphism. -/
noncomputable def coveringAutFiberPerm (hp : Functor.IsCovering p) (e : E)
    (α : Aut (Over.mk p.toCatHom)) : Equiv.Perm (p.Fiber (p.obj e)) :=
  Equiv.ofBijective
    (mapOfCoveringsToFiberFun (p.obj e) α.hom)
    (coveringAutFiberMap_bijective hp e α)

/-- The permutation induced on the fiber by a covering automorphism is equivariant for the
fiber-translation `π(B, p.obj e)`-action. -/
-- Proof sketch: `mapOfCoveringsToFiberFun_comm` gives the required commutation relation with the
-- canonical fiber-translation action, and this is exactly membership in the centralizer subgroup
-- `gSetAut`.
theorem coveringAutFiberPerm_mem_gSetAut (hp : Functor.IsCovering p) (e : E)
    (α : Aut (Over.mk p.toCatHom)) :
    letI := fiberTranslationMulAction hp (p.obj e)
    coveringAutFiberPerm hp e α ∈ gSetAut (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) := by
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  change coveringAutFiberPerm hp e α ∈
    Subgroup.centralizer
      (((MulAction.toPermHom (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e))).range :
        Set (Equiv.Perm (p.Fiber (p.obj e)))))
  rw [Subgroup.mem_centralizer_iff]
  intro τ hτ
  rcases hτ with ⟨γ, rfl⟩
  ext x
  -- Evaluating the centralizer condition pointwise is exactly the equivariance relation from
  -- Theorem 3.5.8.
  simpa [coveringAutFiberPerm] using
    (mapOfCoveringsToFiberFun_comm hp hp (p.obj e) α.hom γ x).symm

/-- The permutation induced by the identity covering automorphism is the identity on the fiber. -/
-- Proof sketch: unfold `coveringAutFiberPerm` and use that the identity morphism of
-- `Over.mk p.toCatHom` restricts to the identity map on every fiber.
theorem coveringAutFiberPerm_one (hp : Functor.IsCovering p) (e : E) :
    coveringAutFiberPerm hp e (1 : Aut (Over.mk p.toCatHom)) = 1 := by
  ext x
  -- The identity over-morphism restricts to the identity on the fiber.
  change mapOfCoveringsToFiberFun (p := p) (p.obj e) (𝟙 (Over.mk p.toCatHom)) x = x
  simpa [mapOfCoveringsToFiberFun_id (p := p)]

/-- The permutation induced on the fiber is multiplicative in the covering automorphism. -/
-- Proof sketch: restriction to the fiber respects composition of maps of coverings, so the
-- permutation attached to `α * β` is the composite of the permutations attached to `α` and `β`.
theorem coveringAutFiberPerm_mul (hp : Functor.IsCovering p) (e : E)
    (α β : Aut (Over.mk p.toCatHom)) :
    coveringAutFiberPerm hp e (α * β) =
      coveringAutFiberPerm hp e α * coveringAutFiberPerm hp e β := by
  ext x
  -- Restriction to the fiber respects composition of covering automorphisms.
  change mapOfCoveringsToFiberFun (p := p) (p.obj e) ((α * β).hom) x =
    mapOfCoveringsToFiberFun (p := p) (p.obj e) α.hom
      (mapOfCoveringsToFiberFun (p := p) (p.obj e) β.hom x)
  rw [show (α * β).hom = β.hom ≫ α.hom by rfl]
  simpa [Function.comp] using
    congrFun (mapOfCoveringsToFiberFun_comp (p := p) (p.obj e) β.hom α.hom) x

/-- The canonical homomorphism from covering automorphisms to automorphisms of the fiber as a
`π(B, p.obj e)`-set. -/
noncomputable def coveringAutToFiberAutHom (hp : Functor.IsCovering p) (e : E) :
    letI := fiberTranslationMulAction hp (p.obj e)
    Aut (Over.mk p.toCatHom) →* Aut_ (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  ((autMulEquivGSetAut (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e))).symm.toMonoidHom).comp
    { toFun := fun α ↦ ⟨coveringAutFiberPerm hp e α, coveringAutFiberPerm_mem_gSetAut hp e α⟩
      map_one' := Subtype.ext (coveringAutFiberPerm_one hp e)
      map_mul' := fun α β ↦ Subtype.ext (coveringAutFiberPerm_mul hp e α β) }

/-- The canonical homomorphism from covering automorphisms to `G`-set automorphisms of the fiber
is bijective when the total groupoid is connected. -/
-- Proof sketch: Theorem 3.5.8 identifies all endomorphisms of the covering with equivariant
-- endomorphisms of the fiber. Restricting to invertible endomorphisms on both sides gives
-- bijectivity on the corresponding automorphism groups.
theorem coveringAutToFiberAutHom_bijective [IsConnected E]
    (hp : Functor.IsCovering p) (e : E) :
    Function.Bijective (coveringAutToFiberAutHom hp e) := by
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  constructor
  · intro α β hαβ
    apply Iso.ext
    apply (mapOfCoveringsToFiber_bijective hp hp (p.obj e)).1
    apply MulActionHom.ext
    intro x
    have hx :
        (coveringAutToFiberAutHom hp e α).hom.hom x =
          (coveringAutToFiberAutHom hp e β).hom.hom x := by
      simpa using
        congrArg
          (fun φ : Aut_ (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) ↦ φ.hom.hom x)
          hαβ
    -- Equality of fiber automorphisms gives equality of the restricted covering maps.
    simpa [coveringAutToFiberAutHom, coveringAutFiberPerm, mapOfCoveringsToFiber] using hx
  · intro φ
    -- Route correction: lift the inverse fiber automorphism through Theorem 3.5.8 instead of
    -- rebuilding the Weyl-group argument directly.
    have hφ_hom_smul :
        ∀ (γ : p.obj e ⟶ p.obj e) (x : p.Fiber (p.obj e)),
          φ.hom.hom (γ • x) = γ • (show p.Fiber (p.obj e) from φ.hom.hom x) := by
      intro γ x
      -- The forward automorphism of the fiber is equivariant by definition.
      simpa [Action.ofMulAction_apply] using ConcreteCategory.congr_hom (φ.hom.comm γ) x
    let φhom : p.Fiber (p.obj e) →[(p.obj e ⟶ p.obj e)] p.Fiber (p.obj e) :=
      { toFun := φ.hom.hom
        map_smul' := hφ_hom_smul }
    have hφ_inv_smul :
        ∀ (γ : p.obj e ⟶ p.obj e) (x : p.Fiber (p.obj e)),
          φ.inv.hom (γ • x) = γ • (show p.Fiber (p.obj e) from φ.inv.hom x) := by
      intro γ x
      -- The inverse automorphism is equivariant for the same fiber action.
      simpa [Action.ofMulAction_apply] using ConcreteCategory.congr_hom (φ.inv.comm γ) x
    let φinv : p.Fiber (p.obj e) →[(p.obj e ⟶ p.obj e)] p.Fiber (p.obj e) :=
      { toFun := φ.inv.hom
        map_smul' := hφ_inv_smul }
    obtain ⟨h, hh⟩ := (mapOfCoveringsToFiber_bijective hp hp (p.obj e)).2 φhom
    obtain ⟨i, hi⟩ := (mapOfCoveringsToFiber_bijective hp hp (p.obj e)).2 φinv
    have hh_apply (x : p.Fiber (p.obj e)) :
        mapOfCoveringsToFiberFun (p := p) (p.obj e) h x = φ.hom.hom x := by
      -- The lifted morphism `h` restricts to the given equivariant automorphism `φ.hom`.
      simpa [mapOfCoveringsToFiber] using
        congrArg
          (fun ψ : p.Fiber (p.obj e) →[(p.obj e ⟶ p.obj e)] p.Fiber (p.obj e) ↦ ψ x)
          hh
    have hi_apply (x : p.Fiber (p.obj e)) :
        mapOfCoveringsToFiberFun (p := p) (p.obj e) i x = φ.inv.hom x := by
      -- Likewise, `i` restricts to the inverse equivariant automorphism `φ.inv.hom`.
      simpa [mapOfCoveringsToFiber] using
        congrArg
          (fun ψ : p.Fiber (p.obj e) →[(p.obj e ⟶ p.obj e)] p.Fiber (p.obj e) ↦ ψ x)
          hi
    have hhi : h ≫ i = 𝟙 (Over.mk p.toCatHom) := by
      apply (mapOfCoveringsToFiber_bijective hp hp (p.obj e)).1
      apply MulActionHom.ext
      intro x
      -- The lifted maps compose to the identity because `φ.hom` and `φ.inv.hom` are inverse.
      have hcompose :
          mapOfCoveringsToFiberFun (p := p) (p.obj e) (h ≫ i) x =
            φ.inv.hom (φ.hom.hom x) := by
        calc
          mapOfCoveringsToFiberFun (p := p) (p.obj e) (h ≫ i) x =
              mapOfCoveringsToFiberFun (p := p) (p.obj e) i
                (mapOfCoveringsToFiberFun (p := p) (p.obj e) h x) := by
                simpa [Function.comp] using
                  congrFun (mapOfCoveringsToFiberFun_comp (p := p) (p.obj e) h i) x
          _ = φ.inv.hom (φ.hom.hom x) := by
                rw [hh_apply x, hi_apply (φ.hom.hom x)]
      have hidentity : φ.inv.hom (φ.hom.hom x) = x := by
        simp only [← comp_apply, Action.hom_inv_hom, id_apply]
      exact hcompose.trans hidentity
    have hih : i ≫ h = 𝟙 (Over.mk p.toCatHom) := by
      apply (mapOfCoveringsToFiber_bijective hp hp (p.obj e)).1
      apply MulActionHom.ext
      intro x
      -- The opposite composite is also the identity because `φ.inv.hom` and `φ.hom` are inverse.
      have hcompose :
          mapOfCoveringsToFiberFun (p := p) (p.obj e) (i ≫ h) x =
            φ.hom.hom (φ.inv.hom x) := by
        calc
          mapOfCoveringsToFiberFun (p := p) (p.obj e) (i ≫ h) x =
              mapOfCoveringsToFiberFun (p := p) (p.obj e) h
                (mapOfCoveringsToFiberFun (p := p) (p.obj e) i x) := by
                simpa [Function.comp] using
                  congrFun (mapOfCoveringsToFiberFun_comp (p := p) (p.obj e) i h) x
          _ = φ.hom.hom (φ.inv.hom x) := by
                rw [hi_apply x, hh_apply (φ.inv.hom x)]
      have hidentity : φ.hom.hom (φ.inv.hom x) = x := by
        simp only [← comp_apply, Action.inv_hom_hom, id_apply]
      exact hcompose.trans hidentity
    have hIso : IsIso h := IsIso.mk ⟨i, hhi, hih⟩
    refine ⟨asIso h, ?_⟩
    ext x
    -- The reconstructed covering automorphism acts on the fiber as the original automorphism `φ`.
    simpa [coveringAutToFiberAutHom, coveringAutFiberPerm, mapOfCoveringsToFiber,
      CategoryTheory.asIso_hom, φhom] using hh_apply x

/-- Corollary 3.5.10 (1): for a connected covering functor `p : E ⥤ B`, the automorphism group
of the covering is canonically isomorphic to the automorphism group of the fiber over `p.obj e`
as a `π(B, p.obj e)`-set. -/
noncomputable def coveringAutMulEquivFiberAut [IsConnected E]
    (hp : Functor.IsCovering p) (e : E) :
    letI := fiberTranslationMulAction hp (p.obj e)
    Aut (Over.mk p.toCatHom) ≃* Aut_ (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
  MulEquiv.ofBijective
    (coveringAutToFiberAutHom hp e)
    (coveringAutToFiberAutHom_bijective hp e)

/-- Evaluating the first clause agrees with the canonical homomorphism
`coveringAutToFiberAutHom`. -/
-- Proof sketch: unfold `coveringAutMulEquivFiberAut`; `MulEquiv.ofBijective` keeps the same
-- underlying function.
theorem coveringAutMulEquivFiberAut_apply [IsConnected E]
    (hp : Functor.IsCovering p) (e : E) (α : Aut (Over.mk p.toCatHom)) :
    coveringAutMulEquivFiberAut hp e α = coveringAutToFiberAutHom hp e α := rfl

/-- The first clause is realized by the canonical homomorphism
`coveringAutToFiberAutHom`. -/
@[simp] theorem coveringAutMulEquivFiberAut_toMonoidHom [IsConnected E]
    (hp : Functor.IsCovering p) (e : E) :
    (coveringAutMulEquivFiberAut hp e).toMonoidHom = coveringAutToFiberAutHom hp e := rfl

/-- The automorphism group of the fiber-translation action is canonically identified with the Weyl
group of the image subgroup `p(π(E, e)) ≤ π(B, p.obj e)`. -/
noncomputable def fiberAutMulEquivWeylGroupMapVertexGroupRange [IsConnected E]
    (hp : Functor.IsCovering p) (e : E) :
    letI := fiberTranslationMulAction hp (p.obj e)
    Aut_ (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) ≃*
      Subgroup.weylGroup ((Functor.mapVertexGroup p e).range) :=
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  letI : MulAction.IsPretransitive (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction_isPretransitive hp (p.obj e)
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  let eW :
      Subgroup.weylGroup (MulAction.stabilizer (p.obj e ⟶ p.obj e) x₀) ≃*
        Aut_ (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    weylGroup_stabilizer_mulEquiv_aut x₀
  show Aut_ (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) ≃*
      Subgroup.weylGroup ((Functor.mapVertexGroup p e).range) from
    (eW.symm).trans
      (MulEquiv.cast (fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e))

/-- Corollary 3.5.10 (2): for a connected covering functor, the automorphism group of the
covering is canonically isomorphic to the Weyl group of the image subgroup
`p(π(E, e)) ≤ π(B, p.obj e)`. -/
noncomputable def coveringAutMulEquivWeylGroupMapVertexGroupRange
    [IsConnected E] (hp : Functor.IsCovering p) (e : E) :
    Aut (Over.mk p.toCatHom) ≃* Subgroup.weylGroup ((Functor.mapVertexGroup p e).range) :=
  (coveringAutMulEquivFiberAut hp e).trans
    (fiberAutMulEquivWeylGroupMapVertexGroupRange hp e)

/-- Evaluating the second clause identifies a covering automorphism with its induced Weyl-group
class through the fiber `π(B, p.obj e)`-set. -/
-- Proof sketch: unfold `coveringAutMulEquivWeylGroupMapVertexGroupRange`; the value is the
-- composite of the fiber-action equivalence and the bundled fiber-action Weyl-group bridge.
theorem coveringAutMulEquivWeylGroupMapVertexGroupRange_apply
    [IsConnected E] (hp : Functor.IsCovering p) (e : E)
    (α : Aut (Over.mk p.toCatHom)) :
    coveringAutMulEquivWeylGroupMapVertexGroupRange hp e α =
      fiberAutMulEquivWeylGroupMapVertexGroupRange hp e
        (coveringAutMulEquivFiberAut hp e α) := rfl

/-- Corollary 3.5.10 (3): for a connected regular covering functor, the automorphism group of the
covering is canonically isomorphic to the quotient `π(B, p.obj e) / p(π(E, e))`. -/
noncomputable def regularCoveringAutMulEquivQuotientMapVertexGroupRange
    [IsConnected E] {e : E} (hp : Functor.IsRegularCovering p e) :
    letI : (Functor.mapVertexGroup p e).range.Normal := hp.normal_mapVertexGroup_range
    Aut (Over.mk p.toCatHom) ≃* ((p.obj e ⟶ p.obj e) ⧸ (Functor.mapVertexGroup p e).range) :=
  letI : (Functor.mapVertexGroup p e).range.Normal := hp.normal_mapVertexGroup_range
  (coveringAutMulEquivWeylGroupMapVertexGroupRange
    hp.isCovering e).trans
    (Subgroup.weylGroupMulEquivQuotientOfNormal ((Functor.mapVertexGroup p e).range))

/-- Evaluating the third clause factors through the Weyl-group description and then the quotient
by the normal image subgroup. -/
-- Proof sketch: unfold
-- `regularCoveringAutMulEquivQuotientMapVertexGroupRange`; its value is the application of
-- `weylGroupMulEquivQuotientOfNormal` to the Weyl-group class from the second clause.
theorem regularCoveringAutMulEquivQuotientMapVertexGroupRange_apply
    [IsConnected E] {e : E} (hp : Functor.IsRegularCovering p e)
    (α : Aut (Over.mk p.toCatHom)) :
    letI : (Functor.mapVertexGroup p e).range.Normal := hp.normal_mapVertexGroup_range
    regularCoveringAutMulEquivQuotientMapVertexGroupRange hp α =
      Subgroup.weylGroupMulEquivQuotientOfNormal ((Functor.mapVertexGroup p e).range)
        (coveringAutMulEquivWeylGroupMapVertexGroupRange
          hp.isCovering e α) := rfl

/-- Corollary 3.5.10 (4): for a connected universal covering functor, the automorphism group of
the covering is canonically isomorphic to `π(B, p.obj e)`. -/
noncomputable def universalCoveringAutMulEquivVertexGroup
    [IsConnected E] {e : E} (hp : Functor.IsUniversalCovering p e) :
    Aut (Over.mk p.toCatHom) ≃* (p.obj e ⟶ p.obj e) :=
  letI : (Functor.mapVertexGroup p e).range.Normal :=
    hp.isRegularCovering.normal_mapVertexGroup_range
  (regularCoveringAutMulEquivQuotientMapVertexGroupRange
    hp.isRegularCovering).trans
    ((QuotientGroup.quotientMulEquivOfEq
      (hp.mapVertexGroup_range_eq_bot)).trans
      QuotientGroup.quotientBot)

/-- Evaluating the fourth clause specializes the quotient description along the equality
`p(π(E, e)) = ⊥`. -/
-- Proof sketch: unfold `universalCoveringAutMulEquivVertexGroup`; its value is the regular-case
-- quotient class, followed by the quotient identifications for the trivial subgroup.
theorem universalCoveringAutMulEquivVertexGroup_apply
    [IsConnected E] {e : E} (hp : Functor.IsUniversalCovering p e)
    (α : Aut (Over.mk p.toCatHom)) :
    letI : (Functor.mapVertexGroup p e).range.Normal :=
      hp.isRegularCovering.normal_mapVertexGroup_range
    universalCoveringAutMulEquivVertexGroup hp α =
      QuotientGroup.quotientBot
        ((QuotientGroup.quotientMulEquivOfEq
          (hp.mapVertexGroup_range_eq_bot))
          (regularCoveringAutMulEquivQuotientMapVertexGroupRange
            hp.isRegularCovering α)) := rfl

end

end CategoryTheory.Functor.IsCovering
