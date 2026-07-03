import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_8_13_1 (from Chap08) -/
universe u v

namespace CategoryTheory

namespace RepresentablePresheaf

scoped notation:max "h[" U "]" => yoneda.obj U

end RepresentablePresheaf

open scoped RepresentablePresheaf

variable {C : Type u} [Category.{v} C]

section OverDescent

/-- Helper for Lemma 8.13.1: an object of the fiber of the slice projection `Over.forget U` over
`V` is canonically determined by its underlying arrow `V ⟶ U`. -/
private def over_fiber_to_hom (U V : C) :
    ((Over.forget U).Fiber V) → (V ⟶ U) :=
  fun a ↦ eqToHom a.2.symm ≫ a.1.hom

/-- Helper for Lemma 8.13.1: the fiber of `Over.forget U` over `V` is in bijection with
the hom-set `V ⟶ U`. -/
private theorem over_fiber_to_hom_bijective (U V : C) :
    Function.Bijective (over_fiber_to_hom U V) := by
  constructor
  · intro a b h
    cases a with
    | mk a ha =>
        cases b with
        | mk b hb =>
            dsimp [over_fiber_to_hom] at h ⊢
            cases a with
            | mk la ra ha' =>
                cases b with
                | mk lb rb hb' =>
                    cases ha
                    cases hb
                    cases ra
                    cases rb
                    have h' : ha' = hb' := by
                      simpa [Over.forget_obj] using h
                    subst h'
                    rfl
  · intro f
    refine ⟨⟨Over.mk f, rfl⟩, ?_⟩
    simp [over_fiber_to_hom]

/-- Helper for Lemma 8.13.1: equality of the underlying arrows to `U` identifies fiber objects in
the slice projection. -/
private theorem over_fiber_eq_of_hom_eq
    {U V : C} {a b : (Over.forget U).Fiber V}
    (h : over_fiber_to_hom U V a = over_fiber_to_hom U V b) :
    a = b :=
  (over_fiber_to_hom_bijective U V).1 h

/-- Helper for Lemma 8.13.1: the fiber object built from `f : V ⟶ U` has underlying arrow `f`
when viewed through `over_fiber_to_hom`. -/
private theorem over_fiber_to_hom_fiber_mk_over_mk
    {U V : C} (f : V ⟶ U) :
    over_fiber_to_hom U V (Functor.Fiber.mk (a := Over.mk f) rfl) = f := by
  change eqToHom rfl.symm ≫ (Over.mk f).hom = f
  simp

/-- Helper for Lemma 8.13.1: any morphism in a slice fiber preserves the underlying arrow to
the terminal object `U`. -/
private theorem over_fiber_to_hom_eq_of_hom
    {U V : C} {a b : (Over.forget U).Fiber V} (h : a ⟶ b) :
    over_fiber_to_hom U V a = over_fiber_to_hom U V b := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  rcases a with ⟨la, ra, fa⟩
  rcases b with ⟨lb, rb, fb⟩
  dsimp at ha hb
  cases ha
  cases hb
  simp [over_fiber_to_hom]
  have hw : (Functor.Fiber.fiberInclusion.map h).left ≫ fb = fa := by
    simpa using Over.w (Functor.Fiber.fiberInclusion.map h)
  have hleft : (Functor.Fiber.fiberInclusion.map h).left = 𝟙 V := by
    simpa using
      (@IsHomLift.fac' _ _ _ _ (Over.forget U) V V _ _ (𝟙 V)
        (Functor.Fiber.fiberInclusion.map h) h.2)
  rw [hleft] at hw
  simpa using (show fa = 𝟙 V ≫ fb from hw.symm)

/-- Helper for Lemma 8.13.1: every hom-set in a fiber of the slice projection `Over.forget U`
is a subsingleton. -/
private theorem over_fiber_hom_subsingleton
    {U V : C} (a b : (Over.forget U).Fiber V) :
    Subsingleton (a ⟶ b) := by
  refine ⟨fun φ ψ ↦ ?_⟩
  apply Functor.Fiber.hom_ext
  apply Over.OverMorphism.ext
  have hφ := @IsHomLift.fac' _ _ _ _ (Over.forget U) V V _ _ (𝟙 V)
    (Functor.Fiber.fiberInclusion.map φ) φ.2
  have hψ := @IsHomLift.fac' _ _ _ _ (Over.forget U) V V _ _ (𝟙 V)
    (Functor.Fiber.fiberInclusion.map ψ) ψ.2
  simpa using hφ.trans hψ.symm

/-- Helper for Lemma 8.13.1: a lift in the slice projection over `f : Y ⟶ Z` records that the
underlying map to `U` on the source is `f` followed by the underlying map on the target. -/
private theorem over_fiber_to_hom_eq_comp_of_isHomLift
    {U Y Z : C} {a : (Over.forget U).Fiber Y} {b : (Over.forget U).Fiber Z}
    {f : Y ⟶ Z} {h : a.1 ⟶ b.1} (hh : Functor.IsHomLift (Over.forget U) f h) :
    over_fiber_to_hom U Y a = f ≫ over_fiber_to_hom U Z b := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  rcases a with ⟨la, ra, fa⟩
  rcases b with ⟨lb, rb, fb⟩
  dsimp at ha hb
  cases ha
  cases hb
  have hfac : (Over.forget U).map h = f := by
    simpa using (@IsHomLift.fac' _ _ _ _ (Over.forget U) Y Z _ _ f h hh)
  have hw : h.left ≫ fb = fa := by
    simpa using Over.w h
  have hw' : fa = f ≫ fb := by
    rw [← hfac]
    simpa using hw.symm
  simpa [over_fiber_to_hom] using hw'

/-- Helper for Lemma 8.13.1: the chosen pullback object in the slice fiber over `Y` represents
precomposition of the underlying arrow to `U` by `f : Y ⟶ Z`. -/
private theorem over_pseudofunctor_map_obj_hom_eq_comp
    {U Y Z : C} (f : Y ⟶ Z) (a : (Over.forget U).Fiber Z) :
    over_fiber_to_hom U Y
        (((canonicalFiberPseudofunctor (Over.forget U)).map f.op.toLoc).toFunctor.obj a) =
      f ≫ over_fiber_to_hom U Z a := by
  let hc := canonicalPullbackChoice (Over.forget U)
  let φ := hc.map f a
  simpa using
    (over_fiber_to_hom_eq_comp_of_isHomLift
      (U := U) (a := ((hc.pullbackFunctor f).obj a)) (b := a) (f := f) (h := φ)
      ((hc.isStronglyCartesian f a).toIsHomLift))

/-- Helper for Lemma 8.13.1: for a functor between discrete categories, equivalence is exactly
bijectivity on objects. -/
private theorem isEquivalence_iff_bijective_obj_of_isDiscrete
    {A B : Type*} [Category A] [Category B] [IsDiscrete A] [IsDiscrete B]
    (G : A ⥤ B) :
    G.IsEquivalence ↔ Function.Bijective G.obj := by
  constructor
  · intro h
    let _ : G.IsEquivalence := h
    refine ⟨?_, ?_⟩
    · intro X Y hXY
      exact obj_ext_of_isDiscrete (G.preimage (eqToHom hXY))
    · intro Y
      rcases Functor.EssSurj.mem_essImage (F := G) Y with ⟨X, ⟨e⟩⟩
      exact ⟨X, obj_ext_of_isDiscrete e.hom⟩
  · intro hG
    let faithfulG : G.Faithful := ⟨fun {_ _} _ _ _ ↦ Subsingleton.elim _ _⟩
    let fullG : G.Full := ⟨fun {X Y} f ↦
      ⟨eqToHom (hG.1 (obj_ext_of_isDiscrete f)), Subsingleton.elim _ _⟩⟩
    let essSurjG : G.EssSurj := Functor.essSurj_of_surj hG.2
    exact { faithful := faithfulG, full := fullG, essSurj := essSurjG }

/-- Helper for Lemma 8.13.1: for a cover `S` of `V`, the canonical descent functor for the slice
projection `Over.forget U` is an equivalence exactly when the representable presheaf `h[U]`
satisfies the sheaf condition for the covering sieve of `S`. -/
private theorem over_cover_toDescentData_isEquivalence_iff_isSheafFor
    (J : GrothendieckTopology C) (U V : C) (S : J.Cover V) :
    ((canonicalFiberPseudofunctor (Over.forget U)).toDescentData
      (fun I : S.Arrow ↦ I.f)).IsEquivalence ↔
      Presieve.IsSheafFor (yoneda.obj U) ((S : Sieve V).arrows) := by
  let DD :=
    (canonicalFiberPseudofunctor (Over.forget U)).DescentData
      (fun I : S.Arrow ↦ I.f)
  let compat :=
    Subtype (Presieve.Arrows.Compatible (yoneda.obj U) (fun I : S.Arrow ↦ I.f))
  let compatOfDescent : DD → compat := fun D ↦
    ⟨fun I ↦ over_fiber_to_hom U I.Y (D.obj I), by
      intro I₁ I₂ Y g₁ g₂ h
      let q : Y ⟶ V := g₁ ≫ I₁.f
      have hg₁ : g₁ ≫ I₁.f = q := rfl
      have hg₂ : g₂ ≫ I₂.f = q := by
        simpa [q] using h.symm
      have hEq :
          over_fiber_to_hom U Y
              (((canonicalFiberPseudofunctor (Over.forget U)).map g₁.op.toLoc).toFunctor.obj
                (D.obj I₁)) =
            over_fiber_to_hom U Y
              (((canonicalFiberPseudofunctor (Over.forget U)).map g₂.op.toLoc).toFunctor.obj
                (D.obj I₂)) := by
        exact over_fiber_to_hom_eq_of_hom (D.hom q g₁ g₂ hg₁ hg₂)
      have hg₁' :
          (yoneda.obj U).map g₁.op (over_fiber_to_hom U I₁.Y (D.obj I₁)) =
            over_fiber_to_hom U Y
              (((canonicalFiberPseudofunctor (Over.forget U)).map g₁.op.toLoc).toFunctor.obj
                (D.obj I₁)) := by
        simpa using
          (over_pseudofunctor_map_obj_hom_eq_comp (U := U) (f := g₁) (a := D.obj I₁)).symm
      have hg₂' :
          over_fiber_to_hom U Y
              (((canonicalFiberPseudofunctor (Over.forget U)).map g₂.op.toLoc).toFunctor.obj
                (D.obj I₂)) =
            (yoneda.obj U).map g₂.op (over_fiber_to_hom U I₂.Y (D.obj I₂)) := by
        simpa using
          over_pseudofunctor_map_obj_hom_eq_comp (U := U) (f := g₂) (a := D.obj I₂)
      exact hg₁'.trans (hEq.trans hg₂')⟩
  have hHomSub :
      ∀ D₁ D₂ : DD, Subsingleton (D₁ ⟶ D₂) := by
    intro D₁ D₂
    refine ⟨fun φ ψ ↦ Pseudofunctor.DescentData.hom_ext (fun I ↦ ?_)⟩
    exact (over_fiber_hom_subsingleton (D₁.obj I) (D₂.obj I)).elim _ _
  have hCompatMap :
      ∀ {D₁ D₂ : DD} (φ : D₁ ⟶ D₂), compatOfDescent D₁ = compatOfDescent D₂ := by
    intro D₁ D₂ φ
    apply Subtype.ext
    funext I
    exact over_fiber_to_hom_eq_of_hom (φ.hom I)
  let G : DD ⥤ Discrete compat := by
    refine
      { obj := fun D ↦ Discrete.mk (compatOfDescent D)
        map := fun {D₁ D₂} φ ↦ ?_
        map_id := ?_
        map_comp := ?_ }
    exact eqToHom (congrArg Discrete.mk (hCompatMap φ))
    · intro D
      exact Subsingleton.elim _ _
    · intro D₁ D₂ D₃ φ ψ
      exact Subsingleton.elim _ _
  let descentOfCompat : compat → DD := fun s ↦
    { obj := fun I ↦ Functor.Fiber.mk (a := Over.mk (s.1 I)) rfl
      hom := fun {Y} q {I₁ I₂} f₁ f₂ hf₁ hf₂ ↦ by
        have h₁ :
            over_fiber_to_hom U Y
                (((canonicalFiberPseudofunctor (Over.forget U)).map f₁.op.toLoc).toFunctor.obj
                  (Functor.Fiber.mk (a := Over.mk (s.1 I₁)) rfl)) =
              (yoneda.obj U).map f₁.op (s.1 I₁) := by
          simpa [over_fiber_to_hom_fiber_mk_over_mk] using
            over_pseudofunctor_map_obj_hom_eq_comp
              (U := U) (f := f₁) (a := Functor.Fiber.mk (a := Over.mk (s.1 I₁)) rfl)
        have h₂ :
            (yoneda.obj U).map f₁.op (s.1 I₁) =
              (yoneda.obj U).map f₂.op (s.1 I₂) := by
          simpa [hf₁, hf₂] using s.2 I₁ I₂ _ f₁ f₂ (by rw [hf₁, hf₂])
        have h₃ :
            (yoneda.obj U).map f₂.op (s.1 I₂) =
              over_fiber_to_hom U Y
                (((canonicalFiberPseudofunctor (Over.forget U)).map f₂.op.toLoc).toFunctor.obj
                  (Functor.Fiber.mk (a := Over.mk (s.1 I₂)) rfl)) := by
          simpa [over_fiber_to_hom_fiber_mk_over_mk] using
            (over_pseudofunctor_map_obj_hom_eq_comp
              (U := U) (f := f₂) (a := Functor.Fiber.mk (a := Over.mk (s.1 I₂)) rfl)).symm
        apply eqToHom
        apply over_fiber_eq_of_hom_eq (U := U)
        exact h₁.trans (h₂.trans h₃)
      pullHom_hom := by
        intro Y' Y g q q' hq I₁ I₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
        exact (over_fiber_hom_subsingleton _ _).elim _ _
      hom_self := by
        intro Y q I g hg
        exact (over_fiber_hom_subsingleton _ _).elim _ _
      hom_comp := by
        intro Y q I₁ I₂ I₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
        exact (over_fiber_hom_subsingleton _ _).elim _ _ }
  have hInverse : ∀ s : compat, compatOfDescent (descentOfCompat s) = s := by
    intro s
    apply Subtype.ext
    funext I
    simp [compatOfDescent, descentOfCompat, over_fiber_to_hom_fiber_mk_over_mk]
  have hObjEq :
      ∀ (D : DD) (I : S.Arrow),
        D.obj I = (descentOfCompat (compatOfDescent D)).obj I := by
    intro D I
    apply over_fiber_eq_of_hom_eq (U := U)
    simp [compatOfDescent, descentOfCompat, over_fiber_to_hom_fiber_mk_over_mk]
  let H : Discrete compat ⥤ DD := by
    refine
      { obj := fun s ↦ descentOfCompat s.as
        map := fun {s t} φ ↦
          eqToHom
            (congrArg (fun x : Discrete compat ↦ descentOfCompat x.as)
              (obj_ext_of_isDiscrete φ))
        map_id := ?_
        map_comp := ?_ }
    · intro s
      exact (hHomSub _ _).elim _ _
    · intro s t u φ ψ
      exact (hHomSub _ _).elim _ _
  let E : DD ≌ Discrete compat :=
    { functor := G
      inverse := H
      unitIso := by
        refine NatIso.ofComponents (fun D ↦ ?_) ?_
        · refine Pseudofunctor.DescentData.isoMk (fun I ↦ ?_) ?_
          · exact eqToIso (hObjEq D I)
          · intro Y q I₁ I₂ f₁ f₂ hf₁ hf₂
            exact (over_fiber_hom_subsingleton _ _).elim _ _
        · intro D₁ D₂ φ
          exact (hHomSub _ _).elim _ _
      counitIso := by
        refine Discrete.natIso ?_
        intro s
        apply eqToIso
        simp [G, H, hInverse] }
  let K : ((Over.forget U).Fiber V) ⥤ Discrete compat := by
    refine
      { obj := fun a ↦
          Discrete.mk (Presieve.Arrows.toCompatible (yoneda.obj U) (fun I : S.Arrow ↦ I.f)
            (over_fiber_to_hom U V a))
        map := fun {a b} φ ↦ ?_
        map_id := ?_
        map_comp := ?_ }
    apply eqToHom
    apply congrArg Discrete.mk
    apply congrArg (Presieve.Arrows.toCompatible (yoneda.obj U) (fun I : S.Arrow ↦ I.f))
    exact over_fiber_to_hom_eq_of_hom φ
    · intro a
      exact Subsingleton.elim _ _
    · intro a b c φ ψ
      exact Subsingleton.elim _ _
  letI : IsDiscrete ((Over.forget U).Fiber V) :=
    { subsingleton := fun a b ↦ over_fiber_hom_subsingleton a b
      eq_of_hom := fun φ ↦ over_fiber_eq_of_hom_eq (over_fiber_to_hom_eq_of_hom φ) }
  have hIso :
      (((canonicalFiberPseudofunctor (Over.forget U)).toDescentData
          (fun I : S.Arrow ↦ I.f)) ⋙ G) ≅ K := by
    refine NatIso.ofComponents (fun a ↦ ?_) ?_
    · apply eqToIso
      apply congrArg Discrete.mk
      apply Subtype.ext
      funext I
      simpa [compatOfDescent] using
        over_pseudofunctor_map_obj_hom_eq_comp (U := U) (f := I.f) (a := a)
    · intro a b φ
      exact Subsingleton.elim _ _
  let Kobj' : ((Over.forget U).Fiber V) → compat := fun a ↦
    Presieve.Arrows.toCompatible (yoneda.obj U) (fun I : S.Arrow ↦ I.f) (over_fiber_to_hom U V a)
  have hDiscreteMk :
      Function.Bijective (fun s : compat ↦ (Discrete.mk s : Discrete compat)) := by
    constructor
    · intro s t hst
      cases hst
      rfl
    · intro s
      exact ⟨s.as, by cases s; rfl⟩
  have hObjBijDiscrete :
      Function.Bijective K.obj ↔ Function.Bijective Kobj' := by
    simpa [K, Kobj', Function.comp] using
      (Function.Bijective.of_comp_iff' hDiscreteMk Kobj')
  have hObjBijFiber :
      Function.Bijective Kobj' ↔
        Function.Bijective (Presieve.Arrows.toCompatible (yoneda.obj U) (fun I : S.Arrow ↦ I.f)) := by
    convert
      (Function.Bijective.of_comp_iff
        (f := Presieve.Arrows.toCompatible (yoneda.obj U) (fun I : S.Arrow ↦ I.f))
        (g := over_fiber_to_hom U V)
        (over_fiber_to_hom_bijective U V)) using 1
  have hObjBij :
      Function.Bijective K.obj ↔
        Function.Bijective (Presieve.Arrows.toCompatible (yoneda.obj U) (fun I : S.Arrow ↦ I.f)) :=
    hObjBijDiscrete.trans hObjBijFiber
  have hDiscrete :
      K.IsEquivalence ↔
        Function.Bijective (Presieve.Arrows.toCompatible (yoneda.obj U) (fun I : S.Arrow ↦ I.f)) := by
    rw [isEquivalence_iff_bijective_obj_of_isDiscrete (G := K), hObjBij]
  have hCompare :
      ((canonicalFiberPseudofunctor (Over.forget U)).toDescentData
          (fun I : S.Arrow ↦ I.f)).IsEquivalence ↔
        K.IsEquivalence := by
    constructor
    · intro hΦ
      let _ :
          ((canonicalFiberPseudofunctor (Over.forget U)).toDescentData
            (fun I : S.Arrow ↦ I.f)).IsEquivalence := hΦ
      let _ : G.IsEquivalence := E.isEquivalence_functor
      have hComp :
          ((((canonicalFiberPseudofunctor (Over.forget U)).toDescentData
              (fun I : S.Arrow ↦ I.f))) ⋙ G).IsEquivalence :=
        by infer_instance
      exact (Functor.isEquivalence_iff_of_iso hIso).1 hComp
    · intro hK
      let _ : K.IsEquivalence := hK
      have hComp :
          ((((canonicalFiberPseudofunctor (Over.forget U)).toDescentData
              (fun I : S.Arrow ↦ I.f))) ⋙ G).IsEquivalence :=
        (Functor.isEquivalence_iff_of_iso hIso).2 hK
      let _ : G.IsEquivalence := E.isEquivalence_functor
      exact Functor.isEquivalence_of_comp_right
        ((canonicalFiberPseudofunctor (Over.forget U)).toDescentData
          (fun I : S.Arrow ↦ I.f)) G
  rw [hCompare, hDiscrete]
  rw [← S.ofArrows_eq, ← Presieve.isSheafFor_iff_generate]
  exact
    (Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible
      (P := yoneda.obj U) (π := fun I : S.Arrow ↦ I.f)).symm

end OverDescent

/- Domain-style sampling for Lemma 8.13.1:
- primary domain: stacks on a site, specialized to representable presheaves and the slice
  projection `Over.forget U`.
- inspected owner-level declarations:
  `presheaf_isSheaf_iff_categoryOfElements_isStackOnSite`,
  `representableElementsOpToOver_isEquivalenceOverBase`,
  `IsStackOnSite`,
  `Over.forget`.
- best owner abstraction: the core owner is
  `IsStackOnSite J ((CategoryOfElements.π F).leftOp)` for a presheaf `F`; the slice projection
  `Over.forget U` is reached from that owner by the canonical over-base equivalence for the
  representable presheaf `h[U]`.
- primitive data: the object `U : C` and the representable presheaf `h[U]`.
- derived API: the slice-category reformulation obtained by transporting the stack condition
  across `representableElementsOpToOver_isEquivalenceOverBase U`.

Source/core/bridge triage:
- `source-facing`: `over_forget_isStackOnSite_iff_representable_isSheaf`.
- `core/canonical`: `presheaf_isSheaf_iff_categoryOfElements_isStackOnSite`.
- `bridge/view`: `representableElementsOpToOver_isEquivalenceOverBase U`. -/

-- Proof sketch: the canonical owner theorem `presheaf_isSheaf_iff_categoryOfElements_isStackOnSite`
-- identifies the sheaf condition on a presheaf with the stack condition on its category of
-- elements. For the representable presheaf `h[U]`, Example `4.38.7` gives the canonical
-- over-base equivalence between that category of elements and the slice projection `Over.forget U`,
-- so transport the stack condition across that equivalence.
/-- Lemma 8.13.1: for an object `U` of a site `(C, J)`, the localization functor
`j_U : C/U ⥤ C`, written in Lean as `Over.forget U`, is a stack over `(C, J)` if and only if the
representable presheaf `h_U`, written canonically as `h[U]`, is a sheaf. This is the canonical
chapter-facing form of the source statement. -/
theorem over_forget_isStackOnSite_iff_representable_isSheaf
    (J : GrothendieckTopology C) (U : C) :
    IsStackOnSite J (Over.forget U) ↔ Presheaf.IsSheaf J (yoneda.obj U) := by
  rw [isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence]
  constructor
  · intro h
    rw [isSheaf_iff_isSheaf_of_type]
    intro V R hR
    let S : J.Cover V := ⟨R, hR⟩
    -- Reduce the target sheaf condition for this covering sieve to the explicit descent comparison.
    exact
      (over_cover_toDescentData_isEquivalence_iff_isSheafFor
        (J := J) (U := U) (V := V) S).1 (h V S)
  · intro h V S
    have hS : Presieve.IsSheafFor (yoneda.obj U) ((S : Sieve V).arrows) := by
      -- Convert the global sheaf hypothesis into the cover-specific sheaf condition.
      exact h.isSheafFor (S : Sieve V) S.condition
    -- Apply the explicit comparison for this fixed cover.
    exact
      (over_cover_toDescentData_isEquivalence_iff_isSheafFor
        (J := J) (U := U) (V := V) S).2 hS

end CategoryTheory

/-! ### Lemma_8_13_2 (from Chap08) -/
open CategoryTheory.BasedFunctor
open scoped Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂ u v vDesc

namespace CategoryTheory

open Bicategory
open scoped RepresentablePresheaf

variable {C : Type u} [Category.{v} C]

private abbrev toFibredCategoryMor
    {J : GrothendieckTopology C} {X Y : StackOver J} (F : X ⟶ Y) :=
  InducedCategory.Hom.toFibredCategoryMor F

private abbrev toBasedFunctor
    {J : GrothendieckTopology C} {X Y : StackOver J} (F : X ⟶ Y) :=
  InducedCategory.Hom.toBasedFunctor F

private abbrev stackTwoHomToFibredCategoryMorTwoHom
    {J : GrothendieckTopology C} {X Y : StackOver J} {F G : X ⟶ Y}
    (η : F ⟶ G) :
    toFibredCategoryMor F ⟶ toFibredCategoryMor G :=
  η.hom.hom

private abbrev stackTwoHomToNatTrans
    {J : GrothendieckTopology C} {X Y : StackOver J} {F G : X ⟶ Y}
    (η : F ⟶ G) :
    (toBasedFunctor F).toFunctor ⟶ (toBasedFunctor G).toFunctor :=
  (stackTwoHomToFibredCategoryMorTwoHom η).hom.hom.toNatTrans

section

variable (J : GrothendieckTopology C)

variable (U : C)

/- Domain-style sampling for Lemma 8.13.2:
- primary domain: stacks over a site, localization of a site at `U`, and the slice strict
  `2`-category over the representable stack `C/U`.
- inspected owner-level declarations:
  `StackOver`,
  `StackOver.ofProjection`,
  `SliceTwoCategory`,
  `FibredCategoryMor.ofBasedFunctor`,
  `StrictPseudofunctor.IsInverse`.
- best owner abstraction: the localized side should use the chapter owner `StackOver (J.over U)`
  directly, and the two source constructions should be packaged as strict pseudofunctors between
  `StackOver (J.over U)` and `SliceTwoCategory (sliceStackOver J U hU)`.
- primitive data: the projection functors produced by Constructions A and B together with the
  stack-on-site proofs for those projections.
- derived API: the bundled `StackOver` objects, their induced slice morphisms, and the inverse
  package `StrictPseudofunctor.IsInverse`.

Source/core/bridge triage:
- `source-facing`: `localizedStacksToSlice`, `sliceToLocalizedStacks`,
  `localizedStacks_equivalent_to_stacks_with_map_to_slice`.
- `core/canonical`: `StackOver`, `StackOver.ofProjection`, `SliceTwoCategory`,
  `FibredCategoryMor.ofBasedFunctor`, `StrictPseudofunctor.IsInverse`.
- `bridge/view`: the representable stack `sliceStackOver` and the private bundled object
  conversions used by Constructions A and B. -/

/-- If the representable presheaf `h_U` is a sheaf on `(C, J)`, then the slice fibred category
`C/U` defines the corresponding representable stack over `(C, J)`. -/
abbrev sliceStackOver
    (hU : Presheaf.IsSheaf J h[U]) : StackOver J :=
  let p : Over U ⥤ C := Over.forget U
  letI : IsStackOnSite J p := by
    simpa [p] using (over_forget_isStackOnSite_iff_representable_isSheaf J U).2 hU
  ⟨FibredCategoryOver.ofFunctor p, by
    simpa [FibredCategoryOver.p, FibredCategoryOver.ofFunctor] using
      (inferInstance : IsStackOnSite J p)⟩

private abbrev sliceTwoHomToNatTrans
    (hU : Presheaf.IsSheaf J h[U])
    {X Y : SliceTwoCategory (sliceStackOver J U hU)} {F G : X ⟶ Y}
    (η : F ⟶ G) :
    (toBasedFunctor F.hom).toFunctor ⟶ (toBasedFunctor G.hom).toFunctor :=
  stackTwoHomToNatTrans η.hom

/-- Construction A on objects: a stack over the localized site `(C/U, J.over U)` defines a stack
over `(C, J)` by composing its projection with `Over.forget U`. -/
private abbrev localizedStackAsStackOver
    (hU : Presheaf.IsSheaf J h[U])
    (X : StackOver (J.over U)) : StackOver J :=
  let p : X.S ⥤ C := X.p ⋙ Over.forget U
  letI : IsStackOnSite J p := by
    change IsStackOnSite J (X.p ⋙ Over.forget U)
    sorry
  ⟨FibredCategoryOver.ofFunctor p, by
    simpa [FibredCategoryOver.p, FibredCategoryOver.ofFunctor] using
      (inferInstance : IsStackOnSite J p)⟩

/-- The based functor over `C` underlying Construction A on the map to `C/U`. -/
private abbrev localizedStackToSliceBasedFunctor
    (hU : Presheaf.IsSheaf J h[U])
    (X : StackOver (J.over U)) :
    (localizedStackAsStackOver J U hU X).toFibredCategoryOver.toBasedCategory ⥤ᵇ
      (sliceStackOver J U hU).toFibredCategoryOver.toBasedCategory where
  toFunctor := show X.S ⥤ Over U from X.p
  w := by
    rfl

private theorem localizedStackToSlice_preservesStronglyCartesian
    (hU : Presheaf.IsSheaf J h[U])
    (X : StackOver (J.over U)) :
    BasedFunctor.PreservesStronglyCartesian
      (localizedStackToSliceBasedFunctor J U hU X) := by
  intro a b φ hφ
  simpa [localizedStackToSliceBasedFunctor, sliceStackOver, FibredCategoryOver.p,
      FibredCategoryOver.ofFunctor] using
    (inferInstance : IsFibredInGroupoids (Over.forget U)).isStronglyCartesian_map
      (X.p.map φ)

/-- Construction A on objects: the canonical morphism from the induced stack over `(C, J)` to the
representable stack `C/U`. -/
private abbrev localizedStackToSliceMorphism
    (hU : Presheaf.IsSheaf J h[U])
    (X : StackOver (J.over U)) :
    FibredCategoryMor
      (localizedStackAsStackOver J U hU X).toFibredCategoryOver
      (sliceStackOver J U hU).toFibredCategoryOver :=
  FibredCategoryMor.ofBasedFunctor
    (localizedStackToSliceBasedFunctor J U hU X)
    (localizedStackToSlice_preservesStronglyCartesian J U hU X)

/-- Construction A on `1`-morphisms, forgetting that the source and target lie over `Over U` and
viewing the same functor as a morphism over `C`. -/
private abbrev localizedStackMapAsStackBasedFunctor
    (hU : Presheaf.IsSheaf J h[U])
    {X Y : StackOver (J.over U)} (F : X ⟶ Y) :
    (localizedStackAsStackOver J U hU X).toFibredCategoryOver.toBasedCategory ⥤ᵇ
      (localizedStackAsStackOver J U hU Y).toFibredCategoryOver.toBasedCategory where
  toFunctor := show X.S ⥤ Y.S from (toBasedFunctor F).toFunctor
  w := by
    sorry

private theorem localizedStackMapAsStack_preservesStronglyCartesian
    (hU : Presheaf.IsSheaf J h[U])
    {X Y : StackOver (J.over U)} (F : X ⟶ Y) :
    BasedFunctor.PreservesStronglyCartesian
      (localizedStackMapAsStackBasedFunctor J U hU F) := by
  intro a b φ hφ
  sorry

private abbrev localizedStackMapAsStackMorphism
    (hU : Presheaf.IsSheaf J h[U])
    {X Y : StackOver (J.over U)} (F : X ⟶ Y) :
    FibredCategoryMor
      (localizedStackAsStackOver J U hU X).toFibredCategoryOver
      (localizedStackAsStackOver J U hU Y).toFibredCategoryOver :=
  FibredCategoryMor.ofBasedFunctor
    (localizedStackMapAsStackBasedFunctor J U hU F)
    (localizedStackMapAsStack_preservesStronglyCartesian J U hU F)

private abbrev localizedStackMapAsStackTwoHom
    (hU : Presheaf.IsSheaf J h[U])
    {X Y : StackOver (J.over U)} {F G : X ⟶ Y} (η : F ⟶ G) :
    localizedStackMapAsStackMorphism J U hU F ⟶
      localizedStackMapAsStackMorphism J U hU G :=
  let τ := stackTwoHomToNatTrans η
  ⟨ObjectProperty.homMk <|
      { toNatTrans := τ
        isHomLift' := by
          intro a
          sorry },
    trivial⟩

private abbrev localizedStackToSliceHom
    (hU : Presheaf.IsSheaf J h[U])
    (X : StackOver (J.over U)) :
    localizedStackAsStackOver J U hU X ⟶
      sliceStackOver J U hU :=
  InducedCategory.Hom.ofFibredCategoryMor (localizedStackToSliceMorphism J U hU X)

private theorem localizedStackToSlice_map_comm
    (hU : Presheaf.IsSheaf J h[U])
    {X Y : StackOver (J.over U)} (F : X ⟶ Y) :
    InducedCategory.Hom.ofFibredCategoryMor (localizedStackMapAsStackMorphism J U hU F) ≫
        localizedStackToSliceHom J U hU Y =
      localizedStackToSliceHom J U hU X := by
  sorry

/-- Construction A of Lemma 8.13.2: a localized stack defines a stack over `(C, J)` equipped with
its canonical map to the representable stack `C/U`. -/
private def localizedStacksToSlicePreCore
    (hU : Presheaf.IsSheaf J h[U]) :
    StrictPseudofunctorPreCore
      (StackOver (J.over U))
      (SliceTwoCategory (sliceStackOver J U hU)) :=
  {
    obj := fun X ↦
      { obj := localizedStackAsStackOver J U hU X
        hom := localizedStackToSliceHom J U hU X }
    map := fun F ↦
      { hom := InducedCategory.Hom.ofFibredCategoryMor (localizedStackMapAsStackMorphism J U hU F)
        comm := localizedStackToSlice_map_comm J U hU F }
    map₂ := fun η ↦
      { hom := InducedCategory.Hom.homMk (localizedStackMapAsStackTwoHom J U hU η)
        comm := by
          sorry
      }
    map_id := by
      intro X
      sorry
    map_comp := by
      intro X Y Z F G
      sorry
    map₂_id := by
      intro X Y F
      sorry
    map₂_comp := by
      intro X Y F G H η θ
      sorry
    map₂_whisker_left := by
      intro a b c f g g' η
      sorry
    map₂_whisker_right := by
      intro a b c f f' η g
      sorry
  }

/-- Construction A of Lemma 8.13.2: a localized stack defines a stack over `(C, J)` equipped with
its canonical map to the representable stack `C/U`. -/
noncomputable def localizedStacksToSlice
    (hU : Presheaf.IsSheaf J h[U]) :
    StrictPseudofunctor
      (StackOver (J.over U))
      (SliceTwoCategory (sliceStackOver J U hU)) :=
  StrictPseudofunctor.mk'' (localizedStacksToSlicePreCore J U hU)

/-- Construction B on objects: a stack over `(C, J)` with a map to `C/U` is viewed as a stack
over the localized site `(C/U, J.over U)` via that map. -/
private abbrev sliceObjectAsLocalizedStack
    (hU : Presheaf.IsSheaf J h[U])
    (X : SliceTwoCategory (sliceStackOver J U hU)) :
    StackOver (J.over U) :=
  let p : X.obj.S ⥤ Over U := (toBasedFunctor X.hom).toFunctor
  letI : IsStackOnSite (J.over U) p := by
    change IsStackOnSite (J.over U) (toBasedFunctor X.hom).toFunctor
    sorry
  ⟨FibredCategoryOver.ofFunctor p, by
    simpa [FibredCategoryOver.p, FibredCategoryOver.ofFunctor] using
      (inferInstance : IsStackOnSite (J.over U) p)⟩

private abbrev sliceHomToLocalizedStackBasedFunctor
    (hU : Presheaf.IsSheaf J h[U])
    {X Y : SliceTwoCategory (sliceStackOver J U hU)}
    (F : X ⟶ Y) :
    (sliceObjectAsLocalizedStack J U hU X).toFibredCategoryOver.toBasedCategory ⥤ᵇ
      (sliceObjectAsLocalizedStack J U hU Y).toFibredCategoryOver.toBasedCategory where
  toFunctor := show X.obj.S ⥤ Y.obj.S from (toBasedFunctor F.hom).toFunctor
  w := by
    sorry

private theorem sliceHomToLocalizedStack_preservesStronglyCartesian
    (hU : Presheaf.IsSheaf J h[U])
    {X Y : SliceTwoCategory (sliceStackOver J U hU)}
    (F : X ⟶ Y) :
    BasedFunctor.PreservesStronglyCartesian
      (sliceHomToLocalizedStackBasedFunctor J U hU F) := by
  intro a b φ hφ
  sorry

/-- Construction B on `1`-morphisms: a triangle over `C/U` induces a morphism over the localized
site `(C/U, J.over U)`. -/
private abbrev sliceHomToLocalizedStackMorphism
    (hU : Presheaf.IsSheaf J h[U])
    {X Y : SliceTwoCategory (sliceStackOver J U hU)}
    (F : X ⟶ Y) :
    FibredCategoryMor
      (sliceObjectAsLocalizedStack J U hU X).toFibredCategoryOver
      (sliceObjectAsLocalizedStack J U hU Y).toFibredCategoryOver :=
  FibredCategoryMor.ofBasedFunctor
    (sliceHomToLocalizedStackBasedFunctor J U hU F)
    (sliceHomToLocalizedStack_preservesStronglyCartesian J U hU F)

private abbrev sliceHomToLocalizedStackTwoHom
    (hU : Presheaf.IsSheaf J h[U])
    {X Y : SliceTwoCategory (sliceStackOver J U hU)}
    {F G : X ⟶ Y} (η : F ⟶ G) :
    sliceHomToLocalizedStackMorphism J U hU F ⟶
      sliceHomToLocalizedStackMorphism J U hU G :=
  let τ := sliceTwoHomToNatTrans J U hU η
  ⟨ObjectProperty.homMk <|
      { toNatTrans := τ
        isHomLift' := by
          intro a
          sorry },
    trivial⟩

/-- Construction B of Lemma 8.13.2: a stack over `(C, J)` equipped with a map to `C/U` defines a
stack over the localized site `(C/U, J.over U)`. -/
private def sliceToLocalizedStacksPreCore
    (hU : Presheaf.IsSheaf J h[U]) :
    StrictPseudofunctorPreCore
      (SliceTwoCategory (sliceStackOver J U hU))
      (StackOver (J.over U)) :=
  {
    obj := fun X ↦ sliceObjectAsLocalizedStack J U hU X
    map := fun F ↦
      InducedCategory.Hom.ofFibredCategoryMor (sliceHomToLocalizedStackMorphism J U hU F)
    map₂ := fun η ↦
      InducedCategory.Hom.homMk (sliceHomToLocalizedStackTwoHom J U hU η)
    map_id := by
      intro X
      sorry
    map_comp := by
      intro X Y Z F G
      sorry
    map₂_id := by
      intro X Y F
      sorry
    map₂_comp := by
      intro X Y F G H η θ
      sorry
    map₂_whisker_left := by
      intro a b c f g g' η
      sorry
    map₂_whisker_right := by
      intro a b c f f' η g
      sorry
  }

/-- Construction B of Lemma 8.13.2: a stack over `(C, J)` equipped with a map to `C/U` defines a
stack over the localized site `(C/U, J.over U)`. -/
noncomputable def sliceToLocalizedStacks
    (hU : Presheaf.IsSheaf J h[U]) :
    StrictPseudofunctor
      (SliceTwoCategory (sliceStackOver J U hU))
      (StackOver (J.over U)) :=
  StrictPseudofunctor.mk'' (sliceToLocalizedStacksPreCore J U hU)

/-- Construction A followed by Construction B is the identity on the strict `2`-category of
stacks over the localized site `(C/U, J.over U)` on objects. -/
@[simp] private theorem sliceToLocalizedStacks_obj_localizedStacksToSlice_obj
    (hU : Presheaf.IsSheaf J h[U]) :
    ∀ X : StackOver (J.over U),
      (sliceToLocalizedStacks J U hU).obj ((localizedStacksToSlice J U hU).obj X) = X := by
  intro X
  sorry

/-- Construction A followed by Construction B is the identity on the strict `2`-category of
stacks over the localized site `(C/U, J.over U)` on `1`-morphisms. -/
@[simp] private theorem sliceToLocalizedStacks_map_localizedStacksToSlice_map
    (hU : Presheaf.IsSheaf J h[U]) :
    ∀ ⦃X Y : StackOver (J.over U)⦄ (F : X ⟶ Y),
      HEq ((sliceToLocalizedStacks J U hU).map ((localizedStacksToSlice J U hU).map F)) F := by
  intro X Y F
  sorry

/-- Construction A followed by Construction B is the identity on the strict `2`-category of
stacks over the localized site `(C/U, J.over U)` on `2`-morphisms. -/
@[simp] private theorem sliceToLocalizedStacks_map₂_localizedStacksToSlice_map₂
    (hU : Presheaf.IsSheaf J h[U]) :
    ∀ ⦃X Y : StackOver (J.over U)⦄ {F G : X ⟶ Y} (η : F ⟶ G),
      HEq ((sliceToLocalizedStacks J U hU).map₂ ((localizedStacksToSlice J U hU).map₂ η)) η := by
  intro X Y F G η
  sorry

/-- Construction B followed by Construction A is the identity on the slice strict `2`-category of
stacks over `(C, J)` above the representable stack `C/U` on objects. -/
@[simp] private theorem localizedStacksToSlice_obj_sliceToLocalizedStacks_obj
    (hU : Presheaf.IsSheaf J h[U]) :
    ∀ X : SliceTwoCategory (sliceStackOver J U hU),
      (localizedStacksToSlice J U hU).obj ((sliceToLocalizedStacks J U hU).obj X) = X := by
  intro X
  sorry

/-- Construction B followed by Construction A is the identity on the slice strict `2`-category of
stacks over `(C, J)` above the representable stack `C/U` on `1`-morphisms, up to transport along
the object equalities from `localizedStacksToSlice_obj_sliceToLocalizedStacks_obj`. -/
private theorem localizedStacksToSlice_map_sliceToLocalizedStacks_map
    (hU : Presheaf.IsSheaf J h[U]) :
    ∀ ⦃X Y : SliceTwoCategory (sliceStackOver J U hU)⦄ (F : X ⟶ Y),
      HEq ((localizedStacksToSlice J U hU).map ((sliceToLocalizedStacks J U hU).map F)) F := by
  intro X Y F
  sorry

/-- Construction B followed by Construction A is the identity on the slice strict `2`-category of
stacks over `(C, J)` above the representable stack `C/U` on `2`-morphisms, up to transport along
the object equalities from `localizedStacksToSlice_obj_sliceToLocalizedStacks_obj`. -/
private theorem localizedStacksToSlice_map₂_sliceToLocalizedStacks_map₂
    (hU : Presheaf.IsSheaf J h[U]) :
    ∀ ⦃X Y : SliceTwoCategory (sliceStackOver J U hU)⦄
      {F G : X ⟶ Y} (η : F ⟶ G),
      HEq ((localizedStacksToSlice J U hU).map₂ ((sliceToLocalizedStacks J U hU).map₂ η)) η := by
  intro X Y F G η
  sorry

/-- Lemma 8.13.2: if the representable presheaf `h[U]` is a sheaf on `(C, J)`, then Construction A
`localizedStacksToSlice` and Construction B `sliceToLocalizedStacks` are inverse strict
`2`-functors between stacks over the localized site `(C/U, J.over U)` and stacks over `(C, J)`
above the representable stack `C/U`. This packages the source statement in the canonical Lean
form `StrictPseudofunctor.IsInverse`. -/
theorem localizedStacks_equivalent_to_stacks_with_map_to_slice
    (hU : Presheaf.IsSheaf J h[U]) :
    StrictPseudofunctor.IsInverse
      (localizedStacksToSlice J U hU)
      (sliceToLocalizedStacks J U hU) := by
  refine
    { left_obj := sliceToLocalizedStacks_obj_localizedStacksToSlice_obj J U hU
      left_map := sliceToLocalizedStacks_map_localizedStacksToSlice_map J U hU
      left_map₂ := sliceToLocalizedStacks_map₂_localizedStacksToSlice_map₂ J U hU
      right_obj := localizedStacksToSlice_obj_sliceToLocalizedStacks_obj J U hU
      right_map := localizedStacksToSlice_map_sliceToLocalizedStacks_map J U hU
      right_map₂ := localizedStacksToSlice_map₂_sliceToLocalizedStacks_map₂ J U hU }

end

end CategoryTheory
