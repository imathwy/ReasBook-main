import Mathlib
import stacks_project.Chap04.Lemma_4_34_1
import stacks_project.Chap08.Lemma_8_4_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u₁ u₂ u₃ v₁ v₂ v₃

namespace CategoryTheory

open BasedFunctor
open Functor IsHomLift IsStronglyCartesian

section

variable {C : Type u₁} {S₁ : Type u₂} {S₂ : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} S₁] [Category.{v₃} S₂]
variable (J : GrothendieckTopology C)

variable (p₁ : S₁ ⥤ C) (p₂ : S₂ ⥤ C)

/- Domain-style sampling for Lemma 8.4.4:
- primary domain: stacks over a site, transported along equivalences in the based category
  `Cat/C`.
- inspected owner-level declarations:
  `IsStackOnSite`,
  `BasedFunctor.IsEquivalenceOverBase`,
  `BasedFunctor.isFibered_iff_of_equivalence_over_base`,
  `isStackOnSite_iff_canonicalFiberPseudofunctor_toDescentData_isEquivalence`.
- best owner abstraction: the source-facing owner remains `IsStackOnSite J p`; the based functor
  `F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂` and the predicate
  `F.IsEquivalenceOverBase` are the canonical Chapter 4 transport interface.
- primitive data: only the two projection functors `p₁`, `p₂` and the over-base equivalence data
  `hF`.
- derived API: the induced transport of fibredness and of the canonical descent-data equivalences
  used to compare the stack conditions.

Source/core/bridge triage:
- `source-facing`: `isStackOnSite_iff_of_equivalence_over_base`.
- `core/canonical`: `IsStackOnSite`, `BasedFunctor.IsEquivalenceOverBase`, and
  `Pseudofunctor.IsStack (canonicalFiberPseudofunctor p) J`.
- `bridge/view`: the coverwise descent-data criterion from Lemma `8.4.2`. -/

/-
Proof sketch: use `BasedFunctor.isFibered_iff_of_equivalence_over_base` to transport the
fibredness part of `IsStackOnSite`, then apply Lemma `8.4.2` to rewrite the stack condition for
each side in terms of equivalence of the canonical descent functors for every cover. The
equivalence-over-base data also upgrades to full faithfulness of the underlying based functor by
the Chapter 4 owner API, which is the canonical input for comparing the resulting descent-data
functors coverwise.
-/
/-- An equivalence over the base between fibred categories is automatically fully faithful on the
underlying based functor. This is a proof-shape helper used in the stack transport argument. -/
private theorem fullyFaithful_of_isEquivalenceOverBase
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase) :
    Nonempty F.FullyFaithful := by
  let _ : F.IsEquivalence := isEquivalence_of_isEquivalenceOverBase F hF
  exact ⟨show F.FullyFaithful from .ofFullyFaithful F.toFunctor⟩

/-- Helper for Lemma 8.4.4: forgetting explicit equivalence-over-base data yields an ordinary
equivalence of the total categories, which supplies the adjointified unit used in the
mixed-hom transport proofs. -/
private noncomputable def ordinary_equivalence_of_equivalence_data_mixed_hom
    {X : BasedCategory.{v₂, u₂} C} {Y : BasedCategory.{v₃, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) :
    X.obj ≌ Y.obj :=
  CategoryTheory.Equivalence.mk
    F.toFunctor
    e.inverse.toFunctor
    ((BasedNatTrans.forgetful X X).mapIso e.unitIso)
    ((BasedNatTrans.forgetful Y Y).mapIso e.counitIso)

/-- Helper for Lemma 8.4.4: the forgotten counit inverse cancels the adjointified ordinary unit
inverse on each source object. This is the core identity behind the mixed-hom push-pull
comparison. -/
private theorem ordinary_equivalence_counit_adjointified_unit_inverse_comp_mixed_hom
    {X : BasedCategory.{v₂, u₂} C} {Y : BasedCategory.{v₃, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) (x : X.obj) :
    e.counitIso.inv.app (F.obj x) ≫
        F.map ((ordinary_equivalence_of_equivalence_data_mixed_hom (C := C) e).unitIso.inv.app x) =
      𝟙 (F.obj x) := by
  -- The ordinary equivalence keeps the forgotten counit, so the standard triangle identity
  -- supplies the needed cancellation directly.
  exact CategoryTheory.Equivalence.counitIso_functor_comp
    (ordinary_equivalence_of_equivalence_data_mixed_hom (C := C) e) x

/-- Helper for Lemma 8.4.4: use the adjointified inverse unit from the forgotten ordinary
equivalence as the source-side bridge in the mixed-hom transport proofs. -/
private noncomputable abbrev adjointified_unit_inv_app_mixed_hom
    {X : BasedCategory.{v₂, u₂} C} {Y : BasedCategory.{v₃, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) (x : X.obj) :
    e.inverse.obj (F.obj x) ⟶ x :=
  (ordinary_equivalence_of_equivalence_data_mixed_hom (C := C) e).unitIso.inv.app x

/-- Helper for Lemma 8.4.4: the adjointified inverse unit is vertical over the identity, so it
can be composed onto pulled-back lift witnesses without changing the base morphism. -/
private theorem adjointified_unit_inv_isHomLift_mixed_hom
    {X : BasedCategory.{v₂, u₂} C} {Y : BasedCategory.{v₃, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) (x : X.obj) :
    X.p.IsHomLift (𝟙 (X.p.obj x)) (adjointified_unit_inv_app_mixed_hom (C := C) e x) := by
  -- Push the adjointified inverse unit forward, identify it with the counit component, and then
  -- pull the resulting vertical lift back across `F`.
  have hε :
      Y.p.IsHomLift (𝟙 (Y.p.obj (F.obj x))) (e.counitIso.hom.app (F.obj x)) := by
    simpa using BasedNatTrans.isHomLift e.counitIso.hom
      (rfl : Y.p.obj (F.obj x) = Y.p.obj (F.obj x))
  have hEq :
      F.map (adjointified_unit_inv_app_mixed_hom (C := C) e x) =
        e.counitIso.hom.app (F.obj x) := by
    simpa [adjointified_unit_inv_app_mixed_hom] using
      ((ordinary_equivalence_of_equivalence_data_mixed_hom (C := C) e).counit_app_functor x).symm
  have hmap :
      Y.p.IsHomLift (𝟙 (Y.p.obj (F.obj x)))
        (F.map (adjointified_unit_inv_app_mixed_hom (C := C) e x)) := by
    rw [hEq]
    exact hε
  have hX :
      X.p.IsHomLift (𝟙 (Y.p.obj (F.obj x)))
        (adjointified_unit_inv_app_mixed_hom (C := C) e x) := by
    exact
      (F.isHomLift_iff (𝟙 (Y.p.obj (F.obj x)))
        (adjointified_unit_inv_app_mixed_hom (C := C) e x)).mp hmap
  rw [← F.w_obj x]
  exact hX

/-- Helper for Lemma 8.4.4: pull a target lifting problem back across the quasi-inverse and the
adjointified inverse unit without changing the underlying base morphism. -/
private theorem inverse_transport_lift_over_base_mixed_hom
    {X : BasedCategory.{v₂, u₂} C} {Y : BasedCategory.{v₃, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F)
    {x y : X.obj} (φ : x ⟶ y)
    {z : Y.obj} (g : Y.p.obj z ⟶ Y.p.obj (F.obj x))
    (ψ : z ⟶ F.obj y)
    [Y.p.IsHomLift (g ≫ Y.p.map (F.map φ)) ψ] :
    X.p.IsHomLift (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ)
      (e.inverse.map ψ ≫ adjointified_unit_inv_app_mixed_hom (C := C) e y) := by
  -- Rewrite the target lifting problem into source coordinates, then compose with the vertical
  -- adjointified inverse unit.
  have hψY : Y.p.IsHomLift (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) ψ := by
    refine IsHomLift.of_fac Y.p _ ψ rfl (F.w_obj y) ?_
    have hbase :
        g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ =
          Y.p.map ψ ≫ eqToHom (F.w_obj y) := by
      calc
        g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ
            = g ≫ Y.p.map (F.map φ) ≫ eqToHom (F.w_obj y) := by
                simpa [Category.assoc] using
                  (congrArg (fun k ↦ g ≫ k ≫ eqToHom (F.w_obj y))
                    (Functor.congr_hom F.w φ)).symm
        _ = Y.p.map ψ ≫ eqToHom (F.w_obj y) := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ eqToHom (F.w_obj y))
                  (IsHomLift.eq_of_isHomLift Y.p (g ≫ Y.p.map (F.map φ)) ψ)
    simpa [Category.assoc] using hbase
  have hψX :
      X.p.IsHomLift (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) (e.inverse.map ψ) :=
    (e.inverse.isHomLift_iff _ ψ).2 hψY
  have hη :
      X.p.IsHomLift (𝟙 (X.p.obj y)) (adjointified_unit_inv_app_mixed_hom (C := C) e y) := by
    exact adjointified_unit_inv_isHomLift_mixed_hom (C := C) e y
  exact @IsHomLift.comp_lift_id_right' _ _ _ _ X.p _ _ _ _ _
    (g ≫ eqToHom (F.w_obj x) ≫ X.p.map φ) (e.inverse.map ψ) hψX
    (X.p.obj y) (adjointified_unit_inv_app_mixed_hom (C := C) e y) hη

/-- Helper for Lemma 8.4.4: push a source lift forward across the counit inverse while preserving
its base morphism. -/
private theorem forward_transport_lift_over_base_mixed_hom
    {X : BasedCategory.{v₂, u₂} C} {Y : BasedCategory.{v₃, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F)
    {x : X.obj} {z : Y.obj} (g : Y.p.obj z ⟶ X.p.obj x)
    (ξ : e.inverse.obj z ⟶ x)
    [X.p.IsHomLift g ξ] :
    Y.p.IsHomLift g (e.counitIso.inv.app z ≫ F.map ξ) := by
  -- Push the source lift along `F`, then precompose with the vertical counit inverse.
  have hξY : Y.p.IsHomLift g (F.map ξ) :=
    (F.isHomLift_iff g ξ).2 (show X.p.IsHomLift g ξ from inferInstance)
  have hε : Y.p.IsHomLift (𝟙 (Y.p.obj z)) (e.counitIso.inv.app z) := by
    simpa using BasedNatTrans.isHomLift e.counitIso.inv (rfl : Y.p.obj z = Y.p.obj z)
  exact @IsHomLift.comp_lift_id_left' _ _ _ _ Y.p _ _ _
    (Y.p.obj z) (e.counitIso.inv.app z) hε _ _ g (F.map ξ) hξY

/-- Helper for Lemma 8.4.4: composing with the canonical base-change isomorphism from `F.w_obj`
does not affect whether a target morphism is a lift. -/
private theorem isHomLift_over_target_eq_iff_mixed_hom
    {X : BasedCategory.{v₂, u₂} C} {Y : BasedCategory.{v₃, u₃} C}
    {F : X ⥤ᵇ Y} {z : Y.obj} {x : X.obj}
    (g : Y.p.obj z ⟶ Y.p.obj (F.obj x))
    (θ : z ⟶ F.obj x) :
    Y.p.IsHomLift g θ ↔ Y.p.IsHomLift (g ≫ eqToHom (F.w_obj x)) θ := by
  -- The extra `eqToHom` only rewrites the codomain into source-side base coordinates.
  exact (IsHomLift.lift_comp_eqToHom_iff Y.p g θ (F.w_obj x)).symm

/-- Helper for Lemma 8.4.4: a target-side factorization pulls back across the quasi-inverse and
the adjointified inverse unit to the corresponding source-side factorization. -/
private theorem pullback_factorization_of_map_factorization_mixed_hom
    {X : BasedCategory.{v₂, u₂} C} {Y : BasedCategory.{v₃, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F)
    {x y : X.obj} (φ : x ⟶ y)
    {z : Y.obj} {τ' : z ⟶ F.obj x} {ψ' : z ⟶ F.obj y}
    (hτ' : τ' ≫ F.map φ = ψ') :
    (e.inverse.map τ' ≫ adjointified_unit_inv_app_mixed_hom (C := C) e x) ≫ φ =
      e.inverse.map ψ' ≫ adjointified_unit_inv_app_mixed_hom (C := C) e y := by
  -- Use naturality of the adjointified inverse unit to move the `F.map φ` factor through the
  -- pulled-back morphism.
  have hη :
      e.inverse.map (F.map φ) ≫ adjointified_unit_inv_app_mixed_hom (C := C) e y =
        adjointified_unit_inv_app_mixed_hom (C := C) e x ≫ φ := by
    let E := ordinary_equivalence_of_equivalence_data_mixed_hom (C := C) e
    have hη' :
        E.inverse.map (E.functor.map φ) ≫ E.unitInv.app y =
          (E.unitInv.app x ≫ φ ≫ E.unit.app y) ≫ E.unitInv.app y := by
      simpa [Category.assoc] using
        congrArg (fun k ↦ k ≫ E.unitInv.app y) (E.inv_fun_map x y φ)
    have hη'' :
        E.inverse.map (E.functor.map φ) ≫ E.unitInv.app y =
          E.unitInv.app x ≫ φ := by
      rw [hη']
      simpa [Category.assoc]
    change E.inverse.map (E.functor.map φ) ≫ E.unitInv.app y = E.unitInv.app x ≫ φ
    exact hη''
  calc
    (e.inverse.map τ' ≫ adjointified_unit_inv_app_mixed_hom (C := C) e x) ≫ φ
        = e.inverse.map τ' ≫
            (adjointified_unit_inv_app_mixed_hom (C := C) e x ≫ φ) := by
              simp [Category.assoc]
    _ = e.inverse.map τ' ≫
          (e.inverse.map (F.map φ) ≫ adjointified_unit_inv_app_mixed_hom (C := C) e y) := by
          rw [← hη]
    _ = e.inverse.map (τ' ≫ F.map φ) ≫ adjointified_unit_inv_app_mixed_hom (C := C) e y := by
          simp [Functor.map_comp, Category.assoc]
    _ = e.inverse.map ψ' ≫ adjointified_unit_inv_app_mixed_hom (C := C) e y := by
          rw [hτ']

/-- Helper for Lemma 8.4.4: pushing a pulled-back morphism forward recovers the original target
morphism. This is the mixed-hom analogue of the standard push-pull identity. -/
private theorem pushforward_pullback_eq_mixed_hom
    {X : BasedCategory.{v₂, u₂} C} {Y : BasedCategory.{v₃, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F)
    {x : X.obj} {z : Y.obj} (θ : z ⟶ F.obj x) :
    e.counitIso.inv.app z ≫
        F.map (e.inverse.map θ ≫ adjointified_unit_inv_app_mixed_hom (C := C) e x) = θ := by
  -- Move `θ` across the counit inverse, then collapse the remaining counit-unit tail.
  rw [Functor.map_comp]
  have hnat :
      e.counitIso.inv.app z ≫ F.map (e.inverse.map θ) ≫
          F.map (adjointified_unit_inv_app_mixed_hom (C := C) e x) =
        θ ≫ e.counitIso.inv.app (F.obj x) ≫
          F.map (adjointified_unit_inv_app_mixed_hom (C := C) e x) := by
    simpa [Functor.comp_map, Category.assoc] using
      (congrArg (fun k ↦ k ≫ F.map (adjointified_unit_inv_app_mixed_hom (C := C) e x))
        (e.counitIso.inv.naturality θ)).symm
  have htail :
      θ ≫ e.counitIso.inv.app (F.obj x) ≫
          F.map (adjointified_unit_inv_app_mixed_hom (C := C) e x) = θ := by
    simpa [adjointified_unit_inv_app_mixed_hom, Category.assoc] using
      congrArg (fun k ↦ θ ≫ k)
        (ordinary_equivalence_counit_adjointified_unit_inverse_comp_mixed_hom
          (C := C) (e := e) x)
  exact hnat.trans htail

/-- Helper for Lemma 8.4.4: explicit equivalence-over-base data preserve strongly cartesian
morphisms even when source and target live in different hom universes. -/
private theorem preservesStronglyCartesian_of_equivalence_data_mixed_hom
    {X : BasedCategory.{v₂, u₂} C} {Y : BasedCategory.{v₃, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) :
    F.PreservesStronglyCartesian := by
  intro a b φ hφ
  refine
    { toIsHomLift := by
        infer_instance
      universal_property' := ?_ }
  intro z g ψ' hψ'
  -- Pull the lifting problem back to the source, solve it there, and then push the solution
  -- forward again across the counit inverse.
  let ψX : e.inverse.obj z ⟶ b :=
    e.inverse.map ψ' ≫ adjointified_unit_inv_app_mixed_hom (C := C) e b
  have hψXlift :
      X.p.IsHomLift ((g ≫ eqToHom (F.w_obj a)) ≫ X.p.map φ) ψX := by
    simpa [ψX] using inverse_transport_lift_over_base_mixed_hom (C := C) (e := e) φ g ψ'
  letI : X.p.IsHomLift ((g ≫ eqToHom (F.w_obj a)) ≫ X.p.map φ) ψX := hψXlift
  obtain ⟨ξ, hξ, hξuniq⟩ :=
    Functor.IsStronglyCartesian.universal_property X.p (X.p.map φ) φ
      (g ≫ eqToHom (F.w_obj a))
      (((g ≫ eqToHom (F.w_obj a)) ≫ X.p.map φ)) rfl ψX
  letI : X.p.IsHomLift (g ≫ eqToHom (F.w_obj a)) ξ := hξ.1
  let ξ' : z ⟶ F.obj a := e.counitIso.inv.app z ≫ F.map ξ
  have hξ'base :
      Y.p.IsHomLift (g ≫ eqToHom (F.w_obj a)) ξ' :=
    forward_transport_lift_over_base_mixed_hom (e := e)
      (g ≫ eqToHom (F.w_obj a)) ξ
  have hξ' : Y.p.IsHomLift g ξ' :=
    (isHomLift_over_target_eq_iff_mixed_hom (F := F) g ξ').mpr hξ'base
  have hpushψ : e.counitIso.inv.app z ≫ F.map ψX = ψ' := by
    simpa [ψX, Functor.map_comp, Category.assoc] using
      pushforward_pullback_eq_mixed_hom (C := C) (e := e) ψ'
  refine ⟨ξ', ⟨hξ', ?_⟩, ?_⟩
  · -- The pushed-forward lift factors through `F.map φ` by functoriality and the pulled-back
    -- source factorization.
    have hstep1 : ξ' ≫ F.map φ = e.counitIso.inv.app z ≫ F.map (ξ ≫ φ) := by
      simp [ξ', Functor.map_comp, Category.assoc]
    have hstep2 :
        e.counitIso.inv.app z ≫ F.map (ξ ≫ φ) =
          e.counitIso.inv.app z ≫ F.map ψX := by
      simpa using congrArg (fun k ↦ e.counitIso.inv.app z ≫ F.map k) hξ.2
    exact hstep1.trans <| hstep2.trans hpushψ
  · intro η hη
    -- Pull any competing target lift back to the source and compare there by uniqueness.
    have hηbase :
        Y.p.IsHomLift (g ≫ eqToHom (F.w_obj a)) η :=
      (isHomLift_over_target_eq_iff_mixed_hom (F := F) g η).mp hη.1
    have hηpull :
        X.p.IsHomLift (g ≫ eqToHom (F.w_obj a))
          (e.inverse.map η ≫ adjointified_unit_inv_app_mixed_hom (C := C) e a) := by
      have hηpre : X.p.IsHomLift (g ≫ eqToHom (F.w_obj a)) (e.inverse.map η) :=
        (e.inverse.isHomLift_iff (g ≫ eqToHom (F.w_obj a)) η).2 hηbase
      have hηunit :
          X.p.IsHomLift (𝟙 (X.p.obj a))
            (adjointified_unit_inv_app_mixed_hom (C := C) e a) := by
        exact adjointified_unit_inv_isHomLift_mixed_hom (C := C) e a
      exact @IsHomLift.comp_lift_id_right' _ _ _ _ X.p _ _ _ _ _
        (g ≫ eqToHom (F.w_obj a)) (e.inverse.map η) hηpre
        (X.p.obj a) (adjointified_unit_inv_app_mixed_hom (C := C) e a) hηunit
    have hηfac :
        (e.inverse.map η ≫ adjointified_unit_inv_app_mixed_hom (C := C) e a) ≫ φ = ψX := by
      simpa [ψX] using
        pullback_factorization_of_map_factorization_mixed_hom (C := C) (e := e) φ hη.2
    have hηeq :
        e.inverse.map η ≫ adjointified_unit_inv_app_mixed_hom (C := C) e a = ξ :=
      hξuniq _ ⟨hηpull, hηfac⟩
    have hpushη :
        η = e.counitIso.inv.app z ≫
          F.map (e.inverse.map η ≫ adjointified_unit_inv_app_mixed_hom (C := C) e a) := by
      symm
      simpa [Functor.map_comp, Category.assoc] using
        pushforward_pullback_eq_mixed_hom (C := C) (e := e) η
    have hstepη :
        e.counitIso.inv.app z ≫
          F.map (e.inverse.map η ≫ adjointified_unit_inv_app_mixed_hom (C := C) e a) =
          e.counitIso.inv.app z ≫ F.map ξ := by
      simpa using congrArg (fun k ↦ e.counitIso.inv.app z ≫ F.map k) hηeq
    exact hpushη.trans <| hstepη.trans rfl

/-- Helper for Lemma 8.4.4: explicit equivalence-over-base data transport fibredness forward in
the mixed-hom setting by transporting a strongly cartesian lift and composing with the vertical
counit component. -/
private theorem isFibered_of_equivalence_data_mixed_hom
    {X : BasedCategory.{v₂, u₂} C} {Y : BasedCategory.{v₃, u₃} C}
    {F : X ⥤ᵇ Y} (e : EquivalenceOverBase F) :
    X.p.IsFibered → Y.p.IsFibered := by
  intro hX
  -- Use the strongly-cartesian lift criterion on the target and solve each lifting problem by
  -- transporting a chosen source cartesian lift across the equivalence data.
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro y V f
  letI : X.p.IsFibered := hX
  obtain ⟨x, φ, hφcart⟩ := IsPreFibered.exists_isCartesian X.p (e.inverse.w_obj y) f
  letI : X.p.IsCartesian f φ := hφcart
  have hφstrong : X.p.IsStronglyCartesian f φ :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian X.p f φ
  have hφowner : X.p.IsStronglyCartesian (X.p.map φ) φ := by
    letI : X.p.IsStronglyCartesian f φ := hφstrong
    exact isStronglyCartesian_rebase_over_target_eq (p := X.p) (hb := e.inverse.w_obj y)
      (f := f) φ
  have hFφstrong_owner :
      Y.p.IsStronglyCartesian (Y.p.map (F.map φ)) (F.map φ) := by
    exact preservesStronglyCartesian_of_equivalence_data_mixed_hom (C := C) (e := e) φ hφowner
  have hFφlift : Y.p.IsHomLift f (F.map φ) :=
    (F.isHomLift_iff f φ).2 (show X.p.IsHomLift f φ from inferInstance)
  have hFφstrong : Y.p.IsStronglyCartesian f (F.map φ) := by
    letI : Y.p.IsStronglyCartesian (Y.p.map (F.map φ)) (F.map φ) := hFφstrong_owner
    letI : Y.p.IsHomLift f (F.map φ) := hFφlift
    exact isStronglyCartesian_of_external_hom_lift (p := Y.p) (f := f) (φ := F.map φ)
  have hεlift : Y.p.IsHomLift (𝟙 (Y.p.obj y)) (e.counitIso.hom.app y) := by
    simpa using BasedNatTrans.isHomLift e.counitIso.hom (rfl : Y.p.obj y = Y.p.obj y)
  have hεstrong : Y.p.IsStronglyCartesian (𝟙 (Y.p.obj y)) (e.counitIso.hom.app y) := by
    let epsIso := (BasedNatTrans.forgetful Y Y).mapIso e.counitIso
    refine
      { toIsHomLift := hεlift
        universal_property' := ?_ }
    intro z g τ hτ
    -- Any lifting problem through the vertical counit is solved by composing with its inverse.
    let χ : z ⟶ F.obj (e.inverse.obj y) := τ ≫ e.counitIso.inv.app y
    have hτ' : Y.p.IsHomLift g τ := by
      simpa using hτ
    have hεinv : Y.p.IsHomLift (𝟙 (Y.p.obj y)) (e.counitIso.inv.app y) := by
      simpa using BasedNatTrans.isHomLift e.counitIso.inv (rfl : Y.p.obj y = Y.p.obj y)
    have hχ : Y.p.IsHomLift g χ := by
      exact @IsHomLift.comp_lift_id_right' _ _ _ _ Y.p _ _ _ _ _
        g τ hτ' (Y.p.obj y) (e.counitIso.inv.app y) hεinv
    refine ⟨χ, ⟨hχ, ?_⟩, ?_⟩
    · simpa [χ, epsIso, Category.assoc] using
        congrArg (fun k ↦ τ ≫ k) (epsIso.inv_hom_id_app y)
    · intro η hη
      have hηcomp :
          η = η ≫ e.counitIso.hom.app y ≫ e.counitIso.inv.app y := by
        rw [← Category.assoc]
        simpa [epsIso] using
          congrArg (fun k ↦ η ≫ k) (epsIso.hom_inv_id_app y).symm
      calc
        η = η ≫ e.counitIso.hom.app y ≫ e.counitIso.inv.app y := hηcomp
        _ = τ ≫ e.counitIso.inv.app y := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ e.counitIso.inv.app y) hη.2
        _ = χ := rfl
  let ψ : F.obj x ⟶ y := F.map φ ≫ e.counitIso.hom.app y
  have hψstrong : Y.p.IsStronglyCartesian f ψ := by
    let epsIso := (BasedNatTrans.forgetful Y Y).mapIso e.counitIso
    have hψlift : Y.p.IsHomLift f ψ := by
      simpa [ψ, Category.assoc] using
        @IsHomLift.comp_lift_id_right' _ _ _ _ Y.p _ _ _ _ _
          f (F.map φ) hFφlift (Y.p.obj y) (e.counitIso.hom.app y) hεlift
    refine
      { toIsHomLift := hψlift
        universal_property' := ?_ }
    intro z g τ hτ
    -- Cancel the vertical counit component on the right and then solve the remaining problem
    -- through the transported strongly cartesian lift `F.map φ`.
    let τ' : z ⟶ F.obj (e.inverse.obj y) := τ ≫ e.counitIso.inv.app y
    have hτ' : Y.p.IsHomLift (g ≫ f) τ' := by
      have hτlift : Y.p.IsHomLift (g ≫ f) τ := by
        simpa using hτ
      have hεinv : Y.p.IsHomLift (𝟙 (Y.p.obj y)) (e.counitIso.inv.app y) := by
        simpa using BasedNatTrans.isHomLift e.counitIso.inv (rfl : Y.p.obj y = Y.p.obj y)
      simpa [τ'] using
        @IsHomLift.comp_lift_id_right' _ _ _ _ Y.p _ _ _ _ _
          (g ≫ f) τ hτlift (Y.p.obj y) (e.counitIso.inv.app y) hεinv
    letI : Y.p.IsStronglyCartesian f (F.map φ) := hFφstrong
    letI : Y.p.IsHomLift (g ≫ f) τ' := hτ'
    obtain ⟨χ, hχ, hχuniq⟩ :=
      Functor.IsStronglyCartesian.universal_property Y.p f (F.map φ) g (g ≫ f) rfl τ'
    refine ⟨χ, ⟨hχ.1, ?_⟩, ?_⟩
    · have hτcancel : τ' ≫ e.counitIso.hom.app y = τ := by
        calc
          τ' ≫ e.counitIso.hom.app y
              = τ ≫ (e.counitIso.inv.app y ≫ e.counitIso.hom.app y) := by
                  simp [τ', Category.assoc]
          _ = τ := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ τ ≫ k) (epsIso.inv_hom_id_app y)
      have hχψ : χ ≫ ψ = τ' ≫ e.counitIso.hom.app y := by
        calc
          χ ≫ ψ = (χ ≫ F.map φ) ≫ e.counitIso.hom.app y := by
              simp [ψ, Category.assoc]
          _ = τ' ≫ e.counitIso.hom.app y := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ k ≫ e.counitIso.hom.app y) hχ.2
      exact hχψ.trans (by simpa using hτcancel)
    · intro η hη
      have hηcancel : (η ≫ ψ) ≫ e.counitIso.inv.app y = η ≫ F.map φ := by
        calc
          (η ≫ ψ) ≫ e.counitIso.inv.app y
              = η ≫ F.map φ ≫ (e.counitIso.hom.app y ≫ e.counitIso.inv.app y) := by
                  simp [ψ, Category.assoc]
          _ = η ≫ F.map φ := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ η ≫ F.map φ ≫ k) (epsIso.hom_inv_id_app y)
      have hηfac : η ≫ F.map φ = τ' := by
        have hηstep2 : (η ≫ ψ) ≫ e.counitIso.inv.app y = τ ≫ e.counitIso.inv.app y := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ k ≫ e.counitIso.inv.app y) hη.2
        have hηstep3 : τ ≫ e.counitIso.inv.app y = τ' := by
          simpa [τ']
        exact hηcancel.symm.trans (hηstep2.trans hηstep3)
      exact hχuniq _ ⟨hη.1, hηfac⟩
  exact ⟨F.obj x, ψ, hψstrong⟩

/-- Helper for Lemma 8.4.4: once the source projection is known to be fibred, an equivalence over
the base transports that fibredness to the target projection. -/
private theorem fibered_target_of_equivalence_over_base
    [p₁.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase) :
    p₂.IsFibered := by
  let e : EquivalenceOverBase F := Classical.choice hF.nonempty
  -- Use the localized mixed-hom transport theorem instead of forcing a same-universe wrapper.
  exact
    isFibered_of_equivalence_data_mixed_hom (C := C) (e := e)
      (show p₁.IsFibered from inferInstance)

/-- Helper for Lemma 8.4.4: choose a quasi-inverse for an equivalence over the base once and for
all so the remaining coverwise comparison can reuse stable notation. -/
private noncomputable abbrev inverse_of_equivalence_over_base
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase) :
    BasedCategory.ofFunctor p₂ ⥤ᵇ BasedCategory.ofFunctor p₁ :=
  (Classical.choice hF.nonempty).inverse

/-- Helper for Lemma 8.4.4: the chosen quasi-inverse is again an equivalence over the base. This
is the reverse-direction datum needed in the fixed-cover comparison. -/
private theorem inverse_isEquivalenceOverBase_of_equivalence_over_base
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase) :
    (inverse_of_equivalence_over_base (p₁ := p₁) (p₂ := p₂) F hF).IsEquivalenceOverBase := by
  let e : EquivalenceOverBase F := Classical.choice hF.nonempty
  simpa [inverse_of_equivalence_over_base] using e.inverse_isEquivalenceOverBase

/-- Helper for Lemma 8.4.4: every fiber functor induced by an equivalence over the base is an
equivalence of categories. This is the fiberwise input for the remaining descent-data transport. -/
private theorem fiberFunctor_isEquivalence_of_equivalence_over_base
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase) (U : C) :
    (F.fiberFunctor U).IsEquivalence := by
  -- Each fiber equivalence is part of the public Chapter 4 transport API.
  exact BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase F hF U

/-- Helper for Lemma 8.4.4: each induced fiber functor is fully faithful, so fixed-cover descent
comparisons can transport morphism components objectwise once the object part is defined. -/
private theorem fiberFunctor_fullyFaithful_of_equivalence_over_base
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase) (U : C) :
    Nonempty (Functor.Full (F.fiberFunctor U)) ∧
      Nonempty (Functor.Faithful (F.fiberFunctor U)) := by
  -- Extract fullness and faithfulness from the already available equivalence on the fiber over
  -- `U`.
  let _ : (F.fiberFunctor U).IsEquivalence :=
    fiberFunctor_isEquivalence_of_equivalence_over_base (p₁ := p₁) (p₂ := p₂) F hF U
  exact
    ⟨⟨inferInstance⟩, ⟨inferInstance⟩⟩

/-- Helper for Lemma 8.4.4: the chosen inverse also induces equivalences on all fibers. This
supplies the backward fiberwise comparison for the remaining descent-data transport. -/
private theorem inverse_fiberFunctor_isEquivalence_of_equivalence_over_base
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase) (U : C) :
    ((inverse_of_equivalence_over_base (p₁ := p₁) (p₂ := p₂) F hF).fiberFunctor U).IsEquivalence := by
  -- The reverse fiber equivalence comes from the chosen quasi-inverse over the base.
  exact
    BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase
      (inverse_of_equivalence_over_base (p₁ := p₁) (p₂ := p₂) F hF)
      (inverse_isEquivalenceOverBase_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF) U

/-- Helper for Lemma 8.4.4: the chosen inverse is also fully faithful on every fiber, so the
backward half of the fixed-cover descent-data comparison can use the same objectwise transport. -/
private theorem inverse_fiberFunctor_fullyFaithful_of_equivalence_over_base
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase) (U : C) :
    Nonempty
        (Functor.Full
          ((inverse_of_equivalence_over_base (p₁ := p₁) (p₂ := p₂) F hF).fiberFunctor U)) ∧
      Nonempty
        (Functor.Faithful
          ((inverse_of_equivalence_over_base (p₁ := p₁) (p₂ := p₂) F hF).fiberFunctor U)) := by
  -- Extract fullness and faithfulness from the inverse equivalence on the fiber over `U`.
  let _ :
      ((inverse_of_equivalence_over_base (p₁ := p₁) (p₂ := p₂) F hF).fiberFunctor U).IsEquivalence :=
    inverse_fiberFunctor_isEquivalence_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF U
  exact ⟨⟨inferInstance⟩, ⟨inferInstance⟩⟩

/-- Helper for Lemma 8.4.4: an equivalence over the base preserves strongly cartesian morphisms in
the owner form needed to build a fibred-category morphism from a based functor. -/
private theorem basedFunctor_preservesStronglyCartesian_of_equivalence_over_base
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase) :
    F.PreservesStronglyCartesian := by
  let e : EquivalenceOverBase F := Classical.choice hF.nonempty
  -- Route correction: use the mixed-hom transport proof directly rather than searching for a
  -- same-universe wrapper theorem.
  exact preservesStronglyCartesian_of_equivalence_data_mixed_hom (C := C) e

/-- Helper for Lemma 8.4.4: an equivalence over the base sends a chosen strongly cartesian lift
over `f` to a strongly cartesian lift over the same arrow `f`. -/
private theorem basedFunctor_map_stronglyCartesian_of_lift
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {a b : S₁} {U V : C} (f : V ⟶ U) (φ : a ⟶ b)
    (hφ : p₁.IsStronglyCartesian f φ) :
    p₂.IsStronglyCartesian f (F.map φ) := by
  -- First rewrite the source lift into owner form, transport strong cartesianness across the
  -- equivalence, and then rewrite the target back over the original base arrow `f`.
  have hφ' : p₁.IsStronglyCartesian (p₁.map φ) φ := by
    subst_hom_lift p₁ f φ
    simpa using hφ
  have hFφ :
      p₂.IsStronglyCartesian (p₂.map (F.map φ)) (F.map φ) :=
    basedFunctor_preservesStronglyCartesian_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF φ hφ'
  have hLift : p₂.IsHomLift f (F.map φ) :=
    (F.isHomLift_iff f φ).2 hφ.toIsHomLift
  letI : p₂.IsStronglyCartesian (p₂.map (F.map φ)) (F.map φ) := hFφ
  letI : p₂.IsHomLift f (F.map φ) := hLift
  exact isStronglyCartesian_of_external_hom_lift (p := p₂) (f := f) (φ := F.map φ)

/-- Helper for Lemma 8.4.4: the canonical pullback functor on fibers is characterized by the
fact that its image factors through the chosen strongly cartesian pullback arrows. -/
private theorem canonical_pullbackFunctor_map_fac
    {S : Type u₂} [Category.{v₂} S] (p : S ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) {x y : p.Fiber U} (φ : x ⟶ y) :
    ((((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map φ)).1 ≫
        (canonicalPullbackChoice p).map f y =
      (canonicalPullbackChoice p).map f x ≫ φ.1 := by
  -- Compare the chosen pullback arrow of `y` with the universal morphism induced by `φ`.
  letI : p.IsHomLift (𝟙 U) φ.1 := φ.2
  have hpull : p.IsStronglyCartesian f ((canonicalPullbackChoice p).map f x) :=
    (canonicalPullbackChoice p).isStronglyCartesian f x
  letI : p.IsHomLift f ((canonicalPullbackChoice p).map f x) := hpull.toIsHomLift
  letI : p.IsHomLift f ((canonicalPullbackChoice p).map f x ≫ φ.1) :=
    IsHomLift.comp_lift_id_right' p f ((canonicalPullbackChoice p).map f x) U φ.1
  letI : p.IsStronglyCartesian f ((canonicalPullbackChoice p).map f y) :=
    (canonicalPullbackChoice p).isStronglyCartesian f y
  -- The universal property of the chosen pullback of `y` forces the factorization identity.
  change
      IsStronglyCartesian.map p f ((canonicalPullbackChoice p).map f y)
        (Category.id_comp f).symm
        ((canonicalPullbackChoice p).map f x ≫ φ.1) ≫
          (canonicalPullbackChoice p).map f y =
        (canonicalPullbackChoice p).map f x ≫ φ.1
  simpa using
    (IsStronglyCartesian.fac p f ((canonicalPullbackChoice p).map f y)
      (Category.id_comp f).symm
      ((canonicalPullbackChoice p).map f x ≫ φ.1))

/-- Helper for Lemma 8.4.4: an equivalence over the base identifies pulling back after applying
`F` with applying `F` after pulling back. This is the mixed-universe replacement for
`FibredCategoryMor.pullbackComparison`. -/
private noncomputable def basedFunctor_pullbackComparison_of_equivalence_over_base
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    f ^*[canonicalPullbackChoice p₂] ((F.fiberFunctor U).obj x) ≅
      (F.fiberFunctor V).obj (f ^*[canonicalPullbackChoice p₁] x) := by
  let hc₁ := canonicalPullbackChoice p₁
  let hc₂ := canonicalPullbackChoice p₂
  -- Compare the two standard pullbacks of `F(x)` over `f` using the transported strongly
  -- cartesian structure on `F.map (hc₁.map f x)`.
  let φ :
      ((F.fiberFunctor V).obj (f ^*[hc₁] x)).1 ⟶
        ((F.fiberFunctor U).obj x).1 :=
    F.map (hc₁.map f x)
  let ψ :
      (f ^*[hc₂] ((F.fiberFunctor U).obj x)).1 ⟶
        ((F.fiberFunctor U).obj x).1 :=
    hc₂.map f ((F.fiberFunctor U).obj x)
  have hφ : p₂.IsStronglyCartesian f φ := by
    simpa [φ] using
      basedFunctor_map_stronglyCartesian_of_lift
        (p₁ := p₁) (p₂ := p₂) F hF f (hc₁.map f x) (hc₁.isStronglyCartesian f x)
  have hψ : p₂.IsStronglyCartesian f ψ :=
    hc₂.isStronglyCartesian f ((F.fiberFunctor U).obj x)
  have hf : f = (Iso.refl V).hom ≫ f := by
    simp
  let e :
      (f ^*[hc₂] ((F.fiberFunctor U).obj x)).1 ≅
        ((F.fiberFunctor V).obj (f ^*[hc₁] x)).1 :=
    domainIsoOfBaseIso p₂ hf φ ψ
  letI : p₂.IsHomLift (𝟙 V) e.hom := by
    change p₂.IsHomLift (Iso.refl V).hom e.hom
    exact domainUniqueUpToIso_inv_isHomLift p₂ hf φ ψ
  letI : p₂.IsHomLift (𝟙 V) e.inv := by
    change p₂.IsHomLift (Iso.refl V).inv e.inv
    exact domainUniqueUpToIso_hom_isHomLift p₂ hf φ ψ
  refine
    { hom := Functor.Fiber.homMk p₂ V e.hom
      inv := Functor.Fiber.homMk p₂ V e.inv
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        change e.hom ≫ e.inv = 𝟙 _
        exact e.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        change e.inv ≫ e.hom = 𝟙 _
        exact e.inv_hom_id }

/-- Helper for Lemma 8.4.4: the pullback-comparison isomorphism for an equivalence over the base
intertwines pullback of vertical morphisms with the image of the pulled-back morphism after
forgetting to the total categories. -/
private theorem canonical_pullbackFunctor_map_isHomLift_identity
    {S : Type u₂} [Category.{v₂} S] (p : S ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) {x y : p.Fiber U} (φ : x ⟶ y) :
    p.IsHomLift (𝟙 V)
      ((((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map φ)).1 := by
  -- A pullback functor on fibers always sends a vertical morphism to a vertical morphism.
  exact (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map φ).2

/-- Helper for Lemma 8.4.4: the pullback-comparison isomorphism itself is vertical over the
identity on the pullback base. -/
private theorem basedFunctor_pullbackComparison_hom_isHomLift_identity
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    p₂.IsHomLift (𝟙 V)
      (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF f x).hom.1 := by
  -- The comparison isomorphism lives inside the fiber over `V`, so its underlying morphism is
  -- vertical.
  exact
    (basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF f x).hom.2

/-- Helper for Lemma 8.4.4: mapping the canonical pullback factorization identity along `F`
preserves the same comparison in the total category. -/
private theorem basedFunctor_map_canonical_pullbackFunctor_map_fac
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (φ : x ⟶ y) :
    F.map ((canonicalPullbackChoice p₁).map f x) ≫ F.map φ.1 =
      F.map ((((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.map φ)).1 ≫
        F.map ((canonicalPullbackChoice p₁).map f y) := by
  -- Map the source pullback factorization identity termwise, then normalize with
  -- functoriality of composition.
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg F.map (canonical_pullbackFunctor_map_fac (p := p₁) f φ).symm

/-- Helper for Lemma 8.4.4: the underlying comparison morphism is characterized by the same
postcomposition identity as the canonical domain-comparison map between strongly cartesian
pullbacks. -/
private theorem basedFunctor_pullbackComparison_hom_postcompose
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    (basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF f x).hom.1 ≫
        F.map ((canonicalPullbackChoice p₁).map f x) =
      (canonicalPullbackChoice p₂).map f ((F.fiberFunctor U).obj x) := by
  let hc₁ := canonicalPullbackChoice p₁
  let hc₂ := canonicalPullbackChoice p₂
  let φ :
      ((F.fiberFunctor V).obj (f ^*[hc₁] x)).1 ⟶
        ((F.fiberFunctor U).obj x).1 :=
    F.map (hc₁.map f x)
  let ψ :
      (f ^*[hc₂] ((F.fiberFunctor U).obj x)).1 ⟶
        ((F.fiberFunctor U).obj x).1 :=
    hc₂.map f ((F.fiberFunctor U).obj x)
  have hφ : p₂.IsStronglyCartesian f φ := by
    -- Transport the chosen source pullback lift across the equivalence over the base.
    simpa [φ, hc₁] using
      basedFunctor_map_stronglyCartesian_of_lift
        (p₁ := p₁) (p₂ := p₂) F hF f (hc₁.map f x) (hc₁.isStronglyCartesian f x)
  have hψ : p₂.IsStronglyCartesian f ψ := by
    -- The target canonical pullback arrow is strongly cartesian by construction.
    simpa [ψ, hc₂] using hc₂.isStronglyCartesian f ((F.fiberFunctor U).obj x)
  have hf : f = (Iso.refl V).hom ≫ f := by
    simp
  -- Forget the fiber wrapper and identify the comparison morphism with the canonical map into
  -- the chosen target pullback object.
  change (Functor.IsStronglyCartesian.domainIsoOfBaseIso p₂ hf φ ψ).hom ≫ φ = ψ
  rw [Functor.IsStronglyCartesian.domainIsoOfBaseIso_hom]
  simpa [Functor.IsStronglyCartesian.fac]

/-- Helper for Lemma 8.4.4: after postcomposing both candidate composites with the chosen
strongly cartesian pullback arrow on `F(y)`, the two total-category composites agree. This is the
rewrite-stable core of the pullback-comparison naturality square. -/
private theorem basedFunctor_pullbackComparison_hom_postcompose_eq
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (φ : x ⟶ y) :
    ((((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.map
        ((F.fiberFunctor U).map φ))).1 ≫
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF f y).hom.1 ≫
        F.map ((canonicalPullbackChoice p₁).map f y) =
      ((basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF f x).hom.1 ≫
          ((F.fiberFunctor V).map
            (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.map φ)).1) ≫
        F.map ((canonicalPullbackChoice p₁).map f y) := by
  -- Rewrite both sides through the canonical target pullback arrow, then compare the remaining
  -- source-side composites using functoriality of `F` on the pullback factorization identity.
  let lhs :=
    ((((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.map
        ((F.fiberFunctor U).map φ))).1 ≫
      (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF f y).hom.1 ≫
      F.map ((canonicalPullbackChoice p₁).map f y)
  let mid₁ :=
    ((((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.map
        ((F.fiberFunctor U).map φ))).1 ≫
      (canonicalPullbackChoice p₂).map f ((F.fiberFunctor U).obj y)
  let mid₂ :=
    (canonicalPullbackChoice p₂).map f ((F.fiberFunctor U).obj x) ≫
      ((F.fiberFunctor U).map φ).1
  let mid₃ :=
    ((basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF f x).hom.1 ≫
      F.map ((canonicalPullbackChoice p₁).map f x)) ≫ ((F.fiberFunctor U).map φ).1
  let mid₄ :=
    (basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF f x).hom.1 ≫
      ((F.fiberFunctor V).map
        (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.map φ)).1 ≫
      F.map ((canonicalPullbackChoice p₁).map f y)
  let rhs :=
    ((basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF f x).hom.1 ≫
        ((F.fiberFunctor V).map
          (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.map φ)).1) ≫
      F.map ((canonicalPullbackChoice p₁).map f y)
  have h₁ : lhs = mid₁ := by
    -- First replace the comparison isomorphism at `y` by the canonical target pullback arrow.
    dsimp [lhs, mid₁]
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          ((((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.map
              ((F.fiberFunctor U).map φ))).1 ≫ k)
        (basedFunctor_pullbackComparison_hom_postcompose
          (p₁ := p₁) (p₂ := p₂) F hF f y)
  have h₂ : mid₁ = mid₂ := by
    -- The target pullback functor factors through the chosen strongly cartesian arrow.
    dsimp [mid₁, mid₂]
    simpa using
      canonical_pullbackFunctor_map_fac (p := p₂) f ((F.fiberFunctor U).map φ)
  have h₃ : mid₂ = mid₃ := by
    -- Rewrite the canonical target pullback arrow at `x` back through the comparison isomorphism.
    dsimp [mid₂, mid₃]
    show
      (canonicalPullbackChoice p₂).map f ((F.fiberFunctor U).obj x) ≫
          ((F.fiberFunctor U).map φ).1 =
        ((basedFunctor_pullbackComparison_of_equivalence_over_base
            (p₁ := p₁) (p₂ := p₂) F hF f x).hom.1 ≫
            F.map ((canonicalPullbackChoice p₁).map f x)) ≫
          ((F.fiberFunctor U).map φ).1
    exact
      (congrArg
        (fun k ↦ k ≫ ((F.fiberFunctor U).map φ).1)
        (basedFunctor_pullbackComparison_hom_postcompose
          (p₁ := p₁) (p₂ := p₂) F hF f x)).symm
  have h₄ : mid₃ = mid₄ := by
    -- Map the source pullback factorization identity along `F` and postcompose by the comparison.
    dsimp [mid₃, mid₄]
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          (basedFunctor_pullbackComparison_of_equivalence_over_base
            (p₁ := p₁) (p₂ := p₂) F hF f x).hom.1 ≫ k)
        (basedFunctor_map_canonical_pullbackFunctor_map_fac
          (p₁ := p₁) (p₂ := p₂) F f φ)
  have h₅ : mid₄ = rhs := by
    -- Reassociate the right-hand composite into the form used by the naturality statement.
    dsimp [mid₄, rhs]
    simp [Category.assoc]
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-- Helper for Lemma 8.4.4: the pullback-comparison isomorphism for an equivalence over the base
intertwines pullback of vertical morphisms with the image of the pulled-back morphism after
forgetting to the total categories. -/
private theorem basedFunctor_pullbackComparison_hom_naturality_over_vertical
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (φ : x ⟶ y) :
    ((((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.map
        ((F.fiberFunctor U).map φ))).1 ≫
      (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF f y).hom.1 =
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF f x).hom.1 ≫
          ((F.fiberFunctor V).map
            (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.map φ)).1 := by
  -- Route correction: compare the two candidate arrows in the total category first, and only
  -- then lift the equality back to the fiber category.
  let e :
      f ^*[canonicalPullbackChoice p₂] ((F.fiberFunctor U).obj x) ≅
        (F.fiberFunctor V).obj (f ^*[canonicalPullbackChoice p₁] x) :=
    basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF f x
  let e' :
      f ^*[canonicalPullbackChoice p₂] ((F.fiberFunctor U).obj y) ≅
        (F.fiberFunctor V).obj (f ^*[canonicalPullbackChoice p₁] y) :=
    basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF f y
  let η :
      ((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.obj
          ((F.fiberFunctor U).obj x) ⟶
        ((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.obj
          ((F.fiberFunctor U).obj y) :=
    ((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.map
      ((F.fiberFunctor U).map φ)
  let θ :
      (F.fiberFunctor V).obj
          (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj x) ⟶
        (F.fiberFunctor V).obj
          (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.obj y) :=
    (F.fiberFunctor V).map
      (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.map φ)
  let hc₁ := canonicalPullbackChoice p₁
  let φF :
      ((F.fiberFunctor V).obj (f ^*[hc₁] y)).1 ⟶ ((F.fiberFunctor U).obj y).1 :=
    F.map (hc₁.map f y)
  have hφF : p₂.IsStronglyCartesian f φF := by
    simpa [φF, hc₁] using
      basedFunctor_map_stronglyCartesian_of_lift
        (p₁ := p₁) (p₂ := p₂) F hF f (hc₁.map f y) (hc₁.isStronglyCartesian f y)
  letI : p₂.IsStronglyCartesian f φF := hφF
  letI : p₂.IsHomLift (𝟙 V) η.1 :=
    canonical_pullbackFunctor_map_isHomLift_identity (p := p₂) f ((F.fiberFunctor U).map φ)
  letI : p₂.IsHomLift (𝟙 V) θ.1 := θ.2
  letI : p₂.IsHomLift (𝟙 V) e.hom.1 := e.hom.2
  letI : p₂.IsHomLift (𝟙 V) e'.hom.1 := e'.hom.2
  letI : p₂.IsHomLift (𝟙 V) (η.1 ≫ e'.hom.1) := by
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ p₂ _ _ _ _ _
      (𝟙 V) η.1
      (canonical_pullbackFunctor_map_isHomLift_identity (p := p₂) f ((F.fiberFunctor U).map φ))
      V e'.hom.1 e'.hom.2
  letI : p₂.IsHomLift (𝟙 V) (e.hom.1 ≫ θ.1) := by
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ p₂ _ _ _ _ _
      (𝟙 V) e.hom.1 e.hom.2
      V θ.1 θ.2
  -- The postcomposition equality now fits the owner-level extensionality principle for the
  -- chosen strongly cartesian pullback arrow `φF`.
  have hcomp :
      η.1 ≫ e'.hom.1 ≫ φF = (e.hom.1 ≫ θ.1) ≫ φF := by
    simpa [η, θ, hc₁, φF, Category.assoc] using
      basedFunctor_pullbackComparison_hom_postcompose_eq
        (p₁ := p₁) (p₂ := p₂) F hF f φ
  have hηe' : p₂.IsHomLift (𝟙 V) (η.1 ≫ e'.hom.1) := by infer_instance
  have heθ : p₂.IsHomLift (𝟙 V) (e.hom.1 ≫ θ.1) := by infer_instance
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ p₂ _ _ _ _
      f φF inferInstance _ _ (𝟙 V) (η.1 ≫ e'.hom.1) (e.hom.1 ≫ θ.1) hηe' heθ <| by
        simpa [Category.assoc] using hcomp

/-- Helper for Lemma 8.4.4: the pullback-comparison isomorphism for an equivalence over the base
intertwines pullback of vertical morphisms with the image of the pulled-back morphism. -/
private theorem basedFunctor_pullbackComparison_naturality_over_vertical
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (φ : x ⟶ y) :
    (((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.map
        ((F.fiberFunctor U).map φ)) ≫
      (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF f y).hom =
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF f x).hom ≫
          (F.fiberFunctor V).map
            (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.map φ) := by
  -- Reduce the fiber statement to the underlying-total-category equality proved just above.
  apply Functor.Fiber.hom_ext
  exact
    basedFunctor_pullbackComparison_hom_naturality_over_vertical
      (p₁ := p₁) (p₂ := p₂) F hF f φ

/-- Helper for Lemma 8.4.4: for a fixed cover arrow, the pullback-comparison isomorphism already
has the exact cover-indexed naturality square needed later when packaging canonical descent data
componentwise. -/
private theorem cover_arrow_pullbackComparison_naturality_over_vertical
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U) {I : S.Arrow} {x y : p₁.Fiber U} (φ : x ⟶ y) :
    (((canonicalFiberPseudofunctor p₂).map I.f.op.toLoc).toFunctor.map
        ((F.fiberFunctor U).map φ)) ≫
      (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF I.f y).hom =
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF I.f x).hom ≫
          (F.fiberFunctor I.Y).map
            (((canonicalFiberPseudofunctor p₁).map I.f.op.toLoc).toFunctor.map φ) := by
  -- This is exactly the general vertical naturality theorem specialized to the chosen cover
  -- member `I`.
  simpa using
    basedFunctor_pullbackComparison_naturality_over_vertical
      (p₁ := p₁) (p₂ := p₂) F hF I.f φ

/-- Helper for Lemma 8.4.4: once a fixed-cover transport functor on descent data is known to be
an equivalence and to compare the two canonical descent functors up to whiskering by the fiber
equivalence over `U`, the equivalence condition on the canonical descent functor cancels across
that comparison. -/
private theorem coverwise_canonicalDescentFunctor_isEquivalence_iff_of_transport
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U)
    (TF :
      ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f)) ⥤
        ((canonicalFiberPseudofunctor p₂).DescentData (fun I : S.Arrow ↦ I.f)))
    [TF.IsEquivalence]
    (e :
      ((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)) ⋙ TF ≅
        (F.fiberFunctor U) ⋙
          ((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f))) :
    ((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)).IsEquivalence ↔
      ((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f)).IsEquivalence := by
  letI fiberEquivU :
      (F.fiberFunctor U).IsEquivalence :=
    fiberFunctor_isEquivalence_of_equivalence_over_base (p₁ := p₁) (p₂ := p₂) F hF U
  constructor
  · intro h₁
    -- Compose the source descent functor with the transport equivalence, then cancel the
    -- fiberwise equivalence on the left of the comparison isomorphism.
    letI :
        ((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)).IsEquivalence := h₁
    have hsrcComp :
        (((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)) ⋙ TF).IsEquivalence :=
      Functor.isEquivalence_trans
        ((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)) TF
    have hcomp :
        ((F.fiberFunctor U) ⋙ ((canonicalFiberPseudofunctor p₂).toDescentData
          (fun I : S.Arrow ↦ I.f))).IsEquivalence :=
      (Functor.isEquivalence_iff_of_iso e).1 hsrcComp
    letI :
        ((F.fiberFunctor U) ⋙ ((canonicalFiberPseudofunctor p₂).toDescentData
          (fun I : S.Arrow ↦ I.f))).IsEquivalence := hcomp
    exact
      Functor.isEquivalence_of_comp_left (F.fiberFunctor U)
        ((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f))
  · intro h₂
    -- Reverse the same cancellation argument: first whisker by the fiber equivalence over `U`,
    -- then transport back across `TF`.
    have htargetComp :
        ((F.fiberFunctor U) ⋙ ((canonicalFiberPseudofunctor p₂).toDescentData
          (fun I : S.Arrow ↦ I.f))).IsEquivalence := by
      exact
        @Functor.isEquivalence_trans _ _ _ _ _ _
          (F.fiberFunctor U)
          ((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f))
          fiberEquivU h₂
    have hcomp :
        (((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)) ⋙ TF).IsEquivalence :=
      (Functor.isEquivalence_iff_of_iso e).2 htargetComp
    letI :
        (((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)) ⋙ TF).IsEquivalence := hcomp
    exact
      Functor.isEquivalence_of_comp_right
        ((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)) TF

/-- Helper for Lemma 8.4.4: for a fixed cover, transport one descent morphism by conjugating it
with the pullback-comparison isomorphisms coming from the equivalence over the base. -/
private noncomputable def cover_descent_data_transport_hom_of_equivalence_over_base
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor p₂).map f₁.op.toLoc).toFunctor.obj
        ((F.fiberFunctor I₁.Y).obj (D.obj I₁))) ⟶
      (((canonicalFiberPseudofunctor p₂).map f₂.op.toLoc).toFunctor.obj
        ((F.fiberFunctor I₂.Y).obj (D.obj I₂))) := by
  -- Route correction: fix the conjugation normal form first so the remaining descent-data laws
  -- can rewrite to one stable comparison term instead of reopening transport coercions each time.
  simpa using
    (basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF f₁ (D.obj I₁)).hom ≫
      (F.fiberFunctor Y).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
      (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF f₂ (D.obj I₂)).inv

/-- Helper for Lemma 8.4.4: the inverse pullback-comparison isomorphism rewrites the right-hand
comparison inverse into a form that can be consumed by `rw` in the fixed-cover transport proofs. -/
private theorem basedFunctor_pullbackComparison_inv_naturality_over_vertical
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (φ : x ⟶ y) :
    (F.fiberFunctor V).map
        (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.map φ) ≫
      (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF f y).inv =
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF f x).inv ≫
          (((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.map
            ((F.fiberFunctor U).map φ)) := by
  -- Move the left comparison hom across the known naturality square, then move the right
  -- comparison hom back to the other side to obtain the inverse-side rewrite.
  let ex :=
    basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF f x
  let ey :=
    basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF f y
  let η :=
    ((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.map
      ((F.fiberFunctor U).map φ)
  let θ :=
    (F.fiberFunctor V).map
      (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.map φ)
  have hhom :
      η ≫ ey.hom = ex.hom ≫ θ := by
    simpa [ex, ey, η, θ] using
      basedFunctor_pullbackComparison_naturality_over_vertical
        (p₁ := p₁) (p₂ := p₂) F hF f φ
  -- Move the right comparison hom back across the naturality square, then cancel the left
  -- comparison isomorphism in the resulting owner-level equality.
  symm
  apply (Iso.eq_comp_inv ey).2
  -- Expand the local abbreviations, then precompose the hom-side naturality square with
  -- `ex.inv` so that `ex.inv ≫ ex.hom` cancels on the right.
  have hhom' := hhom
  dsimp [η, θ] at hhom' ⊢
  have hpre :
      ex.inv ≫
          ((((canonicalFiberPseudofunctor p₂).map f.op.toLoc).toFunctor.map
              ((F.fiberFunctor U).map φ)) ≫ ey.hom) =
        ex.inv ≫
          (ex.hom ≫
            (F.fiberFunctor V).map
              (((canonicalFiberPseudofunctor p₁).map f.op.toLoc).toFunctor.map φ)) := by
    exact congrArg (fun k ↦ ex.inv ≫ k) hhom'
  simpa only [← Category.assoc, ex.inv_hom_id, Category.id_comp] using hpre

/-- Helper for Lemma 8.4.4: transporting an overlap map along the same cover leg on both sides
produces the identity morphism. -/
private theorem cover_descent_data_transport_hom_self_map_id
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I : S.Arrow} (g : Y ⟶ I.Y)
    (hg : g ≫ I.f = q := by cat_disch) :
    (F.fiberFunctor Y).map (D.hom q g g hg hg) =
      𝟙 ((F.fiberFunctor Y).obj
        (((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor.obj (D.obj I))) := by
  -- Rewrite the source overlap map to the identity and then map that identity through the fiber
  -- functor.
  calc
    (F.fiberFunctor Y).map (D.hom q g g hg hg)
        =
          (F.fiberFunctor Y).map
            (𝟙 (((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor.obj (D.obj I))) := by
              simpa using
                congrArg (fun k ↦ (F.fiberFunctor Y).map k) (D.hom_self q g hg)
    _ = 𝟙 ((F.fiberFunctor Y).obj
          (((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor.obj (D.obj I))) := by
          exact (F.fiberFunctor Y).map_id _

/-- Helper for Lemma 8.4.4: transporting an overlap map along the same cover leg on both sides
produces the identity morphism. -/
private theorem basedFunctor_pullbackComparison_hom_inv_id_normalized
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U Y : C} (g : Y ⟶ U) (x : p₁.Fiber U) :
    (basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF g x).hom ≫
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF g x).inv =
      𝟙 (((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.obj
        ((F.fiberFunctor U).obj x)) := by
  -- This is the exact cancellation shape needed after rewriting the middle transported overlap
  -- map to the identity.
  calc
    (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF g x).hom ≫
          (basedFunctor_pullbackComparison_of_equivalence_over_base
            (p₁ := p₁) (p₂ := p₂) F hF g x).inv =
        𝟙 (g ^*[canonicalPullbackChoice p₂] ((F.fiberFunctor U).obj x)) := by
          exact
            (basedFunctor_pullbackComparison_of_equivalence_over_base
              (p₁ := p₁) (p₂ := p₂) F hF g x).hom_inv_id
    _ = 𝟙 (((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.obj
          ((F.fiberFunctor U).obj x)) := by
          rfl

/-- Helper for Lemma 8.4.4: insert the explicit middle identity that appears after rewriting the
self-overlap descent morphism, without changing the pullback-comparison cancellation. -/
private theorem basedFunctor_pullbackComparison_hom_id_inv_normalized
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U Y : C} (g : Y ⟶ U) (x : p₁.Fiber U) :
    (basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF g x).hom ≫
        𝟙 ((F.fiberFunctor Y).obj
          (((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor.obj x)) ≫
        (basedFunctor_pullbackComparison_of_equivalence_over_base
          (p₁ := p₁) (p₂ := p₂) F hF g x).inv =
      𝟙 (((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.obj
        ((F.fiberFunctor U).obj x)) := by
  -- Reassociate away the inserted identity so the already normalized cancellation lemma applies
  -- to the literal displayed shape used in the self-overlap transport proof.
  let e :=
    basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF g x
  have hη :
      e.hom ≫
          𝟙 ((F.fiberFunctor Y).obj
            (((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor.obj x)) ≫
          e.inv =
        e.hom ≫ e.inv := by
    -- Move the inserted identity onto `e.inv`, then reassociate back to the displayed form.
    change e.hom ≫
        (𝟙 ((F.fiberFunctor Y).obj
          (((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor.obj x)) ≫ e.inv) =
      e.hom ≫ e.inv
    exact congrArg (fun k ↦ e.hom ≫ k) (Category.id_comp e.inv)
  have hcancel :
      e.hom ≫ e.inv =
        𝟙 (((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.obj
          ((F.fiberFunctor U).obj x)) := by
    simpa [e] using
      basedFunctor_pullbackComparison_hom_inv_id_normalized
        (p₁ := p₁) (p₂ := p₂) F hF g x
  exact hη.trans hcancel

/-- Helper for Lemma 8.4.4: after reassociating to the literal cocycle shape, the middle factor
`comparison.inv ≫ comparison.hom` can be canceled before postcomposing by the remaining tail. -/
private theorem basedFunctor_pullbackComparison_inv_hom_postcompose_normalized
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U Y : C} (g : Y ⟶ U) (x : p₁.Fiber U)
    {z : p₂.Fiber Y}
    (k :
      (F.fiberFunctor Y).obj
          (((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor.obj x) ⟶ z) :
    (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF g x).inv ≫
      (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF g x).hom ≫
      k = k := by
  -- Use the owner-level iso cancellation in the exact postcomposed shape that appears after the
  -- cocycle proof is reassociated.
  let e :=
    basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF g x
  simpa [e, Category.assoc] using Iso.inv_hom_id_assoc e k

/-- Helper for Lemma 8.4.4: transporting an overlap map along the same cover leg on both sides
produces the identity morphism. -/
private theorem cover_descent_data_transport_hom_self_normalize
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I : S.Arrow} (g : Y ⟶ I.Y)
    (hg : g ≫ I.f = q := by cat_disch) :
    cover_descent_data_transport_hom_of_equivalence_over_base
      (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D q g g hg hg = 𝟙 _ := by
  -- Route correction: normalize the self-overlap transport to the literal
  -- `comparison.hom ≫ 𝟙 ≫ comparison.inv` shape before canceling the comparison isomorphism.
  change
    (basedFunctor_pullbackComparison_of_equivalence_over_base
        (p₁ := p₁) (p₂ := p₂) F hF g (D.obj I)).hom ≫
          (F.fiberFunctor Y).map (D.hom q g g hg hg) ≫
          (basedFunctor_pullbackComparison_of_equivalence_over_base
            (p₁ := p₁) (p₂ := p₂) F hF g (D.obj I)).inv =
      𝟙 (((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.obj
        ((F.fiberFunctor I.Y).obj (D.obj I)))
  let e :=
    basedFunctor_pullbackComparison_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF g (D.obj I)
  have hself :
      (F.fiberFunctor Y).map (D.hom q g g hg hg) =
        𝟙 ((F.fiberFunctor Y).obj
          (((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor.obj (D.obj I))) :=
    cover_descent_data_transport_hom_self_map_id
      (p₁ := p₁) (p₂ := p₂) (J := J) F S D q g hg
  have hself_conj :
      e.hom ≫ (F.fiberFunctor Y).map (D.hom q g g hg hg) ≫ e.inv =
        e.hom ≫
          𝟙 ((F.fiberFunctor Y).obj
            (((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor.obj (D.obj I))) ≫
          e.inv := by
    -- Conjugate the source self-overlap identity by the comparison isomorphism.
    simpa [Category.assoc] using congrArg (fun k ↦ e.hom ≫ k ≫ e.inv) hself
  -- Collapse the source self-overlap morphism to the identity in the middle factor.
  calc
    e.hom ≫ (F.fiberFunctor Y).map (D.hom q g g hg hg) ≫ e.inv
        = e.hom ≫
            𝟙 ((F.fiberFunctor Y).obj
              (((canonicalFiberPseudofunctor p₁).map g.op.toLoc).toFunctor.obj (D.obj I))) ≫
            e.inv := hself_conj
    -- The remaining displayed composite is the exact cancellation wrapper proved just above.
    _ = 𝟙 (((canonicalFiberPseudofunctor p₂).map g.op.toLoc).toFunctor.obj
          ((F.fiberFunctor I.Y).obj (D.obj I))) := by
            simpa [e] using
              basedFunctor_pullbackComparison_hom_id_inv_normalized
                (p₁ := p₁) (p₂ := p₂) F hF g (D.obj I)

/-- Helper for Lemma 8.4.4: transporting the source cocycle relation through the comparison
isomorphisms yields the target cocycle relation for the fixed cover. -/
private theorem cover_descent_data_transport_hom_comp_normalize
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I₁ I₂ I₃ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (hf₃ : f₃ ≫ I₃.f = q := by cat_disch) :
    cover_descent_data_transport_hom_of_equivalence_over_base
        (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D q f₁ f₂ hf₁ hf₂ ≫
    cover_descent_data_transport_hom_of_equivalence_over_base
        (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D q f₂ f₃ hf₂ hf₃ =
      cover_descent_data_transport_hom_of_equivalence_over_base
        (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D q f₁ f₃ hf₁ hf₃ := by
  -- Rewrite all three overlap maps into the same comparison-conjugated normal form, cancel the
  -- middle comparison isomorphism with
  -- `basedFunctor_pullbackComparison_inv_hom_postcompose_normalized`, and then map the source
  -- cocycle identity through the fiber functor over `Y`.
  -- TODO: rewrite the two transport morphisms into the shared comparison-conjugated normal form,
  -- reassociate to the literal `comparison.inv ≫ comparison.hom ≫ _` shape, apply
  -- `basedFunctor_pullbackComparison_inv_hom_postcompose_normalized`, and then map `D.hom_comp`.
  sorry

/-- Helper for Lemma 8.4.4: the pullback compatibility for the transported overlap maps is the
remaining fixed-cover coherence obligation after the conjugation normal form is fixed. -/
private theorem cover_descent_data_transport_hom_pullHom_hom
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (hq : g ≫ q = q')
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (cover_descent_data_transport_hom_of_equivalence_over_base
          (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      cover_descent_data_transport_hom_of_equivalence_over_base
        (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D q' gf₁ gf₂
        (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
        (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) := by
  -- TODO: rewrite both sides with `map_eq_pullHom`, transport the comparison terms using
  -- `basedFunctor_pullbackComparison_naturality_over_vertical`, and finish with
  -- `D.pullHom_hom` on the middle overlap map.
  sorry

/-- Helper for Lemma 8.4.4: the component map of a morphism of descent data is compatible with
the transported overlap maps after conjugating by the pullback-comparison isomorphisms. -/
private theorem cover_descent_data_transport_functor_comm
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U)
    {D₁ D₂ : ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f))}
    (φ : D₁ ⟶ D₂)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor p₂).map f₁.op.toLoc).toFunctor.map
        ((F.fiberFunctor I₁.Y).map (φ.hom I₁))) ≫
      cover_descent_data_transport_hom_of_equivalence_over_base
        (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D₂ q f₁ f₂ hf₁ hf₂ =
      cover_descent_data_transport_hom_of_equivalence_over_base
        (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D₁ q f₁ f₂ hf₁ hf₂ ≫
        (((canonicalFiberPseudofunctor p₂).map f₂.op.toLoc).toFunctor.map
          ((F.fiberFunctor I₂.Y).map (φ.hom I₂))) := by
  -- TODO: rewrite both sides into the comparison-conjugated normal form, use `φ.comm` in the
  -- middle, and move the right comparison inverse with
  -- `basedFunctor_pullbackComparison_inv_naturality_over_vertical`.
  sorry

/-- Helper for Lemma 8.4.4: transport a fixed-cover descent datum objectwise along the given
equivalence over the base. -/
private noncomputable def cover_descent_data_transport_obj_of_equivalence_over_base
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U) :
    ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f)) →
      ((canonicalFiberPseudofunctor p₂).DescentData (fun I : S.Arrow ↦ I.f))
  | D =>
      { obj := fun I ↦ (F.fiberFunctor I.Y).obj (D.obj I)
        hom := fun Y q I₁ I₂ f₁ f₂ hf₁ hf₂ ↦
          cover_descent_data_transport_hom_of_equivalence_over_base
            (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D q f₁ f₂ hf₁ hf₂
        pullHom_hom := by
          intro Y' Y g q q' hq I₁ I₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
          -- Delegate the remaining pullback-compatibility field to the dedicated transport lemma.
          simpa using
            cover_descent_data_transport_hom_pullHom_hom
              (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D g q q' hq f₁ f₂ hf₁ hf₂
              gf₁ gf₂ hgf₁ hgf₂
        hom_self := by
          intro Y q I g hg
          -- Use the dedicated normalization lemma so the object constructor stays flat.
          simpa using
            cover_descent_data_transport_hom_self_normalize
              (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D q g hg
        hom_comp := by
          intro Y q I₁ I₂ I₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
          -- Use the dedicated cocycle transport lemma so the main object definition only records
          -- the source-faithful proof skeleton.
          simpa using
            cover_descent_data_transport_hom_comp_normalize
              (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D q f₁ f₂ f₃ hf₁ hf₂ hf₃ }

/-- Helper for Lemma 8.4.4: assemble the fixed-cover transport on descent data into a functor.
Only the componentwise morphism compatibility remains after the objectwise transport is fixed. -/
private noncomputable def cover_descent_data_transport_functor_of_equivalence_over_base
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U) :
    ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f)) ⥤
      ((canonicalFiberPseudofunctor p₂).DescentData (fun I : S.Arrow ↦ I.f)) where
  obj D :=
    cover_descent_data_transport_obj_of_equivalence_over_base
      (J := J) (p₁ := p₁) (p₂ := p₂) F hF S D
  map {D₁ D₂} φ :=
    { hom := fun I ↦ (F.fiberFunctor I.Y).map (φ.hom I)
      comm := by
        intro Y q I₁ I₂ f₁ f₂ hf₁ hf₂
        -- Invoke the dedicated conjugation compatibility lemma for morphisms of descent data.
        simpa using
          cover_descent_data_transport_functor_comm
            (J := J) (p₁ := p₁) (p₂ := p₂) F hF S φ q f₁ f₂ hf₁ hf₂ }
  map_id X := by
    -- The transport functor acts by the identity on each component because every fiber functor
    -- preserves identity morphisms.
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    change (F.fiberFunctor I.Y).map (𝟙 (X.obj I)) = 𝟙 ((F.fiberFunctor I.Y).obj (X.obj I))
    exact (F.fiberFunctor I.Y).map_id (X.obj I)
  map_comp f g := by
    -- Composition is computed objectwise since the transport functor maps each component through
    -- the corresponding fiber functor.
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    change (F.fiberFunctor I.Y).map (f.hom I ≫ g.hom I) =
      (F.fiberFunctor I.Y).map (f.hom I) ≫ (F.fiberFunctor I.Y).map (g.hom I)
    exact (F.fiberFunctor I.Y).map_comp (f.hom I) (g.hom I)

/-- Helper for Lemma 8.4.4: for a fixed cover, an equivalence over the base should transport the
equivalence of the canonical descent functor between the two fiber pseudofunctors. -/
private theorem coverwise_canonicalDescentFunctor_isEquivalence_iff_of_equivalence_over_base
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase)
    {U : C} (S : J.Cover U) :
    ((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)).IsEquivalence ↔
      ((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f)).IsEquivalence := by
  classical
  -- Route correction: the mixed-hom pullback comparison is already in place, so the remaining
  -- source-faithful step is to package the fixed-cover descent-data transport and then invoke the
  -- abstract cancellation lemma proved just above.
  let e : EquivalenceOverBase F := Classical.choice hF.nonempty
  let G := e.inverse
  let _i := e.counitIso
  let _j := e.unitIso
  let _eU :
      (F.fiberFunctor U).IsEquivalence :=
    fiberFunctor_isEquivalence_of_equivalence_over_base (p₁ := p₁) (p₂ := p₂) F hF U
  let _eUinv :
      (G.fiberFunctor U).IsEquivalence :=
    inverse_fiberFunctor_isEquivalence_of_equivalence_over_base
      (p₁ := p₁) (p₂ := p₂) F hF U
  -- The forward transport functor is the fixed-cover descent-data transport built objectwise from
  -- the fiber functors and pullback-comparison isomorphisms.
  let TF :
      ((canonicalFiberPseudofunctor p₁).DescentData (fun I : S.Arrow ↦ I.f)) ⥤
        ((canonicalFiberPseudofunctor p₂).DescentData (fun I : S.Arrow ↦ I.f)) :=
    cover_descent_data_transport_functor_of_equivalence_over_base
      (J := J) (p₁ := p₁) (p₂ := p₂) F hF S
  have hTF : TF.IsEquivalence := by
    -- TODO: build the inverse fixed-cover transport from `G`, then package the unit and counit
    -- componentwise with `e.unitIso` and `e.counitIso` via `Pseudofunctor.DescentData.isoMk`.
    sorry
  letI : TF.IsEquivalence := hTF
  let eTF :
      ((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)) ⋙ TF ≅
        (F.fiberFunctor U) ⋙
          ((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f)) := by
    -- TODO: for each `x : p₁.Fiber U`, package the components
    -- `basedFunctor_pullbackComparison_of_equivalence_over_base ... I.f x` into a
    -- `Pseudofunctor.DescentData.isoMk`, and then assemble these isomorphisms naturally in `x`.
    sorry
  -- Once the fixed-cover transport is packaged, the remaining argument is the general
  -- equivalence-cancellation lemma for canonical descent functors.
  exact
    coverwise_canonicalDescentFunctor_isEquivalence_iff_of_transport
      (J := J) (p₁ := p₁) (p₂ := p₂) F hF S TF eTF

/-- Lemma 8.4.4: if two categories over the site `(C, J)` are equivalent over the base category
`C`, then one is a stack over `(C, J)` if and only if the other is. -/
theorem isStackOnSite_iff_of_equivalence_over_base
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase) :
    IsStackOnSite J p₁ ↔ IsStackOnSite J p₂ := by
  constructor
  · intro h
    letI : IsStackOnSite J p₁ := h
    letI : p₂.IsFibered :=
      fibered_target_of_equivalence_over_base (p₁ := p₁) (p₂ := p₂) F hF
    have hcover :
        ∀ (U : C) (S : J.Cover U),
          ((canonicalFiberPseudofunctor p₁).toDescentData (fun I : S.Arrow ↦ I.f)).IsEquivalence :=
      (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J p₁).1 h
    -- Reduce the target stack condition to the fixed-cover descent-data comparison.
    exact
      (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J p₂).2
        (fun U S ↦
          (coverwise_canonicalDescentFunctor_isEquivalence_iff_of_equivalence_over_base
            J p₁ p₂ F hF S).1 (hcover U S))
  · intro h
    let e : EquivalenceOverBase F := Classical.choice hF.nonempty
    let G := e.inverse
    have hG : G.IsEquivalenceOverBase := e.inverse_isEquivalenceOverBase
    letI : IsStackOnSite J p₂ := h
    letI : p₁.IsFibered :=
      fibered_target_of_equivalence_over_base (p₁ := p₂) (p₂ := p₁) G hG
    have hcover :
        ∀ (U : C) (S : J.Cover U),
          ((canonicalFiberPseudofunctor p₂).toDescentData (fun I : S.Arrow ↦ I.f)).IsEquivalence :=
      (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J p₂).1 h
    -- Reuse the same fixed-cover comparison for the chosen inverse over-base equivalence.
    exact
      (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J p₁).2
        (fun U S ↦
          (coverwise_canonicalDescentFunctor_isEquivalence_iff_of_equivalence_over_base
            J p₂ p₁ G hG S).1 (hcover U S))

end

end CategoryTheory
