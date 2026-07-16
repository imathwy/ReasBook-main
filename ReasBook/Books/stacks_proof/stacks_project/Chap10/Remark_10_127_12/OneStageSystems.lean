import stacks_proof.stacks_project.Chap10.Lemma_10_127_10
import stacks_proof.stacks_project.Chap10.Lemma_10_127_11
import Mathlib.RingTheory.DualNumber

universe u v w w₀

section

open DirectedLocalHomApproximation
open scoped DualNumber TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Helper for Remark 10.127.12: the canonical `ℤ`-algebra map to `𝔽₂` is finitely presented, hence
essentially of finite presentation. -/
theorem zmodTwo_intCast_essFinitePresentation :
    (Int.castRingHom (ZMod 2)).EssFinitePresentation := by
  -- Route correction: the transport issue here is only the concrete equality
  -- `Int.castRingHom = algebraMap`, so we rewrite to the canonical algebra map instead of adding a
  -- new owner-level transport theorem.
  have hcast : Int.castRingHom (ZMod 2) = algebraMap ℤ (ZMod 2) := by
    ext n
    simp
  have hkerFG : (RingHom.ker (Int.castRingHom (ZMod 2))).FG :=
    Ideal.fg_of_isNoetherianRing _
  have hfpInt : (Int.castRingHom (ZMod 2)).FinitePresentation :=
    RingHom.FinitePresentation.of_surjective
      (Int.castRingHom (ZMod 2)) ZMod.intCast_surjective
      hkerFG
  have hfpRing : (algebraMap ℤ (ZMod 2)).FinitePresentation := by
    -- Rewrite the finitely presented witness to the canonical algebra map without invoking broad
    -- simplification on ring-hom extensionality data.
    rw [← hcast]
    exact hfpInt
  have hfpAlg : Algebra.FinitePresentation ℤ (ZMod 2) := by
    rw [← RingHom.finitePresentation_algebraMap]
    exact hfpRing
  -- Once the ring hom is rewritten, the canonical `ℤ`-algebra on `𝔽₂` carries the standard
  -- essentially-finitely-presented instance.
  letI : Algebra.FinitePresentation ℤ (ZMod 2) := hfpAlg
  rw [hcast, RingHom.essFinitePresentation_algebraMap]
  exact Algebra.EssFinitePresentation.of_finitePresentation ℤ (ZMod 2)

/-- Helper for Remark 10.127.12: every universe lift of `𝔽₂` is essentially of finite type over
`ℤ`. -/
theorem ulift_zmodTwo_intCast_essFiniteType :
    (Int.castRingHom (ULift.{u} (ZMod 2))).EssFiniteType := by
  have hzmodTwo : Algebra.EssFiniteType ℤ (ZMod 2) := by
    -- First read the previous ring-hom witness as the canonical algebra structure on `𝔽₂`.
    have hfp : Algebra.EssFinitePresentation ℤ (ZMod 2) := by
      rw [← RingHom.essFinitePresentation_algebraMap]
      simpa using zmodTwo_intCast_essFinitePresentation
    exact Algebra.EssFinitePresentation.toEssFiniteType ℤ (ZMod 2) hfp
  let e : ULift.{u} (ZMod 2) ≃ₐ[ℤ] ZMod 2 := ULift.algEquiv (R := ℤ) (A := ZMod 2)
  have hulift : Algebra.EssFiniteType ℤ (ULift.{u} (ZMod 2)) := by
    -- Transport the algebra-level finite-type witness across the standard `ULift` equivalence.
    exact (Algebra.EssFiniteType.iff_of_algEquiv e).2 hzmodTwo
  have hcast : Int.castRingHom (ULift.{u} (ZMod 2)) = algebraMap ℤ (ULift.{u} (ZMod 2)) := by
    ext n
    simp
  -- Return to the ring-hom formulation owned by `DirectedLocalHomApproximation`.
  rw [hcast, RingHom.essFiniteType_algebraMap]
  exact hulift

/-- Helper for Remark 10.127.12: the identity map on a ring remains bijective after separate
universe lifts on source and target. -/
theorem ringHom_ulift_id_bijective (A : Type*) [CommRing A] :
    Function.Bijective (RingHom.ulift.{u, v} (RingHom.id A)) := by
  constructor
  · intro x y hxy
    cases x
    cases y
    simp [RingHom.ulift_apply] at hxy
    simpa using hxy
  · intro y
    refine ⟨ULift.up y.down, ?_⟩
    ext
    simp [RingHom.ulift_apply]

/-- Helper for Remark 10.127.12: the lifted identity map on `𝔽₂` is essentially of finite
presentation. -/
theorem ulift_zmodTwo_id_essFinitePresentation :
    let R : Type u := ULift.{u} (ZMod 2)
    let S : Type v := ULift.{v} (ZMod 2)
    let f : R →+* S := RingHom.ulift (RingHom.id (ZMod 2))
    f.EssFinitePresentation := by
  dsimp
  let f : ULift.{u} (ZMod 2) →+* ULift.{v} (ZMod 2) := RingHom.ulift (RingHom.id (ZMod 2))
  letI : Algebra (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2)) := f.toAlgebra
  let e : ULift.{u} (ZMod 2) ≃ₐ[ULift.{u} (ZMod 2)] ULift.{v} (ZMod 2) :=
    AlgEquiv.ofBijective (Algebra.ofId _ _) (ringHom_ulift_id_bijective (A := ZMod 2))
  have hAlg :
      Algebra.EssFinitePresentation (ULift.{u} (ZMod 2)) (ULift.{v} (ZMod 2)) := by
    -- The source algebra is the identity algebra, and the target is equivalent to it via the
    -- lifted identity map, so essential finite presentation transports across that equivalence.
    letI : Algebra.EssFinitePresentation (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2)) :=
      inferInstance
    exact Algebra.EssFinitePresentation.equiv
      (R := ULift.{u} (ZMod 2)) (S := ULift.{u} (ZMod 2)) (T := ULift.{v} (ZMod 2)) e
  -- Finally translate the algebra-level witness back to the ring-hom owned statement.
  rw [RingHom.EssFinitePresentation]
  simpa [f, RingHom.algebraMap_toAlgebra] using hAlg

/-- Helper for Remark 10.127.12: the direct limit of the constant one-stage ring system is the
stage ring itself. -/
noncomputable def punit_const_directLimitRingEquiv (A : Type u) [CommRing A] :
    Ring.DirectLimit (fun _ : PUnit ↦ A) (fun _ _ _ ↦ RingHom.id A) ≃+* A :=
  RingEquiv.ofRingHom
    (Ring.DirectLimit.lift
      (fun _ : PUnit ↦ A) (fun _ _ _ ↦ RingHom.id A) A
      (fun _ ↦ RingHom.id A) (by
        intro i j hij x
        rfl))
    (Ring.DirectLimit.of (fun _ : PUnit ↦ A) (fun _ _ _ ↦ RingHom.id A) PUnit.unit)
    (by
      -- The chosen stage generator followed by the universal cocone map is the identity on `A`.
      ext x
      simpa using
        (Ring.DirectLimit.lift_of
          (G := fun _ : PUnit ↦ A)
          (f := fun _ _ _ ↦ RingHom.id A)
          (P := A)
          (g := fun _ ↦ RingHom.id A)
          (Hg := by intro i j hij y; rfl)
          PUnit.unit x))
    (by
      -- Any element of the singleton direct limit comes from the unique stage generator.
      apply Ring.DirectLimit.hom_ext
      intro i
      cases i
      ext x
      simpa using congrArg
        (Ring.DirectLimit.of (fun _ : PUnit ↦ A) (fun _ _ _ ↦ RingHom.id A) PUnit.unit)
        (Ring.DirectLimit.lift_of
          (G := fun _ : PUnit ↦ A)
          (f := fun _ _ _ ↦ RingHom.id A)
          (P := A)
          (g := fun _ ↦ RingHom.id A)
          (Hg := by intro i j hij y; rfl)
          PUnit.unit x))

/-- Helper for Remark 10.127.12: the singleton direct-limit equivalence sends the unique stage
generator to the underlying element. -/
@[simp] theorem punit_const_directLimitRingEquiv_of (A : Type u) [CommRing A] (x : A) :
    punit_const_directLimitRingEquiv A
        (Ring.DirectLimit.of (fun _ : PUnit ↦ A) (fun _ _ _ ↦ RingHom.id A) PUnit.unit x) = x := by
  -- This is the defining `lift_of` formula for the universal direct-limit map.
  simpa [punit_const_directLimitRingEquiv] using
    (Ring.DirectLimit.lift_of
      (G := fun _ : PUnit ↦ A)
      (f := fun _ _ _ ↦ RingHom.id A)
      (P := A)
      (g := fun _ ↦ RingHom.id A)
      (Hg := by intro i j hij y; rfl)
      PUnit.unit x)

/-- Helper for Remark 10.127.12: the constant singleton transition maps form a directed system. -/
instance punit_constant_directedSystem (A : Type u) [CommRing A] :
    DirectedSystem (fun _ : PUnit ↦ A) (fun _ _ _ ↦ RingHom.id A) where
  map_self := by
    intro _ x
    rfl
  map_map := by
    intro _ _ _ _ _ x
    rfl

/-- Helper for Remark 10.127.12: the identity map on `𝔽₂` is essentially of finite type. -/
theorem zmodTwo_id_essFiniteType :
    (RingHom.id (ZMod 2)).EssFiniteType := by
  -- The identity map is surjective, hence finite type, so it is essentially of finite type.
  simpa using
    (RingHom.FiniteType.of_surjective (RingHom.id (ZMod 2))
      (by intro x; exact ⟨x, rfl⟩)).essFiniteType

/-- Helper for Remark 10.127.12: the canonical map `𝔽₂ → 𝔽₂[ε]` is essentially of finite type
because `ε` generates the dual numbers over the base field. -/
theorem zmodTwo_to_dualNumber_essFiniteType :
    (algebraMap (ZMod 2) ((ZMod 2)[ε])).EssFiniteType := by
  have hrange_le :
      (TrivSqZeroExt.inlAlgHom (ZMod 2) (ZMod 2) (ZMod 2)).range ≤
        Algebra.adjoin (ZMod 2) ({(ε : (ZMod 2)[ε])} : Set ((ZMod 2)[ε])) := by
    intro x hx
    rcases hx with ⟨r, rfl⟩
    -- The image of the base field is always contained in the adjoin.
    change algebraMap (ZMod 2) ((ZMod 2)[ε]) r ∈
      Algebra.adjoin (ZMod 2) ({(ε : (ZMod 2)[ε])} : Set ((ZMod 2)[ε]))
    exact (Algebra.adjoin (ZMod 2) ({(ε : (ZMod 2)[ε])} : Set ((ZMod 2)[ε]))).algebraMap_mem r
  have htop :
      Algebra.adjoin (ZMod 2) ({(ε : (ZMod 2)[ε])} : Set ((ZMod 2)[ε])) = ⊤ := by
    -- The dual-number algebra is generated by the image of the base field together with `ε`,
    -- and the base-field image already lies in the adjoin of `ε`.
    calc
      Algebra.adjoin (ZMod 2) ({(ε : (ZMod 2)[ε])} : Set ((ZMod 2)[ε])) =
          (TrivSqZeroExt.inlAlgHom (ZMod 2) (ZMod 2) (ZMod 2)).range ⊔
            Algebra.adjoin (ZMod 2) ({(ε : (ZMod 2)[ε])} : Set ((ZMod 2)[ε])) := by
              exact (sup_eq_right.mpr hrange_le).symm
      _ = ⊤ := DualNumber.range_inlAlgHom_sup_adjoin_eps (R := ZMod 2) (A := ZMod 2)
  have hfinite :
      Algebra.FiniteType (ZMod 2)
        ↥(Algebra.adjoin (ZMod 2) ({(ε : (ZMod 2)[ε])} : Set ((ZMod 2)[ε]))) :=
    Algebra.FiniteType.adjoin_of_finite
      (R := ZMod 2) (A := (ZMod 2)[ε])
      (t := ({(ε : (ZMod 2)[ε])} : Set ((ZMod 2)[ε])))
      (Set.finite_singleton _)
  letI : Algebra.FiniteType (ZMod 2) ((ZMod 2)[ε]) := by
    let Aε : Subalgebra (ZMod 2) ((ZMod 2)[ε]) :=
      Algebra.adjoin (ZMod 2) ({(ε : (ZMod 2)[ε])} : Set ((ZMod 2)[ε]))
    letI : Algebra.FiniteType (ZMod 2) Aε := hfinite
    have hsurj : Function.Surjective (Aε.val : Aε →ₐ[ZMod 2] (ZMod 2)[ε]) := by
      intro z
      have hz : z ∈ Aε := by
        simpa [Aε, htop] using (show z ∈ (⊤ : Subalgebra (ZMod 2) ((ZMod 2)[ε])) by trivial)
      exact ⟨⟨z, hz⟩, rfl⟩
    exact Algebra.FiniteType.of_surjective (Aε.val) hsurj
  -- Return to the ring-hom formulation owned by the approximation system.
  rw [RingHom.essFiniteType_algebraMap]
  infer_instance

/-- Helper for Remark 10.127.12: locality transfers across `ULift` by reading the unit test on the
underlying ring. -/
instance ulift_isLocalRing (A : Type*) [CommRing A] [IsLocalRing A] :
    IsLocalRing (ULift A) where
  isUnit_or_isUnit_of_add_one {a b} h := by
    have hdown : a.down + b.down = 1 := by
      simpa using congrArg ULift.down h
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one (a := a.down) (b := b.down) hdown with ha | hb
    · left
      exact ha.map (ULift.ringEquiv.symm.toRingHom : A →+* ULift A)
    · right
      exact hb.map (ULift.ringEquiv.symm.toRingHom : A →+* ULift A)

/-- Helper for Remark 10.127.12: `ULift` preserves the local-hom property by composing with the
source and target ring equivalences. -/
theorem ringHom_ulift_isLocalHom {A : Type*} {B : Type*}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] (f : A →+* B)
    [IsLocalHom f] :
    IsLocalHom (RingHom.ulift.{u, v} f) := by
  letI : IsLocalHom (ULift.ringEquiv.toRingHom : ULift.{u} A →+* A) :=
    Function.Surjective.isLocalHom _ ULift.ringEquiv.surjective
  letI : IsLocalHom (ULift.ringEquiv.symm.toRingHom : B →+* ULift.{v} B) :=
    Function.Surjective.isLocalHom _ ULift.ringEquiv.symm.surjective
  -- The lifted map is literally the composite of the two ring equivalences with `f`.
  simpa [RingHom.ulift] using
    (RingHom.isLocalHom_comp (ULift.ringEquiv.symm.toRingHom)
      ((f.comp ULift.ringEquiv.toRingHom)))

/-- Helper for Remark 10.127.12: `ULift` preserves essential finite type by composing with the
source and target ring equivalences. -/
theorem ringHom_ulift_essFiniteType {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.EssFiniteType) :
    (RingHom.ulift.{u, v} f).EssFiniteType := by
  have hsource_surj :
      Function.Surjective (ULift.ringEquiv.toRingHom : ULift.{u} A →+* A) := by
    simpa using ULift.ringEquiv.surjective
  have hsource :
      (ULift.ringEquiv.toRingHom : ULift.{u} A →+* A).EssFiniteType := by
    simpa using
      (RingHom.FiniteType.of_surjective
        (ULift.ringEquiv.toRingHom : ULift.{u} A →+* A) hsource_surj).essFiniteType
  have htarget_surj :
      Function.Surjective (ULift.ringEquiv.symm.toRingHom : B →+* ULift.{v} B) := by
    simpa using ULift.ringEquiv.symm.surjective
  have htarget :
      (ULift.ringEquiv.symm.toRingHom : B →+* ULift.{v} B).EssFiniteType := by
    simpa using
      (RingHom.FiniteType.of_surjective
        (ULift.ringEquiv.symm.toRingHom : B →+* ULift.{v} B)
        htarget_surj).essFiniteType
  -- `RingHom.ulift f` is the composite `ULift A ≃ A → B ≃ ULift B`.
  simpa [RingHom.ulift] using hsource.comp (hf.comp htarget)

/-- Helper for Remark 10.127.12: after identifying both singleton direct limits with their unique
stages, the induced colimit map is exactly the stage map. -/
theorem singleton_constant_system_colimit_comm {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (f : A →+* B) :
    (punit_const_directLimitRingEquiv B).toRingHom.comp
        (Ring.DirectLimit.map
          (fun _ : PUnit ↦ f)
          (fun _ _ _ ↦ by
            ext x
            rfl)) =
      f.comp (punit_const_directLimitRingEquiv A).toRingHom := by
  -- Compare both ring homomorphisms on the unique stage generator of the singleton direct limit.
  apply Ring.DirectLimit.hom_ext
  intro i
  cases i
  ext x
  -- Evaluate both direct-limit maps on the unique stage generator and collapse both singleton
  -- colimits using the explicit `lift_of` formulas.
  have hmap :
      Ring.DirectLimit.map
          (fun _ : PUnit ↦ f)
          (fun _ _ _ ↦ by
            ext y
            rfl)
          (Ring.DirectLimit.of (fun _ : PUnit ↦ A) (fun _ _ _ ↦ RingHom.id A) PUnit.unit x) =
        Ring.DirectLimit.of (fun _ : PUnit ↦ B) (fun _ _ _ ↦ RingHom.id B) PUnit.unit (f x) :=
    Ring.DirectLimit.map_apply_of
      (f := fun _ _ _ ↦ RingHom.id A)
      (f' := fun _ _ _ ↦ RingHom.id B)
      (g := fun _ : PUnit ↦ f)
      (hg := fun _ _ _ ↦ by
        ext y
        rfl)
      (x := x)
  have hmap' := congrArg (punit_const_directLimitRingEquiv B) hmap
  calc
    (punit_const_directLimitRingEquiv B).toRingHom
        ((Ring.DirectLimit.map
          (fun _ : PUnit ↦ f)
          (fun _ _ _ ↦ by
            ext y
            rfl))
          (Ring.DirectLimit.of (fun _ : PUnit ↦ A) (fun _ _ _ ↦ RingHom.id A) PUnit.unit x)) =
      (punit_const_directLimitRingEquiv B).toRingHom
        (Ring.DirectLimit.of (fun _ : PUnit ↦ B) (fun _ _ _ ↦ RingHom.id B) PUnit.unit (f x)) := by
          exact hmap'
    _ = f x := by
      simpa [RingHom.comp_apply] using punit_const_directLimitRingEquiv_of B (f x)
    _ = f ((punit_const_directLimitRingEquiv A)
          (Ring.DirectLimit.of (fun _ : PUnit ↦ A) (fun _ _ _ ↦ RingHom.id A) PUnit.unit x)) := by
            simpa using congrArg f (punit_const_directLimitRingEquiv_of A x).symm

end
