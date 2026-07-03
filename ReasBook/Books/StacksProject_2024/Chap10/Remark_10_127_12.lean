import StacksProject_2024.Chap10.Lemma_10_127_10
import StacksProject_2024.Chap10.Lemma_10_127_11
import Mathlib.RingTheory.DualNumber

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w w₀

section

open DirectedLocalHomApproximation
open scoped DualNumber TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-
Domain sampling:
* Primary domain: directed approximation systems for local homomorphisms of local rings in
  commutative algebra.
* Owner declarations inspected in this domain:
  - `DirectedLocalHomApproximation`
  - `DirectedLocalHomApproximation.HasLocalizationOfQuotientTransitions`
  - `DirectedLocalHomApproximation.HasPrimeLocalizationTransitions`
  - `DirectedLocalHomApproximation.HasFailingPrimeLocalizationTransition`
* Best owner abstraction: `DirectedLocalHomApproximation f`.
* Layer targeted here: `source-facing`. The remark asserts existence of one local essentially
  finitely presented map together with two approximation systems on the same owner object,
  distinguished only by derived transition properties.
* Primitive vs. derived: the directed system, stage rings, local stage maps, colimit
  identifications, and stagewise essential finite-type data are primitive owner data from
  `Lemma_10_127_9`; the good/bad transition conditions are derived properties already owned by
  `Lemma_10_127_10` and `Lemma_10_127_11`, so no extra wrapper predicate is needed here.
-/

variable {R : Type u} {S : Type v} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]

/-- Helper for Remark 10.127.12: the canonical `ℤ`-algebra map to `𝔽₂` is finitely presented, hence
essentially of finite presentation. -/
private theorem zmodTwo_intCast_essFinitePresentation :
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
private theorem ulift_zmodTwo_intCast_essFiniteType :
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
private theorem ringHom_ulift_id_bijective (A : Type*) [CommRing A] :
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
private theorem ulift_zmodTwo_id_essFinitePresentation :
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
private noncomputable def punit_const_directLimitRingEquiv (A : Type u) [CommRing A] :
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
@[simp] private theorem punit_const_directLimitRingEquiv_of (A : Type u) [CommRing A] (x : A) :
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
private instance punit_constant_directedSystem (A : Type u) [CommRing A] :
    DirectedSystem (fun _ : PUnit ↦ A) (fun _ _ _ ↦ RingHom.id A) where
  map_self := by
    intro _ x
    rfl
  map_map := by
    intro _ _ _ _ _ x
    rfl

/-- Helper for Remark 10.127.12: the identity map on `𝔽₂` is essentially of finite type. -/
private theorem zmodTwo_id_essFiniteType :
    (RingHom.id (ZMod 2)).EssFiniteType := by
  -- The identity map is surjective, hence finite type, so it is essentially of finite type.
  simpa using
    (RingHom.FiniteType.of_surjective (RingHom.id (ZMod 2))
      (by intro x; exact ⟨x, rfl⟩)).essFiniteType

/-- Helper for Remark 10.127.12: the canonical map `𝔽₂ → 𝔽₂[ε]` is essentially of finite type
because `ε` generates the dual numbers over the base field. -/
private theorem zmodTwo_to_dualNumber_essFiniteType :
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
private instance ulift_isLocalRing (A : Type*) [CommRing A] [IsLocalRing A] :
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
private theorem ringHom_ulift_isLocalHom {A : Type*} {B : Type*}
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
private theorem ringHom_ulift_essFiniteType {A : Type*} {B : Type*} [CommRing A] [CommRing B]
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
private theorem singleton_constant_system_colimit_comm {A : Type u} {B : Type v}
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

/-- Helper for Remark 10.127.12: `true ≤ false` does not occur in the `Bool`-indexed two-stage
systems used below. -/
private theorem bool_true_not_le_false : ¬ (true ≤ false) := by
  decide

/-- Helper for Remark 10.127.12: a two-stage system has a lower stage `A` and a top stage `B`
indexed by `false ≤ true`. -/
private abbrev two_stageStage (A : Type w) (B : Type w) : Bool → Type w
  | false => A
  | true => B

/-- Helper for Remark 10.127.12: each stage of the two-stage system inherits the ring structure of
the corresponding endpoint ring. -/
private instance two_stageStageCommRing {A : Type w} {B : Type w} [CommRing A] [CommRing B] :
    (i : Bool) → CommRing (two_stageStage A B i)
  | false => inferInstance
  | true => inferInstance

/-- Helper for Remark 10.127.12: the only nontrivial transition in a two-stage system is the map
from the lower stage to the top stage. -/
private def two_stageMap {A : Type w} {B : Type w} [CommRing A] [CommRing B] (τ : A →+* B) :
    ∀ i j : Bool, i ≤ j → two_stageStage A B i →+* two_stageStage A B j
  | false, false, _ => RingHom.id A
  | false, true, _ => τ
  | true, true, _ => RingHom.id B
  | true, false, h => False.elim (bool_true_not_le_false h)

/-- Helper for Remark 10.127.12: the identity transitions of the two-stage system are literally
the identity maps on the corresponding stages. -/
private theorem two_stageMap_self {A : Type w} {B : Type w} [CommRing A] [CommRing B]
    (τ : A →+* B) :
    ∀ i (x : two_stageStage A B i), two_stageMap τ i i le_rfl x = x
  | false, x => rfl
  | true, x => rfl

/-- Helper for Remark 10.127.12: the two-stage transition maps compose exactly as expected. -/
private theorem two_stageMap_map {A : Type w} {B : Type w} [CommRing A] [CommRing B]
    (τ : A →+* B) :
    ∀ {k j i : Bool} (hij : i ≤ j) (hjk : j ≤ k) (x : two_stageStage A B i),
      two_stageMap τ j k hjk (two_stageMap τ i j hij x) =
        two_stageMap τ i k (le_trans hij hjk) x
  | false, false, false, _, _, x => rfl
  | true, false, false, _, _, x => rfl
  | false, true, false, _, hjk, _ => False.elim (bool_true_not_le_false hjk)
  | true, true, false, _, _, x => rfl
  | false, false, true, hij, _, _ => False.elim (bool_true_not_le_false hij)
  | true, false, true, hij, _, _ => False.elim (bool_true_not_le_false hij)
  | false, true, true, _, hjk, _ => False.elim (bool_true_not_le_false hjk)
  | true, true, true, _, _, x => rfl

/-- Helper for Remark 10.127.12: the map from a two-stage system to its top stage is compatible
with the unique nontrivial transition. -/
private def two_stageTopDesc {A : Type w} {B : Type w} [CommRing A] [CommRing B] (τ : A →+* B) :
    (i : Bool) → two_stageStage A B i →+* B
  | false => τ
  | true => RingHom.id B

/-- Helper for Remark 10.127.12: the map from a two-stage system to its top stage is compatible
with the unique nontrivial transition. -/
private theorem two_stage_top_desc_compatible {A : Type w} {B : Type w}
    [CommRing A] [CommRing B] (τ : A →+* B) :
    ∀ {i j : Bool} (hij : i ≤ j),
      (two_stageTopDesc τ j).comp (two_stageMap τ i j hij) = two_stageTopDesc τ i
  | false, false, _ => by
      ext x
      rfl
  | false, true, _ => by
      ext x
      rfl
  | true, false, hij => False.elim (bool_true_not_le_false hij)
  | true, true, _ => by
      ext x
      rfl

/-- Helper for Remark 10.127.12: the compatibility for the top-stage descent map can be read
pointwise on stage elements. -/
private theorem two_stage_top_desc_compatible_apply {A : Type w} {B : Type w}
    [CommRing A] [CommRing B] (τ : A →+* B) :
    ∀ (i j : Bool) (hij : i ≤ j) (x : two_stageStage A B i),
      two_stageTopDesc τ j (two_stageMap τ i j hij x) = two_stageTopDesc τ i x := by
  intro i j hij x
  exact congrArg (fun g : two_stageStage A B i →+* B => g x)
    (two_stage_top_desc_compatible τ hij)

/-- Helper for Remark 10.127.12: the `Bool` two-stage maps satisfy the directed-system relations. -/
private instance two_stageDirectedSystem {A : Type w} {B : Type w} [CommRing A] [CommRing B]
    (τ : A →+* B) :
    DirectedSystem (two_stageStage A B) (fun i j h ↦ two_stageMap τ i j h) where
  map_self := by
    intro i x
    exact two_stageMap_self τ i x
  map_map := by
    intro k j i hij hjk x
    exact two_stageMap_map τ hij hjk x

/-- Helper for Remark 10.127.12: the two-stage direct limit admits a canonical comparison map to
its top stage. -/
private noncomputable def two_stage_top_directLimitToTopHom {A : Type w} {B : Type w}
    [CommRing A] [CommRing B] (τ : A →+* B) :
    Ring.DirectLimit (two_stageStage A B) (fun i j h ↦ two_stageMap τ i j h) →+* B :=
  Ring.DirectLimit.lift
    (two_stageStage A B) (fun i j h ↦ two_stageMap τ i j h) B
    (two_stageTopDesc τ) (two_stage_top_desc_compatible_apply τ)

/-- Helper for Remark 10.127.12: the direct-limit comparison map is the identity on the top-stage
generator. -/
@[simp] private theorem two_stage_top_directLimitToTopHom_of_true {A : Type w} {B : Type w}
    [CommRing A] [CommRing B] (τ : A →+* B) (x : B) :
    two_stage_top_directLimitToTopHom τ
        (Ring.DirectLimit.of (two_stageStage A B) (fun i j h ↦ two_stageMap τ i j h) true x) = x := by
  -- Proof comment: this is the `lift_of` formula evaluated at the top stage, where the cocone map
  -- is the identity on `B`.
  simpa [two_stage_top_directLimitToTopHom, two_stageTopDesc] using
    (Ring.DirectLimit.lift_of
      (G := two_stageStage A B)
      (f := fun i j h ↦ two_stageMap τ i j h)
      (P := B)
      (g := two_stageTopDesc τ)
      (Hg := two_stage_top_desc_compatible_apply τ)
      true x)

/-- Helper for Remark 10.127.12: the direct-limit comparison map sends the lower-stage generator
through the unique transition to the top stage. -/
@[simp] private theorem two_stage_top_directLimitToTopHom_of_false {A : Type w} {B : Type w}
    [CommRing A] [CommRing B] (τ : A →+* B) (x : A) :
    two_stage_top_directLimitToTopHom τ
        (Ring.DirectLimit.of (two_stageStage A B) (fun i j h ↦ two_stageMap τ i j h) false x) = τ x := by
  -- Proof comment: this is the same `lift_of` formula at the lower stage, where the cocone map is
  -- exactly the structure map `τ`.
  simpa [two_stage_top_directLimitToTopHom, two_stageTopDesc] using
    (Ring.DirectLimit.lift_of
      (G := two_stageStage A B)
      (f := fun i j h ↦ two_stageMap τ i j h)
      (P := B)
      (g := two_stageTopDesc τ)
      (Hg := two_stage_top_desc_compatible_apply τ)
      false x)

/-- Helper for Remark 10.127.12: the top-stage inclusion is a left inverse to the comparison map
from the two-stage direct limit. -/
private theorem two_stage_top_directLimit_ofTop_comp_toTop_eq_id {A : Type w} {B : Type w}
    [CommRing A] [CommRing B] (τ : A →+* B) :
    (Ring.DirectLimit.of (two_stageStage A B) (fun i j h ↦ two_stageMap τ i j h) true).comp
        (two_stage_top_directLimitToTopHom τ) =
      RingHom.id _ := by
  -- Route correction: prove the inverse statement at the `RingHom` level first, so the only
  -- relations left are the two generator formulas and the unique `false ≤ true` transition.
  apply Ring.DirectLimit.hom_ext
  intro i
  cases i
  · ext x
    -- Proof comment: the lower-stage generator becomes a top-stage generator via `of_f`.
    calc
      (((Ring.DirectLimit.of (two_stageStage A B) (fun i j h ↦ two_stageMap τ i j h) true).comp
            (two_stage_top_directLimitToTopHom τ)).comp
          (Ring.DirectLimit.of (two_stageStage A B) (fun i j h ↦ two_stageMap τ i j h) false)) x =
        (Ring.DirectLimit.of (two_stageStage A B) (fun i j h ↦ two_stageMap τ i j h) true) (τ x) := by
          change
            (Ring.DirectLimit.of (two_stageStage A B) (fun i j h ↦ two_stageMap τ i j h) true)
                (two_stage_top_directLimitToTopHom τ
                  (Ring.DirectLimit.of (two_stageStage A B) (fun i j h ↦ two_stageMap τ i j h) false x)) =
              (Ring.DirectLimit.of (two_stageStage A B) (fun i j h ↦ two_stageMap τ i j h) true) (τ x)
          rw [two_stage_top_directLimitToTopHom_of_false]
      _ = (Ring.DirectLimit.of (two_stageStage A B) (fun i j h ↦ two_stageMap τ i j h) false) x := by
        simpa [two_stageMap] using (Ring.DirectLimit.of_f
        (G := two_stageStage A B)
        (f := fun i j h ↦ two_stageMap τ i j h)
        (i := false) (j := true) (by decide) x)
  · ext x
    -- Proof comment: the top-stage generator is fixed by the comparison map.
    change
      (Ring.DirectLimit.of (two_stageStage A B) (fun i j h ↦ two_stageMap τ i j h) true)
          (two_stage_top_directLimitToTopHom τ
            (Ring.DirectLimit.of (two_stageStage A B) (fun i j h ↦ two_stageMap τ i j h) true x)) =
        (Ring.DirectLimit.of (two_stageStage A B) (fun i j h ↦ two_stageMap τ i j h) true) x
    rw [two_stage_top_directLimitToTopHom_of_true]

/-- Helper for Remark 10.127.12: a `Bool`-indexed two-stage direct limit is already controlled by
its top stage. -/
private noncomputable def two_stage_top_directLimitRingEquiv {A : Type w} {B : Type w}
    [CommRing A] [CommRing B] (τ : A →+* B) :
    Ring.DirectLimit (two_stageStage A B) (fun i j h ↦ two_stageMap τ i j h) ≃+* B :=
  RingEquiv.ofRingHom
    (two_stage_top_directLimitToTopHom τ)
    (Ring.DirectLimit.of (two_stageStage A B) (fun i j h ↦ two_stageMap τ i j h) true)
    (by
      -- Proof comment: the top-stage inclusion is a right inverse because the comparison map is
      -- literally the identity on the top-stage generator.
      ext x
      exact two_stage_top_directLimitToTopHom_of_true τ x)
    (two_stage_top_directLimit_ofTop_comp_toTop_eq_id τ)

/-- Helper for Remark 10.127.12: the two-stage direct-limit comparison sends the top-stage
generator to the underlying top-stage element. -/
@[simp] private theorem two_stage_top_directLimitRingEquiv_of_true {A : Type w} {B : Type w}
    [CommRing A] [CommRing B] (τ : A →+* B) (x : B) :
    two_stage_top_directLimitRingEquiv τ
        (Ring.DirectLimit.of (two_stageStage A B) (fun i j h ↦ two_stageMap τ i j h) true x) = x := by
  -- Proof comment: after packaging the equivalence, its forward map is still the named comparison
  -- hom, so this reduces to the top-stage generator formula above.
  change
    two_stage_top_directLimitToTopHom τ
        (Ring.DirectLimit.of (two_stageStage A B) (fun i j h ↦ two_stageMap τ i j h) true x) = x
  exact two_stage_top_directLimitToTopHom_of_true τ x

/-- Helper for Remark 10.127.12: the two-stage direct-limit comparison sends the lower-stage
generator through the unique transition to the top stage. -/
@[simp] private theorem two_stage_top_directLimitRingEquiv_of_false {A : Type w} {B : Type w}
    [CommRing A] [CommRing B] (τ : A →+* B) (x : A) :
    two_stage_top_directLimitRingEquiv τ
        (Ring.DirectLimit.of (two_stageStage A B) (fun i j h ↦ two_stageMap τ i j h) false x) = τ x := by
  -- Proof comment: the lower-stage generator formula is inherited from the named comparison hom.
  change
    two_stage_top_directLimitToTopHom τ
        (Ring.DirectLimit.of (two_stageStage A B) (fun i j h ↦ two_stageMap τ i j h) false x) = τ x
  exact two_stage_top_directLimitToTopHom_of_false τ x

/-- Helper for Remark 10.127.12: the lifted identity map between the two `ULift 𝔽₂` universes is a
local ring homomorphism because it is surjective. -/
private theorem ulift_zmodTwo_id_isLocalHom :
    let R : Type u := ULift.{u} (ZMod 2)
    let S : Type v := ULift.{v} (ZMod 2)
    let f : R →+* S := RingHom.ulift (RingHom.id (ZMod 2))
    IsLocalHom f := by
  dsimp
  -- Surjectivity of the lifted identity lets us invoke the standard local-hom criterion.
  exact (ringHom_ulift_id_bijective (A := ZMod 2)).2.isLocalHom

/-- Helper for Remark 10.127.12: the lifted identity map between the two `ULift 𝔽₂` universes is
essentially of finite type. -/
private theorem ulift_zmodTwo_id_essFiniteType :
    let R : Type u := ULift.{u} (ZMod 2)
    let S : Type v := ULift.{v} (ZMod 2)
    let f : R →+* S := RingHom.ulift (RingHom.id (ZMod 2))
    f.EssFiniteType := by
  dsimp
  -- Proof comment: transport the finite-type witness for the identity on `𝔽₂` across the source
  -- and target `ULift` equivalences.
  exact ringHom_ulift_essFiniteType
    (f := RingHom.id (ZMod 2)) zmodTwo_id_essFiniteType

/-- Helper for Remark 10.127.12: the singleton stage square for the lifted identity system
commutes tautologically. -/
private theorem ulift_zmodTwo_punit_square_commutes {i j : PUnit} (h : i ≤ j) :
    ((RingHom.ulift.{u, v} (RingHom.id (ZMod 2))) :
        ULift.{u} (ZMod 2) →+* ULift.{v} (ZMod 2)).comp (RingHom.id _) =
      (RingHom.id _).comp (RingHom.ulift.{u, v} (RingHom.id (ZMod 2))) := by
  -- Proof comment: every source and target transition is the identity in the singleton system.
  ext x
  rfl

/-- Helper for Remark 10.127.12: the next proof step is to package the lifted `𝔽₂` identity map
into an explicit approximation system whose transitions are localizations at prime ideals. -/
private noncomputable def lifted_goodSystem :
    let R : Type u := ULift.{u} (ZMod 2)
    let S : Type v := ULift.{v} (ZMod 2)
    let f : R →+* S := RingHom.ulift (RingHom.id (ZMod 2))
    DirectedLocalHomApproximation f :=
  { Λ := PUnit
    instPreorder := inferInstance
    instNonempty := inferInstance
    instDirectedOrder := inferInstance
    RStage := fun _ ↦ ULift.{u} (ZMod 2)
    instCommRingRStage := fun _ ↦ inferInstance
    map := fun _ _ _ ↦ RingHom.id _
    instDirectedSystemRStage := punit_constant_directedSystem (ULift.{u} (ZMod 2))
    colimitIso := punit_const_directLimitRingEquiv (ULift.{u} (ZMod 2))
    instIsLocalRingRStage := fun _ ↦ inferInstance
    SStage := fun _ ↦ ULift.{v} (ZMod 2)
    instCommRingSStage := fun _ ↦ inferInstance
    instIsLocalRingSStage := fun _ ↦ inferInstance
    stageMap := fun _ ↦ RingHom.ulift (RingHom.id (ZMod 2))
    stageMap_isLocalHom := fun _ ↦ ulift_zmodTwo_id_isLocalHom
    targetMap := fun _ _ _ ↦ RingHom.id _
    instDirectedSystemTarget := punit_constant_directedSystem (ULift.{v} (ZMod 2))
    comm := fun {_ _} h ↦ ulift_zmodTwo_punit_square_commutes h
    targetColimit := punit_const_directLimitRingEquiv (ULift.{v} (ZMod 2))
    colimit_comm := singleton_constant_system_colimit_comm (RingHom.ulift (RingHom.id (ZMod 2)))
    source_essFiniteType := fun _ ↦ ulift_zmodTwo_intCast_essFiniteType
    target_essFiniteType := fun _ ↦ ulift_zmodTwo_id_essFiniteType }

/-- Helper for Remark 10.127.12: the dual numbers over `𝔽₂` are local because a dual number is a
unit exactly when its scalar part is a unit. -/
private instance zmodTwo_dualNumber_isLocalRing : IsLocalRing ((ZMod 2)[ε]) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self ?_
  intro x
  by_cases hx : TrivSqZeroExt.fst x = 0
  · right
    -- Proof comment: if the scalar part vanishes, then the scalar part of `1 - x` is `1`, so
    -- `1 - x` is a unit.
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa [hx]
  · left
    -- Proof comment: a nonzero scalar part is invertible in the base field, hence so is the
    -- whole dual number.
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    exact IsUnit.mk0 _ hx

/-- Helper for Remark 10.127.12: the lifted lower-stage map in the bad system is the universe lift
of the canonical inclusion `𝔽₂ → 𝔽₂[ε]`. -/
private abbrev lifted_zmodTwo_to_dualNumber :
    ULift.{u} (ZMod 2) →+* ULift.{v} ((ZMod 2)[ε]) :=
  RingHom.ulift ((TrivSqZeroExt.inlAlgHom (ZMod 2) (ZMod 2) (ZMod 2)).toRingHom)

/-- Helper for Remark 10.127.12: the unique nontrivial target transition in the bad system is the
universe lift of the projection `𝔽₂[ε] → 𝔽₂`. -/
private abbrev lifted_dualNumber_fst :
    ULift.{v} ((ZMod 2)[ε]) →+* ULift.{v} (ZMod 2) :=
  RingHom.ulift ((TrivSqZeroExt.fstHom (ZMod 2) (ZMod 2) (ZMod 2)).toRingHom)

/-- Helper for Remark 10.127.12: the inclusion `𝔽₂ → 𝔽₂[ε]` is a local map because units are
detected on the scalar part. -/
private theorem zmodTwo_to_dualNumber_isLocalHom :
    IsLocalHom ((TrivSqZeroExt.inlAlgHom (ZMod 2) (ZMod 2) (ZMod 2)).toRingHom) := by
  refine ⟨fun a ha ↦ ?_⟩
  -- Proof comment: the image of `a` is the dual number `inl a`, and `isUnit_inl_iff` reads the
  -- unit test back on the base field element.
  simpa using (TrivSqZeroExt.isUnit_inl_iff (R := ZMod 2) (M := ZMod 2) (r := a)).mp ha

/-- Helper for Remark 10.127.12: the lifted inclusion `ULift 𝔽₂ → ULift 𝔽₂[ε]` remains a local
map. -/
private theorem ulift_zmodTwo_to_dualNumber_isLocalHom :
    IsLocalHom lifted_zmodTwo_to_dualNumber := by
  letI :
      IsLocalHom ((TrivSqZeroExt.inlAlgHom (ZMod 2) (ZMod 2) (ZMod 2)).toRingHom) :=
    zmodTwo_to_dualNumber_isLocalHom
  -- Proof comment: locality is preserved by the source and target `ULift` ring equivalences.
  simpa [lifted_zmodTwo_to_dualNumber] using
    (ringHom_ulift_isLocalHom
      (f := (TrivSqZeroExt.inlAlgHom (ZMod 2) (ZMod 2) (ZMod 2)).toRingHom))

/-- Helper for Remark 10.127.12: the lifted inclusion `ULift 𝔽₂ → ULift 𝔽₂[ε]` is essentially of
finite type. -/
private theorem ulift_zmodTwo_to_dualNumber_essFiniteType :
    lifted_zmodTwo_to_dualNumber.EssFiniteType := by
  -- Proof comment: transport the dual-number finite-type witness across the source and target
  -- `ULift` ring equivalences.
  simpa [lifted_zmodTwo_to_dualNumber] using
    ringHom_ulift_essFiniteType
      (f := (TrivSqZeroExt.inlAlgHom (ZMod 2) (ZMod 2) (ZMod 2)).toRingHom)
      zmodTwo_to_dualNumber_essFiniteType

/-- Helper for Remark 10.127.12: the bad target transition followed by the bad lower-stage map is
the lifted identity on `𝔽₂`. -/
private theorem lifted_dualNumber_fst_comp_inl :
    RingHom.ulift (RingHom.id (ZMod 2)) =
      lifted_dualNumber_fst.comp lifted_zmodTwo_to_dualNumber := by
  -- Proof comment: on each element, the projection kills the square-zero part introduced by the
  -- inclusion and recovers the original field element.
  ext x
  rfl

/-- Helper for Remark 10.127.12: a stagewise map from the constant two-stage source system to a
target two-stage system is determined by its lower and upper components. -/
private abbrev two_stageStageMap {A : Type u} {C : Type v} {B : Type v}
    [CommRing A] [CommRing C] [CommRing B] (σ₀ : A →+* C) (σ₁ : A →+* B) :
    (i : Bool) → two_stageStage A A i →+* two_stageStage C B i
  | false => σ₀
  | true => σ₁

/-- Helper for Remark 10.127.12: the stagewise map into a two-stage target commutes with the
unique nontrivial transition exactly when the top-stage map factors through that transition. -/
private theorem two_stageStageMap_comm {A : Type u} {C : Type v} {B : Type v}
    [CommRing A] [CommRing C] [CommRing B] (σ₀ : A →+* C) (σ₁ : A →+* B) (τ : C →+* B)
    (hσ : σ₁ = τ.comp σ₀) :
    ∀ {i j : Bool} (hij : i ≤ j),
      (two_stageStageMap σ₀ σ₁ j).comp
          (two_stageMap (RingHom.id A) i j hij) =
        (two_stageMap τ i j hij).comp (two_stageStageMap σ₀ σ₁ i)
  | false, false, _ => by
      ext x
      rfl
  | false, true, _ => by
      -- Proof comment: the only nontrivial square is the lower-to-top square, and there it is
      -- exactly the factorization hypothesis `σ₁ = τ ∘ σ₀`.
      ext x
      simpa [two_stageStageMap, two_stageMap, hσ, RingHom.comp_apply]
  | true, false, hij => False.elim (bool_true_not_le_false hij)
  | true, true, _ => by
      ext x
      rfl

/-- Helper for Remark 10.127.12: after collapsing both two-stage direct limits to their top
stages, the induced map from the constant source system is the top-stage structural map. -/
private theorem two_stage_colimit_comm {A : Type u} {C : Type v} {B : Type v}
    [CommRing A] [CommRing C] [CommRing B] (σ₀ : A →+* C) (σ₁ : A →+* B) (τ : C →+* B)
    (hσ : σ₁ = τ.comp σ₀) :
    (two_stage_top_directLimitRingEquiv τ).toRingHom.comp
        (Ring.DirectLimit.map
          (two_stageStageMap σ₀ σ₁)
          (fun _ _ h ↦ two_stageStageMap_comm σ₀ σ₁ τ hσ h)) =
      σ₁.comp (two_stage_top_directLimitRingEquiv (RingHom.id A)).toRingHom := by
  apply Ring.DirectLimit.hom_ext
  intro i
  cases i
  · ext x
    -- Proof comment: the lower generator crosses to the target lower stage, then the target
    -- direct limit collapses it via the unique bad transition `τ`.
    calc
      (((two_stage_top_directLimitRingEquiv τ).toRingHom.comp
            (Ring.DirectLimit.map
              (two_stageStageMap σ₀ σ₁)
              (fun _ _ h ↦ two_stageStageMap_comm σ₀ σ₁ τ hσ h))).comp
          (Ring.DirectLimit.of (two_stageStage A A)
            (fun i j h ↦ two_stageMap (RingHom.id A) i j h) false)) x =
        (two_stage_top_directLimitRingEquiv τ)
          (Ring.DirectLimit.of (two_stageStage C B)
            (fun i j h ↦ two_stageMap τ i j h) false (σ₀ x)) := by
              simp [RingHom.comp_apply, two_stageStageMap]
      _ = τ (σ₀ x) := by
        simpa using two_stage_top_directLimitRingEquiv_of_false τ (σ₀ x)
      _ = σ₁ x := by
        simpa [hσ, RingHom.comp_apply]
      _ =
        ((σ₁.comp (two_stage_top_directLimitRingEquiv (RingHom.id A)).toRingHom).comp
            (Ring.DirectLimit.of (two_stageStage A A)
              (fun i j h ↦ two_stageMap (RingHom.id A) i j h) false)) x := by
                have hx :
                    (two_stage_top_directLimitRingEquiv (RingHom.id A))
                        (Ring.DirectLimit.of (two_stageStage A A)
                          (fun i j h ↦ two_stageMap (RingHom.id A) i j h) false x) = x := by
                  simpa using two_stage_top_directLimitRingEquiv_of_false (RingHom.id A) x
                simpa [RingHom.comp_apply] using congrArg σ₁ hx.symm
  · ext x
    -- Proof comment: the top generator already lives in the final stage on both sides.
    calc
      (((two_stage_top_directLimitRingEquiv τ).toRingHom.comp
            (Ring.DirectLimit.map
              (two_stageStageMap σ₀ σ₁)
              (fun _ _ h ↦ two_stageStageMap_comm σ₀ σ₁ τ hσ h))).comp
          (Ring.DirectLimit.of (two_stageStage A A)
            (fun i j h ↦ two_stageMap (RingHom.id A) i j h) true)) x =
        (two_stage_top_directLimitRingEquiv τ)
          (Ring.DirectLimit.of (two_stageStage C B)
            (fun i j h ↦ two_stageMap τ i j h) true (σ₁ x)) := by
              simp [RingHom.comp_apply, two_stageStageMap]
      _ = σ₁ x := by
        simpa using two_stage_top_directLimitRingEquiv_of_true τ (σ₁ x)
      _ =
        ((σ₁.comp (two_stage_top_directLimitRingEquiv (RingHom.id A)).toRingHom).comp
            (Ring.DirectLimit.of (two_stageStage A A)
              (fun i j h ↦ two_stageMap (RingHom.id A) i j h) true)) x := by
                have hx :
                    (two_stage_top_directLimitRingEquiv (RingHom.id A))
                        (Ring.DirectLimit.of (two_stageStage A A)
                          (fun i j h ↦ two_stageMap (RingHom.id A) i j h) true x) = x := by
                  simpa using two_stage_top_directLimitRingEquiv_of_true (RingHom.id A) x
                simpa [RingHom.comp_apply] using congrArg σ₁ hx.symm

/-- Helper for Remark 10.127.12: the bad system is the two-stage lifted dual-number projection
system. -/
private noncomputable def lifted_badSystem :
    let R : Type u := ULift.{u} (ZMod 2)
    let S : Type v := ULift.{v} (ZMod 2)
    let f : R →+* S := RingHom.ulift (RingHom.id (ZMod 2))
    DirectedLocalHomApproximation f :=
  { Λ := Bool
    instPreorder := inferInstance
    instNonempty := inferInstance
    instDirectedOrder := inferInstance
    RStage := two_stageStage (ULift.{u} (ZMod 2)) (ULift.{u} (ZMod 2))
    instCommRingRStage := fun
      | false => inferInstance
      | true => inferInstance
    map := fun i j h ↦ two_stageMap (RingHom.id (ULift.{u} (ZMod 2))) i j h
    instDirectedSystemRStage := two_stageDirectedSystem (RingHom.id (ULift.{u} (ZMod 2)))
    colimitIso := two_stage_top_directLimitRingEquiv (RingHom.id (ULift.{u} (ZMod 2)))
    instIsLocalRingRStage := fun
      | false => inferInstance
      | true => inferInstance
    SStage := two_stageStage (ULift.{v} ((ZMod 2)[ε])) (ULift.{v} (ZMod 2))
    instCommRingSStage := fun
      | false => inferInstance
      | true => inferInstance
    instIsLocalRingSStage := fun
      | false => inferInstance
      | true => inferInstance
    stageMap := two_stageStageMap lifted_zmodTwo_to_dualNumber (RingHom.ulift (RingHom.id (ZMod 2)))
    stageMap_isLocalHom := fun
      | false => ulift_zmodTwo_to_dualNumber_isLocalHom
      | true => ulift_zmodTwo_id_isLocalHom
    targetMap := fun i j h ↦ two_stageMap lifted_dualNumber_fst i j h
    instDirectedSystemTarget := two_stageDirectedSystem lifted_dualNumber_fst
    comm := fun {_ _} h ↦
      two_stageStageMap_comm
        lifted_zmodTwo_to_dualNumber
        (RingHom.ulift (RingHom.id (ZMod 2)))
        lifted_dualNumber_fst
        lifted_dualNumber_fst_comp_inl h
    targetColimit := two_stage_top_directLimitRingEquiv lifted_dualNumber_fst
    colimit_comm := two_stage_colimit_comm
      lifted_zmodTwo_to_dualNumber
      (RingHom.ulift (RingHom.id (ZMod 2)))
      lifted_dualNumber_fst
      lifted_dualNumber_fst_comp_inl
    source_essFiniteType := fun
      | false => ulift_zmodTwo_intCast_essFiniteType
      | true => ulift_zmodTwo_intCast_essFiniteType
    target_essFiniteType := fun
      | false => ulift_zmodTwo_to_dualNumber_essFiniteType
      | true => ulift_zmodTwo_id_essFiniteType }

/-- Helper for Remark 10.127.12: reindexing a `Type`-indexed directed ring system along
`ULift.down` preserves
the directed-system identities. -/
private instance ulift_isDirectedOrder {ι : Type} [Preorder ι] [IsDirectedOrder ι] :
    IsDirectedOrder (ULift.{w} ι) := by
  refine ⟨?_⟩
  intro i j
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.down j.down
  exact ⟨ULift.up k, hik, hjk⟩

/-- Helper for Remark 10.127.12: reindexing a `Type`-indexed directed ring system along
`ULift.down` preserves
the directed-system identities. -/
private instance ulift_directedSystem {ι : Type} [Preorder ι]
    (G : ι → Type u) [∀ i, CommRing (G i)]
    (φ : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ φ i j h)] :
    DirectedSystem (fun i : ULift.{w} ι ↦ G i.down) (fun i j h ↦ φ i.down j.down h) where
  map_self := by
    intro i x
    simpa using DirectedSystem.map_self (f := fun i j h ↦ φ i j h) x
  map_map := by
    intro i j k hij hjk x
    simpa using DirectedSystem.map_map (f := fun i j h ↦ φ i j h) hij hjk x

/-- Helper for Remark 10.127.12: the direct limit of a `ULift`-reindexed `Type`-indexed system
maps to the
original direct limit by forgetting the lifted index. -/
private noncomputable def directLimit_uliftToOriginal {ι : Type} [Preorder ι]
    (G : ι → Type u) [∀ i, CommRing (G i)]
    (φ : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ φ i j h)] :
    Ring.DirectLimit (fun i : ULift.{w} ι ↦ G i.down) (fun i j h ↦ φ i.down j.down h) →+*
      Ring.DirectLimit G (fun i j h ↦ φ i j h) :=
  Ring.DirectLimit.lift
    (fun i : ULift.{w} ι ↦ G i.down) (fun i j h ↦ φ i.down j.down h)
    (Ring.DirectLimit G (fun i j h ↦ φ i j h))
    (fun i ↦ Ring.DirectLimit.of G (fun i j h ↦ φ i j h) i.down)
    (by
      intro i j hij x
      simpa using (Ring.DirectLimit.of_f hij x))

/-- Helper for Remark 10.127.12: the previous map sends each lifted stage generator to the
corresponding generator in the original direct limit. -/
@[simp] private theorem directLimit_uliftToOriginal_of {ι : Type} [Preorder ι]
    (G : ι → Type u) [∀ i, CommRing (G i)]
    (φ : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ φ i j h)]
    (i : ULift.{w} ι) (x : G i.down) :
    directLimit_uliftToOriginal (G := G) (φ := φ)
        (Ring.DirectLimit.of (fun j : ULift.{w} ι ↦ G j.down) (fun j k h ↦ φ j.down k.down h)
          i x) =
      Ring.DirectLimit.of G (fun j k h ↦ φ j k h) i.down x := by
  -- Proof comment: this is the defining formula for the universal direct-limit lift.
  simpa [directLimit_uliftToOriginal] using
    (Ring.DirectLimit.lift_of
      (G := fun j : ULift.{w} ι ↦ G j.down)
      (f := fun j k h ↦ φ j.down k.down h)
      (P := Ring.DirectLimit G (fun j k h ↦ φ j k h))
      (g := fun j ↦ Ring.DirectLimit.of G (fun j k h ↦ φ j k h) j.down)
      (Hg := by intro i j hij y; rfl)
      i x)

/-- Helper for Remark 10.127.12: the original direct limit maps back to the `ULift`-reindexed
direct limit by inserting `ULift.up` on indices. -/
private noncomputable def directLimit_originalToUlift {ι : Type} [Preorder ι]
    (G : ι → Type u) [∀ i, CommRing (G i)]
    (φ : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ φ i j h)] :
    Ring.DirectLimit G (fun i j h ↦ φ i j h) →+*
      Ring.DirectLimit (fun i : ULift.{w} ι ↦ G i.down) (fun i j h ↦ φ i.down j.down h) :=
  Ring.DirectLimit.lift
    G (fun i j h ↦ φ i j h)
    (Ring.DirectLimit (fun i : ULift.{w} ι ↦ G i.down) (fun i j h ↦ φ i.down j.down h))
    (fun i ↦ Ring.DirectLimit.of (fun j : ULift.{w} ι ↦ G j.down) (fun j k h ↦ φ j.down k.down h)
      (ULift.up i))
    (by
      intro i j hij x
      simpa using (Ring.DirectLimit.of_f hij x))

/-- Helper for Remark 10.127.12: the map back to the lifted direct limit sends each original stage
generator to the corresponding lifted generator. -/
@[simp] private theorem directLimit_originalToUlift_of {ι : Type} [Preorder ι]
    (G : ι → Type u) [∀ i, CommRing (G i)]
    (φ : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ φ i j h)]
    (i : ι) (x : G i) :
    directLimit_originalToUlift (G := G) (φ := φ)
        (Ring.DirectLimit.of G (fun j k h ↦ φ j k h) i x) =
      Ring.DirectLimit.of (fun j : ULift.{w} ι ↦ G j.down) (fun j k h ↦ φ j.down k.down h)
        (ULift.up i) x := by
  -- Proof comment: this is again the defining `lift_of` formula.
  simpa [directLimit_originalToUlift] using
    (Ring.DirectLimit.lift_of
      (G := G)
      (f := fun j k h ↦ φ j k h)
      (P := Ring.DirectLimit (fun j : ULift.{w} ι ↦ G j.down) (fun j k h ↦ φ j.down k.down h))
      (g := fun i ↦
        Ring.DirectLimit.of (fun j : ULift.{w} ι ↦ G j.down) (fun j k h ↦ φ j.down k.down h)
          (ULift.up i))
      (Hg := by intro i j hij y; rfl)
      i x)

/-- Helper for Remark 10.127.12: reindexing a `Type`-indexed directed ring system along `ULift`
does not change
its direct limit. -/
private noncomputable def directLimit_uliftRingEquiv {ι : Type} [Preorder ι]
    (G : ι → Type u) [∀ i, CommRing (G i)]
    (φ : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ φ i j h)] :
    Ring.DirectLimit (fun i : ULift.{w} ι ↦ G i.down) (fun i j h ↦ φ i.down j.down h) ≃+*
      Ring.DirectLimit G (fun i j h ↦ φ i j h) :=
  RingEquiv.ofRingHom
    (directLimit_uliftToOriginal (G := G) (φ := φ))
    (directLimit_originalToUlift (G := G) (φ := φ))
    (by
      -- Proof comment: on every original stage generator, forgetting and then restoring the
      -- lifted index is definitionally the identity.
      apply Ring.DirectLimit.hom_ext
      intro i
      ext x
      simp [directLimit_uliftToOriginal, directLimit_originalToUlift])
    (by
      -- Proof comment: the same argument works on the lifted-index presentation.
      apply Ring.DirectLimit.hom_ext
      intro i
      ext x
      simp [directLimit_uliftToOriginal, directLimit_originalToUlift])

/-- Helper for Remark 10.127.12: the direct-limit equivalence sends a lifted generator to the
corresponding original generator. -/
@[simp] private theorem directLimit_uliftRingEquiv_of {ι : Type} [Preorder ι]
    (G : ι → Type u) [∀ i, CommRing (G i)]
    (φ : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ φ i j h)]
    (i : ULift.{w} ι) (x : G i.down) :
    directLimit_uliftRingEquiv (G := G) (φ := φ)
        (Ring.DirectLimit.of (fun j : ULift.{w} ι ↦ G j.down) (fun j k h ↦ φ j.down k.down h)
          i x) =
      Ring.DirectLimit.of G (fun j k h ↦ φ j k h) i.down x := by
  -- Proof comment: the forward map of the equivalence is the named forgetting morphism.
  exact directLimit_uliftToOriginal_of (G := G) (φ := φ) i x

namespace DirectedLocalHomApproximation

/-- Helper for Remark 10.127.12: the `ULift`-reindexed approximation inherits the original
colimit compatibility statement on each stage generator. -/
private theorem reindex_ulift_colimit_comm {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] {f : R →+* S}
    (A : DirectedLocalHomApproximation.{u, v, 0} f) :
    ((directLimit_uliftRingEquiv (G := A.SStage) (φ := A.targetMap)).trans A.targetColimit).toRingHom.comp
        (Ring.DirectLimit.map (fun i : ULift.{w} A.Λ ↦ A.stageMap i.down)
          (fun _ _ h ↦ A.comm h)) =
      f.comp
        ((directLimit_uliftRingEquiv (G := A.RStage) (φ := A.map)).trans A.colimitIso).toRingHom := by
  -- Proof comment: compare both ring homomorphisms on a lifted stage generator, collapse the two
  -- `ULift` direct-limit presentations back to the original ones, and then invoke the original
  -- colimit square of `A`.
  apply Ring.DirectLimit.hom_ext
  intro i
  ext x
  have hA :=
    congrArg
      (fun g : Ring.DirectLimit A.RStage (fun j k h ↦ A.map j k h) →+* S =>
        g (Ring.DirectLimit.of A.RStage (fun j k h ↦ A.map j k h) i.down x))
      A.colimit_comm
  simpa [RingHom.comp_apply] using hA

/-- Helper for Remark 10.127.12: reindex a directed local approximation along `ULift` so the
index type lands in the ambient universe `w`. -/
noncomputable def reindex_ulift {R : Type u} {S : Type v}
    [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] {f : R →+* S}
    (A : DirectedLocalHomApproximation.{u, v, 0} f) :
    DirectedLocalHomApproximation.{u, v, w} f :=
  { Λ := ULift.{w} A.Λ
    instPreorder := inferInstance
    instNonempty := inferInstance
    instDirectedOrder := inferInstance
    RStage := fun i ↦ A.RStage i.down
    instCommRingRStage := fun i ↦ A.instCommRingRStage i.down
    map := fun i j h ↦ A.map i.down j.down h
    instDirectedSystemRStage := ulift_directedSystem A.RStage A.map
    colimitIso := (directLimit_uliftRingEquiv (G := A.RStage) (φ := A.map)).trans A.colimitIso
    instIsLocalRingRStage := fun i ↦ A.instIsLocalRingRStage i.down
    SStage := fun i ↦ A.SStage i.down
    instCommRingSStage := fun i ↦ A.instCommRingSStage i.down
    instIsLocalRingSStage := fun i ↦ A.instIsLocalRingSStage i.down
    stageMap := fun i ↦ A.stageMap i.down
    stageMap_isLocalHom := fun i ↦ A.stageMap_isLocalHom i.down
    targetMap := fun i j h ↦ A.targetMap i.down j.down h
    instDirectedSystemTarget := ulift_directedSystem A.SStage A.targetMap
    comm := fun {_ _} h ↦ A.comm h
    targetColimit :=
      (directLimit_uliftRingEquiv (G := A.SStage) (φ := A.targetMap)).trans A.targetColimit
    colimit_comm := reindex_ulift_colimit_comm A
    source_essFiniteType := fun i ↦ A.source_essFiniteType i.down
    target_essFiniteType := fun i ↦ A.target_essFiniteType i.down }

/-- Helper for Remark 10.127.12: prime-localization transitions persist after `ULift` reindexing,
because the reindexed transition maps are literally the original ones. -/
private theorem hasPrimeLocalizationTransitions_reindex_ulift {R : Type u} {S : Type v}
    [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] {f : R →+* S}
    {A : DirectedLocalHomApproximation.{u, v, 0} f}
    (hA : A.HasPrimeLocalizationTransitions) :
    (A.reindex_ulift).HasPrimeLocalizationTransitions := by
  intro i j hij
  simpa [DirectedLocalHomApproximation.reindex_ulift] using hA (i := i.down) (j := j.down) hij

/-- Helper for Remark 10.127.12: localization-of-quotient transitions also persist after `ULift`
reindexing. -/
private theorem hasLocalizationOfQuotientTransitions_reindex_ulift {R : Type u} {S : Type v}
    [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] {f : R →+* S}
    {A : DirectedLocalHomApproximation.{u, v, 0} f}
    (hA : A.HasLocalizationOfQuotientTransitions) :
    (A.reindex_ulift).HasLocalizationOfQuotientTransitions := by
  intro i j hij
  simpa [DirectedLocalHomApproximation.reindex_ulift] using hA (i := i.down) (j := j.down) hij

/-- Helper for Remark 10.127.12: a failing prime-localization transition survives `ULift`
reindexing by lifting the same bad indices. -/
private theorem hasFailingPrimeLocalizationTransition_reindex_ulift {R : Type u} {S : Type v}
    [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] {f : R →+* S}
    {A : DirectedLocalHomApproximation.{u, v, 0} f}
    (hA : A.HasFailingPrimeLocalizationTransition) :
    (A.reindex_ulift).HasFailingPrimeLocalizationTransition := by
  rcases hA with ⟨i, j, hij, hbad⟩
  refine ⟨ULift.up i, ULift.up j, hij, ?_⟩
  simpa [DirectedLocalHomApproximation.reindex_ulift] using hbad

end DirectedLocalHomApproximation

/-- Helper for Remark 10.127.12: a surjective ring homomorphism is already a quotient map, hence a
localization of a quotient. -/
private theorem isLocalizationOfQuotient_of_surjective {A : Type u} {B : Type v} [CommRing A]
    [CommRing B] (f : A →+* B) (hf : Function.Surjective f) :
    RingHom.IsLocalizationOfQuotient f := by
  let e : A ⧸ RingHom.ker f ≃+* B := RingHom.quotientKerEquivOfSurjective hf
  let M : Submonoid (A ⧸ RingHom.ker f) := IsUnit.submonoid _
  letI : Algebra (A ⧸ RingHom.ker f) B := e.toRingHom.toAlgebra
  letI : IsLocalization M (A ⧸ RingHom.ker f) := IsLocalization.at_units _ fun _ hx ↦ hx
  let eAlg : (A ⧸ RingHom.ker f) ≃ₐ[A ⧸ RingHom.ker f] B :=
    AlgEquiv.ofRingEquiv (f := e) fun _ ↦ rfl
  letI : IsLocalization M B := IsLocalization.isLocalization_of_algEquiv M eAlg
  -- Proof comment: package the quotient presentation and then identify it with the original
  -- surjective map on each source element.
  refine ⟨RingHom.ker f, inferInstance, M, inferInstance, ?_⟩
  ext x
  simpa [M, e, RingHom.algebraMap_toAlgebra] using
    (RingHom.quotientKerEquivOfSurjective_apply_mk (f := f) hf x)

/-- Helper for Remark 10.127.12: every self-transition base-change map is surjective because
`s ⊗ 1` maps back to `s`. -/
private theorem stageBaseChangeMap_self_surjective {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] {f : R →+* S} (A : DirectedLocalHomApproximation f) (i : A.Λ) :
    Function.Surjective (A.stageBaseChangeMap (i := i) (j := i) le_rfl) := by
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra (A.RStage i) (A.RStage i) := (A.map i i le_rfl).toAlgebra
  intro s
  refine ⟨s ⊗ₜ[A.RStage i] (1 : A.RStage i), ?_⟩
  -- Proof comment: the self-transition sends `s ⊗ 1` to `s * 1`, because both directed-system
  -- self maps act as the identity on elements.
  have htarget : A.targetMap i i le_rfl s = s := by
    simpa using (DirectedSystem.map_self (f := fun j k h ↦ A.targetMap j k h) s)
  calc
    A.stageBaseChangeMap (i := i) (j := i) le_rfl (s ⊗ₜ[A.RStage i] (1 : A.RStage i)) =
      A.targetMap i i le_rfl s * A.stageMap i (1 : A.RStage i) := by
        simpa using
          (DirectedLocalHomApproximation.stageBaseChangeMap_tmul' A (i := i) (j := i) le_rfl s
            (1 : A.RStage i))
    _ = s * 1 := by rw [htarget, map_one]
    _ = s := by simp

/-- Helper for Remark 10.127.12: the singleton target transition is definitionally the identity
map on `ULift 𝔽₂`. -/
private theorem lifted_goodSystem_self_targetMap_eq_id
    (h : (PUnit.unit : PUnit) ≤ PUnit.unit) :
    lifted_goodSystem.targetMap PUnit.unit PUnit.unit h = RingHom.id _ := by
  -- Proof comment: the singleton target system has only identity transition maps.
  rfl

/-- Helper for Remark 10.127.12: the singleton self-transition base-change source identifies with
the target ring by the tensor right-unit equivalence. -/
private noncomputable abbrev lifted_goodSystem_self_stageBaseChange_ridEquiv :
    (ULift.{v} (ZMod 2) ⊗[ULift.{u} (ZMod 2)] ULift.{u} (ZMod 2)) ≃+* ULift.{v} (ZMod 2) :=
  -- TODO: normalize the owner self-transition tensor source to the standard right-unit tensor
  -- presentation and then identify it with `Algebra.TensorProduct.rid`.
  sorry

/-- Helper for Remark 10.127.12: the singleton self-transition base-change map becomes the identity
after collapsing the tensor source by the right-unit equivalence. -/
private theorem lifted_goodSystem_self_stageBaseChange_rid_forward :
    ∀ z : ULift.{v} (ZMod 2) ⊗[ULift.{u} (ZMod 2)] ULift.{u} (ZMod 2),
      lifted_goodSystem.stageBaseChangeMap (i := PUnit.unit) (j := PUnit.unit) le_rfl z =
        (RingHom.id (ULift.{v} (ZMod 2)))
          (lifted_goodSystem_self_stageBaseChange_ridEquiv z) := by
  -- TODO: prove the owner self-transition formula on pure tensors after the missing tensor-source
  -- normalization lemma is available, then extend by tensor induction.
  sorry

/-- Helper for Remark 10.127.12: a prime-localization witness on an owner base-change map can be
transported across a source ring equivalence when the transported map is given in forward form. -/
private theorem exists_prime_localization_witness_of_domain_equiv_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] {f : R →+* S}
    (A : DirectedLocalHomApproximation f) {i j : A.Λ} (h : i ≤ j)
    {T : Type*} [CommRing T] (e : A.targetStageBaseChange h ≃+* T)
    (φ : T →+* A.SStage j)
    (hφ : ∀ z : A.targetStageBaseChange h, A.stageBaseChangeMap h z = φ (e z))
    (ht : A.TransitionIsLocalizationAtPrime h) :
    ∃ p : Ideal T, ∃ _ : p.IsPrime, p.primeCompl.IsLocalizationMap φ := by
  rcases ht with ⟨q, hq, hmapq⟩
  let p : Ideal T := Ideal.comap e.symm.toRingHom q
  letI : q.IsPrime := hq
  have hp : p.IsPrime := by
    -- Proof comment: prime ideals pull back along ring homomorphisms, so the transported prime
    -- on the equivalent source ring stays prime.
    simpa [p] using Ideal.comap_isPrime e.symm.toRingHom q
  letI : Algebra (A.targetStageBaseChange h) (A.SStage j) := (A.stageBaseChangeMap h).toAlgebra
  haveI hlocq : IsLocalization q.primeCompl (A.SStage j) :=
    (isLocalization_iff_isLocalizationMap
      (M := q.primeCompl) (S := A.SStage j)).mpr hmapq
  letI : Algebra T (A.SStage j) := φ.toAlgebra
  have hpmap : p.primeCompl.map e.symm.toMonoidHom = q.primeCompl := by
    -- Proof comment: `p` was defined as the pullback of `q` along `e.symm`, so complements match
    -- after mapping along the same equivalence.
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [p, Ideal.mem_comap] using hy
    · intro hx
      refine ⟨e x, ?_, by simp⟩
      simpa [p, Ideal.mem_comap] using hx
  have htransport :
      IsLocalization p.primeCompl (A.SStage j) := by
    -- Proof comment: reinterpret the transported source algebra as `φ` using the forward
    -- compatibility, then move the localization structure across `e.symm`.
    exact IsLocalization.of_ringEquiv_left
      (e := e.symm)
      hpmap
      (fun x ↦ by
        change φ x = A.stageBaseChangeMap h (e.symm x)
        simpa using (hφ (e.symm x)).symm)
  letI : p.IsPrime := hp
  exact ⟨p, hp,
    (isLocalization_iff_isLocalizationMap
      (M := p.primeCompl) (S := A.SStage j)).mp htransport⟩

/-- Helper for Remark 10.127.12: the unique transition in the good singleton system is a
localization at the maximal ideal of the target stage. -/
private theorem lifted_goodSystem_hasPrimeLocalizationTransitions :
    lifted_goodSystem.HasPrimeLocalizationTransitions := by
  -- TODO: reduce to the unique singleton transition, transport the identity localization witness
  -- across `lifted_goodSystem_self_stageBaseChange_ridEquiv`, and package it as a prime
  -- localization.
  sorry

/-- Helper for Remark 10.127.12: the lifted projection `ULift (𝔽₂[ε]) → ULift 𝔽₂` is surjective. -/
private theorem lifted_dualNumber_fst_surjective :
    Function.Surjective lifted_dualNumber_fst := by
  intro y
  refine ⟨ULift.up ((TrivSqZeroExt.inl y.down : (ZMod 2)[ε])), ?_⟩
  ext
  rfl

/-- Helper for Remark 10.127.12: every prime ideal of `ULift (𝔽₂[ε])` is the maximal ideal, so
its prime complement is exactly the unit submonoid. -/
private theorem ulift_dualNumber_primeCompl_eq_isUnit_submonoid
    (q : Ideal (ULift.{v} ((ZMod 2)[ε]))) [hq : q.IsPrime] :
    q.primeCompl = IsUnit.submonoid (ULift.{v} ((ZMod 2)[ε])) := by
  let q' : Ideal ((ZMod 2)[ε]) := Ideal.comap
    (ULift.ringEquiv.symm.toRingHom : (ZMod 2)[ε] →+* ULift.{v} ((ZMod 2)[ε])) q
  have hq' : q'.IsPrime := by
    simpa [q'] using Ideal.comap_isPrime
      (ULift.ringEquiv.symm.toRingHom : (ZMod 2)[ε] →+* ULift.{v} ((ZMod 2)[ε])) q
  have hεsq : (ULift.up (ε : (ZMod 2)[ε]) : ULift.{v} ((ZMod 2)[ε])) ^ 2 = 0 := by
    apply ULift.ext
    ext <;> simp [pow_two]
  have hεmem : (ε : (ZMod 2)[ε]) ∈ q' := by
    apply Ideal.mem_comap.mpr
    have hpow : (ULift.up (ε : (ZMod 2)[ε]) : ULift.{v} ((ZMod 2)[ε])) ^ 2 ∈ q := by
      simpa [hεsq] using (show (0 : ULift.{v} ((ZMod 2)[ε])) ∈ q from Ideal.zero_mem q)
    exact hq.mem_of_pow_mem 2 hpow
  have hεne : (ε : (ZMod 2)[ε]) ≠ 0 := by
    intro h
    have hsnd := congrArg TrivSqZeroExt.snd h
    simpa using hsnd
  have hq'span : q' = Ideal.span ({(ε : (ZMod 2)[ε])} : Set ((ZMod 2)[ε])) := by
    rcases DualNumber.ideal_trichotomy q' with hbot | hspan | htop
    · exfalso
      rw [hbot] at hεmem
      exact hεne hεmem
    · exact hspan
    · exact False.elim (hq'.ne_top htop)
  have hbase :
      q'.primeCompl = IsUnit.submonoid ((ZMod 2)[ε]) := by
    ext x
    change x ∉ q' ↔ x ∈ IsUnit.submonoid ((ZMod 2)[ε])
    rw [hq'span, ← DualNumber.maximalIdeal_eq_span_singleton_eps]
    change x ∉ IsLocalRing.maximalIdeal ((ZMod 2)[ε]) ↔
      x ∈ IsUnit.submonoid ((ZMod 2)[ε])
    constructor
    · intro hx
      simpa using (IsLocalRing.notMem_maximalIdeal (R := (ZMod 2)[ε]) (x := x)).mp hx
    · intro hx
      exact (IsLocalRing.notMem_maximalIdeal (R := (ZMod 2)[ε]) (x := x)).mpr (by
        simpa using hx)
  ext x
  cases x with
  | up x =>
      change (ULift.up x : ULift.{v} ((ZMod 2)[ε])) ∈ q.primeCompl ↔
        IsUnit (ULift.up x : ULift.{v} ((ZMod 2)[ε]))
      change x ∈ q'.primeCompl ↔ IsUnit (ULift.up x : ULift.{v} ((ZMod 2)[ε]))
      rw [hbase]
      constructor
      · intro hx
        exact hx.map (ULift.ringEquiv.symm.toRingHom : (ZMod 2)[ε] →+* ULift.{v} ((ZMod 2)[ε]))
      · intro hx
        exact hx.map (ULift.ringEquiv.toRingHom : ULift.{v} ((ZMod 2)[ε]) →+* (ZMod 2)[ε])

/-- Helper for Remark 10.127.12: the lifted dual-number generator `ε` is nonzero in
`ULift (𝔽₂[ε])`. -/
private theorem ulift_dualNumber_eps_ne_zero :
    (ULift.up (ε : (ZMod 2)[ε]) : ULift.{v} ((ZMod 2)[ε])) ≠ 0 := by
  intro hzero
  have hsnd := congrArg (fun x : ULift.{v} ((ZMod 2)[ε]) ↦ TrivSqZeroExt.snd x.down) hzero
  simpa using hsnd

/-- Helper for Remark 10.127.12: the lifted projection `ULift (𝔽₂[ε]) → ULift 𝔽₂` cannot be a
localization at a prime, because that would force it to be a localization at units and hence
bijective, contradicting the killed nonzero element `ε`. -/
private theorem lifted_dualNumber_fst_not_isLocalizationMap_at_prime :
    ¬ ∃ q : Ideal (ULift.{v} ((ZMod 2)[ε])),
        ∃ _ : q.IsPrime, q.primeCompl.IsLocalizationMap lifted_dualNumber_fst := by
  intro h
  rcases h with ⟨q, hq, hmapq⟩
  letI : q.IsPrime := hq
  have hmapUnits :
      (IsUnit.submonoid (ULift.{v} ((ZMod 2)[ε]))).IsLocalizationMap lifted_dualNumber_fst := by
    rwa [ulift_dualNumber_primeCompl_eq_isUnit_submonoid q] at hmapq
  letI : Algebra (ULift.{v} ((ZMod 2)[ε])) (ULift.{v} (ZMod 2)) :=
    lifted_dualNumber_fst.toAlgebra
  have hloc :
      IsLocalization (IsUnit.submonoid (ULift.{v} ((ZMod 2)[ε]))) (ULift.{v} (ZMod 2)) :=
    (isLocalization_iff_isLocalizationMap
      (M := IsUnit.submonoid (ULift.{v} ((ZMod 2)[ε])))
      (S := ULift.{v} (ZMod 2))).mpr hmapUnits
  let e :
      ULift.{v} ((ZMod 2)[ε]) ≃ₐ[ULift.{v} ((ZMod 2)[ε])] ULift.{v} (ZMod 2) :=
    IsLocalization.atUnits
      (R := ULift.{v} ((ZMod 2)[ε]))
      (M := IsUnit.submonoid (ULift.{v} ((ZMod 2)[ε])))
      (S := ULift.{v} (ZMod 2))
      (by intro x hx; simpa using hx)
  have heq : e.toRingHom = lifted_dualNumber_fst := by
    ext x
    rfl
  have hinj : Function.Injective lifted_dualNumber_fst := by
    rw [← heq]
    exact e.injective
  have hzero :
      lifted_dualNumber_fst (ULift.up (ε : (ZMod 2)[ε]) : ULift.{v} ((ZMod 2)[ε])) = 0 := by
    rfl
  exact ulift_dualNumber_eps_ne_zero (hinj hzero)

/-- Helper for Remark 10.127.12: the bad false-to-true base-change map becomes the lifted dual
number projection after collapsing the tensor source by the right-unit equivalence. -/
private theorem bool_false_le_true : (false : Bool) ≤ true := by
  decide

/-- Helper for Remark 10.127.12: the bad false-to-true base-change source identifies with the
dual-number stage by the tensor right-unit equivalence. -/
private noncomputable abbrev lifted_badSystem_false_true_stageBaseChange_ridEquiv :
    lifted_badSystem.targetStageBaseChange (i := false) (j := true) bool_false_le_true ≃+*
      ULift.{v} ((ZMod 2)[ε]) :=
  -- Proof comment: the nontrivial base-change source is again the standard right-unit tensor
  -- product over `ULift 𝔽₂`.
  -- TODO: identify the owner false-to-true tensor source with the right-unit tensor source over
  -- `lifted_zmodTwo_to_dualNumber`.
  sorry

/-- Helper for Remark 10.127.12: the bad false-to-true base-change map becomes the lifted dual
number projection after collapsing the tensor source by the right-unit equivalence. -/
private theorem lifted_badSystem_false_true_stageBaseChange_rid_forward :
    ∀ z : lifted_badSystem.targetStageBaseChange (i := false) (j := true) bool_false_le_true,
      lifted_badSystem.stageBaseChangeMap (i := false) (j := true) bool_false_le_true z =
        lifted_dualNumber_fst (lifted_badSystem_false_true_stageBaseChange_ridEquiv z) := by
  -- TODO: after the owner-source identification is explicit, prove the false-to-true forward
  -- formula by tensor induction and the relation `lifted_dualNumber_fst_comp_inl`.
  sorry

/-- Helper for Remark 10.127.12: the unique nontrivial transition in the bad system is a
localization of a quotient but not a localization at a prime. -/
private theorem lifted_badSystem_false_true_transition_properties
    (hFT : (false : Bool) ≤ true) :
    RingHom.IsLocalizationOfQuotient (lifted_badSystem.stageBaseChangeMap hFT) ∧
      ¬ lifted_badSystem.TransitionIsLocalizationAtPrime hFT := by
  -- TODO: rewrite to the canonical `false ≤ true` proof, deduce surjectivity from the forward
  -- formula, and transport any prime-localization witness to `lifted_dualNumber_fst`.
  sorry

/-- Helper for Remark 10.127.12: once the two explicit lifted systems are packaged, the good one
has prime-localization transitions and the bad one fails at a prime-localization transition. -/
private theorem lifted_systems_have_target_properties :
    lifted_goodSystem.HasPrimeLocalizationTransitions ∧
      lifted_badSystem.HasLocalizationOfQuotientTransitions ∧
        lifted_badSystem.HasFailingPrimeLocalizationTransition :=
  -- TODO: combine the good singleton transition theorem, the bad false-to-true transition
  -- theorem, and the self-transition surjectivity lemma to package the two explicit systems.
  sorry

/-- Helper for Remark 10.127.12: the good approximation system has explicit index universe `0`,
so it can be reindexed cleanly into any ambient approximation universe. -/
private noncomputable abbrev goodSystem₀ :
    DirectedLocalHomApproximation.{u, v, 0}
      (RingHom.ulift (RingHom.id (ZMod 2))) :=
  lifted_goodSystem

/-- Helper for Remark 10.127.12: the bad approximation system has explicit index universe `0`,
so it can be reindexed cleanly into any ambient approximation universe. -/
private noncomputable abbrev badSystem₀ :
    DirectedLocalHomApproximation.{u, v, 0}
      (RingHom.ulift (RingHom.id (ZMod 2))) :=
  lifted_badSystem

-- Proof sketch: use the explicit `k = 𝔽₂` example from the remark. The system with
-- `Sₙ = Rₙ / (z, yₙ²)` gives an approximation of the map `R → R / zR` whose successor base-change
-- maps kill `1 ⊗ y_{n + 1}²`, so some transition is not a localization at a prime ideal. Replacing
-- those targets by `Rₙ / zRₙ` gives another approximation of the same local essentially finite
-- presentation map whose transition maps are localizations at prime ideals.
/-- Remark 10.127.12: there exists a local homomorphism of local rings which is essentially of
finite presentation and admits both a good approximation system whose transition maps are
localizations at prime ideals and a different approximation system whose transition maps are still
localizations of quotients but fail to be localizations at prime ideals. -/
theorem exists_essentially_finitePresentation_local_map_with_wrong_approximation_system :
    ∃ (R : Type u) (S : Type v) (_ : CommRing R) (_ : CommRing S) (_ : IsLocalRing R)
      (_ : IsLocalRing S) (f : R →+* S) (_ : IsLocalHom f)
      (_ : RingHom.EssFinitePresentation f) (goodSystem : DirectedLocalHomApproximation f),
      goodSystem.HasPrimeLocalizationTransitions ∧
        ∃ badSystem : DirectedLocalHomApproximation f,
            badSystem.HasLocalizationOfQuotientTransitions ∧
              badSystem.HasFailingPrimeLocalizationTransition := by
  have hprops := lifted_systems_have_target_properties
  rcases hprops with ⟨hgood, hbadQuot, hbadPrime⟩
  have hgood₀ : goodSystem₀.HasPrimeLocalizationTransitions := by
    intro i j hij
    simpa [goodSystem₀] using hgood (i := i) (j := j) hij
  have hbadQuot₀ : badSystem₀.HasLocalizationOfQuotientTransitions := by
    intro i j hij
    simpa [badSystem₀] using hbadQuot (i := i) (j := j) hij
  have hbadPrime₀ : badSystem₀.HasFailingPrimeLocalizationTransition := by
    simpa [badSystem₀] using hbadPrime
  refine ⟨ULift.{u} (ZMod 2), ULift.{v} (ZMod 2), inferInstance, inferInstance,
    inferInstance, inferInstance, RingHom.ulift (RingHom.id (ZMod 2)),
    ulift_zmodTwo_id_isLocalHom, ?_, goodSystem₀.reindex_ulift, ?_⟩
  · simpa using ulift_zmodTwo_id_essFinitePresentation
  · refine ⟨?_, ?_⟩
    · exact DirectedLocalHomApproximation.hasPrimeLocalizationTransitions_reindex_ulift
        (A := goodSystem₀) hgood₀
    · refine ⟨badSystem₀.reindex_ulift, ?_⟩
      exact ⟨DirectedLocalHomApproximation.hasLocalizationOfQuotientTransitions_reindex_ulift
          (A := badSystem₀) hbadQuot₀,
        DirectedLocalHomApproximation.hasFailingPrimeLocalizationTransition_reindex_ulift
          (A := badSystem₀) hbadPrime₀⟩

end
