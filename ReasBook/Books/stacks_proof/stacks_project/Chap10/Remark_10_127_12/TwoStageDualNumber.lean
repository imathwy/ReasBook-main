import stacks_proof.stacks_project.Chap10.Remark_10_127_12.OneStageSystems

universe u v w w₀

section

open DirectedLocalHomApproximation
open scoped DualNumber TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Helper for Remark 10.127.12: `true ≤ false` does not occur in the `Bool`-indexed two-stage
systems used below. -/
theorem bool_true_not_le_false : ¬ (true ≤ false) := by
  decide

/-- Helper for Remark 10.127.12: a two-stage system has a lower stage `A` and a top stage `B`
indexed by `false ≤ true`. -/
abbrev two_stageStage (A : Type w) (B : Type w) : Bool → Type w
  | false => A
  | true => B

/-- Helper for Remark 10.127.12: each stage of the two-stage system inherits the ring structure of
the corresponding endpoint ring. -/
instance two_stageStageCommRing {A : Type w} {B : Type w} [CommRing A] [CommRing B] :
    (i : Bool) → CommRing (two_stageStage A B i)
  | false => inferInstance
  | true => inferInstance

/-- Helper for Remark 10.127.12: the only nontrivial transition in a two-stage system is the map
from the lower stage to the top stage. -/
def two_stageMap {A : Type w} {B : Type w} [CommRing A] [CommRing B] (τ : A →+* B) :
    ∀ i j : Bool, i ≤ j → two_stageStage A B i →+* two_stageStage A B j
  | false, false, _ => RingHom.id A
  | false, true, _ => τ
  | true, true, _ => RingHom.id B
  | true, false, h => False.elim (bool_true_not_le_false h)

/-- Helper for Remark 10.127.12: the identity transitions of the two-stage system are literally
the identity maps on the corresponding stages. -/
theorem two_stageMap_self {A : Type w} {B : Type w} [CommRing A] [CommRing B]
    (τ : A →+* B) :
    ∀ i (x : two_stageStage A B i), two_stageMap τ i i le_rfl x = x
  | false, x => rfl
  | true, x => rfl

/-- Helper for Remark 10.127.12: the two-stage transition maps compose exactly as expected. -/
theorem two_stageMap_map {A : Type w} {B : Type w} [CommRing A] [CommRing B]
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
def two_stageTopDesc {A : Type w} {B : Type w} [CommRing A] [CommRing B] (τ : A →+* B) :
    (i : Bool) → two_stageStage A B i →+* B
  | false => τ
  | true => RingHom.id B

/-- Helper for Remark 10.127.12: the map from a two-stage system to its top stage is compatible
with the unique nontrivial transition. -/
theorem two_stage_top_desc_compatible {A : Type w} {B : Type w}
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
theorem two_stage_top_desc_compatible_apply {A : Type w} {B : Type w}
    [CommRing A] [CommRing B] (τ : A →+* B) :
    ∀ (i j : Bool) (hij : i ≤ j) (x : two_stageStage A B i),
      two_stageTopDesc τ j (two_stageMap τ i j hij x) = two_stageTopDesc τ i x := by
  intro i j hij x
  exact congrArg (fun g : two_stageStage A B i →+* B => g x)
    (two_stage_top_desc_compatible τ hij)

/-- Helper for Remark 10.127.12: the `Bool` two-stage maps satisfy the directed-system relations. -/
instance two_stageDirectedSystem {A : Type w} {B : Type w} [CommRing A] [CommRing B]
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
noncomputable def two_stage_top_directLimitToTopHom {A : Type w} {B : Type w}
    [CommRing A] [CommRing B] (τ : A →+* B) :
    Ring.DirectLimit (two_stageStage A B) (fun i j h ↦ two_stageMap τ i j h) →+* B :=
  Ring.DirectLimit.lift
    (two_stageStage A B) (fun i j h ↦ two_stageMap τ i j h) B
    (two_stageTopDesc τ) (two_stage_top_desc_compatible_apply τ)

/-- Helper for Remark 10.127.12: the direct-limit comparison map is the identity on the top-stage
generator. -/
@[simp] theorem two_stage_top_directLimitToTopHom_of_true {A : Type w} {B : Type w}
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
@[simp] theorem two_stage_top_directLimitToTopHom_of_false {A : Type w} {B : Type w}
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
theorem two_stage_top_directLimit_ofTop_comp_toTop_eq_id {A : Type w} {B : Type w}
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
noncomputable def two_stage_top_directLimitRingEquiv {A : Type w} {B : Type w}
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
@[simp] theorem two_stage_top_directLimitRingEquiv_of_true {A : Type w} {B : Type w}
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
@[simp] theorem two_stage_top_directLimitRingEquiv_of_false {A : Type w} {B : Type w}
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
theorem ulift_zmodTwo_id_isLocalHom :
    let R : Type u := ULift.{u} (ZMod 2)
    let S : Type v := ULift.{v} (ZMod 2)
    let f : R →+* S := RingHom.ulift (RingHom.id (ZMod 2))
    IsLocalHom f := by
  dsimp
  -- Surjectivity of the lifted identity lets us invoke the standard local-hom criterion.
  exact (ringHom_ulift_id_bijective (A := ZMod 2)).2.isLocalHom

/-- Helper for Remark 10.127.12: the lifted identity map between the two `ULift 𝔽₂` universes is
essentially of finite type. -/
theorem ulift_zmodTwo_id_essFiniteType :
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
theorem ulift_zmodTwo_punit_square_commutes {i j : PUnit} (h : i ≤ j) :
    ((RingHom.ulift.{u, v} (RingHom.id (ZMod 2))) :
        ULift.{u} (ZMod 2) →+* ULift.{v} (ZMod 2)).comp (RingHom.id _) =
      (RingHom.id _).comp (RingHom.ulift.{u, v} (RingHom.id (ZMod 2))) := by
  -- Proof comment: every source and target transition is the identity in the singleton system.
  ext x
  rfl

/-- Helper for Remark 10.127.12: the next proof step is to package the lifted `𝔽₂` identity map
into an explicit approximation system whose transitions are localizations at prime ideals. -/
noncomputable def lifted_goodSystem :
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
instance zmodTwo_dualNumber_isLocalRing : IsLocalRing ((ZMod 2)[ε]) := by
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
abbrev lifted_zmodTwo_to_dualNumber :
    ULift.{u} (ZMod 2) →+* ULift.{v} ((ZMod 2)[ε]) :=
  RingHom.ulift ((TrivSqZeroExt.inlAlgHom (ZMod 2) (ZMod 2) (ZMod 2)).toRingHom)

/-- Helper for Remark 10.127.12: the unique nontrivial target transition in the bad system is the
universe lift of the projection `𝔽₂[ε] → 𝔽₂`. -/
abbrev lifted_dualNumber_fst :
    ULift.{v} ((ZMod 2)[ε]) →+* ULift.{v} (ZMod 2) :=
  RingHom.ulift ((TrivSqZeroExt.fstHom (ZMod 2) (ZMod 2) (ZMod 2)).toRingHom)

/-- Helper for Remark 10.127.12: the inclusion `𝔽₂ → 𝔽₂[ε]` is a local map because units are
detected on the scalar part. -/
theorem zmodTwo_to_dualNumber_isLocalHom :
    IsLocalHom ((TrivSqZeroExt.inlAlgHom (ZMod 2) (ZMod 2) (ZMod 2)).toRingHom) := by
  refine ⟨fun a ha ↦ ?_⟩
  -- Proof comment: the image of `a` is the dual number `inl a`, and `isUnit_inl_iff` reads the
  -- unit test back on the base field element.
  simpa using (TrivSqZeroExt.isUnit_inl_iff (R := ZMod 2) (M := ZMod 2) (r := a)).mp ha

/-- Helper for Remark 10.127.12: the lifted inclusion `ULift 𝔽₂ → ULift 𝔽₂[ε]` remains a local
map. -/
theorem ulift_zmodTwo_to_dualNumber_isLocalHom :
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
theorem ulift_zmodTwo_to_dualNumber_essFiniteType :
    lifted_zmodTwo_to_dualNumber.EssFiniteType := by
  -- Proof comment: transport the dual-number finite-type witness across the source and target
  -- `ULift` ring equivalences.
  simpa [lifted_zmodTwo_to_dualNumber] using
    ringHom_ulift_essFiniteType
      (f := (TrivSqZeroExt.inlAlgHom (ZMod 2) (ZMod 2) (ZMod 2)).toRingHom)
      zmodTwo_to_dualNumber_essFiniteType

/-- Helper for Remark 10.127.12: the bad target transition followed by the bad lower-stage map is
the lifted identity on `𝔽₂`. -/
theorem lifted_dualNumber_fst_comp_inl :
    RingHom.ulift (RingHom.id (ZMod 2)) =
      lifted_dualNumber_fst.comp lifted_zmodTwo_to_dualNumber := by
  -- Proof comment: on each element, the projection kills the square-zero part introduced by the
  -- inclusion and recovers the original field element.
  ext x
  rfl

/-- Helper for Remark 10.127.12: a stagewise map from the constant two-stage source system to a
target two-stage system is determined by its lower and upper components. -/
abbrev two_stageStageMap {A : Type u} {C : Type v} {B : Type v}
    [CommRing A] [CommRing C] [CommRing B] (σ₀ : A →+* C) (σ₁ : A →+* B) :
    (i : Bool) → two_stageStage A A i →+* two_stageStage C B i
  | false => σ₀
  | true => σ₁

/-- Helper for Remark 10.127.12: the stagewise map into a two-stage target commutes with the
unique nontrivial transition exactly when the top-stage map factors through that transition. -/
theorem two_stageStageMap_comm {A : Type u} {C : Type v} {B : Type v}
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
theorem two_stage_colimit_comm {A : Type u} {C : Type v} {B : Type v}
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
noncomputable def lifted_badSystem :
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

end
