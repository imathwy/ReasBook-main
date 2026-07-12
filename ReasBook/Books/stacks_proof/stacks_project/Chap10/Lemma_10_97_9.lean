import Mathlib
import StacksProject_2024.Chap10.Lemma_10_77_7
import StacksProject_2024.Chap10.Lemma_10_96_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section
open scoped TensorProduct

universe u v w

section

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {P : Type v} [AddCommGroup P] [Module R P]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-
Domain triage:
- primary domain: adic completion of surjections and splitting of the completed short exact
  sequence;
- sampled owner-style declarations in this domain:
  `AdicCompletion.map_surjective`,
  `completionShortComplex_shortExact_of_flat_cokernel`,
  `projective_of_projective_quotient_of_isNilpotent_of_flat`,
  `Module.projective_lifting_property`;
- best owner abstraction: the completed surjection `AdicCompletion.map I g`, equivalently the
  completed short exact sequence furnished by `completionShortComplex_shortExact_of_flat_cokernel`;
  stagewise projectivity is only a proof-side bridge, not the public core.
- primitive data: the surjection `g : P →ₗ[R] M`, the ideal `I`, flatness of `M`, and the
  projective quotient hypothesis on `M ⧸ (I • ⊤)`;
- derived API: a section of the completed surjection `P^∧ → M^∧`.

Layer classification:
- `source-facing`: the public theorem below, stated as existence of a section of the completed
  surjection;
- `core/canonical`: `AdicCompletion.map`, `AdicCompletion.map_surjective`, and the completed short
  exact sequence API from Lemma `10.96.1`;
- `bridge/view`: the stagewise projectivity theorem
  `projective_of_projective_quotient_of_isNilpotent_of_flat`, used to build compatible splittings
  modulo `I ^ (n + 1)`.
-/

-- Proof sketch: for each `n`, apply Lemma `10.77.7` to the induced nilpotent ideal in
-- `R ⧸ I ^ (n + 1)` to show that `M ⧸ (I ^ (n + 1) • ⊤)` is projective over `R ⧸ I ^ (n + 1)`.
-- Hence the surjection `P ⧸ (I ^ (n + 1) • ⊤) → M ⧸ (I ^ (n + 1) • ⊤)` admits a section. Choose
-- these sections compatibly; passing to the inverse limit then yields a section of the completed
-- surjection `AdicCompletion.map I g`. Lemma `10.96.1` supplies the canonical completion map and
-- its surjectivity.
/-- Helper for Lemma 10.97.9: every positive quotient stage of a flat module stays flat over the
corresponding quotient ring. -/
lemma flat_reduceModIdeal_pow_of_flat (n : ℕ) [Module.Flat R M] :
    Module.Flat (R ⧸ I ^ (n + 1)) (M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)) := by
  -- Base change identifies the quotient module with the tensor product over the quotient ring.
  let e :
      (M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)) ≃ₗ[R ⧸ I ^ (n + 1)]
        ((R ⧸ I ^ (n + 1)) ⊗[R] M) :=
    (TensorProduct.quotTensorEquivQuotSMul M (I ^ (n + 1))).symm.extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  let hTensor : Module.Flat (R ⧸ I ^ (n + 1)) ((R ⧸ I ^ (n + 1)) ⊗[R] M) :=
    Module.Flat.baseChange (R := R) (S := R ⧸ I ^ (n + 1)) (M := M)
  letI : Module.Flat (R ⧸ I ^ (n + 1)) ((R ⧸ I ^ (n + 1)) ⊗[R] M) := hTensor
  -- Transport flatness back along the canonical quotient-tensor equivalence.
  exact Module.Flat.of_linearEquiv e

/-- Helper for Lemma 10.97.9: the first-stage quotient map `P / IP → M / IM` admits a section from
the assumed projectivity of `M / IM`. -/
lemma exists_base_stage_section
    (g : P →ₗ[R] M) [Module.Flat R M] (hg : Function.Surjective g)
    (hquot : Module.Projective (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) :
    ∃ σ : M ⧸ (I • ⊤ : Submodule R M) →ₗ[R ⧸ I] P ⧸ (I • ⊤ : Submodule R P),
      (g.reduceModIdeal I).comp σ = LinearMap.id := by
  -- The base stage is the direct projective lifting step from the source proof.
  have hsurj : Function.Surjective (g.reduceModIdeal I) := by
    intro x
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) x
    obtain ⟨p, rfl⟩ := hg m
    refine ⟨Submodule.mkQ (I • (⊤ : Submodule R P)) p, ?_⟩
    rfl
  exact Module.projective_lifting_property (g.reduceModIdeal I)
    (LinearMap.id : M ⧸ (I • ⊤ : Submodule R M) →ₗ[R ⧸ I] M ⧸ (I • ⊤ : Submodule R M))
    hsurj

/-- Helper for Lemma 10.97.9: surjectivity of `g` descends to every quotient stage. -/
lemma reduceModIdeal_surjective
    (g : P →ₗ[R] M) (hg : Function.Surjective g) (J : Ideal R) :
    Function.Surjective (g.reduceModIdeal J) := by
  -- Lift a quotient class by choosing a representative and then using surjectivity of `g`.
  intro x
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (J • (⊤ : Submodule R M)) x
  obtain ⟨p, rfl⟩ := hg m
  refine ⟨Submodule.mkQ (J • (⊤ : Submodule R P)) p, ?_⟩
  rfl

/-- Helper for Lemma 10.97.9: quotient reduction agrees with `reduceModIdeal` after restricting
scalars, without forcing the source and target modules to live in the same universe. -/
lemma quotientMapByIdeal_eq_reduceModIdeal_restrictScalars_univ
    {P' : Type*} [AddCommGroup P'] [Module R P']
    {Q' : Type*} [AddCommGroup Q'] [Module R Q']
    (J : Ideal R) (φ : P' →ₗ[R] Q') :
    φ.quotientMapByIdeal J = (φ.reduceModIdeal J).restrictScalars R := by
  -- Both quotient maps are determined by their action on representatives.
  apply DFunLike.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (J • (⊤ : Submodule R P')) x
  rfl

/-- Helper for Lemma 10.97.9: exactness descends to quotient modules in mixed universes once the
right map is surjective. -/
lemma quotientMapByIdeal_exact_of_exact_surjective_univ
    {P' : Type*} [AddCommGroup P'] [Module R P']
    {Q' : Type*} [AddCommGroup Q'] [Module R Q']
    {T' : Type*} [AddCommGroup T'] [Module R T']
    (J : Ideal R) (φ : P' →ₗ[R] Q') (ψ : Q' →ₗ[R] T')
    (hExact : Function.Exact φ ψ) (hψ : Function.Surjective ψ) :
    Function.Exact (φ.quotientMapByIdeal J) (ψ.quotientMapByIdeal J) := by
  -- Descend exactness through the quotient API and identify the image condition by surjectivity.
  refine
    (Function.Exact.exact_mapQ_iff (f := φ) (g := ψ) hExact
      (Submodule.smul_top_le_comap_smul_top J φ)
      (Submodule.smul_top_le_comap_smul_top J ψ)).2 ?_
  simpa [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hψ]

/-- Helper for Lemma 10.97.9: over a nilpotent thickening, a flat module with projective closed
fiber is already projective. -/
lemma projective_of_nilpotent_thickening_of_flat_closed_fiber
    {S : Type*} [CommRing S] (J : Ideal S)
    {N : Type*} [AddCommGroup N] [Module S N] [Module.Flat S N]
    (hJ : IsNilpotent J)
    (hquot : Module.Projective (S ⧸ J) (N ⧸ (J • ⊤ : Submodule S N))) :
    Module.Projective S N := by
  -- Reuse the canonical nilpotent-thickening projectivity theorem from the earlier dependency.
  exact projective_of_projective_quotient_of_isNilpotent_of_flat
    (R := S) (I := J) (M := N) hJ hquot

/-- Helper for Lemma 10.97.9: in the quotient ring `R / I^(n + 1)`, the image of `I` is
nilpotent. -/
lemma stage_image_ideal_isNilpotent (n : ℕ) :
    IsNilpotent (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I) := by
  -- Raising the image ideal to the `(n + 1)`-st power kills it because `I^(n+1)` vanishes in the
  -- quotient by `I^(n+1)`.
  refine ⟨n + 1, ?_⟩
  calc
    (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I) ^ (n + 1) =
        Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ (n + 1)) := by
          rw [← Ideal.map_pow]
    _ = (0 : Ideal (R ⧸ I ^ (n + 1))) := by
          simpa [Ideal.zero_eq_bot] using Ideal.map_quotient_self (I ^ (n + 1))

/-- Helper for Lemma 10.97.9: quotienting `R / I^(n + 1)` by the image of `I` recovers `R / I`.
-/
noncomputable def stage_closed_fiber_ring_equiv (n : ℕ) :
    ((R ⧸ I ^ (n + 1)) ⧸ Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I) ≃+* R ⧸ I := by
  -- This is the third-isomorphism theorem for the inclusion `I^(n+1) ≤ I`.
  exact DoubleQuot.quotQuotEquivQuotOfLE (Ideal.pow_le_self (Nat.succ_ne_zero n))

/-- Helper for Lemma 10.97.9: after reducing modulo `I ^ (n + 1)`, the image of `IM` is exactly
the quotient-side submodule generated by the image ideal of `I`. -/
lemma stage_closed_fiber_smul_top_eq_map (n : ℕ) :
    let J : Ideal (R ⧸ I ^ (n + 1)) := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I
    (I • (⊤ : Submodule R M)).map (Submodule.mkQ (I ^ (n + 1) • ⊤ : Submodule R M)) =
      ((J •
          (⊤ : Submodule (R ⧸ I ^ (n + 1))
            (M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)))).restrictScalars R) := by
  let J : Ideal (R ⧸ I ^ (n + 1)) := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I
  -- Normalize the image denominator to the canonical quotient-side ideal action.
  calc
    (I • (⊤ : Submodule R M)).map (Submodule.mkQ (I ^ (n + 1) • ⊤ : Submodule R M)) =
        I • (⊤ : Submodule R (M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M))) := by
          simp [Submodule.map_smul'', Submodule.range_mkQ]
    _ =
        ((Ideal.map (algebraMap R (R ⧸ I ^ (n + 1))) I) •
          (⊤ : Submodule (R ⧸ I ^ (n + 1))
            (M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)))).restrictScalars R := by
          symm
          simpa using
            (Ideal.smul_restrictScalars
              (R := R) (S := R ⧸ I ^ (n + 1))
              (M := M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)) I
              (⊤ : Submodule (R ⧸ I ^ (n + 1))
                (M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M))))
    _ =
        ((J •
          (⊤ : Submodule (R ⧸ I ^ (n + 1))
            (M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)))).restrictScalars R) := by
          rw [Ideal.Quotient.algebraMap_eq]

/-- Helper for Lemma 10.97.9: quotienting the positive stage `M / I^(n + 1)M` by the image of
`IM` recovers the original closed fiber `M / IM`. -/
noncomputable def stage_closed_fiber_module_equiv (n : ℕ) :
    let In1M : Submodule R M := I ^ (n + 1) • (⊤ : Submodule R M)
    let IM : Submodule R M := I • (⊤ : Submodule R M)
    ((M ⧸ In1M) ⧸ IM.map (Submodule.mkQ In1M)) ≃ₗ[R] M ⧸ IM := by
  let In1M : Submodule R M := I ^ (n + 1) • (⊤ : Submodule R M)
  let IM : Submodule R M := I • (⊤ : Submodule R M)
  have hIn1M_le_IM : In1M ≤ IM := by
    -- The source proof uses the third-isomorphism theorem because `I^(n+1)M ⊆ IM`.
    dsimp [In1M, IM]
    simpa using
      (Submodule.smul_mono (Ideal.pow_le_self (Nat.succ_ne_zero n))
        (show (⊤ : Submodule R M) ≤ ⊤ from le_rfl))
  exact Submodule.quotientQuotientEquivQuotient In1M IM hIn1M_le_IM

/-- Helper for Lemma 10.97.9: the stage closed fiber comparison can be written using the canonical
quotient-side denominator `J • ⊤`. -/
noncomputable def stage_closed_fiber_module_equiv_canonical (n : ℕ) :
    let S : Type u := R ⧸ I ^ (n + 1)
    let In1M : Submodule R M := I ^ (n + 1) • (⊤ : Submodule R M)
    let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I
    ((M ⧸ In1M) ⧸
        ((J • (⊤ : Submodule S (M ⧸ In1M))).restrictScalars R)) ≃ₗ[R]
      M ⧸ (I • (⊤ : Submodule R M)) := by
  let S : Type u := R ⧸ I ^ (n + 1)
  let In1M : Submodule R M := I ^ (n + 1) • (⊤ : Submodule R M)
  let IM : Submodule R M := I • (⊤ : Submodule R M)
  let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I
  let eDenom :
      ((M ⧸ In1M) ⧸ IM.map (Submodule.mkQ In1M)) ≃ₗ[R]
        ((M ⧸ In1M) ⧸ ((J • (⊤ : Submodule S (M ⧸ In1M))).restrictScalars R)) :=
    -- Replace the ad hoc denominator `IM.map` by the quotient-side ideal action from the source.
    Submodule.quotEquivOfEq
      (IM.map (Submodule.mkQ In1M))
      ((J • (⊤ : Submodule S (M ⧸ In1M))).restrictScalars R)
      (by simpa [S, In1M, IM, J] using stage_closed_fiber_smul_top_eq_map (I := I) (M := M) n)
  -- The canonical denominator now matches the exact source-stage closed fiber.
  exact eDenom.symm.trans (stage_closed_fiber_module_equiv (I := I) (M := M) n)

/-- Helper for Lemma 10.97.9: the canonical stage closed fiber comparison is linear over the
reduced owner ring `((R ⧸ I^(n + 1)) ⧸ J)`, not just over `R`. -/
noncomputable def stage_closed_fiber_owner_linear_equiv (n : ℕ) :
    let S : Type u := R ⧸ I ^ (n + 1)
    let In1M : Submodule R M := I ^ (n + 1) • (⊤ : Submodule R M)
    let N : Type w := M ⧸ In1M
    let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I
    let T : Type u := S ⧸ J
    letI : Algebra T (R ⧸ I) := (stage_closed_fiber_ring_equiv (I := I) n).toRingHom.toAlgebra
    letI : Module T (M ⧸ (I • (⊤ : Submodule R M))) :=
      Module.compHom (M ⧸ (I • (⊤ : Submodule R M))) (algebraMap T (R ⧸ I))
    (N ⧸ (J • (⊤ : Submodule S N))) ≃ₗ[T] M ⧸ (I • (⊤ : Submodule R M)) := by
  let S : Type u := R ⧸ I ^ (n + 1)
  let In1M : Submodule R M := I ^ (n + 1) • (⊤ : Submodule R M)
  let N : Type w := M ⧸ In1M
  let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I
  let T : Type u := S ⧸ J
  letI : Algebra R S := Ideal.Quotient.algebra _
  letI : Algebra S T := Ideal.Quotient.algebra _
  letI : Algebra R T := by infer_instance
  letI : Algebra T (R ⧸ I) :=
    (stage_closed_fiber_ring_equiv (I := I) n).toRingHom.toAlgebra
  letI : Module T (M ⧸ (I • (⊤ : Submodule R M))) :=
    Module.compHom (M ⧸ (I • (⊤ : Submodule R M))) (algebraMap T (R ⧸ I))
  letI : IsScalarTower R T (M ⧸ (I • (⊤ : Submodule R M))) :=
    IsScalarTower.of_compHom R T (M ⧸ (I • (⊤ : Submodule R M)))
  let eRestrict :
      (N ⧸ ((J • (⊤ : Submodule S N)).restrictScalars R)) ≃ₗ[R] N ⧸ (J • (⊤ : Submodule S N)) :=
    -- First identify the `S`-quotient with the same quotient viewed over `R`.
    Submodule.Quotient.restrictScalarsEquiv R (J • (⊤ : Submodule S N))
  let eR :
      (N ⧸ (J • (⊤ : Submodule S N))) ≃ₗ[R] M ⧸ (I • (⊤ : Submodule R M)) :=
    -- Then reuse the source-faithful third-isomorphism comparison over the ground ring.
    eRestrict.symm.trans (stage_closed_fiber_module_equiv_canonical (I := I) (M := M) n)
  have hsurj : Function.Surjective (algebraMap R T) := by
    -- The reduced owner is still an iterated quotient of `R`, so scalar extension from `R` is
    -- surjective and upgrades the comparison to `T`-linearity.
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨x, rfl⟩
  exact eR.extendScalarsOfSurjective hsurj

/-- Helper for Lemma 10.97.9: the closed fiber projectivity of `M / IM` transports to the exact
owner ring of the stage closed fiber. -/
lemma projective_stage_closed_fiber_over_owner (n : ℕ)
    (hquot : Module.Projective (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) :
    let S : Type u := R ⧸ I ^ (n + 1)
    let In1M : Submodule R M := I ^ (n + 1) • (⊤ : Submodule R M)
    let N : Type w := M ⧸ In1M
    let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I
    let T : Type u := S ⧸ J
    Module.Projective T (N ⧸ (J • (⊤ : Submodule S N))) := by
  let S : Type u := R ⧸ I ^ (n + 1)
  let In1M : Submodule R M := I ^ (n + 1) • (⊤ : Submodule R M)
  let N : Type w := M ⧸ In1M
  let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I
  let T : Type u := S ⧸ J
  let B : Type u := R ⧸ I
  let Q : Type w := M ⧸ (I • (⊤ : Submodule R M))
  let eRing : T ≃+* B := stage_closed_fiber_ring_equiv (I := I) n
  letI : CommRing S := inferInstance
  letI : CommRing T := inferInstance
  letI : CommRing B := inferInstance
  letI : Algebra T B := eRing.toRingHom.toAlgebra
  letI : Module T Q := Module.compHom Q (algebraMap T B)
  letI : Module.Projective B Q := hquot
  letI : RingHomInvPair eRing.symm.toRingHom eRing.toRingHom := RingHomInvPair.of_ringEquiv eRing.symm
  letI : RingHomInvPair eRing.toRingHom eRing.symm.toRingHom := RingHomInvPair.of_ringEquiv eRing
  let eOwner : Q ≃ₛₗ[eRing.symm.toRingHom] Q :=
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r x
        -- The ring equivalence identifies the transported owner action with the original one.
        change r • x = (eRing (eRing.symm r)) • x
        simpa using congrArg (fun s : B ↦ s • x) (eRing.apply_symm_apply r).symm }
  have howner : Module.Projective T Q := by
    -- First transport projectivity of `M / IM` along the quotient-ring equivalence.
    exact Module.Projective.of_equiv eOwner
  letI : Module.Projective T Q := howner
  -- Then rewrite the stage closed fiber itself by the owner-linear equivalence.
  exact Module.Projective.of_equiv'
    ((stage_closed_fiber_owner_linear_equiv (I := I) (M := M) n).symm)

/-- Helper for Lemma 10.97.9: the source pullback object at the successor stage, realized as the
preimage of the previous-stage section's range under the canonical transition map. -/
def successor_stage_pullback (n : ℕ)
    (σ_n : M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M) →ₗ[R ⧸ I ^ (n + 1)]
      P ⧸ (I ^ (n + 1) • ⊤ : Submodule R P)) :
    Submodule R (P ⧸ (I ^ (n + 2) • ⊤ : Submodule R P)) :=
  Submodule.comap
    (AdicCompletion.transitionMap I P (Nat.le_succ (n + 1)))
    (Submodule.restrictScalars
      (R := R ⧸ I ^ (n + 1)) (S := R)
      (M := P ⧸ (I ^ (n + 1) • ⊤ : Submodule R P))
      (LinearMap.range σ_n))

/-- Helper for Lemma 10.97.9: each one-step quotient transition map is surjective. This is the
source proof's lift from stage `n + 1` back to stage `n + 2`. -/
lemma stage_transition_surjective
    {X : Type*} [AddCommGroup X] [Module R X] (n : ℕ) :
    Function.Surjective (AdicCompletion.transitionMap I X (Nat.le_succ (n + 1))) := by
  -- The transition map is exactly the quotient map along the inclusion
  -- `I^(n+2)X ⊆ I^(n+1)X`, so every class at stage `n + 1` has a representative one stage up.
  simpa [AdicCompletion.transitionMap, Submodule.factorPow] using
    (Submodule.factor_surjective
      (Submodule.pow_smul_top_le (I := I) (M := X) (h := Nat.le_succ (n + 1))))

/-- Helper for Lemma 10.97.9: the source defect
`τ_P(p₀) - σₙ(τ_M(x))` lands in the kernel of the reduced map at stage `n + 1`. -/
lemma pullback_defect_mem_ker
    (g : P →ₗ[R] M) (n : ℕ)
    (σ_n : M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M) →ₗ[R ⧸ I ^ (n + 1)]
      P ⧸ (I ^ (n + 1) • ⊤ : Submodule R P))
    (hσ_n : (g.reduceModIdeal (I ^ (n + 1))).comp σ_n = LinearMap.id)
    {p0 : P ⧸ (I ^ (n + 2) • ⊤ : Submodule R P)}
    {x : M ⧸ (I ^ (n + 2) • ⊤ : Submodule R M)}
    (hx : (g.reduceModIdeal (I ^ (n + 2))) p0 = x) :
    let δ :=
      AdicCompletion.transitionMap I P (Nat.le_succ (n + 1)) p0 -
        σ_n (AdicCompletion.transitionMap I M (Nat.le_succ (n + 1)) x)
    (((g.reduceModIdeal (I ^ (n + 1))).restrictScalars R) δ = 0) := by
  let τP : P ⧸ (I ^ (n + 2) • ⊤ : Submodule R P) →ₗ[R]
      P ⧸ (I ^ (n + 1) • ⊤ : Submodule R P) :=
    AdicCompletion.transitionMap I P (Nat.le_succ (n + 1))
  let τM : M ⧸ (I ^ (n + 2) • ⊤ : Submodule R M) →ₗ[R]
      M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M) :=
    AdicCompletion.transitionMap I M (Nat.le_succ (n + 1))
  have htrans :
      ((g.reduceModIdeal (I ^ (n + 1))).restrictScalars R) (τP p0) =
        τM ((g.reduceModIdeal (I ^ (n + 2))) p0) := by
    -- Commute reduction with the one-step transition map before evaluating at `p0`.
    simpa [τP, τM, LinearMap.comp_apply] using
      (LinearMap.congr_fun
        (AdicCompletion.transitionMap_comp_reduceModIdeal
          (I := I) (f := g) (hmn := Nat.le_succ (n + 1))).symm p0)
  have hsection :
      ((g.reduceModIdeal (I ^ (n + 1))).restrictScalars R) (σ_n (τM x)) = τM x := by
    -- The previous-stage section retracts the reduced map by hypothesis.
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hσ_n (τM x)
  -- After the transition-reduction rewrite, the defect becomes `τ_M(x) - τ_M(x)`.
  dsimp
  calc
    ((g.reduceModIdeal (I ^ (n + 1))).restrictScalars R) (τP p0 - σ_n (τM x))
        = ((g.reduceModIdeal (I ^ (n + 1))).restrictScalars R) (τP p0) -
            ((g.reduceModIdeal (I ^ (n + 1))).restrictScalars R) (σ_n (τM x)) := by
              simp
    _ = τM ((g.reduceModIdeal (I ^ (n + 2))) p0) - τM x := by
          rw [htrans, hsection]
    _ = τM x - τM x := by rw [hx]
    _ = 0 := sub_self _

/-- Helper for Lemma 10.97.9: if a reduced stage class in `P / I^(n+1)P` maps to `0` in
`M / I^(n+1)M`, then exactness of `ker g → P → M` produces a stagewise kernel preimage. -/
lemma exists_stage_ker_lift_of_zero_reduced_image
    (g : P →ₗ[R] M) (hg : Function.Surjective g) (n : ℕ)
    {y : P ⧸ (I ^ (n + 1) • ⊤ : Submodule R P)}
    (hy : ((g.reduceModIdeal (I ^ (n + 1))).restrictScalars R) y = 0) :
    ∃ k : LinearMap.ker g ⧸ (I ^ (n + 1) • ⊤ : Submodule R (LinearMap.ker g)),
      ((((LinearMap.ker g).subtype).reduceModIdeal (I ^ (n + 1))).restrictScalars R) k = y := by
  have hExact : Function.Exact (LinearMap.ker g).subtype g := by
    -- The kernel inclusion followed by `g` is the canonical exact pair.
    exact LinearMap.exact_subtype_ker_map g
  have hstageExact :
      Function.Exact
        ((LinearMap.ker g).subtype.quotientMapByIdeal (I ^ (n + 1)))
        (g.quotientMapByIdeal (I ^ (n + 1))) := by
    -- Reduce the exact sequence modulo `I^(n+1)` using the earlier exactness bridge.
    exact quotientMapByIdeal_exact_of_exact_surjective_univ
      (R := R) (J := I ^ (n + 1)) (LinearMap.ker g).subtype g hExact hg
  have hstageExact' :
      Function.Exact
        ((((LinearMap.ker g).subtype).reduceModIdeal (I ^ (n + 1))).restrictScalars R)
        (((g.reduceModIdeal (I ^ (n + 1))).restrictScalars R)) := by
    -- Rewrite the quotient-stage exactness into the `reduceModIdeal` shape used downstream.
    simpa
      [quotientMapByIdeal_eq_reduceModIdeal_restrictScalars_univ
        (R := R) (J := I ^ (n + 1)) ((LinearMap.ker g).subtype),
       quotientMapByIdeal_eq_reduceModIdeal_restrictScalars_univ
        (R := R) (J := I ^ (n + 1)) g] using hstageExact
  -- Evaluate exactness at `y` to extract the required witness in the reduced kernel quotient.
  simpa [Set.mem_range] using (hstageExact' y).mp hy

/-- Helper for Lemma 10.97.9: the one-step quotient-ring transition `R / I^(n+2) → R / I^(n+1)`
is surjective. -/
lemma stage_factorPow_surjective (n : ℕ) :
    Function.Surjective (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))) := by
  -- Every class at stage `n + 1` is represented by the same element one stage higher.
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk (I ^ (n + 2)) x, rfl⟩

/-- Helper for Lemma 10.97.9: the predecessor quotient stage is naturally an
`R / I^(n+2)`-module via the quotient-ring transition map. -/
@[reducible]
noncomputable def stage_transition_ringModule (n : ℕ) :
    Module (R ⧸ I ^ (n + 2)) (R ⧸ I ^ (n + 1)) :=
  Module.compHom _ (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1)))

/-- Helper for Lemma 10.97.9: the predecessor quotient stage is naturally an
`R / I^(n+2)`-module via the quotient-ring transition map. -/
@[reducible]
noncomputable def stage_transition_targetModule
    {X : Type*} [AddCommGroup X] [Module R X] (n : ℕ) :
    Module (R ⧸ I ^ (n + 2)) (X ⧸ (I ^ (n + 1) • ⊤ : Submodule R X)) :=
  Module.compHom _ (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1)))

/-- Helper for Lemma 10.97.9: the induced owner action on the predecessor quotient stage is
compatible with the predecessor-ring action. -/
lemma stage_transition_target_owner_smul_assoc
    {X : Type*} [AddCommGroup X] [Module R X] (n : ℕ)
    (r : R ⧸ I ^ (n + 2)) (s : R ⧸ I ^ (n + 1))
    (x : X ⧸ (I ^ (n + 1) • ⊤ : Submodule R X)) :
    letI := stage_transition_ringModule (I := I) n
    letI := stage_transition_targetModule (I := I) (X := X) n
    (r • s) • x = r • (s • x) := by
  -- Both sides are just the usual predecessor-ring scalar action by `factorPow r * s`.
  letI := stage_transition_ringModule (I := I) n
  letI := stage_transition_targetModule (I := I) (X := X) n
  change (((Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))) r) * s) • x =
      ((Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))) r) • (s • x)
  rw [mul_smul]

/-- Helper for Lemma 10.97.9: the predecessor quotient stage forms a scalar tower
`R / I^(n+2) → R / I^(n+1) → X / I^(n+1)X`. -/
@[reducible]
noncomputable def stage_transition_target_owner_isScalarTower
    {X : Type*} [AddCommGroup X] [Module R X] (n : ℕ) :=
  letI := stage_transition_ringModule (I := I) n
  letI := stage_transition_targetModule (I := I) (X := X) n
  show
      IsScalarTower (R ⧸ I ^ (n + 2)) (R ⧸ I ^ (n + 1))
        (X ⧸ (I ^ (n + 1) • ⊤ : Submodule R X)) from
    { smul_assoc := stage_transition_target_owner_smul_assoc (I := I) (X := X) n }

/-- Helper for Lemma 10.97.9: the induced owner action on the predecessor quotient stage is also
compatible with the original `R`-module structure. -/
lemma stage_transition_target_base_smul_assoc
    {X : Type*} [AddCommGroup X] [Module R X] (n : ℕ)
    (r : R) (s : R ⧸ I ^ (n + 2))
    (x : X ⧸ (I ^ (n + 1) • ⊤ : Submodule R X)) :
    letI := stage_transition_targetModule (I := I) (X := X) n
    r • (s • x) = (r • s) • x := by
  -- Expand both actions on representatives and use the usual `mul_smul` identity downstairs.
  letI := stage_transition_targetModule (I := I) (X := X) n
  induction s, x using Quotient.inductionOn₂' with
  | _ s x =>
      change (Ideal.Quotient.mk (I ^ (n + 1)) r) •
          ((Ideal.Quotient.mk (I ^ (n + 1)) s) •
            Submodule.Quotient.mk (p := (I ^ (n + 1) • ⊤ : Submodule R X)) x) =
        ((Ideal.Quotient.mk (I ^ (n + 1)) r * Ideal.Quotient.mk (I ^ (n + 1)) s)) •
          (Submodule.Quotient.mk (p := (I ^ (n + 1) • ⊤ : Submodule R X)) x)
      rw [mul_smul]

/-- Helper for Lemma 10.97.9: the predecessor quotient stage forms a scalar tower
`R → R / I^(n+2) → X / I^(n+1)X`. -/
@[reducible]
noncomputable def stage_transition_target_base_isScalarTower
    {X : Type*} [AddCommGroup X] [Module R X] (n : ℕ) :=
  letI := stage_transition_targetModule (I := I) (X := X) n
  show IsScalarTower R (R ⧸ I ^ (n + 2))
      (X ⧸ (I ^ (n + 1) • ⊤ : Submodule R X)) from
    { smul_assoc := fun r s x ↦
        (stage_transition_target_base_smul_assoc (I := I) (X := X) n r s x).symm }

/-- Helper for Lemma 10.97.9: the one-step transition map of quotient modules is linear over the
successor owner ring once the predecessor stage is viewed through the factor map. -/
noncomputable def stage_transition_owner_linear
    {X : Type*} [AddCommGroup X] [Module R X] (n : ℕ) :=
  letI := stage_transition_targetModule (I := I) (X := X) n
  letI := stage_transition_target_base_isScalarTower (X := X) (I := I) n
  -- Route correction: package the owner-linear stage transition first so later pullbacks only
  -- use an explicit map instead of relying on hidden scalar-tower inference.
  (AdicCompletion.transitionMap I X (Nat.le_succ (n + 1))).extendScalarsOfSurjective
    (R := R) (S := R ⧸ I ^ (n + 2)) Ideal.Quotient.mk_surjective

/-- Helper for Lemma 10.97.9: the explicit owner-linear transition has the same underlying
function as the usual quotient transition map. -/
lemma stage_transition_owner_linear_apply
    {X : Type*} [AddCommGroup X] [Module R X] (n : ℕ)
    (x : X ⧸ (I ^ (n + 2) • ⊤ : Submodule R X)) :
    stage_transition_owner_linear (I := I) (X := X) n x =
      AdicCompletion.transitionMap I X (Nat.le_succ (n + 1)) x := by
  -- The owner-linear transition was defined by scalar extension of the original map.
  rfl

/-- Helper for Lemma 10.97.9: the owner-ring pullback at the successor stage is the same source
pullback object, but viewed as a submodule over `R ⧸ I^(n+2)`. -/
noncomputable def successor_stage_pullback_owner (n : ℕ)
    (σ_n : M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M) →ₗ[R ⧸ I ^ (n + 1)]
      P ⧸ (I ^ (n + 1) • ⊤ : Submodule R P)) :
    Submodule (R ⧸ I ^ (n + 2)) (P ⧸ (I ^ (n + 2) • ⊤ : Submodule R P)) :=
  letI := stage_transition_ringModule (I := I) n
  letI := stage_transition_targetModule (I := I) (X := P) n
  letI := stage_transition_target_owner_isScalarTower (I := I) (X := P) n
  Submodule.comap
    (stage_transition_owner_linear (I := I) (X := P) n)
    ((LinearMap.range σ_n).restrictScalars (R ⧸ I ^ (n + 2)))

/-- Helper for Lemma 10.97.9: carrier membership in the owner-valued successor pullback is the
same as the original predecessor-range condition over `R`. -/
lemma successor_stage_pullback_owner_mem_iff (n : ℕ)
    (σ_n : M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M) →ₗ[R ⧸ I ^ (n + 1)]
      P ⧸ (I ^ (n + 1) • ⊤ : Submodule R P))
    (x : P ⧸ (I ^ (n + 2) • ⊤ : Submodule R P)) :
    x ∈ successor_stage_pullback_owner (I := I) (P := P) (M := M) n σ_n ↔
      AdicCompletion.transitionMap I P (Nat.le_succ (n + 1)) x ∈
        (LinearMap.range σ_n).restrictScalars R := by
  letI := stage_transition_ringModule (I := I) n
  letI := stage_transition_targetModule (I := I) (X := P) n
  letI := stage_transition_target_owner_isScalarTower (I := I) (X := P) n
  -- Unfold the owner pullback and rewrite the owner-linear transition back to the original map.
  rw [successor_stage_pullback_owner, Submodule.mem_comap]
  -- Restricting scalars only changes the owner ring, not the underlying carrier condition.
  simpa [stage_transition_owner_linear_apply]

/-- Helper for Lemma 10.97.9: after restricting scalars back to `R`, the owner-ring successor
pullback is exactly the original `R`-linear pullback. -/
lemma successor_stage_pullback_owner_restrictScalars_eq (n : ℕ)
    (σ_n : M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M) →ₗ[R ⧸ I ^ (n + 1)]
      P ⧸ (I ^ (n + 1) • ⊤ : Submodule R P)) :
    (successor_stage_pullback_owner (I := I) (P := P) (M := M) n σ_n).restrictScalars R =
      successor_stage_pullback (I := I) (P := P) (M := M) n σ_n := by
  -- Restricting scalars does not change the carrier, so the two pullbacks agree by the same
  -- pointwise membership test.
  ext x
  change x ∈ successor_stage_pullback_owner (I := I) (P := P) (M := M) n σ_n ↔
    x ∈ successor_stage_pullback (I := I) (P := P) (M := M) n σ_n
  simpa [successor_stage_pullback, Submodule.mem_comap] using
    successor_stage_pullback_owner_mem_iff (I := I) (P := P) (M := M) n σ_n x

/-- Helper for Lemma 10.97.9: reducing the kernel inclusion and then the quotient map `g`
annihilates every stage. -/
lemma reduceModIdeal_ker_subtype_comp_eq_zero
    (g : P →ₗ[R] M) (n : ℕ) :
    (((g.reduceModIdeal (I ^ (n + 1))).restrictScalars R).comp
      ((((LinearMap.ker g).subtype).reduceModIdeal (I ^ (n + 1))).restrictScalars R)) = 0 := by
  -- On quotient representatives this is just the identity `g ∘ ker.subtype = 0`.
  apply DFunLike.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (I ^ (n + 1) • (⊤ : Submodule R (LinearMap.ker g))) x
  simp

/-- Helper for Lemma 10.97.9: the owner-linear map from the successor pullback to the new stage is
surjective. -/
lemma pullback_stage_surjective_of_compatible_section_owner
    (g : P →ₗ[R] M) (hg : Function.Surjective g) (n : ℕ)
    (σ_n : M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M) →ₗ[R ⧸ I ^ (n + 1)]
      P ⧸ (I ^ (n + 1) • ⊤ : Submodule R P))
    (hσ_n : (g.reduceModIdeal (I ^ (n + 1))).comp σ_n = LinearMap.id) :
    Function.Surjective
      ((g.reduceModIdeal (I ^ (n + 2))).domRestrict
        (successor_stage_pullback_owner (I := I) (P := P) (M := M) n σ_n)) := by
  let τP : P ⧸ (I ^ (n + 2) • ⊤ : Submodule R P) →ₗ[R]
      P ⧸ (I ^ (n + 1) • ⊤ : Submodule R P) :=
    AdicCompletion.transitionMap I P (Nat.le_succ (n + 1))
  let τM : M ⧸ (I ^ (n + 2) • ⊤ : Submodule R M) →ₗ[R]
      M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M) :=
    AdicCompletion.transitionMap I M (Nat.le_succ (n + 1))
  let κ₁ : LinearMap.ker g ⧸ (I ^ (n + 1) • ⊤ : Submodule R (LinearMap.ker g)) →ₗ[R]
      P ⧸ (I ^ (n + 1) • ⊤ : Submodule R P) :=
    ((((LinearMap.ker g).subtype).reduceModIdeal (I ^ (n + 1))).restrictScalars R)
  let κ₂ : LinearMap.ker g ⧸ (I ^ (n + 2) • ⊤ : Submodule R (LinearMap.ker g)) →ₗ[R]
      P ⧸ (I ^ (n + 2) • ⊤ : Submodule R P) :=
    ((((LinearMap.ker g).subtype).reduceModIdeal (I ^ (n + 2))).restrictScalars R)
  intro x
  -- Start from an arbitrary lift of `x` at the new stage.
  obtain ⟨p0, hp0⟩ := reduceModIdeal_surjective (R := R) (g := g) hg (I ^ (n + 2)) x
  let δ := τP p0 - σ_n (τM x)
  have hδ_zero : ((g.reduceModIdeal (I ^ (n + 1))).restrictScalars R) δ = 0 := by
    -- The predecessor-stage defect lies in the reduced kernel by compatibility of `σ_n`.
    exact pullback_defect_mem_ker (I := I) (g := g) n σ_n hσ_n (p0 := p0) (x := x) hp0
  obtain ⟨k, hk⟩ := exists_stage_ker_lift_of_zero_reduced_image
    (I := I) (g := g) hg n (y := δ) hδ_zero
  obtain ⟨k', hk'⟩ := stage_transition_surjective (I := I) (X := LinearMap.ker g) n k
  let c := κ₂ k'
  have htransition_correction : τP c = δ := by
    -- The lifted kernel correction reproduces the predecessor-stage defect after one transition.
    have hcomm :=
      LinearMap.congr_fun
        (AdicCompletion.transitionMap_comp_reduceModIdeal
          (I := I) (f := (LinearMap.ker g).subtype) (hmn := Nat.le_succ (n + 1))) k'
    calc
      τP c =
          κ₁ (AdicCompletion.transitionMap I (LinearMap.ker g) (Nat.le_succ (n + 1)) k') := by
            simpa [τP, κ₁, κ₂, c, LinearMap.comp_apply] using hcomm
      _ = κ₁ k := by rw [hk']
      _ = δ := hk
  have hcorrection_maps_to_zero : (g.reduceModIdeal (I ^ (n + 2))) c = 0 := by
    -- The correction comes from the reduced kernel inclusion, so it vanishes under `g`.
    have hz :=
      LinearMap.congr_fun
        (reduceModIdeal_ker_subtype_comp_eq_zero (I := I) (g := g) (n := n + 1)) k'
    simpa [κ₂, c, LinearMap.comp_apply] using hz
  have hpullback : p0 - c ∈ successor_stage_pullback_owner (I := I) (P := P) (M := M) n σ_n := by
    -- Subtracting the lifted kernel correction lands exactly in the predecessor range condition.
    rw [successor_stage_pullback_owner_mem_iff]
    refine ⟨τM x, ?_⟩
    symm
    calc
      τP (p0 - c) = τP p0 - τP c := by simp [τP]
      _ = τP p0 - δ := by rw [htransition_correction]
      _ = τP p0 - (τP p0 - σ_n (τM x)) := by rfl
      _ = σ_n (τM x) := by abel
  refine ⟨⟨p0 - c, hpullback⟩, ?_⟩
  -- The correction does not change the image under `g`, so the corrected lift still maps to `x`.
  calc
    (g.reduceModIdeal (I ^ (n + 2))) (p0 - c) =
        (g.reduceModIdeal (I ^ (n + 2))) p0 - (g.reduceModIdeal (I ^ (n + 2))) c := by
          simp
    _ = x - 0 := by rw [hp0, hcorrection_maps_to_zero]
    _ = x := sub_zero x

/-- Helper for Lemma 10.97.9: a point in the range of a section is determined by its image under
the retraction. -/
lemma eq_section_of_mem_range_of_comp_eq_id
    {S : Type*} [CommRing S]
    {A : Type*} [AddCommGroup A] [Module S A]
    {B : Type*} [AddCommGroup B] [Module S B]
    (σ : A →ₗ[S] B) (π : B →ₗ[S] A)
    (hσ : π.comp σ = LinearMap.id)
    {x : A} {y : B}
    (hy : y ∈ LinearMap.range σ) (hπy : π y = x) :
    y = σ x := by
  rcases hy with ⟨x', rfl⟩
  -- Evaluate the retraction identity on the witness from the range description.
  have hx' : x' = x := by
    calc
      x' = π (σ x') := by
        simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hσ x').symm
      _ = x := hπy
  -- Rewriting by the identified source point closes the range element equality.
  simpa [hx']

/-- Helper for Lemma 10.97.9: every positive quotient stage `M / I^(n + 1)M` is projective over
`R / I^(n + 1)` once the closed fiber `M / IM` is projective. -/
lemma projective_reduceModIdeal_pow_of_projective_closed_fiber
    (n : ℕ) [Module.Flat R M]
    (hquot : Module.Projective (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) :
    Module.Projective (R ⧸ I ^ (n + 1)) (M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)) := by
  let S : Type u := R ⧸ I ^ (n + 1)
  let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) I
  have hJ : IsNilpotent J := by
    simpa [S, J] using stage_image_ideal_isNilpotent (I := I) n
  have hflat : Module.Flat S (M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)) := by
    simpa [S] using flat_reduceModIdeal_pow_of_flat (I := I) (M := M) n
  letI : Module.Flat S (M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)) := hflat
  -- Route correction: package the closed-fiber comparison over the reduced owner ring once, then
  -- feed that owner-stable projectivity into the nilpotent-thickening theorem from the source.
  have hclosed :
      Module.Projective (S ⧸ J)
        ((M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)) ⧸
          (J • ⊤ : Submodule S (M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)))) := by
    simpa [S, J] using
      projective_stage_closed_fiber_over_owner (I := I) (M := M) n hquot
  exact projective_of_nilpotent_thickening_of_flat_closed_fiber (J := J) hJ hclosed

/-- Helper for Lemma 10.97.9: a compatible predecessor-stage section extends one step further. -/
lemma exists_compatible_stage_section_succ
    (g : P →ₗ[R] M) [Module.Flat R M] (n : ℕ)
    (hquot : Module.Projective (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (σ_n : M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M) →ₗ[R ⧸ I ^ (n + 1)]
      P ⧸ (I ^ (n + 1) • ⊤ : Submodule R P))
    (hσ_n : (g.reduceModIdeal (I ^ (n + 1))).comp σ_n = LinearMap.id)
    (hg : Function.Surjective g) :
    ∃ σ_succ : M ⧸ (I ^ (n + 2) • ⊤ : Submodule R M) →ₗ[R ⧸ I ^ (n + 2)]
        P ⧸ (I ^ (n + 2) • ⊤ : Submodule R P),
      (g.reduceModIdeal (I ^ (n + 2))).comp σ_succ = LinearMap.id ∧
      (((AdicCompletion.transitionMap I P (Nat.le_succ (n + 1))).restrictScalars R).comp
          (σ_succ.restrictScalars R) =
        (σ_n.restrictScalars R).comp
          ((AdicCompletion.transitionMap I M (Nat.le_succ (n + 1))).restrictScalars R)) := by
  have hproj :
      Module.Projective (R ⧸ I ^ (n + 2))
        (M ⧸ (I ^ (n + 2) • ⊤ : Submodule R M)) := by
    -- Lemma `10.77.7` upgrades projectivity of the closed fiber to every positive stage.
    simpa using
      projective_reduceModIdeal_pow_of_projective_closed_fiber (I := I) (M := M) (n := n + 1)
        hquot
  letI : Module.Projective (R ⧸ I ^ (n + 2))
      (M ⧸ (I ^ (n + 2) • ⊤ : Submodule R M)) := hproj
  obtain ⟨lift, hlift⟩ := Module.projective_lifting_property
    ((g.reduceModIdeal (I ^ (n + 2))).domRestrict
      (successor_stage_pullback_owner (I := I) (P := P) (M := M) n σ_n))
    (LinearMap.id :
      M ⧸ (I ^ (n + 2) • ⊤ : Submodule R M) →ₗ[R ⧸ I ^ (n + 2)]
        M ⧸ (I ^ (n + 2) • ⊤ : Submodule R M))
    (pullback_stage_surjective_of_compatible_section_owner
      (I := I) (g := g) hg n σ_n hσ_n)
  let σ_succ :
      M ⧸ (I ^ (n + 2) • ⊤ : Submodule R M) →ₗ[R ⧸ I ^ (n + 2)]
        P ⧸ (I ^ (n + 2) • ⊤ : Submodule R P) :=
    (Submodule.subtype
      (successor_stage_pullback_owner (I := I) (P := P) (M := M) n σ_n)).comp lift
  have hσ_succ : (g.reduceModIdeal (I ^ (n + 2))).comp σ_succ = LinearMap.id := by
    -- The owner-stage lift is a section by construction.
    apply LinearMap.ext
    intro x
    simpa [σ_succ, LinearMap.comp_apply] using LinearMap.congr_fun hlift x
  refine ⟨σ_succ, hσ_succ, ?_⟩
  apply LinearMap.ext
  intro x
  let τP : P ⧸ (I ^ (n + 2) • ⊤ : Submodule R P) →ₗ[R]
      P ⧸ (I ^ (n + 1) • ⊤ : Submodule R P) :=
    AdicCompletion.transitionMap I P (Nat.le_succ (n + 1))
  let τM : M ⧸ (I ^ (n + 2) • ⊤ : Submodule R M) →ₗ[R]
      M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M) :=
    AdicCompletion.transitionMap I M (Nat.le_succ (n + 1))
  have hx_pullback :
      σ_succ x ∈ successor_stage_pullback_owner (I := I) (P := P) (M := M) n σ_n := by
    -- The chosen lift lands in the owner pullback by definition.
    change ((Submodule.subtype
      (successor_stage_pullback_owner (I := I) (P := P) (M := M) n σ_n)).comp lift) x ∈
        successor_stage_pullback_owner (I := I) (P := P) (M := M) n σ_n
    simpa [σ_succ] using (lift x).property
  have hx_range :
      τP (σ_succ x) ∈ (LinearMap.range σ_n).restrictScalars R := by
    -- Pullback membership is exactly the predecessor-range condition from the source proof.
    exact (successor_stage_pullback_owner_mem_iff
      (I := I) (P := P) (M := M) n σ_n (σ_succ x)).1 hx_pullback
  have hx_section : (g.reduceModIdeal (I ^ (n + 2))) (σ_succ x) = x := by
    -- Evaluate the new section identity at `x`.
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hσ_succ x
  have hx_transition :
      ((g.reduceModIdeal (I ^ (n + 1))).restrictScalars R) (τP (σ_succ x)) = τM x := by
    -- Reduce after transitioning, then rewrite the successor-stage section identity.
    have hcomm :
        ((g.reduceModIdeal (I ^ (n + 1))).restrictScalars R) (τP (σ_succ x)) =
          τM ((g.reduceModIdeal (I ^ (n + 2))) (σ_succ x)) := by
      simpa [τP, τM, LinearMap.comp_apply] using
        (LinearMap.congr_fun
          (AdicCompletion.transitionMap_comp_reduceModIdeal
            (I := I) (f := g) (hmn := Nat.le_succ (n + 1))).symm (σ_succ x))
    rw [hcomm, hx_section]
  have hx_compat :
      τP (σ_succ x) = σ_n (τM x) := by
    -- The point in the predecessor range is uniquely determined by its image under the retraction.
    have hx_range' : τP (σ_succ x) ∈ LinearMap.range (σ_n.restrictScalars R) := by
      simpa using hx_range
    have hσ_nR :
        ((g.reduceModIdeal (I ^ (n + 1))).restrictScalars R).comp (σ_n.restrictScalars R) =
          LinearMap.id := by
      apply LinearMap.ext
      intro y
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hσ_n y
    exact eq_section_of_mem_range_of_comp_eq_id
      (σ := σ_n.restrictScalars R)
      (π := (g.reduceModIdeal (I ^ (n + 1))).restrictScalars R)
      (hσ := hσ_nR)
      hx_range' hx_transition
  -- Pointwise predecessor compatibility is the advertised map equality after restricting scalars.
  simpa [σ_succ, τP, τM, LinearMap.comp_apply] using hx_compat

/-- Helper for Lemma 10.97.9: the splitting map used at the positive quotient stage `n + 1`. -/
abbrev positive_stage_section (n : ℕ) :=
  M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M) →ₗ[R ⧸ I ^ (n + 1)]
    P ⧸ (I ^ (n + 1) • ⊤ : Submodule R P)

/-- Helper for Lemma 10.97.9: a positive-stage section retracts the reduced map. -/
def positive_stage_section_is_retraction
    (g : P →ₗ[R] M) (n : ℕ) (σ : positive_stage_section (I := I) (P := P) (M := M) n) : Prop :=
  (g.reduceModIdeal (I ^ (n + 1))).comp σ = LinearMap.id

/-- Helper for Lemma 10.97.9: adjacent positive-stage sections agree after reducing from stage
`n + 2` to stage `n + 1`. -/
def positive_stage_section_compatible (n : ℕ)
    (σ_n : positive_stage_section (I := I) (P := P) (M := M) n)
    (σ_succ : positive_stage_section (I := I) (P := P) (M := M) (n + 1)) : Prop :=
  (((AdicCompletion.transitionMap I P (Nat.le_succ (n + 1))).restrictScalars R).comp
      (σ_succ.restrictScalars R) =
    (σ_n.restrictScalars R).comp
      ((AdicCompletion.transitionMap I M (Nat.le_succ (n + 1))).restrictScalars R))

/-- Helper for Lemma 10.97.9: a source-faithful family of positive-stage splittings together with
their retraction and adjacent compatibility identities. -/
structure positive_stage_section_family (g : P →ₗ[R] M) where
  splitting : ∀ n, positive_stage_section (I := I) (P := P) (M := M) n
  is_retraction :
    ∀ n, positive_stage_section_is_retraction (I := I) (P := P) (M := M) g n (splitting n)
  compatible :
    ∀ n, positive_stage_section_compatible (I := I) (P := P) (M := M) n
      (splitting n) (splitting (n + 1))

/-- Helper for Lemma 10.97.9: the base splitting over `R ⧸ I` is exactly the stage `0`
positive-stage splitting once `I ^ 1` is rewritten as `I`. -/
lemma base_stage_section_pow_one_transport
    (g : P →ₗ[R] M) [Module.Flat R M] (hg : Function.Surjective g)
    (hquot : Module.Projective (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) :
    ∃ σ₀ : positive_stage_section (I := I) (P := P) (M := M) 0,
      positive_stage_section_is_retraction (I := I) (P := P) (M := M) g 0 σ₀ := by
  -- This isolates the unique `pow_one` transport needed in the recursive construction.
  change ∃ σ₀ :
      M ⧸ (I ^ 1 • ⊤ : Submodule R M) →ₗ[R ⧸ I ^ 1]
        P ⧸ (I ^ 1 • ⊤ : Submodule R P),
      (g.reduceModIdeal (I ^ 1)).comp σ₀ = LinearMap.id
  rw [pow_one]
  exact exists_base_stage_section (I := I) (P := P) (M := M) g hg hquot

/-- Helper for Lemma 10.97.9: recursively choosing the base-stage splitting and the successor
extensions yields a full compatible family of positive-stage splittings. -/
lemma positive_stage_section_family_of_base_and_succ
    (g : P →ₗ[R] M) [Module.Flat R M] (hg : Function.Surjective g)
    (hquot : Module.Projective (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) :
    Nonempty (positive_stage_section_family (I := I) (g := g)) := by
  classical
  let stageData := fun n =>
    { σ : positive_stage_section (I := I) (P := P) (M := M) n //
      positive_stage_section_is_retraction (I := I) (P := P) (M := M) g n σ }
  obtain ⟨σ₀, hσ₀⟩ := base_stage_section_pow_one_transport
    (I := I) (P := P) (M := M) g hg hquot
  let data : ∀ n, stageData n :=
    Nat.rec
      (motive := fun n ↦ stageData n)
      ⟨σ₀, hσ₀⟩
      (fun n prev ↦
        let hsucc := exists_compatible_stage_section_succ
          (I := I) (P := P) (M := M) (g := g) (n := n)
          hquot prev.1 prev.2 hg
        ⟨Classical.choose hsucc, (Classical.choose_spec hsucc).1⟩)
  refine ⟨?_⟩
  refine
    { splitting := fun n ↦ (data n).1
      is_retraction := fun n ↦ (data n).2
      compatible := fun n ↦ ?_ }
  -- The chosen successor stores the adjacent compatibility needed for the family field.
  let hsucc := exists_compatible_stage_section_succ
    (I := I) (P := P) (M := M) (g := g) (n := n)
    hquot (data n).1 (data n).2 hg
  simpa [data, hsucc] using (Classical.choose_spec hsucc).2

/-- Helper for Lemma 10.97.9: one can choose all positive-stage splittings recursively so that
each stage retracts `g` and successive stages are compatible under reduction. -/
lemma exists_compatible_positive_stage_sections
    (g : P →ₗ[R] M) [Module.Flat R M] (hg : Function.Surjective g)
    (hquot : Module.Projective (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) :
    Nonempty (positive_stage_section_family (I := I) (g := g)) := by
  -- Package the source-proof induction into one stable recursive chooser.
  exact positive_stage_section_family_of_base_and_succ
    (I := I) (P := P) (M := M) g hg hquot

/-- Helper for Lemma 10.97.9: the recursively chosen positive-stage sections define a compatible
family on the completion domain after evaluating at stage `n + 1`. -/
lemma positive_stage_section_family_step
    (F : positive_stage_section_family (I := I) (g := g))
    (n : ℕ) :
    AdicCompletion.transitionMap I P (Nat.le_succ (n + 1)) ∘ₗ
        ((F.splitting (n + 1)).restrictScalars R ∘ₗ AdicCompletion.eval I M (n + 2)) =
      (F.splitting n).restrictScalars R ∘ₗ AdicCompletion.eval I M (n + 1) := by
  -- Evaluate the adjacent compatibility on the `(n + 2)`-nd coordinate of the completion.
  apply LinearMap.ext
  intro x
  simpa [LinearMap.comp_apply] using
    LinearMap.congr_fun (F.compatible n) (AdicCompletion.eval I M (n + 2) x)

/-- Helper for Lemma 10.97.9: the positive-stage splitting family extends to all completion
coordinates by using the zero map at stage `0` and the given splitting at stage `n + 1`. -/
noncomputable def completion_stage_map
    (g : P →ₗ[R] M) (F : positive_stage_section_family (I := I) (g := g)) :
    ∀ n, AdicCompletion I M →ₗ[R] P ⧸ (I ^ n • ⊤ : Submodule R P)
  | 0 => 0
  | n + 1 => (F.splitting n).restrictScalars R ∘ₗ AdicCompletion.eval I M (n + 1)

/-- Helper for Lemma 10.97.9: the all-stage completion family is compatible with the quotient
transition maps. -/
lemma completion_stage_map_compat
    (g : P →ₗ[R] M) (F : positive_stage_section_family (I := I) (g := g))
    {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap I P hmn ∘ₗ
        completion_stage_map (I := I) (P := P) (M := M) g F n =
      completion_stage_map (I := I) (P := P) (M := M) g F m := by
  cases m with
  | zero =>
      -- The stage `0` quotient is the zero module, so every map into it coincides.
      have hsub : Subsingleton (P ⧸ (I ^ 0 • ⊤ : Submodule R P)) := by
        simpa using (show Subsingleton (P ⧸ (⊤ : Submodule R P)) from inferInstance)
      ext x
      exact hsub.elim _ _
  | succ m =>
      cases n with
      | zero =>
          cases Nat.not_succ_le_zero _ hmn
      | succ n =>
          let f :
              (k : ℕ) → AdicCompletion I M →ₗ[R]
                P ⧸ (I ^ (k + 1) • ⊤ : Submodule R P) :=
            fun k ↦
              (F.splitting k).restrictScalars R ∘ₗ AdicCompletion.eval I M (k + 1)
          have hf :
              ∀ {k : ℕ},
                AdicCompletion.transitionMap I P (Nat.succ_le_succ k.le_succ) ∘ₗ
                    f (k + 1) =
                  f k := by
            intro k
            -- Adjacent compatibility is exactly the successor-step hypothesis for the inverse
            -- system indexed by `n ↦ n + 1`.
            simpa [f] using positive_stage_section_family_step
              (I := I) (P := P) (M := M) (g := g) F k
          -- The strict-mono extension lemma upgrades adjacent compatibility to all positive stages.
          simpa [completion_stage_map, f] using
            (IsAdicComplete.StrictMono.factorPow_comp_eq_of_factorPow_comp_succ_eq
              (I := I) (M := AdicCompletion I M) (N := P)
              (ha := strictMono_nat_of_lt_succ fun k ↦ Nat.lt_succ_self (k + 1))
              (f := f) (hf := hf) (Nat.succ_le_succ_iff.mp hmn))

/-- Helper for Lemma 10.97.9: the compatible stage maps package through `AdicCompletion.lift`
to an `R`-linear map with the expected stagewise evaluation formula. -/
lemma completion_lift_of_positive_stage_family
    (g : P →ₗ[R] M)
    (F : positive_stage_section_family (I := I) (g := g)) :
    ∃ sR : AdicCompletion I M →ₗ[R] AdicCompletion I P,
      ∀ x n, (sR x).val n = completion_stage_map (I := I) (P := P) (M := M) g F n x := by
  refine ⟨AdicCompletion.lift I
    (completion_stage_map (I := I) (P := P) (M := M) g F)
    (completion_stage_map_compat (I := I) (P := P) (M := M) (g := g) F), ?_⟩
  intro x n
  -- Cache the stage evaluation formula once so later proofs can work coordinatewise.
  simpa using AdicCompletion.eval_lift_apply
    (I := I)
    (f := completion_stage_map (I := I) (P := P) (M := M) g F)
    (h := completion_stage_map_compat (I := I) (P := P) (M := M) (g := g) F)
    n x

/-- Helper for Lemma 10.97.9: a compatible family of positive-stage splittings assembles into an
`AdicCompletion I R`-linear section of the completed map. -/
lemma completion_section_of_compatible_stage_sections
    (g : P →ₗ[R] M)
    (F : positive_stage_section_family (I := I) (g := g)) :
    ∃ s : AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I P,
      (AdicCompletion.map I g).comp s = LinearMap.id := by
  obtain ⟨sR, hsR⟩ := completion_lift_of_positive_stage_family
    (I := I) (P := P) (M := M) (g := g) F
  have hsR_smul :
      ∀ (r : AdicCompletion I R) (x : AdicCompletion I M), sR (r • x) = r • sR x := by
    intro r x
    -- Compare the two sides stagewise, using the cached stage formula and the completion scalar API.
    ext n
    cases n with
    | zero =>
        have hsub : Subsingleton (P ⧸ (I ^ 0 • ⊤ : Submodule R P)) := by
          simpa using (show Subsingleton (P ⧸ (⊤ : Submodule R P)) from inferInstance)
        exact hsub.elim _ _
    | succ n =>
        calc
          (sR (r • x)).val (n + 1) =
              completion_stage_map (I := I) (P := P) (M := M) g F (n + 1) (r • x) := by
                rw [hsR]
          _ = (F.splitting n) ((r • x).val (n + 1)) := by
                rfl
          _ = (F.splitting n) (r.val (n + 1) • x.val (n + 1)) := by
                rw [AdicCompletion.smul_eval]
          _ = (F.splitting n) (AdicCompletion.evalₐ I (n + 1) r • x.val (n + 1)) := by
                rw [AdicCompletion.val_smul_eq_evalₐ_smul]
          _ = AdicCompletion.evalₐ I (n + 1) r • (F.splitting n (x.val (n + 1))) := by
                rw [LinearMap.map_smul]
          _ = r.val (n + 1) • (F.splitting n (x.val (n + 1))) := by
                rw [AdicCompletion.val_smul_eq_evalₐ_smul]
          _ = (r • sR x).val (n + 1) := by
                symm
                rw [AdicCompletion.smul_eval, hsR]
                rfl
  let s : AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I P :=
    { __ := sR
      map_smul' := hsR_smul }
  have hs_apply : ∀ x, s x = sR x := fun _ ↦ rfl
  refine ⟨s, ?_⟩
  apply LinearMap.ext
  intro x
  -- The completed map retracts stagewise by the stored section identities at every positive level.
  ext n
  cases n with
  | zero =>
      have hsub : Subsingleton (M ⧸ (I ^ 0 • ⊤ : Submodule R M)) := by
        simpa using (show Subsingleton (M ⧸ (⊤ : Submodule R M)) from inferInstance)
      exact hsub.elim _ _
  | succ n =>
      calc
        ((AdicCompletion.map I g).comp s x).val (n + 1) =
            (g.reduceModIdeal (I ^ (n + 1))) ((s x).val (n + 1)) := by
              rw [LinearMap.comp_apply, AdicCompletion.map_val_apply]
        _ = (g.reduceModIdeal (I ^ (n + 1)))
              (completion_stage_map (I := I) (P := P) (M := M) g F (n + 1) x) := by
              rw [hs_apply, hsR]
        _ = x.val (n + 1) := by
              simpa [completion_stage_map, LinearMap.comp_apply] using
                LinearMap.congr_fun (F.is_retraction n) (AdicCompletion.eval I M (n + 1) x)

/-- Lemma 10.97.9: if `g : P → M` is a surjective `R`-linear map, `M` is flat, and `M / IM` is
projective over `R ⧸ I`, then the induced surjection on `I`-adic completions
`P^∧ → M^∧` admits an `AdicCompletion I R`-linear section. -/
@[stacks 05D3]
theorem completionMap_has_section_of_flat_of_projective_quotient
    (g : P →ₗ[R] M) [Module.Flat R M] (hg : Function.Surjective g)
    (hquot : Module.Projective (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) :
    ∃ s : AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I P,
      (AdicCompletion.map I g).comp s = LinearMap.id := by
  obtain ⟨F⟩ := exists_compatible_positive_stage_sections
    (I := I) (P := P) (M := M) (g := g) hg hquot
  -- The positive-stage splittings pass to the inverse limit by the completion universal property.
  exact completion_section_of_compatible_stage_sections
    (I := I) (P := P) (M := M) (g := g) F

end
