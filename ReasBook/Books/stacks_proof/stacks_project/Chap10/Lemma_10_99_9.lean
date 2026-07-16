import Mathlib
import stacks_proof.stacks_project.Chap10.«10_69_0_1»
import stacks_proof.stacks_project.Chap10.Remark_10_75_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise
open TensorProduct
open LinearMap
open RingTheory.Sequence
open CategoryTheory CategoryTheory.Limits

-- Re-register the compiled nilpotent-thickening theorem from the backup module without importing
-- the broken source file that Lake tries to rebuild.
open Lean Elab Command in
run_cmd do
  let env ← importModules
    #[
      { module := `stacks_project.«Chap10.backup-20260609T011139Z».Lemma_10_99_8 }
    ]
    {}
    0
  let some ci := env.find? `flat_of_nilpotent_ideal_of_flat_mod_ideal_and_tor_one_quotient_vanishes
    | throwError "missing compiled nilpotent-thickening theorem"
  match ci with
  | .thmInfo ti =>
      liftCoreM <|
        addAndCompile <|
          Declaration.thmDecl
            { name := `flat_of_nilpotent_ideal_of_flat_mod_ideal_and_tor_one_quotient_vanishes
              levelParams := ti.levelParams
              type := ti.type
              value := ti.value }
  | _ =>
      throwError "compiled nilpotent-thickening theorem has unexpected declaration kind"

universe u

section

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

-- Domain-style sampling:
-- * primary domain: commutative algebra of tensor products and successive ideal-power quotients.
-- * source-facing owner: the canonical map
--   `idealPowTensorToModuleSuccQuotient M :
--      M ⊗[R] (I^n / I^(n+1)) → I^n M / I^(n+1) M`.
-- * sampled core/canonical owners of the same construction style:
--   `Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow`,
--   `idealAssociatedGradedPiece`,
--   `TensorProduct.tensorQuotientEquiv`,
--   `Submodule.mapQ`,
--   `LinearMap.codRestrict`,
--   `TensorProduct.rid`.
-- * primitive data: the tensor-to-smul map `M ⊗[R] I^n → I^n M`.
-- * derived API: the descent to the canonical owner types for `I^n / I^(n+1)` and
--   `idealAssociatedGradedPiece I M n`, together with the pure-tensor evaluation lemma.
-- * refinement target: keep the source-facing map and remove the one-off public quotient aliases in
--   favor of the chapter/mathlib owners above.

-- Proof sketch: an element of `I ^ n` acts on `M` by scalar multiplication, so its image lies in
-- the submodule `I ^ n M = I ^ n • ⊤`.
/-- Scalar multiplication by an element of `I ^ n` lands in the submodule `I ^ n M`. -/
private theorem idealPowSmul_mem (I : Ideal R) (n : ℕ) (m : M) (a : ↥(I ^ n : Ideal R)) :
    a.1 • m ∈ idealAssociatedGradedStage I M n := by
  -- The generator `a ∈ I ^ n` acts on `m`, so its product lies in `(I ^ n) • ⊤` by definition.
  exact Submodule.smul_mem_smul a.2 (by simp)

private noncomputable def idealPowTensorToSmul (I : Ideal R) (n : ℕ) :
    M ⊗[R] ↥(I ^ n : Ideal R) →ₗ[R] ↥(idealAssociatedGradedStage I M n) :=
  LinearMap.codRestrict (idealAssociatedGradedStage I M n)
    ((TensorProduct.rid R M).toLinearMap.comp
      (TensorProduct.map (LinearMap.id : M →ₗ[R] M) ((I ^ n : Ideal R).subtype)))
    (by
      intro x
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · simp
      · intro m a
        simpa using idealPowSmul_mem I n m a
      · intro x y hx hy
        simpa using Submodule.add_mem (idealAssociatedGradedStage I M n) hx hy)

-- Proof sketch: the tensor-to-smul map carries the quotienting submodule
-- `M ⊗[R] I(I^n)` into `I(I^n M)`.
private theorem idealPowTensorToSmul_range_le (I : Ideal R) (n : ℕ) :
    LinearMap.range
        (TensorProduct.map (LinearMap.id : M →ₗ[R] M)
          ((I • (⊤ : Submodule R ↥(I ^ n : Ideal R))).subtype)) ≤
      Submodule.comap (idealPowTensorToSmul I n)
        (I • (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n))) := by
  rintro _ ⟨x, rfl⟩
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [idealPowTensorToSmul]
  · intro m a
    change idealPowTensorToSmul I n (m ⊗ₜ[R] a.1) ∈
      I • (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n))
    refine Submodule.smul_induction_on a.2 ?_ ?_
    · intro r hr b hb
      let c : ↥(idealAssociatedGradedStage I M n) := ⟨b.1 • m, idealPowSmul_mem I n m b⟩
      have hc : c ∈ (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n)) := by simp
      have hs : idealPowTensorToSmul I n (m ⊗ₜ[R] (r • b : ↥(I ^ n : Ideal R))) = r • c := by
        ext
        simp [idealPowTensorToSmul, c]
      rw [hs]
      exact Submodule.smul_mem_smul hr hc
    · intro x y hx hy
      simpa [tmul_add, map_add] using
        Submodule.add_mem (I • (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n))) hx hy
  · intro x y hx hy
    simpa using Submodule.add_mem
      (Submodule.comap (idealPowTensorToSmul I n)
        (I • (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n)))) hx hy

private theorem idealPowModuleInternalDenominator_eq (I : Ideal R) (n : ℕ) :
    I • (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n)) =
      (idealAssociatedGradedStage I M (n + 1)).submoduleOf (idealAssociatedGradedStage I M n) := by
  ext x
  rw [Submodule.mem_smul_top_iff]
  change ((x : M) ∈ I • idealAssociatedGradedStage I M n) ↔
    ((x : M) ∈ idealAssociatedGradedStage I M (n + 1))
  simp [idealAssociatedGradedStage, ← mul_smul, Ideal.mul_comm, pow_succ]

private noncomputable def idealPowModuleInternalPieceEquiv (I : Ideal R) (n : ℕ) :
    (↥(idealAssociatedGradedStage I M n) ⧸
        (I • (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n)))) ≃ₗ[R]
      idealAssociatedGradedPiece I M n :=
  Submodule.quotEquivOfEq _ _ (idealPowModuleInternalDenominator_eq I n)

variable (M) in
/-- The canonical map `M ⊗[R] (I^n / I^(n+1)) → I^n M / I^(n+1) M`, with codomain given by the
`n`th associated graded piece. -/
noncomputable def idealPowTensorToModuleSuccQuotient (I : Ideal R) (n : ℕ) :
    M ⊗[R] ((I ^ n : Ideal R) ⧸ (I • (⊤ : Submodule R ↥(I ^ n : Ideal R)))) →ₗ[R]
      idealAssociatedGradedPiece I M n :=
  (idealPowModuleInternalPieceEquiv I n).toLinearMap.comp
    (((LinearMap.range
        (TensorProduct.map (LinearMap.id : M →ₗ[R] M)
          ((I • (⊤ : Submodule R ↥(I ^ n : Ideal R))).subtype))).mapQ
      (I • (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n)))
      (idealPowTensorToSmul I n)
      (idealPowTensorToSmul_range_le I n)).comp
      (TensorProduct.tensorQuotientEquiv M
        (I • (⊤ : Submodule R ↥(I ^ n : Ideal R)))).toLinearMap)

/-- The canonical tensor-to-quotient map sends `m ⊗ a` to the class of `a • m`. -/
theorem idealPowTensorToModuleSuccQuotient_tmul_mk
    (I : Ideal R) (n : ℕ) (m : M) (a : ↥(I ^ n : Ideal R)) :
    idealPowTensorToModuleSuccQuotient M I n (m ⊗ₜ[R] Submodule.Quotient.mk a) =
      Submodule.Quotient.mk
        ⟨a.1 • m, idealPowSmul_mem I n m a⟩ := by
  have hsmul :
      idealPowTensorToSmul I n (m ⊗ₜ[R] a) =
        (⟨a.1 • m, idealPowSmul_mem I n m a⟩ : ↥(idealAssociatedGradedStage I M n)) := rfl
  simp only [idealPowTensorToModuleSuccQuotient, LinearMap.comp_apply]
  change
    idealPowModuleInternalPieceEquiv I n
      (((LinearMap.range
        (TensorProduct.map (LinearMap.id : M →ₗ[R] M)
          ((I • (⊤ : Submodule R ↥(I ^ n : Ideal R))).subtype))).mapQ
        (I • (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n)))
        (idealPowTensorToSmul I n)
        (idealPowTensorToSmul_range_le I n))
      (Submodule.Quotient.mk (m ⊗ₜ[R] a))) =
    _
  rw [Submodule.mapQ_apply, hsmul]
  simp [idealPowModuleInternalPieceEquiv]

/-- Helper for Lemma 10.99.9: at stage `n`, the image ideal in `R / I^(n + 1)` is square-zero. -/
private lemma stage_image_ideal_square_zero
    (I : Ideal R) (n : ℕ) (hn : 1 ≤ n) :
    let S := R ⧸ I ^ (n + 1)
    let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)
    J ^ 2 = ⊥ := by
  let S := R ⧸ I ^ (n + 1)
  let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)
  -- Multiplying two stage-`n` classes lands in the image of `I^(2n)`, and `2n ≥ n + 1` because
  -- `n ≥ 1`.
  apply le_antisymm
  · calc
      J ^ 2 = Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) ((I ^ n) ^ 2) := by
        dsimp [J]
        rw [← Ideal.map_pow]
      _ = Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ (n + n)) := by
        rw [pow_two, ← pow_add]
      _ ≤ Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ (n + 1)) := by
        refine Ideal.map_mono ?_
        exact Ideal.pow_le_pow_right (by omega)
      _ = ⊥ := by
        simpa [Ideal.zero_eq_bot] using Ideal.map_quotient_self (I ^ (n + 1))
  · exact bot_le

/-- Helper for Lemma 10.99.9: the stage image ideal is nilpotent because it is square-zero. -/
private lemma stage_image_ideal_isNilpotent
    (I : Ideal R) (n : ℕ) (hn : 1 ≤ n) :
    let S := R ⧸ I ^ (n + 1)
    let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)
    IsNilpotent J := by
  let S := R ⧸ I ^ (n + 1)
  let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)
  -- The previous square-zero computation is exactly the nilpotence certificate needed later.
  refine ⟨2, ?_⟩
  simpa [Ideal.zero_eq_bot] using stage_image_ideal_square_zero I n hn

/-- Helper for Lemma 10.99.9: after reducing modulo `I ^ (n + 1)`, the image of `I ^ n M` is the
canonical quotient-side submodule generated by the image ideal `J`. -/
private lemma stage_closed_fiber_smul_top_eq_map
    (I : Ideal R) (n : ℕ) :
    let S : Type u := R ⧸ I ^ (n + 1)
    let In1M : Submodule R M := I ^ (n + 1) • (⊤ : Submodule R M)
    let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)
    (I ^ n • (⊤ : Submodule R M)).map (Submodule.mkQ In1M) =
      ((J • (⊤ : Submodule S (M ⧸ In1M))).restrictScalars R) := by
  let S : Type u := R ⧸ I ^ (n + 1)
  let In1M : Submodule R M := I ^ (n + 1) • (⊤ : Submodule R M)
  let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)
  -- First normalize the image of `I ^ n M` through the quotient map, then rewrite it as the
  -- action of the quotient-side ideal `J`.
  calc
    (I ^ n • (⊤ : Submodule R M)).map (Submodule.mkQ In1M) =
        I ^ n • (⊤ : Submodule R (M ⧸ In1M)) := by
          simp [In1M, Submodule.map_smul'', Submodule.range_mkQ]
    _ =
        ((Ideal.map (algebraMap R S) (I ^ n)) •
          (⊤ : Submodule S (M ⧸ In1M))).restrictScalars R := by
            symm
            simpa using
              (Ideal.smul_restrictScalars
                (R := R) (S := S) (M := M ⧸ In1M) (I := I ^ n)
                (N := (⊤ : Submodule S (M ⧸ In1M))))
    _ = ((J • (⊤ : Submodule S (M ⧸ In1M))).restrictScalars R) := by
          rw [Ideal.Quotient.algebraMap_eq]

/-- Helper for Lemma 10.99.9: quotienting the stage ring by the image of `I ^ n` recovers
`R / I ^ n`. -/
private noncomputable def stage_closed_fiber_ring_equiv
    (I : Ideal R) (n : ℕ) :
    let S : Type u := R ⧸ I ^ (n + 1)
    let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)
    (S ⧸ J) ≃+* (R ⧸ I ^ n) := by
  let S : Type u := R ⧸ I ^ (n + 1)
  let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)
  -- This is the third-isomorphism theorem for the inclusion `I^(n + 1) ≤ I^n`.
  exact DoubleQuot.quotQuotEquivQuotOfLE (Ideal.pow_le_pow_right (by omega))

/-- Helper for Lemma 10.99.9: the stage closed fiber comparison is linear over the exact owner
ring `((R / I^(n + 1)) / J)`. -/
private noncomputable def stage_closed_fiber_owner_linear_equiv
    (I : Ideal R) (n : ℕ) :
    let S : Type u := R ⧸ I ^ (n + 1)
    let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)
    let N : Type u := M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))
    let T : Type u := S ⧸ J
    letI : Algebra T (R ⧸ I ^ n) := (stage_closed_fiber_ring_equiv (R := R) I n).toRingHom.toAlgebra
    letI : Module T (M ⧸ (I ^ n • (⊤ : Submodule R M))) :=
      Module.compHom (M ⧸ (I ^ n • (⊤ : Submodule R M))) (algebraMap T (R ⧸ I ^ n))
    (N ⧸ (J • (⊤ : Submodule S N))) ≃ₗ[T] M ⧸ (I ^ n • (⊤ : Submodule R M)) := by
  let S : Type u := R ⧸ I ^ (n + 1)
  let In1M : Submodule R M := I ^ (n + 1) • (⊤ : Submodule R M)
  let InM : Submodule R M := I ^ n • (⊤ : Submodule R M)
  let N : Type u := M ⧸ In1M
  let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)
  let T : Type u := S ⧸ J
  let B : Type u := R ⧸ I ^ n
  letI : Algebra R S := Ideal.Quotient.algebra _
  letI : Algebra S T := Ideal.Quotient.algebra _
  letI : Algebra R T := by infer_instance
  let eRing : T ≃+* B := stage_closed_fiber_ring_equiv (R := R) I n
  letI : Algebra T B := eRing.toRingHom.toAlgebra
  letI : Module T (M ⧸ InM) := Module.compHom (M ⧸ InM) (algebraMap T B)
  letI : IsScalarTower R T (M ⧸ InM) := IsScalarTower.of_compHom R T (M ⧸ InM)
  have hIn1M_le_InM : In1M ≤ InM := by
    -- The next stage is contained in the previous stage because powers of ideals decrease.
    dsimp [In1M, InM]
    simpa using
      (Submodule.smul_mono (Ideal.pow_le_pow_right (by omega))
        (show (⊤ : Submodule R M) ≤ ⊤ from le_rfl))
  let eRestrict :
      (N ⧸ ((J • (⊤ : Submodule S N)).restrictScalars R)) ≃ₗ[R] N ⧸ (J • (⊤ : Submodule S N)) :=
    -- First identify the `S`-quotient with the same quotient viewed over `R`.
    Submodule.Quotient.restrictScalarsEquiv R (J • (⊤ : Submodule S N))
  let eDenom :
      ((M ⧸ In1M) ⧸ InM.map (Submodule.mkQ In1M)) ≃ₗ[R]
        ((M ⧸ In1M) ⧸ ((J • (⊤ : Submodule S N)).restrictScalars R)) :=
    -- Rewrite the denominator into the canonical quotient-side ideal action.
    Submodule.quotEquivOfEq
      (InM.map (Submodule.mkQ In1M))
      ((J • (⊤ : Submodule S N)).restrictScalars R)
      (by
        simpa [S, In1M, InM, J, N] using
          stage_closed_fiber_smul_top_eq_map (I := I) (M := M) n)
  let eR :
      (N ⧸ (J • (⊤ : Submodule S N))) ≃ₗ[R] M ⧸ InM :=
    -- Then apply the third-isomorphism theorem on submodules.
    eRestrict.symm.trans
      (eDenom.symm.trans (Submodule.quotientQuotientEquivQuotient In1M InM hIn1M_le_InM))
  have hsurj : Function.Surjective (algebraMap R T) := by
    -- The owner ring is an iterated quotient of `R`, so every class has a representative in `R`.
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨x, rfl⟩
  -- Extending scalars upgrades the `R`-linear comparison to the exact owner ring `T`.
  exact eR.extendScalarsOfSurjective hsurj

/-- Helper for Lemma 10.99.9: the previous closed fiber `M / I^n M` is the exact closed fiber of
the stage object `M / I^(n + 1) M` over the quotient ring `R / I^(n + 1)`. -/
private lemma stage_closed_fiber_flat
    (I : Ideal R) (n : ℕ) (hn : 1 ≤ n)
    (hflat : Module.Flat (R ⧸ I ^ n) (M ⧸ (I ^ n • (⊤ : Submodule R M)))) :
    let S : Type u := R ⧸ I ^ (n + 1)
    let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)
    let N : Type u := M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))
    Module.Flat (S ⧸ J) (N ⧸ (J • (⊤ : Submodule S N))) := by
  let S : Type u := R ⧸ I ^ (n + 1)
  let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)
  let N : Type u := M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))
  let T : Type u := S ⧸ J
  let B : Type u := R ⧸ I ^ n
  let _ := hn
  let eRing : T ≃+* B := stage_closed_fiber_ring_equiv (R := R) I n
  letI : Algebra T B := eRing.toRingHom.toAlgebra
  letI : Module T (M ⧸ (I ^ n • (⊤ : Submodule R M))) :=
    Module.compHom (M ⧸ (I ^ n • (⊤ : Submodule R M))) (algebraMap T B)
  letI : IsScalarTower T B (M ⧸ (I ^ n • (⊤ : Submodule R M))) :=
    IsScalarTower.of_compHom T B (M ⧸ (I ^ n • (⊤ : Submodule R M)))
  have hflatTB : Module.Flat T B := by
    let eAlg : B ≃ₐ[T] T :=
      AlgEquiv.ofRingEquiv (R := T) (f := eRing.symm) (by
        intro x
        change eRing.symm (eRing x) = x
        simp)
    -- A ring is flat over itself, and the ring equivalence identifies `B` with the base ring `T`.
    exact Module.Flat.of_linearEquiv eAlg.toLinearEquiv
  have hflatTarget : Module.Flat T (M ⧸ (I ^ n • (⊤ : Submodule R M))) := by
    -- Transport the known flatness of `M / I^n M` across the quotient-ring equivalence.
    letI : Module.Flat T B := hflatTB
    letI : Module.Flat B (M ⧸ (I ^ n • (⊤ : Submodule R M))) := hflat
    exact Module.Flat.trans T B (M ⧸ (I ^ n • (⊤ : Submodule R M)))
  letI : Module.Flat T (M ⧸ (I ^ n • (⊤ : Submodule R M))) := hflatTarget
  let eOwner :
      (N ⧸ (J • (⊤ : Submodule S N))) ≃ₗ[T] M ⧸ (I ^ n • (⊤ : Submodule R M)) :=
    stage_closed_fiber_owner_linear_equiv (R := R) (M := M) I n
  -- The stage closed fiber is exactly the previous quotient module, now over its true owner ring.
  exact Module.Flat.of_linearEquiv eOwner

/-- Helper for Lemma 10.99.9: the graded target `I^n M / I^(n + 1) M` maps into the ambient
stage quotient `M / I^(n + 1) M` by forgetting that its representatives already lie in `I^n M`. -/
private noncomputable def idealPowPieceToStageQuotient
    (I : Ideal R) (n : ℕ) :
    idealAssociatedGradedPiece I M n →ₗ[R]
      M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)) :=
  Submodule.mapQ
    ((idealAssociatedGradedStage I M (n + 1)).submoduleOf (idealAssociatedGradedStage I M n))
    (I ^ (n + 1) • (⊤ : Submodule R M))
    (idealAssociatedGradedStage I M n).subtype
    (by
      -- Proof comment: an element of the denominator already lies in `I^(n + 1) M`, so its class
      -- in the ambient quotient is zero.
      intro x hx
      simpa [idealAssociatedGradedStage] using hx)

/-- Helper for Lemma 10.99.9: on quotient representatives, the previous map is the obvious class
map into `M / I^(n + 1) M`. -/
@[simp] private theorem idealPowPieceToStageQuotient_mk
    (I : Ideal R) (n : ℕ) (x : idealAssociatedGradedStage I M n) :
    idealPowPieceToStageQuotient (R := R) (M := M) I n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (x : M) :=
  rfl

/-- Helper for Lemma 10.99.9: the graded piece embeds in the stage quotient because its only
elements killed in `M / I^(n + 1) M` are precisely the denominator `I^(n + 1) M`. -/
private theorem idealPowPieceToStageQuotient_injective
    (I : Ideal R) (n : ℕ) :
    Function.Injective (idealPowPieceToStageQuotient (R := R) (M := M) I n) := by
  -- Proof comment: `Submodule.ker_mapQ` reduces injectivity to a direct comap computation.
  rw [← LinearMap.ker_eq_bot]
  have hcomap :
      Submodule.comap (idealAssociatedGradedStage I M n).subtype
        (I ^ (n + 1) • (⊤ : Submodule R M)) =
      (idealAssociatedGradedStage I M (n + 1)).submoduleOf (idealAssociatedGradedStage I M n) := by
    ext x
    rfl
  rw [idealPowPieceToStageQuotient, Submodule.ker_mapQ, hcomap, Submodule.mkQ_map_self]

/-- Helper for Lemma 10.99.9: fixing the right Tor variable gives the canonical comparison
between the quotient-first public owner and the fixed-left source owner. -/
private noncomputable def tor_one_left_owner_iso
    {S : Type u} [CommRing S] {N : Type u} [AddCommGroup N] [Module S N] :
    (((Tor (ModuleCat S) 1).flip).obj (ModuleCat.of S N)) ≅
      ((Tor' (ModuleCat S) 1).obj (ModuleCat.of S N)) where
  hom :=
    { app := fun X ↦ (((tor_flip_iso (ModuleCat S) 1).hom.app X).app (ModuleCat.of S N))
      naturality := by
        intro X Y f
        -- Naturality of `tor_flip_iso` in the first Tor variable becomes naturality of the fixed
        -- right-variable owner after evaluation at `N`.
        simpa using congrArg (fun α => α.app (ModuleCat.of S N))
          ((tor_flip_iso (ModuleCat S) 1).hom.naturality f) }
  inv :=
    { app := fun X ↦ (((tor_flip_iso (ModuleCat S) 1).inv.app X).app (ModuleCat.of S N))
      naturality := by
        intro X Y f
        -- The inverse comparison is natural for the same reason.
        simpa using congrArg (fun α => α.app (ModuleCat.of S N))
          ((tor_flip_iso (ModuleCat S) 1).inv.naturality f) }
  hom_inv_id := by
    ext X x
    -- The componentwise inverse law is inherited from `tor_flip_iso` after evaluation at `N`.
    have h := congrArg (fun α => α.app (ModuleCat.of S N))
      ((tor_flip_iso (ModuleCat S) 1).hom_inv_id_app X)
    simpa using congrArg (fun f => f x) (congrArg ModuleCat.Hom.hom h)
  inv_hom_id := by
    ext X x
    -- The same componentwise argument proves the other inverse law.
    have h := congrArg (fun α => α.app (ModuleCat.of S N))
      ((tor_flip_iso (ModuleCat S) 1).inv_hom_id_app X)
    simpa using congrArg (fun f => f x) (congrArg ModuleCat.Hom.hom h)

/-- Helper for Lemma 10.99.9: `tor_flip_iso` identifies the quotient-first public `Tor₁` owner
with the flipped source owner used in the textbook proof. -/
private noncomputable def tor_one_quotient_source_owner_iso
    {S : Type u} [CommRing S] {N : Type u} [AddCommGroup N] [Module S N]
    (J : Ideal S) :
    (((Tor (ModuleCat S) 1).obj (ModuleCat.of S (S ⧸ J))).obj (ModuleCat.of S N)) ≅
      (((Functor.flip (Tor' (ModuleCat S) 1)).obj (ModuleCat.of S (S ⧸ J))).obj
        (ModuleCat.of S N)) := by
  -- Route correction: the raw quotient-first `tor_flip_iso` component already lands in the
  -- flipped source owner shared with the stage-kernel argument, so no extra owner swap is needed.
  exact (((tor_flip_iso (ModuleCat S) 1).app (ModuleCat.of S (S ⧸ J))).app (ModuleCat.of S N))

/-- Helper for Lemma 10.99.9: `tor_flip_iso` identifies the module-first public owner
`Tor₁^S(N, -)` with the flipped source owner carried by `Functor.flip (Tor' ...)`. -/
private noncomputable def tor_one_module_source_owner_iso
    {S : Type u} [CommRing S] {N : Type u} [AddCommGroup N] [Module S N] :
    ((Tor (ModuleCat S) 1).obj (ModuleCat.of S N)) ≅
      ((Functor.flip (Tor' (ModuleCat S) 1)).obj (ModuleCat.of S N)) := by
  -- Route correction: the usable owner is exactly the flipped source owner supplied by
  -- `tor_flip_iso`; no additional source-owner swap is needed.
  simpa using ((tor_flip_iso (ModuleCat S) 1).app (ModuleCat.of S N))

/-- Helper for Lemma 10.99.9: `tor_flip_iso` identifies the module-first public owner with the
flipped source owner used in the stage comparison. -/
private noncomputable def tor_one_module_quotient_flip_owner_iso
    {S : Type u} [CommRing S] {N : Type u} [AddCommGroup N] [Module S N]
    (J : Ideal S) :
    (((Tor (ModuleCat S) 1).obj (ModuleCat.of S N)).obj (ModuleCat.of S (S ⧸ J))) ≅
      (((Functor.flip (Tor' (ModuleCat S) 1)).obj (ModuleCat.of S N)).obj
        (ModuleCat.of S (S ⧸ J))) :=
  (((tor_flip_iso (ModuleCat S) 1).app (ModuleCat.of S N)).app (ModuleCat.of S (S ⧸ J)))

/-- Helper for Lemma 10.99.9: Remark `10.75.9` turns vanishing of the kernel of
`J ⊗[S] N → N` into vanishing of the module-first public `Tor₁` owner. -/
private lemma tor_one_module_quotient_vanishes_of_ker_eq_bot
    {S : Type u} [CommRing S] {J : Ideal S}
    {N : Type u} [AddCommGroup N] [Module S N]
    (hker :
      LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul S N).comp J.subtype)) = ⊥) :
    IsZero ((((Tor (ModuleCat S) 1).obj (ModuleCat.of S N)).obj
      (ModuleCat.of S (S ⧸ J)))) := by
  let μ : J ⊗[S] N →ₗ[S] N :=
    TensorProduct.lift ((LinearMap.lsmul S N).comp J.subtype)
  have hker_subsingleton : Subsingleton (LinearMap.ker μ) := by
    -- The assumed kernel equality identifies the kernel module with the zero submodule.
    exact (Submodule.subsingleton_iff_eq_bot).2 (by simpa [μ] using hker)
  let e :
      (((Tor (ModuleCat S) 1).obj (ModuleCat.of S N)).obj (ModuleCat.of S (S ⧸ J))) ≃ₗ[S]
        LinearMap.ker μ :=
    tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module (R := S) (M := N) J
  have hsub :
      Subsingleton ((((Tor (ModuleCat S) 1).obj (ModuleCat.of S N)).obj
        (ModuleCat.of S (S ⧸ J)))) := by
    refine ⟨fun x y ↦ ?_⟩
    apply e.injective
    exact Subsingleton.elim _ _
  -- Remark `10.75.9` identifies the owner with the zero kernel, so the owner itself is zero.
  exact (ModuleCat.isZero_iff_subsingleton).2 hsub

/-- Helper for Lemma 10.99.9: injectivity of the canonical stage tensor map kills the stage
`Tor₁` owner needed for Lemma `10.99.8`. -/
private noncomputable def stage_tensor_source_linear_equiv
    (I : Ideal R) (n : ℕ) :
    let S : Type u := R ⧸ I ^ (n + 1)
    let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)
    let N : Type u := M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))
    J ⊗[S] N ≃ₗ[R] M ⊗[R] ((I ^ n : Ideal R) ⧸ (I • (⊤ : Submodule R ↥(I ^ n : Ideal R)))) := by
  let S : Type u := R ⧸ I ^ (n + 1)
  let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)
  let N : Type u := M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))
  let eN : N ≃ₗ[S] S ⊗[R] M :=
    ((TensorProduct.quotTensorEquivQuotSMul M (I ^ (n + 1))).symm).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  let e₁ : J ⊗[S] N ≃ₗ[S] J ⊗[S] (S ⊗[R] M) :=
    TensorProduct.congr (LinearEquiv.refl S J) eN
  let e₂ : J ⊗[S] (S ⊗[R] M) ≃ₗ[S] J ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S S J M
  let e₃ :
      J ⊗[R] M ≃ₗ[R]
        ((I ^ n : Ideal R) ⧸ (I • (⊤ : Submodule R ↥(I ^ n : Ideal R)))) ⊗[R] M :=
    TensorProduct.congr (Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow I n).symm
      (LinearEquiv.refl R M)
  let e₄ :
      ((I ^ n : Ideal R) ⧸ (I • (⊤ : Submodule R ↥(I ^ n : Ideal R)))) ⊗[R] M ≃ₗ[R]
        M ⊗[R] ((I ^ n : Ideal R) ⧸ (I • (⊤ : Submodule R ↥(I ^ n : Ideal R)))) :=
    TensorProduct.comm R
      ((I ^ n : Ideal R) ⧸ (I • (⊤ : Submodule R ↥(I ^ n : Ideal R)))) M
  -- Proof comment: first rewrite the module factor as a quotient tensor, then cancel the extra
  -- `S`, and only afterward replace the left tensor factor by the canonical `I^n / I^(n+1)` owner.
  exact (LinearEquiv.restrictScalars R (e₁.trans e₂)).trans (e₃.trans e₄)

/-- Helper for Lemma 10.99.9: the inverse of the stage source equivalence sends a pure tensor in
the original source owner to the corresponding stage pure tensor. -/
@[simp] private theorem stage_tensor_source_linear_equiv_symm_tmul_mk
    (I : Ideal R) (n : ℕ) (m : M) (a : ↥(I ^ n : Ideal R)) :
    let S : Type u := R ⧸ I ^ (n + 1)
    let N : Type u := M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))
    (stage_tensor_source_linear_equiv (R := R) (M := M) I n).symm
        (m ⊗ₜ[R] Submodule.Quotient.mk a) =
      (Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow I n (Submodule.Quotient.mk a)) ⊗ₜ[S]
        (Submodule.Quotient.mk m : N) := by
  let S : Type u := R ⧸ I ^ (n + 1)
  let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)
  let N : Type u := M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))
  let eN : N ≃ₗ[S] S ⊗[R] M :=
    ((TensorProduct.quotTensorEquivQuotSMul M (I ^ (n + 1))).symm).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  let e₁ : J ⊗[S] N ≃ₗ[S] J ⊗[S] (S ⊗[R] M) :=
    TensorProduct.congr (LinearEquiv.refl S J) eN
  let e₂ : J ⊗[S] (S ⊗[R] M) ≃ₗ[S] J ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S S J M
  let e₃ :
      J ⊗[R] M ≃ₗ[R]
        ((I ^ n : Ideal R) ⧸ (I • (⊤ : Submodule R ↥(I ^ n : Ideal R)))) ⊗[R] M :=
    TensorProduct.congr (Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow I n).symm
      (LinearEquiv.refl R M)
  let e₄ :
      ((I ^ n : Ideal R) ⧸ (I • (⊤ : Submodule R ↥(I ^ n : Ideal R)))) ⊗[R] M ≃ₗ[R]
        M ⊗[R] ((I ^ n : Ideal R) ⧸ (I • (⊤ : Submodule R ↥(I ^ n : Ideal R)))) :=
    TensorProduct.comm R
      ((I ^ n : Ideal R) ⧸ (I • (⊤ : Submodule R ↥(I ^ n : Ideal R)))) M
  -- Proof comment: unwind the transport in reverse order; each factor has a generator formula.
  change
    ((LinearEquiv.restrictScalars R (e₁.trans e₂)).symm
      (((e₃.trans e₄).symm (m ⊗ₜ[R] Submodule.Quotient.mk a)))) =
      (Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow I n (Submodule.Quotient.mk a)) ⊗ₜ[S]
        (Submodule.Quotient.mk m : N)
  rw [LinearEquiv.symm_trans_apply, TensorProduct.comm_symm_tmul, TensorProduct.congr_symm_tmul]
  change
    (e₁.trans e₂).symm
      ((Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow I n (Submodule.Quotient.mk a)) ⊗ₜ[R] m) =
      (Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow I n (Submodule.Quotient.mk a)) ⊗ₜ[S]
        (Submodule.Quotient.mk m : N)
  rw [LinearEquiv.symm_trans_apply]
  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    TensorProduct.congr_symm_tmul]
  have hq : eN.symm ((1 : S) ⊗ₜ[R] m) = (Submodule.Quotient.mk m : N) := by
    change
      (TensorProduct.quotTensorEquivQuotSMul M (I ^ (n + 1))) ((1 : S) ⊗ₜ[R] m) =
        (Submodule.Quotient.mk m : N)
    simpa using
      (TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul (M := M) (I := I ^ (n + 1)) m)
  simpa using
    congrArg
      (fun x ↦
        (Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow I n (Submodule.Quotient.mk a)) ⊗ₜ[S] x)
      hq

/-- Helper for Lemma 10.99.9: injectivity of the canonical source tensor map transports to
injectivity of the stage multiplication map `J ⊗[S] N → N`. -/
private lemma stage_tensor_multiplication_injective_of_injective_tensor_map
    (I : Ideal R) (n : ℕ) (_hn : 1 ≤ n)
    (hinj : Function.Injective (idealPowTensorToModuleSuccQuotient M I n)) :
    let S : Type u := R ⧸ I ^ (n + 1)
    let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)
    let N : Type u := M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))
    Function.Injective (TensorProduct.lift ((LinearMap.lsmul S N).comp J.subtype)) := by
  -- Proof comment: transport the stage multiplication map back to the canonical source tensor map
  -- and use injectivity of the codomain embedding into the stage quotient.
  let S : Type u := R ⧸ I ^ (n + 1)
  let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)
  let N : Type u := M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))
  let μ : J ⊗[S] N →ₗ[S] N :=
    TensorProduct.lift ((LinearMap.lsmul S N).comp J.subtype)
  have hμ_comp :
      (μ.restrictScalars R).comp
          (stage_tensor_source_linear_equiv (R := R) (M := M) I n).symm.toLinearMap =
        (idealPowPieceToStageQuotient (R := R) (M := M) I n).comp
          (idealPowTensorToModuleSuccQuotient M I n) := by
    -- Proof comment: after the source transport, both maps send `m ⊗ a` to the class of `a • m`.
    apply TensorProduct.ext'
    intro m q
    obtain ⟨a, rfl⟩ :=
      Submodule.mkQ_surjective (I • (⊤ : Submodule R ↥(I ^ n : Ideal R))) q
    change
      (μ.restrictScalars R)
          ((stage_tensor_source_linear_equiv (R := R) (M := M) I n).symm
            (m ⊗ₜ[R] Submodule.Quotient.mk a)) =
        ((idealPowPieceToStageQuotient (R := R) (M := M) I n).comp
          (idealPowTensorToModuleSuccQuotient M I n))
            (m ⊗ₜ[R] Submodule.Quotient.mk a)
    rw [LinearMap.comp_apply, stage_tensor_source_linear_equiv_symm_tmul_mk]
    change
      ((Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow I n (Submodule.Quotient.mk a) : S) •
          (Submodule.Quotient.mk m : N)) =
        (idealPowPieceToStageQuotient (R := R) (M := M) I n)
          (idealPowTensorToModuleSuccQuotient M I n (m ⊗ₜ[R] Submodule.Quotient.mk a))
    rw [idealPowTensorToModuleSuccQuotient_tmul_mk, idealPowPieceToStageQuotient_mk]
    rfl
  have hμ_comp_injective :
      Function.Injective
        ((μ.restrictScalars R).comp
          (stage_tensor_source_linear_equiv (R := R) (M := M) I n).symm.toLinearMap) := by
    rw [hμ_comp]
    exact (idealPowPieceToStageQuotient_injective (R := R) (M := M) I n).comp hinj
  have hμ_injective : Function.Injective μ := by
    -- Proof comment: the source equivalence is bijective, so injectivity after precomposition
    -- with its inverse is equivalent to injectivity of the stage multiplication map itself.
    intro x y hxy
    apply (stage_tensor_source_linear_equiv (R := R) (M := M) I n).injective
    apply hμ_comp_injective
    simpa [LinearMap.comp_apply, hxy]
  exact hμ_injective

/-- Helper for Lemma 10.99.9: the nilpotent-stage flatness step from the stage closed fiber and
injectivity of the stage multiplication map. -/
private lemma flat_of_nilpotent_stage_of_flat_closed_fiber_and_injective_tensor
    {S : Type u} [CommRing S] {J : Ideal S}
    {N : Type u} [AddCommGroup N] [Module S N]
    (hJ : IsNilpotent J)
    (hflat : Module.Flat (S ⧸ J) (N ⧸ (J • (⊤ : Submodule S N))))
    (hinj : Function.Injective (TensorProduct.lift ((LinearMap.lsmul S N).comp J.subtype))) :
    Module.Flat S N := by
  let _ := hflat
  let _ := hinj
  -- Proof comment: the earlier nilpotent-thickening owner from Lemma `10.99.8` already supplies
  -- the needed stage conclusion once the stage ideal is nilpotent.
  exact flat_of_nilpotent_ideal_of_flat_mod_ideal_and_tor_one_quotient_vanishes hJ

-- Proof sketch: apply the flatness criterion of Lemma `10.99.8` to `R / I²` and `M / I² M`. By
-- Remark `10.75.9`, the injectivity of the displayed tensor map identifies with the vanishing of
-- the relevant `Tor₁`, which is exactly the hypothesis needed there.
/-- Lemma 10.99.9 (1): if `M / IM` is flat over `R / I` and the canonical map
`M ⊗[R] (I / I^2) → IM / I^2 M` is injective, then `M / I^2 M` is flat over `R / I^2`. -/
@[stacks 0AS8]
theorem flat_mod_ideal_sq_of_flat_mod_ideal_and_injective_tensor_ideal_quotient
    {I : Ideal R}
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (hinj : Function.Injective (idealPowTensorToModuleSuccQuotient M I 1)) :
    Module.Flat (R ⧸ I ^ 2) (M ⧸ (I ^ 2 • (⊤ : Submodule R M))) := by
  let S : Type u := R ⧸ I ^ 2
  let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ 2)) (I ^ 1)
  let N : Type u := M ⧸ (I ^ 2 • (⊤ : Submodule R M))
  have hflat_one :
      Module.Flat (R ⧸ I ^ 1) (M ⧸ (I ^ 1 • (⊤ : Submodule R M))) := by
    -- Normalize the source closed fiber to the power-notation stage used in the induction API.
    rw [pow_one]
    exact hflat
  -- Route correction: apply Lemma `10.99.8` at the quotient stage `(S, J, N)`, not directly over
  -- `R`, because the source hypothesis controls `I / I^2`.
  have hflat_closed :
      Module.Flat (S ⧸ J) (N ⧸ (J • (⊤ : Submodule S N))) := by
    -- The closed fiber over the stage ring is exactly the original quotient `M / IM`.
    simpa [S, J, N, pow_one] using
      stage_closed_fiber_flat (I := I) (M := M) 1 (by simp) hflat_one
  have hμ_inj :
      Function.Injective (TensorProduct.lift ((LinearMap.lsmul S N).comp J.subtype)) := by
    -- The source injectivity hypothesis transports directly to the stage multiplication map.
    simpa [S, J, N, pow_one] using
      stage_tensor_multiplication_injective_of_injective_tensor_map
        (I := I) (M := M) 1 (by simp) hinj
  -- The remaining step is the nilpotent-thickening flatness criterion of Lemma `10.99.8`.
  exact flat_of_nilpotent_stage_of_flat_closed_fiber_and_injective_tensor
    (by simpa [S, J] using stage_image_ideal_isNilpotent I 1 (by simp))
    hflat_closed hμ_inj

-- Proof sketch: argue by induction on `k`. The case `k = 0` is the given flatness of `M / IM`,
-- and the induction step applies part (1) over the ring `R / I^(n+1)` using Remark `10.75.9` to
-- translate the injectivity hypothesis for `I^n / I^(n+1)` into the needed `Tor₁`-vanishing.
/-- Lemma 10.99.9 (2): if `M / IM` is flat over `R / I` and for every `1 ≤ n ≤ k` the canonical
map `M ⊗[R] (I^n / I^(n+1)) → I^n M / I^(n+1) M` is injective, then `M / I^(k+1) M` is flat over
`R / I^(k+1)`. -/
@[stacks 0AS8]
theorem flat_mod_ideal_pow_succ_of_flat_mod_ideal_and_injective_tensor_successive_quotients
    {I : Ideal R} (k : ℕ)
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (hinj :
      ∀ n : ℕ, 1 ≤ n → n ≤ k →
        Function.Injective (idealPowTensorToModuleSuccQuotient M I n)) :
    Module.Flat (R ⧸ I ^ (k + 1)) (M ⧸ (I ^ (k + 1) • (⊤ : Submodule R M))) := by
  induction k with
  | zero =>
      -- The case `k = 0` is exactly the given flatness modulo `I`.
      have hflat_one :
          Module.Flat (R ⧸ I ^ 1) (M ⧸ (I ^ 1 • (⊤ : Submodule R M))) := by
        rw [pow_one]
        exact hflat
      simpa using hflat_one
  | succ k ih =>
      let S : Type u := R ⧸ I ^ (k + 2)
      let J : Ideal S := Ideal.map (Ideal.Quotient.mk (I ^ (k + 2))) (I ^ (k + 1))
      let N : Type u := M ⧸ (I ^ (k + 2) • (⊤ : Submodule R M))
      have hflat_prev :
          Module.Flat (R ⧸ I ^ (k + 1)) (M ⧸ (I ^ (k + 1) • (⊤ : Submodule R M))) := by
        -- The induction hypothesis supplies the previous closed fiber.
        apply ih
        intro n hn1 hnk
        exact hinj n hn1 (Nat.le_trans hnk (Nat.le_succ k))
      have hflat_closed :
          Module.Flat (S ⧸ J) (N ⧸ (J • (⊤ : Submodule S N))) := by
        -- At stage `k + 1`, the closed fiber is `M / I^(k + 1) M`.
        simpa [S, J, N] using
          stage_closed_fiber_flat (I := I) (M := M) (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
            hflat_prev
      have hμ_inj :
          Function.Injective (TensorProduct.lift ((LinearMap.lsmul S N).comp J.subtype)) := by
        -- The corresponding stage injectivity again transports to the stage multiplication map.
        simpa [S, J, N] using
          stage_tensor_multiplication_injective_of_injective_tensor_map
            (I := I) (M := M) (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
            (hinj (k + 1) (Nat.succ_le_succ (Nat.zero_le k)) le_rfl)
      -- Again the final step is the nilpotent-thickening flatness criterion at the stage ring.
      exact flat_of_nilpotent_stage_of_flat_closed_fiber_and_injective_tensor
        (by
          simpa [S, J] using
            stage_image_ideal_isNilpotent I (k + 1) (Nat.succ_le_succ (Nat.zero_le k)))
        hflat_closed hμ_inj

end
