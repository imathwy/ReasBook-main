import Mathlib
import Mathlib.Data.List.TFAE
import stacks_proof.stacks_project.Chap10.Definition_10_160_1
import stacks_proof.stacks_project.Chap10.Lemma_10_96_3
import stacks_proof.stacks_project.Chap10.Lemma_10_97_3
import stacks_proof.stacks_project.Chap10.Lemma_10_97_6
import stacks_proof.stacks_project.Chap10.Lemma_10_110_9
import stacks_proof.stacks_project.Chap10.Lemma_10_158_7
import stacks_proof.stacks_project.Chap15.Definition_15_37_3
import stacks_proof.stacks_project.Chap15.Lemma_15_37_2

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

noncomputable section

universe u v

section

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A] [IsLocalRing A] [IsNoetherianRing A]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

local instance : IsNoetherianRing ACompletion :=
  adicCompletion_isNoetherianRing (maximalIdeal A)

/-- Helper for Lemma 15.38.2: the extended maximal ideal in the maximal-ideal completion is
maximal. -/
private theorem completion_map_maximalIdeal_isMaximal :
    Ideal.IsMaximal (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) := by
  -- Identify the extended maximal ideal with the kernel of the first evaluation map on the
  -- completion, where maximality is immediate from the field quotient.
  letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  letI : Field (A ⧸ (maximalIdeal A) ^ 1) := by
    let e : A ⧸ (maximalIdeal A) ^ 1 ≃+* A ⧸ maximalIdeal A :=
      Ideal.quotEquivOfEq (pow_one (maximalIdeal A))
    exact IsField.toField (e.toMulEquiv.isField (Field.toIsField _))
  have hker :
      Ideal.map (algebraMap A ACompletion) (maximalIdeal A) =
        RingHom.ker (AdicCompletion.evalₐ (maximalIdeal A) 1) := by
    simpa [pow_one] using
      completionIdeal_pow_eq_ker_evalₐ (maximalIdeal A)
        (Ideal.fg_of_isNoetherianRing (maximalIdeal A)) 1
  simpa [hker] using
    (RingHom.ker_isMaximal_of_surjective
      (AdicCompletion.evalₐ (maximalIdeal A) 1)
      (AdicCompletion.surjective_evalₐ (maximalIdeal A) 1) :
        Ideal.IsMaximal (RingHom.ker (AdicCompletion.evalₐ (maximalIdeal A) 1)))

/-- Helper for Lemma 15.38.2: the maximal-ideal completion of a Noetherian local ring is again a
local ring. -/
private theorem completion_isLocalRing :
    IsLocalRing ACompletion := by
  -- A complete adic ring with maximal defining ideal is local.
  let hmax :
      Ideal.IsMaximal (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) :=
    completion_map_maximalIdeal_isMaximal (A := A)
  letI : Ideal.IsMaximal (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) := hmax
  letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  letI : IsNoetherianRing ACompletion := adicCompletion_isNoetherianRing (maximalIdeal A)
  let hcomplete :
      IsAdicComplete (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) ACompletion :=
    (adicCompletion_isNoetherian_and_isAdicComplete (maximalIdeal A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal A))).2
  letI : IsAdicComplete (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) ACompletion :=
    hcomplete
  exact @isLocalRing_of_isAdicComplete_maximal ACompletion _
    (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) hmax hcomplete

local instance : IsLocalRing ACompletion := completion_isLocalRing (A := A)

/-- Helper for Lemma 15.38.2: in the maximal-ideal completion, the extended maximal ideal is the
actual maximal ideal. -/
private theorem completion_map_maximalIdeal_eq_maximalIdeal :
    Ideal.map (algebraMap A ACompletion) (maximalIdeal A) = maximalIdeal ACompletion := by
  -- Once the extended ideal is known to be maximal in a local ring, it must equal the maximal
  -- ideal.
  letI :
      Ideal.IsMaximal (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) :=
    completion_map_maximalIdeal_isMaximal (A := A)
  exact IsLocalRing.eq_maximalIdeal inferInstance

/-- Helper for Lemma 15.38.2: the completion map of a Noetherian local ring is a local
homomorphism. -/
private instance : IsLocalHom (algebraMap A ACompletion) := by
  -- Compose with the first quotient map from the completion to the residue field.
  let φ : ACompletion →+* A ⧸ maximalIdeal A :=
    (AdicCompletion.evalOneₐ (maximalIdeal A)).toRingHom
  have hcomp : φ.comp (algebraMap A ACompletion) = Ideal.Quotient.mk (maximalIdeal A) := by
    ext x
    simp [φ]
  haveI : IsLocalHom (Ideal.Quotient.mk (maximalIdeal A)) :=
    Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (φ.comp (algebraMap A ACompletion)) := by
    simpa [hcomp]
  exact isLocalHom_of_comp (algebraMap A ACompletion) φ

/-- Helper for Lemma 15.38.2: the maximal-ideal completion is complete for its own maximal-ideal
adic topology. -/
private theorem completion_isAdicComplete_maximalIdeal :
    IsAdicComplete (maximalIdeal ACompletion) ACompletion := by
  -- Transport the canonical adic-completeness statement along the identification of maximal
  -- ideals.
  letI : IsNoetherianRing ACompletion := adicCompletion_isNoetherianRing (maximalIdeal A)
  haveI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  simpa [completion_map_maximalIdeal_eq_maximalIdeal (A := A)] using
    (adicCompletion_isNoetherian_and_isAdicComplete (maximalIdeal A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal A))).2

/-- Helper for Lemma 15.38.2: the maximal-ideal completion carries the expected complete local
ring structure. -/
private instance : IsCompleteLocalRing ACompletion := by
  -- Bundle the local and adic-complete facts proved above.
  exact
    { toIsLocalRing := completion_isLocalRing (A := A)
      toIsAdicComplete := completion_isAdicComplete_maximalIdeal (A := A) }

/-- Helper for Lemma 15.38.2: a separable residue-field extension of a complete local
`k`-algebra admits a coefficient-field section. -/
private theorem exists_residueField_section_of_completeLocal_of_isSeparableOver
    {B : Type v} [CommRing B] [Algebra k B] [IsLocalRing B] [IsCompleteLocalRing B]
    [Algebra.IsSeparableOver k (ResidueField B)] :
    ∃ φ : ResidueField B →ₐ[k] B, (residue B).comp φ = RingHom.id (ResidueField B) := by
  letI : TopologicalSpace (ResidueField B) := ⊥
  letI : DiscreteTopology (ResidueField B) := ⟨rfl⟩
  letI : TopologicalSpace B := Ideal.adicTopology (maximalIdeal B)
  let f : k →+* ResidueField B := algebraMap k (ResidueField B)
  have hfsResidue :
      f.formally_smooth_for_adic (⊥ : Ideal (ResidueField B)) := by
    letI : TopologicalSpace k := ⊥
    letI : DiscreteTopology k := ⟨rfl⟩
    let basisκ : RingFilterBasis (ResidueField B) :=
      Ideal.ringFilterBasis (⊥ : Ideal (ResidueField B))
    letI : TopologicalSpace (ResidueField B) :=
      Ideal.adicTopology (⊥ : Ideal (ResidueField B))
    have htopκ : @IsTopologicalRing (ResidueField B) basisκ.topology _ := by
      change @IsTopologicalRing (ResidueField B) basisκ.topology _
      infer_instance
    letI : IsTopologicalRing (ResidueField B) := htopκ
    letI : TopologicalRing.IsPreadicRing (ResidueField B) :=
      { toIsTopologicalRing := inferInstance
        exists_ideal_isAdic := ⟨⊥, rfl⟩ }
    -- Convert separability of `ResidueField B / k` into the adic formal smoothness of the
    -- discrete field-valued structure map.
    rw [RingHom.formally_smooth_for_adic_iff]
    have hfsAlg : (algebraMap k (ResidueField B)).FormallySmooth := by
      rw [RingHom.formallySmooth_algebraMap]
      exact Algebra.formallySmooth_of_isSeparableOver
    simpa [f] using
      RingHom.FormallySmooth.toTopologically hfsAlg continuous_of_discreteTopology
  have hBAdic : IsAdic (maximalIdeal B) := rfl
  have hBotAdic : IsAdic (⊥ : Ideal (ResidueField B)) := by
    rw [is_bot_adic_iff]
    infer_instance
  have hClosed : IsClosed ((maximalIdeal B : Ideal B) : Set B) := by
    -- In the adic topology, each power of the defining ideal is open, so the maximal ideal is
    -- also closed.
    have hOpen : IsOpen ((maximalIdeal B : Ideal B) : Set B) := by
      simpa [pow_one] using (isAdic_iff.mp hBAdic).1 1
    simpa using AddSubgroup.isClosed_of_isOpen (maximalIdeal B).toAddSubgroup hOpen
  let ψ : ResidueField B →+* B ⧸ maximalIdeal B := RingHom.id (ResidueField B)
  have hψ : Continuous ψ := continuous_of_discreteTopology
  have hcomm :
      (Ideal.Quotient.mk (maximalIdeal B)).comp (algebraMap k B) = ψ.comp f := by
    -- Both sides are the canonical map from `k` into the residue field.
    ext x
    rfl
  have hpow : ∃ t : ℕ+, maximalIdeal B ^ (t : ℕ) ≤ maximalIdeal B := by
    -- The first power already lies in the maximal ideal.
    refine ⟨1, ?_⟩
    simpa using (le_rfl : maximalIdeal B ^ (1 : ℕ) ≤ maximalIdeal B)
  obtain ⟨φ, hφ, hφk, _⟩ :=
    f.exists_continuous_lift_of_formally_smooth_for_adic
      (⊥ : Ideal (ResidueField B)) hfsResidue hBotAdic
      (maximalIdeal B) (maximalIdeal B) hBAdic hClosed hpow
      ψ hψ (algebraMap k B) hcomm
  have hφres : (residue B).comp φ = RingHom.id (ResidueField B) := by
    -- The lifted map splits the quotient map `B → ResidueField B`.
    simpa using hφ
  refine ⟨{ toRingHom := φ, commutes' := DFunLike.congr_fun hφk }, ?_⟩
  simpa using hφres

/-- Helper for Lemma 15.38.2: algebraic formal smoothness of a field extension upgrades to
topological formal smoothness when both fields carry the discrete topology. -/
private theorem field_formallySmoothTopologically_of_formallySmooth
    {k₀ : Type*} {K : Type*} [Field k₀] [Field K] [Algebra k₀ K]
    (hfs : Algebra.FormallySmooth k₀ K) :
    letI : TopologicalSpace k₀ := ⊥
    letI : TopologicalSpace K := ⊥
    (algebraMap k₀ K).FormallySmoothTopologically := by
  letI : TopologicalSpace k₀ := ⊥
  letI : DiscreteTopology k₀ := ⟨rfl⟩
  letI : TopologicalSpace K := ⊥
  letI : DiscreteTopology K := ⟨rfl⟩
  letI : TopologicalRing.IsPreadicRing K :=
    { toIsTopologicalRing := inferInstance
      exists_ideal_isAdic := by
        refine ⟨⊥, ?_⟩
        rw [is_bot_adic_iff]
        infer_instance }
  -- Forget the topology, use algebraic formal smoothness of the field map, and then re-upgrade
  -- it through the discrete-topology bridge.
  have hring : (algebraMap k₀ K).FormallySmooth := by
    rw [RingHom.formallySmooth_algebraMap]
    exact hfs
  exact RingHom.FormallySmooth.toTopologically hring continuous_of_discreteTopology

/-- Helper for Lemma 15.38.2: a formally smooth `k → B` in characteristic zero is already
formally smooth after restricting scalars along the prime field `ℚ → k`. -/
private theorem rational_formally_smooth_for_maximalIdeal_adic_of_formallySmooth
    {B : Type v} [CommRing B] [Algebra k B] [IsLocalRing B] [CharZero k]
    [Algebra ℚ B] [IsScalarTower ℚ k B]
    (hfs : (algebraMap k B).formally_smooth_for_adic (maximalIdeal B)) :
    (algebraMap ℚ B).formally_smooth_for_adic (maximalIdeal B) := by
  -- Route correction: the source proof starts by replacing the coefficient field with the prime
  -- field before constructing the power-series target.
  rw [RingHom.formally_smooth_for_adic_iff] at hfs ⊢
  letI : TopologicalSpace ℚ := ⊥
  letI : DiscreteTopology ℚ := ⟨rfl⟩
  letI : TopologicalSpace k := ⊥
  letI : DiscreteTopology k := ⟨rfl⟩
  letI : TopologicalSpace B := Ideal.adicTopology (maximalIdeal B)
  letI : PerfectField ℚ := PerfectField.ofCharZero
  letI : Algebra.IsSeparableOver ℚ k := Algebra.IsSeparableOver.of_perfectField
  have hprime : RingHom.FormallySmoothTopologically.{0, u, 0} (algebraMap ℚ k) := by
    -- The prime-field extension is algebraically formally smooth, hence topologically formally
    -- smooth in the discrete topology.
    exact
      field_formallySmoothTopologically_of_formallySmooth
        (k₀ := ℚ) (K := k) Algebra.formallySmooth_of_isSeparableOver
  have hcomp :
      RingHom.FormallySmoothTopologically.{0, v, 0}
        ((algebraMap k B).comp (algebraMap ℚ k)) := by
    -- Compose `ℚ → k` with the given `k → B` to descend formal smoothness to the prime field.
    exact RingHom.FormallySmoothTopologically.comp hprime hfs
  simpa [IsScalarTower.algebraMap_eq ℚ k B] using hcomp

/-- Helper for Lemma 15.38.2: in positive characteristic, formal smoothness over `k` descends
along the prime-field map `ZMod p → k`. -/
private theorem zmod_formally_smooth_for_maximalIdeal_adic_of_formallySmooth
    {B : Type v} [CommRing B] [Algebra k B] [IsLocalRing B] {p : ℕ} [Fact p.Prime] [CharP k p]
    [Algebra (ZMod p) k] [Algebra (ZMod p) B] [IsScalarTower (ZMod p) k B]
    (hfs : (algebraMap k B).formally_smooth_for_adic (maximalIdeal B)) :
    (algebraMap (ZMod p) B).formally_smooth_for_adic (maximalIdeal B) := by
  -- Route correction: the source proof first replaces `k` by its prime field before constructing
  -- the coefficient-field section and the power-series presentation.
  rw [RingHom.formally_smooth_for_adic_iff] at hfs ⊢
  letI : TopologicalSpace (ZMod p) := ⊥
  letI : DiscreteTopology (ZMod p) := ⟨rfl⟩
  letI : TopologicalSpace k := ⊥
  letI : DiscreteTopology k := ⟨rfl⟩
  letI : TopologicalSpace B := Ideal.adicTopology (maximalIdeal B)
  letI : PerfectField (ZMod p) := inferInstance
  letI : Algebra.IsSeparableOver (ZMod p) k := Algebra.IsSeparableOver.of_perfectField
  have hprime :
      RingHom.FormallySmoothTopologically.{0, u, 0} (algebraMap (ZMod p) k) := by
    -- Over the finite prime field, separability again upgrades to discrete topological formal
    -- smoothness.
    exact
      field_formallySmoothTopologically_of_formallySmooth
        (k₀ := ZMod p) (K := k) Algebra.formallySmooth_of_isSeparableOver
  have hcomp :
      RingHom.FormallySmoothTopologically.{0, v, 0}
        ((algebraMap k B).comp (algebraMap (ZMod p) k)) := by
    -- Compose `ZMod p → k` with the given `k → B` to descend formal smoothness to the prime
    -- field.
    exact RingHom.FormallySmoothTopologically.comp hprime hfs
  simpa [IsScalarTower.algebraMap_eq (ZMod p) k B] using hcomp

/-- Helper for Lemma 15.38.2: once the coefficient field has been reduced to a perfect prime
field, the remaining complete-case proof starts by splitting the residue map. -/
private theorem isRegularLocalRing_of_complete_perfectField_formallySmooth_for_maximalIdeal_adic
    {k₀ : Type u} [Field k₀] [PerfectField k₀]
    {B : Type v} [CommRing B] [Algebra k₀ B] [IsLocalRing B] [IsNoetherianRing B]
    [IsCompleteLocalRing B]
    (hfs : (algebraMap k₀ B).formally_smooth_for_adic (maximalIdeal B)) :
    IsRegularLocalRing B := by
  let K := ResidueField B
  letI : Algebra.IsSeparableOver k₀ K := Algebra.IsSeparableOver.of_perfectField
  obtain ⟨s, hs⟩ :=
    exists_residueField_section_of_completeLocal_of_isSeparableOver
      (k := k₀) (B := B)
  -- Route correction: the residue-field section is the first source-faithful bridge in the common
  -- prime-field argument. The remaining blocker is the canonical cotangent-basis presentation by a
  -- finite-variable power series ring and the lifted inverse modulo `maximalIdeal B ^ 2`.
  -- TODO: choose cotangent-basis lifts in `maximalIdeal B`, build the canonical surjection
  -- `MvPowerSeries (Fin n) K →ₐ[K] B`, prove it is an equivalence modulo `maximalIdeal^2`, lift
  -- the inverse by `hfs`, and conclude using the induced automorphism criterion on the power
  -- series ring.
  sorry

/-- Helper for Lemma 15.38.2: the proof reduces the general case to the complete local case. -/
private theorem isRegularLocalRing_of_complete_formallySmooth_for_maximalIdeal_adic
    {B : Type v} [CommRing B] [Algebra k B] [IsLocalRing B] [IsNoetherianRing B]
    [IsCompleteLocalRing B]
    (hfs : (algebraMap k B).formally_smooth_for_adic (maximalIdeal B)) :
    IsRegularLocalRing B := by
  -- Route correction: replace the old residue-field-separability detour by the source-faithful
  -- prime-field reduction before building the power-series presentation.
  by_cases hchar0 : ringChar k = 0
  · letI : CharZero k := (CharP.ringChar_zero_iff_CharZero k).mp hchar0
    letI : Algebra ℚ B := RingHom.toAlgebra ((algebraMap k B).comp (algebraMap ℚ k))
    letI : IsScalarTower ℚ k B := IsScalarTower.of_algebraMap_eq fun x ↦ by
      simp [RingHom.algebraMap_toAlgebra]
    have hfsQ :
        (algebraMap ℚ B).formally_smooth_for_adic (maximalIdeal B) :=
      rational_formally_smooth_for_maximalIdeal_adic_of_formallySmooth
        (k := k) (B := B) hfs
    letI : PerfectField ℚ := PerfectField.ofCharZero
    -- After restricting to the prime field, both characteristic branches share the same complete
    -- local power-series presentation argument.
    exact
      isRegularLocalRing_of_complete_perfectField_formallySmooth_for_maximalIdeal_adic
        (k₀ := ℚ) (B := B) hfsQ
  · let p := ringChar k
    have hpprime : Nat.Prime p := CharP.char_prime_of_ne_zero k hchar0
    letI : Fact p.Prime := ⟨hpprime⟩
    letI : CharP k p := inferInstance
    letI : CharP B p := CharP.of_ringHom_of_ne_zero (algebraMap k B) p hpprime.ne_zero
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    letI : Algebra (ZMod p) B := ZMod.algebra B p
    letI : IsScalarTower (ZMod p) k B := by infer_instance
    have hfsFp :
        (algebraMap (ZMod p) B).formally_smooth_for_adic (maximalIdeal B) :=
      zmod_formally_smooth_for_maximalIdeal_adic_of_formallySmooth
        (k := k) (B := B) (p := p) hfs
    letI : PerfectField (ZMod p) := inferInstance
    -- The positive-characteristic branch now feeds into the same perfect-prime-field helper.
    exact
      isRegularLocalRing_of_complete_perfectField_formallySmooth_for_maximalIdeal_adic
        (k₀ := ZMod p) (B := B) hfsFp

/-- Helper for Lemma 15.38.2: regularity descends from the maximal-ideal completion back to the
original local ring. -/
private theorem isRegularLocalRing_of_completion_regular
    [IsRegularLocalRing ACompletion] :
    IsRegularLocalRing A := by
  -- Apply the flat-local descent theorem to the faithfully flat local completion map.
  let _ : RingHom.FaithfullyFlat (algebraMap A ACompletion) :=
    maximalIdeal_adicCompletion_algebraMap_faithfullyFlat A
  exact isRegularLocalRing_of_flat_localHom_of_regularTarget ACompletion

/- Domain-style sampling for Lemma 15.38.2:
- primary domain: local commutative algebra relating adic formal smoothness of `k → A` to the
  regular-local owner on `A`;
- sampled owner declarations of the same kind:
  `RingHom.formally_smooth_for_adic`,
  `RingHom.formally_smooth_for_adic_tfae_completion_invariance`,
  `IsRegularLocalRing`,
  `RingHom.IsRegularRingMap.of_comp_of_faithfullyFlat`;
- best owner abstraction: the hypothesis should be stated directly with the chapter owner
  `(algebraMap k A).formally_smooth_for_adic (maximalIdeal A)`, while the conclusion stays on the
  canonical owner `IsRegularLocalRing A`;
- primitive data: the field `k`, the Noetherian local `k`-algebra `A`, and adic formal smoothness
  of the structure map;
- derived API: completion invariance, complete-local presentations, and regularity descent are
  proof inputs only and should not appear as extra wrapper data in the public statement.

Source/core/bridge triage:
- `source-facing`: the implication from maximal-ideal-adic formal smoothness to regularity;
- `core/canonical`: `RingHom.formally_smooth_for_adic` and `IsRegularLocalRing`;
- `bridge/view`: completion and Cohen-structure arguments used internally in the proof.
-/

-- Proof sketch: pass from the given `k`-adic formal smoothness hypothesis to the completion using
-- the completion invariance results from Section `15.37`, reduce to the complete local case, and
-- then apply Cohen structure to identify the completed ring with a quotient of a power series ring.
-- The induced surjection to the power series ring is an isomorphism on `maximalIdeal / maximalIdeal^2`,
-- forcing the dimension of `A` to equal the embedding dimension, which is the definition of
-- regularity for a Noetherian local ring.
/-- Lemma 15.38.2: if `A` is a Noetherian local `k`-algebra and the structure map `k → A` is
formally smooth for the `maximalIdeal A`-adic topology, then `A` is a regular local ring. -/
@[stacks 07EI]
theorem isRegularLocalRing_of_formallySmooth_for_maximalIdeal_adic
    (hfs : (algebraMap k A).formally_smooth_for_adic (maximalIdeal A)) :
    IsRegularLocalRing A := by
  -- First transfer maximal-ideal-adic formal smoothness to the completion.
  have hcont :
      letI : TopologicalSpace k := Ideal.adicTopology (⊥ : Ideal k)
      letI : TopologicalSpace A := Ideal.adicTopology (maximalIdeal A)
      Continuous (algebraMap k A) := by
    rw [RingHom.continuous_adic_iff_exists_pow_map_le]
    refine ⟨1, ?_⟩
    simpa using
      (bot_le : Ideal.map (algebraMap k A) ((⊥ : Ideal k) ^ 1) ≤ maximalIdeal A)
  have hTFAE :
      List.TFAE [
        (algebraMap k A).formally_smooth_for_adic (maximalIdeal A),
        ((algebraMap A ACompletion).comp (algebraMap k A)).formally_smooth_for_adic
          (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)),
        RingHom.formally_smooth_for_adic
          ((algebraMap k A).adicCompletionMap (⊥ : Ideal k) (maximalIdeal A) hcont)
          (Ideal.map (algebraMap A ACompletion) (maximalIdeal A))
      ] := by
    simpa using
      RingHom.formally_smooth_for_adic_tfae_completion_invariance
        (⊥ : Ideal k) (Ideal.fg_of_isNoetherianRing (⊥ : Ideal k))
        (maximalIdeal A) (Ideal.fg_of_isNoetherianRing (maximalIdeal A))
        (algebraMap k A) hcont
  have hfs_completion_map :
      ((algebraMap A ACompletion).comp (algebraMap k A)).formally_smooth_for_adic
        (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) :=
    (hTFAE.out 0 1).mp hfs
  have hfs_completion :
      (algebraMap k ACompletion).formally_smooth_for_adic (maximalIdeal ACompletion) := by
    -- Rewrite the completion-side ideal and the composite structure map into canonical form.
    simpa [completion_map_maximalIdeal_eq_maximalIdeal (A := A),
      show ((algebraMap A ACompletion).comp (algebraMap k A)) = algebraMap k ACompletion by
        ext x
        rfl] using hfs_completion_map
  have hcompletion_regular : IsRegularLocalRing ACompletion :=
    isRegularLocalRing_of_complete_formallySmooth_for_maximalIdeal_adic
      (k := k) (B := ACompletion) hfs_completion
  -- Then descend regularity along the faithfully flat local completion map.
  let _ : IsRegularLocalRing ACompletion := hcompletion_regular
  exact isRegularLocalRing_of_completion_regular (A := A)

end
