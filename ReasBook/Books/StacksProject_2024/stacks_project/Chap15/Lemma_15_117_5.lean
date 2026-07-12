import Mathlib
import StacksProject_2024.Chap09.Lemma_9_14_5
import StacksProject_2024.Chap10.Definition_10_162_1
import StacksProject_2024.Chap15.Definition_15_116_1
import StacksProject_2024.Chap15.Lemma_15_112_2
import StacksProject_2024.Chap15.Lemma_15_112_5
import StacksProject_2024.Chap15.Remark_15_115_1
import StacksProject_2024.Chap15.Lemma_15_117_1
import StacksProject_2024.Chap15.Lemma_15_117_2
import StacksProject_2024.Chap15.Lemma_15_117_3
import StacksProject_2024.Chap15.Remark_15_117_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w x y z

/-
Domain-style sampling for Lemma 15.117.5:
- primary domain: Epp-style elimination of inseparability for solution fields of extensions of
  discrete valuation rings;
- sampled owner declarations:
  `IsSolutionFor`,
  `IsSeparableSolutionFor`,
  `solutionFor_of_finite_extension`,
  `exists_separableSolution_of_exists_solution`;
- best owner abstraction: the source-facing content here is still the intermediate-field theorem,
  but its solution predicate should be the chapter owner `IsSolutionFor` from
  `Definition_15_116_1`; `IsSeparableSolutionFor` is only companion API because the source asks
  for `K₃ / K₁` to be separable, not necessarily `K₃ / K`;
- primitive-vs-derived split: the primitive data are the DVR extension `A ⊂ B`, its fraction
  fields `K ⊂ L`, the tower `K ⊂ K₁ ⊂ K₂`, and the hypotheses on separability, Nagata-ness, and
  purely inseparable degree; the characteristic-`p` consequence of a purely inseparable extension
  of degree `p` is derived theorem data, not a primitive ambient assumption; the conclusion that
  `K₃` remains a solution is expressed through the owner predicate `IsSolutionFor`, while the
  `K₁`-separability of `K₃` is derived theorem data, not a new owner.

Source/core/bridge triage:
- `source-facing`: the existence of a finite extension `K₃ / K₁` that is separable over `K₁` and
  still solves `A ⊂ B`;
- `core/canonical`: `IsSolutionFor`;
- `bridge/view`: `IsSeparableSolutionFor`, which packages the stronger special case of
  separability over the base field `K`.
-/

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y} {K2 : Type z}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field K1] [Algebra K K1] [Algebra A K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1]
variable [Field K2] [Algebra K1 K2] [Algebra K K2] [Algebra A K2]
variable [IsScalarTower K K1 K2] [IsScalarTower A K K2] [IsScalarTower A K1 K2]
variable [FiniteDimensional K1 K2]
variable {p : ℕ} [Fact p.Prime]
variable [Algebra.IsSeparable K L] [NagataRing B] [IsPurelyInseparable K1 K2]

local notation "A1" => integralClosure A K1
local notation "A2" => integralClosure A K2
local notation "L1" => (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)
local notation "L2" => (L ⊗[K] K2) ⧸ nilradical (L ⊗[K] K2)
local notation "B1" => integralClosure B L1
local notation "B2" => integralClosure B L2

local instance : CommRing L1 :=
  Ideal.Quotient.commRing _

local instance : CommRing L2 :=
  Ideal.Quotient.commRing _

/-- Helper for Lemma 15.117.5: the unreduced tensor tower map on the generic fibers is induced by
the identity on `L` and the field extension map `K₁ → K₂`. -/
private noncomputable abbrev reducedTensorUnreducedTowerMap :
    (L ⊗[K] K1) →ₐ[B] (L ⊗[K] K2) :=
  (Algebra.TensorProduct.map (AlgHom.id L L) (IsScalarTower.toAlgHom K K1 K2)).restrictScalars B

/-- Helper for Lemma 15.117.5: quotienting the unreduced tensor tower map by the nilradical of
the target gives the canonical comparison map from the unreduced `K₁`-fiber to `L₂`. -/
private noncomputable abbrev reducedTensorTowerMapToQuotient :
    (L ⊗[K] K1) →ₐ[B] L2 :=
  (Ideal.Quotient.mkₐ B (nilradical (L ⊗[K] K2))).comp reducedTensorUnreducedTowerMap

/-- Helper for Lemma 15.117.5: the unreduced tensor tower map sends nilpotents to nilpotents, so
it descends to the reduced quotient `L₂`. -/
private theorem reducedTensorUnreducedTowerMap_nilradical_maps_to_zero
    (x : L ⊗[K] K1) (hx : x ∈ nilradical (L ⊗[K] K1)) :
    (reducedTensorTowerMapToQuotient
      (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2) : (L ⊗[K] K1) →ₐ[B] L2) x = 0 := by
  -- Nilpotence is preserved by algebra maps, so the quotient map kills the image of the
  -- nilradical.
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [mem_nilradical]
  rcases mem_nilradical.mp hx with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [reducedTensorUnreducedTowerMap, map_pow] using
    congrArg
      (fun y ↦
        (reducedTensorUnreducedTowerMap
          (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2) :
          (L ⊗[K] K1) →ₐ[B] (L ⊗[K] K2)) y) hn

/-- Helper for Lemma 15.117.5: the induced reduced tensor tower map on `L₁ → L₂`. -/
private noncomputable abbrev reducedTensorQuotientTowerMap : L1 →ₐ[B] L2 :=
  Ideal.Quotient.liftₐ (R₁ := B) (I := nilradical (L ⊗[K] K1))
    (reducedTensorTowerMapToQuotient
      (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2))
    (reducedTensorUnreducedTowerMap_nilradical_maps_to_zero
      (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2))

/-- Helper for Lemma 15.117.5: a finite extension that is both purely inseparable and separable
has vector-space dimension `1` over the base field. -/
private theorem finrank_eq_one_of_purelyInseparable_and_separable
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (hpure : IsPurelyInseparable F E)
    (hsep : Algebra.IsSeparable F E) :
    Module.finrank F E = 1 := by
  -- Purely inseparable extensions have separable degree `1`.
  have hfinSep_one : Field.finSepDegree F E = 1 := by
    rw [Field.isPurelyInseparable_iff_finSepDegree_eq_one]
    exact hpure
  -- For separable extensions, the separable degree is the full finite dimension.
  have hsep_eq : Field.finSepDegree F E = Module.finrank F E := by
    exact (Field.finSepDegree_eq_finrank_iff F E).2 hsep
  -- Comparing the two degree computations forces the ambient finite dimension to be `1`.
  calc
    Module.finrank F E = Field.finSepDegree F E := hsep_eq.symm
    _ = 1 := hfinSep_one

/-- Helper for Lemma 15.117.5: a purely inseparable extension of prime degree cannot already be
separable. -/
private theorem not_isSeparable_of_purelyInseparable_prime_finrank
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (hpure : IsPurelyInseparable F E)
    (hfinrank : Module.finrank F E = p) :
    ¬ Algebra.IsSeparable F E := by
  intro hsep
  -- A simultaneous purely inseparable and separable finite extension would have dimension `1`.
  have hone : Module.finrank F E = 1 :=
    finrank_eq_one_of_purelyInseparable_and_separable hpure hsep
  have hp_eq_one : p = 1 := by
    simpa [hfinrank] using hone
  exact (Fact.out.ne_one hp_eq_one).elim

/-- Helper for Lemma 15.117.5: the initial stage in the finite `p`-root tower is the base field.
-/
private theorem finiteGeneratorStage_zero_eq_bot
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]
    {n : ℕ} (α : Fin n → E) :
    finiteGeneratorStage F α (0 : Fin (n + 1)) = ⊥ := by
  -- At stage `0` no generators have been adjoined yet.
  ext x
  simp [finiteGeneratorStage, finiteGeneratorPrefix]

/-- Helper for Lemma 15.117.5: the first successor stage in a finite `p`-root tower is the simple
extension generated by the first chosen root. -/
private theorem finiteGeneratorStage_one_eq_adjoin_simple
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]
    {n : ℕ} (α : Fin (n + 1) → E) :
    finiteGeneratorStage F α (1 : Fin (n + 2)) = F⟮α 0⟯ := by
  -- At stage `1`, the prefix consists exactly of the first generator.
  rw [finiteGeneratorStage]
  have hprefix :
      finiteGeneratorPrefix α (1 : Fin (n + 2)) = ({α 0} : Set E) := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hj0 : j = 0 := by
        apply Fin.ext
        exact Nat.eq_zero_of_lt_one hj
      simpa [hj0]
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      refine ⟨0, by simpa using Nat.zero_lt_one, ?_⟩
      simpa [hx]
  simpa [hprefix]

/-- Helper for Lemma 15.117.5: a successor stage in the finite `p`-root tower is obtained by
adjoining the new chosen generator to the previous stage. -/
private theorem finiteGeneratorStage_succ_eq_adjoin
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]
    {n : ℕ} (α : Fin n → E) (i : Fin n) :
    finiteGeneratorStage F α (Fin.succ i) =
      (IntermediateField.adjoin (finiteGeneratorStage F α (Fin.castSucc i))
        ({α i} : Set E)).restrictScalars F := by
  have hprefix :
      finiteGeneratorPrefix α (Fin.succ i) =
        Set.insert (α i) (finiteGeneratorPrefix α (Fin.castSucc i)) := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      rcases Nat.lt_succ_iff.mp hj with hjlt | hjeq
      · exact Or.inr ⟨j, hjlt, rfl⟩
      · left
        exact congrArg α (Fin.ext hjeq)
    · intro hx
      rcases hx with rfl | hx
      · exact ⟨i, Nat.lt_succ_self i.1, rfl⟩
      · rcases hx with ⟨j, hj, rfl⟩
        exact ⟨j, Nat.lt_succ_of_lt hj, rfl⟩
  -- Re-express the successor prefix as the previous prefix together with the new generator.
  rw [finiteGeneratorStage, hprefix]
  -- Then use the canonical adjoin-by-insert identity on intermediate fields.
  simpa [finiteGeneratorStage] using
    (Algebra.adjoin_insert_adjoin (R := F)
      (s := finiteGeneratorPrefix α (Fin.castSucc i)) (x := α i))

/-- Helper for Lemma 15.117.5: adjoining a singleton over the base field viewed as `⊥` and then
restricting scalars recovers the usual simple extension. -/
private theorem adjoin_bot_singleton_restrictScalars_eq_adjoin_simple
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E] (x : E) :
    (IntermediateField.adjoin (⊥ : IntermediateField F E) ({x} : Set E)).restrictScalars F =
      F⟮x⟯ := by
  ext y
  constructor
  · intro hy
    simpa using hy
  · intro hy
    simpa using hy

/-- Helper for Lemma 15.117.5: multiplying a simple generator by a nonzero scalar from the base
field does not change the generated intermediate field. -/
private theorem adjoin_simple_eq_top_of_mul_generator
    {c : K1} {α : K2} (hc : c ≠ 0) (hαtop : K1⟮α⟯ = ⊤) :
    K1⟮algebraMap K1 K2 c * α⟯ = ⊤ := by
  let β : K2 := algebraMap K1 K2 c * α
  -- Recover `α` from `β` by multiplying with the inverse scalar from the base field.
  have hα_mem : α ∈ K1⟮β⟯ := by
    have hc_inv_mem : algebraMap K1 K2 c⁻¹ ∈ K1⟮β⟯ := by
      exact IntermediateField.algebraMap_mem (K1⟮β⟯) c⁻¹
    have hβ_mem : β ∈ K1⟮β⟯ := by
      exact IntermediateField.mem_adjoin_simple_self K1 β
    have hmul_mem :
        algebraMap K1 K2 c⁻¹ * β ∈ K1⟮β⟯ := by
      exact IntermediateField.mul_mem (K1⟮β⟯) hc_inv_mem hβ_mem
    simpa [β, mul_assoc, hc] using hmul_mem
  have hle : K1⟮α⟯ ≤ K1⟮β⟯ := by
    exact (IntermediateField.adjoin_simple_le_iff).2 hα_mem
  exact top_unique <| by
    simpa [hαtop] using hle

/-- Helper for Lemma 15.117.5: if `K₂ / K₁` is purely inseparable of prime degree, then it is a
simple extension generated by one element whose `p`th power already lies in the base field. -/
private theorem prime_degree_pth_root_generator
    (hdeg : Module.finrank K1 K2 = p) :
    ∃ α : K2, α ^ p ∈ (⊥ : IntermediateField K1 K2) ∧ K1⟮α⟯ = ⊤ := by
  -- First rule out characteristic zero, where every algebraic extension would be separable.
  have hnot_sep :
      ¬ Algebra.IsSeparable K1 K2 := by
    exact
      not_isSeparable_of_purelyInseparable_prime_finrank
        (F := K1) (E := K2) (show IsPurelyInseparable K1 K2 from inferInstance) hdeg
  have hchar_ne_zero : ringChar K1 ≠ 0 := by
    intro hchar0
    letI : CharZero K1 := (CharP.ringChar_zero_iff_CharZero K1).mp hchar0
    letI : PerfectField K1 := PerfectField.ofCharZero
    have hsep : Algebra.IsSeparable K1 K2 := by
      infer_instance
    exact hnot_sep hsep
  let q := ringChar K1
  have hqprime : Nat.Prime q := CharP.char_prime_of_ne_zero K1 hchar_ne_zero
  letI : Fact q.Prime := ⟨hqprime⟩
  letI : CharP K1 q := inferInstance
  obtain ⟨n, α, hα⟩ := exists_pthRoot_tower_of_finite_purelyInseparable (F := K1) (E := K2) q
  have hn_ne_zero : n ≠ 0 := by
    intro hn
    have hbot_top : (⊥ : IntermediateField K1 K2) = ⊤ := by
      -- If the tower had no generators, its top stage would already be the base field.
      simpa [hn, finiteGeneratorStage_zero_eq_bot] using hα.stage_top
    have hone : Module.finrank K1 K2 = 1 := by
      -- A trivial top stage forces the ambient extension to have degree one.
      exact (IntermediateField.bot_eq_top_iff_finrank_eq_one).1 hbot_top
    have hp_eq_one : p = 1 := by
      simpa [hdeg] using hone
    exact (Fact.out.ne_one hp_eq_one).elim
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn_ne_zero
  let M : IntermediateField K1 K2 :=
    finiteGeneratorStage K1 α (Fin.castSucc (Fin.last m))
  let a : K2 := α (Fin.last m)
  have hstage_top :
      finiteGeneratorStage K1 α (Fin.succ (Fin.last m)) = ⊤ := by
    -- The successor of the predecessor of the final stage is the whole extension.
    simpa using hα.stage_top
  have hrel : Module.finrank M K2 = q := by
    -- The last step in the `q`-root tower has degree `q`.
    simpa [M, hstage_top] using hα.relfinrank_eq (Fin.last m)
  have hmul : Module.finrank K1 M * q = p := by
    -- Compare the total degree with the tower law through the last predecessor stage.
    calc
      Module.finrank K1 M * q = Module.finrank K1 M * Module.finrank M K2 := by
        rw [hrel]
      _ = Module.finrank K1 K2 := by
        rw [finrank_mul_finrank K1 M K2]
      _ = p := hdeg
  have hq_dvd : q ∣ p := by
    refine ⟨Module.finrank K1 M, ?_⟩
    simpa [Nat.mul_comm] using hmul
  have hq_eq_p : q = p := by
    rcases (Nat.dvd_prime (Fact.out : Nat.Prime p)).mp hq_dvd with hq_one | hq_p
    · exact (hqprime.ne_one hq_one).elim
    · exact hq_p
  have hfinrank_M : Module.finrank K1 M = 1 := by
    -- Once `q = p`, the predecessor stage must already be the base field.
    exact Nat.eq_of_mul_eq_mul_right (Fact.out.pos) <| by
      simpa [hq_eq_p] using hmul
  have hbot_top_M : (⊥ : IntermediateField K1 M) = ⊤ := by
    -- Degree one over `K₁` identifies the predecessor stage with the base field.
    exact (IntermediateField.bot_eq_top_iff_finrank_eq_one).2 hfinrank_M
  have hM_bot : M = (⊥ : IntermediateField K1 K2) := by
    ext x
    constructor
    · intro hx
      have hx_top : (⟨x, hx⟩ : M) ∈ (⊤ : IntermediateField K1 M) := by
        simp
      have hx_bot : (⟨x, hx⟩ : M) ∈ (⊥ : IntermediateField K1 M) := by
        simpa [hbot_top_M] using hx_top
      rcases IntermediateField.mem_bot.mp hx_bot with ⟨c, hc⟩
      exact IntermediateField.mem_bot.mpr ⟨c, Subtype.ext_iff.mp hc⟩
    · intro hx
      exact bot_le hx
  have hapow_mem_q : a ^ q ∈ (⊥ : IntermediateField K1 K2) := by
    -- The last generator has its `q`th power in the predecessor stage, now identified with the
    -- base field.
    simpa [a, M, hM_bot] using hα.pth_power_mem (Fin.last m)
  have ha_top : K1⟮a⟯ = ⊤ := by
    have hstage_simple :
        finiteGeneratorStage K1 α (Fin.succ (Fin.last m)) = K1⟮a⟯ := by
      -- After collapsing the predecessor stage to the base field, the final tower step becomes
      -- the simple extension generated by `a`.
      calc
        finiteGeneratorStage K1 α (Fin.succ (Fin.last m)) =
            (IntermediateField.adjoin M ({a} : Set K2)).restrictScalars K1 := by
              simpa [a, M] using
                finiteGeneratorStage_succ_eq_adjoin (F := K1) (E := K2) α (Fin.last m)
        _ = (IntermediateField.adjoin (⊥ : IntermediateField K1 K2) ({a} : Set K2)).restrictScalars K1 := by
              rw [hM_bot]
        _ = K1⟮a⟯ := by
              exact adjoin_bot_singleton_restrictScalars_eq_adjoin_simple (F := K1) (E := K2) a
    calc
      K1⟮a⟯ = finiteGeneratorStage K1 α (Fin.succ (Fin.last m)) := hstage_simple.symm
      _ = ⊤ := hstage_top
  refine ⟨a, ?_, ha_top⟩
  -- Rewrite the `q`th-power containment using `q = p`.
  simpa [hq_eq_p] using hapow_mem_q

/-- Helper for Lemma 15.117.5: after rescaling the prime-degree generator by a suitable power of
the source uniformizer, its `p`th power comes from the source integral closure. -/
private theorem rescaled_pth_root_parameter_mem_source_integralClosure
    (hdeg : Module.finrank K1 K2 = p) :
    ∃ β : K2, ∃ a1' : integralClosure A K1,
      β ^ p = algebraMap (integralClosure A K1) K2 a1' ∧
        K1⟮β⟯ = ⊤ := by
  obtain ⟨π, hπirr, hπmax⟩ :=
    IsExtensionOfDiscreteValuationRings.exists_uniformizer_generator A
  obtain ⟨α, a1, hαpow, hαtop, -⟩ :=
    prime_degree_pth_root_presentation (K1 := K1) (K2 := K2) (p := p) hdeg
  have ha1_integral_K : IsIntegral K a1 := by
    exact Algebra.IsIntegral.isIntegral a1
  -- First clear an arbitrary fraction denominator for `a₁` using the fraction-ring localization.
  obtain ⟨s, hs_integral⟩ :=
    ha1_integral_K.exists_multiple_integral_of_isLocalization (nonZeroDivisors A) a1
  have hs_ne_zero : s.1 ≠ 0 := by
    exact mem_nonZeroDivisors_iff_ne_zero.mp s.2
  obtain ⟨n, hs_assoc⟩ :=
    IsExtensionOfDiscreteValuationRings.associated_uniformizer_pow_of_nonzero
      π s.1 hπmax hs_ne_zero
  -- Replace the arbitrary nonzero denominator by the chosen uniformizer power.
  have hpi_a1_integral :
      IsIntegral A (algebraMap A K1 (π ^ n) * a1) := by
    rcases hs_assoc with ⟨u, hu⟩
    have hu_integral : IsIntegral A (algebraMap A K1 (↑u : A)) := by
      exact isIntegral_algebraMap
    have hmul_integral :
        IsIntegral A
          (algebraMap A K1 (↑u : A) * (algebraMap A K1 s.1 * a1)) := by
      exact hu_integral.mul hs_integral
    simpa [hu, map_mul, mul_assoc, mul_left_comm, mul_comm] using hmul_integral
  -- Multiply by the remaining `(p - 1)`-fold uniformizer power so the final rescaled generator has
  -- `p`th power integral over `A`.
  let a1val : K1 :=
    algebraMap A K1 (π ^ ((p - 1) * n)) * (algebraMap A K1 (π ^ n) * a1)
  have ha1val_integral : IsIntegral A a1val := by
    have hpow_integral :
        IsIntegral A (algebraMap A K1 (π ^ ((p - 1) * n))) := by
      exact isIntegral_algebraMap
    dsimp [a1val]
    exact hpow_integral.mul hpi_a1_integral
  let a1' : integralClosure A K1 := ⟨a1val, ha1val_integral⟩
  let β : K2 := algebraMap A K2 (π ^ n) * α
  refine ⟨β, a1', ?_, ?_⟩
  · -- Compare `β^p` with the chosen integral parameter by first peeling off one factor of
    -- `algebraMap A K₂ (π^n)` and then rewriting the remaining power in the base field.
    have hp_pos : 0 < p := Fact.out.pos
    dsimp [β, a1', a1val]
    calc
      (algebraMap A K2 (π ^ n) * α) ^ p =
          (algebraMap A K2 (π ^ n)) ^ p * α ^ p := by
            rw [mul_pow]
      _ =
          (algebraMap A K2 (π ^ n)) ^ p * algebraMap K1 K2 a1 := by
            rw [hαpow]
      _ =
          (algebraMap A K2 (π ^ n)) ^ (p - 1) *
            (algebraMap A K2 (π ^ n) * algebraMap K1 K2 a1) := by
            rw [← Nat.sub_add_cancel hp_pos, pow_add]
            ring
      _ =
          algebraMap A K2 (π ^ ((p - 1) * n)) *
            (algebraMap A K2 (π ^ n) * algebraMap K1 K2 a1) := by
            rw [← map_pow]
            simp [pow_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ =
          algebraMap (integralClosure A K1) K2
            ⟨a1val, ha1val_integral⟩ := by
            simp [a1val, map_mul, mul_assoc]
  · -- Rescaling by a nonzero base scalar preserves the simple generator property.
    have hpi_pow_ne_zero : π ^ n ≠ 0 := by
      exact pow_ne_zero n hπirr.ne_zero
    have hscalar_ne_zero : algebraMap A K1 (π ^ n) ≠ 0 := by
      exact
        (map_ne_zero_iff (algebraMap A K1)
          (NoZeroSMulDivisors.algebraMap_injective A K1)).2 hpi_pow_ne_zero
    exact
      adjoin_simple_eq_top_of_mul_generator
        (K1 := K1) (K2 := K2) hscalar_ne_zero hαtop

/-- Helper for Lemma 15.117.5: the prime-degree purely inseparable step already has the explicit
monogenic presentation `K₂ ≃ K₁[X] / (X ^ p - a₁)`. -/
private theorem prime_degree_pth_root_presentation
    (hdeg : Module.finrank K1 K2 = p) :
    ∃ α : K2, ∃ a1 : K1,
      α ^ p = algebraMap K1 K2 a1 ∧
        K1⟮α⟯ = ⊤ ∧
        Nonempty (AdjoinRoot (X ^ p - C a1 : Polynomial K1) ≃ₐ[K1] K2) := by
  obtain ⟨α, hαp, hαtop⟩ :=
    prime_degree_pth_root_generator (K1 := K1) (K2 := K2) (p := p) hdeg
  rcases IntermediateField.mem_bot.mp hαp with ⟨a1, ha1⟩
  have hα_integral : IsIntegral K1 α := by
    exact Algebra.IsIntegral.isIntegral α
  have hα_aeval : aeval α (X ^ p - C a1 : Polynomial K1) = 0 := by
    -- The explicit owner polynomial vanishes at `α` because `α ^ p` comes from `a₁`.
    rw [Polynomial.aeval_def, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    exact sub_eq_zero.mpr ha1
  let eTop : K1⟮α⟯ ≃ₐ[K1] K2 :=
    (IntermediateField.equivOfEq hαtop).trans IntermediateField.topEquiv
  have hminpoly_natDegree : (minpoly K1 α).natDegree = p := by
    -- Since `α` generates all of `K₂`, its minimal polynomial has the full prime degree.
    calc
      (minpoly K1 α).natDegree = Module.finrank K1 K1⟮α⟯ := by
        symm
        exact IntermediateField.adjoin.finrank hα_integral
      _ = Module.finrank K1 K2 := by
        simpa using eTop.toLinearEquiv.finrank_eq
      _ = p := hdeg
  have hpoly_natDegree : (X ^ p - C a1 : Polynomial K1).natDegree = p := by
    simpa using Polynomial.natDegree_X_pow_sub_C a1 (Fact.out.ne_zero : p ≠ 0)
  have hminpoly_dvd :
      minpoly K1 α ∣ (X ^ p - C a1 : Polynomial K1) := by
    -- The minimal polynomial divides every polynomial annihilating `α`.
    exact minpoly.dvd K1 α hα_aeval
  have hpoly_eq_minpoly :
      (X ^ p - C a1 : Polynomial K1) = minpoly K1 α := by
    -- Matching degree `p` forces the explicit `p`th-root polynomial to be the minimal polynomial.
    exact
      Polynomial.eq_of_monic_of_dvd_of_natDegree_le
        (minpoly.monic hα_integral)
        (Polynomial.monic_X_pow_sub_C a1 (Fact.out.ne_zero : p ≠ 0))
        hminpoly_dvd
        (by simpa [hpoly_natDegree, hminpoly_natDegree])
  refine ⟨α, a1, ha1, hαtop, ?_⟩
  -- Route correction: package the simple generator into the exact `AdjoinRoot` quotient shape
  -- required by the source deformation argument before addressing integral-closure rows.
  refine ⟨?_⟩
  exact
    (AdjoinRoot.algEquivOfEq K1 (minpoly K1 α) (X ^ p - C a1 : Polynomial K1)
      hpoly_eq_minpoly).symm.trans
      ((IntermediateField.adjoinRootEquivAdjoin K1 hα_integral).trans eTop)

/-- Helper for Lemma 15.117.5: the explicit source monogenic ring for the normalized
purely-inseparable prime step is `A₁[X] / (X ^ p - a₁')`. -/
private noncomputable abbrev sourceMonogenicRing (a1' : A1) :=
  AdjoinRoot (X ^ p - C a1' : Polynomial A1)

/-- Helper for Lemma 15.117.5: the rescaled generator is integral over the source integral
closure `A₁`. -/
private theorem source_generator_isIntegral_over_sourceIntegralClosure
    (β : K2) (a1' : A1)
    (hβpow : β ^ p = algebraMap A1 K2 a1') :
    IsIntegral A1 β := by
  -- The defining `p`th-power equation already has coefficients in `A₁`.
  exact IsIntegral.of_pow Fact.out.pos <| by
    rw [hβpow]
    exact isIntegral_algebraMap

/-- Helper for Lemma 15.117.5: the rescaled generator is integral over the original base DVR
`A`, so it defines an element of `integralClosure A K₂`. -/
private theorem source_generator_isIntegral_over_base
    (β : K2) (a1' : A1)
    (hβpow : β ^ p = algebraMap A1 K2 a1') :
    IsIntegral A β := by
  -- Integrality over `A₁` descends to integrality over `A` along the integral tower
  -- `A ⊆ A₁ ⊆ K₂`.
  exact
    (source_generator_isIntegral_over_sourceIntegralClosure
      (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) β a1' hβpow).tower_top

/-- Helper for Lemma 15.117.5: the normalized source generator annihilates the source
monogenic polynomial in `K₂`. -/
private theorem source_generator_aeval_eq_zero
    (β : K2) (a1' : A1)
    (hβpow : β ^ p = algebraMap A1 K2 a1') :
    aeval β (X ^ p - C a1' : Polynomial A1) = 0 := by
  -- Evaluating term-by-term reduces the claim to the chosen `p`th-power equation.
  rw [Polynomial.aeval_def, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  exact sub_eq_zero.mpr hβpow

/-- Helper for Lemma 15.117.5: the source monogenic ring maps to the generic fiber `K₂` by
sending the distinguished root to the rescaled generator `β`. -/
private noncomputable def sourceMonogenicToField
    (β : K2) (a1' : A1)
    (hβpow : β ^ p = algebraMap A1 K2 a1') :
    sourceMonogenicRing (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) a1' →ₐ[A1] K2 :=
  AdjoinRoot.liftAlgHom (X ^ p - C a1' : Polynomial A1) (Algebra.ofId A1 K2) β
    (source_generator_aeval_eq_zero
      (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) β a1' hβpow)

/-- Helper for Lemma 15.117.5: the integral-closure element defined by the normalized source
generator annihilates the source monogenic polynomial. -/
private theorem source_generator_aeval_eq_zero_in_integralClosure
    (β : K2) (a1' : A1)
    (hβpow : β ^ p = algebraMap A1 K2 a1') :
    let _ : Algebra A1 A2 :=
      sourceIntegralClosureTowerMap
        (A := A) (K := K) (K1 := K1) (K2 := K2).toAlgebra
    let βA2 : A2 :=
      ⟨β,
        source_generator_isIntegral_over_base
          (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) β a1' hβpow⟩
    aeval βA2 (X ^ p - C a1' : Polynomial A1) = 0 := by
  let _ : Algebra A1 A2 :=
    sourceIntegralClosureTowerMap
      (A := A) (K := K) (K1 := K1) (K2 := K2).toAlgebra
  let βA2 : A2 :=
    ⟨β,
      source_generator_isIntegral_over_base
        (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) β a1' hβpow⟩
  -- This is the same `p`th-power relation, now viewed inside the integral-closure subtype.
  ext
  change β ^ p - algebraMap A1 K2 a1' = 0
  exact sub_eq_zero.mpr hβpow

/-- Helper for Lemma 15.117.5: the source monogenic ring maps to `A₂ = integralClosure A K₂` by
sending the distinguished root to the integral element defined by the rescaled generator `β`. -/
private noncomputable def sourceMonogenicToIntegralClosure
    (β : K2) (a1' : A1)
    (hβpow : β ^ p = algebraMap A1 K2 a1') :
    sourceMonogenicRing (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) a1' →ₐ[A1] A2 :=
  let _ : Algebra A1 A2 :=
    sourceIntegralClosureTowerMap
      (A := A) (K := K) (K1 := K1) (K2 := K2).toAlgebra
  let βA2 : A2 :=
    ⟨β,
      source_generator_isIntegral_over_base
        (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) β a1' hβpow⟩
  AdjoinRoot.liftAlgHom (X ^ p - C a1' : Polynomial A1) (Algebra.ofId A1 A2) βA2 <|
    source_generator_aeval_eq_zero_in_integralClosure
      (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) β a1' hβpow

/-- Helper for Lemma 15.117.5: after installing the source monogenic algebra structure on `A₂`,
the canonical map is definitionally the ambient algebra map. -/
private theorem sourceMonogenicToIntegralClosure_eq_algebraMap
    (β : K2) (a1' : A1)
    (hβpow : β ^ p = algebraMap A1 K2 a1') :
    let φA :=
      sourceMonogenicToIntegralClosure
        (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) β a1' hβpow
    let _ : Algebra (sourceMonogenicRing (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) a1') A2 :=
      φA.toAlgebra
    φA.toRingHom =
      algebraMap
        (sourceMonogenicRing (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) a1')
        A2 := by
  rfl

/-- Helper for Lemma 15.117.5: once the source monogenic row is installed on `A₂`, the square of
any nonzero coefficient from `A₁` remains a nonzerodivisor after mapping into `A₂`. -/
private theorem sourceMonogenic_square_mem_nonZeroDivisors
    (β : K2) (a1' : A1)
    (hβpow : β ^ p = algebraMap A1 K2 a1')
    (π1 : A1) (hπ1 : π1 ≠ 0) :
    let φA :=
      sourceMonogenicToIntegralClosure
        (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) β a1' hβpow
    let _ : Algebra
        (sourceMonogenicRing (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) a1')
        A2 :=
      φA.toAlgebra
    algebraMap
        (sourceMonogenicRing (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) a1')
        A2
        (algebraMap
          (integralClosure A K1)
          (sourceMonogenicRing (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) a1')
          (π1 ^ 2)) ∈
      nonZeroDivisors A2 := by
  let φA :=
    sourceMonogenicToIntegralClosure
      (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) β a1' hβpow
  let _ : Algebra
      (sourceMonogenicRing (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) a1')
      A2 :=
    φA.toAlgebra
  have himage_ne_zero : algebraMap A1 A2 (π1 ^ 2) ≠ 0 := by
    -- The source integral closure `A₂` is a domain inside the field `K₂`, so nonzero elements of
    -- `A₁` stay nonzero after the canonical tower map.
    exact
      map_ne_zero (NoZeroSMulDivisors.algebraMap_injective A1 A2)
        (pow_ne_zero 2 hπ1)
  -- Rewrite the source monogenic image through the ambient tower map, then close by domainness of
  -- `A₂`.
  simpa [φA, sourceMonogenicToIntegralClosure_eq_algebraMap, map_pow] using
    (mem_nonZeroDivisors_iff_ne_zero.mpr himage_ne_zero)

/-- Helper for Lemma 15.117.5: every element of `K₂` is a polynomial in the normalized
generator `β` over `K₁` once `β` generates the full simple extension. -/
private theorem source_generator_exists_polynomial_representation
    (β : K2)
    (hβtop : K1⟮β⟯ = ⊤)
    (z : K2) :
    ∃ q : Polynomial K1, aeval β q = z := by
  have hz :
      z ∈ (K1⟮β⟯.toSubalgebra : Set K2) := by
    -- Rewrite the target element into the source simple subalgebra generated by `β`.
    simpa [hβtop] using
      (show z ∈ ((⊤ : IntermediateField K1 K2).toSubalgebra : Set K2) by simp)
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (Algebra.IsAlgebraic.isAlgebraic β)] at hz
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
  rcases hz with ⟨q, hq⟩
  exact ⟨q, hq⟩

/-- Helper for Lemma 15.117.5: a single coefficient of a `K₁`-polynomial can be rewritten using
a nonzero denominator from the source integral closure `A₁`. -/
private theorem source_coeff_fractionRing_clear_denominator
    (c : K1) :
    ∃ n d : A1, d ≠ 0 ∧ algebraMap A1 K1 n = algebraMap A1 K1 d * c := by
  let _ : IsFractionRing A1 K1 := integralClosure.isFractionRing_of_finite_extension K K1
  -- Use the canonical fraction-ring structure on `A₁` to clear one coefficient denominator.
  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors A1) c
  refine ⟨n, d, mem_nonZeroDivisors_iff_ne_zero.mp d.2, ?_⟩
  calc
    algebraMap A1 K1 n = c * algebraMap A1 K1 d := by
      simpa using hnd.symm
    _ = algebraMap A1 K1 d * c := by
      rw [mul_comm]

/-- Helper for Lemma 15.117.5: finitely many coefficients in `K₁` admit one common denominator
from `A₁`. -/
private theorem source_finite_common_denominator_for_family
    (t : Finset ℕ) (c : ℕ → K1) :
    ∃ s : A1, s ≠ 0 ∧
      ∀ n ∈ t, ∃ b : A1, algebraMap A1 K1 b = algebraMap A1 K1 s * c n := by
  induction t using Finset.induction_on with
  | empty =>
      refine ⟨1, one_ne_zero, ?_⟩
      intro n hn
      cases hn
  | @insert n t hn ih =>
      rcases ih with ⟨s, hs, hsupport⟩
      rcases source_coeff_fractionRing_clear_denominator (A := A) (K := K) (K1 := K1) (c n) with
        ⟨bn, dn, hdn, hbn⟩
      refine ⟨s * dn, mul_ne_zero hs hdn, ?_⟩
      intro m hm
      rw [Finset.mem_insert] at hm
      rcases hm with hm | hm
      · subst m
        refine ⟨s * bn, ?_⟩
        -- Multiply the old common denominator by the new coefficient denominator.
        calc
          algebraMap A1 K1 (s * bn) =
              algebraMap A1 K1 s * algebraMap A1 K1 bn := by
                simp
          _ = algebraMap A1 K1 s * (algebraMap A1 K1 dn * c n) := by
                rw [hbn]
          _ = (algebraMap A1 K1 s * algebraMap A1 K1 dn) * c n := by
                ring
          _ = algebraMap A1 K1 (s * dn) * c n := by
                simp [mul_assoc]
      · rcases hsupport m hm with ⟨b, hb⟩
        refine ⟨b * dn, ?_⟩
        -- Previously cleared coefficients absorb the new denominator by one extra factor.
        calc
          algebraMap A1 K1 (b * dn) =
              algebraMap A1 K1 b * algebraMap A1 K1 dn := by
                simp
          _ = (algebraMap A1 K1 s * c m) * algebraMap A1 K1 dn := by
                rw [hb]
          _ = (algebraMap A1 K1 s * algebraMap A1 K1 dn) * c m := by
                ring
          _ = algebraMap A1 K1 (s * dn) * c m := by
                simp [mul_assoc]

/-- Helper for Lemma 15.117.5: the supported coefficients of a `K₁`-polynomial admit one common
denominator in the source integral closure `A₁`. -/
private theorem source_polynomial_support_common_denominator
    (q : Polynomial K1) :
    ∃ s : A1, s ≠ 0 ∧
      ∀ n ∈ q.support, ∃ b : A1, algebraMap A1 K1 b = algebraMap A1 K1 s * q.coeff n := by
  -- Apply the finite-family denominator-clearing lemma to the coefficient function of `q`.
  simpa using
    (source_finite_common_denominator_for_family
      (A := A) (K := K) (K1 := K1) q.support q.coeff)

/-- Helper for Lemma 15.117.5: clearing the supported coefficients of a `K₁`-polynomial produces
an `A₁`-polynomial whose coefficient extension is `C(s) * q`. -/
private theorem exists_cleared_source_polynomial_map_eq
    (q : Polynomial K1) :
    ∃ s : A1, s ≠ 0 ∧ ∃ q₀ : Polynomial A1,
      Polynomial.map (algebraMap A1 K1) q₀ = C (algebraMap A1 K1 s) * q := by
  classical
  rcases source_polynomial_support_common_denominator (A := A) (K := K) (K1 := K1) q with
    ⟨s, hs, hsupport⟩
  choose b hb using hsupport
  let coeff₀ : ℕ → A1 := fun n ↦ if hn : n ∈ q.support then b n hn else 0
  let q₀ : Polynomial A1 := q.support.sum fun n ↦ Polynomial.monomial n (coeff₀ n)
  refine ⟨s, hs, q₀, ?_⟩
  -- Compare coefficients on and off the support of `q`.
  ext n
  rw [Polynomial.coeff_map, Polynomial.coeff_C_mul]
  by_cases hn : n ∈ q.support
  · have hq₀ : q₀.coeff n = coeff₀ n := by
      -- On the support only the `n`th monomial contributes to the `n`th coefficient.
      simp [q₀, Polynomial.coeff_monomial, hn]
    have hqn : q.coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
    have hcoeff₀ : coeff₀ n = b n hn := by
      simp [coeff₀, hqn]
    rw [hq₀, hcoeff₀, hb n hn]
  · have hq₀ : q₀.coeff n = 0 := by
      -- Off the support every monomial contributes zero to the `n`th coefficient.
      simp [q₀, Polynomial.coeff_monomial, hn]
    have hq : q.coeff n = 0 := by
      by_contra hq
      exact hn (Polynomial.mem_support_iff.mpr hq)
    rw [hq₀, hq]
    simp

/-- Helper for Lemma 15.117.5: after clearing coefficients over `A₁`, evaluating at the
normalized generator `β` gives the expected denominator-cleared equality in `K₂`. -/
private theorem source_aeval_map_algebraMap_clear_denominator
    (β : K2)
    {q : Polynomial K1} {s : A1} {q₀ : Polynomial A1}
    (hmap : Polynomial.map (algebraMap A1 K1) q₀ = C (algebraMap A1 K1 s) * q) :
    aeval β q₀ = algebraMap A1 K2 s * aeval β q := by
  -- Keep coefficient clearing separate from the scalar-tower transport `A₁ ⊆ K₁ ⊆ K₂`.
  calc
    aeval β q₀ = aeval β (Polynomial.map (algebraMap A1 K1) q₀) := by
      symm
      simpa using (Polynomial.aeval_map_algebraMap (R := A1) K1 β q₀)
    _ = aeval β (C (algebraMap A1 K1 s) * q) := by
      rw [hmap]
    _ = algebraMap A1 K2 s * aeval β q := by
      simp [IsScalarTower.algebraMap_eq A1 K1 K2]

/-- Helper for Lemma 15.117.5: every polynomial evaluation in the simple extension `K₂` can be
rewritten after clearing denominators in the source monogenic ring coefficients. -/
private theorem exists_cleared_source_polynomial_for_aeval
    (β : K2) (q : Polynomial K1) :
    ∃ s : A1, s ≠ 0 ∧ ∃ q₀ : Polynomial A1,
      aeval β q₀ = algebraMap A1 K2 s * aeval β q := by
  rcases exists_cleared_source_polynomial_map_eq (A := A) (K := K) (K1 := K1) q with
    ⟨s, hs, q₀, hmap⟩
  refine ⟨s, hs, q₀, ?_⟩
  -- Once the coefficient identity is fixed, the scalar-tower evaluation lemma finishes.
  exact
    source_aeval_map_algebraMap_clear_denominator
      (A := A) (K := K) (K1 := K1) (K2 := K2) β hmap

/-- Helper for Lemma 15.117.5: every element of `K₂` is a quotient of two elements of the source
monogenic ring `A₁[X] / (X^p - a₁')` under the canonical map to `K₂`. -/
private theorem exists_num_den_for_source_monogenic_element
    (β : K2) (a1' : A1)
    (hβpow : β ^ p = algebraMap A1 K2 a1')
    (hβtop : K1⟮β⟯ = ⊤)
    (z : K2) :
    ∃ r s : sourceMonogenicRing (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) a1',
      s ≠ 0 ∧
        sourceMonogenicToField
            (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) β a1' hβpow r =
          z *
            sourceMonogenicToField
              (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) β a1' hβpow s := by
  rcases source_generator_exists_polynomial_representation
      (K1 := K1) (K2 := K2) β hβtop z with ⟨q, hq⟩
  rcases exists_cleared_source_polynomial_for_aeval
      (A := A) (K := K) (K1 := K1) (K2 := K2) β q with
    ⟨s, hs, q₀, hclear⟩
  let r :
      sourceMonogenicRing (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) a1' :=
    aeval (AdjoinRoot.root (X ^ p - C a1' : Polynomial A1)) q₀
  let sR :
      sourceMonogenicRing (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) a1' :=
    algebraMap
      A1
      (sourceMonogenicRing (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) a1')
      s
  have hsK2 : algebraMap A1 K2 s ≠ 0 := by
    exact map_ne_zero (NoZeroSMulDivisors.algebraMap_injective A1 K2) hs
  have hsR : sR ≠ 0 := by
    intro hs0
    have hmap0 :
        sourceMonogenicToField
            (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) β a1' hβpow sR = 0 := by
      simpa using congrArg
        (sourceMonogenicToField
          (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) β a1' hβpow) hs0
    exact hsK2 <| by
      simpa [sR, sourceMonogenicToField] using hmap0
  refine ⟨r, sR, hsR, ?_⟩
  -- Evaluate the cleared polynomial numerator in the monogenic quotient, then transport it to
  -- `K₂` through the canonical `AdjoinRoot` map sending the root to `β`.
  calc
    sourceMonogenicToField
        (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) β a1' hβpow r =
      aeval β q₀ := by
        simpa [r, sourceMonogenicToField] using
          (Polynomial.aeval_algHom_apply
            (sourceMonogenicToField
              (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) β a1' hβpow)
            β q₀)
    _ = algebraMap A1 K2 s * aeval β q := hclear
    _ = algebraMap A1 K2 s * z := by
        rw [hq]
    _ = z * algebraMap A1 K2 s := by
        rw [mul_comm]
    _ =
      z *
        sourceMonogenicToField
          (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) β a1' hβpow sR := by
        simp [sR, sourceMonogenicToField]

/-- Helper for Lemma 15.117.5: the source and target integral-closure tower maps send the source
parameter `a₁'` to the same element of `B₂`. -/
private lemma source_to_target_tower_parameter_commutes
    (a1' : A1) :
    let _ : Algebra A1 A2 :=
      sourceIntegralClosureTowerMap
        (A := A) (K := K) (K1 := K1) (K2 := K2).toAlgebra
    reduced_tensor_integralClosure_tower_map
        (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2)
        (reducedTensorBaseChangeIntegralClosureMap
          (A := A) (B := B) (K := K) (L := L) (K1 := K1) a1') =
      reducedTensorBaseChangeIntegralClosureMap
        (A := A) (B := B) (K := K) (L := L) (K1 := K2)
        (sourceIntegralClosureTowerMap
          (A := A) (K := K) (K1 := K1) (K2 := K2) a1') := by
  let _ : Algebra A1 A2 :=
    sourceIntegralClosureTowerMap
      (A := A) (K := K) (K1 := K1) (K2 := K2).toAlgebra
  -- Compare both routes in the ambient reduced tensor field `L₂`; after unfolding the owner
  -- maps, both are induced by the same right tensor-factor inclusion `K₁ → K₂`.
  ext
  change
    reducedTensorQuotientTowerMap
        (((reducedTensorBaseChangeIntegralClosureMap
            (A := A) (B := B) (K := K) (L := L) (K1 := K1) a1' : B1) : L1)) =
      (((reducedTensorBaseChangeIntegralClosureMap
          (A := A) (B := B) (K := K) (L := L) (K1 := K2)
          (sourceIntegralClosureTowerMap
            (A := A) (K := K) (K1 := K1) (K2 := K2) a1') : B2) : L2))
  dsimp [reducedTensorBaseChangeIntegralClosureMap, sourceIntegralClosureTowerMap,
    reducedTensorQuotientTowerMap, reducedTensorTowerMapToQuotient, reducedTensorUnreducedTowerMap]
  rfl

/-- Helper for Lemma 15.117.5: the target monogenic ring for the normalized parameter is
`B₁[X] / (X ^ p - image(a₁'))`. -/
private noncomputable abbrev targetMonogenicRing (a1' : A1) :=
  AdjoinRoot
    (X ^ p -
      C
        (reducedTensorBaseChangeIntegralClosureMap
          (A := A) (B := B) (K := K) (L := L) (K1 := K1) a1') :
      Polynomial B1)

/-- Helper for Lemma 15.117.5: after transporting the normalized source generator into `B₂`,
its `p`th power is the image of the transported parameter from `B₁`. -/
private theorem target_pth_root_transport_in_reduced_tensor_integralClosure
    (β : K2) (a1' : A1)
    (hβpow : β ^ p = algebraMap A1 K2 a1') :
    let _ : Algebra A1 A2 :=
      sourceIntegralClosureTowerMap
        (A := A) (K := K) (K1 := K1) (K2 := K2).toAlgebra
    let _ : Algebra B1 B2 :=
      reduced_tensor_integralClosure_tower_map
        (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2).toAlgebra
    let βA2 : A2 :=
      ⟨β,
        source_generator_isIntegral_over_base
          (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) β a1' hβpow⟩
    let βB2 : B2 :=
      reducedTensorBaseChangeIntegralClosureMap
        (A := A) (B := B) (K := K) (L := L) (K1 := K2) βA2
    βB2 ^ p =
      algebraMap B1 B2
        (reducedTensorBaseChangeIntegralClosureMap
          (A := A) (B := B) (K := K) (L := L) (K1 := K1) a1') := by
  let _ : Algebra A1 A2 :=
    sourceIntegralClosureTowerMap
      (A := A) (K := K) (K1 := K1) (K2 := K2).toAlgebra
  let _ : Algebra B1 B2 :=
    reduced_tensor_integralClosure_tower_map
      (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2).toAlgebra
  let βA2 : A2 :=
    ⟨β,
      source_generator_isIntegral_over_base
        (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) β a1' hβpow⟩
  let βB2 : B2 :=
    reducedTensorBaseChangeIntegralClosureMap
      (A := A) (B := B) (K := K) (L := L) (K1 := K2) βA2
  have hβA2pow : βA2 ^ p = algebraMap A1 A2 a1' := by
    -- The source `p`th-power equation survives unchanged inside the source integral closure.
    ext
    change β ^ p = algebraMap A1 K2 a1'
    exact hβpow
  have hβB2pow :
      βB2 ^ p =
        reducedTensorBaseChangeIntegralClosureMap
          (A := A) (B := B) (K := K) (L := L) (K1 := K2) (algebraMap A1 A2 a1') := by
    -- Apply the canonical target map to the source relation and use multiplicativity.
    simpa [βB2, map_pow] using
      congrArg
        (fun x : A2 ↦
          reducedTensorBaseChangeIntegralClosureMap
            (A := A) (B := B) (K := K) (L := L) (K1 := K2) x)
        hβA2pow
  have htransport :
      reducedTensorBaseChangeIntegralClosureMap
          (A := A) (B := B) (K := K) (L := L) (K1 := K2) (algebraMap A1 A2 a1') =
        algebraMap B1 B2
          (reducedTensorBaseChangeIntegralClosureMap
            (A := A) (B := B) (K := K) (L := L) (K1 := K1) a1') := by
    -- The two routes for transporting the parameter agree by the canonical tower square.
    simpa using
      (source_to_target_tower_parameter_commutes
        (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2) a1').symm
  exact hβB2pow.trans htransport

/-- Helper for Lemma 15.117.5: the image of the normalized source generator in `B₂` satisfies
the target monogenic equation. -/
private theorem target_generator_aeval_eq_zero
    (β : K2) (a1' : A1)
    (hβpow : β ^ p = algebraMap A1 K2 a1') :
    let _ : Algebra A1 A2 :=
      sourceIntegralClosureTowerMap
        (A := A) (K := K) (K1 := K1) (K2 := K2).toAlgebra
    let _ : Algebra B1 B2 :=
      reduced_tensor_integralClosure_tower_map
        (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2).toAlgebra
    let βA2 : A2 :=
      ⟨β,
        source_generator_isIntegral_over_base
          (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) β a1' hβpow⟩
    let βB2 : B2 :=
      reducedTensorBaseChangeIntegralClosureMap
        (A := A) (B := B) (K := K) (L := L) (K1 := K2) βA2
    aeval βB2
      (X ^ p -
        C
          (reducedTensorBaseChangeIntegralClosureMap
            (A := A) (B := B) (K := K) (L := L) (K1 := K1) a1') :
        Polynomial B1) = 0 := by
  let _ : Algebra A1 A2 :=
    sourceIntegralClosureTowerMap
      (A := A) (K := K) (K1 := K1) (K2 := K2).toAlgebra
  let _ : Algebra B1 B2 :=
    reduced_tensor_integralClosure_tower_map
      (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2).toAlgebra
  let βA2 : A2 :=
    ⟨β,
      source_generator_isIntegral_over_base
        (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) β a1' hβpow⟩
  let βB2 : B2 :=
    reducedTensorBaseChangeIntegralClosureMap
      (A := A) (B := B) (K := K) (L := L) (K1 := K2) βA2
  have hβB2pow :
      βB2 ^ p =
        algebraMap B1 B2
          (reducedTensorBaseChangeIntegralClosureMap
            (A := A) (B := B) (K := K) (L := L) (K1 := K1) a1') := by
    -- Route correction: isolate the target-side transported `p`th-power identity before the
    -- final `aeval` expansion so the target owner map is available in exactly the needed shape.
    exact
      target_pth_root_transport_in_reduced_tensor_integralClosure
        (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2) (p := p)
        β a1' hβpow
  -- Expanding `aeval` now reduces the target claim to the transported `p`th-power relation.
  rw [Polynomial.aeval_def, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  exact sub_eq_zero.mpr hβB2pow

-- After transporting the target `p`th-root equation, the owner map `B₂' → B₂` is the canonical
-- `AdjoinRoot` lift.
/-- Helper for Lemma 15.117.5: the target monogenic ring maps to `B₂` by sending the
distinguished root to the image of the normalized source generator. -/
private noncomputable def targetMonogenicToIntegralClosure
    (β : K2) (a1' : A1)
    (hβpow : β ^ p = algebraMap A1 K2 a1') :
    targetMonogenicRing
        (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2) (p := p) a1' →ₐ[B1] B2 :=
  let _ : Algebra A1 A2 :=
    sourceIntegralClosureTowerMap
      (A := A) (K := K) (K1 := K1) (K2 := K2).toAlgebra
  let _ : Algebra B1 B2 :=
    reduced_tensor_integralClosure_tower_map
      (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2).toAlgebra
  let βA2 : A2 :=
    ⟨β,
      source_generator_isIntegral_over_base
        (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) β a1' hβpow⟩
  let βB2 : B2 :=
    reducedTensorBaseChangeIntegralClosureMap
      (A := A) (B := B) (K := K) (L := L) (K1 := K2) βA2
  -- Once the target polynomial is known to vanish at the transported generator, `AdjoinRoot`
  -- supplies the canonical owner map.
  AdjoinRoot.liftAlgHom
    (X ^ p -
      C
        (reducedTensorBaseChangeIntegralClosureMap
          (A := A) (B := B) (K := K) (L := L) (K1 := K1) a1') : Polynomial B1)
    (Algebra.ofId B1 B2)
    βB2
    (target_generator_aeval_eq_zero
      (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2) (p := p)
      β a1' hβpow)

/-- Helper for Lemma 15.117.5: after installing the target monogenic algebra structure on `B₂`,
the canonical target map is definitionally the ambient algebra map. -/
private theorem targetMonogenicToIntegralClosure_eq_algebraMap
    (β : K2) (a1' : A1)
    (hβpow : β ^ p = algebraMap A1 K2 a1') :
    let φB :=
      targetMonogenicToIntegralClosure
        (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2) (p := p)
        β a1' hβpow
    let _ : Algebra
        (targetMonogenicRing
          (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2) (p := p) a1')
        B2 :=
      φB.toAlgebra
    φB.toRingHom =
      algebraMap
        (targetMonogenicRing
          (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2) (p := p) a1')
        B2 := by
  rfl

-- Proof sketch: start from the given solution over the purely inseparable degree-`p` extension
-- `K₂ / K₁`, use the Nagata and separability hypotheses to compare the integral closures after
-- base change, and then perform the Artin-Schreier deformation argument from the textbook to
-- replace the radicial extension by a finite separable extension `K₃ / K₁` while preserving the
-- solution property for `A ⊂ B`.
/-- Lemma 15.117.5: let `A ⊂ B` be an extension of discrete valuation rings with fraction fields
`K ⊂ L`, let `K₂ / K₁ / K` be a tower of finite field extensions, and assume `L / K` is
separable, `B` is Nagata, `p` is prime, `K₂ / K₁` is purely inseparable of degree `p`, and
`K₂ / K` is a solution for `A ⊂ B`. Then there exists a finite separable extension `K₃ / K₁`
such that
`K₃ / K` is again a solution for `A ⊂ B` in the sense of Definition `15.116.1`. -/
theorem exists_separable_solution_of_solution_of_purelyInseparable_degree_eq_prime
    (hK2 : IsSolutionFor A B K L K2)
    (hdeg : Module.finrank K1 K2 = p) :
    ∃ (K3 : Type (max u v w x y z)) (_ : Field K3) (_ : Algebra A K3) (_ : Algebra K K3)
      (_ : IsScalarTower A K K3) (_ : Algebra K1 K3) (_ : IsScalarTower K K1 K3)
      (_ : FiniteDimensional K1 K3) (_ : Algebra.IsSeparable K1 K3),
      IsSolutionFor A B K L K3 := by
  obtain ⟨β, a1', hβpow, hβtop⟩ :=
    rescaled_pth_root_parameter_mem_source_integralClosure
      (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) hdeg
  have hK2_not_sep : ¬ Algebra.IsSeparable K1 K2 := by
    -- The source degree-`p` purely inseparable extension is the nonseparable branch of the proof.
    exact
      not_isSeparable_of_purelyInseparable_prime_finrank
        (F := K1) (E := K2) (show IsPurelyInseparable K1 K2 from inferInstance) hdeg
  -- Route correction: the field-theoretic normalization is now complete in the exact source
  -- shape. The purely inseparable step is now normalized by a generator `β` whose `p`th power
  -- already lies in `integralClosure A K₁`, which is the first exact input for the source
  -- deformation square.
  let _ := β
  let _ := a1'
  let _ := hβpow
  let _ := hβtop
  have hA_nagata : NagataRing A :=
    nagataRing_of_separable_fractionRingExtension (A := A) (B := B)
  letI : NagataRing A := hA_nagata
  let A2' :=
    sourceMonogenicRing (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) a1'
  let φA : A2' →ₐ[A1] A2 :=
    sourceMonogenicToIntegralClosure
      (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) β a1' hβpow
  let B2' :=
    targetMonogenicRing
      (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2) (p := p) a1'
  let φB : B2' →ₐ[B1] B2 :=
    targetMonogenicToIntegralClosure
      (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2) (p := p)
      β a1' hβpow
  let _ : Algebra A2' A2 := φA.toAlgebra
  let _ : Algebra B2' B2 := φB.toAlgebra
  have hφA_eq :
      φA.toRingHom = algebraMap A2' A2 := by
    simpa [A2', φA] using
      (sourceMonogenicToIntegralClosure_eq_algebraMap
        (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p) β a1' hβpow)
  have hφB_eq :
      φB.toRingHom = algebraMap B2' B2 := by
    simpa [B2', φB] using
      (targetMonogenicToIntegralClosure_eq_algebraMap
        (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2) (p := p)
        β a1' hβpow)
  let _ := hφA_eq
  let _ := hφB_eq
  obtain ⟨π, hπirr, hπ_uniformizer⟩ := exists_uniformizer_generator A
  let π1 : A1 := algebraMap A A1 π
  have hπ1_ne : π1 ≠ 0 := by
    -- The chosen source uniformizer stays nonzero in the first integral closure.
    exact
      map_ne_zero (NoZeroSMulDivisors.algebraMap_injective A A1) hπirr.ne_zero
  have hsource_nonZeroDiv :
      algebraMap A2' A2 (algebraMap A1 A2' (π1 ^ 2)) ∈ nonZeroDivisors A2 := by
    -- The source denominator surface for Remark `15.117.4` already satisfies the
    -- nonzerodivisor hypothesis on the lower integral-closure row.
    simpa [A2', φA, π1] using
      (sourceMonogenic_square_mem_nonZeroDivisors
        (A := A) (K := K) (K1 := K1) (K2 := K2) (p := p)
        β a1' hβpow π1 hπ1_ne)
  let _ := hπ_uniformizer
  let _ := hsource_nonZeroDiv
  -- TODO: the source monogenic quotient now has the numerator/denominator API needed to compare
  -- it with the generic fiber `K₂`, but the remaining source-faithful blocker is to turn that
  -- arbitrary denominator clearing into the exact localization-away-`π²` comparison required by
  -- Remark `15.117.4`. The source nonzerodivisor input is now closed; the remaining structural
  -- gap is the exact away-bijective/injective package for `A₂' → A₂`, together with the
  -- matching target-side bridge for `B₂' → B₂`.
  -- After those two away-comparison packages are in place, the final deformation square and the
  -- branchwise transfer of `IsSolutionFor` across Lemma `15.112.5` should follow the textbook
  -- route.
  sorry

end
