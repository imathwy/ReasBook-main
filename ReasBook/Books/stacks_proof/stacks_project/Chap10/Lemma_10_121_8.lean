import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_113_2
import stacks_proof.stacks_project.Chap10.Lemma_10_119_10
import stacks_proof.stacks_project.Chap10.Lemma_10_52_7
import stacks_proof.stacks_project.Chap10.Lemma_10_52_12
import stacks_proof.stacks_project.Chap10.Lemma_10_121_4
import stacks_proof.stacks_project.Chap10.Lemma_10_121_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators nonZeroDivisors
open IsLocalRing

noncomputable section

universe u v w w'

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section InjectiveAlgebraMapFact

variable (A : Type u) {B : Type v}
variable [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
variable [Algebra (FractionRing A) (FractionRing B)]
variable [IsScalarTower A (FractionRing A) (FractionRing B)]

local instance injectiveAlgebraMapFact_of_finiteFractionRingExtension :
    Fact (Function.Injective (algebraMap A B)) :=
  ⟨algebraMap_injective_of_field_isFractionRing A B (FractionRing A) (FractionRing B)⟩

section

variable (A : Type u) {B : Type v}
variable [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
variable [Algebra (FractionRing A) (FractionRing B)]
variable [IsScalarTower A (FractionRing A) (FractionRing B)]

omit [IsDomain B] [Algebra A B] [IsScalarTower A (FractionRing A) (FractionRing B)] in
/-- Helper for Chap10 Lemma 10 121 8: a finite-dimensional extension of fraction fields has
zero transcendence degree in the natural-number term used by the dimension inequality. -/
private theorem fractionRingTrdeg_toNat_eq_zero_of_finiteDimensional
    [FiniteDimensional (FractionRing A) (FractionRing B)] :
    Cardinal.toNat (Algebra.trdeg (FractionRing A) (FractionRing B)) = 0 := by
  -- Finite-dimensional field extensions are algebraic, hence their transcendence degree vanishes.
  simpa using
    congrArg Cardinal.toNat
      (show Algebra.trdeg (FractionRing A) (FractionRing B) = 0 by
        simpa using (trdeg_eq_zero (R := FractionRing A) (A := FractionRing B)))

/-- Helper for Chap10 Lemma 10 121 8: in the generic fiber of a finite-type algebra with finite
fraction-field extension, a prime ideal of the target domain is the generic point. -/
private theorem eq_bot_of_prime_comap_bot_of_finiteType_of_finiteFractionRingExtension
    [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType A B]
    [FiniteDimensional (FractionRing A) (FractionRing B)]
    (q : Ideal B) [q.IsPrime]
    (hm : Ideal.comap (algebraMap A B) q = ⊥) :
    q = ⊥ := by
  -- The dimension inequality bounds the target height by the zero generic-fiber transcendence term.
  have hinj : Function.Injective (algebraMap A B) :=
    algebraMap_injective_of_field_isFractionRing A B (FractionRing A) (FractionRing B)
  have hq : q.LiesOver (⊥ : Ideal A) := ⟨hm.symm⟩
  have hbound :
      ENat.toNat (Ideal.primeHeight q) +
          Cardinal.toNat (Algebra.trdeg (⊥ : Ideal A).ResidueField q.ResidueField) ≤
        ENat.toNat (Ideal.primeHeight (⊥ : Ideal A)) +
          Cardinal.toNat (Algebra.trdeg (FractionRing A) (FractionRing B)) :=
    primeHeight_add_residueFieldTrdeg_le_primeHeight_add_fractionRing_trdeg_of_finiteType
      (R := A) (S := B) hinj (⊥ : Ideal A) q hq
  have hbot_height : Ideal.primeHeight (⊥ : Ideal A) = 0 := by
    rw [Ideal.primeHeight_eq_zero_iff]
    simp [IsDomain.minimalPrimes_eq_singleton_bot A]
  have hgeneric :
      Cardinal.toNat (Algebra.trdeg (FractionRing A) (FractionRing B)) = 0 :=
    fractionRingTrdeg_toNat_eq_zero_of_finiteDimensional (A := A) (B := B)
  have hbound_zero :
      ENat.toNat (Ideal.primeHeight q) +
          Cardinal.toNat (Algebra.trdeg (⊥ : Ideal A).ResidueField q.ResidueField) ≤ 0 := by
    simpa [hbot_height, hgeneric] using hbound
  have hheight_toNat : ENat.toNat (Ideal.primeHeight q) = 0 := by
    -- The residue transcendence term is nonnegative, so the only way the sum is at most zero is
    -- for the height term itself to be zero.
    omega
  have hheight_zero : Ideal.primeHeight q = 0 := by
    -- Noetherianity of the finite-type target lets `toNat` reflect the actual `ℕ∞` height.
    letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
    have hfinite : Ideal.primeHeight q ≠ ⊤ := Ideal.primeHeight_ne_top q
    rw [← ENat.coe_toNat hfinite]
    exact_mod_cast hheight_toNat
  have hmin : q ∈ minimalPrimes B := Ideal.primeHeight_eq_zero_iff.mp hheight_zero
  -- A domain has only the generic minimal prime.
  simpa [IsDomain.minimalPrimes_eq_singleton_bot B] using hmin

omit [IsDomain B] [Algebra (FractionRing A) (FractionRing B)]
  [IsScalarTower A (FractionRing A) (FractionRing B)] in
/-- Helper for Chap10 Lemma 10 121 8: a non-generic maximal ideal of the target lies over the
closed point of the local base. -/
private theorem exists_primesOver_maximalIdeal_of_maximalSpectrum_comap_ne_bot
    [IsLocalRing A] [Ring.KrullDimLE 1 A]
    (m : MaximalSpectrum B)
    (hm : Ideal.comap (algebraMap A B) m.asIdeal ≠ ⊥) :
    ∃ P : (maximalIdeal A).primesOver B, P.1 = m.asIdeal := by
  -- In a one-dimensional local domain, every nonzero prime contraction is the closed point.
  let p : Ideal A := Ideal.comap (algebraMap A B) m.asIdeal
  have hpPrime : p.IsPrime := Ideal.comap_isPrime (algebraMap A B) m.asIdeal
  have hpMax : p.IsMaximal :=
    (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp inferInstance) p hm hpPrime
  have hover : maximalIdeal A = Ideal.comap (algebraMap A B) m.asIdeal := by
    simpa [p] using (IsLocalRing.eq_maximalIdeal hpMax).symm
  letI : m.asIdeal.LiesOver (maximalIdeal A) := ⟨hover⟩
  exact ⟨Ideal.primesOver.mk (maximalIdeal A) m.asIdeal, rfl⟩

/-- Helper for Chap10 Lemma 10 121 8: the closed fiber over the maximal ideal of the local base is
finite under the finite-type and finite fraction-field extension hypotheses. -/
private theorem finite_primesOver_maximalIdeal_of_krullDimLE_one_finiteFractionRingExtension
    [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType A B]
    [FiniteDimensional (FractionRing A) (FractionRing B)] :
    Finite ((maximalIdeal A).primesOver B) := by
  -- If the base is a field, the closed point is generic and the generic-fiber uniqueness helper
  -- makes the fiber a subsingleton. Otherwise the base has Krull dimension exactly one, so the
  -- closed-fiber theorem from Lemma 10.119.10 applies.
  by_cases hfield : IsField A
  · have hmax_bot : maximalIdeal A = (⊥ : Ideal A) :=
      IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
    refine Finite.of_injective (fun _ : (maximalIdeal A).primesOver B ↦ PUnit.unit) ?_
    intro P Q _
    apply Subtype.ext
    have hPcomap : Ideal.comap (algebraMap A B) P.1 = ⊥ := by
      have hover : maximalIdeal A = Ideal.comap (algebraMap A B) P.1 := P.2.2.over
      simpa [hmax_bot] using hover.symm
    have hQcomap : Ideal.comap (algebraMap A B) Q.1 = ⊥ := by
      have hover : maximalIdeal A = Ideal.comap (algebraMap A B) Q.1 := Q.2.2.over
      simpa [hmax_bot] using hover.symm
    have hPbot :
        P.1 = ⊥ :=
      eq_bot_of_prime_comap_bot_of_finiteType_of_finiteFractionRingExtension
        (A := A) (B := B) P.1 hPcomap
    have hQbot :
        Q.1 = ⊥ :=
      eq_bot_of_prime_comap_bot_of_finiteType_of_finiteFractionRingExtension
        (A := A) (B := B) Q.1 hQcomap
    rw [hPbot, hQbot]
  · have hdim : ringKrullDim A = 1 := by
      have hnot_dim0 : ¬ ringKrullDim A ≤ 0 := fun hdim0 ↦ by
        have hkrull0 : Ring.KrullDimLE 0 A := Ring.krullDimLE_iff.mpr hdim0
        exact hfield Ring.KrullDimLE.isField_of_isDomain
      have hle : ringKrullDim A ≤ 1 := Ring.krullDimLE_iff.mp inferInstance
      exact le_antisymm hle (Order.succ_le_of_lt (lt_of_not_ge hnot_dim0))
    exact finite_primesOver_maximalIdeal_of_finite_fractionField_extension (R := A) (S := B) hdim

/-- Under a finite-type extension of domains with finite fraction-field extension from a
Noetherian local domain of Krull dimension at most `1`, the target ring has finite maximal
spectrum. -/
theorem finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension
    [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType A B]
    [FiniteDimensional (FractionRing A) (FractionRing B)] :
    Finite (MaximalSpectrum B) := by
  -- Send a maximal ideal either to the closed fiber or to the unique generic point.
  classical
  letI : Finite ((maximalIdeal A).primesOver B) :=
    finite_primesOver_maximalIdeal_of_krullDimLE_one_finiteFractionRingExtension (A := A) (B := B)
  let f : MaximalSpectrum B → Option ((maximalIdeal A).primesOver B) := fun m ↦
    if h : Ideal.comap (algebraMap A B) m.asIdeal = ⊥ then
      none
    else
      some (Classical.choose
        (exists_primesOver_maximalIdeal_of_maximalSpectrum_comap_ne_bot (A := A) (B := B) m h))
  have hf : Function.Injective f := by
    intro m n hmn
    dsimp [f] at hmn
    by_cases hm : Ideal.comap (algebraMap A B) m.asIdeal = ⊥
    · by_cases hn : Ideal.comap (algebraMap A B) n.asIdeal = ⊥
      · apply MaximalSpectrum.ext
        have hmbot :
            m.asIdeal = ⊥ :=
          eq_bot_of_prime_comap_bot_of_finiteType_of_finiteFractionRingExtension
            (A := A) (B := B) m.asIdeal hm
        have hnbot :
            n.asIdeal = ⊥ :=
          eq_bot_of_prime_comap_bot_of_finiteType_of_finiteFractionRingExtension
            (A := A) (B := B) n.asIdeal hn
        rw [hmbot, hnbot]
      · have hnone_some : (none : Option ((maximalIdeal A).primesOver B)) =
            some (Classical.choose
              (exists_primesOver_maximalIdeal_of_maximalSpectrum_comap_ne_bot
                (A := A) (B := B) n hn)) := by
          simpa [hm, hn] using hmn
        cases hnone_some
    · by_cases hn : Ideal.comap (algebraMap A B) n.asIdeal = ⊥
      · have hsome_none :
            some (Classical.choose
              (exists_primesOver_maximalIdeal_of_maximalSpectrum_comap_ne_bot
                (A := A) (B := B) m hm)) =
              (none : Option ((maximalIdeal A).primesOver B)) := by
          simpa [hm, hn] using hmn
        cases hsome_none
      · apply MaximalSpectrum.ext
        have hm_spec :
            (Classical.choose
              (exists_primesOver_maximalIdeal_of_maximalSpectrum_comap_ne_bot
                (A := A) (B := B) m hm)).1 = m.asIdeal :=
          Classical.choose_spec
            (exists_primesOver_maximalIdeal_of_maximalSpectrum_comap_ne_bot
              (A := A) (B := B) m hm)
        have hn_spec :
            (Classical.choose
              (exists_primesOver_maximalIdeal_of_maximalSpectrum_comap_ne_bot
                (A := A) (B := B) n hn)).1 = n.asIdeal :=
          Classical.choose_spec
            (exists_primesOver_maximalIdeal_of_maximalSpectrum_comap_ne_bot
              (A := A) (B := B) n hn)
        have hchoose :
            Classical.choose
                (exists_primesOver_maximalIdeal_of_maximalSpectrum_comap_ne_bot
                  (A := A) (B := B) m hm) =
              Classical.choose
                (exists_primesOver_maximalIdeal_of_maximalSpectrum_comap_ne_bot
                  (A := A) (B := B) n hn) := by
          simpa [hm, hn] using hmn
        rw [← hm_spec, ← hn_spec]
        exact congrArg (fun P : (maximalIdeal A).primesOver B => P.1) hchoose
  exact Finite.of_injective f hf

end

section

variable (A : Type u) {B : Type v}
variable [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
variable [IsLocalRing A]
variable [Algebra (FractionRing A) (FractionRing B)]
variable [IsScalarTower A (FractionRing A) (FractionRing B)]

omit [IsDomain A] [IsDomain B] [Algebra (FractionRing A) (FractionRing B)]
  [IsScalarTower A (FractionRing A) (FractionRing B)] in
/-- Helper for Chap10 Lemma 10 121 8: every maximal ideal of a module-finite algebra lies over the
maximal ideal of the local base ring. -/
theorem comap_maximalIdeal_of_moduleFinite
    [Module.Finite A B]
    (m : MaximalSpectrum B) :
    Ideal.comap (algebraMap A B) m.asIdeal = maximalIdeal A := by
  -- Module-finiteness gives integrality, so maximal ideals contract to maximal ideals.
  letI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have hmax : (Ideal.comap (algebraMap A B) m.asIdeal).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m.asIdeal
  -- The base ring is local, hence its only maximal ideal is `maximalIdeal A`.
  exact (IsLocalRing.isMaximal_iff A).mp hmax

omit [IsDomain A] [IsDomain B] [Algebra (FractionRing A) (FractionRing B)]
  [IsScalarTower A (FractionRing A) (FractionRing B)] in
/-- Helper for Chap10 Lemma 10 121 8: the closed point contraction gives a `LiesOver` instance for
each maximal ideal of a module-finite algebra over a local ring. -/
theorem maximalIdeal_liesOver_of_moduleFinite
    [Module.Finite A B]
    (m : MaximalSpectrum B) :
    m.asIdeal.LiesOver (maximalIdeal A) := by
  -- Package the already-proved contraction equality in the canonical `LiesOver` form.
  have hover :
      maximalIdeal A = Ideal.comap (algebraMap A B) m.asIdeal := by
    simpa [Ideal.under_def] using (comap_maximalIdeal_of_moduleFinite A m).symm
  exact ⟨hover⟩

omit [IsDomain A] [IsDomain B] [Algebra (FractionRing A) (FractionRing B)]
  [IsScalarTower A (FractionRing A) (FractionRing B)] in
/-- Helper for Chap10 Lemma 10 121 8: a module-finite algebra over a local ring has only finitely
many maximal ideals. -/
theorem finite_maximalSpectrum_of_moduleFinite [Module.Finite A B] :
    Finite (MaximalSpectrum B) := by
  -- A finite algebra is quasi-finite, so the finite fiber over the unique closed point controls all
  -- maximal ideals of `B`.
  letI : Algebra.QuasiFinite A B := inferInstance
  letI : Fintype ((maximalIdeal A).primesOver B) :=
    Set.Finite.fintype
      (Algebra.QuasiFinite.finite_primesOver (R := A) (S := B) (maximalIdeal A))
  let f : MaximalSpectrum B → (maximalIdeal A).primesOver B := fun m ↦
    letI : m.asIdeal.LiesOver (maximalIdeal A) := maximalIdeal_liesOver_of_moduleFinite A m
    Ideal.primesOver.mk (maximalIdeal A) m.asIdeal
  have hf : Function.Injective f := by
    intro m n hmn
    apply MaximalSpectrum.ext
    exact congrArg (fun P : (maximalIdeal A).primesOver B => P.1) hmn
  exact Finite.of_injective f hf

local notation "κA" => Ideal.ResidueField (maximalIdeal A)

/-- Helper for Chap10 Lemma 10 121 8: the residue-field map induced by a module-finite local-base
algebra. -/
instance residueFieldAlgebra_of_moduleFinite
    [Module.Finite A B]
    (m : MaximalSpectrum B) :
    Algebra κA (Ideal.ResidueField m.asIdeal) :=
  (Ideal.ResidueField.map (maximalIdeal A) m.asIdeal (algebraMap A B)
    (comap_maximalIdeal_of_moduleFinite A m).symm).toAlgebra

omit [IsDomain A] [IsDomain B] [Algebra (FractionRing A) (FractionRing B)]
  [IsScalarTower A (FractionRing A) (FractionRing B)] in
/-- Helper for Chap10 Lemma 10 121 8: the residue field at a maximal ideal of a module-finite
algebra is finite over the residue field of the local base. -/
theorem moduleFinite_residueField_of_moduleFinite
    [Module.Finite A B]
    (m : MaximalSpectrum B) :
    Module.Finite κA (Ideal.ResidueField m.asIdeal) := by
  letI : Algebra κA (Ideal.ResidueField m.asIdeal) := residueFieldAlgebra_of_moduleFinite A m
  have hquot : Module.Finite A (B ⧸ m.asIdeal) :=
    Module.Finite.quotient A m.asIdeal
  let eResidue : (B ⧸ m.asIdeal) ≃ₐ[B ⧸ m.asIdeal] m.asIdeal.ResidueField :=
    AlgEquiv.ofBijective
      (Algebra.ofId (B ⧸ m.asIdeal) m.asIdeal.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField m.asIdeal)
  have hfiniteResidue : Module.Finite A m.asIdeal.ResidueField := by
    -- The quotient by `m` is finite over `A`, and it is linearly equivalent to the residue field.
    letI : Module.Finite A (B ⧸ m.asIdeal) := hquot
    exact Module.Finite.equiv (eResidue.toLinearEquiv.restrictScalars A)
  letI : Module.Finite A m.asIdeal.ResidueField := hfiniteResidue
  letI : Algebra.IsIntegral A m.asIdeal.ResidueField :=
    Algebra.IsIntegral.of_finite A m.asIdeal.ResidueField
  have hfiniteOverLocalResidue :
      Module.Finite (IsLocalRing.ResidueField A) m.asIdeal.ResidueField := by
    -- Since the `A`-action on the residue field is integral and has maximal kernel, it descends to
    -- finite generation over the local residue field model.
    letI : Algebra (IsLocalRing.ResidueField A) m.asIdeal.ResidueField :=
      IsLocalRing.ResidueField.algebraOfIsIntegral (R := A) (k := m.asIdeal.ResidueField)
    letI : IsScalarTower A (IsLocalRing.ResidueField A) m.asIdeal.ResidueField :=
      IsLocalRing.ResidueField.isScalarTowerOfIsIntegral
        (R := A) (k := m.asIdeal.ResidueField)
    have hcomap :
        Ideal.comap (algebraMap A m.asIdeal.ResidueField) (⊥ : Ideal m.asIdeal.ResidueField) =
          maximalIdeal A := by
      simpa [RingHom.ker] using
        (eq_maximalIdeal
          (Algebra.ker_algebraMap_isMaximal_of_isIntegral A m.asIdeal.ResidueField))
    refine Module.Finite.of_equiv_equiv
      (Ideal.quotEquivOfEq hcomap)
      (RingEquiv.quotientBot m.asIdeal.ResidueField) ?_
    ext
    rfl
  letI : Module.Finite (IsLocalRing.ResidueField A) m.asIdeal.ResidueField :=
    hfiniteOverLocalResidue
  let eBase : (IsLocalRing.ResidueField A) ≃+* κA :=
    RingEquiv.ofBijective
      (algebraMap (IsLocalRing.ResidueField A) κA)
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))
  have hcompat :
      RingHom.comp (algebraMap κA m.asIdeal.ResidueField) ↑eBase =
        RingHom.comp (RingEquiv.refl m.asIdeal.ResidueField)
          (algebraMap (IsLocalRing.ResidueField A) m.asIdeal.ResidueField) := by
    -- Both presentations send the residue class of `a : A` to its image in `κ(m)`.
    ext x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := A) x
    change algebraMap κA m.asIdeal.ResidueField (algebraMap A κA a) =
      algebraMap A m.asIdeal.ResidueField a
    exact Ideal.ResidueField.map_algebraMap (maximalIdeal A) m.asIdeal (algebraMap A B)
      (comap_maximalIdeal_of_moduleFinite A m).symm a
  exact Module.Finite.of_equiv_equiv eBase (RingEquiv.refl m.asIdeal.ResidueField) hcompat

/-- Helper for Chap10 Lemma 10 121 8: residue-field finiteness as a local instance for
module-finite algebras. -/
instance residueFieldModuleFinite_of_moduleFinite
    [Module.Finite A B]
    (m : MaximalSpectrum B) :
    Module.Finite κA (Ideal.ResidueField m.asIdeal) :=
  moduleFinite_residueField_of_moduleFinite A m

end

section

variable (A : Type u) {B : Type v}
variable [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
variable [Algebra (FractionRing A) (FractionRing B)]
variable [IsScalarTower A (FractionRing A) (FractionRing B)]

private theorem isScalarTower_fractionRing_localization_fractionRing [Module.Finite A B] :
    let K := FractionRing A
    let L := FractionRing B
    let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors A)
    let S := Localization M
    let _ : FaithfulSMul A B :=
      (faithfulSMul_iff_algebraMap_injective A B).mpr
        (algebraMap_injective_of_field_isFractionRing A B K L)
    let hS : M ≤ B⁰ :=
      algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul B
        (show nonZeroDivisors A ≤ A⁰ by rfl)
    let hS' : M ≤ Submonoid.comap (RingHom.id B) B⁰ := by
      simpa using hS
    let f : S →+* L := IsLocalization.map L (RingHom.id B) hS'
    let _ : Algebra S L := f.toAlgebra
    IsScalarTower K S L := by
  simp only
  let K := FractionRing A
  let L := FractionRing B
  let _ : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr
      (algebraMap_injective_of_field_isFractionRing A B K L)
  let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors A)
  let S := Localization M
  have hS : M ≤ B⁰ :=
    algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul B (show nonZeroDivisors A ≤ A⁰ by rfl)
  have hS' : M ≤ Submonoid.comap (RingHom.id B) B⁰ := by
    simpa using hS
  let f : S →+* L := IsLocalization.map L (RingHom.id B) hS'
  let _ : Algebra S L := f.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  apply IsLocalization.ringHom_ext (nonZeroDivisors A)
  ext a
  have h1 : (algebraMap K L) ((algebraMap A K) a) = algebraMap A L a :=
    (IsScalarTower.algebraMap_apply A K L a).symm
  have h2 : (((algebraMap S L).comp (algebraMap K S)).comp (algebraMap A K)) a =
      algebraMap A L a := by
    rw [RingHom.comp_apply, RingHom.comp_apply, (IsScalarTower.algebraMap_apply A K S a).symm]
    have hABS : algebraMap A S a = algebraMap B S (algebraMap A B a) :=
      IsScalarTower.algebraMap_apply A B S a
    rw [hABS]
    have hmap : f (algebraMap B S (algebraMap A B a)) = algebraMap B L (algebraMap A B a) := by
      simpa [f] using (IsLocalization.map_eq hS' (algebraMap A B a) : _)
    simpa [IsScalarTower.algebraMap_apply A B L] using hmap
  exact h1.trans h2.symm

private theorem finiteDimensional_fractionRing_of_moduleFinite [Module.Finite A B] :
    FiniteDimensional (FractionRing A) (FractionRing B) := by
  let K := FractionRing A
  let L := FractionRing B
  let _ : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr
      (algebraMap_injective_of_field_isFractionRing A B K L)
  let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors A)
  let S := Localization M
  have hS : M ≤ B⁰ :=
    algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul B (show nonZeroDivisors A ≤ A⁰ by rfl)
  have hS' : M ≤ Submonoid.comap (RingHom.id B) B⁰ := by
    simpa using hS
  let f : S →+* L := IsLocalization.map L (RingHom.id B) hS'
  letI algKS : Algebra K S := localizationAlgebra (nonZeroDivisors A) B
  letI : Module K S := @Algebra.toModule K S _ _ algKS
  letI : Algebra S L := f.toAlgebra
  letI : Module S L := Algebra.toModule
  letI : IsScalarTower B S L := IsScalarTower.of_algebraMap_eq' (by
    rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp hS', RingHomCompTriple.comp_eq])
  letI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hS
  letI : IsFractionRing S L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M S L
  letI : FiniteDimensional K S := inferInstance
  letI : Field S := fieldOfFiniteDimensional K S
  letI : IsScalarTower K S L := isScalarTower_fractionRing_localization_fractionRing A
  let _ : FiniteDimensional S L := by
    let _ : IsFractionRing S S := IsFractionRing.idem S S
    exact LinearEquiv.finiteDimensional
      (((FractionRing.algEquiv S S).symm.trans (FractionRing.algEquiv S L)).toLinearEquiv)
  exact FiniteDimensional.trans K S L

/-
Domain triage:
* primary domain: orders of vanishing for module-finite extensions of one-dimensional Noetherian
  local domains, expressed through the canonical valuation owner `Ring.ordFrac`;
* sampled owner API: `Ring.ordFrac`,
  `Ring.KrullDimLE.of_isLocalization`,
  `length_eq_sum_residueFieldDegree_mul_length_localizedModule`,
  `finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension`,
  `comap_maximalIdeal_of_finiteType_of_finiteFractionRingExtension`, and
  `moduleFinite_residueField_of_finiteType_of_finiteFractionRingExtension`;
* source-facing layer: the weighted sum formula over maximal localizations;
* core/canonical owners: `Ring.ordFrac` for the valuation and `Module.finrank` for the
  residue-field degree;
* bridge/view: the semilocal bridge theorems above supply finite maximal spectrum, contraction to
  `maximalIdeal A`, and residue-field finiteness, while the only additional local bridge below is
  localization permanence for the `Ring.ordFrac` owner.

Primitive data are the finite algebra `A → B`, the element `y : Frac(B)ˣ`, and the canonical
dimension-at-most-one owner hypothesis `[Ring.KrullDimLE 1 A]`. Derived API consists of
semilocality of `B`, contraction to `maximalIdeal A`, the induced residue-field extensions,
injectivity of `A → B` from the fraction-ring tower, and localization permanence needed to
evaluate `Ring.ordFrac` after localizing at maximal ideals.
-/

-- Proof sketch: first pass the dimension-at-most-one hypothesis from `A` to the finite extension
-- `B`, then localize at `m`. Localization cannot increase Krull dimension, so `Bₘ` still
-- satisfies the `Ring.KrullDimLE 1` hypothesis needed for `Ring.ordFrac`.
omit [Algebra (FractionRing A) (FractionRing B)]
  [IsScalarTower A (FractionRing A) (FractionRing B)] in
/-- The localization of a module-finite extension of a one-dimensional Noetherian local domain at a
maximal ideal still has Krull dimension at most `1`. -/
theorem krullDimLE_one_localizationAtPrime_of_moduleFinite
    [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Module.Finite A B]
    (m : MaximalSpectrum B) :
    Ring.KrullDimLE 1 (Localization.AtPrime m.asIdeal) := by
  have hBdim : Ring.DimensionLEOne B := by
    -- Integral finite extensions of domains preserve the property that every nonzero prime is
    -- maximal.
    letI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
    refine Ring.DimensionLEOne.mk ?_
    intro I hI_ne hI_prime
    letI : I.IsPrime := hI_prime
    obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI_ne
    have hcomap_ne : Ideal.comap (algebraMap A B) I ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem hx0 hxI (Algebra.IsIntegral.isIntegral x)
    have hcomap_max : (Ideal.comap (algebraMap A B) I).IsMaximal :=
      (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp inferInstance)
        (Ideal.comap (algebraMap A B) I) hcomap_ne inferInstance
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap I hcomap_max
  letI : Ring.DimensionLEOne B := hBdim
  have hlocDim : Ring.DimensionLEOne (Localization.AtPrime m.asIdeal) :=
    Ring.DimensionLEOne.localization (Localization.AtPrime m.asIdeal)
      (M := m.asIdeal.primeCompl) m.asIdeal.primeCompl_le_nonZeroDivisors
  letI : Ring.DimensionLEOne (Localization.AtPrime m.asIdeal) := hlocDim
  -- Convert the dimension-one owner back to the `Ring.KrullDimLE 1` form required by `Ring.ordFrac`.
  exact Ring.KrullDimLE.mk₁' fun I hI_ne hI_prime => by
    exact Ideal.IsPrime.isMaximal hI_prime hI_ne

end

section

variable (A : Type u) {B : Type v}
variable [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
variable [Algebra (FractionRing A) (FractionRing B)]
variable [IsScalarTower A (FractionRing A) (FractionRing B)]

section

variable [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Module.Finite A B]

local notation "κA" => Ideal.ResidueField (maximalIdeal A)

local instance :
    FiniteDimensional (FractionRing A) (FractionRing B) :=
  finiteDimensional_fractionRing_of_moduleFinite A

local instance (m : MaximalSpectrum B) :
    Algebra κA (Ideal.ResidueField m.asIdeal) :=
  residueFieldAlgebra_of_moduleFinite A m

local instance (m : MaximalSpectrum B) :
    Module.Finite κA (Ideal.ResidueField m.asIdeal) :=
  moduleFinite_residueField_of_moduleFinite A m

omit [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Module.Finite A B] in
/-- Helper for Chap10 Lemma 10 121 8: a lattice remains a lattice after applying a
fraction-field linear equivalence and then restricting scalars to the base ring. -/
private instance isLattice_map_restrictScalars
    {R : Type u} {K : Type v} {V : Type w} {W : Type w'}
    [CommRing R] [Field K] [Algebra R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [AddCommGroup W] [Module R W] [Module K W] [IsScalarTower R K W]
    (φ : V ≃ₗ[K] W) (M : Submodule R V) [Submodule.IsLattice K M] :
    Submodule.IsLattice K (M.map ((φ.restrictScalars R) : V →ₗ[R] W)) where
  fg := by
    -- Finite generation is preserved by the image of the restricted linear map.
    exact Submodule.IsLattice.fg.map ((φ.restrictScalars R) : V →ₗ[R] W)
  span_eq_top := by
    let φR : V ≃ₗ[R] W := φ.restrictScalars R
    have himage :
        (φ : V →ₗ[K] W) '' (M : Set V) =
          ((M.map ((φ.restrictScalars R) : V →ₗ[R] W) : Submodule R W) : Set W) := by
      -- Identify the set-theoretic image with the submodule image after scalar restriction.
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact Submodule.mem_map_of_mem hy
      · intro hx
        refine ⟨φ.symm x, ?_, by simp⟩
        simpa [φR] using
          (Submodule.mem_map_equiv
            (p := M) (e := φR) (x := x)).mp hx
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := φ.surjective x
    have hy : y ∈ Submodule.span K (M : Set V) := by
      rw [Submodule.IsLattice.span_eq_top]
      trivial
    have hφy : φ y ∈ (Submodule.span K (M : Set V)).map (φ : V →ₗ[K] W) :=
      Submodule.mem_map_of_mem hy
    -- Transport the spanning equality for `M` across `φ`.
    rw [Submodule.map_span, himage] at hφy
    exact hφy

omit [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
  [Algebra (FractionRing A) (FractionRing B)]
  [IsScalarTower A (FractionRing A) (FractionRing B)] [IsLocalRing A] [IsNoetherianRing A]
  [Ring.KrullDimLE 1 A] [Module.Finite A B] in
/-- Helper for Chap10 Lemma 10 121 8: the image of a domain in its fraction field is a lattice. -/
private theorem isLattice_range_algebraMap_of_isFractionRing
    {R : Type u} {K : Type v}
    [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] :
    Submodule.IsLattice K (LinearMap.range (Algebra.linearMap R K) : Submodule R K) := by
  refine ⟨Submodule.fg_range (Algebra.linearMap R K), ?_⟩
  rw [eq_top_iff]
  intro x _
  have hone : (1 : K) ∈ (LinearMap.range (Algebra.linearMap R K) : Submodule R K) :=
    ⟨1, by simp⟩
  have hone_span : (1 : K) ∈
      Submodule.span K ((LinearMap.range (Algebra.linearMap R K) : Submodule R K) : Set K) :=
    Submodule.subset_span hone
  -- The `K`-span contains `1`, so it contains every scalar multiple `x • 1 = x`.
  simpa using (Submodule.smul_mem
    (Submodule.span K ((LinearMap.range (Algebra.linearMap R K) : Submodule R K) : Set K))
    x hone_span)

omit [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
/-- Helper for Chap10 Lemma 10 121 8: the image of `B` spans `FractionRing B` after extending
scalars from `A` to `FractionRing A`. -/
private theorem span_range_algebraMap_fractionRing_of_moduleFinite :
    Submodule.span (FractionRing A)
      ((LinearMap.range ((Algebra.linearMap B (FractionRing B)).restrictScalars A) :
        Submodule A (FractionRing B)) : Set (FractionRing B)) = ⊤ := by
  letI : Module.IsTorsionFree A B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (algebraMap_injective_of_field_isFractionRing A B (FractionRing A) (FractionRing B))
  letI : FaithfulSMul A B := Module.isTorsionFree_iff_faithfulSMul.mp inferInstance
  letI : Algebra.IsAlgebraic A B := Algebra.IsIntegral.isAlgebraic
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := B)
  have hspan_image :
      Submodule.span (FractionRing A) (algebraMap B (FractionRing B) '' Set.range s) = ⊤ := by
    -- Localizing a finite `A`-generating family of `B` makes its image span the fraction field.
    simpa using
      (span_eq_top_localization_localization (Rₛ := FractionRing A) (S := nonZeroDivisors A)
        (Aₛ := FractionRing B) (A := B) (v := Set.range s) hs)
  rw [eq_top_iff]
  intro x hx
  have hx_image :
      x ∈ Submodule.span (FractionRing A) (algebraMap B (FractionRing B) '' Set.range s) := by
    simpa [hspan_image] using hx
  -- The finite generating image lies inside the full range lattice, so the latter also spans.
  exact Submodule.span_mono (by
    rintro z ⟨b, _hb, rfl⟩
    exact ⟨b, rfl⟩) hx_image

omit [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
/-- Helper for Chap10 Lemma 10 121 8: the global range `B -> FractionRing B` is an
`A`-lattice after scalar extension to `FractionRing A`. -/
private instance isLattice_range_algebraMap_fractionRing_of_moduleFinite :
    Submodule.IsLattice (FractionRing A)
      (LinearMap.range ((Algebra.linearMap B (FractionRing B)).restrictScalars A) :
        Submodule A (FractionRing B)) := by
  refine ⟨Submodule.fg_range ((Algebra.linearMap B (FractionRing B)).restrictScalars A), ?_⟩
  -- Finite generation comes from module-finiteness; the preceding helper supplies spanning.
  exact span_range_algebraMap_fractionRing_of_moduleFinite (A := A)

/-- Helper for Chap10 Lemma 10 121 8: the localized range
`B_m -> FractionRing B` is a lattice in the local fraction-field vector space. -/
private instance isLattice_localRange_algebraMap_fractionRing (m : MaximalSpectrum B) :
    Submodule.IsLattice (FractionRing B)
      (LinearMap.range (Algebra.linearMap (Localization.AtPrime m.asIdeal) (FractionRing B)) :
        Submodule (Localization.AtPrime m.asIdeal) (FractionRing B)) := by
  -- This is the generic fraction-field range lattice, applied to the local ring `B_m`.
  exact isLattice_range_algebraMap_of_isFractionRing

/-- Helper for Chap10 Lemma 10 121 8: multiplying the local range lattice by a unit of
`FractionRing B` again gives a local lattice. -/
private theorem isLattice_localRange_map_mulLeft (m : MaximalSpectrum B) (y : (FractionRing B)ˣ) :
    Submodule.IsLattice (FractionRing B)
      ((LinearMap.range (Algebra.linearMap (Localization.AtPrime m.asIdeal) (FractionRing B)) :
        Submodule (Localization.AtPrime m.asIdeal) (FractionRing B)).map
          (((Units.mulLeftLinearEquiv (FractionRing B) (FractionRing B)) y).restrictScalars
            (Localization.AtPrime m.asIdeal) :
            FractionRing B →ₗ[Localization.AtPrime m.asIdeal] FractionRing B)) := by
  letI : Submodule.IsLattice (FractionRing B)
      (LinearMap.range (Algebra.linearMap (Localization.AtPrime m.asIdeal) (FractionRing B)) :
        Submodule (Localization.AtPrime m.asIdeal) (FractionRing B)) :=
    isLattice_localRange_algebraMap_fractionRing m
  -- The preceding transport instance handles the image under the unit multiplication equivalence.
  exact isLattice_map_restrictScalars
    (((Units.mulLeftLinearEquiv (FractionRing B) (FractionRing B)) y)) _

omit [IsDomain A] [IsDomain B] [Algebra A B]
  [IsScalarTower A (FractionRing A) (FractionRing B)] [IsLocalRing A] [IsNoetherianRing A]
  [Ring.KrullDimLE 1 A] [Module.Finite A B] in
/-- Helper for Chap10 Lemma 10 121 8: the determinant of multiplication by a fraction-field unit
is its algebra norm. -/
private theorem det_mulLeftLinearEquiv_eq_norm (y : (FractionRing B)ˣ) :
    (LinearEquiv.det ((Units.mulLeftLinearEquiv (FractionRing A) (FractionRing B)) y) :
        FractionRing A) =
      Algebra.norm (FractionRing A) (y : FractionRing B) := by
  -- The linear equivalence is the unit form of left multiplication, so its determinant is the
  -- algebra norm by the canonical norm computation lemma.
  rw [Algebra.norm_apply, LinearEquiv.coe_det]
  congr 1

omit [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
  [Algebra (FractionRing A) (FractionRing B)]
  [IsScalarTower A (FractionRing A) (FractionRing B)] [IsLocalRing A] [IsNoetherianRing A]
  [Ring.KrullDimLE 1 A] [Module.Finite A B] in
/-- Helper for Chap10 Lemma 10 121 8: over a field, the determinant of left multiplication by a
unit is the unit itself. -/
private theorem det_mulLeftLinearEquiv_self {F : Type*} [Field F] (y : Fˣ) :
    (LinearEquiv.det ((Units.mulLeftLinearEquiv F F) y) : F) = (y : F) := by
  -- The determinant of the one-dimensional left-multiplication map is the scalar multiplier.
  rw [LinearEquiv.coe_det]
  simpa [Units.mulLeftLinearEquiv] using (LinearMap.det_mulLeft (R := F) (a := (y : F)))

/-- Helper for Chap10 Lemma 10 121 8: finite length over a base ring transfers to finite length
over an algebra acting through the same scalar tower. -/
private theorem isFiniteLength_of_tower
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (hM : IsFiniteLength R M) :
    IsFiniteLength S M := by
  -- Unpack finite length into Noetherian and Artinian halves, then use the tower transfer lemmas.
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hM ⊢
  exact
    ⟨isNoetherian_of_tower (R := R) (S := S) (M := M) hM.1,
      isArtinian_of_tower (R := R) (S := S) (M := M) hM.2⟩

omit [Algebra (FractionRing A) (FractionRing B)]
  [IsScalarTower A (FractionRing A) (FractionRing B)] in
/-- Helper for Chap10 Lemma 10 121 8: a module-finite extension of a one-dimensional domain is
again of Krull dimension at most `1`. -/
private theorem krullDimLE_one_of_moduleFinite
    (A : Type u) {B : Type v}
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
    [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Module.Finite A B] :
    Ring.KrullDimLE 1 B := by
  have hBdim : Ring.DimensionLEOne B := by
    -- Integral finite extensions preserve the property that every nonzero prime is maximal.
    letI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
    refine Ring.DimensionLEOne.mk ?_
    intro I hI_ne hI_prime
    letI : I.IsPrime := hI_prime
    obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI_ne
    have hcomap_ne : Ideal.comap (algebraMap A B) I ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem hx0 hxI (Algebra.IsIntegral.isIntegral x)
    have hcomap_max : (Ideal.comap (algebraMap A B) I).IsMaximal :=
      (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp inferInstance)
        (Ideal.comap (algebraMap A B) I) hcomap_ne inferInstance
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap I hcomap_max
  letI : Ring.DimensionLEOne B := hBdim
  -- Repackage the dimension-one owner in the `Ring.KrullDimLE 1` form used by `Ring.ordFrac`.
  exact Ring.KrullDimLE.mk₁' fun I hI_ne hI_prime => by
    exact Ideal.IsPrime.isMaximal hI_prime hI_ne

omit [Algebra (FractionRing A) (FractionRing B)]
  [IsScalarTower A (FractionRing A) (FractionRing B)] in
/-- Helper for Chap10 Lemma 10 121 8: quotienting `B` by a nonzero principal ideal has finite
length as a `B`-module. -/
private theorem principalQuotient_isFiniteLength
    (A : Type u) {B : Type v}
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
    [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Module.Finite A B]
    {c : B} (hc : c ≠ 0) :
    IsFiniteLength B (B ⧸ Ideal.span ({c} : Set B)) := by
  letI : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  letI : Ring.KrullDimLE 1 B := krullDimLE_one_of_moduleFinite (A := A) (B := B)
  -- In a domain, nonzero elements are nonzerodivisors, so the principal quotient owner applies.
  exact isFiniteLength_quotient_span_singleton B (mem_nonZeroDivisors_iff_ne_zero.mpr hc)

omit [Algebra (FractionRing A) (FractionRing B)]
  [IsScalarTower A (FractionRing A) (FractionRing B)] in
/-- Helper for Chap10 Lemma 10 121 8: the semilocal length formula specialized to principal
quotients, with all `ℕ∞` lengths converted to integer-valued finite lengths. -/
private theorem principalQuotientLength_toInt_eq_sum_localizedLength
    {c : B} (hc : c ≠ 0) :
    ((Module.length A (B ⧸ Ideal.span ({c} : Set B))).toNat : ℤ) =
      (let _ : Finite (MaximalSpectrum B) := finite_maximalSpectrum_of_moduleFinite A
       let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite (MaximalSpectrum B)
       ∑ m : MaximalSpectrum B,
        (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℤ) *
          ((Module.length (Localization.AtPrime m.asIdeal)
            (LocalizedModule.AtPrime m.asIdeal (B ⧸ Ideal.span ({c} : Set B)))).toNat : ℤ)) := by
  letI : Finite (MaximalSpectrum B) := finite_maximalSpectrum_of_moduleFinite A
  letI : Fintype (MaximalSpectrum B) := Fintype.ofFinite (MaximalSpectrum B)
  let M := B ⧸ Ideal.span ({c} : Set B)
  have hM : IsFiniteLength B M :=
    principalQuotient_isFiniteLength (A := A) (B := B) hc
  have hlen :
      Module.length A M =
        ∑ m : MaximalSpectrum B,
          (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℕ∞) *
            Module.length (Localization.AtPrime m.asIdeal)
              (LocalizedModule.AtPrime m.asIdeal M) := by
    -- Apply Lemma 10.52.12 to the principal quotient, using the module-finite local residue data.
    simpa [M] using
      (length_eq_sum_residueFieldDegree_mul_length_localizedModule
        (A := A) (B := B) (M := M)
        (comap_maximalIdeal_of_moduleFinite A)
        (fun m ↦ moduleFinite_residueField_of_moduleFinite A m) hM)
  have hloc_ne_top : ∀ m : MaximalSpectrum B,
      Module.length (Localization.AtPrime m.asIdeal)
          (LocalizedModule.AtPrime m.asIdeal M) ≠ ⊤ := by
    intro m
    have hle :
        Module.length (Localization.AtPrime m.asIdeal)
            (LocalizedModule.AtPrime m.asIdeal M) ≤ Module.length B M := by
      simpa [LocalizedModule.AtPrime] using
        (length_localizedModule_le (R := B) (S := m.asIdeal.primeCompl) (M := M))
    exact ne_top_of_le_ne_top (Module.length_ne_top_iff.mpr hM) hle
  have hsummand_ne_top :
      ∀ m ∈ (Finset.univ : Finset (MaximalSpectrum B)),
        (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℕ∞) *
            Module.length (Localization.AtPrime m.asIdeal)
              (LocalizedModule.AtPrime m.asIdeal M) ≠ ⊤ := by
    intro m _hm
    -- The residue degree is finite, and localization cannot increase a finite length to `⊤`.
    exact
      WithTop.mul_ne_top
        (ENat.coe_ne_top (Module.finrank κA (Ideal.ResidueField m.asIdeal))) (hloc_ne_top m)
  have hnat := congrArg ENat.toNat hlen
  rw [ENat.toNat_sum hsummand_ne_top] at hnat
  simp only [ENat.toNat_mul, ENat.toNat_coe] at hnat
  have hnatInt :
      ((Module.length A M).toNat : ℤ) =
        ∑ m : MaximalSpectrum B,
          ((Module.finrank κA (Ideal.ResidueField m.asIdeal) *
              (Module.length (Localization.AtPrime m.asIdeal)
                (LocalizedModule.AtPrime m.asIdeal M)).toNat : ℕ) : ℤ) := by
    exact_mod_cast hnat
  simpa [M, Nat.cast_sum, Nat.cast_mul] using hnatInt

omit [Algebra A B] [IsLocalRing A] [Module.Finite A B] [Algebra (FractionRing A) (FractionRing B)]
  [IsScalarTower A (FractionRing A) (FractionRing B)] in
/-- Helper for Chap10 Lemma 10 121 8: the order monoid hom of a nonzerodivisor is the
exponential of the principal quotient length. -/
private theorem ordMonoidWithZeroHom_eq_exp_principalQuotientLength
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    (a : nonZeroDivisors R) :
    Ring.ordMonoidWithZeroHom R (a : R) =
      WithZero.exp ((Module.length R (R ⧸ Ideal.span ({(a : R)} : Set R))).toNat : ℤ) := by
  have hfin : IsFiniteLength R (R ⧸ Ideal.span ({(a : R)} : Set R)) :=
    isFiniteLength_quotient_span_singleton R a.property
  have hne : Module.length R (R ⧸ Ideal.span ({(a : R)} : Set R)) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr hfin
  -- Unfold the owner definition once, then use finite length to expose the integer exponent.
  simp only [Ring.ordMonoidWithZeroHom, Ring.ord, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, SetLike.coe_mem, if_true]
  rw [← ENat.coe_toNat hne]
  rfl

omit [Algebra A B] [IsLocalRing A] [Module.Finite A B] [Algebra (FractionRing A) (FractionRing B)]
  [IsScalarTower A (FractionRing A) (FractionRing B)] in
/-- Helper for Chap10 Lemma 10 121 8: the logarithm of the order of a fraction presentation is
the difference of the two principal quotient lengths. -/
private theorem log_ordFrac_mk'_eq_principalQuotientLength_sub
    {R : Type u} {K : Type v}
    [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {a : R} {b : nonZeroDivisors R} (ha : a ≠ 0) :
    WithZero.log (Ring.ordFrac R (IsLocalization.mk' K a b)) =
      ((Module.length R (R ⧸ Ideal.span ({a} : Set R))).toNat : ℤ) -
        ((Module.length R (R ⧸ Ideal.span ({(b : R)} : Set R))).toNat : ℤ) := by
  let aNZ : nonZeroDivisors R := ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩
  -- Rewrite the fraction order through the multiplicative owner and then take `log(exp _)`.
  rw [show IsLocalization.mk' K a b = IsLocalization.mk' K (aNZ : R) b by rfl]
  rw [Ring.ordFrac_eq_div R aNZ b]
  rw [ordMonoidWithZeroHom_eq_exp_principalQuotientLength (R := R) aNZ]
  rw [ordMonoidWithZeroHom_eq_exp_principalQuotientLength (R := R) b]
  rw [← WithZero.exp_sub]
  simp [aNZ]

omit [IsDomain B] in
/-- Helper for Chap10 Lemma 10 121 8: localizing a principal quotient gives the quotient of the
local ring by the localized principal ideal. -/
private theorem localizedPrincipalQuotientLength_eq_localPrincipalQuotientLength
    (m : MaximalSpectrum B) (c : B) :
    Module.length (Localization.AtPrime m.asIdeal)
        (LocalizedModule.AtPrime m.asIdeal (B ⧸ Ideal.span ({c} : Set B))) =
      Module.length (Localization.AtPrime m.asIdeal)
        ((Localization.AtPrime m.asIdeal) ⧸
          Ideal.span
            ({algebraMap B (Localization.AtPrime m.asIdeal) c} :
              Set (Localization.AtPrime m.asIdeal))) := by
  let p := m.asIdeal.primeCompl
  let Rm := Localization.AtPrime m.asIdeal
  let I : Submodule B B := Ideal.span ({c} : Set B)
  have hden :
      Submodule.localized p I =
        (Ideal.span ({algebraMap B Rm c} : Set Rm) : Submodule Rm Rm) := by
    -- Normalize the localized denominator to the ideal generated by the localized element.
    change Submodule.localized' Rm p (Algebra.linearMap B Rm) (Ideal.span ({c} : Set B)) =
      (Ideal.span ({algebraMap B Rm c} : Set Rm) : Submodule Rm Rm)
    rw [Ideal.localized'_eq_map]
    rw [Ideal.map_span]
    simp
  let e : LocalizedModule.AtPrime m.asIdeal (B ⧸ I) ≃ₗ[Rm]
      Rm ⧸ (Ideal.span ({algebraMap B Rm c} : Set Rm) : Submodule Rm Rm) :=
    (localizedQuotientEquiv p I).symm.trans (Submodule.quotEquivOfEq _ _ hden)
  -- Transport length across the canonical localized quotient equivalence.
  simpa [p, Rm, I] using e.length_eq

omit [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [Module.Finite A B]
  [Algebra (FractionRing A) (FractionRing B)]
  [IsScalarTower A (FractionRing A) (FractionRing B)] in
/-- Helper for Chap10 Lemma 10 121 8: applying the same linear equivalence to both lattices
preserves their lattice distance. -/
private theorem latticeDistance_map_linearEquiv
    {R : Type u} {K : Type v} {V : Type w} {W : Type w'}
    [CommRing R] [Field K] [Algebra R K] [Ring.KrullDimLE 1 R]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [AddCommGroup W] [Module R W] [Module K W] [IsScalarTower R K W]
    (e : V ≃ₗ[K] W)
    (M N : Submodule R V) [Submodule.IsLattice K M] [Submodule.IsLattice K N] :
    Submodule.latticeDistance
        (M.map ((e.restrictScalars R) : V →ₗ[R] W))
        (N.map ((e.restrictScalars R) : V →ₗ[R] W)) =
      Submodule.latticeDistance M N := by
  let eR : V ≃ₗ[R] W := e.restrictScalars R
  have hmap_inf :
      (M ⊓ N).map (eR : V →ₗ[R] W) =
        M.map (eR : V →ₗ[R] W) ⊓ N.map (eR : V →ₗ[R] W) := by
    -- A linear equivalence carries the intersection exactly to the intersection of the images.
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨Submodule.mem_map_of_mem hy.1, Submodule.mem_map_of_mem hy.2⟩
    · intro hx
      obtain ⟨yM, hyM, hyMx⟩ := hx.1
      obtain ⟨yN, hyN, hyNx⟩ := hx.2
      have hx_eq : eR yM = eR yN := hyMx.trans hyNx.symm
      have hy_eq : yM = yN := eR.injective hx_eq
      have hyMN : yM ∈ N := by
        simpa [hy_eq] using hyN
      exact ⟨yM, ⟨hyM, hyMN⟩, hyMx⟩
  have hlen_left :
      Module.length R
          (M.map (eR : V →ₗ[R] W) ⧸
            ((M.map (eR : V →ₗ[R] W) ⊓ N.map (eR : V →ₗ[R] W)).submoduleOf
              (M.map (eR : V →ₗ[R] W)))) =
        Module.length R (M ⧸ (M ⊓ N).submoduleOf M) := by
    let eM : M ≃ₗ[R] M.map (eR : V →ₗ[R] W) :=
      Submodule.equivMapOfInjective (eR : V →ₗ[R] W) eR.injective M
    have hden :
        ((M ⊓ N).submoduleOf M).map (eM : M →ₗ[R] M.map (eR : V →ₗ[R] W)) =
          ((M.map (eR : V →ₗ[R] W) ⊓ N.map (eR : V →ₗ[R] W)).submoduleOf
            (M.map (eR : V →ₗ[R] W))) := by
      -- Transport the left quotient denominator through the induced equivalence on `M`.
      apply le_antisymm
      · rintro _ ⟨y, hy, rfl⟩
        change ((eM y : M.map (eR : V →ₗ[R] W)) : W) ∈
          M.map (eR : V →ₗ[R] W) ⊓ N.map (eR : V →ₗ[R] W)
        have hyV : (y : V) ∈ M ⊓ N :=
          ⟨y.2, by simpa [Submodule.submoduleOf] using hy⟩
        rw [← hmap_inf]
        exact Submodule.mem_map_of_mem hyV
      · intro x hx
        change (x : W) ∈ M.map (eR : V →ₗ[R] W) ⊓ N.map (eR : V →ₗ[R] W) at hx
        rw [← hmap_inf] at hx
        obtain ⟨y, hy, hyx⟩ := hx
        refine ⟨⟨y, hy.1⟩, ?_, ?_⟩
        · simpa [Submodule.submoduleOf] using hy.2
        · apply Subtype.ext
          simpa [eM] using hyx
    -- The quotient modules are linearly equivalent, so their lengths agree.
    simpa [hden] using
      (Submodule.Quotient.equiv
        ((M ⊓ N).submoduleOf M)
        (((M.map (eR : V →ₗ[R] W) ⊓ N.map (eR : V →ₗ[R] W)).submoduleOf
          (M.map (eR : V →ₗ[R] W)))) eM hden).length_eq.symm
  have hlen_right :
      Module.length R
          (N.map (eR : V →ₗ[R] W) ⧸
            ((M.map (eR : V →ₗ[R] W) ⊓ N.map (eR : V →ₗ[R] W)).submoduleOf
              (N.map (eR : V →ₗ[R] W)))) =
        Module.length R (N ⧸ (M ⊓ N).submoduleOf N) := by
    let eN : N ≃ₗ[R] N.map (eR : V →ₗ[R] W) :=
      Submodule.equivMapOfInjective (eR : V →ₗ[R] W) eR.injective N
    have hden :
        ((M ⊓ N).submoduleOf N).map (eN : N →ₗ[R] N.map (eR : V →ₗ[R] W)) =
          ((M.map (eR : V →ₗ[R] W) ⊓ N.map (eR : V →ₗ[R] W)).submoduleOf
            (N.map (eR : V →ₗ[R] W))) := by
      -- Transport the right quotient denominator through the induced equivalence on `N`.
      apply le_antisymm
      · rintro _ ⟨y, hy, rfl⟩
        change ((eN y : N.map (eR : V →ₗ[R] W)) : W) ∈
          M.map (eR : V →ₗ[R] W) ⊓ N.map (eR : V →ₗ[R] W)
        have hyV : (y : V) ∈ M ⊓ N :=
          ⟨by simpa [Submodule.submoduleOf] using hy, y.2⟩
        rw [← hmap_inf]
        exact Submodule.mem_map_of_mem hyV
      · intro x hx
        change (x : W) ∈ M.map (eR : V →ₗ[R] W) ⊓ N.map (eR : V →ₗ[R] W) at hx
        rw [← hmap_inf] at hx
        obtain ⟨y, hy, hyx⟩ := hx
        refine ⟨⟨y, hy.2⟩, ?_, ?_⟩
        · simpa [Submodule.submoduleOf] using hy.1
        · apply Subtype.ext
          simpa [eN] using hyx
    -- The second quotient is transported by the same equivalence.
    simpa [hden] using
      (Submodule.Quotient.equiv
        ((M ⊓ N).submoduleOf N)
        (((M.map (eR : V →ₗ[R] W) ⊓ N.map (eR : V →ₗ[R] W)).submoduleOf
          (N.map (eR : V →ₗ[R] W)))) eN hden).length_eq.symm
  -- Unfold the distance and replace both quotient lengths by their transported forms.
  rw [Submodule.latticeDistance_def, Submodule.latticeDistance_def]
  rw [hlen_left, hlen_right]

omit [IsDomain A] [IsDomain B] [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  [Module.Finite A B] in
/-- Helper for Chap10 Lemma 10 121 8: the distance from the global range lattice to its
principal multiple is the length of the corresponding principal quotient. -/
private theorem latticeDistance_range_mulLeft_eq_principalQuotientLength
    {c : B} (u : (FractionRing B)ˣ)
    (hu : (u : FractionRing B) = algebraMap B (FractionRing B) c) :
    Submodule.latticeDistance
        (LinearMap.range ((Algebra.linearMap B (FractionRing B)).restrictScalars A) :
          Submodule A (FractionRing B))
        ((LinearMap.range ((Algebra.linearMap B (FractionRing B)).restrictScalars A) :
          Submodule A (FractionRing B)).map
            (((Units.mulLeftLinearEquiv (FractionRing A) (FractionRing B)) u).restrictScalars A :
              FractionRing B →ₗ[A] FractionRing B)) =
      ((Module.length A (B ⧸ Ideal.span ({c} : Set B))).toNat : ℤ) := by
  let K := FractionRing B
  let f : B →ₗ[A] K := (Algebra.linearMap B K).restrictScalars A
  let M : Submodule A K := LinearMap.range f
  let φ : K ≃ₗ[FractionRing A] K :=
    (Units.mulLeftLinearEquiv (FractionRing A) K) u
  let N : Submodule A K := M.map ((φ.restrictScalars A) : K →ₗ[A] K)
  have hNleM : N ≤ M := by
    -- Multiplying an element of the `B`-range by `c ∈ B` stays inside the same range.
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨b, rfl⟩ := hy
    refine ⟨c * b, ?_⟩
    change algebraMap B K (c * b) = (u : K) * algebraMap B K b
    rw [hu, map_mul]
  have hdist :
      Submodule.latticeDistance M N =
        ((Module.length A (M ⧸ N.submoduleOf M)).toNat : ℤ) := by
    -- Since the principal multiple is contained in the range lattice, the second quotient is zero.
    have hinf : M ⊓ N = N := inf_eq_right.mpr hNleM
    rw [Submodule.latticeDistance_def, hinf]
    rw [Submodule.submoduleOf_self]
    simp [K]
  let P : Submodule A B :=
    Submodule.restrictScalars A (Ideal.span ({c} : Set B) : Submodule B B)
  let Q : Submodule A M := N.submoduleOf M
  have hf_injective : Function.Injective f := by
    intro x y hxy
    exact IsFractionRing.injective B K hxy
  let e : B ≃ₗ[A] M := LinearEquiv.ofInjective f hf_injective
  have hmap : P.map (e : B →ₗ[A] M) = Q := by
    -- Under the range equivalence, the principal ideal `(c)` is exactly the principal range `N`.
    apply le_antisymm
    · rintro z ⟨x, hxP, rfl⟩
      change ((e x : M) : K) ∈ N
      obtain ⟨r, hr⟩ := (Ideal.mem_span_singleton'.mp hxP)
      refine ⟨algebraMap B K r, ⟨r, rfl⟩, ?_⟩
      change (u : K) * algebraMap B K r = algebraMap B K x
      calc
        (u : K) * algebraMap B K r = algebraMap B K c * algebraMap B K r := by rw [hu]
        _ = algebraMap B K (c * r) := by rw [map_mul]
        _ = algebraMap B K x := by
              rw [show c * r = x by simpa [mul_comm] using hr]
    · intro z hz
      refine ⟨e.symm z, ?_, ?_⟩
      · change e.symm z ∈ Ideal.span ({c} : Set B)
        change (z : K) ∈ N at hz
        obtain ⟨w, hwM, hφw⟩ := hz
        obtain ⟨r, hrw⟩ := hwM
        have hz_under : algebraMap B K (e.symm z) = (z : K) := by
          -- The inverse of the range equivalence recovers the representative in `B`.
          change f (e.symm z) = (z : K)
          exact LinearEquiv.ofInjective_symm_apply (f := f) (h := hf_injective) z
        have hφ_under : (u : K) * algebraMap B K r = (z : K) := by
          -- Rewrite the image witness for `N` in terms of the chosen range representative `r`.
          have hφ_eq : (u : K) * w = (z : K) := by
            simpa [φ] using hφw
          rw [← hrw] at hφ_eq
          simpa [f] using hφ_eq
        have heq_map : algebraMap B K (e.symm z) = algebraMap B K (c * r) := by
          calc
            algebraMap B K (e.symm z) = (z : K) := hz_under
            _ = (u : K) * algebraMap B K r := hφ_under.symm
            _ = algebraMap B K c * algebraMap B K r := by rw [hu]
            _ = algebraMap B K (c * r) := by rw [map_mul]
        have heq : e.symm z = c * r := IsFractionRing.injective B K heq_map
        exact Ideal.mem_span_singleton'.mpr ⟨r, by simpa [mul_comm, heq]⟩
      · exact LinearEquiv.apply_symm_apply e z
  have hlen_range :
      Module.length A (M ⧸ Q) =
        Module.length A (B ⧸ Ideal.span ({c} : Set B)) := by
    have htransport := (Submodule.Quotient.equiv P Q e hmap).length_eq
    have hrestrict :=
      (Submodule.Quotient.restrictScalarsEquiv A
        (Ideal.span ({c} : Set B) : Submodule B B)).length_eq
    exact htransport.symm.trans hrestrict
  -- Transport the quotient `M/N` back to the explicit principal quotient of `B`.
  simpa [K, M, N, φ] using hdist.trans (congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) hlen_range)

/-- Helper for Chap10 Lemma 10 121 8: a fraction presentation reduces the global multiplication
lattice distance to the difference of the two principal quotient lengths. -/
private theorem global_latticeDistance_mulLeft_range_eq_principalQuotientLength_sub_of_mk_eq
    (y : (FractionRing B)ˣ) {a : B} {b : nonZeroDivisors B}
    (hy : IsLocalization.mk' (FractionRing B) a b = (y : FractionRing B))
    (ha : a ≠ 0) :
    Submodule.latticeDistance
        (LinearMap.range ((Algebra.linearMap B (FractionRing B)).restrictScalars A) :
          Submodule A (FractionRing B))
        ((LinearMap.range ((Algebra.linearMap B (FractionRing B)).restrictScalars A) :
          Submodule A (FractionRing B)).map
            (((Units.mulLeftLinearEquiv (FractionRing A) (FractionRing B)) y).restrictScalars A :
              FractionRing B →ₗ[A] FractionRing B)) =
      ((Module.length A (B ⧸ Ideal.span ({a} : Set B))).toNat : ℤ) -
        ((Module.length A (B ⧸ Ideal.span ({(b : B)} : Set B))).toNat : ℤ) := by
  let K := FractionRing B
  let M : Submodule A K :=
    LinearMap.range ((Algebra.linearMap B K).restrictScalars A)
  let φy : K ≃ₗ[FractionRing A] K :=
    (Units.mulLeftLinearEquiv (FractionRing A) K) y
  have haK : algebraMap B K a ≠ 0 := by
    intro hzero
    exact ha (IsFractionRing.injective B K (by simpa using hzero))
  have hb_ne_zero : (b : B) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.property
  have hbK : algebraMap B K (b : B) ≠ 0 := by
    intro hzero
    exact hb_ne_zero (IsFractionRing.injective B K (by simpa using hzero))
  let ua : Kˣ := Units.mk0 (algebraMap B K a) haK
  let ub : Kˣ := Units.mk0 (algebraMap B K (b : B)) hbK
  let φa : K ≃ₗ[FractionRing A] K :=
    (Units.mulLeftLinearEquiv (FractionRing A) K) ua
  let φb : K ≃ₗ[FractionRing A] K :=
    (Units.mulLeftLinearEquiv (FractionRing A) K) ub
  let Ma : Submodule A K := M.map ((φa.restrictScalars A) : K →ₗ[A] K)
  let Mb : Submodule A K := M.map ((φb.restrictScalars A) : K →ₗ[A] K)
  let Uy : Submodule A K := M.map ((φy.restrictScalars A) : K →ₗ[A] K)
  have hspec : (y : K) * algebraMap B K (b : B) = algebraMap B K a := by
    -- The chosen fraction presentation says that multiplying by the denominator gives `a`.
    have h := IsLocalization.mk'_spec K a b
    rw [hy] at h
    exact h
  have hMb_map_y : Mb.map ((φy.restrictScalars A) : K →ₗ[A] K) = Ma := by
    -- Multiplying first by `b` and then by `y = a / b` is the same principal multiple as
    -- multiplying by `a`.
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨r, rfl⟩ := hw
      refine ⟨algebraMap B K r, ⟨r, rfl⟩, ?_⟩
      change (ua : K) * algebraMap B K r =
        (y : K) * ((ub : K) * algebraMap B K r)
      change algebraMap B K a * algebraMap B K r =
        (y : K) * (algebraMap B K (b : B) * algebraMap B K r)
      rw [← hspec]
      ring
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨r, rfl⟩ := hz
      refine ⟨(ub : K) * algebraMap B K r, ?_, ?_⟩
      · refine ⟨algebraMap B K r, ⟨r, rfl⟩, ?_⟩
        change (ub : K) * algebraMap B K r =
          algebraMap B K (b : B) * algebraMap B K r
        simp [ub]
      · change (y : K) * ((ub : K) * algebraMap B K r) =
          (ua : K) * algebraMap B K r
        change (y : K) * (algebraMap B K (b : B) * algebraMap B K r) =
          algebraMap B K a * algebraMap B K r
        rw [← mul_assoc, hspec]
  have htransport :
      Submodule.latticeDistance Uy Ma = Submodule.latticeDistance M Mb := by
    -- Distance is invariant after applying multiplication by `y` to both lattices.
    simpa [Uy, Ma, Mb, hMb_map_y] using
      (latticeDistance_map_linearEquiv
        (R := A) (K := FractionRing A) (V := K) (W := K) φy M Mb)
  have hdecomp :
      Submodule.latticeDistance M Uy =
        Submodule.latticeDistance M Ma - Submodule.latticeDistance M Mb := by
    have hadd :
        Submodule.latticeDistance M Uy =
          Submodule.latticeDistance M Ma + Submodule.latticeDistance Ma Uy :=
      Submodule.latticeDistance_add (M := M) (M' := Ma) (M'' := Uy)
    have hswap :
        Submodule.latticeDistance Ma Uy = -Submodule.latticeDistance Uy Ma :=
      Submodule.latticeDistance_neg_swap (M := Ma) (M' := Uy)
    rw [hadd, hswap, htransport]
    ring
  have hMa :
      Submodule.latticeDistance M Ma =
        ((Module.length A (B ⧸ Ideal.span ({a} : Set B))).toNat : ℤ) := by
    simpa [K, M, Ma, φa, ua] using
      latticeDistance_range_mulLeft_eq_principalQuotientLength
        (A := A) (B := B) (c := a) ua rfl
  have hMb :
      Submodule.latticeDistance M Mb =
        ((Module.length A (B ⧸ Ideal.span ({(b : B)} : Set B))).toNat : ℤ) := by
    simpa [K, M, Mb, φb, ub] using
      latticeDistance_range_mulLeft_eq_principalQuotientLength
        (A := A) (B := B) (c := (b : B)) ub rfl
  -- Insert the principal lattice `aB`, use invariance to identify the second leg with `bB`,
  -- and rewrite both principal distances as quotient lengths.
  simpa [K, M, Uy, φy] using
    (hdecomp.trans (by rw [hMa, hMb]))

/-- Helper for Chap10 Lemma 10 121 8: after localizing at `m`, the same fraction presentation
reduces the local multiplication lattice distance to localized principal quotient lengths. -/
private theorem local_latticeDistance_mulLeft_range_eq_principalQuotientLength_sub_of_mk_eq
    (m : MaximalSpectrum B)
    [IsNoetherianRing (Localization.AtPrime m.asIdeal)]
    [Ring.KrullDimLE 1 (Localization.AtPrime m.asIdeal)]
    (y : (FractionRing B)ˣ) {a : B} {b : nonZeroDivisors B}
    (hy : IsLocalization.mk' (FractionRing B) a b = (y : FractionRing B))
    (ha : a ≠ 0) :
    Submodule.latticeDistance
        (LinearMap.range
          (Algebra.linearMap (Localization.AtPrime m.asIdeal) (FractionRing B)) :
          Submodule (Localization.AtPrime m.asIdeal) (FractionRing B))
        ((LinearMap.range
          (Algebra.linearMap (Localization.AtPrime m.asIdeal) (FractionRing B)) :
          Submodule (Localization.AtPrime m.asIdeal) (FractionRing B)).map
            (((Units.mulLeftLinearEquiv (FractionRing B) (FractionRing B)) y).restrictScalars
              (Localization.AtPrime m.asIdeal) :
              FractionRing B →ₗ[Localization.AtPrime m.asIdeal] FractionRing B)) =
      ((Module.length (Localization.AtPrime m.asIdeal)
          (LocalizedModule.AtPrime m.asIdeal (B ⧸ Ideal.span ({a} : Set B)))).toNat : ℤ) -
        ((Module.length (Localization.AtPrime m.asIdeal)
          (LocalizedModule.AtPrime m.asIdeal (B ⧸ Ideal.span ({(b : B)} : Set B)))).toNat :
          ℤ) := by
  let Rm := Localization.AtPrime m.asIdeal
  let K := FractionRing B
  let Mm : Submodule Rm K :=
    LinearMap.range (Algebra.linearMap Rm K)
  let φm : K ≃ₗ[K] K :=
    (Units.mulLeftLinearEquiv K K) y
  have hdist_log :
      Submodule.latticeDistance Mm
          (Mm.map ((φm.restrictScalars Rm) : K →ₗ[Rm] K)) =
        WithZero.log (Ring.ordFrac Rm (y : K)) := by
    have hdet :
        Submodule.latticeDistance Mm
            (Mm.map ((φm.restrictScalars Rm) : K →ₗ[Rm] K)) =
          WithZero.log (Ring.ordFrac Rm (LinearEquiv.det φm : K)) := by
      -- Lemma 10.121.7 converts the local lattice distance to the determinant order.
      simpa [Mm, φm, Rm, K] using
        (latticeDistance_image_eq_ordFrac_det
          (R := Rm) (K := K) (V := K) φm Mm)
    have hdet_self :
        WithZero.log (Ring.ordFrac Rm (LinearEquiv.det φm : K)) =
          WithZero.log (Ring.ordFrac Rm (y : K)) := by
      -- In the one-dimensional local fraction field, multiplication by `y` has determinant `y`.
      simpa [φm, K] using
        congrArg (fun z : K => WithZero.log (Ring.ordFrac Rm z))
          (det_mulLeftLinearEquiv_self (F := K) y)
    exact hdet.trans hdet_self
  have ha_loc_ne_zero : algebraMap B Rm a ≠ 0 := by
    intro hzero
    exact ha
      ((IsLocalization.injective (S := Rm) m.asIdeal.primeCompl_le_nonZeroDivisors)
        (by simpa using hzero))
  have hb_ne_zero : (b : B) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.property
  have hb_loc_ne_zero : algebraMap B Rm (b : B) ≠ 0 := by
    intro hzero
    exact hb_ne_zero
      ((IsLocalization.injective (S := Rm) m.asIdeal.primeCompl_le_nonZeroDivisors)
        (by simpa using hzero))
  let bLoc : nonZeroDivisors Rm :=
    ⟨algebraMap B Rm (b : B), mem_nonZeroDivisors_iff_ne_zero.mpr hb_loc_ne_zero⟩
  have hmk_local :
      IsLocalization.mk' K (algebraMap B Rm a) bLoc = (y : K) := by
    have hmk_compare :
        IsLocalization.mk' K (algebraMap B Rm a) bLoc =
          IsLocalization.mk' K a b := by
      -- Compare the fraction presentations over `B` and over the localization `B_m`.
      rw [IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div]
      simp [bLoc, Rm, K, IsScalarTower.algebraMap_apply B Rm K]
    exact hmk_compare.trans hy
  have hlog :
      WithZero.log (Ring.ordFrac Rm (y : K)) =
        ((Module.length Rm (Rm ⧸ Ideal.span ({algebraMap B Rm a} : Set Rm))).toNat : ℤ) -
          ((Module.length Rm
            (Rm ⧸ Ideal.span ({algebraMap B Rm (b : B)} : Set Rm))).toNat : ℤ) := by
    have hbase :=
      log_ordFrac_mk'_eq_principalQuotientLength_sub
        (R := Rm) (K := K) (a := algebraMap B Rm a) (b := bLoc) ha_loc_ne_zero
    rw [hmk_local] at hbase
    simpa [bLoc] using hbase
  have hlen_a :=
    localizedPrincipalQuotientLength_eq_localPrincipalQuotientLength m a
  have hlen_b :=
    localizedPrincipalQuotientLength_eq_localPrincipalQuotientLength m (b : B)
  -- Replace the local quotient normal form by the localized global principal quotients.
  simpa [Rm, K, Mm, φm] using
    (hdist_log.trans (by
      rw [hlog]
      rw [← hlen_a, ← hlen_b]))

/-- Helper for Chap10 Lemma 10 121 8: the global lattice distance for multiplication by a
fraction-field unit decomposes as the residue-degree weighted sum of the local distances. -/
private theorem latticeDistance_mulLeft_range_eq_sum_local_latticeDistance
    (y : (FractionRing B)ˣ) :
    Submodule.latticeDistance
        (LinearMap.range ((Algebra.linearMap B (FractionRing B)).restrictScalars A) :
          Submodule A (FractionRing B))
        ((LinearMap.range ((Algebra.linearMap B (FractionRing B)).restrictScalars A) :
          Submodule A (FractionRing B)).map
            (((Units.mulLeftLinearEquiv (FractionRing A) (FractionRing B)) y).restrictScalars A :
              FractionRing B →ₗ[A] FractionRing B)) =
      let _ : Finite (MaximalSpectrum B) :=
        finite_maximalSpectrum_of_moduleFinite A
      let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite (MaximalSpectrum B)
      let _ : IsNoetherianRing B := IsNoetherianRing.of_finite A B
      let _ : ∀ m : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime m.asIdeal) :=
        fun m ↦
          IsLocalization.isNoetherianRing m.asIdeal.primeCompl
            (Localization.AtPrime m.asIdeal) inferInstance
      let _ : ∀ m : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime m.asIdeal) :=
        fun m ↦ krullDimLE_one_localizationAtPrime_of_moduleFinite A m
      ∑ m : MaximalSpectrum B,
        (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℤ) *
          Submodule.latticeDistance
            (LinearMap.range
              (Algebra.linearMap (Localization.AtPrime m.asIdeal) (FractionRing B)) :
              Submodule (Localization.AtPrime m.asIdeal) (FractionRing B))
            ((LinearMap.range
              (Algebra.linearMap (Localization.AtPrime m.asIdeal) (FractionRing B)) :
              Submodule (Localization.AtPrime m.asIdeal) (FractionRing B)).map
                (((Units.mulLeftLinearEquiv (FractionRing B) (FractionRing B)) y).restrictScalars
                  (Localization.AtPrime m.asIdeal) :
                  FractionRing B →ₗ[Localization.AtPrime m.asIdeal] FractionRing B)) := by
  -- Route correction: the previous arbitrary common-lower quotient route produced transport-heavy
  -- localized quotient goals. Here the only semilocal formula used is the proved principal
  -- quotient formula, applied separately to the numerator and denominator of `y = a / b`.
  classical
  letI : Finite (MaximalSpectrum B) := finite_maximalSpectrum_of_moduleFinite A
  letI : Fintype (MaximalSpectrum B) := Fintype.ofFinite (MaximalSpectrum B)
  letI : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  letI : ∀ m : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime m.asIdeal) :=
    fun m ↦
      IsLocalization.isNoetherianRing m.asIdeal.primeCompl
        (Localization.AtPrime m.asIdeal) inferInstance
  letI : ∀ m : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime m.asIdeal) :=
    fun m ↦ krullDimLE_one_localizationAtPrime_of_moduleFinite A m
  obtain ⟨a, b, hy⟩ := IsLocalization.exists_mk'_eq B⁰ (y : FractionRing B)
  have ha : a ≠ 0 := by
    intro ha0
    have hzero : (y : FractionRing B) = 0 := by
      rw [← hy, ha0, IsLocalization.mk'_zero]
    exact (Units.ne_zero y) hzero
  have hb : (b : B) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.property
  have ha_sum :
      ((Module.length A (B ⧸ Ideal.span ({a} : Set B))).toNat : ℤ) =
        ∑ m : MaximalSpectrum B,
          (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℤ) *
            ((Module.length (Localization.AtPrime m.asIdeal)
              (LocalizedModule.AtPrime m.asIdeal (B ⧸ Ideal.span ({a} : Set B)))).toNat : ℤ) :=
    principalQuotientLength_toInt_eq_sum_localizedLength (A := A) (B := B) ha
  have hb_sum :
      ((Module.length A (B ⧸ Ideal.span ({(b : B)} : Set B))).toNat : ℤ) =
        ∑ m : MaximalSpectrum B,
          (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℤ) *
            ((Module.length (Localization.AtPrime m.asIdeal)
              (LocalizedModule.AtPrime m.asIdeal
                (B ⧸ Ideal.span ({(b : B)} : Set B)))).toNat : ℤ) :=
    principalQuotientLength_toInt_eq_sum_localizedLength (A := A) (B := B) hb
  -- Rewrite the global distance as the numerator-minus-denominator principal length difference,
  -- decompose both principal lengths semilocally, and recombine the local differences.
  simpa using
    (calc
      Submodule.latticeDistance
          (LinearMap.range ((Algebra.linearMap B (FractionRing B)).restrictScalars A) :
            Submodule A (FractionRing B))
          ((LinearMap.range ((Algebra.linearMap B (FractionRing B)).restrictScalars A) :
            Submodule A (FractionRing B)).map
              (((Units.mulLeftLinearEquiv (FractionRing A) (FractionRing B)) y).restrictScalars A :
                FractionRing B →ₗ[A] FractionRing B)) =
          ((Module.length A (B ⧸ Ideal.span ({a} : Set B))).toNat : ℤ) -
            ((Module.length A (B ⧸ Ideal.span ({(b : B)} : Set B))).toNat : ℤ) := by
            exact
              global_latticeDistance_mulLeft_range_eq_principalQuotientLength_sub_of_mk_eq
                (A := A) (B := B) y hy ha
      _ = (∑ m : MaximalSpectrum B,
            (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℤ) *
              ((Module.length (Localization.AtPrime m.asIdeal)
                (LocalizedModule.AtPrime m.asIdeal (B ⧸ Ideal.span ({a} : Set B)))).toNat : ℤ)) -
          (∑ m : MaximalSpectrum B,
            (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℤ) *
              ((Module.length (Localization.AtPrime m.asIdeal)
                (LocalizedModule.AtPrime m.asIdeal
                  (B ⧸ Ideal.span ({(b : B)} : Set B)))).toNat : ℤ)) := by
            rw [ha_sum, hb_sum]
      _ = ∑ m : MaximalSpectrum B,
            ((Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℤ) *
                ((Module.length (Localization.AtPrime m.asIdeal)
                  (LocalizedModule.AtPrime m.asIdeal (B ⧸ Ideal.span ({a} : Set B)))).toNat :
                  ℤ) -
              (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℤ) *
                ((Module.length (Localization.AtPrime m.asIdeal)
                  (LocalizedModule.AtPrime m.asIdeal
                    (B ⧸ Ideal.span ({(b : B)} : Set B)))).toNat : ℤ)) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ m : MaximalSpectrum B,
            (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℤ) *
              (((Module.length (Localization.AtPrime m.asIdeal)
                (LocalizedModule.AtPrime m.asIdeal (B ⧸ Ideal.span ({a} : Set B)))).toNat :
                ℤ) -
                ((Module.length (Localization.AtPrime m.asIdeal)
                  (LocalizedModule.AtPrime m.asIdeal
                    (B ⧸ Ideal.span ({(b : B)} : Set B)))).toNat : ℤ)) := by
            refine Finset.sum_congr rfl ?_
            intro m _hm
            ring
      _ = ∑ m : MaximalSpectrum B,
            (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℤ) *
              Submodule.latticeDistance
                (LinearMap.range
                  (Algebra.linearMap (Localization.AtPrime m.asIdeal) (FractionRing B)) :
                  Submodule (Localization.AtPrime m.asIdeal) (FractionRing B))
                ((LinearMap.range
                  (Algebra.linearMap (Localization.AtPrime m.asIdeal) (FractionRing B)) :
                  Submodule (Localization.AtPrime m.asIdeal) (FractionRing B)).map
                    (((Units.mulLeftLinearEquiv (FractionRing B) (FractionRing B)) y).restrictScalars
                      (Localization.AtPrime m.asIdeal) :
                      FractionRing B →ₗ[Localization.AtPrime m.asIdeal] FractionRing B)) := by
            refine Finset.sum_congr rfl ?_
            intro m _hm
            letI : IsNoetherianRing (Localization.AtPrime m.asIdeal) :=
              IsLocalization.isNoetherianRing m.asIdeal.primeCompl
                (Localization.AtPrime m.asIdeal) inferInstance
            letI : Ring.KrullDimLE 1 (Localization.AtPrime m.asIdeal) :=
              krullDimLE_one_localizationAtPrime_of_moduleFinite A m
            rw [local_latticeDistance_mulLeft_range_eq_principalQuotientLength_sub_of_mk_eq
              (m := m) (y := y) (a := a) (b := b) hy ha])

/-- Helper for Chap10 Lemma 10 121 8: the global norm order is the lattice distance of the
global range lattice under multiplication by `y`. -/
private theorem ordFrac_norm_eq_latticeDistance_mulLeft_range
    (y : (FractionRing B)ˣ) :
    WithZero.log (Ring.ordFrac A (Algebra.norm (FractionRing A) (y : FractionRing B))) =
      Submodule.latticeDistance
        (LinearMap.range ((Algebra.linearMap B (FractionRing B)).restrictScalars A) :
          Submodule A (FractionRing B))
        ((LinearMap.range ((Algebra.linearMap B (FractionRing B)).restrictScalars A) :
          Submodule A (FractionRing B)).map
            (((Units.mulLeftLinearEquiv (FractionRing A) (FractionRing B)) y).restrictScalars A :
              FractionRing B →ₗ[A] FractionRing B)) := by
  let M : Submodule A (FractionRing B) :=
    LinearMap.range ((Algebra.linearMap B (FractionRing B)).restrictScalars A)
  let φA : FractionRing B ≃ₗ[FractionRing A] FractionRing B :=
    (Units.mulLeftLinearEquiv (FractionRing A) (FractionRing B)) y
  have hdet :
      Submodule.latticeDistance M
          (M.map ((φA.restrictScalars A) : FractionRing B →ₗ[A] FractionRing B)) =
        WithZero.log (Ring.ordFrac A (LinearEquiv.det φA : FractionRing A)) := by
    -- Lemma 10.121.7 converts the global lattice distance to the determinant order.
    simpa [M, φA] using
      (latticeDistance_image_eq_ordFrac_det (R := A) (K := FractionRing A)
        (V := FractionRing B) φA M)
  have hnorm :
      WithZero.log (Ring.ordFrac A (Algebra.norm (FractionRing A) (y : FractionRing B))) =
        WithZero.log (Ring.ordFrac A (LinearEquiv.det φA : FractionRing A)) := by
    -- The determinant of multiplication by `y` is its field norm.
    simpa [φA] using
      congrArg (fun z : FractionRing A => WithZero.log (Ring.ordFrac A z))
        (det_mulLeftLinearEquiv_eq_norm (A := A) (B := B) y).symm
  exact hnorm.trans hdet.symm

/-- Helper for Chap10 Lemma 10 121 8: after localizing at a maximal ideal, the lattice distance
of multiplication by `y` is the local order of `y`. -/
private theorem local_latticeDistance_mulLeft_range_eq_ordFrac
    (m : MaximalSpectrum B)
    [IsNoetherianRing (Localization.AtPrime m.asIdeal)]
    [Ring.KrullDimLE 1 (Localization.AtPrime m.asIdeal)]
    (y : (FractionRing B)ˣ) :
    Submodule.latticeDistance
        (LinearMap.range
          (Algebra.linearMap (Localization.AtPrime m.asIdeal) (FractionRing B)) :
          Submodule (Localization.AtPrime m.asIdeal) (FractionRing B))
        ((LinearMap.range
          (Algebra.linearMap (Localization.AtPrime m.asIdeal) (FractionRing B)) :
          Submodule (Localization.AtPrime m.asIdeal) (FractionRing B)).map
            (((Units.mulLeftLinearEquiv (FractionRing B) (FractionRing B)) y).restrictScalars
              (Localization.AtPrime m.asIdeal) :
              FractionRing B →ₗ[Localization.AtPrime m.asIdeal] FractionRing B)) =
      WithZero.log (Ring.ordFrac (Localization.AtPrime m.asIdeal) (y : FractionRing B)) := by
  let φm : FractionRing B ≃ₗ[FractionRing B] FractionRing B :=
    (Units.mulLeftLinearEquiv (FractionRing B) (FractionRing B)) y
  let Mm : Submodule (Localization.AtPrime m.asIdeal) (FractionRing B) :=
    LinearMap.range (Algebra.linearMap (Localization.AtPrime m.asIdeal) (FractionRing B))
  have hdet :
      Submodule.latticeDistance Mm
          (Mm.map
            ((φm.restrictScalars (Localization.AtPrime m.asIdeal)) :
              FractionRing B →ₗ[Localization.AtPrime m.asIdeal] FractionRing B)) =
        WithZero.log
          (Ring.ordFrac (Localization.AtPrime m.asIdeal)
            (LinearEquiv.det φm : FractionRing B)) := by
    -- The determinant/order bridge applies in the localized one-dimensional ring.
    simpa [Mm, φm] using
      (latticeDistance_image_eq_ordFrac_det
        (R := Localization.AtPrime m.asIdeal) (K := FractionRing B)
        (V := FractionRing B) φm Mm)
  have hdet_self :
      WithZero.log
          (Ring.ordFrac (Localization.AtPrime m.asIdeal)
            (LinearEquiv.det φm : FractionRing B)) =
        WithZero.log (Ring.ordFrac (Localization.AtPrime m.asIdeal) (y : FractionRing B)) := by
    -- Over the one-dimensional local fraction field, this determinant is just `y`.
    simpa [φm] using
      congrArg
        (fun z : FractionRing B =>
          WithZero.log (Ring.ordFrac (Localization.AtPrime m.asIdeal) z))
        (det_mulLeftLinearEquiv_self (F := FractionRing B) y)
  exact hdet.trans hdet_self

-- Proof sketch: write the order on the left as the length of `B / yB` via the determinant formula
-- for lattices from Lemma `10.121.7`, decompose that length into the sum of the local lengths over
-- the finitely many maximal ideals of `B` using Lemma `10.52.12`, and identify each local length
-- with the local order of vanishing. The determinant giving the lattice distance is exactly the
-- field norm `Norm_{Frac(B)/Frac(A)}(y)`.
/-- Chap10 Lemma 10 121 8: if `A → B` is a module-finite extension of domains with `A` a one-dimensional
Noetherian local domain, then the order of vanishing on `A` of the norm of `y ∈ Frac(B)ˣ` equals
the sum over the maximal ideals `m` of `B` of the residue-field degree
`[κ(m) : κ(maximalIdeal A)]` times the order of vanishing of `y` in `Bₘ`. -/
@[stacks 02MJ]
theorem ordFrac_norm_eq_sum_residueFieldDegree_mul_local_ordFrac (y : (FractionRing B)ˣ) :
    WithZero.log (Ring.ordFrac A (Algebra.norm (FractionRing A) (y : FractionRing B))) =
      let _ : Finite (MaximalSpectrum B) :=
        finite_maximalSpectrum_of_moduleFinite A
      let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite (MaximalSpectrum B)
      let _ : IsNoetherianRing B := IsNoetherianRing.of_finite A B
      let _ : ∀ m : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime m.asIdeal) :=
        fun m ↦
          IsLocalization.isNoetherianRing m.asIdeal.primeCompl
            (Localization.AtPrime m.asIdeal) inferInstance
      let _ : ∀ m : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime m.asIdeal) :=
        fun m ↦ krullDimLE_one_localizationAtPrime_of_moduleFinite A m
      ∑ m : MaximalSpectrum B,
        (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℤ) *
          WithZero.log (Ring.ordFrac (Localization.AtPrime m.asIdeal) (y : FractionRing B)) := by
  -- Replace the global order by a lattice distance, decompose that distance semilocally, and
  -- convert every local distance back to the corresponding local order.
  letI : Finite (MaximalSpectrum B) := finite_maximalSpectrum_of_moduleFinite A
  letI : Fintype (MaximalSpectrum B) := Fintype.ofFinite (MaximalSpectrum B)
  letI : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  letI : ∀ m : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime m.asIdeal) :=
    fun m ↦
      IsLocalization.isNoetherianRing m.asIdeal.primeCompl
        (Localization.AtPrime m.asIdeal) inferInstance
  letI : ∀ m : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime m.asIdeal) :=
    fun m ↦ krullDimLE_one_localizationAtPrime_of_moduleFinite A m
  calc
    WithZero.log (Ring.ordFrac A (Algebra.norm (FractionRing A) (y : FractionRing B))) =
        Submodule.latticeDistance
          (LinearMap.range ((Algebra.linearMap B (FractionRing B)).restrictScalars A) :
            Submodule A (FractionRing B))
          ((LinearMap.range ((Algebra.linearMap B (FractionRing B)).restrictScalars A) :
            Submodule A (FractionRing B)).map
              (((Units.mulLeftLinearEquiv (FractionRing A) (FractionRing B)) y).restrictScalars A :
                FractionRing B →ₗ[A] FractionRing B)) := by
          exact ordFrac_norm_eq_latticeDistance_mulLeft_range (A := A) (B := B) y
    _ = ∑ m : MaximalSpectrum B,
          (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℤ) *
            Submodule.latticeDistance
              (LinearMap.range
                (Algebra.linearMap (Localization.AtPrime m.asIdeal) (FractionRing B)) :
                Submodule (Localization.AtPrime m.asIdeal) (FractionRing B))
              ((LinearMap.range
                (Algebra.linearMap (Localization.AtPrime m.asIdeal) (FractionRing B)) :
                Submodule (Localization.AtPrime m.asIdeal) (FractionRing B)).map
                  (((Units.mulLeftLinearEquiv (FractionRing B) (FractionRing B)) y).restrictScalars
                    (Localization.AtPrime m.asIdeal) :
                    FractionRing B →ₗ[Localization.AtPrime m.asIdeal] FractionRing B)) := by
          simpa using latticeDistance_mulLeft_range_eq_sum_local_latticeDistance
            (A := A) (B := B) y
    _ = ∑ m : MaximalSpectrum B,
          (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℤ) *
            WithZero.log (Ring.ordFrac (Localization.AtPrime m.asIdeal)
              (y : FractionRing B)) := by
          refine Finset.sum_congr rfl ?_
          intro m _hm
          letI : IsNoetherianRing (Localization.AtPrime m.asIdeal) :=
            IsLocalization.isNoetherianRing m.asIdeal.primeCompl
              (Localization.AtPrime m.asIdeal) inferInstance
          letI : Ring.KrullDimLE 1 (Localization.AtPrime m.asIdeal) :=
            krullDimLE_one_localizationAtPrime_of_moduleFinite A m
          rw [local_latticeDistance_mulLeft_range_eq_ordFrac (m := m) (y := y)]

end

end

end InjectiveAlgebraMapFact
