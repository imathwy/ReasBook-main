import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_1
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_4.ScalarExtensionInduction

/-!
# Elementary induction over algebraically closed coefficient fields

This file packages the universe-polymorphic bridge from Serre's DVR Brauer-induction theorem to
an arbitrary algebraically closed coefficient field.  In characteristic zero we scalar-extend the
top-cyclotomic unit decomposition.  In positive characteristic we choose a prime of the
universe-lifted cyclotomic ring of integers above the residue characteristic, use the DVR theorem
at the localization, and then scalar-extend its residue-field unit decomposition into the given
algebraically closed field.
-/

open IsCyclotomicExtension.Rat
open scoped FiniteRepGrothendieckInduction NumberField Representation

noncomputable section

universe u

namespace Representation

section

variable {G : Type u} [Group G] [Finite G]

local notation "Lexp₀" => CyclotomicField (Monoid.exponent G) ℚ

/-- The full cyclotomic field of the exponent of `G`, lifted into the universe of `G`. -/
private abbrev liftedCyclotomicField : Type u :=
  ULift.{u, 0} Lexp₀

private instance liftedCyclotomicFieldField : Field (liftedCyclotomicField (G := G)) :=
  ULift.field

private instance liftedCyclotomicFieldNumberField :
    NumberField (liftedCyclotomicField (G := G)) :=
  NumberField.of_ringEquiv Lexp₀ (liftedCyclotomicField (G := G))
    (ULift.ringEquiv (R := Lexp₀)).symm

private instance liftedCyclotomicFieldCyclotomic :
    IsCyclotomicExtension {Monoid.exponent G} ℚ (liftedCyclotomicField (G := G)) := by
  classical
  let m := Monoid.exponent G
  letI : NeZero m := Monoid.neZero_exponent_of_finite
  letI : IsCyclotomicExtension {m} ℚ Lexp₀ :=
    CyclotomicField.isCyclotomicExtension (n := m) (K := ℚ)
  rw [IsCyclotomicExtension.iff_adjoin_eq_top]
  constructor
  · intro n hn hn0
    obtain ⟨ζ, hζ⟩ :=
      IsCyclotomicExtension.exists_isPrimitiveRoot
        (S := ({m} : Set ℕ)) (A := ℚ) (B := Lexp₀) hn hn0
    refine ⟨ULift.up ζ, ?_⟩
    have hinj :
        Function.Injective
          ⇑((ULift.ringEquiv (R := Lexp₀)).symm.toRingHom :
            Lexp₀ →+* liftedCyclotomicField (G := G)) :=
      (ULift.ringEquiv (R := Lexp₀)).symm.injective
    exact
      hζ.map_of_injective
        (f := ((ULift.ringEquiv (R := Lexp₀)).symm.toRingHom :
          Lexp₀ →+* liftedCyclotomicField (G := G))) hinj
  · apply Algebra.eq_top_iff.mpr
    intro x
    cases x with
    | up x₀ =>
        have hx₀ :
            x₀ ∈
              Algebra.adjoin ℚ
                {ζ : Lexp₀ | ∃ n : ℕ, n ∈ ({m} : Set ℕ) ∧ n ≠ 0 ∧ ζ ^ n = 1} :=
          IsCyclotomicExtension.adjoin_roots
            (S := ({m} : Set ℕ)) (A := ℚ) (B := Lexp₀) x₀
        induction hx₀ using Algebra.adjoin_induction with
        | mem ζ hζ =>
            apply Algebra.subset_adjoin
            rcases hζ with ⟨n, hn, hn0, hζn⟩
            refine ⟨n, hn, hn0, ?_⟩
            change (ULift.up ζ : liftedCyclotomicField (G := G)) ^ n = 1
            change ULift.up (ζ ^ n) = ULift.up (1 : Lexp₀)
            rw [hζn]
        | algebraMap q =>
            change
              (algebraMap ℚ (liftedCyclotomicField (G := G)) q) ∈
                Algebra.adjoin ℚ
                  {ζ : liftedCyclotomicField (G := G) |
                    ∃ n : ℕ, n ∈ ({m} : Set ℕ) ∧ n ≠ 0 ∧ ζ ^ n = 1}
            exact Subalgebra.algebraMap_mem _ q
        | add a b _ _ ha hb =>
            change
              (ULift.up a : liftedCyclotomicField (G := G)) + ULift.up b ∈
                Algebra.adjoin ℚ
                  {ζ : liftedCyclotomicField (G := G) |
                    ∃ n : ℕ, n ∈ ({m} : Set ℕ) ∧ n ≠ 0 ∧ ζ ^ n = 1}
            exact Subalgebra.add_mem _ ha hb
        | mul a b _ _ ha hb =>
            change
              (ULift.up a : liftedCyclotomicField (G := G)) * ULift.up b ∈
                Algebra.adjoin ℚ
                  {ζ : liftedCyclotomicField (G := G) |
                    ∃ n : ℕ, n ∈ ({m} : Set ℕ) ∧ n ≠ 0 ∧ ζ ^ n = 1}
            exact Subalgebra.mul_mem _ ha hb

/-- At the full cyclotomic field, Serre's arithmetic subgroup is trivial. -/
theorem gammaSubgroup_top_eq_bot_of_cyclotomic
    {L : Type u} [Field L] [NumberField L]
    [IsCyclotomicExtension {Monoid.exponent G} ℚ L] :
    Γ[(⊤ : IntermediateField ℚ L)](G) =
      (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) := by
  unfold Representation.gammaSubgroup
  rw [IntermediateField.fixingSubgroup_top]
  simpa using OrderIso.map_bot (galEquivZMod (Monoid.exponent G) L).mapSubgroup

local instance
    {L : Type u} [Field L] [NumberField L]
    [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
    (K : IntermediateField ℚ L) :
    DecidableEq { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H } :=
  Classical.decEq _

local instance
    {L : Type u} [Field L] [NumberField L]
    [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
    (K : IntermediateField ℚ L)
    (H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H })
    (x : R₀[↥K](H.1)) : Decidable (x ≠ 0) :=
  Classical.dec _

private theorem one_eq_sum_gammaElementary_finiteRepGrothendieckInduction_local
    {L : Type u} [Field L] [NumberField L]
    [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
    (K : IntermediateField ℚ L) :
    ∃ z : Π₀ H : {H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H}, R₀[↥K](H.1),
      (1 : R₀[↥K](G))
        = z.sum (fun H =>
            ⇑(Representation.Subgroup.finiteRepGrothendieckGroupInduction (↥K) H.1)) := by
  classical
  letI : DecidableEq { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H } :=
    Classical.decEq _
  letI (H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H })
      (x : R₀[↥K](H.1)) : Decidable (x ≠ 0) := Classical.dec _
  obtain ⟨χ, hχ⟩ :=
    gammaElementarySubgroupInductionOverField_surjective (K := K) (G := G) (L := L) 1
  set e : ∀ H : {H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H},
      R₀[↥K](H.1) ≃+ R[↥K](H.1) := fun H => finiteRepGrothendieckCharacterAddEquiv' with he
  let Ind₀ : (Π₀ H : {H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H}, R₀[↥K](H.1))
      →+ R₀[↥K](G) :=
    DFinsupp.sumAddHom (fun H => Representation.Subgroup.finiteRepGrothendieckGroupInduction (↥K) H.1)
  have sq : (finiteRepGrothendieckCharacter (↥K) G).comp Ind₀
      = (gammaElementarySubgroupInductionOverField (K := K) (Γ[K](G))).toAddMonoidHom.comp
          (DFinsupp.mapRange.addMonoidHom (fun H => (e H).toAddMonoidHom)) := by
    refine DFinsupp.addHom_ext (fun H c => ?_)
    simp only [AddMonoidHom.comp_apply, Ind₀, DFinsupp.sumAddHom_single,
      DFinsupp.mapRange.addMonoidHom_apply, DFinsupp.mapRange_single,
      LinearMap.toAddMonoidHom_coe, gammaElementarySubgroupInductionOverField_single]
    rw [finiteRepGrothendieckCharacter_subgroupInduction]
    rfl
  refine ⟨DFinsupp.mapRange (fun H => (e H).symm) (fun H => (e H).symm.map_zero) χ, ?_⟩
  apply (finiteRepGrothendieckCharacter_bijective' (K := ↥K) (G := G)).1
  rw [finiteRepGrothendieckCharacter_one]
  rw [(DFinsupp.sumAddHom_apply _ _).symm]
  have := congrFun (congrArg (fun f : _ →+ _ => f.toFun) sq)
    (DFinsupp.mapRange (fun H => (e H).symm) (fun H => (e H).symm.map_zero) χ)
  rw [show (finiteRepGrothendieckCharacter (↥K) G)
        (Ind₀ (DFinsupp.mapRange (fun H => (e H).symm) (fun H => (e H).symm.map_zero) χ))
      = gammaElementarySubgroupInductionOverField (K := K) (Γ[K](G))
          (DFinsupp.mapRange.addMonoidHom (fun H => (e H).toAddMonoidHom)
            (DFinsupp.mapRange (fun H => (e H).symm) (fun H => (e H).symm.map_zero) χ)) from this]
  rw [show DFinsupp.mapRange.addMonoidHom (fun H => (e H).toAddMonoidHom)
        (DFinsupp.mapRange (fun H => (e H).symm) (fun H => (e H).symm.map_zero) χ) = χ from ?_]
  · exact hχ.symm
  · refine DFinsupp.ext fun H => ?_
    rw [DFinsupp.mapRange.addMonoidHom_apply, DFinsupp.mapRange_apply, DFinsupp.mapRange_apply]
    exact (e H).apply_symm_apply (χ H)

/-- A sufficiently large characteristic-zero field receives the lifted full cyclotomic field of
the exponent of `G`. -/
noncomputable def liftedCyclotomicTopAlgHom_of_hasEnoughRoots
    {K : Type u} [Field K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    ↥(⊤ : IntermediateField ℚ (liftedCyclotomicField (G := G))) →ₐ[ℚ] K := by
  classical
  let m := Monoid.exponent G
  let L := liftedCyclotomicField (G := G)
  letI : NeZero m := Monoid.neZero_exponent_of_finite
  letI : IsCyclotomicExtension {m} ℚ L := liftedCyclotomicFieldCyclotomic (G := G)
  have hprim :
      ∀ n ∈ ({m} : Set ℕ), n ≠ 0 → ∃ r : K, IsPrimitiveRoot r n := by
    intro n hn _hn0
    rw [Set.mem_singleton_iff] at hn
    subst n
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K m
  let M : IntermediateField ℚ K :=
    IntermediateField.adjoin ℚ {x : K | ∃ n ∈ ({m} : Set ℕ), n ≠ 0 ∧ x ^ n = 1}
  let e : L ≃ₐ[ℚ] M :=
    Classical.choice
      (IsCyclotomicExtension.nonempty_algEquiv_adjoin_of_exists_isPrimitiveRoot
        (S := {m}) ℚ L K hprim)
  exact
    ((IsScalarTower.toAlgHom ℚ M K).comp e.toAlgHom).comp
      (IntermediateField.topEquiv (F := ℚ) (E := L)).toAlgHom

private theorem finiteRepGrothendieckScalarExtensionHom_one
    {F K : Type u} [Field F] [Field K] [Algebra F K] :
    finiteRepGrothendieckScalarExtensionHom F K G (1 : R₀[F](G)) = (1 : R₀[K](G)) := by
  rw [← finiteRepGrothendieckClass_trivial_eq_one (G := G) K,
    ← finiteRepGrothendieckClass_trivial_eq_one (G := G) F]
  exact finiteRepGrothendieckScalarExtensionHom_trivial_class (F := F) (k := K) (G := G)

/-- Over a sufficiently large characteristic-zero field, the unit of `R₀[K](G)` is an integral sum
of inductions from ordinary elementary subgroups. -/
theorem one_eq_sum_elementary_finiteRepGrothendieckInduction_of_hasEnoughRoots
    {K : Type u} [Field K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    ∃ (ι : Type (u + 1)) (_ : Fintype ι) (H : ι → Subgroup G)
      (_ : ∀ i, IsElementary (H i)),
        ∃ y : ∀ i, R₀[K](H i),
          (1 : R₀[K](G)) =
            ∑ i, Representation.Subgroup.finiteRepGrothendieckGroupInduction K (H i) (y i) := by
  classical
  let L := liftedCyclotomicField (G := G)
  let Ktop : IntermediateField ℚ L := ⊤
  letI : DecidableEq { H : Subgroup G // Subgroup.IsGammaElementary (Γ[Ktop](G)) H } :=
    Classical.decEq _
  obtain ⟨z, hz⟩ :=
    one_eq_sum_gammaElementary_finiteRepGrothendieckInduction_local (G := G) (L := L) Ktop
  let φ : ↥Ktop →ₐ[ℚ] K :=
    liftedCyclotomicTopAlgHom_of_hasEnoughRoots (G := G) (K := K)
  letI : Algebra ↥Ktop K := φ.toRingHom.toAlgebra
  let ι : Type u := { H : Subgroup G // Subgroup.IsGammaElementary (Γ[Ktop](G)) H }
  letI : Fintype ι := inferInstance
  have hz_fin :
      (1 : R₀[↥Ktop](G)) =
        ∑ H : ι,
          Representation.Subgroup.finiteRepGrothendieckGroupInduction (↥Ktop) H.1 (z H) := by
    calc
      (1 : R₀[↥Ktop](G)) =
          z.sum fun H ↦
            ⇑(Representation.Subgroup.finiteRepGrothendieckGroupInduction (↥Ktop) H.1) := by
            exact hz
      _ =
          ∑ H : ι,
            Representation.Subgroup.finiteRepGrothendieckGroupInduction (↥Ktop) H.1 (z H) := by
            exact
              DFinsupp.sum_eq_sum_fintype
                (v := z)
                (f := fun H yH ↦
                  Representation.Subgroup.finiteRepGrothendieckGroupInduction (↥Ktop) H.1 yH)
                (hf := fun H ↦ by simp)
  let ι' : Type (u + 1) := ULift.{u + 1, u} ι
  letI : Fintype ι' := Fintype.ofEquiv ι (Equiv.ulift.symm : ι ≃ ι')
  refine ⟨ι', inferInstance, (fun H : ι' ↦ H.down.1), ?_,
    (fun H : ι' ↦ finiteRepGrothendieckScalarExtensionHom (↥Ktop) K H.down.1 (z H.down)), ?_⟩
  · intro H
    have hΓbot : Γ[Ktop](G) = (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) := by
      simpa [Ktop, L] using
        gammaSubgroup_top_eq_bot_of_cyclotomic
          (G := G) (L := liftedCyclotomicField (G := G))
    exact
      (Subgroup.IsGammaElementary.bot_iff_isElementary H.down.1).1 <|
        by
          rw [← hΓbot]
          exact H.down.2
  · calc
      (1 : R₀[K](G)) =
          finiteRepGrothendieckScalarExtensionHom (↥Ktop) K G (1 : R₀[↥Ktop](G)) := by
            rw [finiteRepGrothendieckScalarExtensionHom_one (F := ↥Ktop) (K := K) (G := G)]
      _ =
          finiteRepGrothendieckScalarExtensionHom (↥Ktop) K G
            (∑ H : ι,
              Representation.Subgroup.finiteRepGrothendieckGroupInduction (↥Ktop) H.1 (z H)) := by
            rw [hz_fin]
      _ =
          ∑ H : ι,
            finiteRepGrothendieckScalarExtensionHom (↥Ktop) K G
              (Representation.Subgroup.finiteRepGrothendieckGroupInduction (↥Ktop) H.1 (z H)) := by
            simp [map_sum]
      _ =
          ∑ H : ι,
            Representation.Subgroup.finiteRepGrothendieckGroupInduction K H.1
              (finiteRepGrothendieckScalarExtensionHom (↥Ktop) K H.1 (z H)) := by
            refine Finset.sum_congr rfl ?_
            intro H _hH
            exact
              finiteRepGrothendieckScalarExtensionHom_subgroupInduction
                (F := ↥Ktop) (k := K) (G := G) H.1 (z H)
      _ =
          ∑ H : ι',
            Representation.Subgroup.finiteRepGrothendieckGroupInduction K H.down.1
              (finiteRepGrothendieckScalarExtensionHom (↥Ktop) K H.down.1 (z H.down)) := by
            exact
              Fintype.sum_equiv (Equiv.ulift.symm : ι ≃ ι') _ _
                (by intro H; rfl)

private theorem charP_residueField_of_liesOver_span_prime
    {p : ℕ} [Fact p.Prime]
    {L : Type u} [Field L] [NumberField L]
    {P : Ideal (𝓞 L)} [P.IsMaximal]
    (hPp : algebraMap ℤ (𝓞 L) (p : ℤ) ∈ P) :
    CharP (P.ResidueField) p := by
  have hpκ_nat : ((p : ℕ) : P.ResidueField) = 0 := by
    have hpκ_int : algebraMap ℤ P.ResidueField (p : ℤ) = 0 := by
      rw [IsScalarTower.algebraMap_apply ℤ (𝓞 L) P.ResidueField]
      exact (Ideal.algebraMap_residueField_eq_zero (I := P)).mpr hPp
    simpa using hpκ_int
  have hchar_dvd : ringChar P.ResidueField ∣ p := ringChar.dvd hpκ_nat
  rcases Nat.Prime.eq_one_or_self_of_dvd (Fact.out : Nat.Prime p)
      (ringChar P.ResidueField) hchar_dvd with hchar_one | hchar_p
  · exact (CharP.ringChar_ne_one (R := P.ResidueField) hchar_one).elim
  · exact ringChar.eq_iff.mp hchar_p

private theorem one_eq_sum_elementary_finiteRepGrothendieckInduction_of_algClosed_posChar
    {k : Type u} [Field k] [IsAlgClosed k]
    {p : ℕ} [Fact p.Prime] [CharP k p] :
    ∃ (ι : Type (u + 1)) (_ : Fintype ι) (H : ι → Subgroup G)
      (_ : ∀ i, IsElementary (H i)),
        ∃ y : ∀ i, R₀[k](H i),
          (1 : R₀[k](G)) =
            ∑ i, Representation.Subgroup.finiteRepGrothendieckGroupInduction k (H i) (y i) := by
  classical
  let L := liftedCyclotomicField (G := G)
  let O := 𝓞 L
  let Pℤ : Ideal ℤ := Ideal.span {(p : ℤ)}
  haveI : Pℤ.IsMaximal := by
    dsimp [Pℤ]
    infer_instance
  obtain ⟨P, hPmax, hPlies⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := ℤ) (S := O) Pℤ
  letI : P.IsMaximal := hPmax
  haveI : P.IsPrime := hPmax.isPrime
  have hPp : algebraMap ℤ O (p : ℤ) ∈ P := by
    have hpℤ : (p : ℤ) ∈ Pℤ := Ideal.mem_span_singleton_self (p : ℤ)
    have h_under : Pℤ = Ideal.under ℤ P := (Ideal.liesOver_iff P Pℤ).mp hPlies
    change algebraMap ℤ O (p : ℤ) ∈ P
    rw [h_under] at hpℤ
    simpa [Ideal.under] using hpℤ
  let A := Localization.AtPrime P
  have hP_ne_bot : P ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hPmax (NumberField.RingOfIntegers.not_isField L)
  letI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (A := O) hP_ne_bot A
  let units : ∀ y : P.primeCompl, IsUnit ((algebraMap O L) y) := by
    intro y
    have hy_ne : (y : O) ≠ 0 := by
      intro hy
      exact y.2 (hy.symm ▸ P.zero_mem)
    exact
      isUnit_iff_ne_zero.mpr
        ((map_ne_zero_iff (algebraMap O L) (IsFractionRing.injective O L)).mpr hy_ne)
  letI algA_L : Algebra A L :=
    (IsLocalization.lift (M := P.primeCompl) (S := A) units).toAlgebra
  haveI towerA_L : IsScalarTower O A L :=
    IsScalarTower.of_algebraMap_eq'
      (IsLocalization.lift_comp (M := P.primeCompl) (S := A) units).symm
  let fracA_L : IsFractionRing A L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl A L
  letI : IsFractionRing A L := fracA_L
  let Ktop : IntermediateField ℚ L := ⊤
  let eTop : ↥Ktop ≃ₐ[ℚ] L := IntermediateField.topEquiv
  letI algA_top : Algebra A ↥Ktop :=
    (eTop.symm.toRingHom.comp (algebraMap A L)).toAlgebra
  let eA : L ≃ₐ[A] ↥Ktop :=
    { eTop.symm.toRingEquiv with
      commutes' := by intro a; rfl }
  let fracA_top : IsFractionRing A ↥Ktop := IsFractionRing.of_algEquiv (R := A) eA
  letI : IsFractionRing A ↥Ktop := fracA_top
  obtain ⟨ι, hι, H, hHΓ, y, hunitκ⟩ :=
    gammaElementarySubgroupFiniteRepGrothendieckInduction_surjective
      (A := A) (G := G) (L := L) Ktop (1 : R₀[IsLocalRing.ResidueField A](G))
  letI : Fintype ι := hι
  let κ := IsLocalRing.ResidueField A
  have hκ_char : CharP κ p := by
    change CharP P.ResidueField p
    exact charP_residueField_of_liesOver_span_prime (p := p) (L := L) (P := P) hPp
  letI : CharP κ p := hκ_char
  letI : Algebra (ZMod p) κ := ZMod.algebra κ p
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  letI : Finite κ := by
    change Finite P.ResidueField
    haveI : Finite (O ⧸ P) := inferInstance
    exact
      Finite.of_surjective (algebraMap (O ⧸ P) P.ResidueField)
        (Ideal.bijective_algebraMap_quotient_residueField P).2
  haveI : Module.Finite (ZMod p) κ := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (ZMod p) κ := Algebra.IsAlgebraic.of_finite (ZMod p) κ
  let ε : κ →ₐ[ZMod p] k := IsAlgClosed.lift
  letI : Algebra κ k := ε.toRingHom.toAlgebra
  let ι' : Type (u + 1) := ULift.{u + 1, u} ι
  letI : Fintype ι' := Fintype.ofEquiv ι (Equiv.ulift.symm : ι ≃ ι')
  refine ⟨ι', inferInstance, (fun i : ι' ↦ H i.down), ?_,
    (fun i : ι' ↦ finiteRepGrothendieckScalarExtensionHom κ k (H i.down) (y i.down)), ?_⟩
  · intro i
    have hΓbot : Γ[Ktop](G) = (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) := by
      simpa [Ktop, L] using
        gammaSubgroup_top_eq_bot_of_cyclotomic
          (G := G) (L := liftedCyclotomicField (G := G))
    exact
      (Subgroup.IsGammaElementary.bot_iff_isElementary (H i.down)).1 <|
        by
          rw [← hΓbot]
          exact hHΓ i.down
  · calc
      (1 : R₀[k](G)) =
          finiteRepGrothendieckScalarExtensionHom κ k G (1 : R₀[κ](G)) := by
            rw [finiteRepGrothendieckScalarExtensionHom_one (F := κ) (K := k) (G := G)]
      _ =
          finiteRepGrothendieckScalarExtensionHom κ k G
            (∑ i,
              Representation.Subgroup.finiteRepGrothendieckGroupInduction κ (H i) (y i)) := by
            rw [hunitκ]
      _ =
          ∑ i,
            finiteRepGrothendieckScalarExtensionHom κ k G
              (Representation.Subgroup.finiteRepGrothendieckGroupInduction κ (H i) (y i)) := by
            simp [map_sum]
      _ =
          ∑ i,
            Representation.Subgroup.finiteRepGrothendieckGroupInduction k (H i)
              (finiteRepGrothendieckScalarExtensionHom κ k (H i) (y i)) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            exact
              finiteRepGrothendieckScalarExtensionHom_subgroupInduction
                (F := κ) (k := k) (G := G) (H i) (y i)
      _ =
          ∑ i : ι',
            Representation.Subgroup.finiteRepGrothendieckGroupInduction k (H i.down)
              (finiteRepGrothendieckScalarExtensionHom κ k (H i.down) (y i.down)) := by
            exact
              Fintype.sum_equiv (Equiv.ulift.symm : ι ≃ ι') _ _
                (by intro i; rfl)

private theorem exists_sum_of_elementary_inductions_of_unit
    {k : Type u} [Field k]
    (hunit :
      ∃ (ι : Type (u + 1)) (_ : Fintype ι) (H : ι → Subgroup G)
        (_ : ∀ i, IsElementary (H i)),
          ∃ y : ∀ i, R₀[k](H i),
            (1 : R₀[k](G)) =
              ∑ i, Representation.Subgroup.finiteRepGrothendieckGroupInduction k (H i) (y i))
    (x : R₀[k](G)) :
    ∃ (ι : Type (u + 1)) (_ : Fintype ι) (H : ι → Subgroup G)
      (_ : ∀ i, IsElementary (H i)),
        ∃ y : ∀ i, R₀[k](H i),
          x = ∑ i, Representation.Subgroup.finiteRepGrothendieckGroupInduction k (H i) (y i) := by
  classical
  obtain ⟨ι, hι, H, hH, y, hunit_sum⟩ := hunit
  letI : Fintype ι := hι
  refine ⟨ι, hι, H, hH,
    (fun i ↦ y i * Representation.Subgroup.finiteRepGrothendieckGroupRestriction k (H i) x), ?_⟩
  calc
    x = (1 : R₀[k](G)) * x := by rw [one_mul]
    _ =
        (∑ i, Representation.Subgroup.finiteRepGrothendieckGroupInduction k (H i) (y i)) *
          x := by
          rw [hunit_sum]
    _ =
        ∑ i, Representation.Subgroup.finiteRepGrothendieckGroupInduction k (H i) (y i) * x := by
          rw [Finset.sum_mul]
    _ =
        ∑ i, Representation.Subgroup.finiteRepGrothendieckGroupInduction k (H i)
          (y i * Representation.Subgroup.finiteRepGrothendieckGroupRestriction k (H i) x) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          exact Representation.finiteRepGrothendieckGroupInduction_mul (H i) (y i) x

/-- Brauer elementary induction over an algebraically closed coefficient field. -/
theorem algClosed_grothendieckClass_exists_sum_of_elementary_subgroup_inductions
    {k : Type u} [Field k] [IsAlgClosed k] (x : R₀[k](G)) :
    ∃ (ι : Type (u + 1)) (_ : Fintype ι) (H : ι → Subgroup G)
      (_ : ∀ i, IsElementary (H i)),
        ∃ y : ∀ i, R₀[k](H i),
          x = ∑ i, Representation.Subgroup.finiteRepGrothendieckGroupInduction k (H i) (y i) := by
  classical
  refine exists_sum_of_elementary_inductions_of_unit (G := G) ?_ x
  by_cases hchar0 : ringChar k = 0
  · letI : CharZero k := (CharP.ringChar_zero_iff_CharZero (R := k)).mp hchar0
    letI : HasEnoughRootsOfUnity k (Monoid.exponent G) :=
      IsSepClosed.hasEnoughRootsOfUnity k (Monoid.exponent G)
    exact
      one_eq_sum_elementary_finiteRepGrothendieckInduction_of_hasEnoughRoots
        (G := G) (K := k)
  · let p := ringChar k
    letI : CharP k p := ringChar.charP (R := k)
    have hp_ne_zero : p ≠ 0 := hchar0
    have hp_ne_one : p ≠ 1 := CharP.char_ne_one k p
    have hp_two_le : 2 ≤ p := by omega
    letI : Fact p.Prime := ⟨CharP.char_is_prime_of_two_le k p hp_two_le⟩
    exact
      one_eq_sum_elementary_finiteRepGrothendieckInduction_of_algClosed_posChar
        (G := G) (k := k) (p := p)

end

end Representation
