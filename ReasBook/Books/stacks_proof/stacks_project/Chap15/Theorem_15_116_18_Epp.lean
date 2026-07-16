import Mathlib
import stacks_proof.stacks_project.Chap15.Definition_15_112_1
import stacks_proof.stacks_project.Chap15.Lemma_15_112_5
import stacks_proof.stacks_project.Chap15.Lemma_15_115_2
import stacks_proof.stacks_project.Chap15.Lemma_15_115_4_Abhyankar_s_lemma
import stacks_proof.stacks_project.Chap15.Definition_15_112_7
import stacks_proof.stacks_project.Chap15.Definition_15_116_1
import stacks_proof.stacks_project.Chap15.Lemma_15_116_5

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v w x

section

/- Domain-style sampling for Theorem 15.116.18 (Epp):
- primary domain: Epp-style elimination of wild ramification for extensions of discrete valuation
  rings, organized around the chapter weak-solution owner;
- sampled owner declarations:
  `IsWeakSolutionFor`,
  `exists_ramificationEliminationSquare`,
  `exists_finite_extension_weakSolution_of_complete_of_residueField_pPowerIntersection`;
- best owner abstraction: this theorem is `source-facing`; its conclusion should remain the chapter
  owner `IsWeakSolutionFor A B K L K1`, while the Epp residue-field hypothesis stays as an
  explicit theorem hypothesis rather than a second public wrapper predicate;
- primitive-vs-derived split: the primitive data are the DVR extension `A ⊂ B`, the chosen
  fraction fields `K ⊂ L`, and the residue-field `p`-power intersection hypothesis; the weak
  solution itself is derived API through the owner `IsWeakSolutionFor`.

Source/core/bridge triage:
- `source-facing`: the existence theorem furnishing a finite weak solution under Epp's
  residue-field hypothesis;
- `core/canonical`: `IsWeakSolutionFor`,
  `exists_ramificationEliminationSquare`, and
  `exists_finite_extension_weakSolution_of_complete_of_residueField_pPowerIntersection`;
- `bridge/view`: the choice of finite extension `K₁ / K` witnessing the weak-solution property.
-/

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]

/-- Helper for Theorem 15.116.18 (Epp): the residue-field hypothesis is vacuous when the source
residue field has characteristic zero. -/
private theorem epp_hypothesis_of_residueCharZero
    (hchar0 : ringChar (ResidueField A) = 0) :
    ringChar (ResidueField A) ≠ 0 →
      ∀ x : ResidueField B,
        x ∈ ⋂ n : ℕ+, Set.range
          (fun y : ResidueField B ↦ y ^ (ringChar (ResidueField A) ^ (n : ℕ))) →
          IsSeparable (ResidueField A) x := by
  -- In residue characteristic zero the antecedent is contradictory, so the hypothesis is
  -- automatic.
  intro hcharpos x hx
  exact False.elim (hcharpos (by simpa [hchar0]))

/-- Helper for Theorem 15.116.18 (Epp): in residue characteristic zero every natural number is
prime to the residue characteristic. -/
private theorem primeToResidueCharacteristic_of_residueCharZero
    (hchar0 : ringChar (ResidueField A) = 0) (n : ℕ) :
    PrimeToResidueCharacteristic A n := by
  -- Any prime residue characteristic would force the residue field to have nonzero ring
  -- characteristic, contradicting `hchar0`.
  intro p _ _
  have hp_eq_zero : p = 0 := by
    calc
      p = ringChar (ResidueField A) := by
        symm
        simpa using (ringChar.eq (ResidueField A) p)
      _ = 0 := hchar0
  exact False.elim (Nat.Prime.ne_zero (Fact.out : Nat.Prime p) hp_eq_zero)

/-- Helper for Theorem 15.116.18 (Epp): algebraic residue-field extensions over residue
characteristic zero are separable. -/
private theorem residueField_isSeparable_of_residueCharZero
    {κ : Type*} [Field κ] [Algebra (ResidueField A) κ]
    [Algebra.IsAlgebraic (ResidueField A) κ]
    (hchar0 : ringChar (ResidueField A) = 0) :
    Algebra.IsSeparable (ResidueField A) κ := by
  -- Over a characteristic-zero field the base is perfect, so every algebraic extension is
  -- separable.
  letI : CharZero (ResidueField A) :=
    (CharP.ringChar_zero_iff_CharZero _).mp hchar0
  letI : PerfectField (ResidueField A) := PerfectField.ofCharZero
  let hsepOver : Algebra.IsSeparableOver (ResidueField A) κ :=
    Algebra.IsSeparableOver.of_perfectField
  exact Algebra.IsSeparableOver.isSeparable (F := ResidueField A) (E := κ) hsepOver

/-- Helper for Theorem 15.116.18 (Epp): in a separable characteristic-`p` extension, a `p`th root
of a base element already lies in the base field. -/
private theorem exists_pth_root_in_base_of_isSeparable
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]
    {p : ℕ} [Fact p.Prime] [CharP F p] [CharP E p] [Algebra.IsSeparable F E]
    {a : F} {y : E} (hy : y ^ p = algebraMap F E a) :
    ∃ x : F, x ^ p = a := by
  have hpow_mem : ∃ n : ℕ, y ^ p ^ n ∈ (algebraMap F E).range := by
    -- The displayed `p`th-power relation already witnesses that the simple extension generated by
    -- `y` is purely inseparable over `F`.
    refine ⟨1, ?_⟩
    refine ⟨a, ?_⟩
    simpa [hy, pow_one]
  haveI : IsPurelyInseparable F F⟮y⟯ := by
    rw [IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem (F := F) (E := E) p]
    simpa using hpow_mem
  have hy_sep : IsSeparable F y := Algebra.IsSeparable.isSeparable F y
  haveI : Algebra.IsSeparable F F⟮y⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F E).2 hy_sep
  have hadjoin_bot : F⟮y⟯ = (⊥ : IntermediateField F E) :=
    IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable (F := F) (E := E) F⟮y⟯
  have hy_mem : y ∈ (⊥ : IntermediateField F E) := by
    -- The simple extension collapses because it is both separable and purely inseparable.
    rw [← hadjoin_bot]
    exact IntermediateField.mem_adjoin_simple_self F y
  rcases (IntermediateField.mem_bot (F := F) (E := E)).mp hy_mem with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  -- Compare the displayed equality after rewriting `y` as the image of the recovered base point.
  apply FaithfulSMul.algebraMap_injective F E
  simpa [hx] using hy

/-- Helper for Theorem 15.116.18 (Epp): in a separable characteristic-`p` extension, a
`p^n`-power root of a base element descends inductively to the base field. -/
private theorem exists_pPower_root_in_base_of_isSeparable
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]
    {p : ℕ} [Fact p.Prime] [CharP F p] [CharP E p] [Algebra.IsSeparable F E]
    (n : ℕ) {a : F} {y : E} (hy : y ^ (p ^ n) = algebraMap F E a) :
    ∃ x : F, x ^ (p ^ n) = a := by
  induction n generalizing a y with
  | zero =>
      -- At exponent `1`, the displayed equality already says that `a` is its own root.
      refine ⟨a, by simp⟩
  | succ n ih =>
      let z : E := y ^ (p ^ n)
      have hz : z ^ p = algebraMap F E a := by
        -- Rewrite the displayed `p^(n + 1)`-power as a `p`th power of the `p^n`-power.
        simpa [z, Nat.pow_succ, pow_mul] using hy
      obtain ⟨b, hb⟩ :=
        exists_pth_root_in_base_of_isSeparable
          (F := F) (E := E) (p := p) hz
      have hz_map : z = algebraMap F E b := by
        -- Frobenius is injective on the field `E`, so equal `p`th powers have equal bases.
        apply (_root_.frobenius E p).injective
        simpa [hz, hb, map_pow]
      obtain ⟨c, hc⟩ := ih (a := b) (y := y) hz_map
      refine ⟨c, ?_⟩
      -- Reassemble the descended `p^n`-root into a descended `p^(n + 1)`-root.
      calc
        c ^ (p ^ Nat.succ n) = (c ^ (p ^ n)) ^ p := by
          rw [Nat.pow_succ, pow_mul]
        _ = b ^ p := by rw [hc]
        _ = a := hb

/-- Helper for Theorem 15.116.18 (Epp): the characteristic-zero branch is the source-faithful
uniformizer-root/Abhyankar construction. -/
private theorem exists_weakSolution_of_residueCharZero_tame_uniformizer_root
    (hchar0 : ringChar (ResidueField A) = 0) :
    ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsWeakSolutionFor A B K L K1 := by
  -- Route correction: the remaining characteristic-zero work is exactly the tame
  -- uniformizer-root witness from the source proof. The easy input needed later is that the
  -- ramification index is automatically prime to the residue characteristic.
  obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible A
  let e : ℕ := ramificationIndex A B
  have he_pos : 0 < e := by
    simpa [e] using
      (IsExtensionOfDiscreteValuationRings.ramificationIndex_pos (A := A) (B := B))
  have hprime :
      PrimeToResidueCharacteristic A e :=
    primeToResidueCharacteristic_of_residueCharZero
      (A := A) hchar0 e
  letI : Fact (Irreducible π) := ⟨hπirr⟩
  letI : NeZero e := ⟨Nat.ne_of_gt he_pos⟩
  let K1 := uniformizerRootExtension π e
  letI : Algebra K K1 := FractionRing.liftAlgebra A K1
  letI : IsScalarTower A K K1 := FractionRing.isScalarTower_liftAlgebra A K1
  letI : Module.Finite K K1 := by
    -- Compare the chosen fraction field `K` with the canonical fraction ring of `A`, then
    -- transport finiteness of the radical extension field across that equivalence.
    let e₁ : FractionRing A ≃+* K := (FractionRing.algEquiv A K).toRingEquiv
    let e₂ : K1 ≃+* K1 := RingEquiv.refl _
    letI : Module.Finite (FractionRing A) K1 := inferInstance
    let f : K1 ≃ₐ[A] K1 := AlgEquiv.refl
    have he :
        RingHom.comp (algebraMap K K1) ↑e₁ =
          RingHom.comp ↑e₂ (algebraMap (FractionRing A) K1) := by
      ext x
      simpa [e₁, e₂] using
        IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K) f x
    exact Module.Finite.of_equiv_equiv e₁ e₂ he
  letI : FiniteDimensional K K1 := inferInstance
  letI : IsIntegralClosure (uniformizerRootExtensionRing π e) A K1 :=
    uniformizerRootExtensionRing_isIntegralClosure
      (A := A) (π := π) (n := e) (hπ := hπirr) (hn := he_pos)
  let eInt : uniformizerRootExtensionRing π e ≃ₐ[A] integralClosure A K1 :=
    IsIntegralClosure.equiv A (uniformizerRootExtensionRing π e) K1 (integralClosure A K1)
  have hsep :
      Algebra.IsSeparable (ResidueField A) (ResidueField B) :=
    residueField_isSeparable_of_residueCharZero
      (A := A) (κ := ResidueField B) hchar0
  have hmapR1 :
      Ideal.map (algebraMap A (uniformizerRootExtensionRing π e)) (maximalIdeal A) =
        maximalIdeal (uniformizerRootExtensionRing π e) ^ e := by
    -- First read off the ramification index on the explicit Kummer ring from Lemma `15.115.2`.
    have hramR1 : ramificationIndex A (uniformizerRootExtensionRing π e) = e := by
      simpa [e] using
        (ramificationIndex_uniformizerRootExtensionRing
          (A := A) (π := π) (n := e) (hπ := hπirr) (hn := he_pos))
    exact
      (ramificationIndex_eq_iff (A := A) (B := uniformizerRootExtensionRing π e) e).mp hramR1 |>.2
  have hmapInt :
      Ideal.map (algebraMap A (integralClosure A K1)) (maximalIdeal A) =
        maximalIdeal (integralClosure A K1) ^ e := by
    -- Then transport the maximal-ideal power identity from the explicit model to the canonical
    -- integral closure used in `IsWeakSolutionFor`.
    calc
      Ideal.map (algebraMap A (integralClosure A K1)) (maximalIdeal A)
          = Ideal.map (eInt.toRingHom.comp (algebraMap A (uniformizerRootExtensionRing π e)))
              (maximalIdeal A) := by
                congr 1
                ext a
                exact (eInt.commutes a).symm
      _ = Ideal.map eInt.toRingHom
            (Ideal.map (algebraMap A (uniformizerRootExtensionRing π e)) (maximalIdeal A)) := by
            rw [Ideal.map_map]
      _ = Ideal.map eInt.toRingHom (maximalIdeal (uniformizerRootExtensionRing π e) ^ e) := by
            rw [hmapR1]
      _ = (Ideal.map eInt.toRingHom (maximalIdeal (uniformizerRootExtensionRing π e))) ^ e := by
            rw [Ideal.map_pow]
      _ = maximalIdeal (integralClosure A K1) ^ e := by
            rw [ringEquiv_map_maximalIdeal (e := eInt)]
  have hramInt : ramificationIndex A (integralClosure A K1) = e := by
    -- Repackage the transported maximal-ideal identity as the ramification index of the
    -- canonical integral-closure model.
    exact
      (ramificationIndex_eq_iff (A := A) (B := integralClosure A K1) e).mpr
        ⟨he_pos, hmapInt⟩
  refine ⟨K1, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [isWeakSolutionFor_iff_map_maximalIdeal]
  intro m hm n hn hnm
  letI : m.IsMaximal := hm
  letI : n.IsMaximal := hn
  letI : n.LiesOver m := hnm
  have hm_eq : m = maximalIdeal (integralClosure A K1) := IsLocalRing.eq_maximalIdeal m
  have hmul : ramificationIndex A B ∣ Ideal.ramificationIdx (maximalIdeal A) m := by
    -- Any maximal branch of the canonical integral closure is the unique maximal ideal, so the
    -- divisibility condition in Abhyankar's lemma is exactly the transported ramification identity.
    simpa [e, hm_eq, ramificationIndex, hramInt] using (dvd_refl e)
  have hfs :
      (Localization.localRingHom m n
          (algebraMap (integralClosure A K1)
            (integralClosure B ((L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1))))
          (n.over_def m)).formally_smooth_for_adic
        (maximalIdeal (Localization.AtPrime n)) :=
    formallySmoothForAdic_localization_branch_of_tame_and_dvd_ramificationIdx
      (A := A) (B := B) (K := K) (L := L) (K1 := K1) hsep hprime m n hmul
  -- Finally, formal smoothness on each localized branch implies weakly unramifiedness, which is
  -- exactly the branchwise equality required by `IsWeakSolutionFor`.
  exact
    (IsExtensionOfDiscreteValuationRings.weaklyUnramified_iff_map_maximalIdeal
      (A := Localization.AtPrime m) (B := Localization.AtPrime n)).mp
      ((formally_smooth_for_maximalIdeal_adic_iff_weakly_unramified_and_separable_residueField
        (A := Localization.AtPrime m) (B := Localization.AtPrime n)).mp hfs).1

/-- Helper for Theorem 15.116.18 (Epp): once the ramification-elimination square from
Lemma `15.116.5` admits a finite weak solution on the top edge, the descent clause returns a
finite weak solution for the original extension. -/
private theorem weakSolution_descends_from_ramification_square
    {Aprime : Type _} [CommRing Aprime] [IsDomain Aprime] [IsDiscreteValuationRing Aprime]
    [Algebra A Aprime] [IsExtensionOfDiscreteValuationRings A Aprime]
    {Bprime : Type _} [CommRing Bprime] [IsDomain Bprime] [IsDiscreteValuationRing Bprime]
    [Algebra B Bprime] [Algebra Aprime Bprime] [Algebra A Bprime]
    [IsScalarTower A Aprime Bprime] [IsScalarTower A B Bprime]
    [IsExtensionOfDiscreteValuationRings B Bprime]
    [IsExtensionOfDiscreteValuationRings Aprime Bprime]
    {Kprime : Type _} [Field Kprime] [Algebra Aprime Kprime] [IsFractionRing Aprime Kprime]
    [Algebra K Kprime] [Algebra A Kprime]
    [IsScalarTower A Aprime Kprime] [IsScalarTower A K Kprime]
    {Lprime : Type _} [Field Lprime] [Algebra Bprime Lprime] [IsFractionRing Bprime Lprime]
    [Algebra L Lprime] [Algebra B Lprime]
    [IsScalarTower B Bprime Lprime] [IsScalarTower B L Lprime]
    [Algebra Kprime Lprime] [Algebra Aprime Lprime]
    [IsScalarTower Aprime Bprime Lprime] [IsScalarTower Aprime Kprime Lprime]
    (hWeakDesc :
      (∃ (K1prime : Type (max _ _ _ _)) (_ : Field K1prime) (_ : Algebra Aprime K1prime)
          (_ : Algebra Kprime K1prime) (_ : IsScalarTower Aprime Kprime K1prime)
          (_ : FiniteDimensional Kprime K1prime),
          IsWeakSolutionFor Aprime Bprime Kprime Lprime K1prime) →
        ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
          (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
          IsWeakSolutionFor A B K L K1)
    (hSquare :
      ∃ (K1prime : Type (max _ _ _ _)) (_ : Field K1prime) (_ : Algebra Aprime K1prime)
        (_ : Algebra Kprime K1prime) (_ : IsScalarTower Aprime Kprime K1prime)
        (_ : FiniteDimensional Kprime K1prime),
        IsWeakSolutionFor Aprime Bprime Kprime Lprime K1prime) :
    ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsWeakSolutionFor A B K L K1 := by
  -- The square theorem already packages the exact descent statement needed in the source proof.
  exact hWeakDesc hSquare

/-- Helper for Theorem 15.116.18 (Epp): once a stable `p`-power intersection element in the top
residue field can be transported back to a stable element of the original residue field, and
separable original residue-field elements are known to land in the left separable closure, the
entire stable intersection lands in that image. -/
private theorem stable_pPowerIntersection_le_image_on_ramification_square
    {κAprime : Type _} [Field κAprime]
    {κBprime : Type _} [Field κBprime]
    [Algebra (ResidueField A) κAprime]
    [Algebra (ResidueField B) κBprime]
    [Algebra κAprime κBprime]
    [Algebra (ResidueField A) κBprime]
    [IsScalarTower (ResidueField A) κAprime κBprime]
    [IsScalarTower (ResidueField A) (ResidueField B) κBprime]
    (hsep :
      ∀ x : ResidueField B,
        x ∈ ⋂ n : ℕ+, Set.range
          (fun y : ResidueField B ↦ y ^ (ringChar (ResidueField A) ^ (n : ℕ))) →
          IsSeparable (ResidueField A) x)
    (htransport :
      ∀ x : κBprime,
        x ∈ ⋂ n : ℕ+, Set.range
          (fun y : κBprime ↦ y ^ (ringChar (ResidueField A) ^ (n : ℕ))) →
          ∃ b : ResidueField B,
            algebraMap (ResidueField B) κBprime b = x ∧
              b ∈ ⋂ n : ℕ+, Set.range
                (fun y : ResidueField B ↦ y ^ (ringChar (ResidueField A) ^ (n : ℕ))))
    (himage :
      ∀ b : ResidueField B,
        IsSeparable (ResidueField A) b →
          algebraMap (ResidueField B) κBprime b ∈ Set.range (algebraMap κAprime κBprime)) :
    (⋂ n : ℕ+, Set.range
      (fun y : κBprime ↦ y ^ (ringChar (ResidueField A) ^ (n : ℕ)))) ⊆
      (Set.range (algebraMap κAprime κBprime) : Set κBprime) := by
  intro x hx
  -- The source proof first transports the stable-intersection condition back to `ResidueField B`.
  rcases htransport x hx with ⟨b, rfl, hb⟩
  -- The original Epp hypothesis then makes `b` separable over `ResidueField A`.
  exact himage b (hsep b hb)

/-- Helper for Theorem 15.116.18 (Epp): if a stable `p^n`-power intersection element upstairs is
already known to come from `ResidueField B`, then its preimage still lies in the stable
intersection downstairs. -/
private theorem mem_stable_pPowerIntersection_of_map_eq
    {κBprime : Type _} [Field κBprime]
    [Algebra (ResidueField B) κBprime]
    {p : ℕ} [Fact p.Prime] [CharP (ResidueField B) p] [CharP κBprime p]
    [Algebra.IsSeparable (ResidueField B) κBprime]
    {b : ResidueField B} {x : κBprime}
    (hbx : algebraMap (ResidueField B) κBprime b = x)
    (hx : x ∈ ⋂ n : ℕ+, Set.range (fun y : κBprime ↦ y ^ (p ^ (n : ℕ)))) :
    b ∈ ⋂ n : ℕ+, Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ))) := by
  refine Set.mem_iInter.2 ?_
  intro n
  rcases Set.mem_iInter.1 hx n with ⟨y, hy⟩
  have hy_base : y ^ (p ^ (n : ℕ)) = algebraMap (ResidueField B) κBprime b := by
    simpa [hbx] using hy
  obtain ⟨c, hc⟩ :=
    exists_pPower_root_in_base_of_isSeparable
      (F := ResidueField B) (E := κBprime) (p := p) (n := (n : ℕ)) hy_base
  exact ⟨c, hc⟩

/-- Helper for Theorem 15.116.18 (Epp): a stable intersection element in the chosen separable
closure admits each compatible `p^n`-root already inside the simple extension it generates over
`ResidueField B`. -/
private theorem pPower_root_mem_adjoin_singleton_of_stable_sepClosure_root
    {κBprime : Type _} [Field κBprime]
    [Algebra (ResidueField B) κBprime]
    [IsSepClosure (ResidueField B) κBprime]
    {p : ℕ} [Fact p.Prime] [CharP (ResidueField B) p] [CharP κBprime p]
    (x : κBprime)
    (hx : x ∈ ⋂ n : ℕ+, Set.range (fun y : κBprime ↦ y ^ (p ^ (n : ℕ))))
    (n : ℕ+) :
    ∃ y : (ResidueField B)⟮x⟯,
      ((y : κBprime) ^ (p ^ (n : ℕ)) = x) := by
  let Fx : IntermediateField (ResidueField B) κBprime := (ResidueField B)⟮x⟯
  have hx_mem : x ∈ Fx := by
    -- The simple field generated by `x` contains `x` by construction.
    simpa [Fx] using IntermediateField.mem_adjoin_simple_self (ResidueField B) x
  rcases Set.mem_iInter.1 hx n with ⟨z, hz⟩
  have hz_base : z ^ (p ^ (n : ℕ)) = algebraMap Fx κBprime ⟨x, hx_mem⟩ := by
    -- Re-express the chosen ambient root as a root of the canonical base element of `Fx`.
    change z ^ (p ^ (n : ℕ)) = x
    simpa using hz
  have hx_sep : IsSeparable (ResidueField B) x := by
    exact Algebra.IsSeparable.isSeparable (ResidueField B) x
  haveI : Algebra.IsSeparable (ResidueField B) Fx := by
    simpa [Fx] using
      (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
        (ResidueField B) κBprime).2 hx_sep
  haveI : Algebra.IsSeparable Fx κBprime :=
    Algebra.IsSeparable.trans (ResidueField B) Fx κBprime
  obtain ⟨y, hy⟩ :=
    exists_pPower_root_in_base_of_isSeparable
      (F := Fx) (E := κBprime) (p := p) (n := (n : ℕ)) hz_base
  refine ⟨y, ?_⟩
  -- Mapping the descended root back to `κBprime` recovers the original element `x`.
  simpa using congrArg (algebraMap Fx κBprime) hy

/-- Helper for Theorem 15.116.18 (Epp): the image of a chosen separable closure of
`ResidueField A` inside a separably closed overfield is exactly the relative separable closure. -/
private theorem map_top_eq_separableClosure_of_sepClosure_tower
    {Aprime : Type _} [Field Aprime] [Algebra (ResidueField A) Aprime]
    [IsSepClosure (ResidueField A) Aprime]
    {κBprime : Type _} [Field κBprime] [Algebra Aprime κBprime]
    [Algebra (ResidueField A) κBprime]
    [IsScalarTower (ResidueField A) Aprime κBprime]
    [IsSepClosed κBprime] :
    (⊤ : IntermediateField (ResidueField A) Aprime).map
        (IsScalarTower.toAlgHom (ResidueField A) Aprime κBprime) =
      separableClosure (ResidueField A) κBprime := by
  -- The source proof uses the chosen separable closure only through its image inside the ambient
  -- separably closed field, so rewrite that image as the canonical relative separable closure.
  have hbot :
      separableClosure Aprime κBprime = (⊥ : IntermediateField Aprime κBprime) := by
    exact (IsSepClosed.separableClosure_eq_bot_iff (F := Aprime) (E := κBprime)).2 inferInstance
  have hmap :
      (separableClosure (ResidueField A) Aprime).map
          (IsScalarTower.toAlgHom (ResidueField A) Aprime κBprime) =
        separableClosure (ResidueField A) κBprime :=
    separableClosure.map_eq_of_separableClosure_eq_bot
      (F := ResidueField A) (E := Aprime) (K := κBprime) hbot
  have htop :
      separableClosure (ResidueField A) Aprime =
        (⊤ : IntermediateField (ResidueField A) Aprime) := by
    exact (separableClosure.eq_top_iff (F := ResidueField A) (E := Aprime)).2 inferInstance
  simpa [htop] using hmap

/-- Helper for Theorem 15.116.18 (Epp): in characteristic `p`, the `p^n`-power map is additive.
-/
private theorem add_pow_pPower
    {F : Type*} [CommSemiring F]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    (n : ℕ) (x y : F) :
    (x + y) ^ (p ^ n) = x ^ (p ^ n) + y ^ (p ^ n) := by
  induction n with
  | zero =>
      -- At exponent `1`, the displayed identity is tautological.
      simp
  | succ n ih =>
      -- Rewrite the `p^(n + 1)`-power as a `p`th power of the `p^n`-power and use Frobenius
      -- additivity once more.
      calc
        (x + y) ^ (p ^ Nat.succ n) = ((x + y) ^ (p ^ n)) ^ p := by
          rw [Nat.pow_succ, pow_mul]
        _ = (x ^ (p ^ n) + y ^ (p ^ n)) ^ p := by
          rw [ih]
        _ = (x ^ (p ^ n)) ^ p + (y ^ (p ^ n)) ^ p := by
          rw [add_pow_char]
        _ = x ^ (p ^ Nat.succ n) + y ^ (p ^ Nat.succ n) := by
          rw [Nat.pow_succ, pow_mul, pow_mul]

/-- Helper for Theorem 15.116.18 (Epp): the stable `p^n`-power intersection always contains `0`.
-/
private theorem zero_mem_stable_pPowerIntersection
    {F : Type*} [Field F]
    {p : ℕ} [Fact p.Prime] [CharP F p] :
    (0 : F) ∈ ⋂ n : ℕ+, Set.range (fun y : F ↦ y ^ (p ^ (n : ℕ))) := by
  -- Every `p^n`-power map sends `0` to `0`.
  refine Set.mem_iInter.2 ?_
  intro n
  exact ⟨0, by simp⟩

/-- Helper for Theorem 15.116.18 (Epp): the stable `p^n`-power intersection always contains `1`.
-/
private theorem one_mem_stable_pPowerIntersection
    {F : Type*} [Field F]
    {p : ℕ} [Fact p.Prime] [CharP F p] :
    (1 : F) ∈ ⋂ n : ℕ+, Set.range (fun y : F ↦ y ^ (p ^ (n : ℕ))) := by
  -- Every `p^n`-power map fixes `1`.
  refine Set.mem_iInter.2 ?_
  intro n
  exact ⟨1, by simp⟩

/-- Helper for Theorem 15.116.18 (Epp): the stable `p^n`-power intersection is closed under
addition. -/
private theorem add_mem_stable_pPowerIntersection
    {F : Type*} [Field F]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    {x y : F}
    (hx : x ∈ ⋂ n : ℕ+, Set.range (fun z : F ↦ z ^ (p ^ (n : ℕ))))
    (hy : y ∈ ⋂ n : ℕ+, Set.range (fun z : F ↦ z ^ (p ^ (n : ℕ)))) :
    x + y ∈ ⋂ n : ℕ+, Set.range (fun z : F ↦ z ^ (p ^ (n : ℕ))) := by
  -- Choose compatible `p^n`-roots of `x` and `y`; Frobenius additivity gives a root of `x + y`.
  refine Set.mem_iInter.2 ?_
  intro n
  rcases Set.mem_iInter.1 hx n with ⟨a, rfl⟩
  rcases Set.mem_iInter.1 hy n with ⟨b, rfl⟩
  refine ⟨a + b, ?_⟩
  simpa using add_pow_pPower (p := p) (n := (n : ℕ)) a b

/-- Helper for Theorem 15.116.18 (Epp): the stable `p^n`-power intersection is closed under
multiplication. -/
private theorem mul_mem_stable_pPowerIntersection
    {F : Type*} [Field F]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    {x y : F}
    (hx : x ∈ ⋂ n : ℕ+, Set.range (fun z : F ↦ z ^ (p ^ (n : ℕ))))
    (hy : y ∈ ⋂ n : ℕ+, Set.range (fun z : F ↦ z ^ (p ^ (n : ℕ)))) :
    x * y ∈ ⋂ n : ℕ+, Set.range (fun z : F ↦ z ^ (p ^ (n : ℕ))) := by
  -- Compatible roots multiply to a compatible root of the product.
  refine Set.mem_iInter.2 ?_
  intro n
  rcases Set.mem_iInter.1 hx n with ⟨a, rfl⟩
  rcases Set.mem_iInter.1 hy n with ⟨b, rfl⟩
  exact ⟨a * b, by simp [mul_pow]⟩

/-- Helper for Theorem 15.116.18 (Epp): the stable `p^n`-power intersection is closed under
inversion. -/
private theorem inv_mem_stable_pPowerIntersection
    {F : Type*} [Field F]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    {x : F}
    (hx : x ∈ ⋂ n : ℕ+, Set.range (fun z : F ↦ z ^ (p ^ (n : ℕ)))) :
    x⁻¹ ∈ ⋂ n : ℕ+, Set.range (fun z : F ↦ z ^ (p ^ (n : ℕ))) := by
  -- In a field, the inverse of a `p^n`-power is the `p^n`-power of the inverse.
  refine Set.mem_iInter.2 ?_
  intro n
  rcases Set.mem_iInter.1 hx n with ⟨a, rfl⟩
  exact ⟨a⁻¹, by simp [inv_pow]⟩

/-- Helper for Theorem 15.116.18 (Epp): the stable `p^n`-power intersection is closed under
negation. -/
private theorem neg_mem_stable_pPowerIntersection
    {F : Type*} [Field F]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    {x : F}
    (hx : x ∈ ⋂ n : ℕ+, Set.range (fun z : F ↦ z ^ (p ^ (n : ℕ)))) :
    -x ∈ ⋂ n : ℕ+, Set.range (fun z : F ↦ z ^ (p ^ (n : ℕ))) := by
  -- Choose compatible roots of `x`; Frobenius additivity rewrites the root of `0 = x + (-x)`
  -- into the desired root of `-x`.
  refine Set.mem_iInter.2 ?_
  intro n
  rcases Set.mem_iInter.1 hx n with ⟨a, rfl⟩
  refine ⟨-a, ?_⟩
  have hsum : a ^ (p ^ (n : ℕ)) + (-a) ^ (p ^ (n : ℕ)) = 0 := by
    simpa using add_pow_pPower (p := p) (n := (n : ℕ)) a (-a)
  have hneg :
      (-a) ^ (p ^ (n : ℕ)) = -(a ^ (p ^ (n : ℕ))) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_comm] using hsum
  simpa [hneg]

/-- Helper for Theorem 15.116.18 (Epp): the stable `p^n`-power intersection in a characteristic-`p`
field forms a subfield. -/
private def stable_pPowerIntersection_subfield
    (F : Type*) [Field F]
    (p : ℕ) [Fact p.Prime] [CharP F p] :
    Subfield F :=
  { carrier := ⋂ n : ℕ+, Set.range (fun y : F ↦ y ^ (p ^ (n : ℕ)))
    zero_mem' := zero_mem_stable_pPowerIntersection (F := F) (p := p)
    one_mem' := one_mem_stable_pPowerIntersection (F := F) (p := p)
    add_mem' := fun ha hb ↦
      add_mem_stable_pPowerIntersection (F := F) (p := p) ha hb
    neg_mem' := fun ha ↦
      neg_mem_stable_pPowerIntersection (F := F) (p := p) ha
    mul_mem' := fun ha hb ↦
      mul_mem_stable_pPowerIntersection (F := F) (p := p) ha hb
    inv_mem' := fun ha ↦
      inv_mem_stable_pPowerIntersection (F := F) (p := p) ha }

/-- Helper for Theorem 15.116.18 (Epp): every stable-intersection element has a `p`th root that
still lies in the stable intersection. -/
private theorem exists_pth_root_mem_stable_pPowerIntersection
    {F : Type*} [Field F]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    {x : F}
    (hx : x ∈ ⋂ n : ℕ+, Set.range (fun z : F ↦ z ^ (p ^ (n : ℕ)))) :
    ∃ y : F, y ^ p = x ∧ y ∈ ⋂ n : ℕ+, Set.range (fun z : F ↦ z ^ (p ^ (n : ℕ))) := by
  rcases Set.mem_iInter.1 hx (1 : ℕ+) with ⟨y, hy⟩
  refine ⟨y, ?_, ?_⟩
  · -- The first-stage witness is already a `p`th root.
    simpa using hy
  · -- Compatibility of deeper roots and injectivity of Frobenius keep that chosen `p`th root
    -- inside the stable intersection.
    refine Set.mem_iInter.2 ?_
    intro n
    rcases Set.mem_iInter.1 hx (Nat.succPNat (n : ℕ)) with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hy_pow : y ^ p = x := by
      simpa using hy
    have hz_pow : (z ^ (p ^ (n : ℕ))) ^ p = x := by
      calc
        (z ^ (p ^ (n : ℕ))) ^ p = z ^ ((p ^ (n : ℕ)) * p) := by
          rw [pow_mul]
        _ = z ^ (p ^ Nat.succ (n : ℕ)) := by
          rw [Nat.pow_succ]
        _ = x := by
          simpa using hz
    have hy_eq : y = z ^ (p ^ (n : ℕ)) := by
      apply (_root_.frobenius F p).injective
      simpa [frobenius_def, hy_pow, hz_pow]
    simpa [hy_eq]

/-- Helper for Theorem 15.116.18 (Epp): the stable-intersection subfield is perfect, because the
Frobenius map is surjective on it. -/
private theorem stable_pPowerIntersection_subfield_perfectField
    {F : Type*} [Field F]
    {p : ℕ} [Fact p.Prime] [CharP F p] :
    PerfectField (stable_pPowerIntersection_subfield F p) := by
  let k := stable_pPowerIntersection_subfield F p
  have hroot : ∀ x : k, ∃ y : k, y ^ p = x := by
    intro x
    rcases exists_pth_root_mem_stable_pPowerIntersection (F := F) (p := p) x.property with
      ⟨y, hy, hyStable⟩
    refine ⟨⟨y, hyStable⟩, ?_⟩
    ext
    simpa using hy
  letI : PerfectRing k p := PerfectRing.ofSurjective k p hroot
  exact PerfectRing.toPerfectField k p

/-- Helper for Theorem 15.116.18 (Epp): after passing to separable closures, the remaining
residue-field task is the direct inclusion of the stable `p^n`-power intersection upstairs into
the image of the left separable closure. -/
private theorem stable_pPowerIntersection_le_image_of_sepClosure_tower
    {Aprime : Type _} [Field Aprime] [Algebra (ResidueField A) Aprime]
    [IsSepClosure (ResidueField A) Aprime]
    {κBprime : Type _} [Field κBprime]
    [Algebra (ResidueField B) κBprime] [Algebra Aprime κBprime]
    [Algebra (ResidueField A) κBprime]
    [IsScalarTower (ResidueField A) Aprime κBprime]
    [IsScalarTower (ResidueField A) (ResidueField B) κBprime]
    [IsSepClosure (ResidueField B) κBprime]
    {p : ℕ} [Fact p.Prime] [CharP (ResidueField A) p] [CharP (ResidueField B) p]
    [CharP κBprime p]
    (hsep :
      ∀ x : ResidueField B,
        x ∈ ⋂ n : ℕ+, Set.range
          (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ))) →
          IsSeparable (ResidueField A) x) :
    (⋂ n : ℕ+, Set.range
      (fun y : κBprime ↦ y ^ (p ^ (n : ℕ)))) ⊆
      (Set.range (algebraMap Aprime κBprime) : Set κBprime) := by
  -- Route correction: the earlier transport-to-`ResidueField B` statement is false in general
  -- (for example over perfect residue fields). The source proof only needs this direct inclusion
  -- after passing to separable closures.
  -- TODO: the finite simple-extension descent is now available via
  -- `pPower_root_mem_adjoin_singleton_of_stable_sepClosure_root`. The remaining blocker is the
  -- Frobenius/minimal-polynomial comparison that turns those descended roots into coefficientwise
  -- stable-intersection membership for `minpoly (ResidueField B) x`; after that, apply `hsep`
  -- coefficientwise and rewrite through `map_top_eq_separableClosure_of_sepClosure_tower`.
  sorry

/-- Helper for Theorem 15.116.18 (Epp): a separable residue-field element of `ResidueField B`
maps into the image of the chosen separable closure of `ResidueField A`. -/
private theorem mem_image_of_isSeparable_of_sepClosure_tower
    {Aprime : Type _} [Field Aprime] [Algebra (ResidueField A) Aprime]
    [IsSepClosure (ResidueField A) Aprime]
    {κBprime : Type _} [Field κBprime]
    [Algebra (ResidueField B) κBprime] [Algebra Aprime κBprime]
    [Algebra (ResidueField A) κBprime]
    [IsScalarTower (ResidueField A) Aprime κBprime]
    [IsScalarTower (ResidueField A) (ResidueField B) κBprime]
    [IsSepClosure (ResidueField B) κBprime]
    (b : ResidueField B) (hb : IsSeparable (ResidueField A) b) :
    algebraMap (ResidueField B) κBprime b ∈ Set.range (algebraMap Aprime κBprime) := by
  let x : κBprime := algebraMap (ResidueField B) κBprime b
  have hx_sep : IsSeparable (ResidueField A) x := by
    -- First map the separable element into the ambient separably closed field.
    exact
      hb.map
        (IsScalarTower.toAlgHom (ResidueField A) (ResidueField B) κBprime)
        (IsScalarTower.toAlgHom (ResidueField A) (ResidueField B) κBprime).injective
  have hx_mem : x ∈ separableClosure (ResidueField A) κBprime := by
    -- Inside `κBprime`, separability over `ResidueField A` is exactly membership in the relative
    -- separable closure.
    exact mem_separableClosure_iff.2 hx_sep
  have hx_map :
      x ∈ (⊤ : IntermediateField (ResidueField A) Aprime).map
        (IsScalarTower.toAlgHom (ResidueField A) Aprime κBprime) := by
    -- Replace the image of the chosen separable closure by the canonical relative one.
    rw [map_top_eq_separableClosure_of_sepClosure_tower
      (A := A) (Aprime := Aprime) (κBprime := κBprime)]
    exact hx_mem
  -- Unpack membership in the image of `Aprime` to the required `Set.range` statement.
  rw [IntermediateField.mem_map] at hx_map
  rcases hx_map with ⟨a, -, ha⟩
  exact ⟨a, by simpa [x] using ha⟩

/-- Helper for Theorem 15.116.18 (Epp): after the ramification-elimination square from
Lemma `15.116.5`, the positive-characteristic branch reduces to the source-faithful
intersection-field/Cohen construction on `Aprime → Bprime`. -/
private theorem exists_square_weakSolution_of_positive_residueChar_after_intersection_transport
    {Aprime : Type _} [CommRing Aprime] [IsDomain Aprime] [IsDiscreteValuationRing Aprime]
    [Algebra A Aprime] [IsExtensionOfDiscreteValuationRings A Aprime]
    {Bprime : Type _} [CommRing Bprime] [IsDomain Bprime] [IsDiscreteValuationRing Bprime]
    [Algebra B Bprime] [Algebra Aprime Bprime] [Algebra A Bprime]
    [IsScalarTower A Aprime Bprime] [IsScalarTower A B Bprime]
    [IsExtensionOfDiscreteValuationRings B Bprime]
    [IsExtensionOfDiscreteValuationRings Aprime Bprime]
    {Kprime : Type _} [Field Kprime] [Algebra Aprime Kprime] [IsFractionRing Aprime Kprime]
    [Algebra K Kprime] [Algebra A Kprime]
    [IsScalarTower A Aprime Kprime] [IsScalarTower A K Kprime]
    {Lprime : Type _} [Field Lprime] [Algebra Bprime Lprime] [IsFractionRing Bprime Lprime]
    [Algebra L Lprime] [Algebra B Lprime]
    [IsScalarTower B Bprime Lprime] [IsScalarTower B L Lprime]
    [Algebra Kprime Lprime] [Algebra Aprime Lprime]
    [IsScalarTower Aprime Bprime Lprime] [IsScalarTower Aprime Kprime Lprime]
    [Algebra (ResidueField A) (ResidueField Aprime)]
    [Algebra (ResidueField B) (ResidueField Bprime)]
    [Algebra (ResidueField Aprime) (ResidueField Bprime)]
    [Algebra (ResidueField A) (ResidueField Bprime)]
    [IsScalarTower (ResidueField A) (ResidueField Aprime) (ResidueField Bprime)]
    [IsScalarTower (ResidueField A) (ResidueField B) (ResidueField Bprime)]
    (hsep :
      ringChar (ResidueField A) ≠ 0 →
        ∀ x : ResidueField B,
          x ∈ ⋂ n : ℕ+, Set.range
            (fun y : ResidueField B ↦ y ^ (ringChar (ResidueField A) ^ (n : ℕ))) →
            IsSeparable (ResidueField A) x)
    (hchar : ringChar (ResidueField A) ≠ 0)
    (hKprimeAlg : Algebra.IsAlgebraic K Kprime)
    (hKprimeSep : Algebra.IsSeparable K Kprime)
    (hLprimeAlg : Algebra.IsAlgebraic L Lprime)
    (hLprimeSep : Algebra.IsSeparable L Lprime)
    (hAprimeSepClosure : IsSepClosure (ResidueField A) (ResidueField Aprime))
    (hBprimeSepClosure : IsSepClosure (ResidueField B) (ResidueField Bprime)) :
    ∃ (K1prime : Type (max _ _ _ _)) (_ : Field K1prime) (_ : Algebra Aprime K1prime)
      (_ : Algebra Kprime K1prime) (_ : IsScalarTower Aprime Kprime K1prime)
      (_ : FiniteDimensional Kprime K1prime),
      IsWeakSolutionFor Aprime Bprime Kprime Lprime K1prime := by
  -- Route correction: the first positive-characteristic input is the original Epp hypothesis on
  -- `ResidueField B`; the remaining source-faithful work must transport stable-intersection
  -- elements across the separable-closure square before running the completion/Cohen reduction.
  let p : ℕ := ringChar (ResidueField A)
  have hp : p.Prime := by
    exact CharP.char_prime_of_ne_zero (ResidueField A) hchar
  letI : Fact p.Prime := ⟨hp⟩
  letI : CharP (ResidueField A) p := ringChar.charP (ResidueField A)
  letI : CharP (ResidueField B) p :=
    CharP.of_ringHom_of_ne_zero
      (algebraMap (ResidueField A) (ResidueField B)) p hp.ne_zero
  letI : CharP (ResidueField Bprime) p :=
    CharP.of_ringHom_of_ne_zero
      (algebraMap (ResidueField A) (ResidueField Bprime)) p hp.ne_zero
  letI : IsSepClosure (ResidueField A) (ResidueField Aprime) := hAprimeSepClosure
  letI : IsSepClosure (ResidueField B) (ResidueField Bprime) := hBprimeSepClosure
  have hbaseStable :
      ∀ x : ResidueField B,
        x ∈ ⋂ n : ℕ+, Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ))) →
          IsSeparable (ResidueField A) x :=
    by simpa [p] using hsep hchar
  have hStableImage :
      (⋂ n : ℕ+, Set.range
        (fun y : ResidueField Bprime ↦ y ^ (ringChar (ResidueField A) ^ (n : ℕ)))) ⊆
        (Set.range
          (algebraMap (ResidueField Aprime) (ResidueField Bprime)) :
            Set (ResidueField Bprime)) := by
    -- Route correction: after passing to separable closures, the stable intersection has to be
    -- placed directly in the image of `ResidueField Aprime`; transporting it back through
    -- `ResidueField B` is not valid in general.
    simpa [p] using
      stable_pPowerIntersection_le_image_of_sepClosure_tower
        (A := A) (B := B)
        (Aprime := ResidueField Aprime) (κBprime := ResidueField Bprime)
        (p := p) hbaseStable
  let k : Subfield (ResidueField Bprime) :=
    stable_pPowerIntersection_subfield (ResidueField Bprime) p
  letI : PerfectField k :=
    stable_pPowerIntersection_subfield_perfectField
      (F := ResidueField Bprime) (p := p)
  have hk_lift :
      ∀ x : k,
        ∃ a : ResidueField Aprime,
          algebraMap (ResidueField Aprime) (ResidueField Bprime) a = x := by
    intro x
    rcases hStableImage x.property with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    exact ha
  let _ := hbaseStable
  let _ := hStableImage
  let _ := k
  let _ := hk_lift
  let _ := hKprimeAlg
  let _ := hKprimeSep
  let _ := hLprimeAlg
  let _ := hLprimeSep
  let _ := hAprimeSepClosure
  let _ := hBprimeSepClosure
  -- TODO: the residue-field object `k`, its perfectness, and the pointwise factorization
  -- `k → ResidueField Aprime → ResidueField Bprime` are now explicit. The remaining
  -- source-faithful blocker is the completion/Cohen packaging that upgrades these pointwise lifts
  -- to the equal-residue-field complete DVR setup needed for Lemma `15.116.17`, and then
  -- descends that witness through the ramification square.
  sorry

-- Proof sketch: if `ResidueField A` has characteristic `0`, the hypothesis is vacuous and one
-- applies the prime-to-residue-characteristic case handled earlier in the chapter. In positive
-- characteristic, use Lemma `15.116.5` to pass to separably closed residue fields, then the
-- completion and Cohen-structure reductions from the textbook proof reduce the problem to
-- Lemma `15.116.17`, which yields the required finite weak solution.
/-- Theorem 15.116.18 (Epp): let `A ⊆ B` be an extension of discrete valuation rings with
fraction fields `K ⊂ L`. Assume that whenever `ResidueField A` has positive characteristic, every
element of the stable intersection of the `p^n`-power subsets of `ResidueField B` is separable
over `ResidueField A`, where `p = ringChar (ResidueField A)`; algebraicity is then a derived
consequence of separability. Then there exists a finite extension `K₁ / K` which is a weak
solution for `A → B`. -/
@[stacks 09F9]
theorem exists_finite_extension_weakSolution_of_epp_hypothesis
    (hsep :
      ringChar (ResidueField A) ≠ 0 →
        ∀ x : ResidueField B,
          x ∈ ⋂ n : ℕ+, Set.range
            (fun y : ResidueField B ↦ y ^ (ringChar (ResidueField A) ^ (n : ℕ))) →
            IsSeparable (ResidueField A) x) :
    ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsWeakSolutionFor A B K L K1 := by
  by_cases hchar0 : ringChar (ResidueField A) = 0
  · -- Proof comment: in characteristic zero the Epp hypothesis is automatic, so the remaining
    -- work is exactly the tame/Abhyankar construction from the source proof.
    exact
      exists_weakSolution_of_residueCharZero_tame_uniformizer_root
        (A := A) (B := B) (K := K) (L := L) hchar0
  · -- Proof comment: first pass to the ramification-elimination square from Lemma `15.116.5`.
    rcases
      exists_ramificationEliminationSquare
        (A := A) (B := B) (K := K) (L := L) with
      ⟨Aprime, _, _, _, _, _, Bprime, _, _, _, _, _, _, _, _, _, _,
        Kprime, _, _, _, _, _, _, _, Lprime, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, _, hKprimeAlg, hKprimeSep, hLprimeAlg, hLprimeSep,
        hAprimeSepClosure, hBprimeSepClosure, hWeakDesc, _, _⟩
    -- Proof comment: the positive-characteristic branch now stops exactly at the square witness
    -- required by the descent clause. This isolates the remaining source-faithful work in one
    -- local frontier instead of mixing it with the descent step.
    have hSquare :
        ∃ (K1prime : Type (max _ _ _ _)) (_ : Field K1prime) (_ : Algebra Aprime K1prime)
          (_ : Algebra Kprime K1prime) (_ : IsScalarTower Aprime Kprime K1prime)
          (_ : FiniteDimensional Kprime K1prime),
          IsWeakSolutionFor Aprime Bprime Kprime Lprime K1prime := by
      exact
        exists_square_weakSolution_of_positive_residueChar_after_intersection_transport
          (A := A) (B := B) (K := K) (L := L)
          (Aprime := Aprime) (Bprime := Bprime) (Kprime := Kprime) (Lprime := Lprime)
          hsep hchar0 hKprimeAlg hKprimeSep hLprimeAlg hLprimeSep
          hAprimeSepClosure hBprimeSepClosure
    -- Proof comment: once the square witness is available, the ramification-elimination square
    -- descends it back to the original DVR extension.
    exact
      weakSolution_descends_from_ramification_square
        (A := A) (B := B) (K := K) (L := L)
        (hWeakDesc := hWeakDesc) hSquare

end
