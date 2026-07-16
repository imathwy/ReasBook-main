import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_2_3.LocalTraceVanishing

noncomputable section

universe u

open scoped MonoidAlgebra Representation
open scoped Pointwise
open CategoryTheory

namespace Representation

section SwanExercise

namespace FiniteProjectiveGroupAlgebraModule

variable (Λ : Type u) [CommRing Λ]
variable (F : Type u) [Field F] [Algebra Λ F]
variable (G : Type u) [Group G]
variable [IsDedekindDomain Λ] [IsFractionRing Λ F] [Finite G]

/-- Helper for Exercise 16-16.2-3: comparison data between a localized projective owner and a
complete local projective owner packages exactly the transport needed to descend the forward
range theorem back to the localized generic fiber. -/
structure LocalizedCompleteProjectiveComparisonData
    {p : ℕ} [Fact p.Prime]
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p)
    [Algebra (Localization.AtPrime (M.1.asIdeal)) F]
    [IsScalarTower Λ (Localization.AtPrime (M.1.asIdeal)) F]
    (Q : FiniteProjectiveGroupAlgebraModule (Localization.AtPrime (M.1.asIdeal)) G) where
  Ahat : Type u
  [instCommRingAhat : CommRing Ahat]
  [instLocalAhat : IsLocalRing Ahat]
  [instHenselianAhat : HenselianLocalRing Ahat]
  [instNoetherianAhat : IsNoetherianRing Ahat]
  [instAdicCompleteAhat : IsAdicComplete (IsLocalRing.maximalIdeal Ahat) Ahat]
  Khat : Type u
  [instFieldKhat : Field Khat]
  [instAlgebraAhatKhat : Algebra Ahat Khat]
  Qhat : FiniteProjectiveGroupAlgebraModule Ahat G
  fieldMap : F →+* Khat
  fieldMap_injective : Function.Injective fieldMap
  character_eq :
    ∀ g : G, fieldMap ((Q.scalarExtension F).character g) =
      (Qhat.scalarExtension Khat).character g
  forwardRange :
    ∀ {x : R₀[Khat](G)},
      x ∈
        (projectiveGrothendieckScalarExtensionHom Ahat Khat :
          P₀[IsLocalRing.ResidueField Ahat](G) →+ R₀[Khat](G)).range →
      ∀ h : G, ¬ IsPRegular p h →
        (finiteRepGrothendieckCharacter Khat G x : G → Khat) h = 0

/-- Helper for Exercise 16-16.2-3: pure completion transport data records the completed
coefficient ring, completed generic field, completed projective owner, and the character
comparison, but does not include the forward range-to-character theorem. -/
structure LocalizedCompleteProjectiveTransportData
    {p : ℕ} [Fact p.Prime]
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p)
    [Algebra (Localization.AtPrime (M.1.asIdeal)) F]
    [IsScalarTower Λ (Localization.AtPrime (M.1.asIdeal)) F]
    (Q : FiniteProjectiveGroupAlgebraModule (Localization.AtPrime (M.1.asIdeal)) G) where
  Ahat : Type u
  [instCommRingAhat : CommRing Ahat]
  [instLocalAhat : IsLocalRing Ahat]
  [instHenselianAhat : HenselianLocalRing Ahat]
  [instNoetherianAhat : IsNoetherianRing Ahat]
  [instAdicCompleteAhat : IsAdicComplete (IsLocalRing.maximalIdeal Ahat) Ahat]
  Khat : Type u
  [instFieldKhat : Field Khat]
  [instAlgebraAhatKhat : Algebra Ahat Khat]
  Qhat : FiniteProjectiveGroupAlgebraModule Ahat G
  fieldMap : F →+* Khat
  fieldMap_injective : Function.Injective fieldMap
  character_eq :
    ∀ g : G, fieldMap ((Q.scalarExtension F).character g) =
      (Qhat.scalarExtension Khat).character g

/-- Helper for Exercise 16-16.2-3: adding an acyclic forward range-to-character theorem to
pure completion transport data gives the completed-local comparison record. -/
theorem localizedCompleteProjectiveComparisonData_of_transportData
    {p : ℕ} [Fact p.Prime]
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p)
    [Algebra (Localization.AtPrime (M.1.asIdeal)) F]
    [IsScalarTower Λ (Localization.AtPrime (M.1.asIdeal)) F]
    (Q : FiniteProjectiveGroupAlgebraModule (Localization.AtPrime (M.1.asIdeal)) G)
    (D : LocalizedCompleteProjectiveTransportData (Λ := Λ) (F := F) (G := G) M Q)
    (hforward :
      letI : CommRing D.Ahat := D.instCommRingAhat
      letI : IsLocalRing D.Ahat := D.instLocalAhat
      letI : HenselianLocalRing D.Ahat := D.instHenselianAhat
      letI : IsNoetherianRing D.Ahat := D.instNoetherianAhat
      letI : IsAdicComplete (IsLocalRing.maximalIdeal D.Ahat) D.Ahat :=
        D.instAdicCompleteAhat
      letI : Field D.Khat := D.instFieldKhat
      letI : Algebra D.Ahat D.Khat := D.instAlgebraAhatKhat
      ∀ {x : R₀[D.Khat](G)},
        x ∈
          (projectiveGrothendieckScalarExtensionHom D.Ahat D.Khat :
            P₀[IsLocalRing.ResidueField D.Ahat](G) →+ R₀[D.Khat](G)).range →
        ∀ h : G, ¬ IsPRegular p h →
          (finiteRepGrothendieckCharacter D.Khat G x : G → D.Khat) h = 0) :
    Nonempty
      (LocalizedCompleteProjectiveComparisonData (Λ := Λ) (F := F) (G := G) M Q) := by
  -- Install the transport fields as instances so the comparison record has the same completed
  -- coefficient data as the pure transport package.
  letI : CommRing D.Ahat := D.instCommRingAhat
  letI : IsLocalRing D.Ahat := D.instLocalAhat
  letI : HenselianLocalRing D.Ahat := D.instHenselianAhat
  letI : IsNoetherianRing D.Ahat := D.instNoetherianAhat
  letI : IsAdicComplete (IsLocalRing.maximalIdeal D.Ahat) D.Ahat :=
    D.instAdicCompleteAhat
  letI : Field D.Khat := D.instFieldKhat
  letI : Algebra D.Ahat D.Khat := D.instAlgebraAhatKhat
  -- The only extra field in the comparison record is the forward theorem.
  exact ⟨{
    Ahat := D.Ahat
    Khat := D.Khat
    Qhat := D.Qhat
    fieldMap := D.fieldMap
    fieldMap_injective := D.fieldMap_injective
    character_eq := D.character_eq
    forwardRange := hforward
  }⟩

/-- Helper for Exercise 16-16.2-3: completed-local comparison data descends Serre's forward
range character vanishing to the original localized generic-fiber character. -/
theorem localizationProjective_character_eq_zero_on_pSingular_of_completeComparison
    {p : ℕ} [Fact p.Prime]
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p)
    [Algebra (Localization.AtPrime (M.1.asIdeal)) F]
    [IsScalarTower Λ (Localization.AtPrime (M.1.asIdeal)) F]
    (Q : FiniteProjectiveGroupAlgebraModule (Localization.AtPrime (M.1.asIdeal)) G)
    (D : LocalizedCompleteProjectiveComparisonData (Λ := Λ) (F := F) (G := G) M Q)
    (g : G) (hg : ¬ IsPRegular p g) :
    (Q.scalarExtension F).character g = 0 := by
  -- The comparison owner is complete local, so the supplied forward theorem applies to its
  -- actual projective scalar-extension class.
  letI : CommRing D.Ahat := D.instCommRingAhat
  letI : IsLocalRing D.Ahat := D.instLocalAhat
  letI : HenselianLocalRing D.Ahat := D.instHenselianAhat
  letI : IsNoetherianRing D.Ahat := D.instNoetherianAhat
  letI : IsAdicComplete (IsLocalRing.maximalIdeal D.Ahat) D.Ahat :=
    D.instAdicCompleteAhat
  letI : Field D.Khat := D.instFieldKhat
  letI : Algebra D.Ahat D.Khat := D.instAlgebraAhatKhat
  have hcompleted :
      (D.Qhat.scalarExtension D.Khat).character g = 0 :=
    projectiveScalarExtension_character_eq_zero_on_pSingular_of_forwardRange
      (A := D.Ahat) (K := D.Khat) (H := G) (p := p)
      D.forwardRange D.Qhat g hg
  -- Injectivity of the comparison field map lets the completed equality descend to `F`.
  apply D.fieldMap_injective
  rw [D.character_eq g, hcompleted, map_zero]

/-- Helper for Exercise 16-16.2-3: pure completion transport data plus the acyclic forward
range theorem already descends character vanishing to the localized generic fiber. -/
theorem localizationProjective_character_eq_zero_on_pSingular_of_transportData
    {p : ℕ} [Fact p.Prime]
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p)
    [Algebra (Localization.AtPrime (M.1.asIdeal)) F]
    [IsScalarTower Λ (Localization.AtPrime (M.1.asIdeal)) F]
    (Q : FiniteProjectiveGroupAlgebraModule (Localization.AtPrime (M.1.asIdeal)) G)
    (D : LocalizedCompleteProjectiveTransportData (Λ := Λ) (F := F) (G := G) M Q)
    (hforward :
      letI : CommRing D.Ahat := D.instCommRingAhat
      letI : IsLocalRing D.Ahat := D.instLocalAhat
      letI : HenselianLocalRing D.Ahat := D.instHenselianAhat
      letI : IsNoetherianRing D.Ahat := D.instNoetherianAhat
      letI : IsAdicComplete (IsLocalRing.maximalIdeal D.Ahat) D.Ahat :=
        D.instAdicCompleteAhat
      letI : Field D.Khat := D.instFieldKhat
      letI : Algebra D.Ahat D.Khat := D.instAlgebraAhatKhat
      ∀ {x : R₀[D.Khat](G)},
        x ∈
          (projectiveGrothendieckScalarExtensionHom D.Ahat D.Khat :
            P₀[IsLocalRing.ResidueField D.Ahat](G) →+ R₀[D.Khat](G)).range →
        ∀ h : G, ¬ IsPRegular p h →
          (finiteRepGrothendieckCharacter D.Khat G x : G → D.Khat) h = 0)
    (g : G) (hg : ¬ IsPRegular p g) :
    (Q.scalarExtension F).character g = 0 := by
  -- First assemble the existing comparison record from the pure transport data.
  obtain ⟨C⟩ :=
    localizedCompleteProjectiveComparisonData_of_transportData
      (Λ := Λ) (F := F) (G := G) M Q D hforward
  -- Then consume the standard completed-comparison descent theorem.
  exact localizationProjective_character_eq_zero_on_pSingular_of_completeComparison
    (Λ := Λ) (F := F) (G := G) M Q C g hg

/-- Helper for Exercise 16-16.2-3: over the localization at a residue-characteristic prime,
Swan's local theorem makes projective generic-fiber characters vanish on `p`-singular elements. -/
theorem localizationProjective_character_eq_zero_on_pSingular
    {p : ℕ} [Fact p.Prime]
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p)
    [Algebra (Localization.AtPrime (M.1.asIdeal)) F]
    [IsScalarTower Λ (Localization.AtPrime (M.1.asIdeal)) F]
    (Q : FiniteProjectiveGroupAlgebraModule (Localization.AtPrime (M.1.asIdeal)) G)
    (g : G) (hg : ¬ IsPRegular p g) :
    (Q.scalarExtension F).character g = 0 := by
  -- Route correction: bypass the obsolete completed-comparison record and apply the theorem-local
  -- local DVR character theorem directly to the localized coefficient ring.
  let A := Localization.AtPrime (M.1.asIdeal)
  letI : IsDiscreteValuationRing A :=
    localizationAtPrime_isDiscreteValuationRing (Λ := Λ) M
  letI : IsFractionRing A F :=
    localizationAtPrime_isFractionRing (Λ := Λ) (F := F) M
  letI : CharP (IsLocalRing.ResidueField A) p :=
    localized_residueField_charP_of_nonzeroResidualCharacteristicMaximalIdeal
      (Λ := Λ) M
  -- The localized owner is now in exactly the shape expected by the local Swan theorem.
  exact localDVR_projective_character_eq_zero_on_pSingular
    (A := A) (K := F) (G := G) (p := p) Q g hg

/-- Helper for Exercise 16-16.2-3: if the localized residue-prime coefficient ring already
carries the complete-local forward range theorem from Theorem 36, then its generic-fiber
projective character vanishes on every `p`-singular element. -/
theorem localizationProjective_character_eq_zero_on_pSingular_of_forwardRange
    {p : ℕ} [Fact p.Prime]
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p)
    [Algebra (Localization.AtPrime (M.1.asIdeal)) F]
    [IsScalarTower Λ (Localization.AtPrime (M.1.asIdeal)) F]
    [HenselianLocalRing (Localization.AtPrime (M.1.asIdeal))]
    [IsNoetherianRing (Localization.AtPrime (M.1.asIdeal))]
    [IsAdicComplete
      (IsLocalRing.maximalIdeal (Localization.AtPrime (M.1.asIdeal)))
      (Localization.AtPrime (M.1.asIdeal))]
    (hforward :
      ∀ {x : R₀[F](G)},
        x ∈
          (projectiveGrothendieckScalarExtensionHom
              (Localization.AtPrime (M.1.asIdeal)) F :
            P₀[IsLocalRing.ResidueField (Localization.AtPrime (M.1.asIdeal))](G) →+
              R₀[F](G)).range →
        ∀ h : G, ¬ IsPRegular p h →
          (finiteRepGrothendieckCharacter F G x : G → F) h = 0)
    (Q : FiniteProjectiveGroupAlgebraModule (Localization.AtPrime (M.1.asIdeal)) G)
    (g : G) (hg : ¬ IsPRegular p g) :
    (Q.scalarExtension F).character g = 0 := by
  -- The completed/local coefficient hypotheses put the actual projective owner in the range of
  -- Serre's projective scalar-extension map, where the supplied forward theorem kills its
  -- character.
  exact projectiveScalarExtension_character_eq_zero_on_pSingular_of_forwardRange
    (A := Localization.AtPrime (M.1.asIdeal)) (K := F) (H := G) (p := p)
    hforward Q g hg

/-- Helper for Exercise 16-16.2-3: at a residue prime of characteristic `p`, the generic-fiber
character of `P` vanishes on the `p`-singular elements. -/
theorem scalarExtension_character_eq_zero_of_not_isPRegular_of_residue_prime
    {p : ℕ} [Fact p.Prime]
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p)
    (g : G) (hg : ¬ IsPRegular p g) :
    (P.scalarExtension F).character g = 0 := by
  let A := Localization.AtPrime (M.1.asIdeal)
  letI : Algebra (FractionRing Λ) F := FractionRing.liftAlgebra Λ F
  letI : Algebra A F :=
    RingHom.toAlgebra ((algebraMap (FractionRing Λ) F).comp (algebraMap A (FractionRing Λ)))
  letI : IsScalarTower Λ A F :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap Λ F x =
        algebraMap (FractionRing Λ) F (algebraMap A (FractionRing Λ) (algebraMap Λ A x))
      calc
        algebraMap Λ F x =
            algebraMap (FractionRing Λ) F (algebraMap Λ (FractionRing Λ) x) :=
              IsScalarTower.algebraMap_apply Λ (FractionRing Λ) F x
        _ = algebraMap (FractionRing Λ) F
              (algebraMap A (FractionRing Λ) (algebraMap Λ A x)) :=
              congrArg (algebraMap (FractionRing Λ) F)
                (IsScalarTower.algebraMap_apply Λ A (FractionRing Λ) x)
  have hlocal :
      ((localized_tensor_owner (Λ := Λ) (G := G) P M).scalarExtension F).character g = 0 :=
    localizationProjective_character_eq_zero_on_pSingular
      (Λ := Λ) (F := F) (G := G) M
      (localized_tensor_owner (Λ := Λ) (G := G) P M) g hg
  -- Compare the localized generic fiber with the original quotient-field scalar extension.
  rw [← localized_tensor_scalarExtension_character_eq
    (Λ := Λ) (F := F) (G := G) (p := p) P M g]
  exact hlocal

/-- Helper for Exercise 16-16.2-3: in the characteristic-zero branch, the residue-prime
character vanishing is exactly the local-DVR Swan reduction. -/
theorem scalarExtension_character_eq_zero_of_not_isPRegular_of_residue_prime_charZero
    {p : ℕ} [Fact p.Prime] [CharZero F]
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p)
    (g : G) (hg : ¬ IsPRegular p g) :
    (P.scalarExtension F).character g = 0 := by
  -- This names the characteristic-zero branch separately, so the public auxiliary theorem no
  -- longer routes the positive-characteristic case through the local DVR Swan input.
  exact scalarExtension_character_eq_zero_of_not_isPRegular_of_residue_prime
    (Λ := Λ) (F := F) (G := G) (p := p) P M g hg

omit [IsDedekindDomain Λ] in
/-- Helper for Exercise 16-16.2-3: when the quotient field `F` has characteristic `p`, every
residue-characteristic witness for `Λ` must have the same prime characteristic. -/
theorem residue_prime_eq_of_charP
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [CharP F p]
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ q) :
    q = p := by
  letI : CharP Λ p :=
    RingHom.charP (algebraMap Λ F) (IsFractionRing.injective Λ F) p
  have hp0 : (p : Λ ⧸ M.1.asIdeal) = 0 := by
    change Ideal.Quotient.mk M.1.asIdeal (p : Λ) = Ideal.Quotient.mk M.1.asIdeal 0
    exact congrArg (Ideal.Quotient.mk M.1.asIdeal) (CharP.cast_eq_zero (R := Λ) p)
  letI : CharP (Λ ⧸ M.1.asIdeal) p :=
    ringChar.of_eq
      (CharP.ringChar_of_prime_eq_zero (R := Λ ⧸ M.1.asIdeal) (Fact.out : Nat.Prime p) hp0)
  have hqchar : CharP M.1.asIdeal.ResidueField q := M.2.2
  letI : CharP M.1.asIdeal.ResidueField p :=
    charP_of_injective_algebraMap
      M.1.asIdeal.injective_algebraMap_quotient_residueField p
  have hpchar : ringChar M.1.asIdeal.ResidueField = p :=
    ringChar.eq (R := M.1.asIdeal.ResidueField) p
  -- Compare the two `CharP` instances on the same residue field through its ring characteristic.
  calc
    q = ringChar M.1.asIdeal.ResidueField := (@ringChar.eq _ _ q hqchar).symm
    _ = p := hpchar

omit [IsDedekindDomain Λ] [Group G] [Finite G] in
/-- Helper for Exercise 16-16.2-3: in positive characteristic, every prime divisor of `|G|` is
the field characteristic of `F`. -/
theorem card_prime_divisor_eq_of_charP
    {p : ℕ} [Fact p.Prime] [CharP F p]
    (hresidue : ∀ q : Nat.Primes, (q : ℕ) ∣ Nat.card G →
      Nonempty (NonzeroResidualCharacteristicMaximalIdeal Λ q))
    (q : Nat.Primes) (hq : (q : ℕ) ∣ Nat.card G) :
    (q : ℕ) = p := by
  obtain ⟨M⟩ := hresidue q hq
  letI : Fact ((q : ℕ).Prime) := ⟨q.2⟩
  -- The previous helper identifies the residue characteristic with the ambient field
  -- characteristic once `F` is known to have positive characteristic.
  exact residue_prime_eq_of_charP (Λ := Λ) (F := F) (p := p) (q := q) M

/-- Helper for Exercise 16-16.2-3: if every prime divisor of a nonzero natural number `n` is the
prime `p`, then `n` is a power of `p`. -/
theorem eq_prime_pow_of_forall_prime_dvd_eq
    {p n : ℕ} [Fact p.Prime]
    (hn : n ≠ 0)
    (hdiv : ∀ q : Nat.Primes, (q : ℕ) ∣ n → (q : ℕ) = p) :
    ∃ m : ℕ, n = p ^ m := by
  refine ⟨n.factorization p, ?_⟩
  apply Nat.eq_pow_of_factorization_eq_single hn
  ext q
  by_cases hqp : q = p
  · subst hqp
    simp
  · by_cases hqprime : q.Prime
    · have hndvd : ¬ q ∣ n := by
        intro hqdvd
        exact hqp (hdiv ⟨q, hqprime⟩ hqdvd)
      simp [Nat.factorization_eq_zero_of_not_dvd hndvd, hqp]
    · simp [Nat.factorization_eq_zero_of_not_prime n hqprime, hqp]

omit [Finite G] in
omit [IsDedekindDomain Λ] in
/-- Helper for Exercise 16-16.2-3: in positive characteristic, every nonidentity element of `G`
is singular for the field characteristic prime. -/
theorem not_isPRegular_ringChar_of_ne_one
    {p : ℕ} [Fact p.Prime] [CharP F p]
    (hresidue : ∀ q : Nat.Primes, (q : ℕ) ∣ Nat.card G →
      Nonempty (NonzeroResidualCharacteristicMaximalIdeal Λ q))
    (g : G) (hg : g ≠ 1) :
    ¬ IsPRegular p g := by
  have horder_ne : orderOf g ≠ 1 := by
    intro h1
    exact hg ((orderOf_eq_one_iff : orderOf g = 1 ↔ g = 1).mp h1)
  obtain ⟨q, hqprime, hqdvd⟩ := Nat.exists_prime_and_dvd horder_ne
  let qPrime : Nat.Primes := ⟨q, hqprime⟩
  have hq_card : q ∣ Nat.card G := dvd_trans hqdvd (orderOf_dvd_natCard g)
  have hqp : q = p :=
    card_prime_divisor_eq_of_charP
      (Λ := Λ) (F := F) (G := G) (p := p) hresidue qPrime hq_card
  -- The prime divisor `q` of `orderOf g` is exactly the field characteristic prime.
  rw [isPRegular_iff_not_dvd_orderOf (p := p) g]
  intro hp_not_dvd
  exact hp_not_dvd <| hqp ▸ hqdvd

/-- Helper for Exercise 16-16.2-3: in positive characteristic the generic-fiber character is zero
on every nonidentity element, because the scalar-extension owner is free over the `p`-group
algebra. -/
theorem scalarExtension_character_eq_zero_of_ne_one_positiveChar
    {p : ℕ} [Fact p.Prime] [CharP F p]
    (hresidue : ∀ q : Nat.Primes, (q : ℕ) ∣ Nat.card G →
      Nonempty (NonzeroResidualCharacteristicMaximalIdeal Λ q))
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (g : G) (hg : g ≠ 1) :
    (P.scalarExtension F).character g = 0 := by
  have hcard_ne_zero : Nat.card G ≠ 0 := by
    exact (Nat.card_ne_zero).2 ⟨inferInstance, inferInstance⟩
  obtain ⟨m, hm⟩ :=
    eq_prime_pow_of_forall_prime_dvd_eq
      (p := p) (n := Nat.card G) hcard_ne_zero
      (fun q hq =>
        card_prime_divisor_eq_of_charP
          (Λ := Λ) (F := F) (G := G) (p := p) hresidue q hq)
  let Q := scalarExtension_owner (Λ := Λ) (F := F) (G := G) P
  have hG : IsPGroup p G := IsPGroup.of_card hm
  letI : Module.Free F[G] Q.V :=
    FiniteProjectiveGroupAlgebraModule.free_of_charP_of_isPGroup
      (k := F) (G := G) (p := p) Q hG
  letI : Module.Finite F[G] Q.V := Module.Finite.of_restrictScalars_finite F F[G] Q.V
  have htraceQ : Q.toFiniteRep.character g = 0 := by
    -- The free group-algebra trace calculation kills any nonidentity group element.
    simpa [FiniteProjectiveGroupAlgebraModule.toFiniteRep,
      FiniteProjectiveGroupAlgebraModule.toRep] using
      trace_action_eq_zero_of_free_over_groupAlgebra
        (R := F) (H := G) (M := Q.V) hg
  have hclass := scalarExtension_owner_class_eq (Λ := Λ) (F := F) (G := G) P
  have hchar_eq : Q.toFiniteRep.character g = (P.scalarExtension F).character g := by
    -- Compare the packaged free owner with the literal scalar-extension representation through
    -- the Grothendieck-character map, which evaluates to ordinary characters on honest classes.
    simpa [finiteRepGrothendieckCharacter_class] using
      congrArg (fun x : R₀[F](G) =>
        (finiteRepGrothendieckCharacter F G x : G → F) g) hclass
  simpa [hchar_eq] using htraceQ

/-- Helper for Exercise 16-16.2-3: every nonidentity element has zero character on the generic
fiber.  In positive characteristic this uses `p`-group freeness; in characteristic zero it chooses
a residue prime dividing the element order and applies the local DVR theorem. -/
theorem scalarExtension_character_eq_zero_of_ne_one_aux
    (hresidue : ∀ p : Nat.Primes, (p : ℕ) ∣ Nat.card G →
      Nonempty (NonzeroResidualCharacteristicMaximalIdeal Λ p))
    (P : FiniteProjectiveGroupAlgebraModule Λ G)
    (g : G) (hg : g ≠ 1) :
    (P.scalarExtension F).character g = 0 := by
  by_cases hchar0 : ringChar F = 0
  · have horder_ne : orderOf g ≠ 1 := by
      intro h1
      exact hg ((orderOf_eq_one_iff : orderOf g = 1 ↔ g = 1).mp h1)
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd horder_ne
    let pPrime : Nat.Primes := ⟨p, hp⟩
    have hp_card : p ∣ Nat.card G := dvd_trans hpdvd (orderOf_dvd_natCard g)
    obtain ⟨M⟩ := hresidue pPrime hp_card
    letI : Fact p.Prime := ⟨hp⟩
    have hsing : ¬ IsPRegular p g := by
      rw [isPRegular_iff_not_dvd_orderOf (p := p) g]
      exact fun hnot => hnot hpdvd
    -- In characteristic zero the source proof localizes at a residue prime and applies Swan's
    -- local DVR character theorem.
    letI : CharZero F := (CharP.ringChar_zero_iff_CharZero (R := F)).mp hchar0
    exact scalarExtension_character_eq_zero_of_not_isPRegular_of_residue_prime_charZero
      (Λ := Λ) (F := F) (G := G) (p := p) P M g hsing
  · let p := ringChar F
    letI : CharP F p := ringChar.charP (R := F)
    have hp_ne_one : p ≠ 1 := CharP.char_ne_one F p
    have hp_two_le : 2 ≤ p := by
      omega
    letI : Fact p.Prime := ⟨CharP.char_is_prime_of_two_le F p hp_two_le⟩
    -- Positive characteristic avoids the local-DVR theorem entirely: the residue hypothesis
    -- forces `G` to be a `p`-group, so projective modules over `F[G]` are free.
    exact scalarExtension_character_eq_zero_of_ne_one_positiveChar
      (Λ := Λ) (F := F) (G := G) (p := p) hresidue P g hg

end FiniteProjectiveGroupAlgebraModule

end SwanExercise

end Representation
