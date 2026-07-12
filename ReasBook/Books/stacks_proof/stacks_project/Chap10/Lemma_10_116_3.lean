import Mathlib
import StacksProject_2024.Chap05.Definition_5_10_1
import StacksProject_2024.Chap10.Lemma_10_17_7
import StacksProject_2024.Chap10.Lemma_10_112_4
import StacksProject_2024.Chap10.Lemma_10_113_1.DimensionEquality
import StacksProject_2024.Chap10.Theorem_10_34_1_Hilbert_Nullstellensatz
import StacksProject_2024.Chap10.Lemma_10_114_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open TopologicalSpace

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/- 
Domain-style sampling for the local dimension formula on affine schemes of finite type over a
field:
- primary domain: local Krull dimension on `Spec(S)`, organized around the owner
  `topologicalKrullDimAt` and the local ring `Localization.AtPrime x.asIdeal`;
- sampled owner declarations of the same kind:
  `topologicalKrullDimAt`,
  `topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over`,
  `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`,
  `IsLocalization.AtPrime.ringKrullDim_eq_height`;
- best owner abstraction: the ambient owner is the local-dimension object `topologicalKrullDimAt`
  on `PrimeSpectrum S`, while the local algebra data are already canonically owned by
  `Localization.AtPrime x.asIdeal` and `x.asIdeal.ResidueField`;
- primitive data: the point `x : PrimeSpectrum S` of the finite type affine scheme `Spec(S)`;
- derived API: the additive decomposition of `topologicalKrullDimAt x` into the Krull dimension of
  the canonical local ring and the transcendence degree of the canonical residue field.

Source/core/bridge triage:
* `source-facing`: the textbook local dimension formula at a prime of a finite type algebra over a
  field;
* `core/canonical`: `topologicalKrullDimAt`, `Localization.AtPrime`, `Ideal.ResidueField`, and
  mathlib's localization-height owner `IsLocalization.AtPrime.ringKrullDim_eq_height`;
* `bridge/view`: the comparison from the local topological owner to maximal localizations from
  Lemma `10.114.5`, together with the chain-length interpretation of heights.

There is no separate local wrapper to keep here: the theorem should speak directly in terms of the
owner objects `topologicalKrullDimAt`, `Localization.AtPrime x.asIdeal`, and
`x.asIdeal.ResidueField`.
-/

/- The full component computation still needs a domain dimension formula for finite type
quotients.  The Nullstellensatz side condition below is one stable piece of that route: closed
points contribute no residue-field transcendence degree. -/
/-- Helper for Chap10 Lemma 10 116 3: the residue field of a maximal ideal in a finite type
algebra over the base field has zero transcendence degree. -/
private theorem maximalSpectrum_residueField_trdeg_toNat_eq_zero
    (m : MaximalSpectrum S) :
    Cardinal.toNat (Algebra.trdeg k m.asIdeal.ResidueField) = 0 := by
  -- The Nullstellensatz makes the residue field finite over `k`; finite field extensions are
  -- algebraic, and algebraic extensions have transcendence degree zero.
  letI : Module.Finite k m.asIdeal.ResidueField :=
    finite_residueField_of_isMaximal_of_finiteType k m.asIdeal
  haveI : Algebra.IsAlgebraic k m.asIdeal.ResidueField :=
    Algebra.IsAlgebraic.of_finite k m.asIdeal.ResidueField
  simpa using congrArg Cardinal.toNat
    (trdeg_eq_zero (R := k) (A := m.asIdeal.ResidueField))

/- The closed-point case is a verified boundary case for the eventual component computation:
there is only one maximal localization above a maximal ideal, and the Nullstellensatz kills the
residue-field transcendence term. -/
/-- Helper for Chap10 Lemma 10 116 3: the desired local-dimension formula holds at closed points
of the affine finite-type scheme. -/
private theorem topologicalKrullDimAt_closedPoint_eq_ringKrullDim_localizationAtPrime_add_trdeg
    (m : MaximalSpectrum S) :
    topologicalKrullDimAt m.toPrimeSpectrum =
      ringKrullDim (Localization.AtPrime m.asIdeal) +
        Cardinal.toNat (Algebra.trdeg k m.asIdeal.ResidueField) := by
  have htop :
      topologicalKrullDimAt m.toPrimeSpectrum =
        ringKrullDim (Localization.AtPrime m.asIdeal) := by
    -- Lemma 10.114.5 rewrites the closed-point local dimension as an infimum over maximal
    -- ideals above `m`; maximality makes that index subtype a singleton.
    rw [topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over
      (k := k) (S := S) m.toPrimeSpectrum]
    letI : Subsingleton {n : MaximalSpectrum S // m.asIdeal ≤ n.asIdeal} := by
      refine ⟨fun a b ↦ Subtype.ext <| MaximalSpectrum.ext <| ?_⟩
      have ha : m.asIdeal = a.1.asIdeal :=
        Ideal.IsMaximal.eq_of_le m.isMaximal a.1.isMaximal.ne_top a.2
      have hb : m.asIdeal = b.1.asIdeal :=
        Ideal.IsMaximal.eq_of_le m.isMaximal b.1.isMaximal.ne_top b.2
      exact ha.symm.trans hb
    let e : {n : MaximalSpectrum S // m.asIdeal ≤ n.asIdeal} := ⟨m, le_rfl⟩
    simpa [e] using
      (ciInf_subsingleton e fun n : {n : MaximalSpectrum S // m.asIdeal ≤ n.asIdeal} ↦
        ringKrullDim (Localization.AtPrime n.1.asIdeal))
  -- The Nullstellensatz residue-field calculation removes the additive transcendence term.
  rw [htop, maximalSpectrum_residueField_trdeg_toNat_eq_zero (k := k) (S := S) m]
  simp

/- This is the same component-supremum normal form as the remaining arbitrary-prime blocker,
but in the closed-point case the already-proved singleton-infimum calculation closes it. -/
/-- Helper for Chap10 Lemma 10 116 3: the component-supremum formula is verified for closed
points. -/
private theorem iSup_topologicalKrullDim_irreducibleComponents_through_closedPoint_eq_height_add_trdeg
    (m : MaximalSpectrum S) :
    (⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
        m.toPrimeSpectrum ∈ (Z : Set (PrimeSpectrum S)) },
        topologicalKrullDim (Z : Set (PrimeSpectrum S))) =
      (m.asIdeal.height : WithBot ℕ∞) +
        Cardinal.toNat (Algebra.trdeg k m.asIdeal.ResidueField) := by
  -- Return from the component supremum to the local-dimension owner from Lemma 10.114.5.
  rw [← topologicalKrullDimAt_eq_iSup_topologicalKrullDim_irreducibleComponents_through
    (k := k) (S := S) m.toPrimeSpectrum]
  -- The closed-point formula gives the local-ring term, and the AtPrime API rewrites it as height.
  rw [topologicalKrullDimAt_closedPoint_eq_ringKrullDim_localizationAtPrime_add_trdeg
    (k := k) (S := S) m]
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m.asIdeal
    (Localization.AtPrime m.asIdeal)]

-- Route correction: the previous maximal-localization infimum route reduces to the same
-- theorem-sized algebraic comparison as the target.  The stable source route is to use the
-- irreducible-component formula from Lemma 10.114.5 and compute those components through minimal
-- prime quotient domains.
/-- Helper for Chap10 Lemma 10 116 3: components through a point can be reindexed by minimal
primes contained in the point's prime ideal, with each component written as a zero locus. -/
private theorem
    iSup_topologicalKrullDim_irreducibleComponents_through_eq_iSup_zeroLocus_minimalPrimesBelow
    (x : PrimeSpectrum S) :
    (⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
        x ∈ (Z : Set (PrimeSpectrum S)) },
        topologicalKrullDim (Z : Set (PrimeSpectrum S))) =
      ⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal },
        topologicalKrullDim (PrimeSpectrum.zeroLocus (q.1.1 : Set S)) := by
  -- Build the explicit correspondence `Z ↦ vanishingIdeal Z`, with inverse `q ↦ V(q)`.
  let e :
      { Z : irreducibleComponents (PrimeSpectrum S) // x ∈ (Z : Set (PrimeSpectrum S)) } ≃
        { q : minimalPrimes S // q.1 ≤ x.asIdeal } := by
    refine
      { toFun := fun Z => ?_
        invFun := fun q => ?_
        left_inv := ?_
        right_inv := ?_ }
    · refine ⟨⟨PrimeSpectrum.vanishingIdeal (Z.1 : Set (PrimeSpectrum S)), ?_⟩, ?_⟩
      · rw [PrimeSpectrum.vanishingIdeal_mem_minimalPrimes]
        rw [(isClosed_of_mem_irreducibleComponents
          (Z.1 : Set (PrimeSpectrum S)) Z.1.2).closure_eq]
        exact Z.1.2
      · intro a ha
        exact (PrimeSpectrum.mem_vanishingIdeal
          (Z.1 : Set (PrimeSpectrum S)) a).mp ha x Z.2
    · refine ⟨⟨PrimeSpectrum.zeroLocus (q.1.1 : Set S), ?_⟩, ?_⟩
      · rw [PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents]
        rw [Ideal.IsPrime.radical (Ideal.minimalPrimes_isPrime q.1.2)]
        exact q.1.2
      · exact (PrimeSpectrum.mem_zeroLocus x (q.1.1 : Set S)).mpr q.2
    · intro Z
      apply Subtype.ext
      apply Subtype.ext
      dsimp
      -- The zero locus of the vanishing ideal is the closure, and components are closed.
      calc
        PrimeSpectrum.zeroLocus
            (PrimeSpectrum.vanishingIdeal (Z.1 : Set (PrimeSpectrum S)) : Set S) =
            closure (Z.1 : Set (PrimeSpectrum S)) :=
          PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure _
        _ = (Z.1 : Set (PrimeSpectrum S)) :=
          (isClosed_of_mem_irreducibleComponents
            (Z.1 : Set (PrimeSpectrum S)) Z.1.2).closure_eq
    · intro q
      apply Subtype.ext
      apply Subtype.ext
      dsimp
      -- A minimal prime is radical, so `V(q)` has vanishing ideal exactly `q`.
      calc
        PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus (q.1.1 : Set S)) =
            q.1.1.radical :=
          PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical q.1.1
        _ = q.1.1 :=
          Ideal.IsPrime.radical (Ideal.minimalPrimes_isPrime q.1.2)
  -- Reindex the supremum along this equivalence and normalize the surviving component.
  refine Equiv.iSup_congr e ?_
  intro Z
  dsimp [e]
  calc
    topologicalKrullDim
        (PrimeSpectrum.zeroLocus
          (PrimeSpectrum.vanishingIdeal (Z.1 : Set (PrimeSpectrum S)) : Set S)) =
        topologicalKrullDim (closure (Z.1 : Set (PrimeSpectrum S))) := by
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    _ = topologicalKrullDim (Z.1 : Set (PrimeSpectrum S)) := by
      rw [(isClosed_of_mem_irreducibleComponents
        (Z.1 : Set (PrimeSpectrum S)) Z.1.2).closure_eq]

/-- Helper for Chap10 Lemma 10 116 3: the component `V(q)` attached to a minimal prime has
the Krull dimension of the quotient ring `S ⧸ q`. -/
private theorem topologicalKrullDim_zeroLocus_minimalPrime_eq_ringKrullDim_quotient
    (q : minimalPrimes S) :
    topologicalKrullDim (PrimeSpectrum.zeroLocus (q.1 : Set S)) =
      ringKrullDim (S ⧸ q.1) := by
  -- The quotient spectrum is homeomorphic to `V(q)`, so topological and ring dimensions agree.
  have hhomeo :
      topologicalKrullDim (PrimeSpectrum (S ⧸ q.1)) =
        topologicalKrullDim (PrimeSpectrum.zeroLocus (q.1 : Set S)) := by
    simpa using
      IsHomeomorph.topologicalKrullDim_eq
        (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus q.1)
        (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus q.1).isHomeomorph
  rw [← hhomeo]
  exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (S ⧸ q.1)

/-- Helper for Chap10 Lemma 10 116 3: the Krull dimension of a prime quotient is the coheight
of the corresponding point of `Spec S`. -/
private theorem ringKrullDim_quotient_eq_coheight (p : Ideal S) [p.IsPrime] :
    ringKrullDim (S ⧸ p) =
      (Order.coheight (⟨p, inferInstance⟩ : PrimeSpectrum S) : WithBot ℕ∞) := by
  -- Move the quotient spectrum to the zero locus, then identify that zero locus with the upper
  -- interval above the prime `p`.
  let y : PrimeSpectrum S := ⟨p, inferInstance⟩
  rw [ringKrullDim_quotient]
  have hzero : PrimeSpectrum.zeroLocus (p : Set S) = Set.Ici y := by
    ext z
    change p ≤ z.asIdeal ↔ y ≤ z
    rfl
  rw [hzero]
  exact (Order.coheight_eq_krullDim_Ici y).symm

/-- Helper for Chap10 Lemma 10 116 3: a finite injective polynomial normalization computes the
Krull dimension of the target. -/
private theorem ringKrullDim_eq_of_finite_injective_polynomial_algebra
    {F : Type*} [Field F] {A : Type*} [CommRing A] [Algebra F A] {d : ℕ}
    (g : MvPolynomial (Fin d) F →ₐ[F] A)
    (hg_injective : Function.Injective g) (hg_finite : AlgHom.Finite g) :
    ringKrullDim A = d := by
  -- Finiteness gives integrality, and the injective integral extension preserves Krull dimension.
  let _ : Algebra (MvPolynomial (Fin d) F) A := g.toAlgebra
  have hg_integral : (algebraMap (MvPolynomial (Fin d) F) A).IsIntegral := by
    simpa [RingHom.algebraMap_toAlgebra] using hg_finite.to_isIntegral
  let _ : Algebra.IsIntegral (MvPolynomial (Fin d) F) A :=
    algebraMap_isIntegral_iff.mp hg_integral
  have hdim :
      ringKrullDim (MvPolynomial (Fin d) F) = ringKrullDim A :=
    ringKrullDim_eq_of_injective_algebraMap_of_isIntegral
      (by simpa [RingHom.algebraMap_toAlgebra] using hg_injective)
  -- The source polynomial ring has dimension equal to its number of variables.
  have hpoly : ringKrullDim (MvPolynomial (Fin d) F) = d := by
    simp
  exact hdim.symm.trans hpoly

/-- Helper for Chap10 Lemma 10 116 3: a finite-type domain over a field has Krull dimension equal
to its transcendence degree over the field. -/
private theorem ringKrullDim_eq_trdeg_of_finiteType_domain
    {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim A = (Cardinal.toNat (Algebra.trdeg k A) : WithBot ℕ∞) := by
  -- Choose Noether normalization `k[t_1, ..., t_d] -> A`.
  obtain ⟨d, g, hg_injective, hg_finite⟩ := exists_finite_inj_algHom_of_fg k A
  have hdim : ringKrullDim A = d :=
    ringKrullDim_eq_of_finite_injective_polynomial_algebra g hg_injective hg_finite
  have htrdeg : Cardinal.toNat (Algebra.trdeg k A) = d := by
    -- The same finite injective map makes `A` algebraic over the polynomial subalgebra.
    let _ : Algebra (MvPolynomial (Fin d) k) A := g.toAlgebra
    let _ : IsScalarTower k (MvPolynomial (Fin d) k) A := by
      refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
      simp [RingHom.algebraMap_toAlgebra]
    let _ : FaithfulSMul (MvPolynomial (Fin d) k) A :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
        simpa [RingHom.algebraMap_toAlgebra] using hg_injective)
    have hIntegral : Algebra.IsIntegral (MvPolynomial (Fin d) k) A :=
      algebraMap_isIntegral_iff.mp (by
        simpa [RingHom.algebraMap_toAlgebra] using hg_finite.to_isIntegral)
    let _ : Algebra.IsIntegral (MvPolynomial (Fin d) k) A := hIntegral
    let _ : Algebra.IsAlgebraic (MvPolynomial (Fin d) k) A :=
      Algebra.IsIntegral.isAlgebraic
    have hzero : Algebra.trdeg (MvPolynomial (Fin d) k) A = 0 :=
      trdeg_eq_zero (R := MvPolynomial (Fin d) k) (A := A)
    -- Split transcendence degree through the polynomial subalgebra, then remove the algebraic
    -- top extension.
    have hadd := lift_trdeg_add_eq (R := k) (S := MvPolynomial (Fin d) k) (A := A)
    have hlift :
        Cardinal.lift.{v, u} (Algebra.trdeg k (MvPolynomial (Fin d) k)) =
          Cardinal.lift.{u, v} (Algebra.trdeg k A) := by
      simpa [hzero] using hadd
    have htoNat :
        Cardinal.toNat (Algebra.trdeg k A) =
          Cardinal.toNat (Algebra.trdeg k (MvPolynomial (Fin d) k)) := by
      rw [← Cardinal.toNat_lift.{u, v} (Algebra.trdeg k A),
        ← Cardinal.toNat_lift.{v, u} (Algebra.trdeg k (MvPolynomial (Fin d) k)), hlift]
    -- Finally evaluate the transcendence degree of the polynomial ring.
    rw [htoNat, MvPolynomial.trdeg_of_isDomain, Cardinal.toNat_lift, Cardinal.mk_fin,
      Cardinal.toNat_natCast]
  rw [hdim, htrdeg]

/-- Helper for Chap10 Lemma 10 116 3: prime quotients inherit the finite-type domain dimension
formula. -/
private theorem ringKrullDim_primeQuotient_eq_trdeg_quotient
    (p : Ideal S) [p.IsPrime] :
    ringKrullDim (S ⧸ p) =
      (Cardinal.toNat (Algebra.trdeg k (S ⧸ p)) : WithBot ℕ∞) := by
  -- Apply the finite-type domain formula to the domain `S ⧸ p`.
  exact ringKrullDim_eq_trdeg_of_finiteType_domain (k := k) (A := S ⧸ p)

/-- Helper for Chap10 Lemma 10 116 3: the residue field of a prime and the corresponding
quotient domain have the same transcendence degree over the base field. -/
private theorem trdeg_primeResidueField_eq_trdeg_quotient
    {A : Type v} [CommRing A] [Algebra k A] (I : Ideal A) [I.IsPrime] :
    Algebra.trdeg k I.ResidueField = Algebra.trdeg k (A ⧸ I) := by
  let T := A ⧸ I
  have hcomap : I = Ideal.comap (Ideal.Quotient.mk I : A →+* T) (⊥ : Ideal T) := by
    ext x
    change x ∈ I ↔ Ideal.Quotient.mk I x = 0
    exact (Ideal.Quotient.eq_zero_iff_mem).symm
  let eResidue : I.ResidueField ≃ₐ[k] ((⊥ : Ideal T).ResidueField) :=
    AlgEquiv.ofBijective
      (Ideal.ResidueField.mapₐ I (⊥ : Ideal T) (Ideal.Quotient.mkₐ k I) hcomap)
      (by
        -- The quotient map is surjective, so it induces a bijection on residue fields over the
        -- prime `I` and the zero prime of the quotient.
        simpa [T] using
          (RingHom.SurjectiveOnStalks.residueFieldMap_bijective
            (f := (Ideal.Quotient.mk I : A →+* T))
            (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective)
            I (⊥ : Ideal T) hcomap))
  let eFrac : FractionRing T ≃ₐ[k] ((⊥ : Ideal T).ResidueField) := by
    -- For the quotient domain, the zero-prime residue field is its fraction field.
    let e : T ≃ₐ[T] T ⧸ (⊥ : Ideal T) := (AlgEquiv.quotientBot T T).symm
    letI : IsFractionRing T ((⊥ : Ideal T).ResidueField) := by
      refine IsFractionRing.of_ringEquiv_left e.toRingEquiv ?_
      intro x
      change algebraMap T ((⊥ : Ideal T).ResidueField) x =
        algebraMap (T ⧸ (⊥ : Ideal T)) ((⊥ : Ideal T).ResidueField)
          (Ideal.Quotient.mk _ x)
      symm
      rfl
    exact AlgEquiv.restrictScalars k (FractionRing.algEquiv T ((⊥ : Ideal T).ResidueField))
  have htrdeg_frac : Algebra.trdeg k (FractionRing T) = Algebra.trdeg k T := by
    -- The fraction field is algebraic over the quotient domain, so the tower formula removes the
    -- top transcendence-degree summand.
    have hadd := trdeg_add_eq (R := k) (S := T) (A := FractionRing T)
    have hz : Algebra.trdeg T (FractionRing T) = 0 := by
      have : Algebra.IsAlgebraic T (FractionRing T) :=
        (IsFractionRing.comap_isAlgebraic_iff (A := T) (K := FractionRing T)
          (C := FractionRing T)).mpr
          (inferInstance : Algebra.IsAlgebraic (FractionRing T) (FractionRing T))
      exact trdeg_eq_zero (R := T) (A := FractionRing T)
    simpa [hz] using hadd.symm
  -- Transport both sides through the common zero-prime residue field and then through the
  -- fraction-field comparison.
  calc
    Algebra.trdeg k I.ResidueField = Algebra.trdeg k ((⊥ : Ideal T).ResidueField) := by
      simpa using AlgEquiv.trdeg_eq (R := k) eResidue
    _ = Algebra.trdeg k (FractionRing T) := by
      symm
      simpa using AlgEquiv.trdeg_eq (R := k) eFrac
    _ = Algebra.trdeg k T := htrdeg_frac
    _ = Algebra.trdeg k (A ⧸ I) := by
      rfl

/-- Helper for Chap10 Lemma 10 116 3: a prime quotient has Krull dimension equal to the
transcendence degree of the prime's residue field. -/
private theorem ringKrullDim_primeQuotient_eq_trdeg_residueField
    (p : Ideal S) [p.IsPrime] :
    ringKrullDim (S ⧸ p) =
      (Cardinal.toNat (Algebra.trdeg k p.ResidueField) : WithBot ℕ∞) := by
  -- Combine the finite-type domain dimension formula for `S ⧸ p` with the residue-field bridge.
  calc
    ringKrullDim (S ⧸ p) =
        (Cardinal.toNat (Algebra.trdeg k (S ⧸ p)) : WithBot ℕ∞) :=
      ringKrullDim_primeQuotient_eq_trdeg_quotient (k := k) (S := S) p
    _ = (Cardinal.toNat (Algebra.trdeg k p.ResidueField) : WithBot ℕ∞) := by
      rw [← trdeg_primeResidueField_eq_trdeg_quotient (k := k) (A := S) p]

/-- Helper for Chap10 Lemma 10 116 3: replacing the base field by the residue field of its
zero prime does not change the natural-number transcendence degree. -/
private theorem fieldBotResidueField_trdeg_toNat_eq
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra ((⊥ : Ideal K).ResidueField) L]
    [IsScalarTower K ((⊥ : Ideal K).ResidueField) L] :
    Cardinal.toNat (Algebra.trdeg ((⊥ : Ideal K).ResidueField) L) =
      Cardinal.toNat (Algebra.trdeg K L) := by
  -- Make the residue field of the zero prime into the fraction field of `K`, hence algebraic
  -- over `K`.
  letI : IsFractionRing K ((⊥ : Ideal K).ResidueField) := by
    let e : K ≃ₐ[K] K ⧸ (⊥ : Ideal K) := (AlgEquiv.quotientBot K K).symm
    refine IsFractionRing.of_ringEquiv_left e.toRingEquiv ?_
    intro x
    change algebraMap K ((⊥ : Ideal K).ResidueField) x =
      algebraMap (K ⧸ (⊥ : Ideal K)) ((⊥ : Ideal K).ResidueField) (Ideal.Quotient.mk _ x)
    symm
    rfl
  have hbase_alg : Algebra.IsAlgebraic K ((⊥ : Ideal K).ResidueField) := by
    let e : (⊥ : Ideal K).ResidueField ≃ₐ[K] K :=
      (FractionRing.algEquiv K ((⊥ : Ideal K).ResidueField)).symm.trans
        (FractionRing.algEquiv K K)
    exact Algebra.IsAlgebraic.of_injective e.toAlgHom e.injective
  have hbase_zero : Algebra.trdeg K ((⊥ : Ideal K).ResidueField) = 0 := by
    exact trdeg_eq_zero (R := K) (A := (⊥ : Ideal K).ResidueField)
  -- The tower formula then identifies the two transcendence degrees after taking `toNat`.
  have hsum :=
    lift_trdeg_add_eq (R := K) (S := (⊥ : Ideal K).ResidueField) (A := L)
  have hlift_eq :
      Cardinal.lift.{u, v} (Algebra.trdeg ((⊥ : Ideal K).ResidueField) L) =
        Cardinal.lift.{u, v} (Algebra.trdeg K L) := by
    simpa [hbase_zero] using hsum
  rw [← Cardinal.toNat_lift.{u, v} (Algebra.trdeg ((⊥ : Ideal K).ResidueField) L),
    ← Cardinal.toNat_lift.{u, v} (Algebra.trdeg K L), hlift_eq]

/-- Helper for Chap10 Lemma 10 116 3: for a finite-type domain over a field, replacing both
rings by their fraction fields does not change the natural-number transcendence degree. -/
private theorem fractionRing_trdeg_toNat_eq_trdeg_of_finiteTypeDomain
    {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    Cardinal.toNat (Algebra.trdeg (FractionRing k) (FractionRing A)) =
      Cardinal.toNat (Algebra.trdeg k A) := by
  -- The fraction field of the base field is algebraic over the base field itself.
  have hbase_alg : Algebra.IsAlgebraic k (FractionRing k) := by
    let e : FractionRing k ≃ₐ[k] k := FractionRing.algEquiv k k
    exact Algebra.IsAlgebraic.of_injective e.toAlgHom e.injective
  have hbase_zero : Algebra.trdeg k (FractionRing k) = 0 := by
    exact trdeg_eq_zero (R := k) (A := FractionRing k)
  have hfracA : Algebra.trdeg k (FractionRing A) = Algebra.trdeg k A := by
    -- The top extension `A ⟶ Frac(A)` is algebraic, so the tower formula removes it.
    have hadd := trdeg_add_eq (R := k) (S := A) (A := FractionRing A)
    have hz : Algebra.trdeg A (FractionRing A) = 0 := by
      have : Algebra.IsAlgebraic A (FractionRing A) :=
        (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := FractionRing A)
          (C := FractionRing A)).mpr
          (inferInstance : Algebra.IsAlgebraic (FractionRing A) (FractionRing A))
      exact trdeg_eq_zero (R := A) (A := FractionRing A)
    simpa [hz] using hadd.symm
  -- The base-field fraction field contributes no transcendence degree, so only `trdeg k A`
  -- remains.
  letI : FaithfulSMul (FractionRing k) (FractionRing A) :=
    FaithfulSMul.of_field_isFractionRing (FractionRing k) (FractionRing A)
      (FractionRing k) (FractionRing A)
  have hsum := lift_trdeg_add_eq (R := k) (S := FractionRing k) (A := FractionRing A)
  have hlift_eq :
      Cardinal.lift.{u, v} (Algebra.trdeg (FractionRing k) (FractionRing A)) =
        Cardinal.lift.{u, v} (Algebra.trdeg k (FractionRing A)) := by
    simpa [hbase_zero] using hsum
  calc
    Cardinal.toNat (Algebra.trdeg (FractionRing k) (FractionRing A)) =
        Cardinal.toNat (Cardinal.lift.{u, v}
          (Algebra.trdeg (FractionRing k) (FractionRing A))) := by
      exact (Cardinal.toNat_lift.{u, v} _).symm
    _ = Cardinal.toNat (Cardinal.lift.{u, v} (Algebra.trdeg k (FractionRing A))) := by
      rw [hlift_eq]
    _ = Cardinal.toNat (Algebra.trdeg k (FractionRing A)) := by
      exact Cardinal.toNat_lift.{u, v} _
    _ = Cardinal.toNat (Algebra.trdeg k A) := by
      rw [hfracA]

/-- Helper for Chap10 Lemma 10 116 3: the compile-safe inequality half of the field-base
height-plus-residue-field transcendence formula. -/
private theorem fieldBase_primeHeight_add_residueFieldTrdeg_toNat_le_trdeg
    {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (p : PrimeSpectrum A) :
    ENat.toNat (Ideal.primeHeight p.asIdeal) +
        Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) ≤
      Cardinal.toNat (Algebra.trdeg k A) := by
  -- The equality support gives the field-base formula with the generic fraction-field term;
  -- normalizing that term gives this inequality direction without importing the inequality file.
  have hdim :=
    fieldBase_primeHeight_add_residueFieldTrdeg_toNat_eq_fractionRing_trdeg
      (k := k) (A := A) p
  have hgeneric := fractionRing_trdeg_toNat_eq_trdeg_of_finiteTypeDomain (k := k) (A := A)
  exact le_of_eq (by simpa [hgeneric] using hdim)

-- Route correction: a direct import of the aggregate Lemma 10.113.1 equality owner was tested and
-- is not compile-safe in the current tree.  Both inequality directions now consume the acyclic
-- field-base equality support, so the target no longer imports the separate inequality module.
/-- Helper for Chap10 Lemma 10 116 3: the reverse inequality in the field-base
height-plus-residue-field transcendence formula. -/
private theorem fieldBase_trdeg_toNat_le_primeHeight_add_residueFieldTrdeg_toNat
    {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (p : PrimeSpectrum A) :
    Cardinal.toNat (Algebra.trdeg k A) ≤
      ENat.toNat (Ideal.primeHeight p.asIdeal) +
        Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) := by
  -- Consume the acyclic field-base equality owner, then normalize the fraction-field
  -- transcendence term back to `trdeg k A`; this is the reverse inequality orientation.
  have hinj : Function.Injective (algebraMap k A) := FaithfulSMul.algebraMap_injective k A
  let _ : FaithfulSMul k A := (faithfulSMul_iff_algebraMap_injective k A).mpr hinj
  have hdim :=
    fieldBase_primeHeight_add_residueFieldTrdeg_toNat_eq_fractionRing_trdeg
      (k := k) (A := A) p
  have hgeneric := fractionRing_trdeg_toNat_eq_trdeg_of_finiteTypeDomain (k := k) (A := A)
  exact le_of_eq (by simpa [hgeneric] using hdim.symm)

/-- Helper for Chap10 Lemma 10 116 3: the field-base dimension formula in natural-number form
for a finite-type domain. -/
private theorem fieldBase_primeHeight_add_residueFieldTrdeg_toNat_eq_trdeg
    {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (p : PrimeSpectrum A) :
    ENat.toNat (Ideal.primeHeight p.asIdeal) +
        Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) =
      Cardinal.toNat (Algebra.trdeg k A) := by
  -- Assemble the two orientations supplied by the acyclic equality support after normalizing the
  -- generic fraction-field term; no separate inequality support is needed here.
  have hle := fieldBase_primeHeight_add_residueFieldTrdeg_toNat_le_trdeg (k := k) (A := A) p
  have hge :=
    fieldBase_trdeg_toNat_le_primeHeight_add_residueFieldTrdeg_toNat (k := k) (A := A) p
  exact le_antisymm hle hge

/-- Helper for Chap10 Lemma 10 116 3: convert the natural-number prime-height formula to the
`WithBot ℕ∞` height formula used by `ringKrullDim`. -/
private theorem primeHeight_toNat_add_coe_eq_height_add
    {A : Type*} [CommRing A] [IsNoetherianRing A] (p : Ideal A) [p.IsPrime] (n : ℕ) :
    (((ENat.toNat (Ideal.primeHeight p) + n : ℕ) : ℕ∞) : WithBot ℕ∞) =
      (p.height : WithBot ℕ∞) + (n : WithBot ℕ∞) := by
  -- Noetherianity makes prime height finite, so `toNat` coerces back to the original height.
  have hfinite : Ideal.primeHeight p ≠ ⊤ := Ideal.primeHeight_ne_top p
  have hheight : p.height = Ideal.primeHeight p := Ideal.height_eq_primeHeight p
  calc
    (((ENat.toNat (Ideal.primeHeight p) + n : ℕ) : ℕ∞) : WithBot ℕ∞) =
        (((ENat.toNat (Ideal.primeHeight p) : ℕ∞) + (n : ℕ∞)) : WithBot ℕ∞) := by
      norm_num
    _ = ((Ideal.primeHeight p + (n : ℕ∞)) : WithBot ℕ∞) := by
      rw [ENat.coe_toNat hfinite]
    _ = (p.height : WithBot ℕ∞) + (n : WithBot ℕ∞) := by
      rw [hheight]
      rfl

/-- Helper for Chap10 Lemma 10 116 3: a finite-type domain over a field satisfies the
height-plus-residue-field transcendence dimension formula at every prime. -/
private theorem finiteTypeDomain_ringKrullDim_eq_height_add_trdeg_residueField
    {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (p : PrimeSpectrum A) :
    ringKrullDim A =
      (p.asIdeal.height : WithBot ℕ∞) +
        Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) := by
  -- Rewrite the domain dimension as `trdeg k A`, then use the field-base dimension formula and
  -- convert its natural-number height term back to the `WithBot ℕ∞` height owner.
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hnat :=
    fieldBase_primeHeight_add_residueFieldTrdeg_toNat_eq_trdeg (k := k) (A := A) p
  calc
    ringKrullDim A = (Cardinal.toNat (Algebra.trdeg k A) : WithBot ℕ∞) :=
      ringKrullDim_eq_trdeg_of_finiteType_domain (k := k) (A := A)
    _ = ((ENat.toNat (Ideal.primeHeight p.asIdeal) +
          Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) : ℕ) : WithBot ℕ∞) := by
      rw [← hnat]
    _ = (p.asIdeal.height : WithBot ℕ∞) +
          Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) :=
      primeHeight_toNat_add_coe_eq_height_add p.asIdeal
        (Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField))

/-- Helper for Chap10 Lemma 10 116 3: the prime of `S ⧸ q` corresponding to `x` when
`q` is a minimal prime below `x.asIdeal`. -/
private noncomputable def quotientPrimeOver
    (x : PrimeSpectrum S) (q : minimalPrimes S) (hqx : q.1 ≤ x.asIdeal) :
    PrimeSpectrum (S ⧸ q.1) :=
  (Ideal.primeSpectrumQuotientOrderIsoZeroLocus q.1).symm ⟨x, hqx⟩

/-- Helper for Chap10 Lemma 10 116 3: the quotient prime over `x` contracts back to
`x.asIdeal`. -/
private theorem quotientPrimeOver_comap_asIdeal
    (x : PrimeSpectrum S) (q : minimalPrimes S) (hqx : q.1 ≤ x.asIdeal) :
    Ideal.comap (Ideal.Quotient.mk q.1) (quotientPrimeOver x q hqx).asIdeal = x.asIdeal := by
  -- Apply the quotient-spectrum order isomorphism back to the named quotient prime.
  have hspec :
      (Ideal.primeSpectrumQuotientOrderIsoZeroLocus q.1) (quotientPrimeOver x q hqx) =
        ⟨x, hqx⟩ := by
    exact (Ideal.primeSpectrumQuotientOrderIsoZeroLocus q.1).apply_symm_apply ⟨x, hqx⟩
  exact congrArg (fun z : PrimeSpectrum.zeroLocus (R := S) (q.1 : Set S) => z.1.asIdeal) hspec

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 116 3: the residue field of the quotient prime over `x` has the
same transcendence degree over `k` as the residue field of `x`. -/
private theorem quotientPrimeOver_residueField_trdeg_toNat_eq
    (x : PrimeSpectrum S) (q : minimalPrimes S) (hqx : q.1 ≤ x.asIdeal) :
    Cardinal.toNat (Algebra.trdeg k (quotientPrimeOver x q hqx).asIdeal.ResidueField) =
      Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := by
  have hcomap :
      x.asIdeal =
        Ideal.comap (Ideal.Quotient.mk q.1) (quotientPrimeOver x q hqx).asIdeal :=
    (quotientPrimeOver_comap_asIdeal (S := S) x q hqx).symm
  have hbij :
      Function.Bijective
        (Ideal.ResidueField.mapₐ x.asIdeal (quotientPrimeOver x q hqx).asIdeal
          (Ideal.Quotient.mkₐ k q.1) hcomap) := by
    -- The quotient map is surjective, hence it induces a bijection on the two residue fields.
    simpa using
      (RingHom.SurjectiveOnStalks.residueFieldMap_bijective
        (f := (Ideal.Quotient.mk q.1 : S →+* S ⧸ q.1))
        (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective)
        x.asIdeal (quotientPrimeOver x q hqx).asIdeal hcomap)
  let eResidue :
      x.asIdeal.ResidueField ≃ₐ[k] (quotientPrimeOver x q hqx).asIdeal.ResidueField :=
    AlgEquiv.ofBijective
      (Ideal.ResidueField.mapₐ x.asIdeal (quotientPrimeOver x q hqx).asIdeal
        (Ideal.Quotient.mkₐ k q.1) hcomap)
      hbij
  -- Transport transcendence degree across the residue-field isomorphism.
  simpa using congrArg Cardinal.toNat (AlgEquiv.trdeg_eq (R := k) eResidue).symm

/-- Helper for Chap10 Lemma 10 116 3: the quotient-prime height is bounded by the height of
the original prime. -/
private theorem quotientPrimeOver_height_le
    (x : PrimeSpectrum S) (q : { q : minimalPrimes S // q.1 ≤ x.asIdeal }) :
    (quotientPrimeOver x q.1 q.2).asIdeal.height ≤ x.asIdeal.height := by
  let e := Ideal.primeSpectrumQuotientOrderIsoZeroLocus q.1.1
  let f : PrimeSpectrum (S ⧸ q.1.1) → PrimeSpectrum S := fun y => (e y).1
  have hf : StrictMono f := by
    -- The quotient-spectrum order isomorphism is strict, and the zero-locus subtype order is
    -- inherited from `Spec S`.
    intro a b hab
    simpa [f] using e.strictMono hab
  have hheight :=
    Order.height_le_height_apply_of_strictMono f hf (quotientPrimeOver x q.1 q.2)
  have himage : f (quotientPrimeOver x q.1 q.2) = x := by
    -- The image of the named quotient prime is exactly `x`.
    apply PrimeSpectrum.ext
    exact quotientPrimeOver_comap_asIdeal (S := S) x q.1 q.2
  rw [himage] at hheight
  simpa [Ideal.height_eq_primeHeight, Ideal.primeHeight] using hheight

/-- Helper for Chap10 Lemma 10 116 3: the residue-field transcendence degree of a prime is the
coheight of that point of `Spec S`, after passing through the quotient-dimension comparison. -/
private theorem residueField_trdeg_toNat_eq_coheight
    (p : Ideal S) [p.IsPrime] :
    (Cardinal.toNat (Algebra.trdeg k p.ResidueField) : WithBot ℕ∞) =
      (Order.coheight (⟨p, inferInstance⟩ : PrimeSpectrum S) : WithBot ℕ∞) := by
  -- First identify the transcendence degree with the dimension of the quotient domain, then
  -- rewrite the quotient spectrum as the upper interval over `p`.
  calc
    (Cardinal.toNat (Algebra.trdeg k p.ResidueField) : WithBot ℕ∞) =
        ringKrullDim (S ⧸ p) :=
      (ringKrullDim_primeQuotient_eq_trdeg_residueField (k := k) (S := S) p).symm
    _ = (Order.coheight (⟨p, inferInstance⟩ : PrimeSpectrum S) : WithBot ℕ∞) :=
      ringKrullDim_quotient_eq_coheight (S := S) p

/-- Helper for Chap10 Lemma 10 116 3: the quotient prime over `x` has the same coheight as
`x`, after identifying their residue fields through the quotient map. -/
private theorem quotientPrimeOver_coheight_eq
    (k : Type u) [Field k] [Algebra k S] [Algebra.FiniteType k S]
    (x : PrimeSpectrum S) (q : minimalPrimes S) (hqx : q.1 ≤ x.asIdeal) :
    Order.coheight (quotientPrimeOver x q hqx) = Order.coheight x := by
  -- Compare coheights through the residue-field transcendence degree, where the quotient map has
  -- already supplied a canonical isomorphism.
  apply WithBot.coe_injective
  calc
    (Order.coheight (quotientPrimeOver x q hqx) : WithBot ℕ∞) =
        Cardinal.toNat
          (Algebra.trdeg k (quotientPrimeOver x q hqx).asIdeal.ResidueField) := by
      rw [← residueField_trdeg_toNat_eq_coheight (k := k) (S := S ⧸ q.1)
        (quotientPrimeOver x q hqx).asIdeal]
    _ = Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := by
      rw [quotientPrimeOver_residueField_trdeg_toNat_eq (k := k) (S := S) x q hqx]
    _ = (Order.coheight x : WithBot ℕ∞) :=
      residueField_trdeg_toNat_eq_coheight (k := k) (S := S) x.asIdeal

/-- Helper for Chap10 Lemma 10 116 3: each minimal-component quotient dimension is the coheight
of the corresponding minimal point of `Spec S`. -/
private theorem ringKrullDim_minimalPrimeQuotient_eq_coheight
    (q : minimalPrimes S) :
    ringKrullDim (S ⧸ q.1) =
      (Order.coheight (⟨q.1, Ideal.minimalPrimes_isPrime q.2⟩ : PrimeSpectrum S) :
        WithBot ℕ∞) := by
  -- This is the quotient/coheight comparison specialized to a minimal prime.
  letI : q.1.IsPrime := Ideal.minimalPrimes_isPrime q.2
  exact ringKrullDim_quotient_eq_coheight (S := S) q.1

/-- Helper for Chap10 Lemma 10 116 3: every chain ending at `x` lies in the quotient component
of a minimal prime below its head, giving the lower bound for the quotient-height supremum. -/
private theorem ltSeries_length_le_iSup_quotientPrimeOver_height
    (x : PrimeSpectrum S) (l : LTSeries (PrimeSpectrum S)) (hlast : l.last = x) :
    (l.length : ℕ∞) ≤
      ⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal },
        (quotientPrimeOver x q.1 q.2).asIdeal.height := by
  -- Choose a minimal prime below the head of the chain; since the chain ends at `x`, this
  -- minimal prime also lies below `x.asIdeal`.
  obtain ⟨p, hp_min, hp_le_head⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S)) (J := l.head.asIdeal) bot_le
  let qmin : minimalPrimes S := ⟨p, hp_min⟩
  have hq_le_x : qmin.1 ≤ x.asIdeal := by
    exact hp_le_head.trans (by simpa [hlast] using (l.head_le_last : l.head ≤ l.last))
  let qidx : { q : minimalPrimes S // q.1 ≤ x.asIdeal } := ⟨qmin, hq_le_x⟩
  let e := Ideal.primeSpectrumQuotientOrderIsoZeroLocus qmin.1
  have hq_le_i (i : Fin (l.length + 1)) : qmin.1 ≤ (l i).asIdeal := by
    exact hp_le_head.trans (show l.head.asIdeal ≤ (l i).asIdeal from l.head_le i)
  -- Transport the whole chain into the quotient spectrum attached to the chosen minimal prime.
  let lq : LTSeries (PrimeSpectrum (S ⧸ qmin.1)) :=
    LTSeries.mk l.length
      (fun i => e.symm ⟨l i, hq_le_i i⟩)
      (fun i j hij => by
        apply e.symm.strictMono
        exact show (⟨l i, hq_le_i i⟩ :
            PrimeSpectrum.zeroLocus (R := S) (qmin.1 : Set S)) <
            ⟨l j, hq_le_i j⟩ from l.strictMono hij)
  have hlast_lq : lq.last = e.symm ⟨x, hq_le_x⟩ := by
    apply e.injective
    simpa [lq, e, RelSeries.last] using hlast
  have hlen : (l.length : ℕ∞) ≤ (e.symm ⟨x, hq_le_x⟩).asIdeal.height := by
    have h := Order.length_le_height_last (p := lq)
    rw [hlast_lq] at h
    simpa only [Ideal.height_eq_primeHeight, Ideal.primeHeight] using h
  -- The chosen quotient component is one of the terms of the supremum.
  exact le_trans hlen (by
    simpa [quotientPrimeOver, qidx, qmin, e] using
      (le_iSup (fun q : { q : minimalPrimes S // q.1 ≤ x.asIdeal } =>
        (quotientPrimeOver x q.1 q.2).asIdeal.height) qidx))

/-- Helper for Chap10 Lemma 10 116 3: quotient primes over all minimal components below `x`
recover exactly the height of `x`. -/
private theorem iSup_quotientPrimeOver_height_eq_height
    (x : PrimeSpectrum S) :
    (⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal },
        (quotientPrimeOver x q.1 q.2).asIdeal.height) = x.asIdeal.height := by
  -- The upper bound is functoriality of height under the quotient-spectrum embedding; the lower
  -- bound maps every chain ending at `x` into a suitable quotient component.
  refine le_antisymm ?_ ?_
  · exact iSup_le fun q => quotientPrimeOver_height_le (S := S) x q
  · rw [Ideal.height_eq_primeHeight, Ideal.primeHeight, Order.height_eq_iSup_last_eq]
    exact iSup₂_le fun l hlast =>
      ltSeries_length_le_iSup_quotientPrimeOver_height (S := S) x l hlast

/-- Helper for Chap10 Lemma 10 116 3: the coheight of a minimal component through `x` splits
as quotient-prime height plus the coheight of `x`. -/
private theorem minimalPrimeComponent_coheight_eq_quotientPrimeOver_height_add_coheight
    (k : Type u) [Field k] [Algebra k S] [Algebra.FiniteType k S]
    (x : PrimeSpectrum S) (q : { q : minimalPrimes S // q.1 ≤ x.asIdeal }) :
    Order.coheight (⟨q.1.1, Ideal.minimalPrimes_isPrime q.1.2⟩ : PrimeSpectrum S) =
      (quotientPrimeOver x q.1 q.2).asIdeal.height + Order.coheight x := by
  -- The finite-type domain dimension formula on `S ⧸ q` gives the component dimension, while
  -- the residue-field bridge identifies the coheight of the quotient prime with that of `x`.
  apply WithBot.coe_injective
  letI : q.1.1.IsPrime := Ideal.minimalPrimes_isPrime q.1.2
  calc
    (Order.coheight
        (⟨q.1.1, Ideal.minimalPrimes_isPrime q.1.2⟩ : PrimeSpectrum S) :
          WithBot ℕ∞) =
        ringKrullDim (S ⧸ q.1.1) :=
      (ringKrullDim_minimalPrimeQuotient_eq_coheight (S := S) q.1).symm
    _ = ((quotientPrimeOver x q.1 q.2).asIdeal.height : WithBot ℕ∞) +
          Cardinal.toNat
            (Algebra.trdeg k (quotientPrimeOver x q.1 q.2).asIdeal.ResidueField) :=
      finiteTypeDomain_ringKrullDim_eq_height_add_trdeg_residueField
        (k := k) (A := S ⧸ q.1.1) (quotientPrimeOver x q.1 q.2)
    _ = ((quotientPrimeOver x q.1 q.2).asIdeal.height : WithBot ℕ∞) +
          (Order.coheight (quotientPrimeOver x q.1 q.2) : WithBot ℕ∞) := by
      rw [residueField_trdeg_toNat_eq_coheight (k := k) (S := S ⧸ q.1.1)
        (quotientPrimeOver x q.1 q.2).asIdeal]
    _ = ((quotientPrimeOver x q.1 q.2).asIdeal.height : WithBot ℕ∞) +
          (Order.coheight x : WithBot ℕ∞) := by
      rw [quotientPrimeOver_coheight_eq (k := k) (S := S) x q.1 q.2]

/-- Helper for Chap10 Lemma 10 116 3: a constant can be pulled out of a nonempty supremum of
`ℕ∞` values after coercing to `WithBot ℕ∞`. -/
private theorem iSup_coe_enat_add_const {ι : Type*} [Nonempty ι]
    (f : ι → ℕ∞) (c : ℕ∞) :
    (⨆ i, ((f i + c : ℕ∞) : WithBot ℕ∞)) =
      (((⨆ i, f i) + c : ℕ∞) : WithBot ℕ∞) := by
  -- Normalize the coercion once, then use the `ℕ∞` additive supremum rule.
  rw [← WithBot.coe_iSup (OrderTop.bddAbove (Set.range fun i => f i + c)), ENat.iSup_add]

/-- Helper for Chap10 Lemma 10 116 3: the remaining catenary/equidimensional order statement
after all quotient and residue-field transports have been removed. -/
private theorem iSup_coheight_minimalPrimesBelow_eq_height_add_coheight
    (k : Type u) [Field k] [Algebra k S] [Algebra.FiniteType k S]
    (x : PrimeSpectrum S) :
    (⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal },
        (Order.coheight
          (⟨q.1.1, Ideal.minimalPrimes_isPrime q.1.2⟩ : PrimeSpectrum S) :
            WithBot ℕ∞)) =
      (x.asIdeal.height : WithBot ℕ∞) + (Order.coheight x : WithBot ℕ∞) := by
  -- Route correction: the component formula is proved by transporting all chains into quotient
  -- components, then applying the finite-type domain dimension formula on each component.
  have hnonempty : Nonempty { q : minimalPrimes S // q.1 ≤ x.asIdeal } := by
    obtain ⟨p, hp_min, hp_le_x⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S)) (J := x.asIdeal) bot_le
    exact ⟨⟨⟨p, hp_min⟩, hp_le_x⟩⟩
  let f : { q : minimalPrimes S // q.1 ≤ x.asIdeal } → ℕ∞ :=
    fun q => (quotientPrimeOver x q.1 q.2).asIdeal.height
  calc
    (⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal },
        (Order.coheight
          (⟨q.1.1, Ideal.minimalPrimes_isPrime q.1.2⟩ : PrimeSpectrum S) :
            WithBot ℕ∞)) =
        ⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal },
          ((f q + Order.coheight x : ℕ∞) : WithBot ℕ∞) := by
      refine iSup_congr fun q => ?_
      rw [minimalPrimeComponent_coheight_eq_quotientPrimeOver_height_add_coheight
        (k := k) (S := S) x q]
    _ = (((⨆ q, f q) + Order.coheight x : ℕ∞) : WithBot ℕ∞) :=
      iSup_coe_enat_add_const f (Order.coheight x)
    _ = ((x.asIdeal.height + Order.coheight x : ℕ∞) : WithBot ℕ∞) := by
      rw [iSup_quotientPrimeOver_height_eq_height (S := S) x]
    _ = (x.asIdeal.height : WithBot ℕ∞) + (Order.coheight x : WithBot ℕ∞) := rfl

/-- Helper for Chap10 Lemma 10 116 3: the remaining algebraic dimension calculation after
reindexing components by minimal primes below `x.asIdeal`. -/
private theorem
    iSup_ringKrullDim_minimalPrimeQuotientsBelow_eq_height_add_trdeg_residueField
    (x : PrimeSpectrum S) :
    (⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal }, ringKrullDim (S ⧸ q.1.1)) =
      (x.asIdeal.height : WithBot ℕ∞) +
        Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := by
  -- Route correction: the quotient/residue-field bridge is now fully separated from the
  -- catenary component statement.  Rewrite every quotient dimension to a coheight, then apply the
  -- isolated order-theoretic component formula.
  have hquotient_to_coheight :
      (⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal }, ringKrullDim (S ⧸ q.1.1)) =
        ⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal },
          (Order.coheight
            (⟨q.1.1, Ideal.minimalPrimes_isPrime q.1.2⟩ : PrimeSpectrum S) :
      WithBot ℕ∞) := by
    exact iSup_congr fun q =>
      ringKrullDim_minimalPrimeQuotient_eq_coheight (S := S) q.1
  have hx_trdeg_to_coheight :
      (Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) : WithBot ℕ∞) =
        (Order.coheight x : WithBot ℕ∞) := by
    simpa using residueField_trdeg_toNat_eq_coheight (k := k) (S := S) x.asIdeal
  calc
    (⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal }, ringKrullDim (S ⧸ q.1.1)) =
        ⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal },
          (Order.coheight
            (⟨q.1.1, Ideal.minimalPrimes_isPrime q.1.2⟩ : PrimeSpectrum S) :
              WithBot ℕ∞) := hquotient_to_coheight
    _ = (x.asIdeal.height : WithBot ℕ∞) + (Order.coheight x : WithBot ℕ∞) :=
      iSup_coheight_minimalPrimesBelow_eq_height_add_coheight (k := k) (S := S) x
    _ = (x.asIdeal.height : WithBot ℕ∞) +
          Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := by
      rw [hx_trdeg_to_coheight]

/-- Helper for Chap10 Lemma 10 116 3: the supremum of dimensions of irreducible components through
a prime is the height of that prime plus the transcendence degree of its residue field. -/
private theorem iSup_topologicalKrullDim_irreducibleComponents_through_eq_height_add_trdeg_residueField
    (x : PrimeSpectrum S) :
    (⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) // x ∈ (Z : Set (PrimeSpectrum S)) },
        topologicalKrullDim (Z : Set (PrimeSpectrum S))) =
      (x.asIdeal.height : WithBot ℕ∞) +
        Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := by
  -- First remove the topological component subtype by reindexing components as zero loci of
  -- minimal primes below `x.asIdeal`.
  calc
    (⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
        x ∈ (Z : Set (PrimeSpectrum S)) },
        topologicalKrullDim (Z : Set (PrimeSpectrum S))) =
        (⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal },
          topologicalKrullDim (PrimeSpectrum.zeroLocus (q.1.1 : Set S))) :=
      iSup_topologicalKrullDim_irreducibleComponents_through_eq_iSup_zeroLocus_minimalPrimesBelow
        (S := S) x
    -- Then identify each zero-locus component with the spectrum of its minimal-prime quotient.
    _ = (⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal }, ringKrullDim (S ⧸ q.1.1)) := by
      exact iSup_congr fun q =>
        topologicalKrullDim_zeroLocus_minimalPrime_eq_ringKrullDim_quotient (S := S) q.1
    -- The remaining step is now the isolated algebraic quotient-dimension supremum.
    _ = (x.asIdeal.height : WithBot ℕ∞) +
          Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) :=
      iSup_ringKrullDim_minimalPrimeQuotientsBelow_eq_height_add_trdeg_residueField
        (k := k) (S := S) x

/-- Helper for Chap10 Lemma 10 116 3: the local topological dimension at a prime is the height of
that prime plus the transcendence degree of its residue field. -/
private theorem topologicalKrullDimAt_eq_height_add_trdeg_residueField
    (x : PrimeSpectrum S) :
    topologicalKrullDimAt x =
      (x.asIdeal.height : WithBot ℕ∞) +
        Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := by
  -- Rewrite local dimension by the irreducible-component formula, matching the source proof.
  rw [topologicalKrullDimAt_eq_iSup_topologicalKrullDim_irreducibleComponents_through
    (k := k) (S := S) x]
  -- The remaining algebraic comparison is isolated in the component/minimal-prime helper above.
  exact iSup_topologicalKrullDim_irreducibleComponents_through_eq_height_add_trdeg_residueField
    (k := k) (S := S) x

/-- Helper for Chap10 Lemma 10 116 3: the Krull dimension of the localization at a prime is the
height of that prime ideal. -/
private theorem ringKrullDim_localizationAtPrime_eq_height (x : PrimeSpectrum S) :
    ringKrullDim (Localization.AtPrime x.asIdeal) = (x.asIdeal.height : WithBot ℕ∞) := by
  -- This is exactly the canonical localization-height comparison for `AtPrime` localizations.
  exact IsLocalization.AtPrime.ringKrullDim_eq_height x.asIdeal
    (Localization.AtPrime x.asIdeal)

/-- Chap10 Lemma 10 116 3: for a point `x` of `X = Spec(S)`, where `S` is a finite type
`k`-algebra and `x.asIdeal` is the corresponding prime ideal `𝔭`, the local dimension `dim_x(X)`
equals the Krull dimension of the localization `S_𝔭` plus the transcendence degree of the residue
field `κ(𝔭) = x.asIdeal.ResidueField` over `k`. -/
@[stacks 00P1]
theorem topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField
    (x : PrimeSpectrum S) :
    topologicalKrullDimAt x =
      ringKrullDim (Localization.AtPrime x.asIdeal) +
        Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := by
  -- First put the local topological dimension into the height/trdeg normal form.
  calc
    topologicalKrullDimAt x =
        (x.asIdeal.height : WithBot ℕ∞) +
          Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) :=
      topologicalKrullDimAt_eq_height_add_trdeg_residueField (k := k) (S := S) x
    -- Then replace the height of `x.asIdeal` by the Krull dimension of the canonical
    -- localization.
    _ = ringKrullDim (Localization.AtPrime x.asIdeal) +
          Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := by
      rw [← ringKrullDim_localizationAtPrime_eq_height (S := S) x]

end
