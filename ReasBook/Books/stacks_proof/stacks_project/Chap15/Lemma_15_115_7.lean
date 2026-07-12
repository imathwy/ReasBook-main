import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Lemma_10_43_6
import StacksProject_2024.Chap15.Definition_15_112_7
import StacksProject_2024.Chap15.Lemma_15_115_2
import StacksProject_2024.Chap15.Lemma_15_115_5
import StacksProject_2024.Chap15.Lemma_15_115_6

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing Algebra Polynomial
open scoped UniformizerRoot TensorProduct

universe u v w

noncomputable section

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable [FiniteDimensional (FractionRing A) L]
variable [Algebra.IsSeparable (FractionRing A) L]

/- Domain-style sampling for Lemma `15.115.7`:
- primary domain: tame ramification of finite separable extensions of the fraction field of a
  discrete valuation ring, detected after adjoining roots of a uniformizer;
- sampled owner declarations:
  `IsTamelyRamifiedWithRespectTo`,
  `IsUnramifiedWithRespectTo`,
  `uniformizerRootExtensionRing`,
  `uniformizerRootExtension`;
- best owner abstraction: the chapter owners `IsTamelyRamifiedWithRespectTo A L` and
  `IsUnramifiedWithRespectTo B L'`, together with the canonical radical-extension ring
  `B = A[π^(1/e)]`;
- primitive-vs-derived split: the source-facing content here is the existence of an unramified
  lift after a radical extension, while the field/ring/tower structures on `A[π^(1/e)]` come from
  the upstream radical-extension owners and should not be repackaged as new public wrapper
  predicates.

Source/core/bridge triage:
- `source-facing`: the three-way criterion for tame ramification;
- `core/canonical`: `IsTamelyRamifiedWithRespectTo`, `IsUnramifiedWithRespectTo`, and
  `uniformizerRootExtensionRing`;
- `bridge/view`: the explicit overfield data witnessing that `L` becomes contained in an
  unramified extension after adjoining a uniformizer root.
-/

-- Proof sketch: `(2) → (1)` combines Lemma `15.115.2` with Lemmas `15.115.5` and `15.115.6`:
-- `A[π^(1/e)] / A` is tamely ramified when `e` is prime to the residue characteristic, an
-- unramified extension above it stays tame, and tameness descends to the intermediate field `L`.
-- `(3) → (2)` is immediate by taking `d = 1`. For `(1) → (3)`, let `e₀` be the least common
-- multiple of the ramification indices of the branches of the integral closure of `A` in `L`; for
-- each prime-to-residue-characteristic `d`, set `e = d * e₀`, form `A[π^(1/e)]`, decompose
-- `L ⊗_K K[π^(1/e)]` into fields, and apply Abhyankar's lemma together with Lemma `15.112.5` to
-- show that each local factor over `A[π^(1/e)]` is unramified.

/-- Helper for Lemma 15.115.7: the integer `1` is always prime to the residue characteristic. -/
lemma primeToResidueCharacteristic_one :
    PrimeToResidueCharacteristic A 1 := by
  -- The only branch condition is coprimality with the residue characteristic prime, and `1` is
  -- coprime to every natural number.
  intro p _ _
  simpa using Nat.one_coprime p

/-- Helper for Lemma 15.115.7: coprimality with the residue characteristic is closed under
multiplication. -/
lemma primeToResidueCharacteristic_mul
    {m n : ℕ}
    (hm : PrimeToResidueCharacteristic A m)
    (hn : PrimeToResidueCharacteristic A n) :
    PrimeToResidueCharacteristic A (m * n) := by
  -- Check the defining coprimality condition prime-by-prime and multiply the two branchwise
  -- coprimality statements.
  intro p _ _
  exact Nat.Coprime.mul_left (hm p) (hn p)

/-- Helper for Lemma 15.115.7: every maximal branch of the integral closure of `A` in `L` lies
over the maximal ideal of the base discrete valuation ring. -/
lemma integralClosure_branch_liesOver_maximalIdeal
    (P : Ideal (integralClosure A L)) [P.IsMaximal] :
    P.LiesOver (maximalIdeal A) := by
  -- Integral extensions of local rings send maximal ideals back to the unique maximal ideal.
  rw [Ideal.liesOver_iff]
  exact (IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)).symm

/-- Helper for Lemma 15.115.7: the radical extension ring `A[π^(1/e)]` is the canonical integral
closure of `A` in its fraction field. -/
noncomputable theorem uniformizer_root_integralClosure_equiv
    {π : A} {e : ℕ} [Fact (Irreducible π)] [NeZero e] :
    A[π^(1/e)] ≃ₐ[A] integralClosure A (FractionRing (A[π^(1/e)])) := by
  letI :
      IsIntegralClosure (A[π^(1/e)]) A (FractionRing (A[π^(1/e)])) :=
    uniformizerRootExtensionRing_isIntegralClosure (A := A) (π := π) (n := e)
  -- Use the canonical owner equivalence between two integral closures of the same fraction field.
  exact
    IsIntegralClosure.equiv A (A[π^(1/e)]) (FractionRing (A[π^(1/e)]))
      (integralClosure A (FractionRing (A[π^(1/e)])))

/-- Helper for Lemma 15.115.7: the actual fraction field of `A[π^(1/e)]` is canonically the
explicit radical extension field used in Lemma `15.115.2`. -/
noncomputable theorem uniformizer_root_fractionRing_algEquiv
    {π : A} {e : ℕ} [Fact (Irreducible π)] [NeZero e] :
    FractionRing (A[π^(1/e)]) ≃ₐ[FractionRing A] K[π^(1/e)] := by
  -- Compare the two fraction-field presentations of the same radical extension ring.
  let eFrac :
      FractionRing (A[π^(1/e)]) ≃ₐ[A[π^(1/e)]] K[π^(1/e)] :=
    FractionRing.algEquiv (A[π^(1/e)]) (K[π^(1/e)])
  -- Restrict scalars to the ambient base field `FractionRing A` used in the main theorem.
  exact eFrac.restrictScalars (FractionRing A)

/-- Helper for Lemma 15.115.7: after identifying the actual fraction field of
`A[π^(1/e)]` with the explicit radical extension field `K[π^(1/e)]`, the tensor base change with
`L` is reduced. -/
lemma uniformizer_root_fractionRingTensorProduct_isReduced
    {π : A} {e : ℕ} [Fact (Irreducible π)] [NeZero e] :
    IsReduced (FractionRing (A[π^(1/e)]) ⊗[FractionRing A] L) := by
  let eK1 := uniformizer_root_fractionRing_algEquiv (A := A) (π := π) (e := e)
  let eTensor :
      FractionRing (A[π^(1/e)]) ⊗[FractionRing A] L ≃ₐ[FractionRing A]
        (K[π^(1/e)] ⊗[FractionRing A] L) :=
    Algebra.TensorProduct.congr eK1 (AlgEquiv.refl (FractionRing A) L)
  let _ : Algebra.IsSeparable (FractionRing A) K[π^(1/e)] := inferInstance
  let _ : IsReduced (K[π^(1/e)] ⊗[FractionRing A] L) := by
    -- The source field `K[π^(1/e)]` is separable over `FractionRing A`, so the reducedness lemma
    -- for separable tensor products applies directly.
    simpa using (Lemma_10_43_6 : IsReduced (K[π^(1/e)] ⊗[FractionRing A] L))
  -- Transport reducedness back across the canonical tensor-product equivalence.
  exact isReduced_of_injective eTensor.toRingHom eTensor.injective

/-- Helper for Lemma 15.115.7: localizing at a prime commutes with transport across a ring
equivalence once the target prime is the image ideal. -/
private noncomputable theorem localization_atPrime_ringEquiv_of_map_prime
    {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (q : Ideal R) [q.IsPrime] :
    Localization.AtPrime q ≃+* Localization.AtPrime (Ideal.map e.toRingHom q) := by
  have hPrimeCompl :
      Submonoid.map e.toMonoidHom q.primeCompl =
        (Ideal.map e.toRingHom q).primeCompl := by
    -- Compare the prime complements through the equivalence elementwise.
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ hy
      rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective] at hy
      rcases hy with ⟨z, hz, hzx⟩
      exact hx (e.injective hzx ▸ hz)
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      intro hx
      exact hy (Ideal.mem_map_of_mem e.toRingHom hx)
  -- Once the prime complements match, the localization universal property gives the equivalence.
  exact
    IsLocalization.ringEquivOfRingEquiv
      (Localization.AtPrime q)
      (Localization.AtPrime (Ideal.map e.toRingHom q))
      e hPrimeCompl

/-- Helper for Lemma 15.115.7: maximality is preserved when an ideal is transported across a ring
equivalence. -/
private theorem ideal_map_isMaximal_of_ringEquiv
    {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (q : Ideal R) [q.IsMaximal] :
    (Ideal.map e.toRingHom q).IsMaximal := by
  -- Push maximality along the surjective equivalence map.
  refine Ideal.IsMaximal.map_of_surjective_of_ker_le
    (f := e.toRingHom) e.surjective ?_
  simpa using (show RingHom.ker e.toRingHom ≤ q from by simp)

/-- Helper for Lemma 15.115.7: contracting an ideal after transporting it across a compatible
ring equivalence gives the same ideal as contracting first. -/
private theorem ideal_map_comap_eq_of_ringEquiv_comp
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : R →+* T) (e : S ≃+* T)
    (he : e.toRingHom.comp f = g) (q : Ideal S) :
    (Ideal.map e.toRingHom q).comap g = q.comap f := by
  ext x
  -- Rewrite the contraction through the equivalence and reduce to the original ideal.
  rw [Ideal.mem_comap, ← he, RingHom.comp_apply]
  rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact e.injective hyx ▸ hy
  · intro hx
    exact ⟨f x, hx, rfl⟩

/-- Helper for Lemma 15.115.7: lies-over is preserved when a branch ideal is transported across a
compatible ring equivalence. -/
private theorem ideal_map_liesOver_of_ringEquiv
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (e : S ≃+* T)
    (he : e.toRingHom.comp (algebraMap R S) = algebraMap R T)
    (p : Ideal R) (q : Ideal S) [q.LiesOver p] :
    (Ideal.map e.toRingHom q).LiesOver p := by
  -- Compare contractions after transport and then reuse the original lies-over equality.
  rw [Ideal.liesOver_iff]
  simpa [Ideal.liesOver_iff] using
    (ideal_map_comap_eq_of_ringEquiv_comp
      (f := algebraMap R S) (g := algebraMap R T) e he q).trans (q.over_def p)

/-- Helper for Lemma 15.115.7: a clause `(2)` witness yields tame ramification over `A` once the
unramified branch data over `A[π^(1/e)]` are transported to the canonical owners required by
Lemmas `15.115.5` and `15.115.6`. -/
lemma tame_of_uniformizer_root_unramified_cover
    {π : A} {e : ℕ} [Fact (Irreducible π)] [NeZero e]
    (he : 1 ≤ e) (hprime : PrimeToResidueCharacteristic A e)
    {L' : Type (max u v)} [Field L']
    [Algebra A L'] [Algebra (FractionRing A) L'] [IsScalarTower A (FractionRing A) L']
    [Algebra (A[π^(1/e)]) L']
    [Algebra (FractionRing (A[π^(1/e)])) L']
    [IsScalarTower (A[π^(1/e)]) (FractionRing (A[π^(1/e)])) L']
    [IsScalarTower (FractionRing A) (FractionRing (A[π^(1/e)])) L']
    [FiniteDimensional (FractionRing (A[π^(1/e)])) L']
    [Algebra.IsSeparable (FractionRing (A[π^(1/e)])) L']
    [Algebra L L'] [IsScalarTower (FractionRing A) L L']
    [FiniteDimensional L L'] [Algebra.IsSeparable L L']
    (hU : IsUnramifiedWithRespectTo (A[π^(1/e)]) L') :
    IsTamelyRamifiedWithRespectTo A L := by
  -- Route correction: the source proof only needs branchwise transport from the explicit owner
  -- `A[π^(1/e)]` to the canonical owner `integralClosure A (FractionRing (A[π^(1/e)]))`.
  -- TODO: prove the tame radical layer on `FractionRing (A[π^(1/e)])`, transport
  -- `IsUnramifiedAt` across `uniformizer_root_integralClosure_equiv` and `AlgEquiv.mapIntegralClosure`,
  -- and then invoke Lemmas `15.115.5` and `15.115.6`.
  let _ := he
  let _ := hprime
  let _ := hU
  sorry

/-- Helper for Lemma 15.115.7: if `e` is prime to the residue characteristic and divisible by
every branch ramification index of `integralClosure A L`, then some canonical branch of the tensor
base change along `A[π^(1/e)]` is unramified over `A[π^(1/e)]`. -/
lemma exists_uniformizer_root_tensor_branch_unramified_cover
    {π : A} {e : ℕ} [Fact (Irreducible π)] [NeZero e]
    (he : 1 ≤ e) (hprime : PrimeToResidueCharacteristic A e)
    (hdiv : ∀ P : MaximalSpectrum (integralClosure A L),
      ramificationIdx (maximalIdeal A) P.asIdeal ∣ e) :
    let B := A[π^(1/e)]
    let K1 := FractionRing B
    ∃ (L' : Type (max u v)) (_ : Field L') (_ : Algebra B L') (_ : Algebra K1 L')
      (_ : IsScalarTower B K1 L') (_ : FiniteDimensional K1 L')
      (_ : Algebra.IsSeparable K1 L') (_ : Algebra (FractionRing A) K1)
      (_ : Algebra (FractionRing A) L')
      (_ : IsScalarTower (FractionRing A) K1 L')
      (_ : Algebra L L') (_ : IsScalarTower (FractionRing A) L L'),
      IsUnramifiedWithRespectTo B L' := by
  -- Route correction: keep the source decomposition on the canonical tensor-product branch fields
  -- instead of introducing a separate ad hoc field-factor owner.
  -- TODO: let `KL = FractionRing (A[π^(1/e)]) ⊗[FractionRing A] L`, choose a maximal branch
  -- quotient `KL ⧸ m.asIdeal`, and prove it is unramified over `A[π^(1/e)]` by combining the
  -- reduced tensor comparison with Abhyankar's lemma on the localized branches.
  let _ := he
  let _ := hprime
  let _ := hdiv
  have hReduced :
      IsReduced (FractionRing (A[π^(1/e)]) ⊗[FractionRing A] L) :=
    uniformizer_root_fractionRingTensorProduct_isReduced
      (A := A) (L := L) (π := π) (e := e)
  let _ := hReduced
  sorry

/-- Helper for Lemma 15.115.7: tame ramification produces a finite common multiple of all branch
ramification indices, and this common multiple remains prime to the residue characteristic. -/
lemma exists_primeTo_common_multiple_of_branch_ramification_indices
    (hL : IsTamelyRamifiedWithRespectTo A L) :
    ∃ e₀ : ℕ, 1 ≤ e₀ ∧ PrimeToResidueCharacteristic A e₀ ∧
      ∀ P : MaximalSpectrum (integralClosure A L),
        ramificationIdx (maximalIdeal A) P.asIdeal ∣ e₀ := by
  classical
  let pSpec : PrimeSpectrum A :=
    ⟨maximalIdeal A, Ideal.IsMaximal.isPrime inferInstance⟩
  letI : Finite (pSpec.asIdeal.primesOver (integralClosure A L)) :=
    Lemma_10_120_18.integralClosure_primesOver_finite_of_ringKrullDim_eq_one
      (A := A) (L := L)
      (IsPrincipalIdealRing.ringKrullDim_eq_one A (IsDiscreteValuationRing.not_a_field A))
      pSpec
  letI : Fintype (pSpec.asIdeal.primesOver (integralClosure A L)) := Fintype.ofFinite _
  let e₀ : ℕ :=
    ∏ P : pSpec.asIdeal.primesOver (integralClosure A L), ramificationIdx (maximalIdeal A) P.1
  refine ⟨e₀, ?_, ?_, ?_⟩
  · -- Each branch ramification index is nonzero, so the finite product is positive.
    refine Nat.succ_le_of_lt (Nat.pos_of_ne_zero ?_)
    classical
    simpa [e₀] using
      Finset.prod_ne_zero_iff.mpr fun P _ ↦
        Ideal.ramificationIdx_ne_zero_of_liesOver
          (R := A) (S := integralClosure A L) P.1
          (IsDiscreteValuationRing.not_a_field A)
  · -- The branchwise coprimality hypotheses in the tame owner multiply across the finite set.
    intro q _ _
    -- Use the canonical `primesOver` owner to read branchwise coprimality from the tame owner.
    exact
      (Nat.coprime_fintype_prod_left_iff
        (s := fun P : pSpec.asIdeal.primesOver (integralClosure A L) ↦
          ramificationIdx (maximalIdeal A) P.1) (x := q)).2 fun P ↦ by
            simpa using hL.ramificationIdx_coprime q P.1
  · -- Every factor divides the product indexed by the full maximal spectrum.
    intro P
    let Pbranch : pSpec.asIdeal.primesOver (integralClosure A L) :=
      ⟨P.asIdeal, Ideal.IsMaximal.isPrime inferInstance,
        integralClosure_branch_liesOver_maximalIdeal (A := A) (L := L) P.asIdeal⟩
    exact
      Finset.dvd_prod_of_mem
        (fun Q : pSpec.asIdeal.primesOver (integralClosure A L) ↦
          ramificationIdx (maximalIdeal A) Q.1)
        (Finset.mem_univ Pbranch)

/-- Helper for Lemma 15.115.7: once the clause `(2)` cover has been transported to the canonical
integral-closure branch data required by Lemma `15.115.5`, the tame radical layer and Lemma
`15.115.6` descend tameness back to the original field `L`. -/
lemma tame_of_uniformizer_root_cover
    {K1 : Type w} [Field K1] [Algebra A K1] [Algebra (FractionRing A) K1]
    [IsScalarTower A (FractionRing A) K1]
    [FiniteDimensional (FractionRing A) K1]
    [Algebra.IsSeparable (FractionRing A) K1]
    {L' : Type (max v w)} [Field L'] [Algebra (FractionRing A) L'] [Algebra K1 L']
    [IsScalarTower A (FractionRing A) L'] [IsScalarTower (FractionRing A) K1 L']
    [FiniteDimensional K1 L'] [Algebra.IsSeparable K1 L']
    [Algebra L L'] [IsScalarTower (FractionRing A) L L']
    [FiniteDimensional L L'] [Algebra.IsSeparable L L']
    (hK1 : IsTamelyRamifiedWithRespectTo A K1)
    (hbranch_sep : ∀ (P : Ideal (integralClosure A L')) [P.IsMaximal],
      Algebra.IsSeparable (P.under (integralClosure A K1)).ResidueField P.ResidueField)
    (hbranch_coprime : ∀ (P : Ideal (integralClosure A L')) [P.IsMaximal]
      (q : ℕ) [Fact q.Prime] [CharP (P.under (integralClosure A K1)).ResidueField q],
        Nat.Coprime (ramificationIdx (P.under (integralClosure A K1)) P) q) :
    IsTamelyRamifiedWithRespectTo A L := by
  letI : IsScalarTower A K1 L' := by
    -- The `A`-action on the cover factors through `FractionRing A ⊆ K1 ⊆ L'`.
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    rw [IsScalarTower.algebraMap_apply A (FractionRing A) K1,
      IsScalarTower.algebraMap_apply A (FractionRing A) L',
      IsScalarTower.algebraMap_apply (FractionRing A) K1 L']
  -- First lift tameness from the radical layer to the top cover via Lemma `15.115.5`.
  have htop : IsTamelyRamifiedWithRespectTo A L' :=
    isTamelyRamifiedWithRespectTo_of_tame_of_forall_tame_over_integralClosure
      (A := A) (L := K1) (M := L') hK1 hbranch_sep hbranch_coprime
  -- Then descend tameness from the top cover to the original field `L` via Lemma `15.115.6`.
  exact
    isTamelyRamifiedWithRespectTo_of_tower
      (A := A) (L := L) (M := L') htop

/-- Lemma 15.115.7: for a discrete valuation ring `A` with fraction field `FractionRing A`, a
chosen uniformizer `π`, and a finite separable extension `L / FractionRing A`, the following are
equivalent: `L` is tamely ramified with respect to `A`; there exists an integer `e ≥ 1` invertible
in the residue field of `A` such that after adjoining an `e`th root of `π`, the field `L` embeds
into an extension unramified with respect to `A[π^(1/e)]`; and there exists an integer `e₀ ≥ 1`
invertible in the residue field of `A` such that the same conclusion holds for every multiple
`d * e₀` with `d ≥ 1` invertible in the residue field of `A`. -/
@[stacks 0EXW]
theorem isTamelyRamifiedWithRespectTo_tfae_uniformizerRootExtensionCriterion
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A)) :
    List.TFAE
      ([ IsTamelyRamifiedWithRespectTo A L
      , ∃ e : ℕ, ∃ he : 1 ≤ e,
          PrimeToResidueCharacteristic A e ∧
            let B := A[π^(1/e)]
            let K1 := FractionRing B
            letI : Fact (Irreducible π) :=
              ⟨(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ⟩
            letI : NeZero e := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one he)⟩
            letI : IsDomain B := inferInstance
            letI : IsDiscreteValuationRing B := inferInstance
            ∃ (L' : Type (max u v)) (_ : Field L') (_ : Algebra B L') (_ : Algebra K1 L')
              (_ : IsScalarTower B K1 L') (_ : FiniteDimensional K1 L')
              (_ : Algebra.IsSeparable K1 L') (_ : Algebra (FractionRing A) K1)
              (_ : Algebra (FractionRing A) L')
              (_ : IsScalarTower (FractionRing A) K1 L')
              (_ : Algebra L L') (_ : IsScalarTower (FractionRing A) L L'),
              IsUnramifiedWithRespectTo B L'
      , ∃ e₀ : ℕ, ∃ he₀ : 1 ≤ e₀,
          PrimeToResidueCharacteristic A e₀ ∧
          ∀ d : ℕ, ∀ hd : 1 ≤ d, PrimeToResidueCharacteristic A d →
            let e := d * e₀
            let B := A[π^(1/e)]
            let K1 := FractionRing B
            let he : 1 ≤ e := by
              simpa [e] using Nat.mul_le_mul hd he₀
            letI : Fact (Irreducible π) :=
              ⟨(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ⟩
            letI : NeZero e := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one he)⟩
            letI : IsDomain B := inferInstance
            letI : IsDiscreteValuationRing B := inferInstance
            ∃ (L' : Type (max u v)) (_ : Field L') (_ : Algebra B L') (_ : Algebra K1 L')
              (_ : IsScalarTower B K1 L') (_ : FiniteDimensional K1 L')
              (_ : Algebra.IsSeparable K1 L') (_ : Algebra (FractionRing A) K1)
              (_ : Algebra (FractionRing A) L')
              (_ : IsScalarTower (FractionRing A) K1 L')
              (_ : Algebra L L') (_ : IsScalarTower (FractionRing A) L L'),
              IsUnramifiedWithRespectTo B L'
      ] : List Prop) := by
  -- Follow the source proof as a cycle `(2) → (1) → (3) → (2)`.
  tfae_have 2 → 1 := by
    rintro ⟨e, he, hprime, hcover⟩
    -- Route correction: reduce the whole implication to the source-faithful helper that transports
    -- the clause `(2)` witness to the canonical owners used by Lemmas `15.115.5` and `15.115.6`.
    letI : Fact (Irreducible π) :=
      ⟨(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ⟩
    letI : NeZero e := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one he)⟩
    rcases hcover with ⟨L', _, _, _, _, _, _, _, _, _, _, _, hU⟩
    exact
      tame_of_uniformizer_root_unramified_cover
        (A := A) (L := L) (π := π) (e := e) he hprime hU
  tfae_have 3 → 2 := by
    rintro ⟨e₀, he₀, hprime₀, hforall⟩
    -- Specialize the universal multiple statement at `d = 1`.
    let h1 : PrimeToResidueCharacteristic A 1 := primeToResidueCharacteristic_one (A := A)
    simpa [Nat.one_mul] using hforall 1 Nat.one_le_one h1
  tfae_have 1 → 3 := by
    intro hL
    -- The source-faithful route picks a common multiple of the branch ramification indices and
    -- then applies Abhyankar's lemma after adjoining the corresponding uniformizer roots.
    rcases
      exists_primeTo_common_multiple_of_branch_ramification_indices
        (A := A) (L := L) hL with
      ⟨e₀, he₀, hprime₀, hdiv⟩
    refine ⟨e₀, he₀, hprime₀, ?_⟩
    intro d hd hdprime
    let e := d * e₀
    have he : 1 ≤ e := by
      -- The chosen multiple `e = d * e₀` stays positive because both factors are positive.
      simpa [e] using Nat.mul_le_mul hd he₀
    have hprime : PrimeToResidueCharacteristic A e := by
      -- Coprimality with the residue characteristic is multiplicative in the exponent.
      simpa [e] using
        primeToResidueCharacteristic_mul (A := A) hdprime hprime₀
    have hdiv_mul : ∀ P : MaximalSpectrum (integralClosure A L),
        ramificationIdx (maximalIdeal A) P.asIdeal ∣ e := by
      intro P
      rcases hdiv P with ⟨k, hk⟩
      refine ⟨d * k, ?_⟩
      calc
        e = d * e₀ := rfl
        _ = d * (ramificationIdx (maximalIdeal A) P.asIdeal * k) := by rw [hk]
        _ = ramificationIdx (maximalIdeal A) P.asIdeal * (d * k) := by ring
    -- The remaining source-faithful blocker is now isolated in the canonical branch-cover helper.
    simpa [e] using
      exists_uniformizer_root_tensor_branch_unramified_cover
        (A := A) (L := L) (π := π) (e := e) he hprime hdiv_mul
  tfae_finish

end
