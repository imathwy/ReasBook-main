import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_112_5
import StacksProject_2024.stacks_project.Chap10.Lemma_10_96_3
import StacksProject_2024.stacks_project.Chap10.Lemma_10_96_6
import StacksProject_2024.stacks_project.Chap10.Lemma_10_97_2
import StacksProject_2024.stacks_project.Chap10.Lemma_10_97_3
import StacksProject_2024.stacks_project.Chap10.Lemma_10_97_6
import StacksProject_2024.stacks_project.Chap15.Lemma_15_18_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_43_9
import StacksProject_2024.stacks_project.Chap15.Lemma_15_51_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_51_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open IsLocalRing
open scoped TensorProduct

namespace FieldAlgebraProperty

/-- Property `(B)` is the prime-local criterion for a field-algebra property over a fixed ground
field. -/
class HasPropertyB (P : FieldAlgebraProperty) : Prop where
  /-- The property `P` can be checked on all prime localizations of a Noetherian algebra. -/
  localizationCriterion (k A : Type u) [Field k] [CommRing A] [Algebra k A]
      [IsNoetherianRing A] :
      P k A ↔ ∀ p : PrimeSpectrum A, P k (Localization.AtPrime p.asIdeal)

/-- Property `(D)` is faithfully flat descent for closed fibers of local ring maps. -/
class HasPropertyD (P : FieldAlgebraProperty) : Prop where
  /-- If `B → C` is faithfully flat local and the closed fiber over `A → C` has `P`, then the
  closed fiber over `A → B` has `P` as well. -/
  closedFiberDescent (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
      [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]
      (hBC : RingHom.FaithfullyFlat (algebraMap B C))
      (hC : P (ResidueField A) ((maximalIdeal A).Fiber C)) :
      P (ResidueField A) ((maximalIdeal A).Fiber B)

end FieldAlgebraProperty

namespace Algebra

section

variable (P : FieldAlgebraProperty)

variable {A : Type u} [CommRing A]
variable (I : Ideal A)
variable [P.HasPropertyB] [P.HasPropertyD]

/- Domain sampling pass:
- primary domain: Chapter 15 formal fibers of adic completion maps for `P`-rings in Noetherian
  commutative algebra;
- sampled owner declarations:
  `IsPRing`,
  `FieldAlgebraProperty.HasPropertyB`,
  `FieldAlgebraProperty.HasPropertyD`,
  `completed_localization_formalFibers_haveProperty_of_quasiFiniteAt`,
  `LocalFormalFibersHaveProperty`;
- best owner abstraction: the source-facing owner is still `IsPRing P A`; this lemma is not a new
  owner, but a `bridge/view` from the local formal-fiber owner to the concrete fiber algebra of
  the global completion map `A → AdicCompletion I A`;
- primitive data: the owner hypothesis `IsPRing P A` together with the transfer/descent axioms
  `(B)` and `(D)`;
- derived API: the specific fiberwise consequence for `p.asIdeal.Fiber (AdicCompletion I A)`.

Source/core/bridge triage:
- `source-facing`: `completion_fibers_have_property_of_pRing`;
- `core/canonical`: `IsPRing`, `P.HasPropertyB`, and `P.HasPropertyD`;
- `bridge/view`: the comparison between the global completion fiber over `p` and the relevant
  completed local fiber used in the descent argument.

Refinement note: the theorem should not expose `[IsNoetherianRing A]` as primitive public data,
because that structure is already part of the source-facing owner hypothesis `IsPRing P A`.
-/

-- Proof sketch: for each prime `p ⊂ A`, localize the completion map at a prime `p'` of
-- `AdicCompletion I A` above `p`. By property `(B)`, it suffices to treat the corresponding local
-- fiber ring. Compare the maximal-ideal completion of `A_p` with the completion of the localized
-- completed ring using Lemma `15.43.9`, then use faithful flatness of the completion map and
-- property `(D)` to descend `P` from the completed local fiber. Finally invoke the `P`-ring
-- hypothesis on `A`.
/-- Helper for Lemma 15.51.6: for a local ring, the quotient by the maximal ideal agrees with the
canonical local residue field. -/
private noncomputable abbrev maximalIdeal_residueField_equiv
    (R : Type*) [CommRing R] [IsLocalRing R] :
    (maximalIdeal R).ResidueField ≃+* ResidueField R :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).symm

/-- Helper for Lemma 15.51.6: localizing at a prime does not change its residue field. -/
private noncomputable abbrev prime_localization_residueField_equiv
    {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] :
    ResidueField (Localization.AtPrime p) ≃+* p.ResidueField :=
  (maximalIdeal_residueField_equiv (Localization.AtPrime p)).symm.trans
    (by
      change (maximalIdeal (Localization.AtPrime p)).ResidueField ≃+* ResidueField (Localization.AtPrime p)
      exact maximalIdeal_residueField_equiv (Localization.AtPrime p))

/-- Helper for Lemma 15.51.6: a surjective local homomorphism induces a bijection on residue
fields. -/
private theorem residueField_bijective_of_surjective_localHom
    {R : Type u} {S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Nontrivial S]
    (f : R →+* S) (hf_surj : Function.Surjective f) [IsLocalHom f] :
    Function.Bijective (ResidueField.map f) := by
  constructor
  · exact RingHom.injective (ResidueField.map f)
  · intro z
    -- Proof comment: lift a target residue class to `S`, then lift that element across the
    -- surjective local map.
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨a, rfl⟩ := hf_surj b
    refine ⟨IsLocalRing.residue R a, ?_⟩
    simpa using IsLocalRing.ResidueField.map_residue f a

/-- Helper for Lemma 15.51.6: after localizing at `q`, the closed fiber is exactly the `q`-fiber
written in prime-pair form. -/
private theorem prime_localization_closedFiber_compare
    (q : PrimeSpectrum A)
    {S : Type u} [CommRing S] [Algebra A S]
    [Algebra (Localization.AtPrime q.asIdeal) S]
    [IsScalarTower A (Localization.AtPrime q.asIdeal) S] :
    P (ResidueField (Localization.AtPrime q.asIdeal))
      ((maximalIdeal (Localization.AtPrime q.asIdeal)).Fiber S) ↔
      P q.asIdeal.ResidueField (q.asIdeal.Fiber S) := by
  constructor
  · intro h
    -- Proof comment: both presentations are definitionally the same fiber algebra.
    simpa using h
  · intro h
    -- Proof comment: rewrite the prime-pair presentation back to the closed-fiber notation.
    simpa using h

/-- Helper for Lemma 15.51.6: quotienting the `I`-adic completion by the extended ideal `I`
recovers the quotient `A / I`. -/
private noncomputable abbrev completion_quotientBy_extendedIdeal_algEquiv
    [IsNoetherianRing A] :
    (AdicCompletion I A ⧸ Ideal.map (algebraMap A (AdicCompletion I A)) I) ≃ₐ[A]
      A ⧸ I :=
  (Ideal.quotientEquivAlgOfEq A
      (by
        simp [pow_one])).trans <|
    ((Ideal.quotientEquivAlgOfEq A
      (completionIdeal_pow_eq_ker_evalₐ (I := I)
        (Ideal.fg_of_isNoetherianRing I) 1)).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := AdicCompletion.evalₐ I 1)
      (AdicCompletion.surjective_evalₐ I 1))).trans
      (Ideal.quotientEquivAlgOfEq A (pow_one I))

/-- Helper for Lemma 15.51.6: each fiber of the completion map is Noetherian because the
completion ring is Noetherian. -/
private theorem completion_fiber_isNoetherianRing
    [IsNoetherianRing A]
    (p : PrimeSpectrum A) :
    IsNoetherianRing (p.asIdeal.Fiber (AdicCompletion I A)) := by
  let Λ := AdicCompletion I A
  let _ : IsNoetherianRing Λ := adicCompletion_isNoetherianRing (R := A) I
  -- Proof comment: commute the tensor factors so the fiber is viewed as an essentially finite type
  -- `Λ`-algebra.
  let _ : Algebra.EssFiniteType Λ (Λ ⊗[A] p.asIdeal.ResidueField) := inferInstance
  let _ : IsNoetherianRing (Λ ⊗[A] p.asIdeal.ResidueField) :=
    Algebra.EssFiniteType.isNoetherianRing Λ (Λ ⊗[A] p.asIdeal.ResidueField)
  exact
    isNoetherianRing_of_ringEquiv (Λ ⊗[A] p.asIdeal.ResidueField)
      (Algebra.TensorProduct.comm A p.asIdeal.ResidueField Λ).toRingEquiv.symm

/-- Helper for Lemma 15.51.6: the localization of the fixed fiber at the prime corresponding to
`q` is the canonical local fiber ring at `q`. -/
private theorem completion_preimageEquivFiber_asIdeal_comap
    (p : PrimeSpectrum A) (q : PrimeSpectrum (AdicCompletion I A))
    (hq : PrimeSpectrum.comap (algebraMap A (AdicCompletion I A)) q = p) :
    Ideal.comap Algebra.TensorProduct.includeRight.toRingHom
      ((PrimeSpectrum.preimageEquivFiber A (AdicCompletion I A) p ⟨q, hq⟩).asIdeal) = q.asIdeal := by
  -- Proof comment: specialize the canonical fixed-fiber contraction lemma to the completion map.
  exact preimageEquivFiber_asIdeal_comap (R := A) (S := AdicCompletion I A) p q hq

/-- Helper for Lemma 15.51.6: the localization of the fixed fiber at the prime corresponding to
`q` is the canonical local fiber ring at `q`. -/
private theorem completion_fiber_local_ringAt_over_eq
    (p : PrimeSpectrum A) (q : PrimeSpectrum (AdicCompletion I A))
    (hq : PrimeSpectrum.comap (algebraMap A (AdicCompletion I A)) q = p) :
    P p.asIdeal.ResidueField
      (Localization.AtPrime
        ((PrimeSpectrum.preimageEquivFiber A (AdicCompletion I A) p ⟨q, hq⟩).asIdeal)) ↔
      P (q.asIdeal.under A).ResidueField
        (fiberLocalRingAt A (AdicCompletion I A) q) := by
  -- Proof comment: `fiberLocalRingAt` is defined to be exactly this prime localization of the
  -- fixed fiber, and `hq` identifies the base residue field.
  simpa [fiberLocalRingAt, fiberPrimeAt, hq]

/-- Helper for Lemma 15.51.6: property `(B)` on the fixed fiber over `p` is equivalent to checking
all prime local fibers above primes of the completion lying over `p`. -/
private theorem completion_fiber_property_iff_forall_prime_local_fibers
    [IsNoetherianRing A]
    (p : PrimeSpectrum A) :
    P p.asIdeal.ResidueField (p.asIdeal.Fiber (AdicCompletion I A)) ↔
      ∀ q : PrimeSpectrum (AdicCompletion I A),
        PrimeSpectrum.comap (algebraMap A (AdicCompletion I A)) q = p →
          P (q.asIdeal.under A).ResidueField
            (fiberLocalRingAt A (AdicCompletion I A) q) := by
  let B := p.asIdeal.Fiber (AdicCompletion I A)
  let _ : IsNoetherianRing B := completion_fiber_isNoetherianRing (A := A) (I := I) p
  have hcriterion :
      P p.asIdeal.ResidueField B ↔
        ∀ Q : PrimeSpectrum B,
          P p.asIdeal.ResidueField (Localization.AtPrime Q.asIdeal) :=
    FieldAlgebraProperty.HasPropertyB.localizationCriterion (P := P) p.asIdeal.ResidueField B
  -- Proof comment: apply `(B)` to the fixed fiber and then reindex its prime spectrum by the
  -- standard correspondence with primes of the completion lying over `p`.
  constructor
  · intro hP q hq
    have hlocal :
        ∀ Q : PrimeSpectrum B,
          P p.asIdeal.ResidueField (Localization.AtPrime Q.asIdeal) :=
      hcriterion.1 hP
    exact
      (completion_fiber_local_ringAt_over_eq (P := P) (A := A) (I := I) p q hq).1 <|
        hlocal (PrimeSpectrum.preimageEquivFiber A (AdicCompletion I A) p ⟨q, hq⟩)
  · intro hlocal
    refine hcriterion.2 ?_
    intro Q
    let q := (PrimeSpectrum.preimageEquivFiber A (AdicCompletion I A) p).symm Q
    -- Proof comment: rewrite the abstract prime of the fixed fiber back to the corresponding
    -- prime of the completion, then invoke the local hypothesis there.
    have hQ :
        (PrimeSpectrum.preimageEquivFiber A (AdicCompletion I A) p) q = Q :=
      (PrimeSpectrum.preimageEquivFiber A (AdicCompletion I A) p).apply_symm_apply Q
    have hQideal :
        ((PrimeSpectrum.preimageEquivFiber A (AdicCompletion I A) p) q).asIdeal = Q.asIdeal :=
      congrArg PrimeSpectrum.asIdeal hQ
    have hlocalq :
        P (q.1.asIdeal.under A).ResidueField (fiberLocalRingAt A (AdicCompletion I A) q.1) :=
      hlocal q.1 q.2
    have hrew :
        P p.asIdeal.ResidueField (Localization.AtPrime Q.asIdeal) := by
      simpa [hQideal] using
        (completion_fiber_local_ringAt_over_eq (P := P) (A := A) (I := I) p q.1 q.2).2 hlocalq
    exact hrew

/-- Helper for Lemma 15.51.6: every prime of the fixed completion fiber specializes to a closed
point of that same fixed fiber. -/
private theorem completion_fiber_prime_over_closed_specialization_exists
    [IsNoetherianRing A]
    (p : PrimeSpectrum A) (q : PrimeSpectrum (AdicCompletion I A))
    (hq : PrimeSpectrum.comap (algebraMap A (AdicCompletion I A)) q = p) :
    ∃ q' : PrimeSpectrum (AdicCompletion I A),
      ∃ hq' : PrimeSpectrum.comap (algebraMap A (AdicCompletion I A)) q' = p,
        q.asIdeal ≤ q'.asIdeal ∧
        ((PrimeSpectrum.preimageOrderIsoFiber A (AdicCompletion I A) p) ⟨q', hq'⟩).asIdeal.IsMaximal := by
  classical
  let e := PrimeSpectrum.preimageOrderIsoFiber A (AdicCompletion I A) p
  let Q : PrimeSpectrum (p.asIdeal.Fiber (AdicCompletion I A)) := e ⟨q, hq⟩
  -- Proof comment: choose a maximal specialization of the corresponding prime inside the fixed
  -- fiber, then transport it back across the fiber/order equivalence.
  obtain ⟨mF, hmFmax, hQmF⟩ := Q.asIdeal.exists_le_maximal Q.2.1
  let M : PrimeSpectrum (p.asIdeal.Fiber (AdicCompletion I A)) := ⟨mF, hmFmax.isPrime⟩
  let q'over : PrimeSpectrum.comap (algebraMap A (AdicCompletion I A)) ⁻¹' {p} := e.symm M
  refine ⟨q'over.1, q'over.2, ?_, ?_⟩
  · have hQM : Q ≤ M := hQmF
    simpa [Q, q'over] using (e.symm.monotone hQM : e.symm Q ≤ e.symm M)
  · have hmaxM : M.asIdeal.IsMaximal := by
      simpa [M] using hmFmax
    simpa [q'over, e] using hmaxM

/-- Helper for Lemma 15.51.6: quotienting the completion by a maximal ideal recovers the
corresponding quotient of the source ring. -/
private noncomputable theorem completion_maximal_local_quotient_equiv
    [IsNoetherianRing A]
    (m' : MaximalSpectrum (AdicCompletion I A)) :
    let Λ := AdicCompletion I A
    let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
    let p : PrimeSpectrum A := q.asIdeal.under A
    (A ⧸ p.asIdeal) ≃+* (Λ ⧸ q.asIdeal) := by
  let Λ := AdicCompletion I A
  let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
  let p : PrimeSpectrum A := q.asIdeal.under A
  let eI := completion_quotientBy_extendedIdeal_algEquiv (A := A) I
  have hIq :
      Ideal.map (algebraMap A Λ) I ≤ q.asIdeal := by
    -- Proof comment: the extended completion ideal lies in the Jacobson radical, hence in every
    -- maximal ideal of the completion.
    exact
      le_trans
        (completion_ideal_le_jacobson (R := A) I)
        (Ring.jacobson_le_of_isMaximal q.asIdeal)
  let χ : A ⧸ p.asIdeal →+* Λ ⧸ q.asIdeal := by
    -- Proof comment: the contraction of `q` is exactly `p`, so the source quotient map is the
    -- canonical quotient map induced by `A → Λ`.
    change A ⧸ Ideal.comap (algebraMap A Λ) q.asIdeal →+* Λ ⧸ q.asIdeal
    exact Ideal.quotientMap q.asIdeal (algebraMap A Λ) le_rfl
  have hχ_inj : Function.Injective χ := by
    -- Proof comment: quotienting by the contracted ideal is the injective case of
    -- `Ideal.quotientMap`.
    change Function.Injective (Ideal.quotientMap q.asIdeal (algebraMap A Λ) le_rfl)
    exact Ideal.quotientMap_injective
  have hχ_surj : Function.Surjective χ := by
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    let xI : Λ ⧸ Ideal.map (algebraMap A Λ) I := Ideal.Quotient.mk _ x
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (eI xI)
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    have hcomm :
        eI (Ideal.Quotient.mk (Ideal.map (algebraMap A Λ) I) (algebraMap A Λ a)) =
          Ideal.Quotient.mk I a := by
      -- Proof comment: the completion quotient equivalence is an `A`-algebra equivalence.
      change eI (algebraMap A (Λ ⧸ Ideal.map (algebraMap A Λ) I) a) =
        algebraMap A (A ⧸ I) a
      simpa using eI.commutes a
    have hx_eq :
        xI = Ideal.Quotient.mk (Ideal.map (algebraMap A Λ) I) (algebraMap A Λ a) := by
      -- Proof comment: after identifying both classes modulo `I`, the chosen representative
      -- already comes from the source ring.
      apply eI.injective
      rw [hcomm]
      exact ha.symm
    have hmemI :
        x - algebraMap A Λ a ∈ Ideal.map (algebraMap A Λ) I := by
      exact Ideal.Quotient.eq.mp (by simpa [xI] using hx_eq)
    -- Proof comment: the difference already lies in the extended completion ideal, which sits in
    -- `q`, so the quotient class modulo `q` comes from `a`.
    symm
    apply Ideal.Quotient.eq.mpr
    exact hIq hmemI
  exact RingEquiv.ofBijective χ ⟨hχ_inj, hχ_surj⟩

/-- Helper for Lemma 15.51.6: the contraction of a maximal ideal of the completion is maximal in
the source ring. -/
private theorem completion_maximal_local_sourcePrime_isMaximal
    [IsNoetherianRing A]
    (m' : MaximalSpectrum (AdicCompletion I A)) :
    let Λ := AdicCompletion I A
    let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
    let p : PrimeSpectrum A := q.asIdeal.under A
    p.asIdeal.IsMaximal := by
  let Λ := AdicCompletion I A
  let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
  let p : PrimeSpectrum A := q.asIdeal.under A
  let e := completion_maximal_local_quotient_equiv (A := A) (I := I) m'
  let _ : Field (Λ ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal
  have hpField : IsField (A ⧸ p.asIdeal) :=
    e.toMulEquiv.isField (Field.toIsField (Λ ⧸ q.asIdeal))
  -- Proof comment: a quotient ring is a field exactly when the defining ideal is maximal.
  exact Ideal.Quotient.maximal_of_isField p.asIdeal hpField

/-- Helper for Lemma 15.51.6: a maximal ideal `q` of the completion is exactly the image of its
contracted maximal ideal `p` in the source ring. -/
private theorem completion_maximal_local_targetIdeal_eq
    [IsNoetherianRing A]
    (m' : MaximalSpectrum (AdicCompletion I A)) :
    let Λ := AdicCompletion I A
    let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
    let p : PrimeSpectrum A := q.asIdeal.under A
    Ideal.map (algebraMap A Λ) p.asIdeal = q.asIdeal := by
  let Λ := AdicCompletion I A
  let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
  let p : PrimeSpectrum A := q.asIdeal.under A
  let eI := completion_quotientBy_extendedIdeal_algEquiv (A := A) I
  have hIq :
      Ideal.map (algebraMap A Λ) I ≤ q.asIdeal := by
    -- Proof comment: the extended completion ideal lies in every maximal ideal of the completion.
    exact
      le_trans
        (completion_ideal_le_jacobson (R := A) I)
        (Ring.jacobson_le_of_isMaximal q.asIdeal)
  have hIp : I ≤ p.asIdeal := by
    -- Proof comment: contract the containment `IΛ ⊆ q` back to the source ring.
    intro a ha
    change algebraMap A Λ a ∈ q.asIdeal
    exact hIq (Ideal.mem_map_of_mem (algebraMap A Λ) ha)
  apply le_antisymm
  · exact Ideal.map_le_iff_le_comap.mpr le_rfl
  · intro x hxq
    let xI : Λ ⧸ Ideal.map (algebraMap A Λ) I := Ideal.Quotient.mk _ x
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (eI xI)
    have hcomm :
        eI (Ideal.Quotient.mk (Ideal.map (algebraMap A Λ) I) (algebraMap A Λ a)) =
          Ideal.Quotient.mk I a := by
      -- Proof comment: the quotient comparison is an `A`-algebra map on source elements.
      change eI (algebraMap A (Λ ⧸ Ideal.map (algebraMap A Λ) I) a) =
        algebraMap A (A ⧸ I) a
      simpa using eI.commutes a
    have hx_eq :
        xI = Ideal.Quotient.mk (Ideal.map (algebraMap A Λ) I) (algebraMap A Λ a) := by
      -- Proof comment: modulo the extended completion ideal, every class comes from `A`.
      apply eI.injective
      rw [hcomm]
      exact ha.symm
    have hdiffI :
        x - algebraMap A Λ a ∈ Ideal.map (algebraMap A Λ) I := by
      exact Ideal.Quotient.eq.mp (by simpa [xI] using hx_eq)
    have hdiffq :
        x - algebraMap A Λ a ∈ q.asIdeal :=
      hIq hdiffI
    have haq :
        algebraMap A Λ a ∈ q.asIdeal := by
      -- Proof comment: subtract the known `IΛ`-difference from `x ∈ q`.
      have hs :
          x + -(x - algebraMap A Λ a) ∈ q.asIdeal :=
        q.asIdeal.add_mem hxq (q.asIdeal.neg_mem hdiffq)
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hs
    have hap :
        a ∈ p.asIdeal := by
      simpa [p] using haq
    have hdiffp :
        x - algebraMap A Λ a ∈ Ideal.map (algebraMap A Λ) p.asIdeal :=
      Ideal.map_mono hIp hdiffI
    have hmapa :
        algebraMap A Λ a ∈ Ideal.map (algebraMap A Λ) p.asIdeal :=
      Ideal.mem_map_of_mem (algebraMap A Λ) hap
    -- Proof comment: both pieces lie in the image of `p`, so `x` does as well.
    have hs :
        (x - algebraMap A Λ a) + algebraMap A Λ a ∈
          Ideal.map (algebraMap A Λ) p.asIdeal :=
      Ideal.add_mem _ hdiffp hmapa
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hs

/-- Helper for Lemma 15.51.6: localizing the equality `pA^∧ = q` gives the equality of maximal
ideals for the branch-local map `A_p → (A^∧)_q`. -/
private theorem completion_maximal_local_map_maximalIdeal_eq
    [IsNoetherianRing A]
    (m' : MaximalSpectrum (AdicCompletion I A)) :
    let Λ := AdicCompletion I A
    let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
    let p : PrimeSpectrum A := q.asIdeal.under A
    let Ap := Localization.AtPrime p.asIdeal
    let Bq := Localization.AtPrime q.asIdeal
    Ideal.map (algebraMap Ap Bq) (maximalIdeal Ap) = maximalIdeal Bq := by
  let Λ := AdicCompletion I A
  let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
  let p : PrimeSpectrum A := q.asIdeal.under A
  let Ap := Localization.AtPrime p.asIdeal
  let Bq := Localization.AtPrime q.asIdeal
  have hqeq :
      Ideal.map (algebraMap A Λ) p.asIdeal = q.asIdeal :=
    completion_maximal_local_targetIdeal_eq (A := A) (I := I) m'
  -- Proof comment: rewrite both local maximal ideals as images of the original primes and compare
  -- them after composing the canonical localization maps.
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal Ap,
    ← IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal Bq]
  calc
    Ideal.map (algebraMap Ap Bq) (Ideal.map (algebraMap A Ap) p.asIdeal) =
        Ideal.map ((algebraMap Ap Bq).comp (algebraMap A Ap)) p.asIdeal := by
          rw [Ideal.map_map]
    _ = Ideal.map ((algebraMap Λ Bq).comp (algebraMap A Λ)) p.asIdeal := by
          rfl
    _ = Ideal.map (algebraMap Λ Bq) (Ideal.map (algebraMap A Λ) p.asIdeal) := by
          rw [Ideal.map_map]
    _ = Ideal.map (algebraMap Λ Bq) q.asIdeal := by rw [hqeq]

/-- Helper for Lemma 15.51.6: every element of `q.primeCompl` stays invertible in the closed
quotient `(A^∧) / q`. -/
private theorem completion_maximal_local_target_quotientMap_isUnit
    [IsNoetherianRing A]
    (m' : MaximalSpectrum (AdicCompletion I A)) :
    let Λ := AdicCompletion I A
    let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
    let Bq := Localization.AtPrime q.asIdeal
    ∀ s : q.asIdeal.primeCompl,
      IsUnit ((Ideal.Quotient.mk q.asIdeal) s.1) := by
  let Λ := AdicCompletion I A
  let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
  let Bq := Localization.AtPrime q.asIdeal
  intro s
  -- Proof comment: modulo a prime ideal, any element outside the prime remains nonzero, hence a
  -- unit in the resulting field.
  refine isUnit_iff_ne_zero.mpr ?_
  intro hs
  exact s.2 <| Ideal.Quotient.eq_zero_iff_mem.mp hs

/-- Helper for Lemma 15.51.6: the localization `(A^∧)_q` maps onto the closed quotient
`(A^∧) / q`. -/
private noncomputable abbrev completion_maximal_local_target_quotientMap
    [IsNoetherianRing A]
    (m' : MaximalSpectrum (AdicCompletion I A)) :
    let Λ := AdicCompletion I A
    let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
    let Bq := Localization.AtPrime q.asIdeal
    Bq →+* (Λ ⧸ q.asIdeal) :=
  let Λ := AdicCompletion I A
  let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
  let Bq := Localization.AtPrime q.asIdeal
  IsLocalization.lift (S := Bq) (g := Ideal.Quotient.mk q.asIdeal)
    (completion_maximal_local_target_quotientMap_isUnit
      (A := A) (I := I) m')

/-- Helper for Lemma 15.51.6: the localized quotient map onto `(A^∧) / q` is surjective. -/
private theorem completion_maximal_local_target_quotientMap_surjective
    [IsNoetherianRing A]
    (m' : MaximalSpectrum (AdicCompletion I A)) :
    let Λ := AdicCompletion I A
    let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
    let Bq := Localization.AtPrime q.asIdeal
    Function.Surjective
      (completion_maximal_local_target_quotientMap (A := A) (I := I) m') := by
  let Λ := AdicCompletion I A
  let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
  let Bq := Localization.AtPrime q.asIdeal
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨algebraMap Λ Bq x, ?_⟩
  -- Proof comment: the localization lift extends the ordinary quotient map on source elements.
  simpa [completion_maximal_local_target_quotientMap] using
    (IsLocalization.lift_eq (S := Bq) (g := Ideal.Quotient.mk q.asIdeal)
      (completion_maximal_local_target_quotientMap_isUnit
        (A := A) (I := I) m') x)

/-- Helper for Lemma 15.51.6: the localized quotient map onto `(A^∧) / q` is a local
homomorphism. -/
private theorem completion_maximal_local_target_quotientMap_isLocalHom
    [IsNoetherianRing A]
    (m' : MaximalSpectrum (AdicCompletion I A)) :
    let Λ := AdicCompletion I A
    let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
    let Bq := Localization.AtPrime q.asIdeal
    IsLocalHom
      (completion_maximal_local_target_quotientMap (A := A) (I := I) m') := by
  let Λ := AdicCompletion I A
  let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
  let Bq := Localization.AtPrime q.asIdeal
  let _ : Field (Λ ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal
  exact
    Function.Surjective.isLocalHom _
      (completion_maximal_local_target_quotientMap_surjective
        (A := A) (I := I) m')

/-- Helper for Lemma 15.51.6: the residue-field map for `A_p → (A^∧)_q` should be obtained by
comparing both local residue fields with the common closed quotient `(A^∧) / q`. -/
private theorem completion_maximal_local_residueField_bijective
    [IsNoetherianRing A]
    (m' : MaximalSpectrum (AdicCompletion I A)) :
    let Λ := AdicCompletion I A
    let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
    let p : PrimeSpectrum A := q.asIdeal.under A
    let Ap := Localization.AtPrime p.asIdeal
    let Bq := Localization.AtPrime q.asIdeal
    Function.Bijective (ResidueField.map (algebraMap Ap Bq)) := by
  let Λ := AdicCompletion I A
  let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
  let p : PrimeSpectrum A := q.asIdeal.under A
  let Ap := Localization.AtPrime p.asIdeal
  let Bq := Localization.AtPrime q.asIdeal
  let _ := completion_maximal_local_quotient_equiv (A := A) (I := I) m'
  let _ := completion_maximal_local_target_quotientMap (A := A) (I := I) m'
  let _ : IsLocalHom
      (completion_maximal_local_target_quotientMap (A := A) (I := I) m') :=
    completion_maximal_local_target_quotientMap_isLocalHom
      (A := A) (I := I) m'
  -- Route correction: the remaining proof obligation is now isolated to the source-faithful
  -- quotient comparison `A / p ≃ (A^∧) / q`, which should identify the residue fields of `A_p`
  -- and `(A^∧)_q` after passing through the two surjective local quotient maps.
  --
  -- TODO: define the source quotient map `Ap → A / p`, prove that postcomposing it with
  -- `completion_maximal_local_quotient_equiv` matches
  -- `completion_maximal_local_target_quotientMap.comp (algebraMap Ap Bq)` by localization
  -- uniqueness, and then deduce the residue-field bijection from the two surjective local maps.
  sorry

/-- Helper for Lemma 15.51.6: the maximal-ideal completions of `A_p` and `(A^∧)_q` are
canonically equivalent once the local residue fields are identified. -/
private noncomputable theorem completion_maximal_local_completion_equiv
    [IsNoetherianRing A]
    (m' : MaximalSpectrum (AdicCompletion I A)) :
    let Λ := AdicCompletion I A
    let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
    let p : PrimeSpectrum A := q.asIdeal.under A
    let Ap := Localization.AtPrime p.asIdeal
    let Bq := Localization.AtPrime q.asIdeal
    AdicCompletion (maximalIdeal Ap) Ap ≃+*
      AdicCompletion (maximalIdeal Bq) Bq := by
  let Λ := AdicCompletion I A
  let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
  let p : PrimeSpectrum A := q.asIdeal.under A
  let Ap := Localization.AtPrime p.asIdeal
  let Bq := Localization.AtPrime q.asIdeal
  let f := Localization.localRingHom p.asIdeal q.asIdeal (algebraMap A Λ) rfl
  let _ : IsNoetherianRing Λ := adicCompletion_isNoetherianRing (R := A) I
  let _ : IsNoetherianRing Ap := inferInstance
  let _ : IsNoetherianRing Bq := inferInstance
  let _ : IsLocalHom (algebraMap Ap Bq) := by
    -- Proof comment: normalize the local branch map to the canonical algebra map.
    simpa [f] using
      (Localization.isLocalHom_localRingHom
        p.asIdeal q.asIdeal (algebraMap A Λ) rfl)
  let _ : Module.Flat Ap Bq :=
    RingHom.flat_algebraMap_iff.mp <| by
      -- Proof comment: completion is flat, and localizing the branch preserves flatness.
      simpa [f] using
        (RingHom.Flat.localRingHom
          (adicCompletion_algebraMap_flat (R := A) (I := I))
          q.asIdeal p.asIdeal rfl)
  have hmax :
      Ideal.map (algebraMap Ap Bq) (maximalIdeal Ap) = maximalIdeal Bq := by
    simpa [Ap, Bq, Λ, p, q] using
      completion_maximal_local_map_maximalIdeal_eq (A := A) (I := I) m'
  have hres :
      Function.Bijective (ResidueField.map (algebraMap Ap Bq)) :=
    completion_maximal_local_residueField_bijective
      (A := A) (I := I) m'
  -- Proof comment: package Lemma `15.43.9` into the ring-equivalence form needed downstream.
  exact
    RingEquiv.ofBijective
      (maximalIdealCompletionMap (algebraMap Ap Bq))
      (maximalIdealCompletionMap_bijective_of_flat_of_residueFieldBijective
        (A := Ap) (B := Bq) hmax hres)

/-- Helper for Lemma 15.51.6: the canonical map `(A^∧)_q → (A_p)^∧` obtained from the completion
comparison is faithfully flat. -/
private theorem completion_maximal_local_to_source_completion_faithfullyFlat
    [IsNoetherianRing A]
    (m' : MaximalSpectrum (AdicCompletion I A)) :
    let Λ := AdicCompletion I A
    let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
    let p : PrimeSpectrum A := q.asIdeal.under A
    let Ap := Localization.AtPrime p.asIdeal
    let Bq := Localization.AtPrime q.asIdeal
    let C := AdicCompletion (maximalIdeal Ap) Ap
    let g : Bq →+* C :=
      (completion_maximal_local_completion_equiv
        (A := A) (I := I) m').symm.toRingHom.comp
        (algebraMap Bq (AdicCompletion (maximalIdeal Bq) Bq))
    RingHom.FaithfullyFlat g := by
  let Λ := AdicCompletion I A
  let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
  let p : PrimeSpectrum A := q.asIdeal.under A
  let Ap := Localization.AtPrime p.asIdeal
  let Bq := Localization.AtPrime q.asIdeal
  let C := AdicCompletion (maximalIdeal Ap) Ap
  let e :=
    completion_maximal_local_completion_equiv (A := A) (I := I) m'
  let g : Bq →+* C :=
    e.symm.toRingHom.comp (algebraMap Bq (AdicCompletion (maximalIdeal Bq) Bq))
  have hff_completion :
      RingHom.FaithfullyFlat
        (algebraMap Bq (AdicCompletion (maximalIdeal Bq) Bq)) :=
    maximalIdeal_adicCompletion_algebraMap_faithfullyFlat Bq
  have hff_equiv : RingHom.FaithfullyFlat e.symm.toRingHom :=
    RingHom.FaithfullyFlat.of_bijective e.symm.bijective
  -- Proof comment: compose the faithfully flat completion map with the inverse completion
  -- equivalence.
  simpa [g] using RingHom.FaithfullyFlat.comp hff_completion hff_equiv

/-- Helper for Lemma 15.51.6: the source-faithful maximal-local block at `q` is the remaining
local comparison step after identifying `A / p` with `(A^∧) / q`. -/
private theorem completion_maximal_localFiber_hasProperty
    [IsNoetherianRing A]
    (hA : IsPRing P A)
    (m' : MaximalSpectrum (AdicCompletion I A)) :
    let q : PrimeSpectrum (AdicCompletion I A) := m'.toPrimeSpectrum
    P (q.asIdeal.under A).ResidueField (fiberLocalRingAt A (AdicCompletion I A) q) := by
  let Λ := AdicCompletion I A
  let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
  let p : PrimeSpectrum A := q.asIdeal.under A
  let Ap := Localization.AtPrime p.asIdeal
  let Bq := Localization.AtPrime q.asIdeal
  let f := Localization.localRingHom p.asIdeal q.asIdeal (algebraMap A Λ) rfl
  let _ : IsNoetherianRing Λ := adicCompletion_isNoetherianRing (R := A) I
  let _ : IsNoetherianRing Ap := inferInstance
  let _ : IsNoetherianRing Bq := inferInstance
  have hflat : f.Flat := by
    -- Proof comment: completion is flat and flatness survives localization at the chosen branch.
    exact
      RingHom.Flat.localRingHom
        (adicCompletion_algebraMap_flat (R := A) (I := I))
        q.asIdeal p.asIdeal rfl
  let _ : IsLocalHom (algebraMap Ap Bq) := by
    -- Proof comment: normalize the local branch map to the canonical algebra map.
    simpa [f] using
      (Localization.isLocalHom_localRingHom
        p.asIdeal q.asIdeal (algebraMap A Λ) rfl)
  let _ : Module.Flat Ap Bq :=
    RingHom.flat_algebraMap_iff.mp <| by
      simpa [f] using hflat
  let C := AdicCompletion (maximalIdeal Ap) Ap
  let e :=
    completion_maximal_local_completion_equiv (A := A) (I := I) m'
  let g : Bq →+* C :=
    e.symm.toRingHom.comp (algebraMap Bq (AdicCompletion (maximalIdeal Bq) Bq))
  let _ : Algebra Bq C := g.toAlgebra
  have hg_comp :
      g.comp (algebraMap Ap Bq) = algebraMap Ap C := by
    ext a
    -- Proof comment: after postcomposing with the completion comparison equivalence, both maps
    -- become the canonical completion map `Ap → (Bq)^∧`.
    apply e.toRingHom.injective
    change (algebraMap Ap (AdicCompletion (maximalIdeal Bq) Bq)) a =
      e ((algebraMap Ap C) a)
    simpa [g, e] using
      DFunLike.congr_fun (maximalIdealCompletionMap_comp (algebraMap Ap Bq)) a
  let _ : IsScalarTower Ap Bq C := IsScalarTower.of_algebraMap_eq' hg_comp
  let _ : IsLocalHom (algebraMap Bq C) := by
    let _ : IsLocalHom e.symm.toRingHom :=
      Function.Surjective.isLocalHom _ e.symm.surjective
    -- Proof comment: the transported map to the source completion is a composite of local maps.
    simpa [g, RingHom.algebraMap_toAlgebra] using
      (inferInstance :
        IsLocalHom
          (e.symm.toRingHom.comp
            (algebraMap Bq (AdicCompletion (maximalIdeal Bq) Bq))))
  have hC :
      P (ResidueField Ap) ((maximalIdeal Ap).Fiber C) := by
    -- Proof comment: this is exactly the `P`-ring formal fiber of `A` at the prime `p`,
    -- rewritten from prime-pair notation to the local closed fiber over `A_p`.
    exact
      (prime_localization_closedFiber_compare
        (P := P) (A := A) (q := p) (S := C)).2 <|
        hA.satisfiesPPrimePairCondition p p le_rfl
  have hBq_closed :
      P (ResidueField Ap) ((maximalIdeal Ap).Fiber Bq) := by
    -- Proof comment: property `(D)` now descends the closed-fiber property from `(A_p)^∧` back
    -- to the localized completion `(A^∧)_q`.
    exact
      FieldAlgebraProperty.HasPropertyD.closedFiberDescent
        (P := P) Ap Bq C
        (hBC := by
          simpa [g, RingHom.algebraMap_toAlgebra] using
            completion_maximal_local_to_source_completion_faithfullyFlat
              (A := A) (I := I) m')
        hC
  -- Proof comment: rewrite the descended closed fiber of `A_p → (A^∧)_q` back to the source
  -- local fiber ring at `q`.
  simpa [Ap, Bq, Λ, p, q, fiberLocalRingAt, fiberPrimeAt] using
    (prime_localization_closedFiber_compare
      (P := P) (A := A) (q := p) (S := Bq)).1 hBq_closed

/-- Lemma 15.51.6: if `A` is a `P`-ring, where `P` satisfies `(B)` and `(D)`, then for every
prime `p` of `A` the fiber ring of the completion map `A → AdicCompletion I A` over `p` has
property `P` over `κ(p)`. -/
theorem completion_fibers_have_property_of_pRing
    (hA : IsPRing P A)
    (p : PrimeSpectrum A) :
    P p.asIdeal.ResidueField (p.asIdeal.Fiber (AdicCompletion I A)) := by
  letI : IsNoetherianRing A := hA.toIsNoetherian
  let Λ := AdicCompletion I A
  letI : IsNoetherianRing Λ := adicCompletion_isNoetherianRing (R := A) I
  let _ := completion_quotientBy_extendedIdeal_algEquiv (A := A) I
  let _ := prime_localization_residueField_equiv p.asIdeal
  -- Route correction: switch to the source theorem's actual endgame. Rather than transporting
  -- from a chosen closed specialization in the fixed fiber back to an arbitrary prime, apply the
  -- maximal-local criterion for `A → A^∧` and isolate the local comparison only at maximal ideals
  -- of the completion.
  have hmax :
      ∀ m' : MaximalSpectrum Λ,
        let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
        P (q.asIdeal.under A).ResidueField (fiberLocalRingAt A Λ q) := by
    intro m'
    simpa [Λ] using
      completion_maximal_localFiber_hasProperty
        (P := P) (A := A) (I := I) hA m'
  -- Proof comment: clause `(3) → (1)` of Lemma `15.51.2` now finishes the global fiber theorem.
  exact
    ((fiberProperty_tfae (P := P) (R := A) (Λ := Λ)).out 2 0).mp hmax p

end

end Algebra

end
