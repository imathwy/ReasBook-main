import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_105_8 (from Chap10) -/
noncomputable section

universe u v

open Ideal PrimeSpectrum TopologicalSpace Order
open scoped PrimeSpectrum

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-
Domain-style sampling in the catenary API:
- topological owner: `CatenarySpace (PrimeSpectrum R)`
- ring owner: `IsCatenaryRing R`
- universal owner: `UniversallyCatenaryRing R`
- layer here: `bridge/view`, since this item characterizes the existing owners through quotients by
  minimal primes

Primitive data already belongs to the owner abstractions from `Lemma_10_105_2` and
`Definition_10_105_3`; this file should only expose the minimal-prime reduction theorems.
-/

/-- Helper for Lemma 10.105.8: points of the irreducible closed set attached to a prime are
exactly the primes specializing from it. -/
private theorem mem_pointsEquivIrreducibleCloseds_iff_le
    (p q : PrimeSpectrum R) :
    p ∈ ((show IrreducibleCloseds (PrimeSpectrum R) from
      PrimeSpectrum.pointsEquivIrreducibleCloseds R q) : Set (PrimeSpectrum R)) ↔ q ≤ p := by
  -- Rewrite the irreducible closed set attached to `q` as `closure {q}` and read off
  -- specialization.
  rw [show ((show IrreducibleCloseds (PrimeSpectrum R) from
      PrimeSpectrum.pointsEquivIrreducibleCloseds R q) : Set (PrimeSpectrum R)) =
      closure ({q} : Set (PrimeSpectrum R)) by rfl]
  rw [← specializes_iff_mem_closure, le_iff_specializes]

/-- Helper for Lemma 10.105.8: for a closed subtype, mapping an irreducible closed subset to the
ambient space is just its set-theoretic image. -/
private theorem map_subtype_val_eq_image_of_isClosed
    {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsClosed S)
    (T : IrreducibleCloseds S) :
    ((IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T :
        IrreducibleCloseds X) : Set X) =
      (Subtype.val : S → X) '' (T : Set S) := by
  -- Closedness of the subtype image keeps the closure built into `IrreducibleCloseds.map`
  -- from enlarging the set.
  rw [IrreducibleCloseds.coe_map, closure_eq_iff_isClosed]
  exact hS.isClosedMap_subtype_val _ T.isClosed

/-- Helper for Lemma 10.105.8: an ambient irreducible closed subset contained in a closed subtype
pulls back to an irreducible closed subset of that subtype. -/
private noncomputable def preimage_irreducibleClosed_of_subset
    {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsClosed S)
    (T : IrreducibleCloseds X) (hTS : (T : Set X) ⊆ S) :
    IrreducibleCloseds S := by
  refine ⟨Subtype.val ⁻¹' (T : Set X), ?_, T.isClosed.preimage continuous_subtype_val⟩
  -- The preimage is homeomorphic to `T`, because every point of `T` already lies in `S`.
  let e : (Subtype.val ⁻¹' (T : Set X) : Set S) ≃ₜ (T : Set X) :=
    hS.isClosedEmbedding_subtypeVal.isEmbedding.homeomorphOfSubsetRange fun x hx ↦
      ⟨⟨x, hTS hx⟩, rfl⟩
  exact (isIrreducible_iff_irreducibleSpace).2 <|
    (e.irreducibleSpace_iff).2 (Subtype.irreducibleSpace T.isIrreducible)

/-- Helper for Lemma 10.105.8: the ambient image of an irreducible closed subset of a closed
subspace still lies inside that subspace. -/
private theorem map_subtype_val_subset_of_isClosed
    {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsClosed S)
    (T : IrreducibleCloseds S) :
    ((IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T :
        IrreducibleCloseds X) : Set X) ⊆ S := by
  -- After rewriting the mapped subset as an image, the subtype condition gives the inclusion.
  rw [map_subtype_val_eq_image_of_isClosed hS T]
  rintro x ⟨y, hy, rfl⟩
  exact y.2

/-- Helper for Lemma 10.105.8: pulling an irreducible closed subset back to a closed subtype and
then mapping it to the ambient space recovers the original subset. -/
@[simp] private theorem map_preimage_irreducibleClosed_of_subset
    {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsClosed S)
    (T : IrreducibleCloseds X) (hTS : (T : Set X) ⊆ S) :
    IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val
        (preimage_irreducibleClosed_of_subset hS T hTS) = T := by
  apply IrreducibleCloseds.ext
  ext x
  -- The image consists exactly of those points of `T`, because `T` already lies in the subtype.
  rw [map_subtype_val_eq_image_of_isClosed hS (preimage_irreducibleClosed_of_subset hS T hTS)]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hTS hx⟩, hx, rfl⟩

/-- Helper for Lemma 10.105.8: an interval of irreducible closed subsets in a closed subspace is
order-isomorphic to the corresponding ambient interval. -/
private noncomputable def closed_subspace_interval_order_iso
    {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsClosed S)
    {T T' : IrreducibleCloseds S} (_hTT' : T ≤ T') :
    Set.Icc T T' ≃o
      Set.Icc
        (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T)
        (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T') := by
  classical
  let e :
      Set.Icc T T' ≃
        Set.Icc
          (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T)
          (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T') :=
    { toFun := fun Z ↦
        -- Map each irreducible closed subset of the subtype to its ambient image.
        ⟨IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val Z.1,
          IrreducibleCloseds.map_mono continuous_subtype_val Z.2.1,
          IrreducibleCloseds.map_mono continuous_subtype_val Z.2.2⟩
      invFun := fun Z ↦
        -- Pull the ambient subset back along the closed embedding of the subtype.
        let ZS : IrreducibleCloseds S :=
          preimage_irreducibleClosed_of_subset hS Z.1
            (Set.Subset.trans Z.2.2 (map_subtype_val_subset_of_isClosed hS T'))
        ⟨ZS,
          by
            intro x hx
            change (x : X) ∈ (Z.1 : Set X)
            have hxT :
                (x : X) ∈
                  (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T :
                    Set X) := by
              rw [map_subtype_val_eq_image_of_isClosed hS T]
              exact ⟨x, hx, rfl⟩
            exact Z.2.1 hxT,
          by
            intro x hx
            have hxZ : (x : X) ∈ (Z.1 : Set X) := by
              simpa using hx
            have hxT' :
                (x : X) ∈
                  (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T' :
                    Set X) := Z.2.2 hxZ
            rw [map_subtype_val_eq_image_of_isClosed hS T'] at hxT'
            rcases hxT' with ⟨y, hy, hyx⟩
            have hyx' : y = x := Subtype.ext hyx
            simpa [hyx'] using hy⟩
      left_inv := by
        intro Z
        apply Subtype.ext
        apply IrreducibleCloseds.ext
        ext x
        -- Pulling the ambient image back along the injective subtype map gives the same subset.
        change
          (x : X) ∈
              (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val Z.1 : Set X) ↔
            x ∈ (Z.1 : Set S)
        rw [map_subtype_val_eq_image_of_isClosed hS Z.1]
        simp
      right_inv := by
        intro Z
        apply Subtype.ext
        simpa using map_preimage_irreducibleClosed_of_subset hS Z.1
          (Set.Subset.trans Z.2.2 (map_subtype_val_subset_of_isClosed hS T')) }
  exact e.toOrderIso
    (by
      intro A B hAB
      exact IrreducibleCloseds.map_mono continuous_subtype_val hAB)
    (by
      intro A B hAB
      change
        ((preimage_irreducibleClosed_of_subset hS A.1
            (Set.Subset.trans A.2.2 (map_subtype_val_subset_of_isClosed hS T')) : Set S) ⊆
          (preimage_irreducibleClosed_of_subset hS B.1
            (Set.Subset.trans B.2.2 (map_subtype_val_subset_of_isClosed hS T')) : Set S))
      intro x hx
      exact hAB (by simpa using hx))

/-- Helper for Lemma 10.105.8: relative codimension is unchanged when passing between a closed
subspace interval and the corresponding ambient interval. -/
private theorem codimBetween_closed_subspace_eq
    {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsClosed S)
    {T T' : IrreducibleCloseds S} (hTT' : T ≤ T') :
    codimBetween T T' hTT' =
      codimBetween
        (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T)
        (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T')
        (IrreducibleCloseds.map_mono continuous_subtype_val hTT') := by
  -- Compare both codimensions by transporting the interval through the closed-subspace order
  -- isomorphism.
  apply WithBot.coe_injective
  calc
    codimBetween T T' hTT' = krullDim (Set.Icc T T') :=
      codimBetween_eq_krullDim hTT'
    _ =
        krullDim
          (Set.Icc
            (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T)
            (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T')) :=
      Order.krullDim_eq_of_orderIso (closed_subspace_interval_order_iso hS hTT')
    _ =
        codimBetween
          (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T)
          (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T')
          (IrreducibleCloseds.map_mono continuous_subtype_val hTT') :=
      (codimBetween_eq_krullDim (IrreducibleCloseds.map_mono continuous_subtype_val hTT')).symm

/-- Helper for Lemma 10.105.8: if `R ⧸ p` is catenary, then the closed subset `V(p)` of
`Spec R` is catenary. -/
private theorem zeroLocus_catenarySpace_of_quotient
    (p : Ideal R) (hp : IsCatenaryRing (R ⧸ p)) :
    CatenarySpace (V((p : Set R))) := by
  -- Transport catenarity across the canonical homeomorphism `Spec (R ⧸ p) ≃ V(p)`.
  letI : IsCatenaryRing (R ⧸ p) := hp
  simpa using (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p).catenarySpace

/-- Helper for Lemma 10.105.8: if all minimal-prime quotients of a Noetherian ring are catenary,
then the ring itself is catenary. -/
private theorem isCatenaryRing_of_forall_minimalPrime_quotient
    (h : ∀ p ∈ minimalPrimes R, IsCatenaryRing (R ⧸ p)) :
    IsCatenaryRing R := by
  rw [isCatenaryRing_iff_catenarySpace_primeSpectrum]
  rw [catenarySpace_iff_finite_codimBetween_and_codimBetween_additive]
  refine ⟨?_, ?_⟩
  · intro T T' hTT'
    let q : PrimeSpectrum R :=
      (PrimeSpectrum.pointsEquivIrreducibleCloseds R).symm
        (show (IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ from T')
    have hq_eq :
        (show IrreducibleCloseds (PrimeSpectrum R) from
          PrimeSpectrum.pointsEquivIrreducibleCloseds R q) = T' := by
      simpa [q] using
        (PrimeSpectrum.pointsEquivIrreducibleCloseds R).apply_symm_apply
          (show (IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ from T')
    obtain ⟨p, hp, hpq⟩ :=
      Ideal.exists_minimalPrimes_le
        (I := (⊥ : Ideal R)) (J := q.asIdeal) bot_le
    have hT'_subset : (T' : Set (PrimeSpectrum R)) ⊆ V((p : Set R)) := by
      intro x hx
      have hxq :
          x ∈ ((show IrreducibleCloseds (PrimeSpectrum R) from
            PrimeSpectrum.pointsEquivIrreducibleCloseds R q) : Set (PrimeSpectrum R)) := by
        simpa [hq_eq] using hx
      have hqx : q.asIdeal ≤ x.asIdeal := by
        exact (show q ≤ x from (mem_pointsEquivIrreducibleCloseds_iff_le x q).mp hxq)
      change p ≤ x.asIdeal
      exact hpq.trans hqx
    have hT_subset : (T : Set (PrimeSpectrum R)) ⊆ V((p : Set R)) :=
      Set.Subset.trans hTT' hT'_subset
    have hV_closed : IsClosed (V((p : Set R)) : Set (PrimeSpectrum R)) := by
      simpa using PrimeSpectrum.isClosed_zeroLocus (p : Set R)
    let T0 : IrreducibleCloseds (V((p : Set R))) :=
      preimage_irreducibleClosed_of_subset hV_closed T hT_subset
    let T1 : IrreducibleCloseds (V((p : Set R))) :=
      preimage_irreducibleClosed_of_subset hV_closed T' hT'_subset
    have hT01 : T0 ≤ T1 := by
      intro x hx
      exact hTT' (by simpa [T0] using hx)
    letI : CatenarySpace (V((p : Set R))) := zeroLocus_catenarySpace_of_quotient p (h p hp)
    have hfinite_sub : codimBetween T0 T1 hT01 < ⊤ :=
      CatenarySpace.finite_codimBetween hT01
    have hcodim :
        codimBetween T0 T1 hT01 = codimBetween T T' hTT' := by
      rw [codimBetween_closed_subspace_eq hV_closed hT01]
      simp [T0, T1]
    simpa [hcodim] using hfinite_sub
  · intro T T' T'' hTT' hT'T''
    let q : PrimeSpectrum R :=
      (PrimeSpectrum.pointsEquivIrreducibleCloseds R).symm
        (show (IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ from T'')
    have hq_eq :
        (show IrreducibleCloseds (PrimeSpectrum R) from
          PrimeSpectrum.pointsEquivIrreducibleCloseds R q) = T'' := by
      simpa [q] using
        (PrimeSpectrum.pointsEquivIrreducibleCloseds R).apply_symm_apply
          (show (IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ from T'')
    obtain ⟨p, hp, hpq⟩ :=
      Ideal.exists_minimalPrimes_le
        (I := (⊥ : Ideal R)) (J := q.asIdeal) bot_le
    have hT''_subset : (T'' : Set (PrimeSpectrum R)) ⊆ V((p : Set R)) := by
      intro x hx
      have hxq :
          x ∈ ((show IrreducibleCloseds (PrimeSpectrum R) from
            PrimeSpectrum.pointsEquivIrreducibleCloseds R q) : Set (PrimeSpectrum R)) := by
        simpa [hq_eq] using hx
      have hqx : q.asIdeal ≤ x.asIdeal := by
        exact (show q ≤ x from (mem_pointsEquivIrreducibleCloseds_iff_le x q).mp hxq)
      change p ≤ x.asIdeal
      exact hpq.trans hqx
    have hT'_subset : (T' : Set (PrimeSpectrum R)) ⊆ V((p : Set R)) :=
      Set.Subset.trans hT'T'' hT''_subset
    have hT_subset : (T : Set (PrimeSpectrum R)) ⊆ V((p : Set R)) :=
      Set.Subset.trans hTT' hT'_subset
    have hV_closed : IsClosed (V((p : Set R)) : Set (PrimeSpectrum R)) := by
      simpa using PrimeSpectrum.isClosed_zeroLocus (p : Set R)
    let T0 : IrreducibleCloseds (V((p : Set R))) :=
      preimage_irreducibleClosed_of_subset hV_closed T hT_subset
    let T1 : IrreducibleCloseds (V((p : Set R))) :=
      preimage_irreducibleClosed_of_subset hV_closed T' hT'_subset
    let T2 : IrreducibleCloseds (V((p : Set R))) :=
      preimage_irreducibleClosed_of_subset hV_closed T'' hT''_subset
    have hT01 : T0 ≤ T1 := by
      intro x hx
      exact hTT' (by simpa [T0] using hx)
    have hT12 : T1 ≤ T2 := by
      intro x hx
      exact hT'T'' (by simpa [T1] using hx)
    have hT02 : T0 ≤ T2 := hT01.trans hT12
    letI : CatenarySpace (V((p : Set R))) := zeroLocus_catenarySpace_of_quotient p (h p hp)
    have hadd_sub :
        codimBetween T0 T2 hT02 =
          codimBetween T0 T1 hT01 + codimBetween T1 T2 hT12 :=
      CatenarySpace.codimBetween_additive hT01 hT12
    have hcodim01 :
        codimBetween T0 T1 hT01 = codimBetween T T' hTT' := by
      rw [codimBetween_closed_subspace_eq hV_closed hT01]
      simp [T0, T1]
    have hcodim12 :
        codimBetween T1 T2 hT12 = codimBetween T' T'' hT'T'' := by
      rw [codimBetween_closed_subspace_eq hV_closed hT12]
      simp [T1, T2]
    have hcodim02 :
        codimBetween T0 T2 hT02 = codimBetween T T'' (hTT'.trans hT'T'') := by
      rw [codimBetween_closed_subspace_eq hV_closed hT02]
      simp [T0, T2]
    simpa [hcodim01, hcodim12, hcodim02] using hadd_sub

/-- Helper for Lemma 10.105.8: a minimal-prime quotient of a finite type `R`-algebra is catenary
once the corresponding minimal-prime quotient of `R` is universally catenary. -/
private theorem minimalPrime_quotient_catenary_of_finiteType
    {A : Type v} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (h : ∀ p ∈ minimalPrimes R, UniversallyCatenaryRing.{u, v} (R ⧸ p))
    (q : Ideal A) (hq : q ∈ minimalPrimes A) :
    IsCatenaryRing (A ⧸ q) := by
  have hq_prime : q.IsPrime := Ideal.minimalPrimes_isPrime hq
  obtain ⟨p, hp, hpq⟩ :=
    Ideal.exists_minimalPrimes_le
      (I := (⊥ : Ideal R)) (J := Ideal.comap (algebraMap R A) q) bot_le
  -- Route correction: instead of proving the contraction of `q` is itself minimal, only choose a
  -- minimal prime below it and give `A ⧸ q` the induced `R ⧸ p`-algebra structure.
  letI : Algebra (R ⧸ p) (A ⧸ q) := Ideal.Quotient.algebraQuotientOfLEComap hpq
  letI : IsScalarTower R (R ⧸ p) (A ⧸ q) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  haveI : Algebra.FiniteType (R ⧸ p) (A ⧸ q) :=
    Algebra.FiniteType.of_restrictScalars_finiteType
      (R := R) (S := R ⧸ p) (A := A ⧸ q)
  let huc : UniversallyCatenaryRing (R ⧸ p) := h p hp
  exact huc.catenary_of_finiteType (A := A ⧸ q)

-- Proof sketch: for the forward implication, pass catenarity to each irreducible component
-- `Spec (R ⧸ p)` cut out by a minimal prime. For the reverse implication, every chain of primes in
-- `R` lies over some minimal prime, reducing the catenary condition to the corresponding quotient.
/-- Lemma 10.105.8 (1): a Noetherian ring is catenary if and only if the quotient by every
minimal prime is catenary. -/
theorem isCatenaryRing_iff_forall_quotient_by_minimalPrime :
    IsCatenaryRing R ↔ ∀ p ∈ minimalPrimes R, IsCatenaryRing (R ⧸ p) := by
  constructor
  · intro hR p hp
    -- The forward direction is just quotient stability of catenarity.
    letI : IsCatenaryRing R := hR
    infer_instance
  · intro h
    -- The reverse direction checks each irreducible-closed interval inside one minimal-prime
    -- component.
    exact isCatenaryRing_of_forall_minimalPrime_quotient h

-- Proof sketch: use the same minimal-prime reduction after base change to finite type algebras
-- over `R`, applying the first clause to each such algebra and its quotients by minimal primes.
/-- Lemma 10.105.8 (2): a Noetherian ring is universally catenary if and only if the quotient by
every minimal prime is universally catenary. -/
theorem universallyCatenaryRing_iff_forall_quotient_by_minimalPrime :
    UniversallyCatenaryRing.{u, v} R ↔
      ∀ p ∈ minimalPrimes R, UniversallyCatenaryRing.{u, v} (R ⧸ p) := by
  constructor
  · intro hR p hp
    -- The forward direction is the quotient-stability construction from Lemma `10.105.7`.
    letI : UniversallyCatenaryRing.{u, v} R := hR
    refine { catenary_of_finiteType := ?_ }
    intro A _ _ _
    let f : R →+* A := (algebraMap (R ⧸ p) A).comp (Ideal.Quotient.mk p)
    letI : Algebra R A := RingHom.toAlgebra f
    letI : IsScalarTower R (R ⧸ p) A :=
      IsScalarTower.of_algebraMap_eq fun x ↦ rfl
    have hfinite : Algebra.FiniteType R A :=
      Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R (R ⧸ p)) inferInstance
    exact (inferInstance : UniversallyCatenaryRing.{u, v} R).catenary_of_finiteType (A := A)
  · intro h
    refine { catenary_of_finiteType := ?_ }
    intro A _ _ _
    -- Reduce catenarity of `A` to its minimal-prime quotients, then apply part (1).
    letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
    exact (isCatenaryRing_iff_forall_quotient_by_minimalPrime (R := A)).2 fun q hq ↦
      minimalPrime_quotient_catenary_of_finiteType h q hq

end

/-! ### Lemma_10_105_9 (from Chap10) -/
universe u v

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Helper for Lemma 10.105.9: if `M` has full support over `R`, then every prime localization
`M_𝔭` still has full support over `R_𝔭`. -/
private lemma localized_support_eq_univ_of_support_eq_univ [Module.Finite R M]
    (hsupp : Module.support R M = Set.univ) (p : PrimeSpectrum R) :
    Module.support (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) =
      Set.univ := by
  ext q
  -- Detect support after localizing by contracting the prime back to `Spec R`.
  rw [Module.mem_support_localizationAtPrime_iff (R := R) (M := M) p q, hsupp]
  simp

/-- Helper for Lemma 10.105.9: localizing the global hypotheses at a prime produces the local
source theorem input. -/
private theorem localized_cohenMacaulay_and_support_eq_univ
    (hCM : Module.LocallyCohenMacaulay R M) (hsupp : Module.support R M = Set.univ)
    (p : PrimeSpectrum R) :
    Module.CohenMacaulay (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) ∧
      Module.support (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) =
        Set.univ := by
  let _ : Module.Finite R M := hCM.toFinite
  constructor
  · -- The locally Cohen-Macaulay owner already packages the localized Cohen-Macaulay statement.
    exact hCM.localizedModule_cohenMacaulay p
  · -- Full support survives the same localization.
    exact localized_support_eq_univ_of_support_eq_univ (R := R) (M := M) hsupp p

/-- Helper for Lemma 10.105.9: catenarity transports across ring equivalences. -/
private theorem isCatenaryRing_of_ringEquiv {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (e : A ≃+* B) [IsCatenaryRing A] :
    IsCatenaryRing B := by
  -- Transport the catenary-space owner across the induced homeomorphism of spectra.
  simpa [IsCatenaryRing] using
    (PrimeSpectrum.homeomorphOfRingEquiv e).catenarySpace

/-- Helper for Lemma 10.105.9: over a Noetherian local ring, the polynomial ring is catenary once
the base admits a Cohen-Macaulay module with full support. -/
private theorem isCatenaryRing_mvPolynomial_of_cohenMacaulay_of_support_eq_univ_local
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    (hCM : Module.CohenMacaulay A N) (hsupp : Module.support A N = Set.univ) (n : ℕ) :
    IsCatenaryRing (MvPolynomial (Fin n) A) := by
  -- Route correction: this is the remaining source-faithful polynomial step. Its intended proof is
  -- to base-change `N` to `A[x₁, …, xₙ]`, check full support primewise, localize at maximal ideals,
  -- and then apply the local chain-length argument there.
  -- TODO: reopen this once the earlier polynomial-base-change dependency compiles again.
  let _ : Module.Finite A N := hCM.toFinite
  let _ := hsupp
  let _ := n
  sorry

/-- Helper for Lemma 10.105.9: over a Noetherian local ring, a Cohen-Macaulay module with full
support forces the ring to be universally catenary. -/
private theorem universallyCatenaryRing_of_cohenMacaulay_of_support_eq_univ_local
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    (hCM : Module.CohenMacaulay A N) (hsupp : Module.support A N = Set.univ) :
    UniversallyCatenaryRing A := by
  let _ : Module.Finite A N := hCM.toFinite
  refine { catenary_of_finiteType := ?_ }
  intro B _ _ _
  obtain ⟨n, π, hπsurj⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := B)).mp inferInstance
  let S := MvPolynomial (Fin n) A
  letI : IsCatenaryRing S :=
    isCatenaryRing_mvPolynomial_of_cohenMacaulay_of_support_eq_univ_local
      (A := A) (N := N) hCM hsupp n
  letI : IsCatenaryRing (S ⧸ RingHom.ker π) :=
    quotient_catenaryRing (R := S) (I := RingHom.ker π)
  let e : S ⧸ RingHom.ker π ≃+* B := RingHom.quotientKerEquivOfSurjective hπsurj
  -- Present the finite-type algebra as a quotient of a catenary polynomial ring.
  exact isCatenaryRing_of_ringEquiv e

/-
Domain-style sampling in the Cohen-Macaulay / universal-catenarity interface:
- sampled owner declarations:
  `Module.LocallyCohenMacaulay`,
  `CohenMacaulayRing`,
  `UniversallyCatenaryRing`,
  `Module.support_of_algebra`;
- best owner abstraction: the main theorem is a `bridge/view` from the chapter owner
  `Module.LocallyCohenMacaulay R M` plus full support to `UniversallyCatenaryRing R`;
- primitive data: `hCM : Module.LocallyCohenMacaulay R M` and
  `hsupp : Module.support R M = Set.univ`;
- derived API: the Cohen-Macaulay-ring corollary, obtained by specializing to the self-module
  `R`.

Source/core/bridge triage:
* source-facing: Lemma `10.105.9` itself, expressing the textbook criterion via a
  Cohen-Macaulay module with full support;
* core/canonical: the owner classes `Module.LocallyCohenMacaulay` and
  `UniversallyCatenaryRing`;
* bridge/view: the self-module specialization through `CohenMacaulayRing`.
-/
-- Proof sketch: localize at an arbitrary prime `p` of `R`. The localized module remains
-- Cohen-Macaulay and still has full support, so Lemmas `10.103.13` and `10.103.9` show that each
-- polynomial localization over `Rₚ` has prime chains of the expected length. Applying
-- Lemma `10.104.7` to polynomial algebras and then the localization criterion for universal
-- catenarity yields the conclusion.
/-- Lemma 10.105.9: more generally, if `R` is a Noetherian ring and `M` is a Cohen-Macaulay
`R`-module whose support is all of `Spec R`, then `R` is universally catenary. -/
theorem universallyCatenaryRing_of_support_eq_univ_of_locallyCohenMacaulay
    (hCM : Module.LocallyCohenMacaulay R M) (hsupp : Module.support R M = Set.univ) :
    UniversallyCatenaryRing R := by
  let _ : Module.Finite R M := hCM.toFinite
  -- Reduce universal catenarity to the prime-local criterion from Lemma `10.105.6`.
  refine ((universallyCatenaryRing_localization_tfae (R := R)).out 1 0 rfl rfl).mp ?_
  intro p
  -- Each prime localization now matches the remaining local theorem.
  obtain ⟨hCMp, hsuppp⟩ :=
    localized_cohenMacaulay_and_support_eq_univ (R := R) (M := M) hCM hsupp p
  exact universallyCatenaryRing_of_cohenMacaulay_of_support_eq_univ_local hCMp hsuppp

end

section

variable {R : Type u} [CommRing R]

-- Proof sketch: apply the general theorem to the self-module `R`. A Cohen-Macaulay ring gives the
-- required local Cohen-Macaulay property for `R`, and the support of the self-module is all of
-- `Spec R`. The theorem header does not repeat a separate `[IsNoetherianRing R]` assumption,
-- since that primitive data already belongs to the owner class `CohenMacaulayRing R`.
/-- A Noetherian Cohen-Macaulay ring is universally catenary. -/
theorem universallyCatenaryRing_of_cohenMacaulayRing (hCM : CohenMacaulayRing R) :
    UniversallyCatenaryRing R := by
  let _ : CohenMacaulayRing R := hCM
  have hker : RingHom.ker (RingHom.id R) = (⊥ : Ideal R) := by
    ext x
    simp
  have hsupp : Module.support R R = Set.univ := by
    simpa [hker, PrimeSpectrum.zeroLocus_bot] using
      (show Module.support R R = PrimeSpectrum.zeroLocus (RingHom.ker (algebraMap R R)) from
        Module.support_of_algebra)
  exact universallyCatenaryRing_of_support_eq_univ_of_locallyCohenMacaulay
    hCM.toLocallyCohenMacaulay hsupp

end

/-! ### Lemma_10_105_10 (from Chap10) -/
noncomputable section

universe u

open IsLocalRing Order PrimeSpectrum TopologicalSpace

/- Domain-style sampling in the catenary/dimension-function API:
- ring owner: `IsCatenaryRing A`
- topological owner: `IsDimensionFunction δ`
- bridge/view: the source function `p ↦ dim (A / p)` on `Spec A`, expressed here through
  `ringKrullDim (A ⧸ p.asIdeal)`

Layer triage:
- `source-facing`: Lemma 10.105.10 is the local Noetherian criterion for catenarity
- `core/canonical`: the owner abstractions are already `IsCatenaryRing` and `IsDimensionFunction`
- `bridge/view`: the quotient-dimension function is derived API and should stay scoped to the
  Noetherian-local setting of the theorem, rather than as a global owner declaration

Primitive data belongs to the existing owner abstractions. The quotient-dimension expression is
kept inline below because `ringKrullDim` is `WithBot`-valued in general, so truncating it with
`unbotD 0` is only source-faithful in the finite-dimensional local setting of this lemma.
-/

section

variable {A : Type u} [CommRing A]

/-- Helper for Lemma 10.105.10: catenarity near the closed point globalizes to a dimension
function normalized to vanish at that closed point. -/
private theorem exists_dimensionFunction_vanishing_at_closedPoint
    [IsNoetherianRing A] [IsLocalRing A] [IsCatenaryRing A] :
    ∃ δ : PrimeSpectrum A → ℤ, IsDimensionFunction δ ∧ δ (closedPoint A) = 0 := by
  -- Start with the local existence theorem at the closed point.
  obtain ⟨U, hclosed_mem, δU, hδU⟩ :=
    exists_open_neighborhood_with_dimensionFunction (X := PrimeSpectrum A) (closedPoint A)
  have hU : U = ⊤ := (closedPoint_mem_iff U).mp hclosed_mem
  subst hU
  let δBase : PrimeSpectrum A → ℤ :=
    fun p ↦ δU ⟨p, by simp⟩
  -- Transport the dimension function from the top open subset back to the ambient spectrum.
  have hδBase : IsDimensionFunction δBase := by
    refine
      { strict_of_specializes := ?_
        eq_add_one_of_immediateSpecialization := ?_ }
    · intro x y hxy hxy_ne
      have hxyU : (⟨x, by simp⟩ : (⊤ : Opens (PrimeSpectrum A))) ⤳ ⟨y, by simp⟩ := by
        simpa using (subtype_specializes_iff (x := ⟨x, by simp⟩) (y := ⟨y, by simp⟩)).2 hxy
      have hxyU_ne : (⟨x, by simp⟩ : (⊤ : Opens (PrimeSpectrum A))) ≠ ⟨y, by simp⟩ := by
        intro h
        exact hxy_ne (Subtype.ext_iff.mp h)
      simpa [δBase] using hδU.strict_of_specializes hxyU hxyU_ne
    · intro x y hxy
      have hxyU :
          IsImmediateSpecialization
            (⟨x, by simp⟩ : (⊤ : Opens (PrimeSpectrum A))) ⟨y, by simp⟩ := by
        refine ⟨?_, ?_, ?_⟩
        · simpa using
            (subtype_specializes_iff (x := ⟨x, by simp⟩) (y := ⟨y, by simp⟩)).2 hxy.specializes
        · intro h
          exact hxy.ne (Subtype.ext_iff.mp h)
        · intro z hxz hzy
          have hxz' : x ⤳ (z : PrimeSpectrum A) := by
            simpa using
              (subtype_specializes_iff (x := ⟨x, by simp⟩) (y := z)).1 hxz
          have hzy' : (z : PrimeSpectrum A) ⤳ y := by
            simpa using
              (subtype_specializes_iff (x := z) (y := ⟨y, by simp⟩)).1 hzy
          rcases hxy.eq_or_eq hxz' hzy' with h | h
          · left
            exact Subtype.ext h
          · right
            exact Subtype.ext h
      simpa [δBase] using hδU.eq_add_one_of_immediateSpecialization hxyU
  let δ : PrimeSpectrum A → ℤ := fun p ↦ δBase p - δBase (closedPoint A)
  -- Normalize by subtracting the closed-point value.
  have hδ : IsDimensionFunction δ := by
    refine
      { strict_of_specializes := ?_
        eq_add_one_of_immediateSpecialization := ?_ }
    · intro x y hxy hxy_ne
      simpa [δ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        hδBase.strict_of_specializes hxy hxy_ne
    · intro x y hxy
      have hstep := hδBase.eq_add_one_of_immediateSpecialization hxy
      dsimp [δ]
      omega
  refine ⟨δ, hδ, ?_⟩
  dsimp [δ]
  ring

/-- Helper for Lemma 10.105.10: in a local spectrum, the codimension from the closed point to a
prime is the coheight of that prime. -/
private theorem closedPoint_codim_eq_coheight [IsLocalRing A] (p : PrimeSpectrum A) :
    codimBetween (toIrreducibleCloseds (closedPoint A)) (toIrreducibleCloseds p)
      (specializes_closedPoint p).toIrreducibleCloseds_le =
      Order.coheight p := by
  let T : IrreducibleCloseds (PrimeSpectrum A) := toIrreducibleCloseds (closedPoint A)
  let T' : IrreducibleCloseds (PrimeSpectrum A) := toIrreducibleCloseds p
  let e : PrimeSpectrum A ≃o (IrreducibleCloseds (PrimeSpectrum A))ᵒᵈ :=
    PrimeSpectrum.pointsEquivIrreducibleCloseds A
  have eDual :
      (Set.Icc T T')ᵒᵈ ≃o
        Set.Icc (show (IrreducibleCloseds (PrimeSpectrum A))ᵒᵈ from T')
          (show (IrreducibleCloseds (PrimeSpectrum A))ᵒᵈ from T) := by
    refine
      { toFun := fun x ↦
          let x' : Set.Icc T T' := show Set.Icc T T' from x
          ⟨show (IrreducibleCloseds (PrimeSpectrum A))ᵒᵈ from x'.1, x'.2.2, x'.2.1⟩
        invFun := fun y ↦
          show (Set.Icc T T')ᵒᵈ from
            ⟨show IrreducibleCloseds (PrimeSpectrum A) from y.1, y.2.2, y.2.1⟩
        left_inv := ?_
        right_inv := ?_
        map_rel_iff' := ?_ }
    · intro x
      ext
      rfl
    · intro y
      ext
      rfl
    · intro x y
      rfl
  have hT : (show (IrreducibleCloseds (PrimeSpectrum A))ᵒᵈ from T) = e (closedPoint A) := by
    rfl
  have hT' : (show (IrreducibleCloseds (PrimeSpectrum A))ᵒᵈ from T') = e p := by
    rfl
  have eInterval :
      Set.Icc (show (IrreducibleCloseds (PrimeSpectrum A))ᵒᵈ from T')
          (show (IrreducibleCloseds (PrimeSpectrum A))ᵒᵈ from T) ≃o
        Set.Icc p (closedPoint A) := by
    refine
      { toFun := fun x ↦ ⟨e.symm x.1, ?_, ?_⟩
        invFun := fun y ↦ ⟨e y.1, ?_, ?_⟩
        left_inv := ?_
        right_inv := ?_
        map_rel_iff' := ?_ }
    · simpa [hT'] using e.symm.monotone x.2.1
    · simpa [hT] using e.symm.monotone x.2.2
    · simpa [hT'] using e.monotone y.2.1
    · simpa [hT] using e.monotone y.2.2
    · intro x
      ext
      simp [e]
    · intro y
      ext
      simp [e]
    · intro x y
      simpa using e.symm.le_iff_le
  -- Compute codimension as the Krull dimension of the corresponding interval, then transport it
  -- to the upper interval `Ici p` in the prime spectrum.
  apply WithBot.coe_injective
  calc
    (codimBetween T T' (specializes_closedPoint p).toIrreducibleCloseds_le : WithBot ℕ∞) =
        Order.krullDim (Set.Icc T T') := codimBetween_eq_krullDim _
    _ = Order.krullDim ((Set.Icc T T')ᵒᵈ) := by
      exact (Order.krullDim_orderDual (α := Set.Icc T T')).symm
    _ =
        Order.krullDim
          (Set.Icc (show (IrreducibleCloseds (PrimeSpectrum A))ᵒᵈ from T')
            (show (IrreducibleCloseds (PrimeSpectrum A))ᵒᵈ from T)) := by
          exact Order.krullDim_eq_of_orderIso eDual
    _ = Order.krullDim (Set.Icc p (closedPoint A)) := by
      exact Order.krullDim_eq_of_orderIso eInterval
    _ = Order.krullDim (Set.Ici p) := by
      rw [show (closedPoint A) = (⊤ : PrimeSpectrum A) by rfl, Set.Icc_top]
    _ = Order.coheight p := (Order.coheight_eq_krullDim_Ici p).symm

/-- Helper for Lemma 10.105.10: the Krull dimension of `A / p` agrees with the codimension from
the closed point to `p`. -/
private theorem prime_quotient_krullDimension_eq_closedPoint_codim
    [IsNoetherianRing A] [IsLocalRing A] (p : PrimeSpectrum A) :
    (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ) =
      (ENat.toNat
        (codimBetween (toIrreducibleCloseds (closedPoint A)) (toIrreducibleCloseds p)
          (specializes_closedPoint p).toIrreducibleCloseds_le) : ℤ) := by
  -- Rewrite the quotient Krull dimension as the coheight of `p`.
  have hquotient :
      ringKrullDim (A ⧸ p.asIdeal) = Order.coheight p := by
    rw [ringKrullDim_quotient]
    have hzero : PrimeSpectrum.zeroLocus (p.asIdeal : Set A) = Set.Ici p := by
      ext q
      change p.asIdeal ≤ q.asIdeal ↔ p ≤ q
      rfl
    rw [hzero]
    exact (Order.coheight_eq_krullDim_Ici p).symm
  -- After removing the `WithBot` wrapper, the remaining quantity is exactly the codimension.
  calc
    (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ)
        = (((Order.coheight p : ℕ∞)).toNat : ℤ) := by
            rw [hquotient]
            simp [WithBot.unbotD_coe]
    _ =
        (ENat.toNat
          (codimBetween (toIrreducibleCloseds (closedPoint A)) (toIrreducibleCloseds p)
            (specializes_closedPoint p).toIrreducibleCloseds_le) : ℤ) := by
              rw [closedPoint_codim_eq_coheight (A := A) p]

/-- Helper for Lemma 10.105.10: a dimension function normalized to be zero at the closed point is
forced to be `p ↦ dim(A / p)`. -/
private theorem normalized_dimensionFunction_eq_primeQuotientKrullDimension
    [IsNoetherianRing A] [IsLocalRing A] {δ : PrimeSpectrum A → ℤ}
    (hδ : IsDimensionFunction δ) (hδ0 : δ (closedPoint A) = 0) :
    ∀ p : PrimeSpectrum A,
      δ p = (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ) := by
  intro p
  -- Lemma 5.20.2 computes the normalized dimension function as codimension from the closed point.
  calc
    δ p = δ p - δ (closedPoint A) := by simpa [hδ0]
    _ =
        (ENat.toNat
          (codimBetween (toIrreducibleCloseds (closedPoint A)) (toIrreducibleCloseds p)
            (specializes_closedPoint p).toIrreducibleCloseds_le) : ℤ) := by
              simpa using
                hδ.sub_eq_codimBetween_pointClosure p (closedPoint A) (specializes_closedPoint p)
    _ = (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ) := by
      symm
      exact prime_quotient_krullDimension_eq_closedPoint_codim (A := A) p

end

-- Proof sketch: for the forward implication, transport catenarity from prime-ideal intervals to the
-- specialization order on `Spec A` and use the local-ring codimension formula at the closed point to
-- identify the resulting dimension function with `p ↦ dim (A / p)`. For the reverse implication,
-- apply the dimension-function criterion for catenarity on the prime spectrum and translate back to
-- the ring-theoretic formulation.
/-- Lemma 10.105.10: for a Noetherian local ring, the ring is catenary if and only if the function
`p ↦ dim (A / p)` is a dimension function on `Spec A`. -/
theorem isCatenaryRing_iff_primeQuotientKrullDimension_isDimensionFunction
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    IsCatenaryRing A ↔
      IsDimensionFunction
        (fun p : PrimeSpectrum A ↦ (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ)) := by
  constructor
  · intro hcat
    letI : IsCatenaryRing A := hcat
    obtain ⟨δ, hδ, hδ0⟩ := exists_dimensionFunction_vanishing_at_closedPoint (A := A)
    -- Compare the normalized dimension function with the quotient-dimension function pointwise.
    have hfun :
        δ =
          (fun p : PrimeSpectrum A ↦
            (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ)) := by
      funext p
      exact normalized_dimensionFunction_eq_primeQuotientKrullDimension
        (A := A) hδ hδ0 p
    simpa [hfun] using hδ
  · intro hdim
    -- The reverse implication is exactly Lemma 5.20.2 on the prime spectrum.
    rw [isCatenaryRing_iff_catenarySpace_primeSpectrum]
    exact hdim.catenarySpace
