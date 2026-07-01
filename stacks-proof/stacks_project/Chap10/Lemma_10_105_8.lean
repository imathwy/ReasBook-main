import Mathlib
import stacks_project.Chap05.Lemma_5_11_5
import stacks_project.Chap05.Lemma_5_11_6
import stacks_project.Chap10.Lemma_10_17_7
import stacks_project.Chap10.Lemma_10_105_7

-- Declarations for this item will be appended below by the statement pipeline.

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
