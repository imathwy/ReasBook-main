import Mathlib
import stacks_proof.stacks_project.Chap05.Definition_5_10_5
import stacks_proof.stacks_project.Chap10.Lemma_10_17_7
import stacks_proof.stacks_project.Chap10.Lemma_10_125_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open TopologicalSpace PrimeSpectrum
open IsLocalRing

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [IsDomain R] [ValuationRing R]
variable [CommRing S] [IsDomain S] [Algebra R S] [Algebra.FiniteType R S]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S
local notation "GenericFiber" => Ideal.Fiber (⊥ : Ideal R) S

/- Domain-style sampling:
- primary domain: fibers of finite-type algebras over valuation rings, with the special fiber
  and generic fiber both expressed by the canonical fiber owner `Ideal.Fiber`;
- sampled owner declarations:
  `Ideal.Fiber`,
  `PrimeSpectrum.preimageHomeomorphFiber`,
  `relativeDimensionAt`,
  `EquidimensionalSpace`,
  `ringKrullDim`;
- best owner abstraction: the special fiber should be written as the canonical owner
  `ClosedFiber = Ideal.Fiber (maximalIdeal R) S`, and the generic fiber should live on the same
  owner level `GenericFiber = Ideal.Fiber (⊥ : Ideal R) S`; the tensor model
  `S ⊗[R] FractionRing R` is only a bridge presentation of `GenericFiber`, while the public
  conclusions belong on `PrimeSpectrum ClosedFiber`, `ringKrullDim ClosedFiber`, and
  `ringKrullDim GenericFiber`;
- primitive data: the valuation-ring map `R → S`, injectivity of `algebraMap R S`, the canonical
  closed fiber `ClosedFiber`, and the generic fiber `GenericFiber`;
- derived API: equidimensionality of `PrimeSpectrum ClosedFiber` and the dimension equality
  `ringKrullDim ClosedFiber = ringKrullDim GenericFiber`.

Source/core/bridge triage:
- `source-facing`: the special-fiber equidimensionality and dimension-comparison statements;
- `core/canonical`: `Ideal.Fiber`, `EquidimensionalSpace`, and `ringKrullDim`;
- `bridge/view`: the tensor-product presentations of `ClosedFiber` and `GenericFiber`.
-/

/-- Helper for Chap10 Lemma 10 125 9: a common dimension for all irreducible components is the
formal data needed for equidimensionality. -/
private theorem equidimensionalSpace_of_componentTopologicalKrullDim_eq
    {X : Type u} [TopologicalSpace X] {d : WithBot ℕ∞}
    (hcomp : ∀ Z : irreducibleComponents X, topologicalKrullDim (Z : Set X) = d) :
    EquidimensionalSpace X := by
  refine ⟨?_⟩
  intro Z₁ Z₂
  -- Compare both component dimensions through the shared value `d`.
  calc
    topologicalKrullDim Z₁ = d := hcomp Z₁
    _ = topologicalKrullDim Z₂ := (hcomp Z₂).symm

/-- Helper for Chap10 Lemma 10 125 9: the supremum of a nonempty constant family of component
dimensions is the shared component dimension. -/
private theorem iSup_componentTopologicalKrullDim_eq
    {X : Type u} [TopologicalSpace X] [Nonempty (irreducibleComponents X)] {d : WithBot ℕ∞}
    (hcomp : ∀ Z : irreducibleComponents X, topologicalKrullDim (Z : Set X) = d) :
    (⨆ Z : irreducibleComponents X, topologicalKrullDim (Z : Set X)) = d := by
  -- Route correction: keep the formal constant-component reduction dependency-light; the missing
  -- heavier bridge is only the comparison of global dimension with this component supremum.
  refine le_antisymm ?_ ?_
  · refine iSup_le fun Z ↦ ?_
    exact le_of_eq (hcomp Z)
  · obtain ⟨Z⟩ := ‹Nonempty (irreducibleComponents X)›
    exact le_iSup_of_le Z (le_of_eq (hcomp Z).symm)

/-- Helper for Chap10 Lemma 10 125 9: at a point, the supremum over the components through that
point collapses to the common component dimension. -/
private theorem iSup_componentsThroughTopologicalKrullDim_eq
    {X : Type u} [TopologicalSpace X] (x : X) {d : WithBot ℕ∞}
    (hcomp : ∀ Z : irreducibleComponents X, topologicalKrullDim (Z : Set X) = d) :
    (⨆ Z : { Z : irreducibleComponents X // x ∈ (Z : Set X) },
      topologicalKrullDim (Z : Set X)) = d := by
  -- The upper bound uses the common-dimension hypothesis componentwise.
  refine le_antisymm ?_ ?_
  · refine iSup_le fun Z ↦ ?_
    exact le_of_eq (hcomp Z.1)
  ·
    -- The irreducible component of `x` supplies a component-through-`x` witnessing the lower
    -- bound for the constant supremum.
    let Z : { Z : irreducibleComponents X // x ∈ (Z : Set X) } :=
      ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩,
        mem_irreducibleComponent⟩
    exact le_iSup_of_le Z (le_of_eq (hcomp Z.1).symm)

/-- Helper for Chap10 Lemma 10 125 9: inclusion of subspaces cannot increase topological Krull
dimension. -/
private theorem topologicalKrullDim_subspace_mono
    {X : Type u} [TopologicalSpace X] {Y Z : Set X} (hYZ : Y ⊆ Z) :
    topologicalKrullDim Y ≤ topologicalKrullDim Z := by
  let f : Y → Z := fun y ↦ ⟨y.1, hYZ y.2⟩
  have hf_comp : Topology.IsInducing ((Subtype.val : Z → X) ∘ f) := by
    -- The composite inclusion is exactly the canonical inclusion of `Y` into `X`.
    simpa [f] using
      (Topology.IsInducing.subtypeVal : Topology.IsInducing (Subtype.val : Y → X))
  have hf : Topology.IsInducing f :=
    (Topology.IsInducing.subtypeVal.of_comp_iff (f := f)).mp hf_comp
  exact IsInducing.topologicalKrullDim_le hf

/-- Helper for Chap10 Lemma 10 125 9: the dimension of a prime quotient is bounded by the
dimension of any irreducible component containing its zero locus. -/
private theorem ringKrullDim_primeQuotient_le_componentDimension
    {A : Type u} [CommRing A] {d : WithBot ℕ∞}
    (hcomp : ∀ Z : irreducibleComponents (PrimeSpectrum A),
      topologicalKrullDim (Z : Set (PrimeSpectrum A)) = d)
    (p : PrimeSpectrum A) :
    ringKrullDim (A ⧸ p.asIdeal) ≤ d := by
  have hp_irred :
      IsIrreducible (PrimeSpectrum.zeroLocus (p.asIdeal : Set A)) := by
    -- A prime ideal has irreducible zero locus.
    refine (PrimeSpectrum.isIrreducible_zeroLocus_iff p.asIdeal).mpr ?_
    simpa [Ideal.IsPrime.radical p.isPrime] using p.isPrime
  obtain ⟨Zset, hZcomp, hVZ⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible
      (PrimeSpectrum.zeroLocus (p.asIdeal : Set A)) hp_irred
  let Z : irreducibleComponents (PrimeSpectrum A) := ⟨Zset, hZcomp⟩
  have hhomeo :
      topologicalKrullDim (PrimeSpectrum (A ⧸ p.asIdeal)) =
        topologicalKrullDim (PrimeSpectrum.zeroLocus (p.asIdeal : Set A)) := by
    -- The quotient spectrum is homeomorphic to the zero locus of `p`.
    simpa using
      IsHomeomorph.topologicalKrullDim_eq
        (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal)
        (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal).isHomeomorph
  calc
    ringKrullDim (A ⧸ p.asIdeal) =
        topologicalKrullDim (PrimeSpectrum (A ⧸ p.asIdeal)) :=
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (A ⧸ p.asIdeal)).symm
    _ = topologicalKrullDim (PrimeSpectrum.zeroLocus (p.asIdeal : Set A)) := hhomeo
    _ ≤ topologicalKrullDim (Z : Set (PrimeSpectrum A)) :=
      topologicalKrullDim_subspace_mono hVZ
    _ = d := hcomp Z

/-- Helper for Chap10 Lemma 10 125 9: the zero locus of a prime ideal is the upper interval
above the corresponding point of the prime spectrum. -/
private theorem primeSpectrum_zeroLocus_prime_eq_Ici
    {A : Type u} [CommRing A] {p : Ideal A} (hp : p.IsPrime) :
    PrimeSpectrum.zeroLocus (p : Set A) =
      Set.Ici (⟨p, hp⟩ : PrimeSpectrum A) := by
  -- Membership in the zero locus is exactly inclusion of the prime ideal.
  ext q
  change p ≤ q.asIdeal ↔ (⟨p, hp⟩ : PrimeSpectrum A) ≤ q
  rfl

/-- Helper for Chap10 Lemma 10 125 9: the Krull dimension is the supremum of the dimensions of
the prime quotients. -/
private theorem ringKrullDim_eq_iSup_primeQuotient
    {A : Type u} [CommRing A] :
    ringKrullDim A = ⨆ p : PrimeSpectrum A, ringKrullDim (A ⧸ p.asIdeal) := by
  have hquot :
      ∀ p : PrimeSpectrum A, ringKrullDim (A ⧸ p.asIdeal) = Order.coheight p := by
    intro p
    -- The quotient by `p` has spectrum the upper interval above `p`.
    rw [ringKrullDim_quotient, primeSpectrum_zeroLocus_prime_eq_Ici (A := A) p.isPrime]
    exact (Order.coheight_eq_krullDim_Ici p).symm
  calc
    ringKrullDim A = ⨆ p : PrimeSpectrum A, ↑(Order.coheight p) := by
      rw [ringKrullDim, Order.krullDim_eq_iSup_coheight]
    _ = ⨆ p : PrimeSpectrum A, ringKrullDim (A ⧸ p.asIdeal) := by
      simp_rw [hquot]

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 125 9: an injective algebra map from a valuation domain makes
the target algebra flat over the base. -/
private theorem flat_of_injective_algebraMap_over_valuationRing
    (hRS : Function.Injective (algebraMap R S)) :
    Module.Flat R S := by
  -- The valuation ring is Bezout, so flatness is equivalent to vanishing torsion.
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  -- For an algebra over a domain, torsion-freeness is exactly injectivity of the algebra map.
  exact Module.isTorsionFree_iff_algebraMap_injective.mpr hRS

omit [IsDomain R] [ValuationRing R] [IsDomain S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 125 9: lifting a prime of a fiber ring back to the ambient
spectrum contracts it along the right tensor inclusion. -/
private theorem preimageEquivFiber_symm_asIdeal
    (p : PrimeSpectrum R) (m : PrimeSpectrum (p.asIdeal.Fiber S)) :
    ((PrimeSpectrum.preimageEquivFiber R S p).symm m).1.asIdeal =
      (m.comap Algebra.TensorProduct.includeRight.toRingHom).asIdeal := by
  -- The inverse branch of `preimageEquivFiber` is exactly this contraction; naming it prevents
  -- the later maximal-point comparison from unfolding the full fiber equivalence repeatedly.
  rfl

omit [IsDomain R] [ValuationRing R] [IsDomain S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 125 9: a prime lifted from a fiber contracts to the base prime of
that fiber. -/
private theorem preimageEquivFiber_symm_comap
    (p : PrimeSpectrum R) (m : PrimeSpectrum (p.asIdeal.Fiber S)) :
    PrimeSpectrum.comap (algebraMap R S)
        ((PrimeSpectrum.preimageEquivFiber R S p).symm m).1 = p := by
  -- The inverse equivalence lands in the subtype of ambient primes lying over `p`.
  simpa using ((PrimeSpectrum.preimageEquivFiber R S p).symm m).2

omit [IsDomain S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 125 9: a point of the closed fiber lifted to the ambient spectrum
contracts to the maximal ideal of the valuation ring. -/
private theorem closedFiberPoint_liftedPrime_contracts
    (x : PrimeSpectrum ClosedFiber) :
    PrimeSpectrum.comap (algebraMap R S)
        ((PrimeSpectrum.preimageEquivFiber R S
          (⟨maximalIdeal R, inferInstance⟩ : PrimeSpectrum R)).symm x).1 =
      (⟨maximalIdeal R, inferInstance⟩ : PrimeSpectrum R) := by
  -- This is the fiber-equivalence contraction bridge specialized to the closed fiber.
  exact preimageEquivFiber_symm_comap
    (R := R) (S := S)
    (⟨maximalIdeal R, inferInstance⟩ : PrimeSpectrum R) x

/-- Helper for Chap10 Lemma 10 125 9: if a point lies on exactly one irreducible component, then
the component-dimension supremum through that point is the dimension of that component. -/
private theorem iSup_componentsThroughTopologicalKrullDim_eq_of_uniqueComponent
    {A : Type u} [CommRing A] (x : PrimeSpectrum A)
    (Z : irreducibleComponents (PrimeSpectrum A))
    (hxZ : x ∈ (Z : Set (PrimeSpectrum A)))
    (hunique : ∀ W : irreducibleComponents (PrimeSpectrum A),
      x ∈ (W : Set (PrimeSpectrum A)) ↔ W = Z) :
    (⨆ W : { W : irreducibleComponents (PrimeSpectrum A) //
        x ∈ (W : Set (PrimeSpectrum A)) },
      topologicalKrullDim (W : Set (PrimeSpectrum A))) =
      topologicalKrullDim (Z : Set (PrimeSpectrum A)) := by
  -- Collapse the component-indexed supremum by replacing every component through `x` with `Z`.
  refine le_antisymm ?_ ?_
  · refine iSup_le fun W ↦ ?_
    have hW : W.1 = Z := (hunique W.1).mp W.2
    exact le_of_eq (by rw [hW])
  · let W : { W : irreducibleComponents (PrimeSpectrum A) //
        x ∈ (W : Set (PrimeSpectrum A)) } := ⟨Z, hxZ⟩
    exact le_iSup_of_le W le_rfl

/-- Helper for Chap10 Lemma 10 125 9: the vanishing ideal of an irreducible component of an
affine spectrum is a prime ideal. -/
private theorem vanishingIdeal_irreducibleComponent_isPrime
    {A : Type u} [CommRing A] (Z : irreducibleComponents (PrimeSpectrum A)) :
    (PrimeSpectrum.vanishingIdeal (Z : Set (PrimeSpectrum A))).IsPrime := by
  have hclosed : IsClosed (Z : Set (PrimeSpectrum A)) :=
    isClosed_of_mem_irreducibleComponents (Z : Set (PrimeSpectrum A)) Z.2
  have hmin :
      PrimeSpectrum.vanishingIdeal (Z : Set (PrimeSpectrum A)) ∈ minimalPrimes A := by
    -- Closed irreducible components correspond to minimal prime ideals under vanishing ideals.
    rw [PrimeSpectrum.vanishingIdeal_mem_minimalPrimes]
    simpa [hclosed.closure_eq] using Z.2
  exact Ideal.minimalPrimes_isPrime hmin

omit [IsDomain S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 125 9: quotienting the closed fiber by a component vanishing ideal
gives a domain. -/
private theorem closedFiberComponentQuotient_isDomain
    (Z : irreducibleComponents (PrimeSpectrum ClosedFiber)) :
    IsDomain
      (ClosedFiber ⧸ PrimeSpectrum.vanishingIdeal (Z : Set (PrimeSpectrum ClosedFiber))) := by
  let I := PrimeSpectrum.vanishingIdeal (Z : Set (PrimeSpectrum ClosedFiber))
  -- The component vanishing ideal is prime, so the quotient ring is a domain.
  letI : I.IsPrime := by
    simpa [I] using vanishingIdeal_irreducibleComponent_isPrime Z
  infer_instance

omit [IsDomain S] in
/-- Helper for Chap10 Lemma 10 125 9: component quotients of the closed fiber are finite type
over the residue field of the valuation ring. -/
private theorem closedFiberComponentQuotient_finiteType
    (Z : irreducibleComponents (PrimeSpectrum ClosedFiber)) :
    Algebra.FiniteType (maximalIdeal R).ResidueField
      (ClosedFiber ⧸ PrimeSpectrum.vanishingIdeal (Z : Set (PrimeSpectrum ClosedFiber))) := by
  -- The closed fiber is finite type over the residue field, and finite type descends to quotients.
  infer_instance

omit [IsDomain S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 125 9: the ambient prime attached to a closed-fiber component lies
over the maximal ideal of the valuation ring. -/
private theorem closedFiberComponent_liftedPrime_contracts
    (Z : irreducibleComponents (PrimeSpectrum ClosedFiber)) :
    PrimeSpectrum.comap (algebraMap R S)
        ((PrimeSpectrum.preimageEquivFiber R S
            (⟨maximalIdeal R, inferInstance⟩ : PrimeSpectrum R)).symm
          (⟨PrimeSpectrum.vanishingIdeal (Z : Set (PrimeSpectrum ClosedFiber)),
            vanishingIdeal_irreducibleComponent_isPrime Z⟩ : PrimeSpectrum ClosedFiber)).1 =
      (⟨maximalIdeal R, inferInstance⟩ : PrimeSpectrum R) := by
  -- Specialize the fiber-prime contraction bridge to the closed fiber over the maximal ideal.
  exact preimageEquivFiber_symm_comap
    (R := R) (S := S)
    (⟨maximalIdeal R, inferInstance⟩ : PrimeSpectrum R)
    (⟨PrimeSpectrum.vanishingIdeal (Z : Set (PrimeSpectrum ClosedFiber)),
      vanishingIdeal_irreducibleComponent_isPrime Z⟩ : PrimeSpectrum ClosedFiber)

/-- Helper for Chap10 Lemma 10 125 9: an irreducible component of an affine spectrum has the
Krull dimension of the quotient by its vanishing ideal. -/
private theorem componentTopologicalKrullDim_eq_ringKrullDim_quotient_vanishingIdeal
    {A : Type u} [CommRing A] (Z : irreducibleComponents (PrimeSpectrum A)) :
    topologicalKrullDim (Z : Set (PrimeSpectrum A)) =
      ringKrullDim (A ⧸ PrimeSpectrum.vanishingIdeal (Z : Set (PrimeSpectrum A))) := by
  let I := PrimeSpectrum.vanishingIdeal (Z : Set (PrimeSpectrum A))
  have hzero :
      PrimeSpectrum.zeroLocus (I : Set A) = (Z : Set (PrimeSpectrum A)) := by
    -- The zero locus of the vanishing ideal is the closure, and components are closed.
    calc
      PrimeSpectrum.zeroLocus (I : Set A) =
          closure (Z : Set (PrimeSpectrum A)) := by
        simpa [I] using
          PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure (Z : Set (PrimeSpectrum A))
      _ = (Z : Set (PrimeSpectrum A)) := by
        exact (isClosed_of_mem_irreducibleComponents
          (Z : Set (PrimeSpectrum A)) Z.2).closure_eq
  have hhomeo :
      topologicalKrullDim (PrimeSpectrum (A ⧸ I)) =
        topologicalKrullDim (PrimeSpectrum.zeroLocus (I : Set A)) := by
    -- The quotient spectrum is homeomorphic to the zero locus of the quotient ideal.
    simpa using
      IsHomeomorph.topologicalKrullDim_eq
        (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I)
        (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I).isHomeomorph
  -- Transport the component dimension through the zero-locus homeomorphism and then use the
  -- affine spectrum/ring-dimension comparison.
  calc
    topologicalKrullDim (Z : Set (PrimeSpectrum A)) =
        topologicalKrullDim (PrimeSpectrum.zeroLocus (I : Set A)) := by
      rw [hzero]
    _ = topologicalKrullDim (PrimeSpectrum (A ⧸ I)) := hhomeo.symm
    _ = ringKrullDim (A ⧸ I) :=
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (A ⧸ I)

/-- Helper for Chap10 Lemma 10 125 9: every irreducible component of the closed fiber has the
same topological Krull dimension as the generic fiber. -/
private theorem closedFiberComponentTopologicalKrullDim_eq_genericFiber
    (hRS : Function.Injective (algebraMap R S))
    (Z : irreducibleComponents (PrimeSpectrum ClosedFiber)) :
    topologicalKrullDim (Z : Set (PrimeSpectrum ClosedFiber)) =
      ringKrullDim GenericFiber := by
  -- Route correction: the remaining source-facing theorem is the component-dimension comparison,
  -- not the quotient normal form.  The formal quotient bridge below now consumes this statement,
  -- so the only open proof obligation is the valuation-ring comparison for each component.
  -- TODO(Chap10 Lemma 10 125 9): prove this by choosing a maximal closed-fiber point on `Z`,
  -- identifying the component dimension with `relativeDimensionAt` at its lift to `Spec S`, and
  -- comparing that relative dimension with the generic-fiber Krull dimension by the normalized
  -- valuation-ring polynomial presentation.
  sorry

/-- Helper for Chap10 Lemma 10 125 9: each closed-fiber component quotient has the same
Krull dimension as the generic fiber. -/
private theorem closedFiberComponentQuotient_ringKrullDim_eq_genericFiber
    (hRS : Function.Injective (algebraMap R S))
    (Z : irreducibleComponents (PrimeSpectrum ClosedFiber)) :
    ringKrullDim
        (ClosedFiber ⧸ PrimeSpectrum.vanishingIdeal (Z : Set (PrimeSpectrum ClosedFiber))) =
      ringKrullDim GenericFiber := by
  -- Convert the quotient back to its irreducible component, then use the source-facing component
  -- dimension comparison.
  calc
    ringKrullDim
        (ClosedFiber ⧸ PrimeSpectrum.vanishingIdeal (Z : Set (PrimeSpectrum ClosedFiber))) =
        topologicalKrullDim (Z : Set (PrimeSpectrum ClosedFiber)) :=
      (componentTopologicalKrullDim_eq_ringKrullDim_quotient_vanishingIdeal Z).symm
    _ = ringKrullDim GenericFiber :=
      closedFiberComponentTopologicalKrullDim_eq_genericFiber hRS Z

/-- Helper for Chap10 Lemma 10 125 9: every irreducible component of the closed fiber has the
same topological Krull dimension as the generic fiber. -/
private theorem specialFiber_componentTopologicalKrullDim_eq_genericFiber
    (hRS : Function.Injective (algebraMap R S))
    (Z : irreducibleComponents (PrimeSpectrum ClosedFiber)) :
    topologicalKrullDim (Z : Set (PrimeSpectrum ClosedFiber)) =
      ringKrullDim GenericFiber := by
  -- This compatibility wrapper preserves the older local name used by the public proofs.
  exact closedFiberComponentTopologicalKrullDim_eq_genericFiber hRS Z

/-- Helper for Chap10 Lemma 10 125 9: if all components of an affine finite-type spectrum over a
field have dimension `d`, then the ring Krull dimension is `d`. -/
private theorem ringKrullDim_eq_of_primeSpectrum_components_eq
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    [Nontrivial A] {d : WithBot ℕ∞}
    (hcomp : ∀ Z : irreducibleComponents (PrimeSpectrum A),
      topologicalKrullDim (Z : Set (PrimeSpectrum A)) = d) :
    ringKrullDim A = d := by
  -- Bound the global ring dimension above by bounding every prime quotient by a containing
  -- irreducible component.
  refine le_antisymm ?_ ?_
  · rw [ringKrullDim_eq_iSup_primeQuotient]
    refine iSup_le fun p ↦ ?_
    exact ringKrullDim_primeQuotient_le_componentDimension hcomp p
  · obtain ⟨x⟩ := (inferInstance : Nonempty (PrimeSpectrum A))
    let Z : irreducibleComponents (PrimeSpectrum A) :=
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    -- Any component is a subspace of the full spectrum, giving the reverse inequality.
    calc
      d = topologicalKrullDim (Z : Set (PrimeSpectrum A)) := (hcomp Z).symm
      _ ≤ topologicalKrullDim (PrimeSpectrum A) :=
        topologicalKrullDim_subspace_le (PrimeSpectrum A) (Z : Set (PrimeSpectrum A))
      _ = ringKrullDim A := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A

-- Proof sketch: if the special fiber is trivial then its prime spectrum is empty, hence
-- equidimensional. Otherwise apply the quasi-finite presentation from Lemma 10.125.2 near each
-- prime of the special fiber and combine it with the lower bound from Lemma 10.125.6 to identify
-- the local dimension at every prime with the common dimension of the generic fiber.
/-- Lemma 10.125.9: if `R` is a valuation ring, `S` is a finite type domain over `R`, and the
structure map `R → S` is injective, then the canonical closed fiber
`ClosedFiber = Ideal.Fiber (maximalIdeal R) S`, canonically presented by `κ(R) ⊗[R] S`, has
equidimensional prime spectrum. -/
@[stacks 00QK]
theorem primeSpectrum_specialFiber_equidimensional_of_finiteType_over_valuationRing
    (hRS : Function.Injective (algebraMap R S)) :
    EquidimensionalSpace (PrimeSpectrum ClosedFiber) := by
  -- The geometric helper supplies a common component dimension, so the formal component criterion
  -- gives equidimensionality immediately.
  exact equidimensionalSpace_of_componentTopologicalKrullDim_eq
    (d := ringKrullDim GenericFiber)
    (specialFiber_componentTopologicalKrullDim_eq_genericFiber hRS)

-- Proof sketch: once the special fiber spectrum is equidimensional with every irreducible
-- component having the generic-fiber dimension, the Krull dimension of the special fiber ring is
-- exactly the Krull dimension of the canonical generic fiber `GenericFiber`, which is presented
-- by the tensor model `S ⊗[R] FractionRing R`.
/-- If the special fiber of a finite type domain over a valuation ring is nontrivial, then its
Krull dimension agrees with that of the canonical generic fiber
`GenericFiber = Ideal.Fiber (⊥ : Ideal R) S`, presented by `S ⊗[R] FractionRing R`. -/
theorem ringKrullDim_specialFiber_eq_genericFiber_of_finiteType_over_valuationRing
    (hRS : Function.Injective (algebraMap R S))
    (hspecial : Nontrivial ClosedFiber) :
    ringKrullDim ClosedFiber = ringKrullDim GenericFiber := by
  letI : Nontrivial ClosedFiber := hspecial
  -- Convert the common component dimension from the previous helper into the global ring
  -- dimension of the finite-type closed fiber over the residue field of `R`.
  exact ringKrullDim_eq_of_primeSpectrum_components_eq
    (k := (maximalIdeal R).ResidueField) (A := ClosedFiber)
    (d := ringKrullDim GenericFiber)
    (specialFiber_componentTopologicalKrullDim_eq_genericFiber hRS)

end
