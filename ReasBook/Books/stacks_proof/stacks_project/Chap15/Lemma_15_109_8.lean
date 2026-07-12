import Mathlib
import StacksProject_2024.Chap10.Definition_10_37_11
import StacksProject_2024.Chap10.Definition_10_43_1
import StacksProject_2024.Chap10.Definition_10_162_1
import StacksProject_2024.Chap10.Lemma_10_162_14
import StacksProject_2024.Chap10.Definition_10_165_2
import StacksProject_2024.Chap10.Lemma_10_165_3
import StacksProject_2024.Chap15.Definition_15_107_6
import StacksProject_2024.Chap15.Lemma_15_43_2
import StacksProject_2024.Chap15.Lemma_15_45_6
import StacksProject_2024.Chap15.Lemma_15_51_4
import StacksProject_2024.Chap15.Proposition_15_51_5

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open scoped TensorProduct

universe u

namespace Algebra

/-- Helper for Lemma 15.109.8: a theorem-local bridge packaging geometric reducedness as a
Chapter 15 field-algebra property. -/
abbrev IsGeometricallyReducedProperty : FieldAlgebraProperty :=
  fun k R ↦ fun [Field k] [CommRing R] [Algebra k R] ↦ IsGeometricallyReduced k R

/-- Helper for Lemma 15.109.8: a theorem-local bridge packaging geometric normality as a
Chapter 15 field-algebra property. -/
abbrev IsGeometricallyNormalProperty : FieldAlgebraProperty :=
  fun k R ↦ fun [Field k] [CommRing R] [Algebra k R] ↦ Algebra.IsGeometricallyNormal.{u, u} k R

end Algebra

namespace Algebra

section

variable {k K k' R : Type u}
variable [Field k] [Field K] [Field k'] [CommRing R]
variable [Algebra k R] [Algebra k K] [Algebra k k'] [Algebra k' R] [IsScalarTower k k' R]

/-- Helper for Lemma 15.109.8: geometric reducedness satisfies Chapter 15 axiom `(A)` inside this
file's local proof scaffold. -/
instance isGeometricallyReduced_hasPropertyA_support :
    IsGeometricallyReducedProperty.HasPropertyA where
  baseChange := by
    intro k R K _ _ _ _ _ _ _ hR
    -- Test the base change against one further field extension and cancel the intermediate tensor.
    change IsGeometricallyReduced K (K ⊗[k] R)
    rw [isGeometricallyReduced_iff_forall_isReduced_tensorProduct]
    intro L _ _
    letI : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
    letI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
    let e : L ⊗[K] (K ⊗[k] R) ≃ₐ[K] L ⊗[k] R :=
      Algebra.TensorProduct.cancelBaseChange k K K L R
    letI : IsReduced (L ⊗[k] R) :=
      (isGeometricallyReduced_iff_forall_isReduced_tensorProduct.mp hR) L
    exact isReduced_of_injective e.toRingHom e.injective

/-- Helper for Lemma 15.109.8: geometric normality satisfies Chapter 15 axiom `(A)` inside this
file's local proof scaffold. -/
instance isGeometricallyNormal_hasPropertyA_support :
    IsGeometricallyNormalProperty.HasPropertyA where
  baseChange := by
    intro k A K _ _ _ _ _ _ _ hA
    -- Test geometric normality after one more field extension and cancel the intermediate base
    -- change back to the original geometric-normality hypothesis.
    refine ⟨?_⟩
    intro L _ _
    letI : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
    letI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
    let e : L ⊗[K] (K ⊗[k] A) ≃ₐ[K] L ⊗[k] A :=
      Algebra.TensorProduct.cancelBaseChange k K K L A
    letI : IsNormalRing (L ⊗[k] A) :=
      IsGeometricallyNormal.isNormalRing_baseChange (k := k) (R := A) L
    exact isNormalRing_of_ringEquiv e.toRingEquiv.symm

/-- Helper for Lemma 15.109.8: geometric normality satisfies Chapter 15 axiom `(B)` inside this
file's local proof scaffold. -/
instance isGeometricallyNormal_hasPropertyB_support :
    IsGeometricallyNormalProperty.HasPropertyB where
  localizationCriterion := by
    intro k A _ _ _ _
    constructor
    · intro hA p
      -- Localization preserves geometric normality directly.
      letI : IsGeometricallyNormal k A := hA
      exact Algebra.IsGeometricallyNormal.of_isLocalization p.asIdeal.primeCompl
    · intro hlocal
      refine ⟨?_⟩
      intro K _ _
      let T := K ⊗[k] A
      letI : CommRing T := inferInstance
      letI : Algebra A T := Algebra.TensorProduct.rightAlgebra
      refine ⟨fun q ↦ ?_⟩
      let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A T) q
      let U := K ⊗[k] Localization.AtPrime p.asIdeal
      letI : CommRing U := inferInstance
      let D := T ⊗[A] Localization.AtPrime p.asIdeal
      letI : CommRing D := inferInstance
      letI : Algebra T D := Algebra.TensorProduct.leftAlgebra
      letI : Algebra (Localization.AtPrime p.asIdeal) D := Algebra.TensorProduct.rightAlgebra
      letI : IsLocalization (Algebra.algebraMapSubmonoid T p.asIdeal.primeCompl) D := by
        infer_instance
      let e : D ≃ₐ[K] U :=
        Algebra.IsPushout.cancelBaseChangeAlg k K A T (Localization.AtPrime p.asIdeal)
      have hdisj :
          Disjoint
              ((Algebra.algebraMapSubmonoid T p.asIdeal.primeCompl :
                Submonoid T) : Set T) q.asIdeal := by
        refine Set.disjoint_left.mpr ?_
        intro x hxM hxq
        rcases hxM with ⟨a, ha, rfl⟩
        exact ha (by simpa [p, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using hxq)
      have hqrange : q ∈ Set.range (PrimeSpectrum.comap (algebraMap T D)) := by
        rwa [PrimeSpectrum.localization_comap_range D
          (Algebra.algebraMapSubmonoid T p.asIdeal.primeCompl)]
      rcases hqrange with ⟨qD, hqD_comap⟩
      letI : IsGeometricallyNormal k (Localization.AtPrime p.asIdeal) := hlocal p
      letI : IsNormalRing U :=
        IsGeometricallyNormal.isNormalRing_baseChange (k := k)
          (R := Localization.AtPrime p.asIdeal) K
      have hD : IsNormalRing D := by
        exact isNormalRing_of_faithfullyFlat e.toRingHom
          (RingHom.FaithfullyFlat.of_bijective e.bijective)
      letI : IsNormalRing D := hD
      have hqD_asIdeal :
          Ideal.comap (algebraMap T D) qD.asIdeal = q.asIdeal := by
        simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hqD_comap
      letI : IsLocalization.AtPrime (Localization.AtPrime qD.asIdeal) q.asIdeal := by
        simpa [hqD_asIdeal] using
          (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
            (Algebra.algebraMapSubmonoid T p.asIdeal.primeCompl)
            (Localization.AtPrime qD.asIdeal) qD.asIdeal)
      let eLoc : Localization.AtPrime q.asIdeal ≃ₐ[T] Localization.AtPrime qD.asIdeal :=
        IsLocalization.algEquiv q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime qD.asIdeal)
      -- The chosen localization of `T` is normal because it matches a prime localization of `D`.
      exact
        ⟨Function.Injective.isDomain eLoc.toRingHom eLoc.injective,
          (isIntegrallyClosed_localizationAtPrime qD).of_equiv eLoc.toRingEquiv.symm⟩

end

end Algebra

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.109.8: a local ring is already the localization at the complement of its
maximal ideal. -/
lemma self_isLocalization_primeCompl_maximalIdeal_of_localRing
    (R : Type u) [CommRing R] [IsLocalRing R] :
    IsLocalization (maximalIdeal R).primeCompl R := by
  -- Every element outside the maximal ideal is a unit, so the identity map already satisfies the
  -- universal property of localizing away from the maximal ideal.
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    exact IsLocalRing.notMem_maximalIdeal.mp y.2
  · intro z
    exact ⟨⟨z, 1⟩, by simp⟩
  · intro x y hxy
    exact ⟨1, by simpa using hxy⟩

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.109.8: localizing a local ring at its maximal ideal gives the ring back. -/
noncomputable abbrev localRingLocalizationAtMaximalIdealAlgEquivSelf
    (R : Type u) [CommRing R] [IsLocalRing R] :
    Localization.AtPrime (maximalIdeal R) ≃ₐ[R] R :=
  let _ : IsLocalization (maximalIdeal R).primeCompl R :=
    self_isLocalization_primeCompl_maximalIdeal_of_localRing (R := R)
  Localization.algEquiv (maximalIdeal R).primeCompl R

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.109.8: the residue field at a prime of the closed-point localization is
canonically identified with the residue field at its image in the original local ring. -/
noncomputable def formalFiber_closed_point_localization_residueFieldAlgEquiv_support
    (q : PrimeSpectrum (Localization.AtPrime (maximalIdeal A))) :
    let qA := PrimeSpectrum.comap
      (localRingLocalizationAtMaximalIdealAlgEquivSelf A).symm.toRingHom q
    qA.asIdeal.ResidueField ≃ₐ[A] q.asIdeal.ResidueField := by
  let e := localRingLocalizationAtMaximalIdealAlgEquivSelf A
  let qA := PrimeSpectrum.comap e.symm.toRingHom q
  have hcomap :
      qA.asIdeal = Ideal.comap e.symm.toRingHom q.asIdeal := by
    -- The transported prime is defined by comapping `q` along the localization equivalence.
    simpa [qA, PrimeSpectrum.comap_asIdeal]
  have hcomap_inv :
      q.asIdeal = Ideal.comap e.toRingHom qA.asIdeal := by
    -- The inverse equivalence transports the image prime back to the original one.
    change q.asIdeal = Ideal.comap e.toRingHom (Ideal.comap e.symm.toRingHom q.asIdeal)
    rw [Ideal.comap_comap]
    have hcomp : e.symm.toRingHom.comp e.toRingHom = RingHom.id _ := by
      ext x
      rfl
    simpa [hcomp]
  let f : qA.asIdeal.ResidueField →ₐ[A] q.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ qA.asIdeal q.asIdeal e.symm hcomap
  let g : q.asIdeal.ResidueField →ₐ[A] qA.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ q.asIdeal qA.asIdeal e hcomap_inv
  have hfg : f.toRingHom.comp g.toRingHom = RingHom.id q.asIdeal.ResidueField := by
    -- On residue classes of localization elements, the forward and backward maps cancel.
    apply Ideal.ResidueField.ringHom_ext
    ext x
    change f (g (algebraMap (Localization.AtPrime (maximalIdeal A)) q.asIdeal.ResidueField x)) =
      algebraMap (Localization.AtPrime (maximalIdeal A)) q.asIdeal.ResidueField x
    dsimp [f, g]
    rw [Ideal.ResidueField.map_algebraMap, Ideal.ResidueField.map_algebraMap]
    simpa using congrArg
      (algebraMap (Localization.AtPrime (maximalIdeal A)) q.asIdeal.ResidueField)
      (e.symm_apply_apply x)
  -- The reverse residue-field map provides the right inverse required for bijectivity.
  refine AlgEquiv.ofBijective f ?_
  refine ⟨f.injective, ?_⟩
  intro x
  refine ⟨g x, ?_⟩
  change (f.toRingHom.comp g.toRingHom) x = x
  rw [hfg]
  simp

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.109.8: a prime of the closed-point localization has the same reduced and
normal formal fibers as its image in `A`. -/
lemma formalFiber_closed_point_localization_property_iff_support
    (q : PrimeSpectrum (Localization.AtPrime (maximalIdeal A))) :
    let qA := PrimeSpectrum.comap
      (localRingLocalizationAtMaximalIdealAlgEquivSelf A).symm.toRingHom q
    (Algebra.IsGeometricallyReduced q.asIdeal.ResidueField
        (q.asIdeal.Fiber
          (AdicCompletion
            (maximalIdeal (Localization.AtPrime (maximalIdeal A)))
            (Localization.AtPrime (maximalIdeal A)))) ↔
      Algebra.IsGeometricallyReduced qA.asIdeal.ResidueField (qA.asIdeal.Fiber ACompletion)) ∧
      (Algebra.IsGeometricallyNormal q.asIdeal.ResidueField
          (q.asIdeal.Fiber
            (AdicCompletion
              (maximalIdeal (Localization.AtPrime (maximalIdeal A)))
              (Localization.AtPrime (maximalIdeal A)))) ↔
        Algebra.IsGeometricallyNormal qA.asIdeal.ResidueField (qA.asIdeal.Fiber ACompletion)) := by
  -- TODO: the residue-field part is now isolated in
  -- `formalFiber_closed_point_localization_residueFieldAlgEquiv_support`. The remaining blocker is
  -- the compatible equivalence between the two completed formal-fiber rings, i.e. identifying the
  -- completion of the closed-point localization with `ACompletion` at the chosen prime.
  sorry

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.109.8: the geometric-reducedness formal-fiber hypothesis is unchanged
after replacing a local ring by its localization at the maximal ideal. -/
lemma geometricallyReduced_formalFibers_closed_point_localization_support
    (hred : LocalFormalFibersHaveProperty Algebra.IsGeometricallyReducedProperty A) :
    LocalFormalFibersHaveProperty Algebra.IsGeometricallyReducedProperty
      (Localization.AtPrime (maximalIdeal A)) := by
  intro q
  let qA := PrimeSpectrum.comap
    (localRingLocalizationAtMaximalIdealAlgEquivSelf A).symm.toRingHom q
  -- The centralized closed-point transport lemma removes the duplicated residue-field/fiber
  -- bookkeeping from the property-specific wrapper.
  exact (formalFiber_closed_point_localization_property_iff_support (A := A) q).1.mpr (hred qA)

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.109.8: the geometric-normality formal-fiber hypothesis is unchanged after
replacing a local ring by its localization at the maximal ideal. -/
lemma geometricallyNormal_formalFibers_closed_point_localization_support
    (hgeom : LocalFormalFibersHaveProperty Algebra.IsGeometricallyNormalProperty A) :
    LocalFormalFibersHaveProperty Algebra.IsGeometricallyNormalProperty
      (Localization.AtPrime (maximalIdeal A)) := by
  intro q
  let qA := PrimeSpectrum.comap
    (localRingLocalizationAtMaximalIdealAlgEquivSelf A).symm.toRingHom q
  -- The same closed-point adapter transports geometric normality without duplicating the fiber
  -- comparison argument.
  exact (formalFiber_closed_point_localization_property_iff_support (A := A) q).2.mpr (hgeom qA)

/- Domain-style sampling:
- primary domain: Noetherian local commutative algebra of formal fibers, Nagata rings,
  henselizations, and strict henselizations;
- sampled owner declarations:
  `LocalFormalFibersHaveProperty`,
  `NagataRing`,
  `branchNumber`,
  `geometricBranchNumber`,
  `branchNumber_le_completion_minimalPrimes`,
  `geometricBranchNumber_le_completion`;
- best owner abstraction: the source-facing hypothesis should stay in the Chapter 15 owner
  `LocalFormalFibersHaveProperty`, specialized to the canonical bridge
  `Algebra.IsGeometricallyNormalProperty`. The branch counts should be expressed through the
  existing owners `branchNumber` and `geometricBranchNumber`, while the completion side uses the
  canonical object `ACompletion`;
- primitive data: the Noetherian local ring `A`, a chosen henselization or strict henselization,
  and the chosen strict henselization of `ACompletion`;
- derived API: the Nagata conclusion for `A`, the minimal-prime count of `ACompletion`, and the
  equality of branch counts.

Source/core/bridge triage:
- `source-facing`: the three clauses of Lemma `15.109.8`;
- `core/canonical`: `LocalFormalFibersHaveProperty`, `NagataRing`, `branchNumber`,
  `geometricBranchNumber`, `minimalPrimes`, and `ACompletion`;
- `bridge/view`: the completion comparison theorems from Lemma `15.109.1` and the compatible
  residue-field comparison used internally to build the strict-henselization comparison in part
  `(3)`.
-/

-- Proof sketch: geometrically normal rings are geometrically reduced, so Lemma `15.52.4` upgrades
-- the hypothesis on the formal fibers of `A` to the Nagata property.
omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.109.8: geometrically normal formal fibers are geometrically reduced. -/
lemma localFormalFibersHaveProperty_geometricallyReduced_of_geometricallyNormal
    (hgeom :
      LocalFormalFibersHaveProperty Algebra.IsGeometricallyNormalProperty A) :
    LocalFormalFibersHaveProperty Algebra.IsGeometricallyReducedProperty A := by
  -- Test geometric reducedness on each field extension and use geometric normality there.
  intro q
  change Algebra.IsGeometricallyReduced q.asIdeal.ResidueField
    (q.asIdeal.Fiber (AdicCompletion (maximalIdeal A) A))
  rw [Algebra.isGeometricallyReduced_iff_forall_isReduced_tensorProduct]
  intro K _ _
  letI :
      Algebra.IsGeometricallyNormal q.asIdeal.ResidueField
        (q.asIdeal.Fiber (AdicCompletion (maximalIdeal A) A)) := hgeom q
  letI : IsNormalRing
      (K ⊗[q.asIdeal.ResidueField] (q.asIdeal.Fiber (AdicCompletion (maximalIdeal A) A))) :=
    Algebra.IsGeometricallyNormal.isNormalRing_baseChange
      (k := q.asIdeal.ResidueField)
      (R := q.asIdeal.Fiber (AdicCompletion (maximalIdeal A) A))
      K
  -- A normal ring is reduced; spell this out through maximal localizations to keep the reduction
  -- step explicit instead of relying on a fragile instance search here.
  refine isReduced_ofLocalizationMaximal
      (K ⊗[q.asIdeal.ResidueField] (q.asIdeal.Fiber (AdicCompletion (maximalIdeal A) A))) ?_
  intro p hp
  let p' :
      PrimeSpectrum
        (K ⊗[q.asIdeal.ResidueField] (q.asIdeal.Fiber (AdicCompletion (maximalIdeal A) A))) :=
    ⟨p, inferInstance⟩
  letI :
      IsDomain
        (Localization.AtPrime p) := by
    simpa using
      (isDomain_localizationAtPrime
        (R := K ⊗[q.asIdeal.ResidueField] (q.asIdeal.Fiber (AdicCompletion (maximalIdeal A) A)))
        p')
  infer_instance

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.109.8: specializing to the closed point shows that the closed formal fiber
is geometrically normal. -/
lemma maximalIdeal_fiber_isGeometricallyNormal_of_geometricallyNormal
    (hgeom :
      LocalFormalFibersHaveProperty Algebra.IsGeometricallyNormalProperty A) :
    Algebra.IsGeometricallyNormal
      (maximalIdeal A).ResidueField ((maximalIdeal A).Fiber ACompletion) := by
  let q : PrimeSpectrum A := ⟨maximalIdeal A, inferInstance⟩
  -- The closed point of a local ring is represented by its maximal ideal.
  simpa [q] using hgeom q

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.109.8: the same specialization gives a geometrically reduced closed formal
fiber. -/
lemma maximalIdeal_fiber_isGeometricallyReduced_of_geometricallyNormal
    (hgeom :
      LocalFormalFibersHaveProperty Algebra.IsGeometricallyNormalProperty A) :
    Algebra.IsGeometricallyReduced
      (maximalIdeal A).ResidueField ((maximalIdeal A).Fiber ACompletion) := by
  let q : PrimeSpectrum A := ⟨maximalIdeal A, inferInstance⟩
  -- Reuse the global normal-to-reduced reduction before restricting to the closed point.
  have hred :
      LocalFormalFibersHaveProperty Algebra.IsGeometricallyReducedProperty A :=
    localFormalFibersHaveProperty_geometricallyReduced_of_geometricallyNormal (A := A) hgeom
  simpa [q] using hred q

omit [IsLocalRing A] [IsNoetherianRing A] in
/-- Helper for Lemma 15.109.8: essentially finite type local extensions preserve the corresponding
`P`-ring structure once the Chapter 15 axioms for `P` are available. -/
lemma isPRing_of_essFiniteType_local_support
    (P : FieldAlgebraProperty)
    [P.HasPropertyA] [P.HasPropertyB] [P.HasPropertyC] [P.HasPropertyD]
    {S : Type u} [CommRing S] [Algebra A S] [Algebra.EssFiniteType A S] [IsLocalRing S]
    (hP : IsPRing P A) :
    IsPRing P S := by
  -- This is exactly Proposition `15.51.5`, repackaged in the local-ring shape used below.
  exact isPRing_of_essFiniteType (P := P) hP

/-- Helper for Lemma 15.109.8: for a Noetherian local ring, the maximal-ideal criterion for a
`P`-ring reduces to transporting the closed formal-fiber hypothesis to the closed-point
localization. -/
theorem isPRing_of_localFormalFibersHaveProperty_closedPoint_support
    (P : FieldAlgebraProperty)
    [P.HasPropertyC] [P.HasPropertyD]
    (htransport :
      LocalFormalFibersHaveProperty P A →
        LocalFormalFibersHaveProperty P (Localization.AtPrime (maximalIdeal A)))
    (hformal : LocalFormalFibersHaveProperty P A) :
    IsPRing P A := by
  -- The generic criterion from Lemma `15.51.4` only asks for the closed point in the local case.
  rw [isPRing_iff_localFormalFibersHaveProperty_atMaximal]
  intro m
  have hm : m.asIdeal = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal m.isMaximal
  cases m
  cases hm
  simpa using htransport hformal

/-- Helper for Lemma 15.109.8: geometrically reduced formal fibers imply the local Nagata
property. -/
theorem nagataRing_of_geometricallyReduced_formalFibers_support
    (hred :
      LocalFormalFibersHaveProperty Algebra.IsGeometricallyReducedProperty A) :
    NagataRing A := by
  -- Route correction: the direct owner import `15.52.4` still fails in this workspace through the
  -- `15.42.2` / `15.41.1` regular-map collision, so keep the local Nagata reduction isolated.
  -- TODO: finish the geometric-reducedness `(A)`-`(D)` package locally; the closed-point
  -- localization transport is now available in the concrete geometric-reducedness form
  -- `geometricallyReduced_formalFibers_closed_point_localization_support`.
  sorry

/-- Lemma 15.109.8 (1): if the formal fibers of the Noetherian local ring `A` are geometrically
normal, then `A` is a Nagata ring. This applies in particular when `A` is excellent or
quasi-excellent. -/
@[stacks 0C2E]
theorem nagataRing_of_geometricallyNormal_formalFibers
    (hgeom :
      LocalFormalFibersHaveProperty Algebra.IsGeometricallyNormalProperty A) :
    NagataRing A := by
  -- First reduce the hypothesis from geometric normality to geometric reducedness on formal fibers.
  have hred :
      LocalFormalFibersHaveProperty Algebra.IsGeometricallyReducedProperty A :=
    localFormalFibersHaveProperty_geometricallyReduced_of_geometricallyNormal hgeom
  -- Route correction: the import-based reuse of `15.52.4` is blocked here by the `15.42.2` vs.
  -- `15.41.1` regular-map owner collision, so isolate the exact source-faithful forward direction
  -- needed for this item as a local support lemma.
  exact nagataRing_of_geometricallyReduced_formalFibers_support (A := A) hred

variable {Ah : Type u}
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

-- Proof sketch: first use part `(1)` to see that `A` is Nagata. Then compare the minimal primes
-- of a chosen henselization `Ah` with those of the completion `ACompletion`: Lemma `15.109.1`
-- gives one inequality, and the Stacks argument reduces the reverse inequality to the domain case,
-- passes to the normalization, and uses normality of the completed local factors.
/-- Lemma 15.109.8 (2): if the formal fibers of the Noetherian local ring `A` are geometrically
normal, then the number of branches of `A`, computed from a chosen henselization `Ah`, equals the
number of minimal primes of its completion `ACompletion`. -/
@[stacks 0C2E]
theorem branchNumber_eq_completion_minimalPrimes_of_geometricallyNormal_formalFibers
    (hgeom :
      LocalFormalFibersHaveProperty Algebra.IsGeometricallyNormalProperty A) :
    branchNumber A Ah = (minimalPrimes ACompletion).encard := by
  -- First record the Nagata conclusion, which is the normalization input in the source proof.
  have hNagata : NagataRing A :=
    nagataRing_of_geometricallyNormal_formalFibers (A := A) hgeom
  -- TODO: carry out the source-faithful normalization/completion sandwich after recovering the
  -- broken completion-comparison layer from `15.109.1`: compare `branchNumber A Ah` and
  -- `(minimalPrimes ACompletion).encard` with the maximal spectrum of the unibranch
  -- normalization of `A`, using the Nagata finiteness statement above.
  sorry

variable {Ash Ahatsh : Type u}
variable [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
variable [CommRing Ahatsh] [Algebra (AdicCompletion (maximalIdeal A) A) Ahatsh]
variable [IsStrictHenselizationOf (AdicCompletion (maximalIdeal A) A) Ahatsh]

-- Proof sketch: apply the branch-count equality to the strict henselization `Ash`, using that
-- strict henselizations preserve geometrically normal formal fibers and the canonical
-- strict-henselization completion comparison from Lemma `15.109.1`; the compatible
-- residue-field comparison needed to build that bridge is internal to the proof.
/-- Lemma 15.109.8 (3): if the formal fibers of the Noetherian local ring `A` are geometrically
normal, then the number of geometric branches of `A` equals the number of geometric branches of
its completion `ACompletion`. -/
@[stacks 0C2E]
theorem geometricBranchNumber_eq_completion_of_geometricallyNormal_formalFibers
    (hgeom :
      LocalFormalFibersHaveProperty Algebra.IsGeometricallyNormalProperty A) :
    geometricBranchNumber A Ash = geometricBranchNumber ACompletion Ahatsh := by
  -- TODO: follow the source route through the strict henselization `Ash`: first show that `Ash`
  -- again has geometrically normal formal fibers, then apply part `(2)` to `Ash`, and finally
  -- identify the completion of `Ash` with the chosen strict henselization over `ACompletion`.
  sorry

end
