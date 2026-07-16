import Mathlib
import stacks_proof.stacks_project.Chap15.Definition_15_107_6
import stacks_proof.stacks_project.Chap15.Definition_15_107_1
import stacks_proof.stacks_project.Chap15.Lemma_15_45_6
import stacks_proof.stacks_project.Chap15.Lemma_15_45_13
import stacks_proof.stacks_project.Chap15.Lemma_15_107_2
import stacks_proof.stacks_project.Chap15.Lemma_15_107_3
import stacks_proof.stacks_project.Chap15.Lemma_15_107_4
import stacks_proof.stacks_project.Chap15.Lemma_15_107_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open scoped Unibranch
open Algebra.TensorProduct
open IsLocalRing

universe u

noncomputable section

/-
Domain-style sampling:
- primary domain: local commutative algebra of henselizations, strict henselizations, minimal
  primes, and the unibranch normalization;
- sampled owner declarations of the same kind:
  `branchNumber`,
  `geometricBranchNumber`,
  `IsUnibranch`,
  `MaximalSpectrum`;
- best owner abstraction: `branchNumber` and `geometricBranchNumber` remain the source-facing
  owners, while the maximal-ideal side of the finite formulas should be expressed through the
  canonical owner `MaximalSpectrum A′` instead of a parallel subtype of maximal ideals;
- primitive data: the local ring `A` together with a chosen henselization or strict
  henselization;
- derived API: cardinality comparisons for minimal primes and for the maximal spectrum of the
  unibranch normalization.

Source/core/bridge triage:
- `source-facing`: the six clauses of Lemma 15.107.7;
- `core/canonical`: `branchNumber`, `geometricBranchNumber`, `IsUnibranch`,
  `IsGeometricallyUnibranch`, `minimalPrimes`, and `MaximalSpectrum`;
- `bridge/view`: the finite-count formulas over `MaximalSpectrum A′`.
-/

/-- Helper for Lemma 15.107.7: a set has cardinality `1` exactly when it has a unique element. -/
lemma encard_eq_one_iff_existsUnique_mem {α : Type u} (s : Set α) :
    s.encard = 1 ↔ ∃! x, x ∈ s := by
  constructor
  · intro hs
    -- Rewrite a singleton cardinality statement as an explicit unique witness.
    rcases Set.encard_eq_one.mp hs with ⟨x, rfl⟩
    refine ⟨x, by simp, ?_⟩
    intro y hy
    simpa using hy
  · rintro ⟨x, hx, huniq⟩
    -- A unique element identifies the set with the singleton containing that element.
    have hs : s = ({x} : Set α) := by
      ext y
      constructor
      · intro hy
        exact huniq y hy
      · rintro rfl
        exact hx
    rw [hs, Set.encard_singleton]

/-- Helper for Lemma 15.107.7: a set-theoretic bijection induces an equivalence of the
corresponding subtype carriers. -/
noncomputable def subtypeEquivOfBijOn
    {α β : Type*} {s : Set α} {t : Set β} {f : α → β}
    (hbij : Set.BijOn f s t) :
    s ≃ t := by
  classical
  refine
    { toFun := fun x ↦ ⟨f x, hbij.mapsTo x.property⟩
      invFun := fun y ↦ ⟨Classical.choose (hbij.surjOn y.property),
        (Classical.choose_spec (hbij.surjOn y.property)).1⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    -- The inverse chooses the unique source point mapping to `f x`.
    apply Subtype.ext
    exact hbij.injOn
      (Classical.choose_spec (hbij.surjOn (hbij.mapsTo x.property))).1
      x.property
      (Classical.choose_spec (hbij.surjOn (hbij.mapsTo x.property))).2
  · intro y
    -- The chosen preimage of a target point maps back to that target point.
    apply Subtype.ext
    exact (Classical.choose_spec (hbij.surjOn y.property)).2

/-- Helper for Lemma 15.107.7: unique witnesses in both directions along a relation give an
equivalence between the corresponding subtype carriers. -/
noncomputable def subtypeEquivOf_existsUnique_relation
    {α β : Type*} {s : Set α} {t : Set β} (R : α → β → Prop)
    (hs : ∀ ⦃x : α⦄, x ∈ s → ∃! y, y ∈ t ∧ R x y)
    (ht : ∀ ⦃y : β⦄, y ∈ t → ∃! x, x ∈ s ∧ R x y) :
    s ≃ t := by
  classical
  refine
    { toFun := fun x ↦ ⟨Classical.choose (hs x.property),
        (Classical.choose_spec (hs x.property)).1.1⟩
      invFun := fun y ↦ ⟨Classical.choose (ht y.property),
        (Classical.choose_spec (ht y.property)).1.1⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    -- Move to the uniquely determined target witness and back.
    let hy : ∃! y, y ∈ t ∧ R x.1 y := hs x.property
    have hy_spec : Classical.choose hy ∈ t ∧ R x.1 (Classical.choose hy) :=
      (Classical.choose_spec hy).1
    let hx : ∃! x', x' ∈ s ∧ R x' (Classical.choose hy) := ht hy_spec.1
    have hx_eq : x.1 = Classical.choose hx :=
      (Classical.choose_spec hx).2 x.1 ⟨x.property, hy_spec.2⟩
    apply Subtype.ext
    exact hx_eq.symm
  · intro y
    -- The same uniqueness argument shows that the chosen source point returns to `y`.
    let hx : ∃! x, x ∈ s ∧ R x y.1 := ht y.property
    have hx_spec : Classical.choose hx ∈ s ∧ R (Classical.choose hx) y.1 :=
      (Classical.choose_spec hx).1
    let hy : ∃! y', y' ∈ t ∧ R (Classical.choose hx) y' := hs hx_spec.1
    have hy_eq : y.1 = Classical.choose hy :=
      (Classical.choose_spec hy).2 y.1 ⟨y.property, hx_spec.2⟩
    apply Subtype.ext
    exact hy_eq.symm

/-- Helper for Lemma 15.107.7: maximal ideals are canonically the same as points of the maximal
spectrum. -/
noncomputable def maximalIdealSubtype_equiv_maximalSpectrum
    (R : Type*) [CommRing R] :
    {m : Ideal R // m.IsMaximal} ≃ MaximalSpectrum R :=
  (MaximalSpectrum.equivSubtype R).symm

/-- Helper for Lemma 15.107.7: under a faithfully flat algebra map, minimal primes contract to
minimal primes. -/
lemma comap_mem_minimalPrimes_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hff : (algebraMap R S).FaithfullyFlat) {Q : Ideal S}
    (hQ : Q ∈ minimalPrimes S) :
    Ideal.comap (algebraMap R S) Q ∈ minimalPrimes R := by
  -- Flatness gives going down, so any smaller prime downstairs would lift to a smaller prime
  -- upstairs, contradicting minimality of `Q`.
  have hflat : (algebraMap R S).Flat := hff.flat
  let _ : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hflat
  refine ⟨⟨Ideal.minimalPrimes_isPrime hQ, bot_le⟩, ?_⟩
  intro J hJ hJ_le
  by_cases hQJ : Ideal.comap (algebraMap R S) Q = J
  · exact hQJ.le
  · let _ : Algebra.HasGoingDown R S := Algebra.HasGoingDown.of_flat
    let _ : J.IsPrime := hJ.1
    let _ : Q.IsPrime := Ideal.minimalPrimes_isPrime hQ
    let _ : Q.LiesOver (Ideal.comap (algebraMap R S) Q) := ⟨rfl⟩
    have hJ_lt_Q : J < Ideal.comap (algebraMap R S) Q :=
      lt_of_le_of_ne hJ_le (Ne.symm hQJ)
    obtain ⟨Q', hQ'_lt, hQ'_prime, _⟩ :=
      Ideal.exists_ideal_lt_liesOver_of_lt (R := R) (S := S) (Q := Q) hJ_lt_Q
    have hQ_le_Q' : Q ≤ Q' :=
      hQ.2 ⟨hQ'_prime, bot_le⟩ hQ'_lt.le
    exact (hQ'_lt.not_ge hQ_le_Q').elim

/-- Helper for Lemma 15.107.7: contraction along a faithfully flat algebra map is surjective on
minimal primes. -/
lemma surjOn_minimalPrimes_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hff : (algebraMap R S).FaithfullyFlat) :
    Set.SurjOn (Ideal.comap (algebraMap R S)) (minimalPrimes S) (minimalPrimes R) := by
  refine ⟨?_, ?_⟩
  · intro Q hQ
    -- The forward direction is exactly the contraction lemma above.
    exact comap_mem_minimalPrimes_of_faithfullyFlat hff hQ
  · intro q hq
    -- Injectivity plus the minimal-prime lifting theorem produce a prime upstairs over `q`.
    have hinj : Function.Injective (algebraMap R S) := hff.injective
    have hker : RingHom.ker (algebraMap R S) = ⊥ := RingHom.ker_eq_bot.2 hinj
    have hqker : q ∈ (RingHom.ker (algebraMap R S)).minimalPrimes := by
      refine ⟨⟨Ideal.minimalPrimes_isPrime hq, ?_⟩, ?_⟩
      · simpa [hker]
      · intro I hI hIq
        exact hq.2 ⟨hI.1, by simpa [hker] using hI.2⟩ hIq
    obtain ⟨Q, hQ, hQq⟩ :=
      Ideal.exists_minimalPrimes_comap_eq (algebraMap R S) q hqker
    exact ⟨Q, hQ, hQq⟩

section Henselization

variable (A Ah : Type u)
variable [CommRing A] [IsLocalRing A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

local notation "A′h" => A′ ⊗[A] Ah

/-- Helper for Lemma 15.107.7: finite-branch comparison identifies minimal primes of the chosen
henselization with maximal points of the unibranch normalization. -/
noncomputable def henselization_minimalPrimes_equiv_maximalSpectrum_unibranchNormalization
    (hfinite : (minimalPrimes A).Finite) :
    {p : Ideal Ah // p ∈ minimalPrimes Ah} ≃ MaximalSpectrum A′ := by
  -- First move minimal primes from `Ah` to the tensor-product normalization.
  let e_min :
      {p : Ideal A′h // p ∈ minimalPrimes A′h} ≃ {p : Ideal Ah // p ∈ minimalPrimes Ah} :=
    subtypeEquivOfBijOn
      (unibranchNormalizationTensorHenselization_bijOn_minimalPrimes
        (A := A) (Ah := Ah) hfinite)
  -- Next, use the unique minimal/maximal-ideal correspondence on the tensor-product side.
  let e_mid :
      {p : Ideal A′h // p ∈ minimalPrimes A′h} ≃ {m : Ideal A′h // m.IsMaximal} :=
    subtypeEquivOf_existsUnique_relation
      (s := minimalPrimes A′h)
      (t := {m : Ideal A′h | m.IsMaximal})
      (R := fun p m ↦ p ≤ m)
      (fun {_} hp ↦ by
        simpa using
          (unibranchNormalizationTensorHenselization_minimalPrime_existsUnique_maximalIdeal
            (A := A) (Ah := Ah) hfinite hp))
      (fun {_} hm ↦ by
        simpa using
          (unibranchNormalizationTensorHenselization_maximalIdeal_existsUnique_minimalPrime
            (A := A) (Ah := Ah) hfinite hm))
  -- Finally transport maximal ideals of `A′h` back to maximal ideals, hence maximal points, of
  -- `A′`.
  let e_max :
      {m : Ideal A′h // m.IsMaximal} ≃ {m : Ideal A′ // m.IsMaximal} :=
    subtypeEquivOfBijOn
      (unibranchNormalizationTensorHenselization_bijOn_maximalIdeals
        (A := A) (Ah := Ah) hfinite)
  exact e_min.symm.trans <| e_mid.trans <| e_max.trans <|
    maximalIdealSubtype_equiv_maximalSpectrum A′

-- Proof sketch: use the comparison of minimal primes from the henselization count with the reduced
-- integral closure and the fact that an infinite set of minimal primes forces the counted set in
-- the definition of `branchNumber` to have infinite cardinality.
/-- Lemma 15.107.7 (1): if a local ring `A` has infinitely many minimal prime ideals, then the
number of branches of `A`, computed from a chosen henselization `Ah`, is `∞`. -/
@[stacks 0C37]
theorem branchNumber_eq_top_of_infinite_minimalPrimes
    (hinf : (minimalPrimes A).Infinite) :
    branchNumber A Ah = ⊤ := by
  -- The henselization map is faithfully flat, so every minimal prime of `A` is the contraction
  -- of a minimal prime of `Ah`.
  have hsurj :
      Set.SurjOn (Ideal.comap (algebraMap A Ah)) (minimalPrimes Ah) (minimalPrimes A) :=
    surjOn_minimalPrimes_of_faithfullyFlat (R := A) (S := Ah)
      (algebraMap_faithfullyFlat_of_isHenselizationOf (R := A) (Rh := Ah))
  have hnotfin : ¬ (minimalPrimes Ah).Finite := by
    intro hfinite
    exact hinf (Set.Finite.of_surjOn _ hsurj hfinite)
  have hinfAh : (minimalPrimes Ah).Infinite := Set.not_finite_iff_infinite.mp hnotfin
  -- Now unfold the source-facing definition and read off the infinite cardinality.
  simpa [branchNumber] using Set.Infinite.encard_eq hinfAh

-- Proof sketch: unfold `branchNumber` and combine Lemma `15.107.3`, turning the statement
-- `branchNumber A Ah = 1` into the existence of a unique minimal prime of `Ah`.
/-- Lemma 15.107.7 (2): the number of branches of `A`, computed from a chosen henselization `Ah`,
is `1` if and only if `A` is unibranch. -/
@[stacks 0C37]
theorem branchNumber_eq_one_iff_isUnibranch :
    branchNumber A Ah = 1 ↔ IsUnibranch A := by
  -- Unfold the branch count and rewrite `encard = 1` as uniqueness of a minimal prime.
  rw [branchNumber, encard_eq_one_iff_existsUnique_mem]
  simpa using
    (isUnibranch_iff_existsUnique_minimalPrime_henselization (A := A) (Ah := Ah)).symm

-- Proof sketch: apply Lemma `15.107.2` to identify minimal primes of the henselization-side
-- normalization base change with minimal primes of `Ah`, then use Lemma `15.107.2 (4)` to replace
-- those minimal primes by points of the maximal spectrum of the reduced integral closure `A'`.
/-- Lemma 15.107.7 (3): if `A` has finitely many minimal primes, then the number of branches of
`A`, computed from a chosen henselization `Ah`, is the number of points of the maximal spectrum of
the unibranch normalization `A'` of `A`. -/
@[stacks 0C37]
theorem branchNumber_eq_encard_maximalIdeals_unibranchNormalization
    (hfinite : (minimalPrimes A).Finite) :
    branchNumber A Ah = (Set.univ : Set (MaximalSpectrum A′)).encard := by
  -- Route correction: follow the source proof literally by transporting the counted set through
  -- the henselization comparison, the unique minimal/maximal-ideal correspondence, and then the
  -- maximal-spectrum wrapper.
  rw [branchNumber]
  simpa using
    Set.encard_congr
      (henselization_minimalPrimes_equiv_maximalSpectrum_unibranchNormalization
        (A := A) (Ah := Ah) hfinite)

end Henselization

section StrictHenselization

variable (A Ash : Type u)
variable [CommRing A] [IsLocalRing A]
variable [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]

local notation "κ" => ResidueField A
local notation "A′sh" => A′ ⊗[A] Ash

/-- Helper for Lemma 15.107.7: after moving from `Ash` to `A′sh`, the source proof next groups
minimal primes by their unique containing maximal ideal. -/
private noncomputable def strictHenselization_minimalPrimes_equiv_maximalIdeals
    (hfinite : (minimalPrimes A).Finite) :
    {p : Ideal A′sh // p ∈ minimalPrimes A′sh} ≃ {n : Ideal A′sh // n.IsMaximal} :=
  subtypeEquivOf_existsUnique_relation
    (s := minimalPrimes A′sh)
    (t := {n : Ideal A′sh | n.IsMaximal})
    (R := fun p n ↦ p ≤ n)
    (fun {_} hp ↦
      unibranchNormalizationTensorStrictHenselization_minimalPrime_existsUnique_maximalIdeal
        (A := A) (Ash := Ash) hfinite hp)
    (fun {_} hn ↦
      unibranchNormalizationTensorStrictHenselization_maximalIdeal_existsUnique_minimalPrime
        (A := A) (Ash := Ash) hfinite hn)

/-- Helper for Lemma 15.107.7: the remaining strict-henselization residue-field input is a
closed-point algebraicity statement for the residue field of the strict henselization. -/
private theorem strictHenselization_closedPoint_residueField_isAlgebraic :
    Algebra.IsAlgebraic κ (ResidueField Ash) := by
  let p : PrimeSpectrum A := ⟨maximalIdeal A, inferInstance⟩
  let q : p.asIdeal.primesOver Ash := Ideal.primesOver.mk p.asIdeal (maximalIdeal Ash)
  -- Apply the strict-henselization residue-field theorem at the closed point.
  simpa [p] using
    (strictHenselization_residueField_isAlgebraic_and_separable
      (R := A) (Rsh := Ash) p q).1

/-- Helper for Lemma 15.107.7: the remaining strict-henselization residue-field input is a
compatible `κ`-algebra map into the chosen algebraic closure. -/
private noncomputable def strictHenselization_residueField_to_algClosure :
    ResidueField Ash →ₐ[κ] AlgebraicClosure κ :=
  let _ : Algebra.IsAlgebraic κ (ResidueField Ash) :=
    strictHenselization_closedPoint_residueField_isAlgebraic (A := A) (Ash := Ash)
  -- Lift the algebraic residue-field extension into the fixed algebraic closure.
  IsAlgClosed.lift κ (ResidueField Ash) (AlgebraicClosure κ)

/-- Helper for Lemma 15.107.7: once a compatible `κ`-algebra map from the residue field of the
strict henselization is fixed, Lemma `15.107.4 (2)` gives the fiber-prime equivalence directly. -/
private noncomputable def fiberPrime_equiv_algHom
    {Kbar : Type u} [Field Kbar] [Algebra κ Kbar] [IsAlgClosure κ Kbar]
    (τ : ResidueField Ash →ₐ[κ] Kbar)
    (m : MaximalSpectrum A′) :
    PrimeSpectrum (m.asIdeal.Fiber A′sh) ≃ (m.asIdeal.ResidueField →ₐ[κ] Kbar) :=
  (fiberPrimeOfAlgHomEquiv (A := A) (Ash := Ash) τ m).symm

/-- Helper for Lemma 15.107.7: fiberwise, the source proof already reduces counting minimal
primes to counting `κ`-algebra maps into a chosen algebraic closure of `κ`. -/
private noncomputable def strictHenselization_fiberSigma_equiv_algHom
    {Kbar : Type u} [Field Kbar] [Algebra κ Kbar] [IsAlgClosure κ Kbar]
    (τ : ResidueField Ash →ₐ[κ] Kbar) :
    (Σ m : MaximalSpectrum A′, PrimeSpectrum (m.asIdeal.Fiber A′sh)) ≃
      (Σ m : MaximalSpectrum A′, (m.asIdeal.ResidueField →ₐ[κ] Kbar)) :=
  Equiv.sigmaCongrRight fun m ↦ fiberPrime_equiv_algHom (A := A) (Ash := Ash) τ m

/-- Helper for Lemma 15.107.7: maximal ideals of `A′sh` should be decomposed by contraction to a
point of `MaximalSpectrum A′` together with the corresponding fiber prime. -/
private noncomputable def strictHenselization_maximalIdeals_equiv_fiberSigma :
    {n : Ideal A′sh // n.IsMaximal} ≃
      (Σ m : MaximalSpectrum A′, PrimeSpectrum (m.asIdeal.Fiber A′sh)) :=
  -- TODO: contract a maximal ideal of `A′sh` to `A′`, prove the contraction is maximal, and then
  -- transport the prime through `PrimeSpectrum.preimageEquivFiber` with the inverse direction as
  -- the explicit inverse map.
  sorry

/-- Helper for Lemma 15.107.7: after fixing the residue-field map `τ`, the fiberwise count is the
same as the weighted count by `κ`-embeddings into the algebraic closure. -/
private noncomputable def strictHenselization_fiberSigma_equiv_weighted_maximalSpectrum
    (τ : ResidueField Ash →ₐ[κ] AlgebraicClosure κ) :
    (Σ m : MaximalSpectrum A′, PrimeSpectrum (m.asIdeal.Fiber A′sh)) ≃
      (Σ m : MaximalSpectrum A′, Field.Emb κ m.ResidueField) :=
  (strictHenselization_fiberSigma_equiv_algHom (A := A) (Ash := Ash) τ).trans
    (Equiv.sigmaCongrRight fun m ↦
      (Field.embEquivOfIsAlgClosed κ m.ResidueField (AlgebraicClosure κ)).symm)

/-- Helper for Lemma 15.107.7: clause `(6)` reduces to the source-faithful sigma decomposition of
minimal primes of `A' ⊗[A] A^sh` by their closed-fiber point in `MaximalSpectrum A'`. -/
noncomputable def
    strictHenselization_minimalPrimes_equiv_weighted_maximalSpectrum_unibranchNormalization
    (hfinite : (minimalPrimes A).Finite) :
    {p : Ideal Ash // p ∈ minimalPrimes Ash} ≃
      (Σ m : MaximalSpectrum A′, Field.Emb κ m.ResidueField) :=
  let e_min :
      {p : Ideal Ash // p ∈ minimalPrimes Ash} ≃
        {p : Ideal A′sh // p ∈ minimalPrimes A′sh} :=
    (subtypeEquivOfBijOn
      (unibranchNormalizationTensorStrictHenselization_bijOn_minimalPrimes
        (A := A) (Ash := Ash) hfinite)).symm
  -- Route correction: isolate the source midpoint
  -- `A′sh`-minimal-primes `≃` `A′sh`-maximal-ideals before the fiber decomposition.
  e_min.trans <|
    (strictHenselization_minimalPrimes_equiv_maximalIdeals (A := A) (Ash := Ash) hfinite).trans <|
      (strictHenselization_maximalIdeals_equiv_fiberSigma (A := A) (Ash := Ash)).trans <|
        strictHenselization_fiberSigma_equiv_weighted_maximalSpectrum
          (A := A) (Ash := Ash)
          (strictHenselization_residueField_to_algClosure (A := A) (Ash := Ash))

-- Proof sketch: use the strict henselization analogue of the branch count and compare minimal
-- primes through Lemma `15.107.4`; an infinite set of minimal primes forces the strict
-- henselization count to be infinite as well.
/-- Lemma 15.107.7 (4): if a local ring `A` has infinitely many minimal prime ideals, then the
number of geometric branches of `A`, computed from a chosen strict henselization `Ash`, is `∞`. -/
@[stacks 0C37]
theorem geometricBranchNumber_eq_top_of_infinite_minimalPrimes
    (hinf : (minimalPrimes A).Infinite) :
    geometricBranchNumber A Ash = ⊤ := by
  -- The strict henselization map is also faithfully flat, so the same minimal-prime contraction
  -- argument applies verbatim.
  have hsurj :
      Set.SurjOn (Ideal.comap (algebraMap A Ash)) (minimalPrimes Ash) (minimalPrimes A) :=
    surjOn_minimalPrimes_of_faithfullyFlat (R := A) (S := Ash)
      (algebraMap_faithfullyFlat_of_isStrictHenselizationOf (R := A) (Rsh := Ash))
  have hnotfin : ¬ (minimalPrimes Ash).Finite := by
    intro hfinite
    exact hinf (Set.Finite.of_surjOn _ hsurj hfinite)
  have hinfAsh : (minimalPrimes Ash).Infinite := Set.not_finite_iff_infinite.mp hnotfin
  -- Unfold the geometric branch count and read off the infinite cardinality.
  simpa [geometricBranchNumber] using Set.Infinite.encard_eq hinfAsh

-- Proof sketch: unfold `geometricBranchNumber` and combine Lemma `15.107.5`, turning the
-- statement
-- `geometricBranchNumber A Ash = 1` into the existence of a unique minimal prime of `Ash`.
/-- Lemma 15.107.7 (5): the number of geometric branches of `A`, computed from a chosen strict
henselization `Ash`, is `1` if and only if `A` is geometrically unibranch. -/
@[stacks 0C37]
theorem geometricBranchNumber_eq_one_iff_isGeometricallyUnibranch :
    geometricBranchNumber A Ash = 1 ↔ IsGeometricallyUnibranch A := by
  -- Route correction: close this clause by the direct strict-henselization criterion from
  -- Lemma `15.107.5`, rather than by duplicating its unique-minimal-prime argument locally.
  rw [geometricBranchNumber, encard_eq_one_iff_existsUnique_mem]
  simpa using
    (isGeometricallyUnibranch_iff_existsUnique_minimalPrime_strictHenselization
      (A := A) (Ash := Ash)).symm

-- Proof sketch: use Lemma `15.107.4 (3)` to replace minimal primes of `Ash` by minimal primes of
-- `A' ⊗[A] A^sh`, use Lemma `15.107.4 (5)` to group them by maximal ideals of `A'`, and then
-- identify each fiber with the separable-degree multiplicity from the residue field extension over
-- `κ` by the actual embedding type `Field.Emb κ m.ResidueField`, equivalently `[κ(m') : κ]_s`,
-- using Lemma `15.107.4 (2)` together with Fields, Lemma `9.14.8`.
/-- Lemma 15.107.7 (6): if `A` has finitely many minimal primes, then the number of geometric
branches of `A`, computed from a chosen strict henselization `Ash`, is obtained by counting each
point `m'` of the maximal spectrum of the unibranch normalization `A'` of `A` with multiplicity
`[κ(m') : κ]_s`. -/
@[stacks 0C37]
theorem geometricBranchNumber_eq_encard_weighted_maximalSpectrum_unibranchNormalization
    (hfinite : (minimalPrimes A).Finite) :
    geometricBranchNumber A Ash =
      (Set.univ :
        Set (Σ m : MaximalSpectrum A′, Field.Emb κ m.ResidueField)).encard :=
    by
      -- Route correction: the source-faithful proof is now reduced to one named equivalence from
      -- minimal primes of `Ash` to the weighted maximal-spectrum sigma type.
      rw [geometricBranchNumber]
      simpa using
        Set.encard_congr
          (strictHenselization_minimalPrimes_equiv_weighted_maximalSpectrum_unibranchNormalization
            (A := A) (Ash := Ash) hfinite)

end StrictHenselization
