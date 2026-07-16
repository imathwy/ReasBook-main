import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_155_1
import stacks_proof.stacks_project.Chap15.Definition_15_41_1
import stacks_proof.stacks_project.Chap15.Lemma_15_41_7
import stacks_proof.stacks_project.Chap15.Lemma_15_43_9
import stacks_proof.stacks_project.Chap15.Lemma_15_45_1
import stacks_proof.stacks_project.Chap15.Lemma_15_50_7
import stacks_proof.stacks_project.Chap15.Lemma_15_109_2
import stacks_proof.stacks_project.Chap15.Lemma_15_109_5
import stacks_proof.stacks_project.Chap16.Theorem_16_13_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open Algebra IsLocalRing
open MvPolynomial

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

local notation "Rhat" => AdicCompletion (maximalIdeal R) R

/-- Helper for Chap16 Theorem 16 13 2: a chosen henselization has the same maximal-ideal
completion as the original local ring, viewed as an `R`-algebra equivalence. -/
private noncomputable def henselizationCompletionAlgEquiv
    (Rh : Type u) [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh] :
    AdicCompletion (maximalIdeal Rh) Rh ≃ₐ[R] Rhat := by
  -- Proof comment: compare the two maximal-ideal completions via the canonical completion
  -- comparison and then forget from `Rh`-linearity down to `R`-linearity.
  letI : IsNoetherianRing Rh := isNoetherianRing_henselization R Rh
  exact (completion_compare_algEquiv_henselization (A := R) (Ah := Rh)).symm.restrictScalars R

/-- Helper for Chap16 Theorem 16 13 2: regularity of the completion map descends from `R` to a
chosen henselization of `R`. -/
private theorem henselizationCompletion_regular
    (Rh : Type u) [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
    (hRhat : (algebraMap R Rhat).IsRegularRingMap) :
    (algebraMap Rh (AdicCompletion (maximalIdeal Rh) Rh)).IsRegularRingMap := by
  letI : IsNoetherianRing Rh := isNoetherianRing_henselization R Rh
  let e : AdicCompletion (maximalIdeal Rh) Rh ≃+* Rhat :=
    (henselizationCompletionAlgEquiv (R := R) Rh).toRingEquiv
  have hcomp :
      (e.toRingHom.comp
        (algebraMap Rh (AdicCompletion (maximalIdeal Rh) Rh))).IsRegularRingMap := by
    -- Proof comment: first transport regularity across the completion equivalence and then
    -- identify the resulting composite with the original completion map `R → Rhat`.
    have htransport :
        ((algebraMap Rhat Rhat).comp (algebraMap R Rhat)).IsRegularRingMap := by
      simpa using
        (RingHom.IsRegularRingMap.comp_of_noetherianFibers hRhat
          (ringEquiv_isRegularRingMap e)
          (by intro p; infer_instance))
    simpa [henselizationCompletionAlgEquiv, RingHom.comp_assoc] using htransport
  exact
    RingHom.IsRegularRingMap.of_comp_of_faithfullyFlat hcomp
      (henselizationMap_faithfullyFlat (R := R) (Rh := Rh))

/-- Helper for Chap16 Theorem 16 13 2: after transporting the formal point to a chosen
henselization, Theorem `16.13.1` gives an exact solution there with the required congruence. -/
private theorem exists_henselizedApproximateSolution
    (Rh : Type u) [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
    (hRhat : (algebraMap R Rhat).IsRegularRingMap)
    {m n : ℕ} (f : Fin m → MvPolynomial (Fin n) R) (a : Fin n → Rhat)
    (ha : ∀ j, aeval a (f j) = 0) (N : ℕ) :
    ∃ c : Fin n → Rh,
      (∀ j, aeval c (f j) = 0) ∧
        ∀ i,
          ((henselizationCompletionAlgEquiv (R := R) Rh).symm (a i) -
              algebraMap Rh (AdicCompletion (maximalIdeal Rh) Rh) (c i)) ∈
            Ideal.map (algebraMap Rh (AdicCompletion (maximalIdeal Rh) Rh))
              ((maximalIdeal Rh) ^ N) := by
  letI : IsNoetherianRing Rh := isNoetherianRing_henselization R Rh
  let aRhHat : Fin n → AdicCompletion (maximalIdeal Rh) Rh :=
    fun i ↦ (henselizationCompletionAlgEquiv (R := R) Rh).symm (a i)
  have haRhHat : ∀ j, aeval aRhHat (f j) = 0 := by
    intro j
    -- Proof comment: evaluation commutes with the completion comparison equivalence.
    simpa [aRhHat] using
      congrArg ((henselizationCompletionAlgEquiv (R := R) Rh).symm) (ha j)
  -- Proof comment: apply the henselian approximation theorem over the chosen henselization.
  simpa [aRhHat] using
    exists_solution_in_ring_of_adicCompletion_solution
      (R := Rh)
      (henselizationCompletion_regular (R := R) Rh hRhat) f aRhHat haRhHat N

/-- Helper for Chap16 Theorem 16 13 2: an étale `R`-algebra branch over the closed point with
unchanged residue field admits a unique map into the chosen henselization. -/
private theorem existsUnique_stageMap_to_henselization
    (Rh : Type u) [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
    {R' : Type u} [CommRing R'] [Algebra R R'] [Algebra.Etale R R']
    (m' : Ideal R') [m'.IsPrime] (hm' : m'.under R = maximalIdeal R)
    (hres : Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal R) m' (algebraMap R R') hm'.symm)) :
    ∃! σ : R' →ₐ[R] Rh,
      m' = Ideal.comap (σ : R' →+* Rh) (maximalIdeal Rh) := by
  -- Proof comment: this is exactly the source-facing henselization lifting theorem specialized to
  -- the chosen henselization target `Rh`.
  simpa using
    (existsUnique_algHom_to_henselization_of_etale_of_residueFieldMap_bijective
      (S := R) (Sh := Rh) (A := R') m' hm' hres)

/- Domain-style sampling:
- primary domain: Artin approximation over Noetherian local rings via étale neighborhoods and the
  completed local ring;
- sampled owner declarations in this domain:
  `RingHom.IsRegularRingMap`,
  `Algebra.Etale`,
  `Ideal.LiesOver`,
  `Ideal.ResidueField.mapₐ`;
- best owner abstraction: the source-facing approximation theorem should be stated directly in
  terms of these canonical owners, without a one-off wrapper predicate for the conjunction of its
  atomic output conditions;
- primitive data: the étale `R`-algebra `R'`, the maximal ideal `m'` lying over `maximalIdeal R`,
  the comparison map `φ : R' →ₐ[R] Rhat`, and the solution `b`;
- derived API: residue-field bijectivity, the exact polynomial-solution condition, and the
  congruence modulo `(m')^N`.

Source/core/bridge triage:
- `source-facing`: the existence theorem below;
- `core/canonical`: `IsRegularRingMap`, `Algebra.Etale`, `Ideal.LiesOver`, and
  `Ideal.ResidueField.mapₐ`;
- `bridge/view`: none is needed here, because the theorem already returns the canonical owner data
  directly. -/

-- Proof sketch: apply Popescu's theorem to the finitely generated `R`-subalgebra of `Rhat`
-- generated by the coordinates of the formal solution, using the geometric regularity of the
-- completion fibers to factor it through a smooth `R`-algebra. Then use the smooth lifting lemma
-- over the residue field to pass to an étale neighborhood with unchanged residue field, and lift
-- the solution there so that its image in `Rhat` agrees with the given formal solution modulo the
-- `N`-th power of the chosen maximal ideal.
/-- Theorem 16.13.2: if `R` is a Noetherian local ring whose completion map has geometrically
regular formal fibers, then every solution in `AdicCompletion (maximalIdeal R) R` of a finite
system of polynomial equations over `R` can, for each `N`, be approximated modulo the `N`-th power
of the maximal ideal by a solution in an étale `R`-algebra with the same residue field at a
maximal ideal lying over `maximalIdeal R`. -/
@[stacks 07QZ]
theorem exists_etale_solution_of_adicCompletion_solution
    (hRhat : (algebraMap R Rhat).IsRegularRingMap)
    {m n : ℕ} (f : Fin m → MvPolynomial (Fin n) R) (a : Fin n → Rhat)
    (ha : ∀ j, aeval a (f j) = 0) (N : ℕ) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (m' : Ideal R') (_ : m'.IsMaximal) (_ : m'.LiesOver (maximalIdeal R))
      (φ : R' →ₐ[R] Rhat) (b : Fin n → R'),
      Function.Bijective
        (Ideal.ResidueField.mapₐ (maximalIdeal R) m' (Algebra.ofId _ _) (m'.over_def _)) ∧
      (∀ j, aeval b (f j) = 0) ∧
      ∀ i, a i - φ (b i) ∈ Ideal.map φ.toRingHom (m' ^ N) := by
  classical
  obtain ⟨Rh, _instRhCommRing, _instRhAlg, hRh⟩ := exists_henselization R
  letI : IsNoetherianRing Rh := isNoetherianRing_henselization R Rh
  obtain ⟨c, hcsol, hcapprox⟩ :=
    exists_henselizedApproximateSolution
      (R := R) Rh hRhat f a ha N
  -- Proof comment: the proof now reduces to descending the exact henselized solution together
  -- with its congruence modulo `(maximalIdeal Rh)^N` to one finite étale stage inside the chosen
  -- henselization.
  have hstageLift :
      ∀ {R' : Type u} [CommRing R'] [Algebra R R'] [Algebra.Etale R R']
        (m' : Ideal R') [_ : m'.IsPrime]
        (hm' : m'.under R = maximalIdeal R),
        Function.Bijective
            (Ideal.ResidueField.mapₐ (maximalIdeal R) m' (Algebra.ofId _ _) hm') →
        ∃! σ : R' →ₐ[R] Rh, m' = Ideal.comap (σ : R' →+* Rh) (maximalIdeal Rh) := by
    intro R' _ _ _ _ m' _ hm' hres
    -- Proof comment: convert the `ₐ`-version of the residue-field map to the ring-hom owner
    -- expected by the henselization lifting theorem.
    simpa using
      existsUnique_stageMap_to_henselization (R := R) (Rh := Rh) m' hm'.symm hres
  -- TODO: package `c` and `hcapprox` as maps from the finitely presented quotient algebra of the
  -- polynomial system, factor both maps through a common finite étale stage using the
  -- filtered-colimit presentation `IsHenselizationOf.isFilteredColimitOfEtale`, set
  -- `m' := Ideal.comap stageMap.toRingHom (maximalIdeal Rh)`, and then transport the resulting
  -- stage congruence back along `henselizationCompletionAlgEquiv`.
  sorry

end
