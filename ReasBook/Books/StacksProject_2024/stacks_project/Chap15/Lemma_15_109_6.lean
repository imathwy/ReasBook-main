import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_155_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_43_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_43_9
import StacksProject_2024.stacks_project.Chap15.Lemma_15_45_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_45_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_109_4

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum IsLocalRing

universe u

noncomputable section

variable {A Ah : Type u}
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A
local notation "AhCompletion" => AdicCompletion (maximalIdeal Ah) Ah
private abbrev PuncturedSpectrum (R : Type u) [CommRing R] [IsLocalRing R] :=
  { p : PrimeSpectrum R // p.asIdeal ≠ maximalIdeal R }

/-
Domain-style sampling:
- primary domain: topological connectedness of punctured prime spectra for Noetherian local rings,
  compared across henselization and maximal-ideal completion;
- sampled owner declarations:
  `PrimeSpectrum`,
  `PreconnectedSpace`,
  `henselizationCompletionComparison`,
  `exists_minimalPrime_henselization_of_completion_minimalPrime_dim_one`;
- best owner abstraction: the punctured spectrum should remain a direct subtype view on the
  canonical owner `PrimeSpectrum R`, while disconnectedness is expressed by the canonical
  topological predicate `¬ PreconnectedSpace _` rather than by a parallel wrapper notion;
- primitive data: the local Noetherian ring `A`, its chosen henselization `Ah`, and the punctured
  spectrum subtype on each local ring;
- derived API: the disconnectedness comparison between the punctured spectra of `Ah` and
  `ACompletion`.

Source/core/bridge triage:
- `source-facing`: the punctured-spectrum disconnectedness equivalence below;
- `core/canonical`: `PrimeSpectrum`, `PreconnectedSpace`, `AdicCompletion`, and `maximalIdeal`;
- `bridge/view`: the canonical henselization-to-completion comparison together with the
  algebraization descent from Lemmas `15.109.4` and `15.109.5`.
-/

-- Proof sketch: identify the completion of the henselization with the completion `ACompletion`,
-- so it suffices to compare the punctured spectra of a henselian local ring and its completion.
-- Faithful flatness of the completion map gives one implication by surjectivity on punctured
-- spectra, and the converse descends a disconnection of the punctured spectrum of `ACompletion`
-- to a disconnection of the punctured spectrum of `Ah` using the algebraization steps from
-- Lemmas `15.109.4` and `15.109.5`.
/-- Helper for Lemma 15.109.6: the maximal-ideal completion of `A` is canonically isomorphic to
the maximal-ideal completion of its henselization `Ah`. -/
lemma completion_equiv_henselization_completion :
    ACompletion ≃+* AhCompletion := by
  letI : IsNoetherianRing Ah := isNoetherianRing_henselization A Ah
  letI : Module.Flat A Ah := henselizationMap_faithfullyFlat.flat
  -- The completion-comparison theorem applies because henselization is flat with unchanged
  -- residue field and maximal ideal.
  exact RingEquiv.ofBijective (maximalIdealCompletionMap (algebraMap A Ah))
    (maximalIdealCompletionMap_bijective_of_flat_of_residueFieldBijective
      (A := A) (B := Ah)
      IsHenselizationOf.map_maximalIdeal
      IsHenselizationOf.residueField_bijective)

/-- Helper for Lemma 15.109.6: under the completion comparison homeomorphism, the punctured
prime-spectra predicates match exactly. -/
lemma puncturedSpectrum_completion_homeomorph_henselizationCompletion_predicate
    (p : PrimeSpectrum ACompletion) :
    p.asIdeal ≠ maximalIdeal ACompletion ↔
      (PrimeSpectrum.homeomorphOfRingEquiv
        (completion_equiv_henselization_completion (A := A) (Ah := Ah)) p).asIdeal ≠
          maximalIdeal AhCompletion := by
  let h : PrimeSpectrum ACompletion ≃ₜ PrimeSpectrum AhCompletion :=
    PrimeSpectrum.homeomorphOfRingEquiv
      (completion_equiv_henselization_completion (A := A) (Ah := Ah))
  let pA : PrimeSpectrum ACompletion := ⟨maximalIdeal ACompletion, inferInstance⟩
  let pAh : PrimeSpectrum AhCompletion := ⟨maximalIdeal AhCompletion, inferInstance⟩
  have hpA : h pA = pAh := by
    -- The completion comparison sends the maximal ideal to the maximal ideal.
    apply Subtype.ext
    exact IsLocalRing.eq_maximalIdeal inferInstance
  have hpAh : h.symm pAh = pA := by
    -- The inverse comparison does the same in the opposite direction.
    apply Subtype.ext
    exact IsLocalRing.eq_maximalIdeal inferInstance
  constructor
  · intro hp hh
    -- If `h p` were the closed point, applying the inverse homeomorphism would force `p` to be
    -- the closed point as well.
    have hh' : h p = pAh := by
      apply Subtype.ext
      simpa [pAh] using hh
    have hp' : p = pA := by
      simpa [pA, hpAh] using congrArg h.symm hh'
    exact hp (by simpa [pA] using congrArg PrimeSpectrum.asIdeal hp')
  · intro hp hh
    -- The same argument with `h⁻¹` proves the converse implication.
    have hh' : p = pA := by
      apply Subtype.ext
      simpa [pA] using hh
    have hp' : h p = pAh := by
      simpa [pAh, hpA] using congrArg h hh'
    exact hp (by simpa [pAh] using congrArg PrimeSpectrum.asIdeal hp')

/-- Helper for Lemma 15.109.6: the completion comparison induces a homeomorphism on punctured
spectra. -/
noncomputable abbrev puncturedSpectrum_completion_homeomorph_henselizationCompletion :
    PuncturedSpectrum ACompletion ≃ₜ PuncturedSpectrum AhCompletion :=
  (PrimeSpectrum.homeomorphOfRingEquiv
      (completion_equiv_henselization_completion (A := A) (Ah := Ah))).subtype
    (puncturedSpectrum_completion_homeomorph_henselizationCompletion_predicate
      (A := A) (Ah := Ah))

/-- Helper for Lemma 15.109.6: a homeomorphism preserves failure of preconnectedness. -/
lemma not_preconnected_iff_of_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) :
    ¬ PreconnectedSpace X ↔ ¬ PreconnectedSpace Y := by
  constructor
  · intro hX hY
    -- A surjective continuous image of a preconnected space is preconnected.
    letI : PreconnectedSpace Y := hY
    have hDense : DenseRange h.symm := h.symm.surjective.denseRange
    exact hX (hDense.preconnectedSpace h.symm.continuous_toFun)
  · intro hY hX
    -- Apply the same argument to the inverse homeomorphism.
    letI : PreconnectedSpace X := hX
    have hDense : DenseRange h := h.surjective.denseRange
    exact hY (hDense.preconnectedSpace h.continuous_toFun)

section CompletionEasyDirection

variable {R : Type u}
variable [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

local notation "RCompletion" => AdicCompletion (maximalIdeal R) R

/-- Helper for Lemma 15.109.6: contraction along the completion map sends a punctured prime of
`R^∧` to a punctured prime of `R`. -/
lemma puncturedSpectrum_completion_comap_mem
    (q : PuncturedSpectrum RCompletion) :
    (PrimeSpectrum.comap (algebraMap R RCompletion) q.1).asIdeal ≠ maximalIdeal R := by
  intro hq
  have hmap :
      Ideal.map (algebraMap R RCompletion) (maximalIdeal R) = maximalIdeal RCompletion :=
    completion_map_maximalIdeal_eq_maximalIdeal (A := R)
  have hle : maximalIdeal RCompletion ≤ q.1.asIdeal := by
    -- Mapping the contracted equality forward forces the closed point upstairs into `q`.
    calc
      maximalIdeal RCompletion =
          Ideal.map (algebraMap R RCompletion) (maximalIdeal R) := hmap.symm
      _ ≤ q.1.asIdeal := Ideal.map_le_iff_le_comap.mpr (by simpa [hq])
  have hq' : q.1.asIdeal = maximalIdeal RCompletion := by
    -- In a local ring every prime is below the maximal ideal, so the reverse inclusion is enough.
    exact le_antisymm (le_maximalIdeal_of_isPrime q.1.asIdeal) hle
  exact q.2 hq'

/-- Helper for Lemma 15.109.6: restrict the prime-spectrum comap of the completion map to the
punctured spectra. -/
noncomputable abbrev puncturedSpectrum_completion_comap :
    PuncturedSpectrum RCompletion → PuncturedSpectrum R := fun q ↦
  ⟨PrimeSpectrum.comap (algebraMap R RCompletion) q.1,
    puncturedSpectrum_completion_comap_mem (R := R) q⟩

/-- Helper for Lemma 15.109.6: the restricted punctured-spectrum comap for the completion map is
continuous. -/
lemma continuous_puncturedSpectrum_completion_comap :
    Continuous (puncturedSpectrum_completion_comap (R := R)) := by
  -- The subtype map is just the usual continuous prime-spectrum contraction.
  refine continuous_subtype_mk ?_
  exact (PrimeSpectrum.continuous_comap (algebraMap R RCompletion)).comp continuous_subtype_val

/-- Helper for Lemma 15.109.6: faithful flatness of the completion map yields surjectivity on the
punctured spectra. -/
lemma puncturedSpectrum_completion_comap_surjective :
    Function.Surjective (puncturedSpectrum_completion_comap (R := R)) := by
  intro p
  obtain ⟨q, hq⟩ :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := RCompletion) p.1
  refine ⟨⟨q, ?_⟩, ?_⟩
  · intro hqmax
    -- If the chosen lift were the closed point upstairs, its contraction would be the closed
    -- point downstairs, contradicting that `p` lies in the punctured spectrum.
    have hpmax : p.1.asIdeal = maximalIdeal R := by
      simpa [hqmax] using congrArg PrimeSpectrum.asIdeal hq
    exact p.2 hpmax
  · -- Equality on the underlying prime ideals proves equality in the punctured subtype.
    apply Subtype.ext
    exact hq

/-- Helper for Lemma 15.109.6: if the punctured spectrum of a Noetherian local ring is
disconnected, then so is the punctured spectrum of its completion. -/
lemma not_preconnected_puncturedSpectrum_completion_of_not_preconnected :
    ¬ PreconnectedSpace (PuncturedSpectrum R) →
      ¬ PreconnectedSpace (PuncturedSpectrum RCompletion) := by
  intro hR hCompletion
  letI : PreconnectedSpace (PuncturedSpectrum RCompletion) := hCompletion
  have hsurj :
      Function.Surjective (puncturedSpectrum_completion_comap (R := R)) :=
    puncturedSpectrum_completion_comap_surjective (R := R)
  have hDense :
      DenseRange (puncturedSpectrum_completion_comap (R := R)) :=
    hsurj.denseRange
  -- Route correction: use the punctured-spectrum contraction map, not a map on the full prime
  -- spectra, so the image lands in the punctured space without extra bookkeeping.
  exact hR
    (hDense.preconnectedSpace (continuous_puncturedSpectrum_completion_comap (R := R)))

end CompletionEasyDirection

/-- Helper for Lemma 15.109.6: failure of preconnectedness on the punctured spectrum produces a
nontrivial disjoint closed cover of that punctured spectrum. This is the topological starting point
of the source proof before taking closures in the ambient prime spectrum. -/
lemma exists_disjoint_closed_cover_of_not_preconnected_puncturedSpectrum
    {R : Type u} [CommRing R] [IsLocalRing R]
    (h : ¬ PreconnectedSpace (PuncturedSpectrum R)) :
    ∃ Z Z' : Set (PuncturedSpectrum R),
      IsClosed Z ∧
      IsClosed Z' ∧
      Disjoint Z Z' ∧
      (Set.univ : Set (PuncturedSpectrum R)) ⊆ Z ∪ Z' ∧
      Z.Nonempty ∧
      Z'.Nonempty := by
  have hnot_univ : ¬ IsPreconnected (Set.univ : Set (PuncturedSpectrum R)) := by
    -- Rewrite the space-level failure of preconnectedness on the underlying universal subset.
    intro huniv
    exact h ⟨huniv⟩
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed isClosed_univ] at hnot_univ
  push_neg at hnot_univ
  rcases hnot_univ with ⟨Z, Z', hZ_closed, hZ'_closed, hcover, hdisjoint, hZ_not_univ,
    hZ'_not_univ⟩
  have hZ_nonempty : Z.Nonempty := by
    -- If `Z` were empty, the cover would force the entire punctured spectrum into `Z'`.
    by_contra hZ_nonempty
    have hZ'_univ : (Set.univ : Set (PuncturedSpectrum R)) ⊆ Z' := by
      intro x hx
      rcases hcover hx with hxZ | hxZ'
      · exact False.elim (hZ_nonempty ⟨x, hxZ⟩)
      · exact hxZ'
    exact hZ'_not_univ hZ'_univ
  have hZ'_nonempty : Z'.Nonempty := by
    -- The symmetric argument shows that `Z'` cannot be empty either.
    by_contra hZ'_nonempty
    have hZ_univ : (Set.univ : Set (PuncturedSpectrum R)) ⊆ Z := by
      intro x hx
      rcases hcover hx with hxZ | hxZ'
      · exact hxZ
      · exact False.elim (hZ'_nonempty ⟨x, hxZ'⟩)
    exact hZ_not_univ hZ_univ
  exact ⟨Z, Z', hZ_closed, hZ'_closed, hdisjoint, hcover, hZ_nonempty, hZ'_nonempty⟩

/-- Helper for Lemma 15.109.6: separating ideals on a local ring give a disconnection of the
punctured spectrum. -/
lemma not_preconnected_puncturedSpectrum_of_separating_ideals
    {R : Type u} [CommRing R] [IsLocalRing R]
    (I I' : Ideal R)
    (hradical : Ideal.radical (I + I') = maximalIdeal R)
    (hmul : I * I' = ⊥)
    (hI : ∃ p : PuncturedSpectrum R, I ≤ p.1.asIdeal)
    (hI' : ∃ p : PuncturedSpectrum R, I' ≤ p.1.asIdeal) :
    ¬ PreconnectedSpace (PuncturedSpectrum R) := by
  let Z : Set (PuncturedSpectrum R) := Subtype.val ⁻¹' PrimeSpectrum.zeroLocus (I : Set R)
  let Z' : Set (PuncturedSpectrum R) := Subtype.val ⁻¹' PrimeSpectrum.zeroLocus (I' : Set R)
  intro hpre
  letI : PreconnectedSpace (PuncturedSpectrum R) := hpre
  have hZ_closed : IsClosed Z := by
    -- The first component is the pullback of the ambient closed set `V(I)`.
    dsimp [Z]
    exact (PrimeSpectrum.isClosed_zeroLocus (I : Set R)).preimage continuous_subtype_val
  have hZ'_closed : IsClosed Z' := by
    -- The second component is the pullback of the ambient closed set `V(I')`.
    dsimp [Z']
    exact (PrimeSpectrum.isClosed_zeroLocus (I' : Set R)).preimage continuous_subtype_val
  have hZZ'_disjoint : Disjoint Z Z' := by
    -- A punctured prime containing both ideals would also contain the closed point.
    rw [Set.disjoint_left]
    intro p hp hp'
    have hIp : I ≤ p.1.asIdeal := by
      exact (PrimeSpectrum.mem_zeroLocus p.1 (I : Set R)).1 hp
    have hI'p : I' ≤ p.1.asIdeal := by
      exact (PrimeSpectrum.mem_zeroLocus p.1 (I' : Set R)).1 hp'
    have hsum : I + I' ≤ p.1.asIdeal := Ideal.add_le.mpr ⟨hIp, hI'p⟩
    have hmax_le : maximalIdeal R ≤ p.1.asIdeal := by
      rw [← hradical]
      exact Ideal.radical_mono hsum
    have hpmax : p.1.asIdeal = maximalIdeal R := by
      exact le_antisymm (le_maximalIdeal_of_isPrime p.1.asIdeal) hmax_le
    exact p.2 hpmax
  have hZZ' := Set.disjoint_left.mp hZZ'_disjoint
  have hcover : (Set.univ : Set (PuncturedSpectrum R)) ⊆ Z ∪ Z' := by
    intro p hp
    by_cases hIp : I ≤ p.1.asIdeal
    · -- Any punctured prime containing `I` belongs to the first closed piece.
      left
      exact (PrimeSpectrum.mem_zeroLocus p.1 (I : Set R)).2 hIp
    · -- Otherwise choose witnesses outside `p`; primality forces `I' ⊆ p`.
      right
      have hI'p : I' ≤ p.1.asIdeal := by
        by_contra hI'p
        rcases SetLike.not_le_iff_exists.mp hIp with ⟨a, haI, ha_not_mem⟩
        rcases SetLike.not_le_iff_exists.mp hI'p with ⟨b, hbI', hb_not_mem⟩
        have hab_mul : a * b ∈ I * I' := Ideal.mul_mem_mul haI hbI'
        have hmul_le : I * I' ≤ p.1.asIdeal := by
          simpa [hmul] using (bot_le : (⊥ : Ideal R) ≤ p.1.asIdeal)
        have hab_mem : a * b ∈ p.1.asIdeal := hmul_le hab_mul
        have hab_or : a ∈ p.1.asIdeal ∨ b ∈ p.1.asIdeal := by
          exact Ideal.IsPrime.mem_or_mem inferInstance hab_mem
        rcases hab_or with ha_mem | hb_mem
        · exact ha_not_mem ha_mem
        · exact hb_not_mem hb_mem
      exact (PrimeSpectrum.mem_zeroLocus p.1 (I' : Set R)).2 hI'p
  have hpreconnected_univ : IsPreconnected (Set.univ : Set (PuncturedSpectrum R)) := by
    -- A preconnected space has preconnected underlying set.
    simpa using (isPreconnected_univ : IsPreconnected (Set.univ : Set (PuncturedSpectrum R)))
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed isClosed_univ] at hpreconnected_univ
  have huniv_subset : (Set.univ : Set (PuncturedSpectrum R)) ⊆ Z ∪ Z' := hcover
  have hchoice :
      (Set.univ : Set (PuncturedSpectrum R)) ⊆ Z ∨
        (Set.univ : Set (PuncturedSpectrum R)) ⊆ Z' :=
    hpreconnected_univ Z Z' hZ_closed hZ'_closed huniv_subset hZZ'_disjoint
  rcases hchoice with hchoice | hchoice
  · obtain ⟨p, hpI'⟩ := hI'
    have hpZ : p ∈ Z := hchoice (by simp)
    have hpZ' : p ∈ Z' := by
      exact (PrimeSpectrum.mem_zeroLocus p.1 (I' : Set R)).2 hpI'
    exact hZZ' p hpZ hpZ'
  · obtain ⟨p, hpI⟩ := hI
    have hpZ : p ∈ Z := by
      exact (PrimeSpectrum.mem_zeroLocus p.1 (I : Set R)).2 hpI
    have hpZ' : p ∈ Z' := hchoice (by simp)
    exact hZZ' p hpZ hpZ'

/-- Helper for Lemma 15.109.6: if `K K' = 0`, then every element of `K + K'` kills the cotangent
module `K / K²`. -/
lemma separating_sum_le_annihilator_cotangent
    {R : Type u} [CommRing R] (K K' : Ideal R) (hmul : K * K' = ⊥) :
    K + K' ≤ Module.annihilator R K.Cotangent := by
  intro x hx
  rw [Ideal.mem_add] at hx
  rcases hx with ⟨a, haK, b, hbK', rfl⟩
  rw [Module.mem_annihilator]
  intro z
  obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective K z
  have ha_zero :
      Ideal.toCotangent K (((a : R) • y : K)) = 0 := by
    -- The `K`-part lands in `K²`, so its cotangent class vanishes tautologically.
    have ha_sq : ((((a : R) • y : K) : R)) ∈ K ^ 2 := by
      change a * (y : R) ∈ K ^ 2
      simpa [pow_two] using Ideal.mul_mem_mul haK y.2
    exact (Ideal.toCotangent_eq_zero K ((a : R) • y)).2 ha_sq
  have hb_mul_zero : (b : R) * (y : R) = 0 := by
    -- The mixed term lies in `K'K = 0`, so it is literally zero in the ring.
    have hb_mem_bot : (b : R) * (y : R) ∈ (⊥ : Ideal R) := by
      have hb_mem_mul : (b : R) * (y : R) ∈ K' * K :=
        Ideal.mul_mem_mul hbK' y.2
      simpa [Ideal.mul_comm, hmul] using hb_mem_mul
    simpa using hb_mem_bot
  have hb_zero :
      Ideal.toCotangent K (((b : R) • y : K)) = 0 := by
    -- The `K'`-part is already zero in `K`, hence also zero modulo `K²`.
    have hb_sq : ((((b : R) • y : K) : R)) ∈ K ^ 2 := by
      change (b : R) * (y : R) ∈ K ^ 2
      rw [hb_mul_zero]
      exact (K ^ 2).zero_mem
    exact (Ideal.toCotangent_eq_zero K ((b : R) • y)).2 hb_sq
  -- Expand the scalar action by a sum and kill both pieces separately.
  change Ideal.toCotangent K ((((a : R) + b) • y : K)) = 0
  rw [add_smul, map_add, ha_zero, hb_zero]

/-- Helper for Lemma 15.109.6: the source separator relation
`maximalIdeal^c ≤ K + K'` together with `KK' = 0` yields the cotangent-annihilator hypothesis
needed for algebraizing `R^∧ / K`. -/
lemma completion_separator_closed_point_power_le_annihilator_cotangent
    {R : Type u} [CommRing R] [IsLocalRing R]
    {c : ℕ} {K K' : Ideal R}
    (hc : maximalIdeal R ^ c ≤ K + K')
    (hmul : K * K' = ⊥) :
    maximalIdeal R ^ c ≤ Module.annihilator R K.Cotangent := by
  -- Route correction: isolate the cotangent-annihilator bridge before the henselian descent, so
  -- the remaining blocker is only the single-ideal algebraization package.
  exact hc.trans (separating_sum_le_annihilator_cotangent K K' hmul)

/-- Helper for Lemma 15.109.6: the same cotangent-annihilator bridge holds after swapping the two
separating ideals. -/
lemma completion_separator_closed_point_power_le_annihilator_cotangent_symm
    {R : Type u} [CommRing R] [IsLocalRing R]
    {c : ℕ} {K K' : Ideal R}
    (hc : maximalIdeal R ^ c ≤ K + K')
    (hmul : K * K' = ⊥) :
    maximalIdeal R ^ c ≤ Module.annihilator R K'.Cotangent := by
  -- The symmetric statement is the same argument with `K` and `K'` exchanged.
  have hswap : K' * K = ⊥ := by
    simpa [Ideal.mul_comm] using hmul
  have hsum : maximalIdeal R ^ c ≤ K' + K := by
    simpa [Ideal.add_comm] using hc
  exact
    completion_separator_closed_point_power_le_annihilator_cotangent
      (R := R) (K := K') (K' := K) hsum hswap

section CompletionAlgebraization

variable {R : Type u}
variable [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

local notation "RCompletion" => AdicCompletion (maximalIdeal R) R

/-- Helper for Lemma 15.109.6: Lemma `15.109.4` algebraizes a quotient `R^∧ / K` as soon as a
power of the closed point of `R^∧` annihilates the cotangent module `K / K²`. -/
lemma exists_finiteType_algebra_with_completion_quotient_of_completion_ideal
    (K : Ideal RCompletion) (c : ℕ)
    (hK :
      maximalIdeal RCompletion ^ c ≤
        Module.annihilator RCompletion K.Cotangent) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra.FiniteType R C),
      Nonempty
        (AdicCompletion (Ideal.map (algebraMap R C) (maximalIdeal R)) C ≃ₐ[R]
          RCompletion ⧸ K) := by
  have hmap_pow :
      Ideal.map (algebraMap R RCompletion) (maximalIdeal R ^ c) =
        maximalIdeal RCompletion ^ c := by
    -- Rewrite the extended closed-point power in the completion using the canonical map of
    -- maximal ideals.
    rw [Ideal.map_pow, completion_map_maximalIdeal_eq_maximalIdeal (A := R)]
  have hker :
      Ideal.map (algebraMap R RCompletion) (maximalIdeal R ^ c) ≤
        Module.annihilator RCompletion
          (RingHom.ker (Ideal.Quotient.mkₐ R K)).Cotangent := by
    -- The kernel of the quotient map is exactly `K`, so the annihilator hypothesis is unchanged.
    simpa [hmap_pow, Ideal.Quotient.mkₐ_eq_mk RCompletion K, Ideal.mk_ker] using hK
  -- This is exactly the single-ideal algebraization step from the source proof.
  simpa [RCompletion] using
    exists_finiteType_algebra_with_completion_algEquiv_of_kernelCotangent_annihilated
      (A := R) (B := R) (C := RCompletion ⧸ K) (I := maximalIdeal R)
      (φ := Ideal.Quotient.mkₐ R K) (hφ := Ideal.Quotient.mkₐ_surjective R K) c hker

/-- Helper for Lemma 15.109.6: a separating pair `K, K'` in the completion algebraizes the
quotient by `K`. This packages the `15.109.4` application after the cotangent-annihilator bridge.
-/
lemma exists_finiteType_algebra_with_completion_quotient_of_separator
    {c : ℕ} {K K' : Ideal RCompletion}
    (hc : maximalIdeal RCompletion ^ c ≤ K + K')
    (hmul : K * K' = ⊥) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra.FiniteType R C),
      Nonempty
        (AdicCompletion (Ideal.map (algebraMap R C) (maximalIdeal R)) C ≃ₐ[R]
          RCompletion ⧸ K) := by
  -- First convert the separator relation into the cotangent-annihilator hypothesis for `K`.
  exact
    exists_finiteType_algebra_with_completion_quotient_of_completion_ideal
      (R := R) K c
      (completion_separator_closed_point_power_le_annihilator_cotangent
        (R := RCompletion) (K := K) (K' := K') hc hmul)

/-- Helper for Lemma 15.109.6: the same separator data algebraizes the quotient by `K'`. -/
lemma exists_finiteType_algebra_with_completion_quotient_of_separator_symm
    {c : ℕ} {K K' : Ideal RCompletion}
    (hc : maximalIdeal RCompletion ^ c ≤ K + K')
    (hmul : K * K' = ⊥) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra.FiniteType R C),
      Nonempty
        (AdicCompletion (Ideal.map (algebraMap R C) (maximalIdeal R)) C ≃ₐ[R]
          RCompletion ⧸ K') := by
  -- Apply the same bridge after swapping the two separating ideals.
  exact
    exists_finiteType_algebra_with_completion_quotient_of_completion_ideal
      (R := R) K' c
      (completion_separator_closed_point_power_le_annihilator_cotangent_symm
        (R := RCompletion) (K := K) (K' := K') hc hmul)

end CompletionAlgebraization

section CompletionSeparators

variable {R : Type u}
variable [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

local notation "RCompletion" => AdicCompletion (maximalIdeal R) R

/-- Helper for Lemma 15.109.6: a disconnected punctured spectrum of the completion yields powered
separating ideals in the completion together with punctured primes containing them. -/
lemma exists_completion_powered_separators_of_not_preconnected_puncturedSpectrum
    (h : ¬ PreconnectedSpace (PuncturedSpectrum RCompletion)) :
    ∃ (c : ℕ) (K K' : Ideal RCompletion) (q q' : PuncturedSpectrum RCompletion),
      0 < c ∧
      maximalIdeal RCompletion ^ c ≤ K + K' ∧
      K * K' = ⊥ ∧
      K ≤ q.1.asIdeal ∧
      K' ≤ q'.1.asIdeal := by
  obtain ⟨Z, Z', hZ_closed, hZ'_closed, hZZ'_disjoint, hcover, hZ_nonempty, hZ'_nonempty⟩ :=
    exists_disjoint_closed_cover_of_not_preconnected_puncturedSpectrum (R := RCompletion) h
  have hZ_closed' : IsClosed Z := hZ_closed
  rw [isClosed_induced_iff] at hZ_closed'
  obtain ⟨TZ, hTZ_closed, hTZ⟩ := hZ_closed'
  have hZ'_closed' : IsClosed Z' := hZ'_closed
  rw [isClosed_induced_iff] at hZ'_closed'
  obtain ⟨TZ', hTZ'_closed, hTZ'⟩ := hZ'_closed'
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal TZ).mp hTZ_closed
  obtain ⟨J', hJ'⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal TZ').mp hTZ'_closed
  have hZ_eq : Z = Subtype.val ⁻¹' PrimeSpectrum.zeroLocus (J : Set RCompletion) := by
    simpa [hJ] using hTZ.symm
  have hZ'_eq : Z' = Subtype.val ⁻¹' PrimeSpectrum.zeroLocus (J' : Set RCompletion) := by
    simpa [hJ'] using hTZ'.symm
  obtain ⟨q, hqZ⟩ := hZ_nonempty
  obtain ⟨q', hq'Z'⟩ := hZ'_nonempty
  have hqJ_mem : q.1 ∈ PrimeSpectrum.zeroLocus (J : Set RCompletion) := by
    simpa [hZ_eq] using hqZ
  have hq'J'_mem : q'.1 ∈ PrimeSpectrum.zeroLocus (J' : Set RCompletion) := by
    simpa [hZ'_eq] using hq'Z'
  have hqJ : J ≤ q.1.asIdeal :=
    (PrimeSpectrum.mem_zeroLocus q.1 (J : Set RCompletion)).1 hqJ_mem
  have hq'J' : J' ≤ q'.1.asIdeal :=
    (PrimeSpectrum.mem_zeroLocus q'.1 (J' : Set RCompletion)).1 hq'J'_mem
  have hclosedPoint_mem_J :
      PrimeSpectrum.closedPoint RCompletion ∈ PrimeSpectrum.zeroLocus (J : Set RCompletion) := by
    -- The closed point lies in the closure of every nonempty specialization-closed piece.
    exact
      (PrimeSpectrum.specializes_closedPoint q.1).mem_closed
        (PrimeSpectrum.isClosed_zeroLocus (J : Set RCompletion)) hqJ_mem
  have hclosedPoint_mem_J' :
      PrimeSpectrum.closedPoint RCompletion ∈ PrimeSpectrum.zeroLocus (J' : Set RCompletion) := by
    -- The same specialization argument applies to the second closed piece.
    exact
      (PrimeSpectrum.specializes_closedPoint q'.1).mem_closed
        (PrimeSpectrum.isClosed_zeroLocus (J' : Set RCompletion)) hq'J'_mem
  have hzeroLocus_sup :
      PrimeSpectrum.zeroLocus ((J + J' : Ideal RCompletion) : Set RCompletion) =
        {PrimeSpectrum.closedPoint RCompletion} := by
    -- On punctured primes the two ambient closures remain disjoint, while the closed point lies in
    -- both closures because each piece is nonempty.
    rw [PrimeSpectrum.zeroLocus_sup]
    ext p
    constructor
    · intro hp
      by_cases hpmax : p.asIdeal = maximalIdeal RCompletion
      · have hpclosed : p = PrimeSpectrum.closedPoint RCompletion := by
          apply Subtype.ext
          simpa [PrimeSpectrum.closedPoint] using hpmax
        simpa [hpclosed]
      · let pp : PuncturedSpectrum RCompletion := ⟨p, hpmax⟩
        have hpZ : pp ∈ Z := by
          simpa [hZ_eq] using hp.1
        have hpZ' : pp ∈ Z' := by
          simpa [hZ'_eq] using hp.2
        exact False.elim ((Set.disjoint_left.mp hZZ'_disjoint) pp hpZ hpZ')
    · intro hp
      rcases Set.mem_singleton_iff.mp hp with rfl
      exact ⟨hclosedPoint_mem_J, hclosedPoint_mem_J'⟩
  have hzeroLocus_mul :
      PrimeSpectrum.zeroLocus ((J * J' : Ideal RCompletion) : Set RCompletion) = Set.univ := by
    -- Every punctured prime belongs to one of the two closed pieces, and the closed point belongs
    -- to both.
    rw [PrimeSpectrum.zeroLocus_mul]
    ext p
    constructor
    · intro hp
      simp
    · intro hp
      by_cases hpmax : p.asIdeal = maximalIdeal RCompletion
      · have hpclosed : p = PrimeSpectrum.closedPoint RCompletion := by
          apply Subtype.ext
          simpa [PrimeSpectrum.closedPoint] using hpmax
        rcases hpclosed with rfl
        exact Or.inl hclosedPoint_mem_J
      · let pp : PuncturedSpectrum RCompletion := ⟨p, hpmax⟩
        have hpp : pp ∈ Z ∪ Z' := hcover (by simp)
        rcases hpp with hpp | hpp
        · exact Or.inl (by simpa [hZ_eq] using hpp)
        · exact Or.inr (by simpa [hZ'_eq] using hpp)
  have hrad :
      Ideal.radical (J + J') = maximalIdeal RCompletion := by
    -- Equality of zero loci identifies the radical of `J + J'` with the closed point ideal.
    have hzeroLocus_eq_max :
        PrimeSpectrum.zeroLocus ((J + J' : Ideal RCompletion) : Set RCompletion) =
          PrimeSpectrum.zeroLocus (maximalIdeal RCompletion : Set RCompletion) := by
      simpa [PrimeSpectrum.closedPoint] using
        hzeroLocus_sup.trans
          (PrimeSpectrum.zeroLocus_eq_singleton (maximalIdeal RCompletion)).symm
    exact (PrimeSpectrum.zeroLocus_eq_iff).mp hzeroLocus_eq_max
  obtain ⟨e, he⟩ :=
    (J + J').exists_radical_pow_le_of_fg (J + J').radical.fg_of_isNoetherianRing
  have hclosedPoint_power :
      maximalIdeal RCompletion ^ (e + 1) ≤ J + J' := by
    -- Replace the radical by the maximal ideal and take one extra power to ensure positivity.
    calc
      maximalIdeal RCompletion ^ (e + 1) =
          (Ideal.radical (J + J')) ^ (e + 1) := by rw [hrad]
      _ = (Ideal.radical (J + J')) ^ e * Ideal.radical (J + J') := by
          rw [Ideal.pow_add]
          simp
      _ ≤ (Ideal.radical (J + J')) ^ e := Ideal.mul_le_left
      _ ≤ J + J' := he
  have hnil : IsNilpotent (J * J') :=
    isNilpotent_of_zeroLocus_eq_univ_of_isNoetherian (R := RCompletion) (J * J') hzeroLocus_mul
  obtain ⟨m, hm⟩ := hnil
  let n := m + 1
  let K : Ideal RCompletion := J ^ n
  let K' : Ideal RCompletion := J' ^ n
  have hn_pos : 0 < n := by
    dsimp [n]
    exact Nat.succ_pos _
  have hnil_pow : (J * J') ^ n = ⊥ := by
    -- One more power of a nilpotent ideal is still zero.
    dsimp [n]
    calc
      (J * J') ^ (m + 1) = (J * J') ^ m * (J * J') := by
        rw [Ideal.pow_add]
        simp
      _ = ⊥ := by simp [hm]
  have hKK' : K * K' = ⊥ := by
    -- The powered separators multiply to zero because `(JJ')^n = 0`.
    calc
      K * K' = J ^ n * J' ^ n := rfl
      _ = (J * J') ^ n := by
          symm
          simpa using (mul_pow J J' n)
      _ = ⊥ := hnil_pow
  have hc :
      maximalIdeal RCompletion ^ ((e + 1) * (n + n)) ≤ K + K' := by
    -- Raise the closed-point containment to a large enough power and split it with the standard
    -- binomial ideal estimate `(J + J')^(n+n) ≤ J^n + J'^n`.
    calc
      maximalIdeal RCompletion ^ ((e + 1) * (n + n)) =
          (maximalIdeal RCompletion ^ (e + 1)) ^ (n + n) := by
            rw [pow_mul]
      _ ≤ (J + J') ^ (n + n) := by
            exact pow_le_pow_left' hclosedPoint_power _
      _ ≤ J ^ n + J' ^ n := by
            simpa [sup_eq_add] using
              (Ideal.sup_pow_add_le_pow_sup_pow (I := J) (J := J') (n := n) (m := n))
      _ = K + K' := rfl
  have hKq : K ≤ q.1.asIdeal := by
    -- Passing from `J` to `J^n` preserves containment in the chosen punctured prime.
    exact (Ideal.pow_le_self hn_pos.ne').trans hqJ
  have hK'q' : K' ≤ q'.1.asIdeal := by
    -- The symmetric containment holds for the second powered separator.
    exact (Ideal.pow_le_self hn_pos.ne').trans hq'J'
  refine ⟨(e + 1) * (n + n), K, K', q, q', ?_, hc, hKK', hKq, hK'q'⟩
  exact Nat.mul_pos (Nat.succ_pos _) (Nat.add_pos hn_pos hn_pos)

end CompletionSeparators

/-- Helper for Lemma 15.109.6: for a henselian Noetherian local ring, disconnectedness of the
punctured spectrum of the completion should descend back to the punctured spectrum of the ring.
-/
lemma not_preconnected_puncturedSpectrum_of_completion_of_henselian
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [HenselianLocalRing R] :
    ¬ PreconnectedSpace (PuncturedSpectrum (AdicCompletion (maximalIdeal R) R)) →
      ¬ PreconnectedSpace (PuncturedSpectrum R) := by
  -- Route correction: the source proof does not descend connectedness abstractly; it first turns
  -- a disconnected punctured spectrum of `R^∧` into separating closed subsets `V(J)` and `V(J')`,
  -- algebraizes `R^∧ / J^n` via Lemma `15.109.4`, and then uses henselian descent exactly as in
  -- the second half of Lemma `15.109.5`.
  intro hCompletion
  obtain ⟨c, K, K', q, q', hc_pos, hc, hmul, hKq, hK'q'⟩ :=
    exists_completion_powered_separators_of_not_preconnected_puncturedSpectrum
      (R := R) hCompletion
  obtain ⟨C, _instC, _algC, _finiteC, hC⟩ :=
    exists_finiteType_algebra_with_completion_quotient_of_separator
      (R := R) (K := K) (K' := K') hc hmul
  obtain ⟨C', _instC', _algC', _finiteC', hC'⟩ :=
    exists_finiteType_algebra_with_completion_quotient_of_separator_symm
      (R := R) (K := K) (K' := K') hc hmul
  -- TODO: descend the two algebraized completion quotients `R^∧ / K` and `R^∧ / K'` to source
  -- quotients `R / I` and `R / I'` using the henselian closed-fiber argument from the second half
  -- of Lemma `15.109.5`. Once that single-ideal descent is formalized, the containments `K ≤ q`
  -- and `K' ≤ q'` contract to punctured witnesses downstairs and `hc`, `hmul` transport to
  -- `maximalIdeal R ^ c ≤ I + I'` and `I * I' = ⊥`, closing by
  -- `not_preconnected_puncturedSpectrum_of_separating_ideals`.
  let _ := c
  let _ := hc_pos
  let _ := K
  let _ := K'
  let _ := q
  let _ := q'
  let _ := hKq
  let _ := hK'q'
  let _ := C
  let _ := C'
  let _ := hC
  let _ := hC'
  sorry

/-- Lemma 15.109.6: for a Noetherian local ring `A` and a chosen henselization `Ah` of `A`, the
punctured spectrum of the maximal-ideal completion `ACompletion = AdicCompletion (maximalIdeal A) A`
is disconnected if and only if the punctured spectrum of `Ah` is disconnected. Here
“disconnected” is formalized as failure of preconnectedness of the corresponding punctured
spectrum. -/
theorem puncturedSpectrum_completion_disconnected_iff_henselization_disconnected :
    ¬ PreconnectedSpace (PuncturedSpectrum ACompletion) ↔
      ¬ PreconnectedSpace (PuncturedSpectrum Ah) := by
  letI : IsNoetherianRing Ah := isNoetherianRing_henselization A Ah
  have hcompletion :
      ¬ PreconnectedSpace (PuncturedSpectrum ACompletion) ↔
        ¬ PreconnectedSpace (PuncturedSpectrum AhCompletion) :=
    not_preconnected_iff_of_homeomorph
      (puncturedSpectrum_completion_homeomorph_henselizationCompletion
        (A := A) (Ah := Ah))
  constructor
  · intro hACompletion
    have hAhCompletion :
        ¬ PreconnectedSpace (PuncturedSpectrum AhCompletion) :=
      hcompletion.mp hACompletion
    -- The remaining source-faithful step is the henselian descent from the completion.
    exact not_preconnected_puncturedSpectrum_of_completion_of_henselian
      (R := Ah) hAhCompletion
  · intro hAh
    have hAhCompletion :
        ¬ PreconnectedSpace (PuncturedSpectrum AhCompletion) :=
      not_preconnected_puncturedSpectrum_completion_of_not_preconnected
        (R := Ah) hAh
    -- Transport the easy-direction result back across the completion isomorphism.
    exact hcompletion.mpr hAhCompletion

end
