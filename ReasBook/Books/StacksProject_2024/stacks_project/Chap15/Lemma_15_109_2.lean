import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_97_6
import StacksProject_2024.stacks_project.Chap15.Lemma_15_41_7
import StacksProject_2024.stacks_project.Chap15.Lemma_15_109_1.Index
import StacksProject_2024.stacks_project.Chap15.Lemma_15_45_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_45_3

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open RingPairCat

universe u

noncomputable section

section

variable {A Ah : Type u}
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A
local notation "A_pair" => pairOfIdeal (maximalIdeal A)
local notation "A_h" => henselizationRing A_pair
local notation "φ" => henselizationCompletionComparison A Ah

local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

/-- Helper for Lemma 15.109.2: regard the completion as an `Ah`-algebra through the canonical
comparison map. -/
local instance completionComparisonAlgebra : Algebra Ah ACompletion :=
  (henselizationCompletionComparison A Ah).toAlgebra

local instance (q : minimalPrimes Ah) : q.1.IsPrime :=
  Ideal.minimalPrimes_isPrime q.2

local instance (Q : minimalPrimes ACompletion) : Q.1.IsPrime :=
  Ideal.minimalPrimes_isPrime Q.2

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.109.2: a local `A`-algebra endomorphism of a chosen henselization is the
identity, by uniqueness in the henselization universal property over `A → A`. -/
lemma henselization_endomorphism_eq_id
    (f : Ah →ₐ[A] Ah) (hf : IsLocalHom (f : Ah →+* Ah)) :
    f = AlgHom.id A Ah := by
  -- The universal property gives a unique local `A`-algebra endomorphism of `Ah`.
  rcases
      existsUnique_algHom_between_henselizations_of_localHom
        (R := A) (S := A) (Rh := Ah) (Sh := Ah) with
    ⟨g, hg_local, hg_unique⟩
  have hid_local : IsLocalHom (((AlgHom.id A Ah : Ah →ₐ[A] Ah) : Ah →+* Ah)) := by
    simpa using (show IsLocalHom (algebraMap Ah Ah) by infer_instance)
  calc
    f = g := hg_unique f hf
    _ = AlgHom.id A Ah := (hg_unique (AlgHom.id A Ah) hid_local).symm

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.109.2: the canonical comparison maps between the chosen henselization and
the owner pair-henselization are inverse `A`-algebra maps. -/
lemma henselizationMap_comp_henselizationMap_eq_id :
    let f : Ah →ₐ[A] A_h := henselizationMap (R := A) (S := A) (Rh := Ah) (Sh := A_h)
    let g : A_h →ₐ[A] Ah := henselizationMap (R := A) (S := A) (Rh := A_h) (Sh := Ah)
    g.comp f = AlgHom.id A Ah ∧ f.comp g = AlgHom.id A A_h := by
  let _ : IsScalarTower A A Ah := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower A A A_h := IsScalarTower.of_algebraMap_eq' rfl
  let f : Ah →ₐ[A] A_h := henselizationMap (R := A) (S := A) (Rh := Ah) (Sh := A_h)
  let g : A_h →ₐ[A] Ah := henselizationMap (R := A) (S := A) (Rh := A_h) (Sh := Ah)
  have hf_local : IsLocalHom (f : Ah →+* A_h) := by
    -- The canonical comparison between henselizations is local.
    simpa [f] using
      (henselizationMap_isLocalHom (R := A) (S := A) (Rh := Ah) (Sh := A_h) :
        IsLocalHom ((henselizationMap (R := A) (S := A) (Rh := Ah) (Sh := A_h) :
          Ah →ₐ[A] A_h).toRingHom))
  have hg_local : IsLocalHom (g : A_h →+* Ah) := by
    -- The reverse canonical comparison is local for the same reason.
    simpa [g] using
      (henselizationMap_isLocalHom (R := A) (S := A) (Rh := A_h) (Sh := Ah) :
        IsLocalHom ((henselizationMap (R := A) (S := A) (Rh := A_h) (Sh := Ah) :
          A_h →ₐ[A] Ah).toRingHom))
  have hgf_local : IsLocalHom ((g.comp f : Ah →ₐ[A] Ah).toRingHom) := by
    -- Both canonical comparison maps are local, so their composite is again local.
    let _ : IsLocalHom (f : Ah →+* A_h) := hf_local
    let _ : IsLocalHom (g : A_h →+* Ah) := hg_local
    simpa [f, g] using
      (RingHom.isLocalHom_comp (g : A_h →+* Ah) (f : Ah →+* A_h) :
        IsLocalHom ((g : A_h →+* Ah).comp (f : Ah →+* A_h)))
  have hfg_local : IsLocalHom ((f.comp g : A_h →ₐ[A] A_h).toRingHom) := by
    -- The same argument applies in the opposite direction.
    let _ : IsLocalHom (f : Ah →+* A_h) := hf_local
    let _ : IsLocalHom (g : A_h →+* Ah) := hg_local
    simpa [f, g] using
      (RingHom.isLocalHom_comp (f : Ah →+* A_h) (g : A_h →+* Ah) :
        IsLocalHom ((f : Ah →+* A_h).comp (g : A_h →+* Ah)))
  have hgf : g.comp f = AlgHom.id A Ah :=
    henselization_endomorphism_eq_id (A := A) (Ah := Ah) (f := g.comp f) hgf_local
  have hfg : f.comp g = AlgHom.id A A_h :=
    henselization_endomorphism_eq_id (A := A) (Ah := A_h) (f := f.comp g) hfg_local
  exact ⟨hgf, hfg⟩

/-- Helper for Lemma 15.109.2: the chosen henselization is canonically equivalent to the owner
pair-henselization, and the completion comparison factors through the owner map. -/
lemma chosen_henselization_equiv_pair_henselization :
    ∃ e : Ah ≃ₐ[A] A_h,
        henselizationCompletionComparison A Ah =
        (RingPairCat.henselizationToAdicCompletion A_pair).comp e.toRingHom := by
  let _ : IsScalarTower A A Ah := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower A A A_h := IsScalarTower.of_algebraMap_eq' rfl
  let f : Ah →ₐ[A] A_h := henselizationMap (R := A) (S := A) (Rh := Ah) (Sh := A_h)
  let g : A_h →ₐ[A] Ah := henselizationMap (R := A) (S := A) (Rh := A_h) (Sh := Ah)
  have hcomp : g.comp f = AlgHom.id A Ah ∧ f.comp g = AlgHom.id A A_h := by
    -- First stabilize the chosen-vs-owner transport at the level of explicit inverse maps.
    simpa [f, g] using henselizationMap_comp_henselizationMap_eq_id (A := A) (Ah := Ah)
  have hgf_apply : ∀ x : Ah, g (f x) = x := by
    -- The composite `g ∘ f` is already the identity on the chosen henselization.
    intro x
    exact DFunLike.congr_fun hcomp.1 x
  have hfg_apply : ∀ y : A_h, f (g y) = y := by
    -- The composite `f ∘ g` is the identity on the owner henselization.
    intro y
    exact DFunLike.congr_fun hcomp.2 y
  have hf_injective : Function.Injective f := by
    -- A left inverse immediately makes the chosen-to-owner map injective.
    intro x y hxy
    calc
      x = g (f x) := by symm; exact hgf_apply x
      _ = g (f y) := by rw [hxy]
      _ = y := hgf_apply y
  have hf_surjective : Function.Surjective f := by
    -- A right inverse provides a canonical preimage of every owner point.
    intro y
    refine ⟨g y, ?_⟩
    exact hfg_apply y
  let e : Ah ≃ₐ[A] A_h := AlgEquiv.ofBijective f ⟨hf_injective, hf_surjective⟩
  refine ⟨e, ?_⟩
  -- With the explicit equivalence in hand, the completion comparison is the owner map composed
  -- with the same canonical henselization comparison map used to define `e`.
  ext x
  rfl

/-- Helper for Lemma 15.109.2: the comparison map from the chosen henselization to the completion
is flat. -/
lemma henselizationCompletionComparison_flat :
    (henselizationCompletionComparison A Ah).Flat := by
  -- Route correction: first transport the owner flatness statement along the explicit
  -- chosen-to-owner henselization equivalence from the previous lemma; only then rewrite back to
  -- the chosen algebra-map view.
  rcases chosen_henselization_equiv_pair_henselization (A := A) (Ah := Ah) with ⟨e, he⟩
  have howner :
      (RingPairCat.henselizationToAdicCompletion A_pair).Flat := by
    simpa using RingPairCat.henselizationToAdicCompletion_flat A_pair
  have heFlat : e.toRingHom.Flat := RingHom.Flat.of_bijective e.bijective
  have hcomp :
      ((RingPairCat.henselizationToAdicCompletion A_pair).comp e.toRingHom).Flat :=
    RingHom.Flat.comp heFlat howner
  -- Rewrite the composite back to the chosen algebra-map description of the comparison.
  exact he.symm ▸ hcomp

/-- Helper for Lemma 15.109.2: contracting a completion minimal prime along the comparison map
again yields a henselization minimal prime. -/
lemma comap_mem_minimalPrimes_of_completion_minimalPrime
    (Q : minimalPrimes ACompletion) :
    Ideal.comap (algebraMap Ah ACompletion) Q ∈ minimalPrimes Ah := by
  have hflat : (algebraMap Ah ACompletion).Flat := by
    simpa [completionComparisonAlgebra, RingHom.algebraMap_toAlgebra] using
      (henselizationCompletionComparison_flat (A := A) (Ah := Ah))
  let _ : Module.Flat Ah ACompletion := RingHom.flat_algebraMap_iff.mp hflat
  refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
  intro J hJ hJ_le
  by_cases hq : Ideal.comap (algebraMap Ah ACompletion) Q = J
  · exact hq.le
  · letI : Algebra.HasGoingDown Ah ACompletion := Algebra.HasGoingDown.of_flat
    letI : J.IsPrime := hJ.1
    letI : Q.1.LiesOver (Ideal.comap (algebraMap Ah ACompletion) Q.1) := ⟨rfl⟩
    have hJ_lt_Q :
        J < Ideal.comap (algebraMap Ah ACompletion) Q.1 :=
      lt_of_le_of_ne hJ_le (Ne.symm hq)
    -- Going down produces a smaller prime below `Q`, contradicting minimality of `Q` over `(0)`.
    obtain ⟨Q', hQ'_lt, hQ'_prime, _⟩ :=
      Ideal.exists_ideal_lt_liesOver_of_lt
        (R := Ah) (S := ACompletion) (Q := Q.1) hJ_lt_Q
    have hQ_le_Q' : Q.1 ≤ Q' :=
      Q.2.2 ⟨hQ'_prime, bot_le⟩ hQ'_lt.le
    exact (hQ'_lt.not_ge hQ_le_Q').elim

/-- Helper for Lemma 15.109.2: a completion branch lying over `q` is minimal over the extended
ideal `qACompletion`. -/
lemma completion_minimalPrime_mem_mapped_ideal_minimalPrimes
    (q : minimalPrimes Ah) {Q : minimalPrimes ACompletion}
    (hQq : Ideal.comap (algebraMap Ah ACompletion) Q = q) :
    Q.1 ∈ (Ideal.map (algebraMap Ah ACompletion) q).minimalPrimes := by
  -- A ring minimal prime remains minimal after enlarging the defining ideal to `qACompletion`.
  refine ⟨⟨inferInstance, Ideal.map_le_iff_le_comap.mpr <| by simpa [hQq]⟩, ?_⟩
  · intro J hJ hJQ
    exact Q.2.2 ⟨hJ.1, bot_le⟩ hJQ

/-- Helper for Lemma 15.109.2: a prime minimal over `qACompletion` contracts back to `q`. -/
lemma contraction_eq_of_mem_mapped_ideal_minimalPrimes
    (q : minimalPrimes Ah) {Q : Ideal ACompletion}
    (hQ : Q ∈ (Ideal.map (algebraMap Ah ACompletion) q).minimalPrimes) :
    Ideal.comap (algebraMap Ah ACompletion) Q = q := by
  have hflat : (algebraMap Ah ACompletion).Flat := by
    simpa [completionComparisonAlgebra, RingHom.algebraMap_toAlgebra] using
      (henselizationCompletionComparison_flat (A := A) (Ah := Ah))
  let _ : Module.Flat Ah ACompletion := RingHom.flat_algebraMap_iff.mp hflat
  have hq_map_le_Q : Ideal.map (algebraMap Ah ACompletion) q ≤ Q := hQ.1.2
  have hq_le_under : q ≤ Ideal.comap (algebraMap Ah ACompletion) Q :=
    Ideal.map_le_iff_le_comap.mp hq_map_le_Q
  by_cases hunder : Ideal.comap (algebraMap Ah ACompletion) Q = q
  · exact hunder
  · letI : Algebra.HasGoingDown Ah ACompletion := Algebra.HasGoingDown.of_flat
    letI : Q.IsPrime := hQ.1.1
    letI : Q.LiesOver (Ideal.comap (algebraMap Ah ACompletion) Q) := ⟨rfl⟩
    have hq_lt_under :
        q < Ideal.comap (algebraMap Ah ACompletion) Q :=
      lt_of_le_of_ne hq_le_under (Ne.symm hunder)
    -- A strict contraction above `q` would go down to a smaller prime over `q`, contradicting
    -- minimality over the extended ideal `qACompletion`.
    obtain ⟨Q', hQ'_lt, hQ'_prime, hQ'_liesOver⟩ :=
      Ideal.exists_ideal_lt_liesOver_of_lt
        (R := Ah) (S := ACompletion) (Q := Q) hq_lt_under
    have hq_map_le_Q' : Ideal.map (algebraMap Ah ACompletion) q ≤ Q' :=
      Ideal.map_le_iff_le_comap.mpr <| by
        simpa [Ideal.under_def] using hQ'_liesOver.over.le
    have hQ_le_Q' : Q ≤ Q' :=
      hQ.2 ⟨hQ'_prime, hq_map_le_Q'⟩ hQ'_lt.le
    exact (hQ'_lt.not_ge hQ_le_Q').elim

/-- Helper for Lemma 15.109.2: a prime minimal over `qACompletion` is already a completion
minimal prime. -/
lemma completion_mem_minimalPrimes_of_mem_mapped_ideal_minimalPrimes
    (q : minimalPrimes Ah) {Q : Ideal ACompletion}
    (hQ : Q ∈ (Ideal.map (algebraMap Ah ACompletion) q).minimalPrimes) :
    Q ∈ minimalPrimes ACompletion := by
  refine ⟨⟨hQ.1.1, bot_le⟩, ?_⟩
  intro J hJ hJ_le_Q
  have hQ_comap : Ideal.comap (algebraMap Ah ACompletion) Q = q :=
    contraction_eq_of_mem_mapped_ideal_minimalPrimes (A := A) (Ah := Ah) q hQ
  have hJ_comap_le_q : Ideal.comap (algebraMap Ah ACompletion) J ≤ q := by
    exact (Ideal.comap_mono (f := algebraMap Ah ACompletion) hJ_le_Q).trans hQ_comap.le
  have hq_le_hJ_comap : q ≤ Ideal.comap (algebraMap Ah ACompletion) J := by
    -- Minimality of `q` over `(0)` forces the contracted prime back up to `q`.
    exact q.2.2 ⟨@Ideal.IsPrime.under Ah _ ACompletion _ _ J hJ.1, bot_le⟩ hJ_comap_le_q
  have hq_map_le_J : Ideal.map (algebraMap Ah ACompletion) q ≤ J :=
    Ideal.map_le_iff_le_comap.mpr hq_le_hJ_comap
  -- Minimality of `Q` over `qACompletion` now forces `Q ≤ J`.
  exact hQ.2 ⟨hJ.1, hq_map_le_J⟩ hJ_le_Q

/-- Helper for Lemma 15.109.2: the radical of `qACompletion` is prime exactly when the completion
has a unique minimal prime above `q`. -/
lemma radical_map_minimal_prime_is_prime_iff_exists_unique_completion_minimal_prime
    (q : minimalPrimes Ah) :
    (Ideal.radical (Ideal.map (algebraMap Ah ACompletion) q)).IsPrime ↔
      ∃! Q : minimalPrimes ACompletion, Ideal.comap (algebraMap Ah ACompletion) Q = q := by
  let I : Ideal ACompletion := Ideal.map (algebraMap Ah ACompletion) q
  constructor
  · intro hprime
    letI : (Ideal.radical I).IsPrime := hprime
    have hrad_mem : Ideal.radical I ∈ I.minimalPrimes := by
      refine ⟨⟨hprime, Ideal.le_radical⟩, ?_⟩
      intro J hJ hIJ
      calc
        Ideal.radical I ≤ J.radical := Ideal.radical_mono hJ.2
        _ = J := Ideal.radical_eq_iff.mpr hJ.1.isRadical
    let Q : minimalPrimes ACompletion :=
      ⟨Ideal.radical I,
        completion_mem_minimalPrimes_of_mem_mapped_ideal_minimalPrimes
          (A := A) (Ah := Ah) q hrad_mem⟩
    refine ⟨Q, ?_, ?_⟩
    · -- The unique prime minimal over `qACompletion` contracts back to `q`.
      exact contraction_eq_of_mem_mapped_ideal_minimalPrimes (A := A) (Ah := Ah) q hrad_mem
    · intro Q' hQ'
      apply Subtype.ext
      -- Every completion minimal prime above `q` is minimal over `qACompletion`, hence equals the
      -- radical once both minimality directions are compared.
      have hQ'mem : Q'.1 ∈ I.minimalPrimes :=
        completion_minimalPrime_mem_mapped_ideal_minimalPrimes (A := A) (Ah := Ah) q hQ'
      have hrad_le_Q' : Ideal.radical I ≤ Q'.1 :=
        calc
          Ideal.radical I ≤ Q'.1.radical := Ideal.radical_mono hQ'mem.1.2
          _ = Q'.1 := Ideal.radical_eq_iff.mpr (show Q'.1.IsRadical from
            (inferInstance : Q'.1.IsPrime).isRadical)
      have hQ'_le_hrad : Q'.1 ≤ Ideal.radical I :=
        hQ'mem.2 ⟨hprime, Ideal.le_radical⟩ hrad_le_Q'
      exact le_antisymm hQ'_le_hrad hrad_le_Q'
  · rintro ⟨Q, hQ, huniq⟩
    have hQmem : Q.1 ∈ I.minimalPrimes :=
      completion_minimalPrime_mem_mapped_ideal_minimalPrimes (A := A) (Ah := Ah) q hQ
    have hsingleton : I.minimalPrimes = {Q.1} := by
      ext J
      constructor
      · intro hJ
        have hJmin :
            J ∈ minimalPrimes ACompletion :=
          completion_mem_minimalPrimes_of_mem_mapped_ideal_minimalPrimes
            (A := A) (Ah := Ah) q hJ
        have hJq :
            Ideal.comap (algebraMap Ah ACompletion) J = q :=
          contraction_eq_of_mem_mapped_ideal_minimalPrimes (A := A) (Ah := Ah) q hJ
        have hJ_eq : (⟨J, hJmin⟩ : minimalPrimes ACompletion) = Q := huniq _ hJq
        exact Set.mem_singleton_iff.mpr <| congrArg Subtype.val hJ_eq
      · intro hJ
        rcases Set.mem_singleton_iff.mp hJ with rfl
        exact hQmem
    have hrad_eq : Ideal.radical I = Q.1 := by
      rw [← Ideal.sInf_minimalPrimes, hsingleton, sInf_singleton]
    -- A singleton minimal-prime set forces the radical to be that prime.
    simpa [I, hrad_eq] using (show Q.1.IsPrime by infer_instance)

/-- Helper for Lemma 15.109.2: equality of the two finite branch counts is equivalent to every
completion fiber over a henselization minimal prime being a singleton. -/
lemma branch_count_eq_iff_exists_unique_completion_fiber :
    branchNumber A Ah = (minimalPrimes ACompletion).encard ↔
      ∀ q : minimalPrimes Ah,
        ∃! Q : minimalPrimes ACompletion, Ideal.comap (algebraMap Ah ACompletion) Q = q := by
  letI : IsNoetherianRing Ah := isNoetherianRing_henselization A Ah
  letI : IsNoetherianRing ACompletion := adicCompletion_isNoetherianRing (maximalIdeal A)
  letI : Fintype (minimalPrimes Ah) := (minimalPrimes.finite_of_isNoetherianRing Ah).fintype
  letI : Fintype (minimalPrimes ACompletion) :=
    (minimalPrimes.finite_of_isNoetherianRing ACompletion).fintype
  let contract : minimalPrimes ACompletion → minimalPrimes Ah := fun Q ↦
    ⟨Ideal.comap (algebraMap Ah ACompletion) Q,
      comap_mem_minimalPrimes_of_completion_minimalPrime (A := A) (Ah := Ah) Q⟩
  have hcontract_surj : Function.Surjective contract := by
    intro q
    rcases
        henselizationCompletion_surjOn_minimalPrimes (A := A) (Ah := Ah) q.2 with
      ⟨Q, hQmin, hQq⟩
    exact ⟨⟨Q, hQmin⟩, by
      apply Subtype.ext
      simpa using hQq⟩
  constructor
  · intro hcount q
    have hcard :
        Fintype.card (minimalPrimes Ah) = Fintype.card (minimalPrimes ACompletion) := by
      rw [branchNumber, (Set.coe_fintypeCard (minimalPrimes Ah)).symm,
        (Set.coe_fintypeCard (minimalPrimes ACompletion)).symm] at hcount
      exact_mod_cast hcount
    classical
    let choosePrime : minimalPrimes Ah → minimalPrimes ACompletion := fun q ↦
      Classical.choose (hcontract_surj q)
    have hchoosePrime : ∀ q : minimalPrimes Ah, contract (choosePrime q) = q := by
      intro q
      exact Classical.choose_spec (hcontract_surj q)
    have hchoosePrime_inj : Function.Injective choosePrime :=
      Function.LeftInverse.injective hchoosePrime
    have hcontract_inj : Function.Injective contract := by
      by_contra hnotinj
      have hchoosePrime_nsurj : ¬ Function.Surjective choosePrime := by
        intro hsec_surj
        apply hnotinj
        intro Q₁ Q₂ hEq
        rcases hsec_surj Q₁ with ⟨q₁, rfl⟩
        rcases hsec_surj Q₂ with ⟨q₂, rfl⟩
        have : q₁ = q₂ := by
          simpa [hchoosePrime q₁, hchoosePrime q₂] using hEq
        simpa [this]
      have hlt :
          Fintype.card (minimalPrimes Ah) < Fintype.card (minimalPrimes ACompletion) :=
        Fintype.card_lt_of_injective_not_surjective
          choosePrime hchoosePrime_inj hchoosePrime_nsurj
      rw [hcard] at hlt
      exact Nat.lt_irrefl _ hlt
    refine ⟨choosePrime q, congrArg Subtype.val (hchoosePrime q), ?_⟩
    intro Q hQ
    have hcontractQ : contract Q = q := by
      apply Subtype.ext
      exact hQ
    exact hcontract_inj (hcontractQ.trans (hchoosePrime q).symm)
  · intro hfiber
    have hcontract_inj : Function.Injective contract := by
      intro Q₁ Q₂ hEq
      rcases hfiber (contract Q₁) with ⟨Q, hQ, huniqQ⟩
      have hQ₁ : Q₁ = Q := huniqQ _ rfl
      have hQ₂ : Q₂ = Q := huniqQ _ (congrArg Subtype.val hEq).symm
      exact hQ₁.trans hQ₂.symm
    have hcard_le₁ :
        Fintype.card (minimalPrimes ACompletion) ≤ Fintype.card (minimalPrimes Ah) :=
      Fintype.card_le_of_injective contract hcontract_inj
    have hcard_le₂ :
        Fintype.card (minimalPrimes Ah) ≤ Fintype.card (minimalPrimes ACompletion) :=
      Fintype.card_le_of_surjective contract hcontract_surj
    have hcard :
        Fintype.card (minimalPrimes Ah) = Fintype.card (minimalPrimes ACompletion) :=
      le_antisymm hcard_le₂ hcard_le₁
    rw [branchNumber, (Set.coe_fintypeCard (minimalPrimes Ah)).symm,
      (Set.coe_fintypeCard (minimalPrimes ACompletion)).symm]
    exact_mod_cast hcard

/-
Domain-style sampling:
- primary domain: Noetherian local commutative algebra of henselizations, maximal-ideal
  completions, and minimal primes;
- sampled owner declarations:
  `branchNumber`,
  `minimalPrimes`,
  `henselizationCompletionComparison`,
  `henselizationCompletion_surjOn_minimalPrimes`;
- best owner abstraction: the source-facing equality criterion should use the canonical owner
  subtype `minimalPrimes Ah` for the minimal primes of the chosen henselization, while the
  comparison map to the completion remains the owner-derived
  `henselizationCompletionComparison A Ah`;
- primitive data: the Noetherian local ring `A`, its chosen henselization `Ah`, and the canonical
  comparison map `Ah → ACompletion`;
- derived API: the branch count `branchNumber A Ah`, the minimal-prime count
  `(minimalPrimes ACompletion).encard`, and the primality of the radicals of extended minimal
  primes.

Source/core/bridge triage:
- `source-facing`: the equivalence below;
- `core/canonical`: `minimalPrimes`, `branchNumber`, `AdicCompletion`, `Ideal.map`,
  `Ideal.radical`;
- `bridge/view`: `henselizationCompletionComparison A Ah`.
-/
-- Proof sketch: by Lemma `15.109.1`, the minimal primes of `ACompletion` surject onto the minimal
-- primes of `Ah`, so equality of branch counts is equivalent to every fiber over a minimal prime
-- of `Ah` consisting of a single minimal prime of `ACompletion`. Since both rings are Noetherian
-- by Lemma `15.45.3` and Algebra, Lemma `10.31.6`, this uniqueness is equivalent to the radical
-- of the extended ideal `qACompletion` being prime for each minimal prime `q` of `Ah`.
/-- Lemma 15.109.2: for a Noetherian local ring `A` with chosen henselization `Ah`, the number of
branches of `A` equals the number of minimal primes of the completion
`ACompletion = AdicCompletion (maximalIdeal A) A` if and only if for every minimal prime `q` of
`Ah`, the radical `√(qACompletion)` is prime. -/
theorem branchNumber_eq_completion_minimalPrimes_iff_radical_map_minimalPrime_isPrime
    :
    branchNumber A Ah = (minimalPrimes ACompletion).encard ↔
      ∀ q : minimalPrimes Ah,
        (Ideal.radical (Ideal.map (henselizationCompletionComparison A Ah) q)).IsPrime :=
      by
  constructor
  · intro hcount q
    -- Route correction: first convert the global count equality into singleton fibers, then apply
    -- the pointwise radical criterion for that fiber.
    have hfiber :
        ∃! Q : minimalPrimes ACompletion, Ideal.comap (algebraMap Ah ACompletion) Q = q :=
      (branch_count_eq_iff_exists_unique_completion_fiber (A := A) (Ah := Ah)).mp hcount q
    simpa [completionComparisonAlgebra, RingHom.algebraMap_toAlgebra] using
      (radical_map_minimal_prime_is_prime_iff_exists_unique_completion_minimal_prime
        (A := A) (Ah := Ah) q).mpr hfiber
  · intro hprime
    apply (branch_count_eq_iff_exists_unique_completion_fiber (A := A) (Ah := Ah)).mpr
    intro q
    have hprime' :
        (Ideal.radical (Ideal.map (algebraMap Ah ACompletion) q)).IsPrime := by
      simpa [completionComparisonAlgebra, RingHom.algebraMap_toAlgebra] using hprime q
    exact
      (radical_map_minimal_prime_is_prime_iff_exists_unique_completion_minimal_prime
        (A := A) (Ah := Ah) q).mp hprime'

end
