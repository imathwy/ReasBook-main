import Mathlib
import StacksProject_2024.Chap09.Lemma_9_25_1_Artin_Schreier_extensions
import StacksProject_2024.Chap10.Definition_10_42_1
import StacksProject_2024.Chap15.Definition_15_112_7
import StacksProject_2024.Chap15.Definition_15_116_1
import StacksProject_2024.Chap15.Lemma_15_112_4
import StacksProject_2024.Chap15.Lemma_15_116_10

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open IsExtensionOfDiscreteValuationRings

universe u v w x y z

section

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/- Domain-style sampling for Lemma 15.116.12:
- primary domain: ramification-eliminating finite base change for extensions of discrete
  valuation rings, organized around the chapter weak-solution owner and the branchwise
  total-ramification owner from Definition `15.112.7`;
- sampled owner declarations:
  `IsWeakSolutionFor`,
  `IsTotallyRamifiedWithRespectTo`,
  `weakSolutionFor_of_weakSolutionFor_comp`,
  `exists_totallyRamified_separable_extension_with_prescribed_uniformizer_congruence`;
- best owner abstraction: this lemma is `source-facing`; the main owner for the conclusion is the
  chapter predicate `IsWeakSolutionFor`, while total ramification should remain the canonical
  owner `IsTotallyRamifiedWithRespectTo A K1`, and the ambient `FractionRing A`-algebra lift
  should be recovered from the canonical `FractionRing.liftAlgebra` bridge instead of being kept
  as primitive witness data;
- primitive-vs-derived split: the primitive witness data are the field `K1`, its `A`- and
  chosen-fraction-field `K`-algebra structures, the `A → K → K1` scalar tower, and
  finite-dimensionality over `K`; the faithful-smul bridge to `FractionRing A`, the
  `FractionRing A`-algebra structure, Galoisness, total ramification, and the weak-solution
  property are derived from that witness via the canonical bridge data and owner predicates.

Source/core/bridge triage:
- `source-facing`: the existence theorem producing a totally ramified Galois weak solution;
- `core/canonical`: `IsWeakSolutionFor` and `IsTotallyRamifiedWithRespectTo`;
- `bridge/view`: `FaithfulSMul.of_field_isFractionRing`, `FractionRing.liftAlgebra`, and
  `FractionRing.isScalarTower_liftAlgebra`, relating the chosen fraction field `K` to the
  total-ramification owner.
-/

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsExtensionOfDiscreteValuationRings A B]
variable [IsExtensionOfDiscreteValuationRings B C]
variable [IsExtensionOfDiscreteValuationRings A C]
variable {K : Type x} {L : Type y} {M : Type z}
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra B L] [Algebra A L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field M] [Algebra A M] [Algebra K M] [Algebra C M] [Algebra L M] [IsFractionRing C M]
variable [IsScalarTower A C M] [IsScalarTower A K M]
variable {p : ℕ} [Fact p.Prime] [CharP K p] [FiniteDimensional L M] [IsGalois L M]

open scoped IntermediateField

/- The source proof starts by replacing the degree-`p` Galois extension `M / L` in characteristic
`p` by an Artin-Schreier presentation. The rest of the argument is an induction on the pole data
of that Artin-Schreier parameter. -/
/-- Helper for Lemma 15.116.12: a degree-`p` Galois extension in characteristic `p` admits an
Artin-Schreier generator. -/
lemma exists_artin_schreier_generator_of_galois_prime_degree
    {k : Type x} [Field k] [Algebra k L] [CharP k p]
    (hLM : Module.finrank L M = p) :
    ∃ ξ : L, ∃ z : M, z ^ p - z = algebraMap L M ξ ∧ L⟮z⟯ = ⊤ := by
  let _ : CharP L p :=
    charP_of_injective_algebraMap (R := k) (A := L) (algebraMap k L).injective p
  -- The Galois group has prime cardinality `p`, hence it is cyclic.
  let _ : IsCyclic Gal(M / L) :=
    isCyclic_of_prime_card (p := p) <| by
      rw [IsGalois.card_aut_eq_finrank L M, hLM]
  obtain ⟨z, hgen, hz_mem⟩ :=
    exists_artin_schreier_generator_of_isCyclic (K := L) (L := M) (p := p) hLM
  rcases (IntermediateField.mem_bot (F := L) (E := M)).mp hz_mem with ⟨ξ, hξ⟩
  -- Repackage the bottom-intermediate-field membership as the displayed Artin-Schreier equation.
  exact ⟨ξ, z, hξ.symm, hgen⟩

/-- Helper for Lemma 15.116.12: every element in the image of `ResidueField A` lies in each
positive `p^n`-power slice appearing in the source intersection hypothesis. -/
lemma mem_pPower_range_of_mem_image_of_pPowerIntersection
    (hκ :
      (Set.range (algebraMap (ResidueField A) (ResidueField B)) : Set (ResidueField B)) =
        ⋂ n : ℕ+, Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ))))
    {b : ResidueField B}
    (hb : b ∈ Set.range (algebraMap (ResidueField A) (ResidueField B))) :
    ∀ n : ℕ+, b ∈ Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ))) := by
  -- Rewrite the source hypothesis as membership in the displayed intersection.
  have hb_inter :
      b ∈ ⋂ n : ℕ+, Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ))) := by
    rw [← hκ]
    exact hb
  -- Each individual `p^n`-power slice is then immediate from the intersection membership.
  exact Set.mem_iInter.mp hb_inter

/-- Helper for Lemma 15.116.12: every residue class outside the image of `ResidueField A` misses
at least one positive `p^n`-power slice from the source intersection hypothesis. -/
lemma exists_missing_pPower_slice_of_not_mem_image_of_pPowerIntersection
    (hκ :
      (Set.range (algebraMap (ResidueField A) (ResidueField B)) : Set (ResidueField B)) =
        ⋂ n : ℕ+, Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ))))
    {b : ResidueField B}
    (hb : b ∉ Set.range (algebraMap (ResidueField A) (ResidueField B))) :
    ∃ n : ℕ+, b ∉ Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ))) := by
  classical
  by_contra hnone
  have hmem :
      b ∈ ⋂ n : ℕ+, Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ))) := by
    -- If no positive slice excludes `b`, then `b` lies in their intersection.
    refine Set.mem_iInter.mpr ?_
    intro n
    by_contra hn
    exact hnone ⟨n, hn⟩
  exact hb <| by simpa [hκ] using hmem

/-- Helper for Lemma 15.116.12: the source intersection hypothesis makes `ResidueField A`
perfect, which is the exact input needed in the base case of the bad-index induction. -/
lemma residueField_perfect_of_pPowerIntersection
    [CharP (ResidueField A) p] [CharP (ResidueField B) p]
    (hκ :
      (Set.range (algebraMap (ResidueField A) (ResidueField B)) : Set (ResidueField B)) =
        ⋂ n : ℕ+, Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ)))) :
    ∀ a : ResidueField A, ∃ b : ResidueField A, b ^ p = a := by
  intro a
  have ha_mem :
      algebraMap (ResidueField A) (ResidueField B) a ∈
        Set.range (algebraMap (ResidueField A) (ResidueField B)) := by
    exact ⟨a, rfl⟩
  obtain ⟨c, hc⟩ :=
    mem_pPower_range_of_mem_image_of_pPowerIntersection (A := A) (B := B) (p := p) hκ ha_mem 1
  have hc_p :
      c ^ p = algebraMap (ResidueField A) (ResidueField B) a := by
    simpa using hc
  have hc_allSlices :
      ∀ n : ℕ+, c ∈ Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ))) := by
    intro n
    let n' : ℕ+ := ⟨(n : ℕ) + 1, Nat.succ_pos _⟩
    obtain ⟨d, hd⟩ :=
      mem_pPower_range_of_mem_image_of_pPowerIntersection
        (A := A) (B := B) (p := p) hκ ha_mem n'
    refine ⟨d, ?_⟩
    -- Pull one Frobenius step off the `p^(n+1)`-power witness using injectivity on the field.
    have hd_shift :
        algebraMap (ResidueField A) (ResidueField B) a = (d ^ (p ^ (n : ℕ))) ^ p := by
      calc
        algebraMap (ResidueField A) (ResidueField B) a = d ^ (p ^ ((n' : ℕ))) := by
          simpa [n'] using hd.symm
        _ = d ^ ((p ^ (n : ℕ)) * p) := by
              simp [n', pow_succ', Nat.mul_comm]
        _ = (d ^ (p ^ (n : ℕ))) ^ p := by rw [pow_mul]
    have hfrobenius :
        frobenius (ResidueField B) p c =
          frobenius (ResidueField B) p (d ^ (p ^ (n : ℕ))) := by
      rw [frobenius_def, frobenius_def, hc_p]
      exact hd_shift
    exact (frobenius_inj (ResidueField B) p) hfrobenius.symm
  have hc_mem_image :
      c ∈ Set.range (algebraMap (ResidueField A) (ResidueField B)) := by
    rw [hκ]
    exact Set.mem_iInter.mpr hc_allSlices
  rcases hc_mem_image with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  -- Compare the displayed `p`th-power identity after mapping into `ResidueField B`.
  apply (algebraMap (ResidueField A) (ResidueField B)).injective
  calc
    algebraMap (ResidueField A) (ResidueField B) (b ^ p)
        = (algebraMap (ResidueField A) (ResidueField B) b) ^ p := by simp
    _ = c ^ p := by rw [hb]
    _ = algebraMap (ResidueField A) (ResidueField B) a := hc_p

/-- Helper for Lemma 15.116.12: once the source residue field is perfect, the residue extension
`ResidueField B / ResidueField A` is separable in the Stacks Project sense, exactly as required by
Lemma `15.116.10`. -/
lemma residueField_isSeparableOver_of_pPowerIntersection
    [CharP (ResidueField A) p] [CharP (ResidueField B) p]
    (hκ :
      (Set.range (algebraMap (ResidueField A) (ResidueField B)) : Set (ResidueField B)) =
        ⋂ n : ℕ+, Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ)))) :
    Algebra.IsSeparableOver (ResidueField A) (ResidueField B) := by
  letI : PerfectRing (ResidueField A) p :=
    PerfectRing.ofSurjective (ResidueField A) p <|
      residueField_perfect_of_pPowerIntersection (A := A) (B := B) (p := p) hκ
  letI : PerfectField (ResidueField A) :=
    PerfectRing.toPerfectField (ResidueField A) p
  -- Over a perfect base field, every extension is separable in the Stacks Project sense.
  infer_instance

/-- Helper for Lemma 15.116.12: a surjective local homomorphism induces a bijection on residue
fields. This is the bridge needed to transport perfectness from `ResidueField A` to the residue
field of the Artinian quotient `A / maximalIdeal A ^ (n + 1)`. -/
lemma residueField_bijective_of_surjective_localHom
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Nontrivial S] (f : R →+* S) (hf_surj : Function.Surjective f) [IsLocalHom f] :
    Function.Bijective (ResidueField.map f) := by
  constructor
  · -- The source residue field is a field, so the induced map is automatically injective.
    exact RingHom.injective (ResidueField.map f)
  · -- Lift target residue classes first to `S`, then along the surjective local map.
    intro z
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨r, rfl⟩ := hf_surj s
    refine ⟨residue R r, ?_⟩
    simpa using IsLocalRing.ResidueField.map_residue f r

/-- Helper for Lemma 15.116.12: every positive power of the maximal ideal in a local ring is
proper, so the corresponding quotient remains nontrivial. -/
lemma quotient_pow_maximalIdeal_ne_top
    {R : Type*} [CommRing R] [IsLocalRing R] (n : ℕ) :
    maximalIdeal R ^ (n + 1) ≠ (⊤ : Ideal R) := by
  intro hpow
  have htop : (⊤ : Ideal R) ≤ maximalIdeal R := by
    calc
      (⊤ : Ideal R) = maximalIdeal R ^ (n + 1) := hpow.symm
      _ ≤ maximalIdeal R := Ideal.pow_le_self (I := maximalIdeal R) (Nat.succ_ne_zero n)
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp htop)

local instance quotient_pow_maximalIdeal_nontrivial
    {R : Type*} [CommRing R] [IsLocalRing R] (n : ℕ) :
    Nontrivial (R ⧸ maximalIdeal R ^ (n + 1)) :=
  Ideal.Quotient.nontrivial_iff.2 (quotient_pow_maximalIdeal_ne_top (R := R) n)

local instance quotient_pow_maximalIdeal_isLocalRing
    {R : Type*} [CommRing R] [IsLocalRing R] (n : ℕ) :
    IsLocalRing (R ⧸ maximalIdeal R ^ (n + 1)) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))
    Ideal.Quotient.mk_surjective

local instance quotient_pow_maximalIdeal_isLocalHom
    {R : Type*} [CommRing R] [IsLocalRing R] (n : ℕ) :
    IsLocalHom (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)) : R →+* R ⧸ maximalIdeal R ^ (n + 1)) :=
  Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective

/-- Helper for Lemma 15.116.12: characteristic `p` descends from a local ring to its residue
field. This keeps the later quotient-level perfectness lemmas in the same characteristic. -/
lemma residueField_charP_of_charP
    {R : Type*} [CommRing R] [IsLocalRing R] [CharP R p] :
    CharP (ResidueField R) p := by
  exact CharP.quotient' p (maximalIdeal R) fun n hn ↦ by
    by_contra hnat
    have hnotunit : ¬ IsUnit (n : R) := by
      simpa [IsLocalRing.mem_maximalIdeal] using hn
    have hnotdvd : ¬ p ∣ n := by
      simpa [CharP.cast_eq_zero_iff R p n] using hnat
    exact hnotunit ((CharP.isUnit_natCast_iff (R := R) (p := p) (Fact.out)).2 hnotdvd)

/-- Helper for Lemma 15.116.12: quotienting a characteristic-`p` local ring by a power of its
maximal ideal stays in characteristic `p`. -/
lemma quotient_pow_maximalIdeal_charP
    {R : Type*} [CommRing R] [IsLocalRing R] [CharP R p] (n : ℕ) :
    CharP (R ⧸ maximalIdeal R ^ (n + 1)) p := by
  have hp_zero : ((p : R ⧸ maximalIdeal R ^ (n + 1))) = 0 := by
    change Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)) (p : R) = 0
    have hp_zero_R : (p : R) = 0 := by
      simpa using (CharP.cast_eq_zero (R := R) p p)
    simpa [hp_zero_R]
  have hchar : ringChar (R ⧸ maximalIdeal R ^ (n + 1)) = p := by
    exact CharP.ringChar_of_prime_eq_zero (R := R ⧸ maximalIdeal R ^ (n + 1)) Fact.out hp_zero
  cases hchar
  infer_instance

/-- Helper for Lemma 15.116.12: quotienting a local ring by a power of its maximal ideal does not
change its residue field. This is the transport needed to move perfectness from `ResidueField A`
to the Artinian quotients that feed Lemma `15.116.10`. -/
noncomputable def residueField_quotient_pow_maximalIdeal_equiv
    {R : Type*} [CommRing R] [IsLocalRing R] (n : ℕ) :
    ResidueField (R ⧸ maximalIdeal R ^ (n + 1)) ≃+* ResidueField R :=
  (RingEquiv.ofBijective
    (ResidueField.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))))
    (residueField_bijective_of_surjective_localHom
      (f := Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))
      Ideal.Quotient.mk_surjective)).symm

/-- Helper for Lemma 15.116.12: under the quotient-residue-field identification, the residue class
of the image of `x` in `R / maximalIdeal R ^ (n + 1)` is the original residue class of `x`. -/
lemma residueField_quotient_pow_maximalIdeal_equiv_apply_residue
    {R : Type*} [CommRing R] [IsLocalRing R] (n : ℕ) (x : R) :
    residueField_quotient_pow_maximalIdeal_equiv (R := R) n
        (residue (R ⧸ maximalIdeal R ^ (n + 1))
          (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)) x)) =
      residue R x := by
  -- The equivalence is the inverse of the residue-field map induced by the quotient projection.
  let e :
      ResidueField R ≃+* ResidueField (R ⧸ maximalIdeal R ^ (n + 1)) :=
    RingEquiv.ofBijective
      (ResidueField.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))))
      (residueField_bijective_of_surjective_localHom
        (f := Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))
        Ideal.Quotient.mk_surjective)
  have hmap :
      residue (R ⧸ maximalIdeal R ^ (n + 1))
          (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)) x) =
        e (residue R x) := by
    simpa [e] using IsLocalRing.ResidueField.map_residue
      (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) x
  rw [hmap]
  exact e.symm_apply_apply (residue R x)

/-- Helper for Lemma 15.116.12: the maximal ideal of `R / maximalIdeal R ^ (n + 1)` is nilpotent.
This is the Artinian input needed before applying Lemma `15.116.10` to quotients modulo powers of
the chosen uniformizer. -/
lemma quotient_pow_maximalIdeal_nilpotent
    {R : Type*} [CommRing R] [IsLocalRing R] (n : ℕ) :
    IsNilpotent (maximalIdeal (R ⧸ maximalIdeal R ^ (n + 1))) := by
  let π : R →+* R ⧸ maximalIdeal R ^ (n + 1) := Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))
  letI : IsLocalRing (R ⧸ maximalIdeal R ^ (n + 1)) :=
    IsLocalRing.of_surjective' π Ideal.Quotient.mk_surjective
  have hmax :
      maximalIdeal (R ⧸ maximalIdeal R ^ (n + 1)) = Ideal.map π (maximalIdeal R) := by
    symm
    exact IsLocalRing.map_maximalIdeal_of_surjective π Ideal.Quotient.mk_surjective
  refine ⟨n + 1, ?_⟩
  calc
    maximalIdeal (R ⧸ maximalIdeal R ^ (n + 1)) ^ (n + 1) =
        Ideal.map π (maximalIdeal R) ^ (n + 1) := by
          rw [hmax]
    _ = Ideal.map π (maximalIdeal R ^ (n + 1)) := by
          rw [Ideal.map_pow]
    _ = ⊥ := by
          apply (Ideal.map_eq_bot_iff_le_ker π).2
          simpa [π, Ideal.mk_ker]

/-- Helper for Lemma 15.116.12: the quotient residue field
`ResidueField (A / maximalIdeal A^(n+1))` is perfect once the source intersection hypothesis makes
`ResidueField A` perfect. This is the transport needed before applying coefficient-field sections
to Artinian quotients. -/
lemma residueField_quotient_pow_maximalIdeal_perfect_of_pPowerIntersection
    [CharP (ResidueField A) p] [CharP (ResidueField B) p]
    (n : ℕ)
    (hκ :
      (Set.range (algebraMap (ResidueField A) (ResidueField B)) : Set (ResidueField B)) =
        ⋂ n : ℕ+, Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ)))) :
    ∀ a : ResidueField (A ⧸ maximalIdeal A ^ (n + 1)),
      ∃ b : ResidueField (A ⧸ maximalIdeal A ^ (n + 1)), b ^ p = a := by
  intro a
  let e := residueField_quotient_pow_maximalIdeal_equiv (R := A) n
  obtain ⟨b, hb⟩ :=
    residueField_perfect_of_pPowerIntersection (A := A) (B := B) (p := p) hκ (e a)
  refine ⟨e.symm b, ?_⟩
  -- Compare the `p`th-power identity after transporting it across the quotient-residue-field
  -- equivalence.
  apply e.injective
  calc
    e ((e.symm b) ^ p) = (e (e.symm b)) ^ p := by simp
    _ = b ^ p := by simp
    _ = e a := hb

/-- Helper for Lemma 15.116.12: every quotient by a positive power of the maximal ideal admits a
residue-field section. This gives the actual Artinian coefficient-field maps used in the source
pole-expansion step, before enforcing compatibility across `A ⊆ B`. -/
lemma exists_residueField_section_quotient_pow_maximalIdeal
    {R : Type*} [CommRing R] [IsLocalRing R] [CharP R p]
    (n : ℕ) :
    ∃ σ : ResidueField (R ⧸ maximalIdeal R ^ (n + 1)) →+* (R ⧸ maximalIdeal R ^ (n + 1)),
      (residue (R ⧸ maximalIdeal R ^ (n + 1))).comp σ =
        RingHom.id (ResidueField (R ⧸ maximalIdeal R ^ (n + 1))) := by
  letI : CharP (R ⧸ maximalIdeal R ^ (n + 1)) p :=
    quotient_pow_maximalIdeal_charP (R := R) (p := p) n
  -- The quotient is Artinian local because its maximal ideal is nilpotent.
  exact
    exists_residueField_section_of_isNilpotent_maximalIdeal
      (A := R ⧸ maximalIdeal R ^ (n + 1)) (p := p)
      (quotient_pow_maximalIdeal_nilpotent (R := R) n)

omit [Algebra A B] [IsExtensionOfDiscreteValuationRings A B] in
/-- Helper for Lemma 15.116.12: both Artinian quotients
`A / maximalIdeal A^(n+1)` and `B / maximalIdeal B^(n+1)` admit residue-field sections. This
packages the first concrete part of the source quotient-section setup before the remaining
compatibility transport across the quotient map. -/
lemma exists_residueField_sections_mod_maximalIdeal_power
    [CharP A p] [CharP B p]
    (n : ℕ) :
    (∃ σA : ResidueField (A ⧸ maximalIdeal A ^ (n + 1)) →+* (A ⧸ maximalIdeal A ^ (n + 1)),
        (residue (A ⧸ maximalIdeal A ^ (n + 1))).comp σA =
          RingHom.id (ResidueField (A ⧸ maximalIdeal A ^ (n + 1)))) ∧
      ∃ σB : ResidueField (B ⧸ maximalIdeal B ^ (n + 1)) →+* (B ⧸ maximalIdeal B ^ (n + 1)),
        (residue (B ⧸ maximalIdeal B ^ (n + 1))).comp σB =
          RingHom.id (ResidueField (B ⧸ maximalIdeal B ^ (n + 1))) := by
  constructor
  · -- The source quotient section comes from the Artinian local quotient of `A`.
    exact exists_residueField_section_quotient_pow_maximalIdeal (R := A) (p := p) n
  · -- The target quotient section is produced in exactly the same Artinian way.
    exact exists_residueField_section_quotient_pow_maximalIdeal (R := B) (p := p) n

/-- Helper for Lemma 15.116.12: weakly unramifiedness identifies the powered maximal ideals
needed to define the quotient comparison map `A / maximalIdeal^(n+1) → B / maximalIdeal^(n+1)`. -/
lemma quotient_pow_maximalIdeal_le_comap_of_weaklyUnramified
    (hAB : WeaklyUnramified A B) (n : ℕ) :
    maximalIdeal A ^ (n + 1) ≤
      Ideal.comap (algebraMap A B) (maximalIdeal B ^ (n + 1)) := by
  -- First rewrite weak ramification as equality of the maximal ideals themselves.
  have hmap :
      Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B := by
    exact
      (IsExtensionOfDiscreteValuationRings.weaklyUnramified_iff_map_maximalIdeal
        (A := A) (B := B)).1 hAB
  have hpow :
      Ideal.map (algebraMap A B) (maximalIdeal A ^ (n + 1)) =
        maximalIdeal B ^ (n + 1) := by
    -- Then pass that equality to the desired power level.
    simpa [hmap] using
      (Ideal.map_pow (algebraMap A B) (maximalIdeal A) (n + 1))
  exact Ideal.map_le_iff_le_comap.mp (le_of_eq hpow)

/-- Helper for Lemma 15.116.12: the canonical map on quotient rings induced by a weakly
unramified extension of discrete valuation rings. -/
noncomputable def quotient_pow_maximalIdeal_map_of_weaklyUnramified
    (hAB : WeaklyUnramified A B) (n : ℕ) :
    A ⧸ maximalIdeal A ^ (n + 1) →+* B ⧸ maximalIdeal B ^ (n + 1) :=
  Ideal.quotientMap (maximalIdeal B ^ (n + 1)) (algebraMap A B)
    (quotient_pow_maximalIdeal_le_comap_of_weaklyUnramified
      (A := A) (B := B) hAB n)

/-- Helper for Lemma 15.116.12: the quotient comparison map agrees with the original algebra map
after precomposing with the quotient projection from `A`. -/
lemma quotient_pow_maximalIdeal_map_comp_mk_of_weaklyUnramified
    (hAB : WeaklyUnramified A B) (n : ℕ) :
    (quotient_pow_maximalIdeal_map_of_weaklyUnramified
        (A := A) (B := B) hAB n).comp
        (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))) =
      (Ideal.Quotient.mk (maximalIdeal B ^ (n + 1))).comp (algebraMap A B) := by
  -- This is exactly the defining compatibility of `Ideal.quotientMap`.
  simpa [quotient_pow_maximalIdeal_map_of_weaklyUnramified] using
    (Ideal.quotientMap_comp_mk
      (f := algebraMap A B)
      (H := quotient_pow_maximalIdeal_le_comap_of_weaklyUnramified
        (A := A) (B := B) hAB n))

/-- Helper for Lemma 15.116.12: the quotient comparison map between Artinian quotients is a local
homomorphism. This is the exact quotient-level bridge needed before applying Lemma `15.116.10`. -/
lemma quotient_pow_maximalIdeal_localHom_of_weaklyUnramified
    (hAB : WeaklyUnramified A B) (n : ℕ) :
    IsLocalHom
      (quotient_pow_maximalIdeal_map_of_weaklyUnramified (A := A) (B := B) hAB n) := by
  let α :=
    quotient_pow_maximalIdeal_map_of_weaklyUnramified (A := A) (B := B) hAB n
  let qA : A →+* A ⧸ maximalIdeal A ^ (n + 1) :=
    Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))
  let qB : B →+* B ⧸ maximalIdeal B ^ (n + 1) :=
    Ideal.Quotient.mk (maximalIdeal B ^ (n + 1))
  have hmaxA :
      maximalIdeal (A ⧸ maximalIdeal A ^ (n + 1)) =
        Ideal.map qA (maximalIdeal A) := by
    -- Quotienting by a proper ideal preserves locality, and the resulting maximal ideal is the
    -- image of the original one.
    symm
    exact IsLocalRing.map_maximalIdeal_of_surjective qA Ideal.Quotient.mk_surjective
  have hcomp :
      α.comp qA = qB.comp (algebraMap A B) := by
    -- The quotient comparison is characterized by commuting with the quotient maps.
    simpa [α, qA, qB] using
      quotient_pow_maximalIdeal_map_comp_mk_of_weaklyUnramified
        (A := A) (B := B) hAB n
  have hcomp_map :
      Ideal.map (qB.comp (algebraMap A B)) (maximalIdeal A) ≤
        maximalIdeal (B ⧸ maximalIdeal B ^ (n + 1)) := by
    have hlocal_comp : IsLocalHom (qB.comp (algebraMap A B)) := inferInstance
    -- The composite `A → B → B / maximalIdeal^(n+1)` is already a local hom, so it sends the
    -- maximal ideal of `A` into the maximal ideal of the quotient.
    exact
      (((IsLocalRing.local_hom_TFAE (qB.comp (algebraMap A B))).out 0 2).mp hlocal_comp)
  have hα_map :
      Ideal.map α (maximalIdeal (A ⧸ maximalIdeal A ^ (n + 1))) ≤
        maximalIdeal (B ⧸ maximalIdeal B ^ (n + 1)) := by
    calc
      Ideal.map α (maximalIdeal (A ⧸ maximalIdeal A ^ (n + 1))) =
          Ideal.map α (Ideal.map qA (maximalIdeal A)) := by
            rw [hmaxA]
      _ = Ideal.map (α.comp qA) (maximalIdeal A) := by
            rw [Ideal.map_map]
      _ = Ideal.map (qB.comp (algebraMap A B)) (maximalIdeal A) := by
            rw [hcomp]
      _ ≤ maximalIdeal (B ⧸ maximalIdeal B ^ (n + 1)) := hcomp_map
  -- Convert the maximal-ideal inclusion back into the local-hom property for `α`.
  exact (((IsLocalRing.local_hom_TFAE α).out 2 0).mp hα_map)

attribute [local instance] quotient_pow_maximalIdeal_localHom_of_weaklyUnramified

/-- Helper for Lemma 15.116.12: after identifying the quotient residue fields with the original
ones, the residue-field map induced by the quotient comparison is the original
`ResidueField A → ResidueField B` map. -/
lemma residueField_map_quotient_pow_maximalIdeal_transport
    (hAB : WeaklyUnramified A B) (n : ℕ) :
    (residueField_quotient_pow_maximalIdeal_equiv (R := B) n).toRingHom.comp
        (ResidueField.map
          (quotient_pow_maximalIdeal_map_of_weaklyUnramified (A := A) (B := B) hAB n)) =
      (algebraMap (ResidueField A) (ResidueField B)).comp
        (residueField_quotient_pow_maximalIdeal_equiv (R := A) n).toRingHom := by
  let α :=
    quotient_pow_maximalIdeal_map_of_weaklyUnramified (A := A) (B := B) hAB n
  let qA : A →+* A ⧸ maximalIdeal A ^ (n + 1) :=
    Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))
  let qB : B →+* B ⧸ maximalIdeal B ^ (n + 1) :=
    Ideal.Quotient.mk (maximalIdeal B ^ (n + 1))
  let _ : IsLocalHom α :=
    quotient_pow_maximalIdeal_localHom_of_weaklyUnramified (A := A) (B := B) hAB n
  ext x
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  -- It suffices to evaluate both sides on residue classes of elements of `A`.
  calc
    ((residueField_quotient_pow_maximalIdeal_equiv (R := B) n).toRingHom.comp
        (ResidueField.map α))
        (residue (A ⧸ maximalIdeal A ^ (n + 1)) (qA a)) =
      residueField_quotient_pow_maximalIdeal_equiv (R := B) n
        (residue (B ⧸ maximalIdeal B ^ (n + 1)) (qB ((algebraMap A B) a))) := by
        -- Rewrite the quotient comparison on representatives and then pass to residues.
        rw [RingHom.comp_apply, IsLocalRing.ResidueField.map_residue]
        simp [α, qA, qB, quotient_pow_maximalIdeal_map_of_weaklyUnramified]
    _ = residue B ((algebraMap A B) a) := by
        simpa using residueField_quotient_pow_maximalIdeal_equiv_apply_residue
          (R := B) n ((algebraMap A B) a)
    _ = (algebraMap (ResidueField A) (ResidueField B))
          (residueField_quotient_pow_maximalIdeal_equiv (R := A) n
            (residue (A ⧸ maximalIdeal A ^ (n + 1)) (qA a))) := by
        -- Finally compare with the original residue-field map on `A → B`.
        rw [residueField_quotient_pow_maximalIdeal_equiv_apply_residue]
        simpa using (IsLocalRing.ResidueField.map_residue (f := algebraMap A B) (r := a))

/-- Helper for Lemma 15.116.12: after choosing a residue-field section on the source local ring,
the induced residue map on the target local ring agrees with the canonical residue-field map even
when source and target live in different universes. -/
lemma residueField_target_residue_comp_eq_map_mixed_universes
    {R : Type*} [CommRing R] [IsLocalRing R]
    {S : Type*} [CommRing S] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (σ : ResidueField R →+* R)
    (hσ : (residue R).comp σ = RingHom.id (ResidueField R)) :
    (residue S).comp ((algebraMap R S).comp σ) = ResidueField.map (algebraMap R S) := by
  -- Evaluate both ring homomorphisms on residue classes and compare them through
  -- `ResidueField.map_residue`.
  ext x
  calc
    residue S ((algebraMap R S) (σ x))
        = ResidueField.map (algebraMap R S) ((residue R) (σ x)) := by
            simpa using (ResidueField.map_residue (f := algebraMap R S) (r := σ x)).symm
    _ = ResidueField.map (algebraMap R S) x := by
          have hx : residue R (σ x) = x := DFunLike.congr_fun hσ x
          simpa [hx]

/-- Helper for Lemma 15.116.12: the compatibility clause of Lemma `15.116.10` remains valid for
source and target local rings in different universes. This is the quotient-level bridge needed in
the proof of Lemma `15.116.12`. -/
theorem exists_compatible_residueField_section_of_isNilpotent_maximalIdeal_mixed_universes
    {R : Type*} [CommRing R] [IsLocalRing R]
    {S : Type*} [CommRing S] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (h_nil' : IsNilpotent (maximalIdeal S))
    (σ : ResidueField R →+* R)
    (hσ : (residue R).comp σ = RingHom.id (ResidueField R))
    [Algebra.IsSeparableOver (ResidueField R) (ResidueField S)] :
    ∃ σ' : ResidueField S →+* S,
      (residue S).comp σ' = RingHom.id (ResidueField S) ∧
        σ'.comp (ResidueField.map (algebraMap R S)) = (algebraMap R S).comp σ := by
  -- Keep the canonical residue-field algebra while giving `S` the theorem-local algebra
  -- structure induced by the chosen section `σ`.
  let κS_alg : Algebra (ResidueField R) (ResidueField S) := inferInstance
  let κS_sep : Algebra.IsSeparableOver (ResidueField R) (ResidueField S) := inferInstance
  letI : Algebra (ResidueField R) S := ((algebraMap R S).comp σ).toAlgebra
  letI : Algebra (ResidueField R) (ResidueField S) := κS_alg
  letI : Algebra.IsSeparableOver (ResidueField R) (ResidueField S) := κS_sep
  letI : Algebra.FormallySmooth (ResidueField R) (ResidueField S) :=
    Algebra.formallySmooth_of_isSeparableOver
  let g : S →ₐ[ResidueField R] ResidueField S :=
    { toRingHom := residue S
      commutes' := DFunLike.congr_fun
        (residueField_target_residue_comp_eq_map_mixed_universes
          (R := R) (S := S) σ hσ) }
  have hS_alg :
      (algebraMap (ResidueField R) S : ResidueField R →+* S) = (algebraMap R S).comp σ := by
    simp [RingHom.algebraMap_toAlgebra]
  have hsurj : Function.Surjective g := by
    simpa [g] using (residue_surjective (R := S))
  have hker_nil : IsNilpotent (RingHom.ker (g : S →+* ResidueField S)) := by
    simpa [g, ker_residue] using h_nil'
  let τ : ResidueField S →ₐ[ResidueField R] S :=
    Algebra.FormallySmooth.liftOfSurjective (AlgHom.id (ResidueField R) (ResidueField S))
      g hsurj hker_nil
  have hτ_alg : g.comp τ = AlgHom.id (ResidueField R) (ResidueField S) :=
    Algebra.FormallySmooth.comp_liftOfSurjective
      (AlgHom.id (ResidueField R) (ResidueField S)) g hsurj hker_nil
  have hτ_ring : (residue S).comp τ.toRingHom = RingHom.id (ResidueField S) := by
    simpa [g] using congrArg AlgHom.toRingHom hτ_alg
  refine ⟨τ.toRingHom, hτ_ring, ?_⟩
  -- Compatibility is exactly `ResidueField R`-linearity of the lifted section.
  ext x
  calc
    τ ((ResidueField.map (algebraMap R S)) x)
        = τ ((algebraMap (ResidueField R) (ResidueField S)) x) := by
            rfl
    _ = (algebraMap (ResidueField R) S) x := τ.commutes x
    _ = ((algebraMap R S).comp σ) x := by rw [hS_alg]

/-- Helper for Lemma 15.116.12: the quotient residue-field extension
`ResidueField (B / maximalIdeal B^(n+1)) / ResidueField (A / maximalIdeal A^(n+1))` is separable
once the source intersection hypothesis makes the quotient residue field of `A` perfect. -/
lemma residueField_quotient_pow_maximalIdeal_isSeparableOver_of_pPowerIntersection
    [CharP A p] [CharP B p]
    (hAB : WeaklyUnramified A B) (n : ℕ)
    (hκ :
      (Set.range (algebraMap (ResidueField A) (ResidueField B)) : Set (ResidueField B)) =
        ⋂ n : ℕ+, Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ)))) :
    let α :
        A ⧸ maximalIdeal A ^ (n + 1) →+* B ⧸ maximalIdeal B ^ (n + 1) :=
      quotient_pow_maximalIdeal_map_of_weaklyUnramified (A := A) (B := B) hAB n
    let _ : Algebra (A ⧸ maximalIdeal A ^ (n + 1)) (B ⧸ maximalIdeal B ^ (n + 1)) := α.toAlgebra
    let _ : IsLocalHom (algebraMap (A ⧸ maximalIdeal A ^ (n + 1))
        (B ⧸ maximalIdeal B ^ (n + 1))) := by
      simpa [α, RingHom.algebraMap_toAlgebra] using
        (quotient_pow_maximalIdeal_localHom_of_weaklyUnramified
          (A := A) (B := B) hAB n)
    Algebra.IsSeparableOver
      (ResidueField (A ⧸ maximalIdeal A ^ (n + 1)))
      (ResidueField (B ⧸ maximalIdeal B ^ (n + 1))) := by
  let α :
      A ⧸ maximalIdeal A ^ (n + 1) →+* B ⧸ maximalIdeal B ^ (n + 1) :=
    quotient_pow_maximalIdeal_map_of_weaklyUnramified (A := A) (B := B) hAB n
  let _ : Algebra (A ⧸ maximalIdeal A ^ (n + 1)) (B ⧸ maximalIdeal B ^ (n + 1)) := α.toAlgebra
  letI : IsLocalHom (algebraMap (A ⧸ maximalIdeal A ^ (n + 1))
      (B ⧸ maximalIdeal B ^ (n + 1))) := by
    simpa [α, RingHom.algebraMap_toAlgebra] using
      (quotient_pow_maximalIdeal_localHom_of_weaklyUnramified
        (A := A) (B := B) hAB n)
  letI : CharP (ResidueField A) p := residueField_charP_of_charP (R := A) (p := p)
  letI : CharP (ResidueField B) p := residueField_charP_of_charP (R := B) (p := p)
  letI : CharP (A ⧸ maximalIdeal A ^ (n + 1)) p :=
    quotient_pow_maximalIdeal_charP (R := A) (p := p) n
  letI : CharP (ResidueField (A ⧸ maximalIdeal A ^ (n + 1))) p :=
    residueField_charP_of_charP
      (R := A ⧸ maximalIdeal A ^ (n + 1)) (p := p)
  letI : PerfectRing (ResidueField (A ⧸ maximalIdeal A ^ (n + 1))) p :=
    PerfectRing.ofSurjective
      (ResidueField (A ⧸ maximalIdeal A ^ (n + 1))) p
      (residueField_quotient_pow_maximalIdeal_perfect_of_pPowerIntersection
        (A := A) (B := B) (p := p) n hκ)
  letI : PerfectField (ResidueField (A ⧸ maximalIdeal A ^ (n + 1))) :=
    PerfectRing.toPerfectField (ResidueField (A ⧸ maximalIdeal A ^ (n + 1))) p
  -- Over a perfect base residue field, every field extension is separable.
  exact Algebra.IsSeparableOver.of_perfectField

/-- Helper for Lemma 15.116.12: for each quotient level `n`, the weakly unramified comparison
`A / maximalIdeal A^(n+1) → B / maximalIdeal B^(n+1)` admits compatible residue-field sections on
both sides. This fully discharges the quotient-section frontier of the source proof. -/
lemma exists_compatible_residue_sections_mod_maximalIdeal_power_of_weaklyUnramified
    [CharP A p] [CharP B p]
    (hAB : WeaklyUnramified A B) (n : ℕ)
    (hκ :
      (Set.range (algebraMap (ResidueField A) (ResidueField B)) : Set (ResidueField B)) =
        ⋂ n : ℕ+, Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ)))) :
    ∃ σA : ResidueField (A ⧸ maximalIdeal A ^ (n + 1)) →+*
        (A ⧸ maximalIdeal A ^ (n + 1)),
      (residue (A ⧸ maximalIdeal A ^ (n + 1))).comp σA =
          RingHom.id (ResidueField (A ⧸ maximalIdeal A ^ (n + 1))) ∧
      ∃ σB : ResidueField (B ⧸ maximalIdeal B ^ (n + 1)) →+*
          (B ⧸ maximalIdeal B ^ (n + 1)),
        (residue (B ⧸ maximalIdeal B ^ (n + 1))).comp σB =
            RingHom.id (ResidueField (B ⧸ maximalIdeal B ^ (n + 1))) ∧
          σB.comp
              (ResidueField.map
                (quotient_pow_maximalIdeal_map_of_weaklyUnramified
                  (A := A) (B := B) hAB n)) =
            (quotient_pow_maximalIdeal_map_of_weaklyUnramified
              (A := A) (B := B) hAB n).comp σA := by
  obtain ⟨σA, hσA⟩ :=
    exists_residueField_section_quotient_pow_maximalIdeal (R := A) (p := p) n
  let α :
      A ⧸ maximalIdeal A ^ (n + 1) →+* B ⧸ maximalIdeal B ^ (n + 1) :=
    quotient_pow_maximalIdeal_map_of_weaklyUnramified (A := A) (B := B) hAB n
  letI : Algebra (A ⧸ maximalIdeal A ^ (n + 1)) (B ⧸ maximalIdeal B ^ (n + 1)) := α.toAlgebra
  letI : CharP (ResidueField A) p := residueField_charP_of_charP (R := A) (p := p)
  letI : CharP (ResidueField B) p := residueField_charP_of_charP (R := B) (p := p)
  letI : IsLocalHom (algebraMap (A ⧸ maximalIdeal A ^ (n + 1))
      (B ⧸ maximalIdeal B ^ (n + 1))) := by
    simpa [α, RingHom.algebraMap_toAlgebra] using
      (quotient_pow_maximalIdeal_localHom_of_weaklyUnramified
        (A := A) (B := B) hAB n)
  letI :
      Algebra.IsSeparableOver
        (ResidueField (A ⧸ maximalIdeal A ^ (n + 1)))
        (ResidueField (B ⧸ maximalIdeal B ^ (n + 1))) :=
    by
      simpa [α, RingHom.algebraMap_toAlgebra] using
        (residueField_quotient_pow_maximalIdeal_isSeparableOver_of_pPowerIntersection
          (A := A) (B := B) (p := p) hAB n hκ)
  obtain ⟨σB, hσB, hcompat⟩ :=
    exists_compatible_residueField_section_of_isNilpotent_maximalIdeal_mixed_universes
      (R := A ⧸ maximalIdeal A ^ (n + 1))
      (S := B ⧸ maximalIdeal B ^ (n + 1))
      (quotient_pow_maximalIdeal_nilpotent (R := B) n) σA hσA
  refine ⟨σA, hσA, σB, hσB, ?_⟩
  -- Re-express the theorem-local algebra map as the canonical quotient comparison map.
  simpa [α, RingHom.algebraMap_toAlgebra] using hcompat

/-- Helper for Lemma 15.116.12: if a residue class misses some positive `p^n`-power slice, then
iteratively removing `p`th roots stops at a maximal factor that is not itself a `p`th power. -/
lemma exists_p_power_factorization_of_missing_slice
    {b : ResidueField B} :
    ∀ n : ℕ,
      b ∉ Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n + 1))) →
        ∃ r : ℕ, ∃ μ : ResidueField B, b = μ ^ (p ^ r) ∧
          μ ∉ Set.range (fun y : ResidueField B ↦ y ^ p)
  | 0, hmiss => by
      -- At the first slice, missing `p^1`-powers means precisely “not a `p`th power”.
      refine ⟨0, b, by simp, ?_⟩
      simpa using hmiss
  | n + 1, hmiss => by
      by_cases hroot : b ∈ Set.range (fun y : ResidueField B ↦ y ^ p)
      · rcases hroot with ⟨x, rfl⟩
        have hmiss' :
            x ∉ Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n + 1))) := by
          intro hx
          apply hmiss
          rcases hx with ⟨y, rfl⟩
          refine ⟨y, ?_⟩
          calc
            y ^ (p ^ (n + 2)) = y ^ ((p ^ (n + 1)) * p) := by
              simp [pow_succ', Nat.mul_comm]
            _ = (y ^ (p ^ (n + 1))) ^ p := by rw [pow_mul]
        rcases exists_p_power_factorization_of_missing_slice (b := x) n hmiss'
          with ⟨r, μ, hμ, hμ_not_p⟩
        refine ⟨r + 1, μ, ?_, hμ_not_p⟩
        -- Reinsert the removed Frobenius step into the factorization exponent.
        calc
          x ^ p = (μ ^ (p ^ r)) ^ p := by rw [hμ]
          _ = μ ^ ((p ^ r) * p) := by rw [pow_mul]
          _ = μ ^ (p ^ (r + 1)) := by simp [pow_succ', Nat.mul_comm]
      · -- If no `p`th root exists already, the maximal factorization stops immediately.
        exact ⟨0, b, by simp, hroot⟩

/-- Helper for Lemma 15.116.12: every residue class outside the image of `ResidueField A`
admits the maximal `p`-power factorization used to choose the weighted-maximal bad index in the
source induction. -/
lemma exists_maximal_p_power_factorization_of_not_mem_image_of_pPowerIntersection
    (hκ :
      (Set.range (algebraMap (ResidueField A) (ResidueField B)) : Set (ResidueField B)) =
        ⋂ n : ℕ+, Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ))))
    {b : ResidueField B}
    (hb : b ∉ Set.range (algebraMap (ResidueField A) (ResidueField B))) :
    ∃ r : ℕ, ∃ μ : ResidueField B, b = μ ^ (p ^ r) ∧
      μ ∉ Set.range (fun y : ResidueField B ↦ y ^ p) := by
  obtain ⟨n, hn⟩ :=
    exists_missing_pPower_slice_of_not_mem_image_of_pPowerIntersection
      (A := A) (B := B) (p := p) hκ hb
  let m : ℕ := Nat.pred (n : ℕ)
  have hm : m + 1 = (n : ℕ) := by
    dsimp [m]
    exact Nat.succ_pred_eq_of_pos n.pos
  have hn' :
      b ∉ Set.range (fun y : ResidueField B ↦ y ^ (p ^ (m + 1))) := by
    simpa [hm] using hn
  exact exists_p_power_factorization_of_missing_slice (B := B) (p := p) (b := b) m hn'

/-- Helper for Lemma 15.116.12: every discrete valuation ring admits a chosen generator of its
maximal ideal. This keeps the source proof's uniformizer choice local to the current file instead
of importing the heavier ramification package from earlier sections. -/
lemma exists_source_uniformizer_generator (R : Type*)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    ∃ π : R, Irreducible π ∧ maximalIdeal R = Ideal.span ({π} : Set R) := by
  -- Choose an irreducible element and read it as a uniformizer generator.
  obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible R
  refine ⟨π, hπirr, ?_⟩
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπirr

/-- Helper for Lemma 15.116.12: a nonempty finite family of bad indices has a weighted-maximal
element. This is the exact finite-set choice used in the source antichain branch before applying
Lemma `15.116.7`. -/
lemma exists_maximal_weighted_index
    (J : Finset ℕ) (w : ℕ → ℕ) (hJ : J.Nonempty) :
    ∃ j ∈ J, ∀ i ∈ J, w i ≤ w j := by
  classical
  obtain ⟨j, hjJ, hjmax⟩ := Finset.exists_max_image J w hJ
  exact ⟨j, hjJ, hjmax⟩

/-- Helper for Lemma 15.116.12: for a positive bad index `j`, one can choose a large enough
`p`-power shift so that the translated denominator `j * p^(r - r_j)` dominates any prescribed
bound `n`. This is the growth input used when picking the base-change degree in the source
antichain branch. -/
lemma exists_large_p_power_shift_of_positive_index
    {j rj n : ℕ} (hj : 0 < j) :
    ∃ r > rj, n < j * p ^ (r - rj) := by
  refine ⟨rj + (n + 1), Nat.lt_add_of_pos_right (Nat.succ_pos n), ?_⟩
  have hj_one : 1 ≤ j := Nat.succ_le_of_lt hj
  have hp_pow : n < p ^ (n + 1) := by
    exact lt_of_lt_of_le (Nat.lt_succ_self n) <|
      Nat.le_of_lt (Nat.lt_pow_self (n := n + 1) (a := p) (Nat.Prime.one_lt Fact.out))
  have hmul : p ^ (n + 1) ≤ j * p ^ (n + 1) := by
    simpa using Nat.mul_le_mul_right (p ^ (n + 1)) hj_one
  have hsub : (rj + (n + 1)) - rj = n + 1 := by
    exact Nat.add_sub_cancel_left rj (n + 1)
  exact lt_of_lt_of_le hp_pow (by simpa [hsub] using hmul)

/-- Helper for Lemma 15.116.12: under a weakly unramified extension of discrete valuation rings,
the image of a chosen source uniformizer still generates the target maximal ideal. -/
lemma source_uniformizer_image_generates_maximalIdeal_of_weaklyUnramified
    (hAB : WeaklyUnramified A B)
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A)) :
    maximalIdeal B = Ideal.span ({algebraMap A B π} : Set B) := by
  -- Weakly unramifiedness identifies the target maximal ideal with the image of the source one.
  have hmap :
      Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B := by
    exact (weaklyUnramified_iff_map_maximalIdeal (A := A) (B := B)).mp hAB
  calc
    maximalIdeal B = Ideal.map (algebraMap A B) (maximalIdeal A) := hmap.symm
    _ = Ideal.map (algebraMap A B) (Ideal.span ({π} : Set A)) := by rw [hπ]
    _ = Ideal.span ({algebraMap A B π} : Set B) := by
      rw [Ideal.map_span]
      simp

/-- Helper for Lemma 15.116.12: every Artin-Schreier parameter in the fraction field of `B`
admits some denominator power of the chosen source uniformizer after a weakly unramified base
step `A ⊆ B`. -/
lemma exists_pole_order_of_artin_schreier_parameter
    (hAB : WeaklyUnramified A B)
    (ξ : L)
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A)) :
    ∃ n : ℕ, ∃ b : B, algebraMap B L b = (algebraMap A L π) ^ n * ξ := by
  let πB : B := algebraMap A B π
  have hπB :
      maximalIdeal B = Ideal.span ({πB} : Set B) := by
    -- First transport the chosen source uniformizer across the weakly unramified step.
    simpa [πB] using
      source_uniformizer_image_generates_maximalIdeal_of_weaklyUnramified
        (A := A) (B := B) hAB π hπ
  obtain ⟨⟨c, d⟩, hfrac⟩ := IsLocalization.surj (nonZeroDivisors B) ξ
  have hd_ne_zero : (d : B) ≠ 0 := by
    exact mem_nonZeroDivisors_iff_ne_zero.mp d.2
  obtain ⟨n, hd_assoc⟩ :=
    associated_uniformizer_pow_of_nonzero (R := B) πB (d : B) hπB hd_ne_zero
  rcases hd_assoc with ⟨u, hu⟩
  refine ⟨n, c * (u : B), ?_⟩
  have hfrac_mul :
      algebraMap B L c = ξ * algebraMap B L d := by
    simpa using hfrac.symm
  -- Replace the arbitrary nonzero localization denominator by a power of the chosen uniformizer.
  calc
    algebraMap B L (c * (u : B))
        = algebraMap B L c * algebraMap B L (u : B) := by
            simp
    _ = (ξ * algebraMap B L d) * algebraMap B L (u : B) := by
          rw [hfrac_mul]
    _ = ξ * (algebraMap B L d * algebraMap B L (u : B)) := by ring
    _ = ξ * algebraMap B L ((d : B) * (u : B)) := by
          simp
    _ = ξ * algebraMap B L (πB ^ n) := by
          rw [hu]
    _ = ξ * (algebraMap B L πB) ^ n := by
          simp
    _ = ξ * (algebraMap A L π) ^ n := by
          rw [show algebraMap B L πB = algebraMap A L π by
            simp [πB, IsScalarTower.algebraMap_eq A B L]]
    _ = (algebraMap A L π) ^ n * ξ := by ring

/-- Helper for Lemma 15.116.12: among all denominator powers clearing the Artin-Schreier
parameter, there is a least pole order. This is the exact source invariant used to split off the
integral branch `n = 0` from the positive-order normalization branch. -/
lemma exists_minimal_pole_order_of_artin_schreier_parameter
    (hAB : WeaklyUnramified A B)
    (ξ : L)
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A)) :
    ∃ n : ℕ, ∃ b : B,
      algebraMap B L b = (algebraMap A L π) ^ n * ξ ∧
      ∀ m : ℕ, m < n →
        ¬ ∃ b' : B, algebraMap B L b' = (algebraMap A L π) ^ m * ξ := by
  classical
  let clearsPole : ℕ → Prop :=
    fun n ↦ ∃ b : B, algebraMap B L b = (algebraMap A L π) ^ n * ξ
  have hclears : ∃ n : ℕ, clearsPole n := by
    -- The preceding denominator-clearing lemma supplies at least one admissible pole order.
    simpa [clearsPole] using
      exists_pole_order_of_artin_schreier_parameter
        (A := A) (B := B) (L := L) hAB ξ π hπ
  refine ⟨Nat.find hclears, ?_⟩
  rcases Nat.find_spec hclears with ⟨b, hb⟩
  refine ⟨b, hb, ?_⟩
  intro m hm hsmaller
  -- Any strictly smaller denominator power contradicts the minimality of `Nat.find`.
  have hle : Nat.find hclears ≤ m := Nat.find_min' hclears hsmaller
  exact (not_lt_of_ge hle) hm

/-- Helper for Lemma 15.116.12: once the Artin-Schreier generator, the source uniformizer, the
maximal `p`-power factorizations in the residue field, and the compatible quotient sections are
fixed, the remaining source proof is exactly the minimal-pole expansion, bad-index antichain
reduction, and the two terminal branch arguments. -/
lemma exists_totallyRamified_galois_weakSolution_of_artin_schreier_generator_and_source_uniformizer
    (hAB : WeaklyUnramified A B)
    (ξ : L) (z : M)
    (hz : z ^ p - z = algebraMap L M ξ)
    (hgen : L⟮z⟯ = ⊤)
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    (hκ_factor :
      ∀ {b : ResidueField B},
        b ∉ Set.range (algebraMap (ResidueField A) (ResidueField B)) →
          ∃ r : ℕ, ∃ μ : ResidueField B, b = μ ^ (p ^ r) ∧
            μ ∉ Set.range (fun y : ResidueField B ↦ y ^ p))
    (hquot_sections :
      ∀ n : ℕ,
        ∃ σA : ResidueField (A ⧸ maximalIdeal A ^ (n + 1)) →+*
            (A ⧸ maximalIdeal A ^ (n + 1)),
          (residue (A ⧸ maximalIdeal A ^ (n + 1))).comp σA =
              RingHom.id (ResidueField (A ⧸ maximalIdeal A ^ (n + 1))) ∧
          ∃ σB : ResidueField (B ⧸ maximalIdeal B ^ (n + 1)) →+*
              (B ⧸ maximalIdeal B ^ (n + 1)),
            (residue (B ⧸ maximalIdeal B ^ (n + 1))).comp σB =
                RingHom.id (ResidueField (B ⧸ maximalIdeal B ^ (n + 1))) ∧
              σB.comp
                  (ResidueField.map
                    (quotient_pow_maximalIdeal_map_of_weaklyUnramified
                      (A := A) (B := B) hAB n)) =
                (quotient_pow_maximalIdeal_map_of_weaklyUnramified
                  (A := A) (B := B) hAB n).comp σA) :
    ∃ (K1 : Type (max u v w x y z)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
        IsGalois K K1 ∧
          (let _ : FaithfulSMul A K1 := FaithfulSMul.of_field_isFractionRing A K1 K K1
           let _ : Algebra (FractionRing A) K1 := FractionRing.liftAlgebra A K1
           let _ : IsScalarTower A (FractionRing A) K1 :=
             FractionRing.isScalarTower_liftAlgebra A K1
           IsTotallyRamifiedWithRespectTo A K1) ∧
          IsWeakSolutionFor A C K M K1 := by
  obtain ⟨n, b0, hb0, hn_min⟩ :=
    exists_minimal_pole_order_of_artin_schreier_parameter
      (A := A) (B := B) (L := L) hAB ξ π hπ
  rcases n with _ | n
  · -- Route correction: the integral branch `n = 0` should now close directly from the source
    -- Artin-Schreier unramified case over `B`, before any coefficient normalization is attempted.
    -- TODO: rewrite `hb0` as `ξ ∈ algebraMap B L (Set.range id)` and identify the resulting
    -- unramified/trivial Artin-Schreier branch with a weak solution for `A → C`.
    sorry
  · -- The positive-order branch is the exact remaining source frontier.
    -- TODO: use `hquot_sections (n + 1)` and `hn_min` to extract the minimal-order pole
    -- expansion, run the bad-index induction on the finite set of coefficients outside the image
    -- of `ResidueField A`, and finish via the good-coefficient and antichain terminal branches.
    sorry

-- Proof sketch: choose an Artin-Schreier generator for the degree-`p` Galois extension `M / L`,
-- apply the ramification trichotomy over `B`, and use the hypothesis on
-- `⋂_{n ≥ 1} (ResidueField B)^(p^n)` together with the totally ramified degree-`p^r` extensions
-- from Lemma `15.116.7` to eliminate the bad residue terms inductively until the base change over
-- `C` becomes weakly unramified.
/-- Lemma 15.116.12: let `A ⊆ B ⊆ C` be extensions of discrete valuation rings with fraction
fields `K ⊆ L ⊆ M`. Assume `A ⊆ B` is weakly unramified, `K` has characteristic `p`, `M / L` is
a degree-`p` Galois extension, and the image of `ResidueField A` in `ResidueField B` is exactly
the intersection of the subsets of `p^n`-powers in `ResidueField B`. Then there exists a finite
Galois extension `K₁ / K`, totally ramified with respect to `A`, which is a weak solution for the
extension `A → C`. -/
theorem exists_totallyRamified_galois_weakSolution_of_degree_p_galois_extension
    (hAB : WeaklyUnramified A B)
    (hLM : Module.finrank L M = p)
    (hκ :
      (Set.range (algebraMap (ResidueField A) (ResidueField B)) : Set (ResidueField B)) =
        ⋂ n : ℕ+, Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ)))) :
    ∃ (K1 : Type (max u v w x y z)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
        IsGalois K K1 ∧
          (let _ : FaithfulSMul A K1 := FaithfulSMul.of_field_isFractionRing A K1 K K1
           let _ : Algebra (FractionRing A) K1 := FractionRing.liftAlgebra A K1
           let _ : IsScalarTower A (FractionRing A) K1 :=
             FractionRing.isScalarTower_liftAlgebra A K1
           IsTotallyRamifiedWithRespectTo A K1) ∧
          IsWeakSolutionFor A C K M K1 := by
  -- Route correction: first install the source-faithful Artin-Schreier presentation of `M / L`;
  -- the remaining work is the pole-order normalization and bad-index induction from the source.
  obtain ⟨ξ, z, hz, hgen⟩ :=
    exists_artin_schreier_generator_of_galois_prime_degree (k := K) (hLM := hLM)
  have hκ_allSlices :
      ∀ {b : ResidueField B},
        b ∈ Set.range (algebraMap (ResidueField A) (ResidueField B)) →
          ∀ n : ℕ+, b ∈ Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ))) :=
    fun {b} hb ↦
      mem_pPower_range_of_mem_image_of_pPowerIntersection (A := A) (B := B) (p := p) hκ hb
  have hκ_missingSlice :
      ∀ {b : ResidueField B},
        b ∉ Set.range (algebraMap (ResidueField A) (ResidueField B)) →
          ∃ n : ℕ+, b ∉ Set.range (fun y : ResidueField B ↦ y ^ (p ^ (n : ℕ))) :=
    fun {b} hb ↦
      exists_missing_pPower_slice_of_not_mem_image_of_pPowerIntersection
        (A := A) (B := B) (p := p) hκ hb
  let _ : CharP A p :=
    RingHom.charP (algebraMap A K) (IsFractionRing.injective A K) p
  let _ : CharP (ResidueField A) p :=
    CharP.quotient' p (maximalIdeal A) fun n hn ↦ by
      by_contra hnat
      have hnotunit : ¬ IsUnit (n : A) := by
        simpa [IsLocalRing.mem_maximalIdeal] using hn
      have hnotdvd : ¬ p ∣ n := by
        simpa [CharP.cast_eq_zero_iff A p n] using hnat
      exact hnotunit ((CharP.isUnit_natCast_iff (R := A) (p := p) (Fact.out)).2 hnotdvd)
  let _ : CharP L p :=
    charP_of_injective_algebraMap (R := K) (A := L) (algebraMap K L).injective p
  let _ : CharP B p :=
    RingHom.charP (algebraMap B L) (IsFractionRing.injective B L) p
  let _ : CharP (ResidueField B) p :=
    CharP.quotient' p (maximalIdeal B) fun n hn ↦ by
      by_contra hnat
      have hnotunit : ¬ IsUnit (n : B) := by
        simpa [IsLocalRing.mem_maximalIdeal] using hn
      have hnotdvd : ¬ p ∣ n := by
        simpa [CharP.cast_eq_zero_iff B p n] using hnat
      exact hnotunit ((CharP.isUnit_natCast_iff (R := B) (p := p) (Fact.out)).2 hnotdvd)
  have hκ_perfect :
      ∀ a : ResidueField A, ∃ b : ResidueField A, b ^ p = a :=
    residueField_perfect_of_pPowerIntersection (A := A) (B := B) (p := p) hκ
  have hκ_separable :
      Algebra.IsSeparableOver (ResidueField A) (ResidueField B) :=
    residueField_isSeparableOver_of_pPowerIntersection (A := A) (B := B) (p := p) hκ
  have hκ_factor :
      ∀ {b : ResidueField B},
        b ∉ Set.range (algebraMap (ResidueField A) (ResidueField B)) →
          ∃ r : ℕ, ∃ μ : ResidueField B, b = μ ^ (p ^ r) ∧
            μ ∉ Set.range (fun y : ResidueField B ↦ y ^ p) :=
    fun {b} hb ↦
      exists_maximal_p_power_factorization_of_not_mem_image_of_pPowerIntersection
        (A := A) (B := B) (p := p) hκ hb
  have hκ_quot_perfect :
      ∀ n : ℕ, ∀ a : ResidueField (A ⧸ maximalIdeal A ^ (n + 1)),
        ∃ b : ResidueField (A ⧸ maximalIdeal A ^ (n + 1)), b ^ p = a :=
    fun n ↦
      residueField_quotient_pow_maximalIdeal_perfect_of_pPowerIntersection
        (A := A) (B := B) (p := p) n hκ
  have hquot_local :
      ∀ n : ℕ,
        IsLocalHom
          (quotient_pow_maximalIdeal_map_of_weaklyUnramified (A := A) (B := B) hAB n) :=
    fun n ↦
      quotient_pow_maximalIdeal_localHom_of_weaklyUnramified
        (A := A) (B := B) hAB n
  have hquot_residue_transport :
      ∀ n : ℕ,
        (residueField_quotient_pow_maximalIdeal_equiv (R := B) n).toRingHom.comp
            (ResidueField.map
              (quotient_pow_maximalIdeal_map_of_weaklyUnramified (A := A) (B := B) hAB n)) =
          (algebraMap (ResidueField A) (ResidueField B)).comp
            (residueField_quotient_pow_maximalIdeal_equiv (R := A) n).toRingHom :=
    fun n ↦
      residueField_map_quotient_pow_maximalIdeal_transport
        (A := A) (B := B) hAB n
  have hquot_sections :
      ∀ n : ℕ,
        ∃ σA : ResidueField (A ⧸ maximalIdeal A ^ (n + 1)) →+*
            (A ⧸ maximalIdeal A ^ (n + 1)),
          (residue (A ⧸ maximalIdeal A ^ (n + 1))).comp σA =
              RingHom.id (ResidueField (A ⧸ maximalIdeal A ^ (n + 1))) ∧
          ∃ σB : ResidueField (B ⧸ maximalIdeal B ^ (n + 1)) →+*
              (B ⧸ maximalIdeal B ^ (n + 1)),
            (residue (B ⧸ maximalIdeal B ^ (n + 1))).comp σB =
                RingHom.id (ResidueField (B ⧸ maximalIdeal B ^ (n + 1))) ∧
              σB.comp
                  (ResidueField.map
                    (quotient_pow_maximalIdeal_map_of_weaklyUnramified
                      (A := A) (B := B) hAB n)) =
                (quotient_pow_maximalIdeal_map_of_weaklyUnramified
                  (A := A) (B := B) hAB n).comp σA :=
    fun n ↦
      exists_compatible_residue_sections_mod_maximalIdeal_power_of_weaklyUnramified
        (A := A) (B := B) (p := p) hAB n hκ
  obtain ⟨π, _, hπ⟩ := exists_source_uniformizer_generator A
  -- Route correction: the theorem is now reduced to the exact source frontier after the
  -- Artin-Schreier presentation and the quotient-section package. The remaining blocker is the
  -- minimal-pole expansion plus bad-index induction, not the preliminary residue-field setup.
  exact
    exists_totallyRamified_galois_weakSolution_of_artin_schreier_generator_and_source_uniformizer
      (A := A) (B := B) (C := C) (K := K) (L := L) (M := M) (p := p) (hAB := hAB)
      ξ z hz hgen π hπ (fun {b} hb ↦ hκ_factor hb) hquot_sections

end
