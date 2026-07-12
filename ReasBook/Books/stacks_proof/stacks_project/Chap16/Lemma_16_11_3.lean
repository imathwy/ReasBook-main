import Mathlib
import StacksProject_2024.Chap10.Lemma_10_144_3
import StacksProject_2024.Chap10.Lemma_10_159_1
import StacksProject_2024.Chap10.Lemma_10_101_8_Crit_re_de_platitude_par_fibres_Nilpotent_case
import StacksProject_2024.Chap10.Definition_10_137_10
import StacksProject_2024.Chap10.Lemma_10_97_7
import StacksProject_2024.Chap10.Lemma_10_153_10
import StacksProject_2024.Chap10.Lemma_10_153_11
import StacksProject_2024.Chap15.Lemma_15_116_10
import StacksProject_2024.Chap15.Lemma_15_116_12

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing

universe u v w x

namespace RingHom

/-- Helper for Lemma 16.11.3: the source-facing smoothness condition for a ring homomorphism is
the smoothness predicate of its induced algebra map. -/
def SmoothAtPrime {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S)
    (q : PrimeSpectrum S) : Prop :=
  let _ : Algebra R S := f.toAlgebra
  Algebra.SmoothAtPrime R S q

end RingHom

namespace Algebra

section

variable {k : Type u} [Field k]
variable {Λ : Type v} [CommRing Λ] [Algebra k Λ]
variable {m : ℕ} {φ : MvPolynomial (Fin m) k →ₐ[k] Λ}
variable {𝔮 : Ideal Λ} [𝔮.IsPrime] {n : ℕ}
variable {D : Type w} [CommRing D] [IsArtinianRing D] [IsLocalRing D]

/- Domain-style sampling for Lemma 16.11.3.

Primary domain: refinement of local Artinian approximation factorizations in commutative algebra by
adjoining a power of a chosen element through an essentially smooth local Artinian extension.

Sampled owner declarations in the surrounding project/mathlib style:
* `Localization.localRingHom` and `Ideal.quotientMap` for the primitive localized factorization
  data `k[y]_(φ⁻¹(𝔮)) / 𝔪(k[y]_(φ⁻¹(𝔮)))^n → D → Λ_𝔮 / 𝔪(Λ_𝔮)^n`;
* `Algebra.SmoothAtPrime` for the essentially smooth source map and `SmoothAtPrime` for the
  essentially smooth refinement map `D → D'` at the closed point of the local Artinian target;
* object-prefix flatness owners `f.Flat` for the localized source map and the final map
  `D' → Λ_𝔮 / (𝔮 Λ_𝔮)^n`;
* `Ideal.Quotient.mk` for the canonical image of `λ ^ q` in the localized quotient target.

Best owner abstraction: this item is source-facing existential output built directly on the
primitive factorization data and hypotheses from Lemma `16.11.2`; the refinement data
`D'`, `D → D'`, and `D' → Λ_𝔮 / (𝔮 Λ_𝔮)^n` are theorem output, not a second packaged owner.

Primitive-vs-derived split:
* primitive input data: the maps `sourceToD`, `DToTarget`, and the flatness, smoothness, and
  quotient-factorization hypotheses from Lemma `16.11.2`, together with the chosen element
  `l : Λ`;
* derived output data: the refined local Artinian ring `D'`, the maps `D → D' → target`, the
  factorization identity, the closed-point smoothness and flatness properties, and a witness that
  the image of `l ^ q` lies in the image of `D'`.

Source/core/bridge triage:
* `source-facing`: the existence of a refined factorization adjoining a positive power of `l`;
* `core/canonical`: `Localization.localRingHom`, `Ideal.comap φ.toRingHom 𝔮`,
  `Ideal.quotientMap`, `Algebra.SmoothAtPrime`, `SmoothAtPrime`, object-prefix flatness owners
  `f.Flat`, and `Ideal.Quotient.mk`;
* `bridge/view`: the explicit witness `z : D'` whose image is the class of `l ^ q`.

This rewrite targets the `source-facing` layer: the theorem should expose the refined factorization
directly from the localized factorization hypotheses, rather than through a one-off wrapper that
duplicates theorem-output fields.
-/

local notation:max "Λ_" 𝔮 => Localization.AtPrime 𝔮
local notation:max "Target" => ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n)
local notation:max "Source" => Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)
local notation:max "SourceQuot" => Source ⧸ (maximalIdeal Source) ^ n
local notation:max "localMap" =>
  Localization.localRingHom (Ideal.comap φ.toRingHom 𝔮) 𝔮 φ.toRingHom rfl
local notation:max "targetMap" =>
  Ideal.quotientMap
    ((maximalIdeal (Λ_ 𝔮)) ^ n)
    localMap
    (pow_maximalIdeal_le_comap_pow_maximalIdeal localMap n)

variable {sourceToD : SourceQuot →+* D}
variable {DToTarget : D →+* Target}

variable {p : ℕ} [Fact p.Prime] [CharP k p]
variable [IsNoetherianRing Λ]

-- Proof sketch: let `λ̄` be the image of `λ` in `Λ_𝔮 / (𝔮 Λ_𝔮)^n` and let `F` be the residue
-- field of `D`. If the residue class of `λ` already lies in `F`, a suitable `p`-power places
-- `λ̄` in `D`. If it is transcendental over `F`, adjoin `λ̄` and localize, which gives a
-- polynomial and hence essentially smooth extension. If it is algebraic, replace it by a suitable
-- `p`-power with separable residue-field image, use the henselian local rings from Lemma
-- `10.153.10` and the finite étale lifting statement of Lemma `10.153.7` to construct `D'`, and
-- then apply the first case inside `D'`.
/-- Helper for Lemma 16.11.3: every positive power of the maximal ideal in a local ring is proper,
so the corresponding quotient is nontrivial. -/
private theorem quotient_pow_maximalIdeal_ne_top_local
    {R : Type*} [CommRing R] [IsLocalRing R] (r : ℕ) :
    maximalIdeal R ^ (r + 1) ≠ (⊤ : Ideal R) := by
  intro hpow
  have htop : (⊤ : Ideal R) ≤ maximalIdeal R := by
    calc
      (⊤ : Ideal R) = maximalIdeal R ^ (r + 1) := hpow.symm
      _ ≤ maximalIdeal R := Ideal.pow_le_self (I := maximalIdeal R) (Nat.succ_ne_zero r)
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp htop)

/-- Helper for Lemma 16.11.3: quotienting `Λ_𝔮` by a positive power of its maximal ideal remains
nontrivial. -/
private theorem targetQuotient_nontrivial_of_pos (hn : 1 ≤ n) : Nontrivial Target := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact Ideal.Quotient.nontrivial_iff.2 <| by
    simpa [Nat.add_comm] using
      (quotient_pow_maximalIdeal_ne_top_local (R := Λ_ 𝔮) r)

/-- Helper for Lemma 16.11.3: the positive-power quotient of `Λ_𝔮` is a local ring. -/
private theorem targetQuotient_isLocalRing_of_pos (hn : 1 ≤ n) : IsLocalRing Target := by
  let _ : Nontrivial Target := targetQuotient_nontrivial_of_pos (n := n) hn
  -- The quotient map from a local ring onto a nontrivial quotient preserves locality.
  exact
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk ((maximalIdeal (Λ_ 𝔮)) ^ n))
      Ideal.Quotient.mk_surjective

/-- Helper for Lemma 16.11.3: the positive-power quotient of `Λ_𝔮` is Artinian. -/
private theorem targetQuotient_isArtinianRing_of_pos (hn : 1 ≤ n) :
    IsArtinianRing Target := by
  let _ : IsLocalRing Target := targetQuotient_isLocalRing_of_pos (n := n) hn
  let _ : IsNoetherianRing (Localization.AtPrime 𝔮) :=
    IsLocalization.isNoetherianRing 𝔮.primeCompl (Localization.AtPrime 𝔮) inferInstance
  let _ : IsNoetherianRing Target := inferInstance
  let π : Localization.AtPrime 𝔮 →+* Target :=
    Ideal.Quotient.mk ((maximalIdeal (Localization.AtPrime 𝔮)) ^ n)
  -- The quotient maximal ideal is nilpotent because we quotient by its `n`th power.
  refine (isArtinianRing_iff_isNilpotent_maximalIdeal (R := Target)).mpr ?_
  refine ⟨n, ?_⟩
  have hmax :
      maximalIdeal Target = Ideal.map π (maximalIdeal (Λ_ 𝔮)) := by
    symm
    exact IsLocalRing.map_maximalIdeal_of_surjective π Ideal.Quotient.mk_surjective
  calc
    maximalIdeal Target ^ n = Ideal.map π (maximalIdeal (Λ_ 𝔮)) ^ n := by
      rw [hmax]
    _ = Ideal.map π (maximalIdeal (Λ_ 𝔮) ^ n) := by
      rw [Ideal.map_pow]
    _ = ⊥ := by
      exact (Ideal.map_eq_bot_iff_le_ker π).2 (by simpa [π, Ideal.mk_ker])

/-- Helper for Lemma 16.11.3: the positive-power quotient of `Λ_𝔮` is henselian because it is a
zero-dimensional local Artinian ring. -/
private theorem targetQuotient_henselian_of_pos (hn : 1 ≤ n) :
    HenselianLocalRing Target := by
  let _ : IsLocalRing Target := targetQuotient_isLocalRing_of_pos (n := n) hn
  let _ : IsArtinianRing Target := targetQuotient_isArtinianRing_of_pos (n := n) hn
  let _ : Ring.KrullDimLE 0 Target := inferInstance
  exact localRing_henselian_of_krullDimLE_zero Target

/-- Helper for Lemma 16.11.3: if `λ̄` lies in the maximal ideal of the positive target quotient,
then a positive power of `λ̄` is already zero, hence already comes from `D`. -/
private theorem exists_powerInImage_of_residueZero
    [Nontrivial Target] [IsLocalRing Target] [IsArtinianRing Target]
    {lbar : Target} (hlbar_mem : lbar ∈ maximalIdeal Target) :
    ∃ q : ℕ, 0 < q ∧ ∃ z : D, DToTarget z = lbar ^ q := by
  have hnil : IsNilpotent (maximalIdeal Target) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal (R := Target)).mp inferInstance
  rcases hnil with ⟨q, hqpow⟩
  have hlbar_pow_mem : lbar ^ (q + 1) ∈ maximalIdeal Target ^ q := by
    have hlbar_pow_mem_high : lbar ^ (q + 1) ∈ maximalIdeal Target ^ (q + 1) := by
      simpa using (Ideal.pow_mem_pow hlbar_mem (q + 1))
    exact (Ideal.pow_le_pow_right (I := maximalIdeal Target) (Nat.le_succ q)) hlbar_pow_mem_high
  have hlbar_pow_zero : lbar ^ (q + 1) = 0 := by
    -- Proof comment: the Artinian nilpotence exponent kills the chosen power of `lbar`.
    have hzero_mem : lbar ^ (q + 1) ∈ (0 : Ideal Target) := hqpow ▸ hlbar_pow_mem
    exact Ideal.mem_bot.mp hzero_mem
  refine ⟨q + 1, Nat.succ_pos q, 0, ?_⟩
  rw [hlbar_pow_zero, map_zero]

/-- Helper for Lemma 16.11.3: a nilpotent element in a nontrivial ring cannot be a unit. -/
private theorem not_isUnit_of_isNilpotent
    {R : Type*} [CommRing R] [Nontrivial R] {x : R} (hx : IsNilpotent x) :
    ¬ IsUnit x := by
  intro hx_unit
  rcases hx with ⟨n, hn⟩
  have hpow_unit : IsUnit (x ^ n) := hx_unit.pow n
  rw [hn] at hpow_unit
  rcases hpow_unit with ⟨u, hu⟩
  have hzero : (0 : R) = 1 := by
    simpa [hu] using u.mul_inv
  exact zero_ne_one hzero

/-- Helper for Lemma 16.11.3: elements of the maximal ideal of an Artinian local ring are
nilpotent. -/
private theorem isNilpotent_of_mem_maximalIdeal_of_artinianLocal
    {R : Type*} [CommRing R] [IsArtinianRing R] [IsLocalRing R]
    {x : R} (hx : x ∈ maximalIdeal R) :
    IsNilpotent x := by
  obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal (R := R)).mp inferInstance
  refine ⟨n, ?_⟩
  -- Proof comment: Artinianity kills a high enough power of the maximal ideal, hence a high
  -- enough power of every element lying in it.
  have hxpow : x ^ n ∈ maximalIdeal R ^ n := Ideal.pow_mem_pow hx n
  rw [hn] at hxpow
  exact Ideal.mem_bot.mp hxpow

/-- Helper for Lemma 16.11.3: every ring map from an Artinian local ring to a nontrivial local
ring is a local homomorphism. -/
private theorem ringHom_isLocalHom_of_artinianLocal_to_local
    {R : Type*} {S : Type*}
    [CommRing R] [IsArtinianRing R] [IsLocalRing R]
    [CommRing S] [Nontrivial S] [IsLocalRing S]
    (f : R →+* S) :
    IsLocalHom f := by
  refine IsLocalHom.mk ?_
  intro x hx_unit
  by_contra hx_nonunit
  have hx_mem : x ∈ maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hx_nonunit
  have hx_nil : IsNilpotent x :=
    isNilpotent_of_mem_maximalIdeal_of_artinianLocal hx_mem
  have hfx_nil : IsNilpotent (f x) := by
    rcases hx_nil with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [map_pow] using congrArg f hn
  -- Proof comment: if `x` were a nonunit, its image would be nilpotent, hence also a nonunit,
  -- contradicting the assumed unit image.
  exact (not_isUnit_of_isNilpotent hfx_nil) hx_unit

/-- Helper for Lemma 16.11.3: if the residue class of `lbar` already lies in the image of the
canonical residue-field map `ResidueField D → ResidueField Target`, then some positive `p`-power
of `lbar` already lies in the image of `D`. -/
private theorem exists_powerInImage_of_residueMemRange
    [Nontrivial Target] [IsLocalRing Target] [IsArtinianRing Target] [CharP D p] [CharP Target p]
    (DToTarget : D →+* Target) {lbar : Target}
    (hlocal : IsLocalHom DToTarget)
    (hamem : residue Target lbar ∈ Set.range (ResidueField.map DToTarget)) :
    ∃ q : ℕ, 0 < q ∧ ∃ z : D, DToTarget z = lbar ^ q := by
  let _ : IsLocalHom DToTarget := hlocal
  have hnilD : IsNilpotent (maximalIdeal D) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal (R := D)).mp inferInstance
  obtain ⟨σ, hσ⟩ :=
    exists_residueField_section_of_isNilpotent_maximalIdeal (A := D) (p := p) hnilD
  rcases hamem with ⟨β, hβ⟩
  let y : D := σ β
  have hy_res :
      residue Target (DToTarget y) = residue Target lbar := by
    -- Proof comment: the chosen residue-field section lifts the residue representative `β`.
    calc
      residue Target (DToTarget y)
          = ResidueField.map DToTarget (residue D y) := by
              simpa using (ResidueField.map_residue (f := DToTarget) (r := y)).symm
      _ = ResidueField.map DToTarget β := by
            have hy : residue D y = β := DFunLike.congr_fun hσ β
            simpa [y] using congrArg (ResidueField.map DToTarget) hy
      _ = residue Target lbar := hβ
  let δ : Target := lbar - DToTarget y
  have hδ_mem : δ ∈ maximalIdeal Target := by
    -- Proof comment: after subtracting the lifted residue representative, only a nilpotent
    -- maximal-ideal error remains.
    have hδ_res : residue Target δ = 0 := by
      simp [δ, hy_res]
    simpa [δ, IsLocalRing.residue, IsLocalRing.ker_residue (R := Target)] using
      (Ideal.Quotient.eq_zero_iff_mem (I := maximalIdeal Target)).1 hδ_res
  obtain ⟨n, hn⟩ := isNilpotent_of_mem_maximalIdeal_of_artinianLocal hδ_mem
  let r : ℕ := (Nat.log p n).succ
  let q : ℕ := p ^ r
  have hn_le_q : n ≤ q := by
    -- Proof comment: a sufficiently large `p`-power dominates the nilpotence exponent.
    exact Nat.le_of_lt (by
      simpa [q, r] using Nat.lt_pow_succ_log_self (b := p) (Nat.Prime.one_lt Fact.out) n)
  have hδ_pow_zero : δ ^ q = 0 := by
    exact pow_eq_zero_of_le hn_le_q hn
  have hlbar_pow :
      lbar ^ q = (DToTarget y) ^ q + δ ^ q := by
    -- Proof comment: Frobenius kills the mixed terms in characteristic `p`.
    have hdecomp : DToTarget y + δ = lbar := by
      dsimp [δ]
      rw [add_sub_cancel]
    have hadd :
        (DToTarget y + δ) ^ (p ^ r) = (DToTarget y) ^ (p ^ r) + δ ^ (p ^ r) :=
      add_pow_char_pow (DToTarget y) δ p r
    calc
      lbar ^ q = (DToTarget y + δ) ^ q := by rw [← hdecomp]
      _ = (DToTarget y) ^ q + δ ^ q := by
        simpa [q] using hadd
  refine ⟨q, by
    exact pow_pos (Nat.Prime.pos Fact.out) _, y ^ q, ?_⟩
  -- Proof comment: the nilpotent error vanishes after the chosen `p`-power, so the remaining
  -- power is exactly the image of `y ^ q`.
  calc
    DToTarget (y ^ q) = (DToTarget y) ^ q := by simp [q]
    _ = (DToTarget y) ^ q + δ ^ q := by rw [hδ_pow_zero, add_zero]
    _ = lbar ^ q := hlbar_pow.symm

/-- Helper for Lemma 16.11.3: an algebraic residue-field element admits a `p`-power whose value
already lies in the separable closure of the simple extension that it generates. -/
private theorem exists_separablePower_in_simpleSeparableClosure
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]
    {p : ℕ} [Fact p.Prime] [CharP F p] {x : E} [Algebra.IsAlgebraic F E] :
    ∃ (E₀ : IntermediateField F E), x ∈ E₀ ∧
      ∃ r : ℕ, ∃ y : separableClosure F E₀, (((y : E₀) : E) = x ^ (p ^ r)) := by
  let E₀ : IntermediateField F E := F⟮x⟯
  have hx_mem : x ∈ E₀ := by
    -- Proof comment: the simple intermediate field is defined to contain `x`.
    exact IntermediateField.subset_adjoin (by simp)
  let x₀ : E₀ := ⟨x, hx_mem⟩
  have hE₀_alg : Algebra.IsAlgebraic F E₀ := by
    -- Proof comment: the simple extension generated by one algebraic element is algebraic.
    exact
      IntermediateField.isAlgebraic_adjoin (K := F) (L := E) (S := ({x} : Set E)) <| by
        intro z hz
        rcases Set.mem_singleton_iff.mp hz with rfl
        exact (isAlgebraic_iff_isIntegral.mp (Algebra.IsAlgebraic.isAlgebraic (K := F) (A := E) x))
  let _ : Algebra.IsAlgebraic F E₀ := hE₀_alg
  let _ : IsPurelyInseparable (separableClosure F E₀) E₀ :=
    separableClosure.isPurelyInseparable F E₀
  obtain ⟨r, y, hy⟩ :=
    IsPurelyInseparable.pow_mem (F := separableClosure F E₀) (q := p) x₀
  refine ⟨E₀, hx_mem, r, y, ?_⟩
  -- Proof comment: coerce the equality from the simple extension back to the ambient field `E`.
  exact congrArg (fun t : E₀ ↦ (t : E)) hy

/-- Helper for Lemma 16.11.3: the algebraic non-range branch reduces to lifting a separable
`p`-power residue extension through a local étale refinement. -/
private theorem exists_powerFactorization_of_algebraicNonrangeResidue
    [Nontrivial Target] [IsLocalRing Target] [IsArtinianRing Target]
    [HenselianLocalRing Target] [HenselianLocalRing D] [CharP D p] [CharP Target p]
    (DToTarget : D →+* Target) {lbar : Target}
    (hflat : DToTarget.Flat)
    (hαmem : residue Target lbar ∉ Set.range (ResidueField.map DToTarget))
    (hAlg : IsAlgebraic (IsLocalRing.ResidueField D) (residue Target lbar)) :
    ∃ q : ℕ, 0 < q ∧
      ∃ (D' : Type (max w v)) (_ : CommRing D') (_ : IsArtinianRing D') (_ : IsLocalRing D')
        (DToD' : D →+* D') (D'ToTarget : D' →+* Target),
        D'ToTarget.comp DToD' = DToTarget ∧
          DToD'.SmoothAtPrime (closedPoint D') ∧
          D'ToTarget.Flat ∧
          ∃ z : D', D'ToTarget z = lbar ^ q := by
  -- Route correction: the algebraic branch first replaces the residue class by a `p`-power that
  -- lands in a finite separable residue extension; only then does one build the étale refinement.
  let F : Type w := ResidueField D
  let E : Type w := ResidueField Target
  let x : E := residue Target lbar
  let _ : Algebra.IsAlgebraic F E := hAlg
  obtain ⟨E₀, hx_mem, r, y, hy⟩ :=
    exists_separablePower_in_simpleSeparableClosure
      (F := F) (E := E) (p := p) (x := x)
  let L : IntermediateField F (separableClosure F E₀) := F⟮y⟯
  have hy_integral : IsIntegral F y := by
    -- Proof comment: every element of the separable closure is algebraic, hence integral.
    exact isAlgebraic_iff_isIntegral.mp
      (Algebra.IsAlgebraic.isAlgebraic (K := F) (A := separableClosure F E₀) y)
  let _ : FiniteDimensional F ↥L := by
    -- Proof comment: the simple extension generated by one integral element is finite.
    simpa [L] using IntermediateField.adjoin.finiteDimensional hy_integral
  have hy_sep : IsSeparable F y := by
    -- Proof comment: elements of the separable closure are separable over the base field.
    exact Algebra.IsSeparable.isSeparable (K := F) (A := separableClosure F E₀) y
  let _ : Algebra.IsSeparable F ↥L := by
    -- Proof comment: separability passes from the generator to the simple intermediate field.
    simpa [L] using
      (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
        (F := F) (E := separableClosure F E₀)).2 hy_sep
  letI : (maximalIdeal D).IsPrime :=
    Ideal.IsMaximal.isPrime (IsLocalRing.maximalIdeal.isMaximal D)
  obtain ⟨R', _, _, _, q, _, _, hqResidue⟩ :=
    exists_etale_liesOver_with_residueField_equiv
      (R := D) (p := maximalIdeal D) (L := ↥L)
  -- Proof comment: the current frontier is now narrowed to localizing the finite étale stage at
  -- `q`, then lifting the compatible residue-field point to `Target`.
  -- TODO: realize the separable simple extension generated by `y` via
  -- `exists_etale_liesOver_with_residueField_equiv`, localize at the prime over
  -- `maximalIdeal D`, use
  -- `existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap`
  -- to map the refinement into `Target`, and finish by reusing
  -- `exists_powerInImage_of_residueMemRange` for the new local map.
  let _ := hflat
  let _ := hαmem
  let _ := hy
  let _ := y
  let _ := r
  let _ := hx_mem
  let _ := hqResidue
  let _ := q
  let _ := R'
  sorry

/-- Helper for Lemma 16.11.3: the transcendental branch should be packaged through a dedicated
local polynomial refinement rather than an over-strong claim that the power already lies in `D`. -/
private theorem exists_powerFactorization_of_transcendentalResidue
    [Nontrivial Target] [IsLocalRing Target] [IsArtinianRing Target]
    [HenselianLocalRing Target] [HenselianLocalRing D] [CharP D p] [CharP Target p]
    (DToTarget : D →+* Target) {lbar : Target}
    (hflat : DToTarget.Flat)
    (hTrans : ¬ IsAlgebraic (IsLocalRing.ResidueField D) (residue Target lbar)) :
    ∃ q : ℕ, 0 < q ∧
      ∃ (D' : Type (max w v)) (_ : CommRing D') (_ : IsArtinianRing D') (_ : IsLocalRing D')
        (DToD' : D →+* D') (D'ToTarget : D' →+* Target),
        D'ToTarget.comp DToD' = DToTarget ∧
          DToD'.SmoothAtPrime (closedPoint D') ∧
          D'ToTarget.Flat ∧
          ∃ z : D', D'ToTarget z = lbar ^ q := by
  -- Route correction: the transcendental residue case must construct a new local Artinian stage
  -- carrying `lbar`; it cannot collapse directly to a witness in `D`.
  let _ := hflat
  let _ := hTrans
  -- Proof comment: this branch still needs a dependency-closed local polynomial stage API that
  -- compiles in the current prefix context; the intended Chapter 10 constructor is not currently
  -- importable without triggering failures in that support file.
  -- TODO: replace this by the source-faithful local polynomial/localization model together with
  -- the closed-fiber flatness argument.
  sorry

/-- Helper for Lemma 16.11.3: after the zero-residue branch, the nonzero branch must return the
theorem's full refinement witness, not an over-strong claim that the power already lies in `D`. -/
private theorem exists_powerFactorization_of_nonzeroResidue
    [Nontrivial Target] [IsLocalRing Target] [IsArtinianRing Target]
    [HenselianLocalRing Target] [HenselianLocalRing D] [CharP D p] [CharP Target p]
    (DToTarget : D →+* Target) {lbar : Target}
    (hflat : DToTarget.Flat)
    (hαne : residue Target lbar ≠ 0) :
    ∃ q : ℕ, 0 < q ∧
      ∃ (D' : Type (max w v)) (_ : CommRing D') (_ : IsArtinianRing D') (_ : IsLocalRing D')
        (DToD' : D →+* D') (D'ToTarget : D' →+* Target),
        D'ToTarget.comp DToD' = DToTarget ∧
          DToD'.SmoothAtPrime (closedPoint D') ∧
          D'ToTarget.Flat ∧
          ∃ z : D', D'ToTarget z = lbar ^ q := by
  let _ : Algebra D Target := DToTarget.toAlgebra
  have hlocal : IsLocalHom DToTarget := by
    -- Proof comment: the Artinian-local source and nontrivial local target give the canonical
    -- local-hom bridge that was missing in earlier attempts.
    simpa [RingHom.algebraMap_toAlgebra] using
      ringHom_isLocalHom_of_artinianLocal_to_local (f := DToTarget)
  let _ : IsLocalHom DToTarget := hlocal
  let κMap : ResidueField D →+* ResidueField Target := ResidueField.map DToTarget
  let α : ResidueField Target := residue Target lbar
  let _ : Algebra (ResidueField D) (ResidueField Target) := κMap.toAlgebra
  have hαne' : α ≠ 0 := by
    simpa [α] using hαne
  -- Route correction: the earlier frontier `∃ z : D, ...` is false in the transcendental and
  -- algebraic branches. The canonical split must instead return the theorem's genuine refinement
  -- witness `D'`.
  by_cases hαmem : α ∈ Set.range κMap
  · obtain ⟨q, hqpos, z, hz⟩ :=
      exists_powerInImage_of_residueMemRange (D := D) (DToTarget := DToTarget)
        (lbar := lbar) hlocal hαmem
    -- Proof comment: once a positive power already lies in the image of `D`, the theorem output
    -- is the harmless universe-lift packaging from the earlier helper.
    exact
      exists_powerFactorization_of_powerInImage (D := D) (DToTarget := DToTarget)
        hflat hqpos (z := z) hz
  · by_cases hAlg : IsAlgebraic (ResidueField D) α
    · -- Proof comment: the algebraic residue case is now isolated as its own branch lemma so the
      -- remaining blocker is exactly the étale-henselian refinement step.
      exact
        exists_powerFactorization_of_algebraicNonrangeResidue
          (D := D) (DToTarget := DToTarget) (lbar := lbar) hflat hαmem hAlg
    · -- Proof comment: the transcendental residue case is isolated behind the intended local
      -- polynomial refinement API.
      exact
        exists_powerFactorization_of_transcendentalResidue
          (D := D) (DToTarget := DToTarget) (lbar := lbar) hflat hAlg

/-- Helper for Lemma 16.11.3: a bijective ring hom is smooth at the closed point of a local
target. -/
private theorem ringHom_smoothAtPrime_closedPoint_of_bijective
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [IsLocalRing S]
    (f : R →+* S) (hf : Function.Bijective f) :
    f.SmoothAtPrime (closedPoint S) := by
  let _ : Algebra R S := f.toAlgebra
  have hsmooth : f.Smooth := RingHom.Smooth.of_bijective hf
  let _ : Algebra.Smooth R S := hsmooth.toAlgebra
  have hIsSmooth : Algebra.IsSmoothAt R (closedPoint S).asIdeal := by
    -- Global smoothness puts every prime of the target in the smooth locus.
    change closedPoint S ∈ Algebra.smoothLocus R S
    rw [Algebra.smoothLocus_eq_univ (R := R) (A := S)]
    trivial
  simpa using
    (Algebra.smoothAtPrime_iff_isSmoothAt (R := R) (S := S) (q := closedPoint S)).2 hIsSmooth

/-- Helper for Lemma 16.11.3: once a positive power of `lbar` already lies in the image of `D`,
the theorem's refinement output is obtained by the harmless universe lift `D' = ULift D`. -/
private theorem exists_powerFactorization_of_powerInImage
    [Nontrivial Target] [IsLocalRing Target] [IsArtinianRing Target]
    (DToTarget : D →+* Target) (hflat : DToTarget.Flat) {lbar : Target} {q : ℕ} (hqpos : 0 < q)
    {z : D} (hz : DToTarget z = lbar ^ q) :
    ∃ q : ℕ, 0 < q ∧
      ∃ (D' : Type (max w v)) (_ : CommRing D') (_ : IsArtinianRing D') (_ : IsLocalRing D')
        (DToD' : D →+* D') (D'ToTarget : D' →+* Target),
        D'ToTarget.comp DToD' = DToTarget ∧
          DToD'.SmoothAtPrime (closedPoint D') ∧
          D'ToTarget.Flat ∧
          ∃ z' : D', D'ToTarget z' = lbar ^ q := by
  let e : D ≃+* ULift.{max w v, w} D := ULift.ringEquiv.symm
  let uliftToD : ULift.{max w v, w} D →+* D := ULift.ringEquiv.toRingHom
  let _ : IsArtinianRing (ULift.{max w v, w} D) := RingEquiv.isArtinianRing e
  let _ : IsLocalRing (ULift.{max w v, w} D) := RingEquiv.isLocalRing e
  refine ⟨q, hqpos, ULift.{max w v, w} D, inferInstance, inferInstance, inferInstance,
    e.toRingHom, RingHom.comp DToTarget uliftToD, ?_, ?_, ?_, ?_⟩
  · ext x
    rfl
  · -- Proof comment: the universe-lifted source map is a ring equivalence, hence smooth.
    simpa [e] using
      ringHom_smoothAtPrime_closedPoint_of_bijective (f := e.toRingHom) e.bijective
  · have hbij : Function.Bijective ⇑uliftToD := ULift.ringEquiv.bijective
    -- Proof comment: flatness is preserved after composing with the inverse of a ring
    -- equivalence.
    simpa [e] using
      RingHom.Flat.comp
        (RingHom.Flat.of_bijective (f := uliftToD) hbij)
        hflat
  · refine ⟨ULift.up z, ?_⟩
    -- Proof comment: the `ULift` wrapper does not change the target element produced by `z`.
    simpa using hz

/-- Lemma 16.11.3: for a local Artinian factorization as in Lemma `16.11.2` and an element
`λ ∈ Λ`, there exists a positive integer `q` and a refinement
`k[y₁, …, yₘ]_(φ⁻¹(𝔮)) / 𝔪(k[y]_(φ⁻¹(𝔮)))^n → D → D' → Λ_𝔮 / 𝔪(Λ_𝔮)^n` such that `D → D'` is
essentially smooth between local Artinian rings, `D' → Λ_𝔮 / 𝔪(Λ_𝔮)^n` is flat, and the image of
`λ ^ q` lies in `D'`. -/
@[stacks 07FI]
theorem exists_powerFactorization_of_localArtinianPolynomialFactorization
    (sourceToD : SourceQuot →+* D)
    (DToTarget : D →+* Target)
    (localized_flat : (localMap).Flat)
    (factorization : DToTarget.comp sourceToD = targetMap)
    (source_smoothAt_closedPoint : sourceToD.SmoothAtPrime (closedPoint D))
    (target_flat : DToTarget.Flat)
    (l : Λ) :
    ∃ q : ℕ, 0 < q ∧
      ∃ (D' : Type (max w v)) (_ : CommRing D') (_ : IsArtinianRing D') (_ : IsLocalRing D')
        (DToD' : D →+* D') (D'ToTarget : D' →+* Target),
        D'ToTarget.comp DToD' = DToTarget ∧
          DToD'.SmoothAtPrime (closedPoint D') ∧
          D'ToTarget.Flat ∧
          ∃ z : D', D'ToTarget z =
            Ideal.Quotient.mk ((maximalIdeal (Λ_ 𝔮)) ^ n) ((algebraMap Λ (Λ_ 𝔮) l) ^ q) := by
  classical
  let baseToTarget : D →+* Target := DToTarget
  by_cases hn : n = 0
  · subst hn
    -- When `n = 0`, the target quotient is the zero ring, so the original factorization already
    -- works after the universe-only lift `D' = ULift D`, with no change to the ring-theoretic
    -- content of the factorization.
    let e : D ≃+* ULift.{max w v, w} D := ULift.ringEquiv.symm
    let uliftToD : ULift.{max w v, w} D →+* D := ULift.ringEquiv.toRingHom
    let _ : IsArtinianRing (ULift.{max w v, w} D) := RingEquiv.isArtinianRing e
    let _ : IsLocalRing (ULift.{max w v, w} D) := RingEquiv.isLocalRing e
    refine ⟨1, Nat.succ_pos _, ULift.{max w v, w} D, inferInstance, inferInstance, inferInstance,
      e.toRingHom, RingHom.comp baseToTarget uliftToD, ?_, ?_, ?_, ?_⟩
    · ext x
      rfl
    · simpa [e] using
        ringHom_smoothAtPrime_closedPoint_of_bijective (f := e.toRingHom) e.bijective
    · have hbij :
          Function.Bijective ⇑uliftToD := by
          exact ULift.ringEquiv.bijective
      simpa [e] using
        RingHom.Flat.comp
          (RingHom.Flat.of_bijective (f := uliftToD) hbij)
          target_flat
    · refine ⟨ULift.up 0, ?_⟩
      -- In the `n = 0` branch the codomain is the quotient by `⊤`, so both sides are definitionally
      -- equal after transporting the quotient by `𝔪^0` to the quotient by `⊤`.
      letI : Subsingleton ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ 0) := by
        simpa [pow_zero] using
          (inferInstance : Subsingleton ((Λ_ 𝔮) ⧸ (⊤ : Ideal (Λ_ 𝔮))))
      exact Subsingleton.elim _ _
  · have hnpos : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
    let _ : Nontrivial Target := targetQuotient_nontrivial_of_pos (n := n) hnpos
    let _ : IsLocalRing Target := targetQuotient_isLocalRing_of_pos (n := n) hnpos
    let _ : IsArtinianRing Target := targetQuotient_isArtinianRing_of_pos (n := n) hnpos
    let _ : HenselianLocalRing Target := targetQuotient_henselian_of_pos (n := n) hnpos
    let _ : HenselianLocalRing D := by
      let _ : Ring.KrullDimLE 0 D := inferInstance
      exact localRing_henselian_of_krullDimLE_zero D
    -- Route correction: the zero-quotient branch is now discharged directly, so the remaining
    -- work is the genuine positive-power refinement argument from the source proof.
    let lbar : Target :=
      Ideal.Quotient.mk ((maximalIdeal (Λ_ 𝔮)) ^ n) (algebraMap Λ (Λ_ 𝔮) l)
    let α : ResidueField Target := residue Target lbar
    let _ : Algebra k D := (sourceToD.comp (algebraMap k SourceQuot)).toAlgebra
    let _ : CharP D p :=
      charP_of_injective_algebraMap (R := k) (A := D) (algebraMap k D).injective p
    let _ : CharP Target p :=
      charP_of_injective_algebraMap (R := k) (A := Target) (algebraMap k Target).injective p
    by_cases hα0 : α = 0
    · have hlbar_mem : lbar ∈ maximalIdeal Target := by
        -- Proof comment: in the zero-residue branch, `lbar` lies in the closed-point ideal.
        simpa [α, IsLocalRing.residue, IsLocalRing.ker_residue (R := Target)] using
          (Ideal.Quotient.eq_zero_iff_mem (I := maximalIdeal Target)).1 hα0
      obtain ⟨q, hqpos, z, hz⟩ :=
        exists_powerInImage_of_residueZero (D := D) (lbar := lbar) hlbar_mem
      let e : D ≃+* ULift.{max w v, w} D := ULift.ringEquiv.symm
      let uliftToD : ULift.{max w v, w} D →+* D := ULift.ringEquiv.toRingHom
      let _ : IsArtinianRing (ULift.{max w v, w} D) := RingEquiv.isArtinianRing e
      let _ : IsLocalRing (ULift.{max w v, w} D) := RingEquiv.isLocalRing e
      refine ⟨q, hqpos, ULift.{max w v, w} D, inferInstance, inferInstance, inferInstance,
        e.toRingHom, RingHom.comp baseToTarget uliftToD, ?_, ?_, ?_, ?_⟩
      · ext x
        rfl
      · -- Proof comment: the universe-lifted source map is bijective, hence smooth at the closed
        -- point.
        simpa [e] using
          ringHom_smoothAtPrime_closedPoint_of_bijective (f := e.toRingHom) e.bijective
      · have hbij :
            Function.Bijective ⇑uliftToD := by
            exact ULift.ringEquiv.bijective
        -- Proof comment: flatness is preserved after composing with the bijective target
        -- equivalence `ULift D ≃ D`.
        simpa [e] using
          RingHom.Flat.comp
            (RingHom.Flat.of_bijective (f := uliftToD) hbij)
            target_flat
      · refine ⟨ULift.up z, ?_⟩
        -- Proof comment: the zero-residue branch already produced a power of `lbar` in the image
        -- of `D`, and the `ULift` wrapper does not change the underlying target element.
        simpa [lbar] using hz
    · -- The zero-residue branch is settled; the remaining frontier is the nonzero residue-field
      -- case split from the source proof, now phrased via the theorem's genuine refinement data.
      obtain ⟨q, hqpos, D', hD'CommRing, hD'Artinian, hD'Local, DToD', D'ToTarget,
          hcomp, hsmooth, hflat, z, hz⟩ :=
        exists_powerFactorization_of_nonzeroResidue (D := D) (DToTarget := DToTarget)
          (lbar := lbar) target_flat hα0
      refine ⟨q, hqpos, D', hD'CommRing, hD'Artinian, hD'Local, DToD', D'ToTarget,
        hcomp, hsmooth, hflat, z, ?_⟩
      -- Proof comment: the nonzero helper already returns the final target element, and only the
      -- concrete spelling of `lbar` must be unfolded here.
      simpa [lbar] using hz

end

end Algebra
