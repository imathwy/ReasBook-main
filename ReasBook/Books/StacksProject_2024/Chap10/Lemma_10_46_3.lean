import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Lemma_10_46_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Helper for Lemma 10.46.3: the positive-power-in-the-image hypothesis survives after
localizing at a prime. -/
lemma exists_pos_pow_mem_range_localRingHom_atPrime_of_exists_pow_mem_range
    (f : R →+* S)
    (hpow : ∀ x : S, ∃ n > 0, x ^ n ∈ f.range)
    (q : PrimeSpectrum S) :
    ∀ x : Localization.AtPrime q.asIdeal, ∃ n > 0,
      x ^ n ∈ (Localization.localRingHom (comap f q).asIdeal q.asIdeal f rfl).range := by
  intro x
  rcases IsLocalization.exists_mk'_eq q.asIdeal.primeCompl x with ⟨a, b, rfl⟩
  rcases hpow a with ⟨n, hn, ha⟩
  rcases ha with ⟨ra, hra⟩
  rcases hpow (b : S) with ⟨m, hm, hb⟩
  rcases hb with ⟨rb, hrb⟩
  let p : PrimeSpectrum R := comap f q
  let f_loc : Localization.AtPrime p.asIdeal →+* Localization.AtPrime q.asIdeal :=
    Localization.localRingHom p.asIdeal q.asIdeal f rfl
  have hrb_not_mem_p : rb ∉ p.asIdeal := by
    intro hrb_mem
    have hfrb_mem_q : f rb ∈ q.asIdeal := by
      simpa [p] using hrb_mem
    have hbpow_mem_q : (b : S) ^ m ∈ q.asIdeal := by
      simpa [hrb] using hfrb_mem_q
    exact b.2 <| (q.2.pow_mem_iff_mem m hm).1 hbpow_mem_q
  have hrb_pow_not_mem_p : rb ^ n ∉ p.asIdeal := by
    intro hrb_pow_mem
    exact hrb_not_mem_p <| (p.2.pow_mem_iff_mem n hn).1 hrb_pow_mem
  have hrb_pow_mem_primeCompl : rb ^ n ∈ p.asIdeal.primeCompl := hrb_pow_not_mem_p
  have hb_pow_mem_primeCompl : (b : S) ^ (m * n) ∈ q.asIdeal.primeCompl := by
    change (b : S) ^ (m * n) ∉ q.asIdeal
    intro hb_pow_mem
    exact b.2 <| (q.2.pow_mem_iff_mem (m * n) (Nat.mul_pos hm hn)).1 hb_pow_mem
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  refine ⟨IsLocalization.mk' (Localization.AtPrime p.asIdeal) (ra ^ m)
      ⟨rb ^ n, hrb_pow_mem_primeCompl⟩, ?_⟩
  -- Rewrite the chosen localization witness into the textbook fraction-power form.
  change
    f_loc (IsLocalization.mk' (Localization.AtPrime p.asIdeal) (ra ^ m)
        ⟨rb ^ n, hrb_pow_mem_primeCompl⟩) =
      IsLocalization.mk' (Localization.AtPrime q.asIdeal) a b ^ (m * n)
  rw [Localization.localRingHom_mk']
  calc
    IsLocalization.mk' (Localization.AtPrime q.asIdeal) (f (ra ^ m))
        ⟨f (rb ^ n), by
          change f (rb ^ n) ∉ q.asIdeal
          intro h
          exact hrb_pow_not_mem_p <| by
            simpa [p] using h⟩
      = IsLocalization.mk' (Localization.AtPrime q.asIdeal) (a ^ (m * n))
          ⟨(b : S) ^ (m * n), hb_pow_mem_primeCompl⟩ := by
            congr 1
            · calc
                f (ra ^ m) = (f ra) ^ m := by rw [map_pow]
                _ = (a ^ n) ^ m := by rw [hra]
                _ = a ^ (n * m) := by rw [pow_mul]
                _ = a ^ (m * n) := by rw [Nat.mul_comm]
            · apply Subtype.ext
              calc
                f (rb ^ n) = (f rb) ^ n := by rw [map_pow]
                _ = ((b : S) ^ m) ^ n := by rw [hrb]
                _ = (b : S) ^ (m * n) := by rw [pow_mul]
    _ = IsLocalization.mk' (Localization.AtPrime q.asIdeal) (a ^ (m * n)) (b ^ (m * n)) := by
          rfl
    _ = IsLocalization.mk' (Localization.AtPrime q.asIdeal) a b ^ (m * n) := by
          simpa using
            (IsLocalization.mk'_pow (M := q.asIdeal.primeCompl)
              (S := Localization.AtPrime q.asIdeal) a b (m * n))

/-- Helper for Lemma 10.46.3: after passing to the residue field of the localization at `q`,
the same positive-power-in-the-image property still holds. -/
lemma exists_pos_pow_mem_range_residueFieldMap_atPrime_of_exists_pow_mem_range
    (f : R →+* S)
    (hpow : ∀ x : S, ∃ n > 0, x ^ n ∈ f.range)
    (q : PrimeSpectrum S) :
    ∀ x : q.asIdeal.ResidueField, ∃ n > 0,
      x ^ n ∈ (Ideal.ResidueField.map (comap f q).asIdeal q.asIdeal f rfl).range := by
  let p : PrimeSpectrum R := comap f q
  let f_loc : Localization.AtPrime p.asIdeal →+* Localization.AtPrime q.asIdeal :=
    Localization.localRingHom p.asIdeal q.asIdeal f rfl
  intro x
  obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective x
  rcases exists_pos_pow_mem_range_localRingHom_atPrime_of_exists_pow_mem_range f hpow q t with
    ⟨n, hn, y, hy⟩
  refine ⟨n, hn, ?_⟩
  refine ⟨IsLocalRing.residue (Localization.AtPrime p.asIdeal) y, ?_⟩
  -- Pass the localization witness to the residue field via the canonical residue map.
  change
    Ideal.ResidueField.map p.asIdeal q.asIdeal f rfl
        (IsLocalRing.residue (Localization.AtPrime p.asIdeal) y) =
      IsLocalRing.residue (Localization.AtPrime q.asIdeal) t ^ n
  rw [IsLocalRing.ResidueField.map_residue]
  simpa [hy] using congrArg (IsLocalRing.residue (Localization.AtPrime q.asIdeal)) hy

-- Proof sketch: represent an element of `κ(q)` by `y / z` in the localization `S_q`; choose
-- positive powers of `y` and `z` coming from `R`, and then `(y / z)^(nm)` lies in the image of
-- the induced map `κ(q ∩ R) → κ(q)`. Applying the field-level bridge from Lemma `10.46.2`
-- packages this source wording around the canonical owner predicate `IsPurelyInseparable`, with
-- the only exceptional branch being algebraicity over a prime field. The residue-field owner
-- object is the prime `p := comap f q`, not an auxiliary ideal-level wrapper around it. The
-- locally nilpotent-kernel hypothesis is only needed for the separate homeomorphism clause, which
-- is exactly the canonical theorem `PrimeSpectrum.isHomeomorph_comap`.
/-- Lemma 10.46.3 (1): if every element of `S` has a positive power in the image of a ring map
`f : R →+* S`, then for every prime `q` of `S` the induced residue-field map
`κ(comap f q) → κ(q)`
satisfies the canonical field-extension alternative from Lemma `10.46.2`: the extension is purely
inseparable, or the target residue field is algebraic over a prime field. This repackages the
textbook power-in-the-image conclusion around the owner notion `IsPurelyInseparable`. The
homeomorphism statement is the canonical theorem `PrimeSpectrum.isHomeomorph_comap`, recalled
below as clause `(2)`. -/
theorem residueFieldMap_purelyInseparable_or_primeFieldAlgebraic_of_exists_pow_mem_range
    (f : R →+* S)
    (hpow : ∀ x : S, ∃ n > 0, x ^ n ∈ f.range)
    (q : PrimeSpectrum S) :
    let p : PrimeSpectrum R := comap f q
    let fκ : p.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
      Ideal.ResidueField.map p.asIdeal q.asIdeal f rfl
    let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := fκ.toAlgebra
    IsPurelyInseparable p.asIdeal.ResidueField q.asIdeal.ResidueField ∨
      PrimeFieldAlgebraic q.asIdeal.ResidueField := by
  let p : PrimeSpectrum R := comap f q
  let fκ : p.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
    Ideal.ResidueField.map p.asIdeal q.asIdeal f rfl
  let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := fκ.toAlgebra
  have hpowκ : ∀ x : q.asIdeal.ResidueField, ∃ n > 0, x ^ n ∈ fκ.range := by
    -- The source proof first passes to `S_q`, then to the residue field `κ(q)`.
    simpa [p, fκ] using
      exists_pos_pow_mem_range_residueFieldMap_atPrime_of_exists_pow_mem_range f hpow q
  have hcases :
      Function.Surjective (algebraMap p.asIdeal.ResidueField q.asIdeal.ResidueField) ∨
        (ringChar p.asIdeal.ResidueField ≠ 0 ∧
          IsPurelyInseparable p.asIdeal.ResidueField q.asIdeal.ResidueField) ∨
        PrimeFieldAlgebraic q.asIdeal.ResidueField := by
    simpa [fκ] using
      (exists_pos_pow_mem_base_iff_surjective_or_positiveCharacteristic_cases
        (k := p.asIdeal.ResidueField) (k' := q.asIdeal.ResidueField)).mp hpowκ
  -- The surjective branch is stronger than needed; an isomorphism gives pure inseparability.
  rcases hcases with hsurj | hpi | hpf
  · let e : p.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField] q.asIdeal.ResidueField :=
      AlgEquiv.ofBijective (Algebra.ofId p.asIdeal.ResidueField q.asIdeal.ResidueField)
        ⟨FaithfulSMul.algebraMap_injective p.asIdeal.ResidueField q.asIdeal.ResidueField, hsurj⟩
    exact Or.inl e.isPurelyInseparable
  · exact Or.inl hpi.2
  · exact Or.inr hpf

/- Lemma 10.46.3 (2): if every element of `S` has a positive power in the image of a ring map
`f : R →+* S` and the kernel of `f` is locally nilpotent, then the induced map on prime spectra is
a homeomorphism. This is exactly the canonical theorem `PrimeSpectrum.isHomeomorph_comap`. -/
recall PrimeSpectrum.isHomeomorph_comap

end
