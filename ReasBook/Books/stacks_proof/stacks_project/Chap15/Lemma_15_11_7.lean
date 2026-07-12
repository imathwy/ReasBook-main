import Mathlib
import StacksProject_2024.Chap15.Lemma_15_11_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open PrimeSpectrum

variable {A : Type u} [CommRing A]

namespace Ideal

/- Domain-style sampling:
- primary domain: henselian pairs in commutative algebra, viewed through the prime-spectrum closed
  subset `V(I)` and the Chapter 15 idempotent-lifting criterion;
- sampled owner declarations:
  `HenselianRing`,
  `Ideal.HasIntegralAlgebraIdempotentLifting`,
  `henselianRing_tfae_etaleLift_idempotents_gabberCriterion`,
  `PrimeSpectrum.zeroLocus_eq_iff`;
- best owner abstraction: the public statement should stay on the canonical owner
  `HenselianRing A I`; the integral-idempotent lifting predicate is derived bridge API from
  Lemma `15.11.6`, and radical equality is the canonical owner-level form of the spectral
  hypothesis `V(I) = V(J)`;
- primitive data: the ideals `I`, `J`, the closed-subset equality `zeroLocus I = zeroLocus J`,
  and for auxiliary integral `A`-algebras `B`, the mapped ideals `Ideal.map (algebraMap A B) I`
  and `Ideal.map (algebraMap A B) J`;
- derived API: the quotient-induced maps on idempotents and the passage from an ideal to its
  radical quotient, which is internal proof infrastructure rather than public owner data.

Source/core/bridge triage:
- `source-facing`: the invariance of henselianity under replacing `I` by an ideal with the same
  closed subset in `Spec A`;
- `core/canonical`: `HenselianRing A I`, `Ideal.HasIntegralAlgebraIdempotentLifting`, and
  `PrimeSpectrum.zeroLocus_eq_iff`;
- `bridge/view`: the zero-locus invariance equivalence for the Chapter 15 integral-idempotent
  lifting owner, proved by passing to the common radical / reduced quotient.
-/

/-- Helper for Lemma 15.11.7: extending two ideals along an algebra map preserves equality of
their prime-spectrum zero loci. -/
private theorem zeroLocus_map_eq_of_zeroLocus_eq (I J : Ideal A)
    (hV : zeroLocus (I : Set A) = zeroLocus (J : Set A))
    {B : Type v} [CommRing B] [Algebra A B] :
    zeroLocus (Ideal.map (algebraMap A B) I : Set B) =
      zeroLocus (Ideal.map (algebraMap A B) J : Set B) := by
  -- Compare membership pointwise by contracting prime ideals along the algebra map.
  ext q
  constructor
  · intro hq
    have hIq : I ≤ Ideal.comap (algebraMap A B) q.asIdeal := by
      exact Ideal.map_le_iff_le_comap.mp <|
        (PrimeSpectrum.mem_zeroLocus q (Ideal.map (algebraMap A B) I : Set B)).mp hq
    have hqI :
        PrimeSpectrum.comap (algebraMap A B) q ∈ zeroLocus (I : Set A) := by
      exact (PrimeSpectrum.mem_zeroLocus (PrimeSpectrum.comap (algebraMap A B) q)
        (I : Set A)).mpr <| by
          simpa [PrimeSpectrum.comap_asIdeal] using hIq
    have hqJ :
        PrimeSpectrum.comap (algebraMap A B) q ∈ zeroLocus (J : Set A) := by
      simpa [hV] using hqI
    exact (PrimeSpectrum.mem_zeroLocus q (Ideal.map (algebraMap A B) J : Set B)).mpr <|
      Ideal.map_le_iff_le_comap.mpr <| by
        simpa [PrimeSpectrum.comap_asIdeal] using
          (PrimeSpectrum.mem_zeroLocus (PrimeSpectrum.comap (algebraMap A B) q)
            (J : Set A)).mp hqJ
  · intro hq
    have hJq : J ≤ Ideal.comap (algebraMap A B) q.asIdeal := by
      exact Ideal.map_le_iff_le_comap.mp <|
        (PrimeSpectrum.mem_zeroLocus q (Ideal.map (algebraMap A B) J : Set B)).mp hq
    have hqJ :
        PrimeSpectrum.comap (algebraMap A B) q ∈ zeroLocus (J : Set A) := by
      exact (PrimeSpectrum.mem_zeroLocus (PrimeSpectrum.comap (algebraMap A B) q)
        (J : Set A)).mpr <| by
          simpa [PrimeSpectrum.comap_asIdeal] using hJq
    have hqI :
        PrimeSpectrum.comap (algebraMap A B) q ∈ zeroLocus (I : Set A) := by
      simpa [hV] using hqJ
    exact (PrimeSpectrum.mem_zeroLocus q (Ideal.map (algebraMap A B) I : Set B)).mpr <|
      Ideal.map_le_iff_le_comap.mpr <| by
        simpa [PrimeSpectrum.comap_asIdeal] using
          (PrimeSpectrum.mem_zeroLocus (PrimeSpectrum.comap (algebraMap A B) q)
            (I : Set A)).mp hqI

/-- Helper for Lemma 15.11.7: a surjective ring map whose kernel consists of nilpotent elements
induces a bijection on idempotents. -/
private theorem bijective_idempotentMap_of_surjective_of_nilpotent_kernel_elements
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] (f : R →+* S)
    (hsurj : Function.Surjective f)
    (hker : ∀ x ∈ RingHom.ker f, IsNilpotent x) :
    Function.Bijective f.idempotentMap := by
  constructor
  · intro e₁ e₂ h
    apply Subtype.ext
    -- Unique lifting across the locally nilpotent kernel forces equal lifts of the same
    -- idempotent in the target.
    obtain ⟨e, he, huniq⟩ :=
      RingHom.existsUnique_isIdempotentElem_eq_of_ker_isNilpotent
        f hker (f e₁.1) (hsurj _) (e₁.2.map f)
    exact (huniq _ ⟨e₁.2, rfl⟩).trans
      (huniq _ ⟨e₂.2, by simpa using (congrArg Subtype.val h).symm⟩).symm
  · intro e
    -- Surjectivity supplies a lift, and the same unique-lifting statement makes it idempotent.
    obtain ⟨e', he', -⟩ :=
      RingHom.existsUnique_isIdempotentElem_eq_of_ker_isNilpotent
        f hker e.1 (hsurj _) e.2
    refine ⟨⟨e', he'.1⟩, ?_⟩
    exact Subtype.ext he'.2

/-- Helper for Lemma 15.11.7: the quotient map from `B ⧸ K` to `B ⧸ √K` is surjective. -/
private theorem radicalQuotientFactor_surjective {B : Type v} [CommRing B] (K : Ideal B) :
    Function.Surjective (Ideal.Quotient.factor (I := K) (J := K.radical) Ideal.le_radical) := by
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  -- Every class modulo `√K` already comes from the class of the same representative modulo `K`.
  exact ⟨Ideal.Quotient.mk K y, rfl⟩

/-- Helper for Lemma 15.11.7: every element in the kernel of `B ⧸ K → B ⧸ √K` is nilpotent. -/
private theorem radicalQuotientFactor_ker_nilpotent_elements
    {B : Type v} [CommRing B] (K : Ideal B) :
    ∀ x ∈ RingHom.ker (Ideal.Quotient.factor (I := K) (J := K.radical) Ideal.le_radical),
      IsNilpotent x := by
  intro x hx
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker] at hx
  change Ideal.Quotient.mk K.radical y = 0 at hx
  have hy : y ∈ K.radical := Ideal.Quotient.eq_zero_iff_mem.mp hx
  rcases Ideal.mem_radical_iff.mp hy with ⟨n, hn⟩
  -- Nilpotence in the radical exactly means some power lands back in `K`, so the class vanishes.
  refine ⟨n, ?_⟩
  change Ideal.Quotient.mk K (y ^ n) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hn

/-- Helper for Lemma 15.11.7: the factor map `B ⧸ K → B ⧸ √K` induces a bijection on
idempotents. -/
private theorem radicalQuotientFactor_bijective_idempotentMap
    {B : Type v} [CommRing B] (K : Ideal B) :
    Function.Bijective
      (Ideal.Quotient.factor (I := K) (J := K.radical) Ideal.le_radical).idempotentMap := by
  -- Apply the general locally-nilpotent-kernel lifting theorem to the quotient factor map.
  exact bijective_idempotentMap_of_surjective_of_nilpotent_kernel_elements
    (Ideal.Quotient.factor (I := K) (J := K.radical) Ideal.le_radical)
    (radicalQuotientFactor_surjective K)
    (radicalQuotientFactor_ker_nilpotent_elements K)

/-- Helper for Lemma 15.11.7: composing with a bijection preserves bijectivity. -/
private theorem bijective_iff_bijective_comp
    {α : Type u} {β : Type v} {γ : Type max u v}
    (f : α → β) (g : β → γ) (hg : Function.Bijective g) :
    Function.Bijective f ↔ Function.Bijective (g ∘ f) := by
  constructor
  · intro hf
    exact hg.comp hf
  · intro hgf
    constructor
    · intro x y hxy
      exact hgf.1 hxy
    · intro z
      obtain ⟨y, rfl⟩ := hg.2 z
      obtain ⟨x, rfl⟩ := hgf.2 y
      exact ⟨x, rfl⟩

/-- Helper for Lemma 15.11.7: bijectivity of the quotient idempotent map depends only on the
radical of the ideal. -/
private theorem bijective_idempotentMap_iff_of_radical_eq
    {B : Type v} [CommRing B] (K L : Ideal B) (hKL : K.radical = L.radical) :
    Function.Bijective (Ideal.Quotient.mk K).idempotentMap ↔
      Function.Bijective (Ideal.Quotient.mk L).idempotentMap := by
  have hK :
      Function.Bijective (Ideal.Quotient.mk K).idempotentMap ↔
        Function.Bijective (Ideal.Quotient.mk K.radical).idempotentMap := by
    let φ : B ⧸ K →+* B ⧸ K.radical :=
      Ideal.Quotient.factor (I := K) (J := K.radical) Ideal.le_radical
    have hφ : Function.Bijective φ.idempotentMap :=
      radicalQuotientFactor_bijective_idempotentMap K
    have hcomp :
        φ.idempotentMap ∘ (Ideal.Quotient.mk K).idempotentMap =
          (Ideal.Quotient.mk K.radical).idempotentMap := by
      funext e
      rfl
    -- The map to `B ⧸ √K` factors through `B ⧸ K`, and the intermediate idempotent map is
    -- already bijective.
    simpa [φ, hcomp] using
      (bijective_iff_bijective_comp
        (Ideal.Quotient.mk K).idempotentMap φ.idempotentMap hφ)
  have hL :
      Function.Bijective (Ideal.Quotient.mk L).idempotentMap ↔
        Function.Bijective (Ideal.Quotient.mk L.radical).idempotentMap := by
    let φ : B ⧸ L →+* B ⧸ L.radical :=
      Ideal.Quotient.factor (I := L) (J := L.radical) Ideal.le_radical
    have hφ : Function.Bijective φ.idempotentMap :=
      radicalQuotientFactor_bijective_idempotentMap L
    have hcomp :
        φ.idempotentMap ∘ (Ideal.Quotient.mk L).idempotentMap =
          (Ideal.Quotient.mk L.radical).idempotentMap := by
      funext e
      rfl
    -- The same reduced-quotient comparison works for `L`.
    simpa [φ, hcomp] using
      (bijective_iff_bijective_comp
        (Ideal.Quotient.mk L).idempotentMap φ.idempotentMap hφ)
  rw [hK, hL, hKL]

-- If two ideals define the same closed subset of `Spec A`, then the Chapter 15 integral
-- idempotent-lifting criterion is the same for both.
private theorem hasIntegralAlgebraIdempotentLifting_iff_of_zeroLocus_eq (I J : Ideal A)
    (hV : zeroLocus (I : Set A) = zeroLocus (J : Set A)) :
    I.HasIntegralAlgebraIdempotentLifting ↔ J.HasIntegralAlgebraIdempotentLifting := by
  -- For every integral `A`-algebra `B`, the mapped ideals `IB` and `JB` have the same zero locus,
  -- hence the same radical by `PrimeSpectrum.zeroLocus_eq_iff`. Passing from `B / IB` and
  -- `B / JB` to the common reduced quotient by that radical does not change idempotents, because
  -- quotienting by a nilradical extension preserves idempotents. Thus the Chapter 15 owner
  -- `HasIntegralAlgebraIdempotentLifting` depends only on the closed subset `V(I)`.
  constructor
  · intro h B _ _ _
    let K : Ideal B := Ideal.map (algebraMap A B) I
    let L : Ideal B := Ideal.map (algebraMap A B) J
    have hKL : K.radical = L.radical := by
      -- Transport the spectral equality to `B`, then convert closed-set equality to radicals.
      exact PrimeSpectrum.zeroLocus_eq_iff.mp <|
        zeroLocus_map_eq_of_zeroLocus_eq I J hV
    have hK : Function.Bijective (Ideal.Quotient.mk K).idempotentMap := by
      simpa [K] using h (B := B)
    exact (bijective_idempotentMap_iff_of_radical_eq K L hKL).mp hK
  · intro h B _ _ _
    let K : Ideal B := Ideal.map (algebraMap A B) I
    let L : Ideal B := Ideal.map (algebraMap A B) J
    have hKL : K.radical = L.radical := by
      -- The same zero-locus comparison yields the same common reduced quotient in the reverse
      -- direction as well.
      exact PrimeSpectrum.zeroLocus_eq_iff.mp <|
        zeroLocus_map_eq_of_zeroLocus_eq I J hV
    have hL : Function.Bijective (Ideal.Quotient.mk L).idempotentMap := by
      simpa [L] using h (B := B)
    exact (bijective_idempotentMap_iff_of_radical_eq K L hKL).mpr hL

end Ideal

-- Proof sketch: by Lemma `15.11.6`, henselianity of `(A, I)` is equivalent to bijectivity on
-- idempotents after quotienting every integral `A`-algebra `B` by `IB`. If `V(I) = V(J)` in
-- `Spec A`, then for every integral `A`-algebra `B` the extended ideals `IB` and `JB` have the
-- same zero locus, so Lemma `10.21.3` identifies the idempotents of `B/IB` and `B/JB`. Hence the
-- idempotent-lifting criterion is the same for `I` and `J`, and the conclusion follows again from
-- Lemma `15.11.6`.
/-- Lemma 15.11.7: if two ideals `I` and `J` of a commutative ring `A` define the same closed
subset of `Spec A`, then the pair `(A, I)` is henselian if and only if the pair `(A, J)` is
henselian. -/
@[stacks 09XJ]
theorem henselianRing_iff_of_zeroLocus_eq (I J : Ideal A)
    (hV : zeroLocus (I : Set A) = zeroLocus (J : Set A)) :
    HenselianRing A I ↔ HenselianRing A J := by
  let Q : Ideal A → Prop := Ideal.HasFiniteAlgebraIdempotentLifting.{u, u}
  let P : Ideal A → Prop := Ideal.HasIntegralAlgebraIdempotentLifting.{u, u}
  let T (K : Ideal A) : List Prop :=
    [HenselianRing A K, K.HasEtaleLiftProperty, Q K, P K, K.SatisfiesGabberRootCriterion]
  have hTfaeI : List.TFAE (T I) := by
    simpa [T, Q, P] using henselianRing_tfae_etaleLift_idempotents_gabberCriterion I
  have hI : HenselianRing A I ↔ P I := by
    simpa [T] using hTfaeI.out 0 3
  have hIJ : P I ↔ P J :=
    Ideal.hasIntegralAlgebraIdempotentLifting_iff_of_zeroLocus_eq I J hV
  have hTfaeJ : List.TFAE (T J) := by
    simpa [T, Q, P] using henselianRing_tfae_etaleLift_idempotents_gabberCriterion J
  have hJ : HenselianRing A J ↔ P J := by
    simpa [T] using hTfaeJ.out 0 3
  exact (hI.trans hIJ).trans hJ.symm

end
