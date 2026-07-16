import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap10.Lemma_10_52_4
import stacks_proof.stacks_project.Chap10.Lemma_10_52_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} {K : Type v} {V : Type w}
variable [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

variable [IsLocalRing R]

open scoped Pointwise
open IsLocalRing

namespace Submodule.IsLattice

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- Helper for Lemma 10.121.4: a finite submodule of the ambient fraction-field module can be
cleared into a controlling lattice by one nonzero scalar. -/
theorem exists_nonzero_scalar_smul_le_of_finite
    {M N : Submodule R V} [IsLattice K M] (hN : Module.Finite R N) :
    ∃ a : R, a ≠ 0 ∧ a • N ≤ M := by
  classical
  rw [Module.Finite.iff_fg] at hN
  obtain ⟨t, ht⟩ := hN
  obtain ⟨s, hs⟩ := IsLattice.fg (A := K) (M := M)
  have hspan_s : Submodule.span K (s : Set V) = ⊤ := by
    -- The same finite family that generates `M` over `R` spans all of `V` over `K`.
    calc
      Submodule.span K (s : Set V) =
          Submodule.span K ((Submodule.span R (s : Set V) : Submodule R V) : Set V) := by
            symm
            rw [Submodule.span_span_of_tower (R := R) (S := K) (s := (s : Set V))]
      _ = Submodule.span K (M : Set V) := by
            rw [hs]
      _ = ⊤ := IsLattice.span_eq_top (A := K) (M := M)
  have hcoords : ∀ i : t, ∃ c : s → K, ∑ j : s, c j • (j : V) = (i : V) := by
    intro i
    -- Each finite generator of `N` lies in the `K`-span of the fixed lattice generators.
    have hi : (i : V) ∈ Submodule.span K (s : Set V) := by
      simpa [hspan_s]
    exact (Submodule.mem_span_finset').mp hi
  choose coeff hcoeff using hcoords
  let coords : t × s → K := fun ij ↦ coeff ij.1 ij.2
  obtain ⟨a', ha'⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (M := nonZeroDivisors R) coords
  let a : R := a'
  have ha : a ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp a'.property
  have hnum_exists :
      ∀ ij : t × s, ∃ r : R, algebraMap R K r = a • coords ij := by
    intro ij
    exact ha' ij
  choose num hnum using hnum_exists
  have hclear_gen : ∀ i : t, a • (i : V) ∈ M := by
    intro i
    have hsum :
        ∑ j : s, (num (i, j) : R) • (j : V) =
          a • ∑ j : s, coeff i j • (j : V) := by
      calc
        ∑ j : s, (num (i, j) : R) • (j : V) =
            ∑ j : s, (a • coeff i j) • (j : V) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              simpa [Algebra.smul_def] using
                congrArg (fun z : K => z • (j : V)) (hnum (i, j))
        _ = a • ∑ j : s, coeff i j • (j : V) := by
              rw [Finset.smul_sum]
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [smul_assoc]
    have hsum_mem : ∑ j : s, (num (i, j) : R) • (j : V) ∈ M := by
      -- Each numerator combination lies in the original lattice.
      refine Submodule.sum_mem M ?_
      intro j hj
      exact Submodule.smul_mem M (num (i, j)) <| by
        rw [← hs]
        exact Submodule.subset_span j.property
    have hrewrite :
        a • (i : V) = ∑ j : s, (num (i, j) : R) • (j : V) := by
      calc
        a • (i : V) = a • ∑ j : s, coeff i j • (j : V) := by
          rw [hcoeff i]
        _ = ∑ j : s, (num (i, j) : R) • (j : V) := hsum.symm
    simpa [hrewrite] using hsum_mem
  refine ⟨a, ha, ?_⟩
  have hsmul_span :
      a • N = Submodule.span R (a • (t : Set V)) := by
    -- Scalar multiplication commutes with the span of the generator set.
    calc
      a • N = a • Submodule.span R (t : Set V) := by
        rw [ht.symm]
      _ = Submodule.span R (a • (t : Set V)) := by
        rw [Submodule.smul_span]
  rw [hsmul_span]
  refine Submodule.span_le.mpr ?_
  rintro x ⟨y, hy, rfl⟩
  exact hclear_gen ⟨y, hy⟩

end Submodule.IsLattice

/-- Helper for Lemma 10.121.4: a finite-length quotient over a local ring is eventually killed by
a power of the maximal ideal inside the ambient module. -/
theorem exists_pow_maximalIdeal_smul_top_le_of_isFiniteLength_quotient
    {W : Type*} [AddCommGroup W] [Module R W] (N : Submodule R W)
    (hquot : IsFiniteLength R (W ⧸ N)) :
    ∃ n : ℕ, ((maximalIdeal R) ^ n • (⊤ : Submodule R W)) ≤ N := by
  -- First kill the quotient itself by a power of the maximal ideal.
  obtain ⟨n, hn⟩ :=
    exists_pow_maximalIdeal_smul_eq_bot_of_isFiniteLength (R := R) (M := W ⧸ N) hquot
  refine ⟨n, ?_⟩
  have hmap : (((maximalIdeal R) ^ n • (⊤ : Submodule R W)).map N.mkQ) = ⊥ := by
    -- The quotient map sends the ambient power straight to the corresponding power on the quotient.
    simpa [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] using hn
  have hmaple :
      (((maximalIdeal R) ^ n • (⊤ : Submodule R W)).map N.mkQ) ≤ ⊥ := by
    simpa [hmap]
  simpa [Submodule.ker_mkQ] using (Submodule.map_le_iff_le_comap.mp hmaple)

/-- Helper for Lemma 10.121.4: if an ideal sends a submodule into a denominator submodule, then the
same ideal annihilates the quotient by that denominator. -/
theorem smul_top_eq_bot_of_smul_le_submoduleOf
    {N P : Submodule R V} (I : Ideal R) (hIP : I • N ≤ P) :
    I • (⊤ : Submodule R (N ⧸ P.submoduleOf N)) = ⊥ := by
  have hsubmoduleOf : I • (⊤ : Submodule R N) ≤ P.submoduleOf N := by
    -- Rewrite the ambient containment through the subtype map of `N`.
    have hmap : (I • (⊤ : Submodule R N)).map N.subtype ≤ P := by
      simpa [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] using hIP
    simpa [Submodule.submoduleOf] using (Submodule.map_le_iff_le_comap.mp hmap)
  have hmaple : ((I • (⊤ : Submodule R N)).map (P.submoduleOf N).mkQ) ≤ ⊥ := by
    exact (Submodule.map_le_iff_le_comap).2 <| by
      simpa [Submodule.ker_mkQ] using hsubmoduleOf
  have hmapeq : ((I • (⊤ : Submodule R N)).map (P.submoduleOf N).mkQ) = ⊥ := by
    exact le_antisymm hmaple bot_le
  -- Transport the vanishing statement across the quotient map.
  simpa [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] using hmapeq

/-- Helper for Lemma 10.121.4: every power of the maximal ideal of a one-dimensional local domain
contains a nonzero element. -/
theorem exists_nonzero_mem_maximalIdeal_pow_of_ringKrullDim_eq_one
    (hdim : ringKrullDim R = 1) (n : ℕ) :
    ∃ a : R, a ∈ (maximalIdeal R) ^ n ∧ a ≠ 0 := by
  -- The maximal ideal is nonzero in dimension one, and powers of a nonzero element stay nonzero.
  have hnotField : ¬ IsField R :=
    (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain (R := R)).mp hdim |>.1
  have hm_ne_bot : maximalIdeal R ≠ ⊥ := by
    intro hm
    exact hnotField ((IsLocalRing.isField_iff_maximalIdeal_eq (R := R)).2 hm)
  obtain ⟨x, hxmem, hx0⟩ := (maximalIdeal R).ne_bot_iff.mp hm_ne_bot
  exact ⟨x ^ n, Ideal.pow_mem_pow hxmem n, pow_ne_zero n hx0⟩

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- Helper for Lemma 10.121.4: a single lattice in the fraction-field module makes the ambient
`K`-module finite. -/
theorem Submodule.IsLattice.moduleFinite_of_isLattice
    {M : Submodule R V} [Submodule.IsLattice K M] :
    Module.Finite K V := by
  obtain ⟨s, hs⟩ := Submodule.IsLattice.fg (A := K) (M := M)
  have hspan :
      Submodule.span K (s : Set V) = ⊤ := by
    -- The finite `R`-generators of `M` already span `V` over the fraction field.
    calc
      Submodule.span K (s : Set V) =
          Submodule.span K ((Submodule.span R (s : Set V) : Submodule R V) : Set V) := by
            symm
            rw [Submodule.span_span_of_tower (R := R) (S := K) (s := (s : Set V))]
      _ = Submodule.span K (M : Set V) := by
            rw [hs]
      _ = ⊤ := Submodule.IsLattice.span_eq_top (A := K) (M := M)
  let f : Submodule.span K (s : Set V) →ₗ[K] V := (Submodule.span K (s : Set V)).subtype
  have hf : Function.Surjective f := by
    intro x
    have hx : x ∈ Submodule.span K (s : Set V) := by
      simpa [hspan]
    exact ⟨⟨x, hx⟩, rfl⟩
  letI : Module.Finite K (Submodule.span K (s : Set V)) := Module.Finite.span_finset K s
  exact Module.Finite.of_surjective f hf

/-- Helper for Lemma 10.121.4: a scalar lying in an ideal whose intrinsic multiple of `M`
lands in `N.submoduleOf M` already sends the ambient module `M` into `N`. -/
theorem smul_le_of_mem_of_submoduleOf_smul_top_le
    {M N : Submodule R V} {I : Ideal R} {a : R}
    (ha : a ∈ I) (hI : I • (⊤ : Submodule R M) ≤ N.submoduleOf M) :
    a • M ≤ N := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  have hmem_top : a • (⟨y, hy⟩ : M) ∈ I • (⊤ : Submodule R M) :=
    Submodule.smul_mem_smul ha (by trivial)
  have hmem_submoduleOf : a • (⟨y, hy⟩ : M) ∈ N.submoduleOf M := hI hmem_top
  simpa [Submodule.submoduleOf] using hmem_submoduleOf

namespace Submodule.IsLattice

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- Helper for Lemma 10.121.4: a nonzero scalar from the base domain acts through a unit in the
fraction field, so its scalar multiple of a lattice is again a lattice. -/
theorem smul_of_ne_zero {M : Submodule R V} [IsLattice K M] {a : R} (ha : a ≠ 0) :
    IsLattice K (a • M : Submodule R V) := by
  let u : Kˣ :=
    Units.mk0 (algebraMap R K a)
      ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha)
  have hu : IsLattice K (u • M : Submodule R V) := inferInstance
  have hEq : (u • M : Submodule R V) = a • M := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      simp [u]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      simp [u]
  simpa [hEq] using hu

end Submodule.IsLattice

/-- Helper for Lemma 10.121.4: quotienting by an intermediate submodule decomposes length
additively. -/
theorem length_quotient_eq_add_length_submodule_quotient_of_le
    {W : Type*} [AddCommGroup W] [Module R W] {J N : Submodule R W} (hJN : J ≤ N) :
    Module.length R (W ⧸ J) =
      Module.length R (W ⧸ N) + Module.length R (N ⧸ J.submoduleOf N) := by
  -- First split `W ⧸ J` by the image of `N`.
  have hsplit :
      Module.length R (W ⧸ J) =
        Module.length R (N.map J.mkQ) + Module.length R ((W ⧸ J) ⧸ N.map J.mkQ) := by
    simpa using
      (Module.length_eq_add_of_exact
        (Submodule.subtype (N.map J.mkQ))
        (Submodule.mkQ (N.map J.mkQ))
        (Submodule.subtype_injective _)
        (Submodule.mkQ_surjective _)
        (LinearMap.exact_subtype_mkQ (N.map J.mkQ)))
  have himage :
      Module.length R (N.map J.mkQ) = Module.length R (N ⧸ J.submoduleOf N) := by
    -- The image of `N` in `W ⧸ J` is canonically the quotient `N / J`.
    let f : N →ₗ[R] W ⧸ J := J.mkQ.comp N.subtype
    have hker : LinearMap.ker f = J.submoduleOf N := by
      ext x
      simp [f, Submodule.submoduleOf]
    have hrange : LinearMap.range f = N.map J.mkQ := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨y.1, y.2, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
    have hequiv :
        Module.length R (N ⧸ J.submoduleOf N) = Module.length R (LinearMap.range f) := by
      simpa [hker] using
        ((Submodule.quotEquivOfEq (J.submoduleOf N) (LinearMap.ker f) hker.symm).trans
          (LinearMap.quotKerEquivRange f)).length_eq
    calc
      Module.length R (N.map J.mkQ) = Module.length R (LinearMap.range f) := by
        rw [hrange]
      _ = Module.length R (N ⧸ J.submoduleOf N) := hequiv.symm
  have hquot :
      Module.length R ((W ⧸ J) ⧸ N.map J.mkQ) = Module.length R (W ⧸ N) := by
    -- The remaining quotient is the usual quotient by `N`.
    simpa using (Submodule.quotientQuotientEquivQuotient J N hJN).length_eq
  calc
    Module.length R (W ⧸ J) =
        Module.length R (N.map J.mkQ) + Module.length R ((W ⧸ J) ⧸ N.map J.mkQ) := hsplit
    _ = Module.length R (N ⧸ J.submoduleOf N) + Module.length R (W ⧸ N) := by
          rw [himage, hquot]
    _ = Module.length R (W ⧸ N) + Module.length R (N ⧸ J.submoduleOf N) := by
          rw [add_comm]

/-
Domain triage:
* primary domain: lattices in fraction-field modules and finite colength quotients over a
  one-dimensional Noetherian local domain;
* sampled owner API: `Submodule.IsLattice`, `Submodule.IsLattice.of_le_of_isLattice_of_fg`,
  `Submodule.IsLattice.sup`, `Submodule.submoduleOf`, `Module.length`, and
  `Module.length_eq_add_of_exact`;
* core/canonical owner: latticehood is owned by `Submodule.IsLattice K`, while finite-colength
  assertions are source-facing reformulations of the finite-length owner on quotients
  `N ⧸ P.submoduleOf N`;
* primitive vs. derived API: the lattice hypotheses should be ambient owner assumptions, ambient
  finite-dimensionality is derived from any lattice hypothesis, and only the quotient-length
  relations remain as explicit source-facing statements;
* layer split: clause (3) for sums is the exact owner theorem `Submodule.IsLattice.sup`, while the
  intersection clause is a source-facing extension of the `Submodule.IsLattice` owner API because
  the mathlib owner `Submodule.IsLattice.inf` is only available under stronger PID hypotheses,
  whereas the Stacks proof only needs Noetherian denominator-clearing in the fraction-field setup.
-/

-- Proof sketch: because `M` is already a lattice, `M'` automatically spans `V` over `K` once
-- `M ≤ M'`. Thus the only extra condition for `M'` to be a lattice is finite generation. The
-- one-dimensional local domain hypothesis identifies finite generation of the over-lattice with
-- finite length of the quotient `M' / M` by clearing denominators and applying the finite-length
-- lemmas for one-dimensional local domains.
/-- Lemma 10.121.4 (1): for an `R`-submodule `M'` with `M ≤ M' ≤ V`, being a lattice, having
finite-length quotient `M' / M`, and being finitely generated over `R` are equivalent. -/
@[stacks 02MF]
theorem tfae_isLattice_length_lt_top_moduleFinite_of_le
    {M M' : Submodule R V} [Submodule.IsLattice K M] (hdim : ringKrullDim R = 1)
    (hMM' : M ≤ M') :
    List.TFAE
      [ Submodule.IsLattice K M'
      , Module.length R (M' ⧸ M.submoduleOf M') < ⊤
      , Module.Finite R M'
      ] := by
  letI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by simpa [hdim])
  tfae_have 1 → 2 := by
    intro hLattice
    letI : Submodule.IsLattice K M' := hLattice
    letI : Module.Finite R M' := inferInstance
    -- Clear denominators into the fixed lattice `M`.
    obtain ⟨a, ha, hsmul⟩ :=
      Submodule.IsLattice.exists_nonzero_scalar_smul_le_of_finite
        (R := R) (K := K) (V := V) (M := M) (N := M') inferInstance
    have hprincipal :
        IsFiniteLength R (R ⧸ Ideal.span ({a} : Set R)) :=
      isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_iff_ne_zero.mpr ha)
    obtain ⟨n, hn⟩ :=
      exists_pow_maximalIdeal_smul_top_le_of_isFiniteLength_quotient
        (R := R) (N := Ideal.span ({a} : Set R)) hprincipal
    have hpow : (maximalIdeal R) ^ n ≤ Ideal.span ({a} : Set R) := by
      -- On the regular module `R`, the submodule containment is exactly the ideal containment.
      simpa using hn
    have hkill_ambient :
        ((maximalIdeal R) ^ n) • M' ≤ M := by
      -- The principal denominator ideal already sends `M'` into `M`.
      calc
        ((maximalIdeal R) ^ n) • M' ≤ Ideal.span ({a} : Set R) • M' := by
          exact Submodule.smul_mono hpow le_rfl
        _ = a • M' := by
          simpa using (Submodule.ideal_span_singleton_smul a M')
        _ ≤ M := hsmul
    have hkill_quot :
        ((maximalIdeal R) ^ n) • (⊤ : Submodule R (M' ⧸ M.submoduleOf M')) = ⊥ :=
      smul_top_eq_bot_of_smul_le_submoduleOf (R := R) (N := M') (P := M)
        ((maximalIdeal R) ^ n) hkill_ambient
    have hfg_max : (maximalIdeal R).FG := by
      simpa [Module.Finite.iff_fg] using (show Module.Finite R (maximalIdeal R) from inferInstance)
    have hfinite_quot :
        IsFiniteLength R (M' ⧸ M.submoduleOf M') :=
      isFiniteLength_of_pow_smul_eq_bot (m := maximalIdeal R) hfg_max hkill_quot
    exact lt_top_iff_ne_top.mpr (Module.length_ne_top_iff.mpr hfinite_quot)
  tfae_have 2 → 3 := by
    intro hlength
    -- Finite length of the quotient and finiteness of `M` imply finiteness of `M'`.
    have hfiniteLength : IsFiniteLength R (M' ⧸ M.submoduleOf M') :=
      Module.length_ne_top_iff.mp hlength.ne
    have hNoetherian :
        IsNoetherian R (M' ⧸ M.submoduleOf M') :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp hfiniteLength).1
    letI : IsNoetherian R (M' ⧸ M.submoduleOf M') := hNoetherian
    letI : Module.Finite R (M' ⧸ M.submoduleOf M') := Module.IsNoetherian.finite R _
    have hfinite_sub : Module.Finite R (M.submoduleOf M') := by
      rw [Module.Finite.iff_fg]
      have hmap_eq : (M.submoduleOf M').map M'.subtype = M := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          simpa [Submodule.submoduleOf] using hy
        · intro hx
          refine ⟨⟨x, hMM' hx⟩, ?_, rfl⟩
          simpa [Submodule.submoduleOf] using hx
      have hfg_map : ((M.submoduleOf M').map M'.subtype).FG := by
        rw [hmap_eq]
        exact Submodule.IsLattice.fg (A := K) (M := M)
      exact Submodule.fg_of_fg_map_injective (f := M'.subtype) (N := M.submoduleOf M')
        M'.injective_subtype hfg_map
    letI : Module.Finite R (M.submoduleOf M') := hfinite_sub
    exact Module.Finite.of_submodule_quotient (M.submoduleOf M')
  tfae_have 3 → 1 := by
    intro hfinite
    letI : Module.Finite R M' := hfinite
    -- The ambient spanning condition is inherited from the smaller lattice `M`.
    refine Submodule.IsLattice.of_le_of_isLattice_of_fg K hMM' ?_
    simpa [Module.Finite.iff_fg] using hfinite
  tfae_finish

-- Proof sketch: one direction is the over-lattice criterion from clause (1), applied to the
-- inclusion `M' ≤ M`. For the converse, finite length of `M / M'` forces some power of the maximal
-- ideal to land inside `M'`, while finite generation of `M'` follows from finite colength, so `M'`
-- contains a `K`-basis of `V` and is therefore a lattice.
/-- Lemma 10.121.4 (2): for a submodule `M' ≤ M`, `M'` is a lattice if and only if the quotient
`M / M'` has finite length over `R`. -/
@[stacks 02MF]
theorem isLattice_iff_length_lt_top_of_le
    {M M' : Submodule R V} [Submodule.IsLattice K M] (hdim : ringKrullDim R = 1)
    (hM'M : M' ≤ M) :
    Submodule.IsLattice K M' ↔
      Module.length R (M ⧸ M'.submoduleOf M) < ⊤ := by
  constructor
  · intro hLattice
    letI : Submodule.IsLattice K M' := hLattice
    -- Reuse the over-lattice criterion with controller lattice `M'`.
    exact
      ((tfae_isLattice_length_lt_top_moduleFinite_of_le
        (R := R) (K := K) (V := V) (M := M') (M' := M) hdim hM'M).out 0 1 rfl rfl).mp
        inferInstance
  · intro hlength
    -- Route correction: finite colength produces a maximal-ideal power inside `M'`, so `M'`
    -- contains a nonzero scalar multiple of the lattice `M`.
    have hfiniteLength : IsFiniteLength R (M ⧸ M'.submoduleOf M) :=
      Module.length_ne_top_iff.mp hlength.ne
    obtain ⟨n, hn⟩ :=
      exists_pow_maximalIdeal_smul_top_le_of_isFiniteLength_quotient
        (R := R) (N := M'.submoduleOf M) hfiniteLength
    obtain ⟨a, ha_mem, ha_ne_zero⟩ :=
      exists_nonzero_mem_maximalIdeal_pow_of_ringKrullDim_eq_one (R := R) hdim n
    have hsmul_le : a • M ≤ M' :=
      smul_le_of_mem_of_submoduleOf_smul_top_le
        (R := R) (V := V) (M := M) (N := M') ha_mem hn
    have hfiniteM' : Module.Finite R M' :=
      by
        letI : IsNoetherian R M := inferInstance
        letI : IsNoetherian R M' := isNoetherian_of_le hM'M
        exact Module.IsNoetherian.finite R M'
    have hfgM' : M'.FG := by
      simpa [Module.Finite.iff_fg] using hfiniteM'
    letI : Submodule.IsLattice K (a • M : Submodule R V) :=
      Submodule.IsLattice.smul_of_ne_zero (R := R) (K := K) (V := V) ha_ne_zero
    -- Enlarge from the nonzero scalar lattice `a • M` to the finite submodule `M'`.
    exact Submodule.IsLattice.of_le_of_isLattice_of_fg K hsmul_le hfgM'

namespace Submodule.IsLattice

omit [IsLocalRing R] in
/-- Lemma 10.121.4 (3): the intersection of two lattices in `V` is again a lattice. -/
@[stacks 02MF]
theorem inf_of_isNoetherianRing {M M' : Submodule R V} [IsLattice K M] [IsLattice K M'] :
    IsLattice K (M ⊓ M') := by
  have hfiniteM : Module.Finite R M := inferInstance
  obtain ⟨a, ha_ne_zero, hsmul_le⟩ :=
    Submodule.IsLattice.exists_nonzero_scalar_smul_le_of_finite
      (R := R) (K := K) (V := V) (M := M') (N := M) hfiniteM
  have hsmul_inf : a • M ≤ M ⊓ M' := by
    refine le_inf ?_ hsmul_le
    rintro _ ⟨x, hx, rfl⟩
    exact M.smul_mem a hx
  have hfinite_inf : Module.Finite R ↥(M ⊓ M') := by
    letI : IsNoetherian R M := inferInstance
    letI : IsNoetherian R ↥(M ⊓ M') := isNoetherian_of_le inf_le_left
    exact Module.IsNoetherian.finite R ↥(M ⊓ M')
  have hfg_inf : (M ⊓ M').FG := by
    simpa [Module.Finite.iff_fg] using hfinite_inf
  letI : IsLattice K (a • M : Submodule R V) :=
    Submodule.IsLattice.smul_of_ne_zero (R := R) (K := K) (V := V) ha_ne_zero
  -- The intersection contains a nonzero scalar multiple of the lattice `M` and is finite.
  exact Submodule.IsLattice.of_le_of_isLattice_of_fg K hsmul_inf hfg_inf

end Submodule.IsLattice

-- Proof sketch: the sum `M ⊔ M'` contains the lattice `M`, so it spans `V`; then clause (1)
-- reduces latticehood of the sum to finite generation, which follows because it is generated by the
-- generators of `M` and `M'`.
/- Lemma 10.121.4 (3): the sum of two lattices in `V` is again a lattice. This is the canonical
owner theorem `Submodule.IsLattice.sup`. -/
recall Submodule.IsLattice.sup

-- Proof sketch: use additivity of module length on the short exact sequence
-- `0 → M' / M → M'' / M → M'' / M' → 0`, whose terms all have finite length because the three
-- submodules are lattices.
/-- Lemma 10.121.4 (4): for lattices `M ≤ M' ≤ M''`, the length of `M'' / M` is the sum of the
lengths of `M' / M` and `M'' / M'`. -/
@[stacks 02MF]
theorem length_eq_add_of_lattice_chain
    {M M' M'' : Submodule R V}
    [Submodule.IsLattice K M] [Submodule.IsLattice K M'] [Submodule.IsLattice K M'']
    (hdim : ringKrullDim R = 1) (hMM' : M ≤ M') (hM'M'' : M' ≤ M'') :
    Module.length R (M'' ⧸ M.submoduleOf M'') =
      Module.length R (M' ⧸ M.submoduleOf M') +
        Module.length R (M'' ⧸ M'.submoduleOf M'') := by
  have hsub :
      M.submoduleOf M'' ≤ M'.submoduleOf M'' := by
    intro x hx
    exact hMM' <| by simpa [Submodule.submoduleOf] using hx
  have hdecomp :
      Module.length R (M'' ⧸ M.submoduleOf M'') =
        Module.length R (M'' ⧸ M'.submoduleOf M'') +
          Module.length R
            ((M'.submoduleOf M'') ⧸
              (M.submoduleOf M'').submoduleOf (M'.submoduleOf M'')) := by
    -- Decompose `M'' / M` through the intermediate denominator `M'`.
    simpa using
      (length_quotient_eq_add_length_submodule_quotient_of_le
        (R := R) (W := M'') hsub)
  have hmid :
      Module.length R
          ((M'.submoduleOf M'') ⧸
            (M.submoduleOf M'').submoduleOf (M'.submoduleOf M'')) =
        Module.length R (M' ⧸ M.submoduleOf M') := by
    -- Normalize the transported middle quotient back to the source-facing quotient `M' / M`.
    let e : M'.submoduleOf M'' ≃ₗ[R] M' := Submodule.submoduleOfEquivOfLe hM'M''
    have hmap :
        ((M.submoduleOf M'').submoduleOf (M'.submoduleOf M'')).map
            (e : M'.submoduleOf M'' →ₗ[R] M') =
          M.submoduleOf M' := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [e, Submodule.submoduleOf] using hy
      · intro hx
        refine ⟨e.symm x, ?_, by simp [e]⟩
        simpa [e, Submodule.submoduleOf] using hx
    simpa [e] using
      (Submodule.Quotient.equiv
        ((M.submoduleOf M'').submoduleOf (M'.submoduleOf M''))
        (M.submoduleOf M') e hmap).length_eq
  calc
    Module.length R (M'' ⧸ M.submoduleOf M'') =
        Module.length R (M'' ⧸ M'.submoduleOf M'') +
          Module.length R
            ((M'.submoduleOf M'') ⧸
              (M.submoduleOf M'').submoduleOf (M'.submoduleOf M'')) := hdecomp
    _ = Module.length R (M'' ⧸ M'.submoduleOf M'') +
          Module.length R (M' ⧸ M.submoduleOf M') := by
          rw [hmid]
    _ = Module.length R (M' ⧸ M.submoduleOf M') +
          Module.length R (M'' ⧸ M'.submoduleOf M'') := by
          rw [add_comm]

/-- Helper for Lemma 10.121.4: quotients of comparable lattices have finite length. -/
theorem length_lt_top_of_isLattice_of_le
    {M M' : Submodule R V} [Submodule.IsLattice K M] [Submodule.IsLattice K M']
    (hdim : ringKrullDim R = 1) (hMM' : M ≤ M') :
    Module.length R (M' ⧸ M.submoduleOf M') < ⊤ := by
  exact
    ((tfae_isLattice_length_lt_top_moduleFinite_of_le
      (R := R) (K := K) (V := V) (M := M) (M' := M') hdim hMM').out 0 1 rfl rfl).mp
      inferInstance

-- Proof sketch: apply the additivity formula from clause (4) to the chains
-- `N ≤ M ∩ M' ≤ M` and `N ≤ M ∩ M' ≤ M'`, then subtract the resulting equalities after converting
-- the finite lengths to integers.
/-- Lemma 10.121.4 (5), first equality: for lattices `N ≤ M ∩ M'`, the difference of the
colengths of `M` and `M'` over `M ∩ M'` agrees with the difference of their colengths over `N`. -/
@[stacks 02MF]
theorem length_difference_inf_eq_length_difference_of_le_inf
    {M M' N : Submodule R V}
    [Submodule.IsLattice K M] [Submodule.IsLattice K M'] [Submodule.IsLattice K N]
    (hdim : ringKrullDim R = 1) (hNle : N ≤ M ⊓ M') :
    ((Module.length R (M ⧸ (M ⊓ M').submoduleOf M)).toNat : ℤ) -
        ((Module.length R (M' ⧸ (M ⊓ M').submoduleOf M')).toNat : ℤ) =
      ((Module.length R (M ⧸ N.submoduleOf M)).toNat : ℤ) -
        ((Module.length R (M' ⧸ N.submoduleOf M')).toNat : ℤ) := by
  let I : Submodule R V := M ⊓ M'
  letI : Submodule.IsLattice K I :=
    Submodule.IsLattice.inf_of_isNoetherianRing (R := R) (K := K) (V := V) (M := M) (M' := M')
  have hlenM :
      Module.length R (M ⧸ N.submoduleOf M) =
        Module.length R (I ⧸ N.submoduleOf I) +
          Module.length R (M ⧸ I.submoduleOf M) := by
    -- Compare the chains `N ≤ I ≤ M`.
    simpa [I] using
      (length_eq_add_of_lattice_chain
        (R := R) (K := K) (V := V) (M := N) (M' := I) (M'' := M) hdim hNle inf_le_left)
  have hlenM' :
      Module.length R (M' ⧸ N.submoduleOf M') =
        Module.length R (I ⧸ N.submoduleOf I) +
          Module.length R (M' ⧸ I.submoduleOf M') := by
    -- Compare the chains `N ≤ I ≤ M'`.
    simpa [I] using
      (length_eq_add_of_lattice_chain
        (R := R) (K := K) (V := V) (M := N) (M' := I) (M'' := M') hdim hNle inf_le_right)
  have hfiniteIN : Module.length R (I ⧸ N.submoduleOf I) < ⊤ :=
    length_lt_top_of_isLattice_of_le (R := R) (K := K) (V := V) (M := N) (M' := I) hdim hNle
  have hfiniteMI : Module.length R (M ⧸ I.submoduleOf M) < ⊤ :=
    length_lt_top_of_isLattice_of_le
      (R := R) (K := K) (V := V) (M := I) (M' := M) hdim inf_le_left
  have hfiniteM'I : Module.length R (M' ⧸ I.submoduleOf M') < ⊤ :=
    length_lt_top_of_isLattice_of_le
      (R := R) (K := K) (V := V) (M := I) (M' := M') hdim inf_le_right
  have hNatM :
      (Module.length R (M ⧸ N.submoduleOf M)).toNat =
        (Module.length R (I ⧸ N.submoduleOf I)).toNat +
          (Module.length R (M ⧸ I.submoduleOf M)).toNat := by
    simpa [ENat.toNat_add hfiniteIN.ne hfiniteMI.ne] using congrArg ENat.toNat hlenM
  have hNatM' :
      (Module.length R (M' ⧸ N.submoduleOf M')).toNat =
        (Module.length R (I ⧸ N.submoduleOf I)).toNat +
          (Module.length R (M' ⧸ I.submoduleOf M')).toNat := by
    simpa [ENat.toNat_add hfiniteIN.ne hfiniteM'I.ne] using congrArg ENat.toNat hlenM'
  have hIntM :
      ((Module.length R (M ⧸ N.submoduleOf M)).toNat : ℤ) =
        ((Module.length R (I ⧸ N.submoduleOf I)).toNat : ℤ) +
          ((Module.length R (M ⧸ I.submoduleOf M)).toNat : ℤ) := by
    exact_mod_cast hNatM
  have hIntM' :
      ((Module.length R (M' ⧸ N.submoduleOf M')).toNat : ℤ) =
        ((Module.length R (I ⧸ N.submoduleOf I)).toNat : ℤ) +
          ((Module.length R (M' ⧸ I.submoduleOf M')).toNat : ℤ) := by
    exact_mod_cast hNatM'
  -- Cancel the common quotient length `length(I / N)`.
  linarith

-- Proof sketch: identify the common difference using the first equality in clause (5), then
-- compute it again with the pair of chains from `M` and `M'` up to the common superlattice
-- `M ⊔ M'`.
/-- Lemma 10.121.4 (5), second equality: the same length difference can also be computed using the
over-lattice `M ⊔ M'`. -/
@[stacks 02MF]
theorem length_difference_inf_eq_length_difference_sup
    {M M' : Submodule R V} [Submodule.IsLattice K M] [Submodule.IsLattice K M']
    (hdim : ringKrullDim R = 1) :
    ((Module.length R (M ⧸ (M ⊓ M').submoduleOf M)).toNat : ℤ) -
        ((Module.length R (M' ⧸ (M ⊓ M').submoduleOf M')).toNat : ℤ) =
      ((Module.length R (↥(M ⊔ M') ⧸ M'.submoduleOf (M ⊔ M'))).toNat : ℤ) -
        ((Module.length R (↥(M ⊔ M') ⧸ M.submoduleOf (M ⊔ M'))).toNat : ℤ) := by
  let I : Submodule R V := M ⊓ M'
  let S : Submodule R V := M ⊔ M'
  letI : Submodule.IsLattice K I :=
    Submodule.IsLattice.inf_of_isNoetherianRing (R := R) (K := K) (V := V) (M := M) (M' := M')
  have hlenM :
      Module.length R (S ⧸ I.submoduleOf S) =
        Module.length R (M ⧸ I.submoduleOf M) +
          Module.length R (S ⧸ M.submoduleOf S) := by
    -- Compare the chains `I ≤ M ≤ S`.
    simpa [I, S] using
      (length_eq_add_of_lattice_chain
        (R := R) (K := K) (V := V) (M := I) (M' := M) (M'' := S) hdim inf_le_left le_sup_left)
  have hlenM' :
      Module.length R (S ⧸ I.submoduleOf S) =
        Module.length R (M' ⧸ I.submoduleOf M') +
          Module.length R (S ⧸ M'.submoduleOf S) := by
    -- Compare the chains `I ≤ M' ≤ S`.
    simpa [I, S] using
      (length_eq_add_of_lattice_chain
        (R := R) (K := K) (V := V) (M := I) (M' := M') (M'' := S) hdim inf_le_right le_sup_right)
  have hfiniteMI : Module.length R (M ⧸ I.submoduleOf M) < ⊤ :=
    length_lt_top_of_isLattice_of_le
      (R := R) (K := K) (V := V) (M := I) (M' := M) hdim inf_le_left
  have hfiniteM'I : Module.length R (M' ⧸ I.submoduleOf M') < ⊤ :=
    length_lt_top_of_isLattice_of_le
      (R := R) (K := K) (V := V) (M := I) (M' := M') hdim inf_le_right
  have hfiniteSM : Module.length R (S ⧸ M.submoduleOf S) < ⊤ :=
    length_lt_top_of_isLattice_of_le
      (R := R) (K := K) (V := V) (M := M) (M' := S) hdim le_sup_left
  have hfiniteSM' : Module.length R (S ⧸ M'.submoduleOf S) < ⊤ :=
    length_lt_top_of_isLattice_of_le
      (R := R) (K := K) (V := V) (M := M') (M' := S) hdim le_sup_right
  have hNatM :
      (Module.length R (S ⧸ I.submoduleOf S)).toNat =
        (Module.length R (M ⧸ I.submoduleOf M)).toNat +
          (Module.length R (S ⧸ M.submoduleOf S)).toNat := by
    simpa [ENat.toNat_add hfiniteMI.ne hfiniteSM.ne] using congrArg ENat.toNat hlenM
  have hNatM' :
      (Module.length R (S ⧸ I.submoduleOf S)).toNat =
        (Module.length R (M' ⧸ I.submoduleOf M')).toNat +
          (Module.length R (S ⧸ M'.submoduleOf S)).toNat := by
    simpa [ENat.toNat_add hfiniteM'I.ne hfiniteSM'.ne] using congrArg ENat.toNat hlenM'
  have hIntM :
      ((Module.length R (S ⧸ I.submoduleOf S)).toNat : ℤ) =
        ((Module.length R (M ⧸ I.submoduleOf M)).toNat : ℤ) +
          ((Module.length R (S ⧸ M.submoduleOf S)).toNat : ℤ) := by
    exact_mod_cast hNatM
  have hIntM' :
      ((Module.length R (S ⧸ I.submoduleOf S)).toNat : ℤ) =
        ((Module.length R (M' ⧸ I.submoduleOf M')).toNat : ℤ) +
          ((Module.length R (S ⧸ M'.submoduleOf S)).toNat : ℤ) := by
    exact_mod_cast hNatM'
  -- Cancel the common quotient length `length(S / I)`.
  linarith

-- Proof sketch: apply clause (4) to the chains `M ≤ N'` and `M' ≤ N'`, then subtract the two
-- equalities. Comparing with the second equality in clause (5) yields the stated common value of
-- the length difference.
/-- Lemma 10.121.4 (5), final equality: if `M ⊔ M' ≤ N'`, the same length difference is also
equal to the difference of the colengths of `M` and `M'` inside `N'`. -/
@[stacks 02MF]
theorem length_difference_sup_eq_length_difference_of_sup_le
    {M M' N' : Submodule R V}
    [Submodule.IsLattice K M] [Submodule.IsLattice K M'] [Submodule.IsLattice K N']
    (hdim : ringKrullDim R = 1) (hsup : M ⊔ M' ≤ N') :
    ((Module.length R (↥(M ⊔ M') ⧸ M'.submoduleOf (M ⊔ M'))).toNat : ℤ) -
        ((Module.length R (↥(M ⊔ M') ⧸ M.submoduleOf (M ⊔ M'))).toNat : ℤ) =
      ((Module.length R (N' ⧸ M'.submoduleOf N')).toNat : ℤ) -
        ((Module.length R (N' ⧸ M.submoduleOf N')).toNat : ℤ) := by
  let S : Submodule R V := M ⊔ M'
  have hlenM :
      Module.length R (N' ⧸ M.submoduleOf N') =
        Module.length R (S ⧸ M.submoduleOf S) +
          Module.length R (N' ⧸ S.submoduleOf N') := by
    -- Compare the chains `M ≤ S ≤ N'`.
    simpa [S] using
      (length_eq_add_of_lattice_chain
        (R := R) (K := K) (V := V) (M := M) (M' := S) (M'' := N') hdim le_sup_left hsup)
  have hlenM' :
      Module.length R (N' ⧸ M'.submoduleOf N') =
        Module.length R (S ⧸ M'.submoduleOf S) +
          Module.length R (N' ⧸ S.submoduleOf N') := by
    -- Compare the chains `M' ≤ S ≤ N'`.
    simpa [S] using
      (length_eq_add_of_lattice_chain
        (R := R) (K := K) (V := V) (M := M') (M' := S) (M'' := N') hdim le_sup_right hsup)
  have hfiniteSM : Module.length R (S ⧸ M.submoduleOf S) < ⊤ :=
    length_lt_top_of_isLattice_of_le
      (R := R) (K := K) (V := V) (M := M) (M' := S) hdim le_sup_left
  have hfiniteSM' : Module.length R (S ⧸ M'.submoduleOf S) < ⊤ :=
    length_lt_top_of_isLattice_of_le
      (R := R) (K := K) (V := V) (M := M') (M' := S) hdim le_sup_right
  have hfiniteN'S : Module.length R (N' ⧸ S.submoduleOf N') < ⊤ :=
    length_lt_top_of_isLattice_of_le
      (R := R) (K := K) (V := V) (M := S) (M' := N') hdim hsup
  have hNatM :
      (Module.length R (N' ⧸ M.submoduleOf N')).toNat =
        (Module.length R (S ⧸ M.submoduleOf S)).toNat +
          (Module.length R (N' ⧸ S.submoduleOf N')).toNat := by
    simpa [ENat.toNat_add hfiniteSM.ne hfiniteN'S.ne] using congrArg ENat.toNat hlenM
  have hNatM' :
      (Module.length R (N' ⧸ M'.submoduleOf N')).toNat =
        (Module.length R (S ⧸ M'.submoduleOf S)).toNat +
          (Module.length R (N' ⧸ S.submoduleOf N')).toNat := by
    simpa [ENat.toNat_add hfiniteSM'.ne hfiniteN'S.ne] using congrArg ENat.toNat hlenM'
  have hIntM :
      ((Module.length R (N' ⧸ M.submoduleOf N')).toNat : ℤ) =
        ((Module.length R (S ⧸ M.submoduleOf S)).toNat : ℤ) +
          ((Module.length R (N' ⧸ S.submoduleOf N')).toNat : ℤ) := by
    exact_mod_cast hNatM
  have hIntM' :
      ((Module.length R (N' ⧸ M'.submoduleOf N')).toNat : ℤ) =
        ((Module.length R (S ⧸ M'.submoduleOf S)).toNat : ℤ) +
          ((Module.length R (N' ⧸ S.submoduleOf N')).toNat : ℤ) := by
    exact_mod_cast hNatM'
  -- Cancel the common quotient length `length(N' / S)`.
  linarith

end
