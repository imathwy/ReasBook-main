import Mathlib
import Mathlib.RingTheory.OrderOfVanishing
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_121_1 (from Chap10) -/
universe u

open scoped nonZeroDivisors

section

variable {R : Type u} [CommRing R]

/-
Domain triage:
* primary domain: order of vanishing and lengths of principal quotients in commutative algebra;
* sampled owner API: `Ring.ord`, `Ring.ord_mul`, `isFiniteLength_quotient_span_singleton`, and
  `Module.length_ne_top_iff`;
* `core/canonical`: `Ring.ord` is the owner for the length of `R / (x)`, and `Ring.ord_mul` is
  the canonical multiplicativity theorem;
* `bridge/view`: the textbook `length_R (R / (x))` formulas are obtained by unfolding `Ring.ord`,
  while finite-length statements are derived from `IsFiniteLength`.

Primitive-vs-derived split:
* primitive data: the ring element `x` and the owner abstractions `Ring.ord` / `IsFiniteLength`;
* derived API: the source-facing equalities between explicit quotient lengths and the `< ⊤`
  reformulation of finite length.
-/

/- Owner bridge: the multiplicative length formula is exactly `Ring.ord_mul` with `Ring.ord`
unfolded. -/
recall Ring.ord_mul

/-- Lemma 10.121.1, source-facing form of `Ring.ord_mul`: if `b` is a nonzerodivisor, then
`length_R (R / (ab)) = length_R (R / (a)) + length_R (R / (b))`. -/
theorem length_quotient_span_singleton_mul_eq_add_of_mem_nonZeroDivisors
    {a b : R} (hb : b ∈ nonZeroDivisors R) :
    Module.length R (R ⧸ Ideal.span {a * b}) =
      Module.length R (R ⧸ Ideal.span {a}) + Module.length R (R ⧸ Ideal.span {b}) := by
  simpa [Ring.ord] using Ring.ord_mul R hb

end

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]

/- Owner bridge: in dimension at most `1`, finite length of `R / xR` is owned by
`isFiniteLength_quotient_span_singleton`, and `Module.length_ne_top_iff` converts that owner
statement to the source-facing inequality. -/
recall isFiniteLength_quotient_span_singleton
recall Module.length_ne_top_iff

/-- If `x` is a nonzerodivisor in a Noetherian ring of Krull dimension at most `1`, then
`R / (x)` has finite length over `R`. -/
theorem length_quotient_span_singleton_lt_top_of_mem_nonZeroDivisors
    {x : R} (hx : x ∈ nonZeroDivisors R) :
    Module.length R (R ⧸ Ideal.span {x}) < ⊤ := by
  simpa [lt_top_iff_ne_top] using
    (Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton R hx))

end

/-! ### Definition_10_121_2 (from Chap10) -/
/- Domain-style sampling in the order-of-vanishing API:
- primitive ring-level data: `Ring.ord`
- multiplicative ring-level bridge: `Ring.ordMonoidWithZeroHom`
- fraction-field owner: `Ring.ordFrac`
- quotient-rule computation: `Ring.ordFrac_eq_div`

Layer triage:
- `source-facing`: the textbook additive notation `ord_R : Kˣ → ℤ`
- `core/canonical`: mathlib already owns the multiplicative fraction-field order of vanishing as
  `Ring.ordFrac`
- `bridge/view`: `Ring.ord` and `Ring.ordFrac_eq_div` give the ring-level and presentation-level
  views of that owner, while `WithZero.log` recovers the additive textbook form

Primitive-vs-derived split:
- primitive data lives in the ring-level length definition `Ring.ord`
- the fraction-field valuation `Ring.ordFrac` is the canonical owner used downstream
- the formula on a presentation `x / y` is derived API, exposed by `Ring.ordFrac_eq_div`
-/

/- Definition 10.121.2: the order of vanishing along a one-dimensional Noetherian local subring
`R` of a field `K` is the canonical fraction-field order-of-vanishing map `Ring.ordFrac`; after
applying `WithZero.log` on nonzero elements, this recovers the textbook additive function
`ord_R : Kˣ → ℤ`. -/
recall Ring.ordFrac

/- Companion recall: for an element `x : R`, the ring-level order of vanishing `Ring.ord R x` is
defined as the module length of `R / (x)`, matching the formula `length_R(R/(x))`. -/
recall Ring.ord

/- Companion recall: the quotient-rule formula for fractions is encoded by `Ring.ordFrac_eq_div`,
which computes the fraction-field order of vanishing on a presentation `x / y` with `x, y ≠ 0`. -/
recall Ring.ordFrac_eq_div

/-! ### Definition_10_121_3 (from Chap10) -/
universe u v w

section

variable {R : Type u} {K : Type v} {V : Type w}
variable [CommRing R] [Field K] [Algebra R K]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/- Domain-style sampling in the fraction-field lattice API:
- primitive data: finite generation of an `R`-submodule and the spanning condition over `K`
- core/canonical owner: `Submodule.IsLattice K`
- bridge/view: the textbook conjunction `Module.Finite R L ∧ Submodule.span K (L : Set V) = ⊤`

Layer triage:
- `source-facing`: Definition 10.121.3 identifies the notion of a lattice in `V`
- `core/canonical`: mathlib already owns this notion as `Submodule.IsLattice K`
- `bridge/view`: the textbook finite-generation-plus-span formulation is a companion restatement,
  not a second owner

Primitive-vs-derived split:
- the owner stores the primitive fields `fg` and `span_eq_top`
- `Module.Finite R L` is derived from `fg` by the canonical instance
- the source-facing conjunction is therefore derived API only
-/

/- Definition 10.121.3: in the fraction-field setting, the canonical notion of a lattice in `V`
is mathlib's `Submodule.IsLattice K`, i.e. an `R`-submodule that is finitely generated and whose
`K`-span is all of `V`. -/
recall Submodule.IsLattice

namespace Submodule

open Module.Finite

/-- The textbook formulation of a lattice is equivalent to mathlib's `Submodule.IsLattice K`. -/
theorem isLattice_iff_moduleFinite_and_span_eq_top (L : Submodule R V) :
    IsLattice K L ↔ Module.Finite R L ∧ span K (L : Set V) = ⊤ := by
  constructor
  · intro hL
    let _ : IsLattice K L := hL
    exact ⟨inferInstance, hL.span_eq_top⟩
  · rintro ⟨hfinite, hspan⟩
    exact ⟨iff_fg.mp hfinite, hspan⟩

end Submodule

end

/-! ### Lemma_10_121_4 (from Chap10) -/
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

/-! ### Definition_10_121_5 (from Chap10) -/
universe u v w

section

variable {R : Type u} {K : Type v} {V : Type w}
variable [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K] [Ring.KrullDimLE 1 R]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/- Domain-style sampling:
- primary domain: lattices in a fraction-field vector space over a one-dimensional Noetherian local
  domain and their finite-colength quotients;
- sampled owner declarations: `Submodule.IsLattice`, `Submodule.submoduleOf`, `Module.length`, and
  `Module.length_ne_top_iff`;
- core/canonical owner: latticehood is already owned by `Submodule.IsLattice K`, while the new
  source-facing object here is the integer-valued distance attached to a pair of lattices;
- primitive data: the two submodules `M` and `M'`;
- derived API: the two quotient lengths from the common intersection are derived from those
  submodules, but they are only source-faithful integers in the ambient finite-length regime
  provided by the one-dimensional local-domain hypotheses already used in `10.121.x`.
-/

namespace Submodule

variable (M M' : Submodule R V)
variable [IsLattice K M] [IsLattice K M']

/-- Definition 10.121.5: for two lattices `M` and `M'` in a `K`-vector space `V`, their distance
is the difference between the colength of `M ∩ M'` in `M` and the colength of `M ∩ M'` in `M'`,
in the one-dimensional Noetherian local-domain fraction-field setting where these colengths are
finite. -/
noncomputable def latticeDistance : ℤ :=
  ((Module.length R (M ⧸ (M ⊓ M').submoduleOf M)).toNat : ℤ) -
    ((Module.length R (M' ⧸ (M ⊓ M').submoduleOf M')).toNat : ℤ)

/-- The lattice distance is the difference of the two quotient colengths from the common
intersection. -/
-- Proof sketch: unfold `latticeDistance`; the statement is definitional.
theorem latticeDistance_def :
    latticeDistance M M' =
      ((Module.length R (M ⧸ (M ⊓ M').submoduleOf M)).toNat : ℤ) -
        ((Module.length R (M' ⧸ (M ⊓ M').submoduleOf M')).toNat : ℤ) := sorry

end Submodule

end

/-! ### Lemma_10_121_6 (from Chap10) -/
universe u v w

section

variable {R : Type u} {K : Type v} {V : Type w}
variable [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K] [Ring.KrullDimLE 1 R]
variable [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

namespace Submodule

variable (M M' : Submodule R V)

/-- Helper for Lemma 10.121.6: under the ambient `KrullDim ≤ 1` hypothesis, a non-field local
domain has Krull dimension exactly `1`. -/
lemma ringKrullDim_eq_one_of_not_isField (hR : ¬ IsField R) :
    ringKrullDim R = 1 := by
  -- The ambient typeclass gives the upper bound `dim R ≤ 1`.
  have hle : ringKrullDim R ≤ 1 :=
    Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 R)
  -- Dimension `0` would force `R` to be a field, contradicting the hypothesis.
  have hnotle_zero : ¬ ringKrullDim R ≤ 0 := by
    intro hzero
    let _ : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr hzero
    exact hR Ring.KrullDimLE.isField_of_isDomain
  have hge : 1 ≤ ringKrullDim R :=
    Order.succ_le_of_lt (lt_of_not_ge hnotle_zero)
  exact le_antisymm hle hge

/-- Helper for Lemma 10.121.6: if the base ring is already a field, then any lattice is the whole
ambient vector space. -/
lemma eq_top_of_isField_of_isLattice [IsLattice K M] (hfield : IsField R) :
    M = ⊤ := by
  classical
  -- Surjectivity of `R → K` lets us rewrite every finite `K`-linear combination with
  -- coefficients coming from `R`, so the `K`-span condition forces `M = ⊤`.
  have hsurj : Function.Surjective (algebraMap R K) :=
    (IsFractionRing.surjective_iff_isField (R := R) (K := K)).mpr hfield
  have hspan : Submodule.span K (M : Set V) = ⊤ :=
    Submodule.IsLattice.span_eq_top (A := K) (M := M)
  apply eq_top_iff.mpr
  intro x hx
  have hxspan : x ∈ Submodule.span K (M : Set V) := by
    simpa [hspan] using hx
  obtain ⟨T, hTM, hxT⟩ := Submodule.mem_span_finite_of_mem_span hxspan
  rw [Submodule.mem_span_finset] at hxT
  obtain ⟨f, hf, hsum⟩ := hxT
  rw [← hsum]
  refine Submodule.sum_mem M fun a ha ↦ ?_
  have haM : a ∈ M := hTM ha
  obtain ⟨r, hr⟩ := hsurj (f a)
  rw [← hr]
  simpa using Submodule.smul_mem M r haM

/-- Helper for Lemma 10.121.6: in the field case, every lattice distance is zero because both
lattices are equal to `⊤`. -/
lemma latticeDistance_eq_zero_of_isField [IsLattice K M] [IsLattice K M'] (hfield : IsField R) :
    latticeDistance M M' = 0 := by
  -- Collapse both lattices to `⊤` and then simplify the defining quotient lengths.
  rw [eq_top_of_isField_of_isLattice (M := M) hfield, eq_top_of_isField_of_isLattice (M := M') hfield]
  rw [Submodule.latticeDistance_def]
  simp

-- Proof sketch: unfold `latticeDistance`; both quotient-length terms are identical when the two
-- lattices agree, so the integer difference is zero.
/-- The distance from a lattice to itself is zero. -/
theorem latticeDistance_self [IsLattice K M] :
    latticeDistance M M = 0 := by
  -- Unfold the distance and simplify the quotient by the full submodule.
  rw [Submodule.latticeDistance_def]
  simp

variable (M'' : Submodule R V)

-- Proof sketch: choose a lattice contained in all three lattices, rewrite each distance as the
-- difference of two finite lengths relative to that common sublattice, and use additivity of
-- module length in short exact sequences to telescope the resulting expression.
/-- Lemma 10.121.6: for lattices `M`, `M'`, and `M''` in a finite-dimensional `K`-vector space
over a one-dimensional Noetherian local domain `R`, the lattice distance is additive:
`d(M, M'') = d(M, M') + d(M', M'')`. The canonical ambient hypothesis is
`[Ring.KrullDimLE 1 R]`. -/
theorem latticeDistance_add [IsLattice K M] [IsLattice K M'] [IsLattice K M'']
    : latticeDistance M M'' = latticeDistance M M' + latticeDistance M' M'' := by
  by_cases hfield : IsField R
  · -- In the field case every lattice is `⊤`, so all three distances vanish.
    rw [latticeDistance_eq_zero_of_isField (M := M) (M' := M'') hfield]
    rw [latticeDistance_eq_zero_of_isField (M := M) (M' := M') hfield]
    rw [latticeDistance_eq_zero_of_isField (M := M') (M' := M'') hfield]
    simp
  · -- In the genuine dimension-one case, compare all three distances through one common lattice.
    let N : Submodule R V := M ⊓ M' ⊓ M''
    have hdim : ringKrullDim R = 1 :=
      ringKrullDim_eq_one_of_not_isField (R := R) hfield
    have hMM' : IsLattice K (M ⊓ M') :=
      Submodule.IsLattice.inf_of_isNoetherianRing (K := K) (M := M) (M' := M')
    letI : IsLattice K N := by
      simpa [N] using
        (Submodule.IsLattice.inf_of_isNoetherianRing (K := K) (M := M ⊓ M') (M' := M'')
          : IsLattice K ((M ⊓ M') ⊓ M''))
    have hNleM : N ≤ M := by
      exact inf_le_left.trans inf_le_left
    have hNleM' : N ≤ M' := by
      exact inf_le_left.trans inf_le_right
    have hNleM'' : N ≤ M'' := by
      exact inf_le_right
    have hNleMM'' : N ≤ M ⊓ M'' := by
      exact le_inf hNleM hNleM''
    have hNleMM' : N ≤ M ⊓ M' := by
      exact le_inf hNleM hNleM'
    have hNleM'M'' : N ≤ M' ⊓ M'' := by
      exact le_inf hNleM' hNleM''
    have hMM'' :
        latticeDistance M M'' =
          ((Module.length R (M ⧸ N.submoduleOf M)).toNat : ℤ) -
            ((Module.length R (M'' ⧸ N.submoduleOf M'')).toNat : ℤ) := by
      -- Rewrite the first distance using the common controlling lattice `N`.
      rw [Submodule.latticeDistance_def]
      exact length_difference_inf_eq_length_difference_of_le_inf
        (R := R) (K := K) (V := V) (M := M) (M' := M'') (N := N) hdim hNleMM''
    have hMM' :
        latticeDistance M M' =
          ((Module.length R (M ⧸ N.submoduleOf M)).toNat : ℤ) -
            ((Module.length R (M' ⧸ N.submoduleOf M')).toNat : ℤ) := by
      -- Rewrite the second distance through the same lattice `N`.
      rw [Submodule.latticeDistance_def]
      exact length_difference_inf_eq_length_difference_of_le_inf
        (R := R) (K := K) (V := V) (M := M) (M' := M') (N := N) hdim hNleMM'
    have hM'M'' :
        latticeDistance M' M'' =
          ((Module.length R (M' ⧸ N.submoduleOf M')).toNat : ℤ) -
            ((Module.length R (M'' ⧸ N.submoduleOf M'')).toNat : ℤ) := by
      -- Rewrite the third distance through the same lattice `N`.
      rw [Submodule.latticeDistance_def]
      exact length_difference_inf_eq_length_difference_of_le_inf
        (R := R) (K := K) (V := V) (M := M') (M' := M'') (N := N) hdim hNleM'M''
    rw [hMM'', hMM', hM'M'']
    ring

-- Proof sketch: unfold `latticeDistance`; swapping `M` and `M'` exchanges the two quotient-length
-- terms, so the defining integer difference changes sign.
/-- Swapping the two lattices negates the lattice distance. -/
theorem latticeDistance_neg_swap [IsLattice K M] [IsLattice K M'] :
    latticeDistance M M' = - latticeDistance M' M := by
  -- Apply additivity to the triangle `M → M' → M` and isolate the skew-symmetry relation.
  have hadd :
      latticeDistance M M = latticeDistance M M' + latticeDistance M' M :=
    latticeDistance_add (M := M) (M' := M') (M'' := M)
  have hself : latticeDistance M M = 0 := latticeDistance_self (M := M)
  linarith

end Submodule

end

/-! ### Lemma_10_121_7 (from Chap10) -/
universe u v w

section

variable {R : Type u} {K : Type v} {V : Type w}
variable [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
variable [FiniteDimensional K V]

open Submodule

/- Domain triage:
* primary domain: lattices in a fraction-field vector space and the order of vanishing of the
  determinant of a `K`-linear automorphism;
* sampled owner API: `Submodule.IsLattice`, `Submodule.latticeDistance`, `Ring.ordFrac`, and
  `WithZero.log`;
* core/canonical owners: `Submodule.IsLattice K` for latticehood and `Ring.ordFrac R` for the
  multiplicative order of vanishing;
* source-facing bridge: `WithZero.log` is the additive recovery map singled out in
  `Definition_10_121_2`;
* layer: this numbered item is a `bridge/view` theorem comparing the source-facing additive
  lattice distance with the canonical determinant valuation;
* primitive data: the lattice `M` and automorphism `φ`;
* derived API: the raw `Ring.ordFrac` equality is only a companion bridge, while the main theorem
  should live at the additive/source-facing layer.
-/

private instance isLattice_map_restrictScalars
    (φ : V ≃ₗ[K] V) (M : Submodule R V) [IsLattice K M] :
    IsLattice K (M.map ((φ.restrictScalars R) : V →ₗ[R] V)) where
  fg := by
    -- A lattice image stays finitely generated because `Submodule.map` preserves finite generation.
    exact IsLattice.fg.map ((φ.restrictScalars R) : V →ₗ[R] V)
  span_eq_top := by
    let φR : V ≃ₗ[R] V := φ.restrictScalars R
    have himage :
        (φ : V →ₗ[K] V) '' (M : Set V) =
          ((M.map ((φ.restrictScalars R) : V →ₗ[R] V) : Submodule R V) : Set V) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact Submodule.mem_map_of_mem hy
      · intro hx
        refine ⟨φ.symm x, ?_, by simp⟩
        simpa [φR] using
          (Submodule.mem_map_equiv
            (p := M) (e := φR) (x := x)).mp hx
    -- Map the spanning equality for `M` across the `K`-linear automorphism.
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := φ.surjective x
    have hy : y ∈ Submodule.span K (M : Set V) := by
      rw [IsLattice.span_eq_top]
      trivial
    have hφy : φ y ∈ (Submodule.span K (M : Set V)).map (φ : V →ₗ[K] V) :=
      Submodule.mem_map_of_mem hy
    rw [Submodule.map_span, himage] at hφy
    exact hφy

-- Proof sketch: first prove the canonical multiplicative bridge in `Ring.ordFrac`, then pass to
-- the additive textbook order of vanishing by applying `WithZero.log` as in
-- `Definition_10_121_2`.
/-- Companion bridge: the lattice-distance identity expressed directly in the canonical
`Ring.ordFrac` owner. -/
theorem exp_latticeDistance_image_eq_ordFrac_det
    [Ring.KrullDimLE 1 R] (φ : V ≃ₗ[K] V) (M : Submodule R V) [IsLattice K M] :
    WithZero.exp (latticeDistance M (M.map ((φ.restrictScalars R) : V →ₗ[R] V))) =
      Ring.ordFrac R (LinearEquiv.det φ : K) := by
  -- TODO: first prove lattice-independence and multiplicativity without importing the currently
  -- broken earlier file `Lemma_10_121_6`, then reduce to standard generators in `K^n`.
  sorry

/-- Lemma 10.121.7: for a lattice `M` in a finite-dimensional `K`-vector space, the lattice
distance between `M` and its image under a `K`-linear automorphism `φ` equals the additive order
of vanishing of `det φ`, recovered from the canonical `Ring.ordFrac` owner by `WithZero.log`. -/
theorem latticeDistance_image_eq_ordFrac_det
    [Ring.KrullDimLE 1 R] (φ : V ≃ₗ[K] V) (M : Submodule R V) [IsLattice K M] :
    latticeDistance M (M.map ((φ.restrictScalars R) : V →ₗ[R] V)) =
      WithZero.log (Ring.ordFrac R (LinearEquiv.det φ : K)) := by
  simpa using congrArg WithZero.log (exp_latticeDistance_image_eq_ordFrac_det φ M)

end

/-! ### Lemma_10_121_8 (from Chap10) -/
open scoped BigOperators nonZeroDivisors
open IsLocalRing

noncomputable section

universe u v

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section InjectiveAlgebraMapFact

variable (A : Type u) {B : Type v}
variable [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
variable [Algebra (FractionRing A) (FractionRing B)]
variable [IsScalarTower A (FractionRing A) (FractionRing B)]

local instance injectiveAlgebraMapFact_of_finiteFractionRingExtension :
    Fact (Function.Injective (algebraMap A B)) :=
  ⟨algebraMap_injective_of_field_isFractionRing A B (FractionRing A) (FractionRing B)⟩

section

variable (A : Type u) {B : Type v}
variable [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
variable [Algebra (FractionRing A) (FractionRing B)]
variable [IsScalarTower A (FractionRing A) (FractionRing B)]

/-- Under a finite-type extension of domains with finite fraction-field extension from a
Noetherian local domain of Krull dimension at most `1`, the target ring has finite maximal
spectrum. -/
theorem finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension
    [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType A B]
    [FiniteDimensional (FractionRing A) (FractionRing B)] :
    Finite (MaximalSpectrum B) := by
  sorry

end

section

variable (A : Type u) {B : Type v}
variable [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
variable [IsLocalRing A]
variable [Algebra (FractionRing A) (FractionRing B)]
variable [IsScalarTower A (FractionRing A) (FractionRing B)]

/-- Every maximal ideal of `B` lies over the maximal ideal of the local base ring `A`. -/
theorem comap_maximalIdeal_of_finiteType_of_finiteFractionRingExtension
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType A B]
    [FiniteDimensional (FractionRing A) (FractionRing B)]
    (m : MaximalSpectrum B) :
    Ideal.comap (algebraMap A B) m.asIdeal = maximalIdeal A := by
  sorry

local notation "κA" => Ideal.ResidueField (maximalIdeal A)

instance residueFieldAlgebra_of_finiteType_of_finiteFractionRingExtension
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType A B]
    [FiniteDimensional (FractionRing A) (FractionRing B)]
    (m : MaximalSpectrum B) :
    Algebra κA (Ideal.ResidueField m.asIdeal) :=
  (Ideal.ResidueField.map (maximalIdeal A) m.asIdeal (algebraMap A B)
    (comap_maximalIdeal_of_finiteType_of_finiteFractionRingExtension A m).symm).toAlgebra

/-- The residue-field extension at any maximal ideal of `B` is module-finite over the residue field
of the maximal ideal of `A`. -/
theorem moduleFinite_residueField_of_finiteType_of_finiteFractionRingExtension
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType A B]
    [FiniteDimensional (FractionRing A) (FractionRing B)]
    (m : MaximalSpectrum B) :
    Module.Finite κA (Ideal.ResidueField m.asIdeal) := by
  sorry

instance residueFieldModuleFinite_of_finiteType_of_finiteFractionRingExtension
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType A B]
    [FiniteDimensional (FractionRing A) (FractionRing B)]
    (m : MaximalSpectrum B) :
    Module.Finite κA (Ideal.ResidueField m.asIdeal) :=
  moduleFinite_residueField_of_finiteType_of_finiteFractionRingExtension A m

end

section

variable (A : Type u) {B : Type v}
variable [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
variable [Algebra (FractionRing A) (FractionRing B)]
variable [IsScalarTower A (FractionRing A) (FractionRing B)]

private theorem isScalarTower_fractionRing_localization_fractionRing [Module.Finite A B] :
    let K := FractionRing A
    let L := FractionRing B
    let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors A)
    let S := Localization M
    let _ : FaithfulSMul A B :=
      (faithfulSMul_iff_algebraMap_injective A B).mpr
        (algebraMap_injective_of_field_isFractionRing A B K L)
    let hS : M ≤ B⁰ :=
      algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul B
        (show nonZeroDivisors A ≤ A⁰ by rfl)
    let hS' : M ≤ Submonoid.comap (RingHom.id B) B⁰ := by
      simpa using hS
    let f : S →+* L := IsLocalization.map L (RingHom.id B) hS'
    let _ : Algebra S L := f.toAlgebra
    IsScalarTower K S L := by
  simp only
  let K := FractionRing A
  let L := FractionRing B
  let _ : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr
      (algebraMap_injective_of_field_isFractionRing A B K L)
  let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors A)
  let S := Localization M
  have hS : M ≤ B⁰ :=
    algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul B (show nonZeroDivisors A ≤ A⁰ by rfl)
  have hS' : M ≤ Submonoid.comap (RingHom.id B) B⁰ := by
    simpa using hS
  let f : S →+* L := IsLocalization.map L (RingHom.id B) hS'
  let _ : Algebra S L := f.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  apply IsLocalization.ringHom_ext (nonZeroDivisors A)
  ext a
  have h1 : (algebraMap K L) ((algebraMap A K) a) = algebraMap A L a :=
    (IsScalarTower.algebraMap_apply A K L a).symm
  have h2 : (((algebraMap S L).comp (algebraMap K S)).comp (algebraMap A K)) a =
      algebraMap A L a := by
    rw [RingHom.comp_apply, RingHom.comp_apply, (IsScalarTower.algebraMap_apply A K S a).symm]
    have hABS : algebraMap A S a = algebraMap B S (algebraMap A B a) :=
      IsScalarTower.algebraMap_apply A B S a
    rw [hABS]
    have hmap : f (algebraMap B S (algebraMap A B a)) = algebraMap B L (algebraMap A B a) := by
      simpa [f] using (IsLocalization.map_eq hS' (algebraMap A B a) : _)
    simpa [IsScalarTower.algebraMap_apply A B L] using hmap
  exact h1.trans h2.symm

private theorem finiteDimensional_fractionRing_of_moduleFinite [Module.Finite A B] :
    FiniteDimensional (FractionRing A) (FractionRing B) := by
  let K := FractionRing A
  let L := FractionRing B
  let _ : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr
      (algebraMap_injective_of_field_isFractionRing A B K L)
  let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors A)
  let S := Localization M
  have hS : M ≤ B⁰ :=
    algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul B (show nonZeroDivisors A ≤ A⁰ by rfl)
  have hS' : M ≤ Submonoid.comap (RingHom.id B) B⁰ := by
    simpa using hS
  let f : S →+* L := IsLocalization.map L (RingHom.id B) hS'
  let _ : Algebra S L := f.toAlgebra
  let _ : IsScalarTower B S L := IsScalarTower.of_algebraMap_eq' (by
    rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp hS', RingHomCompTriple.comp_eq])
  let _ : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hS
  let _ : IsFractionRing S L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M S L
  let _ : FiniteDimensional K S := inferInstance
  let _ : Field S := fieldOfFiniteDimensional K S
  let _ : IsScalarTower K S L := isScalarTower_fractionRing_localization_fractionRing A
  let _ : FiniteDimensional S L := by
    let _ : IsFractionRing S S := IsFractionRing.idem S S
    exact LinearEquiv.finiteDimensional
      (((FractionRing.algEquiv S S).symm.trans (FractionRing.algEquiv S L)).toLinearEquiv)
  exact FiniteDimensional.trans K S L

/-
Domain triage:
* primary domain: orders of vanishing for module-finite extensions of one-dimensional Noetherian
  local domains, expressed through the canonical valuation owner `Ring.ordFrac`;
* sampled owner API: `Ring.ordFrac`,
  `Ring.KrullDimLE.of_isLocalization`,
  `length_eq_sum_residueFieldDegree_mul_length_localizedModule`,
  `finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension`,
  `comap_maximalIdeal_of_finiteType_of_finiteFractionRingExtension`, and
  `moduleFinite_residueField_of_finiteType_of_finiteFractionRingExtension`;
* source-facing layer: the weighted sum formula over maximal localizations;
* core/canonical owners: `Ring.ordFrac` for the valuation and `Module.finrank` for the
  residue-field degree;
* bridge/view: the semilocal bridge theorems above supply finite maximal spectrum, contraction to
  `maximalIdeal A`, and residue-field finiteness, while the only additional local bridge below is
  localization permanence for the `Ring.ordFrac` owner.

Primitive data are the finite algebra `A → B`, the element `y : Frac(B)ˣ`, and the canonical
dimension-at-most-one owner hypothesis `[Ring.KrullDimLE 1 A]`. Derived API consists of
semilocality of `B`, contraction to `maximalIdeal A`, the induced residue-field extensions,
injectivity of `A → B` from the fraction-ring tower, and localization permanence needed to
evaluate `Ring.ordFrac` after localizing at maximal ideals.
-/

-- Proof sketch: first pass the dimension-at-most-one hypothesis from `A` to the finite extension
-- `B`, then localize at `m`. Localization cannot increase Krull dimension, so `Bₘ` still
-- satisfies the `Ring.KrullDimLE 1` hypothesis needed for `Ring.ordFrac`.
/-- The localization of a module-finite extension of a one-dimensional Noetherian local domain at a
maximal ideal still has Krull dimension at most `1`. -/
theorem krullDimLE_one_localizationAtPrime_of_moduleFinite
    [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Module.Finite A B]
    (m : MaximalSpectrum B) :
    Ring.KrullDimLE 1 (Localization.AtPrime m.asIdeal) := by
  sorry

end

section

variable (A : Type u) {B : Type v}
variable [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
variable [Algebra (FractionRing A) (FractionRing B)]
variable [IsScalarTower A (FractionRing A) (FractionRing B)]

section

variable [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Module.Finite A B]

local notation "κA" => Ideal.ResidueField (maximalIdeal A)

local instance :
    FiniteDimensional (FractionRing A) (FractionRing B) :=
  finiteDimensional_fractionRing_of_moduleFinite A

local instance residueFieldAlgebra_of_moduleFinite (m : MaximalSpectrum B) :
    Algebra κA (Ideal.ResidueField m.asIdeal) :=
  residueFieldAlgebra_of_finiteType_of_finiteFractionRingExtension A m

local instance residueFieldModuleFinite_of_moduleFinite (m : MaximalSpectrum B) :
    Module.Finite κA (Ideal.ResidueField m.asIdeal) :=
  moduleFinite_residueField_of_finiteType_of_finiteFractionRingExtension A m

-- Proof sketch: write the order on the left as the length of `B / yB` via the determinant formula
-- for lattices from Lemma `10.121.7`, decompose that length into the sum of the local lengths over
-- the finitely many maximal ideals of `B` using Lemma `10.52.12`, and identify each local length
-- with the local order of vanishing. The determinant giving the lattice distance is exactly the
-- field norm `Norm_{Frac(B)/Frac(A)}(y)`.
/-- Lemma 10.121.8: if `A → B` is a module-finite extension of domains with `A` a one-dimensional
Noetherian local domain, then the order of vanishing on `A` of the norm of `y ∈ Frac(B)ˣ` equals
the sum over the maximal ideals `m` of `B` of the residue-field degree
`[κ(m) : κ(maximalIdeal A)]` times the order of vanishing of `y` in `Bₘ`. -/
theorem ordFrac_norm_eq_sum_residueFieldDegree_mul_local_ordFrac (y : (FractionRing B)ˣ) :
    WithZero.log (Ring.ordFrac A (Algebra.norm (FractionRing A) (y : FractionRing B))) =
      let _ : Finite (MaximalSpectrum B) :=
        finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension A
      let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite (MaximalSpectrum B)
      let _ : IsNoetherianRing B := IsNoetherianRing.of_finite A B
      let _ : ∀ m : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime m.asIdeal) :=
        fun m ↦
          IsLocalization.isNoetherianRing m.asIdeal.primeCompl
            (Localization.AtPrime m.asIdeal) inferInstance
      let _ : ∀ m : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime m.asIdeal) :=
        fun m ↦ krullDimLE_one_localizationAtPrime_of_moduleFinite A m
      ∑ m : MaximalSpectrum B,
        (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℤ) *
          WithZero.log (Ring.ordFrac (Localization.AtPrime m.asIdeal) (y : FractionRing B)) := by
  sorry

end

end

end InjectiveAlgebraMapFact
