import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_9_25_1_Artin_Schreier_extensions (from Chap09) -/
open scoped IntermediateField

universe u v

section

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {p : ℕ} [Fact p.Prime] [CharP K p] [IsGalois K L]

/- Domain-style sampling for Lemma 9.25.1:
- primary domain: cyclic Galois extensions of fields of characteristic `p`;
- sampled owner declarations:
  `IsCyclic`,
  `IsGalois.card_aut_eq_finrank`,
  `IntermediateField.adjoin`,
  `exists_root_adjoin_eq_top_of_isCyclic`;
- best owner abstraction: the clean owner layer for this item is a cyclic Galois extension of
  degree `p`, with the textbook `Gal(L/K) ≃ ℤ/pℤ` formulation handled as a bridge;
- primitive data: the extension `L/K`, the characteristic-`p` hypothesis, cyclicity of `Gal(L / K)`,
  and the degree condition `finrank K L = p`;
- derived API: the source-facing `Gal(L / K) ≃ Multiplicative (ZMod p)` statement below is a thin
  reformulation of that owner-level data.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma phrased with Galois group `ℤ/pℤ`;
- `core/canonical`: the owner theorem `exists_artin_schreier_generator_of_isCyclic`;
- `bridge/view`: the equivalent formulation using a multiplicative `ZMod p` description of the
  Galois group.

There is no upstream Artin--Schreier owner theorem in mathlib, so this file should expose the
cyclic degree-`p` statement directly and keep the textbook group-isomorphism phrasing as a bridge.
-/

/-- Helper for Lemma 9.25.1 (Artin-Schreier extensions): a cyclic generator identifies
`Gal(L / K)` with `Multiplicative (ZMod p)` once its cardinality is known to be `p`. -/
noncomputable def generator_equiv_zmod_of_card_eq
    (σ : Gal(L/K)) (hσ : ∀ τ : Gal(L/K), τ ∈ Subgroup.zpowers σ)
    (hcard : Nat.card (Gal(L/K)) = p) :
    Multiplicative (ZMod p) ≃* Gal(L/K) :=
  zmodMulEquivOfGenerator hσ hcard

/-- Helper for Lemma 9.25.1 (Artin-Schreier extensions): after normalizing a nonzero trace value,
one gets an element whose orbit sum along a cyclic generator is `1`. -/
lemma exists_orbit_sum_eq_one_of_cyclic_generator
    [FiniteDimensional K L] (σ : Gal(L/K))
    (hσ : ∀ τ : Gal(L/K), τ ∈ Subgroup.zpowers σ)
    (hcard : Nat.card (Gal(L/K)) = p) :
    ∃ y : L, ∑ a : Multiplicative (ZMod p),
      (generator_equiv_zmod_of_card_eq σ hσ hcard a) y = 1 := by
  let e : Multiplicative (ZMod p) ≃* Gal(L/K) := generator_equiv_zmod_of_card_eq σ hσ hcard
  have htrace_ne_zero : Algebra.trace K L ≠ 0 := Algebra.trace_ne_zero K L
  have hx : ∃ x : L, Algebra.trace K L x ≠ 0 := by
    by_contra hx
    apply htrace_ne_zero
    ext x
    exact by
      have hx0 : Algebra.trace K L x = 0 := by
        by_contra hx0
        exact hx ⟨x, hx0⟩
      simpa using hx0
  rcases hx with ⟨x, hx⟩
  let y : L := (Algebra.trace K L x)⁻¹ • x
  have hy_trace : Algebra.trace K L y = 1 := by
    -- Scale the chosen element so that its trace becomes exactly `1`.
    simp [y, hx]
  have hy_aut : ∑ τ : Gal(L/K), τ y = 1 := by
    -- Rewrite the trace as the sum over all Galois automorphisms.
    calc
      ∑ τ : Gal(L/K), τ y = algebraMap K L (Algebra.trace K L y) := by
        symm
        exact trace_eq_sum_automorphisms (K := K) (L := L) y
      _ = 1 := by simp [hy_trace]
  have hy_mul : ∑ a : Multiplicative (ZMod p), (e a) y = 1 := by
    -- Transport the automorphism sum along the cyclic generator equivalence.
    calc
      ∑ a : Multiplicative (ZMod p), (e a) y = ∑ τ : Gal(L/K), τ y := by
        simpa using (Equiv.sum_comp e.toEquiv (fun τ : Gal(L/K) ↦ τ y))
      _ = 1 := hy_aut
  exact ⟨y, by simpa [e] using hy_mul⟩

/-- Helper for Lemma 9.25.1 (Artin-Schreier extensions): if the generator fixes an element, then
every Galois automorphism fixes it. -/
lemma fixed_by_generator_of_cyclic
    [FiniteDimensional K L] (σ : Gal(L/K))
    (hσ : ∀ τ : Gal(L/K), τ ∈ Subgroup.zpowers σ)
    {x : L} (hx : σ x = x) :
    ∀ τ : Gal(L/K), τ x = x := by
  have hσpow : ∀ τ : Gal(L/K), τ ∈ Submonoid.powers σ := by
    intro τ
    rw [mem_powers_iff_mem_zpowers]
    exact hσ τ
  intro τ
  rcases hσpow τ with ⟨n, rfl⟩
  induction n with
  | zero =>
      simp
  | succ n ihn =>
      -- Apply the `n`th power of the generator to the fixed-point relation.
      simpa [pow_succ, ihn] using congrArg (fun t : L => (σ ^ n : Gal(L/K)) t) hx

/-- Helper for Lemma 9.25.1 (Artin-Schreier extensions): once a cyclic generator translates `z`
by `1`, the Artin-Schreier value `z^p - z` lies in the fixed field `K`. -/
lemma artin_schreier_value_mem_bot_of_generator_translation
    [FiniteDimensional K L] (σ : Gal(L/K))
    (hσ : ∀ τ : Gal(L/K), τ ∈ Subgroup.zpowers σ)
    {z : L} (hz : σ z = z + 1) :
    z ^ p - z ∈ (⊥ : IntermediateField K L) := by
  let _ : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hfixσ : σ (z ^ p - z) = z ^ p - z := by
    -- The Artin-Schreier polynomial is invariant under the translation `z ↦ z + 1`.
    calc
      σ (z ^ p - z) = (σ z) ^ p - σ z := by simp [map_sub]
      _ = (z + 1) ^ p - (z + 1) := by rw [hz]
      _ = z ^ p + 1 - (z + 1) := by rw [add_pow_char, one_pow]
      _ = z ^ p - z := by ring
  have hfixall : ∀ τ : Gal(L/K), τ (z ^ p - z) = z ^ p - z :=
    fixed_by_generator_of_cyclic σ hσ hfixσ
  exact (IsGalois.mem_bot_iff_fixed (F := K) (E := L) (z ^ p - z)).2 hfixall

/-- Helper for Lemma 9.25.1 (Artin-Schreier extensions): in prime degree, an element translated by
the cyclic generator already generates the whole extension. -/
lemma adjoin_simple_eq_top_of_generator_translation
    [FiniteDimensional K L] (hfin : Module.finrank K L = p) (σ : Gal(L/K))
    {z : L} (hz : σ z = z + 1) :
    K⟮z⟯ = ⊤ := by
  have hz_not_bot : z ∉ (⊥ : IntermediateField K L) := by
    intro hz_bot
    have hfix : σ z = z :=
      (IsGalois.mem_bot_iff_fixed (F := K) (E := L) z).1 hz_bot σ
    have hone : (1 : L) = 0 := by
      calc
        (1 : L) = (z + 1) - z := by ring
        _ = σ z - z := by rw [hz]
        _ = z - z := by rw [hfix]
        _ = 0 := sub_self z
    exact one_ne_zero hone
  have hne_one : Module.finrank K K⟮z⟯ ≠ 1 := by
    intro hz_finrank
    exact hz_not_bot <|
      (IntermediateField.finrank_adjoin_simple_eq_one_iff (F := K) (E := L) (α := z)).1 hz_finrank
  have hdvd : Module.finrank K K⟮z⟯ ∣ p := by
    rw [← hfin]
    simpa [IntermediateField.finrank_top'] using
      (IntermediateField.finrank_dvd_of_le_right
        (K := K) (F := K⟮z⟯) (E := (⊤ : IntermediateField K L)) le_top)
  have hz_finrank : Module.finrank K K⟮z⟯ = p := by
    rcases (Nat.dvd_prime Fact.out).mp hdvd with h1 | hp
    · exact (hne_one h1).elim
    · exact hp
  -- Equal prime degree forces the simple intermediate field to be the whole extension.
  apply IntermediateField.eq_of_le_of_finrank_eq (K := K) (F := K⟮z⟯)
    (E := (⊤ : IntermediateField K L)) le_top
  simpa [IntermediateField.finrank_top', hfin] using hz_finrank

/-- Helper for Lemma 9.25.1 (Artin-Schreier extensions): the cyclic generator acts on the
weighted orbit by shifting the `ZMod p` index by `+1`. -/
lemma weighted_orbit_sum_generator_shift
    (σ : Gal(L/K)) (hσ : ∀ τ : Gal(L/K), τ ∈ Subgroup.zpowers σ)
    (hcard : Nat.card (Gal(L/K)) = p) (y : L) (i : ZMod p) :
    σ (((generator_equiv_zmod_of_card_eq σ hσ hcard) (Multiplicative.ofAdd i)) y)
      = ((generator_equiv_zmod_of_card_eq σ hσ hcard) (Multiplicative.ofAdd (1 + i))) y := by
  let e : Multiplicative (ZMod p) ≃* Gal(L/K) := generator_equiv_zmod_of_card_eq σ hσ hcard
  have hgen : e (Multiplicative.ofAdd 1) = σ := by
    -- The chosen generator corresponds to the class of `1` in `ZMod p`.
    simpa [e, generator_equiv_zmod_of_card_eq] using
      (zmodMulEquivOfGenerator_apply_ofAdd_one (g := σ) (hg := hσ) (hn := hcard))
  -- Evaluate the group law on automorphisms, then collapse the product back through `e`.
  calc
    σ ((e (Multiplicative.ofAdd i)) y)
      = (e (Multiplicative.ofAdd 1)) ((e (Multiplicative.ofAdd i)) y) := by
          rw [hgen]
    _ = ((e (Multiplicative.ofAdd 1)) * e (Multiplicative.ofAdd i)) y := by
          rfl
    _ = (e ((Multiplicative.ofAdd 1) * Multiplicative.ofAdd i)) y := by
          simpa using congrArg (fun τ : Gal(L/K) => τ y)
            ((e.map_mul (Multiplicative.ofAdd 1) (Multiplicative.ofAdd i)).symm)
    _ = ((generator_equiv_zmod_of_card_eq σ hσ hcard) (Multiplicative.ofAdd (1 + i))) y := by
          simp [e]

/-- Helper for Lemma 9.25.1 (Artin-Schreier extensions): after reindexing by `+1`, the shifted
coefficient splits into the orbit term plus the original weighted coefficient. -/
lemma neg_cast_sub_one_smul_eq_self_add_neg_cast_smul
    (i : ZMod p) (t : L) :
    -((ZMod.cast (i - 1 : ZMod p) : K) • t) = t + -((ZMod.cast i : K) • t) := by
  have hcast : (ZMod.cast (i - 1 : ZMod p) : K) = (ZMod.cast i : K) - 1 := by
    -- Move the `ZMod` subtraction into the scalar field `K`.
    rw [ZMod.cast_sub']
    simp
  -- Expand the shifted scalar action and rearrange the additive terms.
  rw [hcast, sub_smul, sub_eq_add_neg, neg_add_rev]
  simp

/-- Helper for Lemma 9.25.1 (Artin-Schreier extensions): a weighted orbit sum with total orbit
sum `1` produces an element translated by the cyclic generator. -/
lemma weighted_orbit_sum_translates_by_one
    (σ : Gal(L/K)) (hσ : ∀ τ : Gal(L/K), τ ∈ Subgroup.zpowers σ)
    (hcard : Nat.card (Gal(L/K)) = p) {y : L}
    (hy : ∑ a : Multiplicative (ZMod p),
      (generator_equiv_zmod_of_card_eq σ hσ hcard a) y = 1) :
    ∃ z : L, σ z = z + 1 := by
  let e : Multiplicative (ZMod p) ≃* Gal(L/K) := generator_equiv_zmod_of_card_eq σ hσ hcard
  let orbitTerm : ZMod p → L := fun i ↦ (e (Multiplicative.ofAdd i)) y
  have hy_orbit : ∑ i : ZMod p, orbitTerm i = 1 := by
    -- Rewrite the orbit sum from `Multiplicative (ZMod p)` to `ZMod p`.
    calc
      ∑ i : ZMod p, orbitTerm i
        = ∑ a : Multiplicative (ZMod p),
            (e (Multiplicative.ofAdd (Multiplicative.toAdd a))) y := by
              simpa [orbitTerm] using
                (Equiv.sum_comp Multiplicative.toAdd
                  (fun i : ZMod p ↦ (e (Multiplicative.ofAdd i)) y)).symm
      _ = ∑ a : Multiplicative (ZMod p), (e a) y := by
            simp
      _ = 1 := hy
  let z : L := -∑ i : ZMod p, ((ZMod.cast i : K) • orbitTerm i)
  refine ⟨z, ?_⟩
  have hmap :
      ∑ i : ZMod p, σ ((ZMod.cast i : K) • orbitTerm i)
        = ∑ i : ZMod p, ((ZMod.cast i : K) • orbitTerm (1 + i)) := by
    -- The generator is `K`-linear and shifts the orbit index by one step.
    refine Finset.sum_congr rfl ?_
    intro i hi
    calc
      σ ((ZMod.cast i : K) • orbitTerm i) = (ZMod.cast i : K) • σ (orbitTerm i) := by
        simpa using (σ.toLinearEquiv.map_smul (ZMod.cast i : K) (orbitTerm i))
      _ = (ZMod.cast i : K) • orbitTerm (1 + i) := by
        rw [weighted_orbit_sum_generator_shift (K := K) (L := L) (p := p) σ hσ hcard y i]
  have hreindex :
      ∑ i : ZMod p, ((ZMod.cast i : K) • orbitTerm (1 + i))
        = ∑ i : ZMod p, ((ZMod.cast (i - 1 : ZMod p) : K) • orbitTerm i) := by
    let shifted : ZMod p → L := fun i ↦ ((ZMod.cast (i - 1 : ZMod p) : K) • orbitTerm i)
    -- Reindex the cyclic orbit sum along the translation `i ↦ i + 1`.
    calc
      ∑ i : ZMod p, ((ZMod.cast i : K) • orbitTerm (1 + i))
        = ∑ i : ZMod p, shifted ((Equiv.addRight (1 : ZMod p)) i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [add_comm]
            simp [shifted]
      _ = ∑ i : ZMod p, shifted i := by
            simpa [shifted] using (Equiv.sum_comp (Equiv.addRight (1 : ZMod p)) shifted)
  -- Route correction: the previous attempt stalled on interface mismatches; the proof closes once
  -- the generator action and the shifted coefficient rewrite are isolated as separate helpers.
  calc
    σ z = σ (-∑ i : ZMod p, ((ZMod.cast i : K) • orbitTerm i)) := by
            rfl
    _ = -(∑ i : ZMod p, σ ((ZMod.cast i : K) • orbitTerm i)) := by
            rw [map_neg, map_sum]
    _ = -(∑ i : ZMod p, ((ZMod.cast i : K) • orbitTerm (1 + i))) := by
            rw [hmap]
    _ = -(∑ i : ZMod p, ((ZMod.cast (i - 1 : ZMod p) : K) • orbitTerm i)) := by
            rw [hreindex]
    _ = ∑ i : ZMod p, -((ZMod.cast (i - 1 : ZMod p) : K) • orbitTerm i) := by
            rw [← Finset.sum_neg_distrib]
    _ = ∑ i : ZMod p, (orbitTerm i + -((ZMod.cast i : K) • orbitTerm i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa using neg_cast_sub_one_smul_eq_self_add_neg_cast_smul
              (K := K) (L := L) (p := p) i (orbitTerm i)
    _ = (∑ i : ZMod p, orbitTerm i) + ∑ i : ZMod p, -((ZMod.cast i : K) • orbitTerm i) := by
            rw [Finset.sum_add_distrib]
    _ = 1 + z := by
            simp [z, hy_orbit, Finset.sum_neg_distrib]
    _ = z + 1 := by
            rw [add_comm]

/-- Lemma 9.25.1 (Artin-Schreier extensions): if `L/K` is a Galois extension of characteristic
`p` whose Galois group is cyclic of order `p`, then `L` is generated by an element `z` satisfying
`z ^ p - z ∈ K`, encoded as membership in the bottom intermediate field. -/
-- Proof sketch: choose a generator `σ` of `Gal(L / K)` and regard it as a `K`-linear operator on
-- `L`. Since `σ ^ p = 1` and the minimal polynomial of `σ` is `(X - 1)^p`, one finds `z : L`
-- with `σ z = z + 1`. Then `z ∉ K`, hence `K⟮z⟯ = ⊤`, and `σ (z ^ p - z) = z ^ p - z` shows
-- that `z ^ p - z` is fixed by the Galois group and therefore lies in `K`.
lemma exists_artin_schreier_generator_of_isCyclic
    [FiniteDimensional K L] [IsCyclic Gal(L/K)] (hfin : Module.finrank K L = p) :
    ∃ z : L, K⟮z⟯ = ⊤ ∧ z ^ p - z ∈ (⊥ : IntermediateField K L) := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  have hcard : Nat.card (Gal(L/K)) = p := by
    rw [IsGalois.card_aut_eq_finrank, hfin]
  obtain ⟨y, hy⟩ := exists_orbit_sum_eq_one_of_cyclic_generator
    (K := K) (L := L) (p := p) σ hσ hcard
  obtain ⟨z, hz⟩ := weighted_orbit_sum_translates_by_one
    (K := K) (L := L) (p := p) σ hσ hcard hy
  refine ⟨z, ?_, ?_⟩
  · -- Prime degree forces the translating element to generate the whole field.
    exact adjoin_simple_eq_top_of_generator_translation (K := K) (L := L) (p := p) hfin σ hz
  · -- The Artin-Schreier value is fixed by the cyclic generator, hence by all automorphisms.
    exact artin_schreier_value_mem_bot_of_generator_translation
      (K := K) (L := L) (p := p) σ hσ hz

/-- A source-facing reformulation of the Artin--Schreier generator statement using an explicit
isomorphism `Gal(L / K) ≃ ℤ/pℤ`. -/
-- Proof sketch: an isomorphism `Gal(L / K) ≃ Multiplicative (ZMod p)` makes the Galois group
-- cyclic of cardinality `p`. By `IsGalois.card_aut_eq_finrank`, the extension has degree `p`, so
-- the cyclic degree-`p` owner theorem applies.
lemma exists_artin_schreier_generator_of_galoisGroup_equiv_zmod
    (hGal : Nonempty (Gal(L/K) ≃* Multiplicative (ZMod p))) :
    ∃ z : L, K⟮z⟯ = ⊤ ∧ z ^ p - z ∈ (⊥ : IntermediateField K L) := by
  let e : Gal(L/K) ≃* Multiplicative (ZMod p) := hGal.some
  let _ : IsCyclic (Gal(L/K)) := (MulEquiv.isCyclic e).2 inferInstance
  let _ : Finite (Gal(L/K)) := Finite.of_equiv (Multiplicative (ZMod p)) e.symm.toEquiv
  let _ : FiniteDimensional K L := IsGalois.finiteDimensional_of_finite (F := K) (E := L)
  have hcard : Nat.card (Gal(L/K)) = p := by
    calc
      Nat.card (Gal(L/K)) = Nat.card (Multiplicative (ZMod p)) := Nat.card_congr e.toEquiv
      _ = Nat.card (ZMod p) := by simpa using Nat.card_congr Multiplicative.toAdd
      _ = p := Nat.card_zmod p
  have hfin : Module.finrank K L = p := by
    rw [← IsGalois.card_aut_eq_finrank (F := K) (E := L), hcard]
  exact exists_artin_schreier_generator_of_isCyclic (K := K) (L := L) (p := p) hfin

end
