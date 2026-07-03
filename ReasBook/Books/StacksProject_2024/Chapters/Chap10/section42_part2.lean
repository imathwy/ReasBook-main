import Mathlib
import Mathlib.FieldTheory.IsPerfectClosure
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_42_4 (from Chap10) -/
universe u v w u1 v1

section

open Algebra

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- Helper for Lemma 10.42.4: the relative separable closure of a finitely generated field
extension is finite over the base field. -/
lemma finiteDimensional_separableClosure_of_essFiniteType
    [Algebra.EssFiniteType k K] :
    FiniteDimensional k (separableClosure k K) := by
  -- The separable closure sits inside the finite-dimensional algebraic closure.
  letI : FiniteDimensional k (algebraicClosure k K) :=
    finiteDimensional_algebraicClosure k K
  letI : Algebra (separableClosure k K) (algebraicClosure k K) :=
    (IntermediateField.inclusion (le_algebraicClosure k K (separableClosure k K))).toAlgebra
  exact FiniteDimensional.left k (separableClosure k K) (algebraicClosure k K)

/-- Helper for Lemma 10.42.4: once a field extension `K / F` is finite-dimensional, the source
induction measure `[K : separableClosure F K]` is available because `K` is also finite-dimensional
over its relative separable closure. -/
lemma finiteDimensional_over_separableClosure_of_finiteDimensional
    (F : IntermediateField k K) [FiniteDimensional F K] :
    FiniteDimensional (separableClosure F K) K := by
  -- The relative separable closure is an intermediate field of the already finite extension
  -- `K / F`, so the top field stays finite-dimensional after enlarging the base to that closure.
  infer_instance

/-- Helper for Lemma 10.42.4: a transcendence-basis stage in a finitely generated extension gives
the finite relative degree over which the source induction on `[K : K_sep]` runs. -/
lemma finiteDimensional_over_separableClosure_of_isTranscendenceBasis
    [Algebra.EssFiniteType k K] {ι : Type*} {x : ι → K}
    (hx : IsTranscendenceBasis k x) :
    FiniteDimensional (separableClosure (IntermediateField.adjoin k (Set.range x)) K) K := by
  let F : IntermediateField k K := IntermediateField.adjoin k (Set.range x)
  -- The transcendence basis makes `K` algebraic over the generated rational-function stage.
  letI : Algebra.IsAlgebraic F K := by
    simpa [F] using hx.isAlgebraic_field
  -- Finite generation then upgrades algebraicity over `F` to a finite-dimensional extension.
  letI : Algebra.EssFiniteType F K := Algebra.EssFiniteType.of_comp k F K
  letI : Module.Finite F K := Algebra.finite_of_essFiniteType_of_isAlgebraic
  letI : FiniteDimensional F K := by infer_instance
  -- Passing from `F` to its relative separable closure preserves finite-dimensionality.
  simpa [F] using
    (finiteDimensional_over_separableClosure_of_finiteDimensional (k := k) (K := K) F)

/-- Helper for Lemma 10.42.4: a finitely generated field extension admits a transcendence-basis
stage whose relative separable closure has finite index in the top field. -/
lemma exists_transcendence_basis_with_finiteDimensional_over_separableClosure
    [Algebra.EssFiniteType k K] :
    ∃ s : Set K,
      IsTranscendenceBasis k (Subtype.val : s → K) ∧
        FiniteDimensional
          (separableClosure (IntermediateField.adjoin k (Set.range (Subtype.val : s → K))) K) K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k K
  refine ⟨s, hs, ?_⟩
  -- This packages the verified prefix of the source proof before the positive-characteristic
  -- coefficient base-change step.
  exact finiteDimensional_over_separableClosure_of_isTranscendenceBasis (k := k) (K := K) hs

/-- Helper for Lemma 10.42.4: the source transcendence basis can be reindexed by
`Fin (Cardinal.toNat (Algebra.trdeg k K))` while keeping the finite relative degree
`[K : separableClosure(k(x_1, ..., x_r), K)]` needed for the source induction. -/
lemma exists_fin_reindexed_transcendence_basis_with_finiteDimensional_over_separableClosure
    [Algebra.EssFiniteType k K] :
    ∃ x : Fin (Cardinal.toNat (Algebra.trdeg k K)) → K,
      IsTranscendenceBasis k x ∧
        FiniteDimensional
          (separableClosure (IntermediateField.adjoin k (Set.range x)) K) K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k K
  obtain ⟨x, hx, hx_adjoin⟩ :=
    exists_fin_reindexed_transcendence_basis (k := k) (K := K) hs
  refine ⟨x, hx, ?_⟩
  -- Reindexing the transcendence basis preserves the generated rational-function stage.
  simpa [hx_adjoin] using
    finiteDimensional_over_separableClosure_of_isTranscendenceBasis (k := k) (K := K) hx

/-- Helper for Lemma 10.42.4: after transporting a polynomial across an algebra equivalence, the
Frobenius-image condition depends only on the composite coefficient map. This isolates the
`aevalEquivField` transport step from the omitted source base-change construction. -/
lemma map_mem_frobenius_range_of_algEquiv
    {F₁ : Type*} {F₂ : Type*} {L : Type*}
    [Field F₁] [Field F₂] [Field L] {p : ℕ} [ExpChar L p]
    (e : F₁ ≃+* F₂) (P : Polynomial F₂) (τ : F₁ →+* L)
    (h :
      (P.map e.symm.toRingHom).map τ ∈ Set.range (Polynomial.map (frobenius L p))) :
    P.map (τ.comp e.symm.toRingHom) ∈ Set.range (Polynomial.map (frobenius L p)) := by
  -- Unpack the Frobenius-range witness on the rational-function side.
  rcases h with ⟨Q, hQ⟩
  refine ⟨Q, ?_⟩
  -- `Polynomial.map_map` collapses the transport to the composite coefficient map.
  simpa [Polynomial.map_map] using hQ

/-- Helper for Lemma 10.42.4: a finite family of scalars acquires `p`th roots after passing to a
finite purely inseparable extension of the base field. -/
lemma exists_finite_purelyInseparable_extension_with_pth_roots
    {p : ℕ} [Fact p.Prime] [CharP k p] (C : Finset k) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'),
      FiniteDimensional k k' ∧
        IsPurelyInseparable k k' ∧
          ∀ a ∈ C, ∃ b : k', b ^ p = algebraMap k k' a := by
  classical
  letI : Algebra k (PerfectClosure k p) := (PerfectClosure.of k p).toAlgebra
  letI : IsPRadical (algebraMap k (PerfectClosure k p)) p := by
    simpa using (PerfectClosure.isPRadical (K := k) (p := p))
  letI : IsPurelyInseparable k (PerfectClosure k p) :=
    IsPRadical.isPurelyInseparable (K := k) (L := PerfectClosure k p) p
  letI : Algebra.IsAlgebraic k (PerfectClosure k p) :=
    IsPurelyInseparable.isAlgebraic k (PerfectClosure k p)
  let root : k → PerfectClosure k p := fun a ↦
    Classical.choose (surjective_frobenius (PerfectClosure k p) p (algebraMap k (PerfectClosure k p) a))
  have hroot : ∀ a : k, root a ^ p = algebraMap k (PerfectClosure k p) a := by
    intro a
    -- The chosen element is a genuine `p`th root because the perfect closure has surjective
    -- Frobenius.
    exact Classical.choose_spec
      (surjective_frobenius (PerfectClosure k p) p (algebraMap k (PerfectClosure k p) a))
  let roots : Finset (PerfectClosure k p) := C.image root
  let k' : IntermediateField k (PerfectClosure k p) :=
    IntermediateField.adjoin k (roots : Set (PerfectClosure k p))
  refine ⟨k', inferInstance, inferInstance, ?_, ?_, ?_⟩
  · -- The extension is generated by finitely many algebraic elements inside the perfect closure.
    exact IntermediateField.finiteDimensional_adjoin fun x _ ↦
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  · -- Each chosen generator has its `p`th power in the base field, so the adjoin is purely
    -- inseparable.
    rw [IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem (F := k) (E := PerfectClosure k p) p]
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    refine ⟨1, ?_⟩
    refine ⟨a, ?_⟩
    simpa [pow_one] using (hroot a).symm
  · intro a ha
    refine ⟨⟨root a, IntermediateField.subset_adjoin (F := k)
      (S := (roots : Set (PerfectClosure k p))) ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    · apply Subtype.val_injective
      -- The adjoined generator itself is the required `p`th root over the finite extension.
      simpa [k', hroot a]

/-- Helper for Lemma 10.42.4: the source polynomial base-change map is injective because
coefficient extension between fields is injective and `MvPolynomial.expand` is injective for
positive exponents. -/
lemma ratFunc_frobenius_baseChange_injective
    {r : ℕ} {k' : Type*} [Field k'] [Algebra k k'] {p : ℕ} [Fact p.Prime] :
    Function.Injective
      ((((MvPolynomial.expand p (σ := Fin r) (R := k')).toRingHom).comp
          (MvPolynomial.map (algebraMap k k'))) :
        MvPolynomial (Fin r) k →+* MvPolynomial (Fin r) k') := by
  intro f g hfg
  -- First cancel the variable-Frobenius expansion, which is injective for prime `p`.
  have hmap :
      MvPolynomial.map (algebraMap k k') f =
        MvPolynomial.map (algebraMap k k') g := by
    exact
      (MvPolynomial.expand_injective (σ := Fin r) (R := k')
        (Nat.pos_of_ne_zero (Nat.Prime.ne_zero (Fact.out : p.Prime)))) hfg
  -- Then cancel the coefficient-extension map, which is injective between fields.
  exact
    MvPolynomial.map_injective (σ := Fin r) (f := algebraMap k k')
      (algebraMap k k').injective hmap

/-- Helper for Lemma 10.42.4: the source rational-function base change adjoining `p`th roots of
the variables is induced from coefficient extension followed by `MvPolynomial.expand`. -/
noncomputable def ratFunc_frobenius_baseChangeHom
    {r : ℕ} {k' : Type*} [Field k'] [Algebra k k'] {p : ℕ} [Fact p.Prime] :
    FractionRing (MvPolynomial (Fin r) k) →+* FractionRing (MvPolynomial (Fin r) k') :=
  IsFractionRing.map
    (K := FractionRing (MvPolynomial (Fin r) k))
    (L := FractionRing (MvPolynomial (Fin r) k'))
    (j :=
      (((MvPolynomial.expand p (σ := Fin r) (R := k')).toRingHom).comp
        (MvPolynomial.map (algebraMap k k'))))
    (ratFunc_frobenius_baseChange_injective (k := k) (k' := k') (r := r) (p := p))

/-- Helper for Lemma 10.42.4: after extending coefficients and replacing each variable by its
`p`th power, a multivariate polynomial whose scalar coefficients acquire `p`th roots becomes a
`p`th power. This is the polynomial-level bridge behind the omitted source base-change step. -/
lemma mvPolynomial_image_is_pth_power_of_coeff_roots
    {σ : Type*} {k' : Type*} [Field k'] [Algebra k k']
    {p : ℕ} [ExpChar k' p] {f : MvPolynomial σ k}
    (hcoeff :
      ∀ d ∈ f.support, ∃ b : k', b ^ p = algebraMap k k' (f.coeff d)) :
    ∃ g : MvPolynomial σ k',
      MvPolynomial.expand p (MvPolynomial.map (algebraMap k k') f) = g ^ p := by
  classical
  let g : MvPolynomial σ k' :=
    f.support.attach.sum fun d ↦
      MvPolynomial.monomial d.1 (Classical.choose (hcoeff d.1 d.2))
  have hmap :
      MvPolynomial.map (algebraMap k k') f = MvPolynomial.map (frobenius k' p) g := by
    ext d
    by_cases hd : d ∈ f.support
    · have hgcoeff : g.coeff d = Classical.choose (hcoeff d hd) := by
        unfold g
        -- Only the monomial indexed by `d` contributes to the `d`-coefficient.
        rw [MvPolynomial.coeff_sum]
        rw [Finset.sum_eq_single ⟨d, hd⟩]
        · simp [MvPolynomial.coeff_monomial]
        · intro a ha had
          have had_ne : a.1 ≠ d := by
            intro h
            exact had (Subtype.ext h)
          simp [MvPolynomial.coeff_monomial, had_ne]
        · intro hnot
          exact (hnot (by simpa using hd)).elim
      -- On support, the chosen scalar root records exactly the Frobenius image coefficient.
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map, hgcoeff]
      simpa [frobenius_def] using (Classical.choose_spec (hcoeff d hd)).symm
    · have hfcoeff : f.coeff d = 0 := MvPolynomial.notMem_support_iff.mp hd
      have hgcoeff : g.coeff d = 0 := by
        unfold g
        -- Off support, every summand contributes zero to the `d`-coefficient.
        rw [MvPolynomial.coeff_sum]
        refine Finset.sum_eq_zero ?_
        intro a ha
        have had_ne : a.1 ≠ d := by
          intro h
          exact hd (h ▸ a.2)
        simp [MvPolynomial.coeff_monomial, had_ne]
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map, hfcoeff, hgcoeff]
      simp
  refine ⟨g, ?_⟩
  -- After rewriting the mapped coefficients as Frobenius images, `map_frobenius_expand`
  -- identifies the expanded polynomial as a `p`th power.
  calc
    MvPolynomial.expand p (MvPolynomial.map (algebraMap k k') f)
        = MvPolynomial.expand p (MvPolynomial.map (frobenius k' p) g) := by
            rw [hmap]
    _ = MvPolynomial.map (frobenius k' p) (MvPolynomial.expand p g) := by
          rw [← MvPolynomial.map_expand]
    _ = g ^ p := by
          simpa using
            (MvPolynomial.map_frobenius_expand (σ := σ) (R := k') (p := p) (f := g))

/-- Helper for Lemma 10.42.4: a polynomial over a characteristic-`p` field lies in the Frobenius
image once each coefficient on its finite support is known to be a `p`th power. This packages the
coefficient-family output needed after the rational-function descent step. -/
lemma polynomial_mem_frobenius_range_of_support_coeff_roots
    {R : Type*} [CommSemiring R] {L : Type*} [Field L] {p : ℕ} [ExpChar L p]
    (τ : R →+* L) (Q : Polynomial R)
    (hcoeff : ∀ n ∈ Q.support, ∃ b : L, τ (Q.coeff n) = b ^ p) :
    Q.map τ ∈ Set.range (Polynomial.map (frobenius L p)) := by
  -- `Polynomial.mem_map_frobenius_range_iff_coeff_eq_pow` reduces the claim to coefficients.
  refine (Polynomial.mem_map_frobenius_range_iff_coeff_eq_pow).2 ?_
  intro n
  by_cases hn : n ∈ Q.support
  · simpa [Polynomial.coeff_map] using hcoeff n hn
  · refine ⟨0, ?_⟩
    rw [Polynomial.coeff_map, Polynomial.notMem_support_iff.mp hn, map_zero]
    simp [expChar_ne_zero L p]

/-- Helper for Lemma 10.42.4: every rational function over the multivariate polynomial ring admits
one chosen numerator/denominator presentation with nonzero denominator. -/
lemma exists_fraction_ring_numerator_denominator
    {r : ℕ} (z : FractionRing (MvPolynomial (Fin r) k)) :
    ∃ ab : MvPolynomial (Fin r) k × MvPolynomial (Fin r) k,
      ab.2 ≠ 0 ∧
        algebraMap (MvPolynomial (Fin r) k) (FractionRing (MvPolynomial (Fin r) k)) ab.1 /
            algebraMap (MvPolynomial (Fin r) k) (FractionRing (MvPolynomial (Fin r) k)) ab.2 = z := by
  -- Use the canonical fraction-ring presentation and then forget the nonzerodivisor witness.
  obtain ⟨a, b, hb, hz⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin r) k) z
  refine ⟨(a, b), mem_nonZeroDivisors_iff_ne_zero.mp hb, hz⟩

/-- Helper for Lemma 10.42.4: after the source Frobenius-style base change, one represented
rational function becomes a `p`th power as soon as the scalar coefficients of the chosen numerator
and denominator acquire `p`th roots. -/
lemma ratFunc_image_is_pth_power_of_repr_coeff_roots
    {r : ℕ} {k' : Type*} [Field k'] [Algebra k k'] {p : ℕ} [Fact p.Prime] [ExpChar k' p]
    {z : FractionRing (MvPolynomial (Fin r) k)}
    {a b : MvPolynomial (Fin r) k} (_hb : b ≠ 0)
    (hz :
      algebraMap (MvPolynomial (Fin r) k) (FractionRing (MvPolynomial (Fin r) k)) a /
          algebraMap (MvPolynomial (Fin r) k) (FractionRing (MvPolynomial (Fin r) k)) b = z)
    (ha :
      ∀ d ∈ a.support, ∃ c : k', c ^ p = algebraMap k k' (a.coeff d))
    (hbcoeff :
      ∀ d ∈ b.support, ∃ c : k', c ^ p = algebraMap k k' (b.coeff d)) :
    ∃ w : FractionRing (MvPolynomial (Fin r) k'),
      ratFunc_frobenius_baseChangeHom (k := k) (k' := k') (r := r) (p := p) z = w ^ p := by
  -- First lift the numerator and denominator separately to `p`th powers after coefficient
  -- extension and variable Frobenius.
  obtain ⟨A, hA⟩ :=
    mvPolynomial_image_is_pth_power_of_coeff_roots
      (k := k) (k' := k') (p := p) (f := a) ha
  obtain ⟨B, hB⟩ :=
    mvPolynomial_image_is_pth_power_of_coeff_roots
      (k := k) (k' := k') (p := p) (f := b) hbcoeff
  refine ⟨algebraMap (MvPolynomial (Fin r) k') (FractionRing (MvPolynomial (Fin r) k')) A /
      algebraMap (MvPolynomial (Fin r) k') (FractionRing (MvPolynomial (Fin r) k')) B, ?_⟩
  -- Then transport the chosen fraction presentation through the fraction-ring map.
  rw [← hz, map_div₀]
  have hAmap :
      ratFunc_frobenius_baseChangeHom (k := k) (k' := k') (r := r) (p := p)
          (algebraMap (MvPolynomial (Fin r) k) (FractionRing (MvPolynomial (Fin r) k)) a) =
        algebraMap (MvPolynomial (Fin r) k') (FractionRing (MvPolynomial (Fin r) k')) (A ^ p) := by
    -- On a polynomial coefficient, the fraction-ring map is just the transported coefficient map.
    delta ratFunc_frobenius_baseChangeHom IsFractionRing.map
    simpa only [IsLocalization.map_eq, RingHom.comp_apply] using
      congrArg
        (algebraMap (MvPolynomial (Fin r) k') (FractionRing (MvPolynomial (Fin r) k'))) hA
  have hBmap :
      ratFunc_frobenius_baseChangeHom (k := k) (k' := k') (r := r) (p := p)
          (algebraMap (MvPolynomial (Fin r) k) (FractionRing (MvPolynomial (Fin r) k)) b) =
        algebraMap (MvPolynomial (Fin r) k') (FractionRing (MvPolynomial (Fin r) k')) (B ^ p) := by
    -- The same simplification applies to the denominator.
    delta ratFunc_frobenius_baseChangeHom IsFractionRing.map
    simpa only [IsLocalization.map_eq, RingHom.comp_apply] using
      congrArg
        (algebraMap (MvPolynomial (Fin r) k') (FractionRing (MvPolynomial (Fin r) k'))) hB
  rw [hAmap, hBmap]
  -- The numerator and denominator images are the chosen `p`th powers, so the fraction is too.
  simp [map_pow, div_pow]

/-- Helper for Lemma 10.42.4: one finite purely inseparable extension of the base field suffices
to make every coefficient in the finite support of a fixed transported polynomial become a `p`th
power after the source rational-function base change. -/
lemma exists_finite_purelyInseparable_extension_for_transported_minpoly_coefficients
    {r : ℕ} {p : ℕ} [Fact p.Prime] [CharP k p]
    (Q : Polynomial (FractionRing (MvPolynomial (Fin r) k))) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'),
      FiniteDimensional k k' ∧
        IsPurelyInseparable k k' ∧
          ∀ n ∈ Q.support, ∃ w : FractionRing (MvPolynomial (Fin r) k'),
            ratFunc_frobenius_baseChangeHom (k := k) (k' := k') (r := r) (p := p) (Q.coeff n) =
              w ^ p := by
  classical
  let R := MvPolynomial (Fin r) k
  let repr : ℕ → R × R := fun n ↦
    Classical.choose
      (exists_fraction_ring_numerator_denominator (k := k) (r := r) (z := Q.coeff n))
  have hrepr :
      ∀ n : ℕ,
        (repr n).2 ≠ 0 ∧
          algebraMap R (FractionRing R) (repr n).1 /
              algebraMap R (FractionRing R) (repr n).2 = Q.coeff n := by
    intro n
    exact
      Classical.choose_spec
        (exists_fraction_ring_numerator_denominator (k := k) (r := r) (z := Q.coeff n))
  let coeffFinset : R → Finset k := fun f ↦ f.support.image f.coeff
  let C : Finset k :=
    Q.support.attach.biUnion fun n ↦
      coeffFinset (repr n.1).1 ∪ coeffFinset (repr n.1).2
  obtain ⟨k', _, _, hk'fd, hk'pi, hk'roots⟩ :=
    exists_finite_purelyInseparable_extension_with_pth_roots (k := k) (p := p) C
  refine ⟨k', inferInstance, inferInstance, hk'fd, hk'pi, ?_⟩
  letI : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
  intro n hn
  have hnum :
      ∀ d ∈ (repr n).1.support, ∃ c : k', c ^ p = algebraMap k k' ((repr n).1.coeff d) := by
    intro d hd
    have hmem_num : ((repr n).1.coeff d) ∈ C := by
      -- The numerator coefficient belongs to the one finite scalar set chosen from `Q.support`.
      refine Finset.mem_biUnion.mpr ?_
      refine ⟨⟨n, hn⟩, by simp, ?_⟩
      exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_image.mpr ⟨d, hd, rfl⟩
    exact hk'roots _ hmem_num
  have hden :
      ∀ d ∈ (repr n).2.support, ∃ c : k', c ^ p = algebraMap k k' ((repr n).2.coeff d) := by
    intro d hd
    have hmem_den : ((repr n).2.coeff d) ∈ C := by
      -- The denominator coefficient belongs to the same finite scalar set.
      refine Finset.mem_biUnion.mpr ?_
      refine ⟨⟨n, hn⟩, by simp, ?_⟩
      exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_image.mpr ⟨d, hd, rfl⟩
    exact hk'roots _ hmem_den
  -- Apply the pointwise rational-function descent lemma to the chosen representation of
  -- `Q.coeff n`.
  exact
    ratFunc_image_is_pth_power_of_repr_coeff_roots
      (k := k) (k' := k') (r := r) (p := p)
      (hrepr n).1 (hrepr n).2 hnum hden

/-- Helper for Lemma 10.42.4: once each support coefficient of one transported polynomial is a
`p`th power after the source base-change map, the whole polynomial lies in the Frobenius image. -/
lemma transported_minpoly_mem_frobenius_range_after_support_descent
    {r : ℕ} {k' : Type*} [Field k'] [Algebra k k'] {p : ℕ} [Fact p.Prime]
    [ExpChar (FractionRing (MvPolynomial (Fin r) k')) p]
    (Q : Polynomial (FractionRing (MvPolynomial (Fin r) k)))
    (hcoeff :
      ∀ n ∈ Q.support, ∃ w : FractionRing (MvPolynomial (Fin r) k'),
        ratFunc_frobenius_baseChangeHom (k := k) (k' := k') (r := r) (p := p) (Q.coeff n) =
          w ^ p) :
    (Q.map (ratFunc_frobenius_baseChangeHom (k := k) (k' := k') (r := r) (p := p))) ∈
      Set.range
        (Polynomial.map
          (frobenius (FractionRing (MvPolynomial (Fin r) k')) p)) := by
  -- Package the coefficientwise witnesses into the canonical Frobenius-range statement.
  exact
    polynomial_mem_frobenius_range_of_support_coeff_roots
      (τ := ratFunc_frobenius_baseChangeHom (k := k) (k' := k') (r := r) (p := p))
      (Q := Q) hcoeff

/-- Helper for Lemma 10.42.4: in a finite-dimensional tower, any intermediate step of relative
degree `p` strictly lowers the ambient degree. This isolates the later source induction drop from
the concrete base-change construction that produces the degree-`p` step. -/
lemma finrank_lt_of_relfinrank_eq_prime
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]
    {A B : IntermediateField F E} [FiniteDimensional A E]
    {p : ℕ} [Fact p.Prime] (hAB : A ≤ B) (hdeg : A.relfinrank B = p) :
    Module.finrank B E < Module.finrank A E := by
  letI : Algebra A B := (IntermediateField.inclusion hAB).toAlgebra
  letI : IsScalarTower A B E := IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  letI : FiniteDimensional B E := FiniteDimensional.right A B E
  -- Rewrite the ambient degree through the relative tower law for `A ≤ B ≤ E`.
  have hmul : A.relfinrank B * Module.finrank B E = Module.finrank A E :=
    IntermediateField.relfinrank_mul_finrank_top (E := E) hAB
  rw [hdeg] at hmul
  have hp : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hpos : 0 < Module.finrank B E := Module.finrank_pos
  -- Since the relative degree is strictly larger than `1`, the tail degree must decrease.
  calc
    Module.finrank B E < p * Module.finrank B E := by
      simpa [Nat.mul_comm] using (lt_mul_of_one_lt_right hpos hp)
    _ = Module.finrank A E := by
      simpa [Nat.mul_comm] using hmul

/-- Helper for Lemma 10.42.4: mapping a degree-`p` simple adjunction across a field embedding
preserves the relative degree of the resulting intermediate extension. -/
lemma relfinrank_map_restrictScalars_adjoin_simple_eq
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]
    {L : Type*} [Field L] [Algebra F L]
    (A : IntermediateField F E) (σ : E →ₐ[F] L) {β : E} {p : ℕ}
    (hdeg : Module.finrank A (IntermediateField.adjoin A ({β} : Set E)) = p) :
    (A.map σ).relfinrank
        (((IntermediateField.adjoin A ({β} : Set E)).restrictScalars F).map σ) = p := by
  let b : E := β
  let B : IntermediateField F E := IntermediateField.adjoin F ((A : Set E) ∪ ({b} : Set E))
  have hA : A ≤ B := by
    -- The source base field is contained in the larger field obtained by adjoining `β`.
    intro x hx
    exact IntermediateField.subset_adjoin (F := F) (S := ((A : Set E) ∪ ({b} : Set E))) (Or.inl hx)
  have hB :
      (IntermediateField.adjoin A ({β} : Set E)).restrictScalars F = B := by
    -- Restricting scalars rewrites the simple adjunction as adjoining `β` over `F`.
    simpa [B, b] using
      (IntermediateField.restrictScalars_adjoin (F := F) (K := A) (S := ({β} : Set E)))
  have hrel : A.relfinrank B = p := by
    -- Compute the relative finrank before mapping and simplify the extended field back to the
    -- original degree-`p` simple adjunction over `A`.
    rw [IntermediateField.relfinrank_eq_finrank_of_le hA]
    rw [IntermediateField.extendScalars_adjoin hA]
    rw [show ((A : Set E) ∪ ({b} : Set E)) = insert b (A : Set E) by
      ext x
      simp]
    have hinsert :
        IntermediateField.adjoin A (insert b (A : Set E)) =
          IntermediateField.adjoin A ({b} : Set E) := by
      refine le_antisymm ?_ ?_
      · rw [IntermediateField.adjoin_le_iff]
        intro y hy
        rcases Set.mem_insert_iff.mp hy with hyb | hyA
        · exact IntermediateField.mem_adjoin_of_mem (F := A) (S := ({b} : Set E)) (by
            simpa [hyb])
        · exact
            IntermediateField.adjoin_contains_field_as_subfield
              (F := A.toSubfield) (S := ({b} : Set E)) hyA
      · exact
          IntermediateField.adjoin.mono (F := A) ({b} : Set E) (insert b (A : Set E))
            (by
              intro y hy
              left
              simpa using hy)
    rw [hinsert]
    simpa [b] using hdeg
  -- The field embedding preserves relative finrank for mapped intermediate fields.
  calc
    (A.map σ).relfinrank (((IntermediateField.adjoin A ({β} : Set E)).restrictScalars F).map σ)
        = (A.map σ).relfinrank (B.map σ) := by rw [hB]
    _ = A.relfinrank B := by
          simpa using IntermediateField.relfinrank_map_map (A := A) (B := B) σ
    _ = p := hrel

/-- Helper for Lemma 10.42.4: after an algebraic base change of the ground field, adjoining the
old separable closure produces the new separable closure. This is the owner-level replacement for
the source compositum identity. -/
lemma adjoin_separableClosure_eq_separableClosure_of_isAlgebraic
    {F : Type*} {B : Type*} {E : Type*}
    [Field F] [Field B] [Field E]
    [Algebra F B] [Algebra F E] [Algebra B E] [IsScalarTower F B E]
    [Algebra.IsAlgebraic F B] :
    IntermediateField.adjoin B (separableClosure F E : Set E) = separableClosure B E := by
  -- This is exactly the canonical mathlib base-change identity for separable closures.
  simpa using separableClosure.adjoin_eq_of_isAlgebraic (F := F) (E := B) (K := E)

/-- Helper for Lemma 10.42.4: after an algebraic base change of the ground field, the image of an
element already lying in the old separable closure lands in the new separable closure. -/
lemma map_mem_separableClosure_of_isAlgebraic_base
    {F : Type*} {B : Type*} {E : Type*} {L : Type*}
    [Field F] [Field B] [Field E] [Field L]
    [Algebra F E] [Algebra F B] [Algebra F L] [Algebra B L] [IsScalarTower F B L]
    [Algebra.IsAlgebraic F B]
    (σ : E →ₐ[F] L) {x : E} (hx : x ∈ separableClosure F E) :
    σ x ∈ separableClosure B L := by
  have hx_sepF : σ x ∈ separableClosure F L :=
    separableClosure.map_le_of_algHom σ (show σ x ∈ (separableClosure F E).map σ from ⟨x, hx, rfl⟩)
  -- The old separable closure is contained in the new one after the algebraic base change.
  exact (separableClosure.le_restrictScalars (F := F) (E := B) (K := L)) hx_sepF

/-- Helper for Lemma 10.42.4: if `α` lies in an intermediate field and is a root of a separable
polynomial in the Frobenius image, then any chosen `p`th root of `α` already lies in that
intermediate field. -/
lemma mem_intermediateField_of_pow_eq_of_aeval_zero_of_separable_of_mem_map_frobenius_range
    {F : Type*} {A : Type*}
    [Field F] [Field A] [Algebra F A]
    (L : IntermediateField F A)
    {p : ℕ} [Fact p.Prime] [CharP F p]
    {α β : A} {P : Polynomial F}
    (hβ : β ^ p = α)
    (hαL : α ∈ L)
    (hPsep : P.Separable)
    (hPα : Polynomial.aeval α P = 0)
    (hmap : P ∈ Set.range (Polynomial.map (frobenius F p))) :
    β ∈ L := by
  letI : CharP A p := charP_of_injective_algebraMap (algebraMap F A).injective p
  let αL : L := ⟨α, hαL⟩
  have hPαL : Polynomial.aeval αL P = 0 := by
    apply (algebraMap L A).injective
    -- Evaluating in the intermediate field and then in the ambient field recovers the same root.
    have h_eval :
        (algebraMap L A) ((Polynomial.aeval αL) P) = Polynomial.aeval α P := by
      simpa [αL] using
        (Polynomial.aeval_algHom_apply (L.val.restrictScalars F) αL P).symm
    exact h_eval.trans hPα
  obtain ⟨γ, hγ⟩ :=
    exists_pth_root_of_aeval_zero_of_separable_of_mem_map_frobenius_range
      (K := F) (L := L) hPsep hPαL hmap
  have hγA : (γ : A) ^ p = α := by
    -- The extracted root in `L` is also a `p`th root of `α` in the ambient field.
    simpa [αL] using congrArg (fun z : L ↦ (z : A)) hγ
  have hβ_eq : β = γ := by
    -- Frobenius is injective on fields of characteristic `p`, so the two `p`th roots coincide.
    exact (frobenius A p).injective (by simpa [frobenius_def, hβ, hγA])
  simpa [hβ_eq] using γ.2

/-- Helper for Lemma 10.42.4: after the source algebraic base change, the image of `β ^ p`
already lies in the new separable closure. -/
lemma mapped_beta_pow_mem_new_separableClosure
    {F : Type*} {B : Type*} {E : Type*} {L : Type*}
    [Field F] [Field B] [Field E] [Field L]
    [Algebra F E] [Algebra F B] [Algebra F L] [Algebra B L] [IsScalarTower F B L]
    [Algebra.IsAlgebraic F B]
    {p : ℕ} (σ : E →ₐ[F] L) {β : E}
    (hβ_pow_mem : β ^ p ∈ separableClosure F E) :
    σ (β ^ p) ∈ separableClosure B L := by
  -- This is exactly the old-separable-closure transport applied to the source element `β ^ p`.
  exact
    map_mem_separableClosure_of_isAlgebraic_base
      (F := F) (B := B) (E := E) (L := L) σ hβ_pow_mem

/-- Helper for Lemma 10.42.4: once the image of the new degree-`p` generator lands in the
separable closure after the purely inseparable base change, the whole mapped simple step already
lies in that new separable closure. -/
lemma mapped_simple_step_le_new_separableClosure
    {F : Type*} {B : Type*} {E : Type*} {L : Type*}
    [Field F] [Field B] [Field E] [Field L]
    [Algebra F E] [Algebra F B] [Algebra F L] [Algebra B L] [IsScalarTower F B L]
    [Algebra.IsAlgebraic F B]
    (σ : E →ₐ[F] L) {β : E}
    (hβ : σ β ∈ separableClosure B L) :
    (((IntermediateField.adjoin (separableClosure F E) ({β} : Set E)).restrictScalars F).map σ) ≤
      (separableClosure B L).restrictScalars F := by
  let A : IntermediateField F E := separableClosure F E
  let M : IntermediateField F E := IntermediateField.adjoin F ((A : Set E) ∪ ({β} : Set E))
  have hM :
      ((IntermediateField.adjoin A ({β} : Set E)).restrictScalars F) = M := by
    -- Normalize the simple adjunction back to one `F`-adjoin so the mapped generators are
    -- exactly the old separable closure together with `β`.
    simpa [M] using
      (IntermediateField.restrictScalars_adjoin (F := F) (K := A) (S := ({β} : Set E)))
  have hAmap :
      A.map σ ≤ (separableClosure B L).restrictScalars F := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx_sepF : σ x ∈ separableClosure F L :=
      separableClosure.map_le_of_algHom σ (show σ x ∈ A.map σ from ⟨x, hx, rfl⟩)
    have hx_adjoin :
        σ x ∈ IntermediateField.adjoin B (separableClosure F L : Set L) := by
      exact IntermediateField.subset_adjoin (F := B) (S := (separableClosure F L : Set L)) hx_sepF
    -- Algebraic base change identifies adjoining the old separable closure with the new one.
    rw [adjoin_separableClosure_eq_separableClosure_of_isAlgebraic (F := F) (B := B) (E := L)] at hx_adjoin
    exact hx_adjoin
  rw [hM]
  unfold M
  rw [IntermediateField.adjoin_map, Set.image_union, Set.image_singleton, IntermediateField.adjoin_union]
  -- The mapped stage is generated by the mapped old separable closure and the one new element.
  refine sup_le ?_ ?_
  · rw [IntermediateField.adjoin_le_iff]
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hAmap (show σ x ∈ A.map σ from ⟨x, hx, rfl⟩)
  · rw [IntermediateField.adjoin_le_iff]
    intro y hy
    have hy' : y = σ β := by simpa using hy
    simpa [hy'] using hβ

/-- Helper for Lemma 10.42.4: an `F`-algebra equivalence transports the finite-dimensional tail
over the relative separable closure to the target field. -/
lemma finiteDimensional_over_separableClosure_of_algEquiv
    {F : Type*} {E : Type*} {L : Type*}
    [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra F L]
    [FiniteDimensional F E]
    (e : E ≃ₐ[F] L) :
    FiniteDimensional (separableClosure F L) L := by
  -- The algebra equivalence transports the finite-dimensional ambient extension to `L / F`.
  letI : FiniteDimensional F L := e.toLinearEquiv.finiteDimensional
  -- The relative separable closure is an intermediate field of that finite extension.
  infer_instance

/-- Helper for Lemma 10.42.4: once the mapped degree-`p` simple step is absorbed into the new
separable closure, the inseparable-degree measure strictly decreases. -/
lemma finInsepDegree_drop_after_absorbing_degree_p_step
    {F : Type*} {B : Type*} {E : Type*} {L : Type*}
    [Field F] [Field B] [Field E] [Field L]
    [Algebra F E] [Algebra F B] [Algebra F L] [Algebra B L] [IsScalarTower F B L]
    [Algebra.IsAlgebraic F B]
    [FiniteDimensional F E]
    [FiniteDimensional (separableClosure F E) E]
    {β : E} {p : ℕ} [Fact p.Prime]
    (e : E ≃ₐ[F] L)
    (hdeg :
      Module.finrank (separableClosure F E)
        (IntermediateField.adjoin (separableClosure F E) ({β} : Set E)) = p)
    (hcontain :
      (((IntermediateField.adjoin (separableClosure F E) ({β} : Set E)).restrictScalars F).map
          e.toAlgHom) ≤ (separableClosure B L).restrictScalars F) :
    Field.finInsepDegree B L < Field.finInsepDegree F E := by
  let A : IntermediateField F E := separableClosure F E
  let S : IntermediateField F L :=
    (((IntermediateField.adjoin A ({β} : Set E)).restrictScalars F).map e.toAlgHom)
  letI : FiniteDimensional F L := e.toLinearEquiv.finiteDimensional
  letI : FiniteDimensional (separableClosure F L) L :=
    finiteDimensional_over_separableClosure_of_algEquiv (F := F) (E := E) (L := L) e
  letI : FiniteDimensional (A.map e.toAlgHom) L := by infer_instance
  letI : FiniteDimensional S L := by infer_instance
  have hAmap : A.map e.toAlgHom = separableClosure F L := by
    -- The field-range equivalence carries the old separable closure to the new one.
    simpa [A] using (separableClosure.map_eq_of_algEquiv (F := F) e)
  have hAleS : A.map e.toAlgHom ≤ S := by
    -- The mapped source separable closure sits inside the mapped simple adjunction.
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x,
      IntermediateField.adjoin_contains_field_as_subfield
        (F := A.toSubfield) (S := ({β} : Set E)) hx,
      rfl⟩
  have hmap_deg :
      (A.map e.toAlgHom).relfinrank S = p := by
    -- Mapping the degree-`p` source step preserves its relative degree.
    simpa [A, S] using
      relfinrank_map_restrictScalars_adjoin_simple_eq
        (F := F) (E := E) (L := L) A e.toAlgHom (β := β) (p := p) hdeg
  have hstrict_step :
      Module.finrank S L < Module.finrank (A.map e.toAlgHom) L := by
    -- A relative degree `p > 1` forces the remaining tail degree to shrink strictly.
    exact finrank_lt_of_relfinrank_eq_prime (A := A.map e.toAlgHom) (B := S) hAleS hmap_deg
  have hmono :
      Module.finrank ((separableClosure B L).restrictScalars F) L ≤ Module.finrank S L := by
    -- Enlarging the intermediate field can only decrease the remaining top degree.
    exact IntermediateField.finrank_le_of_le_left hcontain
  have hstrict_target :
      Module.finrank ((separableClosure B L).restrictScalars F) L < Field.finInsepDegree F E := by
    -- Compare first with the mapped degree-`p` step and then rewrite via the field equivalence.
    calc
      Module.finrank ((separableClosure B L).restrictScalars F) L ≤ Module.finrank S L := hmono
      _ < Module.finrank (A.map e.toAlgHom) L := hstrict_step
      _ = Module.finrank (separableClosure F L) L := by rw [hAmap]
      _ = Field.finInsepDegree F L := rfl
      _ = Field.finInsepDegree F E := by
            simpa using (Field.finInsepDegree_eq_of_equiv (F := F) (E := E) (K := L) e).symm
  -- Finally rewrite the left-hand finrank as the inseparable-degree measure over `B`.
  simpa using hstrict_target

/-- Helper for Lemma 10.42.4: an `F`-algebra embedding of a finite-dimensional field extension has
finite-dimensional field range. This isolates the finite part of the source compositum square from
the later purely inseparable argument. -/
lemma finiteDimensional_fieldRange_of_finiteDimensional
    {F : Type*} {E : Type*} {L : Type*}
    [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra F L]
    [FiniteDimensional F E]
    (σ : E →ₐ[F] L) :
    FiniteDimensional F σ.fieldRange := by
  -- Transport the finite-dimensional structure across the canonical equivalence with the field
  -- range.
  let e : E ≃ₐ[F] σ.fieldRange := AlgEquiv.ofInjectiveField σ
  exact e.toLinearEquiv.finiteDimensional

/-- Helper for Lemma 10.42.4: after transporting the minimal polynomial through one coefficient
base change, the mapped root still annihilates the transported polynomial. This is the `aeval`
adapter needed after the source Frobenius-style coefficient descent. -/
lemma transported_minpoly_aeval_zero_after_base_change
    {F : Type*} {E : Type*} {B : Type*} {L : Type*}
    [Field F] [Field E] [Field B] [Field L]
    [Algebra F E] [Algebra F L] [Algebra B L]
    (σ : E →ₐ[F] L) (φ : F →+* B) {α : E}
    (hφ : (algebraMap B L).comp φ = algebraMap F L) :
    Polynomial.aeval (σ α) ((minpoly F α).map φ) = 0 := by
  -- First rewrite evaluation of the mapped polynomial back to evaluation of the original one.
  have hmap :
      Polynomial.aeval (σ α) ((minpoly F α).map φ) =
        Polynomial.aeval (σ α) (minpoly F α) := by
    symm
    exact Polynomial.aeval_eq_aeval_map (S := L) (T := B) hφ (minpoly F α) (σ α)
  rw [hmap]
  -- Then use the standard `minpoly` root relation transported along the embedding `σ`.
  simpa using (minpoly.aeval_algHom (A := F) (B := E) (B' := L) σ α)

/-- A finite purely inseparable lift of `K / k` whose upper extension becomes separably generated
over the lifted base field. -/
class IsPurelyInseparableLiftWithSeparablyGenerated
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (k' : Type w) [Field k'] [Algebra k k']
    (K' : Type (max v w)) [Field K'] [Algebra k K'] [Algebra K K'] [Algebra k' K']
    [IsScalarTower k K K'] [IsScalarTower k k' K'] : Prop where
  /-- The top extension in the lift is finite. -/
  finiteDimensional_top : FiniteDimensional K K'
  /-- The top extension in the lift is purely inseparable. -/
  purelyInseparable_top : IsPurelyInseparable K K'
  /-- The base change in the lift is finite. -/
  finiteDimensional_base : FiniteDimensional k k'
  /-- The base change in the lift is purely inseparable. -/
  purelyInseparable_base : IsPurelyInseparable k k'
  /-- After the lift, the total extension is separably generated. -/
  separablyGenerated_top : IsSeparablyGenerated k' K'

/-- Helper for Lemma 10.42.4: composing two finite purely inseparable lifts again gives a finite
purely inseparable lift whose top remains separably generated over the final base. -/
lemma compose_purelyInseparable_lifts
    {k' : Type w} [Field k'] [Algebra k k']
    {K' : Type (max v w)} [Field K'] [Algebra k K'] [Algebra K K'] [Algebra k' K']
    [IsScalarTower k K K'] [IsScalarTower k k' K']
    {w' : Type w} [Field w'] [Algebra k' w'] [Algebra k w']
    {L : Type (max v w)} [Field L] [Algebra k L] [Algebra K L] [Algebra k' L] [Algebra K' L]
    [Algebra w' L]
    [IsScalarTower k K L] [IsScalarTower k k' L] [IsScalarTower k' K' L] [IsScalarTower k' w' L]
    [IsScalarTower k w' L] [IsScalarTower K K' L] [IsScalarTower k k' w'] :
    IsPurelyInseparableLiftWithSeparablyGenerated k K k' K' →
      IsPurelyInseparableLiftWithSeparablyGenerated k' K' w' L →
        IsPurelyInseparableLiftWithSeparablyGenerated k K w' L := by
  intro h₁ h₂
  -- The composed square inherits finiteness and purely inseparable top/base edges by transitivity.
  refine
    ⟨?_, ?_, ?_, ?_, ?_⟩
  · letI : FiniteDimensional K K' := h₁.finiteDimensional_top
    letI : FiniteDimensional K' L := h₂.finiteDimensional_top
    exact FiniteDimensional.trans K K' L
  · letI : IsPurelyInseparable K K' := h₁.purelyInseparable_top
    letI : IsPurelyInseparable K' L := h₂.purelyInseparable_top
    exact IsPurelyInseparable.trans (F := K) (E := K') (K := L)
  · letI : FiniteDimensional k k' := h₁.finiteDimensional_base
    letI : FiniteDimensional k' w' := h₂.finiteDimensional_base
    exact FiniteDimensional.trans k k' w'
  · letI : IsPurelyInseparable k k' := h₁.purelyInseparable_base
    letI : IsPurelyInseparable k' w' := h₂.purelyInseparable_base
    exact IsPurelyInseparable.trans (F := k) (E := k') (K := w')
  · -- The second lift already provides separable generation over the final lifted base.
    exact h₂.separablyGenerated_top

/-- Helper for Lemma 10.42.4: if the first square is only a finite purely inseparable step on the
base and top edges, then composing it with a later purely inseparable lift still yields the final
purely inseparable lift with separably generated top. -/
lemma compose_purelyInseparable_step_with_lift
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    {B : Type w} [Field B] [Algebra F B]
    {L : Type (max v w)} [Field L] [Algebra F L] [Algebra E L] [Algebra B L]
    [IsScalarTower F E L] [IsScalarTower F B L]
    [FiniteDimensional F B] [IsPurelyInseparable F B]
    [FiniteDimensional E L] [IsPurelyInseparable E L]
    {B' : Type w} [Field B'] [Algebra F B'] [Algebra B B'] [IsScalarTower F B B']
    {L' : Type (max v w)} [Field L'] [Algebra F L'] [Algebra E L'] [Algebra B L'] [Algebra L L']
    [Algebra B' L']
    [IsScalarTower F E L'] [IsScalarTower E L L'] [IsScalarTower F B' L']
    [IsScalarTower B L L'] [IsScalarTower B B' L'] :
    IsPurelyInseparableLiftWithSeparablyGenerated B L B' L' →
      IsPurelyInseparableLiftWithSeparablyGenerated F E B' L' := by
  intro h
  -- The top edge is the composite `E ⟶ L ⟶ L'`, so finiteness and purely inseparable-ness
  -- propagate by the standard tower lemmas.
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · letI : FiniteDimensional L L' := h.finiteDimensional_top
    exact FiniteDimensional.trans E L L'
  · letI : IsPurelyInseparable L L' := h.purelyInseparable_top
    exact IsPurelyInseparable.trans (F := E) (E := L) (K := L')
  · letI : FiniteDimensional B B' := h.finiteDimensional_base
    exact FiniteDimensional.trans F B B'
  · letI : IsPurelyInseparable B B' := h.purelyInseparable_base
    exact IsPurelyInseparable.trans (F := F) (E := B) (K := B')
  · -- The second lift already provides the final separably generated structure.
    exact h.separablyGenerated_top

/-- Helper for Lemma 10.42.4: over a perfect base field, the identity square already gives the
required purely inseparable lift. -/
lemma exists_identity_lift_with_separablyGenerated_of_perfectField
    [PerfectField k] [Algebra.EssFiniteType k K] :
    ∃ (k' : Type (max u w)) (_ : Field k') (_ : Algebra k k')
      (K' : Type (max v (max u w))) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : IsScalarTower k K K') (_ : IsScalarTower k k' K'),
        IsPurelyInseparableLiftWithSeparablyGenerated k K k' K' := by
  let k' : Type (max u w) := ULift.{w} k
  let K' : Type (max v (max u w)) := ULift.{max u w} K
  let ek : k' ≃ₐ[k] k := by
    change ULift.{w} k ≃ₐ[k] k
    exact ULift.algEquiv (R := k) (A := k)
  letI : Algebra k' k := ULift.algebra' k k
  letI : Algebra k' K := ULift.algebra' k K
  letI : Algebra k' K' := ULift.algebra
  letI : Algebra.IsAlgebraic k k' := ek.symm.isAlgebraic
  letI : PerfectField k' := Algebra.IsAlgebraic.perfectField (K := k) (L := k')
  letI : Algebra.EssFiniteType k' k :=
    (Algebra.EssFiniteType.iff_of_algEquiv (ULift.algEquiv (R := k') (A := k))).mp inferInstance
  letI : Algebra.EssFiniteType k' K := Algebra.EssFiniteType.comp k' k K
  letI : Algebra.EssFiniteType k' K' :=
    (Algebra.EssFiniteType.iff_of_algEquiv (ULift.algEquiv (R := k') (A := K))).mpr inferInstance
  -- Use lifted copies of `k` and `K` so the witness universes match the theorem statement.
  refine ⟨k', inferInstance, inferInstance, K', inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ?_⟩
  -- The witness class fields are all the identity-extension facts.
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · exact (ULift.algEquiv (R := K) (A := K)).symm.isPurelyInseparable
  · infer_instance
  · exact (ULift.algEquiv (R := k) (A := k)).symm.isPurelyInseparable
  · infer_instance

/-- Helper for Lemma 10.42.4: if `K / k` is already separably generated, the source base case
packages into the theorem's widened-universe identity square. -/
lemma exists_identity_lift_with_separablyGenerated_of_isSeparablyGenerated
    (hsepgen : IsSeparablyGenerated k K) :
    ∃ (k' : Type (max u w)) (_ : Field k') (_ : Algebra k k')
      (K' : Type (max v (max u w))) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : IsScalarTower k K K') (_ : IsScalarTower k k' K'),
        IsPurelyInseparableLiftWithSeparablyGenerated k K k' K' := by
  let k' : Type (max u w) := ULift.{w} k
  let K' : Type (max v (max u w)) := ULift.{max u w} K
  let ek : k' ≃ₐ[k] k := by
    change ULift.{w} k ≃ₐ[k] k
    exact ULift.algEquiv (R := k) (A := k)
  letI : Algebra k' k := ULift.algebra' k k
  letI : Algebra k' K := ULift.algebra' k K
  letI : Algebra k' K' := ULift.algebra
  letI : Algebra.IsAlgebraic k k' := ek.symm.isAlgebraic
  have hsepgen_over_lifted_base : IsSeparablyGenerated k' K := by
    rcases hsepgen with ⟨s, hs, hsep⟩
    refine ⟨s, ?_, ?_⟩
    · -- Algebraic base change preserves the chosen transcendence basis.
      exact
        (Algebra.IsAlgebraic.isTranscendenceBasis_iff
          (R := k) (S := k') (A := K) (x := (Subtype.val : s → K))).mp hs
    · let F : IntermediateField k K := IntermediateField.adjoin k s
      let F' : IntermediateField k' K := IntermediateField.adjoin k' s
      letI : Algebra F F' :=
        (IntermediateField.inclusion
          (K := k) (L := K) (E := F) (F := F'.restrictScalars k)
          (IntermediateField.adjoin_le_iff.mpr fun y hy ↦
            IntermediateField.subset_adjoin (F := k') (S := s) hy)).toAlgebra
      letI : IsScalarTower F F' K := .of_algebraMap_eq fun x ↦ rfl
      letI : Algebra.IsSeparable F K := by
        simpa [F] using hsep
      -- Enlarging the intermediate base inside the same tower preserves separability.
      simpa [F, F'] using (Algebra.isSeparable_tower_top_of_isSeparable F F' K)
  have hsepgen_top : IsSeparablyGenerated k' K' := by
    -- Transport the separably generated structure across the lifted copy of `K`.
    exact hsepgen_over_lifted_base.of_algEquiv (ULift.algEquiv (R := k') (A := K)).symm
  refine ⟨k', inferInstance, inferInstance, K', inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ?_⟩
  -- All remaining fields are the identity-extension facts on the lifted copies.
  refine ⟨?_, ?_, ?_, ?_, hsepgen_top⟩
  · infer_instance
  · exact (ULift.algEquiv (R := K) (A := K)).symm.isPurelyInseparable
  · infer_instance
  · exact (ULift.algEquiv (R := k) (A := k)).symm.isPurelyInseparable

/-- Helper for Lemma 10.42.4: the inseparable degree over the transcendence-basis stage is
strictly positive, so the source induction never starts at `0`. -/
lemma finInsepDegree_pos_over_transcendence_basis_stage_aux
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]
    [Algebra.EssFiniteType F E]
    {r : ℕ} {x : Fin r → E}
    (hx : IsTranscendenceBasis F x) :
    0 < Field.finInsepDegree (IntermediateField.adjoin F (Set.range x)) E := by
  let F0 : IntermediateField F E := IntermediateField.adjoin F (Set.range x)
  letI : FiniteDimensional (separableClosure F0 E) E := by
    -- The transcendence-basis stage makes the source inseparable-degree tail finite-dimensional.
    simpa [F0] using
      finiteDimensional_over_separableClosure_of_isTranscendenceBasis (k := F) (K := E) hx
  -- The induction measure is the positive finite rank over the relative separable closure.
  simpa [Field.finInsepDegree, F0] using
    (Module.finrank_pos (R := separableClosure F0 E) (M := E))

/-- Helper for Lemma 10.42.4: any finite-index transcendence-basis stage with separable top
already witnesses separable generation. -/
lemma isSeparablyGenerated_of_isSeparable_over_transcendence_basis_stage_aux
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]
    {r : ℕ} {x : Fin r → E}
    (hx : IsTranscendenceBasis F x)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin F (Set.range x)) E) :
    IsSeparablyGenerated F E := by
  -- The given transcendence basis is already in the exact Stacks-project shape.
  refine ⟨Set.range x, hx.to_subtype_range, ?_⟩
  simpa using hsep

/-- Helper for Lemma 10.42.4: the omitted Stacks successor step can be packaged as one restarted
stage `(B, L, y)` with finite purely inseparable side edges and strictly smaller inseparable
degree over the lifted transcendence-basis stage. -/
lemma exists_base_change_absorbing_degree_p_step_into_separableClosure
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]
    {p : ℕ} [Fact p.Prime] [CharP F p] [Algebra.EssFiniteType F E]
    {r : ℕ} {x : Fin r → E}
    (hx : IsTranscendenceBasis F x)
    {β : E}
    (hβ_deg :
      Module.finrank (separableClosure (IntermediateField.adjoin F (Set.range x)) E)
        (IntermediateField.adjoin
          (separableClosure (IntermediateField.adjoin F (Set.range x)) E) ({β} : Set E)) = p)
    (hβ_pow_mem : β ^ p ∈ separableClosure (IntermediateField.adjoin F (Set.range x)) E) :
    ∃ (B : Type*) (_ : Field B) (_ : Algebra F B)
      (_ : FiniteDimensional F B) (_ : IsPurelyInseparable F B)
      (L : Type*) (_ : Field L) (_ : Algebra F L) (_ : Algebra E L) (_ : Algebra B L)
      (_ : IsScalarTower F E L) (_ : IsScalarTower F B L)
      (_ : FiniteDimensional E L) (_ : IsPurelyInseparable E L)
      (_ : Algebra.EssFiniteType B L)
      (y : Fin r → L),
        IsTranscendenceBasis B y ∧
          Field.finInsepDegree (IntermediateField.adjoin B (Set.range y)) L <
            Field.finInsepDegree (IntermediateField.adjoin F (Set.range x)) E := by
  -- TODO: follow the source route by transporting `minpoly F₀ (β ^ p)` to a Frobenius-style
  -- base change, adjoining `p`th roots of the finitely many support coefficients, constructing
  -- the compositum field over the lifted transcendence-basis stage, and then proving the image of
  -- `β` lands in the new separable closure via Lemma `9.28.2` so the inseparable degree drops.
  -- The current blocker is the universe-polymorphic packaging of that concrete restarted stage
  -- without detouring through later declarations.
  let _ := hx
  let _ := hβ_deg
  let _ := hβ_pow_mem
  sorry

/-- Helper for Lemma 10.42.4: the successor branch is packaged as one next-stage object already in
the exact form consumed by the recursive call. -/
structure SuccessorBranchRecursiveStageData
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
    (n : ℕ) (r : ℕ) where
  /-- The new purely inseparable base field in the successor branch. -/
  F' : Type (max u w)
  /-- The new base field carries a field structure. -/
  instFieldF' : Field F'
  /-- The new base field extends the original base field. -/
  instAlgFF' : Algebra F F'
  /-- The new ambient top field after the source base change and compositum construction. -/
  E' : Type (max v (max u w))
  /-- The new ambient top field carries a field structure. -/
  instFieldE' : Field E'
  /-- The new ambient top field still extends the original base. -/
  instAlgFE' : Algebra F E'
  /-- The new ambient top field extends the original top field. -/
  instAlgEE' : Algebra E E'
  /-- The new ambient top field extends the new base field. -/
  instAlgF'E' : Algebra F' E'
  /-- The old base-to-top tower persists after the successor step. -/
  instTowerFEE' : IsScalarTower F E E'
  /-- The new base-to-top tower needed by the recursive call. -/
  instTowerFF'E' : IsScalarTower F F' E'
  /-- The new base edge is finite. -/
  finiteDimensional_base : FiniteDimensional F F'
  /-- The new base edge is purely inseparable. -/
  purelyInseparable_base : IsPurelyInseparable F F'
  /-- The new top edge is finite. -/
  finiteDimensional_top : FiniteDimensional E E'
  /-- The new top edge is purely inseparable. -/
  purelyInseparable_top : IsPurelyInseparable E E'
  /-- The lifted transcendence basis at the restarted stage. -/
  x' : Fin r → E'
  /-- The restarted stage remains finitely generated over the new base. -/
  essFiniteType_top : Algebra.EssFiniteType F' E'
  /-- The lifted variables remain a transcendence basis over the new base. -/
  hx' : IsTranscendenceBasis F' x'
  /-- The restarted stage already satisfies the recursive inseparable-degree bound. -/
  bound : Field.finInsepDegree (IntermediateField.adjoin F' (Set.range x')) E' ≤ n

/-- Helper for Lemma 10.42.4: the omitted Stacks successor step can be packaged directly as one
restarted stage whose output already matches the recursive-call interface. -/
lemma exists_successor_branch_recursive_stage_data
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    {p : ℕ} [Fact p.Prime] [CharP F p] [Algebra.EssFiniteType F E]
    (n : ℕ) {r : ℕ} {x : Fin r → E}
    (hx : IsTranscendenceBasis F x)
    (hn :
      Field.finInsepDegree (IntermediateField.adjoin F (Set.range x)) E ≤ Nat.succ n)
    {β : E}
    (hβ_deg :
      Module.finrank (separableClosure (IntermediateField.adjoin F (Set.range x)) E)
        (IntermediateField.adjoin
          (separableClosure (IntermediateField.adjoin F (Set.range x)) E) ({β} : Set E)) = p)
    (hβ_pow_mem : β ^ p ∈ separableClosure (IntermediateField.adjoin F (Set.range x)) E) :
    Nonempty (SuccessorBranchRecursiveStageData F E n r) := by
  obtain ⟨B, hBField, hFB, hBfd, hBpi, L, hLField, hFL, hEL, hBL, hFEL, hFBL,
      hELfd, hELpi, hBLEss, y, hy, hdrop⟩ :=
    exists_base_change_absorbing_degree_p_step_into_separableClosure
      (F := F) (E := E) (p := p) hx hβ_deg hβ_pow_mem
  refine ⟨{
    F' := B
    instFieldF' := hBField
    instAlgFF' := hFB
    E' := L
    instFieldE' := hLField
    instAlgFE' := hFL
    instAlgEE' := hEL
    instAlgF'E' := hBL
    instTowerFEE' := hFEL
    instTowerFF'E' := hFBL
    finiteDimensional_base := hBfd
    purelyInseparable_base := hBpi
    finiteDimensional_top := hELfd
    purelyInseparable_top := hELpi
    x' := y
    essFiniteType_top := hBLEss
    hx' := hy
    bound := by omega }⟩

/-- Helper for Lemma 10.42.4: if the inseparable degree over the transcendence-basis stage is
already `1`, then the source induction is in its separable base case and the identity lift
finishes immediately. -/
lemma exists_identity_lift_with_separablyGenerated_of_stage_finInsepDegree_eq_one
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    {r : ℕ} {x : Fin r → E}
    (hx : IsTranscendenceBasis F x)
    (hsepdeg :
      Field.finInsepDegree (IntermediateField.adjoin F (Set.range x)) E = 1) :
    ∃ (F' : Type (max u w)) (_ : Field F') (_ : Algebra F F')
      (E' : Type (max v (max u w))) (_ : Field E') (_ : Algebra F E') (_ : Algebra E E')
      (_ : Algebra F' E') (_ : IsScalarTower F E E') (_ : IsScalarTower F F' E'),
        IsPurelyInseparableLiftWithSeparablyGenerated F E F' E' := by
  let F0 : IntermediateField F E := IntermediateField.adjoin F (Set.range x)
  -- Convert the source degree-one condition into separability over the generated stage.
  have hsep : Algebra.IsSeparable F0 E := by
    rw [isSeparable_iff_finInsepDegree_eq_one]
    exact hsepdeg
  have hsepgen : IsSeparablyGenerated F E :=
    isSeparablyGenerated_of_isSeparable_over_transcendence_basis_stage_aux
      (F := F) (E := E) hx hsep
  -- The separable base case is exactly the identity-lift theorem already proved above.
  simpa [F0] using
    exists_identity_lift_with_separablyGenerated_of_isSeparablyGenerated
      (k := F) (K := E) hsepgen

/-- Helper for Lemma 10.42.4: if the inseparable degree over the transcendence-basis stage is
strictly larger than `1`, then the source proof extracts one degree-`p` simple purely inseparable
step whose `p`th power lies in the relative separable closure. -/
lemma exists_degree_p_simple_step_over_transcendence_basis_stage
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    {p : ℕ} [Fact p.Prime] [CharP F p] [Algebra.EssFiniteType F E]
    {r : ℕ} {x : Fin r → E}
    (hx : IsTranscendenceBasis F x)
    (hgt :
      1 < Field.finInsepDegree (IntermediateField.adjoin F (Set.range x)) E) :
    ∃ β : E,
      Module.finrank (separableClosure (IntermediateField.adjoin F (Set.range x)) E)
        (IntermediateField.adjoin
          (separableClosure (IntermediateField.adjoin F (Set.range x)) E) ({β} : Set E)) = p ∧
      β ^ p ∈ separableClosure (IntermediateField.adjoin F (Set.range x)) E := by
  let F0 : IntermediateField F E := IntermediateField.adjoin F (Set.range x)
  letI : Algebra.IsAlgebraic F0 E := by
    -- The transcendence-basis stage is algebraic over the ambient field extension.
    simpa [F0] using hx.isAlgebraic_field
  let A : IntermediateField F0 E := separableClosure F0 E
  letI : FiniteDimensional A E := by
    -- Finite generation over the original base makes the inseparable tail over `F0` finite.
    simpa [A, F0] using
      finiteDimensional_over_separableClosure_of_isTranscendenceBasis
        (k := F) (K := E) hx
  letI : CharP F0 p := charP_of_injective_algebraMap (algebraMap F F0).injective p
  letI : CharP A p := charP_of_injective_algebraMap (algebraMap F0 A).injective p
  letI : IsPurelyInseparable A E := separableClosure.isPurelyInseparable (F := F0) (E := E)
  have hgt_rank : 1 < Module.finrank A E := by
    simpa [Field.finInsepDegree, A, F0] using hgt
  obtain ⟨β, hβ_deg, hβ_pow_mem_bot, _⟩ :=
    exists_degree_p_simple_step_of_nontrivial
      (K := A) (L := E) p hgt_rank
  refine ⟨β, hβ_deg, ?_⟩
  -- Membership in the bottom field over `A` means exactly membership in the embedded closure `A`.
  simpa [A, IntermediateField.mem_bot] using hβ_pow_mem_bot

/-- Helper for Lemma 10.42.4: the source induction on inseparable degree must quantify over the
current stage before recursing, so the induction hypothesis can be reused after one successor-step
base change. -/
lemma exists_purelyInseparable_lift_with_separablyGenerated_bounded_stage_univ
    (n : ℕ) {F : Type u1} {E : Type v1} [Field F] [Field E] [Algebra F E]
    {p : ℕ} [Fact p.Prime] [CharP F p] [Algebra.EssFiniteType F E]
    {r : ℕ} {x : Fin r → E}
    (hx : IsTranscendenceBasis F x)
    (hn : Field.finInsepDegree (IntermediateField.adjoin F (Set.range x)) E ≤ n) :
    ∃ (F' : Type (max u1 w)) (_ : Field F') (_ : Algebra F F')
      (E' : Type (max v1 (max u1 w))) (_ : Field E') (_ : Algebra F E')
      (_ : Algebra E E') (_ : Algebra F' E')
      (_ : IsScalarTower F E E') (_ : IsScalarTower F F' E'),
        IsPurelyInseparableLiftWithSeparablyGenerated F E F' E' := by
  -- TODO: use a genuinely recursive theorem definition so the recursive call can re-instantiate
  -- this statement at the widened successor-stage universes produced by
  -- `SuccessorBranchRecursiveStageData`. The source mathematical route is already isolated to the
  -- degree-`p` successor package plus one composition step back to the original stage.
  let _ := n
  let _ := hx
  let _ := hn
  sorry

/-- Helper for Lemma 10.42.4: source-faithful induction on the inseparable degree works over an
arbitrary current stage `(F, E, x)` rather than only over the original `(k, K)`. -/
lemma exists_purelyInseparable_lift_with_separablyGenerated_bounded_aux
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    {p : ℕ} [Fact p.Prime] [CharP F p] [Algebra.EssFiniteType F E]
    (n : ℕ) {r : ℕ} {x : Fin r → E}
    (hx : IsTranscendenceBasis F x)
    (hn :
      Field.finInsepDegree (IntermediateField.adjoin F (Set.range x)) E ≤ n) :
    ∃ (F' : Type (max u w)) (_ : Field F') (_ : Algebra F F')
      (E' : Type (max v (max u w))) (_ : Field E') (_ : Algebra F E') (_ : Algebra E E')
      (_ : Algebra F' E') (_ : IsScalarTower F E E') (_ : IsScalarTower F F' E'),
        IsPurelyInseparableLiftWithSeparablyGenerated F E F' E' := by
  -- The old fixed-stage helper is now only the specialization of the stage-universe induction.
  exact
    exists_purelyInseparable_lift_with_separablyGenerated_bounded_stage_univ
      n (F := F) (E := E) (p := p) (r := r) (x := x) hx hn

/-- Helper for Lemma 10.42.4: the original fixed-index positivity statement is now just the
specialization of the generic stage-positivity lemma to `(k, K)`. -/
lemma finInsepDegree_pos_over_transcendence_basis_stage
    [Algebra.EssFiniteType k K]
    {x : Fin (Cardinal.toNat (Algebra.trdeg k K)) → K}
    (hx : IsTranscendenceBasis k x) :
    0 < Field.finInsepDegree (IntermediateField.adjoin k (Set.range x)) K := by
  -- This is the original stage-indexed wrapper around the generic positivity lemma.
  exact
    finInsepDegree_pos_over_transcendence_basis_stage_aux
      (F := k) (E := K) hx

/-- Helper for Lemma 10.42.4: separability over the field generated by a transcendence basis is
exactly the Stacks notion of separably generated. -/
lemma isSeparablyGenerated_of_isSeparable_over_transcendence_basis_stage
    {x : Fin (Cardinal.toNat (Algebra.trdeg k K)) → K}
    (hx : IsTranscendenceBasis k x)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K) :
    IsSeparablyGenerated k K := by
  -- This is the original stage-indexed wrapper around the generic separable-generation lemma.
  exact
    isSeparablyGenerated_of_isSeparable_over_transcendence_basis_stage_aux
      (F := k) (E := K) hx hsep

/-- Helper for Lemma 10.42.4: a bound on the inseparable degree over the transcendence-basis
stage is the source induction parameter for constructing the purely inseparable lift. -/
lemma exists_purelyInseparable_lift_with_separablyGenerated_bounded_by_finInsepDegree
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra.EssFiniteType k K]
    (n : ℕ) {x : Fin (Cardinal.toNat (Algebra.trdeg k K)) → K}
    (hx : IsTranscendenceBasis k x)
    (hn :
      Field.finInsepDegree (IntermediateField.adjoin k (Set.range x)) K ≤ n) :
    ∃ (k' : Type (max u w)) (_ : Field k') (_ : Algebra k k')
      (K' : Type (max v (max u w))) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : IsScalarTower k K K') (_ : IsScalarTower k k' K'),
        IsPurelyInseparableLiftWithSeparablyGenerated k K k' K' := by
  -- Route correction: the actual induction is stage-generic, so this theorem is now only the
  -- original-index wrapper used by the public positive-characteristic proof.
  exact
    exists_purelyInseparable_lift_with_separablyGenerated_bounded_aux
      (F := k) (E := K) (p := p) n hx hn

/-- Helper for Lemma 10.42.4: the mathlib Frobenius linear-independence criterion upgrades a
finitely generated characteristic-`p` extension to a separably generated one. -/
lemma isSeparablyGenerated_of_linearIndepOn_pow
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra.EssFiniteType k K]
    (hlin :
      ∀ s : Finset K,
        LinearIndepOn k _root_.id (s : Set K) →
          LinearIndepOn k (fun x ↦ x ^ p) (s : Set K)) :
    IsSeparablyGenerated k K := by
  -- Apply the owner theorem producing a separating transcendence basis from the Frobenius
  -- linear-independence hypothesis.
  obtain ⟨s, hs, hsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
      (k := k) (K := K) (p := p) (hp := Fact.out) hlin
  refine ⟨(s : Set K), ?_, ?_⟩
  · -- The finite-set witness is the required transcendence basis after forgetting finiteness.
    simpa using hs
  · -- The resulting extension over the generated intermediate field is separable.
    simpa using hsep

/-- Helper for Lemma 10.42.4: after a finite purely inseparable lift satisfies the Frobenius
linear-independence criterion, the lifted top field is already separably generated over the lifted
base field. -/
lemma lift_with_separablyGenerated_of_linearIndepOn_pow
    {k' : Type (max u w)} [Field k'] [Algebra k k']
    {K' : Type (max v (max u w))} [Field K'] [Algebra k K'] [Algebra K K'] [Algebra k' K']
    [IsScalarTower k K K'] [IsScalarTower k k' K']
    [FiniteDimensional k k'] [IsPurelyInseparable k k']
    [FiniteDimensional K K'] [IsPurelyInseparable K K']
    {p : ℕ} [Fact p.Prime] [CharP k' p] [Algebra.EssFiniteType k' K']
    (hlin :
      ∀ s : Finset K',
        LinearIndepOn k' _root_.id (s : Set K') →
          LinearIndepOn k' (fun x ↦ x ^ p) (s : Set K')) :
    IsPurelyInseparableLiftWithSeparablyGenerated k K k' K' := by
  have hsepgen : IsSeparablyGenerated k' K' :=
    isSeparablyGenerated_of_linearIndepOn_pow (k := k') (K := K') (p := p) hlin
  -- The lift data are already purely inseparable and finite; only separable generation remains.
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, hsepgen⟩

/-- Helper for Lemma 10.42.4: in positive characteristic, the remaining work is the source-style
induction on the purely inseparable degree over a separating transcendence basis. -/
lemma exists_purelyInseparable_lift_with_separablyGenerated_of_positiveCharacteristic
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra.EssFiniteType k K] :
    ∃ (k' : Type (max u w)) (_ : Field k') (_ : Algebra k k')
      (K' : Type (max v (max u w))) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : IsScalarTower k K K') (_ : IsScalarTower k k' K'),
        IsPurelyInseparableLiftWithSeparablyGenerated k K k' K' := by
  classical
  by_cases hperfect : PerfectField k
  · -- If the characteristic-`p` base is already perfect, the identity square is enough.
    letI : PerfectField k := hperfect
    exact exists_identity_lift_with_separablyGenerated_of_perfectField (k := k) (K := K)
  · -- Route correction: the source induction is only needed in the imperfect positive-characteristic
    -- case. Choose the source transcendence-basis stage and recurse directly on its inseparable
    -- degree instead of detouring through the stronger Frobenius linear-independence criterion.
    obtain ⟨x, hx, _⟩ :=
      exists_fin_reindexed_transcendence_basis_with_finiteDimensional_over_separableClosure
        (k := k) (K := K)
    exact
      exists_purelyInseparable_lift_with_separablyGenerated_bounded_by_finInsepDegree
        (k := k) (K := K) (p := p)
        (n := Field.finInsepDegree (IntermediateField.adjoin k (Set.range x)) K) hx le_rfl

-- Proof sketch: choose a separating transcendence basis after passing to the separable closure
-- decomposition from Lemma `9.14.6`. In positive characteristic, adjoin finitely many `p`th
-- roots to the base so that one step of the purely inseparable part descends into the separable
-- closure using Lemma `9.28.2`, reducing the inseparable degree. Induct on that degree.
/-- Lemma 10.42.4: for a finitely generated field extension `K/k`, there exist fields `k'` and
`K'` forming a commutative square of extensions over `k`, with `K' / K` and `k' / k` finite
purely inseparable and `K' / k'` separably generated. -/
theorem exists_purelyInseparable_lift_with_separablyGenerated
    [Algebra.EssFiniteType k K] :
    ∃ (k' : Type (max u w)) (_ : Field k') (_ : Algebra k k')
      (K' : Type (max v (max u w))) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : IsScalarTower k K K') (_ : IsScalarTower k k' K'),
        IsPurelyInseparableLiftWithSeparablyGenerated k K k' K' := by
  -- Route correction: the witness universes must be widened to `Type (max u w)` and
  -- `Type (max v (max u w))`; otherwise even the characteristic-zero identity lift is not typable
  -- when the requested witness universes are smaller than the source universes.
  obtain hchar0 | ⟨p, hp, hcharp⟩ := CharP.exists' k
  · -- Characteristic zero is perfect, so the identity square already works.
    letI : CharZero k := hchar0
    letI : PerfectField k := PerfectField.ofCharZero
    exact exists_identity_lift_with_separablyGenerated_of_perfectField (k := k) (K := K)
  · -- The positive-characteristic case is the remaining source-style induction.
    letI : Fact p.Prime := hp
    letI : CharP k p := hcharp
    exact
      exists_purelyInseparable_lift_with_separablyGenerated_of_positiveCharacteristic
        (k := k) (K := K)

end
