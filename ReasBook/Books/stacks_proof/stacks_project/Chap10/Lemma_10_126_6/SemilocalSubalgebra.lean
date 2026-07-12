import StacksProject_2024.Chap10.Lemma_10_126_6.TargetAuxiliary

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FinitePresentation R S]
variable (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Helper for Lemma 10.126.6: the canonical comparison map from the semilocal localization
`S_p` to the prime localization `S_q`. This is the source-proof map `S_p → S_q` used to identify
the localized kernel after the final away shrink. -/
noncomputable def semilocal_to_local_of_lies_over
    (hq : q.LiesOver p) :
    Localization (Algebra.algebraMapSubmonoid S p.primeCompl) →ₐ[S] Localization.AtPrime q :=
  IsLocalization.liftAlgHom
    (M := Algebra.algebraMapSubmonoid S p.primeCompl)
    (f := Algebra.ofId S (Localization.AtPrime q))
    (by
      rintro ⟨_, x, hx, rfl⟩
      have hxq : algebraMap R S x ∈ q.primeCompl := by
        -- Proof comment: an element of `R \ p` stays outside `q` because `q` lies over `p`.
        change algebraMap R S x ∉ q
        intro hxq
        exact hx (by
          rw [hq.over]
          simpa [Ideal.mem_comap] using hxq)
      exact IsLocalization.map_units (Localization.AtPrime q) ⟨algebraMap R S x, hxq⟩)

/-- Helper for Lemma 10.126.6: the canonical semilocal-to-local comparison sends an element of
`S` to its ordinary image in `S_q`. -/
@[simp] theorem semilocal_to_local_of_lies_over_to_map
    (hq : q.LiesOver p) (x : S) :
    semilocal_to_local_of_lies_over (R := R) (S := S) (p := p) (q := q) hq
        (algebraMap S (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) x) =
      algebraMap S (Localization.AtPrime q) x := by
  -- Proof comment: `IsLocalization.liftAlgHom` is characterized by its values on the source ring.
  simp [semilocal_to_local_of_lies_over]

/-- Helper for Lemma 10.126.6: the canonical semilocal-to-local comparison intertwines the two
algebra maps out of `S`. -/
@[simp] theorem semilocal_to_local_of_lies_over_comp_algebraMap
    (hq : q.LiesOver p) :
    (semilocal_to_local_of_lies_over (R := R) (S := S) (p := p) (q := q) hq).toRingHom.comp
        (algebraMap S (Localization (Algebra.algebraMapSubmonoid S p.primeCompl))) =
      algebraMap S (Localization.AtPrime q) := by
  -- Proof comment: compare both ring maps on the dense image of `S` in the semilocal
  -- localization.
  ext x
  simp [semilocal_to_local_of_lies_over]

/-- Helper for Lemma 10.126.6: composing the base away map `R_f → S'_f` with the induced map
`S'_f → S_f` recovers the canonical away map `R_f → S_f`. -/
theorem subalgebra_awayMap_comp_eq_base_awayMap
    (S' : Subalgebra R S) (f : R) :
    (Localization.awayMap S'.val.toRingHom (algebraMap R S' f)).comp
        (Localization.awayMap (algebraMap R S') f) =
      Localization.awayMap (algebraMap R S) f := by
  -- Proof comment: both sides are the canonical maps out of `R_f`, and `IsLocalization` already
  -- records that localizing along `R → S' → S` agrees with localizing along `R → S` directly.
  have hbaseS' :
      Submonoid.powers f ≤
        Submonoid.comap (algebraMap R S') (Submonoid.powers (algebraMap R S' f)) := by
    rintro x ⟨n, rfl⟩
    exact ⟨n, by simp⟩
  have hsub :
      Submonoid.powers (algebraMap R S' f) ≤
        Submonoid.comap S'.val.toRingHom (Submonoid.powers (algebraMap R S f)) := by
    rintro x ⟨n, rfl⟩
    exact ⟨n, by simp⟩
  have hbaseS :
      Submonoid.powers f ≤
        Submonoid.comap (algebraMap R S) (Submonoid.powers (algebraMap R S f)) := by
    rintro x ⟨n, rfl⟩
    exact ⟨n, by simp⟩
  have hcompS' :
      (Localization.awayMap (algebraMap R S') f).comp
          (algebraMap R (Localization.Away f)) =
        (algebraMap S' (Localization.Away (algebraMap R S' f))).comp
          (algebraMap R S') := by
    simpa [Localization.awayMap] using
      (IsLocalization.map_comp
        (Q := Localization.Away (algebraMap R S' f))
        (g := algebraMap R S')
        (hy := hbaseS'))
  have hcompSub :
      (Localization.awayMap S'.val.toRingHom (algebraMap R S' f)).comp
          (algebraMap S' (Localization.Away (algebraMap R S' f))) =
        (algebraMap S (Localization.Away (algebraMap R S f))).comp
          S'.val.toRingHom := by
    simpa [Localization.awayMap] using
      (IsLocalization.map_comp
        (Q := Localization.Away (algebraMap R S f))
        (g := S'.val.toRingHom)
        (hy := hsub))
  have hcompS :
      (Localization.awayMap (algebraMap R S) f).comp
          (algebraMap R (Localization.Away f)) =
        (algebraMap S (Localization.Away (algebraMap R S f))).comp
          (algebraMap R S) := by
    simpa [Localization.awayMap] using
      (IsLocalization.map_comp
        (Q := Localization.Away (algebraMap R S f))
        (g := algebraMap R S)
        (hy := hbaseS))
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  -- Proof comment: after restricting both maps to the dense image of `R` in `R_f`, the two-step
  -- localization square becomes the single-step square `R → S`.
  calc
    (((Localization.awayMap S'.val.toRingHom (algebraMap R S' f)).comp
        (Localization.awayMap (algebraMap R S') f))).comp
        (algebraMap R (Localization.Away f)) =
      (Localization.awayMap S'.val.toRingHom (algebraMap R S' f)).comp
        ((Localization.awayMap (algebraMap R S') f).comp
          (algebraMap R (Localization.Away f))) := by
            rw [RingHom.comp_assoc]
    _ =
      (Localization.awayMap S'.val.toRingHom (algebraMap R S' f)).comp
        ((algebraMap S' (Localization.Away (algebraMap R S' f))).comp
          (algebraMap R S')) := by
            rw [hcompS']
    _ =
      ((Localization.awayMap S'.val.toRingHom (algebraMap R S' f)).comp
        (algebraMap S' (Localization.Away (algebraMap R S' f)))).comp
          (algebraMap R S') := by
            rw [← RingHom.comp_assoc]
    _ =
      ((algebraMap S (Localization.Away (algebraMap R S f))).comp
        S'.val.toRingHom).comp
          (algebraMap R S') := by
            exact congrArg
              (fun F : S' →+* Localization.Away (algebraMap R S f) ↦
                F.comp (algebraMap R S'))
              hcompSub
    _ =
      (algebraMap S (Localization.Away (algebraMap R S f))).comp
        (S'.val.toRingHom.comp (algebraMap R S')) := by
            rw [RingHom.comp_assoc]
    _ =
      (algebraMap S (Localization.Away (algebraMap R S f))).comp
        (algebraMap R S) := by
            rfl
    _ =
      (Localization.awayMap (algebraMap R S) f).comp
        (algebraMap R (Localization.Away f)) := by
            rw [hcompS]

/-- Helper for Lemma 10.126.6: passing from the finite subalgebra neighborhood `S'` back to `S`
does not change the kernel of the base map `R → S'`. -/
theorem subalgebra_algebraMap_ker_eq
    (S' : Subalgebra R S) :
    RingHom.ker (algebraMap R S') = RingHom.ker (algebraMap R S) := by
  ext x
  constructor
  · intro hx
    -- Proof comment: the inclusion `S' ↪ S` carries the `R`-algebra map for `S'` to the one for
    -- `S`, so vanishing in `S'` immediately implies vanishing in `S`.
    change algebraMap R S x = 0
    exact congrArg S'.val hx
  · intro hx
    -- Proof comment: conversely, the inclusion `S' ↪ S` is injective, so vanishing in `S`
    -- already forces vanishing in the finite subalgebra.
    change algebraMap R S' x = 0
    exact Subtype.val_injective <| by simpa using hx

/-- Helper for Lemma 10.126.6: if the kernel of `R → S'` is finitely generated, then injectivity
of the stalk map `R_𝔭 → S'_{𝔮'}` spreads to injectivity on a sufficiently small basic open of the
base. -/
theorem finite_subalgebra_exists_injective_base_away_of_kernel_fg
    (S' : Subalgebra R S)
    (q' : Ideal S') [q'.IsPrime] [q'.LiesOver p]
    (hkerfg : (RingHom.ker (algebraMap R S')).FG)
    (hlocalS' :
      Function.Injective
        (Localization.localRingHom p q' (algebraMap R S') (q'.over_def p))) :
    ∃ f : R, f ∉ p ∧ ∀ f', f ∣ f' →
      Function.Injective (Localization.awayMap (algebraMap R S') f') := by
  -- Proof comment: once the kernel is finitely generated, the owner-local theorem
  -- `exists_awayMap_injective_of_localRingHom_injective` applies directly to the finite
  -- subalgebra neighborhood.
  simpa using
    (Localization.exists_awayMap_injective_of_localRingHom_injective
      (R := R)
      (S := S')
      (p := p)
      (q := q')
      hkerfg
      hlocalS')

/-- Helper for Lemma 10.126.6: if a finite generating family of the finite subalgebra `S'`
becomes a family of explicit base multiples after inverting `f`, then the away map `R_f → S'_f`
is surjective. -/
theorem awayMap_surjective_of_scaled_module_generators
    (S' : Subalgebra R S)
    {n : ℕ} (y : Fin n → S')
    (hy : Submodule.span R (Set.range y) = ⊤)
    (f : R) (a : Fin n → R)
    (ha : ∀ i, algebraMap R S' f * y i = algebraMap R S' (a i)) :
    Function.Surjective (Localization.awayMap (algebraMap R S') f) := by
  rw [Localization.awayMap_surjective_iff]
  intro z
  have hz_mem : z ∈ Submodule.span R (Set.range y) := by
    simpa [hy] using (show z ∈ (⊤ : Submodule R S') by trivial)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hz_mem
  refine ⟨∑ i, c i * a i, 1, ?_⟩
  rw [pow_one]
  -- Proof comment: write `z` as an `R`-linear combination of the chosen generators and then use
  -- the hypotheses `f * y i = a i` to clear the common denominator in one step.
  calc
    algebraMap R S' (∑ i, c i * a i)
        = ∑ i, algebraMap R S' (c i * a i) := by
            simp
    _ = ∑ i, algebraMap R S' (c i) * (algebraMap R S' f * y i) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [ha i, mul_assoc]
    _ = ∑ i, algebraMap R S' f * (algebraMap R S' (c i) * y i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = algebraMap R S' f * ∑ i, algebraMap R S' (c i) * y i := by
          rw [Finset.mul_sum]
    _ = algebraMap R S' f * z := by
          congr 1
          simpa [Algebra.smul_def] using hc

/-- Helper for Lemma 10.126.6: once one refined basic-open witness gives surjectivity for
`R_f → S'_f` and another gives eventual injectivity, taking a common multiple produces a single
base element on which both `R_f → S'_f` and `S'_f → S_f` are bijective. -/
theorem finite_subalgebra_exists_refining_base_away_bijective_of_witnesses
    (S' : Subalgebra R S) (r : S')
    (hr : Function.Bijective (Localization.awayMap S'.val.toRingHom r))
    (hsurj :
      ∃ f : R, f ∉ p ∧ r ∣ algebraMap R S' f ∧
        Function.Surjective (Localization.awayMap (algebraMap R S') f))
    (hinj :
      ∃ f : R, f ∉ p ∧ ∀ f', f ∣ f' →
        Function.Injective (Localization.awayMap (algebraMap R S') f')) :
    ∃ f₄ : R, f₄ ∉ p ∧
      Function.Bijective (Localization.awayMap (algebraMap R S') f₄) ∧
      Function.Bijective
        (Localization.awayMap S'.val.toRingHom (algebraMap R S' f₄)) := by
  obtain ⟨f₁, hf₁, hrf₁, hsurj₁⟩ := hsurj
  obtain ⟨f₂, hf₂, hinj₂⟩ := hinj
  let f₄ : R := f₁ * f₂
  have hf₄ : f₄ ∉ p := by
    -- Proof comment: the common multiple still avoids the prime `p`.
    exact ‹p.IsPrime›.mul_notMem hf₁ hf₂
  have hdiv₁ : f₁ ∣ f₄ := ⟨f₂, by simp [f₄]⟩
  have hdiv₂ : f₂ ∣ f₄ := ⟨f₁, by simp [f₄, mul_comm]⟩
  have hRS'f₄ : Function.Bijective (Localization.awayMap (algebraMap R S') f₄) := by
    constructor
    · -- Proof comment: injectivity is stable after enlarging the basic open.
      exact hinj₂ f₄ hdiv₂
    · -- Proof comment: surjectivity is likewise stable under passing to a common multiple.
      exact Localization.awayMap_surjective_of_dvd (algebraMap R S') hdiv₁ hsurj₁
  have hrf₄ : r ∣ algebraMap R S' f₄ := by
    rcases hrf₁ with ⟨c, hc⟩
    -- Proof comment: if `r` divides `f₁` in `S'`, then it also divides the larger element
    -- `f₁ * f₂`.
    refine ⟨c * algebraMap R S' f₂, ?_⟩
    calc
      algebraMap R S' f₄ = algebraMap R S' (f₁ * f₂) := by rfl
      _ = algebraMap R S' f₁ * algebraMap R S' f₂ := by rw [map_mul]
      _ = (r * c) * algebraMap R S' f₂ := by rw [hc]
      _ = r * (c * algebraMap R S' f₂) := by rw [mul_assoc]
  have hS'f₄ :
      Function.Bijective
        (Localization.awayMap S'.val.toRingHom (algebraMap R S' f₄)) := by
    -- Proof comment: the original neighborhood isomorphism on `D(r)` upgrades to the larger basic
    -- open because `r` divides the chosen base element inside `S'`.
    exact Localization.awayMap_bijective_of_dvd S'.val.toRingHom hrf₄ hr
  exact ⟨f₄, hf₄, hRS'f₄, hS'f₄⟩

/-- Helper for Lemma 10.126.6: once one base element `f` makes both `R_f → S'_f` and
`S'_f → S_f` bijective, the desired product decomposition of `S_f` follows immediately. -/
theorem exists_product_factor_of_refining_subalgebra_away_bijective
    (S' : Subalgebra R S) (f : R)
    (hRS' : Function.Bijective (Localization.awayMap (algebraMap R S') f))
    (hS'S : Function.Bijective
      (Localization.awayMap S'.val.toRingHom (algebraMap R S' f))) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      (Localization.awayMap (algebraMap R S) f).toAlgebra
    ∃ (C : Type w) (_ : CommRing C) (_ : Algebra (Localization.Away f) C),
      Nonempty
        (Localization.Away (algebraMap R S f) ≃ₐ[Localization.Away f]
          (Localization.Away f × C)) := by
  have hcomp :
      Function.Bijective
        ((Localization.awayMap S'.val.toRingHom (algebraMap R S' f)).comp
          (Localization.awayMap (algebraMap R S') f)) := by
    constructor
    · exact hS'S.1.comp hRS'.1
    · exact hS'S.2.comp hRS'.2
  have hbase : Function.Bijective (Localization.awayMap (algebraMap R S) f) := by
    -- Proof comment: rewrite the composite of the two neighborhood isomorphisms as the canonical
    -- away map for `R → S`, then invoke the already prepared trivial-product-factor lemma.
    rw [← subalgebra_awayMap_comp_eq_base_awayMap (R := R) (S := S) S' f]
    exact hcomp
  exact exists_product_factor_of_bijective_awayMap (R := R) (S := S) f hbase

end
