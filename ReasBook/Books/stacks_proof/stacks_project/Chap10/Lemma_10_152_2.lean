import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]

/-! The proof below follows the standard-étale-surjection route from the source proof.  The
surjection is first split once as a quotient by an idempotent kernel; the prime bookkeeping is then
done through the first-isomorphism equivalence to the distinguished localization. -/

/-- Helper for Chap10 Lemma 10 152 2: a `K`-algebra map compatible with an `S`-algebra structure
can be viewed as an `S`-algebra map. -/
private def algHomOfCompatibleBase
    {K : Type u} {S₀ : Type v} {T : Type (max u v)} {C : Type v}
    [CommSemiring K] [CommSemiring S₀] [Semiring T] [Semiring C]
    [Algebra K T] [Algebra K C] [Algebra S₀ T] [Algebra S₀ C]
    (π : T →ₐ[K] C)
    (hπS : ∀ s : S₀, π (algebraMap S₀ T s) = algebraMap S₀ C s) : T →ₐ[S₀] C :=
  { π.toRingHom with commutes' := hπS }

/-- Helper for Chap10 Lemma 10 152 2: an idempotent is complementary to `1 - e` under addition. -/
private theorem idempotent_add_one_sub {T : Type*} [Ring T] (e : T) : e + (1 - e) = 1 := by
  -- This records the additive half of the standard complementary-idempotent decomposition.
  simp

/-- Helper for Chap10 Lemma 10 152 2: an idempotent annihilates its complement. -/
private theorem idempotent_mul_one_sub {T : Type*} [Ring T] {e : T}
    (he : IsIdempotentElem e) : e * (1 - e) = 0 :=
  he.mul_one_sub_self

/-- Helper for Chap10 Lemma 10 152 2: a surjective map whose target is formally étale over a
base splits its source as the quotient by the kernel times the complementary idempotent quotient. -/
private theorem existsProductSplitQuotientKerOfSurjectiveFormallyEtaleTarget
    {K : Type u} {S₀ : Type v} {T : Type (max u v)} {C : Type v}
    [CommRing K] [CommRing S₀] [CommRing T] [CommRing C]
    [Algebra K T] [Algebra K C] [Algebra S₀ T] [Algebra S₀ C]
    [Algebra.FormallyUnramified S₀ T]
    [Algebra.FinitePresentation S₀ T] [Algebra.FinitePresentation S₀ C]
    [Algebra.FormallyEtale S₀ C]
    (π : T →ₐ[K] C) (hπ : Function.Surjective π)
    (hπS : ∀ s : S₀, π (algebraMap S₀ T s) = algebraMap S₀ C s) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra K B)
      (E : T ≃ₐ[K] (T ⧸ RingHom.ker π.toRingHom) × B),
      ∀ z : T, RingHom.fst (T ⧸ RingHom.ker π.toRingHom) B (E z) =
        Ideal.Quotient.mk (RingHom.ker π.toRingHom) z := by
  let πS : T →ₐ[S₀] C := algHomOfCompatibleBase π hπS
  have hπSsurj : Function.Surjective πS := by
    -- The compatible `S₀`-algebra map has the same underlying function as the original map.
    intro y
    obtain ⟨x, hx⟩ := hπ y
    exact ⟨x, hx⟩
  letI : Algebra T C := π.toAlgebra
  have hTowerEq : algebraMap S₀ C = (algebraMap T C).comp (algebraMap S₀ T) := by
    -- The supplied compatibility is exactly the scalar-tower equation for `π.toAlgebra`.
    ext s
    rw [RingHom.comp_apply]
    rw [RingHom.algebraMap_toAlgebra]
    exact (hπS s).symm
  letI : IsScalarTower S₀ T C := IsScalarTower.of_algebraMap_eq' hTowerEq
  have hπalg : Function.Surjective (algebraMap T C) := by
    -- Under `π.toAlgebra`, the algebra map from `T` to `C` is the original surjection.
    intro y
    obtain ⟨x, hx⟩ := hπ y
    refine ⟨x, ?_⟩
    rw [RingHom.algebraMap_toAlgebra]
    exact hx
  have hIdemKer : IsIdempotentElem (RingHom.ker π.toRingHom) := by
    -- Formal étaleness over `S₀` descends along the formally unramified source map, and a
    -- surjective formally étale algebra map has idempotent kernel.
    have hform : Algebra.FormallyEtale T C := Algebra.FormallyEtale.of_restrictScalars (R := S₀)
    have hIdemAlg : IsIdempotentElem (RingHom.ker (algebraMap T C)) :=
      (Algebra.FormallyEtale.iff_of_surjective hπalg).mp hform
    simpa [RingHom.algebraMap_toAlgebra] using hIdemAlg
  have hfg : (RingHom.ker π.toRingHom).FG := by
    -- Finite presentation over `S₀` gives a finitely generated kernel for the compatible
    -- `S₀`-algebra surjection.
    have hfgS : (RingHom.ker πS.toRingHom).FG :=
      Algebra.FinitePresentation.ker_fG_of_surjective πS hπSsurj
    simpa [πS, algHomOfCompatibleBase] using hfgS
  obtain ⟨e, he, hkerSubmodule⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg _ hfg).mp hIdemKer
  have hker : RingHom.ker π.toRingHom = Ideal.span ({e} : Set T) := by
    -- Put the idempotent-generator statement into quotient-normal form.
    simpa using hkerSubmodule
  let B : Type (max u v) := T ⧸ Ideal.span ({1 - e} : Set T)
  letI : CommRing B := inferInstance
  letI : Algebra K B := inferInstance
  let splitEquiv : T ≃ₐ[K] (T ⧸ Ideal.span ({e} : Set T)) × B :=
    AlgEquiv.prodQuotientOfIsIdempotentElem K he he.one_sub (idempotent_add_one_sub e)
      (idempotent_mul_one_sub he)
  let firstEquiv : (T ⧸ Ideal.span ({e} : Set T)) ≃ₐ[K]
      (T ⧸ RingHom.ker π.toRingHom) :=
    Ideal.quotientEquivAlgOfEq (R₁ := K) hker.symm
  let finalEquiv : T ≃ₐ[K] (T ⧸ RingHom.ker π.toRingHom) × B :=
    splitEquiv.trans (AlgEquiv.prodCongr firstEquiv (AlgEquiv.refl : B ≃ₐ[K] B))
  refine ⟨B, inferInstance, inferInstance, finalEquiv, ?_⟩
  intro z
  -- The first coordinate is the quotient by the idempotent kernel, transported through the
  -- kernel-identifying quotient equivalence.
  calc
    RingHom.fst (T ⧸ RingHom.ker π.toRingHom) B (finalEquiv z) =
        firstEquiv (splitEquiv z).1 := by
      simp only [finalEquiv, AlgEquiv.trans_apply, AlgEquiv.prodCongr_apply]
      rfl
    _ = firstEquiv ((Ideal.Quotient.mk (Ideal.span ({e} : Set T))) z) := by
      exact congrArg firstEquiv (AlgEquiv.prodQuotientOfIsIdempotentElem_apply_fst K he
        he.one_sub (idempotent_add_one_sub e) (idempotent_mul_one_sub he) z)
    _ = Ideal.Quotient.mk (RingHom.ker π.toRingHom) z := by
      exact Ideal.quotientEquivAlgOfEq_mk (R₁ := K) hker.symm z

/- Domain-style sampling:
* primary domain: unramified finite-type algebra maps and the étale-local quasi-finite splitting
  theorem at a chosen prime;
* sampled owner declarations:
  `Algebra.IsUnramifiedAt`,
  `Algebra.QuasiFiniteAt`,
  `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`,
  `Ideal.primesOver`;
* best owner abstraction:
  the core/canonical owner is the mathlib theorem
  `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`, reached here through the canonical
  implication `Algebra.IsUnramifiedAt R q → Algebra.QuasiFiniteAt R q`;
* layer triage:
  this numbered item is `source-facing`: it reformulates the idempotent-based owner theorem as a
  two-factor product decomposition with the distinguished prime singled out on the left factor;
* primitive data:
  the finite-type algebra `R → S`, the ideal `p ⊂ R`, the prime `q ⊂ S` with `q` lying over `p`,
  and the canonical local owner `[Algebra.IsUnramifiedAt R q]`;
* derived API:
  the étale neighborhood `R → R'`, the product decomposition `R' ⊗[R] S ≃ A × B`, the surjective
  map `R' → A`, the prime `p` recovered from `q.under R`, and the prime `p'A` identified with the
  chosen prime over `q`.
-/

-- Proof sketch: unramifiedness at `q` makes the localized map quasi-finite at `q`. Apply the
-- étale local splitting theorem that produces an étale neighborhood together with an idempotent in
-- `R' ⊗[R] S`, then convert that idempotent into a product decomposition `A × B`. The factor
-- singled out by the idempotent is finite over `R'`, which yields surjectivity of `R' → A`, and
-- the distinguished prime above `p'` corresponds to the prime lying over `q`.
/-- Chap10 Lemma 10 152 2: if `q` lies over `p`, `R → S` is of finite type, and `R → S` is unramified at
`q`, then after an étale base change `R → R'` with a prime `p'` over `p`, the tensor product
`R' ⊗[R] S` splits as `A × B` so that `R' → A` is surjective and the extended ideal `p' A` is a
prime of `A` lying over both `p'` and `q`. -/
@[stacks 00UX]
theorem exists_etale_baseChange_prod_of_isUnramifiedAt
    (p : Ideal R) (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra.IsUnramifiedAt R q] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p)
      (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R' A)
      (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R' B)
      (e : R' ⊗[R] S ≃ₐ[R'] A × B),
      let pA : Ideal A := Ideal.map (algebraMap R' A) p'
      let πA : S →+* A :=
        (((RingHom.fst A B).comp e.toRingHom).comp
          (includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom)
      Function.Surjective (algebraMap R' A) ∧
        pA.IsPrime ∧
        pA.LiesOver p' ∧
        Ideal.comap πA pA = q := by
  have hpPrime : p.IsPrime := by
    -- The base prime is recovered from the prime `q` lying over it.
    simpa [q.over_def p] using (inferInstance : (q.under R).IsPrime)
  letI : p.IsPrime := hpPrime
  obtain ⟨f, hfq, P, φ, hφ⟩ :=
    Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn (R := R) q
  let R' : Type u := P.Ring
  letI : CommRing R' := inferInstance
  letI : Algebra R R' := inferInstance
  letI : Algebra.Etale R R' := inferInstance
  let A₀ : Type v := Localization.Away f
  letI : CommRing A₀ := inferInstance
  letI : Algebra R A₀ := inferInstance
  letI : Algebra S A₀ := inferInstance
  letI : IsScalarTower R S A₀ := inferInstance
  letI : Algebra R' A₀ := φ.toAlgebra
  letI : IsScalarTower R R' A₀ := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let T : Type (max u v) := R' ⊗[R] S
  letI : CommRing T := inferInstance
  letI : Algebra R' T := inferInstance
  letI : Algebra S T := Algebra.TensorProduct.rightAlgebra
  have hcommScalars :
      ∀ s : S,
        (Algebra.TensorProduct.comm R S R').toRingEquiv (algebraMap S (S ⊗[R] R') s) =
          algebraMap S T s := by
    -- The tensor commutativity equivalence is an `S`-algebra equivalence when the target uses
    -- the right tensor-factor algebra structure.
    intro s
    rw [Algebra.TensorProduct.algebraMap_eq_includeRight]
    rfl
  let commST : S ⊗[R] R' ≃ₐ[S] T :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R S R').toRingEquiv) hcommScalars
  have hEtaleT : Algebra.Etale S T := Algebra.Etale.of_equiv commST
  letI : Algebra.Etale S T := hEtaleT
  let μ : T →ₐ[R'] A₀ :=
    Algebra.TensorProduct.lift (Algebra.ofId R' A₀) (IsScalarTower.toAlgHom R S A₀)
      (fun _ _ => .all _ _)
  have hμ_left (x : R') : μ ((includeLeft : R' →ₐ[R'] T) x) = φ x := by
    -- On the left tensor factor, the induced map is exactly the standard-étale presentation map.
    calc
      μ ((includeLeft : R' →ₐ[R'] T) x) = algebraMap R' A₀ x := by
        exact DFunLike.congr_fun (Algebra.TensorProduct.lift_comp_includeLeft
          (Algebra.ofId R' A₀) (IsScalarTower.toAlgHom R S A₀) (fun _ _ => .all _ _)) x
      _ = φ x := by
        rw [RingHom.algebraMap_toAlgebra]
        rfl
  have hμ_right (x : S) : μ ((includeRight : S →ₐ[R] T) x) = algebraMap S A₀ x := by
    -- On the right tensor factor, the induced map is the localization map from `S`.
    exact DFunLike.congr_fun (Algebra.TensorProduct.lift_comp_includeRight
      (Algebra.ofId R' A₀) (IsScalarTower.toAlgHom R S A₀) (fun _ _ => .all _ _)) x
  have hμ_surj : Function.Surjective μ := by
    -- Surjectivity comes from the standard-étale presentation map on the left factor.
    intro y
    obtain ⟨x, hx⟩ := hφ y
    refine ⟨(includeLeft : R' →ₐ[R'] T) x, ?_⟩
    rw [hμ_left, hx]
  have hμS : ∀ s : S, μ (algebraMap S T s) = algebraMap S A₀ s := by
    -- This is the compatibility needed to reuse the same underlying map as an `S`-algebra map.
    intro s
    rw [Algebra.TensorProduct.algebraMap_eq_includeRight]
    exact hμ_right s
  have hEtaleA₀ : Algebra.Etale S A₀ := Algebra.Etale.of_isLocalizationAway f
  letI : Algebra.Etale S A₀ := hEtaleA₀
  obtain ⟨B, _, _, e, hfst⟩ :=
    existsProductSplitQuotientKerOfSurjectiveFormallyEtaleTarget
      (K := R') (S₀ := S) (T := T) (C := A₀) μ hμ_surj hμS
  let A : Type (max u v) := T ⧸ RingHom.ker μ.toRingHom
  letI : CommRing A := inferInstance
  letI : Algebra R' A := inferInstance
  let κ : T →ₐ[R'] A := Ideal.Quotient.mkₐ R' (RingHom.ker μ.toRingHom)
  let Eker : A ≃ₐ[R'] A₀ := Ideal.quotientKerAlgEquivOfSurjective hμ_surj
  have hEker_mk (z : T) : Eker (κ z) = μ z := by
    -- The first-isomorphism equivalence identifies the quotient class with its image under `μ`.
    exact Ideal.quotientKerAlgEquivOfSurjective_mk hμ_surj z
  have hEker_algebra (x : R') : Eker (algebraMap R' A x) = φ x := by
    -- The algebra map into the quotient is the class of the left tensor inclusion.
    calc
      Eker (algebraMap R' A x) = Eker (κ ((includeLeft : R' →ₐ[R'] T) x)) := by
        rfl
      _ = μ ((includeLeft : R' →ₐ[R'] T) x) := hEker_mk ((includeLeft : R' →ₐ[R'] T) x)
      _ = φ x := hμ_left x
  have hA_surj : Function.Surjective (algebraMap R' A) := by
    -- Transport surjectivity of `φ` back through the quotient-kernel equivalence.
    intro y
    obtain ⟨x, hx⟩ := hφ (Eker y)
    refine ⟨x, ?_⟩
    apply Eker.injective
    rw [hEker_algebra, hx]
  let qf : Ideal A₀ := Ideal.map (algebraMap S A₀) q
  have hdisj : Disjoint (Submonoid.powers f : Set S) ↑q := by
    -- The chosen localization element avoids `q`, so powers of it are disjoint from `q`.
    rw [Ideal.disjoint_powers_iff_notMem _ (Ideal.IsPrime.isRadical inferInstance)]
    exact hfq
  have hqfPrime : qf.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers f) A₀ q inferInstance hdisj
  have hqfComap : Ideal.comap (algebraMap S A₀) qf = q :=
    IsLocalization.comap_map_of_isPrime_disjoint (.powers f) A₀ inferInstance hdisj
  let qA : Ideal A := Ideal.comap Eker.toRingHom qf
  have hqAPrime : qA.IsPrime := by
    -- Pulling a prime back through an equivalence preserves primality.
    exact Ideal.comap_isPrime Eker.toRingHom qf
  let p' : Ideal R' := Ideal.comap (algebraMap R' A) qA
  have hp'Prime : p'.IsPrime := by
    -- The prime on `R'` is the inverse image of the transported localized prime.
    exact Ideal.comap_isPrime (algebraMap R' A) qA
  have hp'Lies : p'.LiesOver p := by
    -- Its contraction to `R` is `p`, because the localized prime contracts to `q`.
    refine ⟨?_⟩
    symm
    ext r
    change (algebraMap R' A ((algebraMap R R') r) ∈ qA) ↔ r ∈ p
    calc
      (algebraMap R' A) ((algebraMap R R') r) ∈ qA ↔
          Eker ((algebraMap R' A) ((algebraMap R R') r)) ∈ qf := Iff.rfl
      _ ↔ φ ((algebraMap R R') r) ∈ qf := by
        rw [hEker_algebra]
      _ ↔ algebraMap R A₀ r ∈ qf := by
        rw [φ.commutes]
      _ ↔ algebraMap R S r ∈ q := by
        have hrmem :
            algebraMap R A₀ r ∈ qf ↔ algebraMap R S r ∈ q := by
          simpa [Ideal.mem_comap, IsScalarTower.algebraMap_apply R S A₀] using
            (show algebraMap R S r ∈ Ideal.comap (algebraMap S A₀) qf ↔
                algebraMap R S r ∈ q by rw [hqfComap])
        exact hrmem
      _ ↔ r ∈ p := by
        simpa [Ideal.mem_comap] using
          (show r ∈ Ideal.comap (algebraMap R S) q ↔ r ∈ p by rw [q.over_def p])
  have hmap_p' : Ideal.map (algebraMap R' A) p' = qA := by
    -- Since `R' → A` is surjective, mapping the contraction of `qA` recovers `qA`.
    exact Ideal.map_comap_of_surjective (algebraMap R' A) hA_surj qA
  have hpAPrime : (Ideal.map (algebraMap R' A) p').IsPrime := by
    rw [hmap_p']
    exact hqAPrime
  have hpALies : (Ideal.map (algebraMap R' A) p').LiesOver p' := by
    refine ⟨?_⟩
    rw [hmap_p']
  have hfinalComap :
      Ideal.comap
          (((RingHom.fst A B).comp e.toRingHom).comp
            (includeRight : S →ₐ[R] T).toRingHom)
          (Ideal.map (algebraMap R' A) p') = q := by
    -- The first projection of the product split is the quotient map, so contraction along the
    -- displayed map is contraction of the localized prime along `S → S_f`.
    rw [hmap_p']
    ext s
    calc
      (((RingHom.fst A B).comp e.toRingHom).comp
            (includeRight : S →ₐ[R] T).toRingHom) s ∈ qA ↔
          Eker ((((RingHom.fst A B).comp e.toRingHom).comp
            (includeRight : S →ₐ[R] T).toRingHom) s) ∈ qf := Iff.rfl
      _ ↔ Eker (κ ((includeRight : S →ₐ[R] T) s)) ∈ qf := by
        change Eker (RingHom.fst A B (e ((includeRight : S →ₐ[R] T) s))) ∈ qf ↔
          Eker (κ ((includeRight : S →ₐ[R] T) s)) ∈ qf
        rw [hfst]
        rfl
      _ ↔ algebraMap S A₀ s ∈ qf := by
        rw [hEker_mk, hμ_right]
      _ ↔ s ∈ q := by
        simpa [Ideal.mem_comap] using
          (show s ∈ Ideal.comap (algebraMap S A₀) qf ↔ s ∈ q by rw [hqfComap])
  -- Assemble the existential data in the target's order.
  refine ⟨R', inferInstance, inferInstance, inferInstance, p', hp'Prime, hp'Lies,
    A, inferInstance, inferInstance, B, inferInstance, inferInstance, e, ?_⟩
  exact ⟨hA_surj, hpAPrime, hpALies, hfinalComap⟩

end
