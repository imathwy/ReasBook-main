import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_159_3 (from Chap10) -/
universe u v u1 v1 u2 v2

section

variable {R : Type u} [CommRing R]

/- Domain-style sampling:
* primary domain: commutative algebra of prime ideals under scalar extension and the induced
  residue-field extension;
* layer triage:
  - `source-facing`: the existence statement for a finite free `R`-algebra realizing a prescribed
    finite extension of `κ(p)` at the extended prime `pS`;
  - `core/canonical`: `Ideal.LiesOver`, `Ideal.ResidueField`, and `Ideal.ResidueField.mapₐ`,
    which are the owner abstractions for the prime-over-prime relation and the `κ(p)`-algebra
    structure on residue fields;
  - `bridge/view`: `Polynomial.Monic.free_adjoinRoot` and `Polynomial.Monic.finite_adjoinRoot`
    for the monic-quotient model used in the proof, and
    `exists_etale_liesOver_with_residueField_equiv` as the separable special case.
* owner decision: the theorem remains source-facing, but the public output should stop at the
  canonical data carried by the owner abstractions.
* primitive data: the finite free `R`-algebra `S`; the extended ideal itself is the canonical
  owner `q := p.map (algebraMap R S)`, so it should not be repackaged as extra primitive data.
* derived API: after fixing the owner instances `q.IsPrime` and `q.LiesOver p`, the only further
  public output is the residue-field `AlgEquiv`; its compatibility with the `κ(p)`-algebra
  structures is already part of the owner API and should not be duplicated by an extra equality.
-/

-- Proof sketch: choose a primitive element of the finite extension `L / κ(p)`, clear
-- denominators in its minimal polynomial over `κ(p)`, and form the monic quotient
-- `S = R[X] / (f)`. The image of `p` in `S` is prime because the reduction of `f` is the
-- minimal polynomial over `κ(p)`, and the residue field of that prime identifies with `L`
-- through the canonical `κ(p)`-algebra equivalence.
/-- Helper for Lemma 10.159.3: a proper intermediate field in a finite extension has strictly
smaller degree both over the base field and up to the ambient field. -/
lemma finrank_lt_of_proper_intermediate
    {k L : Type*} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L]
    (K : IntermediateField k L) (hK_bot : K ≠ ⊥) (hK_top : K ≠ ⊤) :
    Module.finrank k K < Module.finrank k L ∧ Module.finrank K L < Module.finrank k L := by
  -- The degree over the base field cannot stay constant unless `K = ⊤`.
  have hleft_le : Module.finrank k K ≤ Module.finrank k L := by
    simpa [IntermediateField.finrank_top'] using
      (IntermediateField.finrank_le_of_le_right
        (K := k) (L := L) (F := K) (E := (⊤ : IntermediateField k L)) le_top)
  have hleft_ne : Module.finrank k K ≠ Module.finrank k L := by
    intro hEq
    have hEq' : Module.finrank k K = Module.finrank k (⊤ : IntermediateField k L) := by
      simpa [IntermediateField.finrank_top'] using hEq
    exact hK_top <|
      IntermediateField.eq_of_le_of_finrank_eq
        (K := k) (L := L) (F := K) (E := (⊤ : IntermediateField k L)) le_top hEq'
  have hleft : Module.finrank k K < Module.finrank k L := lt_of_le_of_ne hleft_le hleft_ne
  -- The tower degree drops because `K` sits strictly above the bottom field.
  have hbot_lt : (⊥ : IntermediateField k L) < K := by
    refine lt_iff_le_and_ne.mpr ⟨bot_le, ?_⟩
    simpa [eq_comm] using hK_bot
  have hright : Module.finrank K L < Module.finrank k L := by
    simpa [IntermediateField.finrank_bot'] using
      (IntermediateField.finrank_lt_of_gt
        (K := k) (L := L) (F := (⊥ : IntermediateField k L)) (E := K) hbot_lt)
  exact ⟨hleft, hright⟩

/-- Helper for Lemma 10.159.3: a finite field extension of degree `1` is canonically the base
field. -/
noncomputable def algEquiv_of_finrank_eq_one
    {k L : Type*} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L]
    (hfinrank : Module.finrank k L = 1) :
    k ≃ₐ[k] L :=
  let hbot_top : (⊥ : IntermediateField k L) = ⊤ :=
    IntermediateField.bot_eq_top_iff_finrank_eq_one.mpr hfinrank
  -- The bottom field is the base field, and the top field is the ambient extension.
  (IntermediateField.botEquiv k L).symm.trans
    ((IntermediateField.equivOfEq hbot_top).trans IntermediateField.topEquiv)

/-- Helper for Lemma 10.159.3: a monic polynomial over `R ⧸ p` lifts to a monic polynomial over
`R`. -/
lemma exists_monic_lift_of_quotient_polynomial
    (p : Ideal R) (fbar : Polynomial (R ⧸ p)) (hfbar : fbar.Monic) :
    ∃ f : Polynomial R, f.map (Ideal.Quotient.mk p) = fbar ∧ f.Monic := by
  -- Lift each coefficient along the quotient map and then invoke the monic lifting API.
  have hlifts : fbar ∈ Polynomial.lifts (Ideal.Quotient.mk p) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact Ideal.Quotient.mk_surjective (fbar.coeff n)
  obtain ⟨f, hfmap, _, hfmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hfbar
  exact ⟨f, hfmap, hfmonic⟩

/-- Helper for Lemma 10.159.3: quotienting `AdjoinRoot f` by the extended ideal from `R` rewrites
to the reduced polynomial quotient over `R ⧸ p`. -/
noncomputable abbrev adjoinRoot_quotient_equiv_quotient_map
    (p : Ideal R) (f : Polynomial R) :
    (AdjoinRoot f ⧸ Ideal.map (algebraMap R (AdjoinRoot f)) p) ≃ₐ[R]
      Polynomial (R ⧸ p) ⧸
        Ideal.span ({Polynomial.map (Ideal.Quotient.mk p) f} : Set (Polynomial (R ⧸ p))) :=
  AdjoinRoot.quotEquivQuotMap f p

/-- Helper for Lemma 10.159.3: after identifying the reduced polynomial, the quotient of
`AdjoinRoot f` by the extended ideal from `p` is exactly `AdjoinRoot fbar`. -/
noncomputable abbrev adjoinRoot_lift_quotient_equiv_adjoinRoot_quotient
    (p : Ideal R) (f : Polynomial R) (fbar : Polynomial (R ⧸ p))
    (hmap : f.map (Ideal.Quotient.mk p) = fbar) :
    (AdjoinRoot f ⧸ Ideal.map (algebraMap R (AdjoinRoot f)) p) ≃ₐ[R] AdjoinRoot fbar := by
  -- First rewrite to the reduced polynomial quotient, then substitute the identified polynomial.
  exact
    (adjoinRoot_quotient_equiv_quotient_map (R := R) (p := p) f).trans
      (AdjoinRoot.algEquivOfEq (R := R)
        (Polynomial.map (Ideal.Quotient.mk p) f) fbar hmap)

/-- Helper for Lemma 10.159.3: adjoining a root of a monic polynomial produces a finite free
`R`-algebra. -/
lemma adjoinRoot_free_and_finite_of_monic
    (f : Polynomial R) (hf : f.Monic) :
    Module.Free R (AdjoinRoot f) ∧ Module.Finite R (AdjoinRoot f) := by
  -- Mathlib already packages the finite free structure on monic adjoin-root algebras.
  exact ⟨hf.free_adjoinRoot, hf.finite_adjoinRoot⟩

/-- Helper for Lemma 10.159.3: realizations compose along a prime-over-prime tower, and the
second residue-field equivalence can be restricted back to the original residue field. -/
lemma compose_realizations_over_intermediate_field
    {S₁ : Type v} [CommRing S₁] [Algebra R S₁] [Module.Free R S₁] [Module.Finite R S₁]
    (p : Ideal R) [p.IsPrime]
    (q₁ : Ideal S₁) [q₁.IsPrime] [q₁.LiesOver p]
    (hq₁ : q₁ = Ideal.map (algebraMap R S₁) p)
    {S₂ : Type*} [CommRing S₂] [Algebra S₁ S₂] [Module.Free S₁ S₂] [Module.Finite S₁ S₂]
    [Algebra R S₂] [IsScalarTower R S₁ S₂]
    (q₂ : Ideal S₂) [q₂.IsPrime] [q₂.LiesOver q₁]
    (hq₂ : q₂ = Ideal.map (algebraMap S₁ S₂) q₁)
    {L : Type*} [Field L] [Algebra q₁.ResidueField L] [Algebra p.ResidueField L]
    [IsScalarTower p.ResidueField q₁.ResidueField L]
    (_e₂ : q₂.ResidueField ≃ₐ[q₁.ResidueField] L) :
    Module.Free R S₂ ∧ Module.Finite R S₂ ∧
      q₂ = Ideal.map (algebraMap R S₂) p ∧ q₂.LiesOver p := by
  -- The finite free hypotheses compose directly along the algebra tower.
  have hfree : Module.Free R S₂ := Module.Free.trans (R := R) (S := S₁) (M := S₂)
  have hfinite : Module.Finite R S₂ := Module.Finite.trans (R := R) S₁ S₂
  letI : q₂.LiesOver p := Ideal.LiesOver.trans q₂ q₁ p
  have hq : q₂ = Ideal.map (algebraMap R S₂) p := by
    -- The distinguished prime is the iterated extension of `p`, so `Ideal.map_map` closes the
    -- bookkeeping step.
    calc
      q₂ = Ideal.map (algebraMap S₁ S₂) q₁ := hq₂
      _ = Ideal.map (algebraMap S₁ S₂) (Ideal.map (algebraMap R S₁) p) := by rw [hq₁]
      _ = Ideal.map (algebraMap R S₂) p := by
        rw [Ideal.map_map, IsScalarTower.algebraMap_eq R S₁ S₂]
  -- The residue-field comparison itself is deferred to the main induction step, where the
  -- compatible `κ(p)`-algebra structure on the target field has already been fixed.
  exact ⟨hfree, hfinite, hq, inferInstance⟩

/-- Helper for Lemma 10.159.3: if there is no proper intermediate field, then any element outside
the base field generates the whole extension. -/
lemma adjoin_eq_top_of_no_proper_intermediate
    {k L : Type*} [Field k] [Field L] [Algebra k L]
    (hproper : ∀ K : IntermediateField k L, K ≠ ⊥ → K ≠ ⊤ → False)
    {β : L} (hβ : β ∉ (⊥ : IntermediateField k L)) :
    IntermediateField.adjoin k ({β} : Set L) = (⊤ : IntermediateField k L) := by
  -- If the simple extension were not all of `L`, it would be a forbidden proper intermediate
  -- field; if it were bottom, then `β` would already lie in the base field.
  let K : IntermediateField k L := IntermediateField.adjoin k ({β} : Set L)
  by_contra htop
  have hbot : K ≠ (⊥ : IntermediateField k L) := by
    intro hbot
    have hβK : β ∈ K := by
      simpa [K] using IntermediateField.subset_adjoin k ({β} : Set L) (by simp)
    exact hβ <| by simpa [K, hbot] using hβK
  simpa [K] using hproper K hbot htop

/-- Helper for Lemma 10.159.3: in the nontrivial no-proper-intermediate branch, a single element
already generates the entire finite extension. -/
lemma exists_generator_of_no_proper_intermediate_of_finrank_ne_one
    {k L : Type*} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L]
    (hfinrank : Module.finrank k L ≠ 1)
    (hproper : ∀ K : IntermediateField k L, K ≠ ⊥ → K ≠ ⊤ → False) :
    ∃ β : L, IntermediateField.adjoin k ({β} : Set L) = (⊤ : IntermediateField k L) := by
  -- A nontrivial finite extension has some element outside the base field.
  have hbot_ne_top : (⊥ : IntermediateField k L) ≠ ⊤ := by
    intro hbot_top
    exact hfinrank <|
      (IntermediateField.bot_eq_top_iff_finrank_eq_one (F := k) (E := L)).mp hbot_top
  have hlt : (⊥ : IntermediateField k L) < ⊤ := lt_of_le_of_ne bot_le hbot_ne_top
  obtain ⟨β, _, hβ_not_bot⟩ := SetLike.exists_of_lt hlt
  -- In the no-proper-intermediate branch, any such element must generate the whole field.
  exact ⟨β, adjoin_eq_top_of_no_proper_intermediate (k := k) (L := L) hproper hβ_not_bot⟩

/-- Helper for Lemma 10.159.3: if `q` lies over `p` and `R → S` is surjective on stalks, then the
canonical map `κ(p) → κ(q)` is bijective. -/
lemma bijective_algebraMap_residueField_of_surjectiveOnStalks
    {S : Type v} [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hsurj : (algebraMap R S).SurjectiveOnStalks) :
    Function.Bijective (algebraMap p.ResidueField q.ResidueField) := by
  -- The canonical `κ(p)`-algebra map agrees with the owner residue-field map attached to `q/p`.
  have hmap :
      Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p) =
        algebraMap p.ResidueField q.ResidueField := by
    apply Ideal.ResidueField.ringHom_ext (I := p)
    ext r
    simp only [RingHom.comp_apply]
    rw [Ideal.ResidueField.map_algebraMap]
    calc
      (algebraMap S q.ResidueField) ((algebraMap R S) r) = algebraMap R q.ResidueField r := by
        rw [IsScalarTower.algebraMap_apply R S q.ResidueField r]
      _ = (algebraMap p.ResidueField q.ResidueField) ((algebraMap R p.ResidueField) r) := by
        rw [IsScalarTower.algebraMap_apply R p.ResidueField q.ResidueField r]
  -- Surjective-on-stalks then upgrades that owner map to a bijection.
  simpa [hmap] using hsurj.residueFieldMap_bijective p q (Ideal.over_def q p)

/-- Helper for Lemma 10.159.3: a bijective algebra map identifies residue fields over the source
residue field. -/
noncomputable def residueFieldAlgEquivOfBijectiveAlgebraMap
    {S : Type v} [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hbij : Function.Bijective (algebraMap R S)) :
    q.ResidueField ≃ₐ[p.ResidueField] p.ResidueField :=
  -- The source-faithful degree-one branch only needs transport across an isomorphic realization.
  (AlgEquiv.ofBijective (Algebra.ofId p.ResidueField q.ResidueField)
      (bijective_algebraMap_residueField_of_surjectiveOnStalks
        (R := R) (S := S) (p := p) (q := q)
        (RingHom.surjectiveOnStalks_of_surjective hbij.surjective))).symm

/-- Helper for Lemma 10.159.3: an algebra equivalence over the base field transports the target
field extension and preserves its degree. -/
lemma transport_algebra_and_finrank_across_residueField_equiv
    {k k' K L : Type*} [Field k] [Field k'] [Field K] [Field L]
    [Algebra k k'] [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    [FiniteDimensional K L] (e : k' ≃ₐ[k] K) :
    ∃ (_ : Algebra k' L) (_ : IsScalarTower k k' L) (_ : FiniteDimensional k' L),
      Module.finrank k' L = Module.finrank K L := by
  -- Install the transported `k'`-algebra structure on `L` by composing `e` with `K → L`.
  letI : Algebra k' K := e.toRingHom.toAlgebra
  letI : Algebra k' L := RingHom.toAlgebra ((algebraMap K L).comp e.toRingHom)
  letI : IsScalarTower k' K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower k k' L := by
    -- The transported action still agrees with the original `k`-algebra structure via `e`.
    refine IsScalarTower.of_algebraMap_eq' ?_
    apply RingHom.ext
    intro x
    rw [RingHom.comp_apply]
    rw [show algebraMap k' L (algebraMap k k' x) =
        algebraMap K L (e (algebraMap k k' x)) by rfl]
    rw [e.commutes x, IsScalarTower.algebraMap_apply k K L x]
  let e_self : k' ≃ₐ[k'] K :=
    { toRingEquiv := e.toRingEquiv
      commutes' := fun x => rfl }
  letI : FiniteDimensional k' K := e_self.toLinearEquiv.finiteDimensional
  letI : Module.Finite k' L := Module.Finite.trans (R := k') K L
  letI : FiniteDimensional k' L := inferInstance
  -- After transport, the new `k'`-structure on `L` is definitionally the one induced by `e`.
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  exact Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl L) rfl

/-- Helper for Lemma 10.159.3: the degree-`1` branch of the source induction is realized by the
identity algebra `R → R`. -/
lemma exists_finiteFree_with_prime_extendedIdeal_and_residueField_equiv_of_finrank_eq_one
    (p : Ideal R) [p.IsPrime] (L : Type v) [Field L] [Algebra p.ResidueField L]
    [FiniteDimensional p.ResidueField L]
    (hfinrank : Module.finrank p.ResidueField L = 1) :
    ∃ (S : Type (max u v)) (_ : CommRing S) (_ : Algebra R S) (_ : Module.Free R S)
      (_ : Module.Finite R S),
      let q : Ideal S := p.map (algebraMap R S)
      ∃ (_ : q.IsPrime) (_ : q.LiesOver p), Nonempty (q.ResidueField ≃ₐ[p.ResidueField] L) := by
  let e : p.ResidueField ≃ₐ[p.ResidueField] L :=
    algEquiv_of_finrank_eq_one (k := p.ResidueField) (L := L) hfinrank
  let eR : R ≃ₐ[R] ULift.{v} R := (ULift.algEquiv (R := R) (A := R)).symm
  refine ⟨ULift.{v} R, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  -- In the degree-`1` case the source proof takes `S = R`; we use `ULift R` only to match the
  -- universe demanded by the statement, and transport the canonical prime along that equivalence.
  dsimp
  let q : Ideal (ULift.{v} R) := p.map (algebraMap R (ULift.{v} R))
  change ∃ (_ : q.IsPrime) (_ : q.LiesOver p), Nonempty (q.ResidueField ≃ₐ[p.ResidueField] L)
  letI : p.LiesOver p := by
    simpa using (show p.LiesOver (p.under R) from inferInstance)
  have hqprime : q.IsPrime := by
    -- The extended ideal along the identity equivalence is still prime.
    simpa [q] using (Ideal.map_isPrime_of_equiv (eR : R ≃+* ULift.{v} R))
  have hqlies : q.LiesOver p := by
    -- The mapped prime lies over the original prime by the canonical equivariance lemma.
    simpa [q] using (Ideal.map_equiv_liesOver (A := R) (P := p) (p := p) eR)
  refine ⟨hqprime, hqlies, ?_⟩
  letI : q.IsPrime := hqprime
  letI : q.LiesOver p := hqlies
  -- The induced `κ(q)` is canonically `κ(p)`, so we compose that identification with `e`.
  refine ⟨(residueFieldAlgEquivOfBijectiveAlgebraMap
    (R := R) (S := ULift.{v} R) (p := p) (q := q) (AlgEquiv.bijective eR)).trans e⟩

/-- Helper for Lemma 10.159.3: a Nat-strong-induction driver for the source-faithful degree
induction on `L / κ(p)`. -/
theorem exists_finiteFree_with_prime_extendedIdeal_and_residueField_equiv_strong_induction
    (n : ℕ) :
    ∀ {A : Type (max u2 v2)} [CommRing A]
      (p : Ideal A) [p.IsPrime] (L : Type v2) [Field L] [Algebra p.ResidueField L]
      [FiniteDimensional p.ResidueField L],
      Module.finrank p.ResidueField L < n →
      ∃ (S : Type (max u2 v2)) (_ : CommRing S) (_ : Algebra A S) (_ : Module.Free A S)
        (_ : Module.Finite A S),
        let q : Ideal S := p.map (algebraMap A S)
        ∃ (_ : q.IsPrime) (_ : q.LiesOver p), Nonempty (q.ResidueField ≃ₐ[p.ResidueField] L) := by
  refine Nat.strong_induction_on (p := fun n =>
      ∀ {A : Type (max u2 v2)} [CommRing A]
        (p : Ideal A) [p.IsPrime] (L : Type v2) [Field L] [Algebra p.ResidueField L]
        [FiniteDimensional p.ResidueField L],
        Module.finrank p.ResidueField L < n →
        ∃ (S : Type (max u2 v2)) (_ : CommRing S) (_ : Algebra A S) (_ : Module.Free A S)
          (_ : Module.Finite A S),
          let q : Ideal S := p.map (algebraMap A S)
          ∃ (_ : q.IsPrime) (_ : q.LiesOver p),
            Nonempty (q.ResidueField ≃ₐ[p.ResidueField] L)) n ?_
  intro n ih A _ p _ L _ _ _ hdeg
  classical
  -- Route correction: recurse through the strong-induction hypothesis at the ambient degree,
  -- so both the original base ring and the intermediate realization can reuse the same driver.
  by_cases hfinrank : Module.finrank p.ResidueField L = 1
  · -- The degree-`1` branch is still the identity realization from the source proof.
    exact exists_finiteFree_with_prime_extendedIdeal_and_residueField_equiv_of_finrank_eq_one
      (R := A) (p := p) (L := L) hfinrank
  by_cases hproper :
      ∃ K : IntermediateField p.ResidueField L, K ≠ ⊥ ∧ K ≠ ⊤
  · obtain ⟨K, hK_bot, hK_top⟩ := hproper
    have hlt :
        Module.finrank p.ResidueField K < Module.finrank p.ResidueField L ∧
          Module.finrank K L < Module.finrank p.ResidueField L :=
      finrank_lt_of_proper_intermediate
        (k := p.ResidueField) (L := L) K hK_bot hK_top
    have ihL :
        ∀ {B : Type (max u2 v2)} [CommRing B]
          (q : Ideal B) [q.IsPrime] (M : Type v2) [Field M] [Algebra q.ResidueField M]
          [FiniteDimensional q.ResidueField M],
          Module.finrank q.ResidueField M < Module.finrank p.ResidueField L →
          ∃ (T : Type (max u2 v2)) (_ : CommRing T) (_ : Algebra B T) (_ : Module.Free B T)
            (_ : Module.Finite B T),
            let r : Ideal T := q.map (algebraMap B T)
            ∃ (_ : r.IsPrime) (_ : r.LiesOver q), Nonempty (r.ResidueField ≃ₐ[q.ResidueField] M) :=
      ih (Module.finrank p.ResidueField L) hdeg
    -- First realize the proper intermediate field over the original base ring.
    obtain ⟨S₁, hCommRing₁, hAlg₁, hFree₁, hFinite₁, hS₁⟩ :=
      ihL (B := A) (q := p) (M := K) hlt.1
    letI : CommRing S₁ := hCommRing₁
    letI : Algebra A S₁ := hAlg₁
    letI : Module.Free A S₁ := hFree₁
    letI : Module.Finite A S₁ := hFinite₁
    let q₁ : Ideal S₁ := p.map (algebraMap A S₁)
    have hS₁' :
        ∃ (_ : q₁.IsPrime) (_ : q₁.LiesOver p), Nonempty (q₁.ResidueField ≃ₐ[p.ResidueField] K) := by
      simpa [q₁] using hS₁
    obtain ⟨hq₁prime, hqlies₁, ⟨e₁⟩⟩ := hS₁'
    letI : q₁.IsPrime := hq₁prime
    letI : q₁.LiesOver p := hqlies₁
    -- Then transport the residual extension structure from `K` to `q₁.ResidueField`.
    obtain ⟨_, _, _, htransport_finrank⟩ :=
      transport_algebra_and_finrank_across_residueField_equiv
        (k := p.ResidueField) (k' := q₁.ResidueField) (K := K) (L := L) e₁
    have hlt₂ :
        Module.finrank q₁.ResidueField L < Module.finrank p.ResidueField L := by
      simpa [htransport_finrank] using hlt.2
    -- TODO: invoke the same strong-induction hypothesis over `(S₁, q₁)` using `hlt₂`, then add
    -- the composed `A`-algebra structure on the second realization and close with
    -- `compose_realizations_over_intermediate_field`.
    let _ := hlt₂
    sorry
  · have hnoProper :
        ∀ K : IntermediateField p.ResidueField L, K ≠ ⊥ → K ≠ ⊤ → False := by
      intro K hK_bot hK_top
      exact hproper ⟨K, hK_bot, hK_top⟩
    obtain ⟨β, hβ_top⟩ :=
      exists_generator_of_no_proper_intermediate_of_finrank_ne_one
        (k := p.ResidueField) (L := L) hfinrank hnoProper
    -- TODO: keep the source route. Starting from `β` with `κ(p)⟮β⟯ = ⊤`, clear denominators in
    -- its minimal polynomial over `A := R ⧸ p`, replace `β` by a scaled generator whose monic
    -- annihilator descends to `A`, lift that polynomial back to `R`, and finish via
    -- `adjoinRoot_lift_quotient_equiv_adjoinRoot_quotient`.
    let _ := β
    let _ := hβ_top
    sorry

/-- Helper for Lemma 10.159.3: a universe-polymorphic induction package for the source-faithful
degree induction on `L / κ(p)`. -/
theorem exists_finiteFree_with_prime_extendedIdeal_and_residueField_equiv_aux
    {A : Type u1} [CommRing A]
    (p : Ideal A) [p.IsPrime] (L : Type v1) [Field L] [Algebra p.ResidueField L]
    [FiniteDimensional p.ResidueField L] :
    ∃ (S : Type (max u1 v1)) (_ : CommRing S) (_ : Algebra A S) (_ : Module.Free A S)
      (_ : Module.Finite A S),
      let q : Ideal S := p.map (algebraMap A S)
      ∃ (_ : q.IsPrime) (_ : q.LiesOver p), Nonempty (q.ResidueField ≃ₐ[p.ResidueField] L) := by
  classical
  -- Route correction: the recursion now lives in a universe-polymorphic auxiliary theorem so the
  -- proper-intermediate branch can recurse again after changing the base ring.
  by_cases hfinrank : Module.finrank p.ResidueField L = 1
  · -- The base case still follows the textbook proof verbatim: take the identity realization.
    exact exists_finiteFree_with_prime_extendedIdeal_and_residueField_equiv_of_finrank_eq_one
      (R := A) (p := p) (L := L) hfinrank
  by_cases hproper :
      ∃ K : IntermediateField p.ResidueField L, K ≠ ⊥ ∧ K ≠ ⊤
  · obtain ⟨K, hK_bot, hK_top⟩ := hproper
    have hlt :
        Module.finrank p.ResidueField K < Module.finrank p.ResidueField L ∧
          Module.finrank K L < Module.finrank p.ResidueField L :=
      finrank_lt_of_proper_intermediate
        (k := p.ResidueField) (L := L) K hK_bot hK_top
    -- The first induction step realizes the proper intermediate field over the original base.
    obtain ⟨S₁, _, _, _, _, hS₁⟩ :=
      exists_finiteFree_with_prime_extendedIdeal_and_residueField_equiv_aux
        (A := A) (p := p) (L := K)
    let q₁ : Ideal S₁ := p.map (algebraMap A S₁)
    have hS₁' :
        ∃ (_ : q₁.IsPrime) (_ : q₁.LiesOver p), Nonempty (q₁.ResidueField ≃ₐ[p.ResidueField] K) := by
      simpa [q₁] using hS₁
    obtain ⟨hq₁prime, hqlies, ⟨e₁⟩⟩ := hS₁'
    letI : q₁.IsPrime := hq₁prime
    letI : q₁.LiesOver p := hqlies
    have htransport :
        ∃ (_ : Algebra q₁.ResidueField L) (_ : IsScalarTower p.ResidueField q₁.ResidueField L)
          (_ : FiniteDimensional q₁.ResidueField L),
          Module.finrank q₁.ResidueField L = Module.finrank K L := by
      -- This is the transport package needed before the second recursive call.
      simpa using
        transport_algebra_and_finrank_across_residueField_equiv
          (k := p.ResidueField) (k' := q₁.ResidueField) (K := K) (L := L) e₁
    -- TODO: use `htransport` to run the second recursive call over `(S₁, q₁)` through a
    -- universe-polymorphic induction principle, then compose the two realizations with
    -- `compose_realizations_over_intermediate_field`.
    let _ := htransport
    sorry
  · have hnoProper :
        ∀ K : IntermediateField p.ResidueField L, K ≠ ⊥ → K ≠ ⊤ → False := by
      intro K hK_bot hK_top
      exact hproper ⟨K, hK_bot, hK_top⟩
    obtain ⟨β, hβ_top⟩ :=
      exists_generator_of_no_proper_intermediate_of_finrank_ne_one
        (k := p.ResidueField) (L := L) hfinrank hnoProper
    -- TODO: keep the source route. Starting from `β` with `κ(p)⟮β⟯ = ⊤`, clear denominators in
    -- its minimal polynomial over `A := R ⧸ p`, replace `β` by a scaled generator whose minimal
    -- polynomial descends to `A`, lift that monic polynomial back to `R`, and finish via
    -- `adjoinRoot_lift_quotient_equiv_adjoinRoot_quotient`.
    let _ := β
    let _ := hβ_top
    sorry
termination_by Module.finrank p.ResidueField L
decreasing_by
  simpa using hlt.1

/-- Lemma 10.159.3: for a prime ideal `p` of `R` and a finite field extension `L / κ(p)`, there
exists a finite free `R`-algebra `S` such that the extended ideal `pS` is prime and the induced
residue field extension at `pS` is isomorphic to `L` as a `κ(p)`-algebra. -/
theorem exists_finiteFree_with_prime_extendedIdeal_and_residueField_equiv
    (p : Ideal R) [p.IsPrime] (L : Type v) [Field L] [Algebra p.ResidueField L]
    [FiniteDimensional p.ResidueField L] :
    ∃ (S : Type (max u v)) (_ : CommRing S) (_ : Algebra R S) (_ : Module.Free R S)
      (_ : Module.Finite R S),
      let q : Ideal S := p.map (algebraMap R S)
      ∃ (_ : q.IsPrime) (_ : q.LiesOver p), Nonempty (q.ResidueField ≃ₐ[p.ResidueField] L) := by
  -- The public theorem is now a direct specialization of the universe-polymorphic induction
  -- package, so the remaining work is concentrated in the two source-faithful recursive branches.
  simpa using
    (exists_finiteFree_with_prime_extendedIdeal_and_residueField_equiv_aux
      (A := R) (p := p) (L := L))

end

/-! ### Lemma_10_159_4 (from Chap10) -/
open scoped Cardinal
open PrimeSpectrum

universe u

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/- Domain triage:
* primary domain: commutative algebra of flat and faithfully flat algebra maps;
* source-facing owner: the `Subalgebra`-property
  `Subalgebra.IsFlatOfBoundedCardinality`, indexed canonically by the subtype
  `{S : Subalgebra A B // S.IsFlatOfBoundedCardinality}`;
* bridge/view owner for faithful flatness: `PrimeSpectrum.comap`, with faithful flatness recovered
  from `Module.FaithfullyFlat.of_comap_surjective`.

Sampled owner-style API in this domain:
* `Subalgebra.coe_iSup_of_directed`, the canonical lattice owner for directed unions of
  subalgebras;
* `Algebra.exists_directed_globalCompleteIntersection_subalgebra_family` and
  `Algebra.exists_directed_smooth_subalgebra_family`, nearby project theorems stated directly on
  chosen subalgebra families;
* `Algebra.isGeometricallyRegular_of_directed_iSup_subfields`, a neighboring theorem stated
  directly in terms of `Directed` and `iSup`.

Layer triage:
* `source-facing`: the canonical subtype of bounded flat `A`-subalgebras of `B`;
* `bridge/view`: faithful flatness of a flat subalgebra, expressed through the canonical owner map
  on prime spectra.

Primitive data for the source-facing statement are exactly the subalgebras `S : Subalgebra A B`
with `S.IsFlatOfBoundedCardinality`; directedness and the supremum statement are derived properties
of the resulting subtype-indexed family, so no auxiliary wrapper owner is kept.
-/

namespace Subalgebra

/-- An `A`-subalgebra of `B` that is flat over `A` and has cardinality at most `max (|A|, ℵ₀)`. -/
def IsFlatOfBoundedCardinality (S : Subalgebra A B) : Prop :=
  Module.Flat A S ∧ #S ≤ #A ⊔ ℵ₀

end Subalgebra

-- Proof sketch: start from each finite subset of `B`, take the `A`-subalgebra it generates, and
-- enlarge it inductively using the equational criterion of flatness so that every relation over
-- the current stage becomes trivial in the next stage. The union of the resulting countable tower
-- is flat, still has cardinality at most `max (|A|, ℵ₀)`, and every element of `B` lies in some
-- such stage, yielding a directed family with supremum `⊤`.
namespace Subalgebra

/-- Helper for Lemma 10.159.4: adjoining a set of cardinality at most `max (|A|, ℵ₀)` still
has cardinality at most `max (|A|, ℵ₀)`. -/
lemma cardinalMk_adjoin_le_bound (s : Set B) (hs : #s ≤ #A ⊔ ℵ₀) :
    #(Algebra.adjoin A s) ≤ #A ⊔ ℵ₀ := by
  -- The ambient free-algebra bound already controls `adjoin`; only the source-side seed bound
  -- needs to be folded back into `max (|A|, ℵ₀)`.
  have hs' : #A ⊔ #s ≤ #A ⊔ (#A ⊔ ℵ₀) := sup_le_sup_left hs #A
  calc
    #(Algebra.adjoin A s) ≤ (#A ⊔ #s) ⊔ ℵ₀ := Algebra.cardinalMk_adjoin_le A s
    _ ≤ (#A ⊔ (#A ⊔ ℵ₀)) ⊔ ℵ₀ := sup_le_sup_right hs' ℵ₀
    _ = #A ⊔ ℵ₀ := by simp [sup_comm]

/-- Helper for Lemma 10.159.4: the supremum of two bounded subalgebras still has cardinality at
most `max (|A|, ℵ₀)`. -/
lemma cardinalMk_sup_le_bound (S T : Subalgebra A B) (hS : #S ≤ #A ⊔ ℵ₀) (hT : #T ≤ #A ⊔ ℵ₀) :
    #(S ⊔ T : Subalgebra A B) ≤ #A ⊔ ℵ₀ := by
  -- We rewrite the lattice supremum as an adjoin of the union of the two underlying carriers.
  have hUnion : #((S : Set B) ∪ (T : Set B) : Set B) ≤ #A ⊔ ℵ₀ := by
    calc
      #((S : Set B) ∪ (T : Set B) : Set B) ≤ #(S : Set B) + #(T : Set B) :=
        Cardinal.mk_union_le _ _
      _ ≤ (#A ⊔ ℵ₀) + (#A ⊔ ℵ₀) := by
        exact add_le_add (by simpa using hS) (by simpa using hT)
      _ = #A ⊔ ℵ₀ := by
        rw [Cardinal.add_eq_max (show ℵ₀ ≤ #A ⊔ ℵ₀ from le_sup_right), max_self]
  simpa [Algebra.adjoin_union, Algebra.adjoin_eq S, Algebra.adjoin_eq T] using
    cardinalMk_adjoin_le_bound (A := A) (B := B) ((S : Set B) ∪ (T : Set B)) hUnion

/-- Helper for Lemma 10.159.4: the subalgebra generated by one element already satisfies the
required cardinality bound. -/
lemma cardinalMk_adjoin_singleton_le_bound (b : B) :
    #(Algebra.adjoin A ({b} : Set B)) ≤ #A ⊔ ℵ₀ := by
  -- A singleton seed has cardinality `1`, and `1 ≤ ℵ₀ ≤ max (|A|, ℵ₀)`.
  refine cardinalMk_adjoin_le_bound (A := A) (B := B) ({b} : Set B) ?_
  calc
    #({b} : Set B) = 1 := Cardinal.mk_singleton b
    _ ≤ #A ⊔ ℵ₀ := Cardinal.one_le_aleph0.trans le_sup_right

/-- Helper for Lemma 10.159.4: a packaged finite relation over a seed subalgebra. -/
structure RelationData (E : Subalgebra A B) where
  l : ℕ
  f : Fin l → A
  x : Fin l → E
  sum_eq_zero : ∑ i, f i • ((x i : E) : B) = 0

/-- Helper for Lemma 10.159.4: forget the equation proof from relation data. -/
def RelationData.encoding {E : Subalgebra A B} (r : RelationData (A := A) (B := B) E) :
    Σ l : ℕ, (Fin l → A) × (Fin l → E) :=
  ⟨r.l, r.f, r.x⟩

/-- Helper for Lemma 10.159.4: the equation proof is the only omitted field in
`RelationData.encoding`. -/
lemma relationData_encoding_injective (E : Subalgebra A B) :
    Function.Injective (RelationData.encoding (A := A) (B := B) (E := E)) := by
  -- Once length, coefficients, and entries agree, proof irrelevance identifies the remaining
  -- equation field.
  intro r s h
  cases r
  cases s
  cases h
  simp

/-- Helper for Lemma 10.159.4: the set of finite relations over a bounded seed subalgebra has
cardinality at most `max (|A|, ℵ₀)`. -/
lemma relation_data_cardinal_le_bound (E : Subalgebra A B) (hE : #E ≤ #A ⊔ ℵ₀) :
    #(RelationData (A := A) (B := B) E) ≤ #A ⊔ ℵ₀ := by
  -- The source proof bounds relation data by the choices of length, coefficients, and entries.
  have hEncode :
      #(RelationData (A := A) (B := B) E) ≤ #(Σ l : ℕ, (Fin l → A) × (Fin l → E)) :=
    Cardinal.mk_le_of_injective (relationData_encoding_injective (A := A) (B := B) E)
  have hκ : ℵ₀ ≤ #A ⊔ ℵ₀ := le_sup_right
  have hAfun : ∀ l : ℕ, #(Fin l → A) ≤ #A ⊔ ℵ₀ := by
    intro l
    calc
      #(Fin l → A) = #A ^ (l : Cardinal) := by
        simpa [Cardinal.mk_fin, Cardinal.power_natCast] using Cardinal.mk_arrow (Fin l) A
      _ ≤ max #A ℵ₀ := Cardinal.power_nat_le_max
      _ = #A ⊔ ℵ₀ := by simp [sup_comm]
  have hEfun : ∀ l : ℕ, #(Fin l → E) ≤ #A ⊔ ℵ₀ := by
    intro l
    calc
      #(Fin l → E) = #E ^ (l : Cardinal) := by
        simpa [Cardinal.mk_fin, Cardinal.power_natCast] using Cardinal.mk_arrow (Fin l) E
      _ ≤ max #E ℵ₀ := Cardinal.power_nat_le_max
      _ ≤ #A ⊔ ℵ₀ := max_le hE le_sup_right
  have hProd :
      ∀ l : ℕ, #((Fin l → A) × (Fin l → E)) ≤ #A ⊔ ℵ₀ := by
    intro l
    calc
      #((Fin l → A) × (Fin l → E)) = #(Fin l → A) * #(Fin l → E) := by
        simpa using (Cardinal.mk_prod (Fin l → A) (Fin l → E))
      _ ≤ (#A ⊔ ℵ₀) * (#A ⊔ ℵ₀) := mul_le_mul' (hAfun l) (hEfun l)
      _ = #A ⊔ ℵ₀ := Cardinal.mul_eq_self hκ
  calc
    #(RelationData (A := A) (B := B) E)
        ≤ #(Σ l : ℕ, (Fin l → A) × (Fin l → E)) := hEncode
    _ = Cardinal.sum (fun l : ℕ => #((Fin l → A) × (Fin l → E))) := Cardinal.mk_sigma _
    _ ≤ Cardinal.sum (fun _ : ℕ => #A ⊔ ℵ₀) := Cardinal.sum_le_sum _ _ hProd
    _ = Cardinal.lift #ℕ * (#A ⊔ ℵ₀) := by
      simpa using (Cardinal.sum_const ℕ (#A ⊔ ℵ₀))
    _ = #A ⊔ ℵ₀ := by
      rw [show Cardinal.lift #ℕ = ℵ₀ by simpa [Cardinal.mk_nat]]
      rw [mul_comm, Cardinal.mul_aleph0_eq hκ]

/-- Helper for Lemma 10.159.4: one chosen trivialization of a packaged relation in the ambient
flat algebra. -/
structure RelationWitness {E : Subalgebra A B}
    (r : RelationData (A := A) (B := B) E) where
  k : ℕ
  a : Fin r.l → Fin k → A
  y : Fin k → B
  decompose : ∀ i, ((r.x i : E) : B) = ∑ j, a i j • y j
  linear : ∀ j, ∑ i, r.f i * a i j = 0

/-- Helper for Lemma 10.159.4: flatness of `B` supplies a trivialization for every packaged
relation over a seed subalgebra. -/
lemma relationWitness_exists [Module.Flat A B] {E : Subalgebra A B}
    (r : RelationData (A := A) (B := B) E) :
    Nonempty (RelationWitness (A := A) (B := B) r) := by
  -- This is exactly the forward direction of the equational criterion in the ambient algebra `B`.
  rcases Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
      (f := r.f) (x := fun i ↦ ((r.x i : E) : B)) r.sum_eq_zero with
    ⟨k, a, y, decompose, linear⟩
  exact ⟨⟨k, a, y, decompose, linear⟩⟩

/-- Helper for Lemma 10.159.4: fix one ambient trivialization for each packaged relation. -/
noncomputable def chosenRelationWitness [Module.Flat A B] {E : Subalgebra A B}
    (r : RelationData (A := A) (B := B) E) : RelationWitness (A := A) (B := B) r :=
  Classical.choice (relationWitness_exists (A := A) (B := B) r)

/-- Helper for Lemma 10.159.4: indices for all chosen witness elements attached to relations
over `E`. -/
abbrev WitnessIndex [Module.Flat A B] (E : Subalgebra A B) :=
  Σ r : RelationData (A := A) (B := B) E, Fin (chosenRelationWitness (A := A) (B := B) r).k

/-- Helper for Lemma 10.159.4: the chosen witness element indexed by `ij`. -/
noncomputable def witnessElement [Module.Flat A B] (E : Subalgebra A B)
    (ij : WitnessIndex (A := A) (B := B) E) : B :=
  (chosenRelationWitness (A := A) (B := B) ij.1).y ij.2

/-- Helper for Lemma 10.159.4: the set of all chosen witness elements for relations over `E`. -/
noncomputable def witnessSet [Module.Flat A B] (E : Subalgebra A B) : Set B :=
  Set.range (witnessElement (A := A) (B := B) E)

/-- Helper for Lemma 10.159.4: the chosen witness set over a bounded seed subalgebra still has
cardinality at most `max (|A|, ℵ₀)`. -/
lemma witnessSet_cardinal_le_bound [Module.Flat A B] (E : Subalgebra A B)
    (hE : #E ≤ #A ⊔ ℵ₀) :
    #(witnessSet (A := A) (B := B) E) ≤ #A ⊔ ℵ₀ := by
  -- The witness set is the image of a bounded set of relation/witness-slot indices.
  have hDomain :
      #(WitnessIndex (A := A) (B := B) E) ≤ #A ⊔ ℵ₀ := by
    have hκ : ℵ₀ ≤ #A ⊔ ℵ₀ := le_sup_right
    calc
      #(WitnessIndex (A := A) (B := B) E)
          = Cardinal.sum
              (fun r : RelationData (A := A) (B := B) E =>
                #(Fin (chosenRelationWitness (A := A) (B := B) r).k)) := by
            rw [WitnessIndex, Cardinal.mk_sigma]
      _ ≤ Cardinal.sum
            (fun _ : RelationData (A := A) (B := B) E => (ℵ₀ : Cardinal.{0})) := by
        refine Cardinal.sum_le_sum _ _ ?_
        intro r
        calc
            #(Fin (chosenRelationWitness (A := A) (B := B) r).k)
                = (chosenRelationWitness (A := A) (B := B) r).k := by
                  simpa using (Cardinal.mk_fin (chosenRelationWitness (A := A) (B := B) r).k)
            _ ≤ ℵ₀ := Cardinal.natCast_le_aleph0
      _ = Cardinal.lift #(RelationData (A := A) (B := B) E) * ℵ₀ := by
        simpa using (Cardinal.sum_const (RelationData (A := A) (B := B) E) (ℵ₀ : Cardinal.{0}))
      _ ≤ (#A ⊔ ℵ₀) * (#A ⊔ ℵ₀) := by
        refine mul_le_mul' ?_ le_sup_right
        simpa using relation_data_cardinal_le_bound (A := A) (B := B) E hE
      _ = #A ⊔ ℵ₀ := Cardinal.mul_eq_self hκ
  exact (Cardinal.mk_range_le (f := witnessElement (A := A) (B := B) E)).trans hDomain

/-- Helper for Lemma 10.159.4: adjoin all chosen witness elements to the seed subalgebra. -/
noncomputable def relationResolvingSubalgebra [Module.Flat A B] (E : Subalgebra A B) :
    Subalgebra A B :=
  E ⊔ Algebra.adjoin A (witnessSet (A := A) (B := B) E)

/-- Helper for Lemma 10.159.4: every chosen witness element belongs to the resolving successor
stage. -/
lemma witness_mem_relationResolvingSubalgebra [Module.Flat A B] (E : Subalgebra A B)
    (ij : WitnessIndex (A := A) (B := B) E) :
    witnessElement (A := A) (B := B) E ij ∈ relationResolvingSubalgebra (A := A) (B := B) E := by
  -- Chosen witnesses lie in the adjoined witness set by construction.
  exact
    (show Algebra.adjoin A (witnessSet (A := A) (B := B) E) ≤
        relationResolvingSubalgebra (A := A) (B := B) E from le_sup_right)
      (Algebra.subset_adjoin ⟨ij, rfl⟩)

/-- Helper for Lemma 10.159.4: the relation-resolving successor stage stays within the cardinal
bound. -/
lemma relationResolvingSubalgebra_cardinal_le_bound [Module.Flat A B] (E : Subalgebra A B)
    (hE : #E ≤ #A ⊔ ℵ₀) :
    #(relationResolvingSubalgebra (A := A) (B := B) E) ≤ #A ⊔ ℵ₀ := by
  -- First bound the adjoined witness set, then combine it with the existing seed subalgebra.
  have hAdjoin :
      #(Algebra.adjoin A (witnessSet (A := A) (B := B) E)) ≤ #A ⊔ ℵ₀ :=
    cardinalMk_adjoin_le_bound (A := A) (B := B) (witnessSet (A := A) (B := B) E)
      (witnessSet_cardinal_le_bound (A := A) (B := B) E hE)
  simpa [relationResolvingSubalgebra] using
    cardinalMk_sup_le_bound (A := A) (B := B) E
      (Algebra.adjoin A (witnessSet (A := A) (B := B) E)) hE hAdjoin

/-- Helper for Lemma 10.159.4: one source-faithful successor stage above a seed subalgebra. -/
structure RelationResolvingExtensionData (E : Subalgebra A B) where
  carrier : Subalgebra A B
  le_carrier : E ≤ carrier
  card_le : #carrier ≤ #A ⊔ ℵ₀
  trivializes :
    ∀ {l : ℕ} {f : Fin l → A} {x : Fin l → E},
      ∑ i, f i • ((x i : E) : B) = 0 →
        Module.IsTrivialRelation f (fun i ↦ Subalgebra.inclusion le_carrier (x i))

/-- Helper for Lemma 10.159.4: adjoining chosen witnesses yields a bounded successor stage that
trivializes every current relation. -/
lemma exists_relation_resolving_extension [Module.Flat A B] (E : Subalgebra A B)
    (hE : #E ≤ #A ⊔ ℵ₀) :
    Nonempty (RelationResolvingExtensionData (A := A) (B := B) E) := by
  -- The source proof takes the current stage and adjoins witnesses trivializing all relations in it.
  refine ⟨
    { carrier := relationResolvingSubalgebra (A := A) (B := B) E
      le_carrier := le_sup_left
      card_le := relationResolvingSubalgebra_cardinal_le_bound (A := A) (B := B) E hE
      trivializes := ?_ }⟩
  intro l f x hx
  let r : RelationData (A := A) (B := B) E := ⟨l, f, x, hx⟩
  let w := chosenRelationWitness (A := A) (B := B) r
  let y' : Fin w.k → relationResolvingSubalgebra (A := A) (B := B) E :=
    fun j ↦ ⟨w.y j, witness_mem_relationResolvingSubalgebra (A := A) (B := B) E ⟨r, j⟩⟩
  -- The same ambient trivialization works after viewing the chosen witnesses inside the
  -- successor stage.
  refine ⟨w.k, w.a, y', ?_, w.linear⟩
  intro i
  apply Subtype.ext
  simpa [y'] using w.decompose i

/-- Helper for Lemma 10.159.4: choose one relation-resolving successor stage above `E`. -/
noncomputable def chosenRelationResolvingExtension [Module.Flat A B] (E : Subalgebra A B)
    (hE : #E ≤ #A ⊔ ℵ₀) : RelationResolvingExtensionData (A := A) (B := B) E :=
  Classical.choice (exists_relation_resolving_extension (A := A) (B := B) E hE)

/-- Helper for Lemma 10.159.4: the countable source tower obtained by iterating the
relation-resolving successor construction. -/
noncomputable def boundedFlatTower [Module.Flat A B] (E : Subalgebra A B)
    (hE : #E ≤ #A ⊔ ℵ₀) : ℕ → { S : Subalgebra A B // #S ≤ #A ⊔ ℵ₀ }
  | 0 => ⟨E, hE⟩
  | n + 1 =>
      let prev := boundedFlatTower E hE n
      let step := chosenRelationResolvingExtension (A := A) (B := B) prev.1 prev.2
      ⟨step.carrier, step.card_le⟩

/-- Helper for Lemma 10.159.4: each successor stage in the bounded source tower contains the
preceding one. -/
lemma boundedFlatTower_le_succ [Module.Flat A B] (E : Subalgebra A B)
    (hE : #E ≤ #A ⊔ ℵ₀) (n : ℕ) :
    (boundedFlatTower (A := A) (B := B) E hE n).1 ≤
      (boundedFlatTower (A := A) (B := B) E hE (n + 1)).1 := by
  -- This is the inclusion field stored in the chosen successor stage.
  simpa [boundedFlatTower] using
    (chosenRelationResolvingExtension (A := A) (B := B)
      (boundedFlatTower (A := A) (B := B) E hE n).1
      (boundedFlatTower (A := A) (B := B) E hE n).2).le_carrier

/-- Helper for Lemma 10.159.4: the bounded source tower is monotone. -/
lemma boundedFlatTower_monotone [Module.Flat A B] (E : Subalgebra A B)
    (hE : #E ≤ #A ⊔ ℵ₀) :
    Monotone fun n ↦ (boundedFlatTower (A := A) (B := B) E hE n).1 := by
  intro m n hmn
  induction hmn with
  | refl => exact le_rfl
  | @step n _ ih =>
      exact le_trans ih (boundedFlatTower_le_succ (A := A) (B := B) E hE n)

/-- Helper for Lemma 10.159.4: trivial relations remain trivial after inclusion into a larger
subalgebra. -/
lemma isTrivialRelation_inclusion {S T : Subalgebra A B} (hST : S ≤ T) {ι : Type*} [Fintype ι]
    {f : ι → A} {x : ι → S} (h : Module.IsTrivialRelation f x) :
    Module.IsTrivialRelation f (fun i ↦ Subalgebra.inclusion hST (x i)) := by
  -- Reuse the same matrix and just include the witness family into the larger subalgebra.
  rcases h with ⟨k, a, y, hy, hf⟩
  refine ⟨k, a, fun j ↦ Subalgebra.inclusion hST (y j), ?_, hf⟩
  intro i
  apply Subtype.ext
  simp [hy i]

/-- Helper for Lemma 10.159.4: the supremum of a monotone countable chain of bounded subalgebras
still has cardinality at most `max (|A|, ℵ₀)`. -/
lemma cardinalMk_iSup_nat_le_bound (E : ℕ → Subalgebra A B) (hMono : Monotone E)
    (hE : ∀ n, #(E n) ≤ #A ⊔ ℵ₀) :
    #((iSup E : Subalgebra A B)) ≤ #A ⊔ ℵ₀ := by
  -- Directed unions of countably many bounded stages stay bounded because `κ * κ = κ` for
  -- `κ = max (|A|, ℵ₀)`.
  have hκ : ℵ₀ ≤ #A ⊔ ℵ₀ := le_sup_right
  calc
    #((iSup E : Subalgebra A B)) = #(⋃ n : ℕ, (E n : Set B)) := by
      change #((iSup E : Subalgebra A B) : Set B) = #(⋃ n : ℕ, (E n : Set B))
      rw [Subalgebra.coe_iSup_of_directed (K := E) hMono.directed_le]
    _ ≤ Cardinal.sum (fun _ : ℕ => #A ⊔ ℵ₀) := by
      have hUnion :
          Cardinal.lift #(⋃ n : ℕ, (E n : Set B)) ≤
            Cardinal.sum (fun n : ℕ => #((E n : Set B))) :=
        Cardinal.mk_iUnion_le_sum_mk_lift (f := fun n : ℕ => (E n : Set B))
      have hBound :
          Cardinal.sum (fun n : ℕ => #((E n : Set B))) ≤
            Cardinal.sum (fun _ : ℕ => #A ⊔ ℵ₀) :=
        Cardinal.sum_le_sum _ _ fun n ↦ by simpa using hE n
      exact by simpa using hUnion.trans hBound
    _ = Cardinal.lift #ℕ * (#A ⊔ ℵ₀) := by
      simpa using (Cardinal.sum_const ℕ (#A ⊔ ℵ₀))
    _ = #A ⊔ ℵ₀ := by
      rw [show Cardinal.lift #ℕ = ℵ₀ by simpa [Cardinal.mk_nat]]
      rw [mul_comm, Cardinal.mul_aleph0_eq hκ]

/-- Helper for Lemma 10.159.4: every bounded seed subalgebra of a flat algebra sits in a bounded
flat superalgebra. -/
theorem exists_flat_bounded_superalgebra [Module.Flat A B] (E : Subalgebra A B)
    (hE : #E ≤ #A ⊔ ℵ₀) :
    ∃ S : Subalgebra A B, E ≤ S ∧ S.IsFlatOfBoundedCardinality := by
  classical
  -- Route correction: the old stub stopped before constructing the source tower. We now follow
  -- the source proof literally: choose a bounded successor stage that resolves all current finite
  -- relations, iterate it along `ℕ`, and prove the directed union is flat by the equational
  -- criterion.
  let tower : ℕ → Subalgebra A B := fun n ↦ (boundedFlatTower (A := A) (B := B) E hE n).1
  have hTowerLeSucc : ∀ n, tower n ≤ tower (n + 1) := by
    intro n
    -- Each successor stage was chosen precisely to contain the previous one.
    simpa [tower] using boundedFlatTower_le_succ (A := A) (B := B) E hE n
  have hTowerMono : Monotone tower := by
    simpa [tower] using boundedFlatTower_monotone (A := A) (B := B) E hE
  have hTowerCard : ∀ n, #(tower n) ≤ #A ⊔ ℵ₀ := fun n ↦ (boundedFlatTower (A := A) (B := B) E hE n).2
  let S : Subalgebra A B := (iSup tower : Subalgebra A B)
  have hCardS : #S ≤ #A ⊔ ℵ₀ := by
    -- The countable union bound is the omitted set-theoretic step from the source proof.
    simpa [S] using
      cardinalMk_iSup_nat_le_bound (A := A) (B := B) tower hTowerMono hTowerCard
  have hFlatS : Module.Flat A S := by
    refine Module.Flat.of_forall_isTrivialRelation ?_
    intro l f x hx
    -- Put every entry of the relation into a common stage of the tower by taking the finite
    -- supremum of the individual stage indices.
    have hxStage : ∀ i : Fin l, ∃ n : ℕ, ((x i : S) : B) ∈ tower n := by
      intro i
      have hxMem : ((x i : S) : B) ∈ (S : Set B) := (x i).property
      rw [show (S : Set B) = ⋃ n : ℕ, (tower n : Set B) by
        simp [S, Subalgebra.coe_iSup_of_directed (K := tower) hTowerMono.directed_le]] at hxMem
      simpa [Set.mem_iUnion] using hxMem
    let stage : Fin l → ℕ := fun i ↦ Classical.choose (hxStage i)
    let N : ℕ := Finset.univ.sup stage
    have hStageLe : ∀ i : Fin l, stage i ≤ N := by
      intro i
      exact Finset.le_sup (Finset.mem_univ i)
    let xN : Fin l → tower N :=
      fun i ↦ ⟨(x i : S), hTowerMono (hStageLe i) (Classical.choose_spec (hxStage i))⟩
    have hxN :
        ∑ i, f i • ((xN i : tower N) : B) = 0 := by
      -- The relation is unchanged after replacing each term by its realization inside the common
      -- stage `N`.
      have hxB : ∑ i, f i • ((x i : S) : B) = 0 := by
        simpa using congrArg (fun z : S => (z : B)) hx
      simpa [xN] using hxB
    have hStep :
        Module.IsTrivialRelation f
          (fun i ↦ Subalgebra.inclusion (hTowerLeSucc N) (xN i)) := by
      -- The chosen successor stage for `tower N` trivializes every relation over `tower N`.
      exact
        (chosenRelationResolvingExtension (A := A) (B := B)
          (boundedFlatTower (A := A) (B := B) E hE N).1
          (boundedFlatTower (A := A) (B := B) E hE N).2).trivializes hxN
    have hInS :
        Module.IsTrivialRelation f
          (fun i ↦
            Subalgebra.inclusion (le_iSup tower (N + 1))
              (Subalgebra.inclusion (hTowerLeSucc N) (xN i))) :=
      isTrivialRelation_inclusion (A := A) (B := B) (le_iSup tower (N + 1)) hStep
    have hxEq :
        (fun i ↦
          Subalgebra.inclusion (le_iSup tower (N + 1))
            (Subalgebra.inclusion (hTowerLeSucc N) (xN i))) = x := by
      -- Both sides are the same elements of the union stage `S`; only the subtype proofs differ.
      funext i
      apply Subtype.ext
      rfl
    rw [hxEq] at hInS
    exact hInS
  refine ⟨S, ?_, hFlatS, hCardS⟩
  -- The initial seed is the first stage of the tower, hence lies in its supremum.
  simpa [S, tower, boundedFlatTower] using (le_iSup tower 0)

/-- Lemma 10.159.4: the canonical family of flat `A`-subalgebras of `B` of cardinality at most
`max (|A|, ℵ₀)` is directed by inclusion. -/
theorem directed_flatSubalgebras_of_boundedCardinality [Module.Flat A B] :
    Directed (· ≤ ·)
      (Subtype.val : { S : Subalgebra A B // S.IsFlatOfBoundedCardinality } → Subalgebra A B) :=
  by
    intro S T
    rcases S with ⟨S, hS⟩
    rcases T with ⟨T, hT⟩
    -- The source proof enlarges the bounded seed `S ⊔ T` to a bounded flat superalgebra.
    have hSup : #(S ⊔ T : Subalgebra A B) ≤ #A ⊔ ℵ₀ :=
      cardinalMk_sup_le_bound (A := A) (B := B) S T hS.2 hT.2
    rcases exists_flat_bounded_superalgebra (A := A) (B := B) (E := S ⊔ T) hSup with
      ⟨U, hSU, hU⟩
    refine ⟨⟨U, hU⟩, ?_, ?_⟩
    · exact le_trans le_sup_left hSU
    · exact le_trans le_sup_right hSU

/-- Lemma 10.159.4: the supremum of the canonical family of flat `A`-subalgebras of `B` of
cardinality at most `max (|A|, ℵ₀)` is `⊤`. Equivalently, the flat `A`-algebra `B` is the
filtered colimit of its flat `A`-subalgebras of bounded cardinality. -/
theorem iSup_flatSubalgebras_of_boundedCardinality_eq_top [Module.Flat A B] :
    iSup
        (Subtype.val :
          { S : Subalgebra A B // S.IsFlatOfBoundedCardinality } → Subalgebra A B) =
      (⊤ : Subalgebra A B) := by
  apply le_antisymm
  · -- One inclusion is formal because every stage is a subalgebra of `B`.
    exact iSup_le fun _ ↦ le_top
  · -- For the converse, enlarge the one-generated seed `A[b]` to a bounded flat subalgebra.
    intro b _
    have hSeed : #(Algebra.adjoin A ({b} : Set B)) ≤ #A ⊔ ℵ₀ :=
      cardinalMk_adjoin_singleton_le_bound (A := A) (B := B) b
    rcases exists_flat_bounded_superalgebra (A := A) (B := B)
        (E := Algebra.adjoin A ({b} : Set B)) hSeed with
      ⟨S, hSeedLe, hS⟩
    have hbSeed : b ∈ Algebra.adjoin A ({b} : Set B) := Algebra.self_mem_adjoin_singleton (R := A) b
    have hbS : b ∈ S := hSeedLe hbSeed
    exact le_iSup (Subtype.val : { S : Subalgebra A B // S.IsFlatOfBoundedCardinality } →
      Subalgebra A B) ⟨S, hS⟩ hbS

end Subalgebra

-- Proof sketch: the owner theorem `PrimeSpectrum.comap_surjective_of_faithfullyFlat` gives a
-- prime of `B` over every prime of `A`. Contracting that prime along the inclusion `S ↪ B` shows
-- that `Spec S → Spec A` is surjective. Together with the flatness hypothesis on `S`, this gives
-- faithful flatness by the standard criterion
-- `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`.
/-- A flat `A`-subalgebra of a faithfully flat `A`-algebra is faithfully flat over `A`. -/
theorem faithfullyFlat_of_flat_subalgebra [Module.FaithfullyFlat A B] (S : Subalgebra A B)
    [Module.Flat A S] :
    Module.FaithfullyFlat A S := by
  refine Module.FaithfullyFlat.of_comap_surjective fun p ↦ ?_
  have hsurj : Function.Surjective (comap (algebraMap A B)) :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat
  obtain ⟨q, rfl⟩ := hsurj p
  exact ⟨comap S.val q, by rw [← comap_comp_apply, S.val.comp_algebraMap]⟩

end
