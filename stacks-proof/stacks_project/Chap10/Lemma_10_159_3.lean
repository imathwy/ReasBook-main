import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
