import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_143_5
import stacks_proof.stacks_project.Chap15.Definition_15_105_1
import stacks_proof.stacks_project.Chap15.Lemma_15_105_7
import stacks_proof.stacks_project.Chap15.Lemma_15_105_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- Helper for Lemma 15.105.17: the zero-ideal residue field of a field is canonically the field
itself. -/
noncomputable def field_botResidueFieldAlgEquiv (K : Type u) [Field K] :
    K ≃ₐ[K] ((⊥ : Ideal K).ResidueField) := by
  -- Realize `κ((0))` as a fraction ring of `K`, then compare the two fraction-ring models.
  letI : IsFractionRing K ((⊥ : Ideal K).ResidueField) := by
    let e : K ≃ₐ[K] K ⧸ (⊥ : Ideal K) := (AlgEquiv.quotientBot K K).symm
    refine IsFractionRing.of_ringEquiv_left e.toRingEquiv ?_
    intro x
    change algebraMap K ((⊥ : Ideal K).ResidueField) x =
      algebraMap (K ⧸ (⊥ : Ideal K)) ((⊥ : Ideal K).ResidueField) (Ideal.Quotient.mk _ x)
    symm
    rfl
  let eFracK : FractionRing K ≃ₐ[K] K := FractionRing.algEquiv K K
  let eFracResidue : FractionRing K ≃ₐ[K] ((⊥ : Ideal K).ResidueField) :=
    FractionRing.algEquiv K ((⊥ : Ideal K).ResidueField)
  exact eFracK.symm.trans eFracResidue

/-- Helper for Lemma 15.105.17: the fiber prime attached to `q` contracts back to `q` along the
right tensor-factor map. -/
lemma preimageEquivFiber_asIdeal_comap
    (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hq : PrimeSpectrum.comap (algebraMap A B) q = p) :
    Ideal.comap Algebra.TensorProduct.includeRight.toRingHom
      ((PrimeSpectrum.preimageEquivFiber A B p ⟨q, hq⟩).asIdeal) = q.asIdeal := by
  -- Rewrite the fiber prime through the inverse of `PrimeSpectrum.preimageEquivFiber`.
  change
    ((PrimeSpectrum.preimageEquivFiber A B p).symm
      (PrimeSpectrum.preimageEquivFiber A B p ⟨q, hq⟩)).1.asIdeal = q.asIdeal
  exact congrArg
    (fun x : PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p} ↦ x.1.asIdeal)
    ((PrimeSpectrum.preimageEquivFiber A B p).symm_apply_apply ⟨q, hq⟩)

/-- Helper for Lemma 15.105.17: the canonical residue-field map from the original branch `q` to
the corresponding fiber prime `qbar` is an equivalence over the base residue field `κ(p)`. -/
noncomputable def residueField_algEquiv_of_baseChange_fiber_prime
    (p : Ideal A) [p.IsPrime] (q : p.primesOver B) (qbar : PrimeSpectrum (p.Fiber B))
    (hqbar :
      Ideal.comap Algebra.TensorProduct.includeRight.toRingHom qbar.asIdeal = q.1) :
    q.1.ResidueField ≃ₐ[p.ResidueField] qbar.asIdeal.ResidueField := by
  let e : q.1.ResidueField ≃+* qbar.asIdeal.ResidueField :=
    RingEquiv.ofBijective
      (Ideal.ResidueField.map q.1 qbar.asIdeal
        Algebra.TensorProduct.includeRight.toRingHom hqbar.symm)
      ((p.surjectiveOnStalks_residueField.baseChange').residueFieldMap_bijective
        q.1 qbar.asIdeal hqbar.symm)
  refine AlgEquiv.ofRingEquiv (f := e) ?_
  intro x
  -- Reduce the scalar-compatibility check to elements coming from `A`, then compare the two
  -- tensor-factor maps on the common base ring.
  obtain ⟨a, rfl⟩ := p.algebraMap_residueField_surjective x
  change
    e (Ideal.ResidueField.map p q.1 (algebraMap A B) (q.1.over_def p)
      (algebraMap A p.ResidueField a)) =
      algebraMap p.ResidueField qbar.asIdeal.ResidueField (algebraMap A p.ResidueField a)
  rw [show e =
      Ideal.ResidueField.map q.1 qbar.asIdeal
        Algebra.TensorProduct.includeRight.toRingHom hqbar.symm from rfl]
  rw [Ideal.ResidueField.map_algebraMap q.1 qbar.asIdeal
    Algebra.TensorProduct.includeRight.toRingHom hqbar.symm ((algebraMap A B) a)]
  have hbase :
      (Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B) ((algebraMap A B) a) =
        (Algebra.TensorProduct.includeLeft : p.ResidueField →ₐ[A] p.Fiber B)
          ((algebraMap A p.ResidueField) a) := by
    -- The two tensor-factor maps agree on the image of the common base ring `A`.
    simpa using congrArg (fun f : A →+* p.Fiber B => f a)
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap :
        ((Algebra.TensorProduct.includeLeft : p.ResidueField →ₐ[A] p.Fiber B).toRingHom.comp
            (algebraMap A p.ResidueField)) =
          ((Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B).toRingHom.comp
            (algebraMap A B))).symm
  calc
    algebraMap (p.Fiber B) qbar.asIdeal.ResidueField
        ((Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B) ((algebraMap A B) a)) =
      algebraMap (p.Fiber B) qbar.asIdeal.ResidueField
        ((Algebra.TensorProduct.includeLeft : p.ResidueField →ₐ[A] p.Fiber B)
          ((algebraMap A p.ResidueField) a)) := by
        exact congrArg (algebraMap (p.Fiber B) qbar.asIdeal.ResidueField) hbase
    _ =
      algebraMap p.ResidueField qbar.asIdeal.ResidueField (algebraMap A p.ResidueField a) := by
        rfl

/-- Helper for Lemma 15.105.17: a prime of an étale algebra over a field has separable residue
field over the base field. -/
theorem prime_residueField_isSeparable_of_etale_over_field
    {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
    [Algebra.Etale K S] (r : Ideal S) [r.IsPrime] :
    Algebra.IsSeparable K r.ResidueField := by
  have hsepBot : Algebra.IsSeparable ((⊥ : Ideal K).ResidueField) r.ResidueField := by
    -- The source proof uses the étale-away witness `g = 1` and then applies Lemma `10.143.5`.
    exact
      (residueField_finite_and_separable_of_exists_etale_away
        (R := K) (S := S) r
        ⟨1, by
            simpa [Ideal.ne_top_iff_one] using
              (Ideal.IsPrime.ne_top (I := r) inferInstance),
          inferInstance⟩).2
  -- Transport separability from `κ((0))` back to `K` through the canonical base-field
  -- identification.
  rw [Algebra.isSeparable_iff] at hsepBot ⊢
  intro x
  exact IsSeparable.of_algHom (f := (field_botResidueFieldAlgEquiv K).toAlgHom) (hsepBot x)

/-- Helper for Lemma 15.105.17: quotienting a `K`-subalgebra by the comap of an ideal and then
mapping into the ambient quotient is injective. -/
lemma subalgebra_comap_quotient_map_injective
    {K : Type u} {F : Type v} [CommRing K] [CommRing F] [Algebra K F]
    (A₀ : Subalgebra K F) (Q : Ideal F) :
    Function.Injective
      (Ideal.Quotient.map (Ideal.comap (A₀.val : A₀ →+* F) Q) Q
        (A₀.val : A₀ →+* F) le_rfl) := by
  let r : Ideal A₀ := Ideal.comap (A₀.val : A₀ →+* F) Q
  let f : A₀ ⧸ r →+* F ⧸ Q := Ideal.Quotient.map r Q (A₀.val : A₀ →+* F) le_rfl
  -- Compute the kernel of the induced quotient map directly on quotient representatives.
  have hfker : RingHom.ker f = ⊥ := by
    ext x
    change (f x = 0) ↔ x = 0
    constructor
    · intro hx
      obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective x
      -- Membership in the ambient ideal descends exactly to the comap ideal on the stage.
      change Ideal.Quotient.mk Q ((A₀.val : A₀ →+* F) x₀) = 0 at hx
      exact Ideal.Quotient.eq_zero_iff_mem.2 <| by
        simpa [r, Ideal.mem_comap] using (Ideal.Quotient.eq_zero_iff_mem.1 hx)
    · intro hx
      simpa [hx]
  exact (RingHom.injective_iff_ker_eq_bot f).2 hfker

/-- Helper for Lemma 15.105.17: for the two-generator stage `K[a, b]`, the induced quotient map
into `F ⧸ Q` is injective. -/
lemma adjoin_pair_quotient_map_injective
    {K : Type u} {F : Type v} [Field K] [CommRing F] [Algebra K F]
    (Q : Ideal F) (a b : F) :
    Function.Injective
      (Ideal.Quotient.map
        (Ideal.comap (Algebra.adjoin K ({a, b} : Set F)).val Q) Q
        ((Algebra.adjoin K ({a, b} : Set F)).val : Algebra.adjoin K ({a, b} : Set F) →+* F)
        le_rfl) := by
  -- Specialize the general subalgebra injectivity statement to the concrete source-faithful stage.
  exact
    subalgebra_comap_quotient_map_injective
      (A₀ := Algebra.adjoin K ({a, b} : Set F)) Q

/-- Helper for Lemma 15.105.17: a prime of a weakly étale algebra over a field has separable
residue field over the base field. -/
theorem residueField_isSeparable_of_isWeaklyEtale_over_field
    {K : Type u} {F : Type v} [Field K] [CommRing F] [Algebra K F]
    [Algebra.IsWeaklyEtale K F] (Q : Ideal F) [Q.IsPrime] :
    Algebra.IsSeparable K Q.ResidueField := by
  rw [Algebra.isSeparable_iff]
  intro x
  -- Capture the residue-field element by a single ambient element, then shrink to the
  -- source-faithful finitely generated stage `K[a]`.
  obtain ⟨a, rfl⟩ := Q.algebraMap_residueField_surjective x
  let A₀ : Subalgebra K F := Algebra.adjoin K ({a} : Set F)
  let r : Ideal A₀ := Ideal.comap (A₀.val : A₀ →+* F) Q
  letI : r.IsPrime := by
    dsimp [r]
    infer_instance
  let a₀ : A₀ := ⟨a, Algebra.subset_adjoin (by simp)⟩
  have hA₀fg : A₀.FG := by
    -- The singleton-generated stage is finite type, hence finitely generated.
    rw [Subalgebra.fg_iff_finiteType A₀]
    exact Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton a)
  have hA₀et : Algebra.Etale K A₀ := by
    -- Weak étaleness over the field forces each finitely generated stage to be étale.
    exact etale_of_fg_subalgebra_of_isWeaklyEtale A₀ hA₀fg
  have hsepStage : Algebra.IsSeparable K r.ResidueField := by
    letI : Algebra.Etale K A₀ := hA₀et
    -- Étale residue fields over a field are separable by the earlier helper.
    exact prime_residueField_isSeparable_of_etale_over_field (K := K) (S := A₀) r
  -- Transport the separable stage residue class to the ambient residue field.
  have hmap :
      (Ideal.ResidueField.mapₐ r Q A₀.val rfl) (algebraMap A₀ r.ResidueField a₀) =
        algebraMap F Q.ResidueField a := by
    exact Ideal.ResidueField.map_algebraMap r Q A₀.val rfl a₀
  exact
    IsSeparable.of_algHom
      (f := Ideal.ResidueField.mapₐ r Q A₀.val rfl)
      (by
        simpa [hmap] using
          ((Algebra.isSeparable_iff.mp hsepStage) (algebraMap A₀ r.ResidueField a₀)))

/- Domain-style sampling for Lemma 15.105.17:
- primary domain: weakly étale commutative algebra and the induced residue-field extensions along
  primes in a fiber;
- sampled owner declarations:
  `Algebra.IsWeaklyEtale`,
  `Algebra.IsWeaklyEtale.baseChange`,
  `weaklyEtale_over_field_tfae`,
  `Ideal.primesOver`;
- best owner abstraction: the theorem is `source-facing`, but the prime-over-prime input should be
  expressed by the canonical owner set `p.primesOver B` rather than by a raw ideal plus separate
  `[IsPrime]` and `[LiesOver]` arguments;
- primitive data: the weakly étale owner on `A → B`, the prime `p : Ideal A`, and the chosen
  prime over `p` packaged as `q : p.primesOver B`;
- derived API: the induced `p.ResidueField`-algebra structure on `q.1.ResidueField`, together
  with the algebraicity and separability assertions and their atomic projection lemmas.

Source/core/bridge triage:
- `source-facing`: `residueField_isAlgebraic_and_separable_of_isWeaklyEtale`;
- `core/canonical`: `Algebra.IsWeaklyEtale`, `Ideal.primesOver`, and `Ideal.ResidueField`;
- `bridge/view`: base change to the fiber over `p` via `Algebra.IsWeaklyEtale.baseChange`,
  followed by the field-case filtered-colimit characterization `weaklyEtale_over_field_tfae`.
-/

-- Proof sketch: base change the weakly étale map `A → B` along `A → κ(p)` using Lemma
-- `15.105.7`, so `κ(p) → B ⊗[A] κ(p)` is weakly étale. By Lemma `15.105.16`, the fiber algebra is
-- a filtered colimit of étale `κ(p)`-algebras. For a prime `q` over `p`, the residue field
-- `κ(q)` is the residue field of a prime of this fiber algebra, so Algebra Lemma `10.143.4`
-- yields algebraicity and separability over `κ(p)`.
/-- Lemma 15.105.17: if `A → B` is weakly étale, then for every prime `q` of `B` lying over a
prime `p` of `A`, the induced residue-field extension `κ(q) / κ(p)` is algebraic and separable. -/
@[stacks 092R]
theorem residueField_isAlgebraic_and_separable_of_isWeaklyEtale
    [Algebra.IsWeaklyEtale A B]
    (p : Ideal A) [p.IsPrime] (q : p.primesOver B) :
    Algebra.IsAlgebraic p.ResidueField q.1.ResidueField ∧
      Algebra.IsSeparable p.ResidueField q.1.ResidueField := by
  let pSpec : PrimeSpectrum A := ⟨p, inferInstance⟩
  let qSpec : PrimeSpectrum B := ⟨q.1, inferInstance⟩
  have hqSpec : PrimeSpectrum.comap (algebraMap A B) qSpec = pSpec := by
    -- Upgrade the lies-over equality from ideals to prime-spectrum points.
    apply PrimeSpectrum.ext
    simpa [Ideal.under, pSpec, qSpec] using (q.1.over_def p).symm
  let qbar : PrimeSpectrum (p.Fiber B) :=
    PrimeSpectrum.preimageEquivFiber A B pSpec ⟨qSpec, hqSpec⟩
  letI : Field p.ResidueField := IsLocalRing.ResidueField.field (Localization.AtPrime p)
  have hqbar :
      Ideal.comap Algebra.TensorProduct.includeRight.toRingHom qbar.asIdeal = q.1 := by
    -- The distinguished fiber prime contracts back to the original branch `q`.
    simpa [pSpec, qSpec, qbar] using
      preimageEquivFiber_asIdeal_comap (A := A) (B := B) pSpec qSpec hqSpec
  have hsepFiber : Algebra.IsSeparable p.ResidueField qbar.asIdeal.ResidueField := by
    -- Base change the weakly étale map to the fiber over `κ(p)` and apply the field-case helper.
    let hAB : Algebra.IsWeaklyEtale A B := inferInstance
    letI : Algebra.IsWeaklyEtale p.ResidueField (p.Fiber B) :=
      Algebra.IsWeaklyEtale.baseChange (A := A) (A' := p.ResidueField) (B := B) hAB
    exact
      residueField_isSeparable_of_isWeaklyEtale_over_field
        (K := p.ResidueField) (F := p.Fiber B) qbar.asIdeal
  have hsep : Algebra.IsSeparable p.ResidueField q.1.ResidueField := by
    let e : q.1.ResidueField ≃ₐ[p.ResidueField] qbar.asIdeal.ResidueField :=
      residueField_algEquiv_of_baseChange_fiber_prime
        (A := A) (B := B) p q qbar hqbar
    -- The new `κ(p)`-algebra equivalence removes the old scalar-compatibility blocker.
    simpa using (AlgEquiv.Algebra.isSeparable_iff e).1 hsepFiber
  exact ⟨hsep.isAlgebraic, hsep⟩

/-- Companion to
`residueField_isAlgebraic_and_separable_of_isWeaklyEtale`: the induced residue-field extension
along a weakly étale map is algebraic. -/
theorem residueField_isAlgebraic_of_isWeaklyEtale
    [Algebra.IsWeaklyEtale A B]
    (p : Ideal A) [p.IsPrime] (q : p.primesOver B) :
    Algebra.IsAlgebraic p.ResidueField q.1.ResidueField := by
  exact (residueField_isAlgebraic_and_separable_of_isWeaklyEtale p q).1

/-- Companion to
`residueField_isAlgebraic_and_separable_of_isWeaklyEtale`: the induced residue-field extension
along a weakly étale map is separable. -/
theorem residueField_isSeparable_of_isWeaklyEtale
    [Algebra.IsWeaklyEtale A B]
    (p : Ideal A) [p.IsPrime] (q : p.primesOver B) :
    Algebra.IsSeparable p.ResidueField q.1.ResidueField := by
  exact (residueField_isAlgebraic_and_separable_of_isWeaklyEtale p q).2

end
