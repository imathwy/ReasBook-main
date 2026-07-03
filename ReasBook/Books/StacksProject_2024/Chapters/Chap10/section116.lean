import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_116_1 (from Chap10) -/
universe u v

open TopologicalSpace

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [IsDomain S] [Algebra k S] [Algebra.FiniteType k S]

/- 
Domain-style sampling:
- primary domain: Krull dimension and transcendence degree for finite-type domains over a field,
  organized around the chapter's local-dimension owner theorems;
- sampled owner API:
  `topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over`,
  `ringKrullDim_eq_ringKrullDim_localizationAtMaximal_of_finiteType_domain_over_field`,
  `topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField`,
  `FractionRing.algEquiv`;
- best owner abstraction: the local dimension formula at a prime together with the generic-point
  specialization of `Spec S`; the maximal-localization equality is already derived upstream in the
  chapter and should be reused rather than duplicated here;
- primitive data vs derived API: there is no additional source-facing data in this file beyond the
  finite-type domain hypotheses. Both displayed equalities are derived API from the sampled owner
  theorems and the canonical fraction-ring/residue-field identifications at the generic point.

Layer triage:
- `source-facing`: the first theorem, which identifies `ringKrullDim S` with the transcendence
  degree of `FractionRing S`;
- `bridge/view`: the maximal-localization theorem, which should be a thin corollary of the first
  theorem and Lemma `10.114.4`.
-/

theorem topologicalKrullDimAt_genericPoint_eq_ringKrullDim :
    topologicalKrullDimAt (⊥ : PrimeSpectrum S) = ringKrullDim S := by
  rw [topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over
    (⊥ : PrimeSpectrum S)]
  obtain ⟨m0⟩ : Nonempty (MaximalSpectrum S) := by infer_instance
  refine le_antisymm ?_ ?_
  · let m : { m : MaximalSpectrum S // (⊥ : PrimeSpectrum S).asIdeal ≤ m.asIdeal } :=
      ⟨m0, by simp⟩
    exact (iInf_le
      (fun m : { m : MaximalSpectrum S // (⊥ : PrimeSpectrum S).asIdeal ≤ m.asIdeal } ↦
        ringKrullDim (Localization.AtPrime m.1.asIdeal)) m).trans <| by
          simpa using
            (ringKrullDim_eq_ringKrullDim_localizationAtMaximal_of_finiteType_domain_over_field
              m0).symm.le
  · refine le_iInf fun m ↦ ?_
    simpa using
      (ringKrullDim_eq_ringKrullDim_localizationAtMaximal_of_finiteType_domain_over_field
        m.1).le

private noncomputable def genericResidueFieldEquiv :
    FractionRing S ≃ₐ[S] ((⊥ : Ideal S).ResidueField) := by
  let e : S ≃ₐ[S] S ⧸ (⊥ : Ideal S) := (AlgEquiv.quotientBot S S).symm
  letI : IsFractionRing S ((⊥ : Ideal S).ResidueField) := by
    refine IsFractionRing.of_ringEquiv_left e.toRingEquiv ?_
    intro x
    change algebraMap S ((⊥ : Ideal S).ResidueField) x =
      algebraMap (S ⧸ (⊥ : Ideal S)) ((⊥ : Ideal S).ResidueField) (Ideal.Quotient.mk _ x)
    symm
    exact show
        algebraMap (S ⧸ (⊥ : Ideal S)) ((⊥ : Ideal S).ResidueField)
            (Ideal.Quotient.mk (⊥ : Ideal S) x) =
          algebraMap S ((⊥ : Ideal S).ResidueField) x by
      rfl
  exact FractionRing.algEquiv S ((⊥ : Ideal S).ResidueField)

private lemma ringKrullDim_localizationAtPrime_bot_eq_zero :
    ringKrullDim (Localization.AtPrime (⊥ : Ideal S)) = 0 := by
  letI : IsFractionRing S (Localization.AtPrime (⊥ : Ideal S)) := by
    delta IsFractionRing
    simpa [Ideal.primeCompl_bot] using
      (inferInstance : IsLocalization ((⊥ : Ideal S).primeCompl)
        (Localization.AtPrime (⊥ : Ideal S)))
  let e : FractionRing S ≃ₐ[S] Localization.AtPrime (⊥ : Ideal S) :=
    FractionRing.algEquiv S (Localization.AtPrime (⊥ : Ideal S))
  rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
  exact ringKrullDim_eq_zero_of_field (FractionRing S)

-- Proof sketch: write `S` as a quotient of a polynomial ring over `k`, apply Noether
-- normalization to obtain a finite injective map from a polynomial ring in `d = ringKrullDim S`
-- variables, and use the algebraic independence of the source variables in the fraction field of
-- `S` together with finiteness of the induced fraction-field extension to identify `d` with
-- `Cardinal.toNat (Algebra.trdeg k (FractionRing S))`.
/-- Lemma 10.116.1: if `S` is a finite type `k`-algebra that is an integral domain, then the Krull
dimension of `S` equals the transcendence degree of its fraction field over `k`. -/
theorem ringKrullDim_eq_trdeg_fractionRing_of_finiteType_domain_over_field :
    ringKrullDim S = Cardinal.toNat (Algebra.trdeg k (FractionRing S)) := by
  have hlocal :
      topologicalKrullDimAt (⊥ : PrimeSpectrum S) =
        ringKrullDim (Localization.AtPrime (⊥ : Ideal S)) +
          Cardinal.toNat (Algebra.trdeg k ((⊥ : Ideal S).ResidueField)) :=
    topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField
      (⊥ : PrimeSpectrum S)
  have hgeneric :
      ringKrullDim S =
        Cardinal.toNat (Algebra.trdeg k ((⊥ : Ideal S).ResidueField)) := by
    simpa [PrimeSpectrum.asIdeal_bot, topologicalKrullDimAt_genericPoint_eq_ringKrullDim,
      ringKrullDim_localizationAtPrime_bot_eq_zero] using hlocal
  have htrdeg_bot :
      (Cardinal.toNat (Algebra.trdeg k ((⊥ : Ideal S).ResidueField)) : WithBot ℕ∞) =
        Cardinal.toNat (Algebra.trdeg k (FractionRing S)) := by
    let e : FractionRing S ≃ₐ[k] ((⊥ : Ideal S).ResidueField) :=
      genericResidueFieldEquiv.restrictScalars k
    simpa using congrArg (fun n : ℕ ↦ (n : WithBot ℕ∞))
      (congrArg Cardinal.toNat (AlgEquiv.trdeg_eq e).symm)
  exact hgeneric.trans htrdeg_bot

-- Proof sketch: by Lemma `10.114.3`, all local rings of a finite type domain over a field at
-- maximal ideals have the same Krull dimension. Apply the main theorem to compute that common
-- value as the transcendence degree of `FractionRing S` over `k`.
/-- Every localization of a finite type domain over a field at a maximal ideal has Krull dimension
equal to the transcendence degree of the fraction field. -/
theorem ringKrullDim_localizationAtMaximal_eq_trdeg_fractionRing_of_finiteType_domain_over_field
    (m : MaximalSpectrum S) :
    ringKrullDim (Localization.AtPrime m.asIdeal) =
      Cardinal.toNat (Algebra.trdeg k (FractionRing S)) := by
  rw [← ringKrullDim_eq_ringKrullDim_localizationAtMaximal_of_finiteType_domain_over_field
    m]
  exact ringKrullDim_eq_trdeg_fractionRing_of_finiteType_domain_over_field

end

/-! ### Lemma_10_116_2 (from Chap10) -/
universe u v

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/- 
Domain-style sampling:
- primary domain: dimension theory of finite type algebras over a field, organized through quotient
  Krull dimensions and the order-theoretic coheight owner on `PrimeSpectrum`;
- sampled owner declarations of the same kind:
  `ringKrullDim_eq_trdeg_fractionRing_of_finiteType_domain_over_field`,
  `ringKrullDim_quotient`,
  `Order.coheight_eq_krullDim_Ici`,
  `Order.coheight_strictAnti`;
- best owner abstraction: the core canonical owner for the strict inequality is the coheight of the
  corresponding points of `Spec S`; the source-facing transcendence-degree statement should be
  obtained by identifying `ringKrullDim (S ⧸ q)` with `Cardinal.toNat (Algebra.trdeg k
  q.ResidueField)` via Lemma `10.116.1`, rather than by keeping a parallel geometric wrapper;
- primitive data: only the two prime ideals `q`, `q'` and the strict inclusion `hqq' : q < q'`;
- derived API: the quotient/fraction-ring identification with the residue field and the bridge from
  `PrimeSpectrum.zeroLocus q` to the upper interval `Set.Ici ⟨q, _⟩`.

Source/core/bridge triage:
* `source-facing`: the strict transcendence-degree inequality below;
* `core/canonical`: `ringKrullDim_eq_trdeg_fractionRing_of_finiteType_domain_over_field`,
  `ringKrullDim_quotient`, and `Order.coheight`;
* `bridge/view`: the identifications `FractionRing (S ⧸ q) ≃ₐ[k] q.ResidueField` and
  `PrimeSpectrum.zeroLocus q = Set.Ici ⟨q, _⟩`.

This file therefore stays source-facing while reusing the quotient-dimension and coheight owners
already present upstream, rather than introducing a second local dimension-comparison API.
-/

private theorem ringKrullDim_quotient_eq_trdeg_residueField_of_finiteType_over_field
    (q : Ideal S) [q.IsPrime] :
    ringKrullDim (S ⧸ q) = Cardinal.toNat (Algebra.trdeg k q.ResidueField) := by
  let e : FractionRing (S ⧸ q) ≃ₐ[k] q.ResidueField :=
    (FractionRing.algEquiv (S ⧸ q) q.ResidueField).restrictScalars k
  calc
    ringKrullDim (S ⧸ q) = Cardinal.toNat (Algebra.trdeg k (FractionRing (S ⧸ q))) :=
      ringKrullDim_eq_trdeg_fractionRing_of_finiteType_domain_over_field
    _ = Cardinal.toNat (Algebra.trdeg k q.ResidueField) := by
      simpa using congrArg Cardinal.toNat (AlgEquiv.trdeg_eq e)

private theorem ringKrullDim_quotient_eq_coheight (q : Ideal S) [q.IsPrime] :
    ringKrullDim (S ⧸ q) = Order.coheight (⟨q, inferInstance⟩ : PrimeSpectrum S) := by
  let x : PrimeSpectrum S := ⟨q, inferInstance⟩
  rw [ringKrullDim_quotient]
  have hzero : PrimeSpectrum.zeroLocus (q : Set S) = Set.Ici x := by
    ext p
    change q ≤ p.asIdeal ↔ x ≤ p
    rfl
  rw [hzero]
  exact (Order.coheight_eq_krullDim_Ici x).symm

/-- Lemma 10.116.2: if `q ⊂ q'` are distinct prime ideals in a finite type `k`-algebra `S`, then
the transcendence degree of `q'.ResidueField` over `k` is strictly smaller than the transcendence
degree of `q.ResidueField` over `k`. -/
theorem trdeg_residueField_lt_of_lt_of_finiteType_over_field
    (q q' : Ideal S) [q.IsPrime] [q'.IsPrime] (hqq' : q < q') :
    Cardinal.toNat (Algebra.trdeg k q'.ResidueField) <
      Cardinal.toNat (Algebra.trdeg k q.ResidueField) := by
  let x : PrimeSpectrum S := ⟨q, inferInstance⟩
  let x' : PrimeSpectrum S := ⟨q', inferInstance⟩
  have hq' :
      ringKrullDim (S ⧸ q') = Cardinal.toNat (Algebra.trdeg k q'.ResidueField) :=
    ringKrullDim_quotient_eq_trdeg_residueField_of_finiteType_over_field q'
  have hq :
      ringKrullDim (S ⧸ q) = Cardinal.toNat (Algebra.trdeg k q.ResidueField) :=
    ringKrullDim_quotient_eq_trdeg_residueField_of_finiteType_over_field q
  have hx'fin : Order.coheight x' < ⊤ := by
    have hdim : ringKrullDim (S ⧸ q') < ⊤ := by
      rw [hq']
      exact lt_top_iff_ne_top.mpr (fun h ↦ nomatch h)
    rw [ringKrullDim_quotient_eq_coheight q'] at hdim
    exact WithBot.coe_lt_coe.mp hdim
  have hdim : ringKrullDim (S ⧸ q') < ringKrullDim (S ⧸ q) := by
    rw [ringKrullDim_quotient_eq_coheight q', ringKrullDim_quotient_eq_coheight q]
    exact WithBot.coe_lt_coe.mpr <|
      Order.coheight_strictAnti (show x < x' from hqq') hx'fin
  rw [hq', hq] at hdim
  exact ENat.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hdim)

end

/-! ### Lemma_10_116_3 (from Chap10) -/
universe u v

open TopologicalSpace

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/- 
Domain-style sampling for the local dimension formula on affine schemes of finite type over a
field:
- primary domain: local Krull dimension on `Spec(S)`, organized around the owner
  `topologicalKrullDimAt` and the local ring `Localization.AtPrime x.asIdeal`;
- sampled owner declarations of the same kind:
  `topologicalKrullDimAt`,
  `topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over`,
  `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`,
  `IsLocalization.AtPrime.ringKrullDim_eq_height`;
- best owner abstraction: the ambient owner is the local-dimension object `topologicalKrullDimAt`
  on `PrimeSpectrum S`, while the local algebra data are already canonically owned by
  `Localization.AtPrime x.asIdeal` and `x.asIdeal.ResidueField`;
- primitive data: the point `x : PrimeSpectrum S` of the finite type affine scheme `Spec(S)`;
- derived API: the additive decomposition of `topologicalKrullDimAt x` into the Krull dimension of
  the canonical local ring and the transcendence degree of the canonical residue field.

Source/core/bridge triage:
* `source-facing`: the textbook local dimension formula at a prime of a finite type algebra over a
  field;
* `core/canonical`: `topologicalKrullDimAt`, `Localization.AtPrime`, `Ideal.ResidueField`, and
  mathlib's localization-height owner `IsLocalization.AtPrime.ringKrullDim_eq_height`;
* `bridge/view`: the comparison from the local topological owner to maximal localizations from
  Lemma `10.114.5`, together with the chain-length interpretation of heights.

There is no separate local wrapper to keep here: the theorem should speak directly in terms of the
owner objects `topologicalKrullDimAt`, `Localization.AtPrime x.asIdeal`, and
`x.asIdeal.ResidueField`.
-/

-- Proof sketch: combine the description of the local dimension at `x` as the maximum dimension of
-- irreducible components through `x` with the chain decomposition through the prime `x.asIdeal`.
-- The part of a maximal chain below `x.asIdeal` contributes `ringKrullDim (Localization.AtPrime
-- x.asIdeal)`, while the part above it is measured by the transcendence degree of
-- `x.asIdeal.ResidueField` over `k`.
/-- Lemma 10.116.3: for a point `x` of `X = Spec(S)`, where `S` is a finite type `k`-algebra and
`x.asIdeal` is the corresponding prime ideal `𝔭`, the local dimension `dim_x(X)` equals the Krull
dimension of the localization `S_𝔭` plus the transcendence degree of the residue field
`κ(𝔭) = x.asIdeal.ResidueField` over `k`. -/
theorem topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField
    (x : PrimeSpectrum S) :
    topologicalKrullDimAt x =
      ringKrullDim (Localization.AtPrime x.asIdeal) +
        Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := sorry

end

/-! ### Lemma_10_116_4 (from Chap10) -/
universe u v w

open TopologicalSpace

section

variable {k : Type u} [Field k]
variable {S' : Type v} [CommRing S'] [Algebra k S'] [Algebra.FiniteType k S']
variable {S : Type w} [CommRing S] [Algebra k S]

/- 
Domain-style sampling:
- primary domain: local Krull dimension on affine schemes of finite type over a field, compared
  along the prime-spectrum map induced by a surjective algebra homomorphism;
- sampled owner declarations of the same kind:
  `topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField`,
  `IsLocalization.AtPrime.ringKrullDim_eq_height`,
  `RingHom.strictMono_comap_of_surjective`,
  `RingHom.SurjectiveOnStalks.residueFieldMap_bijective`;
- best owner abstraction: the ambient owner remains `topologicalKrullDimAt`, while the
  localization-height and residue-field comparison data are already canonically owned upstream by
  `Localization.AtPrime`, `Ideal.height`, and `Ideal.ResidueField.mapₐ`;
- primitive data: the surjective `k`-algebra map `f : S' →ₐ[k] S`, its surjectivity witness `hf`,
  and the point `x : PrimeSpectrum S`;
- derived API: the local-dimension comparison formula, obtained by reusing the local dimension
  decomposition from Lemma `10.116.3`, the canonical height formula for localizations, and the
  canonical residue-field isomorphism induced by surjectivity on stalks.

Source/core/bridge triage:
* `source-facing`: the dimension comparison formula at corresponding points under a surjective
  morphism;
* `core/canonical`: `topologicalKrullDimAt`,
  `topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField`,
  `IsLocalization.AtPrime.ringKrullDim_eq_height`, and `Ideal.ResidueField.mapₐ`;
* `bridge/view`: the strict monotonicity of `PrimeSpectrum.comap` for surjective maps and the
  residue-field bijectivity theorem derived from `RingHom.surjectiveOnStalks_of_surjective`.
-/

-- Proof sketch: apply Lemma `10.116.3` to `x` and to its inverse-image
-- `PrimeSpectrum.comap f.toRingHom x`. For a surjective `k`-algebra map, the induced extension of
-- residue fields at corresponding primes is an isomorphism, so the transcendence-degree terms are
-- equal and cancel. The remaining terms are the heights of the corresponding prime ideals.
/-- Lemma 10.116.4: if `f : S' →ₐ[k] S` is a surjective morphism, where `S'` is a finite type
`k`-algebra, and `x : PrimeSpectrum S` corresponds to the prime ideal `𝔭 ⊂ S`, then for the
corresponding point `PrimeSpectrum.comap f.toRingHom x : PrimeSpectrum S'`, corresponding to
`𝔭' = Ideal.comap f.toRingHom 𝔭`, the local-dimension difference is the height difference.
Since local dimensions take values in `WithBot ℕ∞`, this is stated in the equivalent additive
form `dim_{x'}(Spec S') = dim_x(Spec S) + (height(𝔭') - height(𝔭))`. -/
theorem topologicalKrullDimAt_comap_eq_add_height_sub_of_surjective_of_finiteType_over_field
    (f : S' →ₐ[k] S) (hf : Function.Surjective f) (x : PrimeSpectrum S) :
    topologicalKrullDimAt (PrimeSpectrum.comap f.toRingHom x) =
      topologicalKrullDimAt x +
        (((PrimeSpectrum.comap f.toRingHom x).asIdeal.height - x.asIdeal.height : ℕ∞) :
          WithBot ℕ∞) := by
  letI : Algebra.FiniteType k S := Algebra.FiniteType.of_surjective f hf
  set x' : PrimeSpectrum S' := PrimeSpectrum.comap f.toRingHom x
  have htrdeg :
      Cardinal.toNat (Algebra.trdeg k x'.asIdeal.ResidueField) =
        Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := by
    let e : x'.asIdeal.ResidueField ≃ₐ[k] x.asIdeal.ResidueField :=
      AlgEquiv.ofBijective (Ideal.ResidueField.mapₐ x'.asIdeal x.asIdeal f rfl)
        ((RingHom.surjectiveOnStalks_of_surjective hf).residueFieldMap_bijective _ _ rfl)
    have htrdeg' := congrArg Cardinal.toNat (AlgEquiv.lift_trdeg_eq e)
    simpa [Cardinal.toNat_lift] using htrdeg'
  have hheight_le : x.asIdeal.height ≤ x'.asIdeal.height := by
    simpa [Ideal.height_eq_primeHeight, Ideal.primeHeight] using
      (Order.height_le_height_apply_of_strictMono
        (PrimeSpectrum.comap f.toRingHom)
        (RingHom.strictMono_comap_of_surjective hf)
        x)
  have hheight :
      ((x'.asIdeal.height : WithBot ℕ∞) : WithBot ℕ∞) =
        (x.asIdeal.height : WithBot ℕ∞) +
          (((x'.asIdeal.height - x.asIdeal.height : ℕ∞) : WithBot ℕ∞)) := by
    exact_mod_cast (add_tsub_cancel_of_le hheight_le).symm
  calc
    topologicalKrullDimAt (PrimeSpectrum.comap f.toRingHom x)
        = (x'.asIdeal.height : WithBot ℕ∞) +
            Cardinal.toNat (Algebra.trdeg k x'.asIdeal.ResidueField) := by
          rw [show topologicalKrullDimAt x' =
              ringKrullDim (Localization.AtPrime x'.asIdeal) +
                Cardinal.toNat (Algebra.trdeg k x'.asIdeal.ResidueField) from
            topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField
              x']
          rw [IsLocalization.AtPrime.ringKrullDim_eq_height x'.asIdeal
            (Localization.AtPrime x'.asIdeal)]
    _ = (x'.asIdeal.height : WithBot ℕ∞) +
          Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := by
          rw [htrdeg]
    _ =
        ((x.asIdeal.height : WithBot ℕ∞) +
          Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField)) +
            (((x'.asIdeal.height - x.asIdeal.height : ℕ∞) : WithBot ℕ∞)) := by
          rw [hheight]
          ac_rfl
    _ = topologicalKrullDimAt x +
          (((x'.asIdeal.height - x.asIdeal.height : ℕ∞) : WithBot ℕ∞)) := by
          rw [show topologicalKrullDimAt x =
              ringKrullDim (Localization.AtPrime x.asIdeal) +
                Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) from
            topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField
              x]
          rw [IsLocalization.AtPrime.ringKrullDim_eq_height x.asIdeal
            (Localization.AtPrime x.asIdeal)]

end

/-! ### Lemma_10_116_5 (from Chap10) -/
open scoped TensorProduct

universe u v w

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
variable {K : Type w} [Field K] [Algebra k K]

/-- Helper for Lemma 10.116.5: a finite injective map from a polynomial algebra over a field
computes the Krull dimension of the target. -/
private lemma ringKrullDim_eq_of_finite_injective_polynomial_algebra
    {F : Type*} [Field F] {A : Type*} [CommRing A] [Algebra F A] {d : ℕ}
    (g : MvPolynomial (Fin d) F →ₐ[F] A)
    (hg_injective : Function.Injective g) (hg_finite : AlgHom.Finite g) :
    ringKrullDim A = d := by
  let _ : Algebra (MvPolynomial (Fin d) F) A := g.toAlgebra
  -- A finite algebra map is integral, so the target has the same Krull dimension as the source.
  have hg_integral : (algebraMap (MvPolynomial (Fin d) F) A).IsIntegral := by
    simpa [RingHom.algebraMap_toAlgebra] using hg_finite.to_isIntegral
  let _ : Algebra.IsIntegral (MvPolynomial (Fin d) F) A :=
    algebraMap_isIntegral_iff.mp hg_integral
  have hdim :
      ringKrullDim (MvPolynomial (Fin d) F) = ringKrullDim A :=
    ringKrullDim_eq_of_injective_algebraMap_of_isIntegral
      (by simpa [RingHom.algebraMap_toAlgebra] using hg_injective)
  have hpoly : ringKrullDim (MvPolynomial (Fin d) F) = d := by
    -- Polynomial rings over fields have Krull dimension equal to the number of variables.
    simp
  exact hdim.symm.trans hpoly

/-- Helper for Lemma 10.116.5: tensoring a finite injective polynomial normalization map with a
field extension preserves injectivity after identifying the tensor source with a polynomial ring
over the larger field. -/
private lemma tensor_baseChange_polynomial_algHom_restrictScalars
    {d : ℕ} (g : MvPolynomial (Fin d) k →ₐ[k] S) :
    (AlgHom.restrictScalars k
      (MvPolynomial.aeval (R := K) (S₁ := K ⊗[k] S) fun i ↦ (1 : K) ⊗ₜ[k] g (MvPolynomial.X i) :
        MvPolynomial (Fin d) K →ₐ[K] K ⊗[k] S)) =
      (Algebra.TensorProduct.map (AlgHom.id k K) g).comp
        ((MvPolynomial.algebraTensorAlgEquiv k K).symm.toAlgHom.restrictScalars k) := by
  apply MvPolynomial.algHom_ext'
  · ext c
    -- Both maps send the coefficient field `K` to the left tensor factor.
    simp [MvPolynomial.algebraTensorAlgEquiv]
  · intro i
    -- On variables, the tensor/equivalence composite lands at `1 ⊗ g(X_i)`.
    simp

/-- Helper for Lemma 10.116.5: tensoring a finite injective polynomial normalization map with a
field extension preserves injectivity after identifying the tensor source with a polynomial ring
over the larger field. -/
private lemma tensor_baseChange_polynomial_algHom_injective
    {d : ℕ} (g : MvPolynomial (Fin d) k →ₐ[k] S) (hg_injective : Function.Injective g) :
    Function.Injective
      (MvPolynomial.aeval (R := K) (S₁ := K ⊗[k] S) fun i ↦ (1 : K) ⊗ₜ[k] g (MvPolynomial.X i) :
        MvPolynomial (Fin d) K →ₐ[K] K ⊗[k] S) := by
  have hraw :
      Function.Injective
        ((Algebra.TensorProduct.map (AlgHom.id k K) g).comp
          ((MvPolynomial.algebraTensorAlgEquiv k K).symm.toAlgHom.restrictScalars k) :
            MvPolynomial (Fin d) K →ₐ[k] K ⊗[k] S) := by
    have hmap :
        Function.Injective
          (Algebra.TensorProduct.map (AlgHom.id k K) g :
            K ⊗[k] MvPolynomial (Fin d) k →ₐ[k] K ⊗[k] S) := by
      -- Over a field, tensoring with `K` preserves injectivity of the normalization map.
      simpa using TensorProduct.map_injective_of_flat_flat
        (AlgHom.id k K).toLinearMap g.toLinearMap
        Function.injective_id hg_injective
    exact hmap.comp (MvPolynomial.algebraTensorAlgEquiv k K).symm.injective
  have hrestricted :
      Function.Injective
        ((AlgHom.restrictScalars k
          (MvPolynomial.aeval (R := K) (S₁ := K ⊗[k] S) fun i ↦ (1 : K) ⊗ₜ[k] g (MvPolynomial.X i) :
            MvPolynomial (Fin d) K →ₐ[K] K ⊗[k] S)) :
          MvPolynomial (Fin d) K →ₐ[k] K ⊗[k] S) := by
    simpa [tensor_baseChange_polynomial_algHom_restrictScalars (K := K) g] using hraw
  simpa using hrestricted

/-- Helper for Lemma 10.116.5: tensoring a finite polynomial normalization map with a field
extension preserves finiteness after identifying the tensor source with a polynomial ring over the
larger field. -/
private lemma tensor_baseChange_polynomial_algHom_finite
    {d : ℕ} (g : MvPolynomial (Fin d) k →ₐ[k] S) (hg_finite : AlgHom.Finite g) :
    AlgHom.Finite
      (MvPolynomial.aeval (R := K) (S₁ := K ⊗[k] S) fun i ↦ (1 : K) ⊗ₜ[k] g (MvPolynomial.X i) :
        MvPolynomial (Fin d) K →ₐ[K] K ⊗[k] S) := by
  have hraw :
      AlgHom.Finite
        ((Algebra.TensorProduct.map (AlgHom.id k K) g).comp
          ((MvPolynomial.algebraTensorAlgEquiv k K).symm.toAlgHom.restrictScalars k) :
            MvPolynomial (Fin d) K →ₐ[k] K ⊗[k] S) := by
    have hmap :
        AlgHom.Finite
          (Algebra.TensorProduct.map (AlgHom.id k K) g :
            K ⊗[k] MvPolynomial (Fin d) k →ₐ[k] K ⊗[k] S) := by
      -- Finiteness is stable under tensor base change along the field extension.
      simpa using RingHom.Finite.tensorProductMap
        (f := AlgHom.id k K) (g := g) (AlgHom.Finite.id k K) hg_finite
    have hequiv :
        AlgHom.Finite
          (((MvPolynomial.algebraTensorAlgEquiv k K).symm.toAlgHom).restrictScalars k :
            MvPolynomial (Fin d) K →ₐ[k] K ⊗[k] MvPolynomial (Fin d) k) := by
      -- An algebra equivalence is finite, so precomposing with the polynomial/tensor equivalence
      -- keeps the normalization finite.
      simpa using RingEquiv.finite (MvPolynomial.algebraTensorAlgEquiv k K).symm.toRingEquiv
    exact AlgHom.Finite.comp hmap hequiv
  have hrestricted :
      AlgHom.Finite
        (AlgHom.restrictScalars k
          (MvPolynomial.aeval (R := K) (S₁ := K ⊗[k] S) fun i ↦ (1 : K) ⊗ₜ[k] g (MvPolynomial.X i) :
            MvPolynomial (Fin d) K →ₐ[K] K ⊗[k] S)) := by
    simpa [tensor_baseChange_polynomial_algHom_restrictScalars (K := K) g] using hraw
  simpa using hrestricted

/-
Source/core/bridge triage:
* primary domain: Krull dimension of finite-type algebras over a field under scalar extension;
* sampled owner API:
  `exists_finite_inj_algHom_of_fg` from mathlib's Noether-normalization file,
  `ringKrullDim_quotient_mvPolynomial_eq_of_finite_injective_polynomial_algebra` from
    Lemma `10.115.4`,
  `ringKrullDim_eq_of_injective_algebraMap_of_isIntegral` from Lemma `10.112.4`,
  `primeSpectrumTopologicalKrullDimAt_eq_of_tensorProduct_fieldExtension` from Lemma `10.116.6`;
* layer: `bridge/view`, since the source-facing statement is a global equality for `ringKrullDim`,
  while the owner-level content lives in Noether normalization, integral invariance of Krull
  dimension, and the local topological-dimension comparison under field extension;
* primitive data vs derived API: no additional public data are primitive here beyond the field
  extension `k → K` and the finite-type `k`-algebra `S`. The equality itself is derived API and
  should remain a thin theorem rather than a new wrapper or packaged construction.
-/

-- Proof sketch: apply Noether normalization to the finite type `k`-algebra `S` to get a finite
-- injective map from a polynomial ring `k[y₁, …, y_d]` with `d = ringKrullDim S`. Base change this
-- map along `k → K` to obtain a finite injective map `K[y₁, …, y_d] → K ⊗[k] S`, then use the
-- polynomial-ring dimension computation over a field together with invariance of Krull dimension
-- under finite injective integral extensions.
/-- Lemma 10.116.5: if `S` is a finite type `k`-algebra and `K / k` is a field extension, then the
Krull dimension of `S` equals the Krull dimension of the base change `K ⊗[k] S`. -/
theorem ringKrullDim_tensorProduct_eq_of_fieldExtension :
    ringKrullDim S = ringKrullDim (K ⊗[k] S) := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · haveI := hS
    haveI : Subsingleton (K ⊗[k] S) := inferInstance
    rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_bot_of_subsingleton]
  · haveI := hS
    obtain ⟨d, g, hg_injective, hg_finite⟩ := exists_finite_inj_algHom_of_fg k S
    let gK : MvPolynomial (Fin d) K →ₐ[K] K ⊗[k] S :=
      MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] g (MvPolynomial.X i)
    have hSdim : ringKrullDim S = d :=
      ringKrullDim_eq_of_finite_injective_polynomial_algebra g hg_injective hg_finite
    have hgK_injective : Function.Injective gK := by
      -- Base change along the field extension preserves injectivity of the normalization map.
      simpa [gK] using tensor_baseChange_polynomial_algHom_injective (K := K) g hg_injective
    have hgK_finite : AlgHom.Finite gK := by
      -- The same base change also preserves finiteness of the normalization map.
      simpa [gK] using tensor_baseChange_polynomial_algHom_finite (K := K) g hg_finite
    have hKdim : ringKrullDim (K ⊗[k] S) = d :=
      ringKrullDim_eq_of_finite_injective_polynomial_algebra gK hgK_injective hgK_finite
    exact hSdim.trans hKdim.symm

end

/-! ### Lemma_10_116_6 (from Chap10) -/
open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {S : Type w} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

local notation "S_K" => K ⊗[k] S
local notation "iSK" => (((includeRight : S →ₐ[k] S_K) : S →+* S_K))

/- 
Domain-style sampling:
- primary domain: local Krull dimension on `Spec(S)` for finite type algebras over a field, under
  tensor base change along a field extension;
- sampled owner declarations of the same kind:
  `topologicalKrullDimAt`,
  `topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField`,
  `ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown`,
  `topologicalKrullDimAt_comap_eq_add_height_sub_of_surjective_of_finiteType_over_field`;
- best owner abstraction: the source-facing theorem should remain an equality between the canonical
  local-dimension owner values `topologicalKrullDimAt x` and `topologicalKrullDimAt xK`, while the
  supporting local-ring/fiber calculations are already owned upstream by `Localization.AtPrime`,
  `fiberLocalRingAt`, and the dimension formulas in Lemmas `10.112.7`, `10.116.3`, and `10.116.4`;
- primitive data: only the point `x : PrimeSpectrum S`, the point `xK : PrimeSpectrum S_K`, and
  the canonical contraction witness `hxK : PrimeSpectrum.comap iSK xK = x`;
- derived API: any quotient-presentation or localization comparison used in the proof. No extra
  public wrapper or duplicate local owner should be introduced here.

Source/core/bridge triage:
* `source-facing`: the invariance of `topologicalKrullDimAt` under tensoring a finite type
  `k`-algebra with a field extension `K / k`;
* `core/canonical`: `topologicalKrullDimAt`, `Localization.AtPrime`, `fiberLocalRingAt`, and the
  local dimension formulas from Lemmas `10.112.7`, `10.116.3`, and `10.116.4`;
* `bridge/view`: the tensor base-change morphism `iSK` and the induced prime-spectrum contraction
  equation `PrimeSpectrum.comap iSK xK = x`.
-/

-- Proof sketch: present `S` as a quotient of a polynomial ring over `k`, base change that
-- presentation to `K`, and compare the height differences given by Lemma `10.112.7` for the two
-- vertical flat maps in the resulting square of local rings. Then use the local-dimension formula
-- from Lemma `10.116.4` for the quotient presentations upstairs and downstairs to cancel the same
-- ambient polynomial-ring dimension.
/-- Lemma 10.116.6: if `S` is a finite type `k`-algebra, `x : Spec(S)` corresponds to a prime of
`S`, and `xK : Spec(K ⊗[k] S)` corresponds to a prime of `K ⊗[k] S` lying over `x`, then the
local topological Krull dimensions at `x` and `xK` are equal. -/
lemma primeSpectrumTopologicalKrullDimAt_eq_of_tensorProduct_fieldExtension
    (x : PrimeSpectrum S) (xK : PrimeSpectrum S_K) (hxK : PrimeSpectrum.comap iSK xK = x) :
    topologicalKrullDimAt x = topologicalKrullDimAt xK := sorry

end

/-! ### Lemma_10_116_7 (from Chap10) -/
open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {S : Type w} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

local notation "S_K" => K ⊗[k] S
local notation "iSK" => (((includeRight : S →ₐ[k] S_K) : S →+* S_K))

/-
Domain-style sampling:
- primary domain: relative fiber dimension for finite type algebras over a field, under tensor base
  change along a field extension;
- sampled owner declarations of the same kind:
  `relativeDimensionAt`,
  `fiberLocalRingAt`,
  `topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField`,
  `ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown`;
- best owner abstraction: the source-facing fiber-dimension quantity is already owned in this
  chapter by `relativeDimensionAt`; the ring `fiberLocalRingAt` is primitive supporting data, not
  the public dimension owner;
- primitive data: the points `x : PrimeSpectrum S`, `xK : PrimeSpectrum S_K`, and the contraction
  witness `hxK : PrimeSpectrum.comap iSK xK = x`;
- derived API: the additive identities comparing `relativeDimensionAt S S_K xK` with local-ring
  dimensions and residue-field transcendence degrees.

Source/core/bridge triage:
* `source-facing`: the fiber-dimension formulas and zero-dimensional fiber point over `x`;
* `core/canonical`: `relativeDimensionAt`, together with the supporting owners
  `Localization.AtPrime`, `fiberLocalRingAt`, and the Chapter 10 local-dimension formulas;
* `bridge/view`: the tensor base-change map `iSK` and the lies-over equation
  `PrimeSpectrum.comap iSK xK = x`.
-/

-- Proof sketch: localize the flat base-change map `S → S_K` at `x` and `xK`, then apply the
-- flat-local dimension formula from Lemma `10.112.7` to identify the dimension of the localized
-- special fiber with the difference between the dimensions of `(S_K)_{xK}` and `S_x`. Since the
-- project records Krull dimensions in `WithBot ℕ∞`, this is stated in the equivalent additive
-- form.
/-- Lemma 10.116.7 (1): for a finite type `k`-algebra `S`, a field extension `K / k`, a point
`x : Spec(S)`, and a point `xK : Spec(K ⊗[k] S)` lying over `x`, the relative dimension of
`S_K / S` at `xK`, plus the dimension of `S_x`, equals the dimension of `(K ⊗[k] S)_{xK}`. -/
lemma relativeDimensionAt_add_ringKrullDim_localizationAtPrime_eq_of_tensorProduct_fieldExtension
    (x : PrimeSpectrum S) (xK : PrimeSpectrum S_K) (hxK : PrimeSpectrum.comap iSK xK = x) :
    relativeDimensionAt S S_K xK + ringKrullDim (Localization.AtPrime x.asIdeal) =
      ringKrullDim (Localization.AtPrime xK.asIdeal) := sorry

-- Proof sketch: combine Lemma `10.116.6`, which identifies the local dimensions of `Spec(S)` and
-- `Spec(S_K)` at corresponding points, with Lemma `10.116.3`, which expresses those local
-- dimensions as `dim S_x + trdeg_k κ(x)` and `dim (S_K)_{xK} + trdeg_K κ(xK)`. Cancelling the
-- local-dimension terms gives the transcendence-degree formula for the fiber dimension, again
-- written in additive form because the dimension values lie in `WithBot ℕ∞`.
/-- Lemma 10.116.7 (2): for a finite type `k`-algebra `S`, a field extension `K / k`, a point
`x : Spec(S)`, and a point `xK : Spec(K ⊗[k] S)` lying over `x`, the relative dimension of
`S_K / S` at `xK`, plus the transcendence degree of `κ(xK)` over `K`, equals the
transcendence degree of `κ(x)` over `k`. -/
lemma relativeDimensionAt_add_trdeg_residueField_eq_of_tensorProduct_fieldExtension
    (x : PrimeSpectrum S) (xK : PrimeSpectrum S_K) (hxK : PrimeSpectrum.comap iSK xK = x) :
    relativeDimensionAt S S_K xK + Cardinal.toNat (Algebra.trdeg K xK.asIdeal.ResidueField) =
      Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := sorry

-- Proof sketch: choose a prime of `S_K` minimal over the extended prime `x.asIdeal • ⊤`; such a
-- point lies over `x`, and the corresponding fiber local ring is zero-dimensional because a
-- minimal prime of the fiber has Krull dimension `0`.
/-- Lemma 10.116.7 (3): for every point `x : Spec(S)`, one can choose a point of
`Spec(K ⊗[k] S)` lying over `x` whose relative dimension is `0`. -/
lemma exists_primeSpectrum_tensorProduct_fieldExtension_with_relativeDimensionAt_eq_zero
    (x : PrimeSpectrum S) :
    ∃ xK : PrimeSpectrum S_K,
      PrimeSpectrum.comap iSK xK = x ∧ relativeDimensionAt S S_K xK = 0 := sorry

end
