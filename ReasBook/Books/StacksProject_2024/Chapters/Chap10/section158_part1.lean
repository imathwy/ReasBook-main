import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.Recall
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_158_1 (from Chap10) -/
universe u v

namespace Algebra

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
variable [Algebra.EssFiniteType k K]

/- Domain-style sampling for Lemma 10.158.1:
- primary domain: finitely generated field extensions and the owner predicates
  `FormallyUnramified`, `Unramified`, `FormallyEtale`, and `Etale`;
- sampled owner declarations:
  `Algebra.formallyUnramified_iff`,
  `Algebra.FormallyUnramified.iff_isSeparable`,
  `Algebra.Unramified`,
  `Algebra.Etale.of_formallyUnramified_of_flat`;
- best owner abstraction: `Algebra.FormallyUnramified k K`, since over an essentially finite type
  field extension it canonically recovers separability, finite-dimensionality, and the finite-type
  or finitely presented hypotheses needed for the unramified and étale owners;
- primitive data: only the field extension `K / k` with `[Algebra.EssFiniteType k K]`;
- derived API: the six source-facing clauses of the `List.TFAE`.

Source/core/bridge triage:
- `source-facing`: the six-way TFAE matching the textbook lemma;
- `core/canonical`: the owner predicates above, especially `Algebra.FormallyUnramified k K`;
- `bridge/view`: the Kähler-differential reformulation
  `Algebra.formallyUnramified_iff` and the finite-generation upgrades from the field case.
-/

private theorem finiteDimensional_and_isSeparable_of_formallyUnramified
    [Algebra.FormallyUnramified k K] :
    FiniteDimensional k K ∧ Algebra.IsSeparable k K := by
  let _ : Module.Finite k K := Algebra.FormallyUnramified.finite_of_free k K
  let _ : FiniteDimensional k K :=
    (Module.Free.chooseBasis k K).finiteDimensional_of_finite
  exact
    ⟨inferInstance, (Algebra.FormallyUnramified.iff_isSeparable k K).mp inferInstance⟩

/-- Lemma 10.158.1: for a finitely generated field extension `K / k`, the following are
equivalent: `K / k` is a finite separable field extension, `Ω[K⁄k] = 0`, `K` is formally
unramified over `k`, `K` is unramified over `k`, `K` is formally étale over `k`, and `K` is étale
over `k`. In Lean, `Ω[K⁄k] = 0` is expressed as `Subsingleton Ω[K⁄k]`, and finite separability as
`FiniteDimensional k K ∧ Algebra.IsSeparable k K`. -/
theorem finite_separable_field_extension_tfae_subsingleton_kaehler_formallyUnramified_unramified_formallyEtale_etale :
    List.TFAE [
      FiniteDimensional k K ∧ Algebra.IsSeparable k K,
      Subsingleton Ω[K⁄k],
      Algebra.FormallyUnramified k K,
      Algebra.Unramified k K,
      Algebra.FormallyEtale k K,
      Algebra.Etale k K
    ] := by
  tfae_have 1 ↔ 3 := by
    constructor
    · rintro ⟨_, _⟩
      exact Algebra.FormallyUnramified.of_isSeparable k K
    · intro _
      exact finiteDimensional_and_isSeparable_of_formallyUnramified
  tfae_have 2 ↔ 3 := (Algebra.formallyUnramified_iff k K).symm
  tfae_have 3 → 4 := by
    intro _
    let _ : Module.Finite k K := Algebra.FormallyUnramified.finite_of_free k K
    let _ : Algebra.FiniteType k K := inferInstance
    exact Algebra.Unramified.mk
  tfae_have 4 → 3 := by
    intro _
    infer_instance
  tfae_have 3 → 6 := by
    intro _
    let _ : Module.Finite k K := Algebra.FormallyUnramified.finite_of_free k K
    let _ : Module.FinitePresentation k K := Module.finitePresentation_of_finite k K
    let _ : Algebra.FinitePresentation k K := Algebra.FinitePresentation.of_finitePresentation k K
    exact Algebra.Etale.of_formallyUnramified_of_flat
  tfae_have 6 → 5 := by
    intro _
    infer_instance
  tfae_have 5 → 3 := by
    intro _
    infer_instance
  tfae_finish

end

end Algebra

/-! ### Lemma_10_158_2 (from Chap10) -/
universe u v

section

variable {k : Type u} {K : Type v} [Field k] [PerfectField k] [Field K] [Algebra k K]
variable {p : ℕ} [Fact p.Prime] [CharP k p]

/-- Helper for Lemma 10.158.2: one explicit presentation datum for the generators of
`KaehlerDifferential.kerTotal`. -/
private inductive KerTotalRelationData (k : Type u) (S : Type v)
    [Field k] [Field S] [Algebra k S] where
  | add (x y : S)
  | mul (x y : S)
  | alg (r : k)

namespace KerTotalRelationData

variable {S : Type v} [Field S] [Algebra k S]

/-- Helper for Lemma 10.158.2: the finitely supported relation attached to one presentation
generator of `KaehlerDifferential.kerTotal`. -/
noncomputable def toFinsupp : KerTotalRelationData k S → S →₀ S
  | .add x y => Finsupp.single x 1 + Finsupp.single y 1 - Finsupp.single (x + y) 1
  | .mul x y => Finsupp.single y x + Finsupp.single x y - Finsupp.single (x * y) 1
  | .alg r => Finsupp.single (algebraMap k S r) 1

end KerTotalRelationData

/-- Helper for Lemma 10.158.2: the explicit generator set whose span is
`KaehlerDifferential.kerTotal`. -/
private def kerTotalGenerators (k : Type u) (S : Type v)
    [Field k] [Field S] [Algebra k S] : Set (S →₀ S) :=
  Set.range (KerTotalRelationData.toFinsupp (k := k) (S := S))

/-- Helper for Lemma 10.158.2: rewriting `KaehlerDifferential.kerTotal` as the span of the
explicit relation datatype keeps the finite-support descent argument readable. -/
private theorem kerTotal_eq_span_generators
    {S : Type v} [Field S] [Algebra k S] :
    KaehlerDifferential.kerTotal k S = Submodule.span S (kerTotalGenerators k S) := by
  -- The two descriptions list the same additive, multiplicative, and base-field generators.
  rw [KaehlerDifferential.kerTotal, kerTotalGenerators]
  congr 1
  ext t
  constructor
  · intro ht
    rcases ht with ((⟨⟨x, y⟩, rfl⟩ | ⟨⟨x, y⟩, rfl⟩) | ⟨r, rfl⟩)
    · exact ⟨.add x y, rfl⟩
    · exact ⟨.mul x y, rfl⟩
    · exact ⟨.alg r, rfl⟩
  · rintro ⟨d, rfl⟩
    cases d <;> simp [KerTotalRelationData.toFinsupp]

/-- Helper for Lemma 10.158.2: the set of field elements appearing in one explicit presentation
relation. -/
private def relationCarrierSet {S : Type v} [Field S] [Algebra k S] :
    KerTotalRelationData k S → Set S
  | .add x y => {x, y}
  | .mul x y => {x, y}
  | .alg _ => ∅

/-- Helper for Lemma 10.158.2: each explicit relation only involves finitely many field elements. -/
private theorem relationCarrierSet_finite {S : Type v} [Field S] [Algebra k S]
    (d : KerTotalRelationData k S) :
    (relationCarrierSet (k := k) d).Finite := by
  cases d <;> simp [relationCarrierSet]

/-- Helper for Lemma 10.158.2: a finitely supported function on an intermediate field embeds into
the ambient finitely supported function by applying the inclusion on both indices and values. -/
private noncomputable def intermediateFieldFinsuppLift
    (L : IntermediateField k K) : (L →₀ L) →ₗ[L] (K →₀ K) :=
  (Finsupp.mapRange.linearMap (Algebra.linearMap L K)).comp
    (Finsupp.lmapDomain L L (fun x : L ↦ (x : K)))

/-- Helper for Lemma 10.158.2: the ambient embedding sends a singleton in the intermediate-field
presentation to the corresponding singleton upstairs. -/
private theorem intermediateFieldFinsuppLift_single
    (L : IntermediateField k K) (x : L) (c : L) :
    intermediateFieldFinsuppLift (k := k) (K := K) L (Finsupp.single x c) =
      Finsupp.single (x : K) (c : K) := by
  -- Both `mapDomain` and `mapRange` preserve singleton generators.
  simp [intermediateFieldFinsuppLift]

/-- Helper for Lemma 10.158.2: the ambient embedding is injective because both the support index
map and the coefficient map are injective. -/
private theorem intermediateFieldFinsuppLift_injective
    (L : IntermediateField k K) :
    Function.Injective (intermediateFieldFinsuppLift (k := k) (K := K) L) := by
  intro f g hfg
  ext x
  have hx :
      algebraMap L K (f x) = algebraMap L K (g x) := by
    -- Evaluate the equality of embedded finitely supported functions at the index `x`.
    simpa [intermediateFieldFinsuppLift] using
      congrArg (fun h : K →₀ K ↦ h (x : K)) hfg
  exact congrArg Subtype.val ((algebraMap L K).injective hx)

/-- Helper for Lemma 10.158.2: if all field elements occurring in one explicit relation already
lie in an intermediate field, then that relation has a lifted copy there. -/
private theorem exists_liftRelationData
    (L : IntermediateField k K) (d : KerTotalRelationData k K)
    (hd : ∀ x ∈ relationCarrierSet (k := k) d, x ∈ L) :
    ∃ dL : KerTotalRelationData k L,
      intermediateFieldFinsuppLift (k := k) (K := K) L
          (KerTotalRelationData.toFinsupp (k := k) (S := L) dL) =
        KerTotalRelationData.toFinsupp (k := k) (S := K) d := by
  cases d with
  | add x y =>
      refine ⟨.add ⟨x, hd x (by simp [relationCarrierSet])⟩
          ⟨y, hd y (by simp [relationCarrierSet])⟩, ?_⟩
      -- The lifted additive relation maps back to the original additive relation.
      simp [KerTotalRelationData.toFinsupp, intermediateFieldFinsuppLift_single]
  | mul x y =>
      refine ⟨.mul ⟨x, hd x (by simp [relationCarrierSet])⟩
          ⟨y, hd y (by simp [relationCarrierSet])⟩, ?_⟩
      -- The lifted multiplicative relation maps back to the original multiplicative relation.
      simp [KerTotalRelationData.toFinsupp, intermediateFieldFinsuppLift_single]
  | alg r =>
      refine ⟨.alg r, ?_⟩
      -- Base-field relations are already defined over every intermediate field.
      simp [KerTotalRelationData.toFinsupp, intermediateFieldFinsuppLift_single]

/-- Helper for Lemma 10.158.2: choose one lifted relation datum in the intermediate field. -/
private noncomputable def liftRelationData
    (L : IntermediateField k K) (d : KerTotalRelationData k K)
    (hd : ∀ x ∈ relationCarrierSet (k := k) d, x ∈ L) :
    KerTotalRelationData k L :=
  Classical.choose (exists_liftRelationData (k := k) (K := K) L d hd)

/-- Helper for Lemma 10.158.2: the chosen lifted relation datum maps back to the original
relation generator in the ambient field. -/
private theorem liftRelationData_spec
    (L : IntermediateField k K) (d : KerTotalRelationData k K)
    (hd : ∀ x ∈ relationCarrierSet (k := k) d, x ∈ L) :
    intermediateFieldFinsuppLift (k := k) (K := K) L
        (KerTotalRelationData.toFinsupp (k := k) (S := L)
          (liftRelationData (k := k) (K := K) L d hd)) =
      KerTotalRelationData.toFinsupp (k := k) (S := K) d :=
  Classical.choose_spec (exists_liftRelationData (k := k) (K := K) L d hd)

/-- Helper for Lemma 10.158.2: if `D a = 0` in `Ω[K⁄k]`, then the finite presentation witness for
that vanishing already lives in a finitely generated intermediate field. -/
private theorem exists_fg_intermediateField_of_D_eq_zero (a : K)
    (ha : KaehlerDifferential.D k K a = 0) :
    ∃ (L : IntermediateField k K) (_ : L.FG) (haL : a ∈ L),
      KaehlerDifferential.D k L ⟨a, haL⟩ = 0 := by
  classical
  -- The quotient presentation identifies `D a` with the class of the singleton generator.
  have hquot :
      (KaehlerDifferential.quotKerTotalEquiv k K).symm (KaehlerDifferential.D k K a) =
        Submodule.mkQ (KaehlerDifferential.kerTotal k K) (Finsupp.single a (1 : K)) := by
    simpa [KaehlerDifferential.derivationQuotKerTotal_apply] using
      Derivation.congr_fun
        (KaehlerDifferential.quotKerTotalEquiv_symm_comp_D (R := k) (S := K)) a
  have hsingle_mem_ker : Finsupp.single a (1 : K) ∈ KaehlerDifferential.kerTotal k K := by
    have hsingle_zero :
        Submodule.mkQ (KaehlerDifferential.kerTotal k K) (Finsupp.single a (1 : K)) = 0 := by
      -- Vanishing of `D a` means the singleton class is zero in the quotient presentation.
      rw [← hquot, ha, map_zero]
    exact (Submodule.Quotient.mk_eq_zero _).1 hsingle_zero
  have hsingle_mem_span :
      Finsupp.single a (1 : K) ∈ Submodule.span K (kerTotalGenerators k K) := by
    rw [← kerTotal_eq_span_generators]
    exact hsingle_mem_ker
  obtain ⟨T, hTsubset, hsingle_mem_span_T⟩ :=
    Submodule.mem_span_finite_of_mem_span hsingle_mem_span
  obtain ⟨coeff, hcoeffT, hsumK⟩ := (Submodule.mem_span_finset).1 hsingle_mem_span_T
  let relationData : ↥T → KerTotalRelationData k K := fun t ↦
    Classical.choose (hTsubset t.2)
  have hrelationData :
      ∀ t : ↥T,
        KerTotalRelationData.toFinsupp (k := k) (S := K) (relationData t) = t.1 := by
    intro t
    exact Classical.choose_spec (hTsubset t.2)
  let relationCarrier : ↥T → Finset K := fun t ↦
    (relationCarrierSet_finite (k := k) (relationData t)).toFinset
  let S : Finset K :=
    insert a (T.image coeff ∪ T.attach.biUnion
      relationCarrier)
  let L : IntermediateField k K := IntermediateField.adjoin k (S : Set K)
  have hLfg : L.FG := by
    -- The chosen carrier set is finite by construction, so its adjoin is finitely generated.
    simpa [L, S] using IntermediateField.fg_adjoin_finset (F := k) S
  have haL : a ∈ L := by
    -- The distinguished element `a` was inserted into the finite carrier set.
    exact IntermediateField.subset_adjoin (F := k) (S := (S : Set K)) (by simp [S])
  have hcoeff_mem_L : ∀ t : ↥T, coeff t.1 ∈ L := by
    intro t
    -- Every coefficient used in the finite linear combination was inserted into the carrier set.
    exact IntermediateField.subset_adjoin (F := k) (S := (S : Set K)) (by
      simp [S]
      exact Or.inr <| Or.inl <| ⟨t.1, t.2, rfl⟩)
  have hcarrier_mem_L :
      ∀ t : ↥T, ∀ x ∈ relationCarrierSet (k := k) (relationData t), x ∈ L := by
    intro t x hx
    -- Every field element appearing in one chosen relation generator was inserted into the carrier.
    exact IntermediateField.subset_adjoin (F := k) (S := (S : Set K)) (by
      simp [S]
      refine Or.inr <| Or.inr <| ?_
      refine ⟨t.1, t.2, ?_⟩
      exact (Set.Finite.mem_toFinset (relationCarrierSet_finite (k := k) (relationData t))).2 hx)
  let coeffL : ↥T → L := fun t ↦ ⟨coeff t.1, hcoeff_mem_L t⟩
  let relationDataL : ↥T → KerTotalRelationData k L := fun t ↦
    liftRelationData (k := k) (K := K) L (relationData t) (hcarrier_mem_L t)
  have hsingle_image :
      intermediateFieldFinsuppLift (k := k) (K := K) L
          (Finsupp.single ⟨a, haL⟩ (1 : L)) =
        Finsupp.single a (1 : K) := by
    -- The ambient embedding sends the descended singleton back to the original singleton.
    simp [intermediateFieldFinsuppLift_single]
  have hsum_image :
      intermediateFieldFinsuppLift (k := k) (K := K) L
          (Finset.sum T.attach fun t ↦
            coeffL t • KerTotalRelationData.toFinsupp (k := k) (S := L) (relationDataL t)) =
        Finsupp.single a (1 : K) := by
    -- Mapping the descended finite linear combination to `K` recovers the original witness.
    calc
      intermediateFieldFinsuppLift (k := k) (K := K) L
          (Finset.sum T.attach fun t ↦
            coeffL t • KerTotalRelationData.toFinsupp (k := k) (S := L) (relationDataL t)) =
        Finset.sum T.attach (fun t ↦
          intermediateFieldFinsuppLift (k := k) (K := K) L
            (coeffL t • KerTotalRelationData.toFinsupp (k := k) (S := L) (relationDataL t))) := by
              simp
      _ = Finset.sum T.attach (fun t ↦ (coeff t.1 : K) • t.1) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            rw [map_smul]
            -- Each lifted generator maps back to the original chosen generator.
            simpa [coeffL, relationDataL, hrelationData t] using
              congrArg (fun z : K →₀ K ↦ (coeff t.1 : K) • z)
                (liftRelationData_spec (k := k) (K := K) L (relationData t) (hcarrier_mem_L t))
      _ = Finset.sum T fun t ↦ coeff t • t := by
            simpa using (Finset.sum_attach T fun t ↦ coeff t • t)
      _ = Finsupp.single a (1 : K) := hsumK
  have hsumL :
      Finset.sum T.attach (fun t ↦
        coeffL t • KerTotalRelationData.toFinsupp (k := k) (S := L) (relationDataL t)) =
      Finsupp.single ⟨a, haL⟩ (1 : L) := by
    -- The ambient embedding is injective, so equality can be checked after mapping to `K`.
    apply intermediateFieldFinsuppLift_injective (k := k) (K := K) L
    rw [hsum_image, hsingle_image]
  have hsingle_mem_ker_L :
      Finsupp.single ⟨a, haL⟩ (1 : L) ∈ KaehlerDifferential.kerTotal k L := by
    rw [kerTotal_eq_span_generators]
    -- The descended singleton is the same finite linear combination of lifted generators.
    rw [← hsumL]
    have hsum_mem :
        Finset.sum T.attach (fun t ↦
          coeffL t • KerTotalRelationData.toFinsupp (k := k) (S := L) (relationDataL t)) ∈
          Submodule.span L (kerTotalGenerators k L) := by
      exact Submodule.sum_mem _ fun t ht ↦
        Submodule.smul_mem _ _ <| Submodule.subset_span ⟨relationDataL t, rfl⟩
    exact hsum_mem
  have hquotL :
      (KaehlerDifferential.quotKerTotalEquiv k L).symm (KaehlerDifferential.D k L ⟨a, haL⟩) =
        Submodule.mkQ (KaehlerDifferential.kerTotal k L)
          (Finsupp.single ⟨a, haL⟩ (1 : L)) := by
    simpa [KaehlerDifferential.derivationQuotKerTotal_apply] using
      Derivation.congr_fun
        (KaehlerDifferential.quotKerTotalEquiv_symm_comp_D (R := k) (S := L)) ⟨a, haL⟩
  have hsingle_zero_L :
      Submodule.mkQ (KaehlerDifferential.kerTotal k L)
        (Finsupp.single ⟨a, haL⟩ (1 : L)) = 0 := by
    exact (Submodule.Quotient.mk_eq_zero _).2 hsingle_mem_ker_L
  have haLzero : KaehlerDifferential.D k L ⟨a, haL⟩ = 0 := by
    -- The quotient presentation again converts kernel membership into vanishing of the differential.
    apply (KaehlerDifferential.quotKerTotalEquiv k L).symm.injective
    rw [hquotL, hsingle_zero_L, map_zero]
  exact ⟨L, hLfg, haL, haLzero⟩

/-- Helper for Lemma 10.158.2: a finitely generated extension of a perfect field admits a finite
separating transcendence basis, and the top field is finite-dimensional over the generated basis
field. -/
private theorem exists_fin_separating_transcendence_basis
    {L : Type v} [Field L] [Algebra k L] [Algebra.EssFiniteType k L] :
    ∃ r : ℕ, ∃ x : Fin r → L,
      IsTranscendenceBasis k x ∧
        Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) L ∧
        FiniteDimensional (IntermediateField.adjoin k (Set.range x)) L := by
  -- Start from the separating transcendence basis available over a perfect base field.
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k L
  -- Reindex the basis by a finite `Fin` type so the later rational-function step has the source
  -- shape `k(x₁, …, x_r)`.
  obtain ⟨x, hx, hx_adjoin⟩ := exists_fin_reindexed_transcendence_basis (k := k) (K := L) hs
  refine ⟨Cardinal.toNat (Algebra.trdeg k L), x, hx, ?_, ?_⟩
  · -- Reindexing does not change the generated basis field, so separability is preserved.
    rw [hx_adjoin]
    exact hsep
  · -- Finite generation upgrades algebraicity over the basis field to finite-dimensionality.
    simpa using finiteDimensional_over_adjoin_of_isTranscendenceBasis (k := k) (K := L) hx

/-- Helper for Lemma 10.158.2: over the basis field generated by a finite transcendence basis,
vanishing of the universal differential should force an element to be a `p`th power. -/
private theorem D_eq_zero_iff_of_algEquiv
    {A : Type*} {B : Type*} [Field A] [Field B] [Algebra k A] [Algebra k B]
    (e : A ≃ₐ[k] B) (a : A) :
    KaehlerDifferential.D k A a = 0 ↔ KaehlerDifferential.D k B (e a) = 0 := by
  constructor
  · intro ha
    letI : Algebra A B := e.toAlgHom.toAlgebra
    -- Apply the functoriality of Kähler differentials along the algebra equivalence.
    simpa using congrArg (KaehlerDifferential.map k k A B) ha
  · intro ha
    letI : Algebra B A := e.symm.toAlgHom.toAlgebra
    -- The inverse algebra equivalence transports the vanishing back to the source field.
    have hmap :
        KaehlerDifferential.D k A ((algebraMap B A) (e a)) = 0 := by
      simpa using congrArg (KaehlerDifferential.map k k B A) ha
    change KaehlerDifferential.D k A (e.symm (e a)) = 0 at hmap
    simpa using hmap

/-- Helper for Lemma 10.158.2: after localizing the multivariate polynomial ring, the source
`dx_i` basis base-changes to a basis of the tensor model of the localized differentials. -/
private noncomputable def fractionMvPolynomialDifferentialBasis (r : ℕ) :
    Module.Basis (Fin r) (FractionRing (MvPolynomial (Fin r) k))
      (TensorProduct (MvPolynomial (Fin r) k)
        (FractionRing (MvPolynomial (Fin r) k))
        (KaehlerDifferential k (MvPolynomial (Fin r) k))) :=
  (KaehlerDifferential.mvPolynomialBasis k (Fin r)).baseChange
    (FractionRing (MvPolynomial (Fin r) k))

/-- Helper for Lemma 10.158.2: after transporting `D(algebraMap a)` to the tensor model of the
localized differentials, its `dx_i`-coordinate is the localized partial derivative of `a`. -/
private theorem fractionMvPolynomial_coordinate_algebraMap
    {r : ℕ} (a : MvPolynomial (Fin r) k) (i : Fin r) :
    let R := MvPolynomial (Fin r) k
    let K0 := FractionRing R
    letI : Algebra.FormallyEtale R K0 := Algebra.FormallyEtale.of_isLocalization
      (nonZeroDivisors R)
    (((fractionMvPolynomialDifferentialBasis (k := k) r).repr).toLinearMap
        ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R K0).symm
          (KaehlerDifferential.D k K0 (algebraMap R K0 a)))) i =
      algebraMap R K0 (MvPolynomial.pderiv i a) := by
  let R := MvPolynomial (Fin r) k
  let K0 := FractionRing R
  letI : Algebra.FormallyEtale R K0 := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R)
  -- Route correction: isolate the transported `D(algebraMap a)` coordinates first, so the
  -- remaining raw rational-function blocker is only the quotient-rule/divisibility argument.
  change
      (((fractionMvPolynomialDifferentialBasis (k := k) r).repr).toLinearMap
          ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R K0).symm
            (KaehlerDifferential.D k K0 (algebraMap R K0 a)))) i =
        algebraMap R K0 (MvPolynomial.pderiv i a)
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  rw [fractionMvPolynomialDifferentialBasis]
  calc
    ((KaehlerDifferential.mvPolynomialBasis k (Fin r)).baseChange K0).repr
          (1 ⊗ₜ[R] (KaehlerDifferential.D k R) a) i =
        (KaehlerDifferential.mvPolynomialBasis k (Fin r)).repr
          (KaehlerDifferential.D k R a) i • (1 : K0) := by
            exact Module.Basis.baseChange_repr_tmul
              (S := K0) (b := KaehlerDifferential.mvPolynomialBasis k (Fin r))
              (x := (1 : K0)) (y := KaehlerDifferential.D k R a) (i := i)
    _ = algebraMap R K0 (MvPolynomial.pderiv i a) := by
          rw [KaehlerDifferential.mvPolynomialBasis_repr_apply, Algebra.smul_def, mul_one]

/-- Helper for Lemma 10.158.2: `IsFractionRing.num/den` gives the canonical reduced presentation
of a rational function in the multivariate fraction field. -/
private theorem fractionMvPolynomial_num_den_eq
    {r : ℕ} (z : FractionRing (MvPolynomial (Fin r) k)) :
    let R := MvPolynomial (Fin r) k
    let K0 := FractionRing R
    algebraMap R K0 (IsFractionRing.num R z) /
      algebraMap R K0 (IsFractionRing.den R z) = z := by
  -- The localization API already packages `z` as its chosen reduced numerator/denominator pair.
  simpa using IsFractionRing.mk'_num_den' (A := MvPolynomial (Fin r) k) z

/-- Helper for Lemma 10.158.2: the canonical numerator and denominator are already relatively
prime, which is exactly the source input needed after clearing denominators. -/
private theorem fractionMvPolynomial_num_den_reduced
    {r : ℕ} (z : FractionRing (MvPolynomial (Fin r) k)) :
    let R := MvPolynomial (Fin r) k
    IsRelPrime (IsFractionRing.num R z) (IsFractionRing.den R z) := by
  -- The same canonical fraction representative is chosen in reduced form.
  simpa using IsFractionRing.num_den_reduced (A := MvPolynomial (Fin r) k) z

/-- Helper for Lemma 10.158.2: this is the raw pure-transcendental source core on the rational
function field before transporting back to the basis field generated by the transcendence basis. -/
private theorem exists_pth_root_of_D_eq_zero_fractionMvPolynomial
    {r : ℕ} (z : FractionRing (MvPolynomial (Fin r) k))
    (hz : KaehlerDifferential.D k (FractionRing (MvPolynomial (Fin r) k)) z = 0) :
    ∃ w : FractionRing (MvPolynomial (Fin r) k), w ^ p = z := by
  let R := MvPolynomial (Fin r) k
  let K0 := FractionRing R
  letI : Algebra.FormallyEtale R K0 := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R)
  let basis := fractionMvPolynomialDifferentialBasis (k := k) r
  have hcoords :
      ∀ i : Fin r,
        (((basis.repr).toLinearMap
            ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R K0).symm
              (KaehlerDifferential.D k K0 z))) i) = 0 := by
    -- Route correction: isolate the source basis coordinates first, so the remaining gap is only
    -- the rational-function Frobenius criterion and not the tensor transport.
    intro i
    have htensor_zero :
        (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R K0).symm
            (KaehlerDifferential.D k K0 z) = 0 := by
      simpa [hz]
    have hcoord_zero :
        (((basis.repr).toLinearMap)
            ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R K0).symm
              (KaehlerDifferential.D k K0 z))) i =
          (((basis.repr).toLinearMap) 0) i := by
      exact congrArg (fun t ↦ (((basis.repr).toLinearMap) t) i) htensor_zero
    calc
      (((basis.repr).toLinearMap)
          ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R K0).symm
            (KaehlerDifferential.D k K0 z))) i =
          (((basis.repr).toLinearMap) 0) i := hcoord_zero
      _ = (0 : Fin r →₀ K0) i := by
            rw [LinearMap.map_zero]
      _ = 0 := by simp
  let num : R := IsFractionRing.num R z
  let den : nonZeroDivisors R := IsFractionRing.den R z
  have hden_ne : (den : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp den.2
  have hnum_den :
      algebraMap R K0 num / algebraMap R K0 (den : R) = z := by
    -- Switch from the ad hoc witness to the canonical reduced fraction representative.
    simpa [num, den, R, K0] using fractionMvPolynomial_num_den_eq (k := k) (z := z)
  have hnum_den_reduced : IsRelPrime num den := by
    -- This is the source coprimeness input needed after clearing denominators coordinatewise.
    simpa [num, den, R] using fractionMvPolynomial_num_den_reduced (k := k) (z := z)
  -- TODO: prove the source pure-transcendental core by evaluating `hcoords` on the canonical
  -- reduced presentation `z = num / den`, rewriting the transported coordinates via the quotient
  -- rule, clearing denominators with `hden_ne`, splitting by `hnum_den_reduced`, and then
  -- applying the characteristic-`p` Frobenius criterion once all partial derivatives vanish.
  let _ := hcoords
  let _ := hden_ne
  let _ := hnum_den
  let _ := hnum_den_reduced
  have hnum_coords :
      ∀ i : Fin r,
        (((basis.repr).toLinearMap
            ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R K0).symm
              (KaehlerDifferential.D k K0 (algebraMap R K0 num)))) i) =
          algebraMap R K0 (MvPolynomial.pderiv i num) := by
    intro i
    simpa [R, K0, num] using fractionMvPolynomial_coordinate_algebraMap (k := k) num i
  have hden_coords :
      ∀ i : Fin r,
        (((basis.repr).toLinearMap
            ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R K0).symm
              (KaehlerDifferential.D k K0 (algebraMap R K0 (den : R))))) i) =
          algebraMap R K0 (MvPolynomial.pderiv i (den : R)) := by
    intro i
    simpa [R, K0, den] using
      fractionMvPolynomial_coordinate_algebraMap (k := k) (a := (den : R)) i
  let _ := hnum_coords
  let _ := hden_coords
  let _ := hden_ne
  let _ := hnum_den
  let _ := hnum_den_reduced
  sorry

/-- Helper for Lemma 10.158.2: transport the raw rational-function source core across the
canonical `aevalEquivField` of the transcendence basis. -/
private theorem exists_pth_root_of_D_eq_zero_of_basis_field
    {L : Type v} [Field L] [Algebra k L] {r : ℕ}
    (x : Fin r → L) (hx : IsTranscendenceBasis k x)
    (c : IntermediateField.adjoin k (Set.range x))
    (hc : KaehlerDifferential.D k (IntermediateField.adjoin k (Set.range x)) c = 0) :
    ∃ b : IntermediateField.adjoin k (Set.range x), b ^ p = c := by
  let e :
      FractionRing (MvPolynomial (Fin r) k) ≃ₐ[k]
        IntermediateField.adjoin k (Set.range x) := hx.1.aevalEquivField
  have hsymm_zero :
      KaehlerDifferential.D k (FractionRing (MvPolynomial (Fin r) k)) (e.symm c) = 0 := by
    -- Move the vanishing statement to the raw rational-function model of the basis field.
    rw [D_eq_zero_iff_of_algEquiv (k := k) e (e.symm c)]
    simpa using hc
  rcases exists_pth_root_of_D_eq_zero_fractionMvPolynomial (k := k) (p := p)
      (z := e.symm c) hsymm_zero with ⟨w, hw⟩
  refine ⟨e w, ?_⟩
  -- Transport the chosen `p`th root back across the algebra equivalence.
  simpa using congrArg e hw

/-- Helper for Lemma 10.158.2: after differentiating the minimal polynomial relation over a finite
separable extension of the basis field, each coefficient must have zero differential downstairs. -/
private theorem minpoly_coeff_D_eq_zero_of_D_eq_zero_of_separating_basis
    {L : Type v} [Field L] [Algebra k L] {r : ℕ}
    (x : Fin r → L) (hx : IsTranscendenceBasis k x)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) L)
    (hfd : FiniteDimensional (IntermediateField.adjoin k (Set.range x)) L)
    (a : L) (ha : KaehlerDifferential.D k L a = 0) :
    ∀ n : ℕ,
      KaehlerDifferential.D k (IntermediateField.adjoin k (Set.range x))
        ((minpoly (IntermediateField.adjoin k (Set.range x)) a).coeff n) = 0 := by
  -- Route correction: the source proof differentiates `minpoly = 0` first and only then uses
  -- linear independence of `1, a, …, a^(d - 1)` to extract coefficientwise vanishing.
  -- TODO: rewrite `d (aeval a (minpoly _ a)) = 0` through the formally etale comparison for the
  -- finite separable extension over `IntermediateField.adjoin k (Set.range x)`, then project the
  -- resulting tensor relation to basis coordinates of `Ω[F⁄k]` and use
  -- `linearIndependent_pow (K := F) (S := L) a` to force each differentiated coefficient to vanish.
  let _ := hx
  let _ := hsep
  let _ := hfd
  let _ := ha
  sorry

/-- Helper for Lemma 10.158.2: once the vanishing statement has been descended to a finitely
generated extension, the remaining source-faithful work is the separating-transcendence-basis and
minimal-polynomial argument. -/
private theorem exists_pth_root_of_D_eq_zero_of_essFiniteType
    {L : Type v} [Field L] [Algebra k L] [Algebra.EssFiniteType k L]
    (a : L) (ha : KaehlerDifferential.D k L a = 0) :
    ∃ b : L, b ^ p = a := by
  -- Route correction: the finite descent is complete, so we now follow the source route over a
  -- separating transcendence basis and isolate the two remaining bridges explicitly.
  obtain ⟨r, x, hx, hsep, hfd⟩ :=
    exists_fin_separating_transcendence_basis (k := k) (L := L)
  let F : IntermediateField k L := IntermediateField.adjoin k (Set.range x)
  letI : Algebra.IsSeparable F L := by simpa [F] using hsep
  letI : FiniteDimensional F L := by simpa [F] using hfd
  letI : CharP F p := charP_of_injective_algebraMap (algebraMap k F).injective p
  have hcoeff_zero :
      ∀ n : ℕ, KaehlerDifferential.D k F ((minpoly F a).coeff n) = 0 := by
    -- The differentiated minimal-polynomial relation is the remaining separable-stage blocker.
    simpa [F] using
      minpoly_coeff_D_eq_zero_of_D_eq_zero_of_separating_basis
        (k := k) (L := L) x hx hsep hfd a ha
  have hcoeff_pth :
      ∀ n : ℕ, ∃ b : F, (minpoly F a).coeff n = b ^ p := by
    intro n
    -- Once the coefficient differential vanishes in the basis field, the pure-transcendental
    -- source step should turn it into a `p`th power there.
    rcases exists_pth_root_of_D_eq_zero_of_basis_field (k := k) (L := L) (p := p)
        x hx ((minpoly F a).coeff n) (hcoeff_zero n) with ⟨b, hb⟩
    exact ⟨b, hb.symm⟩
  -- The Chapter 9 minpoly criterion now matches the source finish exactly.
  exact
    exists_pth_root_of_minpoly_coeff_pth_powers (K := F) (L := L) (p := p)
      (α := a) (Algebra.IsSeparable.isSeparable F a) hcoeff_pth

/- Domain triage:
- primary domain: Kähler differentials of field extensions in characteristic `p`, together with the
  Frobenius / perfect-field interface for `p`th powers;
- sampled owner declarations:
  `KaehlerDifferential.D`,
  `Derivation.leibniz_pow`,
  `exists_pth_root_of_minpoly_coeff_pth_powers`,
  `perfectField_iff_charZero_or_exists_pth_root`;
- best owner abstraction: the canonical universal derivation `KaehlerDifferential.D k K`;
- primitive data: the owner derivation itself and the ambient field/perfectness hypotheses;
- derived API: this source-facing kernel characterization of `KaehlerDifferential.D k K`.

Source/core/bridge triage:
- `source-facing`: `kaehlerDifferential_eq_zero_iff_exists_pth_root`;
- `core/canonical`: `KaehlerDifferential.D k K`;
- `bridge/view`: the `p`th-power side is the source-facing reformulation, while the eventual
  converse proof should reuse the Chapter 9/10 Frobenius and perfect-field owner lemmas rather than
  introduce any local wrapper around them.
-/

-- Proof sketch: if `a = b ^ p`, then the universal derivation kills `a` because
-- `d (b ^ p) = p • b ^ (p - 1) • db = 0` in characteristic `p`. Conversely, reduce to the finitely
-- generated case, choose a separating transcendence basis over the perfect base field, identify
-- `Ω[K⁄k]` with the free `K`-vector space on the differentials of that basis, deduce that the
-- coefficients of the minimal polynomial of `a` have zero differential, then reuse the canonical
-- Chapter 9/10 Frobenius/perfect-field bridge lemmas to conclude that `a` is a `p`th power.
/-- Lemma 10.158.2: over a perfect field `k` of characteristic `p > 0`, an element of an extension
field `K` has zero Kähler differential over `k` if and only if it is a `p`th power in `K`. -/
theorem kaehlerDifferential_eq_zero_iff_exists_pth_root (a : K) :
    KaehlerDifferential.D k K a = 0 ↔ ∃ b : K, b ^ p = a := by
  constructor
  · intro ha
    -- First descend the finite presentation witness for `D a = 0` to a finitely generated
    -- intermediate field, matching the source reduction step.
    obtain ⟨L, hLfg, haL, haLzero⟩ :=
      exists_fg_intermediateField_of_D_eq_zero (k := k) (K := K) a ha
    letI : Algebra.EssFiniteType k L := (IntermediateField.essFiniteType_iff).2 hLfg
    let aL : L := ⟨a, haL⟩
    -- The remaining source argument is isolated in the finitely generated helper.
    obtain ⟨b, hb⟩ :=
      exists_pth_root_of_D_eq_zero_of_essFiniteType (k := k) (p := p) aL haLzero
    exact ⟨b, congrArg Subtype.val hb⟩
  · rintro ⟨b, rfl⟩
    letI : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K]
    simp

end

/-! ### Lemma_10_158_3 (from Chap10) -/
universe u v

/-
Domain-style sampling:
- primary domain: purely inseparable finite field extensions in characteristic `p`, measured by the
  canonical universal derivation on Kähler differentials;
- sampled owner declarations:
  `KaehlerDifferential.D`,
  `kaehlerDifferential_eq_zero_iff_exists_pth_root`,
  `IntermediateField.adjoin`,
  `IntermediateField.relfinrank`;
- best owner abstraction: the source-facing generated intermediate field
  `IntermediateField.adjoin k (Set.range roots)`, together with the owner derivation
  `KaehlerDifferential.D (ZMod p) k`;
- primitive data: the family `a : Fin n → k`, the chosen roots `roots : Fin n → K`, and the
  equations `roots i ^ p = algebraMap k K (a i)`;
- derived API: the degree computation for the generated extension under linear independence of the
  differentials.

Source/core/bridge triage:
- `source-facing`: `relfinrank_adjoin_pthRoots_eq_pow`;
- `core/canonical`: `KaehlerDifferential.D (ZMod p) k`, `IntermediateField.adjoin`, and
  `IntermediateField.relfinrank`;
- `bridge/view`: Lemma `10.158.2`, which converts vanishing of a differential into existence of a
  `p`th root and is the canonical chapter input for the inductive degree-counting argument.
-/

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
variable {p n : ℕ} [Fact p.Prime] [CharP k p]
variable [Algebra (ZMod p) k]

/-- Helper for Lemma 10.158.3: restricting an independent family of differentials to the prefix
indexed by `Fin n` preserves linear independence. -/
lemma linearIndependent_differentials_castSucc
    {a : Fin (n + 1) → k}
    (hd : LinearIndependent k (fun i ↦ KaehlerDifferential.D (ZMod p) k (a i))) :
    LinearIndependent k
      (fun i : Fin n ↦ KaehlerDifferential.D (ZMod p) k (a i.castSucc)) := by
  -- The prefix family is obtained by composing with the canonical embedding `Fin n ↪ Fin (n + 1)`.
  simpa using hd.comp Fin.castSuccEmb Fin.castSuccEmb.injective

/-- Helper for Lemma 10.158.3: the differential of the last element in an independent family is
not in the span of the earlier differentials. -/
lemma last_differential_not_mem_span_prefix
    (a : Fin (n + 1) → k)
    (hd : LinearIndependent k (fun i ↦ KaehlerDifferential.D (ZMod p) k (a i))) :
    KaehlerDifferential.D (ZMod p) k (a (Fin.last n)) ∉
      Submodule.span k
        (Set.range fun i : Fin n ↦ KaehlerDifferential.D (ZMod p) k (a i.castSucc)) := by
  have himage :
      (fun i : Fin (n + 1) ↦ KaehlerDifferential.D (ZMod p) k (a i)) ''
          {i : Fin (n + 1) | ↑i < n} =
        Set.range fun i : Fin n ↦ KaehlerDifferential.D (ZMod p) k (a i.castSucc) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.castSucc, i.is_lt, rfl⟩
  have hlast : (Fin.last n : Fin (n + 1)) ∉ {i : Fin (n + 1) | ↑i < n} := by
    simp
  -- Apply the standard span-exclusion criterion to the last index.
  rw [← himage]
  exact hd.notMem_span_image (s := {i : Fin (n + 1) | ↑i < n}) hlast

/-- Helper for Lemma 10.158.3: adjoining the last chosen root after the prefix field is the same
as adjoining the whole `Fin.snoc` family at once over `k`. -/
lemma adjoin_range_succ_eq_restrictScalars_adjoin_singleton
    (roots₀ : Fin n → K) (β : K) :
    IntermediateField.adjoin k (Set.range (Fin.snoc roots₀ β)) =
      (IntermediateField.adjoin (IntermediateField.adjoin k (Set.range roots₀))
        ({β} : Set K)).restrictScalars k := by
  -- Rewrite the `Fin.snoc` range as the union of the prefix range with the last root.
  rw [Fin.range_snoc]
  calc
    IntermediateField.adjoin k (insert β (Set.range roots₀)) =
        IntermediateField.adjoin k ((Set.range roots₀) ∪ ({β} : Set K)) := by
          congr 1
          ext x
          simp [Set.mem_insert_iff]
    _ = IntermediateField.adjoin k (Set.range roots₀) ⊔ IntermediateField.adjoin k ({β} : Set K) := by
          rw [IntermediateField.adjoin_union]
    _ =
        (IntermediateField.adjoin (IntermediateField.adjoin k (Set.range roots₀))
          ({β} : Set K)).restrictScalars k := by
            symm
            simpa using
              (IntermediateField.restrictScalars_adjoin_eq_sup (F := k) (E := K)
                (IntermediateField.adjoin k (Set.range roots₀)) ({β} : Set K))

/-- Helper for Lemma 10.158.3: adjoining one chosen `p`th root over a field where the base element
is not already a `p`th power gives relative degree `p`. -/
lemma finrank_adjoin_singleton_eq_prime
    (L : IntermediateField k K) (β : K) (a : L)
    (hβ : β ^ p = algebraMap L K a)
    (hnot : ¬ ∃ b : L, b ^ p = a) :
    Module.finrank L (IntermediateField.adjoin L ({β} : Set K)) = p := by
  have hβ_integral_pow : IsIntegral L (β ^ p) := by
    rw [hβ]
    exact isIntegral_algebraMap
  have hβ_integral : IsIntegral L β :=
    IsIntegral.of_pow (show 0 < p by exact (Fact.out : Nat.Prime p).pos) hβ_integral_pow
  have hirr : Irreducible (Polynomial.X ^ p - Polynomial.C a) := by
    -- The nonexistence of a `p`th root in `L` is exactly the irreducibility criterion.
    refine X_pow_sub_C_irreducible_of_prime (Fact.out : Nat.Prime p) ?_
    intro b hb
    exact hnot ⟨b, hb⟩
  have hroot : Polynomial.aeval β (Polynomial.X ^ p - Polynomial.C a) = 0 := by
    -- The chosen generator `β` is a root of `X ^ p - a`.
    calc
      Polynomial.aeval β (Polynomial.X ^ p - Polynomial.C a) =
          β ^ p - algebraMap L K a := by
            simp [Polynomial.aeval_def]
      _ = 0 := by rw [hβ, sub_self]
  have hmin :
      minpoly L β = Polynomial.X ^ p - Polynomial.C a := by
    -- The minimal polynomial agrees with the irreducible polynomial having `β` as a root.
    refine (minpoly.eq_of_irreducible_of_monic hirr hroot ?_).symm
    exact Polynomial.monic_X_pow_sub_C a (Nat.Prime.ne_zero (Fact.out : p.Prime))
  -- The simple-adjunction degree is the degree of the minimal polynomial.
  rw [IntermediateField.adjoin.finrank hβ_integral, hmin]
  simp

/-- Helper for Lemma 10.158.3: linear independence of the differentials produces a derivation on
`k` that kills the prefix elements but not the last one. -/
lemma exists_separator_derivation_kills_prefix_not_last
    (a : Fin (n + 1) → k)
    (hd : LinearIndependent k (fun i ↦ KaehlerDifferential.D (ZMod p) k (a i))) :
    ∃ δ : Derivation (ZMod p) k k,
      (∀ i : Fin n, δ (a i.castSucc) = 0) ∧
      δ (a (Fin.last n)) ≠ 0 := by
  let W : Submodule k (KaehlerDifferential (ZMod p) k) :=
    Submodule.span k
      (Set.range fun i : Fin n ↦ KaehlerDifferential.D (ZMod p) k (a i.castSucc))
  have hnot :
      KaehlerDifferential.D (ZMod p) k (a (Fin.last n)) ∉ W := by
    -- The last differential lies outside the span of the prefix differentials.
    simpa [W] using last_differential_not_mem_span_prefix (k := k) (p := p) a hd
  rcases Submodule.exists_le_ker_of_notMem (p := W) hnot with ⟨φ, hφlast, hWker⟩
  refine ⟨LinearMap.compDer φ (KaehlerDifferential.D (ZMod p) k), ?_⟩
  constructor
  · intro i
    -- The separating functional vanishes on the prefix span, hence on each prefix differential.
    have hi :
        KaehlerDifferential.D (ZMod p) k (a i.castSucc) ∈ W :=
      Submodule.subset_span ⟨i, rfl⟩
    have hzero :
        φ (KaehlerDifferential.D (ZMod p) k (a i.castSucc)) = 0 :=
      hWker hi
    simpa using hzero
  · -- The last differential was chosen outside the kernel, so the induced derivation sees it.
    simpa using hφlast

/-- Helper for Lemma 10.158.3: a `ZMod p`-derivation kills every element that becomes a `p`th
power in its target field. -/
lemma derivation_apply_algebraMap_eq_zero_of_exists_pth_root
    {L : Type v} [Field L] [Algebra k L] [Algebra (ZMod p) L] [CharP L p]
    (D : Derivation (ZMod p) L L) {a : k} {b : L}
    (hb : b ^ p = algebraMap k L a) :
    D (algebraMap k L a) = 0 := by
  -- Differentiate the displayed `p`th-power relation in characteristic `p`.
  calc
    D (algebraMap k L a) = D (b ^ p) := by rw [hb]
    _ = 0 := by
      rw [Derivation.leibniz_pow]
      simp

/-- Helper for Lemma 10.158.3: the `p`th power of an element in the prefix root field lands back
in the intermediate field of `k` generated by Frobenius images and the prefix coefficients. -/
lemma pth_power_mem_separator_closure_of_mem_prefix_adjoin
    (a : Fin (n + 1) → k) (roots₀ : Fin n → K)
    (hroots₀ : ∀ i, roots₀ i ^ p = algebraMap k K (a i.castSucc))
    {x : K}
    (hx : x ∈ IntermediateField.adjoin k (Set.range roots₀)) :
    ∃ c : k,
      c ∈ IntermediateField.adjoin (ZMod p)
        (((frobenius k p).fieldRange : Set k) ∪ Set.range (fun i : Fin n ↦ a i.castSucc)) ∧
      x ^ p = algebraMap k K c := by
  letI : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  let M : IntermediateField (ZMod p) k :=
    IntermediateField.adjoin (ZMod p)
      (((frobenius k p).fieldRange : Set k) ∪ Set.range (fun i : Fin n ↦ a i.castSucc))
  have hprefix_mem : ∀ i : Fin n, a i.castSucc ∈ M := by
    intro i
    -- Each prefix coefficient is one of the explicit generators of `M`.
    exact IntermediateField.subset_adjoin (F := ZMod p)
      (S := (((frobenius k p).fieldRange : Set k) ∪ Set.range (fun j : Fin n ↦ a j.castSucc)))
      (by exact Or.inr ⟨i, rfl⟩)
  have hfrobenius_mem : ∀ r : k, r ^ p ∈ M := by
    intro r
    -- Every `p`th power lies in the Frobenius range, hence among the generators of `M`.
    exact IntermediateField.subset_adjoin (F := ZMod p)
      (S := (((frobenius k p).fieldRange : Set k) ∪ Set.range (fun j : Fin n ↦ a j.castSucc)))
      (by
        left
        simpa [frobenius_def] using RingHom.mem_fieldRange_self (frobenius k p) r)
  -- The controlled invariant is exactly the source proof's claim about `p`th powers in the
  -- prefix root field.
  refine IntermediateField.adjoin_induction (F := k) (s := Set.range roots₀)
    (p := fun y _ ↦ ∃ c : k, c ∈ M ∧ y ^ p = algebraMap k K c)
    ?_ ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨i, rfl⟩
    -- A generator root has `p`th power equal to the corresponding base coefficient.
    exact ⟨a i.castSucc, hprefix_mem i, hroots₀ i⟩
  · intro r
    -- Scalars contribute Frobenius generators.
    exact ⟨r ^ p, hfrobenius_mem r, by simpa using (map_pow (algebraMap k K) r p).symm⟩
  · intro y z hy hz ⟨cy, hcyM, hcy⟩ ⟨cz, hczM, hcz⟩
    -- The characteristic-`p` Frobenius turns addition into addition of `p`th powers.
    refine ⟨cy + cz, M.add_mem hcyM hczM, ?_⟩
    calc
      (y + z) ^ p = y ^ p + z ^ p := by simpa using (add_pow_char (p := p) y z)
      _ = algebraMap k K cy + algebraMap k K cz := by rw [hcy, hcz]
      _ = algebraMap k K (cy + cz) := by rw [map_add]
  · intro y hy ⟨cy, hcyM, hcy⟩
    -- Inversion stays inside the intermediate field, and `p`th powers commute with inversion.
    refine ⟨cy⁻¹, M.inv_mem hcyM, ?_⟩
    calc
      (y⁻¹) ^ p = (y ^ p)⁻¹ := by rw [inv_pow]
      _ = (algebraMap k K cy)⁻¹ := by rw [hcy]
      _ = algebraMap k K (cy⁻¹) := by rw [map_inv₀]
  · intro y z hy hz ⟨cy, hcyM, hcy⟩ ⟨cz, hczM, hcz⟩
    -- Multiplication stays compatible with the `p`th-power invariant.
    refine ⟨cy * cz, M.mul_mem hcyM hczM, ?_⟩
    calc
      (y * z) ^ p = y ^ p * z ^ p := by rw [mul_pow]
      _ = algebraMap k K cy * algebraMap k K cz := by rw [hcy, hcz]
      _ = algebraMap k K (cy * cz) := by rw [map_mul]

/-- Helper for Lemma 10.158.3: a separator derivation kills the intermediate field of `k`
generated by Frobenius images and the prefix coefficients. -/
lemma separator_derivation_eq_zero_on_separator_closure
    (a : Fin (n + 1) → k) (δ : Derivation (ZMod p) k k)
    (hδprefix : ∀ i : Fin n, δ (a i.castSucc) = 0)
    {x : k}
    (hx : x ∈ IntermediateField.adjoin (ZMod p)
      (((frobenius k p).fieldRange : Set k) ∪ Set.range (fun i : Fin n ↦ a i.castSucc))) :
    δ x = 0 := by
  -- The source proof differentiates only inside `k`, so we keep the derivation on the
  -- Frobenius-plus-prefix closure there.
  refine IntermediateField.adjoin_induction (F := ZMod p)
    (s := (((frobenius k p).fieldRange : Set k) ∪ Set.range (fun i : Fin n ↦ a i.castSucc)))
    (p := fun y _ ↦ δ y = 0)
    ?_ ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with hy | hy
    · rcases RingHom.mem_fieldRange.mp hy with ⟨z, rfl⟩
      -- Frobenius generators are `p`th powers, and derivations kill those in characteristic `p`.
      rw [frobenius_def, Derivation.leibniz_pow]
      simp
    · rcases hy with ⟨i, rfl⟩
      -- The separator derivation was chosen to vanish on each prefix coefficient.
      exact hδprefix i
  · intro r
    -- Derivations vanish on the scalar image of the prime field.
    simpa using δ.map_algebraMap r
  · intro y z hy hz hδy hδz
    -- Zero is preserved under addition.
    rw [δ.map_add, hδy, hδz, add_zero]
  · intro y hy hδy
    -- Zero is preserved under inversion inside the field.
    rw [δ.leibniz_inv, hδy]
    simp
  · intro y z hy hz hδy hδz
    -- Zero is preserved under multiplication.
    rw [δ.leibniz, hδy, hδz]
    simp

/-- Helper for Lemma 10.158.3: in the successor step, the last base element does not become a
`p`th power in the prefix field generated by the earlier chosen roots. -/
lemma last_root_not_pth_power_in_prefix
    (a : Fin (n + 1) → k) (roots₀ : Fin n → K)
    (hroots₀ : ∀ i, roots₀ i ^ p = algebraMap k K (a i.castSucc))
    (hd : LinearIndependent k (fun i ↦ KaehlerDifferential.D (ZMod p) k (a i))) :
    ¬ ∃ b : IntermediateField.adjoin k (Set.range roots₀),
      b ^ p =
        algebraMap k (IntermediateField.adjoin k (Set.range roots₀)) (a (Fin.last n)) := by
  rcases exists_separator_derivation_kills_prefix_not_last (k := k) (p := p) a hd with
    ⟨δ, hδprefix, hδlast⟩
  let M : IntermediateField (ZMod p) k :=
    IntermediateField.adjoin (ZMod p)
      (((frobenius k p).fieldRange : Set k) ∪ Set.range (fun i : Fin n ↦ a i.castSucc))
  intro hb
  rcases hb with ⟨b, hb⟩
  have hbK : (b : K) ^ p = algebraMap k K (a (Fin.last n)) := by
    -- Coerce the hypothetical `p`th-root witness from the prefix field to the ambient field.
    exact congrArg Subtype.val hb
  obtain ⟨c, hcM, hcpow⟩ :=
    pth_power_mem_separator_closure_of_mem_prefix_adjoin
      (k := k) (K := K) (p := p) a roots₀ hroots₀ b.2
  have hlast_mem : a (Fin.last n) ∈ M := by
    -- The source contradiction comes from pushing the witness back into the controlled subfield
    -- of `k`, where the separator derivation is already defined.
    have hmap_eq : algebraMap k K c = algebraMap k K (a (Fin.last n)) := by
      rw [← hcpow, hbK]
    exact hmap_eq |> (algebraMap k K).injective |> fun h => h ▸ hcM
  have hδzero :
      δ (a (Fin.last n)) = 0 :=
    separator_derivation_eq_zero_on_separator_closure
      (k := k) (p := p) a δ hδprefix hlast_mem
  -- Route correction: instead of extending `δ` to the prefix field, we keep it on `k` and use the
  -- Frobenius-closure argument from the source proof to force `a_last` into the kernel.
  exact hδlast hδzero

-- Proof sketch: argue by induction on `n`. For the induction step, compare
-- `k(a_1^(1/p), ..., a_(n-1)^(1/p))` with the field obtained by adjoining one more chosen root of
-- `a_n`. If `a_n` became a `p`th power in the smaller field, Lemma `10.158.2` would force
-- `KaehlerDifferential.D (ZMod p) k (a n)` to lie in the `k`-span of the earlier differentials,
-- contradicting linear independence. Hence each step multiplies the relative degree by `p`.
/-- Lemma 10.158.3: if `da₁, ..., daₙ` are linearly independent in `Ω[k⁄ZMod p]`, then adjoining
chosen `p`th roots of the `aᵢ` gives an extension of degree `p ^ n` over `k`. -/
theorem relfinrank_adjoin_pthRoots_eq_pow
    (a : Fin n → k) (roots : Fin n → K)
    (hroots : ∀ i, roots i ^ p = algebraMap k K (a i))
    (hd :
      LinearIndependent k (fun i ↦ KaehlerDifferential.D (ZMod p) k (a i))) :
    (⊥ : IntermediateField k K).relfinrank (IntermediateField.adjoin k (Set.range roots)) =
      p ^ n := by
  induction n with
  | zero =>
      -- The empty family adjoins nothing, so the relative degree is `1 = p ^ 0`.
      simp
  | succ n ih =>
      let a₀ : Fin n → k := fun i ↦ a i.castSucc
      let roots₀ : Fin n → K := fun i ↦ roots i.castSucc
      let a_last : k := a (Fin.last n)
      let root_last : K := roots (Fin.last n)
      let L : IntermediateField k K := IntermediateField.adjoin k (Set.range roots₀)
      have hroots₀ : ∀ i, roots₀ i ^ p = algebraMap k K (a₀ i) := by
        intro i
        exact hroots i.castSucc
      have hd₀ :
          LinearIndependent k (fun i ↦ KaehlerDifferential.D (ZMod p) k (a₀ i)) := by
        -- Restrict the independent differential family to the prefix indices.
        simpa [a₀] using linearIndependent_differentials_castSucc (k := k) (p := p) hd
      have hprefix : (⊥ : IntermediateField k K).relfinrank L = p ^ n := by
        -- Apply the induction hypothesis to the prefix family.
        simpa [L, a₀, roots₀] using ih a₀ roots₀ hroots₀ hd₀
      have hnot :
          ¬ ∃ b : L, b ^ p = algebraMap k L a_last := by
        -- The last source element cannot already be a `p`th power over the prefix field.
        simpa [L, a₀, roots₀, a_last] using
          last_root_not_pth_power_in_prefix
            (k := k) (K := K) (p := p) a roots₀ hroots₀ hd
      have hsimple :
          Module.finrank L (IntermediateField.adjoin L ({root_last} : Set K)) = p := by
        -- The last chosen root gives a simple purely inseparable step of degree `p`.
        have hroot_last : root_last ^ p = algebraMap L K (algebraMap k L a_last) := by
          -- Rewrite the original root equation through the prefix-field tower.
          rw [show algebraMap L K (algebraMap k L a_last) = algebraMap k K a_last by rfl]
          simpa [root_last, a_last] using hroots (Fin.last n)
        exact
          finrank_adjoin_singleton_eq_prime (k := k) (K := K) (p := p) L root_last
            (algebraMap k L a_last) hroot_last hnot
      have hsnoc : Fin.snoc roots₀ root_last = roots := by
        ext i
        rcases Fin.eq_castSucc_or_eq_last i with (⟨j, rfl⟩ | rfl)
        · simp [roots₀]
        · simp [root_last]
      have hrewrite :
          IntermediateField.adjoin k (Set.range roots) =
            (IntermediateField.adjoin L ({root_last} : Set K)).restrictScalars k := by
        -- Normalize the successor stage as a simple adjunction over the prefix field.
        simpa [hsnoc, L, roots₀, root_last] using
          adjoin_range_succ_eq_restrictScalars_adjoin_singleton
            (k := k) (n := n) roots₀ root_last
      have hle :
          L ≤ IntermediateField.adjoin k (Set.range roots) := by
        -- The prefix field embeds into the full field generated by all chosen roots.
        intro x hx
        rw [hrewrite]
        exact
          IntermediateField.adjoin_contains_field_as_subfield
            (F := L.toSubfield) (S := ({root_last} : Set K)) hx
      have hstep :
          L.relfinrank (IntermediateField.adjoin k (Set.range roots)) = p := by
        have hext :
            IntermediateField.extendScalars hle =
              IntermediateField.adjoin L ({root_last} : Set K) := by
          apply IntermediateField.restrictScalars_injective k
          rw [IntermediateField.extendScalars_restrictScalars, hrewrite]
        -- Convert the simple-adjunction finrank into the relative degree in the original tower.
        rw [IntermediateField.relfinrank_eq_finrank_of_le hle, hext]
        exact hsimple
      -- Multiply the prefix degree and the last simple degree.
      calc
        (⊥ : IntermediateField k K).relfinrank (IntermediateField.adjoin k (Set.range roots)) =
            (⊥ : IntermediateField k K).relfinrank L *
              L.relfinrank (IntermediateField.adjoin k (Set.range roots)) := by
                symm
                exact IntermediateField.relfinrank_mul_relfinrank
                  (show (⊥ : IntermediateField k K) ≤ L from bot_le) hle
        _ = p * p ^ n := by rw [hprefix, hstep, Nat.mul_comm]
        _ = p ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]

end

/-! ### Lemma_10_158_4 (from Chap10) -/
open scoped TensorProduct

universe u v

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
variable {p : ℕ} [Fact p.Prime] [CharP k p]

/- Domain triage:
- primary domain: characteristic-`p` field extensions and the Jacobi-Zariski transitivity map on
  Kähler differentials;
- sampled owner declarations:
  - `Algebra.IsSeparableOver`,
  - `KaehlerDifferential.mapBaseChange`,
  - `Algebra.char_p_field_extension_tfae_separable_reduced_one_pth_root_geometrically_reduced_kaehler_injective_h1_cotangent_formally_smooth`;
- best owner abstraction: the chapter owner theorem
  `Algebra.char_p_field_extension_tfae_separable_reduced_one_pth_root_geometrically_reduced_kaehler_injective_h1_cotangent_formally_smooth`,
  whose fourth clause is exactly the injectivity of
  `KaehlerDifferential.mapBaseChange (ZMod p) k K`;
- primitive data: the field extension `K / k` in characteristic `p`;
- derived API: the individual pairwise equivalences extracted from the TFAE owner theorem.

Layer triage:
- `source-facing`: this lemma isolates the textbook equivalence between Stacks-project
  separability and injectivity of the canonical differential map;
- `core/canonical`: the owner TFAE theorem above;
- `bridge/view`: the present lemma is the `0 ↔ 3` projection of that owner theorem.

So this file should stay a thin projection theorem rather than reintroducing a parallel proof
package around the same six-way equivalence.
-/
/-- Lemma 10.158.4: for a field extension `K / k` of characteristic `p > 0`, the Stacks Project
notion that `K / k` is separable is equivalent to injectivity of the canonical map
`K ⊗[k] Ω[k⁄ZMod p] → Ω[K⁄ZMod p]`. -/
theorem isSeparableOver_iff_kaehlerDifferential_mapBaseChange_injective :
    by
      letI : Algebra (ZMod p) k := ZMod.algebra k p
      letI : CharP K p := CharP.of_ringHom_of_ne_zero (algebraMap k K) p (Fact.out : p.Prime).ne_zero
      letI : Algebra (ZMod p) K := ZMod.algebra K p
      letI : IsScalarTower (ZMod p) k K := by infer_instance
      exact
        Algebra.IsSeparableOver k K ↔
          Function.Injective (KaehlerDifferential.mapBaseChange (ZMod p) k K) := by
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  letI : CharP K p := CharP.of_ringHom_of_ne_zero (algebraMap k K) p (Fact.out : p.Prime).ne_zero
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  letI : IsScalarTower (ZMod p) k K := by infer_instance
  let l : List Prop := [
    Algebra.IsSeparableOver k K,
    IsReduced (K ⊗[k] onePthRootExtension k p),
    Algebra.IsGeometricallyReduced k K,
    Function.Injective (KaehlerDifferential.mapBaseChange (ZMod p) k K),
    Subsingleton (Algebra.H1Cotangent k K),
    Algebra.FormallySmooth k K
  ]
  have htfae : List.TFAE l := by
    simpa [l] using
      Algebra.char_p_field_extension_tfae_separable_reduced_one_pth_root_geometrically_reduced_kaehler_injective_h1_cotangent_formally_smooth
  simpa [l] using htfae.out 0 3 (by simp [l]) (by simp [l])

end

/-! ### Lemma_10_158_5 (from Chap10) -/
open scoped TensorProduct

universe u v

namespace Algebra

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/- Domain-style sampling for Lemma 10.158.5:
- primary domain: field extensions, formal smoothness, and the Stacks-project separability owner
  `Algebra.IsSeparableOver`;
- sampled owner declarations:
  `Algebra.IsSeparableOver`,
  `PerfectField.ofCharZero`,
  `Algebra.char_p_field_extension_tfae_separable_reduced_one_pth_root_geometrically_reduced_kaehler_injective_h1_cotangent_formally_smooth`,
  `List.TFAE.out`;
- best owner abstraction: the source-facing owner `Algebra.IsSeparableOver k K`, with the
  characteristic-zero perfect-field instance and the characteristic-`p` owner TFAE supplying the
  two canonical bridges;
- primitive data: the field extension `K / k` together with `[Algebra.FormallySmooth k K]`;
- derived API: the characteristic split and the positive-characteristic reduction through
  the six-way field-extension TFAE.

Source/core/bridge triage:
- `source-facing`: the implication from formal smoothness to Stacks-project separability;
- `core/canonical`: `Algebra.FormallySmooth k K` and `Algebra.IsSeparableOver k K`;
- `bridge/view`: `PerfectField.ofCharZero` in characteristic zero, and the characteristic-`p`
  projection from Proposition `10.158.9`.
-/
-- Proof sketch: split on the characteristic of `k`. In characteristic zero, `k` is perfect, so
-- the owner instance `Algebra.IsSeparableOver.of_perfectField` applies directly. In
-- characteristic `p > 0`, Proposition `10.158.9` already packages the equivalence among
-- separability, reducedness criteria, Kähler-differential injectivity, vanishing of
-- `H₁(L_{K/k})`, and formal smoothness. Project the implication from formal smoothness to
-- `Algebra.IsSeparableOver k K` from that owner theorem.
/-- Lemma 10.158.5: a formally smooth field extension is separable in the Stacks Project sense. -/
theorem isSeparableOver_of_formallySmooth [Algebra.FormallySmooth k K] :
    Algebra.IsSeparableOver k K := by
  rcases CharP.exists' k with hchar0 | ⟨p, hp, hcharp⟩
  · letI : CharZero k := hchar0
    letI : PerfectField k := PerfectField.ofCharZero
    infer_instance
  · letI : Fact p.Prime := hp
    letI : CharP k p := hcharp
    letI : CharP K p := CharP.of_ringHom_of_ne_zero (algebraMap k K) p hp.out.ne_zero
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    letI : IsScalarTower (ZMod p) k K := by infer_instance
    let l : List Prop := [
      Algebra.IsSeparableOver k K,
      IsReduced (K ⊗[k] onePthRootExtension k p),
      Algebra.IsGeometricallyReduced k K,
      Function.Injective (KaehlerDifferential.mapBaseChange (ZMod p) k K),
      Subsingleton (Algebra.H1Cotangent k K),
      Algebra.FormallySmooth k K
    ]
    have htfae : List.TFAE l := by
      simpa [l] using
        Algebra.char_p_field_extension_tfae_separable_reduced_one_pth_root_geometrically_reduced_kaehler_injective_h1_cotangent_formally_smooth
    simpa [l] using
      (htfae.out 0 5 (by simp [l]) (by simp [l])).2 (show Algebra.FormallySmooth k K from inferInstance)

end

end Algebra

/-! ### Lemma_10_158_6 (from Chap10) -/
open scoped TensorProduct

universe u v

namespace Algebra

section

variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]

-- Proof sketch: rewrite formal smoothness using `Algebra.formallySmooth_iff`. Over the field `K`,
-- every `K`-module is free and hence projective, so the projectivity of `Ω[K⁄k]` is automatic.
-- This leaves exactly the vanishing condition on the first cotangent homology module.
/-- Lemma 10.158.6: for a field extension `K/k`, `K` is formally smooth over `k` if and only if
the first cotangent homology `H_1(L_{K/k})` vanishes. In the canonical mathlib formulation, this
vanishing is expressed as `Subsingleton (H1Cotangent k K)`. -/
theorem formallySmooth_iff_subsingleton_h1Cotangent_of_field :
    Algebra.FormallySmooth k K ↔ Subsingleton (Algebra.H1Cotangent k K) := by
  rw [Algebra.formallySmooth_iff]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨inferInstance, h⟩

end

end Algebra

/-! ### Lemma_10_158_7 (from Chap10) -/
universe u v

namespace Algebra

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/- Domain-style sampling for Lemma 10.158.7:
- primary domain: field extensions and the formal smoothness / separability interface over a base
  field;
- sampled owner declarations:
  `isPurelyTranscendental_iff_exists_algebraicIndependent`,
  `Algebra.FormallySmooth.of_algebraicIndependent`,
  `Algebra.FormallyEtale.of_isSeparable`,
  `Algebra.IsSeparableOver`;
- best owner abstraction: the canonical owner `Algebra.FormallySmooth k K`, with the source-facing
  chapter predicates `IsPurelyTranscendental` and `IsSeparableOver` treated as bridge inputs;
- primitive data: the field extension `K / k` together with the source-facing hypotheses
  `IsPurelyTranscendental k K`, `[Algebra.IsSeparable k K]`, or `[Algebra.IsSeparableOver k K]`;
- derived API: the formal smoothness conclusion and the low-priority instance exported from the
  source-facing theorem in part `(3)`.

Source/core/bridge triage:
- `source-facing`: the three textbook implications in Lemma 10.158.7;
- `core/canonical`: `Algebra.FormallySmooth k K` and the exact mathlib owners
  `Algebra.FormallySmooth.of_algebraicIndependent` and
  `Algebra.FormallyEtale.of_isSeparable`;
- `bridge/view`: the chapter owners `IsPurelyTranscendental` and `IsSeparableOver`.
-/

/-- Lemma 10.158.7 (1): a purely transcendental field extension is formally smooth over the base
field. -/
theorem formallySmooth_of_purelyTranscendental
    (hK : IsPurelyTranscendental k K) :
    Algebra.FormallySmooth k K := by
  rcases isPurelyTranscendental_iff_exists_algebraicIndependent.mp hK with
    ⟨ι, x, hx, hx_top⟩
  exact Algebra.FormallySmooth.of_algebraicIndependent hx hx_top

/-- Lemma 10.158.7 (2): a separable algebraic field extension is formally smooth over the base
field. -/
theorem formallySmooth_of_isSeparable [Algebra.IsSeparable k K] :
    Algebra.FormallySmooth k K := by
  letI : Algebra.FormallyEtale k K := Algebra.FormallyEtale.of_isSeparable k K
  infer_instance

/-- Lemma 10.158.7 (3): a separable field extension in the Stacks Project sense is formally smooth
over the base field. -/
-- Proof sketch: write `K` as the filtered union of its finitely generated intermediate
-- extensions; each such subextension is separably generated, hence formally smooth by parts (1)
-- and (2), and then pass to the filtered colimit criterion for formal smoothness of field
-- extensions.
theorem formallySmooth_of_isSeparableOver [IsSeparableOver k K] :
    Algebra.FormallySmooth k K := sorry

/-- Low-priority instance supplied by Lemma 10.158.7 (3). -/
@[instance low] instance [IsSeparableOver k K] : Algebra.FormallySmooth k K :=
  formallySmooth_of_isSeparableOver

end

end Algebra

/-! ### Lemma_10_158_8 (from Chap10) -/
universe u v

namespace Algebra

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/- Domain-style sampling for Lemma 10.158.8:
- primary domain: field extensions and the comparison between formal smoothness and the
  Stacks-project separability owner `Algebra.IsSeparableOver`;
- sampled owner declarations:
  `Algebra.formallySmooth_of_charZero`,
  `Algebra.isSeparableOver_of_formallySmooth`,
  `Algebra.formallySmooth_of_isSeparableOver`;
- best owner abstraction: the chapter owner pair `Algebra.IsSeparableOver k K` and
  `Algebra.FormallySmooth k K`, with characteristic assumptions used only when they add genuine
  mathematical content;
- primitive data: the field extension `K / k`;
- derived API: the characteristic-zero consequence and the bidirectional bridge between the two
  owner predicates.

Source/core/bridge triage:
- `source-facing`: the characteristic-zero formal-smoothness statement and the source's
  positive-characteristic equivalence;
- `core/canonical`: `Algebra.IsSeparableOver k K` and `Algebra.FormallySmooth k K`;
- `bridge/view`: `Algebra.formallySmooth_of_charZero`,
  `isSeparableOver_of_formallySmooth`, and `formallySmooth_of_isSeparableOver`.

The source states part `(2)` only in characteristic `p > 0`, but after Lemmas `10.158.5` and
`10.158.7` that hypothesis is redundant. The refined owner statement is therefore the
unconditional equivalence between the two chapter owners.
-/
/- Lemma 10.158.8 (1): if the characteristic of `k` is zero, then every field extension `K / k`
is formally smooth over `k`. This is Proposition `10.158.9 (3)`, now kept under the canonical
owner name `Algebra.formallySmooth_of_charZero`. -/
recall Algebra.formallySmooth_of_charZero

/-- Lemma 10.158.8 (2): for field extensions, formal smoothness over `k` is equivalent to
separability in the Stacks Project sense. In the source this is stated in characteristic `p > 0`,
but the characteristic hypothesis is redundant after Lemmas `10.158.5` and `10.158.7`. -/
theorem formallySmooth_iff_isSeparableOver :
    Algebra.FormallySmooth k K ↔ Algebra.IsSeparableOver k K := by
  constructor
  · intro h
    letI : Algebra.FormallySmooth k K := h
    exact Algebra.isSeparableOver_of_formallySmooth
  · intro h
    letI : Algebra.IsSeparableOver k K := h
    exact Algebra.formallySmooth_of_isSeparableOver

end

end Algebra

/-! ### Proposition_10_158_9 (from Chap10) -/
open scoped TensorProduct

universe u v

namespace Algebra

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/- Domain-style sampling for Proposition 10.158.9:
- primary domain: field extensions over a base field, with the source-facing properties
  separability in the Stacks Project sense, geometric reducedness, formal smoothness, vanishing of
  `H¹(L_)`, and injectivity of the Jacobi-Zariski base-change map on Kähler differentials;
- sampled owner declarations:
  `Algebra.IsSeparableOver.of_perfectField`,
  `_root_.isGeometricallyReduced_of_isSeparableOver`,
  `Algebra.formallySmooth_iff_subsingleton_h1Cotangent_of_field`,
  `kaehlerDifferential_transitivity_sequence_splits_of_formallySmooth`;
- best owner abstraction: the existing owner predicates
  `Algebra.IsSeparableOver k K`, `Algebra.IsGeometricallyReduced k K`,
  `Algebra.FormallySmooth k K`, and the owner maps on `Algebra.H1Cotangent` and
  `KaehlerDifferential`;
- primitive data: only the field extension `K / k` and the characteristic assumptions;
- derived API: the characteristic-zero specializations and the characteristic-`p` six-way TFAE.

Source/core/bridge triage:
- `source-facing`: the numbered proposition parts, especially the characteristic-`p` TFAE;
- `core/canonical`: the owner predicates above and the canonical Jacobi-Zariski maps;
- `bridge/view`: perfect-field reduction in characteristic zero, geometric reducedness from
  Stacks-separability, the field-level `FormallySmooth ↔ Subsingleton H1Cotangent` bridge, and the
  split transitivity sequence for Kähler differentials.
-/

-- Proof sketch: in characteristic zero every finitely generated intermediate extension is
-- separably generated, since after choosing a transcendence basis the remaining algebraic part is
-- automatically separable. This is exactly the Stacks Project notion `Algebra.IsSeparableOver`.
/-- Proposition 10.158.9 (1): if the characteristic of `k` is zero, then the field extension
`K / k` is separable in the Stacks Project sense. -/
theorem isSeparableOver_of_charZero [CharZero k] :
    Algebra.IsSeparableOver k K := by
  letI : PerfectField k := PerfectField.ofCharZero
  exact Algebra.IsSeparableOver.of_perfectField

-- Proof sketch: combine part (1) with the equivalence between separability and geometric
-- reducedness for field extensions in characteristic `p`, and use the characteristic-zero argument
-- that every finitely generated intermediate extension is separably generated.
/-- Proposition 10.158.9 (2): if the characteristic of `k` is zero, then `K` is geometrically
reduced over `k`. -/
theorem isGeometricallyReduced_of_charZero [CharZero k] :
    Algebra.IsGeometricallyReduced k K := by
  letI : Algebra.IsSeparableOver k K := isSeparableOver_of_charZero
  exact _root_.isGeometricallyReduced_of_isSeparableOver

-- Proof sketch: every finitely generated intermediate extension of a characteristic-zero field is
-- separably generated, so the Stacks Project notion of separability holds; then Lemma `10.158.7`
-- upgrades separability to formal smoothness.
/-- Proposition 10.158.9 (3): if the characteristic of `k` is zero, then `K` is formally smooth
over `k`. -/
theorem formallySmooth_of_charZero [CharZero k] :
    Algebra.FormallySmooth k K := by
  letI : Algebra.IsSeparableOver k K := isSeparableOver_of_charZero
  exact Algebra.formallySmooth_of_isSeparableOver

-- Proof sketch: apply Proposition `10.158.9 (3)` together with Lemma `10.158.6`, which identifies
-- formal smoothness of a field extension with vanishing of the first cotangent homology module.
/-- Proposition 10.158.9 (4): if the characteristic of `k` is zero, then `H_1(L_{K/k}) = 0`.
In the canonical mathlib formulation, this is `Subsingleton (Algebra.H1Cotangent k K)`. -/
theorem subsingleton_h1Cotangent_of_charZero [CharZero k] :
    Subsingleton (Algebra.H1Cotangent k K) := by
  exact
    (Algebra.formallySmooth_iff_subsingleton_h1Cotangent_of_field k K).1
      formallySmooth_of_charZero

-- Proof sketch: apply Proposition `10.158.9 (3)` and then use the split short exact sequence for
-- Kähler differentials of a formally smooth algebra map from Lemma `10.138.9` with base ring `ℤ`.
/-- Proposition 10.158.9 (5): if the characteristic of `k` is zero, then the canonical map
`K ⊗[k] Ω[k⁄ℤ] → Ω[K⁄ℤ]` is injective. -/
theorem kaehlerDifferential_mapBaseChange_int_injective_of_charZero [CharZero k] :
    Function.Injective (KaehlerDifferential.mapBaseChange ℤ k K) := sorry

variable {p : ℕ} [Fact p.Prime] [CharP k p]

-- Proof sketch: clauses `(1)`, `(2)`, and `(3)` come from Lemma `10.44.2`; clause `(6)` is the
-- formal-smoothness owner bridge from Lemma `10.158.7`; clause `(5)` is the field-level
-- cotangent-homology reformulation from Lemma `10.158.6`; and clause `(4)` is the
-- Kähler-differential injectivity clause singled out by the owner theorem below, whose
-- `(1) ↔ (4)` and `(6) → (1)` projections are recorded downstream in Lemmas `10.158.4` and
-- `10.158.5`.
/-- Proposition 10.158.9 (6): if the characteristic of `k` is `p > 0`, then the following are
equivalent for the field extension `K / k`: `K` is separable over `k`, `K ⊗[k] k^{1/p}` is
reduced, `K` is geometrically reduced over `k`, the canonical map
`K ⊗[k] Ω[k⁄ZMod p] → Ω[K⁄ZMod p]` is injective, `H_1(L_{K/k}) = 0`, and `K` is formally smooth
over `k`. The chosen model of `k^{1/p}` is `onePthRootExtension k p`, and the vanishing of
`H_1(L_{K/k})` is expressed as `Subsingleton (Algebra.H1Cotangent k K)`. -/
theorem char_p_field_extension_tfae_separable_reduced_one_pth_root_geometrically_reduced_kaehler_injective_h1_cotangent_formally_smooth :
    by
      letI : Algebra (ZMod p) k := ZMod.algebra k p
      letI : CharP K p := CharP.of_ringHom_of_ne_zero (algebraMap k K) p (Fact.out : p.Prime).ne_zero
      letI : Algebra (ZMod p) K := ZMod.algebra K p
      letI : IsScalarTower (ZMod p) k K := by infer_instance
      exact
        List.TFAE [
          Algebra.IsSeparableOver k K,
          IsReduced (K ⊗[k] onePthRootExtension k p),
          Algebra.IsGeometricallyReduced k K,
          Function.Injective (KaehlerDifferential.mapBaseChange (ZMod p) k K),
          Subsingleton (Algebra.H1Cotangent k K),
          Algebra.FormallySmooth k K
        ] := sorry

end

end Algebra
