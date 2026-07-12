import Mathlib
import StacksProject_2024.Chap09.Lemma_9_28_2
import StacksProject_2024.Chap10.Definition_10_42_1
import StacksProject_2024.Chap10.Lemma_10_42_4
import StacksProject_2024.Chap10.Lemma_10_42_3
import StacksProject_2024.Chap10.Definition_10_45_1
import StacksProject_2024.Chap10.Lemma_10_131_14
import StacksProject_2024.Chap10.Lemma_10_150_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

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
    have ht_mem : coeff t.1 ∈ (S : Set K) := by
      have ht_finset : coeff t.1 ∈ S := by
        apply Finset.mem_insert.mpr
        right
        apply Finset.mem_union.mpr
        left
        exact Finset.mem_image.mpr ⟨t.1, t.2, rfl⟩
      exact ht_finset
    exact IntermediateField.subset_adjoin (F := k) (S := (S : Set K)) ht_mem
  have hcarrier_mem_L :
      ∀ t : ↥T, ∀ x ∈ relationCarrierSet (k := k) (relationData t), x ∈ L := by
    intro t x hx
    -- Every field element appearing in one chosen relation generator was inserted into the carrier.
    have hx_mem : x ∈ (S : Set K) := by
      have hx_finset : x ∈ S := by
        apply Finset.mem_insert.mpr
        right
        apply Finset.mem_union.mpr
        right
        refine Finset.mem_biUnion.mpr ⟨⟨t.1, t.2⟩, by simp, ?_⟩
        exact (Set.Finite.mem_toFinset (relationCarrierSet_finite (k := k) (relationData t))).2 hx
      exact hx_finset
    exact IntermediateField.subset_adjoin (F := k) (S := (S : Set K)) hx_mem
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

section

variable [PerfectField k]

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

end

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

/-- Helper for Lemma 10.158.2: the `m`-coefficient of `X i * pderiv i f` is the expected scalar
multiple of the `m`-coefficient of `f`. -/
private theorem coeff_X_mul_pderiv
    {r : ℕ} (f : MvPolynomial (Fin r) k) (i : Fin r) (m : Fin r →₀ ℕ) :
    (MvPolynomial.X i * MvPolynomial.pderiv i f).coeff m = m i * f.coeff m := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg =>
      -- Compare coefficients after distributing both the product and the partial derivative.
      simp [hf, hg, mul_add]
  | monomial d a =>
      -- On one monomial this is exactly the standard `X_i * ∂_i` computation.
      by_cases hdm : d = m
      · subst hdm
        rw [MvPolynomial.X_mul_pderiv_monomial, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]
        simp
      · rw [MvPolynomial.X_mul_pderiv_monomial, MvPolynomial.coeff_smul]
        simp [MvPolynomial.coeff_monomial, hdm]

section

variable {p : ℕ} [CharP k p]

/-- Helper for Lemma 10.158.2: if every partial derivative of `f` vanishes, then every exponent in
every support monomial of `f` is divisible by `p`. -/
private theorem dvd_of_mem_support_of_allPderivEqZero
    {r : ℕ} (f : MvPolynomial (Fin r) k)
    (hf : ∀ i : Fin r, MvPolynomial.pderiv i f = 0)
    {m : Fin r →₀ ℕ} (hm : m ∈ f.support) (i : Fin r) :
    p ∣ m i := by
  have hcoeff_zero :
      (MvPolynomial.X i * MvPolynomial.pderiv i f).coeff m = 0 := by
    simp [hf i]
  rw [coeff_X_mul_pderiv (k := k) f i m] at hcoeff_zero
  have hmcoeff : f.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hcast_zero : (m i : k) = 0 := by
    exact (mul_eq_zero.mp hcoeff_zero).resolve_right hmcoeff
  exact (CharP.cast_eq_zero_iff k p (m i)).mp hcast_zero

end

section

variable {p : ℕ} [CharP k p]

/-- Helper for Lemma 10.158.2: after all partial derivatives vanish, every coefficient outside the
`p`-multiple support pattern is forced to be zero. -/
private theorem coeff_eq_zero_of_not_dvd_of_allPderivEqZero
    {r : ℕ} (f : MvPolynomial (Fin r) k)
    (hf : ∀ i : Fin r, MvPolynomial.pderiv i f = 0)
    {m : Fin r →₀ ℕ} {i : Fin r} (h : ¬ p ∣ m i) :
    f.coeff m = 0 := by
  by_cases hm : m ∈ f.support
  · exact (h (dvd_of_mem_support_of_allPderivEqZero (k := k) (p := p) f hf hm i)).elim
  · exact MvPolynomial.notMem_support_iff.mp hm

end

/-- Helper for Lemma 10.158.2: a polynomial cannot divide a nonzero partial derivative of itself,
because multiplying back by `X i` raises total degree while keeping support inside the original
support. -/
private theorem pderiv_eq_zero_of_dvd
    {r : ℕ} (f : MvPolynomial (Fin r) k) (i : Fin r)
    (hdiv : f ∣ MvPolynomial.pderiv i f) :
    MvPolynomial.pderiv i f = 0 := by
  by_contra hderiv_ne
  have hsupport :
      (MvPolynomial.X i * MvPolynomial.pderiv i f).support ⊆ f.support := by
    intro m hm
    by_contra hm'
    have hcoeff_zero :
        (MvPolynomial.X i * MvPolynomial.pderiv i f).coeff m = 0 := by
      rw [coeff_X_mul_pderiv (k := k) f i m, MvPolynomial.notMem_support_iff.mp hm']
      simp
    exact (MvPolynomial.mem_support_iff.mp hm) hcoeff_zero
  have hdeg_step :
      (MvPolynomial.pderiv i f).totalDegree + 1 ≤ f.totalDegree := by
    have hdeg_le :
        (MvPolynomial.X i * MvPolynomial.pderiv i f).totalDegree ≤ f.totalDegree :=
      MvPolynomial.totalDegree_le_of_support_subset hsupport
    have hdeg_mul :
        (MvPolynomial.X i * MvPolynomial.pderiv i f).totalDegree =
          (MvPolynomial.pderiv i f).totalDegree + 1 := by
      rw [MvPolynomial.totalDegree_mul_of_isDomain
        (f := MvPolynomial.X i) (g := MvPolynomial.pderiv i f) (by simp) hderiv_ne,
        MvPolynomial.totalDegree_X]
      simp [Nat.add_comm]
    simpa [hdeg_mul, Nat.add_comm]
      using hdeg_le
  have hdeg_dvd :
      f.totalDegree ≤ (MvPolynomial.pderiv i f).totalDegree :=
    MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hderiv_ne
  exact (Nat.not_lt_of_ge hdeg_dvd) (Nat.lt_of_succ_le hdeg_step)

/-- Helper for Lemma 10.158.2: after clearing denominators in a reduced fraction relation, the
canonical numerator and denominator have zero partial derivatives coordinatewise. -/
private theorem pderiv_eq_zero_of_reduced_fraction_relation
    {r : ℕ} (num den : MvPolynomial (Fin r) k)
    (_hden_ne : den ≠ 0) (hrelPrime : IsRelPrime num den)
    (hrel :
      ∀ i : Fin r,
        den * MvPolynomial.pderiv i num = num * MvPolynomial.pderiv i den) :
    ∀ i : Fin r,
      MvPolynomial.pderiv i num = 0 ∧ MvPolynomial.pderiv i den = 0 := by
  intro i
  have hnum_dvd : num ∣ MvPolynomial.pderiv i num := by
    apply hrelPrime.dvd_of_dvd_mul_left
    rw [hrel i]
    exact dvd_mul_right num (MvPolynomial.pderiv i den)
  have hden_dvd : den ∣ MvPolynomial.pderiv i den := by
    apply hrelPrime.symm.dvd_of_dvd_mul_left
    rw [← hrel i]
    exact dvd_mul_right den (MvPolynomial.pderiv i num)
  constructor
  · -- The numerator-divisibility conclusion now collapses by the total-degree argument.
    exact pderiv_eq_zero_of_dvd (k := k) num i hnum_dvd
  · -- The same total-degree argument applies symmetrically to the denominator.
    exact pderiv_eq_zero_of_dvd (k := k) den i hden_dvd

section

variable {p : ℕ} [Fact p.Prime]

/-- Helper for Lemma 10.158.2: if every support exponent is divisible by `p`, then the polynomial
comes by `MvPolynomial.expand p` from a polynomial with divided exponents. -/
private theorem exists_expand_preimage_of_support_dvd
    {r : ℕ} (f : MvPolynomial (Fin r) k)
    (hsupp : ∀ m ∈ f.support, ∀ i : Fin r, p ∣ m i) :
    ∃ g : MvPolynomial (Fin r) k, MvPolynomial.expand p g = f := by
  classical
  let divideExponent : (Fin r →₀ ℕ) → (Fin r →₀ ℕ) := fun m ↦
    Finsupp.onFinset Finset.univ (fun i ↦ m i / p) (by
      intro i hi
      simp)
  have hdivide_mul : ∀ d : Fin r →₀ ℕ, divideExponent (p • d) = d := by
    intro d
    ext i
    change ((p • d) i) / p = d i
    simpa [nsmul_eq_mul, Nat.mul_comm] using
      (Nat.mul_div_right (d i) (Nat.Prime.pos Fact.out))
  have hmul_divideExponent :
      ∀ {m : Fin r →₀ ℕ}, m ∈ f.support → p • divideExponent m = m := by
    intro m hm
    ext i
    simp [divideExponent, hsupp m hm i, Nat.mul_div_cancel']
  let g : MvPolynomial (Fin r) k :=
    f.support.attach.sum fun m ↦ MvPolynomial.monomial (divideExponent m.1) (f.coeff m.1)
  have hgcoeff :
      ∀ d : Fin r →₀ ℕ, g.coeff d = f.coeff (p • d) := by
    intro d
    by_cases hd : p • d ∈ f.support
    · unfold g
      rw [MvPolynomial.coeff_sum]
      rw [Finset.sum_eq_single ⟨p • d, hd⟩]
      · rw [hdivide_mul]
        simp [MvPolynomial.coeff_monomial]
      · intro a ha hne
        have hneq : divideExponent a.1 ≠ d := by
          intro hroot
          apply hne
          apply Subtype.ext
          calc
            a.1 = p • divideExponent a.1 := by
              symm
              exact hmul_divideExponent a.2
            _ = p • d := by rw [hroot]
        simp [MvPolynomial.coeff_monomial, hneq]
      · intro hnot
        exact (hnot (by simpa using hd)).elim
    · have hfcoeff_zero : f.coeff (p • d) = 0 := MvPolynomial.notMem_support_iff.mp hd
      unfold g
      rw [MvPolynomial.coeff_sum, hfcoeff_zero]
      refine Finset.sum_eq_zero ?_
      intro a ha
      have hneq : divideExponent a.1 ≠ d := by
        intro hroot
        have hpd : p • d = a.1 := by
          calc
            p • d = p • divideExponent a.1 := by rw [← hroot]
            _ = a.1 := hmul_divideExponent a.2
        exact hd (hpd ▸ a.2)
      simp [MvPolynomial.coeff_monomial, hneq]
  refine ⟨g, ?_⟩
  ext m
  by_cases hmdiv : ∀ i : Fin r, p ∣ m i
  · have hm : p • divideExponent m = m := by
      ext i
      simp [divideExponent, hmdiv i, Nat.mul_div_cancel']
    rw [← hm, MvPolynomial.coeff_expand_smul (p := p) (hp := Nat.Prime.ne_zero Fact.out)
      g (divideExponent m), hgcoeff]
  · obtain ⟨i, hi⟩ := not_forall.mp hmdiv
    rw [MvPolynomial.coeff_expand_of_not_dvd (φ := g) (m := m) (i := i) hi]
    by_cases hm : m ∈ f.support
    · exact (hi (hsupp m hm i)).elim
    · exact (MvPolynomial.notMem_support_iff.mp hm).symm

end

section

variable {p : ℕ} [PerfectField k] [Fact p.Prime] [CharP k p]

/-- Helper for Lemma 10.158.2: if every partial derivative of `f` vanishes, then `f` is a `p`th
power because its support comes from `MvPolynomial.expand p` and the perfect base field supplies
the coefficient roots. -/
private theorem exists_pth_root_of_allPderivEqZero_mvPolynomial
    {r : ℕ} (f : MvPolynomial (Fin r) k)
    (hf : ∀ i : Fin r, MvPolynomial.pderiv i f = 0) :
    ∃ g : MvPolynomial (Fin r) k, g ^ p = f := by
  classical
  obtain ⟨f0, hf0⟩ :=
    exists_expand_preimage_of_support_dvd (k := k) (p := p) f
      (fun m hm i ↦ dvd_of_mem_support_of_allPderivEqZero (k := k) (p := p) f hf hm i)
  have hcoeff :
      ∀ d ∈ f0.support, ∃ b : k, b ^ p = f0.coeff d := by
    intro d hd
    obtain ⟨b, hb⟩ := surjective_frobenius k p (f0.coeff d)
    exact ⟨b, by simpa [frobenius_def] using hb⟩
  obtain ⟨g, hg⟩ :=
    mvPolynomial_image_is_pth_power_of_coeff_roots
      (k := k) (k' := k) (p := p) (f := f0) hcoeff
  have hg' : MvPolynomial.expand p f0 = g ^ p := by
    simpa [MvPolynomial.map_id] using hg
  refine ⟨g, ?_⟩
  calc
    g ^ p = MvPolynomial.expand p f0 := hg'.symm
    _ = f := hf0

end

/-- Helper for Chap10 Lemma 10 158 2: package the `dx_i`-coordinate of the transported universal
derivation on `FractionRing (MvPolynomial (Fin r) k)` as an ordinary scalar-valued derivation. -/
private noncomputable def fractionMvPolynomialCoordinateDerivation
    {r : ℕ} (i : Fin r) :
    Derivation k (FractionRing (MvPolynomial (Fin r) k)) (FractionRing (MvPolynomial (Fin r) k)) :=
  let R := MvPolynomial (Fin r) k
  let K0 := FractionRing R
  letI : Algebra.FormallyEtale R K0 := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R)
  (((Finsupp.lapply i).comp
      (((fractionMvPolynomialDifferentialBasis (k := k) r).repr).toLinearMap.comp
        (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R K0).symm.toLinearMap)).compDer
    (KaehlerDifferential.D k K0))

/-- Helper for Chap10 Lemma 10 158 2: the packaged coordinate derivation still computes
localized partial derivatives on algebra-map inputs. -/
private theorem fractionMvPolynomialCoordinateDerivation_algebraMap
    {r : ℕ} (a : MvPolynomial (Fin r) k) (i : Fin r) :
    let R := MvPolynomial (Fin r) k
    let K0 := FractionRing R
    fractionMvPolynomialCoordinateDerivation (k := k) i (algebraMap R K0 a) =
      algebraMap R K0 (MvPolynomial.pderiv i a) := by
  let R := MvPolynomial (Fin r) k
  let K0 := FractionRing R
  letI : Algebra.FormallyEtale R K0 := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R)
  -- The packaged derivation is exactly the existing transported coordinate projection.
  change
    ((Finsupp.lapply i).comp
        (((fractionMvPolynomialDifferentialBasis (k := k) r).repr).toLinearMap.comp
          (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R K0).symm.toLinearMap))
      (KaehlerDifferential.D k K0 (algebraMap R K0 a)) =
      algebraMap R K0 (MvPolynomial.pderiv i a)
  simpa using fractionMvPolynomial_coordinate_algebraMap (k := k) (a := a) (i := i)

/-- Helper for Chap10 Lemma 10 158 2: differentiating the canonical reduced product identity for a
rational function yields the cleared partial-derivative relation on its numerator and denominator. -/
private theorem fractionMvPolynomialClearedPderivRelation
    {r : ℕ} (z : FractionRing (MvPolynomial (Fin r) k))
    (hz : KaehlerDifferential.D k (FractionRing (MvPolynomial (Fin r) k)) z = 0) :
    ∀ j : Fin r,
      (IsFractionRing.den (MvPolynomial (Fin r) k) z : MvPolynomial (Fin r) k) *
          MvPolynomial.pderiv j (IsFractionRing.num (MvPolynomial (Fin r) k) z) =
        IsFractionRing.num (MvPolynomial (Fin r) k) z *
          MvPolynomial.pderiv j (IsFractionRing.den (MvPolynomial (Fin r) k) z) := by
  let R := MvPolynomial (Fin r) k
  let K0 := FractionRing R
  let num : R := IsFractionRing.num R z
  let den : R := IsFractionRing.den R z
  have hzcoord :
      ∀ i : Fin r, fractionMvPolynomialCoordinateDerivation (k := k) (r := r) i z = 0 := by
    intro i
    -- The packaged coordinate derivation factors through `D z`, so `hz` kills every coordinate.
    change
      ((fractionMvPolynomialDifferentialBasis (k := k) r).repr
        ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R K0).symm
          (KaehlerDifferential.D k K0 z))) i = 0
    rw [hz]
    rw [LinearEquiv.map_zero, LinearEquiv.map_zero]
    simp
  have hden_ne : den ≠ 0 := by
    -- The canonical denominator lies in the localization's non-zero-divisor submonoid.
    change ((IsFractionRing.den R z : nonZeroDivisors R) : R) ≠ 0
    exact mem_nonZeroDivisors_iff_ne_zero.mp (IsFractionRing.den R z).2
  have hden_map_ne : algebraMap R K0 den ≠ 0 := by
    intro h0
    apply hden_ne
    exact IsFractionRing.injective R K0 (by simpa using h0)
  have hfrac :
      algebraMap R K0 num / algebraMap R K0 den = z := by
    simpa [R, num, den] using fractionMvPolynomial_num_den_eq (k := k) (z := z)
  have hprod :
      algebraMap R K0 num = z * algebraMap R K0 den := by
    exact (div_eq_iff hden_map_ne).mp hfrac
  intro j
  let δ : Fin r → Derivation k K0 K0 :=
    fun j ↦ fractionMvPolynomialCoordinateDerivation (k := k) (r := r) j
  have hcoordRaw : δ j (algebraMap R K0 num) = δ j (z * algebraMap R K0 den) := by
    exact congrArg (δ j) hprod
  have hcoord :
      algebraMap R K0 (MvPolynomial.pderiv j num) =
        z * algebraMap R K0 (MvPolynomial.pderiv j den) := by
    -- Differentiate the product identity and rewrite each algebra-map term by the coordinate rule.
    have hδnum :
        δ j (algebraMap R K0 num) = algebraMap R K0 (MvPolynomial.pderiv j num) := by
      simpa [δ] using
        fractionMvPolynomialCoordinateDerivation_algebraMap
          (k := k) (r := r) (a := num) (i := j)
    have hδden :
        δ j (algebraMap R K0 den) = algebraMap R K0 (MvPolynomial.pderiv j den) := by
      simpa [δ] using
        fractionMvPolynomialCoordinateDerivation_algebraMap
          (k := k) (r := r) (a := den) (i := j)
    have hδz : δ j z = 0 := by
      simpa [δ] using hzcoord j
    rw [Derivation.leibniz, hδnum, hδden, hδz] at hcoordRaw
    simpa [Algebra.smul_def, δ] using hcoordRaw
  have hclear :
      algebraMap R K0 (den * MvPolynomial.pderiv j num) =
        algebraMap R K0 (num * MvPolynomial.pderiv j den) := by
    -- Multiply the differentiated identity by the denominator and rewrite back to the product form.
    calc
      algebraMap R K0 (den * MvPolynomial.pderiv j num)
          = algebraMap R K0 den * algebraMap R K0 (MvPolynomial.pderiv j num) := by
              rw [map_mul]
      _ = algebraMap R K0 den * (z * algebraMap R K0 (MvPolynomial.pderiv j den)) := by
            rw [hcoord]
      _ = (z * algebraMap R K0 den) * algebraMap R K0 (MvPolynomial.pderiv j den) := by
            simp [mul_left_comm, mul_comm]
      _ = algebraMap R K0 num * algebraMap R K0 (MvPolynomial.pderiv j den) := by
            rw [← hprod]
      _ = algebraMap R K0 (num * MvPolynomial.pderiv j den) := by
            rw [map_mul]
  exact IsFractionRing.injective R K0 hclear

section

variable {p : ℕ} [PerfectField k] [Fact p.Prime] [CharP k p]

private theorem exists_pth_root_of_D_eq_zero_fractionMvPolynomial
    {r : ℕ} (z : FractionRing (MvPolynomial (Fin r) k))
    (hz : KaehlerDifferential.D k (FractionRing (MvPolynomial (Fin r) k)) z = 0) :
    ∃ w : FractionRing (MvPolynomial (Fin r) k), w ^ p = z := by
  let R := MvPolynomial (Fin r) k
  let K0 := FractionRing R
  let num : R := IsFractionRing.num R z
  let den : R := IsFractionRing.den R z
  have hden_ne : den ≠ 0 := by
    -- The canonical denominator comes from the localization's non-zero-divisor datum.
    change ((IsFractionRing.den R z : nonZeroDivisors R) : R) ≠ 0
    exact mem_nonZeroDivisors_iff_ne_zero.mp (IsFractionRing.den R z).2
  have hrel :
      ∀ i : Fin r, den * MvPolynomial.pderiv i num = num * MvPolynomial.pderiv i den := by
    -- Package the quotient-rule computation once before invoking the polynomial Frobenius lemmas.
    simpa [R, num, den] using fractionMvPolynomialClearedPderivRelation (k := k) (z := z) hz
  have hrelPrime : IsRelPrime num den := by
    -- The chosen numerator and denominator are already reduced.
    simpa [R, num, den] using fractionMvPolynomial_num_den_reduced (k := k) (z := z)
  have hzero :
      ∀ i : Fin r, MvPolynomial.pderiv i num = 0 ∧ MvPolynomial.pderiv i den = 0 :=
    pderiv_eq_zero_of_reduced_fraction_relation (k := k) num den hden_ne hrelPrime hrel
  have hnum_zero : ∀ i : Fin r, MvPolynomial.pderiv i num = 0 := fun i ↦ (hzero i).1
  have hden_zero : ∀ i : Fin r, MvPolynomial.pderiv i den = 0 := fun i ↦ (hzero i).2
  obtain ⟨numRoot, hnumRoot⟩ :=
    exists_pth_root_of_allPderivEqZero_mvPolynomial (k := k) (p := p) num hnum_zero
  obtain ⟨denRoot, hdenRoot⟩ :=
    exists_pth_root_of_allPderivEqZero_mvPolynomial (k := k) (p := p) den hden_zero
  refine ⟨algebraMap R K0 numRoot / algebraMap R K0 denRoot, ?_⟩
  -- Rebuild the original rational function from the `p`th roots of the reduced numerator and
  -- denominator.
  calc
    (algebraMap R K0 numRoot / algebraMap R K0 denRoot) ^ p
        = (algebraMap R K0 numRoot) ^ p / (algebraMap R K0 denRoot) ^ p := by
            rw [div_pow]
    _ = algebraMap R K0 num / algebraMap R K0 den := by
          rw [← map_pow, hnumRoot, ← map_pow, hdenRoot]
    _ = z := by
          simpa [R, num, den] using fractionMvPolynomial_num_den_eq (k := k) (z := z)

end

/-- Helper for Lemma 10.158.2: evaluate a tensor `L ⊗[F] Ω[F⁄k]` by applying a dual functional
to the Kähler-differential factor and multiplying the resulting scalar into the field factor. -/
private def tensorDualEvalMap
    {F : Type u} {L : Type v} [Field F] [Field L] [Algebra F L]
    (M : Type*) [AddCommGroup M] [Module F M]
    (ell : Module.Dual F M) :
    _root_.TensorProduct F L M →ₗ[F] L :=
  (TensorProduct.rid F L).toLinearMap.comp
    (_root_.TensorProduct.map (R := F) (LinearMap.id : L →ₗ[F] L) ell)

/-- Helper for Lemma 10.158.2: the tensor evaluator sends a pure tensor to the expected scalar
multiple. -/
private theorem tensorDualEvalMap_tmul
    {F : Type u} {L : Type v} [Field F] [Field L] [Algebra F L]
    (M : Type*) [AddCommGroup M] [Module F M]
    (ell : Module.Dual F M) (x : L) (m : M) :
    tensorDualEvalMap (L := L) (M := M) ell (_root_.TensorProduct.tmul F x m) = ell m • x := by
  -- Unfold once and use the canonical tensor-map and right-unit rules.
  simp [tensorDualEvalMap]

section

variable {p : ℕ} [PerfectField k] [Fact p.Prime] [CharP k p]

/-- Helper for Chap10 Lemma 10 158 2: transport the rational-function `p`th-root criterion across
the canonical `aevalEquivField` attached to a finite transcendence basis. -/
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

end

/-- Helper for Chap10 Lemma 10 158 2: after transporting the differentiated minimal-polynomial
relation across the formally étale comparison, only the coefficient-differential tensor sum
survives because `D a = 0`. -/
private theorem transportedMinpolyDifferentialRelation
    {L : Type v} [Field L] [Algebra k L]
    (F : IntermediateField k L)
    (hsep : Algebra.IsSeparable F L)
    (a : L) (ha : KaehlerDifferential.D k L a = 0) :
    Finset.sum (minpoly F a).support
      (fun n ↦
        (a ^ n) ⊗ₜ[F]
          KaehlerDifferential.D k F
            ((minpoly F a).coeff n)) = 0 := by
  let p : Polynomial F := minpoly F a
  letI : Algebra.IsSeparable F L := hsep
  letI : Algebra.FormallyEtale F L := Algebra.FormallyEtale.of_isSeparable F L
  let δ : Derivation k L (_root_.TensorProduct F L (KaehlerDifferential k F)) :=
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k F L).symm.toLinearMap).compDer
      (KaehlerDifferential.D k L)
  have hroot :
      Finset.sum p.support (fun n ↦ a ^ n * algebraMap F L (p.coeff n)) = 0 := by
    -- Rewrite `aeval a p = 0` as a support-indexed sum so the later derivation step is explicit.
    calc
      Finset.sum p.support (fun n ↦ a ^ n * algebraMap F L (p.coeff n)) =
          Finset.sum p.support
            (fun n ↦ Polynomial.aeval a (Polynomial.C (p.coeff n) * Polynomial.X ^ n)) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [Polynomial.C_mul_X_pow_eq_monomial]
            simpa [mul_comm] using
              (Polynomial.aeval_monomial (x := a) (n := n) (r := p.coeff n)).symm
      _ = Polynomial.aeval a (Finset.sum p.support fun n ↦ Polynomial.C (p.coeff n) * Polynomial.X ^ n) := by
            rw [map_sum]
      _ = Polynomial.aeval a p := by
            simpa using congrArg (Polynomial.aeval a) p.as_sum_support_C_mul_X_pow.symm
      _ = 0 := minpoly.aeval F a
  have hδa : δ a = 0 := by
    -- Transporting the zero differential of `a` across the formally étale comparison keeps it zero.
    change (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k F L).symm
        (KaehlerDifferential.D k L a) = 0
    rw [ha, LinearEquiv.map_zero]
  have hδroot :
      δ (Finset.sum p.support (fun n ↦ a ^ n * algebraMap F L (p.coeff n))) = 0 := by
    -- Apply the transported derivation to the support-indexed minimal-polynomial relation.
    simpa using congrArg (fun z : L ↦ δ z) hroot
  have hδalgebraMap (c : F) :
      δ (algebraMap F L c) = 1 ⊗ₜ[F] KaehlerDifferential.D k F c := by
    -- On basis-field scalars, the transported derivation is the formally étale comparison map.
    change (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k F L).symm
        (KaehlerDifferential.D k L (algebraMap F L c)) = 1 ⊗ₜ[F] KaehlerDifferential.D k F c
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  have hδsum :
      Finset.sum p.support
        (fun n ↦
          (a ^ n) ⊗ₜ[F] KaehlerDifferential.D k F (p.coeff n) +
            algebraMap F L (p.coeff n) • (n • a ^ (n - 1) • δ a)) = 0 := by
    -- Expand the derivation termwise; the first summand is the transported coefficient
    -- differential and the second is the usual power-rule contribution from `a`.
    calc
      Finset.sum p.support
          (fun n ↦
            (a ^ n) ⊗ₜ[F] KaehlerDifferential.D k F (p.coeff n) +
              algebraMap F L (p.coeff n) • (n • a ^ (n - 1) • δ a)) =
          Finset.sum p.support (fun n ↦ δ (a ^ n * algebraMap F L (p.coeff n))) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [Derivation.leibniz, Derivation.leibniz_pow, hδalgebraMap]
            rw [TensorProduct.smul_tmul']
            simp
      _ = 0 := by simpa [map_sum] using hδroot
  have hkill :
      Finset.sum p.support (fun n ↦ algebraMap F L (p.coeff n) • (n • a ^ (n - 1) • δ a)) = 0 := by
    -- The power-rule part vanishes because the transported derivation kills `a`.
    refine Finset.sum_eq_zero ?_
    intro n hn
    rw [hδa]
    simp
  -- Remove the vanished `D a` contribution and keep only the coefficient-differential tensor sum.
  rw [Finset.sum_add_distrib, hkill, add_zero] at hδsum
  exact hδsum

/-- Helper for Chap10 Lemma 10 158 2: evaluating the transported tensor relation with a dual
functional turns it into the corresponding scalar polynomial relation. -/
private theorem dualEvaluation_transportMinpolyRelation
    {F : Type*} {L : Type*} [Field F] [Field L] [Algebra k F] [Algebra F L]
    (ell : Module.Dual F (KaehlerDifferential k F)) (a : L) (p : Polynomial F)
    (h :
      Finset.sum p.support
        (fun n ↦ (a ^ n) ⊗ₜ[F] KaehlerDifferential.D k F (p.coeff n)) = 0) :
    Finset.sum p.support
      (fun n ↦ ell (KaehlerDifferential.D k F (p.coeff n)) • a ^ n) = 0 := by
  -- Apply the tensor evaluator termwise to collapse the Kähler-differential factor.
  have hEval := congrArg
    (tensorDualEvalMap (L := L) (M := KaehlerDifferential k F) ell) h
  simpa [tensorDualEvalMap_tmul] using hEval

/-- Helper for Chap10 Lemma 10 158 2: the auxiliary polynomial built from the dualized
coefficient differentials of `minpoly F a` has the expected coefficients. -/
private theorem dualizedMinpolyAuxPolynomial_coeff
    {F : Type*} {L : Type*} [Field F] [Field L] [Algebra k F] [Algebra F L]
    (a : L) (ell : Module.Dual F (KaehlerDifferential k F)) (m : ℕ) :
    let Q : Polynomial F :=
      Finset.sum (minpoly F a).support fun n ↦
        Polynomial.monomial n
          (ell (KaehlerDifferential.D k F ((minpoly F a).coeff n)))
    Q.coeff m = ell (KaehlerDifferential.D k F ((minpoly F a).coeff m)) := by
  by_cases hm : m ∈ (minpoly F a).support
  · -- On the support, the `m`th monomial contributes exactly the desired coefficient.
    change
      (Finset.sum (minpoly F a).support fun n ↦
        Polynomial.monomial n
          (ell (KaehlerDifferential.D k F ((minpoly F a).coeff n)))).coeff m =
        ell (KaehlerDifferential.D k F ((minpoly F a).coeff m))
    rw [Polynomial.finset_sum_coeff, Finset.sum_eq_single_of_mem m hm]
    · simp
    · intro b hb hbm
      simp [Polynomial.coeff_monomial, hbm]
  · -- Away from the support, the minimal-polynomial coefficient and its differential vanish.
    have hcoeff_zero : (minpoly F a).coeff m = 0 := Polynomial.notMem_support_iff.mp hm
    change
      (Finset.sum (minpoly F a).support fun n ↦
        Polynomial.monomial n
          (ell (KaehlerDifferential.D k F ((minpoly F a).coeff n)))).coeff m =
        ell (KaehlerDifferential.D k F ((minpoly F a).coeff m))
    rw [Polynomial.finset_sum_coeff]
    have hsum_zero :
        Finset.sum (minpoly F a).support
          (fun b ↦
            (Polynomial.monomial b
              (ell (KaehlerDifferential.D k F ((minpoly F a).coeff b)))).coeff m) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro b hb
      have hbm : b ≠ m := by
        intro hbm
        exact hm (hbm ▸ hb)
      simp [Polynomial.coeff_monomial, hbm]
    rw [hsum_zero, hcoeff_zero]
    simp

/-- Helper for Chap10 Lemma 10 158 2: the auxiliary polynomial built from the dualized
coefficient differentials of `minpoly F a` has degree strictly less than `minpoly F a`. -/
private theorem dualizedMinpolyAuxPolynomialDegreeLt
    {F : Type*} {L : Type*} [Field F] [Field L] [Algebra k F] [Algebra F L]
    [FiniteDimensional F L]
    (a : L) (ell : Module.Dual F (KaehlerDifferential k F)) :
    let Q : Polynomial F :=
      Finset.sum (minpoly F a).support fun n ↦
        Polynomial.monomial n
          (ell (KaehlerDifferential.D k F ((minpoly F a).coeff n)))
    Q.degree < (minpoly F a).degree := by
  let Q : Polynomial F :=
    Finset.sum (minpoly F a).support fun n ↦
      Polynomial.monomial n
        (ell (KaehlerDifferential.D k F ((minpoly F a).coeff n)))
  have hminpoly_ne : minpoly F a ≠ 0 := minpoly.ne_zero_of_finite F a
  rw [Polynomial.degree_eq_natDegree hminpoly_ne, Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  by_cases hm_eq : m = (minpoly F a).natDegree
  · -- The top coefficient is `1`, so its differential vanishes.
    subst hm_eq
    have hQcoeff :
        Q.coeff (minpoly F a).natDegree =
          ell (KaehlerDifferential.D k F ((minpoly F a).coeff (minpoly F a).natDegree)) := by
      simpa [Q] using
        dualizedMinpolyAuxPolynomial_coeff (k := k) (a := a) (ell := ell)
          (minpoly F a).natDegree
    rw [hQcoeff]
    rw [(minpoly.monic (Algebra.IsIntegral.isIntegral a)).coeff_natDegree]
    simp
  · -- Above the top degree, the minimal-polynomial coefficient is already zero.
    have hm_gt : (minpoly F a).natDegree < m := lt_of_le_of_ne hm (Ne.symm hm_eq)
    have hQcoeff :
        Q.coeff m = ell (KaehlerDifferential.D k F ((minpoly F a).coeff m)) := by
      simpa [Q] using dualizedMinpolyAuxPolynomial_coeff (k := k) (a := a) (ell := ell) m
    rw [hQcoeff]
    simp [Polynomial.coeff_eq_zero_of_natDegree_lt hm_gt]

/-- Helper for Chap10 Lemma 10 158 2: evaluating the dualized auxiliary polynomial at `a`
repackages the transported tensor relation into a scalar minimal-polynomial relation. -/
private theorem dualizedMinpolyAuxPolynomial_aeval_eq_zero
    {F : Type*} {L : Type*} [Field F] [Field L] [Algebra k F] [Algebra F L]
    (a : L) (ell : Module.Dual F (KaehlerDifferential k F))
    (htransport :
      Finset.sum (minpoly F a).support
        (fun n ↦ (a ^ n) ⊗ₜ[F] KaehlerDifferential.D k F ((minpoly F a).coeff n)) = 0) :
    let Q : Polynomial F :=
      Finset.sum (minpoly F a).support fun n ↦
        Polynomial.monomial n
          (ell (KaehlerDifferential.D k F ((minpoly F a).coeff n)))
    Polynomial.aeval a Q = 0 := by
  let Q : Polynomial F :=
    Finset.sum (minpoly F a).support fun n ↦
      Polynomial.monomial n
        (ell (KaehlerDifferential.D k F ((minpoly F a).coeff n)))
  have hscalar :
      Finset.sum (minpoly F a).support
        (fun m ↦ ell (KaehlerDifferential.D k F ((minpoly F a).coeff m)) • a ^ m) = 0 := by
    -- Collapse the transported tensor relation to a scalar relation over the basis field.
    simpa using
      dualEvaluation_transportMinpolyRelation
        (k := k) ell a (minpoly F a) htransport
  -- Repackage the scalarized support sum as an ordinary polynomial evaluation.
  calc
    Polynomial.aeval a Q =
        Finset.sum (minpoly F a).support
          (fun m ↦
            Polynomial.aeval a
              (Polynomial.monomial m
                (ell (KaehlerDifferential.D k F ((minpoly F a).coeff m))))) := by
            simp [Q, map_sum]
    _ =
        Finset.sum (minpoly F a).support
          (fun m ↦ ell (KaehlerDifferential.D k F ((minpoly F a).coeff m)) • a ^ m) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            simp [Polynomial.aeval_monomial, Algebra.smul_def, mul_comm]
    _ = 0 := hscalar

/-- Helper for Chap10 Lemma 10 158 2: the dualized auxiliary polynomial must vanish identically,
because it has `a` as a root while its degree stays below the minimal polynomial of `a`. -/
private theorem dualizedMinpolyAuxPolynomial_eq_zero
    {F : Type*} {L : Type*} [Field F] [Field L] [Algebra k F] [Algebra F L]
    [FiniteDimensional F L]
    (a : L) (ell : Module.Dual F (KaehlerDifferential k F))
    (htransport :
      Finset.sum (minpoly F a).support
        (fun n ↦ (a ^ n) ⊗ₜ[F] KaehlerDifferential.D k F ((minpoly F a).coeff n)) = 0) :
    let Q : Polynomial F :=
      Finset.sum (minpoly F a).support fun n ↦
        Polynomial.monomial n
          (ell (KaehlerDifferential.D k F ((minpoly F a).coeff n)))
    Q = 0 := by
  let Q : Polynomial F :=
    Finset.sum (minpoly F a).support fun n ↦
      Polynomial.monomial n
        (ell (KaehlerDifferential.D k F ((minpoly F a).coeff n)))
  have hQroot : Polynomial.aeval a Q = 0 := by
    -- The previous helper converts the transported tensor relation into the scalar root relation.
    simpa [Q] using
      dualizedMinpolyAuxPolynomial_aeval_eq_zero
        (k := k) (a := a) (ell := ell) htransport
  have hQdeg : Q.degree < (minpoly F a).degree := by
    -- The top coefficient vanishes because `D 1 = 0`, so the auxiliary degree drops.
    simpa [Q] using
      dualizedMinpolyAuxPolynomialDegreeLt (k := k) (a := a) (ell := ell)
  have hQdvd : minpoly F a ∣ Q := minpoly.dvd F a hQroot
  -- Minimality forces every smaller root polynomial to be zero.
  exact Polynomial.eq_zero_of_dvd_of_degree_lt hQdvd hQdeg

private theorem minpoly_coeff_D_eq_zero_of_D_eq_zero_of_separating_basis
    {L : Type v} [Field L] [Algebra k L] {r : ℕ}
    (x : Fin r → L) (_hx : IsTranscendenceBasis k x)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) L)
    (hfd : FiniteDimensional (IntermediateField.adjoin k (Set.range x)) L)
    (a : L) (ha : KaehlerDifferential.D k L a = 0) :
    ∀ n : ℕ,
      KaehlerDifferential.D k (IntermediateField.adjoin k (Set.range x))
        ((minpoly (IntermediateField.adjoin k (Set.range x)) a).coeff n) = 0 := by
  let F : IntermediateField k L := IntermediateField.adjoin k (Set.range x)
  -- Route correction: the raw fraction-field core is now closed, so the only remaining blocker is
  -- the separable-stage coefficient descent. The new route differentiates
  -- `aeval a (minpoly _ a) = 0`, transports once through
  -- `tensorKaehlerEquivOfFormallyEtale`, proves the resulting dualized auxiliary polynomial is zero
  -- for every dual functional via minimality of `minpoly`, and then uses dual separation on the
  -- Kähler module.
  have htransport :
      Finset.sum (minpoly F a).support
        (fun n ↦ (a ^ n) ⊗ₜ[F] KaehlerDifferential.D k F ((minpoly F a).coeff n)) = 0 := by
    -- The transport step is now isolated, so the remaining work is only the scalarized
    -- contradiction against minimality.
    simpa [F] using
      transportedMinpolyDifferentialRelation
        (k := k) (L := L) F hsep a ha
  letI : Algebra.IsSeparable F L := by simpa [F] using hsep
  letI : FiniteDimensional F L := by simpa [F] using hfd
  intro n
  have hdual :
      ∀ ell : Module.Dual F (KaehlerDifferential k F),
        ell (KaehlerDifferential.D k F ((minpoly F a).coeff n)) = 0 := by
    intro ell
    let Q : Polynomial F :=
      Finset.sum (minpoly F a).support fun m ↦
        Polynomial.monomial m
          (ell (KaehlerDifferential.D k F ((minpoly F a).coeff m)))
    have hQzero : Q = 0 := by
      -- The universal dual route replaces the old projective-choice contradiction.
      simpa [Q] using
        dualizedMinpolyAuxPolynomial_eq_zero
          (k := k) (a := a) (ell := ell) htransport
    have hQcoeff :
        Q.coeff n = ell (KaehlerDifferential.D k F ((minpoly F a).coeff n)) := by
      -- The `n`th coefficient of the auxiliary polynomial is exactly the dualized coefficient
      -- differential we want to kill.
      simpa [Q] using dualizedMinpolyAuxPolynomial_coeff (k := k) (a := a) (ell := ell) n
    have hcoeff_zero : Q.coeff n = 0 := by
      simp [hQzero]
    rw [hQcoeff] at hcoeff_zero
    exact hcoeff_zero
  -- Dual separation now upgrades the vanishing of every evaluation to vanishing in the module.
  exact
    (Module.forall_dual_apply_eq_zero_iff F
      (KaehlerDifferential.D k F ((minpoly F a).coeff n))).1 hdual

section

variable {p : ℕ} [PerfectField k] [Fact p.Prime] [CharP k p]

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
/-- Chap10 Lemma 10 158 2: over a perfect field `k` of characteristic `p > 0`, an element of an
extension field `K` has zero Kähler differential over `k` if and only if it is a `p`th power in
`K`. -/
@[stacks 031W]
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

end
