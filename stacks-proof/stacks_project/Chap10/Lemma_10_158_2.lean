import Mathlib
import stacks_project.Chap09.Lemma_9_28_2
import stacks_project.Chap10.Definition_10_42_1
import stacks_project.Chap10.Lemma_10_42_4
import stacks_project.Chap10.Lemma_10_42_3
import stacks_project.Chap10.Definition_10_45_1
import stacks_project.Chap10.Lemma_10_131_14
import stacks_project.Chap10.Lemma_10_150_7

-- Declarations for this item will be appended below by the statement pipeline.

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
