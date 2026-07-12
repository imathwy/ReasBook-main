import StacksProject_2024.Chap15.Lemma_15_97_5
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape
open BerthelotOgusEtaReduction.Nat
open scoped TensorProduct nonZeroDivisors

universe u

section

variable {A : Type u} [CommRing A]

attribute [local instance] HasDerivedCategory.standard

local notation "CpxA" => NatModuleCochainComplex A
local notation "Q" => natComplexToDerived

/- Domain-style sampling:
- primary domain: splitting loci in commutative algebra for the reduced Berthelot-Ogus pair map
  `(1, d^i)` on `η_f M^•`;
- sampled owner declarations:
  `LinearMap.identifiesWithProdSubmodules`,
  `LinearMap.baseChangeIdentifiesWithProdSubmodules`,
  `exists_fgIdeal_iff_baseChangeIdentifiesWithProdSubmodules_of_splitInjection`,
  `BerthelotOgusEtaReduction.Nat.etaReductionPairMap`;
- best owner abstraction:
  `source-facing`: the degree-`i` ideal `J_i(M^•, f)` attached to a bounded-above
    `M : NatModuleCochainComplex A`, available only under the principal-ideal and splitting
    hypotheses that produce it;
  `core/canonical`: the reduced pair map `etaReductionPairMap f M i` together with the generic
    owner predicate `LinearMap.baseChangeIdentifiesWithProdSubmodules`;
  `bridge/view`: the universal-property predicate on ideals of `A ⧸ principalIdeal f`, together
    with the conditional chosen witness obtained after existence and uniqueness are established;
- primitive data vs derived API: the primitive public data are the complex `M`, the degree `i`,
  and the reduced pair map; the universal-property predicate and the conditional canonical ideal are
  derived API on that owner. -/

/-- Helper for Lemma 15.97.8: quotienting a product by the product of two submodules gives the
product of the two quotient modules. -/
private theorem quotient_prod_submodule_equiv
    {M₁ : Type*} [AddCommGroup M₁] [Module A M₁]
    {M₂ : Type*} [AddCommGroup M₂] [Module A M₂]
    (P : Submodule A M₁) (Q : Submodule A M₂) :
    ((M₁ × M₂) ⧸ Submodule.prod P Q) ≃ₗ[A] ((M₁ ⧸ P) × (M₂ ⧸ Q)) := by
  let φ : M₁ × M₂ →ₗ[A] ((M₁ ⧸ P) × (M₂ ⧸ Q)) := LinearMap.prod P.mkQ Q.mkQ
  have hker : LinearMap.ker φ = Submodule.prod P Q := by
    -- Proof comment: the product quotient map vanishes exactly when both coordinates lie in the
    -- prescribed denominator submodules.
    simpa [φ] using (LinearMap.ker_prodMap (f := P.mkQ) (g := Q.mkQ))
  have hsurj : Function.Surjective φ := by
    -- Proof comment: every pair of quotient classes is represented by a pair of ambient elements.
    intro y
    rcases Submodule.mkQ_surjective P y.1 with ⟨x₁, rfl⟩
    rcases Submodule.mkQ_surjective Q y.2 with ⟨x₂, rfl⟩
    exact ⟨(x₁, x₂), rfl⟩
  have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.2 hsurj
  -- Proof comment: rewrite through the actual kernel and then collapse the full range.
  exact
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      (φ.quotKerEquivRange.trans
        ((LinearEquiv.ofEq _ _ hrange).trans Submodule.topEquiv))

/-- Helper for Lemma 15.97.8: quotienting a projective `A`-module by `IM` stays projective over
`A / I`. -/
private theorem projective_quotient_of_projective
    {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Projective A M] (I : Ideal A) :
    Module.Projective (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M)) := by
  have hbase : Module.Projective (A ⧸ I) ((A ⧸ I) ⊗[A] M) := by
    -- Proof comment: tensoring a projective module with the quotient ring keeps it projective.
    simpa using
      (Module.Projective.tensorProduct
        (R := A ⧸ I) (R₀ := A) (M := A ⧸ I) (N := M))
  -- Proof comment: the standard tensor/quotient comparison identifies the quotient module with
  -- the base change of `M`.
  exact Module.Projective.of_equiv' (TensorProduct.quotTensorEquivQuotSMul M I)

namespace NatModuleCochainComplex

/-- An ideal of `A / fA` has the universal property of `J_i(M^\bullet, f)` if its quotient cuts
out exactly the base changes where the reduced map `(1, d^i)` splits as a product of submodules. -/
abbrev etaReductionDecompositionIdealProperty
    (M : CpxA) (f : A) (i : ℕ) (J : Ideal (A ⧸ principalIdeal f)) : Prop :=
  ∀ (B : Type*) [CommRing B] [Algebra (A ⧸ principalIdeal f) B],
    J ≤ RingHom.ker (algebraMap (A ⧸ principalIdeal f) B) ↔
      (etaReductionPairMap f M i).baseChangeIdentifiesWithProdSubmodules B

private abbrev etaReductionDecompositionIdealPropertySelf
    (M : CpxA) (f : A) (i : ℕ) (J : Ideal (A ⧸ principalIdeal f)) : Prop :=
  ∀ (B : Type u) [CommRing B] [Algebra (A ⧸ principalIdeal f) B],
    J ≤ RingHom.ker (algebraMap (A ⧸ principalIdeal f) B) ↔
      (etaReductionPairMap f M i).baseChangeIdentifiesWithProdSubmodules B

/-- Helper for Lemma 15.97.8: the self-universe version of the universal splitting property still
determines the ideal uniquely. -/
private theorem etaReductionDecompositionIdeal_eq_of_propertySelf
    (M : CpxA) (f : A) (i : ℕ)
    {J J' : Ideal (A ⧸ principalIdeal f)}
    (hJ : etaReductionDecompositionIdealPropertySelf M f i J)
    (hJ' : etaReductionDecompositionIdealPropertySelf M f i J') :
    J = J' := by
  -- Proof comment: test the universal property on the quotient by the competing ideal, where the
  -- kernel of the structure map is exactly that ideal.
  apply le_antisymm
  · let B : Type u := (A ⧸ principalIdeal f) ⧸ J'
    have hJ'ker : J' ≤ RingHom.ker (algebraMap (A ⧸ principalIdeal f) B) := by
      simpa [B, Ideal.mk_ker]
    exact (hJ B).2 ((hJ' B).1 hJ'ker)
  · let B : Type u := (A ⧸ principalIdeal f) ⧸ J
    have hJker : J ≤ RingHom.ker (algebraMap (A ⧸ principalIdeal f) B) := by
      simpa [B, Ideal.mk_ker]
    exact (hJ' B).2 ((hJ B).1 hJker)

/-- The universal property of `J_i(M^\bullet, f)` determines the ideal uniquely whenever such an
ideal exists. -/
theorem etaReductionDecompositionIdeal_eq_of_property
    (M : CpxA) (f : A) (i : ℕ)
    {J J' : Ideal (A ⧸ principalIdeal f)}
    (hJ : M.etaReductionDecompositionIdealProperty f i J)
    (hJ' : M.etaReductionDecompositionIdealProperty f i J') :
    J = J' := by
  -- Proof comment: the public universal property restricts to the self-universe version, and the
  -- quotient test above already proves uniqueness there.
  exact etaReductionDecompositionIdeal_eq_of_propertySelf M f i
    (fun B ↦ hJ B) (fun B ↦ hJ' B)

-- Proof sketch: Lemma `15.97.5` makes the degree-`i` unreduced pair map `(1, d^i)` a split
-- monomorphism with finite projective source over `A ⧸ (f)`, and Lemma `15.97.7` then supplies
-- the finitely generated ideal cutting out exactly the base changes where the reduced map
-- identifies its source with a product of submodules.
/-- Helper for Lemma 15.97.8: the reduced degree term of `η_f M` is finite over `A / fA` once
the determinantal ideal is principal. -/
private theorem etaReductionDegree_finite_of_determinantalIdeal_isPrincipal
    (M : CpxA) (f : A) (i : ℕ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    Module.Finite (A ⧸ principalIdeal f)
      ((CochainComplex.reduceModIdeal (principalIdeal f) (η[f] M)).X i) := by
  letI :
      Module.FiniteLocallyFreeOfRank A ((η[f] M).X i) (Module.finrank A (M.X i)) :=
    etaFDegree_finiteLocallyFreeOfRank_of_determinantalIdeal_isPrincipal
      (A := A) (M := M) (f := f) (i := i) (hf := hf) (hI := hI)
  letI : Module.FiniteLocallyFree A ((η[f] M).X i) :=
    Module.finiteLocallyFree_ofRank
      (R := A) (M := (η[f] M).X i) (Module.finrank A (M.X i))
  have hfiniteProjective :
      Module.Finite A ((η[f] M).X i) ∧ Module.Projective A ((η[f] M).X i) := by
    -- Proof comment: finite local freeness is the canonical bridge to finite projectivity.
    exact (module_finite_projective_tfae (R := A) (M := (η[f] M).X i)).out 6 1 |>.mp
      (show Module.FiniteLocallyFree A ((η[f] M).X i) from inferInstance)
  letI : Module.Finite A ((η[f] M).X i) := hfiniteProjective.1
  letI : Module.Projective A ((η[f] M).X i) := hfiniteProjective.2
  have hfiniteQuotA :
      Module.Finite A (((η[f] M).X i) ⧸
        principalIdeal f • (⊤ : Submodule A ((η[f] M).X i))) := by
    -- Proof comment: quotients of finite modules stay finite over the base ring.
    infer_instance
  have hfiniteQuot :
      Module.Finite (A ⧸ principalIdeal f) (((η[f] M).X i) ⧸
        principalIdeal f • (⊤ : Submodule A ((η[f] M).X i))) := by
    -- Proof comment: the quotient ring is finite over `A`, so finiteness ascends back to the
    -- natural `A / fA`-module structure on the quotient.
    letI : Module.Finite A (((η[f] M).X i) ⧸
      principalIdeal f • (⊤ : Submodule A ((η[f] M).X i))) := hfiniteQuotA
    exact Module.Finite.of_restrictScalars_finite A (A ⧸ principalIdeal f)
      (((η[f] M).X i) ⧸ principalIdeal f • (⊤ : Submodule A ((η[f] M).X i)))
  simpa [CochainComplex.reduceModIdeal] using hfiniteQuot

/-- Helper for Lemma 15.97.8: the reduced degree term of `η_f M` is projective over `A / fA`
once the determinantal ideal is principal. -/
private theorem etaReductionDegree_projective_of_determinantalIdeal_isPrincipal
    (M : CpxA) (f : A) (i : ℕ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    Module.Projective (A ⧸ principalIdeal f)
      ((CochainComplex.reduceModIdeal (principalIdeal f) (η[f] M)).X i) := by
  letI :
      Module.FiniteLocallyFreeOfRank A ((η[f] M).X i) (Module.finrank A (M.X i)) :=
    etaFDegree_finiteLocallyFreeOfRank_of_determinantalIdeal_isPrincipal
      (A := A) (M := M) (f := f) (i := i) (hf := hf) (hI := hI)
  letI : Module.FiniteLocallyFree A ((η[f] M).X i) :=
    Module.finiteLocallyFree_ofRank
      (R := A) (M := (η[f] M).X i) (Module.finrank A (M.X i))
  have hfiniteProjective :
      Module.Finite A ((η[f] M).X i) ∧ Module.Projective A ((η[f] M).X i) := by
    -- Proof comment: finite local freeness is the canonical bridge from the unreduced eta-degree
    -- to finite projectivity over `A`.
    exact (module_finite_projective_tfae (R := A) (M := (η[f] M).X i)).out 6 1 |>.mp
      (show Module.FiniteLocallyFree A ((η[f] M).X i) from inferInstance)
  letI : Module.Projective A ((η[f] M).X i) := hfiniteProjective.2
  have hprojQuot :
      Module.Projective (A ⧸ principalIdeal f)
        (((η[f] M).X i) ⧸
          principalIdeal f • (⊤ : Submodule A ((η[f] M).X i))) := by
    -- Proof comment: specialize the local quotient-projectivity transport to the principal
    -- quotient `A / fA`.
    exact projective_quotient_of_projective
      (A := A) (M := ((η[f] M).X i)) (principalIdeal f)
  simpa [CochainComplex.reduceModIdeal] using hprojQuot

/-- Under the principal-ideal hypothesis on `I_i(M^\bullet, f)`, there exists a finitely
generated ideal `J_i(M^\bullet, f)` in `A / fA` with the universal splitting property for the
reduced map `(1, d^i)`. -/
/-- Helper for Lemma 15.97.8: the split mono on the unreduced Nat pair map descends to a concrete
retraction of the reduced pair map. -/
private theorem etaReductionPairMap_retraction_of_determinantalIdeal_isPrincipal
    (M : CpxA) (f : A) (i : ℕ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    ∃ πred,
      πred.comp (etaReductionPairMap f M i) = LinearMap.id := by
  let hsplit :
      IsSplitMono (ModuleCat.ofHom (etaPairMap f M i)) :=
    etaFDegreePairMap_isSplitMono_of_determinantalIdeal_isPrincipal
      (A := A) (f := f) (M := M) (i := i) (hf := hf) (hI := hI)
  let π :
      powerSubmodule f M i × nextPowerSubmodule f M i →ₗ[A]
        etaFDegreeSubmodule f M i :=
    @retraction (ModuleCat A) _ _ _ (ModuleCat.ofHom (etaPairMap f M i)) hsplit
  let πred :
      ((powerSubmodule f M i ⧸
          principalIdeal f • (⊤ : Submodule A (powerSubmodule f M i))) ×
        (nextPowerSubmodule f M i ⧸
          principalIdeal f • (⊤ : Submodule A (nextPowerSubmodule f M i)))) →ₗ
        [A ⧸ principalIdeal f]
          ((CochainComplex.reduceModIdeal (principalIdeal f) (η[f] M)).X i) :=
    LinearMap.coprod
      (LinearMap.reduceModIdeal (principalIdeal f)
        (π.comp (LinearMap.inl A (powerSubmodule f M i) (nextPowerSubmodule f M i))))
      (LinearMap.reduceModIdeal (principalIdeal f)
        (π.comp (LinearMap.inr A (powerSubmodule f M i) (nextPowerSubmodule f M i)))
)
  refine ⟨πred, ?_⟩
  -- Proof comment: evaluate the reduced composite on quotient generators and use the unreduced
  -- retraction identity `etaPairMap ≫ π = 𝟙`.
  ext x
  refine Submodule.Quotient.inductionOn' x ?_
  intro m
  change
    πred
        ((etaReductionPairMap f M i)
          (Submodule.Quotient.mk m)) =
      Submodule.Quotient.mk m
  have hπ :
      π.comp (etaPairMap f M i) = LinearMap.id := by
    simpa using
      (@retraction_comp (ModuleCat A) _ _ _ (ModuleCat.ofHom (etaPairMap f M i)) hsplit)
  simp only [πred, BerthelotOgusEtaReduction.Nat.etaReductionPairMap,
    LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.reduceModIdeal_apply,
    LinearMap.prod_apply, LinearMap.inl_apply, LinearMap.inr_apply]
  simpa using congrArg Submodule.Quotient.mk (LinearMap.congr_fun hπ m)

/-- Helper for Lemma 15.97.8: the reduced Nat pair map is itself a split monomorphism once the
determinantal ideal is principal. -/
private theorem etaReductionPairMap_isSplitMono_of_determinantalIdeal_isPrincipal
    (M : CpxA) (f : A) (i : ℕ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    IsSplitMono (ModuleCat.ofHom (etaReductionPairMap f M i)) := by
  rcases etaReductionPairMap_retraction_of_determinantalIdeal_isPrincipal
      M f i hf hI with ⟨πred, hπred⟩
  refine IsSplitMono.mk' ⟨ModuleCat.ofHom πred, ?_⟩
  ext x
  simpa using LinearMap.congr_fun hπred x

theorem exists_fg_etaReductionDecompositionIdeal_of_determinantalIdeal_isPrincipal
    (M : CpxA) (f : A) (i : ℕ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    ∃ J : Ideal (A ⧸ principalIdeal f),
      J.FG ∧ M.etaReductionDecompositionIdealProperty f i J := by
  have hfinite :
      Module.Finite (A ⧸ principalIdeal f)
        ((CochainComplex.reduceModIdeal (principalIdeal f) (η[f] M)).X i) :=
    etaReductionDegree_finite_of_determinantalIdeal_isPrincipal M f i hf hI
  have hprojective :
      Module.Projective (A ⧸ principalIdeal f)
        ((CochainComplex.reduceModIdeal (principalIdeal f) (η[f] M)).X i) :=
    etaReductionDegree_projective_of_determinantalIdeal_isPrincipal M f i hf hI
  -- Proof comment: the source module is now fully prepared for Lemma `15.97.7`; the only missing
  -- remaining local adapter is a reduced retraction for the pair map. The generic owner theorem
  -- `15.97.7` is still blocked upstream, so we keep the source-faithful gap explicit here.
  letI :
      Module.Finite (A ⧸ principalIdeal f)
        ((CochainComplex.reduceModIdeal (principalIdeal f) (η[f] M)).X i) :=
    hfinite
  letI :
      Module.Projective (A ⧸ principalIdeal f)
        ((CochainComplex.reduceModIdeal (principalIdeal f) (η[f] M)).X i) :=
    hprojective
  have hsplitReduction :
      IsSplitMono (ModuleCat.ofHom (etaReductionPairMap f M i)) :=
    etaReductionPairMap_isSplitMono_of_determinantalIdeal_isPrincipal M f i hf hI
  letI :
      IsSplitMono (ModuleCat.ofHom (etaReductionPairMap f M i)) :=
    hsplitReduction
  -- Proof comment: the reduced pair map is now known to be a split mono with finite projective
  -- source. The remaining blocker is the finite-projective replacement for the false generic owner
  -- from `Lemma_15_97_7`, namely a local theorem cutting out the splitting locus by a finitely
  -- generated ideal using the concrete reduced retraction above.
  sorry

private theorem exists_fg_etaReductionDecompositionIdealSelf_of_determinantalIdeal_isPrincipal
    (M : CpxA) (f : A) (i : ℕ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    ∃ J : Ideal (A ⧸ principalIdeal f),
      J.FG ∧ etaReductionDecompositionIdealPropertySelf M f i J := by
  -- Proof comment: the public existence theorem already provides the stronger all-universes
  -- property, so we just restrict that witness to `Type u`.
  rcases exists_fg_etaReductionDecompositionIdeal_of_determinantalIdeal_isPrincipal
      M f i hf hI with ⟨J, hJfg, hJ⟩
  exact ⟨J, hJfg, fun B ↦ hJ B⟩

/-- The degree-`i` ideal `J_i(M^\bullet, f)` in `A / fA`, defined only under the principal-ideal
hypothesis that guarantees its existence. -/
noncomputable def etaReductionDecompositionIdeal
    (M : CpxA) (f : A) (i : ℕ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    Ideal (A ⧸ principalIdeal f) :=
  Classical.choose
    (exists_fg_etaReductionDecompositionIdealSelf_of_determinantalIdeal_isPrincipal
      M f i hf hI)

/-- The ideal `J_i(M^\bullet, f)` satisfies its defining universal splitting property. -/
theorem etaReductionDecompositionIdeal_property
    (M : CpxA) (f : A) (i : ℕ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    M.etaReductionDecompositionIdealProperty f i
      (M.etaReductionDecompositionIdeal f i hf hI) := by
  -- Proof comment: compare the canonical witness chosen from the self-universe existence theorem
  -- with any witness from the public existence theorem; self-universe uniqueness identifies the
  -- two ideals, so the canonical one inherits the stronger public property.
  rcases exists_fg_etaReductionDecompositionIdeal_of_determinantalIdeal_isPrincipal
      M f i hf hI with ⟨J, _, hJ⟩
  have hChosen :
      etaReductionDecompositionIdealPropertySelf M f i
        (M.etaReductionDecompositionIdeal f i hf hI) :=
    (Classical.choose_spec
      (exists_fg_etaReductionDecompositionIdealSelf_of_determinantalIdeal_isPrincipal
        M f i hf hI)).2
  have hJself : etaReductionDecompositionIdealPropertySelf M f i J := fun B ↦ hJ B
  have hEq :
      M.etaReductionDecompositionIdeal f i hf hI = J :=
    etaReductionDecompositionIdeal_eq_of_propertySelf M f i hChosen hJself
  simpa [hEq] using hJ

/-- Helper for Lemma 15.97.8: the canonical ideal agrees with any ideal satisfying the same
universal splitting property. -/
private theorem etaReductionDecompositionIdeal_eq_canonical_of_property
    (M : CpxA) (f : A) (i : ℕ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (M.etaDeterminantalIdeal f i).IsPrincipal)
    {J : Ideal (A ⧸ principalIdeal f)}
    (hJ : M.etaReductionDecompositionIdealProperty f i J) :
    M.etaReductionDecompositionIdeal f i hf hI = J := by
  -- Proof comment: the chosen canonical witness already satisfies the same universal property, so
  -- uniqueness identifies it with any competing witness.
  exact etaReductionDecompositionIdeal_eq_of_property M f i
    (M.etaReductionDecompositionIdeal_property f i hf hI) hJ

/-- The degree-`i` ideal `J_i(M^\bullet, f)` is finitely generated. -/
theorem etaReductionDecompositionIdeal_fg
    (M : CpxA) (f : A) (i : ℕ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    (M.etaReductionDecompositionIdeal f i hf hI).FG :=
  (Classical.choose_spec
    (exists_fg_etaReductionDecompositionIdealSelf_of_determinantalIdeal_isPrincipal
      M f i hf hI)).1

end NatModuleCochainComplex

namespace EtaReductionDecompositionIdeal

scoped notation "J[" f "]_(" i ")(" M " ; " hf ", " hI ")" =>
  NatModuleCochainComplex.etaReductionDecompositionIdeal M f i hf hI

end EtaReductionDecompositionIdeal

open scoped EtaReductionDecompositionIdeal

/-- Helper for Lemma 15.97.8: extending a bounded-below finite free Nat complex by zero gives a
termwise finite free `ℤ`-indexed complex. -/
private noncomputable instance extend_embeddingUpNat_isTermwiseFiniteFree
    (M : CpxA)
    [∀ j : ℕ, Module.Free A (M.X j)] [∀ j : ℕ, Module.Finite A (M.X j)] :
    CochainComplex.IsTermwiseFiniteFree (M.extend embeddingUpNat) := by
  refine ⟨fun i ↦ ?_⟩
  by_cases hi : 0 ≤ i
  · let e :
        ((M.extend embeddingUpNat).X i) ≃ₗ[A] M.X i.toNat :=
      (M.extendXIso embeddingUpNat (Int.toNat_of_nonneg hi)).toLinearEquiv
    -- Proof comment: in nonnegative degrees, extension by zero is literally the original term.
    exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩
  · let hzero : CategoryTheory.Limits.IsZero ((M.extend embeddingUpNat).X i) :=
      M.isZero_extend_X embeddingUpNat i (by
        intro n hni
        exact hi (hni ▸ Int.natCast_nonneg n))
    letI : Subsingleton ((M.extend embeddingUpNat).X i) := ModuleCat.subsingleton_of_isZero hzero
    let eZero : ((M.extend embeddingUpNat).X i) ≃ₗ[A] (Fin 0 → A) :=
      LinearEquiv.ofSubsingleton _ _
    -- Proof comment: in negative degrees, the extended complex is zero, hence finite free of
    -- rank `0`.
    exact ⟨Module.Free.of_equiv eZero.symm, Module.Finite.equiv eZero.symm⟩

-- Proof sketch: `natComplexToDerived` is built from the same extension-by-zero functor
-- `embeddingUpNat.extendFunctor` used in the textbook bridge from bounded-below `ℕ`-complexes to
-- bounded-below `ℤ`-complexes, so each object is canonically represented by `M.extend
-- embeddingUpNat` in the ordinary derived category.
/-- Helper for Lemma 15.97.8: the Nat-derived object of `M` is isomorphic to the derived object of
its extension-by-zero `ℤ`-indexed complex. -/
private theorem natComplexToDerived_obj_isomorphic_extend
    (M : CpxA) :
    IsIsomorphic ((Q).obj M) (DerivedCategory.Q.obj (M.extend embeddingUpNat)) := by
  -- Proof comment: compare each bounded-below owner with its ambient unbounded owner in turn:
  -- first `D⁺(A) ↪ D(A)`, then `K⁺(A) ↪ K(A)`, then `Comp⁺(A) ↪ Comp(A)`.
  let Xplus : CochainComplex.Plus (ModuleCat A) := (natComplexToPlus (A := A)).obj M
  let Xhom : K⁺(ModuleCat A) := (HomotopyCategory.Plus.quotient (ModuleCat A)).obj Xplus
  let eDerivedBelow :
      (mapBoundedBelowHomotopyToDerivedBelow :
          K⁺(ModuleCat A) ⥤ D⁺(ModuleCat A)) ⋙
        ObjectProperty.ι
          (DerivedCategory.TStructure.t.plus :
            ObjectProperty (DerivedCategory (ModuleCat A))) ≅
      ObjectProperty.ι (HomotopyCategory.plus (ModuleCat A)) ⋙ DerivedCategory.Qh :=
    ObjectProperty.liftCompιIso
      (DerivedCategory.TStructure.t.plus :
        ObjectProperty (DerivedCategory (ModuleCat A)))
      (ObjectProperty.ι (HomotopyCategory.plus (ModuleCat A)) ⋙ DerivedCategory.Qh)
      (fun X ↦ by
        simpa using (CategoryTheory.qh_obj_mem_t_plus (𝒜 := ModuleCat A) X))
  let ePlusQ :
      HomotopyCategory.Plus.quotient (ModuleCat A) ⋙
        ObjectProperty.ι (HomotopyCategory.plus (ModuleCat A)) ≅
      (CochainComplex.plus (ModuleCat A)).ι ⋙
        HomotopyCategory.quotient (ModuleCat A) (up ℤ) :=
    (HomotopyCategory.plus (ModuleCat A)).liftCompιIso
      ((CochainComplex.plus (ModuleCat A)).ι ⋙
        HomotopyCategory.quotient (ModuleCat A) (up ℤ))
      (fun X ↦ by
        simpa [HomotopyCategory.plus] using X.property)
  let eNatPlus :
      natComplexToPlus (A := A) ⋙ (CochainComplex.plus (ModuleCat A)).ι ≅
        embeddingUpNat.extendFunctor (ModuleCat A) :=
    (CochainComplex.plus (ModuleCat A)).liftCompιIso
      (embeddingUpNat.extendFunctor (ModuleCat A))
      (fun X ↦ ⟨0, by
        change CochainComplex.IsStrictlyGE (X.extend embeddingUpNat) 0
        infer_instance⟩)
  refine ⟨?_⟩
  -- Proof comment: after those three lift comparisons, `DerivedCategory.quotientCompQhIso`
  -- identifies the ambient quotient image with `DerivedCategory.Q.obj`.
  simpa [Q, natComplexToDerived, natComplexToPlus, Xplus, Xhom] using
    (eDerivedBelow.app Xhom ≪≫
      DerivedCategory.Qh.mapIso (ePlusQ.app Xplus) ≪≫
      DerivedCategory.Qh.mapIso
        ((HomotopyCategory.quotient (ModuleCat A) (up ℤ)).mapIso (eNatPlus.app M)) ≪≫
      (DerivedCategory.quotientCompQhIso (ModuleCat A)).app (M.extend embeddingUpNat))

-- Proof sketch: if `(f^n) I` is principal and `f` is regular, choose a generator of `(f^n) I`,
-- divide its defining element by the visible power of `f`, and use cancellation by the
-- nonzerodivisor `f^n` to compare the two principal ideals.
/-- Helper for Lemma 15.97.8: cancelling a visible power of a nonzerodivisor preserves
principality of ideals. -/
private theorem Ideal.isPrincipal_of_mul_principalIdeal_pow_of_nonZeroDivisor
    {I : Ideal A} {f : A} (hf : f ∈ nonZeroDivisors A) (n : ℕ)
    (h : (principalIdeal (f ^ n) * I).IsPrincipal) :
    I.IsPrincipal := by
  let g : A := Submodule.IsPrincipal.generator (principalIdeal (f ^ n) * I)
  have hmul :
      principalIdeal (f ^ n) * I = principalIdeal g := by
    -- Proof comment: principal ideals are identified by their chosen generator.
    simpa [g, principalIdeal] using
      (Ideal.span_singleton_generator (principalIdeal (f ^ n) * I))
  have hg_mem : g ∈ principalIdeal (f ^ n) * I := by
    -- Proof comment: the chosen generator belongs to the principal ideal it generates.
    rw [hmul]
    exact Ideal.mem_span_singleton_self g
  rcases Ideal.mem_span_singleton_mul.mp hg_mem with ⟨y, hyI, hgy⟩
  refine ⟨y, ?_⟩
  apply le_antisymm
  · intro x hx
    have hfx_mem : f ^ n * x ∈ principalIdeal (f ^ n) * I := by
      exact Ideal.mem_span_singleton_mul.mpr ⟨x, hx, rfl⟩
    rw [hmul] at hfx_mem
    rcases Ideal.mem_span_singleton'.mp hfx_mem with ⟨c, hcx⟩
    have hpow_nd : f ^ n ∈ nonZeroDivisors A := pow_mem hf n
    have hcancel_mul : f ^ n * (c * y) = f ^ n * x := by
      calc
        f ^ n * (c * y) = c * g := by
          rw [hgy]
          ring
        _ = f ^ n * x := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hcx
    have hxy : c * y = x :=
      (mem_nonZeroDivisors_iff_left.mp hpow_nd) _ <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hcancel_mul
    exact Ideal.mem_span_singleton'.mpr ⟨c, hxy⟩
  · intro x hx
    rcases Ideal.mem_span_singleton'.mp hx with ⟨c, rfl⟩
    exact I.mul_mem_left _ hyI

-- Proof sketch: apply Lemma `15.97.1` to the bounded-above extensions by zero of `M` and `N`.
-- After balancing the alternating-rank tails by suitable powers of `f`, the resulting equality
-- `f^m I_i(M^•, f) = f^n I_i(N^•, f)` and regularity of `f` show that principality of
-- `I_i(M^•, f)` forces principality of `I_i(N^•, f)`.
/-- The degree-`i` determinantal ideal is principal for `N^\bullet` as soon as it is principal for
`M^\bullet` and the two bounded-above finite free complexes represent the same derived object. This
is the bounded-below bridge/view of Lemma `15.97.1`, used below so that the source-facing equality
of the ideals `J_i` needs only the principality hypothesis on the `M`-side; the comparison
hypothesis stays on the chapter’s canonical theorem-level owner `CategoryTheory.IsIsomorphic`. -/
theorem etaDeterminantalIdeal_isPrincipal_of_same_derivedObject
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M N : CpxA)
    [∀ j : ℕ, Module.Free A (M.X j)] [∀ j : ℕ, Module.Finite A (M.X j)]
    [∀ j : ℕ, Module.Free A (N.X j)] [∀ j : ℕ, Module.Finite A (N.X j)]
    (hMbounded : M.IsBoundedAbove)
    (hNbounded : N.IsBoundedAbove)
    (hMN : IsIsomorphic ((Q).obj M) ((Q).obj N))
    (i : ℕ)
    (hIM : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    (N.etaDeterminantalIdeal f i).IsPrincipal := by
  -- Route correction: the source proof compares the `ℤ`-indexed extension-by-zero complexes via
  -- Lemma `15.97.1`, so we first transport the Nat-derived isomorphism to that owner and only
  -- then cancel the visible power of `f`.
  rcases hMbounded with ⟨bM, hMle⟩
  rcases hNbounded with ⟨bN, hNle⟩
  rcases natComplexToDerived_obj_isomorphic_extend (A := A) M with ⟨eM⟩
  rcases natComplexToDerived_obj_isomorphic_extend (A := A) N with ⟨eN⟩
  rcases hMN with ⟨eMN⟩
  rcases alternatingRankTail_balance_exists
      (alternatingRankTail (M.extend embeddingUpNat) (i : ℤ) (bM : ℤ))
      (alternatingRankTail (N.extend embeddingUpNat) (i : ℤ) (bN : ℤ)) with
    ⟨m, n, hbalance⟩
  have hfreg : IsRegular f := by
    rwa [isRegular_iff_mem_nonZeroDivisors]
  have hpow :
      principalIdeal (f ^ m) * M.etaDeterminantalIdeal f i =
        principalIdeal (f ^ n) * N.etaDeterminantalIdeal f i := by
    -- Proof comment: this is exactly Lemma `15.97.1` on the extension-by-zero representatives.
    simpa [NatModuleCochainComplex.etaDeterminantalIdeal] using
      (pow_etaDeterminantalIdeal_eq_of_same_derivedObject
        (A := A) (f := f) (hf := hfreg)
        (M := M.extend embeddingUpNat) (N := N.extend embeddingUpNat)
        (i := (i : ℤ)) (hMle := hMle) (hNle := hNle)
        (hMN := ⟨eM.symm ≪≫ eMN ≪≫ eN⟩) (hbalance := hbalance))
  letI : (M.etaDeterminantalIdeal f i).IsPrincipal := hIM
  have hleftPrincipal :
      (principalIdeal (f ^ m) * M.etaDeterminantalIdeal f i).IsPrincipal := by
    -- Proof comment: multiplying two principal ideals is again principal.
    refine ⟨f ^ m * Submodule.IsPrincipal.generator (M.etaDeterminantalIdeal f i), ?_⟩
    calc
      principalIdeal (f ^ m) * M.etaDeterminantalIdeal f i =
          principalIdeal (f ^ m) *
            principalIdeal (Submodule.IsPrincipal.generator (M.etaDeterminantalIdeal f i)) := by
              rw [Ideal.span_singleton_generator (M.etaDeterminantalIdeal f i)]
      _ = principalIdeal
            (f ^ m * Submodule.IsPrincipal.generator (M.etaDeterminantalIdeal f i)) := by
              simpa [principalIdeal] using
                Ideal.span_singleton_mul_span_singleton
                  (f ^ m) (Submodule.IsPrincipal.generator (M.etaDeterminantalIdeal f i))
  have hrightPrincipal :
      (principalIdeal (f ^ n) * N.etaDeterminantalIdeal f i).IsPrincipal := by
    -- Proof comment: the power-twisted ideals are equal, so the right-hand one is principal too.
    rw [← hpow]
    exact hleftPrincipal
  -- Proof comment: cancel the visible power of the regular element `f`.
  exact Ideal.isPrincipal_of_mul_principalIdeal_pow_of_nonZeroDivisor
    (I := N.etaDeterminantalIdeal f i) hf n hrightPrincipal

-- Proof sketch: use the principal-ideal hypothesis together with Lemma `15.97.5` to see that the
-- reduced maps attached to `M` and `N` are split injections of finite projective modules over
-- `A / fA`. Lemma `15.97.7` identifies the corresponding universal splitting loci, while the
-- derived equivalence transports the reduced `η_f` complexes and their degree-`i` maps. The
-- source-facing ideals with that universal property are therefore equal.
/-- If `M^\bullet` and `N^\bullet` represent the same derived object, then any degree-`i` ideals
of `A / fA` satisfying the universal property of `J_i(M^\bullet, f)` and `J_i(N^\bullet, f)`
agree; the derived comparison is expressed through `CategoryTheory.IsIsomorphic`, not through a
chosen `Iso`. -/
theorem etaReductionDecompositionIdeal_eq_of_same_derivedObject_of_property
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M N : CpxA)
    [∀ j : ℕ, Module.Free A (M.X j)] [∀ j : ℕ, Module.Finite A (M.X j)]
    [∀ j : ℕ, Module.Free A (N.X j)] [∀ j : ℕ, Module.Finite A (N.X j)]
    (hMbounded : M.IsBoundedAbove)
    (hNbounded : N.IsBoundedAbove)
    (hMN : IsIsomorphic ((Q).obj M) ((Q).obj N))
    (i : ℕ)
    {JM JN : Ideal (A ⧸ principalIdeal f)}
    (hJM : M.etaReductionDecompositionIdealProperty f i JM)
    (hJN : N.etaReductionDecompositionIdealProperty f i JN) :
    JM = JN := by
  -- TODO: follow the source-faithful stabilization route from Lemma `15.97.1`: after localizing
  -- away from each prime, replace the derived equivalence by a biproduct with elementary
  -- contractible two-term complexes, compute that `J` is additive under those biproducts, and use
  -- the trivial-disk computation `J(Q_j) = ⊥` to identify the two universal ideals.
  sorry

-- Proof sketch: apply the preceding witness-equality theorem to the canonical ideals
-- `J_i(M^\bullet, f)` and `J_i(N^\bullet, f)`, using their defining universal properties from the
-- existence-and-uniqueness construction above. The principality hypothesis needed to define the
-- `N`-side ideal is derived internally from Lemma `15.97.1` via the bridge theorem just above.
/-- Lemma 15.97.8: if `f` is a nonzerodivisor in `A` and `M^\bullet`, `N^\bullet` are bounded
complexes of finite free `A`-modules representing the same derived object, then the canonical
degree-`i` ideals `J_i(M^\bullet, f)` and `J_i(N^\bullet, f)` of `A / fA` are equal whenever the
degree-`i` determinantal ideal for `M^\bullet` is principal; the corresponding principality for
`N^\bullet` follows from Lemma `15.97.1`. -/
@[stacks 0GSW]
theorem etaReductionDecompositionIdeal_eq_of_same_derivedObject
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M N : CpxA)
    [∀ j : ℕ, Module.Free A (M.X j)] [∀ j : ℕ, Module.Finite A (M.X j)]
    [∀ j : ℕ, Module.Free A (N.X j)] [∀ j : ℕ, Module.Finite A (N.X j)]
    (hMbounded : M.IsBoundedAbove)
    (hNbounded : N.IsBoundedAbove)
    (hMN : IsIsomorphic ((Q).obj M) ((Q).obj N))
    (i : ℕ)
    (hIM : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    J[f]_(i)(M ; hf, hIM) =
      J[f]_(i)(N ; hf,
        etaDeterminantalIdeal_isPrincipal_of_same_derivedObject
          f hf M N hMbounded hNbounded hMN i hIM) := by
  -- Proof comment: once the `N`-side canonical ideal is defined via the principality bridge, the
  -- comparison theorem applies directly to the canonical witnesses on both sides.
  exact etaReductionDecompositionIdeal_eq_of_same_derivedObject_of_property
    f hf M N hMbounded hNbounded hMN i
    (NatModuleCochainComplex.etaReductionDecompositionIdeal_property
      M f i hf hIM)
    (NatModuleCochainComplex.etaReductionDecompositionIdeal_property
      N f i hf
      (etaDeterminantalIdeal_isPrincipal_of_same_derivedObject
        f hf M N hMbounded hNbounded hMN i hIM))

end
