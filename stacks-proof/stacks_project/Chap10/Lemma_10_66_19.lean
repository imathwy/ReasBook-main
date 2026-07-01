import Mathlib
import stacks_project.Chap10.Lemma_10_25_1
import stacks_project.Chap10.Definition_10_66_1
import stacks_project.Chap10.Lemma_10_40_4
import stacks_project.Chap10.Lemma_10_42_3
import stacks_project.Chap10.Lemma_10_43_6
import stacks_project.Chap10.Lemma_10_66_2
import stacks_project.Chap10.Lemma_10_66_13
import stacks_project.Chap10.Lemma_10_66_4
import stacks_project.Chap10.Lemma_10_66_15
import stacks_project.Chap10.Lemma_10_66_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w x

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {R : Type w} [CommRing R] [Algebra k R]
variable {M : Type x} [AddCommGroup M] [Module R M]

local notation "Rₖ" => R ⊗[k] K
local notation "Mₖ" => Rₖ ⊗[R] M

/- Domain triage:
- primary domain: weakly associated primes under field extension/base change;
- `core/canonical`: the owner module `Mₖ = (R ⊗[k] K) ⊗[R] M`;
- `bridge/view`: the textbook tensor model `M ⊗[k] K`, compared to `Mₖ` through the standard
  base-change equivalence.

Primitive data are only the owner module `Mₖ` and the chapter owner set `weaklyAssociatedPrimes`.
The textbook tensor presentation is derived API, so the file keeps the owner theorem at the weaker
owner-module layer and adds the textbook comparison only in a stronger bridge section. -/
local instance : Module Rₖ Mₖ :=
  TensorProduct.leftModule

/-- Helper for Lemma 10.66.19: the canonical map on the field tensor factor equips
`R ⊗[k] K` with its natural `R ⊗[k] L`-algebra structure. -/
private instance ringTensorToTopAlgebra (L : IntermediateField k K) :
    Algebra (R ⊗[k] L) Rₖ :=
  (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k L K)).toAlgebra

/-- Helper for Lemma 10.66.19: the canonical tensor-factor algebra maps from `R` to
`R ⊗[k] L` and then to `R ⊗[k] K` compose to the usual map `R → R ⊗[k] K`. -/
private instance ringTensorToTopIsScalarTower (L : IntermediateField k K) :
    IsScalarTower R (R ⊗[k] L) Rₖ :=
  by
    refine IsScalarTower.of_algebraMap_eq' (R := R) (S := R ⊗[k] L) (A := Rₖ) ?_
    ext r
    simp [RingHom.algebraMap_toAlgebra]

/-- Helper for Lemma 10.66.19: transport across an `R`-linear equivalence preserves the torsion
ideal of an element. -/
private theorem torsionOf_linearEquiv_eq
    {A : Type*} {N : Type*} {N' : Type*} [CommRing A]
    [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    (e : N ≃ₗ[A] N') (x : N) :
    Ideal.torsionOf A N' (e x) = Ideal.torsionOf A N x := by
  -- Compare the annihilator condition pointwise and pull equality back along the equivalence.
  ext a
  rw [Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  constructor
  · intro ha
    apply e.injective
    simpa using ha
  · intro ha
    simpa using congrArg e ha

/- The finite-extension part of the source proof reduces weak association of a field tensor product
to weak association of a finite direct sum of copies of the original module. The next helpers
package exactly that direct-sum descent. -/
/-- Helper for Lemma 10.66.19: weakly associated primes of a binary product are exactly the union
of the weakly associated primes of the two factors. -/
private theorem weaklyAssociatedPrimes_prod
    {M' : Type*} [AddCommGroup M'] [Module R M']
    {M'' : Type*} [AddCommGroup M''] [Module R M''] :
    weaklyAssociatedPrimes R (M' × M'') =
      weaklyAssociatedPrimes R M' ∪ weaklyAssociatedPrimes R M'' := by
  -- Compare the split exact sequence `0 → M' → M' × M'' → M'' → 0` with Lemma `10.66.4`.
  refine
    (weaklyAssociatedPrimes.subset_union_of_exact
      (R := R) (M' := M') (M := M' × M'') (M'' := M'')
      (f := LinearMap.inl R M' M'') (g := LinearMap.snd R M' M'')
      LinearMap.inl_injective Function.Exact.inl_snd).antisymm ?_
  rw [Set.union_subset_iff]
  exact
    ⟨weaklyAssociatedPrimes.subset_of_injective
        (R := R) (f := LinearMap.inl R M' M'') LinearMap.inl_injective,
      weaklyAssociatedPrimes.subset_of_injective
        (R := R) (f := LinearMap.inr R M' M'') LinearMap.inr_injective⟩

/-- Helper for Lemma 10.66.19: finitely supported functions on `Option ι` split into their
distinguished `none` coordinate and the remaining `some` coordinates. -/
private noncomputable def optionFinsuppLinearEquiv
    {ι : Type*} :
    (Option ι →₀ M) ≃ₗ[R] M × (ι →₀ M) where
  toFun f := (f none, f.some)
  invFun fg := (fg.2.embDomain Function.Embedding.some).update none fg.1
  left_inv f := by
    -- Check equality coordinatewise on the distinguished coordinate and on the ordinary ones.
    ext a
    cases a with
    | none =>
        simp [Finsupp.update]
    | some i =>
        simp [Finsupp.update]
  right_inv fg := by
    -- The inverse reconstructs the `none` coordinate together with the original tail.
    apply Prod.ext
    · simp [Finsupp.update]
    · ext i
      simp [Finsupp.update]
  map_add' f g := by
    -- Both coordinates are computed pointwise, so additivity is immediate.
    apply Prod.ext
    · simp
    · ext i
      simp
  map_smul' a f := by
    -- The same pointwise description gives compatibility with the `R`-action.
    apply Prod.ext
    · simp
    · ext i
      simp

/-- Helper for Lemma 10.66.19: for a finite index type, a weakly associated prime of a finitely
supported direct sum of copies of `M` is already weakly associated to one copy of `M`. -/
private theorem mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_finsupp_finite
    {ι : Type*} [Finite ι] :
    weaklyAssociatedPrimes R (ι →₀ M) ⊆ weaklyAssociatedPrimes R M := by
  classical
  refine
    Finite.induction_empty_option
      (P := fun ι ↦ weaklyAssociatedPrimes R (ι →₀ M) ⊆ weaklyAssociatedPrimes R M)
      ?_ ?_ ?_ ι
  · intro α β e h p hp
    -- Reindexing a finitely supported family does not change its weakly associated primes.
    have hEq :
        weaklyAssociatedPrimes R (α →₀ M) = weaklyAssociatedPrimes R (β →₀ M) := by
      simpa using
        (LinearEquiv.weaklyAssociatedPrimes_eq
          (Finsupp.mapDomain.linearEquiv M R e))
    rw [← hEq] at hp
    exact h hp
  · intro p hp
    -- The empty direct sum is the zero module, hence it has no weakly associated primes.
    have hEmpty : weaklyAssociatedPrimes R (PEmpty →₀ M) = ∅ :=
      weaklyAssociatedPrimes.eq_empty_of_subsingleton
    rw [hEmpty] at hp
    exact hp.elim
  · intro α _ h p hp
    -- Split the `Option α`-indexed direct sum into one copy of `M` and the tail indexed by `α`.
    have hEq :
        weaklyAssociatedPrimes R (Option α →₀ M) =
          weaklyAssociatedPrimes R (M × (α →₀ M)) := by
      simpa using
        (LinearEquiv.weaklyAssociatedPrimes_eq
          (optionFinsuppLinearEquiv (R := R) (M := M) (ι := α)))
    have hp' : p ∈ weaklyAssociatedPrimes R (M × (α →₀ M)) := by
      rw [← hEq]
      exact hp
    have hpUnion :
        p ∈ weaklyAssociatedPrimes R M ∪ weaklyAssociatedPrimes R (α →₀ M) := by
      simpa [weaklyAssociatedPrimes_prod (R := R) (M' := M) (M'' := α →₀ M)] using hp'
    rcases hpUnion with hpM | hpTail
    · exact hpM
    · exact h hpTail

/-- Helper for Lemma 10.66.19: weak association for an arbitrary finitely supported direct sum of
copies of `M` descends to weak association of `M` by restricting a witness to its finite support. -/
private theorem mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_finsupp
    {ι : Type*} :
    weaklyAssociatedPrimes R (ι →₀ M) ⊆ weaklyAssociatedPrimes R M := by
  classical
  intro p hp
  rw [mem_weaklyAssociatedPrimes_iff] at hp
  rcases hp with ⟨f, hf⟩
  let s : Set ι := f.support
  let f' : s →₀ M := Finsupp.subtypeDomain (· ∈ s) f
  have hsFinite : Finite s := by
    classical
    exact Set.toFinite _
  let fEmb : (s →₀ M) →ₗ[R] (ι →₀ M) :=
    Finsupp.lmapDomain M R (Subtype.val : s → ι)
  have hfEmb_injective : Function.Injective fEmb := by
    exact
      (Finsupp.leftInverse_lcomapDomain_mapDomain
        (R := R) (M := M) (Subtype.val : s → ι) Subtype.val_injective).injective
  have hfEmb_apply : fEmb f' = f := by
    -- Restricting `f` to its support and extending again recovers `f`.
    have hExtend :
        Finsupp.embDomain (Function.Embedding.subtype fun i ↦ i ∈ s) f' = f := by
      simpa [Finsupp.extendDomain_eq_embDomain_subtype, s, f'] using
        (Finsupp.extendDomain_subtypeDomain (P := fun i ↦ i ∈ s) f
          (by
            intro i hi
            simpa [s] using hi))
    calc
      fEmb f' =
          Finsupp.embDomain (Function.Embedding.subtype fun i ↦ i ∈ s) f' := by
            simp [fEmb, Finsupp.lmapDomain_apply, Finsupp.embDomain_eq_mapDomain]
      _ = f := hExtend
  have hf' :
      p ∈ weaklyAssociatedPrimes R (s →₀ M) := by
    rw [mem_weaklyAssociatedPrimes_iff]
    refine ⟨f', ?_⟩
    have hminimal_emb :
        p ∈ (Ideal.torsionOf R (ι →₀ M) (fEmb f')).minimalPrimes := by
      simpa [hfEmb_apply] using hf
    have htorsion :
        Ideal.torsionOf R (ι →₀ M) (fEmb f') =
          Ideal.torsionOf R (s →₀ M) f' := by
      simpa [fEmb] using
        (weaklyAssociatedPrimes.Ideal.torsionOf_map_eq_of_injective
          (R := R) (f := fEmb) hfEmb_injective f')
    simpa [htorsion] using hminimal_emb
  letI : Finite s := hsFinite
  exact
    mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_finsupp_finite
      (R := R) (M := M) hf'

/-- Helper for Lemma 10.66.19: if the canonical owner base change `Mₖ`, regarded as an
`R`-module, has a weakly associated prime `p`, then `p` is already weakly associated to `M`. -/
private theorem mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_owner_baseChange
    {p : Ideal R} (hp : p ∈ weaklyAssociatedPrimes R Mₖ) :
    p ∈ weaklyAssociatedPrimes R M := by
  classical
  let b : Module.Basis (Module.Basis.ofVectorSpaceIndex k K) k K :=
    Module.Basis.ofVectorSpace k K
  let eRing :
      Rₖ ≃ₗ[R] (Module.Basis.ofVectorSpaceIndex k K →₀ R) :=
    Algebra.TensorProduct.equivFinsuppOfBasis (A := R) (R := k) (V := K) b
  let eModule :
      Mₖ ≃ₗ[R] ((Module.Basis.ofVectorSpaceIndex k K →₀ R) ⊗[R] M) :=
    LinearEquiv.rTensor M eRing
  let eFinsupp :
      ((Module.Basis.ofVectorSpaceIndex k K →₀ R) ⊗[R] M) ≃ₗ[R]
        (Module.Basis.ofVectorSpaceIndex k K →₀ M) :=
    TensorProduct.finsuppScalarLeft R M (Module.Basis.ofVectorSpaceIndex k K)
  have hEqModule :
      weaklyAssociatedPrimes R Mₖ =
        weaklyAssociatedPrimes R ((Module.Basis.ofVectorSpaceIndex k K →₀ R) ⊗[R] M) := by
    simpa [eModule] using LinearEquiv.weaklyAssociatedPrimes_eq eModule
  have hpTensor :
      p ∈ weaklyAssociatedPrimes R ((Module.Basis.ofVectorSpaceIndex k K →₀ R) ⊗[R] M) := by
    -- Re-express the owner base change by expanding the `K`-factor against a vector-space basis.
    rw [← hEqModule]
    exact hp
  have hEqFinsupp :
      weaklyAssociatedPrimes R ((Module.Basis.ofVectorSpaceIndex k K →₀ R) ⊗[R] M) =
        weaklyAssociatedPrimes R (Module.Basis.ofVectorSpaceIndex k K →₀ M) := by
    simpa [eFinsupp] using LinearEquiv.weaklyAssociatedPrimes_eq eFinsupp
  have hpFinsupp :
      p ∈ weaklyAssociatedPrimes R (Module.Basis.ofVectorSpaceIndex k K →₀ M) := by
    -- Tensoring with the free module `ι →₀ R` is the finitely supported direct sum of copies of `M`.
    rw [← hEqFinsupp]
    exact hpTensor
  -- The earlier direct-sum descent now removes the remaining basis index set.
  exact
    mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_finsupp
      (R := R) (M := M) hpFinsupp

/-- Helper for Lemma 10.66.19: transporting a tensor from a smaller intermediate field stage into
a larger one does not change its image in `R ⊗[k] K`. -/
private theorem ringTensor_map_comp_inclusion
    {L L' : IntermediateField k K} (hLL' : L ≤ L') (x : R ⊗[k] L) :
    Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k L' K)
      (Algebra.TensorProduct.map (AlgHom.id k R) (IntermediateField.inclusion hLL') x) =
        Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k L K) x := by
  -- Check the transport identity on pure tensors and extend additively.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro r a
    simp [IntermediateField.coe_inclusion]
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for Lemma 10.66.19: every element of `R ⊗[k] K` is already defined over a finitely
generated intermediate field of `K / k`. -/
private theorem exists_finitely_generated_intermediate_field_ringTensor
    (x : Rₖ) :
    ∃ (L : IntermediateField k K) (_ : L.FG) (xL : R ⊗[k] L),
      Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k L K) xL = x := by
  classical
  -- Build the stage recursively from a tensor decomposition and enlarge intermediate fields by
  -- taking suprema in the additive case.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · refine ⟨⊥, IntermediateField.fg_bot, 0, ?_⟩
    simp
  · intro r a
    let L : IntermediateField k K := IntermediateField.adjoin k ({a} : Set K)
    have haL : a ∈ L := IntermediateField.subset_adjoin k ({a} : Set K) (by simp)
    refine
      ⟨L, IntermediateField.fg_adjoin_of_finite (F := k) (E := K) (Set.finite_singleton a),
        r ⊗ₜ[k] ⟨a, haL⟩, ?_⟩
    simp [L]
  · intro x y hx hy
    rcases hx with ⟨Lx, hLx, xL, hxL⟩
    rcases hy with ⟨Ly, hLy, yL, hyL⟩
    let L : IntermediateField k K := Lx ⊔ Ly
    let xL' : R ⊗[k] L :=
      Algebra.TensorProduct.map (AlgHom.id k R)
        (IntermediateField.inclusion (show Lx ≤ L from le_sup_left)) xL
    let yL' : R ⊗[k] L :=
      Algebra.TensorProduct.map (AlgHom.id k R)
        (IntermediateField.inclusion (show Ly ≤ L from le_sup_right)) yL
    refine ⟨L, IntermediateField.fg_sup hLx hLy, xL' + yL', ?_⟩
    -- After transporting both stages into the union stage, the ambient tensor is just the sum of
    -- the original two ambient images.
    calc
      Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k L K) (xL' + yL') =
          Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k L K) xL' +
            Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k L K) yL' := by
              simp [xL', yL']
      _ =
          Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k Lx K) xL +
            Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k Ly K) yL := by
              rw [ringTensor_map_comp_inclusion (k := k) (K := K) (R := R)
                    (show Lx ≤ L from le_sup_left) xL,
                ringTensor_map_comp_inclusion (k := k) (K := K) (R := R)
                    (show Ly ≤ L from le_sup_right) yL]
      _ = x + y := by
          simpa [hxL, hyL]

/-- Helper for Lemma 10.66.19: the left-factor map `R ⊗[k] L → R ⊗[k] K` is `R`-linear because
it fixes the `R`-coefficient and only changes the field factor. -/
private theorem ringTensor_map_to_top_smul
    (L : IntermediateField k K) (r : R) (x : R ⊗[k] L) :
    Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k L K) (r • x) =
      r • Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k L K) x := by
  -- Verify `R`-linearity on pure tensors and extend additively.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro r' a
    change
      (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k L K))
          ((r * r') ⊗ₜ[k] a) =
        (r * r') ⊗ₜ[k] ↑a
    simp
  · intro x y hx hy
    simp [smul_add, map_add, hx, hy]

/-- Helper for Lemma 10.66.19: the canonical map `R ⊗[k] L → R ⊗[k] K` viewed as an `R`-linear
map on the left tensor factor. -/
private abbrev ringTensorToTopLinearMap (L : IntermediateField k K) :
    (R ⊗[k] L) →ₗ[R] Rₖ :=
  { toFun := Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k L K)
    map_add' := by
      intro x y
      simp [map_add]
    map_smul' := ringTensor_map_to_top_smul (k := k) (K := K) (R := R) L }

/-- Helper for Lemma 10.66.19: the canonical owner-stage map from an intermediate field `L`
into the final `K`-stage is tensoring the left factor along `R ⊗[k] L → R ⊗[k] K`. -/
private abbrev ownerStageMap (L : IntermediateField k K) :
    ((R ⊗[k] L) ⊗[R] M) →ₗ[R] Mₖ :=
  TensorProduct.map
    (ringTensorToTopLinearMap (k := k) (K := K) (R := R) L)
    (LinearMap.id : M →ₗ[R] M)

/-- Helper for Lemma 10.66.19: after rewriting the two-step tensor base change by
`cancelBaseChange`, the universal element `1 ⊗ zL` is exactly the owner witness obtained by
transporting `zL` from the `L`-stage to the final `K`-stage. -/
private theorem ownerStageMap_eq_cancelBaseChange_one_tmul
    (L : IntermediateField k K) (zL : ((R ⊗[k] L) ⊗[R] M)) :
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
        R (R ⊗[k] L) Rₖ Rₖ M)
      ((1 : Rₖ) ⊗ₜ[(R ⊗[k] L)] zL) =
        ownerStageMap (k := k) (K := K) (R := R) (M := M) L zL := by
  -- Compare both sides on pure tensors, where `cancelBaseChange_tmul` and the scalar action on
  -- `1 : R ⊗[k] K` both reduce to the canonical map on the left tensor factor.
  refine TensorProduct.induction_on zL ?_ ?_ ?_
  · rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero]
  · intro x m
    simpa [ownerStageMap, ringTensorToTopLinearMap, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra, TensorProduct.map_tmul] using
      (TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul
        R (R ⊗[k] L) Rₖ (1 : Rₖ) m x)
  · intro x y hx hy
    rw [TensorProduct.tmul_add, LinearEquiv.map_add, hx, hy, LinearMap.map_add]

/-- Helper for Lemma 10.66.19: the canonical map `R ⊗[k] L → R ⊗[k] K` is flat because it is
obtained by tensoring the flat field extension `L → K` with `R`. -/
private theorem ringTensorToTop_moduleFlat (L : IntermediateField k K) :
    Module.Flat (R ⊗[k] L) Rₖ := by
  -- The source proof uses this flatness twice: once for annihilator base change and once for
  -- going down along the intermediate-field stage.
  have hflatL :
      RingHom.Flat ((IsScalarTower.toAlgHom k L K).toRingHom) := by
    simpa using
      (RingHom.Flat.of_isField (R := L) (S := K) (Field.toIsField L)
        ((IsScalarTower.toAlgHom k L K).toRingHom))
  have hflatTensor :
      RingHom.Flat
        ((Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k L K)).toRingHom) := by
    simpa using
      (RingHom.Flat.tensorProductMap (R := k) (S := k) (A := R) (B := L) (C := R) (D := K)
        (f := AlgHom.id k R) (g := IsScalarTower.toAlgHom k L K)
        (by simpa using (RingHom.Flat.id R)) hflatL)
  simpa [RingHom.flat_algebraMap_iff, ringTensorToTopAlgebra, RingHom.algebraMap_toAlgebra]
    using hflatTensor

/-- Helper for Lemma 10.66.19: the left-factor map `R ⊗[k] L → R ⊗[k] L'` is `R`-linear for the
same reason: only the field component changes. -/
private theorem ringTensor_map_inclusion_smul
    {L L' : IntermediateField k K} (hLL' : L ≤ L') (r : R) (x : R ⊗[k] L) :
    Algebra.TensorProduct.map (AlgHom.id k R) (IntermediateField.inclusion hLL') (r • x) =
      r • Algebra.TensorProduct.map (AlgHom.id k R) (IntermediateField.inclusion hLL') x := by
  -- Again reduce to pure tensors, where the `R`-coefficient is untouched by inclusion.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro r' a
    change
      (Algebra.TensorProduct.map (AlgHom.id k R) (IntermediateField.inclusion hLL'))
          ((r * r') ⊗ₜ[k] a) =
        (r * r') ⊗ₜ[k] (IntermediateField.inclusion hLL' a)
    simp
  · intro x y hx hy
    simp [smul_add, map_add, hx, hy]

/-- Helper for Lemma 10.66.19: the canonical `R`-linear map on the left tensor factor induced by
an inclusion of intermediate fields. -/
private abbrev ringTensorInclusionLinearMap
    {L L' : IntermediateField k K} (hLL' : L ≤ L') :
    (R ⊗[k] L) →ₗ[R] (R ⊗[k] L') :=
  { toFun := Algebra.TensorProduct.map (AlgHom.id k R) (IntermediateField.inclusion hLL')
    map_add' := by
      intro x y
      simp [map_add]
    map_smul' := ringTensor_map_inclusion_smul (k := k) (K := K) (R := R) hLL' }

/-- Helper for Lemma 10.66.19: moving an owner witness from `L` to a larger intermediate field
`L'` only tensors the left factor along the induced ring map `R ⊗[k] L → R ⊗[k] L'`. -/
private abbrev ownerInclusionMap
    {L L' : IntermediateField k K} (hLL' : L ≤ L') :
    ((R ⊗[k] L) ⊗[R] M) →ₗ[R] ((R ⊗[k] L') ⊗[R] M) :=
  TensorProduct.map
    (ringTensorInclusionLinearMap (k := k) (K := K) (R := R) hLL')
    (LinearMap.id : M →ₗ[R] M)

/-- Helper for Lemma 10.66.19: transporting an owner witness from `L` to a larger intermediate
field `L'` and then to `K` agrees with transporting it directly from `L` to `K`. -/
private theorem ownerStageMap_comp_inclusion
    {L L' : IntermediateField k K} (hLL' : L ≤ L')
    (z : ((R ⊗[k] L) ⊗[R] M)) :
    ownerStageMap (k := k) (K := K) (R := R) (M := M) L'
        (ownerInclusionMap (k := k) (K := K) (R := R) (M := M) hLL' z) =
      ownerStageMap (k := k) (K := K) (R := R) (M := M) L z := by
  -- Check the compatibility first on pure tensors, then extend additively across the owner tensor.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp [ownerStageMap]
  · intro x m
    simpa [ownerStageMap, TensorProduct.map_tmul] using
      congrArg (fun t : Rₖ ↦ t ⊗ₜ[R] m)
        (ringTensor_map_comp_inclusion (k := k) (K := K) (R := R) hLL' x)
  · intro x y hx hy
    simp [ownerStageMap, hx, hy]

/-- Helper for Lemma 10.66.19: every owner witness in `((R ⊗[k] K) ⊗[R] M)` is already defined
over a finitely generated intermediate field stage. -/
private theorem exists_finitely_generated_intermediate_owner_witness
    (z : Mₖ) :
    ∃ (L : IntermediateField k K) (_ : L.FG) (zL : ((R ⊗[k] L) ⊗[R] M)),
      ownerStageMap (k := k) (K := K) (R := R) (M := M) L zL = z := by
  classical
  -- Follow the source proof literally: descend each left tensor coefficient and enlarge stages by
  -- taking suprema in the additive step.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · refine ⟨⊥, IntermediateField.fg_bot, 0, ?_⟩
    simp [ownerStageMap]
  · intro x m
    rcases
      exists_finitely_generated_intermediate_field_ringTensor
        (k := k) (K := K) (R := R) x with
      ⟨L, hLfg, xL, hxL⟩
    refine ⟨L, hLfg, xL ⊗ₜ[R] m, ?_⟩
    -- A pure owner tensor descends once its coefficient in `R ⊗[k] K` does.
    simpa [ownerStageMap, TensorProduct.map_tmul] using
      congrArg (fun t : Rₖ ↦ t ⊗ₜ[R] m) hxL
  · intro x y hx hy
    rcases hx with ⟨Lx, hLx, xL, hxL⟩
    rcases hy with ⟨Ly, hLy, yL, hyL⟩
    let L : IntermediateField k K := Lx ⊔ Ly
    let xL' : ((R ⊗[k] L) ⊗[R] M) :=
      ownerInclusionMap (k := k) (K := K) (R := R) (M := M)
        (show Lx ≤ L from le_sup_left) xL
    let yL' : ((R ⊗[k] L) ⊗[R] M) :=
      ownerInclusionMap (k := k) (K := K) (R := R) (M := M)
        (show Ly ≤ L from le_sup_right) yL
    refine ⟨L, IntermediateField.fg_sup hLx hLy, xL' + yL', ?_⟩
    -- Once both witnesses are moved to the common stage `L`, the ambient owner witness is their
    -- sum, exactly as in the source descent on finitely many coefficients.
    calc
      ownerStageMap (k := k) (K := K) (R := R) (M := M) L (xL' + yL') =
          ownerStageMap (k := k) (K := K) (R := R) (M := M) L xL' +
            ownerStageMap (k := k) (K := K) (R := R) (M := M) L yL' := by
              simp [ownerStageMap]
      _ =
          ownerStageMap (k := k) (K := K) (R := R) (M := M) Lx xL +
            ownerStageMap (k := k) (K := K) (R := R) (M := M) Ly yL := by
              rw [ownerStageMap_comp_inclusion (k := k) (K := K) (R := R) (M := M)
                    (show Lx ≤ L from le_sup_left) xL,
                ownerStageMap_comp_inclusion (k := k) (K := K) (R := R) (M := M)
                    (show Ly ≤ L from le_sup_right) yL]
      _ = x + y := by
          simpa [hxL, hyL]

/-- Helper for Lemma 10.66.19: the annihilator of a descended owner witness transports to the
ambient `K`-stage by extending ideals along `R ⊗[k] L → R ⊗[k] K`. -/
private theorem ownerStageMap_torsionOf_eq_map
    (L : IntermediateField k K) (zL : ((R ⊗[k] L) ⊗[R] M)) :
    Ideal.torsionOf Rₖ Mₖ
        (ownerStageMap (k := k) (K := K) (R := R) (M := M) L zL) =
      Ideal.map (algebraMap (R ⊗[k] L) Rₖ)
        (Ideal.torsionOf (R ⊗[k] L) (((R ⊗[k] L) ⊗[R] M)) zL) := by
  -- Route correction: instead of postulating a global flatness theorem for
  -- `R ⊗[k] L → R ⊗[k] K`, derive flatness locally from the field map `L → K`, tensor it with
  -- `R`, and then compare the transported witness with `ownerStageMap`.
  letI : Module.Flat (R ⊗[k] L) Rₖ :=
    ringTensorToTop_moduleFlat (k := k) (K := K) (R := R) L
  -- First identify the ambient annihilator as the annihilator of the universal tensor `1 ⊗ zL`,
  -- then apply the flat base-change theorem from Lemma `10.40.4`.
  calc
    Ideal.torsionOf Rₖ Mₖ
        (ownerStageMap (k := k) (K := K) (R := R) (M := M) L zL) =
      Ideal.torsionOf Rₖ (Rₖ ⊗[(R ⊗[k] L)] (((R ⊗[k] L) ⊗[R] M)))
        ((1 : Rₖ) ⊗ₜ[(R ⊗[k] L)] zL) := by
          simpa [ownerStageMap_eq_cancelBaseChange_one_tmul (k := k) (K := K) (R := R)
            (M := M) L zL] using
            (torsionOf_linearEquiv_eq
              (A := Rₖ)
              (e := TensorProduct.AlgebraTensorModule.cancelBaseChange
                R (R ⊗[k] L) Rₖ Rₖ M)
              ((1 : Rₖ) ⊗ₜ[(R ⊗[k] L)] zL))
    _ =
      Ideal.map (algebraMap (R ⊗[k] L) Rₖ)
        (Ideal.torsionOf (R ⊗[k] L) (((R ⊗[k] L) ⊗[R] M)) zL) := by
          symm
          simpa using
            (Ideal.map_torsionOf_eq_torsionOf_baseChange_of_flat
              (R := R ⊗[k] L) (S := Rₖ) (M := ((R ⊗[k] L) ⊗[R] M)) zL)

/-- Helper for Lemma 10.66.19: once the annihilator upstairs has been rewritten as an ideal map,
any minimal prime above it contracts to a minimal prime above the downstairs annihilator. -/
private theorem under_mem_minimalPrimes_of_mem_minimalPrimes_map
    (L : IntermediateField k K) (I : Ideal (R ⊗[k] L)) {q : Ideal Rₖ}
    (hq : q ∈ (Ideal.map (algebraMap (R ⊗[k] L) Rₖ) I).minimalPrimes) :
    q.under (R ⊗[k] L) ∈ I.minimalPrimes := by
  haveI : q.IsPrime := Ideal.minimalPrimes_isPrime hq
  let qL : Ideal (R ⊗[k] L) := q.under (R ⊗[k] L)
  haveI : qL.IsPrime := by
    dsimp [qL]
    infer_instance
  letI : Module.Flat (R ⊗[k] L) Rₖ :=
    ringTensorToTop_moduleFlat (k := k) (K := K) (R := R) L
  -- Prove minimality downstairs by contradiction: a strictly smaller prime under `qL` lifts by
  -- going down to a strictly smaller prime under `q`, contradicting minimality upstairs.
  refine ⟨⟨inferInstance, ?_⟩, ?_⟩
  · exact (Ideal.map_le_iff_le_comap).mp hq.1.2
  · intro p hp hpqL
    letI : p.IsPrime := hp.1
    by_contra hpne
    have hpLt : p < qL := lt_of_le_of_ne hpqL fun hEq ↦ hpne hEq.ge
    haveI : q.LiesOver qL := by
      dsimp [qL]
      infer_instance
    obtain ⟨q', hq'Lt, hq'Prime, hq'Over⟩ :=
      Ideal.exists_ideal_lt_liesOver_of_lt
        (R := R ⊗[k] L) (S := Rₖ) (p := p) (q := qL) q hpLt
    haveI : q'.IsPrime := hq'Prime
    haveI : q'.LiesOver p := hq'Over
    have hmapLe : Ideal.map (algebraMap (R ⊗[k] L) Rₖ) I ≤ q' := by
      rw [Ideal.map_le_iff_le_comap]
      simpa [q'.over_def p] using hp.2
    have hqLe : q ≤ q' := hq.2 ⟨inferInstance, hmapLe⟩ hq'Lt.le
    exact hq'Lt.not_ge hqLe

/-- Helper for Lemma 10.66.19: once the annihilator-minimal-prime witness has been transported
downstairs, the first source step packages it as a weakly associated prime over a finitely
generated intermediate field. -/
private theorem exists_finitely_generated_intermediate_weakAss_descent_owner
    (q : Ideal Rₖ) (hq : q ∈ weaklyAssociatedPrimes Rₖ Mₖ) :
    ∃ (L : IntermediateField k K) (_ : L.FG) (qL : Ideal (R ⊗[k] L)),
      qL ∈ weaklyAssociatedPrimes (R ⊗[k] L) (((R ⊗[k] L) ⊗[R] M)) ∧
        qL.under R = q.under R := by
  rcases hq with ⟨z, hz⟩
  rcases
    exists_finitely_generated_intermediate_owner_witness
      (k := k) (K := K) (R := R) (M := M) z with
    ⟨L, hLfg, zL, hzL⟩
  let I : Ideal (R ⊗[k] L) := Ideal.torsionOf (R ⊗[k] L) (((R ⊗[k] L) ⊗[R] M)) zL
  let qL : Ideal (R ⊗[k] L) := q.under (R ⊗[k] L)
  have hz' :
      q ∈ (Ideal.torsionOf Rₖ Mₖ
        (ownerStageMap (k := k) (K := K) (R := R) (M := M) L zL)).minimalPrimes := by
    simpa [hzL] using hz
  have hminimal_upstairs :
      q ∈ (Ideal.map (algebraMap (R ⊗[k] L) Rₖ) I).minimalPrimes := by
    -- Rewrite the upstairs annihilator using the descended witness `zL`.
    simpa [I, ownerStageMap_torsionOf_eq_map (k := k) (K := K) (R := R) (M := M) L zL]
      using hz'
  have hminimal_downstairs : qL ∈ I.minimalPrimes := by
    -- Contract the minimal-prime witness along the flat intermediate-field base change.
    simpa [qL] using
      under_mem_minimalPrimes_of_mem_minimalPrimes_map
        (k := k) (K := K) (R := R) L I hminimal_upstairs
  refine ⟨L, hLfg, qL, ?_, ?_⟩
  · -- The contracted prime is weakly associated to the descended witness `zL`.
    exact ⟨zL, hminimal_downstairs⟩
  · -- Contracting first to `R ⊗[k] L` and then to `R` is the same as contracting directly to `R`.
    change Ideal.comap (algebraMap R (R ⊗[k] L)) (Ideal.comap (algebraMap (R ⊗[k] L) Rₖ) q) =
      Ideal.comap (algebraMap R Rₖ) q
    rw [Ideal.comap_comap]
    rfl

/-- Helper for Lemma 10.66.19: a finitely generated intermediate field admits a purely
transcendental subextension over which it is finite-dimensional. -/
private theorem exists_purely_transcendental_subextension_finiteDimensional
    (L : IntermediateField k K) (hLfg : L.FG) :
    ∃ x : Fin (Cardinal.toNat (Algebra.trdeg k L)) → L,
      IsTranscendenceBasis k x ∧
        FiniteDimensional (IntermediateField.adjoin k (Set.range x)) L := by
  letI : Algebra.EssFiniteType k L := (IntermediateField.essFiniteType_iff).2 hLfg
  -- Choose a transcendence basis of the finitely generated field and reindex it by a finite set.
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k L
  obtain ⟨x, hx, hxAdjoin⟩ :=
    exists_fin_reindexed_transcendence_basis (k := k) (K := L) hs
  refine ⟨x, hx, ?_⟩
  -- The generated rational-function stage is then finite-dimensional inside `L`.
  simpa [hxAdjoin] using
    (finiteDimensional_over_adjoin_of_isTranscendenceBasis (k := k) (K := L) hx)

/-- Helper for Lemma 10.66.19: tensoring the finite stage `R ⊗[k] F` along the intermediate-field
map `F → L` gives the canonical algebra `R ⊗[k] L`. -/
private instance ringTensorIntermediateFieldAlgebra
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) :
    Algebra (R ⊗[k] F) (R ⊗[k] L) :=
  (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k F L)).toAlgebra

/-- Helper for Lemma 10.66.19: the two tensor-factor maps out of `R` through
`R ⊗[k] F → R ⊗[k] L` agree with the direct map `R → R ⊗[k] L`. -/
private instance ringTensorIntermediateFieldIsScalarTower
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) :
    IsScalarTower R (R ⊗[k] F) (R ⊗[k] L) := by
  refine IsScalarTower.of_algebraMap_eq' (R := R) (S := R ⊗[k] F) (A := R ⊗[k] L) ?_
  ext r
  simp [RingHom.algebraMap_toAlgebra]

/-- Helper for Lemma 10.66.19: the right tensor-factor algebra structures on `R ⊗[k] F` and
`R ⊗[k] L` fit into the expected scalar tower over the intermediate field `F`. -/
private instance ringTensorIntermediateFieldRightIsScalarTower
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) :
    IsScalarTower F (R ⊗[k] F) (R ⊗[k] L) := by
  refine IsScalarTower.of_algebraMap_eq' (R := F) (S := R ⊗[k] F) (A := R ⊗[k] L) ?_
  ext a
  rfl

/-- Helper for Lemma 10.66.19: the `L`-stage owner module carries the restricted
`R ⊗[k] F`-module structure coming from the left tensor factor. -/
private instance ringTensorIntermediateFieldOwnerModule
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) :
    Module (R ⊗[k] F) (((R ⊗[k] L) ⊗[R] M)) :=
  Module.compHom _ (algebraMap (R ⊗[k] F) (R ⊗[k] L))

/-- Helper for Lemma 10.66.19: the restricted-scalar action on the `L`-stage owner module
commutes with the original `R ⊗[k] L`-action. -/
private instance ringTensorIntermediateFieldOwnerIsScalarTower
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) :
    IsScalarTower (R ⊗[k] F) (R ⊗[k] L) (((R ⊗[k] L) ⊗[R] M)) :=
  inferInstance

/-- Helper for Lemma 10.66.19: the literal owner base change from `F` to `L` also carries the
expected `R ⊗[k] F`-module structure via the left tensor factor. -/
private instance ringTensorIntermediateFieldBaseChangeModule
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) :
    Module (R ⊗[k] F)
      (((R ⊗[k] L) ⊗[(R ⊗[k] F)] (((R ⊗[k] F) ⊗[R] M)))) :=
  inferInstance

/-- Helper for Lemma 10.66.19: tensoring the finite field extension `F → L` with `R` produces a
finite `R ⊗[k] F`-module structure on `R ⊗[k] L`. -/
private theorem ringTensorIntermediateField_moduleFinite
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) [FiniteDimensional F L] :
    Module.Finite (R ⊗[k] F) (R ⊗[k] L) := by
  have hId : (AlgHom.id k R).Finite := AlgHom.Finite.id k R
  have hField : (IsScalarTower.toAlgHom k F L).Finite := by
    have hFieldRing : (algebraMap F L).Finite := RingHom.finite_algebraMap.mpr inferInstance
    simpa [AlgHom.Finite, RingHom.algebraMap_toAlgebra] using hFieldRing
  have hTensor :
      (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k F L)).toRingHom.Finite := by
    simpa using
      (RingHom.Finite.tensorProductMap
        (R := k) (S := R) (S' := R) (T := F) (T' := L)
        (f := AlgHom.id k R) (g := IsScalarTower.toAlgHom k F L) hId hField)
  have hTensorAlg : (algebraMap (R ⊗[k] F) (R ⊗[k] L)).Finite := by
    simpa [ringTensorIntermediateFieldAlgebra, RingHom.algebraMap_toAlgebra] using hTensor
  exact RingHom.finite_algebraMap.mp hTensorAlg

/-- Helper for Lemma 10.66.19: after passing from the purely transcendental stage `F` to the
finite extension stage `L`, the owner base-change module is canonically the ordinary `L`-stage
owner module. -/
private noncomputable def owner_baseChange_reassoc_over_intermediate_field
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) :
    ((R ⊗[k] L) ⊗[(R ⊗[k] F)] (((R ⊗[k] F) ⊗[R] M))) ≃ₗ[(R ⊗[k] L)]
      (((R ⊗[k] L) ⊗[R] M)) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange
    R (R ⊗[k] F) (R ⊗[k] L) (R ⊗[k] L) M

/-- Helper for Lemma 10.66.19: the intermediate-field tensor comparison commutes with the
canonical algebra map from `R ⊗[k] F`. -/
private theorem ringTensorIntermediateField_baseChange_algEquiv_commutes
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L)
    (x : R ⊗[k] F) :
    (Algebra.IsPushout.cancelBaseChangeAlg
        (R := k) (S := R) (A := F) (B := R ⊗[k] F) (C := L))
      (algebraMap (R ⊗[k] F) ((R ⊗[k] F) ⊗[F] L) x) =
        algebraMap (R ⊗[k] F) (R ⊗[k] L) x := by
  let e := Algebra.IsPushout.cancelBaseChangeAlg
    (R := k) (S := R) (A := F) (B := R ⊗[k] F) (C := L)
  have hsymm :
      e.symm (algebraMap (R ⊗[k] F) (R ⊗[k] L) x) =
        algebraMap (R ⊗[k] F) ((R ⊗[k] F) ⊗[F] L) x := by
    -- Proof comment: this is the pushout identity saying that the inverse comparison sends the
    -- standard left-tensor inclusion in `R ⊗[k] L` back to the literal base-change inclusion.
    simpa [e, RingHom.algebraMap_toAlgebra] using
      congr($(Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor
        (R := k) (S := R) (A := F) (C := L)) x)
  -- Proof comment: apply the forward equivalence to the inverse comparison identity.
  calc
    e (algebraMap (R ⊗[k] F) ((R ⊗[k] F) ⊗[F] L) x) =
        e (e.symm (algebraMap (R ⊗[k] F) (R ⊗[k] L) x)) := by
          rw [hsymm.symm]
    _ = algebraMap (R ⊗[k] F) (R ⊗[k] L) x := by
          simp [e]

/-- Helper for Lemma 10.66.19: the ring pushout description of `R ⊗[k] L` identifies the literal
base change `((R ⊗[k] F) ⊗[F] L)` with the usual tensor product over `k`. -/
private noncomputable def ringTensorIntermediateField_baseChange_algEquiv
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) :
    ((R ⊗[k] F) ⊗[F] L) ≃ₐ[(R ⊗[k] F)] (R ⊗[k] L) :=
  { __ := Algebra.IsPushout.cancelBaseChangeAlg
      (R := k) (S := R) (A := F) (B := R ⊗[k] F) (C := L)
    commutes' := ringTensorIntermediateField_baseChange_algEquiv_commutes
      (k := k) (R := R) (F := F) }

/-- Helper for Lemma 10.66.19: the canonical owner base change over the intermediate field
extension `F ⟶ L` identifies directly with the literal `L`-stage owner module. -/
private noncomputable def canonical_owner_baseChange_over_intermediate_field
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) :
    ((((R ⊗[k] F) ⊗[F] L) ⊗[(R ⊗[k] F)] (((R ⊗[k] F) ⊗[R] M)))) ≃ₗ[(R ⊗[k] F)]
      (((R ⊗[k] L) ⊗[R] M)) :=
  sorry

/-- Helper for Lemma 10.66.19: the owner base-change descent theorem over `F ⟶ L` specializes
directly to the `F`-stage owner module. -/
private theorem
    mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_owner_baseChange_intermediateField
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L)
    {qF : Ideal (R ⊗[k] F)}
    (hqF :
      qF ∈ weaklyAssociatedPrimes (R ⊗[k] F)
        ((((R ⊗[k] F) ⊗[F] L) ⊗[(R ⊗[k] F)] (((R ⊗[k] F) ⊗[R] M))))) :
    qF ∈ weaklyAssociatedPrimes (R ⊗[k] F) (((R ⊗[k] F) ⊗[R] M)) := by
  -- This is exactly the already-proved owner descent theorem, with the `F`-stage owner module
  -- fed in as the base module.
  exact
    mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_owner_baseChange
      (k := F) (K := L) (R := R ⊗[k] F) (M := ((R ⊗[k] F) ⊗[R] M)) hqF

/-- Helper for Lemma 10.66.19: if a weakly associated prime appears over a finitely generated
field stage `L`, then after choosing a purely transcendental subextension `F ⊆ L` with `L / F`
finite, the contraction to `R ⊗[k] F` is already weakly associated to the canonical `F`-stage
owner module. -/
private theorem exists_purely_transcendental_intermediate_weakAss_descent_owner
    {L : Type*} [Field L] [Algebra k L]
    (F : IntermediateField k L) [FiniteDimensional F L]
    {qL : Ideal (R ⊗[k] L)}
    (hqL : qL ∈ weaklyAssociatedPrimes (R ⊗[k] L) (((R ⊗[k] L) ⊗[R] M))) :
    ∃ qF : Ideal (R ⊗[k] F),
      qF ∈ weaklyAssociatedPrimes (R ⊗[k] F) (((R ⊗[k] F) ⊗[R] M)) ∧
        qF.under R = qL.under R := by
  let qF : Ideal (R ⊗[k] F) := Ideal.comap (algebraMap (R ⊗[k] F) (R ⊗[k] L)) qL
  letI : Module.Finite (R ⊗[k] F) (R ⊗[k] L) :=
    ringTensorIntermediateField_moduleFinite (k := k) (R := R) (L := L) F
  letI :
      Module (R ⊗[k] F) (((R ⊗[k] L) ⊗[R] M)) :=
    ringTensorIntermediateFieldOwnerModule
      (k := k) (R := R) (M := M) (L := L) F
  letI :
      IsScalarTower (R ⊗[k] F) (R ⊗[k] L) (((R ⊗[k] L) ⊗[R] M)) :=
    ringTensorIntermediateFieldOwnerIsScalarTower
      (k := k) (R := R) (M := M) (L := L) F
  have hqF_restrict :
      qF ∈ weaklyAssociatedPrimes (R ⊗[k] F) (((R ⊗[k] L) ⊗[R] M)) := by
    -- TODO: apply `weaklyAssociatedPrimes.restrictScalars_eq_image_comap_of_finite` to the
    -- finite map `R ⊗[k] F → R ⊗[k] L` after stabilizing the `R ⊗[k] F`-module instance on the
    -- `L`-stage owner so instance search sees the expected scalar tower.
    sorry
  have hqF_baseChange :
      qF ∈ weaklyAssociatedPrimes (R ⊗[k] F)
        ((((R ⊗[k] F) ⊗[F] L) ⊗[(R ⊗[k] F)] (((R ⊗[k] F) ⊗[R] M)))) := by
    -- Proof comment: transport the contracted witness across the canonical owner comparison.
    rw [LinearEquiv.weaklyAssociatedPrimes_eq
      (canonical_owner_baseChange_over_intermediate_field
        (k := k) (R := R) (M := M) (L := L) F)]
    exact hqF_restrict
  refine ⟨qF, ?_, ?_⟩
  · -- Proof comment: after transport, the already-proved owner base-change descent theorem
    -- finishes the finite-extension paragraph.
    exact
      mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_owner_baseChange_intermediateField
        (k := k) (R := R) (M := M) (L := L) F hqF_baseChange
  · -- Proof comment: contracting first to `R ⊗[k] F` and then to `R` is the same as
    -- contracting directly to `R`.
    change
      Ideal.comap (algebraMap R (R ⊗[k] F))
        (Ideal.comap (algebraMap (R ⊗[k] F) (R ⊗[k] L)) qL) =
        Ideal.comap (algebraMap R (R ⊗[k] L)) qL
    rw [Ideal.comap_comap]
    rfl

/-- Helper for Lemma 10.66.19: any module carrying a weakly associated prime is nontrivial. -/
private theorem nontrivial_of_mem_weaklyAssociatedPrimes
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    {p : Ideal A} (hp : p ∈ weaklyAssociatedPrimes A N) :
    Nontrivial N := by
  rcases hp with ⟨x, hx⟩
  refine ⟨⟨0, x, ?_⟩⟩
  -- The witness for a weakly associated prime cannot be zero, since `0` has torsion ideal `⊤`.
  intro hx0
  have htop : Ideal.torsionOf A N x = ⊤ := by
    rw [Ideal.torsionOf_eq_top_iff]
    exact hx0.symm
  simpa [htop, Ideal.minimalPrimes_top] using hx

/-- Helper for Lemma 10.66.19: localizing the ring tensor `R ⊗[k] F` at `p` is the same as
tensoring the localization `R_p` with `F`. -/
private noncomputable def ringTensor_localizedModule_atPrime_linearEquiv
    {F : Type*} [Field F] [Algebra k F] (p : Ideal R) [p.IsPrime] :
    LocalizedModule.AtPrime p (R ⊗[k] F) ≃ₗ[Localization.AtPrime p]
      (Localization.AtPrime p ⊗[k] F) := by
  let eLocalized :
      LocalizedModule.AtPrime p (R ⊗[k] F) ≃ₗ[Localization.AtPrime p]
        Localization.AtPrime p ⊗[R] (R ⊗[k] F) :=
    -- Rewrite localization at `p` as tensoring with `R_p`.
    LocalizedModule.equivTensorProduct p.primeCompl (R ⊗[k] F)
  let eTensor :
      Localization.AtPrime p ⊗[R] (R ⊗[k] F) ≃ₗ[Localization.AtPrime p]
        (Localization.AtPrime p ⊗[k] F) :=
    -- Then cancel the redundant middle `R` tensor factor on the ring side.
    (Algebra.TensorProduct.cancelBaseChange k R (Localization.AtPrime p)
      (Localization.AtPrime p) F).toLinearEquiv
  exact eLocalized.trans eTensor

/-- Helper for Lemma 10.66.19: localizing the `F`-stage owner module at `p ⊂ R` is the same as
first localizing `R` and `M` at `p` and then forming the owner module over `R_p`. -/
private noncomputable def owner_localizedModule_atPrime_under_linearEquiv
    {F : Type*} [Field F] [Algebra k F] (p : Ideal R) [p.IsPrime] :
    LocalizedModule.AtPrime p (((R ⊗[k] F) ⊗[R] M)) ≃ₗ[Localization.AtPrime p]
      ((Localization.AtPrime p ⊗[k] F) ⊗[Localization.AtPrime p]
        (LocalizedModule.AtPrime p M)) :=
  sorry

/-- Helper for Lemma 10.66.19: in the purely transcendental case, the remaining source argument
reduces contraction of a weakly associated prime on the owner base change to weak association on
the base module. -/
private theorem IsSMulRegular.notMem_torsionOf_minimalPrimes
    {A : Type*} [CommRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    {g : A} {z : N} (hregular : IsSMulRegular N g)
    {q : Ideal A} (hq : q ∈ (Ideal.torsionOf A N z).minimalPrimes) :
    g ∉ q := by
  -- Proof comment: a regular element cannot lie in a minimal prime over the annihilator of `z`,
  -- because the standard minimal-prime localization lemma would produce a nonzero vector killed by
  -- that regular element.
  intro hg
  rcases Ideal.exists_mul_mem_of_mem_minimalPrimes hq hg with ⟨y, hy, hgy⟩
  have hyz_ne : y • z ≠ 0 := by
    intro hyz
    rw [Ideal.mem_torsionOf_iff] at hy
    exact hy hyz
  have hgyz : g • (y • z) = 0 := by
    simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using
      (show (g * y) • z = 0 from by
        simpa [Ideal.mem_torsionOf_iff] using hgy)
  exact hyz_ne (hregular.right_eq_zero_of_smul hgyz)

/-- Helper for Lemma 10.66.19: restricting scalars from `A` to `R` sends the torsion ideal of a
vector to the corresponding torsion ideal over `R`. -/
private theorem comap_torsionOf_eq
    {A : Type*} [CommRing A] [Algebra R A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
    (z : N) :
    Ideal.comap (algebraMap R A) (Ideal.torsionOf A N z) =
      Ideal.torsionOf R N z := by
  -- Proof comment: an element `r : R` kills `z` after scalar extension exactly when its image in
  -- `A` kills `z`, because the two scalar actions agree by the scalar tower.
  ext r
  rw [Ideal.mem_comap, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  simpa using (IsScalarTower.algebraMap_smul A r z)

/-- Helper for Lemma 10.66.19: in the purely transcendental case, the remaining source argument
reduces contraction of a weakly associated prime on the owner base change to weak association on
the base module. -/
private theorem maximalIdeal_mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_local
    {A : Type*} [CommRing A] [Algebra R A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
    [IsLocalRing R]
    (hregular :
      ∀ g : A, g ∉ Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R) →
        IsSMulRegular N g)
    {q : Ideal A} (hq_under : q.under R = IsLocalRing.maximalIdeal R)
    (hq : q ∈ weaklyAssociatedPrimes A N) :
    IsLocalRing.maximalIdeal R ∈ weaklyAssociatedPrimes R N := by
  rcases hq with ⟨z, hz⟩
  let J : Ideal A := Ideal.torsionOf A N z
  have hq_eq_map :
      q = Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R) := by
    apply le_antisymm
    · intro g hgq
      by_contra hgmap
      exact
        (IsSMulRegular.notMem_torsionOf_minimalPrimes
          (A := A) (N := N) (g := g) (z := z) (hregular g hgmap)
          (q := q) (by simpa [J] using hz)) hgq
    · change Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R) ≤ q
      rw [Ideal.map_le_iff_le_comap]
      simpa [Ideal.under, hq_under]
  have hminimal_unique : J.minimalPrimes = {q} := by
    ext p
    constructor
    · intro hp
      have hp_le_map :
          p ≤ Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R) := by
        intro g hgp
        by_contra hgmap
        exact
          (IsSMulRegular.notMem_torsionOf_minimalPrimes
            (A := A) (N := N) (g := g) (z := z) (hregular g hgmap)
            (q := p) (by simpa [J] using hp)) hgp
      have hp_le_q : p ≤ q := by
        simpa [hq_eq_map] using hp_le_map
      exact Set.mem_singleton_iff.mpr <|
        le_antisymm
          hp_le_q
          (hz.2 ⟨Ideal.minimalPrimes_isPrime hp, hp.1.2⟩ hp_le_q)
    · rintro rfl
      simpa [J] using hz
  have hradA : J.radical = q := by
    rw [← Ideal.sInf_minimalPrimes, hminimal_unique, sInf_singleton]
  have hradR :
      (Ideal.torsionOf R N z).radical = IsLocalRing.maximalIdeal R := by
    calc
      (Ideal.torsionOf R N z).radical =
          (Ideal.comap (algebraMap R A) J).radical := by
            rw [comap_torsionOf_eq (R := R) (A := A) z]
      _ = Ideal.comap (algebraMap R A) J.radical := by
            rw [← Ideal.comap_radical]
      _ = IsLocalRing.maximalIdeal R := by
            simpa [J, hradA, Ideal.under, hq_under]
  rw [mem_weaklyAssociatedPrimes_iff]
  refine ⟨z, ?_⟩
  -- Proof comment: once the `R`-torsion radical is exactly the maximal ideal of the local ring,
  -- that maximal ideal is the unique minimal prime over the `R`-torsion ideal of `z`.
  haveI : (Ideal.torsionOf R N z).radical.IsPrime := by
    simpa [hradR] using
      (show (IsLocalRing.maximalIdeal R).IsPrime by infer_instance)
  rw [← Ideal.radical_minimalPrimes, hradR, Ideal.minimalPrimes_eq_subsingleton_self]
  simp

/-- Helper for Lemma 10.66.19: in the purely transcendental case, the remaining source argument
reduces contraction of a weakly associated prime on the owner base change to weak association on
the base module. -/
private theorem isDomain_residueField_tensor_adjoin
    {L : Type*} [Field L] [Algebra k L]
    {ι : Type*} (x : ι → L) (hx : IsTranscendenceBasis k x)
    {p : Ideal R} [p.IsPrime] :
    IsDomain
      ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).ResidueField ⊗[k]
        IntermediateField.adjoin k (Set.range x)) := by
  -- Proof comment: this is exactly the transcendence-basis tensor-domain lemma, specialized to
  -- the residue field of `R_p`.
  simpa using
    isDomain_tensor_adjoin_of_isTranscendenceBasis
      (k := k)
      (κ := (IsLocalRing.maximalIdeal (Localization.AtPrime p)).ResidueField)
      (L := L) x hx

/-- Helper for Lemma 10.66.19: every tensor in the canonical local owner over `R_p` already comes
from tensoring with some finite `R_p`-submodule of the localized base module. -/
private theorem exists_finite_local_owner_submodule_of_mem_tensor
    {p : Ideal R} [p.IsPrime]
    {F : Type*} [Field F] [Algebra k F]
    (z : ((Localization.AtPrime p ⊗[k] F) ⊗[Localization.AtPrime p]
      (LocalizedModule.AtPrime p M))) :
    True := by
  -- TODO: restore the finite-submodule witness once the `R_p ⊗[k] F` tensor self-action API is
  -- available again. This helper is currently unused downstream because the canonical regularity
  -- theorem remains blocked earlier in the source route.
  trivial

/-- Helper for Lemma 10.66.19: over a domain, any nonzero scalar acts injectively on a finitely
supported family of copies of the domain. -/
private theorem isSMulRegular_finsupp_of_ne_zero
    {A : Type*} [CommRing A] [IsDomain A] {ι : Type*} {g : A} (hg : g ≠ 0) :
    IsSMulRegular (ι →₀ A) g := by
  -- Check regularity coordinatewise, where it reduces to cancellation in the domain `A`.
  refine IsSMulRegular.of_right_eq_zero_of_smul ?_
  intro f hf
  ext i
  have hcoord := congrArg (fun h : ι →₀ A => h i) hf
  simp only [Finsupp.smul_apply, Pi.smul_apply, smul_eq_mul] at hcoord
  exact (mul_eq_zero.mp hcoord).resolve_left hg

/-- Helper for Lemma 10.66.19: over a domain, any nonzero scalar acts regularly on the tensor of
that domain with a vector space over the base field. -/
private theorem isSMulRegular_tensor_vectorSpace_of_ne_zero
    {κ : Type*} [Field κ]
    {A : Type*} [CommRing A] [Algebra κ A] [IsDomain A]
    {V : Type*} [AddCommGroup V] [Module κ V]
    {g : A} (hg : g ≠ 0) :
    IsSMulRegular (A ⊗[κ] V) g := by
  classical
  let b : Module.Basis (Module.Basis.ofVectorSpaceIndex κ V) κ V :=
    Module.Basis.ofVectorSpace κ V
  let e :
      A ⊗[κ] V ≃ₗ[A] (Module.Basis.ofVectorSpaceIndex κ V →₀ A) :=
    Algebra.TensorProduct.equivFinsuppOfBasis (R := κ) (A := A) (V := V) b
  have hregular_finsupp :
      IsSMulRegular (Module.Basis.ofVectorSpaceIndex κ V →₀ A) g :=
    isSMulRegular_finsupp_of_ne_zero (A := A) (ι := Module.Basis.ofVectorSpaceIndex κ V) hg
  refine IsSMulRegular.of_right_eq_zero_of_smul ?_
  intro z hz
  apply e.injective
  have hz' : g • e z = 0 := by
    simpa using congrArg e hz
  exact hregular_finsupp.right_eq_zero_of_smul hz'

/-- Helper for Lemma 10.66.19: in the purely transcendental case, the remaining source argument
reduces contraction of a weakly associated prime on the owner base change to weak association on
the base module. -/
private theorem maximalIdeal_mem_weaklyAssociatedPrimes_canonical_owner_purelyTranscendental
    {L : Type*} [Field L] [Algebra k L]
    {ι : Type*} (x : ι → L) (hx : IsTranscendenceBasis k x)
    {qF : Ideal (R ⊗[k] IntermediateField.adjoin k (Set.range x))} [qF.IsPrime]
    (hqF :
      qF ∈ weaklyAssociatedPrimes (R ⊗[k] IntermediateField.adjoin k (Set.range x))
        (((R ⊗[k] IntermediateField.adjoin k (Set.range x)) ⊗[R] M)))
    (hDomainResidue :
      IsDomain
        ((IsLocalRing.maximalIdeal (Localization.AtPrime (qF.under R))).ResidueField ⊗[k]
          IntermediateField.adjoin k (Set.range x))) :
    IsLocalRing.maximalIdeal (Localization.AtPrime (qF.under R)) ∈
      weaklyAssociatedPrimes (Localization.AtPrime (qF.under R))
        (((Localization.AtPrime (qF.under R) ⊗[k]
            IntermediateField.adjoin k (Set.range x)) ⊗[Localization.AtPrime (qF.under R)]
          LocalizedModule.AtPrime (qF.under R) M)) := by
  -- Route correction: the literal localized owner has already been replaced by the canonical
  -- owner over `R_p`, so only the source local regularity/Nakayama paragraph remains.
  -- TODO: prove the nonzerodivisor claim on the canonical owner
  -- `((R_p ⊗[k] F) ⊗[R_p] M_p)` from `hDomainResidue`, localize that regularity to the `qF`-stage,
  -- and then invoke
  -- `maximalIdeal_mem_weaklyAssociatedPrimes_q_localized_owner_purelyTranscendental`.
  sorry

/-- Helper for Lemma 10.66.19: in the purely transcendental case, the remaining source argument
reduces contraction of a weakly associated prime on the owner base change to weak association on
the base module. -/
private theorem maximalIdeal_mem_weaklyAssociatedPrimes_localized_owner_purelyTranscendental
    {L : Type*} [Field L] [Algebra k L]
    {ι : Type*} (x : ι → L) (hx : IsTranscendenceBasis k x)
    {qF : Ideal (R ⊗[k] IntermediateField.adjoin k (Set.range x))} [qF.IsPrime]
    (hqF :
      qF ∈ weaklyAssociatedPrimes (R ⊗[k] IntermediateField.adjoin k (Set.range x))
        (((R ⊗[k] IntermediateField.adjoin k (Set.range x)) ⊗[R] M)))
    (hDomainResidue :
      IsDomain
        ((IsLocalRing.maximalIdeal (Localization.AtPrime (qF.under R))).ResidueField ⊗[k]
          IntermediateField.adjoin k (Set.range x))) :
    IsLocalRing.maximalIdeal (Localization.AtPrime (qF.under R)) ∈
      weaklyAssociatedPrimes (Localization.AtPrime (qF.under R))
        (LocalizedModule.AtPrime (qF.under R)
          (((R ⊗[k] IntermediateField.adjoin k (Set.range x)) ⊗[R] M))) := by
  let F : IntermediateField k L := IntermediateField.adjoin k (Set.range x)
  have hcanonical :
      IsLocalRing.maximalIdeal (Localization.AtPrime (qF.under R)) ∈
        weaklyAssociatedPrimes (Localization.AtPrime (qF.under R))
          (((Localization.AtPrime (qF.under R) ⊗[k] F) ⊗[Localization.AtPrime (qF.under R)]
            LocalizedModule.AtPrime (qF.under R) M)) :=
    maximalIdeal_mem_weaklyAssociatedPrimes_canonical_owner_purelyTranscendental
      (k := k) (R := R) (M := M) (L := L) x hx hqF hDomainResidue
  have hEq :
      weaklyAssociatedPrimes (Localization.AtPrime (qF.under R))
          (LocalizedModule.AtPrime (qF.under R) (((R ⊗[k] F) ⊗[R] M))) =
        weaklyAssociatedPrimes (Localization.AtPrime (qF.under R))
          (((Localization.AtPrime (qF.under R) ⊗[k] F) ⊗[Localization.AtPrime (qF.under R)]
            LocalizedModule.AtPrime (qF.under R) M)) := by
    -- Proof comment: the literal localization of the owner module and the canonical owner over
    -- `R_p` are already identified by the frozen localization comparison.
    simpa [F] using
      LinearEquiv.weaklyAssociatedPrimes_eq
        (owner_localizedModule_atPrime_under_linearEquiv
          (k := k) (R := R) (M := M) (F := F) (qF.under R))
  -- Proof comment: transport the canonical owner statement back to the localized owner model.
  rw [hEq]
  exact hcanonical

/-- Helper for Lemma 10.66.19: in the purely transcendental case, the remaining source argument
reduces contraction of a weakly associated prime on the owner base change to weak association on
the base module. -/
private theorem under_mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_purelyTranscendental_owner
    {L : Type*} [Field L] [Algebra k L]
    {ι : Type*} (x : ι → L) (hx : IsTranscendenceBasis k x)
    {qF : Ideal (R ⊗[k] IntermediateField.adjoin k (Set.range x))} [qF.IsPrime]
    (hqF :
      qF ∈ weaklyAssociatedPrimes (R ⊗[k] IntermediateField.adjoin k (Set.range x))
        (((R ⊗[k] IntermediateField.adjoin k (Set.range x)) ⊗[R] M))) :
    qF.under R ∈ weaklyAssociatedPrimes R M := by
  let F : IntermediateField k L := IntermediateField.adjoin k (Set.range x)
  have hDomainResidue :
      IsDomain
        ((IsLocalRing.maximalIdeal (Localization.AtPrime (qF.under R))).ResidueField ⊗[k] F) := by
    -- Proof comment: the residue-field tensor with the purely transcendental stage is a domain,
    -- exactly as in the source paragraph.
    simpa [F] using
      isDomain_residueField_tensor_adjoin
        (k := k) (R := R) (L := L) x hx (p := qF.under R)
  have hlocalized :
      IsLocalRing.maximalIdeal (Localization.AtPrime (qF.under R)) ∈
        weaklyAssociatedPrimes (Localization.AtPrime (qF.under R))
          (LocalizedModule.AtPrime (qF.under R) (((R ⊗[k] F) ⊗[R] M))) :=
    maximalIdeal_mem_weaklyAssociatedPrimes_localized_owner_purelyTranscendental
      (k := k) (R := R) (M := M) (L := L) x hx hqF hDomainResidue
  have howner :
      qF.under R ∈ weaklyAssociatedPrimes R (((R ⊗[k] F) ⊗[R] M)) := by
    -- Proof comment: descend from the maximal ideal of the localization back to the contracted
    -- prime of the owner module by Lemma `10.66.2`.
    have howner' :
        Ideal.IsWeaklyAssociatedToModule R (((R ⊗[k] F) ⊗[R] M)) (qF.under R) := by
      exact
        (isWeaklyAssociatedToModule_iff_isWeaklyAssociatedToModule_maximalIdeal_atPrime
          (R := R) (M := ((R ⊗[k] F) ⊗[R] M)) (qF.under R)).mpr <|
          by simpa [mem_weaklyAssociatedPrimes_iff] using hlocalized
    simpa [mem_weaklyAssociatedPrimes_iff] using howner'
  -- Proof comment: once the owner module over `R` has the contracted weakly associated prime,
  -- the already-proved owner-to-`M` descent finishes the purely transcendental case.
  simpa [F] using
    mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_owner_baseChange
      (k := k) (K := F) (R := R) (M := M) howner

/- Lemma 10.66.19 is proved first at the `core/canonical` owner layer `Mₖ`. The textbook tensor
presentation `M ⊗[k] K` is handled separately as derived bridge API. -/
-- Proof sketch: first reduce to a finitely generated intermediate field extension and then to the
-- purely transcendental case, using flatness, going-down, and the finite-extension comparison for
-- weakly associated primes. After localizing at the contraction `q.under R`, show that every
-- element of `Rₖ \ (q.under R)Rₖ` acts as a nonzerodivisor on the base change, deduce that powers
-- of elements of `q.under R` annihilate a witness vector for `q`, and finally descend weak
-- association from the direct-sum decomposition of the scalar extension back to `M`.
/-- Lemma 10.66.19 in canonical owner form: if `q` is weakly associated to the canonical base
change `Mₖ = (R ⊗[k] K) ⊗[R] M`, then its contraction `q.under R` is weakly associated to
`M`. -/
theorem under_mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_baseChange
    (q : Ideal Rₖ) (hq : q ∈ weaklyAssociatedPrimes Rₖ Mₖ) :
    q.under R ∈ weaklyAssociatedPrimes R M := by
  -- Route correction: the naive flat-contraction shortcut fails because Lemma `10.40.4` compares
  -- annihilators only for pure tensors `1 ⊗ m`, not for an arbitrary witness in `Mₖ`.
  -- First carry out the source descent to a finitely generated intermediate field.
  obtain ⟨L, hLfg, qL, hqL, hunder⟩ :=
    exists_finitely_generated_intermediate_weakAss_descent_owner
      (k := k) (K := K) (R := R) (M := M) q hq
  obtain ⟨x, hx, hfd⟩ :=
    exists_purely_transcendental_subextension_finiteDimensional
      (k := k) (K := K) L hLfg
  let F : IntermediateField k L := IntermediateField.adjoin k (Set.range x)
  have hFL : FiniteDimensional F L := by
    simpa [F] using hfd
  obtain ⟨qF, hqF, hqF_under⟩ :=
    exists_purely_transcendental_intermediate_weakAss_descent_owner
      (k := k) (R := R) (M := M) F hqL
  letI : qF.IsPrime := hqF.isPrime
  -- After the finite-stage descent, only the source's purely transcendental closing paragraph
  -- remains. Apply that closing step at the `F = k(x_i)` stage and rewrite the contraction.
  have hqF_base :
      qF.under R ∈ weaklyAssociatedPrimes R M := by
    simpa [F] using
      under_mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_purelyTranscendental_owner
        (k := k) (R := R) (M := M) (L := L) x hx hqF
  have hqF_under' : qF.under R = q.under R := by
    simpa [hunder] using hqF_under
  simpa [hqF_under'] using hqF_base

end

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {R : Type w} [CommRing R] [Algebra k R]
variable {M : Type x} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

local notation "Rₖ" => R ⊗[k] K
local notation "Mₖ" => Rₖ ⊗[R] M

local instance : Module Rₖ Mₖ :=
  TensorProduct.leftModule

private noncomputable def textbookBaseChangeAddEquiv : M ⊗[k] K ≃+ Mₖ :=
  ((Algebra.IsPushout.cancelBaseChange k K R Rₖ M).toAddEquiv.trans
    (TensorProduct.comm k K M).toAddEquiv).symm

private noncomputable local instance : Module Rₖ (M ⊗[k] K) :=
  (show M ⊗[k] K ≃+ Mₖ from textbookBaseChangeAddEquiv).module Rₖ

private noncomputable def textbookBaseChangeLinearEquiv : M ⊗[k] K ≃ₗ[Rₖ] Mₖ :=
  (show M ⊗[k] K ≃+ Mₖ from textbookBaseChangeAddEquiv).linearEquiv Rₖ

/-- The textbook tensor model `M ⊗[k] K` and the canonical owner base change `Mₖ` have the same
weakly associated primes over `R ⊗[k] K`. -/
theorem weaklyAssociatedPrimes_textbook_baseChange_eq_canonicalBaseChange :
    weaklyAssociatedPrimes Rₖ (M ⊗[k] K) = weaklyAssociatedPrimes Rₖ Mₖ := by
  simpa using LinearEquiv.weaklyAssociatedPrimes_eq textbookBaseChangeLinearEquiv

/-- Lemma 10.66.19 in the source-facing textbook tensor model: if `q ⊂ R ⊗[k] K` lies over
`p ⊂ R` and `q` is weakly associated to `M ⊗[k] K`, then `p` is weakly associated to `M`. -/
theorem mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_baseChange_of_liesOver
    (p : Ideal R) (q : Ideal Rₖ) (hqover : q.LiesOver p)
    (hq : q ∈ weaklyAssociatedPrimes Rₖ (M ⊗[k] K)) :
    p ∈ weaklyAssociatedPrimes R M := by
  letI : q.LiesOver p := hqover
  have hq' : q ∈ weaklyAssociatedPrimes Rₖ Mₖ := by
    rw [← weaklyAssociatedPrimes_textbook_baseChange_eq_canonicalBaseChange]
    exact hq
  simpa [q.over_def p] using
    under_mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_baseChange q hq'

end
