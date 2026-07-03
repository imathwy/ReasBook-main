import Mathlib
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_39_7 (from Chap10) -/
universe u v w

section flat_base_change

variable {R : Type u} {R' : Type v} [CommRing R] [CommRing R'] [Algebra R R']
variable {M : Type w} [AddCommGroup M] [Module R M]

section

variable [Module.Flat R M]

/- Lemma 10.39.7 (Stacks tag `00HI`): if `M` is flat over `R`, then its base change to `R'` is
flat over `R'`. In mathlib the canonical base-changed module is `R' ⊗[R] M`, which is canonically
isomorphic to the textbook tensor product `M ⊗[R] R'`. This is exactly `Module.Flat.baseChange`. -/
recall Module.Flat.baseChange

end

section

variable [Module.FaithfullyFlat R M]

/- Companion recall: the faithfully flat clause of tag `00HI` is the canonical base-change
instance for `Module.FaithfullyFlat`, again on the standard mathlib model `R' ⊗[R] M` of the
textbook module `M ⊗[R] R'`. -/
recall Module.FaithfullyFlat.instTensorProduct

end

end flat_base_change

/-! ### Lemma_10_39_8 (from Chap10) -/
/- Lemma 10.39.8 (Stacks tag `00HJ`): for a faithfully flat ring map `R → R'`, an `R`-module `M`
is flat over `R` if and only if its canonical base change `R' ⊗[R] M` is flat over `R'`. This is
exactly the canonical faithfully flat descent theorem `Module.Flat.iff_flat_tensorProduct`; the
textbook notation `M' = R' ⊗[R] M` is just the usual name for this base-changed module. -/
recall Module.Flat.iff_flat_tensorProduct

/-! ### Lemma_10_39_9 (from Chap10) -/
open TensorProduct
open AlgebraTensorModule
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {S' : Type w} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
variable {M : Type x} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

private theorem lTensor_assoc_naturality
    {N N' : Type*} [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
    (f : N →ₗ[R] N') :
    lTensor S S' (lTensor S M f) ∘ₗ (assoc R S S' S' M N).restrictScalars S =
      (assoc R S S' S' M N').restrictScalars S ∘ₗ lTensor S (S' ⊗[S] M) f := by
  ext s m n
  rfl

-- Proof sketch: for any injective `R`-linear map `N → N'`, first tensor with `M` over `R`, then
-- identify tensoring with `S' ⊗[S] M` over `R` with tensoring the resulting map with `S'` over
-- `S`; flatness of `S → S'` preserves injectivity.
/-- Lemma 10.39.9 (1), in canonical module form: if `S'` is flat over `S` and `M` is flat over
`R`, then `S' ⊗[S] M` is flat over `R`. -/
theorem flat_baseChange_of_flat [Module.Flat S S'] [Module.Flat R M] :
    Module.Flat R (S' ⊗[S] M) := by
  rw [Module.Flat.iff_lTensor_exact]
  intro N₁ N₂ N₃ _ _ _ _ _ _ l₁₂ l₂₃ h
  have hM : Function.Exact (lTensor S M l₁₂) (lTensor S M l₂₃) := by
    simpa [coe_lTensor] using Module.Flat.lTensor_exact M h
  have hS' : Function.Exact (lTensor S S' (lTensor S M l₁₂)) (lTensor S S' (lTensor S M l₂₃)) := by
    simpa [coe_lTensor] using Module.Flat.lTensor_exact S' hM
  have hBase :
      Function.Exact (lTensor S (S' ⊗[S] M) l₁₂) (lTensor S (S' ⊗[S] M) l₂₃) :=
    (Function.Exact.iff_of_ladder_linearEquiv
      (lTensor_assoc_naturality l₁₂)
      (lTensor_assoc_naturality l₂₃)).1 hS'
  simpa [coe_lTensor] using hBase

-- Proof sketch: the forward implication is `flat_baseChange_of_flat`; for the converse, test
-- `R`-flatness on injective maps, tensor the resulting kernel criterion with `S'` over `S`, and
-- use faithful flatness of `S → S'` to reflect injectivity back to the original map.
/-- Lemma 10.39.9 (2), in canonical module form: if `S'` is faithfully flat over `S`, then an
`S`-module `M` is flat over `R` if and only if its base change `S' ⊗[S] M` is flat over `R`. -/
theorem flat_iff_flat_baseChange_of_faithfullyFlat
    [Module.FaithfullyFlat S S'] :
    Module.Flat R M ↔ Module.Flat R (S' ⊗[S] M) := by
  constructor
  · intro
    exact flat_baseChange_of_flat
  · intro hBaseChange
    rw [Module.Flat.iff_lTensor_exact]
    intro N₁ N₂ N₃ _ _ _ _ _ _ l₁₂ l₂₃ h
    have hS' : Function.Exact (lTensor S (S' ⊗[S] M) l₁₂) (lTensor S (S' ⊗[S] M) l₂₃) := by
      simpa [coe_lTensor] using Module.Flat.lTensor_exact (S' ⊗[S] M) h
    have hBase : Function.Exact (lTensor S S' (lTensor S M l₁₂)) (lTensor S S' (lTensor S M l₂₃)) :=
      Function.Exact.of_ladder_linearEquiv_of_exact
        (lTensor_assoc_naturality l₁₂)
        (lTensor_assoc_naturality l₂₃)
        hS'
    have hM : Function.Exact (lTensor S M l₁₂) (lTensor S M l₂₃) :=
      Module.FaithfullyFlat.lTensor_reflects_exact S S' (lTensor S M l₁₂) (lTensor S M l₂₃)
        hBase
    simpa [coe_lTensor] using hM

end

/-! ### Lemma_10_39_10 (from Chap10) -/
open TensorProduct
open AlgebraTensorModule

universe u v w

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 10.39.10: if an `S`-module `M` is flat as an `R`-module and faithfully flat as an
`S`-module, then the algebra map `R → S` is flat. -/
theorem algebraMap_flat_of_flat_of_faithfullyFlat (M : Type w) [AddCommGroup M] [Module S M]
    [Module.Flat R (RestrictScalars R S M)] [Module.FaithfullyFlat S M] :
    (algebraMap R S).Flat := by
  letI : Module R M := Module.restrictScalars R S M
  letI : IsScalarTower R S M := IsScalarTower.restrictScalars R S M
  letI : Module.Flat R M := by
    change Module.Flat R (RestrictScalars R S M)
    infer_instance
  rw [RingHom.flat_algebraMap_iff, Module.Flat.iff_lTensor_exact]
  intro N₁ N₂ N₃ _ _ _ _ _ _ l₁₂ l₂₃ h
  have hM : Function.Exact (lTensor S M l₁₂) (lTensor S M l₂₃) := by
    simpa [coe_lTensor] using Module.Flat.lTensor_exact M h
  have hSM :
      Function.Exact (lTensor S M (lTensor S S l₁₂))
        (lTensor S M (lTensor S S l₂₃)) :=
    (Function.Exact.iff_of_ladder_linearEquiv
      (lTensor_comp_cancelBaseChange R S S l₁₂)
      (lTensor_comp_cancelBaseChange R S S l₂₃)).1 hM
  simpa using
    (Module.FaithfullyFlat.lTensor_exact_iff_exact S M
      (lTensor S S l₁₂) (lTensor S S l₂₃)).1 hSM

end

/-! ### Lemma_10_39_11_Equational_criterion_of_flatness (from Chap10) -/
section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/- Lemma 10.39.11 (Equational criterion of flatness): an `R`-module `M` is flat if and only if
every relation in `M` is trivial. In mathlib, triviality of a finite relation
`∑ i, f i • x i = 0` is the predicate `Module.IsTrivialRelation f x`, and the canonical owner
theorem for this criterion is `Module.Flat.iff_forall_isTrivialRelation`. -/
recall Module.Flat.iff_forall_isTrivialRelation

end

/-! ### Lemma_10_39_12 (from Chap10) -/
universe u

open CategoryTheory MonoidalCategory
open LinearMap

namespace CategoryTheory.ShortComplex.ShortExact

section

variable {R : Type u} [CommRing R]

/- Domain triage:
- primary domain: flat modules and tensor exactness for short complexes of `R`-modules;
- sampled owner declarations: `CategoryTheory.ShortComplex.UniversallyExact`,
  `LinearMap.UniversallyInjective`, `Module.Flat.iff_lTensor_exact`, and `ShortComplex.map`;
- owner choice: universal exactness of a short complex is the canonical owner-level statement, and
  short exactness after tensoring with a fixed module is the source-facing companion statement.
-/

-- Proof sketch: exactness and flatness of the cokernel give universal injectivity of `S.f` via
-- `LinearMap.lTensor_injective_of_exact_of_flat`, so `S` is universally exact in the owner sense.
/-- Lemma 10.39.12, owner form: a short exact sequence of `R`-modules with flat cokernel is
universally exact. -/
theorem universallyExact_of_flat_X₃ {S : ShortComplex (ModuleCat R)}
    (hS : S.ShortExact) [Module.Flat R S.X₃] :
    ShortComplex.UniversallyExact S := by
  -- First extract the function-level exactness data from the short exact sequence.
  have hExact : Function.Exact S.f.hom S.g.hom := by
    simpa using (ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  have hSurj : Function.Surjective S.g.hom := hS.moduleCat_surjective_g
  refine ⟨hS, ?_⟩
  intro Q _ _
  -- The flat cokernel criterion gives injectivity after left tensoring, and commutativity of the
  -- tensor factors converts that to the `rTensor` formulation used by `UniversallyInjective`.
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
  exact LinearMap.lTensor_injective_of_exact_of_flat S.g.hom hSurj S.f.hom
    hS.moduleCat_injective_f hExact Q

-- Proof sketch: combine the owner form `universallyExact_of_flat_X₃` with right exactness of
-- tensor products and the universal injectivity of the first map.
/-- Lemma 10.39.12: if `0 ⟶ M'' ⟶ M' ⟶ M ⟶ 0` is a short exact sequence of `R`-modules and
`M` is flat, then for every `R`-module `N` the tensor sequence
`0 ⟶ N ⊗[R] M'' ⟶ N ⊗[R] M' ⟶ N ⊗[R] M ⟶ 0` is short exact. -/
theorem tensorLeft_of_flat_cokernel {S : ShortComplex (ModuleCat R)}
    (hS : S.ShortExact) [Module.Flat R S.X₃] (N : ModuleCat R) :
    (S.map (tensorLeft N)).ShortExact := by
  have hU : ShortComplex.UniversallyExact S := universallyExact_of_flat_X₃ hS
  have hExact : Function.Exact S.f.hom S.g.hom := by
    simpa using (ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  have hSurj : Function.Surjective S.g.hom := hS.moduleCat_surjective_g
  have hTensorExact : Function.Exact (S.f.hom.lTensor N) (S.g.hom.lTensor N) :=
    lTensor_exact N hExact hSurj
  -- Universal exactness supplies injectivity of the first tensorized map.
  have hTensorInj : Function.Injective (S.f.hom.lTensor N) := by
    rw [LinearMap.lTensor_inj_iff_rTensor_inj]
    exact hU.universallyInjective_f N inferInstance inferInstance
  -- Flatness of the cokernel gives exactness after tensoring, and surjectivity is preserved.
  refine ModuleCat.shortComplex_shortExact (S.map (tensorLeft N)) ?_ ?_ ?_
  · simpa [ModuleCat.hom_whiskerLeft] using hTensorExact
  · simpa [ModuleCat.hom_whiskerLeft] using hTensorInj
  · simpa [ModuleCat.hom_whiskerLeft] using LinearMap.lTensor_surjective N hSurj

end

end CategoryTheory.ShortComplex.ShortExact

/-! ### Lemma_10_39_13 (from Chap10) -/
universe u

open LinearMap

namespace CategoryTheory
namespace ShortComplex

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat R)}

/- Domain-style sampling:
- primary domain: flatness propagation in short exact complexes of `R`-modules;
- inspected owner declarations: `CategoryTheory.ShortComplex.ShortExact`,
  `CategoryTheory.ShortComplex.UniversallyExact.flat_X₁`,
  `CategoryTheory.ShortComplex.ShortExact.universallyExact_of_flat_X₃`,
  `LinearMap.lTensor_injective_of_exact_of_flat`;
- owner abstraction: `S.ShortExact` is the source-facing owner for the middle-term statement,
  while `UniversallyExact S` is only the bridge/view needed for the left-term statement;
- primitive data vs. derived API: short exactness is the primitive datum for `flat_X₂`, while
  universal exactness is derived from flatness of the cokernel and used only to recover `flat_X₁`.
  No separate equivalence wrapper between `flat_X₁` and `flat_X₂` is mathematically primitive. -/

namespace ShortExact

/-- Lemma 10.39.13 (1): in a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of `R`-modules, if the
left and right terms are flat, then the middle term is flat. -/
theorem flat_X₂ (hS : S.ShortExact) [Module.Flat R S.X₁] [Module.Flat R S.X₃] :
    Module.Flat R S.X₂ := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ i hi
  have hExact : Function.Exact S.f.hom S.g.hom := by
    simpa using (ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  have hSurj : Function.Surjective S.g.hom := hS.moduleCat_surjective_g
  have hN₁ : Function.Exact (0 : Unit →ₗ[R] TensorProduct R N S.X₁) (lTensor N S.f.hom) := by
    rw [LinearMap.exact_zero_iff_injective]
    exact LinearMap.lTensor_injective_of_exact_of_flat S.g.hom hSurj S.f.hom
      hS.moduleCat_injective_f hExact N
  have hN₂ : Function.Exact (lTensor N S.f.hom) (lTensor N S.g.hom) :=
    lTensor_exact N hExact hSurj
  have hP₁ : Function.Exact (0 : Unit →ₗ[R] TensorProduct R P S.X₁) (lTensor P S.f.hom) := by
    rw [LinearMap.exact_zero_iff_injective]
    exact LinearMap.lTensor_injective_of_exact_of_flat S.g.hom hSurj S.f.hom
      hS.moduleCat_injective_f hExact P
  exact LinearMap.injective_of_surjective_of_injective_of_injective
    (0 : Unit →ₗ[R] TensorProduct R N S.X₁) (lTensor N S.f.hom) (lTensor N S.g.hom)
    (0 : Unit →ₗ[R] TensorProduct R P S.X₁) (lTensor P S.f.hom) (lTensor P S.g.hom)
    (0 : Unit →ₗ[R] Unit) (i.rTensor S.X₁) (i.rTensor S.X₂) (i.rTensor S.X₃)
    (by ext; simp)
    (by
      ext x
      simp [LinearMap.lTensor_comp_rTensor])
    (by
      ext x
      simp [LinearMap.lTensor_comp_rTensor])
    hN₁ hN₂ hP₁
    (by
      intro u
      cases u
      exact ⟨(), rfl⟩)
    (Module.Flat.rTensor_preserves_injective_linearMap i hi)
    (Module.Flat.rTensor_preserves_injective_linearMap i hi)

/-- Lemma 10.39.13 (2): in a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of `R`-modules, if the
middle and right terms are flat, then the left term is flat. -/
theorem flat_X₁ (hS : S.ShortExact) [Module.Flat R S.X₂] [Module.Flat R S.X₃] :
    Module.Flat R S.X₁ :=
  UniversallyExact.flat_X₁ (universallyExact_of_flat_X₃ hS)

end ShortExact
end ShortComplex
end CategoryTheory

/-! ### Lemma_10_39_14 (from Chap10) -/
universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Lemma 10.39.14 is a `bridge/view` restatement of the owner theorem
`Module.FaithfullyFlat.iff_zero_iff_rTensor_zero`: an `R`-module `M` is faithfully flat if and
only if it is flat and for every `R`-linear map `α : N →ₗ[R] N'`, one has `α = 0` exactly when
the induced map `LinearMap.rTensor M α` is zero. The source wording `α = 0 ↔ α ⊗ id_M = 0`
simply reverses the inner equivalence, so the main entry should be direct canonical recall. -/
recall Module.FaithfullyFlat.iff_zero_iff_rTensor_zero

end

/-! ### Lemma_10_39_15 (from Chap10) -/
open scoped TensorProduct

universe u v

section

/- Layering for this item:
* source-facing: fiberwise nontriviality over prime and maximal residue fields;
* core/canonical owner: `Module.FaithfullyFlat` together with its tensor-faithfulness and
  proper-ideal criteria;
* bridge/view: the canonical comparison
  `M ⊗[R] m.ResidueField ≃ₗ[R] M ⧸ m • (⊤ : Submodule R M)` for maximal ideals.
-/

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- For a maximal ideal `m`, tensoring with `m.ResidueField` is equivalent to reducing modulo
`m • M`. This is the nontriviality form of the canonical quotient-residue-field identification
combined with `TensorProduct.tensorQuotEquivQuotSMul`. -/
theorem nontrivial_tensor_residueField_iff_nontrivial_quotSMul
    (m : Ideal R) [m.IsMaximal] :
    Nontrivial (M ⊗[R] m.ResidueField) ↔ Nontrivial (M ⧸ m • (⊤ : Submodule R M)) := by
  let e : M ⊗[R] m.ResidueField ≃ₗ[R] M ⧸ m • (⊤ : Submodule R M) :=
    (TensorProduct.congr (LinearEquiv.refl R M)
        (AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ m) m.ResidueField)
          (Ideal.bijective_algebraMap_quotient_residueField m)).toLinearEquiv).symm ≪≫ₗ
      TensorProduct.tensorQuotEquivQuotSMul M m
  exact e.nontrivial_congr

section Flat

variable [Module.Flat R M]

open Module.FaithfullyFlat

/-- A flat `R`-module is faithfully flat if and only if all of its fibers over maximal ideals are
nontrivial. -/
theorem faithfullyFlat_iff_forall_nontrivial_tensor_residueField :
    Module.FaithfullyFlat R M ↔
      ∀ (m : Ideal R) (_ : m.IsMaximal), Nontrivial (M ⊗[R] m.ResidueField) := by
  constructor
  · intro h m hm
    letI : Module.FaithfullyFlat R M := h
    letI : m.IsMaximal := hm
    infer_instance
  · intro h
    refine (iff_flat_and_proper_ideal R M).2 ?_
    refine ⟨inferInstance, fun I hI htop ↦ ?_⟩
    obtain ⟨m, hm, hIm⟩ := I.exists_le_maximal hI
    have hmQuot : Nontrivial (M ⧸ m • (⊤ : Submodule R M)) :=
      (nontrivial_tensor_residueField_iff_nontrivial_quotSMul m).mp (h m hm)
    have hmTop : m • (⊤ : Submodule R M) = ⊤ := eq_top_iff.2 <| by
      calc
        ⊤ = I • (⊤ : Submodule R M) := htop.symm
        _ ≤ m • (⊤ : Submodule R M) := Submodule.smul_mono hIm le_rfl
    exact (not_nontrivial_iff_subsingleton.mpr <| by rwa [Submodule.Quotient.subsingleton_iff]) hmQuot

/-- A flat `R`-module is faithfully flat if and only if all of its fibers over prime ideals are
nontrivial. -/
theorem faithfullyFlat_iff_forall_nontrivial_tensor_primeResidueField :
    Module.FaithfullyFlat R M ↔
      ∀ p : PrimeSpectrum R, Nontrivial (M ⊗[R] p.asIdeal.ResidueField) := by
  constructor
  · intro h p
    letI : Module.FaithfullyFlat R M := h
    infer_instance
  · intro h
    exact faithfullyFlat_iff_forall_nontrivial_tensor_residueField.2 fun m hm ↦ by
      letI : m.IsPrime := hm.isPrime
      exact h (⟨m, inferInstance⟩ : PrimeSpectrum R)

/-- Lemma 10.39.15: for a flat `R`-module `M`, the following are equivalent: `M` is faithfully
flat; for every nontrivial `R`-module `N`, the tensor product `M ⊗[R] N` is nontrivial; for every
prime `p : PrimeSpectrum R`, the fiber `M ⊗[R] κ(p)` is nontrivial; and for every maximal ideal
`m`, the tensor product `M ⊗[R] m.ResidueField` is nontrivial, equivalently `M ⧸ m • ⊤` is
nontrivial via `nontrivial_tensor_residueField_iff_nontrivial_quotSMul`. -/
-- Proof sketch: use `Module.FaithfullyFlat.iff_flat_and_lTensor_faithful` for the equivalence
-- between faithful flatness and nontriviality after tensoring with every nontrivial module. The
-- implications to prime and maximal residue fields are immediate specializations. For the converse,
-- use the maximal-ideal hypothesis together with the tensor-quotient identification
-- `M ⊗[R] κ(m) ≃ₗ[R] M ⧸ m • ⊤` and the canonical proper-ideal criterion
-- `Module.FaithfullyFlat.iff_flat_and_proper_ideal`.
theorem faithfullyFlat_tfae_nontrivial_tensor_residueField :
    List.TFAE
      [Module.FaithfullyFlat R M,
        ∀ (N : Type (max u v)) [AddCommGroup N] [Module R N],
          Nontrivial N → Nontrivial (M ⊗[R] N),
        ∀ p : PrimeSpectrum R, Nontrivial (M ⊗[R] p.asIdeal.ResidueField),
        ∀ (m : Ideal R) (_ : m.IsMaximal), Nontrivial (M ⊗[R] m.ResidueField)] := by
  tfae_have 1 ↔ 2 := by
    rw [iff_flat_and_lTensor_faithful]
    exact and_iff_right inferInstance
  tfae_have 1 ↔ 3 := by
    exact faithfullyFlat_iff_forall_nontrivial_tensor_primeResidueField
  tfae_have 1 ↔ 4 := by
    exact faithfullyFlat_iff_forall_nontrivial_tensor_residueField
  tfae_finish

end Flat

end

/-! ### Lemma_10_39_16 (from Chap10) -/
universe u v

section

open PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Layering for this item:
* source-facing: `faithfullyFlat_iff_closedPoints_subset_range`, the textbook closed-point
  criterion for faithful flatness;
* core/canonical owner: `RingHom.FaithfullyFlat`, `PrimeSpectrum.comap`,
  `StableUnderGeneralization`, and `closedPoints`;
* bridge/view: `specComap_surjective_iff_closedPoints_subset_range`, which rewrites the
  source criterion through the owner theorem
  `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`.
-/

-- Proof sketch: for the forward direction, surjectivity obviously implies that every closed point
-- lies in the image. For the converse, the image of `Spec(S) → Spec(R)` is stable under
-- generalization for a flat map, so containing all closed points forces surjectivity.
/-- Lemma 10.39.16, clauses (2) and (3): for a flat ring map `f : R →+* S`, the induced map
`Spec(S) → Spec(R)` is surjective if and only if every closed point of `Spec(R)` lies in its
image. -/
theorem specComap_surjective_iff_closedPoints_subset_range (f : R →+* S) (hf : f.Flat) :
    Function.Surjective (comap f) ↔ closedPoints (PrimeSpectrum R) ⊆ Set.range (comap f) := by
  constructor
  · intro h x hx
    exact Set.mem_range.mpr (h x)
  · intro hclosed x
    let image : Set (PrimeSpectrum R) := Set.range (comap f)
    have himage : StableUnderGeneralization image :=
      (RingHom.Flat.generalizingMap_comap hf).stableUnderGeneralization_range
    obtain ⟨m, hm, hxm⟩ := x.asIdeal.exists_le_maximal x.2.1
    let xMax : PrimeSpectrum R := ⟨m, hm.isPrime⟩
    have hxMax : xMax ∈ image := by
      apply hclosed
      simpa [closedPoints] using
        (isClosed_singleton_iff_isMaximal xMax).2 hm
    exact himage ((le_iff_specializes x xMax).mp hxm) hxMax

/-- Lemma 10.39.16: for a flat ring map `f : R →+* S`, `f` is faithfully flat if and only if
every closed point of `Spec(R)` lies in the image of `Spec(S) → Spec(R)`. Together with the
canonical theorem `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`, this recovers the
textbook three-way equivalence with surjectivity of `Spec(S) → Spec(R)`. -/
theorem faithfullyFlat_iff_closedPoints_subset_range (f : R →+* S) (hf : f.Flat) :
    f.FaithfullyFlat ↔ closedPoints (PrimeSpectrum R) ⊆ Set.range (comap f) := by
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective,
    specComap_surjective_iff_closedPoints_subset_range f hf]
  exact and_iff_right hf

end

/-! ### Lemma_10_39_17 (from Chap10) -/
/-
Lemma 10.39.17: a flat local ring homomorphism between local rings is faithfully flat.

Layering for this item:
* source-facing: a flat local ring homomorphism of local rings is faithfully flat;
* core/canonical owner: `Module.FaithfullyFlat.of_flat_of_isLocalHom`;
* bridge/view: the ring-hom statement is the canonical algebraized view for `algebraMap`.
-/
recall Module.FaithfullyFlat.of_flat_of_isLocalHom

/-! ### Lemma_10_39_18 (from Chap10) -/
universe u v w x

open scoped TensorProduct
open LocalizedModule TensorProduct
open TensorProduct.AlgebraTensorModule

section LocalizationFlatness

variable {R : Type u} [CommRing R]
variable (S : Submonoid R) {Rₛ : Type v} [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]

/- Canonical recall: for a multiplicative subset `S` of a ring `R`, the localization `S⁻¹R`
is flat as an `R`-algebra. This is exactly the canonical theorem `IsLocalization.flat`. -/
recall IsLocalization.flat

variable {N : Type w} [AddCommMonoid N] [Module R N] [Module Rₛ N] [IsScalarTower R Rₛ N]

/- Canonical recall: if `M` is a module over a localization `S⁻¹R`, then `M` is flat over `R`
if and only if it is flat over `S⁻¹R`. This is exactly the canonical theorem
`Module.flat_iff_of_isLocalization`. -/
recall Module.flat_iff_of_isLocalization

variable {M : Type v} [AddCommMonoid M] [Module R M]

-- Proof sketch: one direction is preserved by localization at a prime, and the converse follows
-- by reducing to the maximal-local criterion after localizing further at maximal ideals over each
-- prime.
/-- Lemma 10.39.18 (1): an `R`-module `M` is flat if and only if each localization `Mₚ` is flat
over `Rₚ` for every prime ideal `p` of `R`. -/
theorem flat_iff_flat_localizedModule_atPrime
    : Module.Flat R M ↔
        ∀ p : PrimeSpectrum R,
          Module.Flat (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) := by
  constructor
  · intro hM p
    -- Localizing a flat module at a prime remains flat over the localized ring.
    letI : Module.Flat R M := hM
    simpa [LocalizedModule.AtPrime] using
      (Module.Flat.localizedModule (M := M) p.asIdeal.primeCompl)
  · intro h
    -- The prime-local hypothesis in particular gives the maximal-local one.
    apply Module.flat_of_localized_maximal
    intro P hP
    exact
      (Module.flat_iff_of_isLocalization (Localization.AtPrime P) P.primeCompl
        (M := LocalizedModule.AtPrime P M)).mp <|
        by simpa [LocalizedModule.AtPrime] using h ⟨P, inferInstance⟩

-- Proof sketch: use the canonical maximal-local criterion in mathlib for one direction and
-- localization of flat modules for the reverse implication.
/-- Lemma 10.39.18 (2): an `R`-module `M` is flat if and only if each localization `Mₘ` is flat
over `Rₘ` for every maximal ideal `m` of `R`. -/
theorem flat_iff_flat_localizedModule_atMaximal
    : Module.Flat R M ↔
        ∀ m : MaximalSpectrum R,
          Module.Flat (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal M) := by
  constructor
  · intro hM m
    -- Localizing a flat module at a maximal ideal remains flat over the localized ring.
    letI : Module.Flat R M := hM
    simpa [LocalizedModule.AtPrime] using
      (Module.Flat.localizedModule (M := M) m.asIdeal.primeCompl)
  · intro h
    -- This is exactly the canonical maximal-local criterion for flatness.
    apply Module.flat_of_localized_maximal
    intro P hP
    exact
      (Module.flat_iff_of_isLocalization (Localization.AtPrime P) P.primeCompl
        (M := LocalizedModule.AtPrime P M)).mp <|
        by simpa [LocalizedModule.AtPrime] using h ⟨P, hP⟩

end LocalizationFlatness

section RelativeLocalizationFlatness

variable {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

noncomputable section

/- The localization of an `A`-module at a prime `Q` of `A` is canonically a module over the
localization of `R` at the inverse-image prime `Q ∩ R`, via the local ring map
`R_(Q ∩ R) → A_Q`. -/
noncomputable instance (Q : Ideal A) [Q.IsPrime] :
    Module (Localization.AtPrime (Q.under R)) (LocalizedModule.AtPrime Q M) :=
  Module.compHom (LocalizedModule.AtPrime Q M)
    (Localization.localRingHom (Q.under R) Q (algebraMap R A) rfl)

noncomputable instance (Q : Ideal A) [Q.IsPrime] :
    IsScalarTower (Localization.AtPrime (Q.under R)) (Localization.AtPrime Q)
      (LocalizedModule.AtPrime Q M) := by
  letI : Module (Localization.AtPrime (Q.under R)) (LocalizedModule.AtPrime Q M) :=
    Module.compHom (LocalizedModule.AtPrime Q M)
      (Localization.localRingHom (Q.under R) Q (algebraMap R A) rfl)
  simpa using
    (IsScalarTower.restrictScalars (Localization.AtPrime (Q.under R)) (Localization.AtPrime Q)
      (LocalizedModule.AtPrime Q M))

variable {N : Type x} [AddCommMonoid N] [Module R N]

/-- Helper for Lemma 10.39.18: localizing `X ⊗[R] Q` at a multiplicative subset of `A` agrees
with tensoring the localized `A`-module `X` over `R` with `Q`. -/
noncomputable def localized_tensor_right_equiv
    (T : Submonoid A) {X : Type*} [AddCommMonoid X] [Module R X] [Module A X]
    [IsScalarTower R A X] (Q : Type*) [AddCommMonoid Q] [Module R Q] :
    LocalizedModule T X ⊗[R] Q ≃ₗ[A] LocalizedModule T (X ⊗[R] Q) :=
  IsLocalizedModule.linearEquiv T
    (AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap T X))
    (LocalizedModule.mkLinearMap T (X ⊗[R] Q))

/-- Helper for Lemma 10.39.18: the `R_(q ∩ R)`-action on `M_q` is compatible with the original
`R`-action. -/
noncomputable instance (Q : Ideal A) [Q.IsPrime] :
    IsScalarTower R (Localization.AtPrime (Q.under R)) (LocalizedModule.AtPrime Q M) :=
  IsScalarTower.of_algebraMap_smul fun r x ↦ by
    change
      (Localization.localRingHom (Q.under R) Q (algebraMap R A) rfl
        (algebraMap R (Localization.AtPrime (Q.under R)) r)) • x = r • x
    rw [Localization.localRingHom_to_map]
    simp

/-- Helper for Lemma 10.39.18: the canonical localized tensor map is exactly tensoring on the
localized module. -/
lemma localized_lTensor_map_eq
    (T : Submonoid A) {X : Type*} [AddCommMonoid X] [Module R X] [Module A X]
    [IsScalarTower R A X] {Q Q' : Type*} [AddCommMonoid Q] [AddCommMonoid Q']
    [Module R Q] [Module R Q'] (f : Q →ₗ[R] Q') :
    IsLocalizedModule.map T
        (AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap T X))
        (AlgebraTensorModule.rTensor R Q' (LocalizedModule.mkLinearMap T X))
        (AlgebraTensorModule.lTensor A X f) =
      AlgebraTensorModule.lTensor A (LocalizedModule T X) f := by
  -- Freeze `map_lTensor` at the concrete localization model so later rewrites do not leave any
  -- localized codomain implicit.
  simpa using
    (IsLocalizedModule.map_lTensor (S := T) (R := R) (A := A) (M := X)
      (M' := LocalizedModule T X) (N := Q) (P := Q')
      (f := f) (g := LocalizedModule.mkLinearMap T X))

/-- Helper for Lemma 10.39.18: after the canonical localization-tensor identification, localizing
`X ⊗[R] f` agrees with tensoring `f` against the localized module `X_T`. -/
lemma localized_lTensor_intertwines
    (T : Submonoid A) {X : Type*} [AddCommMonoid X] [Module R X] [Module A X]
    [IsScalarTower R A X] {Q Q' : Type*} [AddCommMonoid Q] [AddCommMonoid Q']
    [Module R Q] [Module R Q'] (f : Q →ₗ[R] Q') :
    ((LocalizedModule.map T (AlgebraTensorModule.lTensor A X f)).restrictScalars A).comp
        (localized_tensor_right_equiv (R := R) (A := A) T Q).toLinearMap =
      (localized_tensor_right_equiv (R := R) (A := A) T Q').toLinearMap.comp
        (AlgebraTensorModule.lTensor A (LocalizedModule T X) f) := by
  -- Route correction: replace the old pure-tensor extensional proof by the canonical owner
  -- transport identity `restrictScalars_map_eq`, then rewrite the middle map by `map_lTensor`.
  let eQ := localized_tensor_right_equiv (R := R) (A := A) (X := X) T Q
  let eQ' := localized_tensor_right_equiv (R := R) (A := A) (X := X) T Q'
  have hlocalized :
      IsLocalizedModule.map T
          (AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap T X))
          (AlgebraTensorModule.rTensor R Q' (LocalizedModule.mkLinearMap T X))
          (AlgebraTensorModule.lTensor A X f) =
        AlgebraTensorModule.lTensor A (LocalizedModule T X) f :=
    localized_lTensor_map_eq (R := R) (A := A) (T := T) (X := X) f
  have hmap :
      (LocalizedModule.map T (AlgebraTensorModule.lTensor A X f)).restrictScalars A =
        (eQ'.toLinearMap.comp
          (AlgebraTensorModule.lTensor A (LocalizedModule T X) f)).comp
          eQ.symm.toLinearMap := by
    -- The canonical tensor-localization equivalence is the localized-module `iso`, so the owner
    -- theorem becomes exactly the desired conjugation formula.
    rw [LocalizedModule.restrictScalars_map_eq (R := A) (S := T)
      (g₁ := AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap T X))
      (g₂ := AlgebraTensorModule.rTensor R Q' (LocalizedModule.mkLinearMap T X))
      (l := AlgebraTensorModule.lTensor A X f)]
    rw [hlocalized]
    simpa [eQ, eQ', localized_tensor_right_equiv, IsLocalizedModule.linearEquiv,
      IsLocalizedModule.iso_localizedModule_eq_refl, LinearMap.comp_assoc]
  -- Postcompose the conjugation formula by `eQ` so the inverse comparison map cancels.
  calc
    ((LocalizedModule.map T (AlgebraTensorModule.lTensor A X f)).restrictScalars A).comp eQ.toLinearMap
        = (((eQ'.toLinearMap.comp
            (AlgebraTensorModule.lTensor A (LocalizedModule T X) f)).comp
              eQ.symm.toLinearMap).comp eQ.toLinearMap) := by
            rw [hmap]
    _ = eQ'.toLinearMap.comp (AlgebraTensorModule.lTensor A (LocalizedModule T X) f) := by
      ext z
      simp [LinearMap.comp_assoc]

/-- Helper for Lemma 10.39.18: injectivity of the localization of `X ⊗[R] f` is equivalent to
injectivity of tensoring `f` against the localized module `X_T`. -/
lemma localized_lTensor_injective_iff
    (T : Submonoid A) {X : Type*} [AddCommMonoid X] [Module R X] [Module A X]
    [IsScalarTower R A X] {Q Q' : Type*} [AddCommMonoid Q] [AddCommMonoid Q']
    [Module R Q] [Module R Q'] (f : Q →ₗ[R] Q') :
    Function.Injective (LocalizedModule.map T (AlgebraTensorModule.lTensor A X f)) ↔
      Function.Injective (AlgebraTensorModule.lTensor A (LocalizedModule T X) f) := by
  -- The owner injectivity criterion already compares the localized map with the corresponding
  -- map between arbitrary localized-module models, and the explicit adapter identifies it with
  -- tensoring on the localized module.
  have hiff :=
    (IsLocalizedModule.map_injective_iff_localizedModuleMap_injective
      (S := T)
      (g₁ := AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap T X))
      (g₂ := AlgebraTensorModule.rTensor R Q' (LocalizedModule.mkLinearMap T X))
      (l := AlgebraTensorModule.lTensor A X f)).symm
  rw [localized_lTensor_map_eq (R := R) (A := A) (T := T) (X := X) (f := f)] at hiff
  exact hiff

/-- Helper for Lemma 10.39.18: localizing an `A`-module preserves flatness over the base ring
`R`. -/
lemma flat_localizedModule_of_flat (T : Submonoid A) (hM : Module.Flat R M) :
    Module.Flat R (LocalizedModule T M) := by
  -- Use the submodule version of the flatness criterion so only additive-monoid structure is
  -- needed on the localized module.
  rw [Module.Flat.iff_lTensor_injectiveₛ] at hM ⊢
  intro Q _ _ N
  have hTensor : Function.Injective (N.subtype.lTensor M) := hM N
  have hTensorA : Function.Injective (AlgebraTensorModule.lTensor A M N.subtype) := by
    simpa [AlgebraTensorModule.coe_lTensor] using hTensor
  have hLocalized :
      Function.Injective (LocalizedModule.map T (AlgebraTensorModule.lTensor A M N.subtype)) :=
    LocalizedModule.map_injective T (AlgebraTensorModule.lTensor A M N.subtype) hTensorA
  have hLocalizedTensor :=
    (localized_lTensor_injective_iff (R := R) (A := A) T (X := M) N.subtype).mp hLocalized
  simpa [AlgebraTensorModule.coe_lTensor] using hLocalizedTensor

/-- Helper for Lemma 10.39.18: if `M` is flat over `R`, then its localization at a prime of `A`
is flat over the corresponding localized base ring `R_(q ∩ R)`. -/
lemma flat_localizedModule_atPrime_over_under_of_flat (hM : Module.Flat R M)
    (q : PrimeSpectrum A) :
    Module.Flat (Localization.AtPrime (q.asIdeal.under R))
      (LocalizedModule.AtPrime q.asIdeal M) := by
  -- First view `M_q` as an `R`-flat module, then convert to flatness over `R_(q ∩ R)`.
  letI : Module (Localization.AtPrime (q.asIdeal.under R)) (LocalizedModule.AtPrime q.asIdeal M) :=
    Module.compHom (LocalizedModule.AtPrime q.asIdeal M)
      (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R A) rfl)
  letI :
      IsScalarTower R (Localization.AtPrime (q.asIdeal.under R))
        (LocalizedModule.AtPrime q.asIdeal M) :=
      inferInstance
  have hLocalizedR : Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) :=
    flat_localizedModule_of_flat (R := R) (A := A) q.asIdeal.primeCompl hM
  exact
    (Module.flat_iff_of_isLocalization
      (Localization.AtPrime (q.asIdeal.under R)) (q.asIdeal.under R).primeCompl
      (M := LocalizedModule.AtPrime q.asIdeal M)).mpr hLocalizedR

/-- Helper for Lemma 10.39.18: flatness over `R` descends from the maximal localizations over the
under-rings `R_(m ∩ R)`. -/
lemma flat_of_flat_localizedModule_atMaximal_over_under
    (h :
      ∀ m : MaximalSpectrum A,
        Module.Flat (Localization.AtPrime (m.asIdeal.under R))
          (LocalizedModule.AtPrime m.asIdeal M)) :
    Module.Flat R M := by
  -- Convert each maximal-local hypothesis to an `R`-flat localized module and apply the owner
  -- theorem `Module.flat_of_isLocalized_maximal`.
  apply Module.flat_of_isLocalized_maximal
    (R := R) (S := A) (M := M)
    (Mₚ := fun P _ ↦ LocalizedModule.AtPrime P M)
    (f := fun P _ ↦ LocalizedModule.mkLinearMap P.primeCompl M)
  intro P hP
  letI : Module (Localization.AtPrime (P.under R)) (LocalizedModule.AtPrime P M) :=
    Module.compHom (LocalizedModule.AtPrime P M)
      (Localization.localRingHom (P.under R) P (algebraMap R A) rfl)
  letI :
      IsScalarTower R (Localization.AtPrime (P.under R)) (LocalizedModule.AtPrime P M) :=
      inferInstance
  have hPflat :
      Module.Flat (Localization.AtPrime (P.under R)) (LocalizedModule.AtPrime P M) :=
    h ⟨P, hP⟩
  exact
    (Module.flat_iff_of_isLocalization
      (Localization.AtPrime (P.under R)) (P.under R).primeCompl
      (M := LocalizedModule.AtPrime P M)).mp hPflat

/-- Helper for Lemma 10.39.18: localizing away from an element of `A` preserves flatness over
the base ring `R`. -/
lemma flat_localizedModule_away_of_flat (a : A) (hM : Module.Flat R M) :
    Module.Flat R (LocalizedModule.Away a M) := by
  -- This is the previous localization-preservation lemma specialized to a principal submonoid.
  simpa [LocalizedModule.Away] using
    flat_localizedModule_of_flat (R := R) (A := A) (Submonoid.powers a) hM

-- Proof sketch: if `M` is flat over `R`, then every localization away from a generator remains
-- flat; conversely, use the localization-away spanning criterion for flatness over the target ring.
/-- Lemma 10.39.18 (3): if `g₁, …, gₘ` generate the unit ideal of an `R`-algebra `A`, then an
`A`-module `M` is flat over `R` if and only if every localization `M[1 / gᵢ]` is flat over `R`. -/
theorem flat_iff_flat_localizedModule_away_of_span_eq_top
    {n : ℕ} (g : Fin n → A) (hg : Ideal.span (Set.range g) = ⊤) :
    Module.Flat R M ↔ ∀ i : Fin n, Module.Flat R (LocalizedModule.Away (g i) M) := by
  constructor
  · intro hM i
    -- Each localization away from a generator is still flat over `R`.
    exact flat_localizedModule_away_of_flat (R := R) (A := A) (g i) hM
  · intro hAway
    -- The local flatness data match the canonical owner `Module.flat_of_isLocalized_span`.
    apply Module.flat_of_isLocalized_span
      (R := R) (S := A) (M := M) (s := Set.range g) hg
      (Mₛ := fun a ↦ LocalizedModule.Away a.1 M)
      (g := fun a ↦ LocalizedModule.mkLinearMap (Submonoid.powers a.1) M)
    rintro ⟨a, ⟨i, rfl⟩⟩
    exact hAway i

-- Proof sketch: localize a flat `R`-module `M` at each prime of `A` for one implication; for the
-- converse, descend flatness from all prime localizations lying over `R`.
/-- Lemma 10.39.18 (4): for an `R`-algebra `A` and an `A`-module `M`, `M` is flat over `R` if and
only if for every prime ideal `q` of `A`, the localization `M_q` is flat over
`R_{q ∩ R}`. -/
theorem flat_iff_flat_localizedModule_atPrime_over_under
    : Module.Flat R M ↔
        ∀ q : PrimeSpectrum A,
          Module.Flat (Localization.AtPrime (q.asIdeal.under R))
            (LocalizedModule.AtPrime q.asIdeal M) := by
  constructor
  · intro hM q
    -- Relative prime local flatness is localization-preservation plus the localized-ring criterion.
    exact flat_localizedModule_atPrime_over_under_of_flat (R := R) (A := A) hM q
  · intro hPrime
    -- The prime-local hypotheses in particular give the maximal-local ones.
    exact flat_of_flat_localizedModule_atMaximal_over_under (R := R) (A := A)
      (M := M) fun m ↦ by
        simpa using hPrime m.toPrimeSpectrum

-- Proof sketch: the forward implication follows by localization at maximal ideals of `A`; the
-- converse is obtained from the prime-local criterion by restricting to maximal ideals.
/-- Lemma 10.39.18 (5): for an `R`-algebra `A` and an `A`-module `M`, `M` is flat over `R` if and
only if for every maximal ideal `m` of `A`, the localization `Mₘ` is flat over
`R_{m ∩ R}`. -/
theorem flat_iff_flat_localizedModule_atMaximal_over_under
    : Module.Flat R M ↔
        ∀ m : MaximalSpectrum A,
          Module.Flat (Localization.AtPrime (m.asIdeal.under R))
            (LocalizedModule.AtPrime m.asIdeal M) := by
  constructor
  · intro hM m
    -- The maximal-local statement is the prime-local statement specialized to a maximal ideal.
    simpa using
      flat_localizedModule_atPrime_over_under_of_flat (R := R) (A := A) hM m.toPrimeSpectrum
  · intro hMax
    -- This is exactly the maximal-local descent helper proved above.
    exact flat_of_flat_localizedModule_atMaximal_over_under (R := R) (A := A) (M := M) hMax

end

end RelativeLocalizationFlatness

/-! ### Lemma_10_39_19 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

/- Domain triage:
* primary domain: going down for commutative algebras and prime ideals lying over one another;
* sampled owner declarations:
  `Algebra.HasGoingDown`,
  `Algebra.HasGoingDown.of_flat`,
  `Ideal.exists_ideal_lt_liesOver_of_lt`,
  and the chapter-level owner recall in `Definition_10_41_1`;
* layer: `core/canonical` for the owner instance, with the source-shaped strict prime-lifting
  statement as derived `bridge/view` API.

Primitive-vs-derived split:
* primitive data: none; the source content is carried by the owner predicate
  `Algebra.HasGoingDown R S` under the ambient flatness hypothesis;
* derived API: the existence of a strict prime below a chosen `q'` lying over `p'`.
-/
/- Lemma 10.39.19: flat algebras satisfy the canonical going-down property
`Algebra.HasGoingDown R S`. This owner instance is exactly `Algebra.HasGoingDown.of_flat`. -/
recall Algebra.HasGoingDown.of_flat

/- Companion recall: after instantiating the owner theorem above, the textbook strict
prime-ideal conclusion is the canonical theorem `Ideal.exists_ideal_lt_liesOver_of_lt`. -/
recall Ideal.exists_ideal_lt_liesOver_of_lt

end

/-! ### Lemma_10_39_20 (from Chap10) -/
open CategoryTheory Limits
open CategoryTheory.Under
open CommRingCat
open CommRingCat.Hom

universe u v

/- Domain-style sampling for Lemma 10.39.20:
- primary domain: filtered colimits of commutative `R`-algebras in `Under (CommRingCat.of R)`;
- sampled owner declarations:
  `RingHom.FaithfullyFlat`,
  `CategoryTheory.MorphismProperty.IsStableUnderFilteredColimits`,
  `PrimeSpectrum.comap_surjective_of_faithfullyFlat`,
  `flat_of_isColimit_filtered_system`;
- best owner abstraction: filtered-colimit stability of the morphism property
  `fun f : A ⟶ B ↦ (hom f).FaithfullyFlat`, with the source-facing `Under` theorem below as a
  wrapper around that owner statement;
- primitive data: a filtered diagram `F`, a colimit cocone `c`, and the stagewise owner property
  `(hom (F.obj j).hom).FaithfullyFlat`;
- derived API: the source-facing cocone-point and chosen-colimit faithful-flatness conclusions.

Source/core/bridge triage:
- `source-facing`: faithful flatness of the structural map of a filtered colimit `R`-algebra;
- `core/canonical`: `RingHom.FaithfullyFlat` organized as a morphism property stable under filtered
  colimits;
- `bridge/view`: the `Under (CommRingCat.of R)` presentation, whose underlying ring diagram is the
  target of the owner stability statement.
-/

section

variable {R : Type u} [CommRing R]
variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ Under (CommRingCat.of R))

namespace RingHom.FaithfullyFlat

-- Proof sketch: use `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`. For flatness, forget
-- the diagram to `R`-modules and apply Lemma `10.39.3` to the underlying filtered colimit. For
-- surjectivity on prime spectra, pick any stage and lift a prime of `R` there via
-- `PrimeSpectrum.comap_surjective_of_faithfullyFlat`; then compose with the cocone map and rewrite
-- with `PrimeSpectrum.comap_comp_apply` and `Under.w`.
/-- Faithful flatness is stable under filtered colimits of commutative-ring morphisms. -/
instance isStableUnderFilteredColimits :
    CategoryTheory.MorphismProperty.IsStableUnderFilteredColimits
      (fun {A B : CommRingCat} (f : A ⟶ B) ↦ (hom f).FaithfullyFlat) := by
  -- TODO: package the fixed-base theorem below into the general morphism-property statement by
  -- base-changing an arbitrary filtered natural transformation along the source colimit cocone.
  sorry

end RingHom.FaithfullyFlat

/-- Helper for Lemma 10.39.20: any colimit cocone of a filtered diagram of nontrivial
commutative rings has a nontrivial cocone point. -/
theorem nontrivial_of_isColimit_filtered_system
    (G : J ⥤ CommRingCat.{max u v}) (c : Cocone G) (hc : IsColimit c)
    [∀ j, Nontrivial (G.obj j)] :
    Nontrivial ↑c.pt := by
  -- Proof comment: transport to the canonical filtered-colimit cocone, where nontriviality is
  -- already available from the earlier filtered-colimit theorem.
  let e := hc.coconePointUniqueUpToIso (CommRingCat.FilteredColimits.colimitCoconeIsColimit G)
  letI : Nontrivial ((CommRingCat.FilteredColimits.colimitCocone G).pt) :=
    filtered_colimit_nontrivial G
  obtain ⟨x, y, hxy⟩ :=
    Nontrivial.exists_pair_ne (α := (CommRingCat.FilteredColimits.colimitCocone G).pt)
  exact ⟨e.symm.commRingCatIsoToRingEquiv x, e.symm.commRingCatIsoToRingEquiv y, fun h ↦
    hxy (e.symm.commRingCatIsoToRingEquiv.injective h)⟩

/-- Helper for Lemma 10.39.20: after quotienting by a maximal ideal, each faithfully flat stage
has a nontrivial closed fiber. -/
theorem stage_pushout_nontrivial_of_faithfully_flat
    {j : J} (hF : ∀ j, (hom (F.obj j).hom).FaithfullyFlat)
    (m : Ideal R) [m.IsMaximal] :
    Nontrivial (((Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk m))).obj (F.obj j)).right) := by
  letI : Algebra R (F.obj j).right := (F.obj j).hom.hom.toAlgebra
  letI : Module R (F.obj j).right := (F.obj j).hom.hom.toAlgebra.toModule
  letI : Module.FaithfullyFlat R (F.obj j).right := by
    exact
      (RingHom.faithfullyFlat_algebraMap_iff
        (R := R) (S := (F.obj j).right)).mp <| by
          simpa [RingHom.algebraMap_toAlgebra] using hF j
  have hm_ne_top : m ≠ ⊤ := (inferInstance : m.IsMaximal).ne_top
  letI : Nontrivial (R ⧸ m) := by
    exact (Ideal.Quotient.nontrivial_iff).2 hm_ne_top
  letI : Nontrivial (TensorProduct R (R ⧸ m) ((F.obj j).right)) := by
    exact
      (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_left
        (R := R) (M := R ⧸ m) (N := (F.obj j).right)).2 inferInstance
  let e :=
    CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of (R ⧸ m)) (F.obj j)
  -- Proof comment: the pushout-model fiber ring is canonically the tensor-product fiber ring.
  obtain ⟨x, y, hxy⟩ :=
    Nontrivial.exists_pair_ne (α := TensorProduct R (R ⧸ m) ((F.obj j).right))
  have hinj : Function.Injective e.hom.right :=
    (ConcreteCategory.bijective_of_isIso e.hom.right).injective
  exact ⟨e.hom.right x, e.hom.right y, fun h ↦ hxy (hinj h)⟩

/-- Helper for Lemma 10.39.20: forgetting a filtered diagram of commutative `R`-algebras to
`R`-modules sends stagewise flatness to flatness of the colimit algebra. -/
theorem flat_of_isColimit_filtered_system_under
    (c : Cocone F) (hc : IsColimit c) (hF : ∀ j, (hom (F.obj j).hom).Flat) :
    (hom c.pt.hom).Flat := by
  -- Route correction: the remaining source-faithful work is to package the explicit underlying
  -- `ModuleCat R` diagram of `F`, prove its cocone is colimiting by reflecting through
  -- `forget (ModuleCat R)` and comparing with the forgotten `CommRingCat` colimit cocone, and
  -- then apply Lemma `10.39.3` to that module diagram.
  -- TODO: build the `ModuleCat` diagram with universe-stable forgetful comparison to the ring
  -- cocone, then invoke `flat_of_isColimit_filtered_system`.
  sorry

/-- Helper for Lemma 10.39.20: after quotienting by a maximal ideal, the pushed-out colimit
ring stays nontrivial because filtered colimits preserve the inequality `1 ≠ 0`. -/
theorem pushout_colimit_nontrivial_of_filtered_faithfully_flat_system
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, (hom (F.obj j).hom).FaithfullyFlat)
    (m : Ideal R) [m.IsMaximal] :
    Nontrivial (((Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk m))).obj c.pt).right) := by
  -- Route correction: the remaining structural step is to package the pushed-out diagram in a
  -- universe-stable `CommRingCat` universe so that `Under.pushout` and
  -- `nontrivial_of_isColimit_filtered_system` agree definitionally on the same codomain category.
  -- TODO: compare the literal pushed-out diagram with the rebundled `CommRingCat` diagram used by
  -- `nontrivial_of_isColimit_filtered_system`, then apply stagewise nontriviality.
  sorry

/-- Helper for Lemma 10.39.20: a nontrivial pushed-out colimit over `R ⧸ m` yields a prime of the
colimit ring whose contraction back to `R` is the maximal ideal `m`. -/
theorem pushout_colimit_closed_point_lift
    (c : Cocone F) (m : Ideal R) [m.IsMaximal]
    [Nontrivial (((Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk m))).obj c.pt).right)] :
    (⟨m, inferInstance⟩ : PrimeSpectrum R) ∈
      Set.range (PrimeSpectrum.comap (hom c.pt.hom)) := by
  classical
  obtain ⟨y'⟩ := PrimeSpectrum.nonempty_iff_nontrivial.mpr
    (show Nontrivial (((Under.pushout (CommRingCat.ofHom (Ideal.Quotient.mk m))).obj c.pt).right)
      from inferInstance)
  let y : PrimeSpectrum c.pt.right :=
    PrimeSpectrum.comap
      (pushout.inl c.pt.hom (CommRingCat.ofHom (Ideal.Quotient.mk m))).hom y'
  refine ⟨y, ?_⟩
  -- Proof comment: contract first along the pushout leg into `c.pt.right`, then rewrite the
  -- composite through the quotient square and use maximality to identify the contraction.
  change PrimeSpectrum.comap
      ((pushout.inl c.pt.hom (CommRingCat.ofHom (Ideal.Quotient.mk m))).hom.comp
        (hom c.pt.hom)) y' = _
  rw [show
      (pushout.inl c.pt.hom (CommRingCat.ofHom (Ideal.Quotient.mk m))).hom.comp (hom c.pt.hom) =
        (pushout.inr c.pt.hom (CommRingCat.ofHom (Ideal.Quotient.mk m))).hom.comp
          (Ideal.Quotient.mk m) by
        simpa using congrArg CommRingCat.Hom.hom
          (pushout.condition (f := c.pt.hom)
            (g := CommRingCat.ofHom (Ideal.Quotient.mk m)))]
  change PrimeSpectrum.comap (Ideal.Quotient.mk m)
      (PrimeSpectrum.comap
        (pushout.inr c.pt.hom (CommRingCat.ofHom (Ideal.Quotient.mk m))).hom y') = _
  apply PrimeSpectrum.ext
  -- Proof comment: every contraction from the quotient ring contains the kernel of the quotient
  -- map, which is exactly `m`.
  have hle :
      m ≤ (PrimeSpectrum.comap (Ideal.Quotient.mk m)
        (PrimeSpectrum.comap
          (pushout.inr c.pt.hom (CommRingCat.ofHom (Ideal.Quotient.mk m))).hom y')).asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal, Ideal.mk_ker] using
      (Ideal.ker_le_comap (Ideal.Quotient.mk m))
  exact
    (Ideal.IsMaximal.eq_of_le
      (I := m)
      (J := (PrimeSpectrum.comap (Ideal.Quotient.mk m)
        (PrimeSpectrum.comap
          (pushout.inr c.pt.hom (CommRingCat.ofHom (Ideal.Quotient.mk m))).hom y')).asIdeal)
      (show m.IsMaximal from inferInstance)
      (PrimeSpectrum.comap (Ideal.Quotient.mk m)
        (PrimeSpectrum.comap
          (pushout.inr c.pt.hom (CommRingCat.ofHom (Ideal.Quotient.mk m))).hom y')).2.ne_top
      hle).symm

/-- Helper for Lemma 10.39.20: every closed point of `Spec R` lifts to the colimit ring of a
filtered faithfully flat system. -/
theorem closed_points_subset_range_of_filtered_faithfully_flat_system
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, (hom (F.obj j).hom).FaithfullyFlat) :
    closedPoints (PrimeSpectrum R) ⊆
      Set.range (PrimeSpectrum.comap (hom c.pt.hom)) := by
  intro x hx
  have hxmax : x.asIdeal.IsMaximal := by
    -- Proof comment: a closed point of the prime spectrum is exactly a maximal ideal.
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp (by simpa [closedPoints] using hx)
  letI : x.asIdeal.IsMaximal := hxmax
  letI :
      Nontrivial (((Under.pushout
        (CommRingCat.ofHom (Ideal.Quotient.mk x.asIdeal))).obj c.pt).right) :=
    pushout_colimit_nontrivial_of_filtered_faithfully_flat_system
      (F := F) c hc hF x.asIdeal
  -- Proof comment: the nontrivial quotient fiber over the closed point supplies a prime of the
  -- pushed-out colimit, and its contraction gives back the original closed point.
  simpa using pushout_colimit_closed_point_lift (F := F) c x.asIdeal

-- Proof sketch: use Lemma 10.39.3 for the flatness part after forgetting the `R`-algebra diagram
-- to `R`-modules, then apply Lemma 10.39.16 to the closed-point lifting statement above.
/-- Lemma 10.39.20: if `c` is a colimit cocone of a filtered diagram of faithfully flat
commutative `R`-algebras, then its cocone point is faithfully flat over `R`. This is the
canonical filtered-diagram formulation in `Under (CommRingCat.of R)`. -/
theorem faithfullyFlat_of_isColimit_filtered_system
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, (hom (F.obj j).hom).FaithfullyFlat) :
    (hom c.pt.hom).FaithfullyFlat := by
  have hflat : (hom c.pt.hom).Flat :=
    flat_of_isColimit_filtered_system_under (F := F) c hc (fun j ↦ (hF j).1)
  -- Proof comment: Lemma `10.39.16` reduces faithful flatness to flatness plus the closed-point
  -- lifting statement proved above.
  rw [faithfullyFlat_iff_closedPoints_subset_range _ hflat]
  exact closed_points_subset_range_of_filtered_faithfully_flat_system F c hc hF

/-- Companion form of Lemma 10.39.20 for the chosen colimit object `colimit F`. -/
theorem faithfullyFlat_colimit_of_filtered_system
    [HasColimit F]
    (hF : ∀ j, (hom (F.obj j).hom).FaithfullyFlat) :
    (hom (colimit F).hom).FaithfullyFlat := by
  simpa using faithfullyFlat_of_isColimit_filtered_system F (colimit.cocone F)
    (colimit.isColimit F) hF

end
