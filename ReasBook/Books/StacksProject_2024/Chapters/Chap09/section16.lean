import Mathlib
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_9_16_1 (from Chap09) -/
noncomputable section

open Polynomial

universe u v

variable {F : Type u} [Field F]
variable (P : F[X])

/- Lemma 9.16.1: the canonical field `P.SplittingField` is a splitting field of `P` over `F`;
this is exactly the canonical instance `Polynomial.IsSplittingField.splittingField`. -/
recall Polynomial.IsSplittingField.splittingField

variable {E : Type v} [Field E] [Algebra F E]

/- Companion recall for Lemma 9.16.1: a splitting field is normal over the base field, via the
canonical theorem `Normal.of_isSplittingField`. -/
recall Normal.of_isSplittingField

/- Companion recall for Lemma 9.16.1: any splitting field of `P` is `F`-algebra isomorphic to the
canonical splitting field `P.SplittingField`; this is exactly
`Polynomial.IsSplittingField.algEquiv`. -/
recall Polynomial.IsSplittingField.algEquiv

/-! ### Definition_9_16_2 (from Chap09) -/
noncomputable section

universe u

variable {F : Type u} [Field F]

/- Definition 9.16.2: for a nonconstant polynomial `P ∈ F[X]`, the field extension
`P.SplittingField/F` constructed in Lemma 9.16.1 is called the splitting field of `P` over `F`.
In mathlib this is the canonical owner `Polynomial.SplittingField P`; the source's nonconstancy
hypothesis is not part of the definition itself. -/
recall Polynomial.SplittingField (P : Polynomial F) : Type u

/-! ### Lemma_9_16_3 (from Chap09) -/
noncomputable section

open IntermediateField

universe u

variable {F E : Type u} [Field F] [Field E] [Algebra F E]

variable [Algebra.IsAlgebraic F E]

/- Lemma 9.16.3: the canonical field `normalClosure F E (AlgebraicClosure E)` is the normal
closure of `E/F` inside `AlgebraicClosure E`; this is exactly the mathlib theorem
`isNormalClosure_normalClosure`. -/
recall isNormalClosure_normalClosure

/- Companion recall: in `AlgebraicClosure E`, the field
`normalClosure F E (AlgebraicClosure E)` is normal over `F`. -/
recall normalClosure.normal

/- Companion recall: the minimality statement for the normal closure inside `AlgebraicClosure E`
is the canonical theorem `normalClosure_le_iff_of_normal`; applied to the
distinguished copy `(⊥ : IntermediateField E (AlgebraicClosure E)).restrictScalars F`, it says
that a normal intermediate field contains the normal closure exactly when it contains `E`. -/
recall normalClosure_le_iff_of_normal

/- Companion recall: when `E/F` is finite, its normal closure in `AlgebraicClosure E` is finite
over `F`. -/
section

variable [FiniteDimensional F E]

recall normalClosure.is_finiteDimensional

end

/-! ### Definition_9_16_4 (from Chap09) -/
noncomputable section

open IntermediateField

universe u

variable {F E : Type u} [Field F] [Field E] [Algebra F E]

/- Domain-style sampling for Definition 9.16.4:
- primary domain: normal closures of field extensions;
- sampled canonical declarations:
  `IntermediateField.normalClosure`,
  `normalClosure_def`,
  `isNormalClosure_normalClosure`,
  `normalClosure.is_finiteDimensional`;
- best owner abstraction: `IntermediateField.normalClosure`, specialized here to the ambient field
  `AlgebraicClosure E`.

Source/core/bridge triage:
- `source-facing`: the textbook name "the normal closure of `E` over `F`";
- `core/canonical`: the intermediate field `normalClosure F E (AlgebraicClosure E)`;
- `bridge/view`: Lemma 9.16.3 and its companion recalls, which provide the normal-closure
  specification, normality, and finiteness properties of this canonical field.

Primitive data are only the fields `F`, `E`, the `F`-algebra structure on `E`, and the ambient
field `AlgebraicClosure E`. The `IsNormalClosure` witness and finiteness/normality statements are
derived API. In particular, the source's finite-extension hypothesis is not primitive data of the
owner itself, so this file should remain a direct recall of the owner specialization rather than
introducing any local wrapper or alias.
-/

/- Definition 9.16.4: for a finite field extension `E/F`, the field
`normalClosure F E (AlgebraicClosure E)` constructed in Lemma 9.16.3 is called the normal
closure of `E` over `F`. -/
#check normalClosure F E (AlgebraicClosure E)

/- Companion recall: `IntermediateField.normalClosure` is the owner-level relative normal closure
for any field extension `E/F`; Definition 9.16.4 is its specialization to `AlgebraicClosure E`. -/
recall IntermediateField.normalClosure

/-! ### Lemma_9_16_5 (from Chap09) -/
open IntermediateField

universe u v

section

variable {K : Type u} {L : Type v}
variable [Field K] [Field L] [Algebra K L] [Normal K L]

/-- Every finite intermediate field of a normal extension lies in a finite normal
intermediate field. -/
-- Proof sketch: take the normal closure of `M` inside `L`; it contains `M`, is finite over `K`,
-- with normality over `K`.
theorem exists_finite_normal_intermediate_field
    (M : IntermediateField K L) [FiniteDimensional K M] :
    ∃ (N : IntermediateField K L) (_ : FiniteDimensional K N), M ≤ N ∧ Normal K N := by
  -- The canonical normal closure already has the required containment and finiteness.
  refine ⟨IntermediateField.normalClosure K M L,
    normalClosure.is_finiteDimensional K M L, ?_, normalClosure.normal K M L⟩
  exact IntermediateField.le_normalClosure M

/-- Helper for Lemma 9.16.5: a finite set of elements of `L` is contained in one finite normal
`K`-intermediate field. -/
lemma exists_finite_normal_container_of_finite_set
    (s : Set L) (hs : s.Finite) :
    ∃ (E : IntermediateField K L) (_ : FiniteDimensional K E), (∀ x ∈ s, x ∈ E) ∧ Normal K E := by
  classical
  let E₀ : IntermediateField K L := IntermediateField.adjoin K s
  have hE₀fin : FiniteDimensional K E₀ := by
    letI : Fintype s := hs.fintype
    simpa [E₀] using
      (IntermediateField.finiteDimensional_adjoin (K := K) (L := L) (S := s)
        (fun x hx ↦ IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic x)))
  letI : FiniteDimensional K E₀ := hE₀fin
  refine ⟨IntermediateField.normalClosure K E₀ L,
    normalClosure.is_finiteDimensional K E₀ L, ?_, normalClosure.normal K E₀ L⟩
  intro x hx
  exact (IntermediateField.le_normalClosure E₀) (IntermediateField.subset_adjoin K s hx)

omit [Normal K L] in
/-- Helper for Lemma 9.16.5: restricting scalars from `M⟮t⟯` to `K` gives the compositum of `M`
with the `K`-field generated by `t`. -/
lemma adjoin_generators_over_intermediate_restrictScalars_eq_sup
    (M : IntermediateField K L) (t : Set L) (E : IntermediateField K L)
    (hE : IntermediateField.adjoin K t = E) :
    (IntermediateField.adjoin M t).restrictScalars K = M ⊔ E := by
  -- Restricting scalars turns adjoining over `M` into adjoining over `K` together with `M`.
  rw [IntermediateField.restrictScalars_adjoin_eq_sup, hE]

/-- Lemma 9.16.5: if `M/K` is normal with `M'/M` finite inside `L`, then `M'` is contained
in an intermediate field `N/M` that is finite normal over `K`. -/
-- Proof sketch: first place the finitely generated `M`-subextension `M'` inside a finite
-- intermediate field over `K`; then take its normal closure inside `L`; view the result as an
-- intermediate field over `M`.
theorem exists_finite_extension_normal_over_base
    (M : IntermediateField K L) [Normal K M]
    (M' : IntermediateField M L) [FiniteDimensional M M'] :
    ∃ (N : IntermediateField M L) (_ : FiniteDimensional M N), M' ≤ N ∧ Normal K N := by
  classical
  -- A finite extension is finitely generated, so fix generators for `M' / M`.
  obtain ⟨s, hsfinite, hsadjoin⟩ :=
    IntermediateField.fg_def.mp
      ((IntermediateField.essFiniteType_iff (F := M) (E := L) (K := M')).mp inferInstance)
  -- Enclose those generators in one finite normal `K`-intermediate field.
  obtain ⟨E, hEfin, hsE, hEnormal⟩ :=
    exists_finite_normal_container_of_finite_set (K := K) (L := L) s hsfinite
  -- Choose finite `K`-generators for that enclosing field.
  obtain ⟨t, htfinite, htadjoin⟩ :=
    IntermediateField.fg_def.mp
      ((IntermediateField.essFiniteType_iff (F := K) (E := L) (K := E)).mp inferInstance)
  let N : IntermediateField M L := IntermediateField.adjoin M t
  have hNfinite : FiniteDimensional M N := by
    -- Adjoining finitely many algebraic elements over a field stays finite dimensional.
    letI : Fintype t := htfinite.fintype
    exact IntermediateField.finiteDimensional_adjoin
      (fun x _ ↦ IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic x))
  refine ⟨N, hNfinite, ?_, ?_⟩
  · -- It suffices to show that the chosen `M`-generators already lie in `N`.
    rw [← hsadjoin]
    refine IntermediateField.adjoin_le_iff.mpr ?_
    intro x hx
    have hxE : x ∈ E := hsE x hx
    have hxRestrict : x ∈ N.restrictScalars K := by
      rw [adjoin_generators_over_intermediate_restrictScalars_eq_sup
        (K := K) (L := L) M t E htadjoin]
      exact (show E ≤ M ⊔ E from le_sup_right) hxE
    simpa using hxRestrict
  · -- The restricted `K`-field is `M ⊔ E`, hence normal over `K`.
    have hNrestrict : N.restrictScalars K = M ⊔ E := by
      exact adjoin_generators_over_intermediate_restrictScalars_eq_sup
        (K := K) (L := L) M t E htadjoin
    have hnormal_restrict : Normal K (N.restrictScalars K) := by
      rw [hNrestrict]
      letI : Normal K E := hEnormal
      infer_instance
    exact (IntermediateField.restrictScalars_normal (F := K) (K := M) (E := N)).mp
      hnormal_restrict

end

/-! ### Lemma_9_16_6 (from Chap09) -/
open scoped TensorProduct
open scoped FieldExtensionDegree
open IntermediateField

noncomputable section

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/- Domain-style sampling for Lemma 9.16.6:
- primary domain: finite extensions, their `K`-embeddings into an algebraic closure, the canonical
  normal closure, and the indexed tensor product of the resulting conjugate copies;
- sampled owner declarations:
  `Field.Emb`,
  `Field.finSepDegree`,
  `IntermediateField.normalClosure`,
  `normalClosure.algHomEquiv`,
  `PiTensorProduct.liftAlgHom`,
  `AlgHom.fintype`,
  `Field.finSepDegree_eq_of_isAlgClosed`;
- best owner abstraction: the canonical owner is the embedding-indexed tensor product map obtained
  by lifting the product of the canonical factors `L →ₐ[K] normalClosure K L (AlgebraicClosure L)`;
- primitive data vs. derived API:
  primitive data are the canonical owner type `Field.Emb K L` and the owner field
  `normalClosure K L (AlgebraicClosure L)`, together with the finite embedding index needed to
  form the indexed tensor product and finite product;
  the tensor-product comparison map and its `Fin (Cardinal.toNat [L : K]_s)` reindexing are
  derived from these.

Source/core/bridge triage:
- `source-facing`: the textbook finite-copy existence statement with
  `Fin (Cardinal.toNat [L : K]_s)` tensor factors;
- `core/canonical`: the embedding-indexed map
  `(⨂[K] σ : Field.Emb K L, L) →ₐ[K] normalClosure K L (AlgebraicClosure L)`;
- `bridge/view`: reindexing the embedding-indexed tensor product by an arbitrary finite type, and
  in particular by `Fin (Cardinal.toNat [L : K]_s)`, where finite dimensionality is used only to
  supply the canonical finite embedding index and the finite bridge from `Field.sepDegree K L`
  to a natural number.

The file therefore takes the embedding-indexed owner map as the public canonical declaration,
proves its pure-tensor formula from the primitive finite-index data, and derives the textbook
`Fin (Cardinal.toNat [L : K]_s)` existence statement only in the finite-dimensional bridge layer,
using `Field.finSepDegree` only internally as a numerical bridge. -/

local notation "N" => IntermediateField.normalClosure K L (AlgebraicClosure L)
local notation "ιN" => IntermediateField.val N

section EmbeddingIndexed

variable [Fintype (Field.Emb K L)]

/-- The canonical comparison map from the embedding-indexed tensor product of the conjugate copies
of `L` to the normal closure of `L/K` in `AlgebraicClosure L`. -/
noncomputable def piTensorProductToNormalClosure : (⨂[K] _ : Field.Emb K L, L) →ₐ[K] N :=
  let e : (L →ₐ[K] N) ≃ Field.Emb K L := normalClosure.algHomEquiv K L (AlgebraicClosure L)
  PiTensorProduct.liftAlgHom
    ((MultilinearMap.mkPiAlgebra K (Field.Emb K L) N).compLinearMap
      fun σ ↦ (e.symm σ).toLinearMap)
    (by simp [MultilinearMap.compLinearMap_apply])
    (by
      intro x y
      simp [MultilinearMap.compLinearMap_apply, Finset.prod_mul_distrib])

/-- On a pure tensor, `piTensorProductToNormalClosure` multiplies the images of the chosen tensor
entries under all `K`-embeddings of `L` into `AlgebraicClosure L`. -/
@[simp]
theorem piTensorProductToNormalClosure_tprod (x : Field.Emb K L → L) :
    ((piTensorProductToNormalClosure K L) (PiTensorProduct.tprod K x) : AlgebraicClosure L) =
      ∏ σ : Field.Emb K L, σ (x σ) := by
  classical
  let e : (L →ₐ[K] N) ≃ Field.Emb K L := normalClosure.algHomEquiv K L (AlgebraicClosure L)
  change ιN ((piTensorProductToNormalClosure K L) (PiTensorProduct.tprod K x)) = _
  unfold piTensorProductToNormalClosure
  rw [PiTensorProduct.liftAlgHom, AlgHom.ofLinearMap_apply, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, map_prod]
  refine Finset.prod_congr rfl fun σ _ ↦ ?_
  exact congrArg (fun f : Field.Emb K L ↦ f (x σ)) (e.apply_symm_apply σ)

end EmbeddingIndexed

/-- A reindexed tensor-product map with the expected pure-tensor formula is automatically
surjective onto the normal closure. -/
private theorem surjective_of_tprod_formula {ι : Type*} [Fintype ι]
    (e : ι ≃ Field.Emb K L) (φ : (⨂[K] _ : ι, L) →ₐ[K] N)
    (hφ : ∀ x : ι → L,
      (φ (PiTensorProduct.tprod K x) : AlgebraicClosure L) = ∏ i, e i (x i)) :
    Function.Surjective φ := by
  classical
  let _ : Finite (Field.Emb K L) := Finite.of_equiv ι e
  let _ : Fintype (Field.Emb K L) := Fintype.ofFinite (Field.Emb K L)
  have hKL : Algebra.IsAlgebraic K L := by
    by_contra hKL
    letI : Algebra.Transcendental K L :=
      (Algebra.transcendental_iff_not_isAlgebraic).2 hKL
    letI : Infinite (Field.Emb K L) := Field.infinite_emb_of_transcendental K L
    exact Finite.false (Finite.of_fintype (Field.Emb K L))
  letI : Algebra.IsAlgebraic K L := hKL
  letI : Algebra.IsAlgebraic K (AlgebraicClosure L) :=
    Algebra.IsAlgebraic.trans K L (AlgebraicClosure L)
  letI : Algebra.IsAlgebraic K N := Algebra.IsAlgebraic.of_injective ιN Subtype.val_injective
  let eSub : Subalgebra K N ≃o IntermediateField K N := subalgebraEquivIntermediateField
  let R : IntermediateField K N := eSub φ.range
  have hRsub : R.toSubalgebra = φ.range := by
    ext x
    change x ∈ eSub φ.range ↔ x ∈ φ.range
    simp [eSub]
  have htop : R = ⊤ := by
    apply map_injective ιN
    refine le_antisymm ?_ ?_
    · exact map_mono ιN le_top
    · rw [← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]
      refine normalClosure_le_iff.2 fun σ ↦ ?_
      intro y hy
      rcases (AlgHom.mem_fieldRange).1 hy with ⟨x, rfl⟩
      change σ x ∈ (R.map ιN).toSubalgebra
      rw [toSubalgebra_map, hRsub, Subalgebra.mem_map]
      refine ⟨φ (PiTensorProduct.tprod K (Pi.mulSingle (e.symm σ) x)), AlgHom.mem_range_self φ _, ?_⟩
      change (φ (PiTensorProduct.tprod K (Pi.mulSingle (e.symm σ) x)) : AlgebraicClosure L) = σ x
      have hmulSingle :
          (fun i ↦ e i ((Pi.mulSingle (e.symm σ) x : ι → L) i)) =
            (Pi.mulSingle (e.symm σ) (σ x) : ι → AlgebraicClosure L) := by
        ext i
        by_cases h : i = e.symm σ
        · subst h
          simp
        · simp [Pi.mulSingle, h]
      calc
        (φ (PiTensorProduct.tprod K (Pi.mulSingle (e.symm σ) x)) : AlgebraicClosure L) =
            ∏ i, e i ((Pi.mulSingle (e.symm σ) x : ι → L) i) := hφ _
        _ = ∏ i, (Pi.mulSingle (e.symm σ) (σ x) : ι → AlgebraicClosure L) i := by
          rw [hmulSingle]
        _ = σ x := Fintype.prod_pi_mulSingle' (e.symm σ) (σ x)
  have hrange : φ.range = ⊤ := by
    rw [← hRsub, htop]
    rfl
  exact (AlgHom.range_eq_top φ).mp hrange

section EmbeddingIndexed

variable [Fintype (Field.Emb K L)]

/-- The embedding-indexed comparison map onto the normal closure is surjective. -/
theorem surjective_piTensorProductToNormalClosure :
    Function.Surjective (piTensorProductToNormalClosure K L) := by
  exact surjective_of_tprod_formula K L (Equiv.refl (Field.Emb K L))
    (piTensorProductToNormalClosure K L)
    (piTensorProductToNormalClosure_tprod K L)

end EmbeddingIndexed

section FiniteDegreeBridge

variable [FiniteDimensional K L]

/-- The finite embedding count is the natural-number realization of the separable degree
`[L : K]_s`. -/
private theorem natCard_emb_eq_toNat_sepDegree :
    Nat.card (Field.Emb K L) = Cardinal.toNat [L : K]_s := by
  calc
    Nat.card (Field.Emb K L) = Field.finSepDegree K L := by
      symm
      exact Field.finSepDegree_eq_of_isAlgClosed K L (AlgebraicClosure L)
    _ = Cardinal.toNat [L : K]_s := Field.finSepDegree_eq K L

/-- A chosen reindexing of `Fin (Cardinal.toNat [L : K]_s)` by the `K`-embeddings of `L` into
`AlgebraicClosure L`, obtained from the cardinality formula for the separable degree. -/
private noncomputable def sepDegreeEmbEquiv :
    Fin (Cardinal.toNat [L : K]_s) ≃ Field.Emb K L := by
  refine (Fintype.equivFinOfCardEq ?_).symm
  rw [Fintype.card_eq_nat_card]
  exact natCard_emb_eq_toNat_sepDegree K L

/-- Reindex the constant-family tensor product by an equivalence of finite index types. -/
private noncomputable def piTensorProductReindexAlgEquiv {ι : Type*} [Fintype ι]
    (e : ι ≃ Field.Emb K L) : (⨂[K] _ : ι, L) ≃ₐ[K] (⨂[K] _ : Field.Emb K L, L) :=
  AlgEquiv.ofLinearEquiv
    (PiTensorProduct.reindex K (fun _ : ι ↦ L) e)
    (by
      rw [PiTensorProduct.one_def, PiTensorProduct.one_def, PiTensorProduct.reindex_tprod]
      rfl)
    (by
      intro x y
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r f =>
          induction y using PiTensorProduct.induction_on with
          | smul_tprod s g =>
              simp [PiTensorProduct.tprod_mul_tprod, Pi.mul_def]
          | add y₁ y₂ hy₁ hy₂ =>
              rw [mul_add, map_add, map_add, hy₁, hy₂, mul_add]
      | add x₁ x₂ hx₁ hx₂ =>
          rw [add_mul, map_add, map_add, hx₁, hx₂, add_mul])

/-- Lemma 9.16.6: the finite tensor product of `Cardinal.toNat [L : K]_s` copies of `L` over `K`
surjects onto the normal closure of `L/K` inside `AlgebraicClosure L`. This is the source-facing
finite-degree reindexing corollary of `surjective_piTensorProductToNormalClosure`; the auxiliary
numerical API `Field.finSepDegree K L` is used only internally to identify `Cardinal.toNat [L : K]_s`
with the number of `K`-embeddings of `L` into `AlgebraicClosure L`. -/
theorem exists_surjective_piTensorProduct_to_normalClosure :
    ∃ φ : (⨂[K] _ : Fin (Cardinal.toNat [L : K]_s), L) →ₐ[K] N,
      Function.Surjective φ := by
  let φ : (⨂[K] _ : Fin (Cardinal.toNat [L : K]_s), L) →ₐ[K] N :=
    (piTensorProductToNormalClosure K L).comp
      (piTensorProductReindexAlgEquiv K L (sepDegreeEmbEquiv K L)).toAlgHom
  refine ⟨φ, ?_⟩
  exact (surjective_piTensorProductToNormalClosure K L).comp
    (piTensorProductReindexAlgEquiv K L (sepDegreeEmbEquiv K L)).surjective

end FiniteDegreeBridge
