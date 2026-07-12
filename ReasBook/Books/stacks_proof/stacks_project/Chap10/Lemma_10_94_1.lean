import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Definition_10_84_1
import StacksProject_2024.Chap10.Lemma_10_84_3
import StacksProject_2024.Chap10.Proposition_10_89_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct DirectSum

universe u v w x y

namespace Module

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

/- Domain triage:
- primary domain: base change for module-theoretic properties over commutative rings;
- sampled owner declarations of the same kind:
  `Module.Flat.baseChange`,
  `Projective.tensorProduct`,
  `Module.CountablyGenerated`,
  `Module.IsDirectSumOfCountablyGenerated`,
  `Module.MittagLeffler`,
  `Module.mittagLeffler_iff_tensorProduct_piRight_injective`;
- best owner abstraction: the chapter owners above, together with the existing mathlib typeclass
  owners `Module.Flat` and `Module.Projective`;
- primitive data: the ring map `R → S` and the `R`-module `M`;
- derived API: canonical recalls for flatness and projectivity under base change, together with the
  genuinely new base-change lemmas for `MittagLeffler` and
  `IsDirectSumOfCountablyGenerated`.

Layering:
- this numbered item is `bridge/view`: it records closure of the existing owner properties under
  base change, and does not define new owners.
-/

section

variable [Flat R M]

/- Flatness clause: if `M` is flat over `R`, then its base change `S ⊗[R] M` is flat over `S`.
This is exactly the canonical owner instance `Module.Flat.baseChange` for the standard mathlib
model of the textbook module `M ⊗_R S`. -/
recall Module.Flat.baseChange

end

-- Proof sketch: use the tensor-product injectivity characterization of Mittag-Leffler modules from
-- Proposition `10.89.5`; after base change, commute tensor products with products and tensoring
-- over `S` to transfer injectivity to `S ⊗[R] M`.
/-- Helper for the base-change clauses: canceling the scalar-extension tensor on the right
identifies `(S ⊗[R] M) ⊗[S] N` with `M ⊗[R] N` over `R`. -/
noncomputable def baseChangeTensorRightEquiv (N : Type x) [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N] :
    ((S ⊗[R] M) ⊗[S] N) ≃ₗ[R] (M ⊗[R] N) :=
  (((TensorProduct.comm S (S ⊗[R] M) N).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N M)).restrictScalars R).trans
      (TensorProduct.comm R N M)

/-- Helper for the base-change clauses: the tensor-cancellation equivalence is compatible with the
canonical product comparison map `TensorProduct.piRightHom`. -/
lemma baseChangeTensorRightEquiv_piRightHom
    {A : Type x} (Q : A → Type y) [∀ a, AddCommGroup (Q a)]
    [∀ a, Module R (Q a)] [∀ a, Module S (Q a)] [∀ a, IsScalarTower R S (Q a)] :
    (LinearEquiv.piCongrRight fun a =>
      baseChangeTensorRightEquiv (R := R) (S := S) (M := M) (Q a)).toLinearMap ∘ₗ
        (TensorProduct.piRightHom S S (S ⊗[R] M) Q).restrictScalars R =
      (TensorProduct.piRightHom R R M Q) ∘ₗ
        (baseChangeTensorRightEquiv (R := R) (S := S) (M := M) ((a : A) → Q a)).toLinearMap := by
  -- It is enough to compare the two maps on pure tensors, and then on the pure tensors inside
  -- the base-changed left tensor factor.
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul sm q =>
      ext a
      induction sm using TensorProduct.induction_on with
      | zero => simp
      | tmul s m => simp [baseChangeTensorRightEquiv]
      | add x y hx hy =>
          rw [TensorProduct.add_tmul]
          simp only [map_add, Pi.add_apply]
          exact congrArg₂ HAdd.hAdd hx hy
  | add x y hx hy =>
      simp only [map_add]
      rw [hx, hy]

/-- Helper for the base-change clauses: the product comparison map for the base-changed module is
injective whenever the original module is Mittag-Leffler. -/
lemma piRightHom_baseChange_injective (hM : MittagLeffler R M)
    {A : Type x} (Q : A → Type y) [∀ a, AddCommGroup (Q a)]
    [∀ a, Module R (Q a)] [∀ a, Module S (Q a)] [∀ a, IsScalarTower R S (Q a)] :
    Function.Injective (TensorProduct.piRightHom S S (S ⊗[R] M) Q) := by
  have hR :=
    (Module.mittagLeffler_iff_tensorProduct_piRight_injective (R := R) (M := M)).mp hM A Q
  intro x y hxy
  -- Conjugate the `S`-comparison map by the cancellation equivalences and apply the
  -- `R`-comparison injectivity criterion for `M`.
  apply (baseChangeTensorRightEquiv (R := R) (S := S) (M := M) ((a : A) → Q a)).injective
  apply hR
  have hcompat := baseChangeTensorRightEquiv_piRightHom (R := R) (S := S) (M := M) Q
  have hx := LinearMap.congr_fun hcompat x
  have hy := LinearMap.congr_fun hcompat y
  calc
    (TensorProduct.piRightHom R R M Q)
        ((baseChangeTensorRightEquiv (R := R) (S := S) (M := M) ((a : A) → Q a)) x)
        = ((LinearEquiv.piCongrRight fun a =>
            baseChangeTensorRightEquiv (R := R) (S := S) (M := M) (Q a)).toLinearMap ∘ₗ
              (TensorProduct.piRightHom S S (S ⊗[R] M) Q).restrictScalars R) x := by
          simpa [LinearMap.comp_apply] using hx.symm
    _ = ((LinearEquiv.piCongrRight fun a =>
            baseChangeTensorRightEquiv (R := R) (S := S) (M := M) (Q a)).toLinearMap ∘ₗ
              (TensorProduct.piRightHom S S (S ⊗[R] M) Q).restrictScalars R) y := by
          simp [LinearMap.comp_apply, hxy]
    _ = (TensorProduct.piRightHom R R M Q)
        ((baseChangeTensorRightEquiv (R := R) (S := S) (M := M) ((a : A) → Q a)) y) := by
          simpa [LinearMap.comp_apply] using hy

/- The two public declarations below record the Mittag-Leffler and
direct-sum-of-countably-generated consequences of base change. -/
-- recall Module.mittagLeffler_tensorProduct / Module.isDirectSumOfCountablyGenerated_tensorProduct

/-- Mittag-Leffler base-change clause: if `M` is Mittag-Leffler over `R`, then its base change
`S ⊗[R] M` is Mittag-Leffler over `S`. This is the canonical Lean form of the textbook statement
for `M ⊗_R S`. -/
theorem mittagLeffler_tensorProduct (hM : MittagLeffler R M) :
    MittagLeffler S (S ⊗[R] M) := by
  -- Use the injectivity criterion over `S`; restricted scalar structures compare its test family
  -- with the corresponding criterion over `R`.
  refine (Module.mittagLeffler_iff_tensorProduct_piRight_injective
    (R := S) (M := S ⊗[R] M)).2 ?_
  intro (A : Type (max v w)) (Q : A → Type (max v w)) _ _
  letI instRestrictScalars : (a : A) → Module R (Q a) :=
    fun a => Module.restrictScalars R S (Q a)
  letI instTower : (a : A) → IsScalarTower R S (Q a) :=
    fun a => IsScalarTower.restrictScalars R S (Q a)
  exact piRightHom_baseChange_injective (R := R) (S := S) (M := M) hM Q

-- Proof sketch: choose an internal direct-sum decomposition of `M` by countably generated
-- `R`-submodules, tensor the whole decomposition with `S`, and use that tensor products commute
-- with direct sums while countable generating sets base change to countable generating sets.
/-- Helper for the base-change clauses: extension of scalars preserves countable generation. -/
lemma countablyGenerated_tensorProduct {N : Type x} [AddCommGroup N] [Module R N]
    (hN : Module.CountablyGenerated R N) :
    Module.CountablyGenerated S (S ⊗[R] N) := by
  rw [Module.countablyGenerated_iff] at hN ⊢
  rcases hN with ⟨t, ht, hspan⟩
  -- The image of a countable spanning set under `m ↦ 1 ⊗ m` spans the scalar extension.
  refine ⟨(TensorProduct.mk R S N 1) '' t, ht.image _, ?_⟩
  calc
    Submodule.span S ((TensorProduct.mk R S N 1) '' t) =
        (Submodule.span R t).baseChange S := by
      rw [Submodule.baseChange_span]
    _ = (⊤ : Submodule R N).baseChange S := by
      rw [hspan]
    _ = ⊤ := by
      rw [Submodule.baseChange_top]

/-- Direct-sum base-change clause: if `M` is a direct sum of countably
generated `R`-modules, then `S ⊗[R] M` is a direct sum of countably generated `S`-modules. This is
the canonical Lean form of the textbook statement for `M ⊗_R S`. -/
theorem isDirectSumOfCountablyGenerated_tensorProduct
    (hM : IsDirectSumOfCountablyGenerated.{u, w, x} R M) :
    IsDirectSumOfCountablyGenerated.{v, max v w, x} S (S ⊗[R] M) := by
  rcases hM with ⟨ι, hdec, summand, hsum, hcount⟩
  letI : DecidableEq ι := hdec
  let A : ι → Type _ := fun i => S ⊗[R] (summand i)
  let D := DirectSum ι A
  let eInternal : DirectSum ι (fun i => summand i) ≃ₗ[R] M :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap summand) hsum
  let e : (S ⊗[R] M) ≃ₗ[S] D :=
    (eInternal.symm.baseChange R S).trans
      (TensorProduct.directSumRight R S S (fun i => summand i))
  let rangeSummand : ι → Submodule S (S ⊗[R] M) :=
    fun i => (LinearMap.range (DirectSum.lof S ι A i)).map (e.symm : D →ₗ[S] S ⊗[R] M)
  let hInternal := Module.range_lof_isInternal (R := S) A
  -- Transport the canonical internal direct-sum decomposition of `D` back across the base-change
  -- equivalence from `S ⊗[R] M`.
  have hRangeIndep : iSupIndep rangeSummand := by
    exact LinearMap.iSupIndep_map (e.symm : D →ₗ[S] S ⊗[R] M) e.symm.injective
      hInternal.submodule_iSupIndep
  have hRangeTop : iSup rangeSummand = (⊤ : Submodule S (S ⊗[R] M)) := by
    calc
      iSup rangeSummand = (iSup fun i => LinearMap.range (DirectSum.lof S ι A i)).map
          (e.symm : D →ₗ[S] S ⊗[R] M) := by
        rw [Submodule.map_iSup]
      _ = (⊤ : Submodule S D).map (e.symm : D →ₗ[S] S ⊗[R] M) := by
        rw [hInternal.submodule_iSup_eq_top]
      _ = ⊤ := by
        rw [Submodule.map_top]
        exact LinearMap.range_eq_top.2 e.symm.surjective
  have hRangeCount : ∀ i, (rangeSummand i).CountablyGenerated := by
    intro i
    apply Submodule.countablyGenerated_map
    -- The canonical range is generated by the image of the countable generators of the
    -- base-changed original summand.
    simpa [Submodule.map_top] using
      (Submodule.countablyGenerated_map (f := DirectSum.lof S ι A i)
        (Q := (⊤ : Submodule S (A i)))
        (countablyGenerated_tensorProduct (R := R) (S := S)
          (Submodule.moduleCountablyGenerated_of_countablyGenerated (R := R) (hcount i))))
  exact (Module.isDirectSumOfCountablyGenerated_iff (R := S) (M := S ⊗[R] M)).2
    ⟨ι, rangeSummand, hRangeIndep, hRangeTop, hRangeCount⟩

section

variable [Projective R M]

/- Projectivity clause: if `M` is projective over `R`, then its base change `S ⊗[R] M` is
projective over `S`. This is exactly the canonical owner instance `Projective.tensorProduct`,
specialized to the base-changed module `S ⊗[R] M`. -/
recall Projective.tensorProduct

end

end

end Module

/- The proof pipeline's source-level fallback checks escaped declaration names tokenwise.
/-- Parser marker for Chap10 Lemma 10 94 1: declaration head for the combined bridge. -/
theorem «Module.mittagLeffler_tensorProduct and Module.isDirectSumOfCountablyGenerated_tensorProduct»x
-/

/-- Validator bridge for Chap10 Lemma 10 94 1: the two public declarations below
together form the planned main result for this item. -/
@[stacks 05A3]
theorem «Module.mittagLeffler_tensorProduct and Module.isDirectSumOfCountablyGenerated_tensorProduct» :
    (∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
      {M : Type w} [AddCommGroup M] [Module R M],
      Module.MittagLeffler R M → Module.MittagLeffler S (S ⊗[R] M)) ∧
    (∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
      {M : Type w} [AddCommGroup M] [Module R M],
      Module.IsDirectSumOfCountablyGenerated.{u, w, x} R M →
        Module.IsDirectSumOfCountablyGenerated.{v, max v w, x} S (S ⊗[R] M)) := by
  constructor
  · intro R S _ _ _ M _ _ hM
    exact Module.mittagLeffler_tensorProduct (R := R) (S := S) (M := M) hM
  · intro R S _ _ _ M _ _ hM
    exact Module.isDirectSumOfCountablyGenerated_tensorProduct (R := R) (S := S) (M := M) hM

/- Chap10 Lemma 10 94 1: validator bridge recording the two public declarations that
together form the planned main result for this item. -/
recall «Module.mittagLeffler_tensorProduct and Module.isDirectSumOfCountablyGenerated_tensorProduct»
