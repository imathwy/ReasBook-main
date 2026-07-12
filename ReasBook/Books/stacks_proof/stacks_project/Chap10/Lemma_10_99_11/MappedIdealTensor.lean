import Mathlib
import StacksProject_2024.Chap10.Lemma_10_39_18
import StacksProject_2024.Chap10.Lemma_10_51_5
import StacksProject_2024.Chap10.Remark_10_75_9
import StacksProject_2024.Chap10.Lemma_10_79_2
import StacksProject_2024.Chap10.Lemma_10_99_10_Variant_of_the_local_criterion

open CategoryTheory.Limits IsLocalRing
open scoped TensorProduct Pointwise

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite S M]

abbrev FlatQuotientsByIdealPowers (M : Type w) [AddCommGroup M] [Module R M]
    (I : Ideal R) : Prop :=
  ∀ n : ℕ, 1 ≤ n → Module.Flat (R ⧸ I ^ n) (M ⧸ (I ^ n • (⊤ : Submodule R M)))

/-- Helper for Chap10 Lemma 10 99 11: the quotient `M / ISM` is naturally a module over
`R / I`. -/
instance mappedIdealQuotient_module_over_sourceQuotient (I : Ideal R) :
    Module (R ⧸ I) (M ⧸ ((Ideal.map (algebraMap R S) I) • (⊤ : Submodule S M))) :=
  Module.compHom _ (algebraMap (R ⧸ I) (S ⧸ Ideal.map (algebraMap R S) I))

/-- Helper for Chap10 Lemma 10 99 11: the quotient `M / ISM` is an `R`-to-`R / I` scalar tower. -/
instance mappedIdealQuotient_isScalarTower_source_sourceQuotient (I : Ideal R) :
    IsScalarTower R (R ⧸ I) (M ⧸ ((Ideal.map (algebraMap R S) I) • (⊤ : Submodule S M))) :=
  IsScalarTower.of_algebraMap_smul fun r x ↦
    Submodule.Quotient.induction_on _ x fun m ↦ by
      change Submodule.Quotient.mk ((algebraMap R S r) • m) = Submodule.Quotient.mk (r • m)
      rw [← algebraMap_smul S r m]

/-- Helper for Chap10 Lemma 10 99 11: the quotient `M / ISM` is an `(R / I)`-to-`(S / IS)`
scalar tower. -/
instance mappedIdealQuotient_isScalarTower_sourceQuotient_targetQuotient (I : Ideal R) :
    IsScalarTower (R ⧸ I) (S ⧸ Ideal.map (algebraMap R S) I)
      (M ⧸ ((Ideal.map (algebraMap R S) I) • (⊤ : Submodule S M))) :=
  IsScalarTower.of_algebraMap_smul fun r x ↦
    Submodule.Quotient.induction_on _ x fun m ↦ rfl

/-- Helper for Chap10 Lemma 10 99 11: for any ring and module, quotienting by `JM` produces a
module over the quotient ring `S / J`. -/
instance quotientModule_module_over_ringQuotient
    {A : Type*} {N : Type*} [CommRing A] [AddCommGroup N] [Module A N] (J : Ideal A) :
    Module (A ⧸ J) (N ⧸ (J • (⊤ : Submodule A N))) :=
  inferInstance

/-- Helper for Chap10 Lemma 10 99 11: quotienting by `JM` also gives the scalar tower
`S → S / J → M / JM`. -/
instance quotientModule_isScalarTower_ring_ringQuotient
    {A : Type*} {N : Type*} [CommRing A] [AddCommGroup N] [Module A N] (J : Ideal A) :
    IsScalarTower A (A ⧸ J) (N ⧸ (J • (⊤ : Submodule A N))) :=
  IsScalarTower.of_algebraMap_smul fun a x ↦
    Submodule.Quotient.induction_on _ x fun n ↦ rfl

/-- Helper for Lemma 10.99.11: flatness of a module makes the canonical multiplication map
`I ⊗ N → N` injective. -/
lemma source_tensor_to_module_injective_of_flat
    {A : Type*} [CommRing A] {I : Ideal A} {N : Type*} [AddCommGroup N] [Module A N]
    (hflat : Module.Flat A N) :
    Function.Injective (TensorProduct.lift ((LinearMap.lsmul A N).comp I.subtype)) := by
  let μ : I ⊗[A] N →ₗ[A] N :=
    TensorProduct.lift ((LinearMap.lsmul A N).comp I.subtype)
  letI : Module.Flat A N := hflat
  have hrt : Function.Injective (I.subtype.rTensor N) :=
    Module.Flat.rTensor_preserves_injective_linearMap I.subtype Subtype.val_injective
  -- Proof comment: compare multiplication with tensoring the ideal inclusion and then evaluating
  -- `A ⊗ N ≃ N`.
  have hμ :
      μ = (TensorProduct.lid A N).toLinearMap.comp (I.subtype.rTensor N) := by
    ext a n
    rfl
  change Function.Injective μ
  rw [hμ]
  exact (TensorProduct.lid A N).injective.comp hrt

/-- Helper for Lemma 10.99.11: an element of an ideal maps linearly into its extension. -/
noncomputable def ideal_to_mapped_ideal
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) :
    I →ₗ[A] Ideal.map (algebraMap A B) I :=
  { toFun := fun a ↦
      ⟨algebraMap A B (a : A), Ideal.mem_map_of_mem (algebraMap A B) a.2⟩
    map_add' := by
      intro a b
      -- Proof comment: equality in the mapped ideal is checked on the ambient ring element.
      ext
      simp
    map_smul' := by
      intro r a
      -- Proof comment: the restricted scalar action on the mapped ideal is transported through
      -- `algebraMap`.
      ext
      simp [Algebra.smul_def] }

/-- Helper for Lemma 10.99.11: the tensor bridge from an ideal to its extension. -/
noncomputable def mapped_ideal_tensor_map
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) {N : Type*} [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] :
    I ⊗[A] N →ₗ[A] Ideal.map (algebraMap A B) I ⊗[B] N :=
  TensorProduct.lift
    { toFun := fun a ↦
        (TensorProduct.mk B (Ideal.map (algebraMap A B) I) N
          (ideal_to_mapped_ideal (A := A) (B := B) I a)).restrictScalars A
      map_add' := by
        intro a b
        -- Proof comment: pure tensors preserve addition in the left ideal factor.
        ext n
        simpa [ideal_to_mapped_ideal] using
          (TensorProduct.add_tmul
            (ideal_to_mapped_ideal (A := A) (B := B) I a)
            (ideal_to_mapped_ideal (A := A) (B := B) I b) n)
      map_smul' := by
        intro r a
        -- Proof comment: move the source scalar through the mapped ideal element and then through
        -- the tensor product.
        ext n
        simpa [ideal_to_mapped_ideal, Algebra.smul_def] using
          (TensorProduct.smul_tmul'
            (R := B) (r := algebraMap A B r)
            (m := ideal_to_mapped_ideal (A := A) (B := B) I a) (n := n)).symm }

/-- Helper for Lemma 10.99.11: the tensor bridge from an ideal to its extension is surjective. -/
lemma mapped_ideal_tensor_map_surjective
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) {N : Type*} [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] :
    Function.Surjective (mapped_ideal_tensor_map (A := A) (B := B) (N := N) I) := by
  have hmap_span :
      Ideal.map (algebraMap A B) I =
        Ideal.span (Set.range fun a : I ↦ algebraMap A B (a : A)) := by
    calc
      Ideal.map (algebraMap A B) I =
          Ideal.map (algebraMap A B) (Ideal.span (I : Set A)) := by
            rw [Ideal.span_eq]
      _ = Ideal.span ((algebraMap A B) '' (I : Set A)) := by
            rw [Ideal.map_span]
      _ = Ideal.span (Set.range fun a : I ↦ algebraMap A B (a : A)) := by
            congr 1
            ext x
            constructor
            · rintro ⟨a, ha, rfl⟩
              exact ⟨⟨a, ha⟩, rfl⟩
            · rintro ⟨a, rfl⟩
              exact ⟨a, a.2, rfl⟩
  intro z
  -- Proof comment: tensor induction reduces surjectivity to pure tensors in the target.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · exact ⟨0, by simp⟩
  · intro y n
    have hy_span :
        (y : B) ∈ Ideal.span (Set.range fun a : I ↦ algebraMap A B (a : A)) := by
      simpa [hmap_span] using y.2
    rcases Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp hy_span with ⟨c, hc⟩
    let xPre :=
      Finset.sum c.support fun a ↦ (a ⊗ₜ[A] ((c a) • n) : I ⊗[A] N)
    let yTerms : I → Ideal.map (algebraMap A B) I := fun a ↦
      ⟨c a * algebraMap A B (a : A),
        Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem (algebraMap A B) a.2)⟩
    refine ⟨xPre, ?_⟩
    -- Proof comment: expand the chosen preimage and collapse the resulting sum back to `y ⊗ n`.
    calc
      mapped_ideal_tensor_map (A := A) (B := B) (N := N) I xPre =
          Finset.sum c.support fun a ↦
            mapped_ideal_tensor_map (A := A) (B := B) (N := N) I
              (a ⊗ₜ[A] ((c a) • n)) := by
            simp [xPre, mapped_ideal_tensor_map]
      _ = Finset.sum c.support fun a ↦ yTerms a ⊗ₜ[B] n := by
            refine Finset.sum_congr rfl fun a ha ↦ ?_
            change
              (ideal_to_mapped_ideal (A := A) (B := B) I a) ⊗ₜ[B] ((c a) • n) =
                yTerms a ⊗ₜ[B] n
            calc
              (ideal_to_mapped_ideal (A := A) (B := B) I a) ⊗ₜ[B] ((c a) • n) =
                  (c a • ideal_to_mapped_ideal (A := A) (B := B) I a) ⊗ₜ[B] n := by
                    simpa using
                      (TensorProduct.smul_tmul'
                        (R := B) (r := c a)
                        (m := ideal_to_mapped_ideal (A := A) (B := B) I a)
                        (n := n)).symm
              _ = yTerms a ⊗ₜ[B] n := by
                    apply congrArg (fun t : Ideal.map (algebraMap A B) I ↦ t ⊗ₜ[B] n)
                    ext
                    simp [yTerms, ideal_to_mapped_ideal, mul_comm]
      _ = (Finset.sum c.support yTerms) ⊗ₜ[B] n := by
            simpa using (TensorProduct.sum_tmul (R := B) c.support yTerms n).symm
      _ = y ⊗ₜ[B] n := by
            apply congrArg (fun t : Ideal.map (algebraMap A B) I ↦ t ⊗ₜ[B] n)
            ext
            simpa [yTerms, Finsupp.sum] using hc
  · intro x y hx hy
    rcases hx with ⟨x', rfl⟩
    rcases hy with ⟨y', rfl⟩
    exact ⟨x' + y', by simp [mapped_ideal_tensor_map]⟩

/-- Helper for Lemma 10.99.11: the mapped-ideal multiplication map agrees with the source
multiplication map after the canonical tensor bridge. -/
lemma mapped_ideal_tensor_to_module_comp
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) {N : Type*} [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] :
    (TensorProduct.lift
      ((LinearMap.lsmul B N).comp (Ideal.map (algebraMap A B) I).subtype)).restrictScalars A ∘ₗ
        mapped_ideal_tensor_map (A := A) (B := B) (N := N) I =
      TensorProduct.lift ((LinearMap.lsmul A N).comp I.subtype) := by
  -- Proof comment: both composites send `a ⊗ n` to the scalar action of `a` on `n`.
  ext a n
  simp [mapped_ideal_tensor_map, ideal_to_mapped_ideal]

/-- Helper for Lemma 10.99.11: injectivity of `I ⊗[A] N → N` descends to injectivity of
`Ideal.map I ⊗[B] N → N`. -/
lemma mapped_ideal_tensor_to_module_injective_of_source_injective
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) {N : Type*} [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N]
    (hinj :
      Function.Injective (TensorProduct.lift ((LinearMap.lsmul A N).comp I.subtype))) :
    Function.Injective
      (TensorProduct.lift
        ((LinearMap.lsmul B N).comp (Ideal.map (algebraMap A B) I).subtype)) := by
  let μA : I ⊗[A] N →ₗ[A] N :=
    TensorProduct.lift ((LinearMap.lsmul A N).comp I.subtype)
  let μB : Ideal.map (algebraMap A B) I ⊗[B] N →ₗ[B] N :=
    TensorProduct.lift
      ((LinearMap.lsmul B N).comp (Ideal.map (algebraMap A B) I).subtype)
  have hcompare :
      (μB.restrictScalars A).comp
          (mapped_ideal_tensor_map (A := A) (B := B) (N := N) I) =
        μA := by
    -- Proof comment: the source and mapped multiplication maps commute with the tensor bridge.
    simpa [μA, μB] using
      mapped_ideal_tensor_to_module_comp (A := A) (B := B) (N := N) I
  -- Proof comment: descend injectivity through the surjective bridge
  -- `I ⊗[A] N → Ideal.map(I) ⊗[B] N`.
  intro x y hxy
  rcases mapped_ideal_tensor_map_surjective (A := A) (B := B) (N := N) I x with ⟨x', rfl⟩
  rcases mapped_ideal_tensor_map_surjective (A := A) (B := B) (N := N) I y with ⟨y', rfl⟩
  have hxyA : μA x' = μA y' := by
    calc
      μA x' =
          (μB.restrictScalars A)
            (mapped_ideal_tensor_map (A := A) (B := B) (N := N) I x') := by
              simpa [LinearMap.comp_apply] using
                (congrArg (fun f ↦ f x') hcompare).symm
      _ =
          (μB.restrictScalars A)
            (mapped_ideal_tensor_map (A := A) (B := B) (N := N) I y') := by
              simpa [μB] using hxy
      _ = μA y' := by
            simpa [LinearMap.comp_apply] using congrArg (fun f ↦ f y') hcompare
  exact congrArg
    (mapped_ideal_tensor_map (A := A) (B := B) (N := N) I)
    (hinj hxyA)

end
