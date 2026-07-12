import StacksProject_2024.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import StacksProject_2024.Chap10.Lemma_10_39_10
import StacksProject_2024.Chap10.Lemma_10_39_15
import StacksProject_2024.Chap10.Lemma_10_99_4
import StacksProject_2024.Chap10.Lemma_10_99_10_Variant_of_the_local_criterion
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open TensorProduct.AlgebraTensorModule
open CategoryTheory
open IsLocalRing
open CategoryTheory.Limits
open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type v}
variable [CommRing R] [CommRing S]
variable [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S]
variable [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module S M] [Module R M]
variable [IsScalarTower R S M]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S
local notation "ClosedFiberModule" => ClosedFiber ⊗[S] M
local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)

/- Domain-style sampling for the Noetherian fiberwise flatness criterion:
* primary domain: flatness of modules and algebra maps across local homomorphisms of Noetherian
  local rings, with the closed fiber carried by the canonical owner `Ideal.Fiber`;
* sampled owner declarations:
  `Ideal.Fiber`,
  `length_base_change_eq_length_mul_closed_fiber`,
  `free_of_flat_of_free_closedFiber`,
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`,
  `algebraMap_flat_of_flat_of_faithfullyFlat`;
* best owner abstraction: flatness lives on the canonical owners `Module.Flat`,
  `Module.FaithfullyFlat`, and `RingHom.Flat`, while the closed fiber and the fiber module belong
  on the owners `ClosedFiber = Ideal.Fiber (maximalIdeal R) S` and
  `ClosedFiberModule = ClosedFiber ⊗[S] M`; the quotient presentation
  `M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))` is only a bridge to
  the local criterion `10.99.10`.

Primitive data vs. derived API:
* primitive data: the local diagram `R → S → S'`, the finite nonzero `S'`-module `M`, flatness of
  `M` over `R`, and flatness of the canonical closed-fiber module `ClosedFiberModule` over
  `ClosedFiber`;
* derived API: flatness of `M` over `S`, faithful flatness of `M` over `S`, and then flatness of
  the algebra map `R → S`.

Source/core/bridge triage:
* `source-facing`: the two Stacks statements below;
* `core/canonical`: the owner predicates `Module.Flat`, `Module.FaithfullyFlat`, and
  `RingHom.Flat`, together with the canonical closed-fiber ring/module owners `ClosedFiber` and
  `ClosedFiberModule`;
* `bridge/view`: the quotient presentation of the closed fiber
  `S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)` and of the fiber module
  `M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))`.
-/

/-- Helper for Lemma 10.99.15 (Critère de platitude par fibres; Noetherian case): flatness of a
module makes the canonical multiplication map `I ⊗ N → N` injective. -/
private lemma source_tensor_to_module_injective_of_flat
    {A : Type*} [CommRing A] {I : Ideal A} {N : Type*} [AddCommGroup N] [Module A N]
    (hflat : Module.Flat A N) :
    Function.Injective (TensorProduct.lift ((LinearMap.lsmul A N).comp I.subtype)) := by
  let μ : I ⊗[A] N →ₗ[A] N :=
    TensorProduct.lift ((LinearMap.lsmul A N).comp I.subtype)
  letI : Module.Flat A N := hflat
  have hrt : Function.Injective (I.subtype.rTensor N) :=
    Module.Flat.rTensor_preserves_injective_linearMap I.subtype Subtype.val_injective
  -- Proof comment: compare the multiplication map with the tensor of the ideal inclusion
  -- followed by the standard identification `A ⊗ N ≃ N`.
  have hμ :
      μ = (TensorProduct.lid A N).toLinearMap.comp (I.subtype.rTensor N) := by
    ext a n
    rfl
  change Function.Injective μ
  rw [hμ]
  exact (TensorProduct.lid A N).injective.comp hrt

/-- Helper for Lemma 10.99.15 (Critère de platitude par fibres; Noetherian case): the source
ideal maps additively into its extension. -/
private lemma ideal_to_mapped_ideal_map_add
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (a b : I) :
    (⟨algebraMap A B (a + b : A), Ideal.mem_map_of_mem (algebraMap A B) (a + b).2⟩ :
      Ideal.map (algebraMap A B) I) =
      ⟨algebraMap A B (a : A), Ideal.mem_map_of_mem (algebraMap A B) a.2⟩ +
        ⟨algebraMap A B (b : A), Ideal.mem_map_of_mem (algebraMap A B) b.2⟩ := by
  -- Proof comment: equality in the mapped ideal is checked on the ambient ring element.
  ext
  simp

/-- Helper for Lemma 10.99.15 (Critère de platitude par fibres; Noetherian case): the source
ideal maps linearly into its extension. -/
private lemma ideal_to_mapped_ideal_map_smul
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (r : A) (a : I) :
    (⟨algebraMap A B (r • a : A), Ideal.mem_map_of_mem (algebraMap A B) (r • a).2⟩ :
      Ideal.map (algebraMap A B) I) =
      r • ⟨algebraMap A B (a : A), Ideal.mem_map_of_mem (algebraMap A B) a.2⟩ := by
  -- Proof comment: the restricted scalar action on the mapped ideal is transported through
  -- `algebraMap`.
  ext
  simp [Algebra.smul_def]

/-- Helper for Lemma 10.99.15 (Critère de platitude par fibres; Noetherian case): the original
ideal maps linearly into its extension. -/
private noncomputable def ideal_to_mapped_ideal
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) :
    I →ₗ[A] Ideal.map (algebraMap A B) I :=
  { toFun := fun a ↦
      ⟨algebraMap A B (a : A), Ideal.mem_map_of_mem (algebraMap A B) a.2⟩
    map_add' := ideal_to_mapped_ideal_map_add (A := A) (B := B) I
    map_smul' := ideal_to_mapped_ideal_map_smul (A := A) (B := B) I }

/-- Helper for Lemma 10.99.15 (Critère de platitude par fibres; Noetherian case): the tensor
bridge is additive in the left ideal factor. -/
private lemma mapped_ideal_tensor_left_map_add
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) {N : Type*} [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N]
    (a b : I) :
    (TensorProduct.mk B (Ideal.map (algebraMap A B) I) N
        (ideal_to_mapped_ideal (A := A) (B := B) I (a + b))).restrictScalars A =
      (TensorProduct.mk B (Ideal.map (algebraMap A B) I) N
        (ideal_to_mapped_ideal (A := A) (B := B) I a)).restrictScalars A +
      (TensorProduct.mk B (Ideal.map (algebraMap A B) I) N
        (ideal_to_mapped_ideal (A := A) (B := B) I b)).restrictScalars A := by
  -- Proof comment: after mapping the ideal element into `B`, pure tensors preserve sums.
  ext n
  simpa [ideal_to_mapped_ideal] using
    (TensorProduct.add_tmul
      (ideal_to_mapped_ideal (A := A) (B := B) I a)
      (ideal_to_mapped_ideal (A := A) (B := B) I b) n)

/-- Helper for Lemma 10.99.15 (Critère de platitude par fibres; Noetherian case): the tensor
bridge is `A`-linear in the left ideal factor. -/
private lemma mapped_ideal_tensor_left_map_smul
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) {N : Type*} [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N]
    (r : A) (a : I) :
    (TensorProduct.mk B (Ideal.map (algebraMap A B) I) N
        (ideal_to_mapped_ideal (A := A) (B := B) I (r • a))).restrictScalars A =
      r • (TensorProduct.mk B (Ideal.map (algebraMap A B) I) N
        (ideal_to_mapped_ideal (A := A) (B := B) I a)).restrictScalars A := by
  -- Proof comment: move the source scalar across the mapped ideal element and then across the
  -- pure tensor in the codomain.
  ext n
  simpa [ideal_to_mapped_ideal, Algebra.smul_def] using
    (TensorProduct.smul_tmul'
      (R := B) (r := algebraMap A B r)
      (m := ideal_to_mapped_ideal (A := A) (B := B) I a) (n := n)).symm

/-- Helper for Lemma 10.99.15 (Critère de platitude par fibres; Noetherian case): the canonical
tensor bridge from the source ideal to its mapped ideal. -/
private noncomputable def mapped_ideal_tensor_map
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) {N : Type*} [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] :
    I ⊗[A] N →ₗ[A] Ideal.map (algebraMap A B) I ⊗[B] N :=
  TensorProduct.lift
    { toFun := fun a ↦
        (TensorProduct.mk B (Ideal.map (algebraMap A B) I) N
          (ideal_to_mapped_ideal (A := A) (B := B) I a)).restrictScalars A
      map_add' := mapped_ideal_tensor_left_map_add (A := A) (B := B) (N := N) I
      map_smul' := mapped_ideal_tensor_left_map_smul (A := A) (B := B) (N := N) I }

/-- Helper for Lemma 10.99.15 (Critère de platitude par fibres; Noetherian case): the tensor
bridge has the expected value on pure tensors. -/
@[simp] private lemma mapped_ideal_tensor_map_tmul
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) {N : Type*} [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] (a : I) (n : N) :
    mapped_ideal_tensor_map (A := A) (B := B) (N := N) I (a ⊗ₜ[A] n) =
      (ideal_to_mapped_ideal (A := A) (B := B) I a) ⊗ₜ[B] n := by
  -- Proof comment: this is the defining computation rule of `TensorProduct.lift`.
  rfl

/-- Helper for Lemma 10.99.15 (Critère de platitude par fibres; Noetherian case): the tensor
bridge from an ideal to its extension is surjective. -/
private lemma mapped_ideal_tensor_map_surjective
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
  -- Proof comment: tensor induction reduces surjectivity to pure tensors in the target tensor.
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
            simp [xPre]
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
    exact ⟨x' + y', by simp⟩

/-- Helper for Lemma 10.99.15 (Critère de platitude par fibres; Noetherian case): the mapped
ideal multiplication map agrees with the source multiplication map after the tensor bridge. -/
private lemma mapped_ideal_tensor_to_module_comp
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) {N : Type*} [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] :
    (TensorProduct.lift
      ((LinearMap.lsmul B N).comp (Ideal.map (algebraMap A B) I).subtype)).restrictScalars A ∘ₗ
        mapped_ideal_tensor_map (A := A) (B := B) (N := N) I =
      TensorProduct.lift ((LinearMap.lsmul A N).comp I.subtype) := by
  -- Proof comment: both composites send `a ⊗ n` to the scalar action of `a` on `n`.
  ext a n
  simp [ideal_to_mapped_ideal]

/-- Helper for Lemma 10.99.15 (Critère de platitude par fibres; Noetherian case): injectivity of
the source multiplication map descends to injectivity over the mapped ideal. -/
private lemma mapped_ideal_tensor_to_module_injective_of_source_injective
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

omit [IsLocalRing S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing R] [IsNoetherianRing S]
  [Module R M] [IsScalarTower R S M] in
/-- Helper for Lemma 10.99.15 (Critère de platitude par fibres; Noetherian case): closed-fiber
scalars coming from `S` agree with the standard quotient action on `M / 𝔪S M`. -/
private lemma closed_fiber_quotient_smul_eq_source_smul (s : S)
    (q : M ⧸ (𝔪S • (⊤ : Submodule S M))) :
    letI : Algebra ClosedFiber (S ⧸ 𝔪S) :=
      (closedFiber_quotient_equiv (R := R) (S := S)).symm.toAlgHom.toAlgebra
    letI : Module ClosedFiber (M ⧸ (𝔪S • (⊤ : Submodule S M))) :=
      Module.compHom (M ⧸ (𝔪S • (⊤ : Submodule S M))) (algebraMap ClosedFiber (S ⧸ 𝔪S))
    ((algebraMap S ClosedFiber s) • q : M ⧸ (𝔪S • (⊤ : Submodule S M))) = s • q := by
  letI : Algebra ClosedFiber (S ⧸ 𝔪S) :=
    (closedFiber_quotient_equiv (R := R) (S := S)).symm.toAlgHom.toAlgebra
  letI : Module ClosedFiber (M ⧸ (𝔪S • (⊤ : Submodule S M))) :=
    Module.compHom (M ⧸ (𝔪S • (⊤ : Submodule S M))) (algebraMap ClosedFiber (S ⧸ 𝔪S))
  -- Proof comment: rewrite the transported `ClosedFiber`-scalar through the quotient-ring owner
  -- and then identify the resulting quotient scalar with the original `S`-action.
  change
    ((algebraMap ClosedFiber (S ⧸ 𝔪S) (algebraMap S ClosedFiber s)) • q :
      M ⧸ (𝔪S • (⊤ : Submodule S M))) = s • q
  rw [show algebraMap ClosedFiber (S ⧸ 𝔪S) (algebraMap S ClosedFiber s) =
      Ideal.Quotient.mk 𝔪S s by
        change
          (closedFiber_quotient_equiv (R := R) (S := S)).symm (algebraMap S ClosedFiber s) =
            Ideal.Quotient.mk 𝔪S s
        simpa using closedFiber_quotient_equiv_symm_algebraMap (R := R) (S := S) s]
  simpa using
    (ideal_scalar_action_eq_quotient_scalar_action
      (R := S) (I := 𝔪S) (N := M ⧸ (𝔪S • (⊤ : Submodule S M))) s q).symm

omit [IsLocalRing S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing R] [IsNoetherianRing S] in
/-- Helper for Lemma 10.99.15 (Critère de platitude par fibres; Noetherian case): the closed
fiber ring is flat over the quotient `S / 𝔪S` identified with it. -/
private lemma closed_fiber_ring_flat_over_quotient :
    let Abar : Type v := S ⧸ 𝔪S
    letI : Algebra Abar ClosedFiber :=
      (closedFiber_quotient_equiv (R := R) (S := S)).toRingEquiv.toRingHom.toAlgebra
    Module.Flat Abar ClosedFiber := by
  let Abar : Type v := S ⧸ 𝔪S
  let eRing : Abar ≃+* ClosedFiber :=
    (closedFiber_quotient_equiv (R := R) (S := S)).toRingEquiv
  letI : Algebra Abar ClosedFiber := eRing.toRingHom.toAlgebra
  have eAlg : ClosedFiber ≃ₐ[Abar] Abar :=
    AlgEquiv.ofRingEquiv (R := Abar) (f := eRing.symm) (by
      intro x
      change eRing.symm (eRing x) = x
      simp)
  -- Proof comment: after identifying `ClosedFiber` with the base ring `S / 𝔪S`, flatness is the
  -- self-flatness of the ring transported across the ring equivalence.
  exact Module.Flat.of_linearEquiv eAlg.toLinearEquiv

/-- Helper for Lemma 10.99.15 (Critère de platitude par fibres; Noetherian case): the source
closed-fiber tensor module is the quotient `M / 𝔪S M` with its transported `ClosedFiber`-owner. -/
private noncomputable def closed_fiber_tensor_owner_linear_equiv :
    let Abar : Type v := S ⧸ 𝔪S
    letI : Algebra ClosedFiber Abar :=
      (closedFiber_quotient_equiv (R := R) (S := S)).symm.toAlgHom.toAlgebra
    letI : Module ClosedFiber (M ⧸ (𝔪S • (⊤ : Submodule S M))) :=
      Module.compHom (M ⧸ (𝔪S • (⊤ : Submodule S M))) (algebraMap ClosedFiber Abar)
    ClosedFiberModule ≃ₗ[ClosedFiber] (M ⧸ (𝔪S • (⊤ : Submodule S M))) := by
  let Abar : Type v := S ⧸ 𝔪S
  let _ : Algebra ClosedFiber Abar :=
    (closedFiber_quotient_equiv (R := R) (S := S)).symm.toAlgHom.toAlgebra
  let _ : Module ClosedFiber (M ⧸ (𝔪S • (⊤ : Submodule S M))) :=
    Module.compHom (M ⧸ (𝔪S • (⊤ : Submodule S M))) (algebraMap ClosedFiber Abar)
  let _ : IsScalarTower S ClosedFiber (M ⧸ (𝔪S • (⊤ : Submodule S M))) :=
    -- Proof comment: the transported `ClosedFiber`-action restricts back to the original
    -- quotient `S`-action because `ClosedFiber` is just the quotient ring `S / 𝔪S`.
    IsScalarTower.of_algebraMap_smul (R := S) (A := ClosedFiber)
      (M := M ⧸ (𝔪S • (⊤ : Submodule S M))) fun s q ↦
        closed_fiber_quotient_smul_eq_source_smul (R := R) (S := S) (M := M) s q
  let eChange : ClosedFiberModule ≃ₗ[S] (Abar ⊗[S] M) :=
    -- Proof comment: first rewrite the left tensor factor `ClosedFiber` as the quotient ring
    -- `S ⧸ 𝔪S`, keeping the source module `M` fixed.
    TensorProduct.congr
      ((closedFiber_quotient_equiv (R := R) (S := S)).symm.toLinearEquiv)
      (LinearEquiv.refl S M)
  let eQuot : (Abar ⊗[S] M) ≃ₗ[Abar] (M ⧸ (𝔪S • (⊤ : Submodule S M))) :=
    -- Proof comment: after changing the left tensor factor, the standard
    -- `quotTensorEquivQuotSMul` equivalence gives the quotient presentation.
    (TensorProduct.quotTensorEquivQuotSMul M 𝔪S).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  -- Route correction: instead of transporting flatness on the quotient carrier directly, move
  -- along the tensor-side comparison and only then apply the canonical tensor/quotient bridge.
  exact
    (eChange.trans (LinearEquiv.restrictScalars S eQuot)).extendScalarsOfSurjective
      (closedFiber_algebraMap_surjective (R := R) (S := S))

omit [IsLocalRing S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing R] [IsNoetherianRing S]
  [Module R M] [IsScalarTower R S M] in
/-- Helper for Lemma 10.99.15 (Critère de platitude par fibres; Noetherian case): the quotient
module `M / 𝔪S M` is flat over `S / 𝔪S` once the closed-fiber tensor module is flat. -/
private lemma flat_closed_fiber_tensor_over_quotient
    (hflat_closedFiber : Module.Flat ClosedFiber ClosedFiberModule) :
    Module.Flat (S ⧸ 𝔪S) (M ⧸ (𝔪S • (⊤ : Submodule S M))) := by
  let Abar : Type v := S ⧸ 𝔪S
  let eRing : Abar ≃+* ClosedFiber :=
    (closedFiber_quotient_equiv (R := R) (S := S)).toRingEquiv
  letI : Algebra Abar ClosedFiber := eRing.toRingHom.toAlgebra
  letI : Algebra ClosedFiber Abar := eRing.symm.toRingHom.toAlgebra
  letI : Module ClosedFiber (M ⧸ (𝔪S • (⊤ : Submodule S M))) :=
    Module.compHom (M ⧸ (𝔪S • (⊤ : Submodule S M))) (algebraMap ClosedFiber Abar)
  letI : IsScalarTower Abar ClosedFiber (M ⧸ (𝔪S • (⊤ : Submodule S M))) :=
    -- Proof comment: the `Abar`-action obtained by passing through `ClosedFiber` is the standard
    -- quotient action because the ring equivalence is inverse to itself on coefficients.
    IsScalarTower.of_algebraMap_smul (R := Abar) (A := ClosedFiber)
      (M := M ⧸ (𝔪S • (⊤ : Submodule S M))) fun a q ↦ by
        change ((algebraMap ClosedFiber Abar (algebraMap Abar ClosedFiber a)) • q :
          M ⧸ (𝔪S • (⊤ : Submodule S M))) = a • q
        change (((closedFiber_quotient_equiv (R := R) (S := S)).symm
          ((closedFiber_quotient_equiv (R := R) (S := S)) a)) • q :
            M ⧸ (𝔪S • (⊤ : Submodule S M))) = a • q
        simp
  have hflatAbarClosedFiber : Module.Flat Abar ClosedFiber :=
    closed_fiber_ring_flat_over_quotient
  have hflatClosedFiberQuot :
      Module.Flat ClosedFiber (M ⧸ (𝔪S • (⊤ : Submodule S M))) := by
    let eOwner :
        ClosedFiberModule ≃ₗ[ClosedFiber] (M ⧸ (𝔪S • (⊤ : Submodule S M))) :=
      closed_fiber_tensor_owner_linear_equiv (R := R) (S := S) (M := M)
    -- Proof comment: the tensor-side owner comparison converts the hypothesis to the quotient
    -- carrier without introducing a second quotient-owner transport.
    letI : Module.Flat ClosedFiber ClosedFiberModule := hflat_closedFiber
    exact Module.Flat.of_linearEquiv eOwner.symm
  letI : Module.Flat Abar ClosedFiber := hflatAbarClosedFiber
  letI : Module.Flat ClosedFiber (M ⧸ (𝔪S • (⊤ : Submodule S M))) := hflatClosedFiberQuot
  -- Proof comment: compose flatness of the owner ring over `S / 𝔪S` with flatness of the fiber
  -- module over `ClosedFiber`.
  exact Module.Flat.trans Abar ClosedFiber (M ⧸ (𝔪S • (⊤ : Submodule S M)))

omit [IsLocalRing S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing R] [IsNoetherianRing S]
  [Module R M] [IsScalarTower R S M] in
/-- Helper for Lemma 10.99.15 (Critère de platitude par fibres; Noetherian case): closed-fiber
flatness transports to the quotient presentation required by the local criterion. -/
private lemma flat_quotient_module_of_flat_closedFiber
    (hflat_closedFiber : Module.Flat ClosedFiber ClosedFiberModule) :
    Module.Flat (S ⧸ 𝔪S) (M ⧸ (𝔪S • (⊤ : Submodule S M))) := by
  -- Proof comment: the previous lemma already packages the source-faithful tensor-side transport
  -- from the closed fiber to the quotient presentation used in the local criterion.
  exact flat_closed_fiber_tensor_over_quotient
    (R := R) (S := S) (M := M) hflat_closedFiber

omit [IsLocalRing S] [IsNoetherianRing S] in
/-- Helper for Lemma 10.99.15 (Critère de platitude par fibres; Noetherian case): kernel
vanishing for the multiplication map yields vanishing of `Tor₁` with the corresponding quotient. -/
private lemma tor_one_module_quotient_vanishes_of_ker_eq_bot
    (I : Ideal S)
    (hker :
      LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul S M).comp I.subtype)) = ⊥) :
    IsZero ((((Tor (ModuleCat S) 1).obj (ModuleCat.of S M)).obj (ModuleCat.of S (S ⧸ I)))) := by
  let μ : I ⊗[S] M →ₗ[S] M :=
    TensorProduct.lift ((LinearMap.lsmul S M).comp I.subtype)
  have hkerSubsingleton : Subsingleton (LinearMap.ker μ) := by
    -- Proof comment: the assumed kernel equality identifies the kernel module with the zero one.
    exact (Submodule.subsingleton_iff_eq_bot).2 (by simpa [μ] using hker)
  let e :
      (((Tor (ModuleCat S) 1).obj (ModuleCat.of S M)).obj (ModuleCat.of S (S ⧸ I))) ≃ₗ[S]
        LinearMap.ker μ :=
    tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module (R := S) (M := M) I
  have hsub :
      Subsingleton ((((Tor (ModuleCat S) 1).obj (ModuleCat.of S M)).obj
        (ModuleCat.of S (S ⧸ I)))) := by
    refine ⟨fun x y ↦ ?_⟩
    apply e.injective
    exact Subsingleton.elim _ _
  -- Proof comment: Remark `10.75.9` identifies this owner with the zero kernel.
  exact (ModuleCat.isZero_iff_subsingleton).2 hsub

-- Proof sketch: apply the variant of the local criterion for flatness to the local homomorphism
-- `S → S'` and the ideal `Ideal.map (algebraMap R S) (maximalIdeal R) ⊂ S`. The canonical
-- hypothesis that `ClosedFiberModule = ClosedFiber ⊗[S] M` is flat over
-- `ClosedFiber = (maximalIdeal R).Fiber S` is transported internally to the quotient presentation
-- needed by Lemma `10.99.10`, while flatness of `M` over `R` identifies the required
-- `Tor₁^S(S / 𝔪_R S, M)` vanishing via the injectivity argument from the textbook and Remark
-- `10.75.9`.
/-- Lemma 10.99.15 (Critère de platitude par fibres; Noetherian case): for local homomorphisms
`R → S → S'` of Noetherian local rings and a finite nonzero `S'`-module `M`, if the closed fiber
`ClosedFiberModule = ((maximalIdeal R).Fiber S) ⊗[S] M`, equivalently
`M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))`, is flat over the
closed-fiber ring `ClosedFiber = (maximalIdeal R).Fiber S`, equivalently
`S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`, and `M` is flat over `R`, then `M` is flat
over `S`. -/
@[stacks 00MP]
theorem flat_over_middleRing_of_flat_closedFiber_and_flat_over_base
    (S' : Type w) [CommRing S'] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalRing S'] [IsLocalHom (algebraMap S S')] [IsNoetherianRing S']
    [Module S' M] [IsScalarTower S S' M] [IsScalarTower R S' M] [Module.Finite S' M]
    (hflat_closedFiber : Module.Flat ClosedFiber ClosedFiberModule) (hflat_R : Module.Flat R M) :
    Module.Flat S M := by
  let I : Ideal S := 𝔪S
  have hI : I ≠ ⊤ := by
    -- Proof comment: the image of the maximal ideal under a local map is always proper.
    exact (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)).ne
  have hflat_mod :
      Module.Flat (S ⧸ I) (M ⧸ (I • (⊤ : Submodule S M))) := by
    -- Proof comment: transport the closed-fiber flatness hypothesis to the quotient owner
    -- required by Lemma `10.99.10`.
    simpa [I] using
      flat_quotient_module_of_flat_closedFiber (R := R) (S := S) (M := M) hflat_closedFiber
  have hsource_inj :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul R M).comp (maximalIdeal R).subtype)) := by
    -- Proof comment: flatness over the base ring makes the source multiplication map injective.
    exact
      source_tensor_to_module_injective_of_flat
        (A := R) (I := maximalIdeal R) (N := M) hflat_R
  have hmul_inj :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul S M).comp I.subtype)) := by
    -- Proof comment: descend injectivity through the canonical surjection
    -- `maximalIdeal R ⊗[R] M → I ⊗[S] M`.
    simpa [I] using
      mapped_ideal_tensor_to_module_injective_of_source_injective
        (A := R) (B := S) (I := maximalIdeal R) (N := M) hsource_inj
  have hTor :
      IsZero (Tor₁[S](M, S ⧸ I)) := by
    have hker :
        LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul S M).comp I.subtype)) = ⊥ := by
      simpa using LinearMap.ker_eq_bot.2 hmul_inj
    -- Proof comment: identify the quotient `Tor₁` owner with the kernel from Remark `10.75.9`.
    simpa [I] using
      tor_one_module_quotient_vanishes_of_ker_eq_bot
        (I := I) hker
  -- Proof comment: the hypotheses now match the variant local criterion over the local map
  -- `S → S'`.
  simpa [I] using
    flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal
      (R := S) (S := S') (M := M) I hI hTor hflat_mod

-- Proof sketch: the main theorem gives flatness of `M` over `S`. Using that `M` is finite over the local
-- ring `S'` and nonzero, Nakayama gives a nonzero residue-field fiber over `S'`; the closed-fiber
-- flatness hypothesis then forces `M / maximalIdeal S • ⊤` to be nontrivial, so Lemma `10.39.15`
-- yields faithful flatness of `M` over `S`. Finally apply the descent lemma saying that an
-- `S`-module which is flat over `R` and faithfully flat over `S` forces `R → S` to be flat.
/-- Under the same closed-fiber flatness and base-flatness hypotheses, the local homomorphism
`R → S` is flat. -/
theorem algebraMap_flat_of_flat_closedFiber_and_flat_over_base
    (S' : Type w) [CommRing S'] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalRing S'] [IsLocalHom (algebraMap S S')] [IsNoetherianRing S'] [Module S' M]
    [IsScalarTower S S' M] [IsScalarTower R S' M] [Module.Finite S' M] [Nontrivial M]
    (hflat_closedFiber : Module.Flat ClosedFiber ClosedFiberModule) (hflat_R : Module.Flat R M) :
    (algebraMap R S).Flat := by
  have hflat_S : Module.Flat S M :=
    flat_over_middleRing_of_flat_closedFiber_and_flat_over_base S' hflat_closedFiber hflat_R
  letI : Module.Flat S M := hflat_S
  let P' : Submodule S' M := maximalIdeal S' • (⊤ : Submodule S' M)
  let P : Submodule S M := P'.restrictScalars S
  have hquot_P' : Nontrivial (M ⧸ P') := by
    rw [Submodule.Quotient.nontrivial_iff]
    intro htop
    have hmax_jac : maximalIdeal S' ≤ Ring.jacobson S' := by
      simp [IsLocalRing.ringJacobson_eq_maximalIdeal]
    have hsub : Subsingleton M :=
      subsingleton_of_ideal_smul_top_eq_top_of_le_ring_jacobson
        (maximalIdeal S') htop hmax_jac
    exact (not_nontrivial_iff_subsingleton.mpr hsub) inferInstance
  have hquot_P : Nontrivial (M ⧸ P) :=
    (Submodule.Quotient.restrictScalarsEquiv S P').surjective.nontrivial
  have hsmul : maximalIdeal S • (⊤ : Submodule S M) ≤ P := by
    refine Submodule.smul_le.2 fun a ha m hm ↦ ?_
    change a • m ∈ P'.restrictScalars S
    change a • m ∈ P'
    rw [← IsScalarTower.algebraMap_smul S' a m]
    have hmem_map : algebraMap S S' a ∈ Ideal.map (algebraMap S S') (maximalIdeal S) :=
      Ideal.mem_map_of_mem _ ha
    have hmem : algebraMap S S' a ∈ maximalIdeal S' :=
      (IsLocalRing.map_maximalIdeal_le (algebraMap S S')) hmem_map
    exact
      Submodule.smul_mem_smul hmem (by simp)
  have hquot_S : Nontrivial (M ⧸ (maximalIdeal S • (⊤ : Submodule S M))) :=
    (Submodule.factor_surjective hsmul).nontrivial
  have hff_S : Module.FaithfullyFlat S M := by
    -- Proof comment: faithful flatness over the local ring `S` is detected on the residue field.
    refine
      faithfullyFlat_iff_forall_nontrivial_tensor_residueField.2 fun m hm ↦ ?_
    have hm_eq : m = maximalIdeal S := IsLocalRing.eq_maximalIdeal hm
    subst hm_eq
    exact
      (nontrivial_tensor_residueField_iff_nontrivial_quotSMul (maximalIdeal S)).2 hquot_S
  -- The remaining step is exactly the owner descent theorem `10.39.10`.
  have hflatRRestrict : Module.Flat R (RestrictScalars R S M) := by
    letI : Module.Flat R M := hflat_R
    exact Module.Flat.of_linearEquiv (restrictScalars_linearEquiv (R := R) (S := S) (M := M))
  letI : Module.Flat R (RestrictScalars R S M) := hflatRRestrict
  letI : Module.FaithfullyFlat S M := hff_S
  simpa using algebraMap_flat_of_flat_of_faithfullyFlat (R := R) (S := S) (M := M)

end
