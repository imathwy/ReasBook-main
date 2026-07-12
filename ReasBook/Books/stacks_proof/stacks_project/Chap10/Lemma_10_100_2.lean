import StacksProject_2024.Chap10.Lemma_10_39_9
import StacksProject_2024.Chap10.Lemma_10_99_7_Local_criterion_for_flatness
import StacksProject_2024.Chap10.Lemma_10_99_10_Variant_of_the_local_criterion
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open IsLocalRing
open scoped TensorProduct

universe u v w x y z

noncomputable section

variable {R : Type u} {S : Type v} {R' : Type w} {S' : Type x} {M : Type y}
variable [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
variable [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S']
variable [IsScalarTower R S S'] [IsScalarTower R R' S']
variable [IsLocalRing R] [IsLocalRing R'] [IsLocalRing S']
variable [IsLocalHom (algebraMap R' S')]
variable [IsNoetherianRing R'] [IsNoetherianRing S']
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite S M]

/-
Domain-style sampling:
- primary domain: commutative algebra of flatness for finite modules over local homomorphisms,
  combined with tensor-product base change;
- sampled owner declarations of the same kind:
  `flat_baseChange_of_flat`,
  `flat_of_residueField_tor_one_vanishing`,
  `tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module`;
- best owner abstraction: the public conclusion is the canonical owner `Module.Flat`, while the
  ring-map flatness hypotheses are expressed by the canonical object-prefix owner predicate
  `f.Flat`;
- primitive data: the local base ring `R`, the local Noetherian target map `R' → S'`, the finite
  `S`-module `M`, the flatness of the two horizontal maps, and the maximal-ideal identification
  in `R'`;
- derived API: flatness of the base-changed module `S' ⊗[S] M` over `R'`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma below about base change of a finite flat module under the
  maximal-ideal hypothesis;
- `core/canonical`: `Module.Flat`, `RingHom.Flat`, and the local flatness criterion
  `flat_of_residueField_tor_one_vanishing`;
- `bridge/view`: tensor-product base change and the Tor/kernel comparison from
  `tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module`.
-/

-- Proof sketch: first use flatness of `S → S'` and Lemma `10.39.9` to see that `S' ⊗[S] M` is
-- still flat over `R`. Since `R → R'` is flat, the hypothesis on the maximal ideals identifies
-- `maximalIdeal R ⊗[R] R'` with `maximalIdeal R'`, so injectivity of
-- `maximalIdeal R ⊗[R] (S' ⊗[S] M) → S' ⊗[S] M` transfers to injectivity of
-- `maximalIdeal R' ⊗[R'] (S' ⊗[S] M) → S' ⊗[S] M`. Remark `10.75.9` then gives the vanishing of
-- `Tor₁^{R'}(ResidueField R', S' ⊗[S] M)`, and Lemma `10.99.7` yields flatness over `R'`; the
-- local hypotheses on `R → S`, `R → R'`, and `S → S'` are not used in this route.
/-- Helper for Lemma 10.100.2: flatness of an `A`-module makes the canonical map
`I ⊗[A] N → N` injective for every ideal `I`. -/
lemma ideal_tensor_to_module_injective_of_flat
    {A : Type*} [CommRing A] {I : Ideal A} {N : Type*} [AddCommGroup N] [Module A N]
    (hN : Module.Flat A N) :
    Function.Injective (TensorProduct.lift ((LinearMap.lsmul A N).comp I.subtype)) := by
  let μ : I ⊗[A] N →ₗ[A] N :=
    TensorProduct.lift ((LinearMap.lsmul A N).comp I.subtype)
  letI : Module.Flat A N := hN
  have hrt : Function.Injective (I.subtype.rTensor N) :=
    Module.Flat.rTensor_preserves_injective_linearMap I.subtype Subtype.val_injective
  -- Proof comment: compare the canonical multiplication map with the tensor of the ideal
  -- inclusion followed by `TensorProduct.lid`.
  have hμ :
      μ = (TensorProduct.lid A N).toLinearMap.comp (I.subtype.rTensor N) := by
    ext a n
    rfl
  change Function.Injective μ
  rw [hμ]
  exact (TensorProduct.lid A N).injective.comp hrt

omit [IsLocalRing R] [IsLocalRing R'] [IsNoetherianRing R'] in
/-- Helper for Lemma 10.100.2: the image of an element of `I` lies in the mapped ideal. -/
lemma algebraMap_mem_mapped_ideal
    (I : Ideal R) (a : I) :
    algebraMap R R' (a : R) ∈ Ideal.map (algebraMap R R') I := by
  exact Ideal.mem_map_of_mem (algebraMap R R') a.2

/-- Helper for Lemma 10.100.2: the original ideal maps linearly into its extension. -/
noncomputable def ideal_to_mapped_ideal
    (I : Ideal R) :
    I →ₗ[R] Ideal.map (algebraMap R R') I :=
  { toFun := fun a ↦
      ⟨algebraMap R R' (a : R), algebraMap_mem_mapped_ideal (R := R) (R' := R') I a⟩
    map_add' := by
      intro a b
      ext
      simp
    map_smul' := by
      intro r a
      ext
      simp [Algebra.smul_def] }

omit [IsLocalRing R] [IsLocalRing R'] [IsNoetherianRing R'] in
/-- Helper for Lemma 10.100.2: the tensor bridge is additive in the ideal factor. -/
lemma mapped_ideal_tensor_left_map_add
    (I : Ideal R) {N : Type*} [AddCommGroup N] [Module R' N] [Module R N] [IsScalarTower R R' N]
    (a b : I) :
    (TensorProduct.mk R' (Ideal.map (algebraMap R R') I) N
        (ideal_to_mapped_ideal (R := R) (R' := R') I (a + b))).restrictScalars R =
      (TensorProduct.mk R' (Ideal.map (algebraMap R R') I) N
        (ideal_to_mapped_ideal (R := R) (R' := R') I a)).restrictScalars R +
      (TensorProduct.mk R' (Ideal.map (algebraMap R R') I) N
        (ideal_to_mapped_ideal (R := R) (R' := R') I b)).restrictScalars R := by
  -- Proof comment: after mapping the ideal element into `R'`, `TensorProduct.mk` sends sums of
  -- left factors to sums of pure tensors.
  ext n
  simpa [ideal_to_mapped_ideal] using
    (TensorProduct.add_tmul
      (ideal_to_mapped_ideal (R := R) (R' := R') I a)
      (ideal_to_mapped_ideal (R := R) (R' := R') I b) n)

omit [IsLocalRing R] [IsLocalRing R'] [IsNoetherianRing R'] in
/-- Helper for Lemma 10.100.2: the tensor bridge is `R`-linear in the ideal factor. -/
lemma mapped_ideal_tensor_left_map_smul
    (I : Ideal R) {N : Type*} [AddCommGroup N] [Module R' N] [Module R N] [IsScalarTower R R' N]
    (r : R) (a : I) :
    (TensorProduct.mk R' (Ideal.map (algebraMap R R') I) N
        (ideal_to_mapped_ideal (R := R) (R' := R') I (r • a))).restrictScalars R =
      r • (TensorProduct.mk R' (Ideal.map (algebraMap R R') I) N
        (ideal_to_mapped_ideal (R := R) (R' := R') I a)).restrictScalars R := by
  -- Proof comment: move the source scalar across the mapped ideal element and then across the
  -- pure tensor in the codomain.
  ext n
  simpa [ideal_to_mapped_ideal, Algebra.smul_def] using
    (TensorProduct.smul_tmul'
      (R := R') (r := algebraMap R R' r)
      (m := ideal_to_mapped_ideal (R := R) (R' := R') I a) (n := n)).symm

omit [IsLocalRing R] [IsLocalRing R'] [IsNoetherianRing R'] in
/-- Helper for Lemma 10.100.2: the canonical tensor bridge from the source ideal to its mapped
ideal sends `a ⊗ n` to the corresponding pure tensor in the target tensor product. -/
noncomputable def mapped_ideal_tensor_map
    (I : Ideal R) {N : Type*} [AddCommGroup N] [Module R' N] [Module R N] [IsScalarTower R R' N] :
    I ⊗[R] N →ₗ[R] Ideal.map (algebraMap R R') I ⊗[R'] N :=
  TensorProduct.lift
    { toFun := fun a ↦
        (TensorProduct.mk R' (Ideal.map (algebraMap R R') I) N
          (ideal_to_mapped_ideal (R := R) (R' := R') I a)).restrictScalars R
      map_add' := mapped_ideal_tensor_left_map_add (R := R) (R' := R') (N := N) I
      map_smul' := mapped_ideal_tensor_left_map_smul (R := R) (R' := R') (N := N) I }

omit [IsLocalRing R] [IsLocalRing R'] [IsNoetherianRing R'] in
/-- Helper for Lemma 10.100.2: the tensor bridge has the expected value on pure tensors. -/
@[simp] lemma mapped_ideal_tensor_map_tmul
    (I : Ideal R) {N : Type*} [AddCommGroup N] [Module R' N] [Module R N] [IsScalarTower R R' N]
    (a : I) (n : N) :
    mapped_ideal_tensor_map (R := R) (R' := R') (N := N) I (a ⊗ₜ[R] n) =
      (ideal_to_mapped_ideal (R := R) (R' := R') I a) ⊗ₜ[R'] n := by
  -- Proof comment: this is exactly the defining computation rule of `TensorProduct.lift`.
  rfl

omit [IsLocalRing R] [IsLocalRing R'] [IsNoetherianRing R'] in
/-- Helper for Lemma 10.100.2: every element in the span of the image of `I` lies in the mapped
ideal. -/
lemma mem_mapped_ideal_of_mem_span_range
    (I : Ideal R) {x : R'}
    (hx : x ∈ Submodule.span R' (Set.range fun a : I ↦ algebraMap R R' (a : R))) :
    x ∈ Ideal.map (algebraMap R R') I := by
  -- Proof comment: `Ideal.map` is exactly the ideal span of the image of `I`.
  simpa [Ideal.map, Ideal.submodule_span_eq, Set.image_eq_range] using hx

omit [IsLocalRing R] [IsLocalRing R'] [IsNoetherianRing R'] in
/-- Helper for Lemma 10.100.2: the mapped-ideal tensor bridge is surjective. -/
lemma mapped_ideal_tensor_map_surjective
    (I : Ideal R) {N : Type*} [AddCommGroup N] [Module R' N] [Module R N] [IsScalarTower R R' N] :
    Function.Surjective (mapped_ideal_tensor_map (R := R) (R' := R') (N := N) I) := by
  -- Route correction: the earlier subtype-varying induction target was brittle. Normalize the
  -- mapped ideal as a span first, then perform tensor induction on the target tensor and expand
  -- the left factor through a finitely supported span presentation.
  have hmap_span :
      Ideal.map (algebraMap R R') I =
        Ideal.span (Set.range fun a : I ↦ algebraMap R R' (a : R)) := by
    calc
      Ideal.map (algebraMap R R') I =
          Ideal.map (algebraMap R R') (Ideal.span (I : Set R)) := by
            rw [Ideal.span_eq]
      _ = Ideal.span ((algebraMap R R') '' (I : Set R)) := by
            rw [Ideal.map_span]
      _ = Ideal.span (Set.range fun a : I ↦ algebraMap R R' (a : R)) := by
            congr 1
            ext x
            constructor
            · rintro ⟨a, ha, rfl⟩
              exact ⟨⟨a, ha⟩, rfl⟩
            · rintro ⟨a, rfl⟩
              exact ⟨a, a.2, rfl⟩
  intro z
  -- Proof comment: tensor induction reduces surjectivity to pure tensors in the target tensor
  -- product over the mapped ideal.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · exact ⟨0, by simp⟩
  · intro y n
    have hy_span :
        (y : R') ∈ Ideal.span (Set.range fun a : I ↦ algebraMap R R' (a : R)) := by
      simpa [hmap_span] using y.2
    rcases Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp hy_span with ⟨c, hc⟩
    let xPre :=
      Finset.sum c.support fun a ↦ (a ⊗ₜ[R] ((c a) • n) : I ⊗[R] N)
    let yTerms : I → Ideal.map (algebraMap R R') I := fun a ↦
      ⟨c a * algebraMap R R' (a : R),
        Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem (algebraMap R R') a.2)⟩
    refine ⟨xPre, ?_⟩
    -- Proof comment: expand the chosen preimage and collapse the resulting finite sum back to
    -- the target pure tensor using the span presentation of `y`.
    calc
      mapped_ideal_tensor_map (R := R) (R' := R') (N := N) I xPre =
          Finset.sum c.support fun a ↦
            mapped_ideal_tensor_map (R := R) (R' := R') (N := N) I
              (a ⊗ₜ[R] ((c a) • n)) := by
            simp [xPre]
      _ = Finset.sum c.support fun a ↦ yTerms a ⊗ₜ[R'] n := by
            refine Finset.sum_congr rfl fun a ha ↦ ?_
            change
              (ideal_to_mapped_ideal (R := R) (R' := R') I a) ⊗ₜ[R'] ((c a) • n) =
                yTerms a ⊗ₜ[R'] n
            calc
              (ideal_to_mapped_ideal (R := R) (R' := R') I a) ⊗ₜ[R'] ((c a) • n) =
                  (c a • ideal_to_mapped_ideal (R := R) (R' := R') I a) ⊗ₜ[R'] n := by
                    simpa using
                      (TensorProduct.smul_tmul'
                        (R := R') (r := c a)
                        (m := ideal_to_mapped_ideal (R := R) (R' := R') I a)
                        (n := n)).symm
              _ = yTerms a ⊗ₜ[R'] n := by
                    apply congrArg (fun t : Ideal.map (algebraMap R R') I ↦ t ⊗ₜ[R'] n)
                    ext
                    simp [yTerms, ideal_to_mapped_ideal, mul_comm]
      _ = (Finset.sum c.support yTerms) ⊗ₜ[R'] n := by
            simpa using (TensorProduct.sum_tmul (R := R') c.support yTerms n).symm
      _ = y ⊗ₜ[R'] n := by
            apply congrArg (fun t : Ideal.map (algebraMap R R') I ↦ t ⊗ₜ[R'] n)
            ext
            simpa [yTerms, Finsupp.sum] using hc
  · intro x y hx hy
    rcases hx with ⟨x', rfl⟩
    rcases hy with ⟨y', rfl⟩
    refine ⟨x' + y', ?_⟩
    simp

omit [IsLocalRing R] [IsLocalRing R'] [IsNoetherianRing R'] in
/-- Helper for Lemma 10.100.2: the mapped-ideal multiplication map agrees with the source
multiplication map after the tensor bridge. -/
lemma mapped_ideal_tensor_to_module_comp
    (I : Ideal R) {N : Type*} [AddCommGroup N] [Module R' N] [Module R N] [IsScalarTower R R' N] :
    (TensorProduct.lift
      ((LinearMap.lsmul R' N).comp (Ideal.map (algebraMap R R') I).subtype)).restrictScalars R ∘ₗ
        mapped_ideal_tensor_map (R := R) (R' := R') (N := N) I =
      TensorProduct.lift ((LinearMap.lsmul R N).comp I.subtype) := by
  -- Proof comment: both composites send a pure tensor `a ⊗ n` to the scalar action of `a` on
  -- `n`, viewed once through `R` and once through `R'`.
  ext a n
  simp [ideal_to_mapped_ideal]

omit [IsLocalRing R] [IsLocalRing R'] [IsNoetherianRing R'] in
/-- Helper for Lemma 10.100.2: injectivity of `I ⊗[R] N → N` descends to injectivity of
`Ideal.map I ⊗[R'] N → N` through the canonical surjective tensor bridge. -/
lemma mapped_ideal_tensor_to_module_injective_of_source_injective
    (I : Ideal R) {N : Type*} [AddCommGroup N] [Module R' N] [Module R N] [IsScalarTower R R' N]
    (hinj :
      Function.Injective (TensorProduct.lift ((LinearMap.lsmul R N).comp I.subtype))) :
    Function.Injective
      (TensorProduct.lift
        ((LinearMap.lsmul R' N).comp (Ideal.map (algebraMap R R') I).subtype)) := by
  let μR : I ⊗[R] N →ₗ[R] N :=
    TensorProduct.lift ((LinearMap.lsmul R N).comp I.subtype)
  let μR' : Ideal.map (algebraMap R R') I ⊗[R'] N →ₗ[R'] N :=
    TensorProduct.lift
      ((LinearMap.lsmul R' N).comp (Ideal.map (algebraMap R R') I).subtype)
  have hcompare :
      (μR'.restrictScalars R).comp
          (mapped_ideal_tensor_map (R := R) (R' := R') (N := N) I) =
        μR := by
    -- Proof comment: both multiplication maps send a source pure tensor to the same scalar
    -- action on `N`, once directly over `R` and once through the mapped ideal over `R'`.
    simpa [μR, μR'] using mapped_ideal_tensor_to_module_comp (R := R) (R' := R') (N := N) I
  -- Proof comment: descend injectivity from `μR` through the surjective bridge
  -- `I ⊗[R] N → (Ideal.map I) ⊗[R'] N`.
  intro x y hxy
  rcases mapped_ideal_tensor_map_surjective (R := R) (R' := R') (N := N) I x with ⟨x', rfl⟩
  rcases mapped_ideal_tensor_map_surjective (R := R) (R' := R') (N := N) I y with ⟨y', rfl⟩
  have hxyR : μR x' = μR y' := by
    calc
      μR x' =
          (μR'.restrictScalars R)
            (mapped_ideal_tensor_map (R := R) (R' := R') (N := N) I x') := by
              simpa [LinearMap.comp_apply] using
                (congrArg (fun f ↦ f x') hcompare).symm
      _ =
          (μR'.restrictScalars R)
            (mapped_ideal_tensor_map (R := R) (R' := R') (N := N) I y') := by
              simpa [μR'] using hxy
      _ = μR y' := by
            simpa [LinearMap.comp_apply] using congrArg (fun f ↦ f y') hcompare
  exact congrArg
    (mapped_ideal_tensor_map (R := R) (R' := R') (N := N) I)
    (hinj hxyR)

/-- Helper for Lemma 10.100.2: fixing the right Tor variable gives the canonical comparison
between the public owner and the fixed-left source owner. -/
private noncomputable def tor_one_left_owner_iso
    {A : Type u} [CommRing A]
    (M' : ModuleCat A) :
    (((Tor (ModuleCat A) 1).flip).obj M') ≅ ((Tor' (ModuleCat A) 1).obj M') where
  hom :=
    { app := fun X ↦ (((tor_flip_iso (ModuleCat A) 1).hom.app X).app M')
      naturality := by
        intro X Y f
        -- Proof comment: evaluating `tor_flip_iso` at the fixed right variable preserves
        -- naturality in the left variable.
        simpa using congrArg (fun α ↦ α.app M') ((tor_flip_iso (ModuleCat A) 1).hom.naturality f) }
  inv :=
    { app := fun X ↦ (((tor_flip_iso (ModuleCat A) 1).inv.app X).app M')
      naturality := by
        intro X Y f
        -- Proof comment: the inverse comparison is natural for the same reason.
        simpa using congrArg (fun α ↦ α.app M') ((tor_flip_iso (ModuleCat A) 1).inv.naturality f) }
  hom_inv_id := by
    ext X x
    -- Proof comment: the componentwise inverse law is inherited from `tor_flip_iso`.
    have h := congrArg (fun α ↦ α.app M') ((tor_flip_iso (ModuleCat A) 1).hom_inv_id_app X)
    simpa using congrArg (fun f ↦ f x) (congrArg ModuleCat.Hom.hom h)
  inv_hom_id := by
    ext X x
    -- Proof comment: and likewise for the other inverse law.
    have h := congrArg (fun α ↦ α.app M') ((tor_flip_iso (ModuleCat A) 1).inv_hom_id_app X)
    simpa using congrArg (fun f ↦ f x) (congrArg ModuleCat.Hom.hom h)

/-- Helper for Lemma 10.100.2: degree `1` of the canonical comparison between the module-first
public Tor owner and the flipped source owner. -/
noncomputable def tor_one_module_flip_owner_iso
    {A : Type u} [CommRing A] {N : Type u} [AddCommGroup N] [Module A N] :
    ((Tor (ModuleCat A) 1).obj (ModuleCat.of A N)) ≅
      ((Functor.flip (Tor' (ModuleCat A) 1)).obj (ModuleCat.of A N)) := by
  simpa using ((tor_flip_iso (ModuleCat A) 1).app (ModuleCat.of A N))

/-- Helper for Lemma 10.100.2: the module-first public owner `Tor₁^A(N, -)` agrees with the
fixed-left source owner used by the tensor-kernel comparison. -/
noncomputable def tor_one_module_source_owner_iso
    {A : Type u} [CommRing A] {N : Type u} [AddCommGroup N] [Module A N] :
    ((Tor (ModuleCat A) 1).flip.obj (ModuleCat.of A N)) ≅
      ((Tor' (ModuleCat A) 1).obj (ModuleCat.of A N)) := by
  -- Proof comment: evaluate the fixed-right-variable comparison at `ModuleCat.of A N`.
  simpa using tor_one_left_owner_iso (A := A) (M' := ModuleCat.of A N)

/-- Helper for Lemma 10.100.2: at the quotient object `A / J`, the flipped source owner
`Tor'₁^A(A / J, N)` agrees with the fixed-left source owner `Tor'₁^A(N, A / J)` via the common
kernel model from Remark `10.75.9`. -/
noncomputable def tor_one_quotient_flip_to_source_owner_iso
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type u} [AddCommGroup N] [Module A N]
    (J : Ideal A) :
    ((((Functor.flip (Tor' (ModuleCat A) 1)).obj (ModuleCat.of A N)).obj
      (ModuleCat.of A (A ⧸ J)))) ≅
      ((((Tor' (ModuleCat A) 1).obj (ModuleCat.of A N)).obj
        (ModuleCat.of A (A ⧸ J)))) := by
  let eFlipPublic :
      ((((Functor.flip (Tor' (ModuleCat A) 1)).obj (ModuleCat.of A N)).obj
        (ModuleCat.of A (A ⧸ J)))) ≅
        ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A N)).obj
          (ModuleCat.of A (A ⧸ J)))) :=
    ((tor_one_module_flip_owner_iso (A := A) (N := N)).app (ModuleCat.of A (A ⧸ J))).symm
  let ePublicKer :
      ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A N)).obj
        (ModuleCat.of A (A ⧸ J)))) ≅
        ModuleCat.of A
          (LinearMap.ker
            (TensorProduct.lift ((LinearMap.lsmul A N).comp J.subtype))) :=
    (tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module (R := A) (M := N) J).toModuleIso
  let eSourceKer :
      ((((Tor' (ModuleCat A) 1).obj (ModuleCat.of A N)).obj
        (ModuleCat.of A (A ⧸ J)))) ≅
        ModuleCat.of A
          (LinearMap.ker
            (TensorProduct.lift ((LinearMap.lsmul A N).comp J.subtype))) :=
    (source_owner_tor_one_quotient_equiv_ker_ideal_tensor_to_module
      (R := A) (M := N) J).toModuleIso
  -- Proof comment: both quotient-level source owners are identified with the same tensor kernel.
  exact eFlipPublic ≪≫ ePublicKer ≪≫ eSourceKer.symm

/-- Helper for Lemma 10.100.2: vanishing of the kernel of `I ⊗[A] N → N` forces the module-first
quotient `Tor₁` owner to vanish. -/
lemma tor_one_module_quotient_vanishes_of_ker_eq_bot
    {A : Type u} [CommRing A] {I : Ideal A} {N : Type u} [AddCommGroup N] [Module A N]
    (hker :
      LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul A N).comp I.subtype)) = ⊥) :
    IsZero ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A N)).obj
      (ModuleCat.of A (A ⧸ I)))) := by
  let μ : I ⊗[A] N →ₗ[A] N :=
    TensorProduct.lift ((LinearMap.lsmul A N).comp I.subtype)
  have hker_subsingleton : Subsingleton (LinearMap.ker μ) := by
    -- Proof comment: the assumed kernel equality identifies the kernel module with the zero
    -- submodule.
    exact (Submodule.subsingleton_iff_eq_bot).2 (by simpa [μ] using hker)
  let e :
      (((Tor (ModuleCat A) 1).obj (ModuleCat.of A N)).obj (ModuleCat.of A (A ⧸ I))) ≃ₗ[A]
        LinearMap.ker μ :=
    tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module (R := A) (M := N) I
  have hsub :
      Subsingleton ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A N)).obj
        (ModuleCat.of A (A ⧸ I)))) := by
    refine ⟨fun x y ↦ ?_⟩
    apply e.injective
    exact Subsingleton.elim _ _
  -- Proof comment: Remark `10.75.9` identifies this Tor owner with the zero kernel.
  exact (ModuleCat.isZero_iff_subsingleton).2 hsub

/-- Helper for Lemma 10.100.2: in the same-universe local-ring setting, injectivity of
`maximalIdeal A ⊗[A] N → N` gives the residue-field `Tor₁` vanishing used by the local criterion.
-/
lemma residueField_tor_one_vanishes_of_maximalIdeal_tensor_injective
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {N : Type u}
    [AddCommGroup N] [Module A N]
    (hinj :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul A N).comp (maximalIdeal A).subtype))) :
    IsZero (Tor₁[A](ResidueField A, N)) := by
  have hker :
      LinearMap.ker
          (TensorProduct.lift ((LinearMap.lsmul A N).comp (maximalIdeal A).subtype)) = ⊥ :=
    LinearMap.ker_eq_bot.2 hinj
  have hmoduleFirstQuot :
      IsZero ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A N)).obj
        (ModuleCat.of A (A ⧸ maximalIdeal A)))) := by
    -- Proof comment: Remark `10.75.9` turns injectivity of the multiplication map into the
    -- quotient-level module-first `Tor₁` vanishing.
    exact
      tor_one_module_quotient_vanishes_of_ker_eq_bot
        (A := A) (I := maximalIdeal A) (N := N) hker
  have hflippedSourceQuot :
      IsZero ((((Functor.flip (Tor' (ModuleCat A) 1)).obj (ModuleCat.of A N)).obj
        (ModuleCat.of A (A ⧸ maximalIdeal A)))) := by
    let eModule :
        (((Tor (ModuleCat A) 1).obj (ModuleCat.of A N)).obj
          (ModuleCat.of A (A ⧸ maximalIdeal A))) ≅
          ((((Functor.flip (Tor' (ModuleCat A) 1)).obj (ModuleCat.of A N)).obj
            (ModuleCat.of A (A ⧸ maximalIdeal A)))) :=
      (tor_one_module_flip_owner_iso (A := A) (N := N)).app
        (ModuleCat.of A (A ⧸ maximalIdeal A))
    -- Proof comment: first move the module-first public owner to the flipped source owner.
    exact IsZero.of_iso hmoduleFirstQuot eModule.symm
  have hsourceQuot :
      IsZero ((((Tor' (ModuleCat A) 1).obj (ModuleCat.of A N)).obj
        (ModuleCat.of A (A ⧸ maximalIdeal A)))) := by
    let eSource :
        ((((Functor.flip (Tor' (ModuleCat A) 1)).obj (ModuleCat.of A N)).obj
          (ModuleCat.of A (A ⧸ maximalIdeal A)))) ≅
          ((((Tor' (ModuleCat A) 1).obj (ModuleCat.of A N)).obj
            (ModuleCat.of A (A ⧸ maximalIdeal A)))) :=
      tor_one_quotient_flip_to_source_owner_iso (A := A) (N := N) (maximalIdeal A)
    -- Proof comment: then compare the two source-owner orientations through the shared kernel.
    exact IsZero.of_iso hflippedSourceQuot eSource.symm
  have hquotTor :
      IsZero ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A (A ⧸ maximalIdeal A))).obj
        (ModuleCat.of A N))) := by
    let ePublic :
        (((Tor (ModuleCat A) 1).obj (ModuleCat.of A (A ⧸ maximalIdeal A))).obj
          (ModuleCat.of A N)) ≅
          (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A N)).obj
            (ModuleCat.of A (A ⧸ maximalIdeal A))) :=
      tor_one_quotient_source_owner_iso (R := A) (M := N) (maximalIdeal A)
    -- Proof comment: swap back to the quotient-first public owner that the local criterion uses.
    exact IsZero.of_iso hsourceQuot ePublic
  -- Proof comment: the local ring residue field is the maximal-ideal quotient, so the quotient
  -- owner above is exactly the residue-field owner after transport along the canonical equivalence.
  simpa [IsLocalRing.ResidueField] using hquotTor

/-- Helper for Lemma 10.100.2: injectivity of `I ⊗[A] N → N` persists after lifting only the
module universe. -/
lemma ulift_ideal_tensor_injective
    {A : Type u} [CommRing A] {I : Ideal A}
    {N : Type v} [AddCommGroup N] [Module A N]
    (hinj : Function.Injective (TensorProduct.lift ((LinearMap.lsmul A N).comp I.subtype))) :
    Function.Injective
      (TensorProduct.lift ((LinearMap.lsmul A (ULift.{max u v} N)).comp I.subtype)) := by
  let μ : I ⊗[A] N →ₗ[A] N :=
    TensorProduct.lift ((LinearMap.lsmul A N).comp I.subtype)
  let μu : I ⊗[A] ULift.{max u v} N →ₗ[A] ULift.{max u v} N :=
    TensorProduct.lift ((LinearMap.lsmul A (ULift.{max u v} N)).comp I.subtype)
  let eTensor :
      I ⊗[A] ULift.{max u v} N ≃ₗ[A] I ⊗[A] N :=
    TensorProduct.congr (LinearEquiv.refl A I)
      (ULift.moduleEquiv : ULift.{max u v} N ≃ₗ[A] N)
  have hSquare :
      μ.comp eTensor.toLinearMap =
        (ULift.moduleEquiv : ULift.{max u v} N ≃ₗ[A] N).toLinearMap.comp μu := by
    -- Proof comment: after identifying `ULift N` with `N`, both multiplication maps send a pure
    -- tensor to the same scalar multiple.
    ext i n
    rfl
  -- Proof comment: transfer injectivity across the tensor-product linear equivalence and the
  -- canonical identification `ULift N ≃ N`.
  intro x y hxy
  apply eTensor.injective
  apply hinj
  calc
    μ (eTensor x) =
        (ULift.moduleEquiv : ULift.{max u v} N ≃ₗ[A] N) (μu x) := by
          simpa [LinearMap.comp_apply] using congrArg (fun f ↦ f x) hSquare
    _ =
        (ULift.moduleEquiv : ULift.{max u v} N ≃ₗ[A] N) (μu y) := by
          simpa using congrArg
            (fun z ↦ (ULift.moduleEquiv : ULift.{max u v} N ≃ₗ[A] N) z) hxy
    _ = μ (eTensor y) := by
          simpa [LinearMap.comp_apply] using (congrArg (fun f ↦ f y) hSquare).symm

/-- Helper for Lemma 10.100.2: the injective maximal-ideal tensor map transports to the common
`ULift` universe needed by the local criterion. -/
lemma ulift_maximalIdeal_tensor_injective
    {A : Type u} [CommRing A] [IsLocalRing A] {N : Type v}
    [AddCommGroup N] [Module A N]
    [IsLocalRing (ULift.{max u v} A)]
    (hinj :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul A N).comp (maximalIdeal A).subtype))) :
    Function.Injective
      (TensorProduct.lift
        ((LinearMap.lsmul (ULift.{max u v} A) (ULift.{max u v} N)).comp
          (maximalIdeal (ULift.{max u v} A)).subtype)) := by
  let Au : Type max u v := ULift.{max u v} A
  let Nu : Type max u v := ULift.{max u v} N
  have hinj_u :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul A Nu).comp (maximalIdeal A).subtype)) := by
    -- Proof comment: first lift only the module universe while keeping the source ring fixed.
    simpa [Nu] using
      ulift_ideal_tensor_injective (A := A) (I := maximalIdeal A) (N := N) hinj
  have hmapped :
      Function.Injective
        (TensorProduct.lift
          ((LinearMap.lsmul Au Nu).comp
            (Ideal.map (algebraMap A Au) (maximalIdeal A)).subtype)) :=
    mapped_ideal_tensor_to_module_injective_of_source_injective
      (R := A) (R' := Au) (N := Nu) (I := maximalIdeal A) hinj_u
  have hsurj : Function.Surjective (algebraMap A Au) := by
    intro a
    cases a with
    | up a =>
        exact ⟨a, rfl⟩
  have hmap :
      Ideal.map (algebraMap A Au) (maximalIdeal A) = maximalIdeal Au :=
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A Au) hsurj
  -- Proof comment: the mapped source maximal ideal is exactly the maximal ideal upstairs.
  rw [← hmap]
  exact hmapped

/-- Helper for Lemma 10.100.2: the lifted injective maximal-ideal tensor map gives the lifted
residue-field `Tor₁`-vanishing required by the local criterion. -/
lemma ulift_residueField_tor_one_vanishes_of_maximalIdeal_tensor_injective
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {N : Type v}
    [AddCommGroup N] [Module A N]
    [IsLocalRing (ULift.{max u v} A)]
    (hinj :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul A N).comp (maximalIdeal A).subtype))) :
    IsZero (Tor₁[ULift.{max u v} A](ResidueField (ULift.{max u v} A), ULift.{max u v} N)) := by
  let Au : Type max u v := ULift.{max u v} A
  let Nu : Type max u v := ULift.{max u v} N
  letI : IsNoetherianRing Au := isNoetherianRing_of_ringEquiv A (ULift.ringEquiv : Au ≃+* A).symm
  -- Proof comment: after transporting injectivity to the common universe, reuse the already
  -- proved same-universe residue-field `Tor₁` vanishing lemma directly.
  simpa [Au, Nu] using
    residueField_tor_one_vanishes_of_maximalIdeal_tensor_injective
      (A := Au) (N := Nu)
      (ulift_maximalIdeal_tensor_injective (A := A) (N := N) hinj)

/-- Helper for Lemma 10.100.2: flatness descends across an algebra equivalence on the base ring
and a linear equivalence on the module. -/
lemma flat_descend_of_algEquiv_and_linearEquiv
    {A : Type u} [CommRing A] {Au : Type z} [CommRing Au] [Algebra A Au]
    {N : Type v} [AddCommGroup N] [Module A N]
    {Nu : Type z} [AddCommGroup Nu] [Module A Nu] [Module Au Nu] [IsScalarTower A Au Nu]
    (eA : Au ≃ₐ[A] A) (eN : N ≃ₗ[A] Nu)
    (hflat : Module.Flat Au Nu) :
    Module.Flat A N := by
  have hflatAAu : Module.Flat A Au := by
    -- Proof comment: the algebra equivalence identifies `Au` with the free rank-one `A`-module
    -- `A` itself.
    exact Module.Flat.of_linearEquiv eA.toLinearEquiv
  have hflatANu : Module.Flat A Nu := by
    -- Proof comment: compose flatness along `A → Au`.
    letI : Module.Flat A Au := hflatAAu
    letI : Module.Flat Au Nu := hflat
    exact Module.Flat.trans A Au Nu
  -- Proof comment: finally remove the module comparison by linear equivalence.
  letI : Module.Flat A Nu := hflatANu
  exact Module.Flat.of_linearEquiv eN

/-- Helper for Lemma 10.100.2: flatness over the lifted ring descends back through the canonical
`ULift` ring and module equivalences. -/
lemma ulift_flat_descend
    {A : Type u} [CommRing A] {N : Type v} [AddCommGroup N] [Module A N]
    (hflat : Module.Flat (ULift.{max u v} A) (ULift.{max u v} N)) :
    Module.Flat A N := by
  -- Proof comment: specialize the generic descent lemma to the canonical `ULift` equivalences.
  let eA : ULift.{max u v} A ≃ₐ[A] A := ULift.algEquiv (R := A) (A := A)
  let eN : N ≃ₗ[A] ULift.{max u v} N := (ULift.moduleEquiv (R := A) (M := N)).symm
  exact flat_descend_of_algEquiv_and_linearEquiv
    (A := A) (Au := ULift.{max u v} A) (N := N) (Nu := ULift.{max u v} N)
    eA eN
    hflat

/-- Lemma 10.100.2: if `R` is local, `R' → S'` is a local homomorphism of local Noetherian rings,
the horizontal maps `R → R'` and `S → S'` are flat, `M` is a finite `S`-module that is flat over
`R`, and the image of `maximalIdeal R` in `R'` is `maximalIdeal R'`, then the base change
`S' ⊗[S] M` is flat over `R'`. -/
@[stacks 0GEB]
theorem flat_baseChange_of_finite_of_flat_of_maximalIdeal_map_eq
    (hRR' : (algebraMap R R').Flat)
    (hSS' : (algebraMap S S').Flat)
    (hM : Module.Flat R M)
    (hmax : Ideal.map (algebraMap R R') (maximalIdeal R) = maximalIdeal R') :
    Module.Flat R' (S' ⊗[S] M) := by
  let N := S' ⊗[S] M
  let _ : (algebraMap R R').Flat := hRR'
  have hSS'_flat : Module.Flat S S' := (RingHom.flat_algebraMap_iff).1 hSS'
  let _ : Module.Flat S S' := hSS'_flat
  let _ : Module.Flat R M := hM
  have hN_flat_R : Module.Flat R N := by
    -- Proof comment: flat base change along `S → S'` preserves the original `R`-flatness of `M`.
    simpa [N] using (flat_baseChange_of_flat (R := R) (S := S) (S' := S') (M := M))
  have hsource_inj :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul R N).comp (maximalIdeal R).subtype)) :=
    ideal_tensor_to_module_injective_of_flat (A := R) (I := maximalIdeal R) hN_flat_R
  have hmapped_inj :
      Function.Injective
        (TensorProduct.lift
          ((LinearMap.lsmul R' N).comp
            (Ideal.map (algebraMap R R') (maximalIdeal R)).subtype)) :=
    mapped_ideal_tensor_to_module_injective_of_source_injective
      (R := R) (R' := R') (N := N) (I := maximalIdeal R) hsource_inj
  have hmaximal_inj :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul R' N).comp (maximalIdeal R').subtype)) := by
    -- Proof comment: the maximal-ideal hypothesis identifies the mapped source ideal with the
    -- target maximal ideal, matching the textbook midpoint exactly.
    rw [← hmax]
    exact hmapped_inj
  let Aw : Type max w (max x y) := ULift.{max w (max x y)} R'
  let Nw : Type max w (max x y) := ULift.{max w (max x y)} N
  let eAw : Aw ≃+* R' := ULift.ringEquiv
  letI : IsLocalRing Aw := RingEquiv.isLocalRing eAw.symm
  letI : IsNoetherianRing Aw := isNoetherianRing_of_ringEquiv R' eAw.symm
  letI : Algebra Aw R' := eAw.toRingHom.toAlgebra
  letI : Algebra Aw S' := ((algebraMap R' S').comp (algebraMap Aw R')).toAlgebra
  letI : IsLocalHom (algebraMap Aw R') :=
    Function.Surjective.isLocalHom _ eAw.surjective
  letI : IsLocalHom (algebraMap Aw S') := by
    -- Proof comment: the lifted local map is just the composite `Aw → R' → S'`.
    change IsLocalHom ((algebraMap R' S').comp (algebraMap Aw R'))
    exact RingHom.isLocalHom_comp _ _
  let algAwS' : Algebra Aw S' := inferInstance
  let modS'N : Module S' N := inferInstance
  let modAwN : Module Aw N := inferInstance
  let modS'Nw : Module S' Nw := inferInstance
  let modAwNw : Module Aw Nw := inferInstance
  let towerAwSN : @IsScalarTower Aw S' N algAwS'.toSMul modS'N.toSMul modAwN.toSMul := by
    refine @IsScalarTower.mk Aw S' N algAwS'.toSMul modS'N.toSMul modAwN.toSMul ?_
    intro a s n
    cases a with
    | up a =>
        simpa [Algebra.smul_def, ULift.smul_def] using (smul_assoc a s n)
  let hTower : @IsScalarTower Aw S' Nw algAwS'.toSMul modS'Nw.toSMul modAwNw.toSMul := by
    refine @IsScalarTower.mk Aw S' Nw algAwS'.toSMul modS'Nw.toSMul modAwNw.toSMul ?_
    intro a s n
    cases a with
    | up a =>
        cases n with
        | up n =>
            apply ULift.down_injective
            change (((algebraMap R' S') a * s) • n = a • (s • n))
            simpa [Algebra.smul_def] using (smul_assoc a s n)
  letI : Module.Finite S' Nw :=
    Module.Finite.equiv (ULift.moduleEquiv (R := S') (M := N)).symm
  have hTor_w :
      IsZero (Tor₁[Aw](ResidueField Aw, Nw)) := by
    -- Route correction: instead of reopening the Tor owner-transport issue, move to the common
    -- `ULift` universe and reuse the same-universe residue-field criterion already proved above.
    simpa [Aw, Nw] using
      ulift_residueField_tor_one_vanishes_of_maximalIdeal_tensor_injective
        (A := R') (N := N) hmaximal_inj
  have hflat_w : Module.Flat Aw Nw := by
    -- Proof comment: the local criterion now applies directly to the lifted local map
    -- `Aw → S'`, using the transported residue-field `Tor₁` vanishing proved above.
    exact
      @flat_of_residueField_tor_one_vanishing Aw S' Nw
        _ _ algAwS' _ _ _ _ _ _ modS'Nw modAwNw hTower _ hTor_w
  -- Proof comment: descend the lifted flatness along `ULift.algEquiv` on the base ring and
  -- `ULift.moduleEquiv` on the base-changed module.
  simpa [Aw, Nw, N] using
    (ulift_flat_descend (A := R') (N := N) hflat_w)

end
