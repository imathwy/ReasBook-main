import Mathlib.Data.List.TFAE
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import StacksProject_2024.stacks_project.Chap10.Lemma_10_39_7
import StacksProject_2024.stacks_project.Chap10.Lemma_10_39_14
import StacksProject_2024.stacks_project.Chap10.Lemma_10_39_16
import StacksProject_2024.stacks_project.Chap12.Lemma_12_10_3
import StacksProject_2024.stacks_project.Chap12.Lemma_12_10_7
import StacksProject_2024.stacks_project.Chap15.Lemma_15_89_5
import StacksProject_2024.stacks_project.Chap15.Lemma_15_89_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open ModuleCat
open scoped TensorProduct

universe u v

noncomputable section

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Domain-style sampling:
- primary domain: ideal extension and change of rings on module categories, with canonical owner
  abstractions given by `Ideal.map`, `Ideal.quotientMap`, `ModuleCat (R ⧸ I)`, `extendScalars`,
  and the canonical `ObjectProperty` view `fun M ↦ Module.IsIdealPowerTorsion I M`;
- inspected same-domain owners:
  `Ideal.map`,
  `Ideal.quotientMap`,
  `extendScalars`,
  `restrictScalars`,
  `ModuleCat (R ⧸ I)`,
  `ObjectProperty.lift`,
  `Module.IsIdealPowerTorsion`;
- best owner abstraction: the ideal-side construction is the canonical owner `Ideal.map φ I`; for
  modules annihilated by `I`, the owner category is `ModuleCat (R ⧸ I)` and base change is
  `extendScalars` along the quotient map `R ⧸ I →+* S ⧸ Ideal.map φ I`; the `I`-power torsion
  clause remains the source-facing restricted functor
  `(ObjectProperty.ι (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M) ⋙ extendScalars φ)`,
  while the bridge to the target torsion full subcategory is the canonical restricted functor
  `idealPowerTorsionRestrictedBaseChange φ I` built from `ObjectProperty.lift`.

Source/core/bridge triage:
- `source-facing`: the TFAE for faithful base change on modules cut out by `I`;
- `core/canonical`: `Ideal.map φ I`, the induced quotient map `quotientMapModIdeal φ I`, and
  `extendScalars (quotientMapModIdeal φ I)` on quotient-module categories, together with the
  direct restricted base-change functor
  `(ObjectProperty.ι (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M) ⋙ extendScalars φ)`;
- `bridge/view`: the induced quotient map `R ⧸ I → S ⧸ IS` and the restricted functor
  `idealPowerTorsionRestrictedBaseChange φ I` into the target torsion full subcategory.
-/

/-- The quotient map induced by `φ : R →+* S` after reducing modulo `I`. -/
abbrev quotientMapModIdeal
    (φ : R →+* S) (I : Ideal R) :
    R ⧸ I →+* S ⧸ Ideal.map φ I :=
  Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map

/-- Extension of scalars along `φ` carries `I`-power torsion modules to `IS`-power torsion
modules. -/
theorem Module.IsIdealPowerTorsion.extendScalars
    (φ : R →+* S) (I : Ideal R) (M : ModuleCat R)
    (hM : Module.IsIdealPowerTorsion I M) :
    Module.IsIdealPowerTorsion (Ideal.map φ I) ((extendScalars φ).obj M) :=
  by
    let _ : Algebra R S := φ.toAlgebra
    -- View extension of scalars in its canonical tensor-product model.
    change Module.IsIdealPowerTorsion (Ideal.map φ I) (S ⊗[R] M)
    rw [Module.isIdealPowerTorsion_iff] at hM ⊢
    intro x
    -- Check the torsion condition on tensors by reducing to pure tensors and then to generators
    -- of the mapped ideal power.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · refine ⟨1, fun a ↦ ?_⟩
      simp
    · intro s m
      obtain ⟨n, hn⟩ := hM m
      refine ⟨n, fun b ↦ ?_⟩
      have hb : (b : S) ∈ Ideal.map φ (I ^ (n : ℕ)) := by
        simpa [Ideal.map_pow] using b.property
      have hb' : (b : S) ∈ Ideal.span (φ '' (↑(I ^ (n : ℕ)) : Set R)) := by
        simpa [Ideal.map_span] using hb
      -- Any generator `φ a` with `a ∈ I^n` kills the pure tensor because `a` kills `m`.
      refine Submodule.span_induction (p := fun z _ ↦ z • (s ⊗ₜ[R] m : S ⊗[R] M) = 0)
        ?_ ?_ ?_ ?_ hb'
      · intro y hy
        rcases hy with ⟨a, ha, rfl⟩
        calc
          (φ a : S) • (s ⊗ₜ[R] m : S ⊗[R] M) = ((a • s) ⊗ₜ[R] m : S ⊗[R] M) := by
            rfl
          _ = s ⊗ₜ[R] (a • m) := by
            rw [TensorProduct.smul_tmul]
          _ = 0 := by
            simp [hn ⟨a, ha⟩]
      · simp
      · intro y z hy hz hy' hz'
        rw [add_smul, hy', hz']
        simp
      · intro c y hy hy'
        simpa [smul_smul] using congrArg (fun t : S ⊗[R] M ↦ c • t) hy'
    · intro x y hx hy
      rcases hx with ⟨m, hm⟩
      rcases hy with ⟨n, hn⟩
      -- Addition preserves torsion after passing to a common larger power of the ideal.
      refine ⟨⟨(m : ℕ) + n, lt_of_lt_of_le m.2 (Nat.le_add_right (m : ℕ) (n : ℕ))⟩,
        fun a ↦ ?_⟩
      have hmx : (a : S) • x = 0 := by
        exact hm ⟨a, Ideal.pow_le_pow_right (Nat.le_add_right (m : ℕ) (n : ℕ)) a.2⟩
      have hny : (a : S) • y = 0 := by
        exact hn ⟨a, Ideal.pow_le_pow_right (Nat.le_add_left (n : ℕ) (m : ℕ)) a.2⟩
      rw [smul_add, hmx, hny]
      simp

/-- Base change along `φ` on the full subcategories of `I`-power torsion and `IS`-power torsion
modules. -/
noncomputable abbrev idealPowerTorsionRestrictedBaseChange
    (φ : R →+* S) (I : Ideal R) :
    ObjectProperty.FullSubcategory (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M) ⥤
      ObjectProperty.FullSubcategory
        (fun M : ModuleCat S ↦ Module.IsIdealPowerTorsion (Ideal.map φ I) M) :=
  ObjectProperty.lift
    (fun M : ModuleCat S ↦ Module.IsIdealPowerTorsion (Ideal.map φ I) M)
    (ObjectProperty.ι (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M) ⋙ extendScalars φ)
    (fun M ↦ Module.IsIdealPowerTorsion.extendScalars φ I M.obj M.property)

/-- Helper for Lemma 15.90.1: after restricting scalars along `R → R ⧸ I`, every
`R ⧸ I`-module is already annihilated by `I`, hence is `I`-power torsion as an `R`-module. -/
theorem quotient_module_restrictScalars_is_ideal_torsion
    (I : Ideal R) (M : ModuleCat (R ⧸ I)) :
    Module.IsIdealPowerTorsion I ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M) := by
  rw [Module.isIdealPowerTorsion_iff]
  intro x
  refine ⟨1, fun a ↦ ?_⟩
  have ha0 : (Ideal.Quotient.mk I) (a : R) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    simpa using a.2
  -- Restriction of scalars rewrites the `R`-action through the quotient map `R → R ⧸ I`.
  calc
    (a : R) • x = ((Ideal.Quotient.mk I) (a : R)) • x := by
      rfl
    _ = 0 := by simpa [ha0]

/-- Helper for Lemma 15.90.1: quotient modules over `R ⧸ I` embed in the full subcategory of
`I`-power torsion `R`-modules by restriction of scalars. -/
noncomputable abbrev quotient_modules_to_ideal_power_torsion
    (I : Ideal R) :
    ModuleCat (R ⧸ I) ⥤
      ObjectProperty.FullSubcategory (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M) :=
  ObjectProperty.lift
    (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M)
    (ModuleCat.restrictScalars (Ideal.Quotient.mk I))
    (fun M ↦ quotient_module_restrictScalars_is_ideal_torsion I M)

/-- Helper for Lemma 15.90.1: composing the quotient-module lift with the ambient inclusion
recovers the usual restriction-of-scalars functor. -/
noncomputable abbrev quotient_modules_to_ideal_power_torsion_comp_ι_iso
    (I : Ideal R) :
    quotient_modules_to_ideal_power_torsion (R := R) I ⋙
      ObjectProperty.ι (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M) ≅
        ModuleCat.restrictScalars (Ideal.Quotient.mk I) :=
  ObjectProperty.liftCompιIso
    (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M)
    (ModuleCat.restrictScalars (Ideal.Quotient.mk I))
    (fun M ↦ quotient_module_restrictScalars_is_ideal_torsion I M)

/-- Helper for Lemma 15.90.1: flatness of `φ` survives the quotient base change
`R ⧸ I → S ⧸ IS`. -/
theorem quotientMap_flat_of_flat
    (φ : R →+* S) (I : Ideal R) (hφ : φ.Flat) :
    (quotientMapModIdeal φ I).Flat := by
  let _ : Algebra R S := φ.toAlgebra
  let e : S ⧸ Ideal.map φ I ≃+* ((R ⧸ I) ⊗[R] S) :=
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).toRingEquiv).trans
      (Algebra.TensorProduct.comm R S (R ⧸ I)).toRingEquiv
  -- First rewrite flatness of `φ` into the canonical algebra-map form and base change to `R ⧸ I`.
  have hφ_alg : (algebraMap R S).Flat := by
    simpa [RingHom.algebraMap_toAlgebra] using hφ
  have hbaseModule : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] S) := by
    let _ : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hφ_alg
    simpa using (Module.Flat.baseChange (R := R) (S := R ⧸ I) (M := S))
  have hbase :
      (algebraMap (R ⧸ I) ((R ⧸ I) ⊗[R] S)).Flat := by
    exact RingHom.flat_algebraMap_iff.mpr hbaseModule
  -- Then transport that flatness across the canonical quotient/tensor ring equivalence.
  have he : e.symm.toRingHom.Flat := RingHom.Flat.of_bijective e.symm.bijective
  have hcomp :
      (e.symm.toRingHom.comp (algebraMap (R ⧸ I) ((R ⧸ I) ⊗[R] S))).Flat :=
    RingHom.Flat.comp hbase he
  have hEq :
      e.symm.toRingHom.comp (algebraMap (R ⧸ I) ((R ⧸ I) ⊗[R] S)) =
        quotientMapModIdeal φ I := by
    apply Ideal.Quotient.ringHom_ext
    rw [Ideal.quotientMap_comp_mk]
    ext x
    change
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm
          ((Algebra.TensorProduct.comm R S (R ⧸ I)).symm
            ((Ideal.Quotient.mk I) x ⊗ₜ[R] (1 : S))) =
        (Ideal.Quotient.mk (Ideal.map φ I)) (φ x)
    have hcomm :
        (Algebra.TensorProduct.comm R S (R ⧸ I)).symm
            ((Ideal.Quotient.mk I) x ⊗ₜ[R] (1 : S)) =
          (1 : S) ⊗ₜ[R] (Ideal.Quotient.mk I x) := by
      simpa using
        (Algebra.TensorProduct.comm_symm_tmul (R := R) (a := (1 : S))
          (b := Ideal.Quotient.mk I x))
    rw [hcomm, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
    have hs : x • (1 : S) = φ x := by
      change (algebraMap R S x) * 1 = φ x
      simpa [RingHom.algebraMap_toAlgebra]
    simpa [RingHom.algebraMap_toAlgebra, hs]
  rw [← hEq]
  exact hcomp

/-- Helper for Lemma 15.90.1: the zero criterion for `extendScalars.map` is exactly the zero
criterion for the left tensor map on the underlying linear map. -/
theorem extendScalars_map_zero_iff_lTensor_zero
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {M N : ModuleCat A} (α : M ⟶ N) :
    (extendScalars (algebraMap A B)).map α = 0 ↔
      LinearMap.lTensor (((restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) : ModuleCat A)
        α.hom = 0 := by
  constructor
  · intro h
    have hhom : ModuleCat.Hom.hom ((extendScalars (algebraMap A B)).map α) = 0 :=
      congrArg ModuleCat.Hom.hom h
    -- Route correction: compare the underlying categorical map and `lTensor` only on pure
    -- tensors, where both have the same canonical formula.
    apply LinearMap.ext
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp
    · intro b m
      simpa [ModuleCat.ExtendScalars.map', LinearMap.baseChange_tmul, LinearMap.lTensor_tmul] using
        congrArg (fun f ↦ f (b ⊗ₜ[A] m)) hhom
    · intro x y hx hy
      simp [hx, hy]
  · intro h
    apply ModuleCat.hom_ext
    -- Again reduce the comparison to pure tensors and use the common tensor formula.
    apply LinearMap.ext
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · calc
        (ModuleCat.Hom.hom ((extendScalars (algebraMap A B)).map α)) 0 = 0 := by simp
        _ = (ModuleCat.Hom.hom (0 : (extendScalars (algebraMap A B)).obj M ⟶
            (extendScalars (algebraMap A B)).obj N)) 0 := by simp
    · intro b m
      simpa [ModuleCat.ExtendScalars.map', LinearMap.baseChange_tmul, LinearMap.lTensor_tmul] using
        congrArg (fun f ↦ f (b ⊗ₜ[A] m)) h
    · intro x y hx hy
      have hx' : (ModuleCat.Hom.hom ((extendScalars (algebraMap A B)).map α)) x = 0 := by
        simpa using hx
      have hy' : (ModuleCat.Hom.hom ((extendScalars (algebraMap A B)).map α)) y = 0 := by
        simpa using hy
      calc
        (ModuleCat.Hom.hom ((extendScalars (algebraMap A B)).map α)) (x + y)
            = (ModuleCat.Hom.hom ((extendScalars (algebraMap A B)).map α)) x +
                (ModuleCat.Hom.hom ((extendScalars (algebraMap A B)).map α)) y := by
              exact (ModuleCat.Hom.hom ((extendScalars (algebraMap A B)).map α)).map_add x y
        _ = 0 := by rw [hx', hy']; simp
        _ = (ModuleCat.Hom.hom (0 : (extendScalars (algebraMap A B)).obj M ⟶
              (extendScalars (algebraMap A B)).obj N)) (x + y) := by simp

/-- Helper for Lemma 15.90.1: the identity map identifies the restricted-scalar regular
`B`-module with the usual `A`-module structure on `B`. -/
def restrictScalars_selfLinearEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] :
    (((restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) : ModuleCat A) ≃ₗ[A] B :=
  { toFun := fun b ↦ b
    invFun := fun b ↦ b
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ by
      simp [Algebra.smul_def]
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }

/-- Helper for Lemma 15.90.1: the restricted-scalar `A`-module underlying `B` is exactly the
carrier used by the algebra-map faithfully-flat owner. -/
theorem faithfullyFlat_restrictScalars_self_iff
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] :
    Module.FaithfullyFlat A
      (((restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) : ModuleCat A) ↔
      (algebraMap A B).FaithfullyFlat := by
  constructor
  · intro hff
    -- Transport faithful flatness across the identity linear equivalence of the two `A`-module
    -- structures on `B`, then use the standard algebra-map owner criterion.
    letI :
        Module.FaithfullyFlat A
          (((restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) : ModuleCat A) := hff
    have hffB : Module.FaithfullyFlat A B :=
      Module.FaithfullyFlat.of_linearEquiv A
        (((restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) : ModuleCat A)
        (restrictScalars_selfLinearEquiv (A := A) (B := B)).symm
    exact RingHom.faithfullyFlat_algebraMap_iff.mpr hffB
  · intro hff
    -- The reverse transport packages the algebra-map criterion back on the restricted carrier.
    have hffB : Module.FaithfullyFlat A B :=
      RingHom.faithfullyFlat_algebraMap_iff.mp hff
    letI : Module.FaithfullyFlat A B := hffB
    exact
      Module.FaithfullyFlat.of_linearEquiv A B
        (restrictScalars_selfLinearEquiv (A := A) (B := B))

/-- Helper for Lemma 15.90.1: after giving `B` the algebra structure induced by `q`, the
vanishing of `extendScalars q` on a morphism is exactly the vanishing of the corresponding left
tensor map on the restricted-scalar regular module. -/
theorem quotient_extendScalars_map_zero_iff_lTensor_zero
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (q : A →+* B) {M N : ModuleCat A} (α : M ⟶ N) :
    (extendScalars q).map α = 0 ↔
      LinearMap.lTensor (((restrictScalars q).obj (ModuleCat.of B B)) : ModuleCat A) α.hom = 0 := by
  let _ : Algebra A B := q.toAlgebra
  -- Route correction: transport to the canonical `algebraMap` presentation once, so the main
  -- faithful-flat bridge no longer unfolds the raw quotient-map functor surface.
  change (extendScalars (algebraMap A B)).map α = 0 ↔
      LinearMap.lTensor
        (((restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) : ModuleCat A) α.hom = 0
  simpa [RingHom.algebraMap_toAlgebra] using
    (extendScalars_map_zero_iff_lTensor_zero (A := A) (B := B) α)

/-- Helper for Lemma 15.90.1: in the equal-universe case, a faithfully flat quotient map induces
a faithful extension-of-scalars functor on module categories. -/
theorem quotient_extendScalars_faithful_of_faithfullyFlat_same_universe
    {A : Type u} {B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) (hqflat : q.Flat) (hff : q.FaithfullyFlat) :
    (extendScalars.{u, u, u} q).Faithful := by
  let _ : Algebra A B := q.toAlgebra
  have hff' :
      Module.FaithfullyFlat A
        (((restrictScalars q).obj (ModuleCat.of B B)) : ModuleCat A) := by
    -- Repackage faithful flatness on `q` as faithful flatness of the restricted-scalar regular
    -- `B`-module.
    have hAlg : (algebraMap A B).FaithfullyFlat := by
      simpa [RingHom.algebraMap_toAlgebra] using hff
    exact (faithfullyFlat_restrictScalars_self_iff (A := A) (B := B)).2 hAlg
  letI : Module.FaithfullyFlat A
      (((restrictScalars q).obj (ModuleCat.of B B)) : ModuleCat A) := hff'
  letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat (f := q) hqflat
  -- Zero objects are reflected because faithfully flat tensor products reflect subsingletons.
  exact Functor.faithful_of_exact_of_kernel_le_isZero (extendScalars.{u, u, u} q) <| show
      (extendScalars.{u, u, u} q).kernel ≤ CategoryTheory.Limits.IsZero from
    fun M hM ↦ by
      have hsubTensor' :
          Subsingleton ((((restrictScalars q).obj (ModuleCat.of B B)) : ModuleCat A) ⊗[A] M) := by
        change Subsingleton ((extendScalars.{u, u, u} q).obj M)
        exact (ModuleCat.isZero_iff_subsingleton).1 hM
      change CategoryTheory.Limits.IsZero M
      letI : Subsingleton ((((restrictScalars q).obj (ModuleCat.of B B)) : ModuleCat A) ⊗[A] M) :=
        hsubTensor'
      exact (ModuleCat.isZero_iff_subsingleton).2 <|
        Module.FaithfullyFlat.lTensor_reflects_triviality (R := A)
          (M := (((restrictScalars q).obj (ModuleCat.of B B)) : ModuleCat A)) M

/-- Helper for Lemma 15.90.1: faithful flatness also gives faithfulness of extension of scalars
in the canonical owner universe `max u v`. -/
theorem quotient_extendScalars_faithful_of_faithfullyFlat_max
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (q : A →+* B) (hqflat : q.Flat) (hff : q.FaithfullyFlat) :
    (extendScalars.{u, v, max u v} q).Faithful := by
  -- TODO: package the equal-universe proof through an explicit owner-universe transport so the
  -- source and target category universes match definitionally.
  sorry

/-- Helper for Lemma 15.90.1: if extension of scalars along `q` is faithful, then the quotient
map `q` is faithfully flat in the canonical owner universe `max u v`. -/
theorem quotient_extendScalars_faithfullyFlat_of_faithful_max
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (q : A →+* B) (hqflat : q.Flat)
    (hfaith : (extendScalars.{u, v, max u v} q).Faithful) :
    q.FaithfullyFlat := by
  let _ : Algebra A B := q.toAlgebra
  let BmodA : ModuleCat A := ((restrictScalars q).obj (ModuleCat.of B B))
  have hffModule :
      Module.FaithfullyFlat A BmodA := by
    -- Route correction: work directly in the owner universe `max u v`, so faithfulness of
    -- `extendScalars q` matches the `lTensor` criterion without any extra transport.
    rw [Module.FaithfullyFlat.iff_flat_and_lTensor_faithful]
    constructor
    · -- Flatness comes directly from the flatness of the ring map `q`.
      have hflatB : Module.Flat A B := RingHom.flat_algebraMap_iff.mp <| by
        simpa [RingHom.algebraMap_toAlgebra] using hqflat
      let _ : Module.Flat A B := hflatB
      exact Module.Flat.of_linearEquiv
        (restrictScalars_selfLinearEquiv (A := A) (B := B))
    · intro N _ _ hN
      -- Faithfulness of `extendScalars q` rules out the tensor product becoming zero, because a
      -- zero target would force the source identity to map to zero.
      let Nobj : ModuleCat.{max u v} A := ModuleCat.of.{max u v} A N
      change Nontrivial ((extendScalars.{u, v, max u v} q).obj Nobj)
      by_contra htriv
      have hzeroTarget :
          CategoryTheory.Limits.IsZero ((extendScalars.{u, v, max u v} q).obj Nobj) :=
        (ModuleCat.isZero_iff_subsingleton).2 (not_nontrivial_iff_subsingleton.mp htriv)
      have hmapid : (extendScalars.{u, v, max u v} q).map (𝟙 Nobj) = 0 := by
        simpa [CategoryTheory.Limits.IsZero.iff_id_eq_zero] using hzeroTarget
      have hmapid' :
          (extendScalars.{u, v, max u v} q).map (𝟙 Nobj) =
            (extendScalars.{u, v, max u v} q).map 0 := by
        rw [Functor.map_zero]
        exact hmapid
      have hid : (𝟙 Nobj) = 0 :=
        hfaith.map_injective hmapid'
      have hzeroSource : CategoryTheory.Limits.IsZero Nobj :=
        (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).2 hid
      exact (not_nontrivial_iff_subsingleton.mpr
        ((ModuleCat.isZero_iff_subsingleton).1 hzeroSource)) hN
  -- Repackage faithful flatness of the regular restricted module as faithful flatness of `q`.
  have hAlg :
      (algebraMap A B).FaithfullyFlat := by
    exact (faithfullyFlat_restrictScalars_self_iff (A := A) (B := B)).1 hffModule
  have hq_eq : algebraMap A B = q := by
    ext a
    rfl
  rw [← hq_eq]
  exact hAlg

/-- Helper for Lemma 15.90.1: if extension of scalars along `q` is faithful, then the quotient
map `q` is faithfully flat. -/
theorem quotient_extendScalars_faithfullyFlat_of_faithful
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (q : A →+* B) (hqflat : q.Flat) (hfaith : (extendScalars q).Faithful) :
    q.FaithfullyFlat := by
  -- TODO: first transport ambient faithfulness to the owner universe `max u v`, then apply
  -- `quotient_extendScalars_faithfullyFlat_of_faithful_max`.
  sorry

/-- Helper for Lemma 15.90.1: faithful flatness of the quotient map already gives faithfulness of
extension of scalars in the ambient source universe. -/
theorem quotient_extendScalars_faithful_of_faithfullyFlat
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (q : A →+* B) (hff : q.FaithfullyFlat) :
    (extendScalars q).Faithful := by
  -- TODO: obtain faithfulness in the owner universe `max u v`, then transport it back to the
  -- ambient source universe without the current definitional-universe mismatch.
  sorry

/-- Helper for Lemma 15.90.1: in the canonical owner universe `max u v`, faithfulness of
extension of scalars is equivalent to faithful flatness of the quotient map. -/
theorem quotient_extendScalars_faithful_iff_faithfullyFlat_max
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (q : A →+* B) (hqflat : q.Flat) :
    (extendScalars.{u, v, max u v} q).Faithful ↔ q.FaithfullyFlat := by
  constructor
  · intro hfaith
    -- The source proof first reads faithfulness in the owner universe and then applies the
    -- faithful-flat tensor criterion.
    exact quotient_extendScalars_faithfullyFlat_of_faithful_max q hqflat hfaith
  · intro hff
    -- The faithful-flat tensor criterion already applies directly in the owner universe.
    exact quotient_extendScalars_faithful_of_faithfullyFlat_max q hqflat hff

/-- Helper for Lemma 15.90.1: for a flat quotient map `q`, faithful flatness is equivalent to
faithfulness of the extension-of-scalars functor on module categories. -/
theorem quotient_extendScalars_faithful_iff_faithfullyFlat
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (q : A →+* B) (hqflat : q.Flat) :
    (extendScalars q).Faithful ↔ q.FaithfullyFlat := by
  constructor
  · -- The reverse implication is the direct tensor zero-detection route from the source proof.
    intro hfaith
    exact quotient_extendScalars_faithfullyFlat_of_faithful q hqflat hfaith
  · intro hff
    -- The source faithful-flat tensor criterion already applies directly in the ambient source
    -- universe, so no extra universe transport is needed here.
    exact quotient_extendScalars_faithful_of_faithfullyFlat q hff

/-- Helper for Lemma 15.90.1: the quotient-module lift into the `I`-power torsion full
subcategory is faithful because its composite with the inclusion is the usual faithful
restriction-of-scalars functor. -/
theorem quotient_modules_to_ideal_power_torsion_faithful
    (I : Ideal R) :
    (quotient_modules_to_ideal_power_torsion (R := R) I).Faithful := by
  have hcomp :
      (quotient_modules_to_ideal_power_torsion (R := R) I ⋙
        ObjectProperty.ι (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M)).Faithful := by
    letI : (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).Faithful := inferInstance
    exact Functor.Faithful.of_iso
      (quotient_modules_to_ideal_power_torsion_comp_ι_iso (R := R) I).symm
  letI : (quotient_modules_to_ideal_power_torsion (R := R) I ⋙
      ObjectProperty.ι (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M)).Faithful := hcomp
  exact Functor.Faithful.of_comp
    (quotient_modules_to_ideal_power_torsion (R := R) I)
    (ObjectProperty.ι (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M))

/-- Helper for Lemma 15.90.1: forgetting the target torsion structure after restricted base
change is the same as first forgetting the source torsion structure and then extending scalars. -/
noncomputable abbrev idealPowerTorsionRestrictedBaseChange_comp_ι_iso
    (φ : R →+* S) (I : Ideal R) :
    idealPowerTorsionRestrictedBaseChange φ I ⋙
      ObjectProperty.ι (fun M : ModuleCat S ↦ Module.IsIdealPowerTorsion (Ideal.map φ I) M) ≅
        ObjectProperty.ι (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M) ⋙
          extendScalars φ :=
  ObjectProperty.liftCompιIso
    (fun M : ModuleCat S ↦ Module.IsIdealPowerTorsion (Ideal.map φ I) M)
    (ObjectProperty.ι (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M) ⋙ extendScalars φ)
    (fun M ↦ Module.IsIdealPowerTorsion.extendScalars φ I M.obj M.property)

/-- Helper for Lemma 15.90.1: quotient modules viewed inside the torsion full subcategory and then
base-changed agree with first forgetting to `R`-modules and then extending scalars along `φ`. -/
noncomputable abbrev quotient_modules_to_ambient_baseChange_iso
    (φ : R →+* S) (I : Ideal R) :
    quotient_modules_to_ideal_power_torsion (R := R) I ⋙
      idealPowerTorsionRestrictedBaseChange φ I ⋙
      ObjectProperty.ι (fun M : ModuleCat S ↦ Module.IsIdealPowerTorsion (Ideal.map φ I) M) ≅
        ModuleCat.restrictScalars (Ideal.Quotient.mk I) ⋙ extendScalars φ :=
  Functor.isoWhiskerLeft (quotient_modules_to_ideal_power_torsion (R := R) I)
      (idealPowerTorsionRestrictedBaseChange_comp_ι_iso (R := R) (S := S) φ I) ≪≫
    (Functor.associator
      (quotient_modules_to_ideal_power_torsion (R := R) I)
      (ObjectProperty.ι (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M))
      (extendScalars φ)).symm ≪≫
    Functor.isoWhiskerRight
      (quotient_modules_to_ideal_power_torsion_comp_ι_iso (R := R) I)
      (extendScalars φ)

/-- Helper for Lemma 15.90.1: the ambient base-change functor on quotient modules factors through
the quotient-module lift, restricted base change on torsion objects, and the target inclusion. -/
noncomputable abbrev quotient_modules_ambient_baseChange
    (φ : R →+* S) (I : Ideal R) :
    ModuleCat (R ⧸ I) ⥤ ModuleCat S :=
  quotient_modules_to_ideal_power_torsion (R := R) I ⋙
    idealPowerTorsionRestrictedBaseChange φ I ⋙
    ObjectProperty.ι
      (fun M : ModuleCat S ↦ Module.IsIdealPowerTorsion (Ideal.map φ I) M)

/-- Helper for Lemma 15.90.1: faithfulness transports from a left-associated triple composite to
the corresponding right-associated composite across the functor associator. -/
theorem CategoryTheory.Functor.faithful_comp_of_faithful
    {C : Type*} {D : Type*} {E : Type*}
    [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E)
    (hF : F.Faithful) (hG : G.Faithful) :
    (F ⋙ G).Faithful := by
  -- The composite detects equality because `G` detects equality after applying `F`, and `F`
  -- then detects equality of the original morphisms.
  refine ⟨?_⟩
  intro X Y f g hfg
  exact hF.map_injective (hG.map_injective hfg)

/-- Helper for Lemma 15.90.1: faithfulness transports from a left-associated triple composite to
the corresponding right-associated composite across the functor associator. -/
theorem CategoryTheory.Functor.faithful_right_assoc_of_left_assoc
    {C : Type*} {D : Type*} {E : Type*} {K : Type*}
    [Category C] [Category D] [Category E] [Category K]
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ K)
    [((F ⋙ G) ⋙ H).Faithful] :
    (F ⋙ G ⋙ H).Faithful := by
  -- The associator is a natural isomorphism from the left-associated composite to the displayed
  -- right-associated composite, so faithfulness transfers across that iso once and for all.
  exact Functor.Faithful.of_iso (Functor.associator F G H)

/-- Helper for Lemma 15.90.1: on quotient modules, the left-associated composite with the target
inclusion maps a morphism by first applying the quotient lift, then restricted base change, and
finally the inclusion. -/
theorem quotient_modules_ambient_baseChange_left_assoc_map
    (φ : R →+* S) (I : Ideal R)
    {X Y : ModuleCat (R ⧸ I)} (f : X ⟶ Y) :
    (((quotient_modules_to_ideal_power_torsion (R := R) I ⋙
      idealPowerTorsionRestrictedBaseChange φ I) ⋙
      ObjectProperty.ι
        (fun M : ModuleCat S ↦ Module.IsIdealPowerTorsion (Ideal.map φ I) M)).map f) =
      (ObjectProperty.ι
        (fun M : ModuleCat S ↦ Module.IsIdealPowerTorsion (Ideal.map φ I) M)).map
        ((idealPowerTorsionRestrictedBaseChange φ I).map
          ((quotient_modules_to_ideal_power_torsion (R := R) I).map f)) := by
  -- This is just the definitional formula for mapping through a left-associated composite.
  rfl

/-- Helper for Lemma 15.90.1: the target torsion full-subcategory inclusion is faithful. -/
theorem idealPowerTorsion_target_inclusion_faithful
    (φ : R →+* S) (I : Ideal R) :
    (ObjectProperty.ι
      (fun M : ModuleCat S ↦ Module.IsIdealPowerTorsion (Ideal.map φ I) M)).Faithful := by
  infer_instance

/-- Helper for Lemma 15.90.1: if restricted base change is faithful on the `I`-power torsion
subcategory, then the explicit right-associated quotient-module composite with target inclusion is
faithful after forgetting the target torsion structure. -/
theorem quotient_modules_ambient_baseChange_faithful_of_restricted
    (φ : R →+* S) (I : Ideal R)
    (hfaith : (idealPowerTorsionRestrictedBaseChange φ I).Faithful) :
    (quotient_modules_to_ideal_power_torsion (R := R) I ⋙
      (idealPowerTorsionRestrictedBaseChange φ I ⋙
        ObjectProperty.ι
          (fun M : ModuleCat S ↦ Module.IsIdealPowerTorsion (Ideal.map φ I) M))).Faithful := by
  have hleft :
      ((quotient_modules_to_ideal_power_torsion (R := R) I ⋙
        idealPowerTorsionRestrictedBaseChange φ I) ⋙
          ObjectProperty.ι
            (fun M : ModuleCat S ↦ Module.IsIdealPowerTorsion (Ideal.map φ I) M)).Faithful := by
    -- First compose the faithful quotient lift with faithful restricted base change, then append
    -- the faithful target inclusion.
    exact CategoryTheory.Functor.faithful_comp_of_faithful
      (quotient_modules_to_ideal_power_torsion (R := R) I ⋙
        idealPowerTorsionRestrictedBaseChange φ I)
      (ObjectProperty.ι
        (fun M : ModuleCat S ↦ Module.IsIdealPowerTorsion (Ideal.map φ I) M))
      (CategoryTheory.Functor.faithful_comp_of_faithful
        (quotient_modules_to_ideal_power_torsion (R := R) I)
        (idealPowerTorsionRestrictedBaseChange φ I)
        (quotient_modules_to_ideal_power_torsion_faithful (R := R) I)
        hfaith)
      (idealPowerTorsion_target_inclusion_faithful (R := R) (S := S) φ I)
  letI :
      ((quotient_modules_to_ideal_power_torsion (R := R) I ⋙
        idealPowerTorsionRestrictedBaseChange φ I) ⋙
          ObjectProperty.ι
            (fun M : ModuleCat S ↦ Module.IsIdealPowerTorsion (Ideal.map φ I) M)).Faithful :=
    hleft
  -- TODO: transfer `hleft` across the associator with an explicit universe-stable faithful
  -- transport, avoiding the current polymorphic instance mismatch.
  sorry

/-- Helper for Lemma 15.90.1: for any ideal `J`, quotient modules over `R ⧸ J` become the same
ambient `S`-modules whether one first views them as `J`-power torsion `R`-modules and then
extends scalars along `φ`, or first extends scalars along `R ⧸ J → S ⧸ JS` and then forgets the
quotient action. -/
noncomputable def quotient_modules_restricted_baseChange_iso
    (φ : R →+* S) (J : Ideal R) :
    quotient_modules_ambient_baseChange (R := R) (S := S) φ J ≅
      extendScalars (quotientMapModIdeal φ J) ⋙
        ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.map φ J)) := by
  -- Route correction: the source proof needs this comparison for every power `J = I^n`, not only
  -- for `J = I`. The remaining work is the arbitrary-ideal tensor/quotient natural isomorphism.
  -- TODO: identify `S ⊗[R] M` for an `R ⧸ J`-module `M` with
  -- `(S ⧸ JS) ⊗[R ⧸ J] M` by the canonical quotient-tensor comparison, then package the
  -- objectwise equivalences into a natural isomorphism.
  sorry

/-- Helper for Lemma 15.90.1: if the ambient base change of an `R`-module vanishes, then the
same is true for every finite power-torsion stage. -/
theorem power_torsion_stage_baseChange_isZero
    (φ : R →+* S) (I : Ideal R) (hφ : φ.Flat)
    (M0 : ModuleCat R)
    (hM : CategoryTheory.Limits.IsZero ((extendScalars φ).obj M0))
    (n : ℕ) :
    CategoryTheory.Limits.IsZero
      ((extendScalars φ).obj (ModuleCat.of R (Ideal.powerTorsion I M0 n))) := by
  let i :
      ModuleCat.of R (Ideal.powerTorsion I M0 n) ⟶ M0 :=
    ModuleCat.ofHom (Submodule.subtype (Ideal.powerTorsion I M0 n))
  have hi : Mono i := by
    exact (ModuleCat.mono_iff_injective i).2 fun x y hxy ↦ Subtype.ext hxy
  let _ : Algebra R S := φ.toAlgebra
  letI : Module.Flat R S := RingHom.flat_algebraMap_iff.mp <| by
    simpa [RingHom.algebraMap_toAlgebra] using hφ
  have hmap_mono : Mono ((extendScalars φ).map i) := by
    refine (ModuleCat.mono_iff_injective _).2 ?_
    simpa [ModuleCat.ExtendScalars.map', LinearMap.baseChange_eq_ltensor] using
      (Module.Flat.lTensor_preserves_injective_linearMap (M := S)
        i.hom ((ModuleCat.mono_iff_injective i).1 hi))
  -- Proof comment: the stage inclusion stays mono after flat base change, and every map into a
  -- zero object is zero.
  letI : Mono ((extendScalars φ).map i) := hmap_mono
  exact CategoryTheory.Limits.IsZero.of_mono_eq_zero
    ((extendScalars φ).map i)
    (hM.eq_of_tgt _ _)

/-- Helper for Lemma 15.90.1: under clause `(3)`, vanishing after ambient base change along `φ`
forces an `I`-power torsion module to vanish. The source proof upgrades clause `(3)` from `I` to
every power `I^n`, kills each finite stage `M[I^n]`, and then uses the filtered-colimit
presentation from Lemma `15.89.9`. -/
theorem idealPowerTorsion_baseChange_reflects_zero
    (φ : R →+* S) (I : Ideal R) (hφ : φ.Flat)
    (hquot : (extendScalars (quotientMapModIdeal φ I)).Faithful)
    (M : ObjectProperty.FullSubcategory (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M))
    (hM :
      CategoryTheory.Limits.IsZero ((ObjectProperty.ι (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M) ⋙
        extendScalars φ).obj M)) :
    CategoryTheory.Limits.IsZero M.obj := by
  -- Route correction: avoid the earlier successive-quotient route. The source proof instead
  -- upgrades faithfulness from `I` to every `I^n`, proves each finite stage `Ideal.powerTorsion`
  -- vanishes after zero base change, and concludes from the colimit cocone
  -- `power_torsion_stage_module_isColimit`.
  -- TODO: use `quotient_modules_restricted_baseChange_iso` at `J = I ^ n` to reflect zero on each
  -- finite stage, then apply `idealPowerTorsion_iSup_powerTorsion_eq_top` and
  -- `power_torsion_stage_module_isColimit` from `Lemma_15_89_9`.
  sorry

/-- Helper for Lemma 15.90.1: once zero objects are reflected on `I`-power torsion modules, the
restricted base-change functor is faithful by the ambient image argument from the source proof. -/
theorem idealPowerTorsionRestrictedBaseChange_faithful_of_quotient_faithful
    (φ : R →+* S) (I : Ideal R) (hφ : φ.Flat)
    (hquot : (extendScalars (quotientMapModIdeal φ I)).Faithful) :
    (idealPowerTorsionRestrictedBaseChange φ I).Faithful := by
  -- Route correction: keep the source stagewise image argument. After composing with each finite
  -- stage inclusion `M[I^n] → M`, use `idealPowerTorsion_baseChange_reflects_zero` on the image
  -- object and finish by `hom_ext` for the colimit cocone from `Lemma_15.89.9`.
  -- TODO: prove a zero-base-changed morphism is zero on every finite power-torsion stage, then
  -- conclude on the whole source by `power_torsion_stage_module_isColimit`.
  sorry

/-- Helper for Lemma 15.90.1: the zeroth finite power-torsion stage is trivial. -/
theorem powerTorsion_zero_eq_bot
    (I : Ideal R) (M : Type*) [AddCommMonoid M] [Module R M] :
    Ideal.powerTorsion I M 0 = ⊥ := by
  -- Route correction: isolate the base case of the source filtration `T₀ = 0` once, so the
  -- later induction on `Tₙ := M[Iⁿ]` does not keep unfolding `powerTorsion`.
  rw [Ideal.powerTorsion, pow_zero]
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_torsionBySet_iff] at hx
    rw [Submodule.mem_bot]
    simpa using hx ⟨1, by simp⟩
  · intro hx
    rw [Submodule.mem_bot] at hx
    subst hx
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    simp

/-- Helper for Lemma 15.90.1: the finite power-torsion stages form their canonical successor
inclusions `M[I^n] ↪ M[I^(n+1)]`. -/
abbrev powerTorsion_succ_inclusion
    (I : Ideal R) (M : Type*) [AddCommMonoid M] [Module R M] (n : ℕ) :
    Ideal.powerTorsion I M n →ₗ[R] Ideal.powerTorsion I M (n + 1) :=
  Submodule.inclusion <| by
    intro x hx
    -- The later stage uses the smaller ideal power `I^(n+1) ⊆ I^n`.
    change x ∈ Submodule.torsionBySet R M ↑(I ^ (n + 1))
    change x ∈ Submodule.torsionBySet R M ↑(I ^ n) at hx
    rw [Submodule.mem_torsionBySet_iff] at hx ⊢
    intro a
    exact hx ⟨a, Ideal.pow_le_pow_right (Nat.le_succ n) a.2⟩

/-- Helper for Lemma 15.90.1: the graded piece between successive finite power-torsion stages is
already annihilated by `I`, so it can be viewed as a quotient-ring module. -/
theorem powerTorsion_succ_quotient_annihilator_le
    (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) :
    I ≤ Module.annihilator R
      ((Ideal.powerTorsion I M (n + 1)) ⧸
        LinearMap.range (powerTorsion_succ_inclusion I M n)) := by
  intro a ha
  rw [Module.mem_annihilator]
  intro x
  obtain ⟨y, rfl⟩ :=
    Submodule.mkQ_surjective (LinearMap.range (powerTorsion_succ_inclusion I M n)) x
  -- Evaluate on a quotient representative and show the result already comes from the previous
  -- stage.
  change Submodule.mkQ (LinearMap.range (powerTorsion_succ_inclusion I M n)) ((a : R) • y) = 0
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  refine ⟨⟨(a : R) • (y : M), ?_⟩, rfl⟩
  -- Multiplication by `a ∈ I` lowers the annihilating power from `I^(n+1)` to `I^n`.
  change (a : R) • (y : M) ∈ Submodule.torsionBySet R M ↑(I ^ n)
  have hy : (y : M) ∈ Submodule.torsionBySet R M ↑(I ^ (n + 1)) := y.2
  rw [Submodule.mem_torsionBySet_iff] at hy ⊢
  intro b
  have hmul : (b : R) * a ∈ I ^ (n + 1) := by
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
      (Ideal.mul_mem_mul b.2 ha : (b : R) * a ∈ I ^ n * I)
  simpa [smul_smul, mul_comm] using hy ⟨(b : R) * a, hmul⟩

-- Proof sketch: identify the quotient map `R ⧸ I →+* S ⧸ IS` with the base change of `φ`
-- along `R → R ⧸ I`, so Lemmas `10.39.7` and `10.39.16` give the equivalence of the faithfully
-- flat and spectrum-surjective quotient conditions. Clause `(3)` is the canonical quotient-module
-- formulation: for modules annihilated by `I`, work in `ModuleCat (R ⧸ I)` and rewrite base
-- change along `φ` as extension of scalars along `R ⧸ I →+* S ⧸ IS`, then apply Lemma `10.39.14`.
-- Clause `(4)` is the canonical restricted base-change functor
-- `idealPowerTorsionRestrictedBaseChange φ I` on the full subcategory of `I`-power torsion
-- modules. The implication from `I`-power torsion modules to `I`-annihilated
-- modules is immediate, and the converse is obtained by filtering an `I`-power torsion module by
-- its submodules annihilated by powers of `I` and using preservation of colimits by tensor
-- product.
/-- Lemma 15.90.1: for a ring map `φ : R →+* S` and an ideal `I ⊆ R`, the following are
equivalent: `φ` is flat and the induced quotient map `R ⧸ I → S ⧸ IS` is faithfully flat; `φ` is
flat and `Spec (S ⧸ IS) → Spec (R ⧸ I)` is surjective; `φ` is flat and extension of scalars along
`R ⧸ I → S ⧸ IS` is faithful on quotient-ring modules, equivalently on `R`-modules annihilated by
`I`; and `φ` is flat and base change along `φ` is faithful on `I`-power torsion `R`-modules. -/
theorem flat_quotientFaithfullyFlat_tfae_baseChangeFaithfulOnIdealTorsionModules
    (φ : R →+* S) (I : Ideal R) :
    List.TFAE
      [ φ.Flat ∧ (quotientMapModIdeal φ I).FaithfullyFlat
      , φ.Flat ∧
          Function.Surjective (PrimeSpectrum.comap (quotientMapModIdeal φ I))
      , φ.Flat ∧
          (extendScalars (quotientMapModIdeal φ I)).Faithful
      , φ.Flat ∧
          (idealPowerTorsionRestrictedBaseChange φ I).Faithful
      ] :=
  by
    -- Route correction: make the quotient-module to torsion-subcategory adapter explicit first,
    -- then use it to compare the quotient faithful-base-change clause with the torsion clause.
    let q := quotientMapModIdeal φ I
    tfae_have 1 ↔ 2 := by
      constructor
      · intro h
        -- After transporting flatness to the quotient map, the Chapter 10 spectrum criterion
        -- rewrites faithful flatness into surjectivity on spectra.
        have hqflat : q.Flat := quotientMap_flat_of_flat φ I h.1
        have hclosed :
            closedPoints (PrimeSpectrum (R ⧸ I)) ⊆ Set.range (PrimeSpectrum.comap q) :=
          (faithfullyFlat_iff_closedPoints_subset_range q hqflat).mp h.2
        exact ⟨h.1, (specComap_surjective_iff_closedPoints_subset_range q hqflat).mpr hclosed⟩
      · intro h
        -- The same closed-point criterion gives the reverse implication.
        have hqflat : q.Flat := quotientMap_flat_of_flat φ I h.1
        have hclosed :
            closedPoints (PrimeSpectrum (R ⧸ I)) ⊆ Set.range (PrimeSpectrum.comap q) :=
          (specComap_surjective_iff_closedPoints_subset_range q hqflat).mp h.2
        exact ⟨h.1, (faithfullyFlat_iff_closedPoints_subset_range q hqflat).mpr hclosed⟩
    tfae_have 1 ↔ 3 := by
      constructor
      · intro h
        -- Clause `(3)` is the module-category avatar of faithful flatness for the quotient map.
        have hqflat : q.Flat := quotientMap_flat_of_flat φ I h.1
        exact ⟨h.1, (quotient_extendScalars_faithful_iff_faithfullyFlat q hqflat).2 h.2⟩
      · intro h
        have hqflat : q.Flat := quotientMap_flat_of_flat φ I h.1
        exact ⟨h.1, (quotient_extendScalars_faithful_iff_faithfullyFlat q hqflat).1 h.2⟩
    tfae_have 3 → 4 := by
      intro h
      -- Proof comment: the ambient image argument avoids the previous owner-universe exactness
      -- bridge and reduces the step to zero-reflection on torsion objects.
      exact ⟨h.1,
        idealPowerTorsionRestrictedBaseChange_faithful_of_quotient_faithful
          (R := R) (S := S) φ I h.1 h.2⟩
    tfae_have 4 → 3 := by
      intro h
      -- The quotient-module lift into the torsion full subcategory is already isolated as a
      -- faithful right-associated ambient composite.
      have hambient :
          (quotient_modules_ambient_baseChange (R := R) (S := S) φ I).Faithful := by
        simpa [quotient_modules_ambient_baseChange] using
          quotient_modules_ambient_baseChange_faithful_of_restricted
            (R := R) (S := S) φ I h.2
      letI :
          (quotient_modules_ambient_baseChange (R := R) (S := S) φ I).Faithful :=
        hambient
      have hcomp :
          (extendScalars q ⋙
            ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.map φ I))).Faithful := by
        -- Transport the ambient witness across the quotient-module comparison isomorphism.
        exact Functor.Faithful.of_iso
          (quotient_modules_restricted_baseChange_iso (R := R) (S := S) φ I)
      letI :
          (extendScalars q ⋙
            ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.map φ I))).Faithful :=
        hcomp
      -- Finally cancel the faithful postcomposition by restriction of scalars.
      exact ⟨h.1, Functor.Faithful.of_comp
        (extendScalars q)
        (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.map φ I)))⟩
    tfae_finish

end
