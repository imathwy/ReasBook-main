import stacks_proof.stacks_project.Chap10.Lemma_10_99_17.TorOneExact
import stacks_proof.stacks_project.Chap10.Lemma_10_99_17.LocalizationFaithful

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

section

variable {A : Type u} [CommRing A]
variable {M : Type u} [AddCommGroup M] [Module A M]
variable {r : ℕ} (f : Fin r → A)

local notation "I" => Ideal.span (Set.range f)
local notation "Ā" => A ⧸ I
local notation "M̄" => M ⧸ (I • (⊤ : Submodule A M))
set_option quotPrecheck false in
local notation "TorQ[" n "]" =>
  (((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).obj (ModuleCat.of A Ā))

/-- Helper for Lemma 10.99.17: on a tensor product, tensoring scalar multiplication on the right
factor is the same as literal scalar multiplication on the tensor module. This is the chain-level
identity needed for the source-owner `lsmul` comparison. -/
lemma rTensor_lsmul_eq_lsmul_tensor
    {P K : Type u} [AddCommGroup P] [Module A P] [AddCommGroup K] [Module A K] (a : A) :
    (LinearMap.lsmul A K a).rTensor P =
      LinearMap.lsmul A (K ⊗[A] P) a := by
  -- Proof comment: both linear maps send a pure tensor `k ⊗ p` to `(a • k) ⊗ p = a • (k ⊗ p)`.
  ext k p
  simpa [LinearMap.lsmul_apply] using (TensorProduct.smul_tmul' a k p).symm

/-- Helper for Lemma 10.99.17: in `ModuleCat`, whiskering scalar multiplication on the right
factor by tensor product is still literal scalar multiplication on the tensor module. This is the
categorical form of the chain-level identity used in the remaining source-owner comparison. -/
lemma tensorRight_map_lsmul_eq_lsmul
    {P K : Type u} [AddCommGroup P] [Module A P] [AddCommGroup K] [Module A K] (a : A) :
    ((tensorRight (ModuleCat.of A P)).map
      (ModuleCat.ofHom (LinearMap.lsmul A K a))).hom =
      LinearMap.lsmul A (K ⊗[A] P) a := by
  -- Proof comment: `tensorRight` maps a morphism to the corresponding `rTensor` map, so the
  -- tensor-level lemma applies directly.
  simpa [ModuleCat.hom_whiskerRight] using
    rTensor_lsmul_eq_lsmul_tensor (A := A) (K := K) (P := P) a

/-- Helper for Lemma 10.99.17: in `ModuleCat`, scalar multiplication on the identity morphism is
the linear map `x ↦ a • x`. This is the bundled-category form of `LinearMap.lsmul_apply`. -/
lemma moduleCat_hom_smul_id_eq_lsmul (a : A) (X : ModuleCat A) :
    ModuleCat.Hom.hom (a • 𝟙 X) = LinearMap.lsmul A ↑X a := by
  -- Proof comment: morphisms in `ModuleCat` are linear maps, and scalar multiplication is the
  -- ambient scalar action on those linear maps.
  ext x
  rfl

/-- Helper for Lemma 10.99.17: tensoring scalar multiplication on the right factor on the left by
an `A`-module `P` is literal scalar multiplication on `P ⊗[A] K`. This is the left-handed tensor
counterpart to `rTensor_lsmul_eq_lsmul_tensor`. -/
lemma lTensor_lsmul_eq_lsmul_tensor
    {P K : Type u} [AddCommGroup P] [Module A P] [AddCommGroup K] [Module A K] (a : A) :
    LinearMap.lTensor P (LinearMap.lsmul A K a) =
      LinearMap.lsmul A (P ⊗[A] K) a := by
  -- Proof comment: both linear maps send a pure tensor `p ⊗ k` to `p ⊗ (a • k) = a • (p ⊗ k)`.
  ext p k
  simpa [LinearMap.lsmul_apply] using (TensorProduct.tmul_smul p k a).symm

/-- Helper for Lemma 10.99.17: on any tensorized projective-resolution complex, the chain map
induced by `LinearMap.lsmul A K a` is literal scalar multiplication. This isolates the verified
chain-level part of the remaining `lsmul` comparison. -/
lemma tensorRight_mapHomologicalComplex_lsmul_eq_smul
    {K : Type u} [AddCommGroup K] [Module A K]
    (a : A) (C : ChainComplex (ModuleCat A) ℕ) :
    (NatTrans.mapHomologicalComplex
      ((tensoringRight (ModuleCat.{u} A)).map
        (ModuleCat.ofHom (LinearMap.lsmul A K a)))
      (ComplexShape.down ℕ)).app C =
      a • 𝟙 (((tensorRight (ModuleCat.of A K)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj C) := by
  -- Proof comment: `mapHomologicalComplex` acts degreewise, so it suffices to compare the
  -- component maps, where the tensor-level `lsmul` identity already applies.
  ext n x
  simpa [moduleCat_hom_smul_id_eq_lsmul] using
    congrArg (fun φ : ↑(C.X n) ⊗[A] K →ₗ[A] ↑(C.X n) ⊗[A] K => φ x)
      (lTensor_lsmul_eq_lsmul_tensor (A := A) (P := C.X n) (K := K) a)

/-- Helper for Lemma 10.99.17: the short-complex cutout in degree `n` sends scalar multiplication
on a homological complex to scalar multiplication on the associated short complex. This reduces the
remaining `lsmul` blocker to a pure homology transport step. -/
lemma shortComplexFunctor_map_smul_id
    (n : ℕ) {C : ChainComplex (ModuleCat A) ℕ} (a : A) :
    (HomologicalComplex.shortComplexFunctor (ModuleCat A) (ComplexShape.down ℕ) n).map
        (a • 𝟙 C) =
      a • 𝟙 (C.sc n) := by
  -- Proof comment: the short-complex functor remembers only the three adjacent components, and
  -- scalar multiplication by `a` acts componentwise on each of them.
  ext <;>
    simp [HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor']
  · rfl
  · rfl
  · rfl

/-- Helper for Lemma 10.99.17: the homology map of scalar multiplication on a chain complex is
literal scalar multiplication on the homology object. This is the last transport step needed in
the fixed-resolution `lsmul` computation. -/
lemma homologicalComplex_homologyMap_smul_id
    (n : ℕ) {C : ChainComplex (ModuleCat A) ℕ} (a : A) :
    HomologicalComplex.homologyMap (a • 𝟙 C) n =
      a • 𝟙 ((HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) n).obj C) := by
  -- Proof comment: expand `HomologicalComplex.homologyMap` through the degree-`n` short-complex
  -- cutout, where scalar linearity is already available in mathlib.
  dsimp [HomologicalComplex.homologyMap]
  rw [shortComplexFunctor_map_smul_id]
  rw [ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

/-- Helper for Chap10 Lemma 10 99 17: applying `M ⊗[A] -` degreewise to scalar
multiplication on a complex gives scalar multiplication on the tensorized complex. -/
lemma tensorLeft_mapHomologicalComplex_smul_id
    (a : A) (C : ChainComplex (ModuleCat A) ℕ) :
    ((tensorLeft (ModuleCat.of A M)).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (a • 𝟙 C) =
      a • 𝟙 (((tensorLeft (ModuleCat.of A M)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C) := by
  -- Proof comment: compare the chain maps degreewise; on each component this is exactly the
  -- tensor-level identity `m ⊗ (a • k) = a • (m ⊗ k)`.
  ext n x
  simpa [moduleCat_hom_smul_id_eq_lsmul] using
    congrArg (fun φ : M ⊗[A] ↑(C.X n) →ₗ[A] M ⊗[A] ↑(C.X n) => φ x)
      (lTensor_lsmul_eq_lsmul_tensor (A := A) (P := M) (K := C.X n) a)

/-- Helper for Chap10 Lemma 10 99 17: in the public module-first owner `K ↦ Torₙ^A(M, K)`,
the morphism induced by scalar multiplication `K ⟶ K` is literal scalar multiplication on the
Tor module. -/
lemma tor_module_map_lsmul_eq_smul
    (n : ℕ) {K : Type u} [AddCommGroup K] [Module A K] (a : A) :
    (((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map
      (ModuleCat.ofHom (LinearMap.lsmul A K a))) =
      ModuleCat.ofHom
        (LinearMap.lsmul A
          ↑((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).obj
            (ModuleCat.of A K))) a) := by
  let X : ModuleCat A := ModuleCat.of A K
  let P : CategoryTheory.ProjectiveResolution X := CategoryTheory.projectiveResolution X
  let C : ChainComplex (ModuleCat A) ℕ :=
    (((tensorLeft (ModuleCat.of A M)).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)
  let e :
      ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).obj X)) ≅
        (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) n).obj C :=
    P.isoLeftDerivedObj (tensorLeft (ModuleCat.of A M)) n
  have hw :
      (a • 𝟙 P.complex) ≫ P.π =
        P.π ≫ (ChainComplex.single₀ (ModuleCat A)).map
          (ModuleCat.ofHom (LinearMap.lsmul A K a)) := by
    -- Proof comment: scalar multiplication on the chosen resolution descends to scalar
    -- multiplication on the resolved module.
    refine HomologicalComplex.Hom.ext ?_
    funext i
    cases i with
    | zero =>
        apply ModuleCat.hom_ext
        ext x
        dsimp
        change (P.π.f 0).hom (a • x) = a • (P.π.f 0).hom x
        exact (P.π.f 0).hom.map_smul a x
    | succ i =>
        apply ModuleCat.hom_ext
        ext x
        simp only [Linear.smul_comp, Category.id_comp, HomologicalComplex.smul_f_apply,
          ProjectiveResolution.π_f_succ, ModuleCat.hom_smul, ModuleCat.hom_zero,
          LinearMap.smul_apply, LinearMap.zero_apply, HomologicalComplex.comp_f, zero_comp]
        exact smul_zero a
  have hMapCat :
      (((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map
          (ModuleCat.ofHom (LinearMap.lsmul A K a))) =
        e.hom ≫
          (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) n).map
            (((tensorLeft (ModuleCat.of A M)).mapHomologicalComplex
              (ComplexShape.down ℕ)).map (a • 𝟙 P.complex)) ≫
          e.inv := by
    -- Proof comment: compute the public module-first Tor map on the chosen projective resolution
    -- of the second variable.
    simpa [X, C, e, Tor] using
      (CategoryTheory.Functor.leftDerived_map_eq
        (tensorLeft (ModuleCat.of A M)) n (ModuleCat.ofHom (LinearMap.lsmul A K a))
        (a • 𝟙 P.complex) hw)
  rw [hMapCat]
  rw [tensorLeft_mapHomologicalComplex_smul_id (A := A) (M := M) (a := a) (C := P.complex)]
  have hHomology :
      (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) n).map
          (a • 𝟙 C) =
        a • 𝟙 ((HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) n).obj C) := by
    -- Proof comment: homology turns scalar multiplication on a complex into scalar
    -- multiplication on the homology object.
    simpa [HomologicalComplex.homologyMap] using
      homologicalComplex_homologyMap_smul_id (A := A) (n := n) (C := C) a
  rw [hHomology]
  -- Proof comment: the final conjugation by the comparison isomorphism preserves the scalar
  -- action because the isomorphism is `A`-linear.
  apply ModuleCat.hom_ext
  ext x
  change e.inv.hom (a • e.hom.hom x) = a • x
  rw [LinearMap.map_smul]
  simpa using congrArg (fun y => a • y)
    (LinearEquiv.symm_apply_apply e.toLinearEquiv x)

/-- Helper for Lemma 10.99.17: in the fixed-left source owner `K ↦ Tor'_n^A(M, K)`, the morphism
induced by scalar multiplication `K ⟶ K` is literal scalar multiplication on the Tor module. This
is the projective-resolution computation behind the public-owner `lsmul` comparison used in the
generator descent. -/
lemma source_owner_map_lsmul_eq_smul
    (n : ℕ) {K : Type u} [AddCommGroup K] [Module A K] (a : A) :
    ((((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).map
      (ModuleCat.ofHom (LinearMap.lsmul A K a)))) =
      ModuleCat.ofHom
        (LinearMap.lsmul A
          ↑((((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).obj
            (ModuleCat.of A K))) a) := by
  let X : ModuleCat A := ModuleCat.of A K
  let P : CategoryTheory.ProjectiveResolution (ModuleCat.of A M) :=
    CategoryTheory.projectiveResolution (ModuleCat.of A M)
  let C : ChainComplex (ModuleCat A) ℕ :=
    (((tensorRight X).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)
  let e :
      ((((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).obj X)) ≅
        (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) n).obj C :=
    source_owner_tor_projective_resolution_iso (A := A) (M := M) X n
  have hMapCat :
      ((((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).map
          (ModuleCat.ofHom (LinearMap.lsmul A K a)))) =
        e.hom ≫
          HomologicalComplex.homologyMap
            ((NatTrans.mapHomologicalComplex
                ((tensoringRight (ModuleCat.{u} A)).map
                  (ModuleCat.ofHom (LinearMap.lsmul A K a)))
                (ComplexShape.down ℕ)).app P.complex)
            n ≫
          e.inv := by
    -- Proof comment: compute the source-owner Tor map on the fixed projective resolution of `M`.
    simpa [X, C, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
      (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
        ((tensoringRight (ModuleCat.{u} A)).map
          (ModuleCat.ofHom (LinearMap.lsmul A K a))) P n)
  rw [hMapCat]
  rw [tensorRight_mapHomologicalComplex_lsmul_eq_smul (A := A) (K := K) (a := a) (C := P.complex)]
  rw [homologicalComplex_homologyMap_smul_id (A := A) (n := n) (C := C) a]
  -- Proof comment: conjugating scalar multiplication across the comparison isomorphism leaves the
  -- literal scalar action on the source-owner Tor module.
  apply ModuleCat.hom_ext
  ext x
  change e.inv.hom (a • e.hom.hom x) = a • x
  rw [LinearMap.map_smul]
  simpa using congrArg (fun y => a • y)
    (LinearEquiv.symm_apply_apply e.toLinearEquiv x)

/-- Helper for Lemma 10.99.17: in the public quotient-first owner `K ↦ Tor_n^A(K, M)`, the
morphism induced by `LinearMap.lsmul A K a` is literal scalar multiplication on the Tor module.
This is the owner-level identity needed to turn exactness into injectivity in the generator
descent. -/
lemma tor_public_map_lsmul_eq_smul
    (n : ℕ) {K : Type u} [AddCommGroup K] [Module A K] (a : A) :
    (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map
      (ModuleCat.ofHom (LinearMap.lsmul A K a)))) =
      ModuleCat.ofHom
        (LinearMap.lsmul A
          ↑(((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).obj
            (ModuleCat.of A K))) a) := by
  let X : ModuleCat A := ModuleCat.of A K
  let e :
      (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).obj X)) ≅
        ((((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).obj X)) :=
    (tor_left_owner_iso (A := A) (M := M) n).app X
  have hNat :
      (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map
          (ModuleCat.ofHom (LinearMap.lsmul A K a)))) ≫
        e.hom =
        e.hom ≫
          ((((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).map
            (ModuleCat.ofHom (LinearMap.lsmul A K a)))) := by
    -- Proof comment: transport the public-owner map to the fixed-left source owner by naturality
    -- of `tor_left_owner_iso`.
    simpa [e] using
      ((tor_left_owner_iso (A := A) (M := M) n).hom.naturality
        (ModuleCat.ofHom (LinearMap.lsmul A K a)))
  apply (cancel_mono e.hom).1
  rw [hNat, source_owner_map_lsmul_eq_smul (A := A) (M := M) (n := n) (K := K) a]
  -- Proof comment: the comparison isomorphism is linear, so scalar multiplication commutes with
  -- its forward map and returns to the quotient-first public owner.
  apply ModuleCat.hom_ext
  ext x
  simpa [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.lsmul_apply] using
    (LinearMap.map_smul e.hom.hom a x).symm

/-- Helper for Lemma 10.99.17: if the left Tor variable is flat, then every higher public Tor
owner against the fixed module `M` vanishes. This isolates the standard higher-Tor vanishing used
after localizing away from a generator. -/
lemma tor_succ_isZero_of_flat_left
    (n : ℕ) {P : Type u} [AddCommGroup P] [Module A P] [Module.Flat A P] :
    IsZero ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A P)).obj
      (ModuleCat.of A M))) := by
  let X : ModuleCat A := ModuleCat.of A P
  let Q : CategoryTheory.ProjectiveResolution (ModuleCat.of A M) :=
    CategoryTheory.projectiveResolution (ModuleCat.of A M)
  let K : ChainComplex (ModuleCat A) ℕ :=
    ((tensorLeft X).mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex
  -- Proof comment: compute the public owner on a projective resolution of `M`; flatness of `P`
  -- preserves the exact `(n + 2, n + 1, n)` tensor row, so the resulting homology is zero.
  refine IsZero.of_iso ?_ (Q.isoLeftDerivedObj (tensorLeft X) (n + 1))
  have hExactTensor : K.ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff' K (n + 2) (n + 1) n (by simp) (by simp)]
    simpa [K] using Module.Flat.lTensor_shortComplex_exact (M := X) _ (Q.exact_succ n)
  exact hExactTensor.isZero_homology

/-- Helper for Lemma 10.99.17: if the coefficient module in the fixed-left source owner is flat,
then every higher `Tor'` object vanishes. This is the correct source-owner flatness statement for
the right tensor factor. -/
lemma source_owner_tor_succ_isZero_of_flat_right
    (n : ℕ) {P : Type u} [AddCommGroup P] [Module A P]
    {K : Type u} [AddCommGroup K] [Module A K] [Module.Flat A K] :
    IsZero ((((Tor' (ModuleCat A) (n + 1)).obj (ModuleCat.of A P)).obj
      (ModuleCat.of A K))) := by
  let X : ModuleCat A := ModuleCat.of A K
  let Q : CategoryTheory.ProjectiveResolution (ModuleCat.of A P) :=
    CategoryTheory.projectiveResolution (ModuleCat.of A P)
  let C : ChainComplex (ModuleCat A) ℕ :=
    (((tensorRight X).mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex)
  -- Proof comment: compute the fixed-left source owner on a projective resolution of `P`;
  -- flatness of the coefficient module `K` keeps the `(n + 2, n + 1, n)` tensor row exact after
  -- tensoring on the right.
  refine IsZero.of_iso ?_ (source_owner_tor_projective_resolution_iso (A := A) (M := P) X (n + 1))
  have hExactTensor : C.ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff' C (n + 2) (n + 1) n (by simp) (by simp)]
    simpa [C] using Module.Flat.rTensor_shortComplex_exact (M := X) _ (Q.exact_succ n)
  exact hExactTensor.isZero_homology

/-- Helper for Lemma 10.99.17: localizing an `A`-module away from `a` agrees with the tensor
product base change `A[1 / a] ⊗[A] T`. This is the concrete object-level bridge used when
transporting zero objects through localization. -/
noncomputable def away_localizedModule_iso_tensorProduct
    (a : A) (T : Type u) [AddCommGroup T] [Module A T] :
    ModuleCat.of (Localization.Away a) (LocalizedModule.Away a T) ≅
      ModuleCat.of (Localization.Away a) (Localization.Away a ⊗[A] T) := by
  -- Proof comment: the localized module is canonically the tensor-product base change
  -- `A[1 / a] ⊗[A] T`.
  simpa [LocalizedModule.Away, Localization.Away] using
    (LocalizedModule.equivTensorProduct (Submonoid.powers a) T).toModuleIso

/-- Helper for Lemma 10.99.17: if the tensor-product base change `A[1 / a] ⊗[A] T` is zero, then
the literal away-localization `T[1 / a]` is also zero. This packages the stable final transport
needed in the localization-kill step. -/
  lemma isZero_away_localizedModule_of_isZero_tensorProduct
    (a : A) {T : Type u} [AddCommGroup T] [Module A T]
    (hT : IsZero (ModuleCat.of (Localization.Away a) (Localization.Away a ⊗[A] T))) :
    IsZero
      (ModuleCat.of (Localization.Away a) (LocalizedModule.Away a T)) := by
  -- Proof comment: the previous tensor-product identification converts the zero tensor base
  -- change into the zero literal localization object.
  exact IsZero.of_iso hT (away_localizedModule_iso_tensorProduct (A := A) a T)

/-- Helper for Lemma 10.99.17: if the kernel and cokernel rows for multiplication by `a` have the
expected Tor-vanishing, then the induced scalar action on the public quotient-first owner is
injective. This packages the exactness part of the source proof's generator-descent step. -/
lemma tor_public_smul_injective_of_kernel_and_quotient_vanishing
    {K : Type u} [AddCommGroup K] [Module A K] (a : A) (n : ℕ)
    (hker :
      IsZero
        (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A (LinearMap.ker (LinearMap.lsmul A K a))))))
    (hquot :
      IsZero
        (((((Tor (ModuleCat A) (n + 1)).flip).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A (K ⧸ LinearMap.range (LinearMap.lsmul A K a))))))
    (hmap :
      (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map
        (ModuleCat.ofHom (LinearMap.lsmul A K a)))) =
        ModuleCat.ofHom
          (LinearMap.lsmul A
            ↑(((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).obj
              (ModuleCat.of A K))) a)) :
    Function.Injective
      fun t :
        ↑(((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A K))) ↦
        a • t := by
  let μ : K →ₗ[A] K := LinearMap.lsmul A K a
  let β₀ : K →ₗ[A] LinearMap.range μ := μ.rangeRestrict
  let γ₀ : LinearMap.range μ →ₗ[A] K := (LinearMap.range μ).subtype
  let q : K →ₗ[A] K ⧸ LinearMap.range μ := Submodule.mkQ (LinearMap.range μ)
  have hExactKerBase : Function.Exact (LinearMap.ker μ).subtype β₀ := by
    -- Proof comment: replacing `μ` by its range-restriction leaves the kernel and image
    -- unchanged, so the standard kernel exactness lemma still applies.
    rw [LinearMap.exact_iff]
    simp [β₀]
  let Sker : ShortComplex (ModuleCat A) :=
    ShortComplex.moduleCatMk (LinearMap.ker μ).subtype β₀
      (Function.Exact.linearMap_comp_eq_zero hExactKerBase)
  let Squot : ShortComplex (ModuleCat A) :=
    ShortComplex.moduleCatMk γ₀ q
      (Function.Exact.linearMap_comp_eq_zero
        (by
          simpa [γ₀, q] using
            (LinearMap.exact_subtype_mkQ (LinearMap.range μ))))
  have hSker : Sker.ShortExact := by
    -- Proof comment: `0 → ker μ → K → range μ → 0` is the first exact row in the source proof.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      simpa [Sker] using hExactKerBase
    · exact (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
    · exact (ModuleCat.epi_iff_surjective _).2 <| by
        simpa [Sker, β₀] using μ.surjective_rangeRestrict
  have hSquot : Squot.ShortExact := by
    -- Proof comment: `0 → range μ → K → K / range μ → 0` is the second exact row.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      simpa [Squot, γ₀, q] using
        (LinearMap.exact_subtype_mkQ (LinearMap.range μ))
    · exact (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
    · exact (ModuleCat.epi_iff_surjective _).2 <| by
        simpa [Squot, q] using Submodule.mkQ_surjective (LinearMap.range μ)
  have hExactKer :
      Function.Exact
        (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map Sker.f).hom)
        (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map Sker.g).hom) := by
    -- Proof comment: read the same-degree exact window off the first short exact row.
    simpa [Sker] using
      tor_public_middle_exact_of_shortExact (A := A) (M := M) (S := Sker) hSker n
  obtain ⟨δ, hExactQuot⟩ :=
    tor_public_succ_exact_of_shortExact (A := A) (M := M) (S := Squot) hSquot n
  have hKerMapZero :
      ((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map Sker.f) = 0 := by
    -- Proof comment: the first row starts with a zero Tor object by hypothesis on `ker μ`.
    simpa [Sker] using hker.eq_of_src
      (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map Sker.f)) 0
  have hδZero : δ = 0 := by
    -- Proof comment: the second row starts with a zero higher Tor object by hypothesis on
    -- `K / range μ`.
    simpa [Squot] using hquot.eq_of_src δ 0
  have hβ_injective :
      Function.Injective
        (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map Sker.g).hom) := by
    have hkerβ :
        LinearMap.ker (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map Sker.g).hom) =
          ⊥ := by
      calc
        LinearMap.ker (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map Sker.g).hom)
            =
          LinearMap.range (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map Sker.f).hom) :=
              LinearMap.exact_iff.mp hExactKer
        _ = ⊥ := by
              have hzero :
                  (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map Sker.f).hom) = 0 :=
                congrArg ModuleCat.Hom.hom hKerMapZero
              simpa [hzero] using (LinearMap.range_eq_bot.mpr hzero)
    exact (LinearMap.ker_eq_bot).1 hkerβ
  have hγ_injective :
      Function.Injective
        (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map Squot.f).hom) := by
    have hkerγ :
        LinearMap.ker (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map Squot.f).hom) =
          ⊥ := by
      calc
        LinearMap.ker (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map Squot.f).hom)
            = LinearMap.range δ.hom := LinearMap.exact_iff.mp hExactQuot
        _ = ⊥ := by
              have hzero : δ.hom = 0 := congrArg ModuleCat.Hom.hom hδZero
              simpa [hzero] using (LinearMap.range_eq_bot.mpr hzero)
    exact (LinearMap.ker_eq_bot).1 hkerγ
  have hμ_cat : Sker.g ≫ Squot.f = ModuleCat.ofHom μ := by
    -- Proof comment: the two short exact rows recombine to multiplication by `a` on `K`.
    ext x
    rfl
  have hTorμ :
      (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map
          (ModuleCat.ofHom μ))).hom =
        (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map Squot.f).hom).comp
          (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map Sker.g).hom) := by
    have hmapComp :
        ((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map
          (ModuleCat.ofHom μ)) =
          ((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map Sker.g) ≫
            ((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map Squot.f) := by
      simpa [hμ_cat] using
        ((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map_comp Sker.g Squot.f)
    simpa using congrArg ModuleCat.Hom.hom hmapComp
  have hTorμ_injective :
      Function.Injective
        (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map
          (ModuleCat.ofHom μ))).hom := by
    rw [hTorμ]
    exact hγ_injective.comp hβ_injective
  have hmap_hom :
      (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map
        (ModuleCat.ofHom μ))).hom =
        LinearMap.lsmul A
          ↑(((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).obj
            (ModuleCat.of A K))) a := by
    simpa [μ] using congrArg ModuleCat.Hom.hom hmap
  -- Proof comment: after identifying the Tor map of `μ = lsmul a` with literal scalar
  -- multiplication, injectivity of the composite Tor map becomes injectivity of `a • -`.
  intro x y hxy
  have hxy' :
      (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map
        (ModuleCat.ofHom μ))).hom x =
        (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map
          (ModuleCat.ofHom μ))).hom y := by
    rw [hmap_hom]
    simpa [LinearMap.lsmul_apply] using hxy
  exact hTorμ_injective hxy'

end
