import StacksProject_2024.Chap10.Lemma_10_143_11.KernelIdealTransport

-- Declarations moved out of `Lemma_10_143_11.lean` to keep the active proof file small.

open scoped TensorProduct

universe u v w x

namespace RingHom

section

variable {Aprime : Type u} {A : Type v} {Bprime : Type w} {B : Type x}
variable [CommRing Aprime] [CommRing A] [CommRing Bprime] [CommRing B]
variable (g : Aprime →+* Bprime) (qA : Aprime →+* A) (qB : Bprime →+* B) (f : A →+* B)

/-- Helper for Lemma 10.143.11: the explicit textbook map `IC → J` sends an element to zero
exactly when its underlying ring element lies in the comparison kernel. -/
lemma ideal_map_restrict_eq_zero_iff
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] {T : Type*} [CommRing T]
    {I : Ideal R} {f : R →+* S} {g : R →+* T} {φ : S →+* T}
    (hcomp : φ.comp f = g) (x : Ideal.map f I) :
    ideal_map_restrict f g φ I hcomp x = 0 ↔ ((x : Ideal.map f I) : S) ∈ RingHom.ker φ := by
  constructor
  · intro hx
    -- Equality in the subtype target is equality of the underlying ring elements.
    rw [RingHom.mem_ker]
    exact congrArg Subtype.val hx
  · intro hx
    -- Conversely, vanishing in the codomain ring makes the subtype element zero.
    apply Subtype.ext
    rwa [RingHom.mem_ker] at hx

/-- Helper for Lemma 10.143.11: injectivity of the textbook ideal comparison `IC → J`
forces the residual kernel inside `IC` to vanish. -/
lemma inf_eq_bot_of_ideal_map_restrict_injective
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] {T : Type*} [CommRing T]
    {I : Ideal R} {f : R →+* S} {g : R →+* T} {φ : S →+* T}
    (hcomp : φ.comp f = g)
    (hinj : Function.Injective (ideal_map_restrict f g φ I hcomp)) :
    RingHom.ker φ ⊓ Ideal.map f I = ⊥ := by
  apply le_antisymm
  · intro x hx
    -- View `x` as an element of `f(I)`, then compare it with zero through injectivity.
    rw [Ideal.mem_bot]
    have hx_zero :
        ideal_map_restrict f g φ I hcomp ⟨x, hx.2⟩ = 0 := by
      exact (ideal_map_restrict_eq_zero_iff (I := I) (f := f) (g := g) hcomp ⟨x, hx.2⟩).2 hx.1
    have hmap_zero : ideal_map_restrict f g φ I hcomp 0 = 0 := by
      apply Subtype.ext
      simp [ideal_map_restrict]
    have hx_zero' :
        ideal_map_restrict f g φ I hcomp ⟨x, hx.2⟩ =
          ideal_map_restrict f g φ I hcomp 0 := by
      exact hx_zero.trans hmap_zero.symm
    have hx_eq : (⟨x, hx.2⟩ : Ideal.map f I) = 0 := hinj hx_zero'
    exact congrArg Subtype.val hx_eq
  · exact bot_le

/-- Helper for Lemma 10.143.11: once the residual comparison kernel inside `IC` is zero, the
kernel term produced by `Ideal.mapCotangent_ker_of_surjective` is also zero. -/
lemma residual_cotangent_kernel_eq_bot_of_inf_eq_bot
    {R : Type*} [CommRing R] (I K : Ideal R)
    (hInf : K ⊓ I = ⊥) :
    (Submodule.comap I.subtype (K ⊓ I)).map (Ideal.toCotangent I) = ⊥ := by
  -- After rewriting the residual ideal to `⊥`, only the zero submodule remains.
  rw [hInf]
  simp

/-- Helper for Lemma 10.143.11: after identifying the source and target quotient kernels with the
textbook ideals, the cotangent comparison induced by `φ` is surjective and its kernel is exactly
the cotangent image of the residual kernel `ker φ ⊆ f(I)`. -/
lemma mapCotangent_surjective_and_ker_eq_residual_of_comp_eq_of_ker_eq
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    (hSurj : Function.Surjective φ)
    (hq : qB.comp φ = qC)
    (hcomp : φ.comp (algebraMap R C) = algebraMap R B₁)
    (hSrc : RingHom.ker qC = Ideal.map (algebraMap R C) I)
    (hTgt : RingHom.ker qB = Ideal.map (algebraMap R B₁) I) :
    let φAlg : C →ₐ[R] B₁ :=
      { toRingHom := φ
        commutes' := fun r ↦ by
          -- The cotangent comparison uses the same `R`-algebra structure encoded by `hcomp`.
          exact congrArg (fun h : R →+* B₁ ↦ h r) hcomp }
    let hle : Ideal.map (algebraMap R C) I ≤ Ideal.comap φAlg (Ideal.map (algebraMap R B₁) I) :=
      ideal_map_le_comap_of_comp_eq (algebraMap R C) (algebraMap R B₁) φ I hcomp
    Function.Surjective
        (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
          φAlg hle) ∧
      LinearMap.ker
          (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
            φAlg hle) =
        ((Submodule.comap (Ideal.map (algebraMap R C) I).subtype (RingHom.ker φ)).map
          (Ideal.toCotangent (Ideal.map (algebraMap R C) I))).restrictScalars R := by
  let φAlg : C →ₐ[R] B₁ :=
    { toRingHom := φ
      commutes' := fun r ↦ by
        -- The cotangent comparison uses the same `R`-algebra structure encoded by `hcomp`.
        exact congrArg (fun h : R →+* B₁ ↦ h r) hcomp }
  let hle : Ideal.map (algebraMap R C) I ≤ Ideal.comap φAlg (Ideal.map (algebraMap R B₁) I) :=
    ideal_map_le_comap_of_comp_eq (algebraMap R C) (algebraMap R B₁) φ I hcomp
  -- Repackage the goal using the explicit `R`-algebra map and its induced ideal inclusion.
  change Function.Surjective
      (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
        φAlg hle) ∧
    LinearMap.ker
        (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
          φAlg hle) =
      ((Submodule.comap (Ideal.map (algebraMap R C) I).subtype (RingHom.ker φ)).map
        (Ideal.toCotangent (Ideal.map (algebraMap R C) I))).restrictScalars R
  letI : Algebra C B₁ := φ.toAlgebra
  letI : IsScalarTower R C B₁ := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext r
    exact congrArg (fun h : R →+* B₁ ↦ h r) hcomp.symm
  have hkerφ_le : RingHom.ker φ ≤ Ideal.map (algebraMap R C) I :=
    ker_le_ideal_map_of_comp_eq_of_ker_eq (I := I) (c := algebraMap R C) hq hSrc
  have hcomap_eq :
      Ideal.comap (algebraMap C B₁) (Ideal.map (algebraMap R B₁) I) =
        RingHom.ker (algebraMap C B₁) ⊔ Ideal.map (algebraMap R C) I := by
    -- The pullback ideal is exactly the source ideal together with the residual kernel.
    simpa using
      ideal_comap_eq_ker_sup_of_comp_eq_of_ker_eq
        (I := I) (c := algebraMap R C) (g := algebraMap R B₁)
        (qC := qC) (qB := qB) (φ := φ) hq hSrc hTgt hkerφ_le
  let hleC :
      Ideal.map (algebraMap R C) I ≤
        Ideal.comap (Algebra.ofId C B₁) (Ideal.map (algebraMap R B₁) I) :=
    le_of_le_of_eq le_sup_right hcomap_eq.symm
  have hmap_eq :
      Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
          φAlg hle =
        (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
          (Algebra.ofId C B₁) hleC).restrictScalars R := by
    -- The owner `C`-linear cotangent map has the same generator formula as the mixed-scalar map.
    exact mapCotangent_restrictScalars_eq_of_toRingHom_eq (R := R) (A := C) (B := B₁) φAlg rfl hle hleC
  have hsurjC :
      Function.Surjective
        (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
          (Algebra.ofId C B₁) hleC) := by
    -- Apply the owner surjectivity theorem in the `C`-algebra structure coming from `φ`.
    simpa [hleC] using
      (Ideal.mapCotangent_surjective_of_comap_eq
        (A := C) (B := B₁) (surj := by simpa using hSurj)
        (I := Ideal.map (algebraMap R B₁) I) (J := Ideal.map (algebraMap R C) I) hcomap_eq)
  have hkerC :
      LinearMap.ker
          (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
            (Algebra.ofId C B₁) hleC) =
        (Submodule.comap (Ideal.map (algebraMap R C) I).subtype (RingHom.ker (algebraMap C B₁))).map
          (Ideal.toCotangent (Ideal.map (algebraMap R C) I)) := by
    -- The owner kernel theorem gives the residual kernel with an explicit intersection by `IC`.
    calc
      LinearMap.ker
          (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
            (Algebra.ofId C B₁) hleC) =
          (Submodule.comap (Ideal.map (algebraMap R C) I).subtype
            (RingHom.ker (algebraMap C B₁) ⊓ Ideal.map (algebraMap R C) I)).map
              (Ideal.toCotangent (Ideal.map (algebraMap R C) I)) := by
            simpa [hleC] using
              (Ideal.mapCotangent_ker_of_surjective
                (A := C) (B := B₁) (surj := by simpa using hSurj)
                (I := Ideal.map (algebraMap R B₁) I) (J := Ideal.map (algebraMap R C) I) hcomap_eq)
      _ =
          (Submodule.comap (Ideal.map (algebraMap R C) I).subtype (RingHom.ker (algebraMap C B₁))).map
            (Ideal.toCotangent (Ideal.map (algebraMap R C) I)) := by
            rw [submodule_comap_subtype_inf_eq_comap]
  have hkerR :
      LinearMap.ker
          ((Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
            (Algebra.ofId C B₁) hleC).restrictScalars R) =
        ((Submodule.comap (Ideal.map (algebraMap R C) I).subtype (RingHom.ker φ)).map
          (Ideal.toCotangent (Ideal.map (algebraMap R C) I))).restrictScalars R := by
    -- Restrict scalars from the owner `C`-linear statement to the ambient `R`-linear one.
    simpa using congrArg (fun K ↦ K.restrictScalars R) hkerC
  constructor
  · -- Surjectivity is unchanged under restriction of scalars, and `hmap_eq` identifies the maps.
    simpa [hmap_eq] using hsurjC
  · -- Rewrite the target kernel through the restricted owner map and use the packaged kernel formula.
    simpa [hmap_eq] using hkerR

/-- Helper for Lemma 10.143.11: a cotangent comparison map is injective once conjugating it by
source and target linear equivalences gives the identity. -/
lemma mapCotangent_injective_of_conjugation_eq_id
    {R : Type*} [CommRing R]
    {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    [Algebra R A] [Algebra R B]
    {I₁ : Ideal A} {I₂ : Ideal B} {f : A →ₐ[R] B}
    (h : I₁ ≤ I₂.comap f)
    {M : Type*} [AddCommGroup M] [Module R M]
    (eSrc : I₁.Cotangent ≃ₗ[R] M) (eTgt : I₂.Cotangent ≃ₗ[R] M)
    (hconj :
      (eTgt.toLinearMap.comp (Ideal.mapCotangent I₁ I₂ f h)).comp eSrc.symm.toLinearMap =
        (LinearMap.id : M →ₗ[R] M)) :
    Function.Injective (Ideal.mapCotangent I₁ I₂ f h) := by
  intro x y hxy
  -- Evaluate the conjugated identity on the two source coordinates and compare through `hxy`.
  apply eSrc.injective
  have hxid :
      ((eTgt.toLinearMap.comp (Ideal.mapCotangent I₁ I₂ f h)).comp eSrc.symm.toLinearMap)
        (eSrc x) =
        eSrc x := by
    exact congrArg (fun l : M →ₗ[R] M ↦ l (eSrc x)) hconj
  have hyid :
      ((eTgt.toLinearMap.comp (Ideal.mapCotangent I₁ I₂ f h)).comp eSrc.symm.toLinearMap)
        (eSrc y) =
        eSrc y := by
    exact congrArg (fun l : M →ₗ[R] M ↦ l (eSrc y)) hconj
  calc
    eSrc x =
        ((eTgt.toLinearMap.comp (Ideal.mapCotangent I₁ I₂ f h)).comp eSrc.symm.toLinearMap)
          (eSrc x) := hxid.symm
    _ = eTgt ((Ideal.mapCotangent I₁ I₂ f h) x) := by
          simp [LinearMap.comp_apply]
    _ = eTgt ((Ideal.mapCotangent I₁ I₂ f h) y) := by rw [hxy]
    _ =
        ((eTgt.toLinearMap.comp (Ideal.mapCotangent I₁ I₂ f h)).comp eSrc.symm.toLinearMap)
          (eSrc y) := by
          simp [LinearMap.comp_apply]
    _ = eSrc y := hyid

/-- Helper for Lemma 10.143.11: if the cotangent comparison for the textbook ideal map becomes
the identity after transport to a common model, then the textbook ideal map itself is injective. -/
lemma ideal_map_restrict_injective_of_conjugation_eq_id
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] {T : Type*} [CommRing T]
    [Algebra R S] [Algebra R T]
    {I : Ideal R} {φ : S →+* T}
    (hcomp : φ.comp (algebraMap R S) = algebraMap R T)
    (hSrcSq : (Ideal.map (algebraMap R S) I) ^ 2 = ⊥)
    {M : Type*} [AddCommGroup M] [Module R M]
    (eSrc : (Ideal.map (algebraMap R S) I).Cotangent ≃ₗ[R] M)
    (eTgt : (Ideal.map (algebraMap R T) I).Cotangent ≃ₗ[R] M)
    (hconj :
      (eTgt.toLinearMap.comp
          (Ideal.mapCotangent (Ideal.map (algebraMap R S) I) (Ideal.map (algebraMap R T) I)
            { toRingHom := φ
              commutes' := fun x ↦ by
                -- The cotangent comparison uses the same algebra structure as `ideal_map_restrict`.
                exact congrArg (fun h : R →+* T ↦ h x) hcomp }
            (ideal_map_le_comap_of_comp_eq (algebraMap R S) (algebraMap R T) φ I hcomp))).comp
        eSrc.symm.toLinearMap =
        (LinearMap.id : M →ₗ[R] M)) :
    Function.Injective (ideal_map_restrict (algebraMap R S) (algebraMap R T) φ I hcomp) := by
  -- First upgrade the transported-identity statement to cotangent injectivity.
  have hCotInj :
      Function.Injective
        (Ideal.mapCotangent (Ideal.map (algebraMap R S) I) (Ideal.map (algebraMap R T) I)
          { toRingHom := φ
            commutes' := fun x ↦ by
              -- This is the same `R`-algebra structure encoded by `hcomp`.
              exact congrArg (fun h : R →+* T ↦ h x) hcomp }
          (ideal_map_le_comap_of_comp_eq (algebraMap R S) (algebraMap R T) φ I hcomp)) :=
    mapCotangent_injective_of_conjugation_eq_id
      (I₁ := Ideal.map (algebraMap R S) I) (I₂ := Ideal.map (algebraMap R T) I)
      (f := { toRingHom := φ
              commutes' := fun x ↦ by
                exact congrArg (fun h : R →+* T ↦ h x) hcomp })
      (h := ideal_map_le_comap_of_comp_eq (algebraMap R S) (algebraMap R T) φ I hcomp)
      eSrc eTgt hconj
  -- Then reuse the existing square-zero bridge from cotangent injectivity to ideal injectivity.
  exact ideal_map_restrict_injective_of_mapCotangent_injective
    (R := R) (S := S) (T := T) (I := I) (φ := φ) hcomp hSrcSq hCotInj

/-- Helper for Lemma 10.143.11: once the common model is built at cotangent level, the existing
square-zero identifications convert it into the ideal-level transport identity used for kernels. -/
lemma common_model_ideal_transport_identity_of_cotangent_conjugation_eq_id
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {qC : C →+* B₀} {qB : B₁ →+* B₀} {φAlg : C →ₐ[R] B₁}
    (hq : qB.comp φAlg.toRingHom = qC)
    (hcomp : φAlg.toRingHom.comp (algebraMap R C) = algebraMap R B₁)
    (hSrc : RingHom.ker qC = Ideal.map (algebraMap R C) I)
    (hTgt : RingHom.ker qB = Ideal.map (algebraMap R B₁) I)
    (hSrcSq : (Ideal.map (algebraMap R C) I) ^ 2 = ⊥)
    (hTgtSq : (Ideal.map (algebraMap R B₁) I) ^ 2 = ⊥)
    {M : Type*} [AddCommGroup M] [Module R M]
    (eCotSrc : M ≃ₗ[R] (Ideal.map (algebraMap R C) I).Cotangent)
    (eCotTgt : M ≃ₗ[R] (Ideal.map (algebraMap R B₁) I).Cotangent)
    (hconj :
      (eCotTgt.symm.toLinearMap.comp
          (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
            φAlg
            (ideal_map_le_comap_of_comp_eq
              (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp))).comp
        eCotSrc.toLinearMap =
        (LinearMap.id : M →ₗ[R] M)) :
    ∃ (eIdealSrc : M ≃ Ideal.map (algebraMap R C) I)
      (eIdealTgt : M ≃ Ideal.map (algebraMap R B₁) I),
      ∀ x : M,
        eIdealTgt.symm
          ((ideal_equiv_ker qB (Ideal.map (algebraMap R B₁) I) hTgt).symm
            (kernel_restrict (qC := qC) (qB := qB) (φ := φAlg.toRingHom) hq
              ((eIdealSrc.trans
                (ideal_equiv_ker qC (Ideal.map (algebraMap R C) I) hSrc)) x))) = x := by
  let eIdealSrc : M ≃ Ideal.map (algebraMap R C) I :=
    eCotSrc.toEquiv.trans
      (ideal_equiv_cotangent_of_square_zero (Ideal.map (algebraMap R C) I) hSrcSq).symm.toEquiv
  let eIdealTgt : M ≃ Ideal.map (algebraMap R B₁) I :=
    eCotTgt.toEquiv.trans
      (ideal_equiv_cotangent_of_square_zero (Ideal.map (algebraMap R B₁) I) hTgtSq).symm.toEquiv
  refine ⟨eIdealSrc, eIdealTgt, ?_⟩
  intro x
  have hsrc_toCot :
      Ideal.toCotangent (Ideal.map (algebraMap R C) I) (eIdealSrc x) = eCotSrc x := by
    -- The source ideal model is obtained by inverting the square-zero cotangent equivalence.
    change
      ideal_equiv_cotangent_of_square_zero (Ideal.map (algebraMap R C) I) hSrcSq
        ((ideal_equiv_cotangent_of_square_zero (Ideal.map (algebraMap R C) I) hSrcSq).symm
          (eCotSrc x)) =
        eCotSrc x
    simp
  have hkernel :
      (ideal_equiv_ker qB (Ideal.map (algebraMap R B₁) I) hTgt).symm
        (kernel_restrict (qC := qC) (qB := qB) (φ := φAlg.toRingHom) hq
          ((eIdealSrc.trans
            (ideal_equiv_ker qC (Ideal.map (algebraMap R C) I) hSrc)) x)) =
      ideal_map_restrict (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp (eIdealSrc x) := by
    -- Rewrite the restricted kernel comparison as the explicit textbook ideal map.
    simpa [eIdealSrc, Equiv.trans_apply] using
      kernel_restrict_eq_ideal_map_restrict
        (I := I) (c := algebraMap R C) (g := algebraMap R B₁)
        (qC := qC) (qB := qB) (φ := φAlg.toRingHom) hq hcomp hSrc hTgt (eIdealSrc x)
  have hmap :
      Ideal.toCotangent (Ideal.map (algebraMap R B₁) I)
          (ideal_map_restrict (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp
            (eIdealSrc x)) =
        Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
          φAlg
          (ideal_map_le_comap_of_comp_eq
            (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp)
          (eCotSrc x) := by
    have hmap0 :
        (ideal_equiv_cotangent_of_square_zero (Ideal.map (algebraMap R B₁) I) hTgtSq).symm
          (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
            φAlg
            (ideal_map_le_comap_of_comp_eq
              (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp)
            (Ideal.toCotangent (Ideal.map (algebraMap R C) I) (eIdealSrc x))) =
          ideal_map_restrict (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp
            (eIdealSrc x) := by
      -- Expand the cotangent map on the source generator and then invert the target square-zero
      -- cotangent equivalence.
      simpa using
        square_zero_symm_mapCotangent_toCotangent_eq_ideal_map_restrict
          (R := R) (S := C) (T := B₁) (I := I) (φ := φAlg.toRingHom)
          hcomp hTgtSq (eIdealSrc x)
    -- Route correction: prove the identity in cotangent coordinates first, then descend to ideals.
    simpa [hsrc_toCot] using
      (congrArg
        (ideal_equiv_cotangent_of_square_zero (Ideal.map (algebraMap R B₁) I) hTgtSq)
        hmap0).symm
  have hx :
      eCotTgt.symm
        (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
          φAlg
          (ideal_map_le_comap_of_comp_eq
            (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp)
          (eCotSrc x)) = x := by
    -- Evaluate the conjugated cotangent identity on the chosen common-model element.
    exact congrArg (fun l : M →ₗ[R] M ↦ l x) hconj
  calc
    eIdealTgt.symm
        ((ideal_equiv_ker qB (Ideal.map (algebraMap R B₁) I) hTgt).symm
          (kernel_restrict (qC := qC) (qB := qB) (φ := φAlg.toRingHom) hq
            ((eIdealSrc.trans
              (ideal_equiv_ker qC (Ideal.map (algebraMap R C) I) hSrc)) x))) =
      eIdealTgt.symm
        (ideal_map_restrict (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp
          (eIdealSrc x)) := by
            rw [hkernel]
    _ =
      eCotTgt.symm
        (Ideal.toCotangent (Ideal.map (algebraMap R B₁) I)
          (ideal_map_restrict (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp
            (eIdealSrc x))) := by
              rfl
    _ =
      eCotTgt.symm
        (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
          φAlg
          (ideal_map_le_comap_of_comp_eq
            (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp)
          (eCotSrc x)) := by
            rw [hmap]
    _ = x := by
      simpa [LinearMap.comp_apply] using hx

end

end RingHom
