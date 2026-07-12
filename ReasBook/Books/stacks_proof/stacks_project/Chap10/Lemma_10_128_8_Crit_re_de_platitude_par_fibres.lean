import StacksProject_2024.Chap10.Lemma_10_39_15
import StacksProject_2024.Chap10.Lemma_10_99_4
import StacksProject_2024.Chap10.Lemma_10_100_2
import StacksProject_2024.Chap10.Lemma_10_128_7
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open IsLocalRing
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {S' : Type w} {M : Type x}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
variable [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
variable [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
variable [AddCommGroup M] [Module S M] [Module S' M] [Module R M]
variable [IsScalarTower S S' M] [IsScalarTower R S M] [IsScalarTower R S' M]
variable [Module.FinitePresentation S' M]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S
local notation "ClosedFiberModule" => ClosedFiber ⊗[S] M

/- Domain-style sampling for the fiberwise flatness criterion with essentially finitely presented
local maps:
* primary domain: local commutative algebra of flatness along local ring maps, with closed fibers
  carried by the canonical owner `Ideal.Fiber`;
* sampled owner declarations:
  `Ideal.Fiber`,
  `RingHom.EssFinitePresentation`,
  `flat_over_middleRing_of_flat_closedFiber_and_flat_over_base`,
  `algebraMap_flat_of_flat_of_faithfullyFlat`;
* best owner abstraction: the closed fiber should live on the canonical owners
  `ClosedFiber = Ideal.Fiber (maximalIdeal R) S` and `ClosedFiberModule = ClosedFiber ⊗[S] M`,
  while the conclusions belong on `Module.Flat S M` and `(algebraMap R S).Flat`; the quotient
  models `S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)` and
  `M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))` are only bridge
  views.

Primitive data vs. derived API:
* primitive data: the local diagram `R → S → S'`, essential finite presentation of `R → S` and
  `R → S'`, a finitely presented `S'`-module `M`, flatness of the canonical closed-fiber module
  `ClosedFiberModule` over `ClosedFiber`, and flatness of `M` over `R`;
* derived API: flatness of `M` over `S`, and with the extra source-facing nontriviality hypothesis,
  flatness of the local map `R → S`.

Source/core/bridge triage:
* `source-facing`: the two clauses of Lemma `10.128.8`;
* `core/canonical`: `RingHom.EssFinitePresentation`, `Ideal.Fiber`, `Module.Flat`, and
  `RingHom.Flat`;
* `bridge/view`: the quotient presentations of the closed fiber ring and module.
-/

/-- Helper for Chap10 Lemma 10 128 8 Crit re de platitude par fibres: after a finitely
presented source change, essential finite presentation of the composite makes the target
essentially finitely presented over the new source. -/
private lemma essFinitePresentation_of_comp_finitePresentationSource
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [Algebra.FinitePresentation A B]
    (hAC : Algebra.EssFinitePresentation A C) :
    Algebra.EssFinitePresentation B C := by
  -- Route correction: instead of constructing a localized presentation of `C` over `B`
  -- generator-by-generator, base-change `A → C` to `B` and then compose with the multiplication
  -- retraction `B ⊗[A] C → C`.
  let D : Type (max v w) := B ⊗[A] C
  letI : CommRing D := inferInstance
  letI : Algebra B D := inferInstance
  letI : Algebra C D := Algebra.TensorProduct.rightAlgebra
  let toC : D →ₐ[A] C :=
    Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom A B C) (AlgHom.id A C)
  letI : Algebra D C := toC.toRingHom.toAlgebra
  have hsection_fp : RingHom.FinitePresentation (algebraMap D C) := by
    -- Proof comment: the right tensor inclusion `C → B ⊗[A] C` is finite type by base-changing
    -- the finitely presented `A`-algebra `B`; its composite with multiplication is the identity.
    have hright_finiteType : RingHom.FiniteType (algebraMap C D) := by
      letI : Algebra.FinitePresentation C (C ⊗[A] B) := inferInstance
      have hfpD : Algebra.FinitePresentation C D :=
        Algebra.FinitePresentation.equiv (Algebra.TensorProduct.commRight A C B)
      letI : Algebra.FinitePresentation C D := hfpD
      rw [RingHom.finiteType_algebraMap]
      exact Algebra.FiniteType.of_finitePresentation
    have hcomp_fp :
        RingHom.FinitePresentation ((algebraMap D C).comp (algebraMap C D)) := by
      have hcomp_eq :
          (algebraMap D C).comp (algebraMap C D) = RingHom.id C := by
        ext c
        simp [D, toC, RingHom.algebraMap_toAlgebra]
      rw [hcomp_eq]
      exact RingHom.FinitePresentation.id C
    exact RingHom.FinitePresentation.of_comp_finiteType (algebraMap C D) hcomp_fp
      hright_finiteType
  have hDC : Algebra.EssFinitePresentation D C := by
    -- Proof comment: a finitely presented algebra map is, in particular, essentially finitely
    -- presented; the algebra structure on `C` is the multiplication retraction above.
    have hDfp : Algebra.FinitePresentation D C := by
      rw [← RingHom.finitePresentation_algebraMap]
      exact hsection_fp
    letI : Algebra.FinitePresentation D C := hDfp
    exact Algebra.EssFinitePresentation.of_finitePresentation D C
  have hTowerBDC : IsScalarTower B D C := by
    -- Proof comment: multiplication sends the left tensor inclusion back to the given map
    -- `B → C`, so the composed `B → D → C` structure is the original one.
    exact IsScalarTower.of_algebraMap_eq' (R := B) (S := D) (A := C) <| by
      ext b
      simp [D, toC, RingHom.algebraMap_toAlgebra]
  letI : IsScalarTower B D C := hTowerBDC
  have hBD : Algebra.EssFinitePresentation B D := by
    -- Proof comment: base-change the assumed essential finite presentation of `A → C` along
    -- the finitely presented source map `A → B`.
    letI : Algebra.EssFinitePresentation A C := hAC
    infer_instance
  -- Proof comment: compose the base-changed essential finite presentation with the finitely
  -- presented multiplication retraction.
  exact Algebra.EssFinitePresentation.trans (R := B) (S := D) (T := C) hBD hDC

/-- Helper for Chap10 Lemma 10 128 8 Crit re de platitude par fibres: essential finite
presentation descends across a localization of the source. -/
private lemma essFinitePresentation_of_comp_sourceLocalization
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (N : Submonoid A) [IsLocalization N B]
    (hAC : Algebra.EssFinitePresentation A C) :
    Algebra.EssFinitePresentation B C := by
  have hlocC : IsLocalization (Algebra.algebraMapSubmonoid C N) C := by
    -- Proof comment: denominators already invert in `B`, hence also after mapping from `B` to
    -- `C`; localizing `C` at those units leaves it unchanged.
    refine IsLocalization.at_units (Algebra.algebraMapSubmonoid C N) ?_
    rintro x hx
    rcases hx with ⟨n, hn, rfl⟩
    simpa [IsScalarTower.algebraMap_apply A B C] using
      (IsLocalization.map_units B ⟨n, hn⟩).map (algebraMap B C)
  letI : IsLocalization (Algebra.algebraMapSubmonoid C N) C := hlocC
  letI : Algebra.IsPushout A C B C := Algebra.isPushout_of_isLocalization N B C C
  have hbaseChange : Algebra.EssFinitePresentation B (B ⊗[A] C) := by
    -- Proof comment: base-change the essentially finitely presented `A`-algebra `C` to `B`.
    letI : Algebra.EssFinitePresentation A C := hAC
    infer_instance
  letI : Algebra.EssFinitePresentation B (B ⊗[A] C) := hbaseChange
  let eRing : (B ⊗[A] C) ≃+* C :=
    (Algebra.TensorProduct.commRight A B C).toRingEquiv.trans
      (Algebra.IsPushout.equiv A C B C).toRingEquiv
  have hcompat :
      ∀ b : B, eRing (algebraMap B (B ⊗[A] C) b) = algebraMap B C b := by
    -- Proof comment: the pushout equivalence sends the base-changed source generator back to
    -- its original image in `C`.
    intro b
    dsimp [eRing]
    rw [Algebra.IsPushout.equiv_tmul]
    simp
  let eAlg : (B ⊗[A] C) ≃ₐ[B] C := AlgEquiv.ofRingEquiv (R := B) (f := eRing) hcompat
  -- Proof comment: transport the base-changed essential finite presentation across the canonical
  -- pushout equivalence.
  exact Algebra.EssFinitePresentation.equiv (R := B) (S := B ⊗[A] C) (T := C) eAlg

omit [IsLocalRing R] [IsLocalRing S] [IsLocalRing S'] [IsLocalHom (algebraMap R S)]
  [IsLocalHom (algebraMap S S')] in
/-- Helper for Chap10 Lemma 10 128 8 Crit re de platitude par fibres: if `R → S` and
`R → S'` are essentially of finite presentation, then so is the middle map `S → S'`. -/
private lemma middleTargetEssFinitePresentation_of_comp
    (hRS : RingHom.EssFinitePresentation (algebraMap R S))
    (hRS' : RingHom.EssFinitePresentation (algebraMap R S')) :
    RingHom.EssFinitePresentation (algebraMap S S') := by
  -- Proof comment: unpack `R → S` as a localization of a finitely presented `R`-algebra, cancel
  -- the finitely presented source stage against `R → S'`, then descend across the localization
  -- from that stage to `S`.
  have hRS_alg : Algebra.EssFinitePresentation R S :=
    (RingHom.essFinitePresentation_algebraMap).mp hRS
  have hRS'_alg : Algebra.EssFinitePresentation R S' :=
    (RingHom.essFinitePresentation_algebraMap).mp hRS'
  rw [Algebra.essFinitePresentation_iff_exists_finitePresentation] at hRS_alg
  rcases hRS_alg with ⟨P, hPCommRing, hRP, hPS, hTowerRPS, hPfp, N, hlocS⟩
  letI : CommRing P := hPCommRing
  letI : Algebra R P := hRP
  letI : Algebra P S := hPS
  letI : IsScalarTower R P S := hTowerRPS
  letI : Algebra.FinitePresentation R P := hPfp
  letI : IsLocalization N S := hlocS
  letI : Algebra P S' := ((algebraMap S S').comp (algebraMap P S)).toAlgebra
  letI : IsScalarTower P S S' := IsScalarTower.of_algebraMap_eq' rfl
  have hTowerRPS' : IsScalarTower R P S' := by
    -- Proof comment: the `P → S → S'` algebra structure extends the original `R → S'` map.
    exact IsScalarTower.of_algebraMap_eq (R := R) (S := P) (A := S') fun r ↦ by
      calc
        algebraMap R S' r = algebraMap S S' (algebraMap R S r) := by
              rw [← RingHom.comp_apply]
              exact DFunLike.congr_fun (IsScalarTower.algebraMap_eq R S S') r
        _ = algebraMap S S' (algebraMap P S (algebraMap R P r)) := by
              rw [← RingHom.comp_apply]
              exact congrArg (algebraMap S S') (DFunLike.congr_fun
                (IsScalarTower.algebraMap_eq R P S) r)
        _ = algebraMap P S' (algebraMap R P r) := by
              rfl
  letI : IsScalarTower R P S' := hTowerRPS'
  have hPS' : Algebra.EssFinitePresentation P S' :=
    essFinitePresentation_of_comp_finitePresentationSource
      (A := R) (B := P) (C := S') hRS'_alg
  have hSS'_alg : Algebra.EssFinitePresentation S S' :=
    essFinitePresentation_of_comp_sourceLocalization
      (A := P) (B := S) (C := S') N hPS'
  exact (RingHom.essFinitePresentation_algebraMap).mpr hSS'_alg

/-- Helper for Chap10 Lemma 10 128 8 Crit re de platitude par fibres: essential finite
presentation is unchanged after replacing the source by a `ULift`-equivalent ring. -/
private lemma uliftSourceEssFinitePresentation
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] [Algebra A B]
    (hAB : (algebraMap A B).EssFinitePresentation) :
    let Au : Type max v x := ULift.{max v x, v} A
    letI : Algebra Au B := ULift.algebra' A B
    (algebraMap Au B).EssFinitePresentation := by
  let Au : Type max v x := ULift.{max v x, v} A
  let e : Au ≃+* A := ULift.ringEquiv
  letI : Algebra Au B := ULift.algebra' A B
  have hLift : e.toRingHom.EssFinitePresentation := by
    -- Proof comment: the `ULift` source is algebra-equivalent to itself over `Au`, hence its
    -- comparison map to `A` is essentially of finite presentation.
    letI : Algebra Au A := e.toRingHom.toAlgebra
    rw [RingHom.EssFinitePresentation]
    have hcompat : ∀ a : Au, e a = algebraMap Au A a := by
      intro a
      rfl
    let eAlg : Au ≃ₐ[Au] A := AlgEquiv.ofRingEquiv (R := Au) (f := e) hcompat
    exact Algebra.EssFinitePresentation.equiv (R := Au) (S := Au) (T := A) eAlg
  -- Proof comment: the lifted source map is the composition of the `ULift` equivalence with the
  -- original essentially finitely presented map.
  change ((algebraMap A B).comp e.toRingHom).EssFinitePresentation
  exact hLift.comp hAB

/-- Helper for Chap10 Lemma 10 128 8 Crit re de platitude par fibres: after mapping an ideal
into a lifted ring, quotienting recovers the original quotient ring. -/
private lemma uliftQuotientRingEquivAux
    {A : Type v} [CommRing A] (J : Ideal A) :
    J =
      (J.map (algebraMap A (ULift.{max v x, v} A))).map
        ((ULift.algEquiv (R := A) (A := A) : ULift.{max v x, v} A ≃ₐ[A] A) :
          ULift.{max v x, v} A →+* A) := by
  let eu : ULift.{max v x, v} A ≃ₐ[A] A := ULift.algEquiv (R := A) (A := A)
  -- Proof comment: the `ULift` algebra equivalence is inverse to the canonical lift.
  calc
    J = J.map (RingHom.id A) := by
      simp
    _ = J.map ((eu : ULift.{max v x, v} A →+* A).comp
          (algebraMap A (ULift.{max v x, v} A))) := by
        ext a
        rfl
    _ = (J.map (algebraMap A (ULift.{max v x, v} A))).map
          (eu : ULift.{max v x, v} A →+* A) := by
        rw [Ideal.map_map]

/-- Helper for Chap10 Lemma 10 128 8 Crit re de platitude par fibres: the lifted quotient ring
is canonically ring-equivalent to the original quotient. -/
private noncomputable def uliftQuotientRingEquiv
    {A : Type v} [CommRing A] (J : Ideal A) :
    ((ULift.{max v x, v} A) ⧸ J.map (algebraMap A (ULift.{max v x, v} A))) ≃+*
      (A ⧸ J) :=
  (Ideal.quotientEquivAlg _ _ (ULift.algEquiv (R := A) (A := A))
    (uliftQuotientRingEquivAux (A := A) J)).toRingEquiv

/-- Helper for Chap10 Lemma 10 128 8 Crit re de platitude par fibres: quotienting by
`J • ⊤` commutes with lifting only the module universe. -/
private lemma uliftModuleQuotientEquiv_exists
    {A : Type v} [CommRing A] {N : Type x} [AddCommGroup N] [Module A N] (J : Ideal A) :
    Nonempty ((((ULift.{max v x, x} N) ⧸
      (J • (⊤ : Submodule A (ULift.{max v x, x} N)))) ≃ₗ[A ⧸ J]
        (N ⧸ (J • (⊤ : Submodule A N))))) := by
  let eA :
      ((ULift.{max v x, x} N) ⧸
          (J • (⊤ : Submodule A (ULift.{max v x, x} N)))) ≃ₗ[A]
        (N ⧸ (J • (⊤ : Submodule A N))) :=
    Submodule.Quotient.equiv
      (J • (⊤ : Submodule A (ULift.{max v x, x} N)))
      (J • (⊤ : Submodule A N))
      (ULift.moduleEquiv : ULift.{max v x, x} N ≃ₗ[A] N)
      (by
        -- Proof comment: the lifted module equivalence preserves the ideal-generated top
        -- submodule exactly.
        simpa [Submodule.map_smul''])
  -- Proof comment: the quotient modules carry their canonical `A / J`-actions, so the same
  -- equivalence upgrades to the quotient owner.
  exact ⟨eA.extendScalarsOfSurjective Ideal.Quotient.mk_surjective⟩

/-- Helper for Chap10 Lemma 10 128 8 Crit re de platitude par fibres: the quotient-module
equivalence produced by the lifted module comparison. -/
private noncomputable def uliftModuleQuotientEquiv
    {A : Type v} [CommRing A] {N : Type x} [AddCommGroup N] [Module A N] (J : Ideal A) :
    ((ULift.{max v x, x} N) ⧸ (J • (⊤ : Submodule A (ULift.{max v x, x} N)))) ≃ₗ[A ⧸ J]
      (N ⧸ (J • (⊤ : Submodule A N))) :=
  Classical.choice (uliftModuleQuotientEquiv_exists (A := A) (N := N) J)

omit [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Module R M] [IsScalarTower R S M] in
/-- Helper for Chap10 Lemma 10 128 8 Crit re de platitude par fibres: closed-fiber flatness on
the canonical tensor owner gives flatness of the quotient presentation. -/
private lemma closedFiberQuotientModuleFlat_of_closedFiberTensorFlat
    (hflat_closedFiber : Module.Flat ClosedFiber ClosedFiberModule) :
    Module.Flat (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))
      (M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))) := by
  let I : Ideal S := Ideal.map (algebraMap R S) (maximalIdeal R)
  let Abar : Type v := S ⧸ I
  let eRing : Abar ≃+* ClosedFiber :=
    (closedFiber_quotient_equiv (R := R) (S := S)).toRingEquiv
  letI : Algebra Abar ClosedFiber := eRing.toRingHom.toAlgebra
  letI : Algebra ClosedFiber Abar := eRing.symm.toRingHom.toAlgebra
  letI : Module ClosedFiber (M ⧸ (I • (⊤ : Submodule S M))) :=
    Module.compHom (M ⧸ (I • (⊤ : Submodule S M))) (algebraMap ClosedFiber Abar)
  letI : IsScalarTower Abar ClosedFiber (M ⧸ (I • (⊤ : Submodule S M))) :=
    IsScalarTower.of_algebraMap_smul (R := Abar) (A := ClosedFiber)
      (M := M ⧸ (I • (⊤ : Submodule S M))) fun a q ↦ by
        -- Proof comment: the two quotient-ring actions agree because `closedFiber_quotient_equiv`
        -- is inverse to itself on representatives.
        change ((algebraMap ClosedFiber Abar (algebraMap Abar ClosedFiber a)) • q :
          M ⧸ (I • (⊤ : Submodule S M))) = a • q
        change (((closedFiber_quotient_equiv (R := R) (S := S)).symm
          ((closedFiber_quotient_equiv (R := R) (S := S)) a)) • q :
            M ⧸ (I • (⊤ : Submodule S M))) = a • q
        simp
  have hflatAbarClosedFiber : Module.Flat Abar ClosedFiber := by
    -- Proof comment: the closed-fiber ring is flat over the quotient ring because the two rings
    -- are equivalent.
    have hcompat : ∀ a : Abar, eRing.symm (eRing a) = a := by
      intro a
      simp
    let eAlg : ClosedFiber ≃ₐ[Abar] Abar :=
      AlgEquiv.ofRingEquiv (R := Abar) (f := eRing.symm) hcompat
    exact Module.Flat.of_linearEquiv eAlg.toLinearEquiv
  have hflatClosedFiberQuot :
      Module.Flat ClosedFiber (M ⧸ (I • (⊤ : Submodule S M))) := by
    let eOwner :
        ClosedFiberModule ≃ₗ[ClosedFiber] (M ⧸ (I • (⊤ : Submodule S M))) :=
      closed_fiber_module_quotient_equiv (R := R) (S := S) (M := M)
    -- Proof comment: move the flatness hypothesis from the tensor owner to the quotient owner.
    letI : Module.Flat ClosedFiber ClosedFiberModule := hflat_closedFiber
    exact Module.Flat.of_linearEquiv eOwner.symm
  letI : Module.Flat Abar ClosedFiber := hflatAbarClosedFiber
  letI : Module.Flat ClosedFiber (M ⧸ (I • (⊤ : Submodule S M))) := hflatClosedFiberQuot
  -- Proof comment: compose quotient-ring flatness of the closed fiber with flatness of the
  -- quotient module over the closed fiber.
  exact Module.Flat.trans Abar ClosedFiber (M ⧸ (I • (⊤ : Submodule S M)))

/-- Helper for Chap10 Lemma 10 128 8 Crit re de platitude par fibres: quotient flatness
transports when both the base ring and module are raised to a common `ULift` universe. -/
private lemma uliftQuotientFlat_of_quotientFlat
    {A : Type v} [CommRing A] {N : Type x} [AddCommGroup N] [Module A N]
    (J : Ideal A)
    (hflat : Module.Flat (A ⧸ J) (N ⧸ (J • (⊤ : Submodule A N)))) :
    let Au : Type max v x := ULift.{max v x, v} A
    let Nu : Type max v x := ULift.{max v x, x} N
    let Ju : Ideal Au := J.map (algebraMap A Au)
    Module.Flat (Au ⧸ Ju) (Nu ⧸ (Ju • (⊤ : Submodule Au Nu))) := by
  let Au : Type max v x := ULift.{max v x, v} A
  let Nu : Type max v x := ULift.{max v x, x} N
  let Ju : Ideal Au := J.map (algebraMap A Au)
  let T : Type max v x := Au ⧸ Ju
  let B : Type v := A ⧸ J
  let eRing : T ≃+* B := uliftQuotientRingEquiv J
  letI : Algebra T B := eRing.toRingHom.toAlgebra
  letI : Module T (N ⧸ (J • (⊤ : Submodule A N))) :=
    Module.compHom (N ⧸ (J • (⊤ : Submodule A N))) (algebraMap T B)
  letI : IsScalarTower A T (N ⧸ (J • (⊤ : Submodule A N))) :=
    IsScalarTower.of_compHom A T (N ⧸ (J • (⊤ : Submodule A N)))
  letI : IsScalarTower T B (N ⧸ (J • (⊤ : Submodule A N))) :=
    IsScalarTower.of_compHom T B (N ⧸ (J • (⊤ : Submodule A N)))
  have hflatTB : Module.Flat T B := by
    -- Proof comment: the lifted quotient ring is ring-equivalent to the original quotient ring.
    have hcompat : ∀ t : T, eRing.symm (eRing t) = t := by
      intro t
      simp
    let eAlg : B ≃ₐ[T] T := AlgEquiv.ofRingEquiv (R := T) (f := eRing.symm) hcompat
    exact Module.Flat.of_linearEquiv eAlg.toLinearEquiv
  have hflatTarget : Module.Flat T (N ⧸ (J • (⊤ : Submodule A N))) := by
    -- Proof comment: transport the original quotient flatness across the quotient-ring
    -- equivalence.
    letI : Module.Flat T B := hflatTB
    letI : Module.Flat B (N ⧸ (J • (⊤ : Submodule A N))) := hflat
    exact Module.Flat.trans T B (N ⧸ (J • (⊤ : Submodule A N)))
  have hJu_restrict :
      ((Ju • (⊤ : Submodule Au Nu)).restrictScalars A) =
        (J • (⊤ : Submodule A Nu)) := by
    -- Proof comment: restricting the lifted denominator back to `A` recovers the original
    -- quotient denominator on the lifted module.
    simpa [Ju] using
      (Ideal.smul_restrictScalars
        (R := A) (S := Au) (M := Nu) (I := J) (N := (⊤ : Submodule Au Nu)))
  have hsurjAT : Function.Surjective (algebraMap A T) := by
    -- Proof comment: every lifted quotient class has a representative from the original ring.
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rcases y with ⟨a⟩
    exact ⟨a, rfl⟩
  have eOwnerA :
      (Nu ⧸ (Ju • (⊤ : Submodule Au Nu))) ≃ₗ[A]
        N ⧸ (J • (⊤ : Submodule A N)) := by
    let eRestrict :
        (Nu ⧸ ((Ju • (⊤ : Submodule Au Nu)).restrictScalars A)) ≃ₗ[A]
          Nu ⧸ (Ju • (⊤ : Submodule Au Nu)) :=
      Submodule.Quotient.restrictScalarsEquiv A (Ju • (⊤ : Submodule Au Nu))
    let eDenom :
        (Nu ⧸ ((Ju • (⊤ : Submodule Au Nu)).restrictScalars A)) ≃ₗ[A]
          Nu ⧸ (J • (⊤ : Submodule A Nu)) :=
      Submodule.quotEquivOfEq
        ((Ju • (⊤ : Submodule Au Nu)).restrictScalars A)
        (J • (⊤ : Submodule A Nu))
        hJu_restrict
    let eULift :
        (Nu ⧸ (J • (⊤ : Submodule A Nu))) ≃ₗ[A]
          N ⧸ (J • (⊤ : Submodule A N)) :=
      (uliftModuleQuotientEquiv (A := A) (N := N) J).restrictScalars A
    -- Proof comment: normalize the lifted quotient first as an `A`-module, then upgrade scalars
    -- through the quotient map.
    exact eRestrict.symm.trans (eDenom.trans eULift)
  have eOwner :
      (Nu ⧸ (Ju • (⊤ : Submodule Au Nu))) ≃ₗ[T]
        N ⧸ (J • (⊤ : Submodule A N)) :=
    eOwnerA.extendScalarsOfSurjective hsurjAT
  letI : Module.Flat T (N ⧸ (J • (⊤ : Submodule A N))) := hflatTarget
  -- Proof comment: remove the lifted quotient owner by the linear equivalence above.
  exact Module.Flat.of_linearEquiv eOwner

/-- Helper for Chap10 Lemma 10 128 8 Crit re de platitude par fibres: flatness over a source
ring kills the lifted quotient `Tor₁` term for the mapped ideal. -/
private lemma uliftMappedIdealTorOneQuotientVanishes_of_flat
    {A : Type u} {B : Type v} {N : Type x}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (I : Ideal A) (hflat : Module.Flat A N) :
    let Bu : Type max v x := ULift.{max v x, v} B
    let Nu : Type max v x := ULift.{max v x, x} N
    let IB : Ideal B := Ideal.map (algebraMap A B) I
    let Iu : Ideal Bu := IB.map (algebraMap B Bu)
    IsZero (Tor₁[Bu](Nu, Bu ⧸ Iu)) := by
  let Bu : Type max v x := ULift.{max v x, v} B
  let Nu : Type max v x := ULift.{max v x, x} N
  let IB : Ideal B := Ideal.map (algebraMap A B) I
  let Iu : Ideal Bu := IB.map (algebraMap B Bu)
  have hsource_inj :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul A N).comp I.subtype)) := by
    -- Proof comment: flatness over `A` makes the ideal multiplication tensor map injective.
    exact ideal_tensor_to_module_injective_of_flat (A := A) (I := I) (N := N) hflat
  have hIB_inj :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul B N).comp IB.subtype)) := by
    -- Proof comment: transport injectivity from the source ideal to its image in `B`.
    simpa [IB] using
      mapped_ideal_tensor_to_module_injective_of_source_injective
        (R := A) (R' := B) (I := I) (N := N) hsource_inj
  have hIB_Nu_inj :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul B Nu).comp IB.subtype)) := by
    -- Proof comment: raise only the module universe while keeping the `B`-ideal fixed.
    simpa [Nu] using
      ulift_ideal_tensor_injective (A := B) (I := IB) (N := N) hIB_inj
  have hIu_inj :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul Bu Nu).comp Iu.subtype)) := by
    -- Proof comment: finally transport injectivity to the mapped ideal in the lifted ring.
    simpa [Iu] using
      mapped_ideal_tensor_to_module_injective_of_source_injective
        (R := B) (R' := Bu) (I := IB) (N := Nu) hIB_Nu_inj
  have hker :
      LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul Bu Nu).comp Iu.subtype)) = ⊥ :=
    LinearMap.ker_eq_bot.2 hIu_inj
  -- Proof comment: Remark `10.75.9`, exposed through Lemma `10.100.2`, identifies this zero
  -- kernel with the quotient `Tor₁` owner.
  exact tor_one_module_quotient_vanishes_of_ker_eq_bot (A := Bu) (I := Iu) (N := Nu) hker

-- Proof sketch: avoid the failed synchronized Noetherian-stage route. First prove the middle map
-- `S → S'` is essentially of finite presentation, then raise `S` and `M` to a common `ULift`
-- universe and apply Lemma `10.128.7` to the lifted local map. The closed-fiber flatness and
-- base-flatness hypotheses are transported to the quotient-flatness and `Tor₁` inputs required by
-- that criterion, and the resulting lifted flatness descends back along `ULift`.
/-- Lemma 10.128.8 (Critère de platitude par fibres) (2): under the same hypotheses, the
`S'`-module `M` is flat over `S`. Here the fiberwise hypothesis is expressed on the canonical
closed-fiber owner `ClosedFiberModule = ((maximalIdeal R).Fiber S) ⊗[S] M` over
`ClosedFiber = (maximalIdeal R).Fiber S`, not on a separate quotient-packaged wrapper. -/
@[stacks 00R7]
theorem flat_over_middleRing_of_essFinitePresentation_of_flat_closedFiber_and_flat_over_base
    (hRS : RingHom.EssFinitePresentation (algebraMap R S))
    (hRS' : RingHom.EssFinitePresentation (algebraMap R S'))
    (hflat_closedFiber : Module.Flat ClosedFiber ClosedFiberModule) (hflat_R : Module.Flat R M) :
    Module.Flat S M := by
  -- Route correction: the old proof tried to synchronize Noetherian approximation stages. The
  -- stable route applies the already proved essential finite-presentation local criterion after
  -- lifting `S` and `M` to one universe.
  have _tower_R_S'_M : IsScalarTower R S' M := inferInstance
  let Su : Type max v x := ULift.{max v x, v} S
  let Mu : Type max v x := ULift.{max v x, x} M
  let I : Ideal S := Ideal.map (algebraMap R S) (maximalIdeal R)
  let Ju : Ideal Su := I.map (algebraMap S Su)
  let eSu : Su ≃+* S := ULift.ringEquiv
  letI : Algebra Su S' := ULift.algebra' S S'
  letI : IsLocalRing Su := RingEquiv.isLocalRing eSu.symm
  letI : IsLocalHom eSu.toRingHom := Function.Surjective.isLocalHom _ eSu.surjective
  letI : IsLocalHom (algebraMap Su S') := by
    -- Proof comment: the lifted local map is the composite `ULift S → S → S'`.
    change IsLocalHom ((algebraMap S S').comp eSu.toRingHom)
    exact RingHom.isLocalHom_comp _ _
  letI : Module S' Mu := inferInstance
  letI : Module Su Mu := inferInstance
  letI : IsScalarTower Su S' Mu := inferInstance
  letI : Module.FinitePresentation S' Mu := by
    -- Proof comment: finite presentation survives replacing the module by the linearly
    -- equivalent `ULift` copy.
    exact Module.FinitePresentation.of_equiv
      ((ULift.moduleEquiv : Mu ≃ₗ[S'] M).symm)
  have hSS' : RingHom.EssFinitePresentation (algebraMap S S') :=
    middleTargetEssFinitePresentation_of_comp hRS hRS'
  have hSuS' : RingHom.EssFinitePresentation (algebraMap Su S') := by
    -- Proof comment: replace the source `S` of the middle map by the equivalent lifted ring.
    simpa [Su, eSu] using
      uliftSourceEssFinitePresentation (A := S) (B := S') hSS'
  have hJu : Ju ≠ ⊤ := by
    -- Proof comment: properness of the image of the maximal ideal is preserved by the lifted
    -- quotient-ring equivalence.
    let T : Type max v x := Su ⧸ Ju
    let B : Type v := S ⧸ I
    let eRing : T ≃+* B := uliftQuotientRingEquiv I
    have hI : I ≠ ⊤ := (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)).ne
    letI : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hI
    letI : Nontrivial T := eRing.toEquiv.nontrivial
    exact Ideal.Quotient.nontrivial_iff.mp inferInstance
  have hflatQuot : Module.Flat (Su ⧸ Ju) (Mu ⧸ (Ju • (⊤ : Submodule Su Mu))) := by
    -- Proof comment: transport canonical closed-fiber flatness first to the quotient presentation
    -- over `S / I`, then to the lifted quotient over `Su / Ju`.
    have hflatI : Module.Flat (S ⧸ I) (M ⧸ (I • (⊤ : Submodule S M))) := by
      simpa [I] using
        closedFiberQuotientModuleFlat_of_closedFiberTensorFlat
          (R := R) (S := S) (M := M) hflat_closedFiber
    simpa [Su, Mu, Ju, I] using
      uliftQuotientFlat_of_quotientFlat (A := S) (N := M) I hflatI
  have hTor : IsZero (Tor₁[Su](Mu, Su ⧸ Ju)) := by
    -- Proof comment: base flatness makes the source ideal multiplication injective; the mapped
    -- ideal and `ULift` transport helpers turn that into the required quotient `Tor₁` vanishing.
    simpa [Su, Mu, Ju, I] using
      uliftMappedIdealTorOneQuotientVanishes_of_flat
        (A := R) (B := S) (N := M) (maximalIdeal R) hflat_R
  have hflatSuMu : Module.Flat Su Mu := by
    -- Proof comment: all inputs now match Lemma `10.128.7` for the lifted local map.
    exact
      flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal_of_essFinitePresentation
        (R := Su) (S := S') (M := Mu) hSuS' Ju hJu hTor hflatQuot
  -- Proof comment: descend flatness through the canonical `ULift` ring and module equivalences.
  exact ulift_flat_descend (A := S) (N := M) hflatSuMu

/-- Helper for Chap10 Lemma 10 128 8 Crit re de platitude par fibres: a nonzero finitely
presented module over a local target is faithfully flat over the middle ring once it is flat
there. The target ring is an explicit parameter so the local and finite-presentation target
context is available inside the proof. -/
private theorem faithfullyFlatOverMiddleRing_of_flat_and_nontrivialTarget
    (S' : Type w) [CommRing S'] [Algebra S S'] [IsLocalRing S']
    [IsLocalHom (algebraMap S S')] [Module S' M] [IsScalarTower S S' M]
    [Module.FinitePresentation S' M] [Nontrivial M]
    (hflat_S : Module.Flat S M) : Module.FaithfullyFlat S M := by
  -- Proof comment: install the flatness conclusion so the residue-field criterion for faithful
  -- flatness can be applied over the local middle ring.
  letI : Module.Flat S M := hflat_S
  let P' : Submodule S' M := maximalIdeal S' • (⊤ : Submodule S' M)
  let P : Submodule S M := P'.restrictScalars S
  have hquot_P' : Nontrivial (M ⧸ P') := by
    -- Proof comment: Nakayama over the local target ring makes the maximal-ideal quotient of
    -- the nonzero finite module nonzero.
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
    -- Proof comment: locality of `S → S'` sends the maximal ideal of `S` into that of `S'`.
    refine Submodule.smul_le.2 fun a ha m hm ↦ ?_
    change a • m ∈ P'.restrictScalars S
    change a • m ∈ P'
    rw [← IsScalarTower.algebraMap_smul S' a m]
    have hmem_map : algebraMap S S' a ∈ Ideal.map (algebraMap S S') (maximalIdeal S) :=
      Ideal.mem_map_of_mem _ ha
    have hmem : algebraMap S S' a ∈ maximalIdeal S' :=
      (IsLocalRing.map_maximalIdeal_le (algebraMap S S')) hmem_map
    have htop_mem : m ∈ (⊤ : Submodule S' M) := by
      simp
    exact Submodule.smul_mem_smul hmem htop_mem
  have hquot_S : Nontrivial (M ⧸ (maximalIdeal S • (⊤ : Submodule S M))) :=
    (Submodule.factor_surjective hsmul).nontrivial
  -- Proof comment: over a local ring, flatness plus a nonzero residue-field fiber is faithful
  -- flatness.
  refine faithfullyFlat_iff_forall_nontrivial_tensor_residueField.2 fun m hm ↦ ?_
  have hm_eq : m = maximalIdeal S := IsLocalRing.eq_maximalIdeal hm
  subst hm_eq
  exact (nontrivial_tensor_residueField_iff_nontrivial_quotSMul (maximalIdeal S)).2 hquot_S

-- Proof sketch: approximate the two essentially finitely presented local maps `R → S` and
-- `R → S'` together with the finitely presented `S'`-module `M` by a sufficiently large Noetherian
-- stage using Lemmas `10.127.11` and `10.127.13`. Lemma `10.128.3` descends the flatness of `M`
-- over `R` and of the canonical closed fiber `ClosedFiberModule` over `ClosedFiber` to that stage,
-- where Lemma `10.99.15` applies. Base-changing the resulting stagewise flatness statement back to
-- `R → S → S'` yields flatness of the local map `R → S`.
/-- Chap10 Lemma 10 128 8 Crit re de platitude par fibres: for local rings `R`, `S`, `S'` and
local homomorphisms `R → S → S'`, assume `R → S` and `R → S'` are essentially of finite
presentation, `M` is a nonzero finitely presented `S'`-module, the canonical closed fiber
`ClosedFiberModule = ((maximalIdeal R).Fiber S) ⊗[S] M`, equivalently
`M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))`, is flat over
`ClosedFiber = (maximalIdeal R).Fiber S`, equivalently
`S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`, and `M` is flat over `R`. Then `R → S` is
flat. -/
@[stacks 00R7]
theorem algebraMap_flat_of_essFinitePresentation_of_flat_closedFiber_and_flat_over_base
    (hRS : RingHom.EssFinitePresentation (algebraMap R S))
    (hRS' : RingHom.EssFinitePresentation (algebraMap R S')) [Nontrivial M]
    (hflat_closedFiber : Module.Flat ClosedFiber ClosedFiberModule) (hflat_R : Module.Flat R M) :
    (algebraMap R S).Flat := by
  -- Proof comment: first consume clause (2), which is the genuine approximation statement.
  have hflat_S : Module.Flat S M :=
    flat_over_middleRing_of_essFinitePresentation_of_flat_closedFiber_and_flat_over_base
      hRS hRS' hflat_closedFiber hflat_R
  letI : Module.Flat S M := hflat_S
  have hff_S : Module.FaithfullyFlat S M :=
    faithfullyFlatOverMiddleRing_of_flat_and_nontrivialTarget S' hflat_S
  have hflatRRestrict : Module.Flat R (RestrictScalars R S M) := by
    -- Proof comment: move the given `R`-flatness to the explicit restricted-scalar owner used by
    -- the descent theorem.
    letI : Module.Flat R M := hflat_R
    exact Module.Flat.of_linearEquiv (restrictScalars_linearEquiv (R := R) (S := S) (M := M))
  letI : Module.Flat R (RestrictScalars R S M) := hflatRRestrict
  letI : Module.FaithfullyFlat S M := hff_S
  -- Proof comment: faithful-flat descent of flatness is exactly Lemma `10.39.10`.
  simpa using algebraMap_flat_of_flat_of_faithfullyFlat (R := R) (S := S) (M := M)

end
