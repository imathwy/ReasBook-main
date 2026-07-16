import stacks_proof.stacks_project.Chap10.Lemma_10_99_11.QuotientLocalization

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

/-- Helper for Lemma 10.99.11: quotienting a `ULift` of the module by `K • ⊤` gives the same
closed fiber as quotienting the original module. -/
lemma ulift_module_quotient_equiv_exists
    {A : Type u} [CommRing A] {K : Ideal A}
    {N : Type w} [AddCommGroup N] [Module A N] :
    Nonempty ((((ULift.{u} N) ⧸ (K • (⊤ : Submodule A (ULift.{u} N)))) ≃ₗ[A ⧸ K]
      (N ⧸ (K • (⊤ : Submodule A N))))) := by
  let eA :
      ((ULift.{u} N) ⧸ (K • (⊤ : Submodule A (ULift.{u} N)))) ≃ₗ[A]
        (N ⧸ (K • (⊤ : Submodule A N))) :=
    Submodule.Quotient.equiv
      (K • (⊤ : Submodule A (ULift.{u} N)))
      (K • (⊤ : Submodule A N))
      (ULift.moduleEquiv : ULift.{u} N ≃ₗ[A] N)
      (by
        -- Proof comment: `ULift.moduleEquiv` preserves the denominator `K • ⊤`.
        simpa [Submodule.map_smul''])
  -- Proof comment: both quotient modules carry the canonical `A ⧸ K`-action.
  exact ⟨eA.extendScalarsOfSurjective Ideal.Quotient.mk_surjective⟩

/-- Helper for Lemma 10.99.11: choose the quotient-module equivalence induced by
`ULift.moduleEquiv`. -/
noncomputable def ulift_module_quotient_equiv
    {A : Type u} [CommRing A] {K : Ideal A}
    {N : Type w} [AddCommGroup N] [Module A N] :
    ((ULift.{u} N) ⧸ (K • (⊤ : Submodule A (ULift.{u} N)))) ≃ₗ[A ⧸ K]
      (N ⧸ (K • (⊤ : Submodule A N))) :=
  Classical.choice ulift_module_quotient_equiv_exists

/-- Helper for Lemma 10.99.11: quotienting the lifted base ring by the image of `K` recovers the
original quotient ring. -/
lemma ulift_quotient_ring_equiv_aux
    {A : Type u} [CommRing A] (K : Ideal A) {N : Type w} [AddCommGroup N] [Module A N] :
    K =
      (K.map (algebraMap A (ULift.{w} A))).map
        ((ULift.algEquiv (R := A) (A := A) : ULift.{w} A ≃ₐ[A] A) : ULift.{w} A →+* A) := by
  let eu : ULift.{w} A ≃ₐ[A] A := ULift.algEquiv (R := A) (A := A)
  -- Proof comment: `ULift.algEquiv` is inverse to the canonical lift `A → ULift A`.
  calc
    K = K.map (RingHom.id A) := by simp
    _ = K.map ((eu : ULift.{w} A →+* A).comp (algebraMap A (ULift.{w} A))) := by
          ext a
          rfl
    _ = (K.map (algebraMap A (ULift.{w} A))).map (eu : ULift.{w} A →+* A) := by
          rw [Ideal.map_map]

/-- Helper for Lemma 10.99.11: the `ULift` presentation of the quotient ring is canonically
ring-equivalent to the original quotient ring. -/
noncomputable def ulift_quotient_ring_equiv
    {A : Type u} [CommRing A] (K : Ideal A) {N : Type w} [AddCommGroup N] [Module A N] :
    ((ULift.{w} A) ⧸ K.map (algebraMap A (ULift.{w} A))) ≃+* (A ⧸ K) :=
  (Ideal.quotientEquivAlg _ _ (ULift.algEquiv (R := A) (A := A))
    (ulift_quotient_ring_equiv_aux (K := K) (N := N))).toRingEquiv

/-- Helper for Lemma 10.99.11: lifting a local homomorphism through `ULift` preserves the local
hom property. -/
lemma ringHom_ulift_isLocalHom
    {A : Type u} {B : Type v} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (g : A →+* B) [IsLocalHom g] :
    IsLocalHom (RingHom.ulift g) := by
  letI : IsLocalRing (ULift A) := by
    exact IsLocalRing.of_surjective'
      (ULift.ringEquiv.symm.toRingHom : A →+* ULift A)
      (by
        intro x
        exact ⟨ULift.down x, by cases x <;> rfl⟩)
  letI : IsLocalRing (ULift B) := by
    exact IsLocalRing.of_surjective'
      (ULift.ringEquiv.symm.toRingHom : B →+* ULift B)
      (by
        intro x
        exact ⟨ULift.down x, by cases x <;> rfl⟩)
  letI : IsLocalHom (ULift.ringEquiv.toRingHom : ULift A →+* A) :=
    Function.Surjective.isLocalHom _ ULift.ringEquiv.surjective
  letI : IsLocalHom (ULift.ringEquiv.symm.toRingHom : B →+* ULift B) :=
    Function.Surjective.isLocalHom _ ULift.ringEquiv.symm.surjective
  -- Proof comment: the lifted map is the original local map conjugated by the canonical
  -- `ULift` ring equivalences.
  simpa [RingHom.ulift] using
    (RingHom.isLocalHom_comp (ULift.ringEquiv.symm.toRingHom)
      (g.comp ULift.ringEquiv.toRingHom))

/-- Helper for Lemma 10.99.11: injectivity of `K ⊗[A] N → N` is unchanged by lifting only the
module universe. -/
lemma ulift_injective_tensor_transport
    {A : Type u} [CommRing A] {K : Ideal A}
    {N : Type w} [AddCommGroup N] [Module A N]
    (hinj : Function.Injective (TensorProduct.lift ((LinearMap.lsmul A N).comp K.subtype))) :
    Function.Injective
      (TensorProduct.lift ((LinearMap.lsmul A (ULift.{u} N)).comp K.subtype)) := by
  let μ : K ⊗[A] N →ₗ[A] N :=
    TensorProduct.lift ((LinearMap.lsmul A N).comp K.subtype)
  let μu : K ⊗[A] ULift.{u} N →ₗ[A] ULift.{u} N :=
    TensorProduct.lift ((LinearMap.lsmul A (ULift.{u} N)).comp K.subtype)
  let eTensor :
      K ⊗[A] ULift.{u} N ≃ₗ[A] K ⊗[A] N :=
    TensorProduct.congr (LinearEquiv.refl A K) (ULift.moduleEquiv : ULift.{u} N ≃ₗ[A] N)
  have hSquare :
      μ.comp eTensor.toLinearMap =
        (ULift.moduleEquiv : ULift.{u} N ≃ₗ[A] N).toLinearMap.comp μu := by
    -- Proof comment: once `ULift N` is identified with `N`, both tensor multiplication maps are
    -- literally the same scalar-action map on pure tensors.
    ext k n
    rfl
  intro x y hxy
  apply eTensor.injective
  apply hinj
  calc
    μ (eTensor x) =
        (ULift.moduleEquiv : ULift.{u} N ≃ₗ[A] N) (μu x) := by
          simpa [LinearMap.comp_apply] using congrArg (fun f ↦ f x) hSquare
    _ =
        (ULift.moduleEquiv : ULift.{u} N ≃ₗ[A] N) (μu y) := by
          simpa using congrArg (fun z ↦ (ULift.moduleEquiv : ULift.{u} N ≃ₗ[A] N) z) hxy
    _ = μ (eTensor y) := by
          simpa [LinearMap.comp_apply] using (congrArg (fun f ↦ f y) hSquare).symm

-- Proof sketch: lift the local ring map, the module, and the ideal to a common universe; turn
-- the given `Tor₁` vanishing into injectivity of `K ⊗ N → N`, transport that injectivity to the
-- lifted mapped ideal, transport the closed-fiber flatness by the quotient `ULift` equivalences,
-- apply Lemma `10.99.10` upstairs, and descend flatness back to the original module.
/-- Helper for Lemma 10.99.11: a universe-stable wrapper around Lemma `10.99.10`. -/
theorem flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal_univ
    {A : Type u} {B : Type v} {N : Type w}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Module.Finite B N]
    (K : Ideal A) (hK : K ≠ ⊤)
    (hμ_inj : Function.Injective (TensorProduct.lift ((LinearMap.lsmul A N).comp K.subtype)))
    (hflat : Module.Flat (A ⧸ K) (N ⧸ (K • (⊤ : Submodule A N)))) :
    Module.Flat A N := by
  let Au : Type max u w := ULift.{w} A
  let Bu : Type max v w := ULift.{w} B
  let Nu : Type max u w := ULift.{u} N
  let Ku : Ideal Au := K.map (algebraMap A Au)
  let T : Type max u w := Au ⧸ Ku
  let C : Type u := A ⧸ K
  let eRing : T ≃+* C := ulift_quotient_ring_equiv (A := A) (K := K) (N := N)
  let _ : Algebra A Au := ULift.algebra
  let _ : Algebra A Bu := ULift.algebra
  let _ : Algebra Au Bu := ULift.algebra' A Bu
  letI : IsLocalRing Au := by
    exact IsLocalRing.of_surjective'
      (ULift.ringEquiv.symm.toRingHom : A →+* Au)
      (by
        intro x
        exact ⟨ULift.down x, by cases x <;> rfl⟩)
  letI : IsLocalRing Bu := by
    exact IsLocalRing.of_surjective'
      (ULift.ringEquiv.symm.toRingHom : B →+* Bu)
      (by
        intro x
        exact ⟨ULift.down x, by cases x <;> rfl⟩)
  letI : IsNoetherianRing Au := by
    exact isNoetherianRing_of_ringEquiv A (ULift.ringEquiv : Au ≃+* A).symm
  letI : IsNoetherianRing Bu := by
    exact isNoetherianRing_of_ringEquiv B (ULift.ringEquiv : Bu ≃+* B).symm
  letI : IsLocalHom (algebraMap Au Bu) := by
    simpa [Au, Bu] using ringHom_ulift_isLocalHom (g := algebraMap A B)
  letI : Algebra Bu B := (ULift.ringEquiv : Bu ≃+* B).toRingHom.toAlgebra
  letI : Module Bu N := Module.compHom N (algebraMap Bu B)
  let σ : B →+* Bu := ULift.ringEquiv.symm.toRingHom
  letI : RingHomSurjective σ := RingHomSurjective.mk ULift.ringEquiv.symm.surjective
  let f : N →ₛₗ[σ] N :=
    { toFun := id
      map_add' := by simp
      map_smul' := by
        intro c x
        rfl }
  letI : Module.Finite Bu N := Module.Finite.of_surjective f (fun x ↦ ⟨x, rfl⟩)
  letI : Module.Finite Bu Nu :=
    Module.Finite.equiv (ULift.moduleEquiv (R := Bu) (M := N)).symm
  have hKu : Ku ≠ ⊤ := by
    let _ : Nontrivial C := Ideal.Quotient.nontrivial_iff.mpr hK
    let _ : Nontrivial T := eRing.toEquiv.nontrivial
    exact Ideal.Quotient.nontrivial_iff.mp inferInstance
  have hμu_source_inj :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul A Nu).comp K.subtype)) := by
    -- Proof comment: first lift only the module universe on the source injective tensor map.
    simpa [Nu] using ulift_injective_tensor_transport (A := A) (K := K) (N := N) hμ_inj
  have hμu_inj :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul Au Nu).comp Ku.subtype)) := by
    -- Proof comment: then rewrite the left tensor factor from `K` to its image `Ku` in the
    -- lifted base ring.
    simpa [Ku] using
      mapped_ideal_tensor_to_module_injective_of_source_injective
        (A := A) (B := Au) (I := K) (N := Nu) hμu_source_inj
  have hTor_u :
      IsZero (Tor₁[Au](Nu, Au ⧸ Ku)) := by
    have hker_u :
        LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul Au Nu).comp Ku.subtype)) = ⊥ := by
      exact LinearMap.ker_eq_bot.mpr hμu_inj
    -- Proof comment: upstairs, the same kernel-to-Tor bridge gives the required Tor-vanishing.
    simpa [Ku] using
      tor_one_module_quotient_vanishes_of_ker_eq_bot (A := Au) (J := Ku) (N := Nu) hker_u
  letI : Algebra T C := eRing.toRingHom.toAlgebra
  letI : Module T (N ⧸ (K • (⊤ : Submodule A N))) :=
    Module.compHom (N ⧸ (K • (⊤ : Submodule A N))) (algebraMap T C)
  letI : IsScalarTower A T (N ⧸ (K • (⊤ : Submodule A N))) :=
    IsScalarTower.of_compHom A T (N ⧸ (K • (⊤ : Submodule A N)))
  letI : IsScalarTower T C (N ⧸ (K • (⊤ : Submodule A N))) :=
    IsScalarTower.of_compHom T C (N ⧸ (K • (⊤ : Submodule A N)))
  have hKu_restrict :
      ((Ku • (⊤ : Submodule Au Nu)).restrictScalars A) =
        (K • (⊤ : Submodule A Nu)) := by
    -- Proof comment: restricting the lifted denominator from `Au` back to `A` recovers the
    -- original denominator `K • ⊤`.
    simpa [Ku] using
      (Ideal.smul_restrictScalars
        (R := A) (S := Au) (M := Nu) (I := K) (N := (⊤ : Submodule Au Nu)))
  have hsurjAT : Function.Surjective (algebraMap A T) := by
    -- Proof comment: every quotient class upstairs has a representative from `A`, because both
    -- the `ULift` ring and its quotient are represented by source elements.
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rcases x with ⟨x⟩
    exact ⟨x, rfl⟩
  have eOwnerA :
      (Nu ⧸ (Ku • (⊤ : Submodule Au Nu))) ≃ₗ[A]
        N ⧸ (K • (⊤ : Submodule A N)) := by
    let eRestrict :
        (Nu ⧸ ((Ku • (⊤ : Submodule Au Nu)).restrictScalars A)) ≃ₗ[A]
          Nu ⧸ (Ku • (⊤ : Submodule Au Nu)) :=
      Submodule.Quotient.restrictScalarsEquiv A (Ku • (⊤ : Submodule Au Nu))
    let eDenom :
        (Nu ⧸ ((Ku • (⊤ : Submodule Au Nu)).restrictScalars A)) ≃ₗ[A]
          Nu ⧸ (K • (⊤ : Submodule A Nu)) :=
      Submodule.quotEquivOfEq
        ((Ku • (⊤ : Submodule Au Nu)).restrictScalars A)
        (K • (⊤ : Submodule A Nu))
        hKu_restrict
    let eULift :
        (Nu ⧸ (K • (⊤ : Submodule A Nu))) ≃ₗ[A]
          N ⧸ (K • (⊤ : Submodule A N)) :=
      (ulift_module_quotient_equiv (A := A) (K := K) (N := N)).restrictScalars A
    -- Proof comment: compare the lifted closed fiber to the original one by first restricting
    -- scalars on the quotient, then normalizing the denominator, and finally removing the module
    -- universe lift.
    exact eRestrict.symm.trans (eDenom.trans eULift)
  have eOwner :
      (Nu ⧸ (Ku • (⊤ : Submodule Au Nu))) ≃ₗ[T]
        N ⧸ (K • (⊤ : Submodule A N)) :=
    -- Proof comment: the previous `A`-linear comparison upgrades to the true owner ring `T`
    -- because `A → T` is surjective.
    eOwnerA.extendScalarsOfSurjective hsurjAT
  have hflatTC : Module.Flat T C := by
    let eAlg : C ≃ₐ[T] T :=
      AlgEquiv.ofRingEquiv (R := T) (f := eRing.symm) (by
        intro x
        change eRing.symm (eRing x) = x
        exact eRing.symm_apply_apply x)
    exact Module.Flat.of_linearEquiv eAlg.toLinearEquiv
  have hflatTarget : Module.Flat T (N ⧸ (K • (⊤ : Submodule A N))) := by
    letI : Module.Flat T C := hflatTC
    letI : Module.Flat C (N ⧸ (K • (⊤ : Submodule A N))) := hflat
    exact Module.Flat.trans T C (N ⧸ (K • (⊤ : Submodule A N)))
  have hflat_uquot :
      Module.Flat T (Nu ⧸ (Ku • (⊤ : Submodule Au Nu))) := by
    letI : Module.Flat T (N ⧸ (K • (⊤ : Submodule A N))) := hflatTarget
    exact Module.Flat.of_linearEquiv eOwner
  have hflatAuNu : Module.Flat Au Nu := by
    -- Proof comment: all lifted hypotheses now match the exact common-universe owner expected by
    -- Lemma `10.99.10`.
    exact
      flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal
        (R := Au) (S := Bu) (M := Nu) Ku hKu hTor_u hflat_uquot
  have hflatANu : Module.Flat A Nu := by
    have hflatAAu : Module.Flat A Au := by
      -- Proof comment: `ULift A` is flat over `A` because it is linearly equivalent to `A`.
      exact Module.Flat.of_linearEquiv (ULift.algEquiv (R := A) (A := A)).toLinearEquiv
    letI : Module.Flat A Au := hflatAAu
    letI : Module.Flat Au Nu := hflatAuNu
    exact Module.Flat.trans A Au Nu
  letI : Module.Flat A (ULift.{u} N) := by
    simpa [Nu] using hflatANu
  -- Proof comment: remove the remaining module `ULift` after descending the base ring.
  exact Module.Flat.of_linearEquiv (ULift.moduleEquiv (R := A) (M := N)).symm

end
