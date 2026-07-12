import StacksProject_2024.Chap10.Lemma_10_127_7.TensorDiagram

open CategoryTheory Limits
open Algebra.TensorProduct
open scoped TensorProduct

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A]
variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ CommAlgCat.{u} A) [HasColimit F]

/-- Helper for Lemma 10.127.7: transporting the original colimit cocone across the equivalence
`CommAlgCat A ≃ Under (CommRingCat.of A)` preserves the colimit property. -/
noncomputable abbrev tensor_base_change_equivalence_under_cocone_isColimit :
    IsColimit
      (((commAlgCatEquivUnder (CommRingCat.of A)).functor).mapCocone (colimit.cocone F)) := by
  -- Proof comment: equivalences preserve all colimits, so this first source-faithful transport
  -- is immediate.
  exact
    isColimitOfPreserves
      ((commAlgCatEquivUnder (CommRingCat.of A)).functor)
      (colimit.isColimit F)

/-- Helper for Lemma 10.127.7: tensoring the `Under`-valued diagram with `S` preserves the
filtered colimit because `CommRingCat.tensorProd` is a left adjoint via pushout. -/
noncomputable abbrev tensor_base_change_backend_under_cocone_isColimit
    (S : Type u) [CommRing S] [Algebra A S] :
    IsColimit (tensor_base_change_backend_under_cocone (A := A) (J := J) F S) := by
  -- Route correction: instead of asking instance search to synthesize colimit preservation for
  -- `tensorProd` directly, transport the known left-adjoint structure along
  -- `tensorProdIsoPushout`.
  let _ :
      (CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).IsLeftAdjoint :=
    Functor.isLeftAdjoint_of_iso
      (CommRingCat.tensorProdIsoPushout (CommRingCat.of A) (CommRingCat.of S)).symm
  -- Proof comment: left adjoints preserve all colimits, so the backend tensor cocone stays
  -- colimiting after this second source-faithful transport.
  exact isColimitOfPreserves
    (CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S))
    (tensor_base_change_equivalence_under_cocone_isColimit (A := A) (J := J) F)

/-- Helper for Lemma 10.127.7: the right object of the `Under`-object corresponding to an
`A`-algebra is the original commutative ring. -/
lemma tensor_base_change_backend_under_right_eq
    (T : CommAlgCat.{u} A) :
    (((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T).right = CommRingCat.of ↑T := by
  -- Proof comment: `commAlgCatEquivUnder` sends `T` to the under-object `A → T`, so forgetting
  -- the structure map recovers the original commutative ring.
  simp [commAlgCatEquivUnder, CommRingCat.mkUnder_right]

/-- Helper for Lemma 10.127.7: the right object of the backend `Under`-object is canonically
`A`-algebra equivalent to the original algebra. -/
noncomputable def tensor_base_change_backend_under_right_algEquiv
    (T : CommAlgCat.{u} A) :
    letI : Algebra A (((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T).right :=
      ((((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T).hom).hom.toAlgebra
    ↑(((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T).right ≃ₐ[A] ↑T := by
  letI : Algebra A (((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T).right :=
    ((((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T).hom).hom.toAlgebra
  have hT :
      (((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T).right = CommRingCat.of ↑T :=
    tensor_base_change_backend_under_right_eq (A := A) T
  -- Proof comment: after rewriting the right object back to `T`, the desired algebra equivalence
  -- is just the identity.
  cases hT
  refine
    { toRingEquiv := RingEquiv.refl _
      commutes' := ?_ }
  intro a
  rfl

/-- Helper for Lemma 10.127.7: the canonical algebra equivalence from the backend right object to
the original algebra acts as the identity on elements. -/
@[simp] lemma tensor_base_change_backend_under_right_algEquiv_apply
    (T : CommAlgCat.{u} A)
    (x : (((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T).right) :
    tensor_base_change_backend_under_right_algEquiv (A := A) T x = x := by
  -- Proof comment: after unfolding the backend-right equivalence, the proof reduced it to the
  -- identity algebra equivalence by rewriting the right object back to `T`.
  let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T
  letI : Algebra A U.right := U.hom.hom.toAlgebra
  have hT : U.right = CommRingCat.of ↑T := tensor_base_change_backend_under_right_eq (A := A) T
  cases hT
  rfl

/-- Helper for Lemma 10.127.7: for a fixed backend `Under`-object, forgetting after tensoring with
`S` produces the literal tensor-product stage. -/
lemma tensor_base_change_backend_forget_obj_eq_under
    (S : Type u) [CommRing S] [Algebra A S]
    (U : Under (CommRingCat.of A)) :
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    (Under.forget (CommRingCat.of S)).obj
      ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).obj U) =
      CommRingCat.of (S ⊗[A] U.right) := by
  letI : Algebra A U.right := U.hom.hom.toAlgebra
  -- Proof comment: `tensorProd.obj` is `mkUnder S (S ⊗[A] U.right)`, and forgetting `Under`
  -- drops only the structure map.
  simp [CommRingCat.tensorProd, CommRingCat.mkUnder_right]
  constructor
  · rfl
  · rfl

/-- Helper for Lemma 10.127.7: the backend `Under`-object attached to an `A`-algebra is the
canonical object `A → T`. -/
lemma tensor_base_change_backend_under_obj_eq_mkUnder
    (T : CommAlgCat.{u} A) :
    ((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T =
      CommRingCat.mkUnder (CommRingCat.of A) ↑T := by
  -- Proof comment: this is exactly how `commAlgCatEquivUnder` is defined on objects.
  rfl

/-- Helper for Lemma 10.127.7: the backend map attached to an algebra morphism is literally the
same morphism viewed in the under category. -/
@[simp] lemma tensor_base_change_backend_under_map_eq_toUnder
    {T T' : CommAlgCat.{u} A} (g : T ⟶ T') :
    ((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g = g.hom.toUnder := by
  -- Proof comment: `commAlgCatEquivUnder` is defined on morphisms by applying `AlgHom.toUnder`.
  rfl

/-- Helper for Lemma 10.127.7: specializing the backend-forget object equality to the under-object
coming from an `A`-algebra exposes the intermediate tensor stage `S ⊗[A] U.right`. -/
lemma tensor_base_change_backend_forget_obj_eq_backend_right
    (S : Type u) [CommRing S] [Algebra A S]
    (T : CommAlgCat.{u} A) :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    (Under.forget (CommRingCat.of S)).obj
      ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).obj U) =
      CommRingCat.of (S ⊗[A] U.right) := by
  -- Proof comment: this is the direct specialization of
  -- `tensor_base_change_backend_forget_obj_eq_under` to the backend object attached to `T`; it is
  -- the normalization step needed before simplifying later `eqToHom` transports.
  exact tensor_base_change_backend_forget_obj_eq_under (A := A) (S := S)
    (((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T)

/-- Helper for Lemma 10.127.7: in the pushout model for the backend tensor stage, the left
generator map from `S` is exactly the canonical left tensor inclusion. -/
lemma tensor_base_change_backend_pushout_inv_comp_includeLeft
    (S : Type u) [CommRing S] [Algebra A S]
    (T : CommAlgCat.{u} A) :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    pushout.inr U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right =
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] U.right) := by
  -- Proof comment: this is exactly mathlib's pushout comparison specialized to the backend
  -- `Under`-object attached to the algebra `T`.
  dsimp
  simpa using CommRingCat.pushout_inr_tensorProdObjIsoPushoutObj_inv_right
    (R := CommRingCat.of A) (S := CommRingCat.of S)
    (((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T))

/-- Helper for Lemma 10.127.7: in the pushout model for the backend tensor stage, the right
generator map from the backend algebra is exactly the canonical right tensor inclusion. -/
lemma tensor_base_change_backend_pushout_inv_comp_includeRight
    (S : Type u) [CommRing S] [Algebra A S]
    (T : CommAlgCat.{u} A) :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    pushout.inl U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right =
      CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight : U.right →ₐ[A] S ⊗[A] U.right).toRingHom) := by
  -- Proof comment: this is the companion pushout comparison for the right tensor generator, again
  -- specialized to the backend object attached to `T`.
  dsimp
  simpa using CommRingCat.pushout_inl_tensorProdObjIsoPushoutObj_inv_right
    (R := CommRingCat.of A) (S := CommRingCat.of S)
    (((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T))

/-- Helper for Lemma 10.127.7: the final `eqToHom` transport in the forgotten backend tensor stage
identifies the left tensor generator with the literal pushout-model left generator map. -/
lemma tensor_base_change_backend_eqToHom_comp_includeLeft
    (S : Type u) [CommRing S] [Algebra A S]
    (T : CommAlgCat.{u} A) :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] U.right) ≫
        eqToHom (tensor_base_change_backend_forget_obj_eq_under (A := A) (S := S) U).symm =
      pushout.inr U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right := by
  -- Proof comment: after rewriting the forgotten backend object equality to reflexivity, the
  -- transport disappears and the goal is exactly the pushout comparison for the left generator.
  let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
  letI : Algebra A U.right := U.hom.hom.toAlgebra
  cases tensor_base_change_backend_forget_obj_eq_under (A := A) (S := S) U
  simpa only [eqToHom_refl, Category.comp_id] using
    (tensor_base_change_backend_pushout_inv_comp_includeLeft (A := A) (S := S) T).symm

/-- Helper for Lemma 10.127.7: the final `eqToHom` transport in the forgotten backend tensor stage
identifies the right tensor generator with the literal pushout-model right generator map. -/
lemma tensor_base_change_backend_eqToHom_comp_includeRight
    (S : Type u) [CommRing S] [Algebra A S]
    (T : CommAlgCat.{u} A) :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight : U.right →ₐ[A] S ⊗[A] U.right).toRingHom) ≫
        eqToHom (tensor_base_change_backend_forget_obj_eq_under (A := A) (S := S) U).symm =
      pushout.inl U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right := by
  -- Proof comment: the same transport simplification reduces the right-generator statement to the
  -- existing pushout comparison formula.
  let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
  letI : Algebra A U.right := U.hom.hom.toAlgebra
  cases tensor_base_change_backend_forget_obj_eq_under (A := A) (S := S) U
  simpa only [eqToHom_refl, Category.comp_id] using
    (tensor_base_change_backend_pushout_inv_comp_includeRight (A := A) (S := S) T).symm

/-- Helper for Lemma 10.127.7: the forgotten backend tensor stage is canonically isomorphic to the
literal tensor stage used in the source proof. -/
noncomputable def tensor_base_change_backend_forget_obj_iso
    (S : Type u) [CommRing S] [Algebra A S]
    (T : CommAlgCat.{u} A) :
    (Under.forget (CommRingCat.of S)).obj
      ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).obj
        (((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T)) ≅
      CommRingCat.of (S ⊗[A] ↑T) := by
  let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T
  letI : Algebra A U.right := U.hom.hom.toAlgebra
  let e : CommRingCat.of (S ⊗[A] U.right) ≅ CommRingCat.of (S ⊗[A] ↑T) :=
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : S ≃ₐ[A] S)
      (tensor_base_change_backend_under_right_algEquiv (A := A) T)).toRingEquiv.toCommRingCatIso
  -- Proof comment: first identify the forgotten backend stage with `S ⊗[A] U.right`, then use
  -- the canonical `A`-algebra equivalence `U.right ≃ₐ[A] T` on the right tensor factor.
  exact eqToIso (tensor_base_change_backend_forget_obj_eq_under (A := A) (S := S) U) ≪≫ e

/-- Helper for Lemma 10.127.7: before the final object-transport, the right-factor comparison
isomorphism fixes the left tensor generator. -/
lemma tensor_base_change_backend_congr_symm_comp_includeLeft
    (S : Type u) [CommRing S] [Algebra A S]
    (T : CommAlgCat.{u} A) :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] ↑T) ≫
        CommRingCat.ofHom
          ((Algebra.TensorProduct.congr
            (AlgEquiv.refl : S ≃ₐ[A] S)
            (tensor_base_change_backend_under_right_algEquiv (A := A) T)).symm.toRingHom) =
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] U.right) := by
  -- Proof comment: the comparison changes only the right tensor factor, so the left generator is
  -- untouched before the remaining `eqToHom` transport is applied.
  let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
  letI : Algebra A U.right := U.hom.hom.toAlgebra
  ext x
  change
    (Algebra.TensorProduct.congr
        (AlgEquiv.refl : S ≃ₐ[A] S)
        (tensor_base_change_backend_under_right_algEquiv (A := A) T)).symm
      (x ⊗ₜ[A] (1 : ↑T)) =
    x ⊗ₜ[A] (1 : (((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T).right))
  simpa using
    (Algebra.TensorProduct.congr_symm_apply
      (AlgEquiv.refl : S ≃ₐ[A] S)
      (tensor_base_change_backend_under_right_algEquiv (A := A) T)
      (x ⊗ₜ[A] (1 : ↑T)))

/-- Helper for Lemma 10.127.7: before the final object-transport, the right tensor generator is
carried along the inverse of the backend-right algebra equivalence. -/
lemma tensor_base_change_backend_congr_symm_comp_includeRight
    (S : Type u) [CommRing S] [Algebra A S]
    (T : CommAlgCat.{u} A) :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight : ↑T →ₐ[A] S ⊗[A] ↑T).toRingHom) ≫
        CommRingCat.ofHom
          ((Algebra.TensorProduct.congr
            (AlgEquiv.refl : S ≃ₐ[A] S)
            (tensor_base_change_backend_under_right_algEquiv (A := A) T)).symm.toRingHom) =
      CommRingCat.ofHom
        ((((Algebra.TensorProduct.includeRight : U.right →ₐ[A] S ⊗[A] U.right).comp
            (tensor_base_change_backend_under_right_algEquiv (A := A) T).symm)).toRingHom) := by
  -- Proof comment: on the right tensor generator, the same comparison simply rewrites the backend
  -- right object back along its canonical algebra equivalence to `T`.
  let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
  letI : Algebra A U.right := U.hom.hom.toAlgebra
  ext x
  change
    (Algebra.TensorProduct.congr
        (AlgEquiv.refl : S ≃ₐ[A] S)
        (tensor_base_change_backend_under_right_algEquiv (A := A) T)).symm
      ((1 : S) ⊗ₜ[A] x) =
    (1 : S) ⊗ₜ[A] (tensor_base_change_backend_under_right_algEquiv (A := A) T).symm x
  simpa using
    (Algebra.TensorProduct.congr_symm_apply
      (AlgEquiv.refl : S ≃ₐ[A] S)
      (tensor_base_change_backend_under_right_algEquiv (A := A) T)
      ((1 : S) ⊗ₜ[A] x))

/-- Helper for Lemma 10.127.7: the inverse of the stage comparison isomorphism carries the left
tensor generator to the pushout-model left generator map. -/
lemma tensor_base_change_backend_forget_obj_iso_inv_comp_includeLeft
    (S : Type u) [CommRing S] [Algebra A S]
    (T : CommAlgCat.{u} A) :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] ↑T) ≫
        (tensor_base_change_backend_forget_obj_iso (A := A) (S := S) T).inv =
      pushout.inr U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right := by
  -- Proof comment: unfold the stage comparison isomorphism, separate the congr-side normalization
  -- from the final object transport, and then apply the dedicated left-generator adapter.
  let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
  letI : Algebra A U.right := U.hom.hom.toAlgebra
  calc
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] ↑T) ≫
        (tensor_base_change_backend_forget_obj_iso (A := A) (S := S) T).inv =
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] ↑T) ≫
          CommRingCat.ofHom
            ((Algebra.TensorProduct.congr
              (AlgEquiv.refl : S ≃ₐ[A] S)
              (tensor_base_change_backend_under_right_algEquiv (A := A) T)).symm.toRingHom) ≫
            eqToHom (tensor_base_change_backend_forget_obj_eq_under (A := A) (S := S) U).symm := by
        simp [tensor_base_change_backend_forget_obj_iso, U]
        rfl
    _ =
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] U.right) ≫
        eqToHom (tensor_base_change_backend_forget_obj_eq_under (A := A) (S := S) U).symm := by
        simpa [Category.assoc] using congrArg
          (fun f ↦ f ≫ eqToHom (tensor_base_change_backend_forget_obj_eq_under
            (A := A) (S := S) U).symm)
          (tensor_base_change_backend_congr_symm_comp_includeLeft (A := A) (S := S) T)
    _ =
      pushout.inr U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right := by
        simpa [U] using
          tensor_base_change_backend_eqToHom_comp_includeLeft (A := A) (S := S) T

/-- Helper for Lemma 10.127.7: the inverse of the stage comparison isomorphism carries the right
tensor generator to the pushout-model right generator map. -/
lemma tensor_base_change_backend_congr_symm_comp_includeRight_transport
    (S : Type u) [CommRing S] [Algebra A S]
    (T : CommAlgCat.{u} A) :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    CommRingCat.ofHom
        ((((Algebra.TensorProduct.includeRight : U.right →ₐ[A] S ⊗[A] U.right).comp
            (tensor_base_change_backend_under_right_algEquiv (A := A) T).symm)).toRingHom) ≫
        eqToHom (tensor_base_change_backend_forget_obj_eq_under (A := A) (S := S) U).symm =
      pushout.inl U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right := by
  let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
  letI : Algebra A U.right := U.hom.hom.toAlgebra
  -- Proof comment: after rewriting the backend right object back to `T`, the source-side algebra
  -- equivalence is the identity and the statement reduces to the existing `eqToHom` adapter.
  have hU : U.right = CommRingCat.of ↑T := tensor_base_change_backend_under_right_eq (A := A) T
  cases hU
  simpa only [Category.comp_id] using
    (tensor_base_change_backend_eqToHom_comp_includeRight (A := A) (S := S) T)

/-- Helper for Lemma 10.127.7: the inverse of the stage comparison isomorphism carries the right
tensor generator to the pushout-model right generator map. -/
lemma tensor_base_change_backend_forget_obj_iso_inv_comp_includeRight
    (S : Type u) [CommRing S] [Algebra A S]
    (T : CommAlgCat.{u} A) :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight : ↑T →ₐ[A] S ⊗[A] ↑T).toRingHom) ≫
        (tensor_base_change_backend_forget_obj_iso (A := A) (S := S) T).inv =
      pushout.inl U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right := by
  -- Proof comment: unfold the stage comparison isomorphism, isolate the congr-side right
  -- generator formula, and then close with the dedicated transport-stable adapter.
  let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
  letI : Algebra A U.right := U.hom.hom.toAlgebra
  calc
    CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight : ↑T →ₐ[A] S ⊗[A] ↑T).toRingHom) ≫
        (tensor_base_change_backend_forget_obj_iso (A := A) (S := S) T).inv =
      CommRingCat.ofHom
          ((Algebra.TensorProduct.includeRight : ↑T →ₐ[A] S ⊗[A] ↑T).toRingHom) ≫
          CommRingCat.ofHom
            ((Algebra.TensorProduct.congr
              (AlgEquiv.refl : S ≃ₐ[A] S)
              (tensor_base_change_backend_under_right_algEquiv (A := A) T)).symm.toRingHom) ≫
            eqToHom (tensor_base_change_backend_forget_obj_eq_under (A := A) (S := S) U).symm := by
        simp [tensor_base_change_backend_forget_obj_iso, U]
        rfl
    _ =
      CommRingCat.ofHom
          ((((Algebra.TensorProduct.includeRight : U.right →ₐ[A] S ⊗[A] U.right).comp
              (tensor_base_change_backend_under_right_algEquiv (A := A) T).symm)).toRingHom) ≫
          eqToHom (tensor_base_change_backend_forget_obj_eq_under (A := A) (S := S) U).symm := by
        simpa [Category.assoc] using congrArg
          (fun f ↦ f ≫ eqToHom (tensor_base_change_backend_forget_obj_eq_under
            (A := A) (S := S) U).symm)
          (tensor_base_change_backend_congr_symm_comp_includeRight (A := A) (S := S) T)
    _ =
      pushout.inl U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right := by
        simpa [U] using
          tensor_base_change_backend_congr_symm_comp_includeRight_transport
            (A := A) (S := S) T

/-- Helper for Lemma 10.127.7: conjugating the backend tensor-transition map by the pushout-model
comparison isomorphisms identifies it with the literal pushout transition map. -/
lemma tensor_base_change_pushout_map_conj
    (S : Type u) [CommRing S] [Algebra A S]
    {T T' : CommAlgCat.{u} A} (g : T ⟶ T') :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    let U' := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T')
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    letI : Algebra A U'.right := U'.hom.hom.toAlgebra
    (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right ≫
        ((Under.forget (CommRingCat.of S)).map
          ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).map
            (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g))) =
      ((Under.pushout (CommRingCat.ofHom (algebraMap A S))).map
          (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g)).right ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U').inv.right := by
  -- Proof comment: this is exactly the right component of the inverse naturality square for
  -- `tensorProdIsoPushout`.
  simpa [CommRingCat.tensorProdIsoPushout_app] using
    (congrArg (fun f ↦ f.right)
      ((CommRingCat.tensorProdIsoPushout (CommRingCat.of A) (CommRingCat.of S)).inv.naturality
        (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g))).symm

/-- Helper for Lemma 10.127.7: the commutativity witness defining the pushout transition map
attached to an `A`-algebra morphism `g`. -/
lemma tensor_base_change_pushout_map_desc_comm
    (S : Type u) [CommRing S] [Algebra A S]
    {T T' : CommAlgCat.{u} A} (g : T ⟶ T') :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    let U' := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T')
    U.hom ≫
        (CommRingCat.ofHom g.hom.toRingHom ≫
          pushout.inl U'.hom (CommRingCat.ofHom (algebraMap A S))) =
      CommRingCat.ofHom (algebraMap A S) ≫
        pushout.inr U'.hom (CommRingCat.ofHom (algebraMap A S)) := by
  let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
  let U' := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T')
  -- Proof comment: after identifying the backend map with `g.toUnder`, the defining relation is
  -- exactly the pushout square condition for `U'`.
  have hg :
      CommRingCat.ofHom (algebraMap A ↑T) ≫ CommRingCat.ofHom g.hom.toRingHom =
        CommRingCat.ofHom (algebraMap A ↑T') := by
    ext a
    exact g.hom.commutes a
  calc
    U.hom ≫
        (CommRingCat.ofHom g.hom.toRingHom ≫
          pushout.inl U'.hom (CommRingCat.ofHom (algebraMap A S))) =
      (CommRingCat.ofHom (algebraMap A ↑T) ≫ CommRingCat.ofHom g.hom.toRingHom) ≫
        pushout.inl U'.hom (CommRingCat.ofHom (algebraMap A S)) := by
          rfl
    _ =
      CommRingCat.ofHom (algebraMap A ↑T') ≫
        pushout.inl U'.hom (CommRingCat.ofHom (algebraMap A S)) := by
          simpa [Category.assoc] using congrArg
            (fun f ↦ f ≫ pushout.inl U'.hom (CommRingCat.ofHom (algebraMap A S))) hg
    _ =
      CommRingCat.ofHom (algebraMap A S) ≫
        pushout.inr U'.hom (CommRingCat.ofHom (algebraMap A S)) := by
          simpa [U', Category.assoc] using
            (show U'.hom ≫ pushout.inl U'.hom (CommRingCat.ofHom (algebraMap A S)) =
                CommRingCat.ofHom (algebraMap A S) ≫
                  pushout.inr U'.hom (CommRingCat.ofHom (algebraMap A S)) from
              pushout.condition)

/-- Helper for Lemma 10.127.7: the right component of `Under.pushout.map` is the literal
`pushout.desc` on the pushout model. -/
lemma tensor_base_change_pushout_map_right_eq_desc
    (S : Type u) [CommRing S] [Algebra A S]
    {T T' : CommAlgCat.{u} A} (g : T ⟶ T') :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    let U' := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T')
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    letI : Algebra A U'.right := U'.hom.hom.toAlgebra
    ((Under.pushout (CommRingCat.ofHom (algebraMap A S))).map
      (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g)).right =
      pushout.desc
        (CommRingCat.ofHom g.hom.toRingHom ≫
          pushout.inl U'.hom (CommRingCat.ofHom (algebraMap A S)))
        (pushout.inr U'.hom (CommRingCat.ofHom (algebraMap A S)))
        (tensor_base_change_pushout_map_desc_comm (A := A) (S := S) g) := by
  let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
  let U' := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T')
  letI : Algebra A U.right := U.hom.hom.toAlgebra
  letI : Algebra A U'.right := U'.hom.hom.toAlgebra
  -- Proof comment: unfold only the right component of `Under.pushout.map`; after rewriting the
  -- backend morphism to `g.toUnder`, both sides are the same pushout-desc map.
  apply pushout.hom_ext
  · simp only [Under.pushout_map, Under.homMk_right, pushout.inl_desc]
    rfl
  · simp only [Under.pushout_map, Under.homMk_right, pushout.inr_desc]
    rfl

/-- Helper for Lemma 10.127.7: the pushout-model transition map fixes the left tensor generator. -/
lemma tensor_base_change_pushout_map_comp_includeLeft
    (S : Type u) [CommRing S] [Algebra A S]
    {T T' : CommAlgCat.{u} A} (g : T ⟶ T') :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    let U' := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T')
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    letI : Algebra A U'.right := U'.hom.hom.toAlgebra
    pushout.inr U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right ≫
        ((Under.forget (CommRingCat.of S)).map
          ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).map
            (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g))) =
      pushout.inr U'.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U').inv.right := by
  -- Proof comment: compose `tensor_base_change_pushout_map_conj` on the left with `pushout.inr`
  -- and then simplify the pushout transition map by `pushout.inr_desc`.
  let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
  let U' := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T')
  letI : Algebra A U.right := U.hom.hom.toAlgebra
  letI : Algebra A U'.right := U'.hom.hom.toAlgebra
  calc
    pushout.inr U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right ≫
        ((Under.forget (CommRingCat.of S)).map
          ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).map
            (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g))) =
      pushout.inr U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (((Under.pushout (CommRingCat.ofHom (algebraMap A S))).map
          (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g)).right ≫
            (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U').inv.right) := by
          simpa [Category.assoc] using congrArg
            (fun k ↦ pushout.inr U.hom (CommRingCat.ofHom (algebraMap A S)) ≫ k)
            (tensor_base_change_pushout_map_conj (A := A) (S := S) g)
    _ =
      (pushout.inr U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        ((Under.pushout (CommRingCat.ofHom (algebraMap A S))).map
          (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g)).right) ≫
            (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U').inv.right := by
          simp [Category.assoc]
    _ =
      pushout.inr U'.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U').inv.right := by
          rw [tensor_base_change_pushout_map_right_eq_desc (A := A) (S := S) g]
          simpa [Category.assoc] using congrArg
            (fun k ↦ k ≫ (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U').inv.right)
            (pushout.inr_desc
              (CommRingCat.ofHom g.hom.toRingHom ≫
                pushout.inl U'.hom (CommRingCat.ofHom (algebraMap A S)))
              (pushout.inr U'.hom (CommRingCat.ofHom (algebraMap A S)))
              (tensor_base_change_pushout_map_desc_comm (A := A) (S := S) g))

/-- Helper for Lemma 10.127.7: the pushout-model transition map sends the right tensor generator
through the algebra map `g`. -/
lemma tensor_base_change_pushout_map_comp_includeRight
    (S : Type u) [CommRing S] [Algebra A S]
    {T T' : CommAlgCat.{u} A} (g : T ⟶ T') :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    let U' := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T')
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    letI : Algebra A U'.right := U'.hom.hom.toAlgebra
    pushout.inl U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right ≫
        ((Under.forget (CommRingCat.of S)).map
          ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).map
            (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g))) =
      CommRingCat.ofHom g.hom.toRingHom ≫
        pushout.inl U'.hom (CommRingCat.ofHom (algebraMap A S)) ≫
          (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U').inv.right := by
  -- Proof comment: compose `tensor_base_change_pushout_map_conj` on the left with `pushout.inl`
  -- and then simplify the pushout transition map by `pushout.inl_desc`.
  let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
  let U' := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T')
  letI : Algebra A U.right := U.hom.hom.toAlgebra
  letI : Algebra A U'.right := U'.hom.hom.toAlgebra
  have h_conj :
      pushout.inl U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
          (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right ≫
          ((Under.forget (CommRingCat.of S)).map
            ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).map
              (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g))) =
        pushout.inl U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
          (((Under.pushout (CommRingCat.ofHom (algebraMap A S))).map
            (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g)).right ≫
              (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U').inv.right) := by
    simpa [Category.assoc] using congrArg
      (fun k ↦ pushout.inl U.hom (CommRingCat.ofHom (algebraMap A S)) ≫ k)
      (tensor_base_change_pushout_map_conj (A := A) (S := S) g)
  have h_assoc :
      pushout.inl U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
          (((Under.pushout (CommRingCat.ofHom (algebraMap A S))).map
            (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g)).right ≫
              (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U').inv.right) =
        (pushout.inl U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
          ((Under.pushout (CommRingCat.ofHom (algebraMap A S))).map
            (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g)).right) ≫
              (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U').inv.right := by
    simp [Category.assoc]
  have h_desc :
      (pushout.inl U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        ((Under.pushout (CommRingCat.ofHom (algebraMap A S))).map
          (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g)).right) ≫
            (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U').inv.right =
        CommRingCat.ofHom g.hom.toRingHom ≫
          pushout.inl U'.hom (CommRingCat.ofHom (algebraMap A S)) ≫
            (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U').inv.right := by
    rw [tensor_base_change_pushout_map_right_eq_desc (A := A) (S := S) g]
    simpa [Category.assoc] using congrArg
      (fun k ↦ k ≫ (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U').inv.right)
      (pushout.inl_desc
        (CommRingCat.ofHom g.hom.toRingHom ≫
          pushout.inl U'.hom (CommRingCat.ofHom (algebraMap A S)))
        (pushout.inr U'.hom (CommRingCat.ofHom (algebraMap A S)))
        (tensor_base_change_pushout_map_desc_comm (A := A) (S := S) g))
  exact h_conj.trans (h_assoc.trans h_desc)

/-- Helper for Lemma 10.127.7: after identifying the backend tensor stages with the literal tensor
products by the canonical stage isomorphisms, the forgotten backend tensor map is exactly the
literal tensor map on the right factor. -/
lemma tensor_base_change_backend_forget_hom_conj_eq_literal
    (S : Type u) [CommRing S] [Algebra A S]
    {T T' : CommAlgCat.{u} A} (g : T ⟶ T') :
    (tensor_base_change_backend_forget_obj_iso (A := A) (S := S) T).inv ≫
        ((Under.forget (CommRingCat.of S)).map
        ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).map
            (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g))) ≫
        (tensor_base_change_backend_forget_obj_iso (A := A) (S := S) T').hom =
      CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A S) g.hom).toRingHom := by
  -- Route correction: compare backend and literal tensor maps through the canonical stage
  -- isomorphisms, rather than trying to force definitional equalities between bundled objects.
  -- Proof comment: both sides are maps out of a tensor product, so it suffices to compare them on
  -- the left and right tensor generators and then apply tensor-product extensionality.
  let f :
      CommRingCat.of (S ⊗[A] ↑T) ⟶ CommRingCat.of (S ⊗[A] ↑T') :=
    (tensor_base_change_backend_forget_obj_iso (A := A) (S := S) T).inv ≫
      ((Under.forget (CommRingCat.of S)).map
        ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).map
          (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g))) ≫
      (tensor_base_change_backend_forget_obj_iso (A := A) (S := S) T').hom
  have h_left :
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] ↑T) ≫ f =
        CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] ↑T') := by
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    let U' := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T')
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    letI : Algebra A U'.right := U'.hom.hom.toAlgebra
    -- Proof comment: the left tensor generator is unchanged by base change on the right factor.
    calc
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] ↑T) ≫ f =
        pushout.inr U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
          (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right ≫
          ((Under.forget (CommRingCat.of S)).map
            ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).map
              (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g))) ≫
          (tensor_base_change_backend_forget_obj_iso (A := A) (S := S) T').hom := by
            simpa [f, U, Category.assoc] using congrArg
              (fun k ↦ k ≫
                ((Under.forget (CommRingCat.of S)).map
                  ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).map
                    (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g))) ≫
                (tensor_base_change_backend_forget_obj_iso (A := A) (S := S) T').hom)
              (tensor_base_change_backend_forget_obj_iso_inv_comp_includeLeft
                (A := A) (S := S) T)
      _ =
        pushout.inr U'.hom (CommRingCat.ofHom (algebraMap A S)) ≫
          (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U').inv.right ≫
          (tensor_base_change_backend_forget_obj_iso (A := A) (S := S) T').hom := by
            simpa [Category.assoc] using congrArg
              (fun k ↦ k ≫ (tensor_base_change_backend_forget_obj_iso
                (A := A) (S := S) T').hom)
              (tensor_base_change_pushout_map_comp_includeLeft (A := A) (S := S) g)
      _ =
        CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] ↑T') := by
          simpa [Category.assoc, U'] using (congrArg
            (fun k ↦ k ≫ (tensor_base_change_backend_forget_obj_iso
              (A := A) (S := S) T').hom)
            (tensor_base_change_backend_forget_obj_iso_inv_comp_includeLeft
              (A := A) (S := S) T')).symm
  have h_right :
      CommRingCat.ofHom
          ((Algebra.TensorProduct.includeRight : ↑T →ₐ[A] S ⊗[A] ↑T).toRingHom) ≫ f =
        CommRingCat.ofHom g.hom.toRingHom ≫
          CommRingCat.ofHom
            ((Algebra.TensorProduct.includeRight : ↑T' →ₐ[A] S ⊗[A] ↑T').toRingHom) := by
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    let U' := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T')
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    letI : Algebra A U'.right := U'.hom.hom.toAlgebra
    -- Proof comment: the right tensor generator is transported exactly by `g`.
    have h_start :
        CommRingCat.ofHom
            ((Algebra.TensorProduct.includeRight : ↑T →ₐ[A] S ⊗[A] ↑T).toRingHom) ≫ f =
          pushout.inl U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
            (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right ≫
            ((Under.forget (CommRingCat.of S)).map
              ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).map
                (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g))) ≫
            (tensor_base_change_backend_forget_obj_iso (A := A) (S := S) T').hom := by
      simpa [f, U, Category.assoc] using congrArg
        (fun k ↦ k ≫
          ((Under.forget (CommRingCat.of S)).map
            ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).map
              (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g))) ≫
          (tensor_base_change_backend_forget_obj_iso (A := A) (S := S) T').hom)
        (tensor_base_change_backend_forget_obj_iso_inv_comp_includeRight
          (A := A) (S := S) T)
    have h_mid :
        pushout.inl U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
            (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right ≫
            ((Under.forget (CommRingCat.of S)).map
              ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).map
                (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g))) ≫
            (tensor_base_change_backend_forget_obj_iso (A := A) (S := S) T').hom =
          CommRingCat.ofHom g.hom.toRingHom ≫
            pushout.inl U'.hom (CommRingCat.ofHom (algebraMap A S)) ≫
            (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U').inv.right ≫
            (tensor_base_change_backend_forget_obj_iso (A := A) (S := S) T').hom := by
      simpa [Category.assoc] using congrArg
        (fun k ↦ k ≫ (tensor_base_change_backend_forget_obj_iso
          (A := A) (S := S) T').hom)
        (tensor_base_change_pushout_map_comp_includeRight (A := A) (S := S) g)
    have h_end :
        CommRingCat.ofHom g.hom.toRingHom ≫
            pushout.inl U'.hom (CommRingCat.ofHom (algebraMap A S)) ≫
            (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U').inv.right ≫
            (tensor_base_change_backend_forget_obj_iso (A := A) (S := S) T').hom =
          CommRingCat.ofHom g.hom.toRingHom ≫
            CommRingCat.ofHom
              ((Algebra.TensorProduct.includeRight : ↑T' →ₐ[A] S ⊗[A] ↑T').toRingHom) := by
      simpa [Category.assoc, U'] using (congrArg
        (fun k ↦ CommRingCat.ofHom g.hom.toRingHom ≫ k ≫
          (tensor_base_change_backend_forget_obj_iso
            (A := A) (S := S) T').hom)
        (tensor_base_change_backend_forget_obj_iso_inv_comp_includeRight
          (A := A) (S := S) T')).symm
    exact h_start.trans (h_mid.trans h_end)
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · -- Proof comment: both ring maps preserve zero.
    simp [f]
  · intro s t
    -- Proof comment: a pure tensor factors as a product of its left and right generators.
    have hs :
        f.hom (s ⊗ₜ[A] (1 : ↑T)) = s ⊗ₜ[A] (1 : ↑T') := by
      simpa [f] using congrArg
        (fun k : CommRingCat.of S ⟶ CommRingCat.of (S ⊗[A] ↑T') ↦ k.hom s)
        h_left
    have ht :
        f.hom ((1 : S) ⊗ₜ[A] t) = (1 : S) ⊗ₜ[A] g.hom t := by
      simpa [f] using congrArg
        (fun k : CommRingCat.of ↑T ⟶ CommRingCat.of (S ⊗[A] ↑T') ↦ k.hom t)
        h_right
    calc
      f.hom (s ⊗ₜ[A] t) = f.hom ((s ⊗ₜ[A] (1 : ↑T)) * ((1 : S) ⊗ₜ[A] t)) := by
        simp [tmul_mul_tmul]
      _ = f.hom (s ⊗ₜ[A] (1 : ↑T)) * f.hom ((1 : S) ⊗ₜ[A] t) := by
        rw [map_mul]
      _ = (s ⊗ₜ[A] (1 : ↑T')) * ((1 : S) ⊗ₜ[A] g.hom t) := by
        rw [hs, ht]
      _ = (Algebra.TensorProduct.map (AlgHom.id A S) g.hom) (s ⊗ₜ[A] t) := by
        simp [tmul_mul_tmul]
  · intro z₁ z₂ hz₁ hz₂
    rw [RingHom.map_add, RingHom.map_add, hz₁, hz₂]

/-- Helper for Lemma 10.127.7: after forgetting the backend `Under` proof data, the transported
tensor diagram is canonically isomorphic to the literal tensor-stage diagram used in the source
proof. -/
abbrev tensor_base_change_backend_forget_diagram_iso
    (S : Type u) [CommRing S] [Algebra A S] :
    (tensor_base_change_backend_under_diagram (A := A) (J := J) F S) ⋙
        Under.forget (CommRingCat.of S) ≅
      tensor_base_change_diagram (A := A) (J := J) F S :=
  by
    -- Proof comment: the components are the canonical stage comparison isomorphisms.
    refine NatIso.ofComponents
      (fun j ↦ tensor_base_change_backend_forget_obj_iso (A := A) (S := S) (F.obj j))
      (fun {_ _} f ↦ ?_)
    -- Proof comment: naturality is exactly the conjugation identity for the stage map `F.map f`.
    simpa [tensor_base_change_backend_under_diagram, tensor_base_change_diagram, Category.assoc] using
      congrArg
        (fun k ↦
          (tensor_base_change_backend_forget_obj_iso (A := A) (S := S) (F.obj _)).hom ≫ k)
        (tensor_base_change_backend_forget_hom_conj_eq_literal
          (A := A) (S := S) (T := F.obj _) (T' := F.obj _) (g := F.map f))

/-- Helper for Lemma 10.127.7: forgetting the backend tensor cocone matches the literal tensor
cocone after precomposing along the backend-forget diagram isomorphism. -/
noncomputable abbrev tensor_base_change_backend_forget_cocone_iso_ext
    (S : Type u) [CommRing S] [Algebra A S] :
    (Under.forget (CommRingCat.of S)).mapCocone
        (tensor_base_change_backend_under_cocone (A := A) (J := J) F S) ≅
      (Cocone.precompose
        (tensor_base_change_backend_forget_diagram_iso
          (A := A) (J := J) (F := F) S).hom).obj
        (tensor_base_change_cocone (A := A) (J := J) F S) := by
  -- Proof comment: once the backend/literal conjugation is available for every structure map
  -- `colimit.ι F j`, the cocone comparison is a direct `Cocone.ext`.
  refine Cocone.ext
    (tensor_base_change_backend_forget_obj_iso (A := A) (S := S) (colimit F))
    (fun j ↦ ?_)
  -- Proof comment: each cocone leg is the special case of the already-proved conjugation formula
  -- for the structure map `colimit.ι F j`.
  simpa [tensor_base_change_backend_under_cocone, tensor_base_change_cocone,
    tensor_base_change_backend_forget_diagram_iso, tensor_base_change_backend_under_diagram,
    tensor_base_change_diagram, Category.assoc] using
    congrArg
      (fun k ↦
        (tensor_base_change_backend_forget_obj_iso (A := A) (S := S) (F.obj j)).hom ≫ k)
      (tensor_base_change_backend_forget_hom_conj_eq_literal
        (A := A) (S := S) (T := F.obj j) (T' := colimit F) (g := colimit.ι F j))

/-- Helper for Lemma 10.127.7: the tensor-base-change cocone is colimiting. -/
noncomputable abbrev tensor_base_change_cocone_isColimit
    (S : Type u) [CommRing S] [Algebra A S] :
    IsColimit (tensor_base_change_cocone (A := A) (J := J) F S) :=
  by
    -- Route correction: instead of transporting inside `Under`, first forget the backend cocone
    -- to plain commutative rings, where the comparison to the literal tensor cocone is stable.
    -- Proof comment: first forget the proven backend colimit cocone, then transport that
    -- colimit witness across the explicit cocone isomorphism to the precomposed literal cocone,
    -- and finally remove the precomposition via the diagram isomorphism.
    let hc_under := tensor_base_change_backend_under_cocone_isColimit
      (A := A) (J := J) F S
    let hc_forget := isColimitOfPreserves (Under.forget (CommRingCat.of S)) hc_under
    let hc_pre :
        IsColimit
          ((Cocone.precompose
            (tensor_base_change_backend_forget_diagram_iso
              (A := A) (J := J) (F := F) S).hom).obj
            (tensor_base_change_cocone (A := A) (J := J) F S)) :=
      IsColimit.ofIsoColimit hc_forget
        (tensor_base_change_backend_forget_cocone_iso_ext
          (A := A) (J := J) (F := F) S)
    exact
      (IsColimit.precomposeHomEquiv
        (tensor_base_change_backend_forget_diagram_iso
          (A := A) (J := J) (F := F) S)
        (tensor_base_change_cocone (A := A) (J := J) F S)).1 hc_pre

/-- Helper for Lemma 10.127.7: a filtered index category has an object, which is the only extra
input needed by `Under.isColimitLiftCocone`. -/
lemma tensor_base_change_index_nonempty : Nonempty J := by
  -- Proof comment: a cocone over the empty diagram picks out an object of the filtered category.
  let c : Cocone ((Functor.empty (C := J)) : Discrete.{v} PEmpty ⥤ J) :=
    (IsFiltered.cocone_nonempty ((Functor.empty (C := J)) : Discrete.{v} PEmpty ⥤ J)).some
  exact ⟨c.pt⟩

end
