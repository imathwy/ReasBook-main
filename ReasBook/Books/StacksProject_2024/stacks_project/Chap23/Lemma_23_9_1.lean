import StacksProject_2024.Chap10.Lemma_10_112_8
import StacksProject_2024.Chap23.Lemma_23_9_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing

namespace RingHom

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B]

/-
Owner/API note:
* the semantic `lean_leansearch` tool was not exposed in this run, so the owner choice was checked
  directly against local project precedents for `RingHom.KernelIsGeneratedByRegularSequence`,
  complete local rings, and regular local quotients;
* no existing repository owner for a "good factorization" of a local map was present, so the
  source-faithful intermediate-ring structure is introduced here.
-/

/-- A good factorization of a local homomorphism `f : A →+* B` consists of a Noetherian local ring
`S`, a flat local map `A → S` with regular closed fiber, and a surjective local map `S → B`
whose composite is `f`. -/
structure GoodFactorization (f : A →+* B) where
  middle : Type (max u v)
  instCommRing : CommRing middle
  instIsLocalRing : IsLocalRing middle
  instIsNoetherianRing : IsNoetherianRing middle
  left : A →+* middle
  right : middle →+* B
  left_isLocalHom : IsLocalHom left
  right_isLocalHom : IsLocalHom right
  right_surjective : Function.Surjective right
  left_flat : left.Flat
  closedFiber_regular :
    let _ : Algebra A middle := left.toAlgebra
    IsRegularLocalRing (Ideal.Fiber (maximalIdeal A) middle)
  comp_eq : right.comp left = f

attribute [instance] GoodFactorization.instCommRing GoodFactorization.instIsLocalRing
attribute [instance] GoodFactorization.instIsNoetherianRing

variable {f : A →+* B}

/-- The closed fiber of a good factorization is the canonical fiber ring over the maximal ideal of
the source local ring. -/
abbrev GoodFactorization.ClosedFiber (P : GoodFactorization f) :=
  let _ : Algebra A P.middle := P.left.toAlgebra
  Ideal.Fiber (maximalIdeal A) P.middle

/-- The kernel condition of Lemma 23.9.1, viewed as a property of the good factorization itself. -/
abbrev GoodFactorization.KernelIsGeneratedByRegularSequence (P : GoodFactorization f) : Prop :=
  P.right.KernelIsGeneratedByRegularSequence

omit [IsLocalRing B] in
/-- A good factorization exhibits `f` as a local homomorphism. -/
theorem GoodFactorization.isLocalHom (P : GoodFactorization f) : IsLocalHom f := by
  let _ : IsLocalHom P.left := P.left_isLocalHom
  let _ : IsLocalHom P.right := P.right_isLocalHom
  simpa [P.comp_eq] using (RingHom.isLocalHom_comp P.right P.left : IsLocalHom (P.right.comp P.left))

omit [IsLocalRing B] in
/-- A good factorization supplies the canonical local-hom structure on its composite map. -/
instance GoodFactorization.instIsLocalHom (P : GoodFactorization f) : IsLocalHom f :=
  P.isLocalHom

/-- The maximal-ideal completion map attached to a good factorization. This packages the local-hom
structure supplied by the factorization so downstream completion-map statements do not need an
extra ambient `IsLocalHom f` binder. -/
noncomputable abbrev GoodFactorization.completionMap (P : GoodFactorization f) :=
  let _ : IsLocalHom f := P.isLocalHom
  maximalIdealCompletionMap f

/-- The completion-map local-complete-intersection condition attached to a good factorization. -/
abbrev GoodFactorization.CompletionMapIsLocalCompleteIntersection
    (P : GoodFactorization f) : Prop :=
  RingHom.IsLocalCompleteIntersection P.completionMap

omit [IsLocalRing B] in
/-- Unfolding the factorization-level kernel condition recovers the map-level condition on the
right map. -/
@[simp] theorem GoodFactorization.kernelIsGeneratedByRegularSequence_iff_right
    (P : GoodFactorization f) :
    P.KernelIsGeneratedByRegularSequence ↔ P.right.KernelIsGeneratedByRegularSequence :=
  Iff.rfl

omit [IsLocalRing B] in
/-- The closed fiber of a good factorization is a regular local ring. -/
theorem GoodFactorization.closedFiber_isRegularLocalRing (P : GoodFactorization f) :
    IsRegularLocalRing P.ClosedFiber :=
  P.closedFiber_regular

/-
The quotient-form closed fiber only depends on `A` and the intermediate ring of the good
factorization, so the target local-ring hypothesis is omitted from this companion theorem.
-/
omit [IsLocalRing B] in
/-- The quotient presentation `S ⧸ 𝔪_A S` of the closed fiber in a good factorization is a
regular local ring. This is the form consumed by the completion-map criterion of
Lemma `23.9.4`. -/
theorem GoodFactorization.closedFiberQuotient_isRegularLocalRing (P : GoodFactorization f) :
    let _ : Algebra A P.middle := P.left.toAlgebra
    IsRegularLocalRing (P.middle ⧸ Ideal.map (algebraMap A P.middle) (maximalIdeal A)) := by
  let _ : Algebra A P.middle := P.left.toAlgebra
  let _ : IsRegularLocalRing P.ClosedFiber := P.closedFiber_isRegularLocalRing
  simpa [GoodFactorization.ClosedFiber, RingHom.algebraMap_toAlgebra] using
    (IsRegularLocalRing.of_ringEquiv
      (closedFiberQuotAlgEquiv :
        Ideal.Fiber (maximalIdeal A) P.middle ≃ₐ[A]
          P.middle ⧸ Ideal.map (algebraMap A P.middle) (maximalIdeal A)).toRingEquiv :
        IsRegularLocalRing (P.middle ⧸ Ideal.map (algebraMap A P.middle) (maximalIdeal A)))

/-- For a good factorization of a complete Noetherian local map, the regular-sequence kernel
condition is equivalent to the canonical local-complete-intersection condition on the induced map
of maximal-ideal completions. -/
theorem GoodFactorization.kernelIsGeneratedByRegularSequence_iff_completionMap_isLocalCompleteIntersection
    (P : GoodFactorization f) [IsNoetherianRing A] [IsNoetherianRing B]
    [IsCompleteLocalRing A] [IsCompleteLocalRing B] :
    P.KernelIsGeneratedByRegularSequence ↔ P.CompletionMapIsLocalCompleteIntersection := by
  let _ : IsLocalHom f := P.isLocalHom
  let _ : Algebra A P.middle := P.left.toAlgebra
  let _ : Algebra P.middle B := P.right.toAlgebra
  let _ : Algebra A B := f.toAlgebra
  let _ : IsScalarTower A P.middle B := IsScalarTower.of_algebraMap_eq' P.comp_eq.symm
  let _ : IsLocalHom (algebraMap A P.middle) := by
    simpa [RingHom.algebraMap_toAlgebra] using P.left_isLocalHom
  let _ : IsLocalHom (algebraMap P.middle B) := by
    simpa [RingHom.algebraMap_toAlgebra] using P.right_isLocalHom
  let _ : IsLocalHom (algebraMap A B) := by
    simpa [RingHom.algebraMap_toAlgebra] using (P.isLocalHom : IsLocalHom f)
  let _ : Module.Flat A P.middle := RingHom.flat_algebraMap_iff.mp <| by
    simpa [RingHom.algebraMap_toAlgebra] using P.left_flat
  simpa [GoodFactorization.KernelIsGeneratedByRegularSequence,
    GoodFactorization.CompletionMapIsLocalCompleteIntersection, GoodFactorization.completionMap,
    GoodFactorization.ClosedFiber, Ideal.Fiber, RingHom.algebraMap_toAlgebra] using
    (RingHom.kernelIsGeneratedByRegularSequence_iff_completionMap_isLocalCompleteIntersection
      P.right_surjective P.closedFiberQuotient_isRegularLocalRing)

/-- The completion-map local-complete-intersection condition is independent of the chosen good
factorization. -/
theorem GoodFactorization.completionMapIsLocalCompleteIntersection_iff
    (P Q : GoodFactorization f) :
    P.CompletionMapIsLocalCompleteIntersection ↔ Q.CompletionMapIsLocalCompleteIntersection := by
  let _ : IsLocalHom f := P.isLocalHom
  simpa [GoodFactorization.CompletionMapIsLocalCompleteIntersection,
    GoodFactorization.completionMap]

/-- For complete Noetherian local source and target, the kernel condition in Lemma 23.9.1 is
independent of the chosen good factorization. -/
theorem GoodFactorization.kernelIsGeneratedByRegularSequence_iff
    (P Q : GoodFactorization f) [IsNoetherianRing A] [IsNoetherianRing B]
    [IsCompleteLocalRing A] [IsCompleteLocalRing B] :
    P.KernelIsGeneratedByRegularSequence ↔ Q.KernelIsGeneratedByRegularSequence := by
  have hP :
      P.KernelIsGeneratedByRegularSequence ↔ P.CompletionMapIsLocalCompleteIntersection := by
    simpa using P.kernelIsGeneratedByRegularSequence_iff_completionMap_isLocalCompleteIntersection
  have hQ :
      Q.KernelIsGeneratedByRegularSequence ↔ Q.CompletionMapIsLocalCompleteIntersection := by
    simpa using Q.kernelIsGeneratedByRegularSequence_iff_completionMap_isLocalCompleteIntersection
  exact hP.trans <|
    (GoodFactorization.completionMapIsLocalCompleteIntersection_iff P Q).trans hQ.symm

/-- For complete Noetherian local source and target, the kernel condition in Lemma 23.9.1 holds
for some good factorization exactly when the induced maximal-ideal completion map attached to a
chosen good factorization is a local complete intersection homomorphism. -/
theorem GoodFactorization.exists_kernelIsGeneratedByRegularSequence_iff_completionMap_isLocalCompleteIntersection
    (P : GoodFactorization f) [IsNoetherianRing A] [IsNoetherianRing B]
    [IsCompleteLocalRing A] [IsCompleteLocalRing B] :
    (∃ Q : GoodFactorization f, Q.KernelIsGeneratedByRegularSequence) ↔
      P.CompletionMapIsLocalCompleteIntersection := by
  have hP :
      P.KernelIsGeneratedByRegularSequence ↔ P.CompletionMapIsLocalCompleteIntersection := by
    simpa using P.kernelIsGeneratedByRegularSequence_iff_completionMap_isLocalCompleteIntersection
  constructor
  · rintro ⟨Q, hQ⟩
    have hQ' :
        Q.KernelIsGeneratedByRegularSequence ↔ Q.CompletionMapIsLocalCompleteIntersection := by
      simpa using Q.kernelIsGeneratedByRegularSequence_iff_completionMap_isLocalCompleteIntersection
    exact
      (GoodFactorization.completionMapIsLocalCompleteIntersection_iff Q P).1 (hQ'.1 hQ)
  · intro hf
    exact ⟨P, hP.2 hf⟩

/-- For complete Noetherian local source and target, the kernel condition in Lemma 23.9.1 holds
for every good factorization exactly when the induced maximal-ideal completion map attached to a
chosen good factorization is a local complete intersection homomorphism. -/
theorem GoodFactorization.forall_kernelIsGeneratedByRegularSequence_iff_completionMap_isLocalCompleteIntersection
    (P : GoodFactorization f) [IsNoetherianRing A] [IsNoetherianRing B]
    [IsCompleteLocalRing A] [IsCompleteLocalRing B] :
    (∀ Q : GoodFactorization f, Q.KernelIsGeneratedByRegularSequence) ↔
      P.CompletionMapIsLocalCompleteIntersection := by
  constructor
  · intro hQ
    exact (P.kernelIsGeneratedByRegularSequence_iff_completionMap_isLocalCompleteIntersection).1
      (hQ P)
  · intro hf Q
    exact
      (Q.kernelIsGeneratedByRegularSequence_iff_completionMap_isLocalCompleteIntersection).2
        ((GoodFactorization.completionMapIsLocalCompleteIntersection_iff Q P).2 hf)

/-- Every local homomorphism of Noetherian complete local rings admits a good factorization. -/
theorem GoodFactorization.nonempty (f : A →+* B) [IsLocalHom f]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsCompleteLocalRing A] [IsCompleteLocalRing B] :
    Nonempty (GoodFactorization f) := by
  sorry

/-- Lemma 23.9.1: let `A → B` be a local homomorphism of Noetherian complete local rings. Then the
condition that for a good factorization `A → S → B` the kernel of `S → B` is generated by a
regular sequence is independent of the chosen good factorization: it holds for some good
factorization if and only if it holds for every good factorization. -/
@[stacks 09QA]
theorem exists_goodFactorization_kernelIsGeneratedByRegularSequence_iff_forall
    (f : A →+* B) [IsNoetherianRing A] [IsNoetherianRing B]
    [IsCompleteLocalRing A] [IsCompleteLocalRing B] [IsLocalHom f] :
    (∃ P : GoodFactorization f, P.KernelIsGeneratedByRegularSequence) ↔
      ∀ P : GoodFactorization f, P.KernelIsGeneratedByRegularSequence := by
  rcases GoodFactorization.nonempty f with ⟨P⟩
  exact
    P.exists_kernelIsGeneratedByRegularSequence_iff_completionMap_isLocalCompleteIntersection.trans
      P.forall_kernelIsGeneratedByRegularSequence_iff_completionMap_isLocalCompleteIntersection.symm

end

end RingHom
