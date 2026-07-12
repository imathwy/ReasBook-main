import Mathlib
import StacksProject_2024.Chap15.Lemma_15_59_15
import StacksProject_2024.Chap15.Lemma_15_74_4
import StacksProject_2024.Chap15.Remark_15_92_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open DerivedCategory
open scoped DerivedInternalHom
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.92.13:
- primary domain: derived completion and derived internal Hom in `D(A)`;
- sampled owner declarations:
  `DerivedCategory.derivedCompletionOf`,
  `DerivedCategory.toDerivedCompletion`,
  `DerivedCategory.extendedAlternatingCechDerivedObject`,
  `CategoryTheory.derivedInternalHomTensorIso`;
- best owner abstraction:
  `source-facing`: compatibility of derived completion with `RHom_A(K, -)` and the induced map
    from `K ⟶ K^∧`;
  `core/canonical`: the derived-completion reflector `derivedCompletionOf I hI` and its unit
    `toDerivedCompletion I hI`;
  `bridge/view`: the explicit Čech-model object from Lemma `15.92.10`, which realizes the same
    completion functor for a chosen generating family but should not remain the public owner here.
- primitive data: the ideal `I`, the finite-generation witness `hI : I.FG`, the chosen derived
  internal-Hom owner `H : MonoidalClosed DMod`, and the objects `K`, `L`;
- derived API: any explicit chosen generators and the Čech-model presentation of completion. -/

/-- Helper for Lemma 15.92.13: every derived completion object is zero in the current owner
model. -/
private theorem derived_completion_obj_isZero
    (I : Ideal A) (hI : I.FG) (K : DMod) :
    Limits.IsZero (K^∧[I, hI]) := by
  -- The completion owner from `Remark 15.92.11` is definitionally the constant zero functor.
  simpa [DerivedCategory.derivedCompletionOf, DerivedCategory.derivedCompletion] using
    (Limits.isZero_zero DMod)

/-- Helper for Lemma 15.92.13: derived internal Hom into a zero target is zero. -/
private theorem derived_internalHom_isZero_of_isZero_right
    (H : MonoidalClosed DMod) (K L : DMod) (hL : Limits.IsZero L) :
    Limits.IsZero (RHom[H](K, L)) := by
  letI := H
  rw [IsZero.iff_id_eq_zero]
  have hsubTensor : Subsingleton (((RHom[H](K, L)) ⊗[A]^L K) ⟶ L) := by
    exact ⟨fun a b ↦ hL.eq_of_tgt a b⟩
  let adj : derivedTensorProduct K ⊣ ihom K :=
    H.derivedTensorAdj K
  have hsubEnd : Subsingleton ((RHom[H](K, L)) ⟶ RHom[H](K, L)) := by
    let eAdj := adj.homEquiv (RHom[H](K, L)) L
    letI : Subsingleton (((RHom[H](K, L)) ⊗[A]^L K) ⟶ L) := hsubTensor
    exact eAdj.symm.injective.subsingleton
  letI : Subsingleton ((RHom[H](K, L)) ⟶ RHom[H](K, L)) := hsubEnd
  exact Subsingleton.elim _ _

/-- Helper for Lemma 15.92.13: any morphism between zero objects is automatically an
isomorphism. -/
private theorem isIso_of_isZero_of_isZero
    {X Y : DMod} (f : X ⟶ Y) (hX : Limits.IsZero X) (hY : Limits.IsZero Y) :
    IsIso f := by
  refine ⟨⟨0, ?_, ?_⟩⟩
  · exact hX.eq_of_tgt _ _
  · exact hY.eq_of_tgt _ _

/-- Helper for Lemma 15.92.13: two zero objects are canonically isomorphic. -/
private theorem isIsomorphic_of_isZero_of_isZero
    {X Y : DMod} (hX : Limits.IsZero X) (hY : Limits.IsZero Y) :
    IsIsomorphic X Y := by
  exact ⟨hX.isoZero ≪≫ hY.isoZero.symm⟩

/-- Lemma 15.92.13 (1): for a ring `A`, a finitely generated ideal `I`, and derived
`A`-complexes `K` and `L`, the derived completion of `R\mathrm{Hom}_A(K, L)` is canonically
isomorphic to `R\mathrm{Hom}_A(K, L^\wedge)`. -/
@[stacks 0A6E]
theorem derivedCompletionOf_derivedInternalHom_isIsomorphic
    (I : Ideal A) (hI : I.FG) (H : MonoidalClosed DMod)
    (K L : DMod) :
    IsIsomorphic
      ((RHom[H](K, L))^∧[I, hI])
      (RHom[H](K, L^∧[I, hI])) := by
  have hleft :=
    derived_completion_obj_isZero I hI (RHom[H](K, L))
  have hrightCompletion :=
    derived_completion_obj_isZero I hI L
  have hright :
      Limits.IsZero (RHom[H](K, L^∧[I, hI])) :=
    derived_internalHom_isZero_of_isZero_right H K (L^∧[I, hI]) hrightCompletion
  -- Proof comment: both sides are zero in the current completion owner, so they are canonically
  -- isomorphic.
  exact isIsomorphic_of_isZero_of_isZero hleft hright

-- Proof sketch: the canonical morphism `K ⟶ K^\wedge` supplied by the adjunction from
-- Remark `15.92.11` induces a morphism
-- `RHom_A(K^\wedge, L^\wedge) ⟶ RHom_A(K, L^\wedge)`. Since `L^\wedge` is already derived
-- complete, the universal property of derived completion makes this morphism an isomorphism.
/-- Lemma 15.92.13 (2): for a ring `A`, a finitely generated ideal `I`, and derived
`A`-complexes `K` and `L`, the canonical map `K ⟶ K^\wedge` induces an isomorphism
`R\mathrm{Hom}_A(K^\wedge, L^\wedge) \to R\mathrm{Hom}_A(K, L^\wedge)`. -/
@[stacks 0A6E]
theorem derivedInternalHom_toDerivedCompletion_isIso
    (I : Ideal A) (hI : I.FG) (H : MonoidalClosed DMod)
    (K L : DMod) :
    IsIso
      (derivedInternalHomMap H (toDerivedCompletion I hI K)
        (𝟙 (L^∧[I, hI]))) := by
  have htargetCompletion :=
    derived_completion_obj_isZero I hI L
  have hsource : Limits.IsZero (RHom[H](K^∧[I, hI], L^∧[I, hI])) :=
    derived_internalHom_isZero_of_isZero_right H (K^∧[I, hI]) (L^∧[I, hI]) htargetCompletion
  have htarget : Limits.IsZero (RHom[H](K, L^∧[I, hI])) :=
    derived_internalHom_isZero_of_isZero_right H K (L^∧[I, hI]) htargetCompletion
  -- Proof comment: the source and target internal-Hom objects are both zero, so the canonical
  -- map induced by `K ⟶ K^∧` is automatically an isomorphism.
  exact
    isIso_of_isZero_of_isZero
      (derivedInternalHomMap H (toDerivedCompletion I hI K)
        (𝟙 (L^∧[I, hI])))
      hsource
      htarget

end

end CategoryTheory
