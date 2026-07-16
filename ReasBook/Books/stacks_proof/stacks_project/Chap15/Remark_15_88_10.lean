import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import stacks_proof.stacks_project.Chap15.Lemma_15_88_1_FixedBase

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "SeqMod" => SequentialInverseSystem (ModuleCat A)
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "DSeq" => DerivedCategory SeqMod
local notation "KSeq" => HomotopyCategory SeqMod (up ℤ)
local notation "CpxSeq" => CochainComplex SeqMod ℤ
local notation "Δ" => (Functor.const ℕᵒᵖ : ModuleCat A ⥤ SeqMod)

/- Domain-style sampling for Remark 15.88.10:
- primary domain: the fixed-base derived inverse-limit functor `R lim` on sequential inverse
  systems of `A`-modules, together with the fixed-right-factor derived tensor endofunctor on
  `D(ℕᵒᵖ ⥤ Mod A)`;
- sampled owner declarations:
  `CategoryTheory.additiveFunctorTotalRightDerived (lim : SeqMod ⥤ ModuleCat A)`,
  `Functor.mapDerivedCategory`,
  `Functor.totalLeftDerived`,
  `CategoryTheory.Quotient.lift`,
  `HomologicalComplex.mapBifunctorMapHomotopy₁`,
  `Functor.totalLeftDerived`;
- best owner abstraction: the source-facing remark is the composite
  `D(A) ⥤ D(ℕᵒᵖ ⥤ Mod A) ⥤ D(ℕᵒᵖ ⥤ Mod A) ⥤ D(A)`, whose middle factor is not a new local
  public owner but a private bridge functor built by left deriving totalized tensoring with a
  chosen representative of the right factor;
- primitive vs. derived:
  primitive data are the fixed derived inverse system `E : DSeq`, the diagonal functor `Δ`, and
  the fixed-base derived inverse-limit owner
  `additiveFunctorTotalRightDerived (lim : SeqMod ⥤ ModuleCat A)`;
  derived API is the source-facing composite functor of the remark.
- source/core/bridge triage:
  `source-facing`: `derivedInverseLimitTensorFunctor`;
  `core/canonical`: `Functor.mapDerivedCategory`, `Functor.totalLeftDerived`,
    `CategoryTheory.Quotient.lift`, and
    `additiveFunctorTotalRightDerived (lim : SeqMod ⥤ ModuleCat A)`;
  `bridge/view`: the private fixed-base derived tensor helper used to express the remark as a
    composite functor without introducing a second public tensor owner. -/

/-- The pointwise tensor product on sequential inverse systems of `A`-modules is additive in each
variable. -/
local instance sequentialAModuleInverseSystem_monoidalPreadditive :
    MonoidalPreadditive SeqMod where
  whiskerLeft_zero := by
    intro X Y Z
    apply NatTrans.ext
    funext n
    change X.obj n ◁ (0 : Y.obj n ⟶ Z.obj n) = 0
    simp
  zero_whiskerRight := by
    intro X Y Z
    apply NatTrans.ext
    funext n
    change (0 : Y.obj n ⟶ Z.obj n) ▷ X.obj n = 0
    simp
  whiskerLeft_add := by
    intro X Y Z f g
    apply NatTrans.ext
    funext n
    change X.obj n ◁ (f.app n + g.app n) = X.obj n ◁ f.app n + X.obj n ◁ g.app n
    simp
  add_whiskerRight := by
    intro X Y Z f g
    apply NatTrans.ext
    funext n
    change (f.app n + g.app n) ▷ X.obj n = f.app n ▷ X.obj n + g.app n ▷ X.obj n
    simp

/-- The homotopy-category tensor-totalization functor on sequential inverse systems with fixed
right tensor factor. -/
private abbrev totalizedTensorWithFixedComplexHomotopyFunctor
    (P : CpxSeq) :
    KSeq ⥤ KSeq :=
  CategoryTheory.Quotient.lift _
    ((((curriedTensor SeqMod).map₂CochainComplex).flip.obj P) ⋙
      HomotopyCategory.quotient SeqMod (up ℤ))
    (fun _ _ _ _ ⟨h⟩ ↦
      HomotopyCategory.eq_of_homotopy _ _
        (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 P)
          (curriedTensor SeqMod) (up ℤ)))

/-- The homotopy-category source functor whose total left derived functor computes tensoring by a
chosen derived inverse system `E`. -/
private abbrev tensorRightDerivedSourceFunctor
    (E : DSeq) : KSeq ⥤ DSeq :=
  totalizedTensorWithFixedComplexHomotopyFunctor
      (((DerivedCategory.Qh : KSeq ⥤ DSeq).objPreimage E).as) ⋙
    (DerivedCategory.Qh : KSeq ⥤ DSeq)

/-- Tensoring with a fixed derived inverse system admits a total left derived endofunctor on
`D(ℕᵒᵖ ⥤ Mod A)`. -/
private theorem tensorRightDerivedSourceFunctor_hasLeftDerivedFunctor
    (E : DSeq) :
    (tensorRightDerivedSourceFunctor E).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso SeqMod (up ℤ)) := sorry

/-- The fixed-right-factor derived tensor endofunctor on `D(ℕᵒᵖ ⥤ Mod A)`. This helper stays
private so the remark exposes only the source-facing composite functor below. -/
private noncomputable abbrev tensorRightDerivedFunctor
    (E : DSeq) : DSeq ⥤ DSeq :=
  letI := tensorRightDerivedSourceFunctor_hasLeftDerivedFunctor E
  (tensorRightDerivedSourceFunctor E).totalLeftDerived
    (DerivedCategory.Qh : KSeq ⥤ DSeq)
    (HomotopyCategory.quasiIso SeqMod (up ℤ))

/-- The private fixed-right-factor derived tensor helper commutes with the triangulated shift. -/
private noncomputable instance tensorRightDerivedFunctor_commShift
    (E : DSeq) :
    (tensorRightDerivedFunctor E).CommShift ℤ := sorry

/-- The private fixed-right-factor derived tensor helper is exact in the triangulated sense. -/
private theorem tensorRightDerivedFunctor_isTriangulated
    (E : DSeq) :
    (tensorRightDerivedFunctor E).IsTriangulated := sorry

/-- The constant inverse-system functor on `A`-modules is additive. -/
local instance constantInverseSystemFunctor_additive :
    ((Functor.const ℕᵒᵖ : ModuleCat A ⥤ SeqMod)).Additive where
  map_add := by
    intro X Y f g
    ext n x
    rfl

/-- The constant inverse-system functor on `A`-modules preserves finite limits. -/
local instance constantInverseSystemFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (Functor.const ℕᵒᵖ : ModuleCat A ⥤ SeqMod) := by
  infer_instance

/-- The constant inverse-system functor on `A`-modules preserves finite colimits. -/
local instance constantInverseSystemFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (Functor.const ℕᵒᵖ : ModuleCat A ⥤ SeqMod) := by
  infer_instance

/-- Remark 15.88.10: for a chosen lift `E ∈ D(ℕᵒᵖ ⥤ Mod A)` of the inverse system `(E_n)` in
`D(A)`, the functor
`K ↦ R lim (Δ(K) ⊗_A^{\mathbf L} E)` is the composite of the diagonal functor
`D(A) ⥤ D(ℕᵒᵖ ⥤ Mod A)`, the fixed-right-factor derived tensor endofunctor, and the derived
inverse-limit functor from Lemma `15.88.1`. -/
@[stacks 091J]
abbrev derivedInverseLimitTensorFunctor
    (E : DSeq) : DMod ⥤ DMod :=
  (((Functor.const ℕᵒᵖ : ModuleCat A ⥤ SeqMod).mapDerivedCategory) : DMod ⥤ DSeq) ⋙
    tensorRightDerivedFunctor E ⋙
    additiveFunctorTotalRightDerived.{u + 1, u + 1, u + 1, u, u}
      (lim : SeqMod ⥤ ModuleCat A)

/-- The fixed-base tensor-derived-inverse-limit functor commutes with the triangulated shift. -/
noncomputable instance derivedInverseLimitTensorFunctor_commShift
    (E : DSeq) :
    (derivedInverseLimitTensorFunctor E).CommShift ℤ := by
  dsimp [derivedInverseLimitTensorFunctor]
  infer_instance

-- Proof sketch: the diagonal functor is exact because it is induced from an exact functor between
-- abelian categories, the middle tensor functor is exact by
-- `tensorRightDerivedFunctor_isTriangulated`, and the derived inverse-limit functor is exact as
-- the triangulated right derived functor used in Lemma `15.88.1`; the composite of exact
-- functors is exact.
/-- The functor `K ↦ R lim (Δ(K) ⊗_A^{\mathbf L} E)` is exact in the triangulated sense. -/
theorem derivedInverseLimitTensorFunctor_isTriangulated
    (E : DSeq) :
    (derivedInverseLimitTensorFunctor E).IsTriangulated := by
  letI : (derivedInverseLimitTensorFunctor E).CommShift ℤ := by
    simpa using derivedInverseLimitTensorFunctor_commShift E
  sorry

end
