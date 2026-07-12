import StacksProject_2024.Chap13.Lemma_13_5_7
import StacksProject_2024.Chap13.Lemma_13_5_4
import StacksProject_2024.Chap13.Definition_13_6_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.MorphismProperty
open CategoryTheory.MorphismProperty.IsInvertedBy
open scoped CategoryTheory.ObjectProperty

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

section

variable {D : Type u₁} [Category.{v₁} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
variable (P : ObjectProperty D) [P.IsTriangulated]
variable {A : Type u₂} [Category.{v₂} A] [Abelian A]
variable {D' : Type u₃} [Category.{v₃} D'] [Limits.HasZeroObject D'] [HasShift D' ℤ]
  [Preadditive D'] [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']

local instance trWQ_isLocalization : P.trW.Q.IsLocalization P.trW :=
  Functor.q_isLocalization P.trW

/-- Helper for Lemma 13.6.8: the Verdier quotient carries the canonical shift structure coming
from the localization `P.trW.Localization`. -/
local instance verdierQuotientHasShift : HasShift (D / P) ℤ := by
  change HasShift P.trW.Localization ℤ
  infer_instance

/-- Helper for Lemma 13.6.8: the Verdier quotient functor commutes with the canonical shift on the
quotient category. -/
local instance verdierQuotientFunctorCommShift : (P.trW.Q : D ⥤ D / P).CommShift ℤ := by
  infer_instance

/-- Helper for Lemma 13.6.8: the Verdier quotient carries the canonical pretriangulated structure
induced by localization. -/
local instance verdierQuotientPretriangulated : Pretriangulated (D / P) := by
  change Pretriangulated P.trW.Localization
  infer_instance

/-- Helper for Lemma 13.6.8: all shift functors on the Verdier quotient are additive because the
localized shifts on `P.trW.Localization` are additive. -/
local instance verdierQuotientShiftAdditive :
    ∀ n : ℤ, Functor.Additive (shiftFunctor (D / P) n) := by
  intro n
  change Functor.Additive (shiftFunctor P.trW.Localization n)
  infer_instance

/-- Helper for Lemma 13.6.8: the localization model `P.trW.Localization` carries additive shift
functors in the bundled `∀ n` form expected by the triangulated owner API. -/
local instance verdierLocalizationShiftAdditive :
    ∀ n : ℤ, Functor.Additive (shiftFunctor P.trW.Localization n) := by
  intro n
  infer_instance

/-- Helper for Lemma 13.6.8: the Verdier quotient is triangulated because `D` is triangulated and
`P` is a triangulated subcategory. -/
local instance verdierQuotientIsTriangulated : IsTriangulated (D / P) := by
  change IsTriangulated P.trW.Localization
  infer_instance

/-- Helper for Lemma 13.6.8: the Verdier quotient functor is triangulated with respect to the
canonical triangulated structure on the quotient. -/
local instance verdierQuotientFunctorIsTriangulated :
    (P.trW.Q : D ⥤ D / P).IsTriangulated := by
  letI : ∀ n : ℤ, Functor.Additive (shiftFunctor P.trW.Localization n) :=
    verdierLocalizationShiftAdditive P
  change (P.trW.Q : D ⥤ P.trW.Localization).IsTriangulated
  infer_instance

omit [IsTriangulated D] [P.IsTriangulated] in
/-- Helper for Lemma 13.6.8: if a homological functor vanishes on `P`, then it inverts every
morphism in the Verdier class `P.trW`. -/
private theorem trW_isInvertedBy_of_le_homologicalKernel
    (H : D ⥤ A) [H.IsHomological] (hP : P ≤ H.homologicalKernel) :
    IsInvertedBy P.trW H := by
  letI := Functor.ShiftSequence.tautological H ℤ
  -- First pass to the shift-zero companion, where `mem_homologicalKernel_trW_iff` applies
  -- directly to the source hypothesis `P ≤ H.homologicalKernel`.
  have hShift : IsInvertedBy P.trW (H.shift (0 : ℤ)) := by
    intro X Y f hf
    have hf' : H.homologicalKernel.trW f := by
      rcases hf with ⟨Z, g, h, hT, hZ⟩
      exact ⟨Z, g, h, hT, hP _ hZ⟩
    exact ((H.mem_homologicalKernel_trW_iff f).1 hf') 0
  -- The shift-zero functor is canonically isomorphic to `H`, so invertedness transfers back.
  rw [← MorphismProperty.IsInvertedBy.iff_of_iso P.trW (H.isoShiftZero ℤ)]
  exact hShift

omit [IsTriangulated D] [P.IsTriangulated] in
/-- Helper for Lemma 13.6.8: if an exact functor vanishes on `P`, then it inverts every morphism
in the Verdier class `P.trW`. -/
private theorem trW_isInvertedBy_of_le_kernel
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated] (hP : P ≤ F.kernel) :
    IsInvertedBy P.trW F := by
  -- Route correction: avoid proving exactness of the quotient lift directly; first identify the
  -- larger kernel-generated Verdier class that `F` already inverts.
  have hkernel : IsInvertedBy F.kernel.trW F := by
    intro X Y f hf
    simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F,
      MorphismProperty.inverseImage_iff, isomorphisms.iff] using hf
  refine of_le P.trW F.kernel.trW F hkernel ?_
  intro _ _ f hf
  rcases hf with ⟨Z, g, h, hT, hZ⟩
  exact ⟨Z, g, h, hT, hP _ hZ⟩

/-- Helper for Lemma 13.6.8: a strict quotient factorization of a homological functor is
homological. -/
private theorem strict_homological_factorization_isHomological
    (H : D ⥤ A) [H.IsHomological] (H' : D / P ⥤ A)
    (hfac : (P.trW.Q : D ⥤ D / P) ⋙ H' = H) :
    H'.IsHomological := by
  -- The quotient functor is essentially surjective on arrows, so homologicality descends.
  letI : Functor.EssSurj ((P.trW.Q).mapArrow) := Localization.essSurj_mapArrow P.trW.Q P.trW
  exact Functor.isHomological_of_localization P.trW.Q H' H (eqToIso hfac)

/-- Helper for Lemma 13.6.8: a strict quotient factorization of an exact functor carries the
canonical exact structure induced from localization. -/
private theorem strict_exact_factorization_has_exact_structure
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated] (F' : D / P ⥤ D')
    (hfac : (P.trW.Q : D ⥤ D / P) ⋙ F' = F) :
    ∃ hcomm : F'.CommShift ℤ, letI : F'.CommShift ℤ := hcomm; F'.IsTriangulated := by
  -- Route correction: package the strict factorization as a localization lifting and use the
  -- canonical shift structure produced by `Functor.commShiftOfLocalization`.
  letI : HasShift (D / P) ℤ := verdierQuotientHasShift P
  letI : (P.trW.Q : D ⥤ D / P).CommShift ℤ := verdierQuotientFunctorCommShift P
  letI : Pretriangulated (D / P) := verdierQuotientPretriangulated P
  letI : IsTriangulated (D / P) := verdierQuotientIsTriangulated P
  letI : Localization.Lifting P.trW.Q P.trW F F' := ⟨eqToIso hfac⟩
  let hcomm : F'.CommShift ℤ :=
    Functor.commShiftOfLocalization (P.trW.Q : D ⥤ D / P) P.trW ℤ F F'
  refine ⟨hcomm, ?_⟩
  letI : F'.CommShift ℤ := hcomm
  -- Exactness then descends along the quotient functor once the localization comparison iso is
  -- known to commute with shifts and the quotient is essentially surjective on arrows.
  letI : Functor.EssSurj ((P.trW.Q).mapArrow) := Localization.essSurj_mapArrow P.trW.Q P.trW
  letI : NatTrans.CommShift (Localization.Lifting.iso P.trW.Q P.trW F F').hom ℤ :=
    by
      -- With the canonical localization-induced `CommShift`, shift compatibility of the
      -- comparison isomorphism is already packaged by mathlib.
      exact inferInstanceAs (NatTrans.CommShift
        (Localization.Lifting.iso P.trW.Q P.trW F F').hom ℤ)
  letI : ∀ n : ℤ, Functor.Additive (shiftFunctor P.trW.Localization n) :=
    verdierLocalizationShiftAdditive P
  letI : Pretriangulated P.trW.Localization := by
    simpa using (verdierQuotientPretriangulated (P := P) : Pretriangulated (D / P))
  letI : IsTriangulated P.trW.Localization := by
    simpa using (verdierQuotientIsTriangulated (P := P) : IsTriangulated (D / P))
  -- Isolate the final owner theorem in a smaller subproof so elaboration sees the local exact
  -- structure on the quotient functor directly.
  let htri : F'.IsTriangulated := by
    letI : (P.trW.Q : D ⥤ D / P).IsTriangulated := by
      exact Triangulated.Localization.isTriangulated_functor (L := P.trW.Q) (W := P.trW)
    exact Functor.isTriangulated_of_precomp_iso
      (F := (P.trW.Q : D ⥤ D / P)) (G := F') (H := F)
      (Localization.Lifting.iso P.trW.Q P.trW F F')
  exact htri

/- Domain-style sampling for Lemma `13.6.8`.
- primary domain: Verdier localization of triangulated categories and factorization of functors
  through the quotient by a triangulated subcategory;
- sampled owner declarations:
  `Localization.Construction.lift`,
  `Localization.Construction.fac`,
  `Localization.liftNatIso`,
  `homological_factorization_isHomological`,
  `exact_factorization_isTriangulated`;
- best owner abstraction: the quotient functor `P.trW.Q` together with its canonical
  localization lifts; the source-facing theorem here needs the strict construction
  lift `Localization.Construction.lift` because the statement asks for literal equality
  `P.trW.Q ⋙ H' = H`, while homologicality and exactness should still be imported from the
  canonical localization-lift theorems rather than reproved locally;
- primitive data: a functor `H` or `F` together with the source-faithful hypothesis that `P`
  lies in its homological kernel or ordinary kernel, equivalently that `P.trW` is inverted;
- derived API: the lifted functor through `P.trW.Q`, its factorization equality, uniqueness, and
  the induced homological / triangulated structure.

Source/core/bridge triage:
- `source-facing`: the two existence-and-uniqueness statements below, matching the textbook lemma;
- `core/canonical`: `Localization.Construction.lift` / `fac` / `uniq`,
  `Localization.liftNatIso`, and the owner theorems
  `homological_factorization_isHomological` / `exact_factorization_isTriangulated`;
- `bridge/view`: the passage from the source hypothesis `P ≤ H.homologicalKernel` or
  `P ≤ F.kernel` to the inverted-morphism hypothesis needed by the localization owner,
  and then from the strict construction lift to the canonical localization lift up to iso.

Accordingly, this file keeps the source-facing existential statements, while direct downstream use
should prefer the canonical localization lift itself rather than re-extracting a witness from
`∃!`. -/

-- Proof sketch: the hypothesis `P ≤ H.homologicalKernel` implies that every morphism in `P.trW`
-- is inverted by `H`. The source-facing statement asks for a strict factorization equality, so we
-- take the strict construction lift `Localization.Construction.lift H hH`. To import the
-- homological structure canonically, compare this strict lift with the canonical localization lift
-- `Localization.lift H hH P.trW.Q` via `Localization.liftNatIso`, and transfer the owner theorem
-- `homological_factorization_isHomological`.
/-- Lemma 13.6.8 (1): if a homological functor `H : D ⥤ A` vanishes on the full triangulated
subcategory `P`, then there exists a unique factorization of `H` through the Verdier quotient
functor `P.trW.Q : D ⥤ D / P`, and the factor functor is homological. -/
theorem existsUnique_homological_factorization_through_triangulated_quotient
    (H : D ⥤ A) [H.IsHomological] (hP : P ≤ H.homologicalKernel) :
    ∃! H' : D / P ⥤ A, P.trW.Q ⋙ H' = H ∧ H'.IsHomological := by
  -- The source hypothesis identifies the exact morphism property needed by localization.
  have hH : P.trW.IsInvertedBy H := trW_isInvertedBy_of_le_homologicalKernel P H hP
  let hQ := Localization.strictUniversalPropertyFixedTargetQ P.trW A
  let H' : D / P ⥤ A := hQ.lift H hH
  refine ⟨H', ?_, ?_⟩
  · refine ⟨hQ.fac H hH, ?_⟩
    -- The strict lift is homological by the localization descent helper.
    exact strict_homological_factorization_isHomological P H H' (hQ.fac H hH)
  · intro H'' hH''
    -- Uniqueness is the strict universal property of the quotient functor.
    exact hQ.uniq _ _ (hH''.1.trans (hQ.fac H hH).symm)

-- Proof sketch: since `P ≤ F.kernel`, every morphism in `P.trW` is sent by `F` to an
-- isomorphism, so the strict construction lift gives the required literal factorization. The
-- exact structure on this strict lift comes from the owner API for localization lifts:
-- `Functor.commShiftOfLocalization` provides the induced `CommShift ℤ` structure, and
-- `Functor.isTriangulated_of_precomp_iso` upgrades it to a triangulated functor.
/-- Lemma 13.6.8 (2): if an exact functor `F : D ⥤ D'` vanishes on the full triangulated
subcategory `P`, then there exists a unique factorization of `F` through the Verdier quotient
functor `P.trW.Q : D ⥤ D / P`, and the factor functor is exact; in Lean, exactness is encoded by
the existence of a `CommShift ℤ` structure together with `Functor.IsTriangulated`. -/
theorem existsUnique_exact_factorization_through_triangulated_quotient
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated] (hP : P ≤ F.kernel) :
    ∃! F' : D / P ⥤ D',
      (P.trW.Q ⋙ F' = F) ∧
        ∃ hcomm : F'.CommShift ℤ, letI : F'.CommShift ℤ := hcomm; F'.IsTriangulated := by
  let hF : P.trW.IsInvertedBy F := trW_isInvertedBy_of_le_kernel P F hP
  let hQ := Localization.strictUniversalPropertyFixedTargetQ P.trW D'
  let F' : D / P ⥤ D' := hQ.lift F hF
  refine ⟨F', ?_, ?_⟩
  · refine ⟨hQ.fac F hF, ?_⟩
    -- The strict lift inherits its exact structure from the canonical localization lifting data.
    exact strict_exact_factorization_has_exact_structure P F F' (hQ.fac F hF)
  · intro F'' hF''
    -- Again, strict uniqueness comes from the localization universal property.
    exact hQ.uniq _ _ (hF''.1.trans (hQ.fac F hF).symm)

end

end CategoryTheory
