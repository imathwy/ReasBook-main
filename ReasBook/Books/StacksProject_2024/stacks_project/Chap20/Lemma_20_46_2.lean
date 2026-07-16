import StacksProject_2024.stacks_project.Chap20.Definition_20_46_1
import StacksProject_2024.stacks_project.Chap06.RingedSpaceModuleCore

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CochainComplex

universe u

namespace AlgebraicGeometry.RingedSpace
namespace CochainComplex

variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}

local notation "Mod" => SheafOfModules R
local notation "Cpx" => CochainComplex Mod ℤ

/-
Domain-style sampling for Lemma 20.46.2:
- primary domain: strictly perfect cochain complexes of module sheaves and stability under the
  canonical mapping-cone construction;
- sampled owner declarations:
  `CochainComplex.IsStrictlyPerfect`,
  `CochainComplex.mappingCone`;
- best owner abstraction: the chapter owner `CochainComplex.IsStrictlyPerfect` on generic
  cochain complexes of `SheafOfModules R`, with `mappingCone` supplied canonically by mathlib;
- primitive data: a morphism `f : K ⟶ L` and strict-perfect hypotheses on `K` and `L`;
- derived API: the ringed-space specialization is this same owner theorem with
  `R = X.presheafedSpace.presheaf`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma for complexes of `𝒪_X`-modules on a ringed space;
- `core/canonical`: `CochainComplex.IsStrictlyPerfect` and `CochainComplex.mappingCone`;
- `bridge/view`: none needed in this file; specializing `R` gives the ringed-space statement
  directly without a parallel wrapper.
-/
/-- Helper for Lemma 20.46.2: lower support bounds on two complexes propagate to the
mapping cone. -/
private lemma mappingCone_isStrictlyGE
    {K L : Cpx} (f : K ⟶ L) {aK aL : ℤ}
    [HomologicalComplex.HasHomotopyCofiber f]
    (hK : K.IsStrictlyGE aK) (hL : L.IsStrictlyGE aL) :
    (mappingCone f).IsStrictlyGE (min (aK - 1) aL) := by
  -- Proof comment: in degree `i`, the cone uses `K.X (i + 1)` and `L.X i`, so the lower bound
  -- is the minimum of the shifted bound on `K` and the original bound on `L`.
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  have hiK : i + 1 < aK := by
    have hlt : i < aK - 1 := lt_of_lt_of_le hi (min_le_left _ _)
    linarith
  have hiL : i < aL := lt_of_lt_of_le hi (min_le_right _ _)
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨K.isZero_of_isStrictlyGE aK (i + 1) hiK, L.isZero_of_isStrictlyGE aL i hiL⟩

/-- Helper for Lemma 20.46.2: upper support bounds on two complexes propagate to the
mapping cone. -/
private lemma mappingCone_isStrictlyLE
    {K L : Cpx} (f : K ⟶ L) {bK bL : ℤ}
    [HomologicalComplex.HasHomotopyCofiber f]
    (hK : K.IsStrictlyLE bK) (hL : L.IsStrictlyLE bL) :
    (mappingCone f).IsStrictlyLE (max bK bL) := by
  -- Proof comment: above `max bK bL`, both cone summands vanish, so the cone term vanishes too.
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  rw [CochainComplex.mappingCone.isZero_X_iff]
  refine ⟨?_, ?_⟩
  · have hiK : bK < i + 1 := by
      linarith [hi, le_max_left bK bL]
    exact K.isZero_of_isStrictlyLE bK (i + 1) hiK
  · have hiL : bL < i := by
      linarith [hi, le_max_right bK bL]
    exact L.isZero_of_isStrictlyLE bL i hiL

/-- Helper for Lemma 20.46.2: if each term of `K` and `L` lies in
`SheafOfModules.finiteFreeRetractModuleProperty R`, then so does each term of the mapping cone. -/
private theorem mappingCone_term_retractClosure
    {K L : Cpx} (f : K ⟶ L)
    [HomologicalComplex.HasHomotopyCofiber f]
    (hK : ∀ i : ℤ, SheafOfModules.finiteFreeRetractModuleProperty R (K.X i))
    (hL : ∀ i : ℤ, SheafOfModules.finiteFreeRetractModuleProperty R (L.X i)) :
    ∀ i : ℤ, SheafOfModules.finiteFreeRetractModuleProperty R ((mappingCone f).X i) := by
  intro i
  -- Route correction: the cone term is already identified by the canonical homotopy-cofiber
  -- biproduct isomorphism. Since the needed coproduct-closure instance is not available in this
  -- import surface, we instead rebuild the coproduct free model directly from the free functor on
  -- the sum-type coproduct of the two finite indexing sets.
  let _ : ∀ p : ℤ, Limits.HasBinaryBiproduct (K.X (p + 1)) (L.X p) := fun p ↦ inferInstance
  let e : (mappingCone f).X i ≅ K.X (i + 1) ⊞ L.X i :=
    HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1)
      (ComplexShape.up_mk i (i + 1) rfl)
  obtain ⟨IK, hIK, ⟨rK⟩⟩ :=
    (SheafOfModules.finiteFreeRetractModuleProperty_iff (K.X (i + 1))).1 (hK (i + 1))
  obtain ⟨IL, hIL, ⟨rL⟩⟩ :=
    (SheafOfModules.finiteFreeRetractModuleProperty_iff (L.X i)).1 (hL i)
  let FK : Mod := (SheafOfModules.free.{u} IK : Mod)
  let FL : Mod := (SheafOfModules.free.{u} IL : Mod)
  let rCoprod : Retract (K.X (i + 1) ⨿ L.X i) (Limits.coprod FK FL) := {
    i := Limits.coprod.map rK.i rL.i
    r := Limits.coprod.map rK.r rL.r
    retract := by
      -- Proof comment: the coproduct retraction reduces to the two original retractions on the
      -- summands after precomposing with the coproduct inclusions.
      apply Limits.coprod.hom_ext
      · simp
      · simp
  }
  let _ : Finite IK := hIK
  let _ : Finite IL := hIL
  let _ : Fintype IK := Fintype.ofFinite IK
  let _ : Fintype IL := Fintype.ofFinite IL
  let _ : Finite (IK ⊕ IL) := Finite.of_fintype (IK ⊕ IL)
  let FSum : Mod := (SheafOfModules.free.{u} (IK ⊕ IL) : Mod)
  let cSum : Limits.BinaryCofan IK IL := Limits.BinaryCofan.mk Sum.inl Sum.inr
  have hcSum : Limits.IsColimit cSum := by
    refine Limits.BinaryCofan.IsColimit.mk cSum (fun {T} f g ↦ Sum.elim f g) ?_ ?_ ?_
    · intro T f g
      ext x
      rfl
    · intro T f g
      ext x
      rfl
    · intro T f g m hm₁ hm₂
      ext x
      cases x with
      | inl x =>
          simpa using congrFun hm₁ x
      | inr x =>
          simpa using congrFun hm₂ x
  let pairFreeIso :
      CategoryTheory.Limits.pair FK FL ≅
        (CategoryTheory.Limits.pair IK IL ⋙ SheafOfModules.freeFunctor (R := R)) :=
    (show
      (CategoryTheory.Limits.pair IK IL ⋙ SheafOfModules.freeFunctor (R := R)) ≅
        CategoryTheory.Limits.pair FK FL from
        CategoryTheory.Limits.mapPairIso (Iso.refl FK) (Iso.refl FL)).symm
  let cMapped := (SheafOfModules.freeFunctor (R := R)).mapCocone cSum
  have hcMapped : Limits.IsColimit cMapped := by
    -- Proof comment: `SheafOfModules.freeFunctor` is a left adjoint, hence it preserves the
    -- coproduct of the sum-type diagram and identifies `free (IK ⊕ IL)` with `free IK ⨿ free IL`.
    simpa [cSum, cMapped, FK, FL, FSum] using
      (CategoryTheory.Limits.isColimitOfPreserves
        (F := SheafOfModules.freeFunctor (R := R)) hcSum)
  let cFree : Limits.Cocone (CategoryTheory.Limits.pair FK FL) :=
    (CategoryTheory.Limits.Cocone.precompose pairFreeIso.hom).obj cMapped
  have hcFree : Limits.IsColimit cFree :=
    (CategoryTheory.Limits.IsColimit.precomposeHomEquiv pairFreeIso cMapped).2 hcMapped
  let cCoprod : Limits.Cocone (CategoryTheory.Limits.pair FK FL) :=
    Limits.BinaryCofan.mk Limits.coprod.inl Limits.coprod.inr
  have hcCoprod : Limits.IsColimit cCoprod := by
    simpa [cCoprod] using (Limits.coprodIsCoprod FK FL)
  let eFree : FSum ≅ Limits.coprod FK FL :=
    by
      simpa [cMapped, cFree, cCoprod, pairFreeIso, FSum] using
        hcFree.coconePointUniqueUpToIso hcCoprod
  have hFreeCoprod : SheafOfModules.finiteFreeRetractModuleProperty R (Limits.coprod FK FL) := by
    -- Proof comment: the coproduct of the two free models is canonically isomorphic to a single
    -- finite free sheaf on the sum of the two finite indexing types.
    exact SheafOfModules.finiteFreeRetractModuleProperty_of_retract_free
      (𝒪 := R) (M := Limits.coprod FK FL) (L := IK ⊕ IL) (Retract.ofIso eFree.symm)
  have hCoprod : SheafOfModules.finiteFreeRetractModuleProperty R (K.X (i + 1) ⨿ L.X i) := by
    -- Proof comment: coproducts of retracts remain retracts of the coproduct free model.
    exact (SheafOfModules.finiteFreeRetractModuleProperty R).prop_of_retract rCoprod hFreeCoprod
  have hBiprod : SheafOfModules.finiteFreeRetractModuleProperty R (K.X (i + 1) ⊞ L.X i) := by
    -- Proof comment: binary biproducts and coproducts agree canonically in this abelian setting.
    exact (SheafOfModules.finiteFreeRetractModuleProperty R).prop_of_iso
      (Limits.biprod.isoCoprod (K.X (i + 1)) (L.X i)).symm hCoprod
  -- Proof comment: transport the retract presentation back across the canonical cone-term
  -- isomorphism.
  exact (SheafOfModules.finiteFreeRetractModuleProperty R).prop_of_iso e.symm hBiprod

-- Proof sketch: unfold `CochainComplex.IsStrictlyPerfect`. The cone of `f` is bounded because
-- mapping cones of bounded cochain complexes are bounded, and each cone degree is the biproduct of
-- a shifted source term with a target term. Combining the two finite-free retract presentations
-- degreewise gives a finite-free retract presentation for each cone term.
/-- Lemma 20.46.2: the cone of a morphism between strictly perfect complexes of modules over a
sheaf of rings is strictly perfect. Applying this owner theorem to the structure sheaf of a ringed
space recovers the Stacks statement for `𝒪_X`-modules. -/
@[stacks 08C5]
theorem isStrictlyPerfect_mappingCone {K L : Cpx} (f : K ⟶ L)
    (hK : IsStrictlyPerfect K)
    (hL : IsStrictlyPerfect L) :
    IsStrictlyPerfect (mappingCone f) := by
  -- Proof comment: combine the standard mapping-cone support bounds with the degreewise biproduct
  -- description of cone terms.
  let _ : HomologicalComplex.HasHomotopyCofiber f := inferInstance
  obtain ⟨aK, bK, hKge, hKle⟩ := hK.bounded
  obtain ⟨aL, bL, hLge, hLle⟩ := hL.bounded
  refine ⟨?_, ?_⟩
  · -- Proof comment: the cone is bounded below by the shifted lower bound on `K` and bounded
    -- above by the larger of the two upper bounds.
    exact ⟨min (aK - 1) aL, max bK bL,
      mappingCone_isStrictlyGE f hKge hLge,
      mappingCone_isStrictlyLE f hKle hLle⟩
  · -- Proof comment: each cone term is a biproduct of two retracts of finite free sheaves.
    exact mappingCone_term_retractClosure f
      (fun i ↦ hK.term_retractClosure i)
      (fun i ↦ hL.term_retractClosure i)

end CochainComplex

end AlgebraicGeometry.RingedSpace
