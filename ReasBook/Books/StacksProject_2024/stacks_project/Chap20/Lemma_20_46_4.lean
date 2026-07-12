import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap18.Lemma_18_17_2
import StacksProject_2024.Chap20.Definition_20_46_1

open AlgebraicGeometry
open CategoryTheory
open scoped RingedSpace.Hom
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

namespace CochainComplex

variable {X Y : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "ModY" => RingedSpace.Modules Y
local notation "FiniteFreeRetractsX" =>
  SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf

section

variable (f : X ⟶ Y)

local notation "fStar" => f^*
local notation "fStarComplex" => Functor.mapHomologicalComplex (fStar) (up ℤ)

/-- Helper for Lemma 20.46.4: strict lower and upper bounds are preserved by pullback. -/
private lemma pullback_bounded
    (E : CochainComplex ModY ℤ)
    (hbounded : ∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b) :
    ∃ a b : ℤ,
      CochainComplex.IsStrictlyGE ((fStarComplex).obj E) a ∧
        CochainComplex.IsStrictlyLE ((fStarComplex).obj E) b := by
  rcases hbounded with ⟨a, b, hGE, hLE⟩
  refine ⟨a, b, ?_, ?_⟩
  · -- Proof comment: reuse the same lower cutoff and transport vanishing termwise through `f^*`.
    rw [CochainComplex.isStrictlyGE_iff] at hGE ⊢
    intro i hi
    simpa [CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
      Functor.map_isZero (fStar) (hGE i hi)
  · -- Proof comment: reuse the same upper cutoff and map the zero terms through pullback.
    rw [CochainComplex.isStrictlyLE_iff] at hLE ⊢
    intro i hi
    simpa [CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
      Functor.map_isZero (fStar) (hLE i hi)

/-- Helper for Lemma 20.46.4: a retract of a free sheaf stays in
`SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf` after pullback. -/
private lemma pullbackRetractOfFree
    {M : ModY} {I : Type u} [Finite I]
    (r : Retract M (SheafOfModules.free.{u} I : ModY)) :
    FiniteFreeRetractsX ((fStar).obj M) := by
  -- Proof comment: map the retract through `f^*`, then replace the pulled-back free target by a
  -- canonical free sheaf using the finite-free pullback instance.
  let _ : ((fStar).obj (SheafOfModules.free.{u} I : ModY)).IsFiniteFree := inferInstance
  obtain ⟨J, hJ, ⟨e⟩⟩ := _root_.SheafOfModules.IsFiniteFree.exists_iso_free
    (ℱ := (fStar).obj (SheafOfModules.free.{u} I : ModY))
  let _ : Finite J := hJ
  exact SheafOfModules.finiteFreeRetractModuleProperty_of_retract_free
    ((r.map (fStar)).trans (Retract.ofIso e))

/-- Helper for Lemma 20.46.4: each degree term of a strictly perfect complex stays a retract of a
finite free module after pullback. -/
private lemma pullback_term_finiteFreeRetract
    (E : CochainComplex ModY ℤ)
    (hterm : ∀ i : ℤ,
      ∃ I, Finite I ∧
        Nonempty (Retract (E.X i) (SheafOfModules.free.{u} I : ModY))) :
    ∀ i : ℤ, FiniteFreeRetractsX (((fStarComplex).obj E).X i) := by
  intro i
  -- Proof comment: degreewise retract witnesses from `E` remain retracts of finite free sheaves
  -- after applying the pullback functor.
  rcases hterm i with ⟨I, hI, ⟨r⟩⟩
  let _ : Finite I := hI
  simpa [CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
    (pullbackRetractOfFree (f := f) (M := E.X i) (I := I) r)

/-- Lemma 20.46.4: if `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` is a morphism of ringed spaces and `𝓕^•` is a
strictly perfect complex of `𝒪_Y`-modules, then the pulled-back complex `f^*𝓕^•` is a strictly
perfect complex of `𝒪_X`-modules. -/
@[stacks 09U6]
theorem isStrictlyPerfect_pullback
    (E : CochainComplex ModY ℤ) (hE : IsStrictlyPerfect E) :
    IsStrictlyPerfect ((fStarComplex).obj E) := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: strict support bounds are preserved termwise by the pullback functor.
    exact pullback_bounded (f := f) E hE.bounded
  · -- Proof comment: each term remains a retract of a finite free sheaf after pullback.
    exact pullback_term_finiteFreeRetract (f := f) E (fun i ↦ hE.term_retract_free i)

end

end CochainComplex

end AlgebraicGeometry.RingedSpace
