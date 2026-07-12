import StacksProject_2024.Chap17.Definition_17_25_9
import StacksProject_2024.Chap31.Definition_31_27_4
import StacksProject_2024.Chap31.Definition_31_26_7
import StacksProject_2024.Chap31.Lemma_31_25_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped RingedSpacePicard

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})
variable [IsLocallyNoetherian X] [IsIntegral X]
variable [PrimeDivisorDiscreteValuationRings X]
variable [MonoidalCategory (RingedSpace.Modules X.toLocallyRingedSpace.toRingedSpace)]
variable [SymmetricCategory (RingedSpace.Modules X.toLocallyRingedSpace.toRingedSpace)]

local notation "JX" => Opens.grothendieckTopology X.toTopCat
local notation "ModX" => ringedSiteModuleCategory JX X.𝒪
local notation "IsInvertibleX" =>
  (fun ℒ : ModX ↦ Functor.IsEquivalence (tensorRight ℒ))
local notation "picardReprX" => ringedSitePicardGroup.repr JX X.𝒪
local notation "picardMkX" => ringedSitePicardGroup.mk JX X.𝒪

private instance picardReprX_isInvertible
    (x : Pic(X.toLocallyRingedSpace.toRingedSpace)) :
    IsInvertibleX (picardReprX x) := by
  simpa [picardReprX] using
    (ringedSitePicardGroup.repr_isInvertible JX X.𝒪 x)

/-- A private chosen regular meromorphic section of an invertible `\mathcal O_X`-module on an
integral scheme, obtained from the existence statement of `31.25.4`. -/
private noncomputable abbrev chosenMeromorphicSection
    (ℒ : ModX) [IsInvertibleX ℒ] : X.toLocallyRingedSpace.meromorphicSections ℒ :=
  Classical.choose <| exists_regularMeromorphicSection_of_isIntegral (X := X) ℒ

/- 31.27.5.1: for a locally Noetherian integral scheme `X`, the source displays the canonical map
`\mathrm{Pic}(X) \to \mathrm{Cl}(X)`. In the current Lean project, the Picard side is available
through the Chapter 17 ringed-space notation
`Pic(X.toLocallyRingedSpace.toRingedSpace)`, while the divisor-class-group codomain is the
Chapter 31 notation `Cl(X)`. The comparison homomorphism sends the Picard class of an invertible
sheaf to the Weil divisor class of any regular meromorphic section of that sheaf. -/
noncomputable def meromorphicSectionWeilDivisor
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (data : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s Z) : Div(X) where
  coeff Z :=
    meromorphicSectionWeilDivisorCoeff ℒ s data Z
  locallyFinite_nonzeroCoefficients := by
    simpa using
      locallyFinite_meromorphicSectionWeilDivisorCoeff_ne_zero (X := X) ℒ s data

@[simp] theorem meromorphicSectionWeilDivisor_coeff
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (data : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s Z)
    (Z : PrimeDivisor X) :
    (meromorphicSectionWeilDivisor X ℒ s data).coeff Z =
      meromorphicSectionWeilDivisorCoeff ℒ s data Z :=
  rfl

/-- The divisor class of a meromorphic section, obtained by packaging the coefficient owner of
`31.27.4` into the Chapter 31 quotient `Cl(X)`. -/
noncomputable def meromorphicSectionWeilDivisorClass
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (data : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s Z) : Cl(X) :=
  weilDivisorClassGroupMk X <| meromorphicSectionWeilDivisor X ℒ s data

@[simp] theorem meromorphicSectionWeilDivisorClass_def
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (data : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s Z) :
    meromorphicSectionWeilDivisorClass X ℒ s data =
      weilDivisorClassGroupMk X (meromorphicSectionWeilDivisor X ℒ s data) :=
  rfl

/-- The divisor class of a meromorphic section is independent of the prime-divisor presentation
used to compute it. This is the `Cl(X)`-valued form of the
well-definedness statement from `31.27.4`. -/
theorem meromorphicSectionWeilDivisorClass_eq
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s s' : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (data : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s Z)
    (data' : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s' Z) :
    meromorphicSectionWeilDivisorClass X ℒ s data =
      meromorphicSectionWeilDivisorClass X ℒ s' data' := by
  rcases exists_functionFieldUnit_sub_of_meromorphicSectionWeilDivisorCoeff
      (X := X) ℒ s s' data data' with ⟨f, hf⟩
  have hdiv :
      meromorphicSectionWeilDivisor X ℒ s data =
        meromorphicSectionWeilDivisor X ℒ s' data' + principalWeilDivisor X f := by
    ext Z
    simpa using hf Z
  have hprincipal :
      weilDivisorClassGroupMk X (principalWeilDivisor X f) = 0 := by
    exact (QuotientAddGroup.eq_zero_iff (principalWeilDivisor X f)).2
      (principalWeilDivisor_mem_principalWeilDivisors X f)
  calc
    meromorphicSectionWeilDivisorClass X ℒ s data
        = weilDivisorClassGroupMk X (meromorphicSectionWeilDivisor X ℒ s data) :=
      rfl
    _ = weilDivisorClassGroupMk X
          (meromorphicSectionWeilDivisor X ℒ s' data' + principalWeilDivisor X f) := by
      rw [hdiv]
    _ = weilDivisorClassGroupMk X (meromorphicSectionWeilDivisor X ℒ s' data') +
          weilDivisorClassGroupMk X (principalWeilDivisor X f) := by
      simpa using
        (weilDivisorClassGroupMk X).map_add
          (meromorphicSectionWeilDivisor X ℒ s' data') (principalWeilDivisor X f)
    _ = weilDivisorClassGroupMk X (meromorphicSectionWeilDivisor X ℒ s' data') := by
      rw [hprincipal, add_zero]
    _ = meromorphicSectionWeilDivisorClass X ℒ s' data' := rfl

private instance primeDivisor_genericPointStalk_krullDimLE
    (Z : PrimeDivisor X) :
    Ring.KrullDimLE 1 Z.genericPointStalk := by
  letI := primeDivisorDiscreteValuationRing X Z
  exact Ring.krullDimLE_iff.mpr <| by
    simpa [IsDiscreteValuationRing.ringKrullDim_eq_one Z.genericPointStalk] using
      (show (1 : WithBot ℕ∞) ≤ 1 from le_rfl)

private noncomputable def chosenPrimeDivisorOrderPresentation
    (ℒ : ModX) [IsInvertibleX ℒ] :
    ∀ Z : PrimeDivisor X,
      PrimeDivisorOrderPresentation ℒ (chosenMeromorphicSection X ℒ) Z := fun Z ↦
  { krullDimLE := inferInstance
    quotient := 0 }

/- Internal implementation detail: the public owner of `31.27.5.1` is the comparison map
`Pic(X) → Cl(X)`. The choice-built class of an explicit invertible module stays private, and its
public surface is exposed only through the source-facing companion theorems below. -/
private noncomputable def chosenInvertibleModuleWeilDivisorClass
    (ℒ : ModX) [IsInvertibleX ℒ] :
    Cl(X) :=
  meromorphicSectionWeilDivisorClass X ℒ
    (chosenMeromorphicSection X ℒ) (chosenPrimeDivisorOrderPresentation X ℒ)

/-- The canonical comparison homomorphism `\mathrm{Pic}(X) \to \mathrm{Cl}(X)`. -/
noncomputable def picardToWeilDivisorClassGroup :
    Pic(X.toLocallyRingedSpace.toRingedSpace) →+ Cl(X) where
  toFun x :=
    chosenInvertibleModuleWeilDivisorClass X <|
      picardReprX x
  map_zero' := by
    rw [← ringedSitePicardGroup.mk_unit JX X.𝒪]
    rfl
  map_add' x y := by
    rw [show picardReprX (x + y) =
        picardReprX x ⊗ picardReprX y by
        simpa [picardReprX] using
          (ringedSitePicardGroup.mk_tensor JX X.𝒪
            (picardReprX x) (picardReprX y)).symm]
    rfl

/-- On a Picard class, the comparison map is computed by the divisor class of any explicit
meromorphic section of the canonical representative chosen by the Picard owner. -/
theorem picardToWeilDivisorClassGroup_repr
    (x : Pic(X.toLocallyRingedSpace.toRingedSpace))
    (s : X.toLocallyRingedSpace.meromorphicSections (picardReprX x))
    (data : ∀ Z : PrimeDivisor X,
      PrimeDivisorOrderPresentation (picardReprX x) s Z) :
    picardToWeilDivisorClassGroup X x =
      meromorphicSectionWeilDivisorClass X
        (picardReprX x) s data := by
  let s₀ := chosenMeromorphicSection X (picardReprX x)
  let data₀ := chosenPrimeDivisorOrderPresentation X (picardReprX x)
  change meromorphicSectionWeilDivisorClass X
      (picardReprX x) s₀ data₀ =
    meromorphicSectionWeilDivisorClass X
      (picardReprX x) s data
  exact meromorphicSectionWeilDivisorClass_eq X
    (picardReprX x) s₀ s data₀ data

/-- On an explicit invertible module, the comparison map agrees with the divisor class of any
meromorphic section equipped with prime-divisor local-presentation data. -/
theorem picardToWeilDivisorClassGroup_mk
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (data : ∀ Z : PrimeDivisor X, PrimeDivisorOrderPresentation ℒ s Z) :
    picardToWeilDivisorClassGroup X (picardMkX ℒ) =
      meromorphicSectionWeilDivisorClass X ℒ s data := by
  exact meromorphicSectionWeilDivisorClass_eq X
    (picardReprX (picardMkX ℒ))
    (chosenMeromorphicSection X (picardReprX (picardMkX ℒ))) s
    (chosenPrimeDivisorOrderPresentation X (picardReprX (picardMkX ℒ))) data

end AlgebraicGeometry.Scheme
