import StacksProject_2024.Chap31.ClosedImmersionIdealSubobject
import StacksProject_2024.Chap31.Definition_31_14_1

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: Chapter 31 keeps the source-facing divisor owner `D : S.IdealSheafData`, with
-- pullback of closed subschemes canonically `D.comap f`. The associated sheaf and canonical
-- section are already owned by `effectiveCartierDivisorAssociatedSheaf` and
-- `effectiveCartierDivisorCanonicalSection` on the closed-immersion ideal subobject, so the
-- public hypotheses here ask directly for the invertibility data those owners consume.

variable {S S' : Scheme.{u}}

local notation "ModS" => Scheme.Modules S
local notation "ModS'" => Scheme.Modules S'
local notation "𝒪S'" => (SheafOfModules.unit S'.ringCatSheaf : ModS')

/-- The Chapter 31 effective-Cartier ideal condition on an ideal-sheaf subobject. -/
local abbrev EffectiveCartierIdeal
    {X : Scheme.{u}}
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : Scheme.Modules X)) : Prop :=
  Functor.IsEquivalence (tensorRight (Subobject.underlying.obj I))

/-- The canonical ideal subobject attached to an ideal-sheaf divisor datum. -/
local abbrev divisorIdealSubobject {X : Scheme.{u}} (D : X.IdealSheafData) :
    Subobject (SheafOfModules.unit X.ringCatSheaf : Scheme.Modules X) :=
  closedImmersionIdealSubobject D.subschemeι

private instance instFactEffectiveCartierIdeal_divisorIdealSubobject
    {X : Scheme.{u}} (D : X.IdealSheafData) [D.IsEffectiveCartierDivisor] :
    Fact (EffectiveCartierIdeal (divisorIdealSubobject D)) :=
  ⟨show Functor.IsEquivalence (tensorRight (RingedSpace.closedImmersionIdealSheaf D.subschemeι.toShHom))
      from AlgebraicGeometry.IsEffectiveCartierDivisor.toIsEquivalence D.subschemeι⟩

/-- The scheme-level specialization of the canonical pullback of a global section. -/
noncomputable abbrev pullbackSections (f : S' ⟶ S) {ℒ : ModS} (s : ℒ.sections) :
    ((Scheme.Modules.pullback f).obj ℒ).sections :=
  AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackSections f s

/-- Lemma 31.14.5 (1): if `D` is an effective Cartier divisor on `S`, then for any morphism
`f : S' ⟶ S`, the pullback of `\mathcal O_S(D)` agrees with the associated invertible sheaf of
the pullback divisor `f^*D = D.comap f`, represented by its canonical closed-immersion ideal
subobject. -/
theorem pullbackAssociatedSheaf_iso
    (f : S' ⟶ S) (D : S.IdealSheafData)
    [D.IsEffectiveCartierDivisor] [(D.comap f).IsEffectiveCartierDivisor] :
    (Scheme.Modules.pullback f).obj
        (effectiveCartierDivisorAssociatedSheaf (divisorIdealSubobject D)) ≅
      effectiveCartierDivisorAssociatedSheaf (divisorIdealSubobject (D.comap f)) := by
  sorry

/-- Lemma 31.14.5 (2): under the pullback identification of associated invertible sheaves from
`pullbackAssociatedSheaf_iso`, the canonical section `1_D` pulls back to the canonical section of
the pullback divisor `f^*D`. -/
theorem pullbackCanonicalSection_eq
    (f : S' ⟶ S) (D : S.IdealSheafData)
    [D.IsEffectiveCartierDivisor] [(D.comap f).IsEffectiveCartierDivisor] :
    SheafOfModules.sectionsMap
        (pullbackAssociatedSheaf_iso f D).hom
        (pullbackSections f
          (effectiveCartierDivisorCanonicalSection (divisorIdealSubobject D))) =
      effectiveCartierDivisorCanonicalSection (divisorIdealSubobject (D.comap f)) := by
  sorry

/-- Companion to `pullbackAssociatedSheaf_iso`: the pullback identification can be transported
along any equality identifying the canonical pullback-divisor ideal subobject with another chosen
effective-Cartier representative. -/
theorem pullbackAssociatedSheaf_iso_of_eq
    (f : S' ⟶ S) (D : S.IdealSheafData)
    [D.IsEffectiveCartierDivisor] [(D.comap f).IsEffectiveCartierDivisor]
    (I' : Subobject 𝒪S')
    [Fact (EffectiveCartierIdeal I')]
    (hI' : divisorIdealSubobject (D.comap f) = I') :
    (Scheme.Modules.pullback f).obj
        (effectiveCartierDivisorAssociatedSheaf (divisorIdealSubobject D)) ≅
      effectiveCartierDivisorAssociatedSheaf I' := by
  simpa [hI'] using pullbackAssociatedSheaf_iso f D

/-- Companion to `pullbackCanonicalSection_eq`: after transporting the associated-sheaf
identification along an equality of ideal-sheaf representatives, the pulled-back canonical section
is the canonical section of that representative. -/
theorem pullbackCanonicalSection_eq_of_eq
    (f : S' ⟶ S) (D : S.IdealSheafData)
    [D.IsEffectiveCartierDivisor] [(D.comap f).IsEffectiveCartierDivisor]
    (I' : Subobject 𝒪S')
    [Fact (EffectiveCartierIdeal I')]
    (hI' : divisorIdealSubobject (D.comap f) = I') :
    SheafOfModules.sectionsMap
        (pullbackAssociatedSheaf_iso_of_eq f D I' hI').hom
        (pullbackSections f
          (effectiveCartierDivisorCanonicalSection (divisorIdealSubobject D))) =
      effectiveCartierDivisorCanonicalSection I' := by
  simpa [hI'] using pullbackCanonicalSection_eq f D

end AlgebraicGeometry.Scheme
