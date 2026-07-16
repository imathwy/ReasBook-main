import Mathlib
import StacksProject_2024.stacks_project.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.stacks_project.Chap29.Lemma_29_32_15

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry

variable {Z X S : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced only generic immersion API. Local Chapter 29
-- precedent fixes the differential sheaves as `Ω[f.toShHom]`, the conormal sheaf as
-- `immersionConormalSheaf`, and local split exactness via `RingedSpace.moduleStalkHom` and
-- `ShortComplex.Splitting`.

/-- A morphism `i : Z ⟶ X` has a left inverse over `S` with respect to `f : X ⟶ S` if it admits a
retraction `r : X ⟶ Z` whose composite with the structural map of `Z` over `S` is `f`. -/
def HasLeftInverseOver (i : Z ⟶ X) (f : X ⟶ S) : Prop :=
  ∃ r : X ⟶ Z, i ≫ r = 𝟙 Z ∧ r ≫ i ≫ f = f

/-- Companion expansion for `HasLeftInverseOver`. -/
theorem hasLeftInverseOver_iff (i : Z ⟶ X) (f : X ⟶ S) :
    HasLeftInverseOver i f ↔ ∃ r : X ⟶ Z, i ≫ r = 𝟙 Z ∧ r ≫ i ≫ f = f := sorry

/-- The source-local form of admitting a left inverse: around every point of `Z`, the restriction
of `i` to an open neighbourhood of its image has a left inverse over `S`. -/
def LocallyHasLeftInverseOver (i : Z ⟶ X) (f : X ⟶ S) : Prop :=
  ∀ z : Z, ∃ U : X.Opens, i.base z ∈ U ∧ HasLeftInverseOver (i ∣_ U) (U.ι ≫ f)

/-- Companion expansion for `LocallyHasLeftInverseOver`. -/
theorem locallyHasLeftInverseOver_iff (i : Z ⟶ X) (f : X ⟶ S) :
    LocallyHasLeftInverseOver i f ↔
      ∀ z : Z, ∃ U : X.Opens, i.base z ∈ U ∧
        HasLeftInverseOver (i ∣_ U) (U.ι ≫ f) := sorry

section

variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) CommRingCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Z) CommRingCat.{u})]

/-- The conormal-relative-differentials sequence
`0 ⟶ C_{Z/X} ⟶ i^* Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0` is exact and stalkwise split. The two maps are the
comparison maps of Lemma 29.32.15, represented in the current project by existential comparison
morphisms. -/
def ConormalRelativeDifferentialsSequenceExactStalkwiseSplit
    (i : Z ⟶ X) [IsImmersion i] (f : X ⟶ S) : Prop :=
  ∃ δ : immersionConormalSheaf i ⟶
      (RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom],
    ∃ ψ : (RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom] ⟶
        Ω[(i ≫ f).toShHom],
      ∃ hδψ : δ ≫ ψ = 0,
        (ShortComplex.mk δ ψ hδψ).Exact ∧ Epi ψ ∧
          ∀ z : Z,
            ∃ hz : RingedSpace.moduleStalkHom z δ ≫ RingedSpace.moduleStalkHom z ψ = 0,
              Nonempty
                ((ShortComplex.mk
                  (RingedSpace.moduleStalkHom z δ)
                  (RingedSpace.moduleStalkHom z ψ)
                  hz).Splitting)

/-- Companion expansion for `ConormalRelativeDifferentialsSequenceExactStalkwiseSplit`. -/
theorem conormalRelativeDifferentialsSequenceExactStalkwiseSplit_iff
    (i : Z ⟶ X) [IsImmersion i] (f : X ⟶ S) :
    ConormalRelativeDifferentialsSequenceExactStalkwiseSplit i f ↔
      ∃ δ : immersionConormalSheaf i ⟶
          (RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom],
        ∃ ψ : (RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom] ⟶
            Ω[(i ≫ f).toShHom],
          ∃ hδψ : δ ≫ ψ = 0,
            (ShortComplex.mk δ ψ hδψ).Exact ∧ Epi ψ ∧
              ∀ z : Z,
                ∃ hz : RingedSpace.moduleStalkHom z δ ≫ RingedSpace.moduleStalkHom z ψ = 0,
                  Nonempty
                    ((ShortComplex.mk
                      (RingedSpace.moduleStalkHom z δ)
                      (RingedSpace.moduleStalkHom z ψ)
                      hz).Splitting) := sorry

/-- Lemma 29.32.16: let `i : Z ⟶ X` be an immersion of schemes over `S`, and assume `i`
locally has a left inverse. Then the canonical sequence
`0 ⟶ C_{Z/X} ⟶ i^* Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0` of Lemma 29.32.15 is locally split exact. -/
@[stacks 0474]
theorem conormalRelativeDifferentialsSequenceExactStalkwiseSplit_of_locallyHasLeftInverse
    (i : Z ⟶ X) [IsImmersion i] (f : X ⟶ S)
    (hleft : LocallyHasLeftInverseOver i f) :
    ConormalRelativeDifferentialsSequenceExactStalkwiseSplit i f := sorry

end

section

variable {X S : Scheme.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology ↥S) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥S) CommRingCat.{u}]
variable [(Opens.grothendieckTopology ↥S).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology ↥S).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥S) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥S).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥S) CommRingCat.{u})]

/-- If `s : S ⟶ X` is a section of `f : X ⟶ S`, then the conormal-to-pulled-back-differentials
map `C_{S/X} ⟶ s^* Ω_{X/S}` induced by `d_{X/S}` is an isomorphism. In the current project this
is stated as the existence of the canonical left comparison map of Lemma 29.32.15 with `IsIso`. -/
@[stacks 0474]
theorem exists_isIso_conormalToPullbackDifferentials_of_section
    (f : X ⟶ S) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) :
    ∃ δ : immersionConormalSheaf s ⟶
        (RingedSpace.Hom.pullback s.toShHom).obj Ω[f.toShHom],
      ∃ ψ : (RingedSpace.Hom.pullback s.toShHom).obj Ω[f.toShHom] ⟶
          Ω[(s ≫ f).toShHom],
        ∃ hδψ : δ ≫ ψ = 0, (ShortComplex.mk δ ψ hδψ).ShortExact ∧ IsIso δ := sorry

end

end AlgebraicGeometry
