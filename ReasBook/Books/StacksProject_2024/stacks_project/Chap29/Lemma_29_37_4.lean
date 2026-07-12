import StacksProject_2024.Chap24.Definition_24_3_1
import StacksProject_2024.Chap29.Definition_29_37_1
import StacksProject_2024.Chap29.RelativeProjPresentation

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the canonical morphism predicates `QuasiCompact`,
  `QuasiSeparated`, `IsOpenImmersion`, and `IsImmersion`.
- Local project inspection found the Chapter 29 relative-ampleness owner
  `RelativelyAmple`, the Chapter 28 absolute owner `Scheme.Modules.IsAmple`, the cover
  pattern using `TopologicalSpace.IsOpenCover`, and the partial relative-`Proj` presentation
  owner `Scheme.Hom.RelativeProjPresentation`.
- The Stacks tag evidence is consistent: item tag `01VJ` and source URL
  `https://stacks.math.columbia.edu/tag/01VJ`.
-/

/-- Restrict an `\mathcal O_X`-module to the preimage of an open subscheme of the base. -/
abbrev restrictToBaseOpenPreimage (V : S.Opens) : (f ⁻¹ᵁ V).toScheme.Modules :=
  restrictToBasePreimage f L V

/-- The open-cover local form of relative ampleness for an invertible module. -/
@[stacks 01VJ]
class RelativelyAmpleOnBaseOpenCover [Scheme.Modules.Invertible L] : Prop where
  /-- There is an open cover of the base on which the restricted module is relatively ample. -/
  exists_cover :
    ∃ (ι : Type u) (V : ι → S.Opens), TopologicalSpace.IsOpenCover V ∧
      ∀ i : ι,
        RelativelyAmple (f ∣_ V i) (restrictToBaseOpenPreimage f L (V i))

/-- The affine-open-cover local form of relative ampleness for an invertible module. -/
@[stacks 01VJ]
class AmpleOnAffineBaseOpenCover [Scheme.Modules.Invertible L] : Prop where
  /-- There is an affine open cover of the base on which the restricted module is ample. -/
  exists_cover :
    ∃ (ι : Type u) (V : ι → S.Opens), TopologicalSpace.IsOpenCover V ∧
      (∀ i : ι, IsAffineOpen (V i)) ∧
        ∀ i : ι,
          ∃ hInv : Scheme.Modules.Invertible (restrictToBaseOpenPreimage f L (V i)),
            @Scheme.Modules.IsAmple (f ⁻¹ᵁ V i).toScheme
              (restrictToBaseOpenPreimage f L (V i)) hInv

/-- A relative Proj presentation attached to a graded algebra map into the nonnegative tensor
powers of an invertible module. -/
@[stacks 01VJ]
structure RelativelyAmpleProjPresentation [Scheme.Modules.Invertible L] where
  /-- The target quasi-coherent graded algebra sheaf on the base. -/
  algebra : GradedAlgebraSheaf.{u, u} S.sheaf
  /-- Every graded piece of the algebra is quasi-coherent. -/
  algebra_isQuasicoherent : ∀ n : ℤ, (algebra n).IsQuasicoherent
  /-- The relative Proj object associated to the graded algebra. -/
  proj : Scheme.{u}
  /-- The structure morphism of the relative Proj. -/
  structureMap : proj ⟶ S
  /-- The local relative Proj presentation API for the structure morphism. -/
  projPresentation : Scheme.Hom.RelativeProjPresentation structureMap
  /-- The morphism `r_{\mathcal L,\psi} : X ⟶ Proj_S(\mathcal A)`. -/
  comparison : X ⟶ proj
  /-- The comparison morphism lies over the original morphism `f`. -/
  comparison_over_base : comparison ≫ structureMap = f
  /-- The open subset `U(\psi)` of `X` attached to the graded algebra map. -/
  domain : X.Opens
  /-- The degreewise map `\psi : f^*\mathcal A \to \oplus_d L^{\otimes d}`.  The degree `d`
  component lands in the chosen tensor power of `L`. -/
  psi :
    ∀ d : ℕ,
      (Scheme.Modules.pullback f).obj (algebra (Int.ofNat d)) ⟶
        (inferInstance : Scheme.Modules.Invertible L) d

/-- The relative Proj presentation has quasi-coherent graded pieces. -/
instance [Scheme.Modules.Invertible L] (P : RelativelyAmpleProjPresentation f L) (n : ℤ) :
    (P.algebra n).IsQuasicoherent :=
  P.algebra_isQuasicoherent n

/-- The associated relative Proj comparison is an open immersion. -/
@[stacks 01VJ]
class HasOpenImmersionRelativelyAmpleProjPresentation [Scheme.Modules.Invertible L] : Prop where
  /-- There exists a presentation whose associated comparison map is an open immersion and whose
  open subset `U(\psi)` is all of `X`. -/
  exists_presentation :
    ∃ presentation : RelativelyAmpleProjPresentation f L,
      presentation.domain = ⊤ ∧ IsOpenImmersion presentation.comparison

/-- The canonical pushforward graded algebra presentation from
`f_*(\bigoplus_{d \ge 0} L^{\otimes d})` has an open-immersion comparison. -/
@[stacks 01VJ]
class HasCanonicalOpenImmersionRelativelyAmpleProjPresentation [Scheme.Modules.Invertible L] :
    Prop extends QuasiSeparated f where
  /-- There exists the presentation attached to the canonical pushforward graded algebra and the
  adjunction map, with open-immersion comparison. -/
  exists_presentation :
    ∃ presentation : RelativelyAmpleProjPresentation f L,
      presentation.domain = ⊤ ∧
        ∃ hcanon : ∀ d : ℕ,
            presentation.algebra (Int.ofNat d) =
              (Scheme.Modules.pushforward f).obj ((inferInstance : Scheme.Modules.Invertible L) d),
          (∀ d : ℕ,
            presentation.psi d =
              (Scheme.Modules.pullback f).map (eqToHom (hcanon d)) ≫
                (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app
                  ((inferInstance : Scheme.Modules.Invertible L) d)) ∧
            IsOpenImmersion presentation.comparison

/-- The associated relative Proj comparison is an immersion. -/
@[stacks 01VJ]
class HasImmersionRelativelyAmpleProjPresentation [Scheme.Modules.Invertible L] : Prop where
  /-- There exists a presentation whose associated comparison map is an immersion and whose open
  subset `U(\psi)` is all of `X`. -/
  exists_presentation :
    ∃ presentation : RelativelyAmpleProjPresentation f L,
      presentation.domain = ⊤ ∧ IsImmersion presentation.comparison

/-- Lemma 29.37.4: for a quasi-compact morphism of schemes and an invertible sheaf on the source,
the six standard criteria for relative ampleness are equivalent: global relative ampleness, local
relative ampleness on an open cover of the base, ampleness on an affine open cover of the base, the
relative `Proj` open-immersion presentation, the canonical pushforward relative `Proj`
open-immersion presentation with `f` quasi-separated, and the relative `Proj` immersion
presentation. -/
@[stacks 01VJ]
theorem relativelyAmple_tfae
    [QuasiCompact f] [Scheme.Modules.Invertible L] :
    List.TFAE [
      RelativelyAmple f L,
      RelativelyAmpleOnBaseOpenCover f L,
      AmpleOnAffineBaseOpenCover f L,
      HasOpenImmersionRelativelyAmpleProjPresentation f L,
      HasCanonicalOpenImmersionRelativelyAmpleProjPresentation f L,
      HasImmersionRelativelyAmpleProjPresentation f L] := sorry

end

end AlgebraicGeometry
