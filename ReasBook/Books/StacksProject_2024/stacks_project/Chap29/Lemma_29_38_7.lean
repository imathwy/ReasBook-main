import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_38_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall / owner check:
-- `lean_leansearch` surfaced the canonical module-adjunction owner
-- `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` and generic immersion /
-- projective-spectrum API.
-- Local Chapter 29 precedent already fixes the source-facing owner for condition (1) as
-- `RelativelyVeryAmple` together with `RelativelyVeryAmplePresentation`.
-- The current checkout still does not expose a stable source-facing owner for the relative-`Proj`
-- morphism `r_{L, ψ}` or for the graded generation-in-degree-one clause, so the file records the
-- source-proof directions that can be stated faithfully on the existing local surfaces.

section

variable {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}

/-- The local-on-the-base form of relative very ampleness: after pulling `L` back to each member
of some open cover of `S`, the restricted morphism carries a relatively very ample invertible
module. -/
@[stacks 01VR]
class RelativelyVeryAmpleOpenCover (f : X ⟶ S) (L : X.Modules)
    [Scheme.Modules.Invertible L] : Prop where
  /-- There is an open cover of the base on whose pullback pieces the restricted module is
  relatively very ample. -/
  exists_cover :
    ∃ (ι : Type u) (V : ι → S.Opens), TopologicalSpace.IsOpenCover V ∧
      ∀ i : ι,
        ∃ hInv : Scheme.Modules.Invertible (restrictToBasePreimage f L (V i)),
          @RelativelyVeryAmple (f ⁻¹ᵁ V i).toScheme (V i).toScheme
            (f ∣_ V i) (restrictToBasePreimage f L (V i)) hInv

/-- The canonical counit map `f^* f_* L ⟶ L` of the pullback/pushforward adjunction. -/
abbrev canonicalPushforwardCounit
    (f : X ⟶ S) (L : X.Modules) :
    ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward f).obj L)) ⟶ L :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app L

/-- The pushforward-presentation form of relative very ampleness: `f` is quasi-separated, the
canonical counit `f^* f_* L ⟶ L` is epic, and `L` is exhibited by an immersion into a projective
bundle attached to the pushforward module `f_* L`. -/
@[stacks 01VR]
class CanonicalPushforwardRelativelyVeryAmplePresentation
    (f : X ⟶ S) (L : X.Modules) [Scheme.Modules.Invertible L] : Prop where
  /-- The source clause `f` is quasi-separated. -/
  quasiSeparated : QuasiSeparated f
  /-- The canonical map `f^* f_* L ⟶ L` is surjective, recorded categorically as an epimorphism. -/
  counit_epi : Epi (canonicalPushforwardCounit f L)
  /-- The associated map to the projective bundle of `f_* L` is an immersion, recorded through the
  existing projective-bundle presentation owner. -/
  exists_presentation :
    ∃ (P : Scheme.{u}) (π : P ⟶ S)
      (hπ : Scheme.IsProjectiveBundle π ((Scheme.Modules.pushforward f).obj L)) (i : X ⟶ P),
      RelativelyVeryAmplePresentation f L π ((Scheme.Modules.pushforward f).obj L) hπ i

/-- Lemma 29.38.7 (1): if `\mathcal L` is relatively very ample on `X/S`, then there exists an
open cover of `S` such that the pullback of `\mathcal L` to each preimage piece is relatively very
ample for the restricted morphism. -/
@[stacks 01VR]
theorem relativelyVeryAmpleOpenCover_of_relativelyVeryAmple
    [Scheme.Modules.Invertible L] (hL : RelativelyVeryAmple f L) :
    RelativelyVeryAmpleOpenCover f L := sorry

/-- Lemma 29.38.7 (2): assume `f : X ⟶ S` is quasi-compact. If there exists an open cover of `S`
such that the pullback of `\mathcal L` to each preimage piece is relatively very ample for the
restricted morphism, then `f` is quasi-separated, the canonical map `f^* f_* \mathcal L ⟶
\mathcal L` is surjective, and the associated map to the projective bundle of `f_* \mathcal L`
is an immersion. -/
@[stacks 01VR]
theorem canonicalPushforwardPresentation_of_relativelyVeryAmpleOpenCover
    [QuasiCompact f] [Scheme.Modules.Invertible L]
    (hL : RelativelyVeryAmpleOpenCover f L) :
    CanonicalPushforwardRelativelyVeryAmplePresentation f L := sorry

/-- Lemma 29.38.7 (3): assume `f : X ⟶ S` is quasi-compact. If `f` is quasi-separated, the
canonical map `f^* f_* \mathcal L ⟶ \mathcal L` is surjective, and the associated map to the
projective bundle of `f_* \mathcal L` is an immersion, then `\mathcal L` is relatively very ample
on `X/S`. -/
@[stacks 01VR]
theorem relativelyVeryAmple_of_canonicalPushforwardPresentation
    [QuasiCompact f] [Scheme.Modules.Invertible L]
    (hL : CanonicalPushforwardRelativelyVeryAmplePresentation f L) :
    RelativelyVeryAmple f L := sorry

end

/- Lemma 29.38.7 also contains the graded-algebra clause involving a quasi-coherent graded
`\mathcal O_S`-algebra generated in degree `1` and the associated morphism
`r_{\mathcal L, \psi} : X ⟶ \underline{\mathrm{Proj}}_S(\mathcal A)`. The current checkout
already exposes partial owners such as `GradedAlgebraSheaf` and `Scheme.Hom.RelativeProjPresentation`,
but it still lacks a stable source-facing owner for that generation-in-degree-one hypothesis and
for the associated relative-`Proj` immersion. The omitted `(4) → (3) → (1)` route should be added
against that future owner, not hidden behind a dummy wrapper. -/

end AlgebraicGeometry
