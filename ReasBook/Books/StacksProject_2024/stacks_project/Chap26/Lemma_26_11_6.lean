import Mathlib
import StacksProject_2024.Chap26.Definition_26_5_2
import StacksProject_2024.Chap26.Lemma_26_11_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

/- Source/core/bridge triage for Lemma 26.11.6:
- `source-facing`: an affine open `V` admits a finite standard-open cover refining a given affine
  open cover `𝒰`;
- `core/canonical`: `PrimeSpectrum.StandardOpenCover (Γ(X, V))` is the canonical owner of the
  finite standard-open cover of the affine scheme `V`;
- `bridge/view`: the scheme-side members of that cover are the affine basic opens
  `X.affineBasicOpen (W.generator i)`, together with the refinement equalities showing that each is
  also a standard open in some member of `𝒰`. -/

namespace PrimeSpectrum.StandardOpenCover

/-- A standard open cover of an affine open `V` refines an affine open cover `𝒰` of `X` if each
member of the standard open cover is also a basic open in some member of `𝒰`. -/
def RefinesAffineOpenCover
    {X : AlgebraicGeometry.Scheme} {V : X.affineOpens}
    (W : PrimeSpectrum.StandardOpenCoverOf (1 : Γ(X, V)))
    (𝒰 : X.AffineOpenCover) : Prop :=
  ∃ u : W.index → 𝒰.I₀,
    ∀ i, ∃ g : Γ(X, (𝒰.openCover.f (u i)).opensRange),
      (X.affineBasicOpen (W.generator i) : X.Opens) = X.basicOpen g

/-- The affine basic opens defined by a standard open cover of `Γ(X, V)` cover the affine open
subset `V`. This is the scheme-side expression of `W.iSup_eq_top`. -/
theorem iSup_affineBasicOpen_eq
    {X : AlgebraicGeometry.Scheme} {V : X.affineOpens}
    (W : PrimeSpectrum.StandardOpenCoverOf (1 : Γ(X, V))) :
    (⨆ i, (X.affineBasicOpen (W.generator i) : X.Opens)) = V := by
  have himage :
      (⨆ i, X.basicOpen (W.generator i)) =
        V.2.fromSpec ''ᵁ (⨆ i, PrimeSpectrum.basicOpen (W.generator i)) := by
    calc
      (⨆ i, X.basicOpen (W.generator i))
          = ⨆ i, V.2.fromSpec ''ᵁ PrimeSpectrum.basicOpen (W.generator i) := by
            ext x
            simp [V.2.fromSpec_image_basicOpen]
      _ = V.2.fromSpec ''ᵁ (⨆ i, PrimeSpectrum.basicOpen (W.generator i)) := by
        rw [Scheme.Hom.image_iSup]
  have hcover :
      V.2.fromSpec ''ᵁ (⨆ i, PrimeSpectrum.basicOpen (W.generator i)) = V := by
    have htop :
        V.2.fromSpec ''ᵁ (⨆ i, PrimeSpectrum.basicOpen (W.generator i)) =
          V.2.fromSpec ''ᵁ (⊤ : TopologicalSpace.Opens (PrimeSpectrum (Γ(X, V)))) := by
      have htop' :
          V.2.fromSpec ''ᵁ
              (⨆ i, (W i : TopologicalSpace.Opens (PrimeSpectrum (Γ(X, V))))) =
            V.2.fromSpec ''ᵁ (⊤ : TopologicalSpace.Opens (PrimeSpectrum (Γ(X, V)))) := by
        exact
          congrArg
            (fun U : TopologicalSpace.Opens (PrimeSpectrum (Γ(X, V))) ↦ V.2.fromSpec ''ᵁ U)
            (PrimeSpectrum.StandardOpenCover.iSup_eq_top W)
      simpa [PrimeSpectrum.StandardOpenCoverOf.coeFn_apply] using htop'
    exact htop.trans <| V.2.fromSpec.image_top_eq_opensRange.trans <| by
      simpa using V.2.opensRange_fromSpec
  calc
    (⨆ i, (X.affineBasicOpen (W.generator i) : X.Opens))
        = ⨆ i, X.basicOpen (W.generator i) := by
          simp [Scheme.affineBasicOpen_coe]
    _ = V.2.fromSpec ''ᵁ (⨆ i, PrimeSpectrum.basicOpen (W.generator i)) := himage
    _ = V := hcover

end PrimeSpectrum.StandardOpenCover

namespace AlgebraicGeometry.Scheme

/-- Lemma 26.11.6: for an affine open cover `𝒰` of a scheme `X` and an affine open subset `V`,
there is a finite standard open cover of `V` whose members are each also a standard open in one of
the members of `𝒰`. The fact that these affine basic opens cover `V` itself is the canonical
companion theorem `PrimeSpectrum.StandardOpenCover.iSup_affineBasicOpen_eq`. -/
@[stacks 01IX]
theorem exists_standardOpenCover_refining_affineOpenCover
    {X : Scheme} (𝒰 : X.AffineOpenCover) (V : X.affineOpens) :
    ∃ W : PrimeSpectrum.StandardOpenCoverOf (1 : Γ(X, V)),
      PrimeSpectrum.StandardOpenCover.RefinesAffineOpenCover W 𝒰 := sorry

end AlgebraicGeometry.Scheme
