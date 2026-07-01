import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import stacks_project.Chap15.Definition_15_65_1
import stacks_project.Chap15.Lemma_15_67_4
import stacks_project.Chap15.Lemma_15_60_3
import stacks_project.Chap15.Lemma_15_77_1
import stacks_project.Chap15.Definition_15_75_1

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling:
- primary domain: localization of pseudo-coherent derived objects, truncation triangles in the
  standard `t`-structure, and control of the localized upper truncation by the chapter owners for
  perfectness, tor-amplitude, and compatible biproduct splittings;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `HasTorAmplitudeGE`,
  `derivedTensorWithAlgebra`,
  `derivedTensorWithAlgebraHomologyComparison`,
  `t.triangleLEGE_distinguished`,
  `existsUnique_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge`;
- best owner abstraction: the source-facing localization theorem should state its conclusions
  directly in terms of the owner truncation triangle for
  `K ⊗[R]^L[Localization.Away f]`, together with the canonical owners
  `DerivedCategory.IsPerfect`, `HasTorAmplitudeGE`, and
  `derivedTensorWithAlgebraHomologyComparison`, not via a second public package or local wrapper
  alias;
- primitive data: the localized object `K ⊗_R^{\mathbf L} R_f`, the canonical truncation triangle
  from `t.triangleLEGE_distinguished`, and its truncation maps;
- derived API: perfectness and tor-amplitude of `τ_{\ge i + 1}`, together with the
  unique compatible splitting of the localized truncation triangle.

Source/core/bridge triage:
- `source-facing`: the existential localization theorem below;
- `core/canonical`: `DerivedCategory.IsPerfect`, `HasTorAmplitudeGE`, and
  `derivedTensorWithAlgebraHomologyComparison`, with the truncation triangle owned by
  `t.triangleLEGE_distinguished`;
- `bridge/view`: the residue-field specialization of
  `derivedTensorWithAlgebraHomologyComparison`, together with the native compatibility equations
  on the canonical truncation maps; the splitting itself should stay in the owner-level `∃! e`
  form from Lemma `15.77.1`.
-/

section

variable (𝔭 : PrimeSpectrum R)

local notation "κ" => 𝔭.asIdeal.ResidueField

-- Proof sketch: apply the Stacks argument after replacing `K` by a bounded-above finite-free
-- representative supplied by pseudo-coherence. The surjectivity hypothesis yields a basis of the
-- middle cohomology after tensoring with `κ(𝔭)` that can be lifted to cycles. Use Algebra,
-- Lemma `10.79.4`, to localize away from some `f ∉ 𝔭` so that the degree-`i` differential splits
-- off a finite projective cokernel, which makes `τ_{\ge i + 1}` perfect with tor-amplitude in
-- `[i + 1, ∞]`. Then apply the canonical truncation triangle together with Lemma `15.77.1` to
-- obtain the unique compatible biproduct decomposition of the localized truncation triangle,
-- while keeping any auxiliary projective-amplitude bound internal to that construction.
/-- Lemma 15.77.2: let `R` be a commutative ring, let `𝔭` be a prime ideal of `R` represented by
`𝔭 : PrimeSpectrum R`, and let `K^•` be a pseudo-coherent object of `D(R)`. Assume the
canonical base-change map
`H^i(K^•) ⊗_R κ(𝔭) ⟶ H^i(K^• \otimes_R^{\mathbf L} κ(𝔭))`
is surjective in degree `i`. Then there exists `f ∈ R` with `f ∉ 𝔭` such that the upper
truncation `τ_{\ge i + 1}(K^• \otimes_R^{\mathbf L} R_f)` is perfect and has tor-amplitude in
`[i + 1, ∞]`; moreover, the localized truncation triangle admits a unique splitting compatible
with the standard truncation maps. -/
theorem exists_localizationAway_split_of_residueField_homology_surjective
    (K : DMod) (i : ℤ) (hK : K.IsPseudoCoherent)
    (hsurj : Epi (derivedTensorWithAlgebraHomologyComparison κ K i)) :
    ∃ f : R, f ∉ 𝔭.asIdeal ∧
      ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f])).IsPerfect ∧
        HasTorAmplitudeGE
          ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]))
          (i + 1) ∧
          ∃! e :
              K ⊗[R]^L[Localization.Away f] ≅
                (t.truncLE i).obj (K ⊗[R]^L[Localization.Away f]) ⊞
                  (t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]),
            ((t.truncLEι i).app (K ⊗[R]^L[Localization.Away f])) ≫ e.hom = biprod.inl ∧
              e.hom ≫ biprod.snd =
                ((t.truncGEπ (i + 1)).app (K ⊗[R]^L[Localization.Away f])) := sorry

end

end

end CategoryTheory
