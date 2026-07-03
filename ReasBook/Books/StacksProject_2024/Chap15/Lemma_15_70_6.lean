import Mathlib
import StacksProject_2024.Chap13.Definition_13_11_3
import StacksProject_2024.Chap13.Definition_13_27_1
import StacksProject_2024.Chap15.Definition_15_70_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open scoped CategoryTheory
open scoped DerivedExt

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

local notation "Mod" => ModuleCat R
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/- Domain-style sampling:
- primary domain: finite injective dimension for bounded-below derived `R`-complexes, tested by
  vanishing of derived `Ext` groups from ideal quotients;
- sampled owner declarations:
  `D⁺(Mod)`,
  `HasFiniteInjectiveDimension`,
  `injectiveAmplitudeIn_ext_vanishing_tfae`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.isGE_iff`;
- best owner abstraction: the source-facing owner here remains
  `HasFiniteInjectiveDimension K.obj`, while the bounded-below hypothesis should be carried by the
  Chapter `13` owner `K : D⁺(Mod)` rather than by the surrogate datum
  `∃ n : ℤ, K.IsGE n`;
- primitive vs. derived:
  primitive data are the ideal `I`, the bounded-below derived object `K : D⁺(Mod)`, and
  finite cohomology modules;
  derived API is the eventual vanishing of `Ext^i((single₀).obj (R ⧸ J), K)` for ideals
  `J ⊇ I`, with `ShiftedHom` kept only as the core owner behind the Chapter `13` notation;
- source/core/bridge triage:
  `source-facing`: `finiteInjectiveDimension_iff_exists_ext_vanishing_ideal_quotients_ge`;
  `core/canonical`: `HasFiniteInjectiveDimension`, `DerivedCategory.IsGE`, and `ShiftedHom`;
  `bridge/view`: the cohomology-vanishing description of `D⁺(R)`, which is demoted in favor of
    the owner-level bounded-below hypothesis.
-/

-- Proof sketch: the forward implication is obtained by computing `Ext` against a bounded
-- injective representative of `K`. For the reverse implication, use Lemma `15.70.2` to reduce
-- finite injective dimension to vanishing of `Ext^i_R(M, K)` for all finite modules `M`; then
-- filter `M` by cyclic quotients, reduce to prime quotients `R/𝔭`, and use Noetherian induction.
-- When `I ⊈ 𝔭`, choose `f ∈ I \ 𝔭`, compare `R/𝔭` with `R/(𝔭, f)`, and apply finite generation of
-- the relevant `Ext` modules plus Nakayama's lemma. The bounded-below hypothesis is carried by
-- the Chapter `13` owner `K : D⁺(R)`.
/-- Lemma 15.70.6: let `R` be a Noetherian ring, let `I ⊆ R` be an ideal contained in the
Jacobson radical, and let `K ∈ D^+(R)` have finite cohomology modules. Then `K` has finite
injective dimension if and only if there exists an integer `b` such that
`Ext^i_R(R/J, K) = 0` for every `i > b` and every ideal `J ⊇ I`. -/
theorem finiteInjectiveDimension_iff_exists_ext_vanishing_ideal_quotients_ge
    (I : Ideal R) (hI : I ≤ Ring.jacobson R) (K : D⁺(Mod))
    (hKfinite : ∀ i : ℤ, Module.Finite R ((H i).obj K.obj)) :
    HasFiniteInjectiveDimension K.obj ↔
      ∃ b : ℤ,
        ∀ (J : Ideal R), I ≤ J →
          ∀ i : ℤ, b < i →
            ∀ e : Ext^i((single₀).obj (ModuleCat.of R (R ⧸ J)), K.obj), e = 0 := sorry

end

end CategoryTheory
