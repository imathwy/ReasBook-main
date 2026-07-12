import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import StacksProject_2024.Chap18.Definition_18_28_1
import StacksProject_2024.Chap21.Definition_21_17_2
import StacksProject_2024.Chap21.Definition_21_46_1_Core

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open DerivedCategory
open RingedSite.Hom (ModuleCat ModuleDerived)
open SheafOfModules.RingedSite.CochainComplex

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "X" => RingedSite.ofCommRingSheaf J 𝒪
local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "DMod" => ModuleDerived X
local notation "Cpx" => CochainComplex Mod ℤ

variable [CategoryWithHomology (ModuleCat (RingedSite.ofCommRingSheaf J 𝒪))]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ModuleDerived (RingedSite.ofCommRingSheaf J 𝒪))]

/- Domain-style sampling for Lemma 21.46.3:
- primary domain: tor-amplitude in `D(𝒪)` on a commutative ringed site, characterized by
  bounded flat representatives;
- sampled owner declarations:
  `SheafOfModules.RingedSite.HasTorAmplitudeIn`,
  `SheafOfModules.RingedSite.IsFlat`,
  `CochainComplex.IsTermwiseFlat`,
  `Q.obj`;
- best owner abstraction:
  `source-facing`: the representative criterion below for tor-amplitude in `[a, b]` on the
    commutative ringed site `RingedSite.ofCommRingSheaf J 𝒪`;
  `core/canonical`: the Chapter 21 owner `HasTorAmplitudeIn` on `ModuleDerived X` and the
    Chapter 18/21 flatness owners `IsFlat 𝒪` and `CochainComplex.IsTermwiseFlat`;
  `bridge/view`: a cochain representative `K` supported in `[a, b]` whose flatness is expressed
    through the canonical complex-level owner `CochainComplex.IsTermwiseFlat`, rather than by an
    unpacked degreewise hypothesis.

Primitive vs. derived:
- primitive data: the commutative ringed site presentation `(J, 𝒪)`, the derived object `E`,
  bounds `a, b`, and a cochain complex `K` supported in `[a, b]` whose terms are flat
  `𝒪`-modules, expressed by `IsTermwiseFlat K`;
- derived API: the equivalence between the owner predicate `HasTorAmplitudeIn E a b` and the
  direct existential representative criterion in the theorem below.

Source/core/bridge triage:
- `source-facing`: the direct existential representative criterion in the theorem below;
- `core/canonical`: `X`, `ModuleCat X`, `ModuleDerived X`, `HasTorAmplitudeIn`, and
  `IsFlat 𝒪`;
- `bridge/view`: `Q.obj K`. -/

-- Proof sketch: if `E` is represented by such a flat complex, derived tensor products are computed
-- termwise, so tor-amplitude is immediate from the degree support. Conversely, start from a
-- K-flat replacement with flat terms as in Lemma `21.17.11`, trim the complex from above using
-- vanishing of the top cohomology and flat-kernel preservation from Lemma `18.28.10`, and then
-- truncate below `a`; Lemma `21.46.2` gives flatness in the new degree `a` term.
/-- Lemma 21.46.3: an object `E` of `D(𝒪_X)` has tor-amplitude in `[a, b]` if and only if it is
isomorphic in `D(𝒪_X)` to a cochain complex `ℰ^•` of flat `𝒪_X`-modules with `ℰ^i = 0` for
`i ∉ [a, b]`. -/
@[stacks 08G1]
theorem hasTorAmplitudeIn_iff_exists_flat_representative
    (E : DMod) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔
      ∃ (K : Cpx) (_ : E ≅ Q.obj K),
        K.IsStrictlyGE a ∧ K.IsStrictlyLE b ∧ IsTermwiseFlat K := by
  sorry

namespace HasTorAmplitudeIn

/-- A tor-amplitude bound in `[a, b]` yields a flat representative supported in `[a, b]`. -/
theorem exists_flat_representative
    {E : DMod} {a b : ℤ}
    (hE : HasTorAmplitudeIn E a b) :
    ∃ (K : Cpx) (_ : E ≅ Q.obj K),
      K.IsStrictlyGE a ∧ K.IsStrictlyLE b ∧ IsTermwiseFlat K :=
  (hasTorAmplitudeIn_iff_exists_flat_representative E a b).1 hE

end HasTorAmplitudeIn

/-- A bounded flat representative supported in `[a, b]` gives tor-amplitude in `[a, b]`. -/
theorem hasTorAmplitudeIn_of_exists_flat_representative
    {E : DMod} {a b : ℤ}
    (hE : ∃ (K : Cpx) (_ : E ≅ Q.obj K),
      K.IsStrictlyGE a ∧ K.IsStrictlyLE b ∧ IsTermwiseFlat K) :
    HasTorAmplitudeIn E a b :=
  (hasTorAmplitudeIn_iff_exists_flat_representative E a b).2 hE

end

end SheafOfModules.RingedSite
