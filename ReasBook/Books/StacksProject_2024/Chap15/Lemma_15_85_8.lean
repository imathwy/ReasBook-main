import Mathlib
import stacks_project.Chap13.Definition_13_11_3

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

open DerivedCategory.TStructure

section

variable {𝒜 : Type u} [Category 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]

/-
Domain-style sampling for Lemma 15.85.8:
- primary domain: the canonical `t`-structure on derived categories of abelian categories, and
  its specialization to scalar endomorphisms of two-term derived `R`-modules;
- sampled owner declarations in this domain:
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`,
  `DerivedCategory.homologyFunctor`,
  `CategoryTheory.Epi`;
- best owner abstraction: the cohomological amplitude hypotheses belong to the canonical
  `t`-structure owners `K.IsGE (-1)`, `K.IsLE 0`, `K'.IsGE (-1)`, and `K'.IsLE 0`, while the map
  hypotheses are the canonical categorical conditions `IsIso ((H^0).map α)` and
  `Epi ((H^(-1)).map α)`, whose intrinsic categorical conclusion is `Epi α`;
- primitive data vs. derived API: for the owner theorem below, the primitive inputs are `K`, `K'`,
  `α`, and the cohomological hypotheses. In the module specialization, the canonical bridge is the
  purely categorical `cancel_epi` argument after obtaining `Epi α`; the hypotheses on `H^0(α)`
  and `H^{-1}(α)` are source-facing bridge data used only to supply `Epi α`. The proof-route data
  involving a kernel object `M`, a distinguished triangle, and the vanishing
  `Hom(M⟦2⟧, K') = 0` are internal bridge data and should not become public wrapper data.

Source/core/bridge triage:
- `source-facing`: the scalar-annihilation transfer theorem in `D(R)` below;
- `core/canonical`: the owner predicates `IsGE` / `IsLE`, the homology-map hypotheses on `α`,
  and the resulting categorical conclusion `Epi α` in `D(𝒜)`;
- `bridge/view`: the distinguished-triangle argument and the Chapter 13 vanishing/factorization
  lemmas used in the proof sketch.
-/

-- Proof sketch: let `M` be the kernel of `H⁻¹(α)`. The hypotheses on the two-term cohomology of
-- `K` and `K'`, together with `H⁰(α)` being an isomorphism and `H⁻¹(α)` being surjective, place
-- `α` in a distinguished triangle `M⟦1⟧ ⟶ K ⟶ K' ⟶ M⟦2⟧`. If `f • 𝟙 K = 0`, then
-- `α ≫ (f • 𝟙 K') = 0`, so `f • 𝟙 K'` factors through a morphism `M⟦2⟧ ⟶ K'`. Lemma `13.27.3`
-- gives `Hom(M⟦2⟧, K') = 0` because `M⟦2⟧` is concentrated in degree `-2` and `K'` has
-- cohomology only in degrees `-1` and `0`.
/-- Owner form of Lemma 15.85.8: in the derived category of an abelian category, a morphism
between two-term objects inducing an isomorphism on `H^0` and an epimorphism on `H^{-1}` is
itself an epimorphism.
-/
theorem epi_of_h0_iso_of_hneg1_epi
    {K K' : D(𝒜)} (α : K ⟶ K')
    (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    (hK'GE : K'.IsGE (-1)) (hK'LE : K'.IsLE 0)
    (hα0 : IsIso ((H^0).map α))
    (hαneg1 : Epi ((H^(-1)).map α)) :
    Epi α := sorry

end

section

variable {R : Type u} [CommRing R]

local notation "ModR" => ModuleCat R
local notation "DModR" => DerivedCategory ModR

/-- Lemma 15.85.8: let `α : K ⟶ K'` be a morphism in `D(R)` between objects with cohomology only
in degrees `-1` and `0`. If `H⁰(α)` is an isomorphism and `H⁻¹(α)` is an epimorphism, then any
scalar `f : R` acting by zero on `K` also acts by zero on `K'`. -/
theorem smul_id_eq_zero_of_h0_iso_of_hneg1_epi
    {K K' : DModR} (α : K ⟶ K') (f : R)
    (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    (hK'GE : K'.IsGE (-1)) (hK'LE : K'.IsLE 0)
    (hα0 : IsIso ((H^0).map α))
    (hαneg1 : Epi ((H^(-1)).map α))
    (hf : f • 𝟙 K = 0) :
    f • 𝟙 K' = 0 := by
  letI : Epi α := epi_of_h0_iso_of_hneg1_epi α hKGE hKLE hK'GE hK'LE hα0 hαneg1
  refine (cancel_epi α).1 ?_
  calc
    α ≫ (f • 𝟙 K') = f • α := by simp
    _ = (f • 𝟙 K) ≫ α := by simp
    _ = 0 := by simpa [hf]
    _ = α ≫ 0 := by simp

end

end CategoryTheory
