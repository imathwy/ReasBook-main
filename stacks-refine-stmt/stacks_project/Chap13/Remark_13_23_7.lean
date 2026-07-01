import Mathlib
import stacks_project.Chap13.Definition_13_18_1
import stacks_project.Chap13.Remark_13_18_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape HomotopyCategory

noncomputable section

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling:
- primary domain: canonical comparison morphisms between injective resolutions of the same
  cochain complex in the homotopy category;
- sampled owner declarations:
  `CochainComplex.InjectiveResolution`,
  `CochainComplex.InjectiveResolution.injective`,
  `CochainComplex.InjectiveResolution.plus`,
  `CochainComplex.homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective`;
- best owner abstraction: the source-facing owner here is
  `CochainComplex.InjectiveResolution`, while the precomposition bijection of Remark 13.18.5 is
  the core/canonical theorem controlling comparison morphisms into a bounded-below injective
  complex;
- primitive data: a cochain complex `K` together with injective resolutions `I`, `J` of `K`;
- derived API: the canonical homotopy-category comparison morphism `I ⟶ J` and the
  source-facing uniqueness statement that characterizes it.

Source/core/bridge triage:
- `source-facing`: the `InjectiveResolution` comparison morphism and its uniqueness statement;
- `core/canonical`: `homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective`;
- `bridge/view`: none; this file should use the core bijection directly rather than introducing a
  parallel local comparison-morphism API outside the injective-resolution owner namespace.
-/

namespace InjectiveResolution

private noncomputable def comparisonEquiv {K : CochainComplex 𝒜 ℤ} (I J : InjectiveResolution K) :
    ((quotient 𝒜 (up ℤ)).obj I ⟶ (quotient 𝒜 (up ℤ)).obj J) ≃
      ((quotient 𝒜 (up ℤ)).obj K ⟶ (quotient 𝒜 (up ℤ)).obj J) :=
  let Q := quotient 𝒜 (up ℤ)
  Equiv.ofBijective (fun a : Q.obj I ⟶ Q.obj J ↦ Q.map I.ι ≫ a)
    (homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective I.ι J)

-- Proof sketch: apply the core owner theorem
-- `homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective` to the
-- quasi-isomorphism `I.ι : K ⟶ I`. The desired morphism is the unique preimage of the class of
-- `J.ι` under the resulting bijection.
/-- The canonical comparison morphism between two injective resolutions of the same cochain
complex in the homotopy category. -/
noncomputable def homotopyComparison {K : CochainComplex 𝒜 ℤ} (I J : InjectiveResolution K) :
    (quotient 𝒜 (up ℤ)).obj I ⟶ (quotient 𝒜 (up ℤ)).obj J :=
  (comparisonEquiv I J).symm ((quotient 𝒜 (up ℤ)).map J.ι)

@[reassoc]
theorem ι_homotopyComparison {K : CochainComplex 𝒜 ℤ} (I J : InjectiveResolution K) :
    (quotient 𝒜 (up ℤ)).map I.ι ≫ homotopyComparison I J =
      (quotient 𝒜 (up ℤ)).map J.ι := by
  let Q := quotient 𝒜 (up ℤ)
  let e := comparisonEquiv I J
  change (fun a : Q.obj I ⟶ Q.obj J ↦ Q.map I.ι ≫ a) (e.symm (Q.map J.ι)) = Q.map J.ι
  exact e.apply_symm_apply (Q.map J.ι)

attribute [simp] ι_homotopyComparison_assoc

  theorem homotopyComparison_unique {K : CochainComplex 𝒜 ℤ} (I J : InjectiveResolution K)
    {a : (quotient 𝒜 (up ℤ)).obj I ⟶ (quotient 𝒜 (up ℤ)).obj J}
    (ha : (quotient 𝒜 (up ℤ)).map I.ι ≫ a = (quotient 𝒜 (up ℤ)).map J.ι) :
    a = homotopyComparison I J := by
  let hbij :=
    homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective I.ι J
  exact hbij.injective (ha.trans (I.ι_homotopyComparison J).symm)

/-- Remark 13.23.7: for injective resolutions `I` and `J` of a cochain complex `K`, there is a
unique morphism from `I` to `J` in the homotopy category whose composite with the map `K ⟶ I` is
the map `K ⟶ J`. The source text assumes `K` bounded below, but that hypothesis is redundant once
`I` and `J` are given. -/
theorem existsUnique_homotopyComparison
    {K : CochainComplex 𝒜 ℤ} (I J : InjectiveResolution K) :
    ∃! a :
        (quotient 𝒜 (up ℤ)).obj I ⟶
          (quotient 𝒜 (up ℤ)).obj J,
      (quotient 𝒜 (up ℤ)).map I.ι ≫ a =
        (quotient 𝒜 (up ℤ)).map J.ι := by
  refine ⟨homotopyComparison I J, I.ι_homotopyComparison J, ?_⟩
  intro a ha
  exact homotopyComparison_unique I J ha

end InjectiveResolution

end CochainComplex
