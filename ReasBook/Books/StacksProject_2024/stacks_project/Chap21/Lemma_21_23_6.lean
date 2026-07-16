import StacksProject_2024.stacks_project.Chap21.Lemma_21_20_3
import StacksProject_2024.stacks_project.Chap21.Lemma_21_23_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open Opposite
open RingedSite.Hom
open scoped RingedSiteCohomology

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling for Lemma 21.23.6:
- primary domain: cohomology sheaves of derived inverse limits on a ringed site, together with the
  Milnor comparison maps obtained from a chosen derived-limit presentation;
- sampled owner declarations:
  `cohomologySheaf`,
  `cohomologySheafMap`,
  `cohomologyOverObject`,
  `objectwiseCohomologyInverseSystem`,
  `underlyingAbelianCohomologySheaf`,
  `CategoryTheory.IsDerivedLimitStageComparison`,
  `ringedSiteDerivedSectionsOverObject_cohomology_shortExact`;
- best owner abstraction: the target statement is about sections of the cohomology sheaf
  `𝓗[m](X, K)`, so the public surface should be expressed using the owner `cohomologySheaf`,
  with the induced map on sections over `V` written as the evaluation
  `((cohomologySheafMap X m c).1.app (op V))`; the local vanishing and injectivity hypotheses are
  source-facing on the objectwise cohomology tower `n ↦ H^m(I.Y, K_n)`, canonically owned by
  `objectwiseCohomologyInverseSystem X I.Y Ksys m`; the comparison map itself is source-facing as
  a stage comparison `K ⟶ K_{nV}` from a chosen derived limit, so the public statement should use
  the Chapter 13 owner `IsDerivedLimitStageComparison`, while the bridge-level Milnor-product data
  stay internal;
- primitive data: a ringed site `X`, an object `V : X`, a tower
  `Ksys : ℕᵒᵖ ⥤ ModuleDerived X`, a chosen derived-limit object `K`, a stage comparison
  `c : K ⟶ K_{nV}`, and a degree `m`;
- derived API: the objectwise cohomology tower
  `objectwiseCohomologyInverseSystem X I.Y Ksys q` controlling the local hypotheses, its
  `transitionMap`s and `firstDerivedLimit`, and the induced map on sections over `V` of the
  cohomology sheaf.

Source/core/bridge triage:
- `source-facing`: injectivity on the sections over `V` of the cohomology sheaf map induced by
  the stage comparison `K ⟶ K_{nV}`, with hypotheses stated on the objectwise groups
  `H^q(I.Y, K_n)`;
- `core/canonical`: `cohomologySheaf`, `underlyingAbelianCohomologySheaf`,
  `cohomologySheafMap`, `objectwiseCohomologyInverseSystem`, `IsDerivedLimit`,
  `IsDerivedLimitStageComparison`, `SequentialInverseSystem.transitionMap`,
  `SequentialInverseSystem.firstDerivedLimit`, and
  `ringedSiteDerivedSectionsOverObject_cohomology_shortExact`;
- `bridge/view`: the Milnor-product presentation of the stage comparison is kept internal via a
  private helper; the theorem surface itself stays on the canonical sections map of `𝓗[m](X, K)`.
-/

section

variable (X : RingedSite.{u, v})
variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]

local notation "DModX" => ModuleDerived X

variable (Ksys : ℕᵒᵖ ⥤ DModX) (K : DModX)

-- Proof sketch: apply Lemma `21.20.3` to identify the source and target cohomology sheaves with
-- the sheafifications of the presheaves `U ↦ H^m(U, K)` and `U ↦ H^m(U, K_{nV})`. Over a member
-- `I.Y` of a covering from the chosen cofinal family, the Milnor short exact sequence from
-- Lemma `21.23.2` and the vanishing of the `R^1 lim` term identify `H^m(I.Y, K)` with the
-- inverse limit `lim_n H^m(I.Y, K_n)`, and the eventual
-- injectivity of the transition maps forces the image of a locally vanishing section in
-- `H^m(I.Y, K_{nV})` to come from zero. Sheafification then upgrades this local criterion to
-- injectivity on sections of the cohomology sheaf over `V`.
private theorem cohomologySheafSection_stageProjection_injective_of_cofinal_coverSystem
    (V : X)
    (m : ℤ)
    (nV : ℕ)
    [HasProduct (inverseSystemFamily Ksys)]
    (ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys)
    (hι : HasMilnorTriangle.WithMap Ksys ι)
    (CovV : X.siteTopology.Cover V → Prop)
    (hcofinal :
      ∀ S : X.siteTopology.Cover V,
        ∃ T : X.siteTopology.Cover V, CovV T ∧ Nonempty (T ⟶ S))
    (hR1vanish :
      ∀ ⦃T : X.siteTopology.Cover V⦄, CovV T → ∀ I : T.Arrow,
        IsZero ((objectwiseCohomologyInverseSystem X I.Y Ksys (m - 1)).firstDerivedLimit))
    (hinj :
      ∀ ⦃T : X.siteTopology.Cover V⦄, CovV T → ∀ I : T.Arrow, ∀ n : ℕ, ∀ hn : nV ≤ n,
        Mono ((objectwiseCohomologyInverseSystem X I.Y Ksys m).transitionMap hn)) :
    Mono
      ((cohomologySheafMap X m (ι ≫ Pi.π (inverseSystemFamily Ksys) nV)).1.app (op V)) := sorry

/-- Lemma 21.23.6: let `X` be a ringed site, let `(K_n)` be a sequential inverse system in
`D(𝒪_X)`, let `V : X`, and let `m : ℤ`. Assume there is an integer `nV` and a cofinal
family `CovV` of coverings of `V` such that for every cover `T ∈ CovV` and every member
`I : T.Arrow`, the Milnor term `R^1 lim_n H^(m - 1)(I.Y, K_n)` vanishes and the
transition maps `H^m(I.Y, K_n) ⟶ H^m(I.Y, K_{nV})` are injective for all `n ≥ nV`. Then any
stage comparison `c : K ⟶ K_{nV}` from a chosen derived limit `K = R lim_n K_n` induces an
injective map on sections over `V` of the cohomology-sheaf morphism
`𝓗[m](X, K) ⟶ 𝓗[m](X, K_{nV})`. -/
@[stacks 0D6L]
theorem cohomologySheafSection_stageComparison_injective_of_cofinal_coverSystem
    (V : X)
    (m : ℤ)
    (nV : ℕ)
    (c : K ⟶ Ksys.obj (op nV))
    (hc : IsDerivedLimitStageComparison Ksys K nV c)
    (CovV : X.siteTopology.Cover V → Prop)
    (hcofinal :
      ∀ S : X.siteTopology.Cover V,
        ∃ T : X.siteTopology.Cover V, CovV T ∧ Nonempty (T ⟶ S))
    (hR1vanish :
      ∀ ⦃T : X.siteTopology.Cover V⦄, CovV T → ∀ I : T.Arrow,
        IsZero ((objectwiseCohomologyInverseSystem X I.Y Ksys (m - 1)).firstDerivedLimit))
    (hinj :
      ∀ ⦃T : X.siteTopology.Cover V⦄, CovV T → ∀ I : T.Arrow, ∀ n : ℕ, ∀ hn : nV ≤ n,
        Mono ((objectwiseCohomologyInverseSystem X I.Y Ksys m).transitionMap hn))
    :
    Mono ((cohomologySheafMap X m c).1.app (op V)) := sorry

end
