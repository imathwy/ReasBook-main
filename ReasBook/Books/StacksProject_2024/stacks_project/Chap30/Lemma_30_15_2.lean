import StacksProject_2024.stacks_project.Chap30.Lemma_30_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped DirectSum

noncomputable section

universe u v

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` surfaced the canonical `Proj` owner and the direct-sum
mapping API `DirectSum.map`/`DirectSum.toAddMonoid`. Local Chapter 30 precedent, especially
Lemmas 30.14.3 and 30.15.1, represents arbitrary-`Proj` twists by explicit chosen families because
the current project does not yet expose a concrete associated-sheaf/twist owner for every graded
module on `Proj(A)`. -/

section

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] [hNoetherian : IsNoetherianRing A]
variable (d : ℕ) (generators : Finset A)
variable (generatorDegree : {x // x ∈ generators} → ℕ)
variable (hgenerated : Algebra.adjoin (𝒜 0) (generators : Set A) = ⊤)
variable (hhomogeneous : ∀ x : {x // x ∈ generators}, x.1 ∈ 𝒜 (generatorDegree x))
variable (hpositive : ∀ x : {x // x ∈ generators}, 0 < generatorDegree x)
variable (hd_dvd : ∀ x : {x // x ∈ generators}, generatorDegree x ∣ d)
variable (hd_min : ∀ e : ℕ, (∀ x : {x // x ∈ generators}, generatorDegree x ∣ e) → d ∣ e)
variable (Mpiece : ℤ → Type u) [∀ n, AddCommGroup (Mpiece n)]
variable [hModule : Module A (DirectSum ℤ Mpiece)]
variable [hFinite : Module.Finite A (DirectSum ℤ Mpiece)]

include hNoetherian d generators generatorDegree hgenerated hhomogeneous hpositive hd_dvd hd_min
include Mpiece hModule hFinite

/-- Lemma 30.15.2 (1): for a Noetherian graded ring `A`, a finite graded `A`-module `M`, and
`d` the least common multiple of the positive degrees of homogeneous generators of `A` over `A₀`,
the truncated graded module
`N' = \bigoplus_{n \ge k} H^0(Proj(A), \widetilde{M(n)})` is finite over `A`. The family
`shiftedAssociatedSheaf` is the chosen owner of the sheaves `\widetilde{M(n)}`. -/
@[stacks 0B5R]
theorem finiteGradedModule_projShiftedAssociatedSheafTruncatedGlobalSections_finite
    (shiftedAssociatedSheaf : ℤ → (Proj 𝒜).Modules) (k : ℤ)
    [Module A (projCoherentSheafTruncatedGlobalSections 𝒜 shiftedAssociatedSheaf k)] :
    Module.Finite A (projCoherentSheafTruncatedGlobalSections 𝒜 shiftedAssociatedSheaf k) := sorry

/-- Lemma 30.15.2 (2): for the associated coherent sheaf `\widetilde M` on `Proj(A)`, the
truncated graded module
`N = \bigoplus_{n \ge k} H^0(Proj(A), \widetilde M(n))` is finite over `A`. The family
`associatedSheafTwist` is the chosen owner of the twists `\widetilde M(n)`. -/
@[stacks 0B5R]
theorem finiteGradedModule_projAssociatedSheafTwistTruncatedGlobalSections_finite
    (associatedSheaf : (Proj 𝒜).Modules) [associatedSheaf.IsCoherent]
    (associatedSheafTwist : ℤ → (Proj 𝒜).Modules) (k : ℤ)
    [Module A (projCoherentSheafTruncatedGlobalSections 𝒜 associatedSheafTwist k)] :
    Module.Finite A (projCoherentSheafTruncatedGlobalSections 𝒜 associatedSheafTwist k) := sorry

/-- Lemma 30.15.2 (3): the canonical map `N → N'` is represented in the current API by the
componentwise map on the truncated direct sums, built from the degreewise comparison maps
`H^0(Proj(A), \widetilde M(n)) → H^0(Proj(A), \widetilde{M(n)})`. -/
@[stacks 0B5R]
def projAssociatedSheafTwistTruncatedGlobalSectionsToShiftedMap
    (associatedSheafTwist shiftedAssociatedSheaf : ℤ → (Proj 𝒜).Modules) (k : ℤ)
    (degreeComparison : ∀ n : ℤ,
      projCoherentSheafCohomology 𝒜 (associatedSheafTwist n) 0 ⟶
        projCoherentSheafCohomology 𝒜 (shiftedAssociatedSheaf n) 0) :
    AddCommGrpCat.of (projCoherentSheafTruncatedGlobalSections 𝒜 associatedSheafTwist k) ⟶
      AddCommGrpCat.of (projCoherentSheafTruncatedGlobalSections 𝒜 shiftedAssociatedSheaf k) :=
  AddCommGrpCat.ofHom <|
    DirectSum.map fun n : {n : ℤ // k ≤ n} ↦
      AddCommGrpCat.Hom.hom (degreeComparison n.1)

/-- The truncated global-sections comparison map is the direct sum of the degreewise comparison
maps. -/
theorem projAssociatedSheafTwistTruncatedGlobalSectionsToShiftedMap_def
    (associatedSheafTwist shiftedAssociatedSheaf : ℤ → (Proj 𝒜).Modules) (k : ℤ)
    (degreeComparison : ∀ n : ℤ,
      projCoherentSheafCohomology 𝒜 (associatedSheafTwist n) 0 ⟶
        projCoherentSheafCohomology 𝒜 (shiftedAssociatedSheaf n) 0) :
    projAssociatedSheafTwistTruncatedGlobalSectionsToShiftedMap 𝒜
        associatedSheafTwist shiftedAssociatedSheaf k degreeComparison =
      AddCommGrpCat.ofHom
        (DirectSum.map fun n : {n : ℤ // k ≤ n} ↦
          AddCommGrpCat.Hom.hom (degreeComparison n.1)) := sorry

/-- Lemma 30.15.2 (4): if `k` is small enough so that the lower graded pieces of `M` vanish, the
degreewise section maps assemble to the canonical map
`M → \bigoplus_{n \ge k} H^0(Proj(A), \widetilde{M(n)})`. -/
@[stacks 0B5R]
def finiteGradedModuleToProjShiftedAssociatedSheafTruncatedGlobalSectionsMap
    (shiftedAssociatedSheaf : ℤ → (Proj 𝒜).Modules) (k : ℤ)
    (hk : ∀ n : ℤ, n < k → IsZero (AddCommGrpCat.of (Mpiece n)))
    (sectionMap : ∀ n : ℤ,
      AddCommGrpCat.of (Mpiece n) ⟶ projCoherentSheafCohomology 𝒜 (shiftedAssociatedSheaf n) 0) :
    AddCommGrpCat.of (DirectSum ℤ Mpiece) ⟶
      AddCommGrpCat.of (projCoherentSheafTruncatedGlobalSections 𝒜 shiftedAssociatedSheaf k) :=
  let _ := hk
  AddCommGrpCat.ofHom <|
    DirectSum.toAddMonoid fun n : ℤ ↦
      if h : k ≤ n then
        (DirectSum.of
          (fun n : {n : ℤ // k ≤ n} ↦
            (projCoherentSheafCohomology 𝒜 (shiftedAssociatedSheaf n.1) 0 : Type u))
          ⟨n, h⟩).comp (AddCommGrpCat.Hom.hom (sectionMap n))
      else
        0

/-- The map from a finite graded module to truncated global sections is assembled from the
degreewise section maps, with zero on degrees below the truncation bound. -/
theorem finiteGradedModuleToProjShiftedAssociatedSheafTruncatedGlobalSectionsMap_def
    (shiftedAssociatedSheaf : ℤ → (Proj 𝒜).Modules) (k : ℤ)
    (hk : ∀ n : ℤ, n < k → IsZero (AddCommGrpCat.of (Mpiece n)))
    (sectionMap : ∀ n : ℤ,
      AddCommGrpCat.of (Mpiece n) ⟶ projCoherentSheafCohomology 𝒜 (shiftedAssociatedSheaf n) 0) :
    finiteGradedModuleToProjShiftedAssociatedSheafTruncatedGlobalSectionsMap 𝒜 Mpiece
        shiftedAssociatedSheaf k hk sectionMap =
      AddCommGrpCat.ofHom
        (DirectSum.toAddMonoid fun n : ℤ ↦
          if h : k ≤ n then
            (DirectSum.of
              (fun n : {n : ℤ // k ≤ n} ↦
                (projCoherentSheafCohomology 𝒜 (shiftedAssociatedSheaf n.1) 0 : Type u))
              ⟨n, h⟩).comp (AddCommGrpCat.Hom.hom (sectionMap n))
          else
            0) := sorry

/-- Lemma 30.15.2 (5): for all sufficiently large degrees, the canonical maps
`M_n → N'_n = H^0(Proj(A), \widetilde{M(n)})` are isomorphisms. -/
@[stacks 0B5R]
theorem finiteGradedModule_projShiftedAssociatedSheaf_sectionMap_eventually_isIso
    (shiftedAssociatedSheaf : ℤ → (Proj 𝒜).Modules)
    (sectionMap : ∀ n : ℤ,
      AddCommGrpCat.of (Mpiece n) ⟶ projCoherentSheafCohomology 𝒜 (shiftedAssociatedSheaf n) 0) :
    ∃ b : ℤ, ∀ n : ℤ, b ≤ n → IsIso (sectionMap n) := sorry

/-- Lemma 30.15.2 (6): in every degree divisible by the lcm `d`, the degree component of the
canonical map `N → N'` is an isomorphism. -/
@[stacks 0B5R]
theorem projAssociatedSheafTwistToShiftedAssociatedSheaf_degreeComparison_isIso_of_dvd
    (associatedSheafTwist shiftedAssociatedSheaf : ℤ → (Proj 𝒜).Modules)
    (degreeComparison : ∀ n : ℤ,
      projCoherentSheafCohomology 𝒜 (associatedSheafTwist n) 0 ⟶
        projCoherentSheafCohomology 𝒜 (shiftedAssociatedSheaf n) 0) :
    ∀ n : ℤ, (d : ℤ) ∣ n → IsIso (degreeComparison n) := sorry

end

end AlgebraicGeometry
