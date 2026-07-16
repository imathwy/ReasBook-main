import StacksProject_2024.stacks_project.Chap29.Lemma_29_55_10

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

section

variable (A : Type u) [CommRing A]

/-- Ring condition combining the two hypotheses from Lemma 29.55.10 that characterize weak
normality of affine schemes with finitely many irreducible components. -/
class WeaklyNormalCriterionRing : Prop extends SeminormalRing A where
  /-- The prime divisibility condition from Lemma 29.55.10. -/
  dvd_of_pow_dvd_natCast_mul :
    ∀ p : ℕ, Nat.Prime p →
      ∀ z w : A,
        z ∈ nonZeroDivisors A →
        z ^ p ∣ w ^ p →
        z ∣ (p : A) * w →
        z ∣ w

/-- Unfold the ring condition used in the weak-normality affine criterion. -/
theorem weaklyNormalCriterionRing_iff :
    WeaklyNormalCriterionRing A ↔
      SeminormalRing A ∧
        ∀ p : ℕ, Nat.Prime p →
          ∀ z w : A,
            z ∈ nonZeroDivisors A →
            z ^ p ∣ w ^ p →
            z ∣ (p : A) * w →
            z ∣ w := sorry

end

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X]
variable [QuasiCompact (genericPointSpectrumCoproductTo X)]
variable [QuasiSeparated (genericPointSpectrumCoproductTo X)]

-- Semantic recall: `lean_leansearch` surfaced affine/open-cover scheme APIs, while local
-- Chapter 29 precedent fixes weak normality as `Scheme.WeaklyNormal` and Lemma 29.55.10 fixes
-- the affine section-ring condition as `SeminormalRing` plus the prime divisibility property.
-- The Stacks tag evidence is consistent: item tag `0H3U` agrees with the source URL ending in
-- `/tag/0H3U`.

/-- Open subschemes inherit the hypothesis that quasi-compact opens have finitely many
irreducible components. -/
instance instHasFiniteIrreducibleComponentsOnCompactOpensToScheme (U : X.Opens) :
    HasFiniteIrreducibleComponentsOnCompactOpens U.toScheme := sorry

/-- Lemma 29.55.11 (1): for a scheme `X` such that every quasi-compact open has finitely many
irreducible components, `X` is weakly normal if and only if every affine open `U ⊆ X` has section
ring satisfying conditions (1) and (2) of Lemma 29.55.10. -/
@[stacks 0H3U]
theorem weaklyNormal_iff_forall_affineOpen_sectionsRing_primeDivisibility :
    WeaklyNormal X ↔
      ∀ U : X.affineOpens,
        SeminormalRing (Γ(X, (U : X.Opens))) ∧
          ∀ p : ℕ, Nat.Prime p →
            ∀ z w : Γ(X, (U : X.Opens)),
              z ∈ nonZeroDivisors (Γ(X, (U : X.Opens))) →
              z ^ p ∣ w ^ p →
              z ∣ (p : Γ(X, (U : X.Opens))) * w →
              z ∣ w := sorry

/-- Lemma 29.55.11 (2): for a scheme `X` such that every quasi-compact open has finitely many
irreducible components, `X` is weakly normal if and only if it admits an affine open covering
whose section rings satisfy conditions (1) and (2) of Lemma 29.55.10. -/
@[stacks 0H3U]
theorem weaklyNormal_iff_exists_affineOpenCover_sectionsRing_primeDivisibility :
    WeaklyNormal X ↔
      ∃ ι : Type v, ∃ U : ι → X.affineOpens, (⨆ i, (U i : X.Opens)) = ⊤ ∧
        ∀ i, WeaklyNormalCriterionRing (Γ(X, (U i : X.Opens))) := sorry

/-- Lemma 29.55.11 (3): for a scheme `X` such that every quasi-compact open has finitely many
irreducible components, `X` is weakly normal if and only if it admits an open covering by weakly
normal open subschemes. -/
@[stacks 0H3U]
theorem weaklyNormal_iff_exists_openCover_by_weaklyNormal :
    WeaklyNormal X ↔
      ∃ ι : Type v, ∃ U : ι → X.Opens, TopologicalSpace.IsOpenCover U ∧
        ∀ i, WeaklyNormal (U i).toScheme := sorry

/-- Lemma 29.55.11 (4): if a scheme `X` satisfying the finite-irreducible-components hypothesis
on quasi-compact opens is weakly normal, then every open subscheme of `X` is weakly normal. -/
@[stacks 0H3U]
theorem weaklyNormal_toScheme (hX : WeaklyNormal X) (U : X.Opens) :
    WeaklyNormal U.toScheme := sorry

end AlgebraicGeometry.Scheme
