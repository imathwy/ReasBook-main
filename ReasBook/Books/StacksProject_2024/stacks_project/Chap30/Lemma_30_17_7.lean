import StacksProject_2024.Chap28.Lemma_28_29_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme} [MonoidalCategory X.Modules]

/-- The scheme-module monoidal structure viewed on modules over the underlying ringed space. -/
local instance instMonoidalCategoryRingedSpaceModulesForLemma30177 :
    MonoidalCategory (SheafOfModules X.toRingedSpace.ringCatSheaf) :=
  inferInstanceAs (MonoidalCategory X.Modules)

-- Semantic recall: `lean_leansearch` surfaced the canonical affine-scheme owner `IsAffine`,
-- while local Chapter 28/30 precedent represents invertibility by the tensor-right equivalence,
-- integral tensor powers by the tensor-right autoequivalence formula, and global cohomology as
-- `Sheaf.H'` on the top open. Importing the packaged `Scheme.Modules.IsAmple` owner currently
-- forces Lake to rebuild upstream nonvanishing-locus files before this target elaborates, where
-- the read-only Lake state fails; this statement therefore expands the Definition 28.26.1
-- ampleness fields using the dependency-closed nonvanishing-open surface from Lemma 28.29.6. The
-- Stacks tag evidence is consistent with tag `0EBD`.

/-- Lemma 30.17.7: let `X` be a scheme and let `L` be an ample invertible
`\mathcal O_X`-module. If there is an integer `n₀` such that
`H^p(X, L^{\otimes -n}) = 0` for every integer `n ≥ n₀` and every `p > 0`, then `X` is
affine. -/
@[stacks 0EBD]
theorem isAffine_of_isAmple_higherCohomology_neg_tensorPower_isZero
    (L : X.Modules) [Functor.IsEquivalence (tensorRight L)]
    (hX_compact : IsCompact (Set.univ : Set X))
    (hL_ample : ∀ x : X, ∃ n : ℕ+,
      ∃ s : Γ(RingedSpace.tensorPowerSheaf L n, ⊤),
        ∃ U : X.Opens, TensorPowerSectionAffineNonvanishingAt L n s U x)
    (n₀ : ℤ)
    (hvanish : ∀ (n : ℤ), n₀ ≤ n → ∀ (p : ℕ), 0 < p →
      IsZero (((SheafOfModules.toSheaf X.ringCatSheaf).obj
        (((tensorRight L).asEquivalence ^ (-n)).functor.obj
          (SheafOfModules.unit X.ringCatSheaf : X.Modules))).H' p
        (⊤ : X.Opens))) :
    IsAffine X := sorry

end AlgebraicGeometry.Scheme.Modules
