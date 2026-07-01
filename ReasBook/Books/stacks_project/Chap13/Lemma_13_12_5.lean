import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
open CategoryTheory
open CategoryTheory.ComposableArrows
open DerivedCategory.TStructure

universe w v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

local notation "H" => DerivedCategory.homologyFunctor 𝒜

/- Domain-style sampling for Lemma 13.12.5:
- primary domain: truncation factorization in the canonical `t`-structure on `D(\mathcal A)`,
  with stepwise vanishing measured by the derived-category homology functors;
- sampled owner declarations:
  `DerivedCategory.IsLE`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.isLE_iff`,
  `DerivedCategory.isGE_iff`,
  `DerivedCategory.homologyFunctor`,
  `TStructure.liftTruncLE`,
  `TStructure.descTruncGE`,
  `t.truncLEι`,
  `t.truncGEπ`;
- best owner abstraction: the source-facing data are already a chain in `DerivedCategory 𝒜`,
  whose endpoint boundedness belongs to the canonical owners `S.left.IsLE 0` and
  `S.right.IsGE 0`; the degreewise vanishing of the induced homology maps remains explicit
  primitive data, but now at the same owner layer;
- primitive data: the composable-arrow diagram `S : ComposableArrows (DerivedCategory 𝒜) n` and
  the vanishing of the degree `-j` or `j` homology-functor maps for its successive arrows
  `S.arrow j`;
- derived API: existence of a factorization through the canonical truncation maps
  `τ_{\le -n}(S.right) ⟶ S.right` and `S.left ⟶ τ_{\ge n}(S.left)`;
- source/core/bridge triage:
  `source-facing`: the two factorization theorems below;
  `core/canonical`: the owners `DerivedCategory.IsLE` / `IsGE`, the homology functors `H i`,
    and the truncation morphisms `t.truncLEι`, `t.truncGEπ`;
  `bridge/view`: `DerivedCategory.isLE_iff` / `isGE_iff`, translating the textbook cohomology
    vanishing conditions into those owner predicates.

Accordingly, this file keeps the two source-facing factorization theorems, upgrades only the
public surface from chosen cochain-complex representatives to the intrinsic derived-category
objects and deletes the redundant complex-level wrapper surface.
-/

-- Proof sketch: argue by induction on the length of the composable-arrow diagram. The case
-- `n = 1` comes from the distinguished truncation triangle of Remark 13.12.4 and the vanishing
-- of the induced map on degree-`0` homology; the induction step factors first through
-- `τ_{\le -(n-1)}` of the penultimate complex and then applies the case `n = 1` to the induced
-- map between successive truncations.
/-- Lemma 13.12.5: if `K₀ ⟶ ⋯ ⟶ Kₙ` is a chain in `D(\mathcal A)` whose source is `≤ 0`
(equivalently, has no positive cohomology) and whose degree-`-j` homology-functor maps vanish at
each step, then the total composite factors through the canonical truncation map
`τ_{\le -n}(Kₙ) ⟶ Kₙ`. -/
theorem exists_factor_through_truncLE_of_stepwise_homologyMap_eq_zero
    {n : ℕ} (S : ComposableArrows (DerivedCategory 𝒜) n)
    (h₀ : S.left.IsLE 0)
    (hstep : ∀ j (hj : j < n), (H (-(j : ℤ))).map (S.arrow j hj).hom = 0) :
    ∃ φ : S.left ⟶ (t.truncLE (-(n : ℤ))).obj S.right,
      φ ≫ (t.truncLEι (-(n : ℤ))).app S.right = S.hom := sorry

-- Proof sketch: apply the previous induction argument to the dual truncation triangles. The base
-- case `n = 1` uses the distinguished triangle for `τ_{\ge 1}`, and the induction step factors
-- successively through `τ_{\ge j}` because each degree-`j` homology map is zero.
/-- Dual form of Lemma 13.12.5: if `K₀ ⟶ ⋯ ⟶ Kₙ` is a chain in `D(\mathcal A)` whose target is
`≥ 0` (equivalently, has no negative cohomology) and whose degree-`j` homology-functor maps
vanish at each step, then the total composite factors through the canonical map
`K₀ ⟶ τ_{\ge n}(K₀)`. -/
theorem exists_factor_through_truncGE_of_stepwise_homologyMap_eq_zero
    {n : ℕ} (S : ComposableArrows (DerivedCategory 𝒜) n)
    (h₀ : S.right.IsGE 0)
    (hstep : ∀ j (hj : j < n), (H (j : ℤ)).map (S.arrow j hj).hom = 0) :
    ∃ φ : (t.truncGE (n : ℤ)).obj S.left ⟶ S.right,
      (t.truncGEπ (n : ℤ)).app S.left ≫ φ = S.hom := sorry

end CategoryTheory
