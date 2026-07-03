import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/- Domain-style sampling for Lemma 13.4.5:
- primary domain: distinguished triangles in a pretriangulated category and the exactness of the
  covariant and contravariant Hom sequences attached to them;
- sampled core/canonical declarations:
  `Triangle.coyoneda_exact₂`,
  `Triangle.yoneda_exact₂`,
  `comp_distTriang_mor_zero₁₂`;
- best owner abstraction: the canonical owner is a distinguished triangle `T ∈ distTriang D`,
  together with the exactness API on the `mor₁`-`mor₂` segment;
- primitive data: the distinguished triangle `T` and the exactness-relevant vanishing conditions
  `φ.hom₁ = 0` and `φ'.hom₃ = 0` on two triangle endomorphisms;
- derived API: the textbook `(0,b,0)` and `(0,b',0)` formulation is an immediate corollary of the
  owner-level exactness statement below, so it should not remain as a second packaged public
  theorem;
- source/core/bridge triage:
  `source-facing`: the Stacks-project vanishing statement for the textbook composite `bb'`;
  `core/canonical`: the distinguished-triangle exactness lemmas above;
  `bridge/view`: the textbook `(0,b,0)`/`(0,b',0)` reformulation, obtained immediately by
    instantiating the owner-level theorem, so no second wrapper theorem is kept.
-/

-- Proof sketch: use `φ'.comm₂` and `φ.comm₁` together with `hφ'₃` and `hφ₁` to factor
-- `φ'.hom₂` through `T.mor₁` and `φ.hom₂` through `T.mor₂` via `Triangle.coyoneda_exact₂`
-- and `Triangle.yoneda_exact₂`; then the middle composite vanishes by
-- `comp_distTriang_mor_zero₁₂`.
/-- Lemma 13.4.5: for endomorphisms `φ` and `φ'` of a distinguished triangle, the composite
`φ'.hom₂ ≫ φ.hom₂` vanishes as soon as `φ.hom₁ = 0` and `φ'.hom₃ = 0`. -/
theorem endomorphism_hom₂_comp_eq_zero {T : Triangle D}
    (hT : T ∈ distTriang D) (φ φ' : End T) (hφ₁ : φ.hom₁ = 0) (hφ'₃ : φ'.hom₃ = 0) :
    φ'.hom₂ ≫ φ.hom₂ = 0 := by
  obtain ⟨g', hg'⟩ := T.coyoneda_exact₂ hT φ'.hom₂ (by
    rw [← φ'.comm₂, hφ'₃, comp_zero])
  obtain ⟨g, hg⟩ := T.yoneda_exact₂ hT φ.hom₂ (by
    rw [φ.comm₁, hφ₁, zero_comp])
  calc
    φ'.hom₂ ≫ φ.hom₂ = (g' ≫ T.mor₁) ≫ (T.mor₂ ≫ g) := by rw [hg', hg]
    _ = g' ≫ (T.mor₁ ≫ T.mor₂) ≫ g := by simp [Category.assoc]
    _ = 0 := by rw [comp_distTriang_mor_zero₁₂ _ hT, zero_comp, comp_zero]

end
