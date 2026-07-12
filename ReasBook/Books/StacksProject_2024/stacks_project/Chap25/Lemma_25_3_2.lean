import Mathlib
import StacksProject_2024.Chap25.Lemma_25_2_3
import StacksProject_2024.Chap25.Lemma_25_3_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u

namespace CategoryTheory

open CategoryTheory.Limits
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

-- Semantic search note: `lean_leansearch` recalled mathlib's general Grothendieck-topology
-- stability API, but the verified local owner here is the Chapter 25 covering-morphism API on
-- semi-representable families, so the statements stay on `Hom.IsCovering`.

namespace SemiRepresentableFamily

namespace Hom

/-- The fiber family of a morphism of semi-representable families over a chosen target component. -/
def fiber {K L : SR(C)} (φ : K ⟶ L) (j : L.index) : SR(C, L.obj j) where
  I := { i : K.index // φ.f i = j }
  obj := fun i ↦ by
    rcases i with ⟨i, hi⟩
    subst hi
    exact Over.mk (φ.φ i)

/-- A morphism of semi-representable families is covering if each fiber family over a target
component generates a covering sieve on that component. -/
def IsCovering (J : GrothendieckTopology C) {K L : SR(C)} (φ : K ⟶ L) : Prop :=
  ∀ j : L.index, (fiber φ j).toSieve ∈ J (L.obj j)

end Hom

/-- Lemma 25.3.2 (1): a composition of covering morphisms in `SR(C)` is a covering morphism. -/
theorem isCovering_comp {K L M : SR(C)} (φ : K ⟶ L) (ψ : L ⟶ M)
    (hφ : Hom.IsCovering J φ) (hψ : Hom.IsCovering J ψ) :
    Hom.IsCovering J (φ ≫ ψ) := sorry

/-- Lemma 25.3.2 (2): if `φ : K ⟶ L` is covering, then the chosen pullback of `φ` along any
`ψ : L' ⟶ L` in `SR(C)` has covering second projection to `L'`. -/
theorem pullback_snd_isCovering {K L L' : SR(C)} [HasPullbacks C]
    (φ : K ⟶ L) (ψ : L' ⟶ L) (hφ : Hom.IsCovering J φ) :
    Hom.IsCovering J (Limits.pullback.snd φ ψ) := sorry

/-- Lemma 25.3.2 (3): if `C` has products of pairs, then the product of two covering morphisms in
`SR(C)` is again a covering morphism. -/
theorem prod_map_isCovering {A B K L : SR(C)} [HasBinaryProducts C]
    (f : A ⟶ B) (g : K ⟶ L) (hf : Hom.IsCovering J f) (hg : Hom.IsCovering J g) :
    Hom.IsCovering J (Limits.prod.map f g : A ⨯ K ⟶ B ⨯ L) := sorry

namespace Over

/-- Lemma 25.3.2 (4): a composition of covering morphisms in `SR(C, X)` is a covering morphism.
-/
theorem isCovering_comp {X : C} {K L M : SR(C, X)} (φ : K ⟶ L) (ψ : L ⟶ M)
    (hφ : Hom.IsCovering J φ) (hψ : Hom.IsCovering J ψ) :
    Hom.IsCovering J (φ ≫ ψ) := sorry

/-- Lemma 25.3.2 (5): if `φ : K ⟶ L` is covering in `SR(C, X)`, then its pullback along any
`ψ : L' ⟶ L` in `SR(C, X)` has covering second projection to `L'`. -/
theorem pullback_snd_isCovering {X : C} {K L L' : SR(C, X)} [HasPullbacks C]
    (φ : K ⟶ L) (ψ : L' ⟶ L) (hφ : Hom.IsCovering J φ) :
    Hom.IsCovering J (Limits.pullback.snd φ ψ) := sorry

/-- Lemma 25.3.2 (6): if `C` has fibre products, then the product of two covering morphisms in
`SR(C, X)` is again a covering morphism. -/
theorem prod_map_isCovering {X : C} {A B K L : SR(C, X)} [HasPullbacks C]
    (f : A ⟶ B) (g : K ⟶ L) (hf : Hom.IsCovering J f) (hg : Hom.IsCovering J g) :
    Hom.IsCovering J (Limits.prod.map f g : A ⨯ K ⟶ B ⨯ L) := sorry

end Over
end SemiRepresentableFamily

end CategoryTheory
