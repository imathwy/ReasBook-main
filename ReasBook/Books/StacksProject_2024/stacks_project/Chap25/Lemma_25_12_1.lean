import Mathlib
import StacksProject_2024.Chap14.Definition_14_18_1
import StacksProject_2024.Chap25.Definition_25_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open SimplexCategory SimplexCategory.Truncated
open scoped CategoryTheory.SemiRepresentableFamily Simplicial SimplexCategory.Truncated

noncomputable section

universe w v u

namespace CategoryTheory

-- Semantic search note: no `lean_leansearch` tool was available in this run; the owner choice
-- follows the Chapter 14 split-simplicial-object API and the Chapter 25 `SR(C)` component-morphism
-- API.

namespace SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable {I : Type*} [Category I]

/-- The target index of the component of a map between `I`-indexed semi-representable families. -/
abbrev componentIndex (K : Iᵒᵖ ⥤ SR(C)) {i j : I} (φ : i ⟶ j)
    (a : (K.obj (op j)).index) :=
  (K.map φ.op).f a

@[simp] theorem componentIndex_eq_f (K : Iᵒᵖ ⥤ SR(C)) {i j : I} (φ : i ⟶ j)
    (a : (K.obj (op j)).index) :
    componentIndex K φ a = (K.map φ.op).f a :=
  rfl

/-- The component morphism of a map between `I`-indexed semi-representable families. -/
abbrev componentMap (K : Iᵒᵖ ⥤ SR(C)) {i j : I} (φ : i ⟶ j)
    (a : (K.obj (op j)).index) :
    (K.obj (op j)).obj a ⟶ (K.obj (op i)).obj (componentIndex K φ a) :=
  (K.map φ.op).φ a

@[simp] theorem componentMap_eq_φ (K : Iᵒᵖ ⥤ SR(C)) {i j : I} (φ : i ⟶ j)
    (a : (K.obj (op j)).index) :
    componentMap K φ a = (K.map φ.op).φ a :=
  rfl

/-- Predicate recording that every component map induced by an epimorphism in the indexing
category is an isomorphism. -/
def ComponentwiseIsIsoOnEpis (K : Iᵒᵖ ⥤ SR(C)) : Prop :=
  ∀ {i j : I} (φ : i ⟶ j) [Epi φ] (a : (K.obj (op j)).index), IsIso (componentMap K φ a)

/-- Under the epimorphism criterion, every component map is an isomorphism. -/
theorem isIso_componentMap_of_componentwiseIsIsoOnEpis {K : Iᵒᵖ ⥤ SR(C)}
    (hK : ComponentwiseIsIsoOnEpis K) {i j : I} (φ : i ⟶ j) [Epi φ]
    (a : (K.obj (op j)).index) : IsIso (componentMap K φ a) :=
  hK φ a

end SemiRepresentableFamily

namespace SimplicialObject.Truncated

variable {C : Type u} [Category.{v} C]
open SemiRepresentableFamily

private abbrev truncatedSimplex (r n : ℕ) (hn : n ≤ r) : SimplexCategory.Truncated r :=
  { obj := SimplexCategory.mk n, property := hn }

/-- The component morphism induced by a truncated degeneracy operator. -/
abbrev degeneracyComponentMap {r n : ℕ} (K : SimplicialObject.Truncated (SR(C)) r)
    (hn : n < r) (j : Fin (n + 1))
    (i : (K.obj
      (op (truncatedSimplex r n (Nat.le_of_lt hn)))).index) :
    (K.obj
      (op (truncatedSimplex r n (Nat.le_of_lt hn)))).obj i ⟶
      (K.obj
        (op (truncatedSimplex r (n + 1) (Nat.succ_le_of_lt hn)))).obj
        (componentIndex K
          (SimplexCategory.Truncated.σ r j (Nat.succ_le_of_lt hn) (Nat.le_of_lt hn)) i) :=
  componentMap K
    (SimplexCategory.Truncated.σ r j (Nat.succ_le_of_lt hn) (Nat.le_of_lt hn)) i

@[simp] theorem degeneracyComponentMap_eq_componentMap {r n : ℕ}
    (K : SimplicialObject.Truncated (SR(C)) r) (hn : n < r) (j : Fin (n + 1))
    (i : (K.obj
      (op (truncatedSimplex r n (Nat.le_of_lt hn)))).index) :
    degeneracyComponentMap K hn j i =
      componentMap K
        (SimplexCategory.Truncated.σ r j (Nat.succ_le_of_lt hn) (Nat.le_of_lt hn)) i :=
  rfl

/-- Predicate recording that every component map induced by a truncated degeneracy morphism is an
isomorphism. -/
def ComponentwiseIsIsoOnDegeneracies {r : ℕ} (K : SimplicialObject.Truncated (SR(C)) r) : Prop :=
  ∀ ⦃n : ℕ⦄ (hn : n < r) (j : Fin (n + 1))
    (i : (K.obj
      (op (truncatedSimplex r n (Nat.le_of_lt hn)))).index),
    IsIso (degeneracyComponentMap K hn j i)

/-- Under the degeneracy criterion, every truncated degeneracy component map is an isomorphism. -/
theorem isIso_degeneracyComponentMap_of_componentwiseIsIsoOnDegeneracies {r : ℕ}
    {K : SimplicialObject.Truncated (SR(C)) r}
    (hK : ComponentwiseIsIsoOnDegeneracies K)
    {n : ℕ} (hn : n < r) (j : Fin (n + 1))
    (i : (K.obj
      (op (truncatedSimplex r n (Nat.le_of_lt hn)))).index) :
    IsIso (degeneracyComponentMap K hn j i) :=
  hK hn j i

/-- Lemma 25.12.1 (1): an `r`-truncated simplicial semi-representable family is split exactly when
every component map induced by a surjective simplex morphism is an isomorphism. -/
@[stacks 0DAU]
theorem isSplit_iff_componentwiseIsIsoOnEpis
    {r : ℕ} (K : SimplicialObject.Truncated (SR(C)) r) :
    Nonempty (Splitting K) ↔ SemiRepresentableFamily.ComponentwiseIsIsoOnEpis K := sorry

/-- Lemma 25.12.1 (2): for an `r`-truncated simplicial semi-representable family, it suffices to
check the surjective-simplex isomorphism condition only on the degeneracy maps. -/
@[stacks 0DAU]
theorem componentwiseIsIsoOnEpis_iff_componentwiseIsIsoOnDegeneracies
    {r : ℕ} (K : SimplicialObject.Truncated (SR(C)) r) :
    SemiRepresentableFamily.ComponentwiseIsIsoOnEpis K ↔ ComponentwiseIsIsoOnDegeneracies K := sorry

/-- A split truncated simplicial semi-representable family satisfies the surjective-simplex
componentwise isomorphism criterion. -/
theorem componentwiseIsIsoOnEpis_of_isSplit {r : ℕ}
    {K : SimplicialObject.Truncated (SR(C)) r}
    (hK : Nonempty (Splitting K)) :
    SemiRepresentableFamily.ComponentwiseIsIsoOnEpis K :=
  (isSplit_iff_componentwiseIsIsoOnEpis K).1 hK

/-- The surjective-simplex componentwise isomorphism criterion produces a splitting. -/
theorem isSplit_of_componentwiseIsIsoOnEpis {r : ℕ}
    {K : SimplicialObject.Truncated (SR(C)) r}
    (hK : SemiRepresentableFamily.ComponentwiseIsIsoOnEpis K) : Nonempty (Splitting K) :=
  (isSplit_iff_componentwiseIsIsoOnEpis K).2 hK

/-- A truncated simplicial semi-representable family is split exactly when the component maps
induced by the truncated degeneracy morphisms are isomorphisms. -/
theorem isSplit_iff_componentwiseIsIsoOnDegeneracies {r : ℕ}
    (K : SimplicialObject.Truncated (SR(C)) r) :
    Nonempty (Splitting K) ↔ ComponentwiseIsIsoOnDegeneracies K := by
  rw [isSplit_iff_componentwiseIsIsoOnEpis K,
    componentwiseIsIsoOnEpis_iff_componentwiseIsIsoOnDegeneracies K]

/-- A split truncated simplicial semi-representable family satisfies the truncated degeneracy
componentwise isomorphism criterion. -/
theorem componentwiseIsIsoOnDegeneracies_of_isSplit {r : ℕ}
    {K : SimplicialObject.Truncated (SR(C)) r}
    (hK : Nonempty (Splitting K)) :
    ComponentwiseIsIsoOnDegeneracies K :=
  (isSplit_iff_componentwiseIsIsoOnDegeneracies K).1 hK

/-- The truncated degeneracy componentwise isomorphism criterion produces a splitting. -/
theorem isSplit_of_componentwiseIsIsoOnDegeneracies {r : ℕ}
    {K : SimplicialObject.Truncated (SR(C)) r}
    (hK : ComponentwiseIsIsoOnDegeneracies K) : Nonempty (Splitting K) :=
  (isSplit_iff_componentwiseIsIsoOnDegeneracies K).2 hK

end SimplicialObject.Truncated

namespace SimplicialObject

variable {C : Type u} [Category.{v} C]
open SemiRepresentableFamily

/-- The component morphism induced by a simplicial degeneracy operator. -/
abbrev degeneracyComponentMap (K : SimplicialObject (SR(C))) (n : ℕ) (j : Fin (n + 1))
    (i : (K.obj (op ⦋n⦌)).index) :
    (K.obj (op ⦋n⦌)).obj i ⟶
      (K.obj (op ⦋n + 1⦌)).obj
        (componentIndex K (SimplexCategory.σ j) i) :=
  componentMap K (SimplexCategory.σ j) i

@[simp] theorem degeneracyComponentMap_eq_componentMap
    (K : SimplicialObject (SR(C))) (n : ℕ) (j : Fin (n + 1))
    (i : (K.obj (op ⦋n⦌)).index) :
    degeneracyComponentMap K n j i = componentMap K (SimplexCategory.σ j) i :=
  rfl

/-- Predicate recording that every component map induced by a degeneracy morphism is an
isomorphism. -/
def ComponentwiseIsIsoOnDegeneracies (K : SimplicialObject (SR(C))) : Prop :=
  ∀ (n : ℕ) (j : Fin (n + 1)) (i : (K.obj (op ⦋n⦌)).index),
    IsIso (degeneracyComponentMap K n j i)

/-- Under the degeneracy criterion, every simplicial degeneracy component map is an isomorphism. -/
theorem isIso_degeneracyComponentMap_of_componentwiseIsIsoOnDegeneracies
    {K : SimplicialObject (SR(C))} (hK : ComponentwiseIsIsoOnDegeneracies K)
    (n : ℕ) (j : Fin (n + 1)) (i : (K.obj (op ⦋n⦌)).index) :
    IsIso (degeneracyComponentMap K n j i) :=
  hK n j i

/-- Lemma 25.12.1 (3): a simplicial semi-representable family is split exactly when every
component map induced by a surjective simplex morphism is an isomorphism. -/
@[stacks 0DAU]
theorem isSplit_iff_componentwiseIsIsoOnEpis
    (K : SimplicialObject (SR(C))) :
    Nonempty (SimplicialObject.Splitting K) ↔ SemiRepresentableFamily.ComponentwiseIsIsoOnEpis K :=
  sorry

/-- Lemma 25.12.1 (4): for a simplicial semi-representable family, it suffices to check the
surjective-simplex isomorphism condition only on the degeneracy maps. -/
@[stacks 0DAU]
theorem componentwiseIsIsoOnEpis_iff_componentwiseIsIsoOnDegeneracies
    (K : SimplicialObject (SR(C))) :
    SemiRepresentableFamily.ComponentwiseIsIsoOnEpis K ↔ ComponentwiseIsIsoOnDegeneracies K := sorry

/-- A split simplicial semi-representable family satisfies the surjective-simplex componentwise
isomorphism criterion. -/
theorem componentwiseIsIsoOnEpis_of_isSplit
    {K : SimplicialObject (SR(C))} (hK : Nonempty (SimplicialObject.Splitting K)) :
    SemiRepresentableFamily.ComponentwiseIsIsoOnEpis K :=
  (isSplit_iff_componentwiseIsIsoOnEpis K).1 hK

/-- The surjective-simplex componentwise isomorphism criterion produces a splitting. -/
theorem isSplit_of_componentwiseIsIsoOnEpis
    {K : SimplicialObject (SR(C))}
    (hK : SemiRepresentableFamily.ComponentwiseIsIsoOnEpis K) :
    Nonempty (SimplicialObject.Splitting K) :=
  (isSplit_iff_componentwiseIsIsoOnEpis K).2 hK

/-- A simplicial semi-representable family is split exactly when the component maps induced by the
degeneracy morphisms are isomorphisms. -/
theorem isSplit_iff_componentwiseIsIsoOnDegeneracies
    (K : SimplicialObject (SR(C))) :
    Nonempty (SimplicialObject.Splitting K) ↔ ComponentwiseIsIsoOnDegeneracies K := by
  rw [isSplit_iff_componentwiseIsIsoOnEpis K,
    componentwiseIsIsoOnEpis_iff_componentwiseIsIsoOnDegeneracies K]

/-- A split simplicial semi-representable family satisfies the degeneracy componentwise
isomorphism criterion. -/
theorem componentwiseIsIsoOnDegeneracies_of_isSplit
    {K : SimplicialObject (SR(C))} (hK : Nonempty (SimplicialObject.Splitting K)) :
    ComponentwiseIsIsoOnDegeneracies K :=
  (isSplit_iff_componentwiseIsIsoOnDegeneracies K).1 hK

/-- The degeneracy componentwise isomorphism criterion produces a splitting. -/
theorem isSplit_of_componentwiseIsIsoOnDegeneracies
    {K : SimplicialObject (SR(C))}
    (hK : ComponentwiseIsIsoOnDegeneracies K) :
    Nonempty (SimplicialObject.Splitting K) :=
  (isSplit_iff_componentwiseIsIsoOnDegeneracies K).2 hK

end SimplicialObject

end CategoryTheory
