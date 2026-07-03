import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_12_1 (from Chap12) -/
namespace CategoryTheory

open ComposableArrows

universe vA uA vB uB

/- Domain-style sampling:
- primary domain: cohomological `δ`-functors on short exact sequences in preadditive
  categories, organized around the induced long exact cohomology sequence.
- inspected canonical declarations in this domain:
  `CategoryTheory.DeltaFunctor`,
  `CategoryTheory.Functor.Additive`,
  `CategoryTheory.ShortComplex.ShortExact`,
  `Functor.homologySequenceComposableArrows₅_exact`,
  `ComposableArrows.Exact`,
  `CohomologicalDeltaFunctor.Hom`.
- best owner abstraction in this file: `CohomologicalDeltaFunctor`.
- `source-facing`: a cohomological `δ`-functor with its degreewise additive functors, connecting
  morphisms, left exactness in degree `0`, long-exact five-term windows, and naturality.
- `core/canonical`: the owner structure `CohomologicalDeltaFunctor`, together with the canonical
  owners `CohomologicalDeltaFunctor.Hom` and `CohomologicalDeltaFunctor.IsUniversal`.
- `bridge/view`: the adjacent exactness lemmas `map_exact`, `exact_map_g_δ`, `exact_δ_map_f`,
  and the assembly lemma `exact₅_of_adjacent_exactness`.
- Primitive data vs derived API: the primitive owner data are the degreewise additive functors,
  the connecting morphisms, the degree-zero monomorphism statement, the five-term exactness datum,
  and naturality in short exact sequences. The adjacent exactness lemmas, category structure, and
  uniqueness consequences are derived API from that owner layer. None of these primitive fields
  uses abelianity, so the owner abstraction lives at the weaker preadditive level.
-/

/-- Definition 12.12.1: A cohomological `δ`-functor from `A` to `B` consists of additive
functors `Fⁿ : A ⥤ B` for `n ≥ 0`, together with connecting morphisms attached to each short exact
sequence in `A`, such that the induced long sequence is exact and these connecting morphisms are
natural in morphisms of short exact sequences. The owner structure only uses the canonical
preadditive exactness API. -/
structure CohomologicalDeltaFunctor (A : Type uA) [Category.{vA} A] [Preadditive A]
    (B : Type uB) [Category.{vB} B] [Preadditive B] where
  /-- The degreewise additive functors `Fⁿ`. -/
  F : ℕ → A ⥤+ B
  /-- The connecting morphism `Fⁿ(C) ⟶ Fⁿ⁺¹(A)` attached to a short exact sequence
  `0 ⟶ A ⟶ B ⟶ C ⟶ 0`. -/
  δ ⦃S : ShortComplex A⦄ (hS : S.ShortExact) (n : ℕ) :
    (F n).obj.obj S.X₃ ⟶ (F (n + 1)).obj.obj S.X₁
  /-- Exactness at the initial term `F⁰(A)` of the long exact sequence. -/
  mono_map_f_zero ⦃S : ShortComplex A⦄ (hS : S.ShortExact) : Mono ((F 0).obj.map S.f)
  /-- The six-term window
  `Fⁿ(X₁) ⟶ Fⁿ(X₂) ⟶ Fⁿ(X₃) ⟶ Fⁿ⁺¹(X₁) ⟶ Fⁿ⁺¹(X₂) ⟶ Fⁿ⁺¹(X₃)` attached to a short exact
  sequence is exact. The shorter exactness statements are derived from this owner datum. -/
  exact₅ ⦃S : ShortComplex A⦄ (hS : S.ShortExact) (n : ℕ) :
    (mk₅ ((F n).obj.map S.f) ((F n).obj.map S.g) (δ hS n)
      ((F (n + 1)).obj.map S.f) ((F (n + 1)).obj.map S.g)).Exact
  /-- The connecting morphisms form a commutative square with morphisms of short exact sequences. -/
  δ_naturality ⦃S T : ShortComplex A⦄ (hS : S.ShortExact) (hT : T.ShortExact)
      (φ : S ⟶ T) (n : ℕ) :
    CommSq ((F n).obj.map φ.τ₃) (δ hS n) (δ hT n) ((F (n + 1)).obj.map φ.τ₁)

namespace CohomologicalDeltaFunctor

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]

/-- A cohomological `δ`-functor can be evaluated at a degree to recover its additive functor in
that degree. -/
instance : CoeFun (CohomologicalDeltaFunctor A B) (fun _ ↦ ℕ → A ⥤+ B) where
  coe T := T.F

/-- Exactness at `Fⁿ(B)` for the long exact sequence attached to a short exact sequence. -/
theorem map_exact (F : CohomologicalDeltaFunctor A B) {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) :
    (S.map (F n).obj).Exact := by
  simpa using (F.exact₅ hS n).exact 0

/-- The connecting morphism annihilates the image of `Fⁿ(B) ⟶ Fⁿ(C)`. -/
@[simp, reassoc]
theorem map_g_comp_δ (F : CohomologicalDeltaFunctor A B) {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) :
    (F n).obj.map S.g ≫ F.δ hS n = 0 := by
  simpa using (F.exact₅ hS n).toIsComplex.zero 1

/-- Exactness at `Fⁿ(C)` for the long exact sequence attached to a short exact sequence. -/
theorem exact_map_g_δ (F : CohomologicalDeltaFunctor A B) {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk ((F n).obj.map S.g) (F.δ hS n) (F.map_g_comp_δ hS n)).Exact := by
  simpa [map_g_comp_δ] using (F.exact₅ hS n).exact 1

/-- The connecting morphism factors through the kernel of `Fⁿ⁺¹(A) ⟶ Fⁿ⁺¹(B)`. -/
@[simp, reassoc]
theorem δ_comp_map_f (F : CohomologicalDeltaFunctor A B) {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) :
    F.δ hS n ≫ (F (n + 1)).obj.map S.f = 0 := by
  simpa using (F.exact₅ hS n).toIsComplex.zero 2

/-- Exactness at `Fⁿ⁺¹(A)` for the long exact sequence attached to a short exact sequence. -/
theorem exact_δ_map_f (F : CohomologicalDeltaFunctor A B) {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk (F.δ hS n) ((F (n + 1)).obj.map S.f) (F.δ_comp_map_f hS n)).Exact := by
  simpa [δ_comp_map_f] using (F.exact₅ hS n).exact 2

/-- The owner five-term exactness datum can be assembled from the three adjacent short-complex
exactness statements. -/
theorem exact₅_of_adjacent_exactness
    {F : ℕ → A ⥤+ B}
    {δ : ∀ ⦃S : ShortComplex A⦄ (_hS : S.ShortExact) (n : ℕ),
      (F n).obj.obj S.X₃ ⟶ (F (n + 1)).obj.obj S.X₁}
    (map_g_comp_δ : ∀ ⦃S : ShortComplex A⦄ (hS : S.ShortExact) (n : ℕ),
      (F n).obj.map S.g ≫ δ hS n = 0)
    (δ_comp_map_f : ∀ ⦃S : ShortComplex A⦄ (hS : S.ShortExact) (n : ℕ),
      δ hS n ≫ (F (n + 1)).obj.map S.f = 0)
    (map_exact : ∀ ⦃S : ShortComplex A⦄ (_hS : S.ShortExact) (n : ℕ), (S.map (F n).obj).Exact)
    (exact_map_g_δ : ∀ ⦃S : ShortComplex A⦄ (hS : S.ShortExact) (n : ℕ),
      (ShortComplex.mk ((F n).obj.map S.g) (δ hS n) (map_g_comp_δ hS n)).Exact)
    (exact_δ_map_f : ∀ ⦃S : ShortComplex A⦄ (hS : S.ShortExact) (n : ℕ),
      (ShortComplex.mk (δ hS n) ((F (n + 1)).obj.map S.f) (δ_comp_map_f hS n)).Exact)
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (mk₅ ((F n).obj.map S.f) ((F n).obj.map S.g) (δ hS n)
      ((F (n + 1)).obj.map S.f) ((F (n + 1)).obj.map S.g)).Exact := by
  refine exact_of_δ₀ (map_exact hS n).exact_toComposableArrows ?_
  refine exact_of_δ₀ (exact_map_g_δ hS n).exact_toComposableArrows ?_
  exact exact_of_δ₀ (exact_δ_map_f hS n).exact_toComposableArrows
    (map_exact hS (n + 1)).exact_toComposableArrows

/-- A morphism of cohomological `δ`-functors is a graded natural transformation compatible with
the connecting morphisms. -/
@[ext] structure Hom (F G : CohomologicalDeltaFunctor A B) where
  /-- The degreewise natural transformations. -/
  app (n : ℕ) : (F n).obj ⟶ (G n).obj
  /-- The degreewise natural transformations form a commutative square with the connecting
  morphisms. -/
  comm ⦃S : ShortComplex A⦄ (hS : S.ShortExact) (n : ℕ) :
    CommSq ((app n).app S.X₃) (F.δ hS n) (G.δ hS n) ((app (n + 1)).app S.X₁)

namespace Hom

/-- The identity morphism of a cohomological `δ`-functor. -/
def id (F : CohomologicalDeltaFunctor A B) : Hom F F where
  app n := 𝟙 ((F n).obj)
  comm {_} hS n := CommSq.mk (by simp)

/-- The composite of two morphisms of cohomological `δ`-functors. -/
def comp {F G H : CohomologicalDeltaFunctor A B} (τ : Hom F G) (σ : Hom G H) : Hom F H where
  app n := τ.app n ≫ σ.app n
  comm {_} hS n := CommSq.horiz_comp (τ.comm hS n) (σ.comm hS n)

end Hom

/-- Cohomological `δ`-functors form a category by degreewise composition of morphisms. -/
instance : Category (CohomologicalDeltaFunctor A B) where
  Hom F G := Hom F G
  id := Hom.id
  comp τ σ := Hom.comp τ σ
  id_comp := by
    intro F G τ
    ext n X
    simp [Hom.comp, Hom.id]
  comp_id := by
    intro F G τ
    ext n X
    simp [Hom.comp, Hom.id]
  assoc := by
    intro F G H K τ σ ρ
    ext n X
    simp [Hom.comp, Category.assoc]

@[simp] theorem id_app (F : CohomologicalDeltaFunctor A B) (n : ℕ) :
    (𝟙 F : F ⟶ F).app n = 𝟙 ((F n).obj) :=
  rfl

@[simp] theorem comp_app {F G H : CohomologicalDeltaFunctor A B} (τ : F ⟶ G) (σ : G ⟶ H)
    (n : ℕ) :
    (τ ≫ σ).app n = τ.app n ≫ σ.app n :=
  rfl

/-- A cohomological `δ`-functor is universal if every degree-zero natural transformation extends
uniquely to a morphism of `δ`-functors. -/
class IsUniversal (F : CohomologicalDeltaFunctor A B) : Prop where
  existsUnique_hom (G : CohomologicalDeltaFunctor A B) (t : (F 0).obj ⟶ (G 0).obj) :
    ∃! τ : F ⟶ G, τ.app 0 = t

-- Proof sketch: apply universality of `G` to the prescribed degree-zero comparison
-- `eG.hom ≫ eH.inv`, apply universality of `H` to the inverse comparison, and use uniqueness of
-- extensions to show that the two induced morphisms are inverse.
/-- A universal cohomological `δ`-functor with prescribed degree-zero term `F` is determined up to
a unique invertible morphism of `δ`-functors. -/
theorem universal_delta_functor_unique_up_to_unique_iso
    (F : A ⥤ B)
    {G H : CohomologicalDeltaFunctor A B}
    (hG_univ : IsUniversal G) (hH_univ : IsUniversal H)
    (eG : (G 0).obj ≅ F) (eH : (H 0).obj ≅ F) :
    ∃! e : G ≅ H, e.hom.app 0 = eG.hom ≫ eH.inv := sorry

end CohomologicalDeltaFunctor

end CategoryTheory

/-! ### Definition_12_12_2 (from Chap12) -/
namespace CategoryTheory

/- Domain-style sampling:
- primary domain: morphisms of cohomological `δ`-functors between abelian categories.
- relevant upstream chapter declarations inspected in `Definition_12_12_1`:
  `CohomologicalDeltaFunctor.Hom`,
  `CohomologicalDeltaFunctor.Hom.app`,
  `CohomologicalDeltaFunctor.Hom.comm`,
  `CohomologicalDeltaFunctor.Hom.comp`.
- `source-facing`: the textbook notion of a morphism of cohomological `δ`-functors.
- `core/canonical`: `CohomologicalDeltaFunctor.Hom`.
- `bridge/view`: the degreewise component projection `CohomologicalDeltaFunctor.Hom.app` and the
  compatibility-square projection `CohomologicalDeltaFunctor.Hom.comm`.
- Primitive data vs derived API: the primitive owner data is exactly the degreewise natural
  transformation family together with compatibility with the connecting morphisms; identity,
  composition, and the category structure are derived API from that owner.
-/

/- Definition 12.12.2: a morphism of cohomological `δ`-functors is exactly the canonical owner
structure `CohomologicalDeltaFunctor.Hom`. -/
recall CohomologicalDeltaFunctor.Hom

end CategoryTheory

/-! ### Definition_12_12_3 (from Chap12) -/
namespace CategoryTheory

/- Domain-style sampling:
- primary domain: universal cohomological `δ`-functors in an abelian-category setting.
- declarations inspected in the chapter owner API:
  `CohomologicalDeltaFunctor.Hom`,
  `CohomologicalDeltaFunctor.IsUniversal`,
  `CohomologicalDeltaFunctor.universal_delta_functor_unique_up_to_unique_iso`.
- `source-facing`: the textbook predicate that a cohomological `δ`-functor is universal.
- `core/canonical`: `CohomologicalDeltaFunctor.IsUniversal`.
- `bridge/view`: the extension-and-uniqueness clause carried by the owner predicate.
- Primitive data vs derived API: the primitive owner data are the cohomological `δ`-functor and
  the owner universality predicate; the explicit extension-and-uniqueness statement for a fixed
  degree-zero morphism is derived API from that owner predicate.
-/

/- Definition 12.12.3: universality of a cohomological `δ`-functor is exactly the canonical
predicate `CohomologicalDeltaFunctor.IsUniversal`. -/
recall CohomologicalDeltaFunctor.IsUniversal

end CategoryTheory

/-! ### Lemma_12_12_4 (from Chap12) -/
universe vA vB uA uB

/-
Domain-style sampling:
- primary domain: cohomological `δ`-functors on abelian categories, with weak effaceability as the
  degreewise hypothesis used to prove universality.
- declarations inspected in the nearby owner API and supporting mathlib object-property API:
  `CohomologicalDeltaFunctor`,
  `CohomologicalDeltaFunctor.IsUniversal`,
  `CohomologicalDeltaFunctor.Hom`,
  `CohomologicalDeltaFunctor.universal_delta_functor_unique_up_to_unique_iso`.
- best owner abstraction in this file: `CohomologicalDeltaFunctor.IsUniversal` for the conclusion;
  the weak-effaceability assumption is source-facing data and should stay spelled out directly.
- `source-facing`: the positive-degree effaceability criterion
  `∀ n > 0, ∀ X, ∃ Y, ∃ u : X ⟶ Y, Mono u ∧ Fⁿ(u) = 0`.
- `core/canonical`: `CohomologicalDeltaFunctor.IsUniversal`.
- `bridge/view`: none needed in the public API of this lemma; the additive-functor-to-functor
  forgetful view stays internal to the theorem statement.
- primitive data vs derived API: the primitive datum is the source-level existence, for each
  positive degree and each object, of a monomorphism annihilated by that degree functor; the
  universality conclusion is the derived canonical property.
-/

namespace CategoryTheory

namespace CohomologicalDeltaFunctor

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]

/-- Lemma 12.12.4: if every positive degree of a cohomological `δ`-functor is weakly
effaceable, then the `δ`-functor is universal. -/
-- Proof sketch: extend a degree-zero morphism of `δ`-functors inductively on the degree. For the
-- inductive step, choose a monomorphism `u : X ⟶ Y` killing `F^(n+1)(u)`, use the long exact
-- sequence for `0 ⟶ X ⟶ Y ⟶ Y/X ⟶ 0` to identify `F^(n+1)(X)` with a cokernel built from degree
-- `n`, and define the next component by the universal property of that cokernel; uniqueness comes
-- from the same construction.
theorem isUniversal_of_higherDegreesWeaklyEffaceable
    (F : CohomologicalDeltaFunctor A B)
    (hF : ∀ n : ℕ, n > 0 → ∀ X : A, ∃ (Y : A) (u : X ⟶ Y), Mono u ∧ (F n).obj.map u = 0) :
    F.IsUniversal := sorry

end CohomologicalDeltaFunctor

end CategoryTheory

/-! ### Lemma_12_12_5 (from Chap12) -/
namespace CategoryTheory

/- Domain-style sampling:
- primary domain: universal cohomological `δ`-functors in an abelian-category setting.
- declarations inspected in the chapter owner API:
  `CohomologicalDeltaFunctor.Hom`,
  `CohomologicalDeltaFunctor.IsUniversal`,
  the extension-and-uniqueness clause carried by `CohomologicalDeltaFunctor.IsUniversal`,
  `CohomologicalDeltaFunctor.universal_delta_functor_unique_up_to_unique_iso`.
- `source-facing`: the uniqueness-up-to-unique-isomorphism statement for universal cohomological
  `δ`-functors with prescribed degree-zero identification.
- `core/canonical`: `CohomologicalDeltaFunctor.universal_delta_functor_unique_up_to_unique_iso`.
- `bridge/view`: none needed here, since the textbook lemma already coincides with the owner
  theorem.
- Primitive data vs derived API: the primitive data are the owner object
  `CohomologicalDeltaFunctor`, its morphisms `CohomologicalDeltaFunctor.Hom`, the universality
  predicate `CohomologicalDeltaFunctor.IsUniversal`, and the prescribed degree-zero isomorphisms;
  uniqueness up to unique isomorphism is derived API from that owner layer.
-/

/- Lemma 12.12.5: the uniqueness-up-to-unique-isomorphism statement for universal cohomological
`δ`-functors is the owner theorem
`CohomologicalDeltaFunctor.universal_delta_functor_unique_up_to_unique_iso`. -/
recall CohomologicalDeltaFunctor.universal_delta_functor_unique_up_to_unique_iso

end CategoryTheory
