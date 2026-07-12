import Mathlib

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

/-- The notion appearing in Chap12 Definition 12 12 1: a cohomological `δ`-functor from `A` to `B`
consists of additive
functors `Fⁿ : A ⥤ B` for `n ≥ 0`, together with connecting morphisms attached to each short exact
sequence in `A`, such that the induced long sequence is exact and these connecting morphisms are
natural in morphisms of short exact sequences. The owner structure only uses the canonical
preadditive exactness API. -/
@[stacks 010Q]
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

/-- If a short exact row admits a section of `g`, then its connecting morphism is zero. -/
theorem δ_eq_zero_of_section (F : CohomologicalDeltaFunctor A B) {S : ShortComplex A}
    (hS : S.ShortExact) (s : S.X₃ ⟶ S.X₂) (hs : s ≫ S.g = 𝟙 S.X₃) (n : ℕ) :
    F.δ hS n = 0 := by
  calc
    F.δ hS n = (F n).obj.map (𝟙 S.X₃) ≫ F.δ hS n := by simp
    _ = (F n).obj.map (s ≫ S.g) ≫ F.δ hS n := by rw [← hs]
    _ = (F n).obj.map s ≫ ((F n).obj.map S.g ≫ F.δ hS n) := by
      simp [Functor.map_comp, Category.assoc]
    _ = 0 := by
      simp [F.map_g_comp_δ hS n]

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
/-- Chap12 Definition 12 12 1: universal cohomological `δ`-functors with the same prescribed
degree-zero term are determined up to a unique invertible morphism of `δ`-functors. -/
theorem universal_delta_functor_unique_up_to_unique_iso
    (F : A ⥤ B)
    {G H : CohomologicalDeltaFunctor A B}
    (hG_univ : IsUniversal G) (hH_univ : IsUniversal H)
    (eG : (G 0).obj ≅ F) (eH : (H 0).obj ≅ F) :
    ∃! e : G ≅ H, e.hom.app 0 = eG.hom ≫ eH.inv := by
  -- Extend the prescribed degree-zero comparison in both directions by universality.
  obtain ⟨τ, hτ0, hτ_unique⟩ := hG_univ.existsUnique_hom H (eG.hom ≫ eH.inv)
  obtain ⟨σ, hσ0, hσ_unique⟩ := hH_univ.existsUnique_hom G (eH.hom ≫ eG.inv)
  -- The forward composite has identity degree-zero component, so universality forces it to be `𝟙 G`.
  have hτσ0 : (τ ≫ σ).app 0 = 𝟙 ((G 0).obj) := by
    simp [comp_app, hτ0, hσ0, Category.assoc]
  have hτσ : τ ≫ σ = 𝟙 G := by
    obtain ⟨ρ, hρ0, hρ_unique⟩ := hG_univ.existsUnique_hom G (𝟙 ((G 0).obj))
    have hρ : ρ = 𝟙 G := by
      exact (hρ_unique (𝟙 G) (by simp [id_app])).symm
    exact (hρ_unique (τ ≫ σ) hτσ0).trans hρ
  -- The reverse composite is handled symmetrically using universality of `H`.
  have hστ0 : (σ ≫ τ).app 0 = 𝟙 ((H 0).obj) := by
    simp [comp_app, hτ0, hσ0, Category.assoc]
  have hστ : σ ≫ τ = 𝟙 H := by
    obtain ⟨ρ, hρ0, hρ_unique⟩ := hH_univ.existsUnique_hom H (𝟙 ((H 0).obj))
    have hρ : ρ = 𝟙 H := by
      exact (hρ_unique (𝟙 H) (by simp [id_app])).symm
    exact (hρ_unique (σ ≫ τ) hστ0).trans hρ
  -- Package the comparison morphisms into the unique isomorphism with the required degree-zero part.
  refine ⟨⟨τ, σ, hτσ, hστ⟩, hτ0, ?_⟩
  intro e' he'
  apply Iso.ext
  simpa using hτ_unique e'.hom he'

end CohomologicalDeltaFunctor

end CategoryTheory
