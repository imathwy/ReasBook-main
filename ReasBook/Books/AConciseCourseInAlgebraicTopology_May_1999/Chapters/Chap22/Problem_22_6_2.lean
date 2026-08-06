import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

open CategoryTheory
open HomologicalComplex HomologicalComplex.HomologySequence

noncomputable section

-- Semantic recall via `lean_leansearch`: `ChainComplex.linearYonedaObj` is the canonical
-- cochain-level owner for coefficients in an abelian group, while
-- `CategoryTheory.ShortComplex.ShortExact.δ` and
-- `HomologicalComplex.HomologySequence.composableArrows₅` package the Bockstein connecting map
-- and its exact five-arrow segment.

/-- The degree-`n` cohomology object of a chain complex `X` with coefficients in `A`, realized as
the `n`th homology of the canonical cochain complex `X.linearYonedaObj ℤ A`. -/
abbrev coefficientCohomology
    (X : ChainComplex (ModuleCat ℤ) ℕ) (A : ModuleCat ℤ) (n : ℕ) : ModuleCat ℤ :=
  (X.linearYonedaObj ℤ A).homology n

/-- The cochain map induced by a coefficient homomorphism `φ : A ⟶ B`. -/
abbrev coefficientCochainMap
    (X : ChainComplex (ModuleCat ℤ) ℕ) {A B : ModuleCat ℤ} (φ : A ⟶ B) :
    X.linearYonedaObj ℤ A ⟶ X.linearYonedaObj ℤ B :=
  (HomologicalComplex.unopFunctor (ModuleCat ℤ) (ComplexShape.down ℕ)).map
    (((NatTrans.mapHomologicalComplex
      (((CategoryTheory.linearYoneda ℤ (ModuleCat ℤ)).map φ).rightOp)
      (ComplexShape.down ℕ)).app X).op)

@[simp] theorem coefficientCochainMap_id
    (X : ChainComplex (ModuleCat ℤ) ℕ) (A : ModuleCat ℤ) :
    coefficientCochainMap X (𝟙 A) = 𝟙 (X.linearYonedaObj ℤ A) := by
  ext n
  rfl

@[simp] theorem coefficientCochainMap_comp
    (X : ChainComplex (ModuleCat ℤ) ℕ) {A B C : ModuleCat ℤ}
    (φ : A ⟶ B) (ψ : B ⟶ C) :
    coefficientCochainMap X (φ ≫ ψ) =
      coefficientCochainMap X φ ≫ coefficientCochainMap X ψ := by
  ext n
  rfl

/-- Coefficient change on `X.linearYonedaObj ℤ A` is functorial in the coefficient module `A`. -/
noncomputable def coefficientCochainFunctor
    (X : ChainComplex (ModuleCat ℤ) ℕ) :
    ModuleCat ℤ ⥤ CochainComplex (ModuleCat ℤ) ℕ where
  obj A := X.linearYonedaObj ℤ A
  map φ := coefficientCochainMap X φ
  map_id A := coefficientCochainMap_id X A
  map_comp φ ψ := coefficientCochainMap_comp X φ ψ

instance coefficientCochainFunctor_preservesZeroMorphisms
    (X : ChainComplex (ModuleCat ℤ) ℕ) :
    (coefficientCochainFunctor X).PreservesZeroMorphisms where
  map_zero _ _ := by
    ext n
    rfl

/-- The short complex of cochain complexes induced from a short complex of coefficient groups. -/
noncomputable def coefficientCochainShortComplex
    (X : ChainComplex (ModuleCat ℤ) ℕ) (S : ShortComplex (ModuleCat ℤ)) :
    ShortComplex (CochainComplex (ModuleCat ℤ) ℕ) :=
  S.map (coefficientCochainFunctor X)

/-- Degree-`n` coefficient cohomology is functorial in the coefficient module. -/
noncomputable def coefficientCohomologyFunctor
    (X : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    ModuleCat ℤ ⥤ ModuleCat ℤ :=
  coefficientCochainFunctor X ⋙
    HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n

/-- Problem 22.6.2 (1): a coefficient homomorphism `φ : A ⟶ B` induces the degree-`n`
cohomology operation `coefficientCohomology X A n ⟶ coefficientCohomology X B n`. -/
abbrev coefficientCohomologyOperation
    (X : ChainComplex (ModuleCat ℤ) ℕ) {A B : ModuleCat ℤ} (φ : A ⟶ B) (n : ℕ) :
    coefficientCohomology X A n ⟶ coefficientCohomology X B n :=
  (coefficientCohomologyFunctor X n).map φ

@[simp] theorem coefficientCohomologyOperation_id
    (X : ChainComplex (ModuleCat ℤ) ℕ) (A : ModuleCat ℤ) (n : ℕ) :
    coefficientCohomologyOperation X (𝟙 A) n = 𝟙 (coefficientCohomology X A n) := by
  change (coefficientCohomologyFunctor X n).map (𝟙 A) =
    𝟙 ((coefficientCohomologyFunctor X n).obj A)
  exact (coefficientCohomologyFunctor X n).map_id A

/-- Coefficient-induced cohomology operations are functorial in the coefficient morphism. -/
@[simp] theorem coefficientCohomologyOperation_comp
    (X : ChainComplex (ModuleCat ℤ) ℕ) {A B C : ModuleCat ℤ}
    (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    coefficientCohomologyOperation X (φ ≫ ψ) n =
      coefficientCohomologyOperation X φ n ≫ coefficientCohomologyOperation X ψ n := by
  change (coefficientCohomologyFunctor X n).map (φ ≫ ψ) =
    (coefficientCohomologyFunctor X n).map φ ≫ (coefficientCohomologyFunctor X n).map ψ
  exact (coefficientCohomologyFunctor X n).map_comp φ ψ

/-- If each `X.X n` is projective, then a short exact sequence of coefficient groups induces a
short exact sequence of coefficient cochain complexes. -/
theorem coefficientCochainShortComplex_shortExact
    (X : ChainComplex (ModuleCat ℤ) ℕ) (hX : ∀ n, Projective (X.X n))
    (S : ShortComplex (ModuleCat ℤ)) (hS : S.ShortExact) :
    (coefficientCochainShortComplex X S).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  change
    ((coefficientCochainShortComplex X S).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) n)).ShortExact
  haveI : Projective (X.X n) := hX n
  haveI : Mono S.f := hS.mono_f
  haveI : Epi S.g := hS.epi_g
  refine
    { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    refine ⟨hS.exact.liftFromProjective x ?_, ?_⟩
    · simpa using hx
    · simpa using hS.exact.liftFromProjective_comp x (by simpa using hx)
  · rw [ModuleCat.mono_iff_injective]
    intro x y hxy
    exact (cancel_mono S.f).1 (by simpa using hxy)
  · rw [ModuleCat.epi_iff_surjective]
    intro x
    refine ⟨Projective.factorThru x S.g, ?_⟩
    change Projective.factorThru x S.g ≫ S.g = x
    exact Projective.factorThru_comp x S.g

/-- Problem 22.6.2 (2): a short exact sequence of coefficient groups induces the degree-`n`
Bockstein cohomology operation
`coefficientCohomology X S.X₃ n ⟶ coefficientCohomology X S.X₁ (n + 1)`. -/
abbrev bocksteinOperation
    (X : ChainComplex (ModuleCat ℤ) ℕ) (hX : ∀ n, Projective (X.X n))
    (S : ShortComplex (ModuleCat ℤ)) (hS : S.ShortExact) (n : ℕ) :
    coefficientCohomology X S.X₃ n ⟶ coefficientCohomology X S.X₁ (n + 1) :=
  (coefficientCochainShortComplex_shortExact X hX S hS).δ n (n + 1) rfl

/-- The five-arrow cohomology sequence induced by a short exact coefficient sequence. -/
abbrev bocksteinCohomologyComposableArrows₅
    (X : ChainComplex (ModuleCat ℤ) ℕ) (hX : ∀ n, Projective (X.X n))
    (S : ShortComplex (ModuleCat ℤ)) (hS : S.ShortExact) (n : ℕ) :
    ComposableArrows (ModuleCat ℤ) 5 :=
  composableArrows₅
    (coefficientCochainShortComplex_shortExact X hX S hS) n (n + 1) rfl

/-- The Bockstein operation is the third arrow in the five-arrow cohomology exact sequence
associated to the short exact coefficient sequence. -/
theorem bocksteinOperation_def
    (X : ChainComplex (ModuleCat ℤ) ℕ) (hX : ∀ n, Projective (X.X n))
    (S : ShortComplex (ModuleCat ℤ)) (hS : S.ShortExact) (n : ℕ) :
    bocksteinOperation X hX S hS n =
      (bocksteinCohomologyComposableArrows₅ X hX S hS n).map' 2 3 := rfl

/-- The five-arrow cohomology sequence induced by a short exact coefficient sequence is exact. -/
theorem bocksteinCohomologyComposableArrows₅_exact
    (X : ChainComplex (ModuleCat ℤ) ℕ) (hX : ∀ n, Projective (X.X n))
    (S : ShortComplex (ModuleCat ℤ)) (hS : S.ShortExact) (n : ℕ) :
    (bocksteinCohomologyComposableArrows₅ X hX S hS n).Exact := by
  simpa [bocksteinCohomologyComposableArrows₅] using
    composableArrows₅_exact (coefficientCochainShortComplex_shortExact X hX S hS) n (n + 1) rfl
