import Mathlib
import StacksProject_2024.Chap13.Definition_13_34_1
import StacksProject_2024.Chap15.«15_74_0_2»
import StacksProject_2024.Chap15.Lemma_15_92_18
import StacksProject_2024.Chap15.Lemma_15_95_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "single0" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/-- The `n`th quotient stage `(A / I^(n+1))[0]` in the ideal-power completion tower. -/
abbrev idealPowerQuotientDerivedStage (I : Ideal A) (n : ℕ) : DMod :=
  (single0).obj (ModuleCat.of A (A ⧸ I ^ (n + 1)))

/-- The transition morphism `(A / I^(n+2))[0] ⟶ (A / I^(n+1))[0]` in the ideal-power quotient
tower. -/
abbrev idealPowerQuotientDerivedStep (I : Ideal A) (n : ℕ) :
    idealPowerQuotientDerivedStage I (n + 1) ⟶
      idealPowerQuotientDerivedStage I n :=
  (single0).map
    (ModuleCat.ofHom
      ((Ideal.Quotient.factorₐ A
          (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).toLinearMap))

/-- The inverse system `((A / I^(n+1))[0])_n` in `D(A)`. -/
abbrev idealPowerQuotientDerivedInverseSystem (I : Ideal A) : ℕᵒᵖ ⥤ DMod :=
  Functor.ofOpSequence (idealPowerQuotientDerivedStep I)

/-- The inverse system `(K \otimes_A^{\mathbf L} (A / I^(n+1))[0])_n` used in derived completion
by the powers of `I`. -/
abbrev idealPowerQuotientTensorDerivedInverseSystem
    (I : Ideal A) (K : DMod) : ℕᵒᵖ ⥤ DMod :=
  idealPowerQuotientDerivedInverseSystem I ⋙ derivedTensorProduct K

/-- The canonical map from `K` to the `n`th quotient-tensor stage
`K \otimes_A^{\mathbf L} (A / I^(n+1))[0]`. -/
abbrev idealPowerQuotientTensorToStage
    (I : Ideal A) (K : DMod) (n : ℕ) :
    K ⟶ (idealPowerQuotientTensorDerivedInverseSystem I K).obj (op n) :=
  (singleZeroDerivedTensorIso K).inv ≫
    (derivedTensorProduct K).map
      ((single0).map
        (ModuleCat.ofHom ((Ideal.Quotient.mkₐ A (I ^ (n + 1))).toLinearMap)))

/-- A morphism `c : K ⟶ L` is the canonical comparison from `K` to a chosen derived limit of the
ideal-power quotient tensor tower if `L` sits in the Milnor triangle of that tower and the stage
projections recover the canonical quotient-stage maps
`K ⟶ K \otimes_A^{\mathbf L} (A / I^(n+1))[0]`. -/
def IsDerivedCompletionIdealPowerQuotientTensorComparison
    (I : Ideal A) (K L : DMod) (c : K ⟶ L) : Prop :=
  ∃ _ : HasProduct (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)),
    ∃ ι :
        L ⟶ ∏ᶜ inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K),
      HasMilnorTriangle.WithMap (idealPowerQuotientTensorDerivedInverseSystem I K) ι ∧
        ∀ n : ℕ,
          c ≫ ι ≫
              Pi.π
                (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K))
                n =
            idealPowerQuotientTensorToStage I K n

/-- A quotient-tower derived-completion comparison presents its target as a derived limit of the
ideal-power quotient tensor tower. -/
theorem IsDerivedCompletionIdealPowerQuotientTensorComparison.isDerivedLimit
    {I : Ideal A} {K L : DMod} {c : K ⟶ L}
    (hc : IsDerivedCompletionIdealPowerQuotientTensorComparison I K L c) :
    IsDerivedLimit (idealPowerQuotientTensorDerivedInverseSystem I K) L := by
  rcases hc with ⟨hP, _, hι, _⟩
  let _ : HasProduct (inverseSystemFamily (idealPowerQuotientTensorDerivedInverseSystem I K)) := hP
  exact ⟨hP, hι.hasMilnorTriangle (idealPowerQuotientTensorDerivedInverseSystem I K)⟩

end

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Proposition 15.95.2:
- primary domain: derived completion in `D(A)` via the canonical comparison
  `K ⟶ R\!\varprojlim (K \otimes_A^{\mathbf L} (A / I^(n+1))[0])`;
- sampled owner declarations:
  `IsDerivedCompletionKoszulPowerTensorComparison`,
  `derivedLimitOfKoszulPowerTensorFunctorAdjunction`,
  `derivedCompleteObjectProperty`,
  `exists_pro_isomorphism_derived_completion_koszul_powers_to_power_quotients`;
- best owner abstraction: this proposition is a `bridge/view` statement. Its source-facing owner is
  the quotient-tower comparison predicate below, while the canonical target owner remains the
  adjunction with the inclusion of the full subcategory of derived-complete objects;
- primitive vs. derived:
  primitive data are the quotient tower, the functor `L`, the natural transformation `η`, and the
  fact that each `η.app K` is the canonical quotient-tower comparison map;
  the derived API is the induced adjunction `L ⊣ ι` and its consequence `L.IsLeftAdjoint`.

Source/core/bridge triage:
- `source-facing`: the quotient-tower comparison map formalizing
  `K ⟶ R\!\varprojlim (K \otimes_A^{\mathbf L} (A / I^(n+1))[0])`;
- `core/canonical`: `DerivedCategory.derivedCompleteObjectProperty I`, its inclusion functor, and
  `Adjunction`;
- `bridge/view`: the passage from the quotient-tower comparison to the powered-Koszul comparison of
  Lemma `15.92.18`, using the pro-isomorphism of Lemma `15.95.1`. -/

-- Proof sketch: choose generators `f` of `I`. Proposition `15.95.1` identifies the quotient
-- tower with the powered Koszul tower up to pro-isomorphism. Transport the supplied quotient-tower
-- comparison along this pro-isomorphism to obtain the owner predicate
-- `IsDerivedCompletionKoszulPowerTensorComparison f`, and then apply
-- `derivedLimitOfKoszulPowerTensorFunctorAdjunction`. The isomorphism criterion for objects
-- already derived complete is the corresponding quotient-tower reformulation of Lemma `15.92.17`.
/-- For a Noetherian ring `A` and an ideal `I ⊆ A`, a canonical comparison
`c : K ⟶ L` from `K` to a chosen derived limit of the quotient tower
`(K \otimes_A^{\mathbf L} (A / I^(n+1))[0])_n` is an isomorphism exactly when `K` is derived
complete with respect to `I`. This is the quotient-tower form of the powered-Koszul criterion from
Lemma `15.92.17`. -/
theorem isDerivedCompleteWithRespectTo_iff_isIso_derivedIdealPowerQuotientCompletionComparison
    [IsNoetherianRing A] (I : Ideal A) {K L : DMod} (c : K ⟶ L)
    (hc : IsDerivedCompletionIdealPowerQuotientTensorComparison I K L c) :
    K.IsDerivedCompleteWithRespectTo I ↔ IsIso c := by
  sorry

-- Proof sketch: choose generators of `I`, transport the quotient-tower comparison to the
-- powered-Koszul comparison through the pro-isomorphism of Lemma `15.95.1`, and apply the
-- canonical adjunction owner `derivedLimitOfKoszulPowerTensorFunctorAdjunction`.
/-- Proposition 15.95.2: let `A` be a Noetherian ring and let `I ⊆ A` be an ideal. Let
`L : D(A) ⥤ D_{comp}(A, I)` be a functor to the full subcategory of objects derived complete with
respect to `I`, and let `η : 𝟭 ⟶ L ⋙ ι` be a natural transformation such that each component
`η.app K` is the canonical comparison map
`K ⟶ R\!\varprojlim (K \otimes_A^{\mathbf L} (A / I^(n+1))[0])` in the source-facing sense of
`IsDerivedCompletionIdealPowerQuotientTensorComparison`. Then `L` is left adjoint to the
inclusion `ι : D_{comp}(A, I) ⥤ D(A)`. The proposition-level `L.IsLeftAdjoint` statement is only
the derived consequence recorded below. -/
noncomputable def derivedLimitOfIdealPowerQuotientTensorFunctorAdjunction
    [IsNoetherianRing A] (I : Ideal A)
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionIdealPowerQuotientTensorComparison I K (L.obj K).obj (η.app K)) :
    L ⊣ (DerivedCategory.derivedCompleteObjectProperty I).ι := by
  sorry

/-- Derived consequence of Proposition `15.95.2`: the quotient-tower derived-limit functor is a
left adjoint. The source-facing content is the adjunction
`derivedLimitOfIdealPowerQuotientTensorFunctorAdjunction`. -/
theorem derivedLimitOfIdealPowerQuotientTensorFunctor_isLeftAdjoint
    [IsNoetherianRing A] (I : Ideal A)
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionIdealPowerQuotientTensorComparison I K (L.obj K).obj (η.app K)) :
    L.IsLeftAdjoint :=
  (derivedLimitOfIdealPowerQuotientTensorFunctorAdjunction I L η hη).isLeftAdjoint

end
