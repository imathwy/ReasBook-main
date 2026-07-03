import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_95_1 (from Chap15) -/
open CategoryTheory
open SequentialProObjectMorphismRep

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A] {r : ℕ}

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "single0" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/- Domain-style sampling for Lemma 15.95.1:
- primary domain: sequential pro-object comparison between the powered Koszul tower in `D(A)` and
  the degree-zero image of the powered quotient tower from Situation `15.92.15`;
- sampled owner declarations:
  `koszulPowerQuotientStage`,
  `koszulPowerQuotientInverseSystem`,
  `derivedCompletionKoszulPowersDerivedInverseSystem`,
  `SequentialProObjectMorphismRep.toProObjectHom`;
- best owner abstraction: the quotient side should reuse the source-facing module-level owner
  `koszulPowerQuotientInverseSystem` and pass to `D(A)` by whiskering with the canonical degree-zero
  single functor, while the comparison itself should be expressed through a sequential
  representative together with the induced owner-level morphism of pro-objects
  `a.toProObjectHom`;
- primitive data: the powered quotient modules `A / (f_1^(n+1), \ldots, f_r^(n+1))` from
  Situation `15.92.15`;
- derived API: their images in `D(A)` and the resulting pro-isomorphism statement.

Source/core/bridge triage:
- `source-facing`: the pro-isomorphism between the powered Koszul tower and the quotient tower;
- `core/canonical`: `koszulPowerQuotientInverseSystem`,
  `derivedCompletionKoszulPowersDerivedInverseSystem`, `SequentialProObjectMorphismRep`, and
  `SequentialProObjectMorphismRep.toProObjectHom`;
- `bridge/view`: the degree-zero single-functor realization of the quotient tower inside `D(A)`. -/

/-- The `n`th quotient stage `A / (f_1^(n+1), \ldots, f_r^(n+1))`, viewed in degree `0` in
`D(A)`. -/
abbrev derivedCompletionPowerQuotientDerivedStage
    (f : Fin r → A) (n : ℕ) : DMod :=
  (single0).obj (koszulPowerQuotientStage f n)

/-- The inverse system of quotient objects
`(A / (f_1^(n+1), \ldots, f_r^(n+1)))[0]` in `D(A)`, obtained by applying the degree-zero single
functor to the owner tower `koszulPowerQuotientInverseSystem f` from Situation `15.92.15`. -/
abbrev derivedCompletionPowerQuotientDerivedInverseSystem
    (f : Fin r → A) : ℕᵒᵖ ⥤ DMod :=
  koszulPowerQuotientInverseSystem f ⋙ single0

end

end CategoryTheory

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {r : ℕ}

local notation "DMod" => DerivedCategory (ModuleCat A)

-- Proof sketch: for each `n`, the powered Koszul complex `K_n^•` fits into the canonical
-- distinguished triangle whose degree-zero term is the quotient `A/(f_1^(n+1), …, f_r^(n+1))`.
-- By the pro-truncation criterion from the derived-category references cited in the textbook, it
-- suffices to show that the negative truncation tower is pro-zero; for bounded powered Koszul
-- complexes over a Noetherian ring, this reduces to eventual vanishing of the negative cohomology
-- transition maps, which follows from Artin-Rees together with the annihilation statement of
-- Lemma `15.28.6`.
/-- Lemma 15.95.1: if `A` is Noetherian, then the powered Koszul tower
`(K(A; f_1^(n+1), \ldots, f_r^(n+1)))_n` and the quotient tower
`(A / (f_1^(n+1), \ldots, f_r^(n+1)))[0]_n`, viewed as sequential pro-objects of `D(A)`, are
isomorphic. This is the item-file indexing convention in which stage `0` corresponds to the
textbook stage `n = 1`. -/
theorem exists_pro_isomorphism_derived_completion_koszul_powers_to_power_quotients
    (f : Fin r → A) :
    ∃ a :
        SequentialProObjectMorphismRep
          (derivedCompletionKoszulPowersDerivedInverseSystem f)
          (derivedCompletionPowerQuotientDerivedInverseSystem f),
      IsIso a.toProObjectHom := sorry

end

/-! ### Proposition_15_95_2 (from Chap15) -/
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

/-! ### Lemma_15_95_3 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.SequentialInverseSystem
open ModuleCat
open AdicCompletion
open Opposite

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "DModMinus" => boundedAboveDerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "single₀" => (ModuleCat.single0Functor : ModuleCat A ⥤ DMod)

/- Domain-style sampling for Lemma 15.95.3:
- primary domain: derived `I`-adic completion in `D(A)` and the Milnor short exact sequence for
  the quotient-tensor inverse system `(K ⊗_A^L (A / I^(n+1))[0])_n`;
- sampled owner declarations:
  `DerivedCategory.derivedCompletionOf`,
  `CategoryTheory.derivedLimit_cohomology_shortExact`,
  `CategoryTheory.IsDerivedCompletionIdealPowerQuotientTensorComparison`,
  `idealPowerQuotientTorInverseSystem`,
  `SequentialInverseSystem.shift`;
- best owner abstraction: the public statements should be source-facing short exact sequences on
  the canonical owner `K^∧[I, hI]`; the chosen quotient-tower presentation is bridge/view data
  internal to the proof, owned by
  `IsDerivedCompletionIdealPowerQuotientTensorComparison`, while the module case should expose the
  source-facing Tor tower through the canonical shifted owner
  `(idealPowerQuotientTorInverseSystem I M p).shift 1`;
- primitive vs. derived:
  primitive data are the ideal `I`, the object `K` or module `M`, and the canonical derived
  completion owner `K^∧[I, hI]`;
  derived API is the Milnor short exact sequence, specialized for modules to the canonical Tor
  tower together with the explicit shifted bridge from the quotient-tensor homology tower, and for
  bounded-above objects to the canonical quotient-tensor cohomology tower.

Source/core/bridge triage:
- `source-facing`: the two short exact sequence theorems below for `M^∧` and `K^∧`;
- `core/canonical`: `DerivedCategory.derivedCompletionOf`,
  `CategoryTheory.derivedLimit_cohomology_shortExact`, and
  `CategoryTheory.IsDerivedCompletionIdealPowerQuotientTensorComparison`;
- `bridge/view`: any chosen Milnor-triangle or stagewise identification used to compare the
  canonical owner with the quotient tower. -/

private theorem cohomology_shortExact_of_derivedIdealPowerQuotientCompletionComparison
    [IsNoetherianRing A] (I : Ideal A)
    {K L : DMod} {c : K ⟶ L}
    (hc : IsDerivedCompletionIdealPowerQuotientTensorComparison I K L c)
    (i : ℕ) :
    ∃ (ι :
        firstDerivedLimit
            (idealPowerQuotientTensorDerivedInverseSystem I K ⋙ H (-(i : ℤ) - 1)) ⟶
          (H (-(i : ℤ))).obj L)
      (π :
        (H (-(i : ℤ))).obj L ⟶
          limit (idealPowerQuotientTensorDerivedInverseSystem I K ⋙ H (-(i : ℤ))))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  simpa using
    derivedLimit_cohomology_shortExact
      (idealPowerQuotientTensorDerivedInverseSystem I K) L hc.isDerivedLimit (-(i : ℤ))

section

variable (I : Ideal A)
variable (M : Type u) [AddCommGroup M] [Module A M]

/-- Bridge/view companion for Lemma `15.95.3`: for a module `M`, the cohomology tower of the
quotient-tensor inverse system
`((single₀.obj M) \otimes_A^{\mathbf L} (A / I^(n+1))[0])_n`
in degree `-p` is canonically the shifted Tor tower
`(Tor_p^A(M, A / I^(n+1)))_n`, realized by the chapter owner
`(idealPowerQuotientTorInverseSystem I M p).shift 1`. -/
theorem idealPowerQuotientTensorSingle_homology_eq_shiftedTor
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] (p : ℕ) :
    idealPowerQuotientTensorDerivedInverseSystem I ((single₀).obj (ModuleCat.of A M)) ⋙
        H (-(p : ℤ)) =
      (idealPowerQuotientTorInverseSystem I M p).shift 1 := by
  sorry

private theorem moduleDerivedCompletion_cohomology_shortExact_of_comparison
    [IsNoetherianRing A] (I : Ideal A)
    (M : Type u) [AddCommGroup M] [Module A M]
    (i : ℕ)
    (hc :
      IsDerivedCompletionIdealPowerQuotientTensorComparison I
        ((single₀).obj (ModuleCat.of A M))
        (((single₀).obj (ModuleCat.of A M))^∧[I, I.fg_of_isNoetherianRing])
        (DerivedCategory.toDerivedCompletion I I.fg_of_isNoetherianRing
          ((single₀).obj (ModuleCat.of A M)))) :
    ∃ (ι :
        ((idealPowerQuotientTorInverseSystem I M (i + 1)).shift 1).firstDerivedLimit ⟶
          (H (-(i : ℤ))).obj
            (((single₀).obj (ModuleCat.of A M))^∧[I, I.fg_of_isNoetherianRing]))
      (π :
        (H (-(i : ℤ))).obj
            (((single₀).obj (ModuleCat.of A M))^∧[I, I.fg_of_isNoetherianRing]) ⟶
          limit ((idealPowerQuotientTorInverseSystem I M i).shift 1))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  have hTorSucc :
      idealPowerQuotientTensorDerivedInverseSystem I ((single₀).obj (ModuleCat.of A M)) ⋙
          H (-(i : ℤ) - 1) =
        (idealPowerQuotientTorInverseSystem I M (i + 1)).shift 1 := by
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      idealPowerQuotientTensorSingle_homology_eq_shiftedTor I M (i + 1)
  have hTor :
      idealPowerQuotientTensorDerivedInverseSystem I ((single₀).obj (ModuleCat.of A M)) ⋙
          H (-(i : ℤ)) =
        (idealPowerQuotientTorInverseSystem I M i).shift 1 := by
    simpa using idealPowerQuotientTensorSingle_homology_eq_shiftedTor I M i
  simpa [firstDerivedLimit] using
    (hTorSucc ▸ hTor ▸
      cohomology_shortExact_of_derivedIdealPowerQuotientCompletionComparison I hc i)

end

section

variable [IsNoetherianRing A]
variable (I : Ideal A)
variable (M : Type u) [AddCommGroup M] [Module A M]

/-- Lemma 15.95.3: for an `A`-module `M`, the canonical derived `I`-adic completion
`((single₀).obj (ModuleCat.of A M))^∧[I, I.fg_of_isNoetherianRing]` fits into the short exact
sequence
`0 → R^1 \!\varprojlim Tor_{i + 1}^A(M, A / I^(n+1)) → H^{-i}(M^∧) →
\varprojlim Tor_i^A(M, A / I^(n+1)) → 0`, expressed on the source-facing tower by the shifted
chapter owner `(idealPowerQuotientTorInverseSystem I M p).shift 1`, whose stage `n` is
`Tor_p^A(M, A / I^(n+1))`. -/
theorem derivedCompletionOfModule_cohomology_shortExact
    (i : ℕ) :
    ∃ (ι :
        ((idealPowerQuotientTorInverseSystem I M (i + 1)).shift 1).firstDerivedLimit ⟶
          (H (-(i : ℤ))).obj
            (((single₀).obj (ModuleCat.of A M))^∧[I, I.fg_of_isNoetherianRing]))
      (π :
        (H (-(i : ℤ))).obj
            (((single₀).obj (ModuleCat.of A M))^∧[I, I.fg_of_isNoetherianRing]) ⟶
          limit ((idealPowerQuotientTorInverseSystem I M i).shift 1))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  let c :
      (single₀).obj (ModuleCat.of A M) ⟶
        ((single₀).obj (ModuleCat.of A M))^∧[I, I.fg_of_isNoetherianRing] :=
    DerivedCategory.toDerivedCompletion I I.fg_of_isNoetherianRing
      ((single₀).obj (ModuleCat.of A M))
  have hc :
      IsDerivedCompletionIdealPowerQuotientTensorComparison I
        ((single₀).obj (ModuleCat.of A M))
        (((single₀).obj (ModuleCat.of A M))^∧[I, I.fg_of_isNoetherianRing])
        c := by
    sorry
  simpa [c] using
    moduleDerivedCompletion_cohomology_shortExact_of_comparison I M i hc

end

section

variable [IsNoetherianRing A]

/-- The bounded-above analogue of Lemma `15.95.3`: for `K ∈ D^-(A)`, the canonical derived
completion `(K.obj)^∧[I, I.fg_of_isNoetherianRing]` fits into the Milnor short exact sequence
attached to the quotient-tensor tower
`(K.obj ⊗_A^{\mathbf L} (A / I^(n+1))[0])_n`. -/
theorem boundedAboveDerivedCompletion_cohomology_shortExact
    (I : Ideal A) (K : DModMinus) (i : ℕ) :
    ∃ (ι :
        firstDerivedLimit
            (idealPowerQuotientTensorDerivedInverseSystem I K.obj ⋙ H (-(i : ℤ) - 1)) ⟶
          (H (-(i : ℤ))).obj ((K.obj)^∧[I, I.fg_of_isNoetherianRing]))
      (π :
        (H (-(i : ℤ))).obj ((K.obj)^∧[I, I.fg_of_isNoetherianRing]) ⟶
          limit (idealPowerQuotientTensorDerivedInverseSystem I K.obj ⋙ H (-(i : ℤ))))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  let c :
      K.obj ⟶ (K.obj)^∧[I, I.fg_of_isNoetherianRing] :=
    DerivedCategory.toDerivedCompletion I I.fg_of_isNoetherianRing K.obj
  have hc :
      IsDerivedCompletionIdealPowerQuotientTensorComparison I
        K.obj ((K.obj)^∧[I, I.fg_of_isNoetherianRing]) c := by
    sorry
  simpa [c] using
    cohomology_shortExact_of_derivedIdealPowerQuotientCompletionComparison I hc i

end

end

/-! ### Lemma_15_95_4 (from Chap15) -/
noncomputable section

open CategoryTheory
open AdicCompletion
open scoped CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace DerivedCategory

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)

/- Domain-style sampling for Lemma 15.95.4:
- primary domain: cohomology of derived `I`-adic completion in `DerivedCategory (ModuleCat A)`;
- sampled owner declarations:
  `DerivedCategory.derivedCompletionOf`,
  `DerivedCategory.homologyFunctor`,
  `DerivedCategory.isDerivedCompleteWithRespectTo_iff_mem_derivedCategoryCohomologyInProperty`,
  `AdicCompletion`,
  `AdicCompletion.mapToComplete`,
  `Ideal.fg_of_isNoetherianRing`;
- best owner abstraction: this is a `source-facing` comparison theorem whose core owners are the
  chapter derived-completion object `K^∧[I, hI]`, the chapter cohomology owner `H^i`, and the module-side
  completion owner `AdicCompletion I`;
- primitive vs. derived:
  primitive data are the ideal `I`, the derived object `K`, the degree `n`, and the finite
  cohomology hypothesis on `K`;
  derived API is the canonical comparison morphism from
  `AdicCompletion I (H^n(K))` to `H^n(K^∧[I, hI])` and the resulting isomorphism. -/

private theorem homology_derivedCompletionOf_isDerivedComplete
    (I : Ideal A) (K : DMod) (n : ℤ) :
    ((H n).obj (K^∧[I, I.fg_of_isNoetherianRing])).IsDerivedCompleteWithRespectTo I := by
  have hcomplete :
      (K^∧[I, I.fg_of_isNoetherianRing]).IsDerivedCompleteWithRespectTo I :=
    derivedCompletionOf_isDerivedComplete I I.fg_of_isNoetherianRing K
  exact
    (isDerivedCompleteWithRespectTo_iff_mem_derivedCategoryCohomologyInProperty I
      (K^∧[I, I.fg_of_isNoetherianRing])).mp hcomplete n

/- The target module of the canonical completion comparison is `I`-adically complete. This is the
module-level owner needed to define the comparison map via `AdicCompletion.mapToComplete`. -/
theorem isAdicComplete_homology_derivedCompletionOf
    (I : Ideal A) (K : DMod) (n : ℤ)
    (hK : ∀ i : ℤ, Module.Finite A ((H i).obj K)) :
    IsAdicComplete I ((H n).obj (K^∧[I, I.fg_of_isNoetherianRing])) := by
  sorry

/-- The canonical comparison morphism
`(H^n(K))^∧ → H^n(K^∧)` from ordinary `I`-adic completion to the `n`th cohomology of derived
completion. -/
noncomputable abbrev homologyCompletionComparison
    (I : Ideal A) (K : DMod) (n : ℤ)
    (hK : ∀ i : ℤ, Module.Finite A ((H i).obj K)) :
    ModuleCat.of A (AdicCompletion I ((H n).obj K)) ⟶
      (H n).obj (K^∧[I, I.fg_of_isNoetherianRing]) :=
  let _ :
      IsAdicComplete I ((H n).obj (K^∧[I, I.fg_of_isNoetherianRing])) :=
    isAdicComplete_homology_derivedCompletionOf I K n hK
  ModuleCat.ofHom <|
    mapToComplete I ((H n).map (toDerivedCompletion I I.fg_of_isNoetherianRing K)).hom

-- Proof sketch: truncate `K` above a fixed degree `n`, use pseudo-coherence of the truncation from
-- the finite-cohomology hypothesis over the Noetherian ring `A`, represent it by a bounded-above
-- finite free complex, and compute derived completion termwise. Exactness of `I`-adic completion
-- on finite modules identifies the resulting degree-`n` cohomology with the completion of
-- `H^n(K)`, and the finite cohomological dimension of derived completion removes the truncation.
/-- Lemma 15.95.4: if `A` is Noetherian, `I ⊆ A` is an ideal, and every cohomology module of
`K ∈ D(A)` is finite, then the canonical comparison morphism
`(H^n(K))^∧ → H^n(K^∧[I, hI])` is an isomorphism. -/
theorem homologyCompletionComparison_isIso
    (I : Ideal A) (K : DMod) (n : ℤ)
    (hK : ∀ i : ℤ, Module.Finite A ((H i).obj K)) :
    IsIso (homologyCompletionComparison I K n hK) := by
  sorry

/-- Lemma 15.95.4, isomorphism form: if every cohomology module of `K` is finite, then
`H^n(K^∧[I, hI])` is canonically isomorphic to the ordinary `I`-adic completion of `H^n(K)`. -/
noncomputable abbrev homology_derivedCompletionOf_iso_adicCompletion
    (I : Ideal A) (K : DMod) (n : ℤ)
    (hK : ∀ i : ℤ, Module.Finite A ((H i).obj K)) :
    (H n).obj (K^∧[I, I.fg_of_isNoetherianRing]) ≅
      ModuleCat.of A (AdicCompletion I ((H n).obj K)) :=
  let _ := homologyCompletionComparison_isIso I K n hK
  (asIso (homologyCompletionComparison I K n hK)).symm

end

end DerivedCategory

/-! ### Lemma_15_95_5 (from Chap15) -/
noncomputable section

universe u

section

variable {A : Type u} [CommRing A]
variable {I : Ideal A} {M : ModuleCat A}

namespace ModuleCat

/-
Domain-style sampling for Lemma 15.95.5:
- primary domain: derived completeness, adic completeness, and finite generation of modules over
  the completed ring `AdicCompletion I A`;
- sampled owner declarations:
  `IsAdicComplete`,
  `ModuleCat.isAdicComplete_iff_isDerivedCompleteWithRespectTo_and_isHausdorff`,
  `moduleFinite_of_finite_quotient_of_isHausdorff`,
  `AdicCompletion.module`,
  `AdicCompletion.ofLinearEquiv`;
- best owner abstraction: this is a `source-facing` theorem on `M`; the core owners are
  `IsAdicComplete I M` and `Module.Finite (AdicCompletion I A) M`, while the completion-side
  statement for `AdicCompletion I M` is only a `bridge/view`;
- primitive vs. derived:
  primitive data are the ideal `I`, the module `M`, the derived-completeness hypothesis, and the
  finite quotient `M / I M`;
  derived API is the canonical `Module (AdicCompletion I A) M` instance under
  `IsAdicComplete I M`, together with the completion-side finiteness conclusion for
  `AdicCompletion I M`.
-/

open AdicCompletion

namespace IsAdicComplete

-- Transport the canonical `AdicCompletion I A`-action on `AdicCompletion I M` across
-- `AdicCompletion.ofLinearEquiv I M`.
noncomputable instance [IsAdicComplete I M] :
    Module (AdicCompletion I A) M :=
  Module.compHom M <|
    ((ofLinearEquiv I M).symm.conjRingEquiv.toRingHom).comp
      (Module.toModuleEnd A (AdicCompletion I M))

-- Proof sketch: equip `M` with its canonical `AdicCompletion I A`-module structure from `hM`,
-- compare it with the canonical completion module `AdicCompletion I M` using
-- `AdicCompletion.ofLinearEquiv I M`, and apply the owner-facing finiteness criterion from
-- Lemma `10.96.12`.
/-- If `M` is already `I`-adically complete, then `M`, equipped with its canonical
`AdicCompletion I A`-module structure, is finite as soon as `M / I M` is finite over `A / I`. -/
theorem moduleFinite_over_adicCompletion_of_finite_quotient
    [IsAdicComplete I M]
    [Module.Finite (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M))] :
    Module.Finite (AdicCompletion I A) M := sorry

end IsAdicComplete

section

variable [IsNoetherianRing A]

-- Proof sketch: use Proposition `15.92.5` to identify adic completeness with derived
-- completeness plus `I`-adic separatedness, prove the separatedness hypothesis from the
-- Noetherian finiteness input, and conclude by Chapter `10`.
/-- Under the hypotheses of Lemma `15.95.5`, the module `M` is `I`-adically complete. -/
theorem isAdicComplete_of_isDerivedComplete_of_finite_quotient
    (hM : M.IsDerivedCompleteWithRespectTo I)
    [Module.Finite (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M))] :
    IsAdicComplete I M := sorry

-- Proof sketch: combine the completeness bridge above with the owner theorem in the
-- `IsAdicComplete` namespace.
/-- Lemma 15.95.5: if `M` is derived complete with respect to `I` and `M / I M` is finite over
`A / I`, then `M`, equipped with its canonical `AdicCompletion I A`-module structure, is a finite
module over the completed ring `AdicCompletion I A`. -/
theorem moduleFinite_over_adicCompletion_of_isDerivedComplete_of_finite_quotient
    (hM : M.IsDerivedCompleteWithRespectTo I)
    [Module.Finite (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M))] :
    let _ : IsAdicComplete I M :=
      isAdicComplete_of_isDerivedComplete_of_finite_quotient hM
    Module.Finite (AdicCompletion I A) M := by
  let _ : IsAdicComplete I M :=
    isAdicComplete_of_isDerivedComplete_of_finite_quotient hM
  exact IsAdicComplete.moduleFinite_over_adicCompletion_of_finite_quotient

-- Proof sketch: first apply Lemma `15.95.5` to `M`, then transport finite generation across the
-- canonical identification `AdicCompletion.ofLinearEquiv I M`.
/-- Completion-side companion to Lemma `15.95.5`: under the same hypotheses,
`AdicCompletion I M` is a finite module over `AdicCompletion I A`. -/
theorem moduleFinite_adicCompletion_of_isDerivedComplete_of_finite_quotient
    (hM : M.IsDerivedCompleteWithRespectTo I)
    [Module.Finite (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M))] :
    Module.Finite (AdicCompletion I A) (AdicCompletion I M) := sorry

end

end ModuleCat

end

/-! ### Lemma_15_95_6 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AdicCompletion
open scoped TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "single₀" => (ModuleCat.single0Functor : ModuleCat A ⥤ DMod)
local notation "Away" => LocalizedModule.Away

/- Domain-style sampling for Lemma 15.95.6:
- primary domain: derived `I`-adic completion of degree-zero objects in `D(A)`, together with the
  module-theoretic tensor and localization realizations that feed the source text;
- sampled owner declarations:
  `ModuleCat.single0Functor`,
  `singleFunctorIso_of_isGE_of_isLE`,
  `derivedCompletionOfModule_cohomology_shortExact`,
  `DerivedCategory.homology_derivedCompletionOf_iso_adicCompletion`,
  `AdicCompletion`,
  `tor_eventually_zero_map_quotient_pow`,
  `LocalizedModule.equivTensorProduct`;
- best owner abstraction: the main public statements should identify the canonical derived
  completion object `((single₀).obj X)^∧[I, I.fg_of_isNoetherianRing]` itself with the canonical
  degree-zero owner `(single₀).obj (AdicCompletion I X)` in `D(A)`, formalized propositionally as
  `IsIsomorphic` because this file does not yet expose a canonical comparison morphism; the
  degree-zero comparison and off-zero vanishing remain companion API used to build that
  identification through `singleFunctorIso_of_isGE_of_isLE`; the Milnor short exact sequence of
  Lemma `15.95.3` is the core owner input, while the tensor-product/localization descriptions
  remain bridge/view input to the proof;
- primitive vs. derived:
  primitive data are the ideal `I`, the finite module `M`, and the auxiliary flat or localized
  module appearing in the two source statements;
  derived API is the source-facing identification of the actual derived-completion object with the
  degree-zero object on `AdicCompletion I X`, together with degree-zero comparison and off-zero
  vanishing as supporting companions.

Source/core/bridge triage:
- `source-facing`: the two derived-category completion isomorphisms below for `M ⊗[A] N` and
  `Away f M`;
- `core/canonical`: `ModuleCat.single0Functor`, `DerivedCategory.derivedCompletionOf`, the
  Milnor short exact sequence owner `derivedCompletionOfModule_cohomology_shortExact`,
  `singleFunctorIso_of_isGE_of_isLE`, and the module-side completion owner `AdicCompletion`;
- `bridge/view`: the tensor-product model and the localization/tensor comparison
  `LocalizedModule.equivTensorProduct`. -/

-- Proof sketch: apply Lemma `15.95.3` to `X := M ⊗[A] N`. Since `N` is flat, the Tor towers
-- `Tor_i^A(X, A / I^(n+1))` identify with `Tor_i^A(M, A / I^(n+1)) ⊗[A] N`, so Lemma `15.27.3`
-- makes them pro-zero for `i > 0`. The `i = 0` term is the usual quotient tower
-- `(M ⊗[A] N) / I^(n+1)(M ⊗[A] N)`.
/-- Degree-zero companion for Lemma `15.95.6 (1)`: if `M` is finite and `N` is flat, then the
zero-th cohomology of the derived completion of `(M ⊗[A] N)[0]` is isomorphic to the ordinary
`I`-adic completion of `M ⊗[A] N`. This is the degree-zero input used to build the full
derived-object identification in `tensor_finite_flat_derivedCompletion_usual_adicCompletion`. -/
theorem tensor_finite_flat_homology_zero_derivedCompletion_isomorphic_adicCompletion
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (N : Type u) [AddCommGroup N] [Module A N] [Module.Flat A N] :
    IsIsomorphic
      ((H 0).obj
        (((single₀).obj (ModuleCat.of A (M ⊗[A] N)))^∧[I, I.fg_of_isNoetherianRing]))
      (ModuleCat.of A (AdicCompletion I (M ⊗[A] N))) := by
  sorry

-- Proof sketch: for `X = M ⊗[A] N`, flatness of `N` identifies the tower
-- `Tor_i^A(X, A / I^(n + 1))` with `Tor_i^A(M, A / I^(n + 1)) ⊗[A] N`. Lemma `15.27.3` makes the
-- positive-degree Tor towers pro-zero, so Lemma `15.95.3` yields that the derived `I`-adic
-- completion of `X[0]` has no nonzero cohomology outside degree `0`. This off-zero vanishing,
-- together with
-- `tensor_finite_flat_homology_zero_derivedCompletion_isomorphic_adicCompletion`, supplies the
-- proposition-level
-- derived-category isomorphism in `tensor_finite_flat_derivedCompletion_usual_adicCompletion`.
/-- Off-zero vanishing companion for Lemma `15.95.6 (1)`: if `M` is finite and `N` is flat, then
the derived completion of `(M ⊗[A] N)[0]` has zero cohomology in every degree `n ≠ 0`. Together
with `tensor_finite_flat_homology_zero_derivedCompletion_isomorphic_adicCompletion`, this yields
the full derived-object identification with the degree-zero object on the ordinary completion. -/
theorem tensor_finite_flat_homology_derivedCompletion_isZero_of_ne_zero
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (N : Type u) [AddCommGroup N] [Module A N] [Module.Flat A N] (n : ℤ) (hn : n ≠ 0) :
      IsZero ((H n).obj
        (((single₀).obj (ModuleCat.of A (M ⊗[A] N)))^∧[I, I.fg_of_isNoetherianRing])) := by
  sorry

-- Proof sketch: combine the degree-zero comparison
-- `tensor_finite_flat_homology_zero_derivedCompletion_isomorphic_adicCompletion` with the off-zero
-- vanishing in `tensor_finite_flat_homology_derivedCompletion_isZero_of_ne_zero` to obtain the
-- canonical bounds `IsGE 0` and `IsLE 0`, then identify the resulting single-degree object with
-- the ordinary completion.
/-- Lemma 15.95.6 (1): if `I` is an ideal in a Noetherian ring `A`, `M` is a finite `A`-module,
and `N` is a flat `A`-module, then the derived `I`-adic completion of `M ⊗[A] N`, viewed as a
degree-zero object of `D(A)`, is isomorphic to the degree-zero object on the ordinary `I`-adic
completion of `M ⊗[A] N`. -/
theorem tensor_finite_flat_derivedCompletion_usual_adicCompletion
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (N : Type u) [AddCommGroup N] [Module A N] [Module.Flat A N] :
    IsIsomorphic
      (((single₀).obj (ModuleCat.of A (M ⊗[A] N)))^∧[I, I.fg_of_isNoetherianRing])
      ((single₀).obj (ModuleCat.of A (AdicCompletion I (M ⊗[A] N)))) := by
  sorry

-- Proof sketch: specialize the tensor statement to `N = Localization.Away f`, then transport the
-- conclusion across the canonical localization/tensor equivalence
-- `LocalizedModule.equivTensorProduct`.
/-- Degree-zero companion for Lemma `15.95.6 (2)`: for a finite module `M`, the zero-th
cohomology of the derived completion of `M_f[0]` is isomorphic to the ordinary `I`-adic
completion of the localization `M_f`. This is obtained by transporting part `(1)` along
`LocalizedModule.equivTensorProduct`. -/
theorem localizationAway_finite_homology_zero_derivedCompletion_isomorphic_adicCompletion
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (f : A) :
    IsIsomorphic
      ((H 0).obj
        (((single₀).obj (ModuleCat.of A (Away f M)))^∧[I, I.fg_of_isNoetherianRing]))
      (ModuleCat.of A (AdicCompletion I (Away f M))) := by
  sorry

-- Proof sketch: specialize the previous tensor-product statement to `N = Localization.Away f`,
-- use the standard identification of `M_f` with `M ⊗[A] A_f`, and transport the resulting
-- degree-zero cohomology description along that localization equivalence, and reuse the same
-- Tor-vanishing argument to conclude that all other cohomology groups vanish.
/-- Off-zero vanishing companion for Lemma `15.95.6 (2)`: for a finite module `M`, the derived
completion of `M_f[0]` has zero cohomology in every degree `n ≠ 0`. -/
theorem localizationAway_finite_homology_derivedCompletion_isZero_of_ne_zero
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (f : A)
    (n : ℤ) (hn : n ≠ 0) :
      IsZero ((H n).obj
        (((single₀).obj (ModuleCat.of A (Away f M)))^∧[I, I.fg_of_isNoetherianRing])) := by
  sorry

-- Proof sketch: combine
-- `localizationAway_finite_homology_zero_derivedCompletion_isomorphic_adicCompletion` with
-- `localizationAway_finite_homology_derivedCompletion_isZero_of_ne_zero` to obtain the canonical
-- `t`-structure bounds and conclude by `singleFunctorIso_of_isGE_of_isLE`.
/-- Lemma 15.95.6 (2): if `I` is an ideal in a Noetherian ring `A`, `M` is a finite `A`-module,
and `f ∈ A`, then the derived `I`-adic completion of the localization `M_f`, viewed as a
degree-zero object of `D(A)`, is isomorphic to the degree-zero object on the ordinary `I`-adic
completion of `M_f`. -/
theorem localizationAway_finite_derivedCompletion_usual_adicCompletion
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (f : A) :
    IsIsomorphic
      (((single₀).obj (ModuleCat.of A (Away f M)))^∧[I, I.fg_of_isNoetherianRing])
      ((single₀).obj (ModuleCat.of A (AdicCompletion I (Away f M)))) := by
  sorry

end

/-! ### Lemma_15_95_7 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace DerivedCategory

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "DModMinus" => boundedAboveDerivedCategory (ModuleCat A)
local notation "single₀" => (ModuleCat.single0Functor : ModuleCat A ⥤ DMod)

/- Domain-style sampling for Lemma 15.95.7:
- primary domain: derived `I`-adic completion and derived tensor products in `D(A)`, with
  pseudo-coherent right tensor factors;
- sampled owner declarations:
  `DerivedCategory.derivedCompletionOf`,
  the notation owner `K^∧[I, hI]` from `Remark_15_92_11`,
  `CategoryTheory.derivedTensorProduct` together with the notation `K ⊗[A]^L L`,
  `DerivedCategory.IsPseudoCoherent`;
- best owner abstraction: the source-facing content is the compatibility of the canonical derived
  completion owner with the canonical derived tensor owner, so the public statements should use
  `K^∧[I, hI]`, `K ⊗[A]^L L`, and the chapter pseudo-coherence predicates directly rather than
  the raw functor-application spelling;
- primitive vs. derived:
  primitive data are the ideal `I`, the bounded-above object `K`, and the finite module or
  pseudo-coherent object on the right;
  derived API is the resulting `IsIsomorphic` comparison in `D(A)`.

Source/core/bridge triage:
- `source-facing`: the two completion-vs-tensor compatibility statements below;
- `core/canonical`: `derivedCompletionOf`, the notation `K^∧[I, hI]`, the tensor owner
  `derivedTensorProduct`, the notation `K ⊗[A]^L L`, and `IsPseudoCoherent`;
- `bridge/view`: the degree-zero embedding `ModuleCat.single0Functor` for a finite module `M`. -/

-- Proof sketch: part `(1)` is the finite-module case of part `(2)`, viewing `M` as the degree-zero
-- derived object `(single₀).obj M`. Over the Noetherian ring `A`, finite modules are
-- pseudo-coherent, so the pseudo-coherent tensor-commutation statement applies to `L = M[0]`.
/-- Lemma 15.95.7 (1): if `K ∈ D^-(A)` and `M` is a finite `A`-module, then derived `I`-adic
completion commutes with tensoring `K` by `M`, viewed in degree `0`. -/
theorem derivedCompletionOf_derivedTensorProduct_module_isomorphic_of_finite
    (I : Ideal A) (K : DModMinus) (M : ModuleCat A) (hM : Module.Finite A M) :
    IsIsomorphic
      ((K.obj ⊗[A]^L (single₀).obj M)^∧[I, I.fg_of_isNoetherianRing])
      (K.obj^∧[I, I.fg_of_isNoetherianRing] ⊗[A]^L (single₀).obj M) := sorry

-- Proof sketch: represent the bounded-above complex `K` by a bounded-above complex of free
-- modules, represent the pseudo-coherent object `L` by a bounded-above complex of finite free
-- modules, compute the derived tensor product by totalization, and apply the termwise
-- compatibility of derived completion with tensoring by finite free modules from the preceding
-- completion lemmas.
/-- Lemma 15.95.7 (2): if `K ∈ D^-(A)` and `L ∈ D(A)` is pseudo-coherent, then derived
`I`-adic completion commutes with the derived tensor product `K \otimes_A^{\mathbf L} L`. -/
theorem derivedCompletionOf_derivedTensorProduct_isomorphic_of_isPseudoCoherent
    (I : Ideal A) (K : DModMinus) (L : DMod) (hL : L.IsPseudoCoherent) :
    IsIsomorphic
      ((K.obj ⊗[A]^L L)^∧[I, I.fg_of_isNoetherianRing])
      (K.obj^∧[I, I.fg_of_isNoetherianRing] ⊗[A]^L L) := sorry

end

end DerivedCategory
