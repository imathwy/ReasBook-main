import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_18_42_1 (from Chap18) -/
noncomputable section

universe u v w

namespace CategoryTheory

open CategoryTheory.Limits
open Opposite

variable {C : Type u} [Category.{v} C]
/- Domain-style sampling:
- primary domain: constant presheaves/sheaves of abelian groups on a site and preservation of
  short exact sequences by exact functors;
- sampled owner declarations:
  `Functor.const`,
  `constantSheaf`,
  `presheafToSheaf`,
  `ExactFunctor.of`,
  `ShortComplex.ShortExact.map_of_exact`;
- best owner abstraction: the exact-functor factorization
  `Functor.const Cᵒᵖ ⋙ presheafToSheaf J AddCommGrpCat.{w}`, whose sheaf-level owner is
  `constantSheaf J AddCommGrpCat.{w}`;
- primitive data: the short exact sequence `S` in `AddCommGrpCat`, plus the site `J` for the
  sheafification stage;
- derived API: exactness of the constant presheaf sequence is the bridge/view layer, and the
  sheaf-level theorem is obtained by applying exact sheafification.

Source/core/bridge triage:
- `source-facing`: `shortExact_constantAbelianSheaf`;
- `core/canonical`: `Functor.const Cᵒᵖ`, `constantSheaf J AddCommGrpCat.{w}`,
  `presheafToSheaf J AddCommGrpCat.{w}`, and `ShortComplex.ShortExact.map_of_exact`;
- `bridge/view`: `shortExact_constantAbelianPresheaf`, which records the honest constant-presheaf
  stage before sheafification.

The source statement is about constant sheaves on a site, so the main labeled entry remains at the
`constantSheaf` owner. The previous bridge through the underlying presheaf of `constantSheaf` was
semantically wrong, because `constantSheaf` is the sheafification of the constant presheaf rather
than a sectionwise copy of the original abelian group on arbitrary objects. The correct bridge is
therefore the exact constant-presheaf sequence, followed by exact sheafification at the
`HasSheafify` layer. -/

variable {J : GrothendieckTopology C}

local instance constantSheaf_preservesZeroMorphisms [HasWeakSheafify J AddCommGrpCat.{w}] :
    (constantSheaf J AddCommGrpCat.{w}).PreservesZeroMorphisms := by
  dsimp [constantSheaf]
  infer_instance

-- Proof sketch: `Functor.const Cᵒᵖ` is exact, so it carries short exact sequences of abelian
-- groups to short exact sequences of constant abelian presheaves.
/-- Companion to Lemma 18.42.1: a short exact sequence of abelian groups remains short exact after
applying the constant abelian presheaf functor. -/
theorem shortExact_constantAbelianPresheaf
    (S : ShortComplex AddCommGrpCat.{w}) (hS : S.ShortExact) :
    (S.map (Functor.const Cᵒᵖ : AddCommGrpCat.{w} ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{w})).ShortExact := by
  simpa using
    hS.map_of_exact (Functor.const Cᵒᵖ : AddCommGrpCat.{w} ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{w})

-- Proof sketch: `constantSheaf J AddCommGrpCat` is `Functor.const Cᵒᵖ ⋙ presheafToSheaf`, so the
-- sheaf statement follows from the presheaf bridge together with exactness of `presheafToSheaf`.
/-- Lemma 18.42.1: for a site `(\mathcal C, J)`, a short exact sequence of abelian groups remains
short exact after applying the constant abelian sheaf functor
`constantSheaf J AddCommGrpCat`. -/
theorem shortExact_constantAbelianSheaf
    [HasSheafify J AddCommGrpCat.{w}]
    (S : ShortComplex AddCommGrpCat.{w}) (hS : S.ShortExact) :
    (S.map (constantSheaf J AddCommGrpCat.{w})).ShortExact := by
  simpa [constantSheaf] using
    (show ((S.map (Functor.const Cᵒᵖ : AddCommGrpCat.{w} ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{w})).map
        (presheafToSheaf J AddCommGrpCat.{w})).ShortExact from
      (shortExact_constantAbelianPresheaf (C := C) S hS).map_of_exact
        (presheafToSheaf J AddCommGrpCat.{w}))

end CategoryTheory

/-! ### Lemma_18_42_2 (from Chap18) -/
open CategoryTheory Opposite
open CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u

namespace CategoryTheory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {Λ : Type u} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{u} Λ)]

/-- The presheaf `U ↦ \underline{M}(U) \otimes_\Lambda Q` obtained by tensoring the underlying
presheaf of the constant sheaf of `M` with the fixed module `Q`. -/
abbrev constantModuleTensorSectionsPresheaf
    (J : GrothendieckTopology C) (M Q : ModuleCat.{u} Λ) :
    Cᵒᵖ ⥤ ModuleCat.{u} Λ :=
  ((constantSheaf J (ModuleCat.{u} Λ)).obj M).obj ⋙ tensorRight Q

/-- The canonical natural transformation from the constant presheaf with value `M ⊗ Q` to the
presheaf `U ↦ \underline{M}(U) \otimes_\Lambda Q`. -/
abbrev constantModuleTensorComparisonNatTrans
    (J : GrothendieckTopology C) (M Q : ModuleCat.{u} Λ) :
    ((Functor.const Cᵒᵖ).obj (M ⊗ Q)) ⟶
      constantModuleTensorSectionsPresheaf J M Q :=
  (Functor.constComp Cᵒᵖ M (tensorRight Q)).inv ≫
    Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M)) (tensorRight Q)

-- Proof sketch: choose a finite presentation of `Q`, tensor the resulting right exact sequence
-- with the constant sheaf of `M`, and use exactness of the constant abelian-sheaf functor together
-- with preservation of finite direct sums by evaluation on `U` to identify the resulting cokernel
-- presheaf with `U ↦ \underline{M}(U) \otimes_\Lambda Q`.
/-- The presheaf `U ↦ \underline{M}(U) \otimes_\Lambda Q` is a sheaf when `Q` is finitely
presented. -/
theorem constantModuleTensorSectionsPresheaf_isSheaf
    (J : GrothendieckTopology C) (M Q : ModuleCat.{u} Λ) [Module.FinitePresentation Λ Q] :
    Presheaf.IsSheaf J (constantModuleTensorSectionsPresheaf J M Q) := sorry

/-- The sheaf whose sections over `U` are `\underline{M}(U) \otimes_\Lambda Q`. -/
abbrev constantModuleTensorSectionsSheaf
    (J : GrothendieckTopology C) (M Q : ModuleCat.{u} Λ) [Module.FinitePresentation Λ Q] :
    Sheaf J (ModuleCat.{u} Λ) :=
  ⟨constantModuleTensorSectionsPresheaf J M Q,
    constantModuleTensorSectionsPresheaf_isSheaf J M Q⟩

/-- The canonical comparison morphism from the constant sheaf of `M ⊗_\Lambda Q` to the sheaf
`U ↦ \underline{M}(U) \otimes_\Lambda Q`. -/
abbrev constantModuleTensorComparison
    (J : GrothendieckTopology C) (M Q : ModuleCat.{u} Λ) [Module.FinitePresentation Λ Q] :
    (constantSheaf J (ModuleCat.{u} Λ)).obj (M ⊗ Q) ⟶
      constantModuleTensorSectionsSheaf J M Q :=
  ObjectProperty.homMk <|
    sheafifyLift J
      (constantModuleTensorComparisonNatTrans J M Q)
      (constantModuleTensorSectionsPresheaf_isSheaf J M Q)

-- Proof sketch: the previous theorem makes `U ↦ \underline{M}(U) \otimes_\Lambda Q` into a sheaf,
-- so the canonical map from the constant presheaf with value `M ⊗ Q` factors uniquely through its
-- sheafification `\underline{M \otimes_\Lambda Q}`. The finite-presentation argument shows this
-- factorization is an isomorphism on every section object.
/-- Lemma 18.42.2: if `Q` is a finitely presented `\Lambda`-module, then for every `U : C` the
canonical comparison
`\underline{M \otimes_\Lambda Q}(U) \to \underline{M}(U) \otimes_\Lambda Q` is an isomorphism. -/
theorem constantModuleTensorComparison_app_isIso
    (M Q : ModuleCat.{u} Λ) [Module.FinitePresentation Λ Q] (U : C) :
    IsIso ((constantModuleTensorComparison J M Q).hom.app (op U)) := sorry

end CategoryTheory

/-! ### Lemma_18_42_3 (from Chap18) -/
open CategoryTheory Opposite

noncomputable section

universe u

namespace CategoryTheory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {Λ : Type u} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{u} Λ)]

-- Proof sketch: by Lemma 10.39.5 it is enough to test injectivity after tensoring with a finite
-- ideal `I ⊆ Λ`. Coherence makes `I` finitely presented, so Lemma 18.42.2 identifies
-- `\underline M(U) ⊗ I` with `\underline{M ⊗ I}(U)`. Since `M` is flat, `M ⊗ I → M` is
-- injective, and evaluation of the induced morphism of constant sheaves at `U` remains injective.
/-- Lemma 18.42.3: if `Λ` is a coherent ring, `M` is a flat `Λ`-module, and `U` is an object of
the site `C`, then the `Λ`-module of sections `\underline M(U)` of the constant sheaf is flat. -/
theorem constantSheaf_app_flat
    (hcoh : ∀ (I : Ideal Λ) [Module.Finite Λ I], Module.FinitePresentation Λ I)
    (M : ModuleCat.{u} Λ) [Module.Flat Λ M] (U : C) :
    Module.Flat Λ (((constantSheaf J (ModuleCat.{u} Λ)).obj M).1.obj (op U)) := sorry

end CategoryTheory

/-! ### Lemma_18_42_4 (from Chap18) -/
open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace CategoryTheory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {Λ : Type u} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{u} Λ)]

/-- The `n`th quotient `Λ / I^n`, viewed as an object of `ModuleCat Λ`. -/
abbrev idealPowerQuotientSequence (I : Ideal Λ) (n : ℕ) : ModuleCat.{u} Λ :=
  ModuleCat.of Λ (Λ ⧸ I ^ n)

/-- The transition map `Λ / I^(n + 1) → Λ / I^n` in the `I`-adic quotient tower. -/
abbrev idealPowerQuotientTransition (I : Ideal Λ) (n : ℕ) :
    idealPowerQuotientSequence I (n + 1) ⟶ idealPowerQuotientSequence I n :=
  ModuleCat.ofHom
    (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right (Nat.le_succ n))).toLinearMap

/-- The inverse system `n ↦ Λ / I^n` in `ModuleCat Λ`. -/
abbrev idealPowerQuotientSystem (I : Ideal Λ) : ℕᵒᵖ ⥤ ModuleCat.{u} Λ :=
  Functor.ofOpSequence (idealPowerQuotientTransition I)

/-- The inverse system of constant sheaves with values `Λ / I^n`. -/
abbrev constantIdealPowerQuotientSheafSystem
    (J : GrothendieckTopology C) (I : Ideal Λ) :
    ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{u} Λ) :=
  idealPowerQuotientSystem I ⋙ constantSheaf J (ModuleCat.{u} Λ)

/-- The completed constant sheaf `\underline Λ^∧ = lim_n \underline{Λ / I^n}`. -/
abbrev constantIadicCompletionSheaf
    (J : GrothendieckTopology C) (I : Ideal Λ) :
    Sheaf J (ModuleCat.{u} Λ) :=
  limit (constantIdealPowerQuotientSheafSystem J I)

/-- The constant sheaf with value `Λ / I`. -/
abbrev constantIdealQuotientSheaf
    (J : GrothendieckTopology C) (I : Ideal Λ) :
    Sheaf J (ModuleCat.{u} Λ) :=
  (constantIdealPowerQuotientSheafSystem J I).obj (op 1)

/-- The sections of the completed constant sheaf over `U`. -/
abbrev constantIadicCompletionSections
    (J : GrothendieckTopology C) (I : Ideal Λ) (U : C) :
    ModuleCat.{u} Λ :=
  (constantIadicCompletionSheaf J I).1.obj (op U)

/-- The sections of the constant quotient sheaf `\underline{Λ / I}` over `U`. -/
abbrev constantIdealQuotientSections
    (J : GrothendieckTopology C) (I : Ideal Λ) (U : C) :
    ModuleCat.{u} Λ :=
  (constantIdealQuotientSheaf J I).1.obj (op U)

/-- The canonical map from the sections of the completed constant sheaf to the sections of
`\underline{Λ / I}`, induced by the projection to the first quotient in the inverse system. -/
abbrev constantIadicCompletionSectionsToConstantIdealQuotient
    (J : GrothendieckTopology C) (I : Ideal Λ) (U : C) :
    constantIadicCompletionSections J I U →ₗ[Λ] constantIdealQuotientSections J I U :=
  (((limit.π (constantIdealPowerQuotientSheafSystem J I) (op 1)).hom.app (op U)).hom)

-- Proof sketch: the target is a `Λ / I`-module, so multiplication by any element of `I` is zero;
-- hence the projection to the first quotient annihilates `I · \underline{Λ}^∧(U)`.
/-- The projection from completed sections to `\underline{Λ / I}(U)` kills the submodule generated
by `I`. -/
theorem smul_top_le_constantIadicCompletionSectionsToConstantIdealQuotient_ker
    (J : GrothendieckTopology C) (I : Ideal Λ) (U : C) :
    I • (⊤ : Submodule Λ (constantIadicCompletionSections J I U)) ≤
      LinearMap.ker
        (constantIadicCompletionSectionsToConstantIdealQuotient J I U) := sorry

/-- The canonical map from the quotient of completed sections modulo `I` to
`\underline{Λ / I}(U)`. -/
abbrev constantIadicCompletionSectionsModIComparison
    (J : GrothendieckTopology C) (I : Ideal Λ) (U : C) :
    ((constantIadicCompletionSections J I U) ⧸
      (I • (⊤ : Submodule Λ (constantIadicCompletionSections J I U)))) →ₗ[Λ]
      constantIdealQuotientSections J I U :=
  (I • (⊤ : Submodule Λ (constantIadicCompletionSections J I U))).liftQ
    (constantIadicCompletionSectionsToConstantIdealQuotient J I U)
    (smul_top_le_constantIadicCompletionSectionsToConstantIdealQuotient_ker
      J I U)

-- Proof sketch: evaluate the inverse-limit sheaf at `U`, identify the result with the limit of the
-- system `Λ / I^n` of flat `Λ / I^n`-modules with surjective transition maps, and then apply the
-- flatness criterion for inverse limits over a Noetherian base.
/-- Lemma 18.42.4 (1): for a Noetherian ring `Λ`, the sections of the completed constant sheaf
`\underline Λ^∧ = lim_n \underline{Λ / I^n}` are flat over `Λ`. -/
theorem constantIadicCompletionSheaf_app_flat
    [IsNoetherianRing Λ] (I : Ideal Λ) (U : C) :
    Module.Flat Λ (constantIadicCompletionSections J I U) := sorry

-- Proof sketch: compare the inverse system `Λ / I^n` with its reduction modulo `I`, use exactness
-- of inverse limits with surjective transition maps, and identify the resulting quotient with the
-- constant sheaf on `Λ / I`.
/-- Lemma 18.42.4 (2): the quotient of the completed constant sheaf by `I` identifies with the
constant sheaf `\underline{Λ / I}` on sections. -/
theorem constantIadicCompletionSectionsModIComparison_bijective
    [IsNoetherianRing Λ] (I : Ideal Λ) (U : C) :
    Function.Bijective (constantIadicCompletionSectionsModIComparison J I U) := sorry

end CategoryTheory

/-! ### Lemma_18_42_5 (from Chap18) -/
open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The constant `RingCat`-valued presheaf with value `Λ` on a site. -/
abbrev constantRingPresheaf (Λ : Type w) [Ring Λ] : Cᵒᵖ ⥤ RingCat.{w} :=
  (Functor.const Cᵒᵖ).obj (RingCat.of Λ)

/-- The constant sheaf of rings `\underline{\Lambda}` on a site. -/
abbrev constantRingSheaf (J : GrothendieckTopology C) (Λ : Type w) [Ring Λ]
    [HasWeakSheafify J RingCat.{w}] : Sheaf J RingCat.{w} :=
  (presheafToSheaf J RingCat.{w}).obj (constantRingPresheaf Λ)

/-- The constant presheaf of `\Lambda`-modules with value `M`, viewed as a presheaf of modules
over the constant ring presheaf `\Lambda`. -/
abbrev constantModulePresheaf (Λ : Type w) [Ring Λ] (M : ModuleCat.{w} Λ) :
    PresheafOfModules ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) := by
  let F : Cᵒᵖ ⥤ AddCommGrpCat.{w} :=
    ((Functor.const Cᵒᵖ).obj M) ⋙ forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}
  letI (X : Cᵒᵖ) : Module ↑(((Functor.const Cᵒᵖ).obj (RingCat.of Λ)).obj X) ↑(F.obj X) := by
    change Module Λ ↑M
    infer_instance
  exact PresheafOfModules.ofPresheaf F
    (fun {X Y} f r m ↦ by
      rfl)

/-- The constant sheaf of `\underline{\Lambda}`-modules associated with a `\Lambda`-module `M`. -/
abbrev constantModuleSheaf (J : GrothendieckTopology C) (Λ : Type w) [Ring Λ]
    (M : ModuleCat.{w} Λ)
    [HasWeakSheafify J RingCat.{w}]
    [J.WEqualsLocallyBijective RingCat.{w}]
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    SheafOfModules (constantRingSheaf J Λ) :=
  let hW : J.W (toSheafify J (constantRingPresheaf Λ)) :=
    J.W_toSheafify (constantRingPresheaf Λ)
  let hι : Presheaf.IsLocallyInjective J
      (toSheafify J (constantRingPresheaf Λ)) :=
    hW.isLocallyInjective
  let hs : Presheaf.IsLocallySurjective J
      (toSheafify J (constantRingPresheaf Λ)) :=
    hW.isLocallySurjective
  (@PresheafOfModules.sheafification _ _ _ _ _ (toSheafify J (constantRingPresheaf Λ))
      hι hs _ _).obj
    (constantModulePresheaf Λ M)

variable {Λ : Type w} [Ring Λ]
variable [HasWeakSheafify J RingCat.{w}]
variable [J.WEqualsLocallyBijective RingCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{w}]
variable [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ X : C, (J.over X).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

-- Proof sketch: if `M` is finitely generated, its generators define global sections of the
-- constant sheaf that generate it locally, so `\underline M` is of finite type. Conversely,
-- choose an object of the site that is not sheaf theoretically empty; local finite generation on
-- that object comes from finitely many elements of `M`, and injectivity of restriction to a
-- nonempty object shows those elements already generate `M`.
/-- Lemma 18.42.5 (1): the constant sheaf `\underline M` of `\underline{\Lambda}`-modules is of
finite type if and only if the `\Lambda`-module `M` is finite, assuming the sheaf topos of the
site is not empty. -/
theorem isFiniteType_constantModuleSheaf_iff_module_finite
    (M : ModuleCat.{w} Λ)
    (hne : ∃ U : C, ¬ J.IsSheafTheoreticallyEmpty U) :
    (constantModuleSheaf J Λ M).IsFiniteType ↔ Module.Finite Λ M := sorry

-- Proof sketch: finite presentation of `\underline M` implies finite type by the first clause.
-- Choose a finite generating set of `M`, use the induced short exact sequence
-- `0 → K → Λ^{\oplus r} → M → 0`, pass to constant sheaves using exactness of the constant sheaf
-- functor, and apply the finite-presentation kernel criterion to conclude that `K` is finite.
-- The converse follows by sheafifying a finite presentation of `M`.
/-- Lemma 18.42.5 (2): the constant sheaf `\underline M` of `\underline{\Lambda}`-modules is
finitely presented if and only if the `\Lambda`-module `M` is finitely presented, assuming the
sheaf topos of the site is not empty. -/
theorem isFinitePresentation_constantModuleSheaf_iff_module_finitePresentation
    (M : ModuleCat.{w} Λ)
    (hne : ∃ U : C, ¬ J.IsSheafTheoreticallyEmpty U) :
    (constantModuleSheaf J Λ M).IsFinitePresentation ↔
      Module.FinitePresentation Λ M := sorry

end CategoryTheory
