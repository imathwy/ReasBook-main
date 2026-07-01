import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

/-
Domain-style sampling for 21.37.2.1:
- primary domain: adjunction Hom-set equivalences on derived categories of sheaves of modules;
- inspected owner declarations/usages:
  `Adjunction.homEquiv`,
  the direct specialization pattern in `Lemma_7_5_4`,
  the derived-category composite-with-comparison pattern in `Lemma_21_43_5`,
  and the derived-adjunction existence theorem
  `derivedLowerShriek_isLeftAdjoint_of_inverseImageRightDerived` in `Lemma_21_37_2`;
- best owner abstraction: `Adjunction.homEquiv` for a chosen adjunction `LgShriek ⊣ gStar`;
- primitive-vs-derived split:
  primitive data are the chosen functors `LgShriek`, `gStar`, the adjunction `adj`, and the
  objects `K` and `L`;
  the Hom-set equivalence is derived API, and the symmetric orientation is only the thin
  bridge/view needed to match the source wording.

Source/core/bridge triage:
- `source-facing`: the equivalence
  `Hom_{D(g^{-1}\mathcal O_\mathcal D)}(K, g^*L) ≃ Hom_{D(\mathcal O_\mathcal D)}(Lg_!K, L)`;
- `core/canonical`: `Adjunction.homEquiv`;
- `bridge/view`: the symmetric form `(adj.homEquiv K L).symm`.

The former `derivedLowerShriek_homEquiv` and `derivedLowerShriek_homEquiv_def` were exact-interface
wrappers with no extra mathematics and no downstream users, so the refined file should recall the
owner directly and specialize it in place.
-/

section

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (u : C ⥤ D) [Functor.IsContinuous u JC JD]
variable (𝒪D : Sheaf JD CommRingCat.{u})

private abbrev sourceModules
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    (𝒪D : Sheaf JD CommRingCat.{u}) :=
  SheafOfModules
    ((sheafCompose JC (forget₂ CommRingCat RingCat)).obj
      ((u.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D))

private abbrev targetModules
    (JD : GrothendieckTopology D)
    (𝒪D : Sheaf JD CommRingCat.{u}) :=
  SheafOfModules ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪D)

private abbrev sourceDerived
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    (𝒪D : Sheaf JD CommRingCat.{u}) :=
  DerivedCategory (sourceModules JC JD u 𝒪D)

private abbrev targetDerived
    (JD : GrothendieckTopology D)
    (𝒪D : Sheaf JD CommRingCat.{u}) :=
  DerivedCategory (targetModules JD 𝒪D)

variable
  [Abelian (sourceModules JC JD u 𝒪D)]
  [CategoryWithHomology (sourceModules JC JD u 𝒪D)]
  [Abelian (targetModules JD 𝒪D)]
  [CategoryWithHomology (targetModules JD 𝒪D)]

variable
  (gStar : targetDerived JD 𝒪D ⥤ sourceDerived JC JD u 𝒪D)
  (LgShriek : sourceDerived JC JD u 𝒪D ⥤ targetDerived JD 𝒪D)
  (adj : LgShriek ⊣ gStar)
  (K : sourceDerived JC JD u 𝒪D)
  (L : targetDerived JD 𝒪D)

/- 21.37.2.1, owner form: once `LgShriek ⊣ gStar` is chosen, the canonical Hom-set equivalence is
the owner equivalence `Adjunction.homEquiv`. -/
recall Adjunction.homEquiv

/- 21.37.2.1: the textbook orientation
`Hom_{D(g^{-1}\mathcal O_\mathcal D)}(K, g^*L) ≃ Hom_{D(\mathcal O_\mathcal D)}(Lg_!K, L)` is
exactly the symmetric form of `Adjunction.homEquiv`. -/
#check (((adj.homEquiv K L).symm) : (K ⟶ gStar.obj L) ≃ (LgShriek.obj K ⟶ L))

end
