import StacksProject_2024.stacks_project.Chap07.Definition_7_40_2
import StacksProject_2024.stacks_project.Chap13.Lemma_13_37_2
import StacksProject_2024.stacks_project.Chap18.Lemma_18_28_8
import StacksProject_2024.stacks_project.Chap18.Lemma_18_30_4
import StacksProject_2024.stacks_project.Chap21.Lemma_21_52_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.IsGrothendieckAbelian
open scoped SheafOfModules.RingedSite.LocalizedStructureModuleExtensionByZero

noncomputable section

universe u w

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable {𝒪 : Sheaf J CommRingCat.{u}}

local notation "Mod" => SheafOfModules (ringSheaf J 𝒪)
local notation "DMod" => DerivedCategory Mod

/-- The object property of `𝒪`-modules isomorphic to `j![𝒪, U]` for some quasi-compact object
`U`. -/
abbrev quasiCompactLocalizedStructureModuleExtensionByZero : ObjectProperty Mod :=
  fun ℱ : Mod ↦
    ∃ U : C, J.QuasiCompactObject U ∧ Nonempty (j![𝒪, U] ≅ ℱ)

section

omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]

/-- An `𝒪`-module belongs to
`quasiCompactLocalizedStructureModuleExtensionByZero` exactly when it is isomorphic to
`j![𝒪, U]` for some quasi-compact object `U`. -/
theorem quasiCompactLocalizedStructureModuleExtensionByZero_iff (ℱ : Mod) :
    quasiCompactLocalizedStructureModuleExtensionByZero ℱ ↔
      ∃ U : C, J.QuasiCompactObject U ∧ Nonempty (j![𝒪, U] ≅ ℱ) :=
  Iff.rfl

/-- Each quasi-compact lower-shriek module `j![𝒪, U]` belongs to
`quasiCompactLocalizedStructureModuleExtensionByZero`. -/
theorem quasiCompactLocalizedStructureModuleExtensionByZero_self
    {U : C} (hU : J.QuasiCompactObject U) :
    quasiCompactLocalizedStructureModuleExtensionByZero (j![𝒪, U]) :=
  ⟨U, hU, ⟨Iso.refl _⟩⟩

end

section

omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]

/-- Any module in `quasiCompactLocalizedStructureModuleExtensionByZero` is compact. -/
theorem isCompactObject_of_quasiCompactLocalizedStructureModuleExtensionByZero
    {ℱ : Mod}
    (hℱ : quasiCompactLocalizedStructureModuleExtensionByZero ℱ) :
    IsCompactObject ℱ := by
  rcases hℱ with ⟨U, hU, ⟨e⟩⟩
  exact ObjectProperty.prop_of_iso (IsCompactObject : ObjectProperty Mod) e
    (localizedStructureModuleExtensionByZero_isCompactObject J 𝒪 U hU)

end

/- Domain-style sampling for Lemma 21.52.2:
- primary domain: compact generation of `DMod` by the standard sheaves `j![𝒪, U]`, restricted to
  the quasi-compact subfamily on a ringed site;
- sampled owner declarations:
  `compactObject_isRetract_of_finiteCoproductComplex_of_separatingFamily`,
  `exists_epi_from_coproduct_localizedStructureModuleExtensionByZero`,
  `localizedStructureModuleExtensionByZero_isCompactObject`,
  `ObjectProperty.IsSeparating`,
  `ObjectProperty.additiveClosure`;
- best owner abstraction: the core owner is the chapter theorem
  `compactObject_isRetract_of_finiteCoproductComplex_of_separatingFamily`; the local source-facing
  owner is `quasiCompactLocalizedStructureModuleExtensionByZero`, i.e. the object property of
  modules isomorphic to the canonical family `U ↦ j![𝒪, U]` on quasi-compact objects `U`;
- primitive-vs-derived split: the primitive local data are the quasi-compact cover hypothesis and
  the compactness of each generator `j![𝒪, U]`; the bounded-complex conclusion is derived from the
  chapter owner applied to the separating object property
  `quasiCompactLocalizedStructureModuleExtensionByZero`, and the termwise finite-sum condition is
  expressed via `P.additiveClosure`.

Source/core/bridge triage:
- `source-facing`: compact objects of `DMod` are retracts of bounded complexes built from finite
  direct sums of quasi-compact `j![𝒪, U]`;
- `core/canonical`: `compactObject_isRetract_of_finiteCoproductComplex_of_separatingFamily`;
- `bridge/view`: the object property `quasiCompactLocalizedStructureModuleExtensionByZero`.
-/

-- Proof sketch: apply the object-property theorem
-- `compactObject_isRetract_of_finiteCoproductComplex_of_separatingFamily` to the quasi-compact
-- family `quasiCompactLocalizedStructureModuleExtensionByZero`. The quasi-compact covering
-- hypothesis supplies the separating condition, and Lemma `18.30.4` gives compactness of each
-- generator `j![𝒪, U]`.
private theorem quasiCompactLocalizedStructureModuleExtensionByZero_coverEpi
    (hEnough : J.HasEnoughObjectsWithProperty J.QuasiCompactObject) (V : C) :
    ∃ (A : Type u) (U : A → C),
      (∀ a, J.QuasiCompactObject (U a)) ∧
        ∃ (δ : (∐ fun a : A ↦ j![𝒪, (U a)]) ⟶ j![𝒪, V]),
          Epi δ := by
  sorry

private noncomputable def flattenedLocalizedStructureModuleCoproductMap
    {I : Type u} (A : I → Type u) (U : ∀ i, A i → C) (V : I → C)
    (δ : ∀ i, (∐ fun a : A i ↦ j![𝒪, (U i a)]) ⟶ j![𝒪, (V i)]) :
    (∐ fun p : Sigma A ↦ j![𝒪, (U p.1 p.2)]) ⟶
      (∐ fun i : I ↦ j![𝒪, (V i)]) :=
  Sigma.desc (fun p : Sigma A ↦
    Sigma.ι (fun a : A p.1 ↦ j![𝒪, (U p.1 a)]) p.2 ≫
      δ p.1 ≫
        Sigma.ι (fun i : I ↦ j![𝒪, (V i)]) p.1)

omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})] in
private theorem flattenedLocalizedStructureModuleCoproductMap_ι
    {I : Type u} (A : I → Type u) (U : ∀ i, A i → C) (V : I → C)
    (δ : ∀ i, (∐ fun a : A i ↦ j![𝒪, (U i a)]) ⟶ j![𝒪, (V i)]) (i : I) (a : A i) :
    Sigma.ι (fun p : Sigma A ↦ j![𝒪, (U p.1 p.2)]) ⟨i, a⟩ ≫
        flattenedLocalizedStructureModuleCoproductMap A U V δ =
      Sigma.ι (fun b : A i ↦ j![𝒪, (U i b)]) a ≫
        δ i ≫
          Sigma.ι (fun j : I ↦ j![𝒪, (V j)]) i := by
  dsimp [flattenedLocalizedStructureModuleCoproductMap]
  rw [Limits.Sigma.ι_desc]

omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})] in
private theorem flattenedLocalizedStructureModuleCoproductMap_epi
    {I : Type u} (A : I → Type u) (U : ∀ i, A i → C) (V : I → C)
    (δ : ∀ i, (∐ fun a : A i ↦ j![𝒪, (U i a)]) ⟶ j![𝒪, (V i)])
    [∀ i, Epi (δ i)] :
    Epi (flattenedLocalizedStructureModuleCoproductMap A U V δ) := by
  refine ⟨?_⟩
  intro ℱ α β hαβ
  apply Limits.Sigma.hom_ext
  intro i
  apply (cancel_epi (δ i)).1
  apply Limits.Sigma.hom_ext
  intro a
  have hcomp := congrArg
    (fun γ ↦
      Sigma.ι (fun p : Sigma A ↦ j![𝒪, (U p.1 p.2)]) ⟨i, a⟩ ≫ γ)
    hαβ
  have hpre :
      Sigma.ι (fun p : Sigma A ↦ j![𝒪, (U p.1 p.2)]) ⟨i, a⟩ ≫
          flattenedLocalizedStructureModuleCoproductMap A U V δ ≫ α =
        Sigma.ι (fun p : Sigma A ↦ j![𝒪, (U p.1 p.2)]) ⟨i, a⟩ ≫
          flattenedLocalizedStructureModuleCoproductMap A U V δ ≫ β := by
    simpa [Category.assoc] using hcomp
  have hflat := flattenedLocalizedStructureModuleCoproductMap_ι A U V δ i a
  have hflatα :
      Sigma.ι (fun a : A i ↦ j![𝒪, (U i a)]) a ≫ δ i ≫
          Sigma.ι (fun i : I ↦ j![𝒪, (V i)]) i ≫ α =
        Sigma.ι (fun p : Sigma A ↦ j![𝒪, (U p.1 p.2)]) ⟨i, a⟩ ≫
          flattenedLocalizedStructureModuleCoproductMap A U V δ ≫ α := by
    have h := congrArg (fun γ ↦ γ ≫ α) hflat.symm
    simpa [Category.assoc] using h
  have hflatβ :
      Sigma.ι (fun p : Sigma A ↦ j![𝒪, (U p.1 p.2)]) ⟨i, a⟩ ≫
          flattenedLocalizedStructureModuleCoproductMap A U V δ ≫ β =
        Sigma.ι (fun a : A i ↦ j![𝒪, (U i a)]) a ≫ δ i ≫
          Sigma.ι (fun i : I ↦ j![𝒪, (V i)]) i ≫ β := by
    have h := congrArg (fun γ ↦ γ ≫ β) hflat
    simpa [Category.assoc] using h
  calc
    Sigma.ι (fun a : A i ↦ j![𝒪, (U i a)]) a ≫ δ i ≫
        Sigma.ι (fun i : I ↦ j![𝒪, (V i)]) i ≫ α =
      Sigma.ι (fun p : Sigma A ↦ j![𝒪, (U p.1 p.2)]) ⟨i, a⟩ ≫
        flattenedLocalizedStructureModuleCoproductMap A U V δ ≫ α := hflatα
    _ =
      Sigma.ι (fun p : Sigma A ↦ j![𝒪, (U p.1 p.2)]) ⟨i, a⟩ ≫
        flattenedLocalizedStructureModuleCoproductMap A U V δ ≫ β := hpre
    _ =
      Sigma.ι (fun a : A i ↦ j![𝒪, (U i a)]) a ≫ δ i ≫
        Sigma.ι (fun i : I ↦ j![𝒪, (V i)]) i ≫ β := hflatβ

/-- The quasi-compact lower-shriek modules `j![𝒪, U]` form a separating family as soon as every
object of the site admits a cover by quasi-compact objects. -/
theorem quasiCompactLocalizedStructureModuleExtensionByZero_isSeparating
    (hEnough : J.HasEnoughObjectsWithProperty J.QuasiCompactObject) :
    (quasiCompactLocalizedStructureModuleExtensionByZero : ObjectProperty Mod).IsSeparating := by
  classical
  refine ObjectProperty.IsSeparating.mk_of_exists_epi ?_
  intro ℱ
  obtain ⟨I, V, ψ, hψ⟩ :=
    exists_epi_from_coproduct_localizedStructureModuleExtensionByZero ℱ
  choose A U hU δ hδ using
    fun i : I ↦ quasiCompactLocalizedStructureModuleExtensionByZero_coverEpi hEnough (V i)
  let W : Sigma A → Mod := fun p ↦ j![𝒪, (U p.1 p.2)]
  let θ :
      (∐ fun p : Sigma A ↦ W p) ⟶
        (∐ fun i : I ↦ j![𝒪, (V i)]) :=
    flattenedLocalizedStructureModuleCoproductMap A U V δ
  let φ : (∐ fun p : Sigma A ↦ W p) ⟶ ℱ := θ ≫ ψ
  refine ⟨Sigma A, W, ?_, _, colimit.isColimit _, φ, ?_⟩
  · intro p
    exact quasiCompactLocalizedStructureModuleExtensionByZero_self
      (hU p.1 p.2)
  · letI : ∀ i, Epi (δ i) := hδ
    letI : Epi θ :=
      flattenedLocalizedStructureModuleCoproductMap_epi A U V δ
    letI : Epi ψ := hψ
    dsimp [φ]
    infer_instance

/-- Lemma 21.52.2: if every object of the ringed site admits a covering by quasi-compact objects,
then every compact object of `DMod` is a retract of an object represented by a bounded complex
whose terms are finite direct sums of modules `j![𝒪, U]` with `U` quasi-compact. -/
@[stacks 094C]
theorem compactObject_isRetract_of_finiteCoproductComplex_of_quasiCompact_localizedStructureModuleExtensionByZero
    [IsGrothendieckAbelian.{w} Mod]
    (hEnough : J.HasEnoughObjectsWithProperty J.QuasiCompactObject)
    {K : DMod} (hK : IsCompactObject K) :
    ∃ P : Compᵇ(Mod),
      (∀ i : ℤ, quasiCompactLocalizedStructureModuleExtensionByZero.additiveClosure (P.obj.X i)) ∧
        Nonempty (Retract K (DerivedCategory.Q.obj P.obj)) := by
  let P : ObjectProperty Mod := quasiCompactLocalizedStructureModuleExtensionByZero
  have hsep : P.IsSeparating :=
    quasiCompactLocalizedStructureModuleExtensionByZero_isSeparating hEnough
  have hsmall : ∀ E : Mod, P E → IsCompactObject E := by
    intro E hE
    exact isCompactObject_of_quasiCompactLocalizedStructureModuleExtensionByZero hE
  simpa [P] using
    compactObject_isRetract_of_finiteCoproductComplex_of_separatingFamily P hK hsep hsmall

end

end SheafOfModules.RingedSite
