import StacksProject_2024.Chap13.Lemma_13_33_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

section

variable {C : Type u} [Category.{v} C]

/- For a filtration `F₀ P ⟶ F₁ P ⟶ F₂ P ⟶ ⋯` as in property `(P)`, the source proof builds the
first map on `⨿ i, F i P` as the telescope difference `𝟙 - shift` and the second map as the direct
sum of the stage maps into the ambient object `P`. The filtration data must therefore remember the
cocone from the stages to `P` together with the colimit identification, rather than only the
abstract sequential diagram. -/

/-- A chosen filtration corresponding to property `(P)` on an object `P`, recorded by its stages,
the transition maps, and the cocone exhibiting `P` as the colimit of the stage diagram. -/
structure PropertyPFiltration (P : C) where
  /-- The stage `F_i P` of the filtration. -/
  stage : ℕ → C
  /-- The transition map `F_i P ⟶ F_{i + 1} P`. -/
  step : ∀ i : ℕ, stage i ⟶ stage (i + 1)
  /-- The natural cocone map from the stage diagram to the ambient object `P`. -/
  toCocone : Functor.ofSequence step ⟶ (Functor.const ℕ).obj P
  /-- The object `P` is the colimit of the sequential diagram of filtration stages. -/
  isColimit : IsColimit (Cocone.mk P toCocone)

namespace PropertyPFiltration

/-- The sequential diagram of filtration stages attached to a property `(P)` filtration. -/
abbrev diagram {P : C} (F : PropertyPFiltration P) : ℕ ⥤ C :=
  Functor.ofSequence F.step

/-- The cocone from the filtration stages to the ambient object. -/
abbrev cocone {P : C} (F : PropertyPFiltration P) : Cocone F.diagram :=
  Cocone.mk P F.toCocone

/-- A chosen property `(P)` filtration provides the colimit of its stage diagram. -/
instance instHasColimit {P : C} (F : PropertyPFiltration P) : HasColimit F.diagram :=
  HasColimit.mk ⟨F.cocone, F.isColimit⟩

/-- The chosen colimit comparison from the canonical sequential colimit to the ambient object
carrying the filtration. -/
abbrev colimitComparison {P : C} (F : PropertyPFiltration P) :
    colimit F.diagram ≅ P :=
  (colimit.isColimit F.diagram).coconePointUniqueUpToIso F.isColimit

section

variable [Preadditive C] [HasCountableCoproducts C]

/-- The telescope relation vanishes after summing the structure maps of a property `(P)`
filtration. -/
theorem telescopeCompDescZero {P : C} (F : PropertyPFiltration P) :
    sequentialTelescopeMap F.diagram ≫ Limits.Sigma.desc F.toCocone.app = 0 := by
  simpa using
    sequentialTelescopeMap_comp_sigmaDesc F.diagram F.toCocone.app
      (fun n ↦ by
        simpa using F.toCocone.naturality (homOfLE (Nat.le_succ n)))

/-- The telescope short complex attached to a property `(P)` filtration. -/
abbrev telescopeShortComplex {P : C} (F : PropertyPFiltration P) : ShortComplex C :=
  ShortComplex.mk (sequentialTelescopeMap F.diagram) (Limits.Sigma.desc F.toCocone.app)
    F.telescopeCompDescZero

end

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]

/-- Lemma 22.20.1: for a chosen filtration `F_•` of an object `P` with `P` identified as the
colimit of its stages, the telescope sequence
`0 ⟶ ⨿ i, F i P ⟶ ⨿ i, F i P ⟶ P ⟶ 0`
is short exact. -/
@[stacks 09KL]
theorem telescopeShortExact {P : C} (F : PropertyPFiltration P) :
    F.telescopeShortComplex.ShortExact := by
  let e :
      (ShortComplex.mk (sequentialTelescopeMap F.diagram)
        (Limits.Sigma.desc (colimit.ι F.diagram))
        (sequentialTelescopeMap_comp_sigmaDesc F.diagram (colimit.ι F.diagram)
          (fun n ↦ colimit.w F.diagram (homOfLE (Nat.le_succ n))))) ≅
        F.telescopeShortComplex :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) F.colimitComparison
      (by simp [PropertyPFiltration.telescopeShortComplex, PropertyPFiltration.diagram])
      (by
        apply Limits.Sigma.hom_ext
        intro n
        simp only [Iso.refl_hom, Category.id_comp]
        rw [Limits.Sigma.ι_desc, Limits.Sigma.ι_desc_assoc]
        simpa [PropertyPFiltration.telescopeShortComplex,
          PropertyPFiltration.diagram, PropertyPFiltration.cocone,
          PropertyPFiltration.colimitComparison] using
          (IsColimit.comp_coconePointUniqueUpToIso_hom
            (colimit.isColimit F.diagram)
            F.isColimit n).symm)
  exact ShortComplex.shortExact_of_iso e (sequentialTelescope_shortExact F.diagram)

end
end PropertyPFiltration
end
