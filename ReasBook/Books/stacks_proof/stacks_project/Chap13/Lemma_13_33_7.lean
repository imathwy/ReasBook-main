import Mathlib
import StacksProject_2024.Chap13.Definition_13_33_1
import StacksProject_2024.Chap13.Lemma_13_33_5
import StacksProject_2024.Chap13.Lemma_13_33_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.CoproductsFromFiniteFiltered
open CategoryTheory.Pretriangulated
open DerivedCategory

universe w v u

noncomputable section

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
variable [HasColimitsOfShape ℕ 𝒜] [HasExactColimitsOfShape ℕ 𝒜]

/- Domain-style sampling for Lemma 13.33.7:
- primary domain: homotopy colimits in derived categories, obtained from the telescope triangle of
  a sequential diagram of cochain complexes;
- inspected owner declarations:
  `CategoryTheory.IsHomotopyColimitOf`,
  `CategoryTheory.derivedCategory_Q_preserves_countableCoproduct`,
  `CategoryTheory.sequentialTelescope_shortExact`;
- best owner abstraction:
  the source-facing datum is the sequential diagram `S : ℕ ⥤ CochainComplex 𝒜 ℤ`, and the
  canonical owner for the conclusion is `IsHomotopyColimitOf (S ⋙ DerivedCategory.Q)`;
- primitive-vs-derived split:
  the primitive data are only the diagram `S`;
  the countable coproduct in `DerivedCategory 𝒜` and the distinguished telescope triangle are
  derived API coming from the Chapter 13 coproduct-preservation bridge and the exact telescope
  short exact sequence.

Source/core/bridge triage:
- `source-facing`: the termwise colimit complex represents a homotopy colimit of the image
  sequence in the derived category;
- `core/canonical`: `IsHomotopyColimitOf (S ⋙ DerivedCategory.Q)`;
- `bridge/view`: the local countable-coproduct bridge on `𝒜`, together with
  `derivedCategory_hasCountableCoproducts_of_exactCountableCoproducts`, supplies the owner
  predicate with the needed coproduct of `Q.obj (S.obj n)`. -/

local instance : HasCountableCoproducts 𝒜 := hasCountableCoproducts_of_sequentialColimits

local instance : CountableAB4 𝒜 := by
  let _ : HasFiniteBiproducts 𝒜 := Abelian.hasFiniteBiproducts
  exact CountableAB4.of_countableAB5 𝒜

-- Proof sketch: exact sequential colimits give the short exact telescope sequence
-- `0 ⟶ ⨿ L_n^• ⟶ ⨿ L_n^• ⟶ colim L_n^• ⟶ 0`. Applying the localization functor
-- `CochainComplex 𝒜 ℤ ⥤ DerivedCategory 𝒜` and the canonical distinguished-triangle construction
-- for short exact sequences yields the standard telescope triangle, so the termwise colimit is
-- best recorded via the canonical owner `IsHomotopyColimitOf`.
/-- Helper for Lemma 13.33.7: the coproduct comparison identifies the `n`th localized summand map
with the image of the `n`th summand injection before localization. -/
lemma termwise_colimit_coproduct_comparison_ι
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) (n : ℕ) :
    Sigma.ι (S ⋙ Q).obj n ≫ (PreservesCoproduct.iso Q S.obj).inv =
      Q.map (Sigma.ι S.obj n) := by
  -- Rewrite the coproduct comparison through `sigmaComparison`, then cancel the inverse
  -- comparison on the right.
  have hhom :
      (PreservesCoproduct.iso Q S.obj).hom =
        inv (sigmaComparison Q S.obj) := by
    apply IsIso.eq_inv_of_hom_inv_id
    simpa [PreservesCoproduct.inv_hom] using
      (Iso.inv_hom_id (PreservesCoproduct.iso Q S.obj))
  have hι :
      Q.map (Sigma.ι S.obj n) ≫ (PreservesCoproduct.iso Q S.obj).hom =
        Sigma.ι (S ⋙ Q).obj n := by
    rw [hhom]
    change Q.map (Sigma.ι S.obj n) ≫ inv (sigmaComparison Q S.obj) =
      Sigma.ι (fun x ↦ Q.obj (S.obj x)) n
    exact Limits.map_ι_comp_inv_sigmaComparison Q S.obj n
  apply (cancel_mono (PreservesCoproduct.iso Q S.obj).hom).1
  simpa [Category.assoc] using hι.symm

/-- Helper for Lemma 13.33.7: after transporting the coproduct of the localized complexes to the
localized coproduct, the telescope map agrees with the localized telescope map. -/
lemma termwise_colimit_telescope_map_comm (S : ℕ ⥤ CochainComplex 𝒜 ℤ) :
    sequentialTelescopeMap (S ⋙ Q) ≫ (PreservesCoproduct.iso Q S.obj).inv =
      (PreservesCoproduct.iso Q S.obj).inv ≫ Q.map (sequentialTelescopeMap S) := by
  -- Check the transported telescope map on each coproduct summand of `∐ Q(Sₙ)`.
  apply Limits.Sigma.hom_ext
  intro n
  rw [Sigma.ι_comp_sequentialTelescopeMap_assoc, Preadditive.sub_comp]
  simp [Functor.map_sub, Functor.map_comp, Sigma.ι_comp_sequentialTelescopeMap_assoc,
    Category.assoc, termwise_colimit_coproduct_comparison_ι]

/-- Helper for Lemma 13.33.7: the coproduct map to the localized colimit is the coproduct desc of
the localized colimit structure maps. -/
lemma termwise_colimit_explicit_triangle_comm₂ (S : ℕ ⥤ CochainComplex 𝒜 ℤ) :
    Limits.Sigma.desc (fun n ↦ Q.map (colimit.ι S n)) ≫ (Iso.refl (Q.obj (colimit S))).hom =
      (PreservesCoproduct.iso Q S.obj).symm.hom ≫ Q.map (Limits.Sigma.desc (colimit.ι S)) := by
  -- The coproduct comparison is exactly the map that identifies the localized termwise coproduct
  -- with the coproduct object in the derived category.
  simpa using
    (Limits.sigmaComparison_map_desc Q S.obj (colimit S) (colimit.ι S)).symm

/-- Helper for Lemma 13.33.7: the shifted coproduct comparison cancels the auxiliary connecting
morphism back to the short-exact-sequence connecting morphism. -/
lemma termwise_colimit_explicit_triangle_comm₃ (S : ℕ ⥤ CochainComplex 𝒜 ℤ) :
    (triangleOfSESδ (sequentialTelescope_shortExact S) ≫
        ((PreservesCoproduct.iso Q S.obj).hom⟦(1 : ℤ)⟧')) ≫
      ((PreservesCoproduct.iso Q S.obj).symm.hom⟦(1 : ℤ)⟧') =
    (Iso.refl (Q.obj (colimit S))).hom ≫ triangleOfSESδ (sequentialTelescope_shortExact S) := by
  -- Move the inverse comparison through the shift, then use `hom_inv_id`.
  have hshift :
      ((PreservesCoproduct.iso Q S.obj).hom⟦(1 : ℤ)⟧') ≫
          ((PreservesCoproduct.iso Q S.obj).symm.hom⟦(1 : ℤ)⟧') =
        𝟙 _ := by
    simpa using
      congrArg
        (fun k ↦ (shiftFunctor (DerivedCategory 𝒜) (1 : ℤ)).map k)
        (Iso.hom_inv_id (PreservesCoproduct.iso Q S.obj))
  calc
    (triangleOfSESδ (sequentialTelescope_shortExact S) ≫
        ((PreservesCoproduct.iso Q S.obj).hom⟦(1 : ℤ)⟧')) ≫
        ((PreservesCoproduct.iso Q S.obj).symm.hom⟦(1 : ℤ)⟧') =
      triangleOfSESδ (sequentialTelescope_shortExact S) ≫ 𝟙 _ := by
        rw [Category.assoc, hshift]
    _ = (Iso.refl (Q.obj (colimit S))).hom ≫ triangleOfSESδ (sequentialTelescope_shortExact S) := by
        simp

/-- Helper for Lemma 13.33.7: the triangle of the telescope short exact sequence is isomorphic to
the source-facing telescope triangle on the localized sequential diagram. -/
noncomputable def termwise_colimit_explicit_triangle_iso (S : ℕ ⥤ CochainComplex 𝒜 ℤ) :
    Triangle.mk
        (sequentialTelescopeMap (S ⋙ Q))
        (Limits.Sigma.desc (fun n ↦ Q.map (colimit.ι S n)))
        (triangleOfSESδ (sequentialTelescope_shortExact S) ≫
          ((PreservesCoproduct.iso Q S.obj).hom⟦(1 : ℤ)⟧')) ≅
      DerivedCategory.triangleOfSES (sequentialTelescope_shortExact S) :=
  Triangle.isoMk _ _
    (PreservesCoproduct.iso Q S.obj).symm
    (PreservesCoproduct.iso Q S.obj).symm
    (Iso.refl _)
    (termwise_colimit_telescope_map_comm (𝒜 := 𝒜) S)
    (termwise_colimit_explicit_triangle_comm₂ (𝒜 := 𝒜) S)
    (termwise_colimit_explicit_triangle_comm₃ (𝒜 := 𝒜) S)

/-- Helper for Lemma 13.33.7: the explicit telescope triangle for the localized sequential
diagram is distinguished. -/
lemma termwise_colimit_explicit_triangle_distinguished (S : ℕ ⥤ CochainComplex 𝒜 ℤ) :
    Triangle.mk
        (sequentialTelescopeMap (S ⋙ Q))
        (Limits.Sigma.desc (fun n ↦ Q.map (colimit.ι S n)))
        (triangleOfSESδ (sequentialTelescope_shortExact S) ≫
          ((PreservesCoproduct.iso Q S.obj).hom⟦(1 : ℤ)⟧')) ∈
      distTriang (DerivedCategory 𝒜) := by
  -- Transport distinguishedness across the explicit triangle isomorphism from the telescope short
  -- exact sequence.
  refine isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished
    (sequentialTelescope_shortExact S)) _ ?_
  exact termwise_colimit_explicit_triangle_iso (𝒜 := 𝒜) S

/-- Lemma 13.33.7: if an abelian category admits exact sequential colimits, then the termwise
colimit of a sequential system of cochain complexes is a homotopy colimit of the induced
sequential diagram in the derived category. -/
@[stacks 0949]
theorem termwise_colimit_is_homotopy_colimit (S : ℕ ⥤ CochainComplex 𝒜 ℤ) :
    IsHomotopyColimitOf (S ⋙ Q) (Q.obj (colimit S)) := by
  -- Use the canonical telescope triangle coming from the short exact telescope sequence.
  refine ⟨Limits.Sigma.desc (fun n ↦ Q.map (colimit.ι S n)),
    triangleOfSESδ (sequentialTelescope_shortExact S) ≫
      ((PreservesCoproduct.iso Q S.obj).hom⟦(1 : ℤ)⟧'),
    termwise_colimit_explicit_triangle_distinguished (𝒜 := 𝒜) S⟩

/-- The canonical map from the telescope coproduct `∐ Q(Sₙ)` to the derived image of the termwise
colimit complex. This is the source-facing map used when the homotopy-colimit presentation from
`termwise_colimit_is_homotopy_colimit` is expressed by the actual short exact telescope sequence of
`S`. -/
def termwise_colimit_presentation_map (S : ℕ ⥤ CochainComplex 𝒜 ℤ) :
    ∐ (fun n ↦ Q.obj (S.obj n)) ⟶ Q.obj (colimit S) :=
  (PreservesCoproduct.iso Q S.obj).inv ≫ Q.map (Limits.Sigma.desc (colimit.ι S))

/-- Helper for Lemma 13.33.7: the source-facing presentation map is the coproduct desc of the
localized structure maps to the colimit. -/
lemma termwise_colimit_presentation_map_eq_desc (S : ℕ ⥤ CochainComplex 𝒜 ℤ) :
    termwise_colimit_presentation_map S =
      Limits.Sigma.desc (fun n ↦ Q.map (colimit.ι S n)) := by
  -- This is exactly the coproduct comparison formula for the localized cocone.
  simpa [termwise_colimit_presentation_map] using
    Limits.sigmaComparison_map_desc Q S.obj (colimit S) (colimit.ι S)

/-- The connecting morphism in the canonical telescope triangle presenting `Q.obj (colimit S)` as
a homotopy colimit of `S ⋙ Q`. -/
def termwise_colimit_presentation_connecting (S : ℕ ⥤ CochainComplex 𝒜 ℤ) :
    Q.obj (colimit S) ⟶ (∐ fun n ↦ Q.obj (S.obj n))⟦(1 : ℤ)⟧ :=
  triangleOfSESδ (sequentialTelescope_shortExact S) ≫
    ((PreservesCoproduct.iso Q S.obj).hom⟦(1 : ℤ)⟧')

-- Proof sketch: start from the distinguished triangle `triangleOfSES` attached to the canonical
-- telescope short exact sequence of `S`, then transport its first two objects from
-- `Q.obj (∐ Sₙ)` to the actual coproduct `∐ Q(Sₙ)` using `PreservesCoproduct.iso Q S.obj`.
/-- The canonical telescope triangle for the termwise colimit complex is distinguished. This is
the explicit source-facing presentation underlying `termwise_colimit_is_homotopy_colimit`. -/
theorem termwise_colimit_presentation_distinguished (S : ℕ ⥤ CochainComplex 𝒜 ℤ) :
    Triangle.mk
        (sequentialTelescopeMap (S ⋙ Q))
        (termwise_colimit_presentation_map S)
        (termwise_colimit_presentation_connecting S) ∈
      distTriang (DerivedCategory 𝒜) := by
  -- Rewrite the source-facing presentation to the explicit telescope triangle already proved
  -- above.
  rw [termwise_colimit_presentation_map_eq_desc]
  exact termwise_colimit_explicit_triangle_distinguished (𝒜 := 𝒜) S

end

end CategoryTheory
