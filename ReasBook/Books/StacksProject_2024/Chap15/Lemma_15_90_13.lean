import StacksProject_2024.Chap15.Lemma_15_90_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u w

section

variable {R : Type u} [CommRing R]
variable {S : Type u} [CommRing S] [Algebra R S]
variable {t : ℕ} (f : Fin t → R)

/- Domain-style sampling:
- primary domain: formal glueing for module categories, with the genuine glueing category carrying
  comparison and overlap isomorphisms.
- inspected owner declarations:
  `FormalGlueingDatum`,
  `FormalGlueingDatum.Hom`,
  `AwayModuleGlueing`,
  `LocalizedModule.equivTensorProduct`,
  `formalGlueingCan`.
- best owner abstraction:
  the source-facing category `FormalGlueingDatum f` from `Remark 15.90.10`, with the overlap side
  built from the chapter-local localization-glueing owner `AwayModuleGlueing` and with genuine
  glueing morphisms encoded by `FormalGlueingDatum.Hom`.
- primitive data:
  the base `S`-module, the localized `R_(fᵢ)`-modules, the comparison isomorphisms, and the
  overlap isomorphisms.
- derived API in this file:
  exactness of `formalGlueingCan S f` under flatness and preservation of colimits by
  `formalGlueingCan S f`.
- layer:
  `source-facing`; this lemma is about the actual glueing category `Glue(R → S, f₁, …, fₜ)`, not a
  surrogate product presentation.
-/

-- Proof sketch: under flatness, localization and tensor product are exact on the comparison and
-- overlap terms, so the canonical functor `Can` is exact on the abelian glueing category.
/-- Lemma 15.90.13 (2): if `R → S` is flat, then the canonical formal glueing functor `Can` is
exact. -/
theorem formalGlueingCan_exact [Module.Flat R S] :
    exactFunctor (ModuleCat.{max u w} R) (Glue S f) (formalGlueingCan S f) := by
  sorry

/-- Lemma 15.90.13 (3): the canonical formal glueing functor preserves all colimits because it is
a left adjoint by Lemma `15.90.11`. -/
noncomputable instance formalGlueingCan_preservesColimits :
    PreservesColimits (formalGlueingCan S f) :=
  inferInstance

end
