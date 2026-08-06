import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_7_2

open CategoryTheory

universe u w

/-
Semantic recall: `lean_leansearch` for an omega-spectrum replacement API did not return a useful
project-level hit. Repo inspection shows `Prespectrum` now carries the source-facing morphism
surface `T ⟶ U`, while a stable-equivalence owner has not yet been formalized. The file therefore
records the
chosen omega-spectrum replacement data via `OmegaSpectrumModel TO`, including the source-facing
stable-homotopy-group replacement isomorphisms, and names the associated prespectrum as
`MO TO model`.
-/

/-- Auxiliary data for a chosen omega-prespectrum equipped with a comparison map from the Thom
prespectrum `TO`, together with the replacement condition required in Definition 25.6.1: the
comparison map itself induces isomorphisms on all stable homotopy groups. -/
structure OmegaSpectrumModel (TO : Prespectrum.{u, w}) where
  toPrespectrum : Prespectrum.{u, w}
  comparisonMap : TO ⟶ toPrespectrum
  comparisonMap_isStableEquivalence : Prespectrum.IsStableEquivalence comparisonMap
  isOmegaPrespectrum : OmegaPrespectrum toPrespectrum

/-- The underlying prespectrum of an omega-spectrum model of `TO` is an
`OmegaPrespectrum`. -/
instance omegaPrespectrum_toPrespectrum
    (TO : Prespectrum.{u, w}) (model : OmegaSpectrumModel TO) :
    OmegaPrespectrum model.toPrespectrum :=
  model.isOmegaPrespectrum

/-- Definition 25.6.1: `MO` is the spectrum associated to the Thom prespectrum `TO` after
replacing `TO` by an Omega-spectrum model. In the current repo, this associated spectrum is the
chosen replacement prespectrum carried by `model`. -/
abbrev MO (TO : Prespectrum.{u, w}) (model : OmegaSpectrumModel TO) : Prespectrum.{u, w} :=
  model.toPrespectrum

/-- The associated spectrum `MO TO model` is an `OmegaPrespectrum`. -/
instance omegaPrespectrum_MO
    (TO : Prespectrum.{u, w}) (model : OmegaSpectrumModel TO) :
    OmegaPrespectrum (MO TO model) :=
  model.isOmegaPrespectrum

/-- The chosen omega-spectrum replacement of `TO` comes with a direct comparison map
`TO ⟶ MO TO model`. -/
abbrev moComparisonMap
    (TO : Prespectrum.{u, w}) (model : OmegaSpectrumModel TO) :
    TO ⟶ MO TO model :=
  model.comparisonMap

/-- Unfolding `moComparisonMap` recovers the comparison morphism stored in the chosen
omega-spectrum model. -/
@[simp]
theorem moComparisonMap_def
    (TO : Prespectrum.{u, w}) (model : OmegaSpectrumModel TO) :
    moComparisonMap TO model = model.comparisonMap :=
  rfl

/-- The isomorphism on degree-`n` stable homotopy groups induced by the comparison map
`TO ⟶ MO TO model`. -/
noncomputable def moStableHomotopyGroupIso
    (TO : Prespectrum.{u, w}) (model : OmegaSpectrumModel TO) (n : ℤ) :
    Prespectrum.stableHomotopyGroup TO n ≅
      Prespectrum.stableHomotopyGroup (MO TO model) n :=
  letI : IsIso (Prespectrum.stableHomotopyGroupMap model.comparisonMap n) :=
    model.comparisonMap_isStableEquivalence n
  asIso (Prespectrum.stableHomotopyGroupMap model.comparisonMap n)

/-- The stable-homotopy-group isomorphism for `MO` has underlying map equal to the map induced by
the comparison morphism. -/
@[simp] theorem moStableHomotopyGroupIso_hom
    (TO : Prespectrum.{u, w}) (model : OmegaSpectrumModel TO) (n : ℤ) :
    (moStableHomotopyGroupIso TO model n).hom =
      Prespectrum.stableHomotopyGroupMap model.comparisonMap n := by
  simp [moStableHomotopyGroupIso]

/-- Unfolding `MO` recovers the chosen replacement prespectrum. -/
@[simp]
theorem MO_def (TO : Prespectrum.{u, w}) (model : OmegaSpectrumModel TO) :
    MO TO model = model.toPrespectrum :=
  rfl
