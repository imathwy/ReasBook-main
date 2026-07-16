import Mathlib
import StacksProject_2024.stacks_project.Chap13.Definition_13_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits HomologicalComplex₂

noncomputable section

universe v u

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling:
- primary domain: cohomological double complexes and their columnwise injective resolutions;
- sampled owner declarations:
  `CochainComplex.Plus`,
  `CochainComplex.plus_iff`,
  `CategoryTheory.InjectiveResolution`,
  `CategoryTheory.InjectiveResolution.cochainComplex`,
  `CategoryTheory.InjectiveResolution.ι'`,
  `CochainComplex.Plus (CochainComplex 𝒜 ℤ)`;
- best owner abstraction: the source-facing object is a Cartan-Eilenberg resolution, but the
  bounded-below source complex and the horizontal boundedness of the double complex should be
  owned by the canonical `CochainComplex.Plus` owners, while the row/image-column constructions
  live on the ambient double complex `HomologicalComplex₂`, the kernel/image/homology columns are
  owned by the canonical `HomologicalComplex.cycles` / `image` / `.homology` APIs, and the
  chosen resolution of each single object should be owned by `CategoryTheory.InjectiveResolution`;
  horizontally bounded-below double complex, its augmentation from `K.obj`, and the chosen
  column/cycles/image/homology objectwise injective resolutions with comparison isos;
- derived API here: the bottom row, the horizontal image columns, and the induced augmentations.

This file is therefore `source-facing`, but its repeated row/column views should live on
the ambient `HomologicalComplex₂`/`HomologicalComplex` owners rather than through exact-interface
local aliases; the single-object resolutions should be read through the canonical owner
`CategoryTheory.InjectiveResolution`, and the vertical bounded-below property should be derived
from those canonical resolutions rather than stored as parallel primitive data.
-/

/-- Definition 13.21.1: a Cartan-Eilenberg resolution of a bounded-below cochain complex
`K : CochainComplex.Plus 𝒜` in
an abelian category consists of a double complex `I^{\bullet,\bullet}` and an augmentation
`ε : K^• ⟶ I^{\bullet,0}` such that the double complex is horizontally bounded below, each column
resolves the corresponding term of `K^•`, and likewise the cycles, image, and
horizontal-homology columns resolve the corresponding kernel, image, and cohomology objects of
`K^•`. -/
structure CartanEilenbergResolution (K : CochainComplex.Plus 𝒜) where
  /-- The horizontally bounded-below double complex `I^{\bullet,\bullet}` underlying the
  Cartan-Eilenberg resolution. -/
  doubleComplex : CochainComplex.Plus (CochainComplex 𝒜 ℤ)
  /-- The augmentation `ε : K^• ⟶ I^{\bullet,0}` into the bottom row. -/
  ε : K.obj ⟶ (flip doubleComplex.obj).X 0
  /-- A chosen injective resolution of the object `K^p`, owned by
  `CategoryTheory.InjectiveResolution`. -/
  columnResolution (p : ℤ) : CategoryTheory.InjectiveResolution (K.obj.X p)
  /-- The chosen `p`-th injective resolution is identified with the actual column
  `I^{p,\bullet}`. -/
  columnIso (p : ℤ) : (columnResolution p).cochainComplex ≅ doubleComplex.obj.X p
  /-- The degree-zero component of the column augmentation agrees with the bottom-row
  augmentation. -/
  columnAugmentation_f_zero (p : ℤ) :
    ((columnResolution p).ι' ≫ (columnIso p).hom).f 0 = ε.f p
  /-- A chosen injective resolution of the object `ker(d_K^p)`, owned by
  `K.obj.cycles p`. -/
  cyclesResolution (p : ℤ) : CategoryTheory.InjectiveResolution (K.obj.cycles p)
  /-- The chosen cycles-column injective resolution is identified with the actual cycles complex,
  i.e. the kernel of `d_1^{p,\bullet}`. -/
  cyclesIso (p : ℤ) :
    (cyclesResolution p).cochainComplex ≅ doubleComplex.obj.cycles p
  /-- A chosen injective resolution of the object `im(d_K^p)`. -/
  imageResolution (p : ℤ) :
    CategoryTheory.InjectiveResolution (image (K.obj.d p (p + 1)))
  /-- The chosen image-column injective resolution is identified with the actual image complex
  of `d_1^{p,\bullet}`. -/
  imageIso (p : ℤ) :
    (imageResolution p).cochainComplex ≅ image (doubleComplex.obj.d p (p + 1))
  /-- A chosen injective resolution of the object `H^p(K^•)`. -/
  homologyResolution (p : ℤ) : CategoryTheory.InjectiveResolution (K.obj.homology p)
  /-- The chosen horizontal-homology injective resolution is identified with the actual complex
  `H_I^p(I^{\bullet,\bullet})`. -/
  homologyIso (p : ℤ) :
    (homologyResolution p).cochainComplex ≅ doubleComplex.obj.homology p

variable {K : CochainComplex.Plus 𝒜}

namespace CartanEilenbergResolution

/-- Every column of a Cartan-Eilenberg resolution is zero in negative vertical degrees. -/
theorem vertical_isStrictlyGE (I : CartanEilenbergResolution K) (p : ℤ) :
    CochainComplex.IsStrictlyGE (I.doubleComplex.obj.X p) 0 := by
  let _ : CochainComplex.IsStrictlyGE ((I.columnResolution p).cochainComplex) 0 := inferInstance
  simpa using CochainComplex.isStrictlyGE_of_iso (I.columnIso p) 0

end CartanEilenbergResolution

end
