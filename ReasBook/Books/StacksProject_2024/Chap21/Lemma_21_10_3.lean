import Mathlib
import Mathlib.Algebra.Homology.CochainComplexPlus
import StacksProject_2024.Chap13.Lemma_13_20_3
import StacksProject_2024.Chap21.Lemma_21_9_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat]
variable [EnoughInjectives (Sheaf J AddCommGrpCat)]

attribute [local instance] HasDerivedCategory.standard

section

variable (U : C) [Limits.HasFiniteProducts (Over U)]
variable {ι : Type (max u v)} (family : ι → Over U)

/-- The Čech complex functor on abelian sheaves, obtained by forgetting to abelian presheaves and
then applying the Čech complex on the slice site over `U`. -/
abbrev cechComplexOnAbelianSheaves :
    Sheaf J AddCommGrpCat ⥤ CochainComplex AddCommGrpCat ℕ :=
  sheafToPresheaf J AddCommGrpCat ⋙ cechComplexOnPresheaves U family

-- Proof sketch: extending an `ℕ`-indexed cochain complex along `embeddingUpNat` produces a
-- `ℤ`-indexed cochain complex that is strictly zero in negative degrees, so it is bounded below.
/-- The extended Čech complex of an abelian sheaf is bounded below as a `\mathbf Z`-indexed
cochain complex. -/
theorem cechComplexOnAbelianSheavesToPlus_obj_mem
    (F : Sheaf J AddCommGrpCat) :
    CochainComplex.plus AddCommGrpCat
      (((cechComplexOnAbelianSheaves U family).obj F).extend ComplexShape.embeddingUpNat) := sorry

/-- The Čech complex functor on abelian sheaves, regarded as a bounded-below cochain-complex
functor so that it can be viewed in `D^+(\mathbf Z)`. -/
abbrev cechComplexOnAbelianSheavesToPlus :
    Sheaf J AddCommGrpCat ⥤ CochainComplex.Plus AddCommGrpCat :=
  (CochainComplex.plus AddCommGrpCat).lift
    ((cechComplexOnAbelianSheaves U family) ⋙
      (ComplexShape.embeddingUpNat).extendFunctor AddCommGrpCat)
    (fun F ↦ cechComplexOnAbelianSheavesToPlus_obj_mem U family F)

/-- The functor sending an abelian sheaf to its Čech complex for the covering `family`, viewed as
an object of the bounded-below derived category `D^+(\mathbf Z)`. -/
abbrev abelianSheafCechDerivedFunctor :
    Sheaf J AddCommGrpCat ⥤ boundedBelowDerivedCategory AddCommGrpCat :=
  cechComplexOnAbelianSheavesToPlus U family ⋙
    boundedBelowCochainComplexToDerivedBelow (𝟭 AddCommGrpCat)

/-- Sections over a fixed object of the site define an additive functor on abelian sheaves. -/
local instance sheafSectionsFunctor_additive :
    (((sheafSections J AddCommGrpCat).obj (op U))).Additive := sorry

/-- The bounded-below derived global-sections functor `RΓ(U,-)` on abelian sheaves over the site.
-/
abbrev abelianSheafDerivedSectionsFunctor :
    Sheaf J AddCommGrpCat ⥤ boundedBelowDerivedCategory AddCommGrpCat :=
  degreeZeroToBoundedBelowDerived ((sheafSections J AddCommGrpCat).obj (op U))

/-- The degree-`p` Čech cohomology functor on abelian sheaves for the covering `family`. -/
abbrev abelianSheafCechCohomologyFunctor (p : ℕ) :
    Sheaf J AddCommGrpCat ⥤ AddCommGrpCat :=
  sheafToPresheaf J AddCommGrpCat ⋙ (cechCohomologyDegree U family p).obj

/-- The degree-`p` site cohomology functor `\mathcal F \mapsto H^p(U, \mathcal F)` on abelian
sheaves. -/
abbrev abelianSheafSiteCohomologyFunctor (p : ℕ) :
    Sheaf J AddCommGrpCat ⥤ AddCommGrpCat :=
  ((sheafSections J AddCommGrpCat).obj (op U)).rightDerived p

-- Proof sketch: choose an injective resolution `ℱ ⟶ ℐ^•`, form the double complex
-- `\check{\mathcal C}^\bullet(\mathcal U, \mathcal I^\bullet)`, and compare both
-- `\check{\mathcal C}^\bullet(\mathcal U, \mathcal F)` and `\Gamma(U,\mathcal I^\bullet)` with
-- its total complex. Lemma `21.10.2` gives acyclicity of the rows for injectives, so
-- Lemma `12.25.4` makes the comparison from sections a quasi-isomorphism. Passing to `D^+`
-- yields the required natural transformation from the Čech complex functor to `RΓ(U,-)`.
/-- Lemma 21.10.3: for a covering family `family : ι → Over U` on the slice site `(C / U,
J.over U)`, there exists a natural transformation from the Čech complex functor
`\check{\mathcal C}^\bullet(\mathcal U,-)` to the bounded-below derived global-sections functor
`RΓ(U,-)` on abelian sheaves, both viewed as functors `\mathrm{Ab}(C) ⥤ D^+(\mathbf Z)`. -/
theorem cechDerivedFunctor_exists_natTrans_to_derivedSections
    (hfamily : (J.over U).CoversTop family) :
    ∃ τ :
      (abelianSheafCechDerivedFunctor U family :
        Sheaf J AddCommGrpCat ⥤ boundedBelowDerivedCategory AddCommGrpCat) ⟶
        abelianSheafDerivedSectionsFunctor U,
      True := sorry

-- Proof sketch: apply the cohomology functor `H^p` to the derived-category transformation from
-- `cechDerivedFunctor_exists_natTrans_to_derivedSections`. The source identifies with the degree
-- `p` Čech cohomology functor by construction of the bounded-below complex, and the target is the
-- `p`-th right derived functor of sections, i.e. `H^p(U,-)`.
/-- The derived Čech-to-cohomology comparison induces a degree-`p` natural transformation
`\check H^p(U,-) \to H^p(U,-)` on abelian sheaves. -/
theorem cechCohomology_exists_natTrans_to_siteCohomology
    (hfamily : (J.over U).CoversTop family) (p : ℕ) :
    ∃ τ :
      (abelianSheafCechCohomologyFunctor U family p :
        Sheaf J AddCommGrpCat ⥤ AddCommGrpCat) ⟶
        abelianSheafSiteCohomologyFunctor U p,
      True := sorry

end

end CategoryTheory
