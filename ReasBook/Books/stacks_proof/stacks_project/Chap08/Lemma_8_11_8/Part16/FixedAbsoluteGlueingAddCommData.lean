import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part16.UnderlyingAbsoluteGlueingBand

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

/-- Helper for Chap08 Lemma 8 11 8/Part16: the fixed absolute-glueing additive reconstruction
package for a single source datum. -/
abbrev fixedAbsoluteGlueingAddCommSheafData
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J) : Prop :=
  ∃ G : Sheaf J AddCommGrpCat.{max u v},
    ∃ _forgetIso :
      (G.1 ⋙ forget AddCommGrpCat.{max u v}) ≅
        (absoluteGlueingReconstruction (J := J) F).1,
      ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
        G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparison y

/-- Helper for Chap08 Lemma 8 11 8/Part16: component data for a reconstructed additive sheaf
package as fixed absolute-glueing additive reconstruction data. -/
theorem fixedAbsoluteGlueingAddCommSheafDataOfComponents
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (G : Sheaf J AddCommGrpCat.{max u v})
    (forgetIso :
      (G.1 ⋙ forget AddCommGrpCat.{max u v}) ≅
        (absoluteGlueingReconstruction (J := J) F).1)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x)
    (compatibility : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparison y) :
    fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F := by
  -- The fixed-data predicate is the component package itself; this lemma records the stable
  -- assembly point that future slicewise AddComm reconstruction data should target.
  exact ⟨G, forgetIso, comparison, compatibility⟩

/-- Helper for Chap08 Lemma 8 11 8/Part16: fixed additive reconstruction data transports
across an isomorphism of the underlying absolute-glueing datum. -/
theorem fixedAbsoluteGlueingAddCommSheafDataOfIso
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {F F' : GrothendieckTopology.AbsoluteGlueing J} (e : F ≅ F')
    (hfixed : fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F) :
    fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F' := by
  -- Transport only the auxiliary forgetful comparison with the reconstructed Type-valued sheaf;
  -- the global AddComm sheaf and its local automorphism-sheaf comparisons are unchanged.
  obtain ⟨G, forgetIso, comparison, compatibility⟩ := hfixed
  let E : Sheaf J (Type (max u v)) ≌ GrothendieckTopology.AbsoluteGlueing J :=
    (GrothendieckTopology.sheafToAbsoluteGlueingFunctor (J := J)).asEquivalence
  let Riso :
      absoluteGlueingReconstruction (J := J) F ≅
        absoluteGlueingReconstruction (J := J) F' :=
    E.inverse.mapIso e
  let forgetIso' :
      (G.1 ⋙ forget AddCommGrpCat.{max u v}) ≅
        (absoluteGlueingReconstruction (J := J) F').1 :=
    { hom := forgetIso.hom ≫ Riso.hom.1
      inv := Riso.inv.1 ≫ forgetIso.inv
      hom_inv_id := by
        simp [Category.assoc]
      inv_hom_id := by
        simp [Category.assoc] }
  exact ⟨G, forgetIso', comparison, compatibility⟩

/-- Helper for Chap08 Lemma 8 11 8/Part16: fixed absolute-glueing additive data projects to
the global additive sheaf and its conjugation-compatible local comparison family. -/
theorem fixedAbsoluteGlueingAddCommSheafDataComparisonData
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {F : GrothendieckTopology.AbsoluteGlueing J}
    (hfixed : fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v},
      ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
        G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparison y := by
  -- Discard only the auxiliary forgetful comparison with the reconstructed Type sheaf; the
  -- additive sheaf and its local comparison law are exactly the data consumed by `IsGerbeBand`.
  obtain ⟨G, _forgetIso, comparison, compatibility⟩ := hfixed
  exact ⟨G, comparison, compatibility⟩

/-- Helper for Chap08 Lemma 8 11 8/Part16: any fixed absolute-glueing datum with its
underlying comparison family and fixed additive reconstruction packages as source-and-fixed
reconstruction data. -/
theorem sourceAndFixedAdditiveReconstructionDataOfFixedDatum
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hfixed : fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F) :
    ∃ F : GrothendieckTopology.AbsoluteGlueing J,
      ∃ comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
          F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
        ∃ _compatibilityF :
          ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
            comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
              comparisonF y,
          fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F := by
  -- This helper isolates the pure existential packaging step from the source-specific choice of
  -- absolute-glueing datum.
  exact ⟨F, comparisonF, compatibilityF, hfixed⟩

/-- Helper for Chap08 Lemma 8 11 8/Part16: the strengthened source package needed by the
source proof.  Compared with `underlyingAbsoluteGlueingBandData`, this retains the additive
reconstruction for the same absolute-glueing owner.  For the canonical chosen-cover source, this
is where the proof's transition characterization
`γ^V_{T,x} ∘ ρ_f|_T = γ^U_{T,x}` must eventually be recorded and consumed. -/
abbrev underlyingAbsoluteGlueingBandDataWithFixedAddCommSheafData
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) : Prop :=
  ∃ F : GrothendieckTopology.AbsoluteGlueing J,
    ∃ comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
        F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
      ∃ _compatibilityF :
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparisonF y,
        fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F

/-- Helper for Chap08 Lemma 8 11 8/Part16: the strengthened source package forgets to the
underlying absolute-glueing source datum. -/
theorem underlyingAbsoluteGlueingBandDataOfFixedAddCommSource
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (data :
      underlyingAbsoluteGlueingBandDataWithFixedAddCommSheafData
        (𝒮 := 𝒮) hAbelian) :
    underlyingAbsoluteGlueingBandData (𝒮 := 𝒮) hAbelian := by
  obtain ⟨F, comparisonF, compatibilityF, _hfixed⟩ := data
  exact ⟨F, comparisonF, compatibilityF⟩

/-- Helper for Chap08 Lemma 8 11 8/Part16: project the fixed additive reconstruction retained
by the strengthened source package. -/
theorem fixedAbsoluteGlueingAddCommSheafDataOfFixedAddCommSource
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (data :
      underlyingAbsoluteGlueingBandDataWithFixedAddCommSheafData
        (𝒮 := 𝒮) hAbelian) :
    fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian
      (Classical.choose data) := by
  obtain ⟨comparisonF, compatibilityF, hfixed⟩ := Classical.choose_spec data
  exact hfixed

/-- Helper for Chap08 Lemma 8 11 8/Part16: a source-and-fixed reconstruction package forgets
the fixed additive data and leaves the underlying absolute-glueing source datum. -/
theorem underlyingAbsoluteGlueingBandDataOfSourceAndFixedPackage
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (data :
      ∃ F : GrothendieckTopology.AbsoluteGlueing J,
        ∃ comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
            F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
          ∃ _compatibilityF :
            ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
              comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
                comparisonF y,
            fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F) :
    underlyingAbsoluteGlueingBandData (𝒮 := 𝒮) hAbelian := by
  -- The combined package stores the source object first; discard only the additive
  -- reconstruction component.
  obtain ⟨F, comparisonF, compatibilityF, _hfixed⟩ := data
  exact ⟨F, comparisonF, compatibilityF⟩

/-- Helper for Chap08 Lemma 8 11 8/Part16: a source absolute-glueing package and fixed
additive reconstruction for its chosen object assemble the source-and-fixed reconstruction data. -/
theorem sourceAndFixedAdditiveReconstructionDataOfSourceData
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (hsource : underlyingAbsoluteGlueingBandData (𝒮 := 𝒮) hAbelian)
    (hfixed :
      fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian
        (Classical.choose hsource)) :
    ∃ F : GrothendieckTopology.AbsoluteGlueing J,
      ∃ comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
          F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
        ∃ _compatibilityF :
          ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
            comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
              comparisonF y,
          fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F := by
  -- Project the comparison family and its conjugation law from the chosen source package, then
  -- reuse the fixed-datum packager so later source-specific proofs do not repeat this projection.
  have hcomparison :
      ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
          (Classical.choose hsource).obj U ≅
            automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparison y :=
    Classical.choose_spec hsource
  obtain ⟨comparisonF, compatibilityF⟩ := hcomparison
  exact
    sourceAndFixedAdditiveReconstructionDataOfFixedDatum (𝒮 := 𝒮) hAbelian
      (Classical.choose hsource)
      comparisonF
      compatibilityF
      hfixed

/-- Helper for Chap08 Lemma 8 11 8/Part16: a reconstructed additive sheaf package for one
absolute-glueing object is exactly fixed additive reconstruction data for that object. -/
theorem fixedAbsoluteGlueingAddCommSheafDataOfReconstructionPackage
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (data :
      ∃ G : Sheaf J AddCommGrpCat.{max u v},
        ∃ _forgetIso :
          (G.1 ⋙ forget AddCommGrpCat.{max u v}) ≅
            (absoluteGlueingReconstruction (J := J) F).1,
          ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
            G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
            ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
              comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
                comparison y) :
    fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F := by
  -- The fixed-data predicate is definitionally the same reconstructed additive package; keeping
  -- this adapter named makes the remaining source-specific blocker explicit.
  exact data

/-- Helper for Chap08 Lemma 8 11 8/Part16: project the local comparison family and conjugation
law from a chosen underlying absolute-glueing source datum. -/
theorem underlyingSourceComparisonPackage
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (hsource : underlyingAbsoluteGlueingBandData (𝒮 := 𝒮) hAbelian) :
    ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
        (Classical.choose hsource).obj U ≅
          automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
      ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
        comparison x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
          comparison y := by
  -- The chosen source datum stores exactly this dependent comparison package.
  exact Classical.choose_spec hsource

/-- Helper for Chap08 Lemma 8 11 8/Part16: a fixed additive reconstruction theorem for every
compatible absolute-glueing datum specializes to the object chosen by one source datum. -/
theorem fixedAbsoluteGlueingAddCommSheafDataOfUnderlyingSourceFromReconstruction
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (hsource : underlyingAbsoluteGlueingBandData (𝒮 := 𝒮) hAbelian)
    (hreconstructed :
      ∀ (F : GrothendieckTopology.AbsoluteGlueing J)
        (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
          F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x),
        (∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparisonF y) →
          fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F) :
    fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian
      (Classical.choose hsource) := by
  -- Read the comparison family and conjugation law from the chosen source datum, then apply the
  -- reconstruction theorem to exactly that chosen absolute-glueing object.
  obtain ⟨comparisonF, compatibilityF⟩ := Classical.choose_spec hsource
  exact hreconstructed (Classical.choose hsource) comparisonF compatibilityF

/-- Helper for Chap08 Lemma 8 11 8/Part16: a compatible family of sections of a Type-valued
sheaf over a cover has a unique global amalgamation.  This local copy avoids depending on the
currently unavailable `SectionDescent` import chain while keeping the source-proof route explicit.
-/
theorem fixedSectionAmalgamateOfCover_existsUnique
    (R : Sheaf J (Type (max u v))) {U : C} (S : J.Cover U)
    (s : ∀ I : S.Arrow, R.1.obj (op I.Y))
    (hs : ∀ ⦃W : C⦄ ⦃I K : S.Arrow⦄ (a : W ⟶ I.Y) (b : W ⟶ K.Y),
      a ≫ I.f = b ≫ K.f → R.1.map a.op (s I) = R.1.map b.op (s K)) :
    ∃! t : R.1.obj (op U), ∀ I : S.Arrow, R.1.map I.f.op t = s I := by
  let x : ∀ I : S.Arrow, PUnit.{max u v + 1} ⟶ R.1.obj (op I.Y) := fun I _ ↦ s I
  have hcover : Sieve.ofArrows (fun I : S.Arrow ↦ I.Y) (fun I ↦ I.f) ∈ J U := by
    rw [show Sieve.ofArrows (fun I : S.Arrow ↦ I.Y) (fun I ↦ I.f) = (S : Sieve U) by
      ext Y g
      constructor
      · intro hg
        rcases (Sieve.mem_ofArrows_iff
            (fun I : S.Arrow ↦ I.Y) (fun I ↦ I.f) g).mp hg with ⟨I, a, rfl⟩
        exact (S : Sieve U).downward_closed I.hf a
      · intro hg
        exact Sieve.ofArrows_mk _ _ ({ Y := Y, f := g, hf := hg } : S.Arrow)]
    exact S.condition
  have hx :
      ∀ ⦃W : C⦄ ⦃I K : S.Arrow⦄ (a : W ⟶ I.Y) (b : W ⟶ K.Y),
        a ≫ I.f = b ≫ K.f → x I ≫ R.1.map a.op = x K ≫ R.1.map b.op := by
    intro W I K a b h
    funext p
    exact hs a b h
  obtain ⟨g, hg, huniq⟩ :=
    R.2.existsUnique_amalgamation_ofArrows
      (fun I : S.Arrow ↦ I.f) hcover x hx
  refine ⟨g PUnit.unit, ?_, ?_⟩
  · intro I
    exact congrFun (hg I) PUnit.unit
  · intro t ht
    have htfun : (fun _ : PUnit.{max u v + 1} ↦ t) = g := by
      apply huniq
      intro I
      funext p
      exact ht I
    exact congrFun htfun PUnit.unit

/-- Helper for Chap08 Lemma 8 11 8/Part16: choose the global section amalgamating a compatible
family on a cover. -/
noncomputable def fixedSectionAmalgamateOfCover
    (R : Sheaf J (Type (max u v))) {U : C} (S : J.Cover U)
    (s : ∀ I : S.Arrow, R.1.obj (op I.Y))
    (hs : ∀ ⦃W : C⦄ ⦃I K : S.Arrow⦄ (a : W ⟶ I.Y) (b : W ⟶ K.Y),
      a ≫ I.f = b ≫ K.f → R.1.map a.op (s I) = R.1.map b.op (s K)) :
    R.1.obj (op U) :=
  Classical.choose (fixedSectionAmalgamateOfCover_existsUnique R S s hs)

/-- Helper for Chap08 Lemma 8 11 8/Part16: the chosen amalgamation restricts to the prescribed
local section on each cover arrow. -/
theorem fixedSectionAmalgamateOfCover_map
    (R : Sheaf J (Type (max u v))) {U : C} (S : J.Cover U)
    (s : ∀ I : S.Arrow, R.1.obj (op I.Y))
    (hs : ∀ ⦃W : C⦄ ⦃I K : S.Arrow⦄ (a : W ⟶ I.Y) (b : W ⟶ K.Y),
      a ≫ I.f = b ≫ K.f → R.1.map a.op (s I) = R.1.map b.op (s K))
    (I : S.Arrow) :
    R.1.map I.f.op (fixedSectionAmalgamateOfCover R S s hs) = s I := by
  exact (Classical.choose_spec (fixedSectionAmalgamateOfCover_existsUnique R S s hs)).1 I

/-- Helper for Chap08 Lemma 8 11 8/Part16: any section with the prescribed cover restrictions is
the chosen amalgamation. -/
theorem fixedSectionAmalgamateOfCover_ext
    (R : Sheaf J (Type (max u v))) {U : C} (S : J.Cover U)
    (s : ∀ I : S.Arrow, R.1.obj (op I.Y))
    (hs : ∀ ⦃W : C⦄ ⦃I K : S.Arrow⦄ (a : W ⟶ I.Y) (b : W ⟶ K.Y),
      a ≫ I.f = b ≫ K.f → R.1.map a.op (s I) = R.1.map b.op (s K))
    {t : R.1.obj (op U)}
    (ht : ∀ I : S.Arrow, R.1.map I.f.op t = s I) :
    t = fixedSectionAmalgamateOfCover R S s hs := by
  exact
    (Classical.choose_spec (fixedSectionAmalgamateOfCover_existsUnique R S s hs)).2 t ht

/-- Helper for Chap08 Lemma 8 11 8/Part16: a cover in the base site detects equality of sections
of a Type-valued sheaf. -/
theorem fixedSection_eq_of_cover_restrictions
    (R : Sheaf J (Type (max u v))) {U : C} (S : J.Cover U)
    (s t : R.1.obj (op U))
    (hst : ∀ I : S.Arrow, R.1.map I.f.op s = R.1.map I.f.op t) :
    s = t := by
  exact (((isSheaf_iff_isSheaf_of_type J R.1).1 R.property).isSeparated _ S.2).ext
    (fun Y g hg ↦ hst ({ Y := Y, f := g, hf := hg } : S.Arrow))

/-- Helper for Chap08 Lemma 8 11 8/Part16: if a fiber over `U` has an object `x`, then the
terminal sections of the reconstructed Type-valued sheaf over `U` are equivalent to the terminal
sections of the additive automorphism sheaf of `x`. -/
noncomputable def fixedReconstructedTerminalSectionEquiv
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C} (x : 𝒮.p.Fiber U) :
    (absoluteGlueingReconstruction (J := J) F).1.obj (op U) ≃
      (𝒮.automorphismAddCommSheaf hAbelian x).1.obj (op (Over.mk (𝟙 U))) := by
  let T : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))
  let overIso := absoluteGlueingReconstructionOverIso (J := J) F U
  let cmp := comparisonF x
  exact
    { toFun := fun a ↦ (cmp.hom.1.app T) ((overIso.hom.1.app T) a)
      invFun := fun b ↦ (overIso.inv.1.app T) ((cmp.inv.1.app T) b)
      left_inv := by
        intro a
        calc
          (overIso.inv.1.app T)
              ((cmp.inv.1.app T) ((cmp.hom.1.app T) ((overIso.hom.1.app T) a))) =
            (overIso.inv.1.app T) ((overIso.hom.1.app T) a) := by
              have hcmp :
                  (cmp.inv.1.app T) ((cmp.hom.1.app T) ((overIso.hom.1.app T) a)) =
                    (overIso.hom.1.app T) a :=
                congrFun
                  (congrArg (fun η ↦ η.1.app T) cmp.hom_inv_id)
                  ((overIso.hom.1.app T) a)
              exact congrArg (fun z ↦ (overIso.inv.1.app T) z) hcmp
          _ = a := by
              exact
                congrFun
                  (congrArg (fun η ↦ η.1.app T) overIso.hom_inv_id)
                  a
      right_inv := by
        intro b
        calc
          (cmp.hom.1.app T)
              ((overIso.hom.1.app T) ((overIso.inv.1.app T) ((cmp.inv.1.app T) b))) =
            (cmp.hom.1.app T) ((cmp.inv.1.app T) b) := by
              have hover :
                  (overIso.hom.1.app T) ((overIso.inv.1.app T) ((cmp.inv.1.app T) b)) =
                    (cmp.inv.1.app T) b :=
                congrFun
                  (congrArg (fun η ↦ η.1.app T) overIso.inv_hom_id)
                  ((cmp.inv.1.app T) b)
              exact congrArg (fun z ↦ (cmp.hom.1.app T) z) hover
          _ = b := by
              exact
                congrFun
                  (congrArg (fun η ↦ η.1.app T) cmp.inv_hom_id)
                  b }

/-- Helper for Chap08 Lemma 8 11 8/Part16: the additive structure on reconstructed terminal
sections transported from a chosen fiber object's automorphism sheaf. -/
@[reducible]
noncomputable def fixedReconstructedTerminalSectionAddCommGroupOfFiber
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C} (x : 𝒮.p.Fiber U) :
    AddCommGroup ((absoluteGlueingReconstruction (J := J) F).1.obj (op U)) :=
  Equiv.addCommGroup
    (fixedReconstructedTerminalSectionEquiv
      (𝒮 := 𝒮) hAbelian F comparisonF x)

/-- Helper for Chap08 Lemma 8 11 8/Part16: over a base object with a chosen fiber object, the
terminal sections of the reconstructed Type-valued sheaf inherit the abelian group structure
transported from that object's automorphism sheaf. -/
theorem fixedReconstructedTerminalSections_addCommGroup_of_fiber
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C} (x : 𝒮.p.Fiber U) :
    Nonempty (AddCommGroup
      ((absoluteGlueingReconstruction (J := J) F).1.obj (op U))) := by
  exact ⟨fixedReconstructedTerminalSectionAddCommGroupOfFiber
    (𝒮 := 𝒮) hAbelian F comparisonF x⟩

/-- Helper for Chap08 Lemma 8 11 8/Part16: the terminal-section equivalence used to transport the
additive structure preserves addition by construction. -/
theorem fixedReconstructedTerminalSectionEquiv_map_add
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C} (x : 𝒮.p.Fiber U) :
    letI : AddCommGroup ((absoluteGlueingReconstruction (J := J) F).1.obj (op U)) :=
      fixedReconstructedTerminalSectionAddCommGroupOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF x
    ∀ a b,
      fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF x (a + b) =
        fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF x a +
          fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF x b := by
  letI : AddCommGroup ((absoluteGlueingReconstruction (J := J) F).1.obj (op U)) :=
    fixedReconstructedTerminalSectionAddCommGroupOfFiber
      (𝒮 := 𝒮) hAbelian F comparisonF x
  intro a b
  let e := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF x
  change e (e.symm (e a + e b)) = e a + e b
  exact e.apply_symm_apply (e a + e b)

/-- Helper for Chap08 Lemma 8 11 8/Part16: the terminal-section equivalence transported through
the fixed underlying comparison is compatible with conjugation in the fiber. -/
theorem fixedReconstructedTerminalSectionEquiv_conj_apply
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (a : (absoluteGlueingReconstruction (J := J) F).1.obj (op U)) :
    ((automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ).hom.1.app
        (op (Over.mk (𝟙 U))))
      (fixedReconstructedTerminalSectionEquiv
        (𝒮 := 𝒮) hAbelian F comparisonF x a) =
      fixedReconstructedTerminalSectionEquiv
        (𝒮 := 𝒮) hAbelian F comparisonF y a := by
  let T : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))
  let z := (absoluteGlueingReconstructionOverIso (J := J) F U).hom.1.app T a
  have hcompat :=
    congrFun
      (congrArg (fun η ↦ η.1.app T)
        (congrArg Iso.hom
          (compatibilityF (U := U) (x := x) (y := y) φ)))
      z
  simpa [fixedReconstructedTerminalSectionEquiv, T, z, Iso.trans_hom,
    automorphismUnderlyingSheafConj, automorphismUnderlyingSheafConj_hom,
    NatTrans.comp_app] using hcompat

/-- Helper for Chap08 Lemma 8 11 8/Part16: the explicit transported sum on reconstructed
terminal sections is independent of replacing the chosen fiber object by an isomorphic one. -/
theorem fixedReconstructedTerminalSectionEquiv_add_transport_eq_of_morphism
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (a b : (absoluteGlueingReconstruction (J := J) F).1.obj (op U)) :
    let ex := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF x
    let ey := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF y
    ex.symm (ex a + ex b) = ey.symm (ey a + ey b) := by
  let T : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))
  let ex := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF x
  let ey := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF y
  let c := (automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ).hom.1.app T
  apply ey.injective
  calc
    ey (ex.symm (ex a + ex b)) =
        c (ex (ex.symm (ex a + ex b))) := by
          rw [fixedReconstructedTerminalSectionEquiv_conj_apply
            (𝒮 := 𝒮) hAbelian F comparisonF compatibilityF φ
            (ex.symm (ex a + ex b))]
    _ = c (ex a + ex b) := by
          rw [ex.apply_symm_apply]
    _ = c (ex a) + c (ex b) := by
          exact map_add c.hom (ex a) (ex b)
    _ = ey a + ey b := by
          rw [fixedReconstructedTerminalSectionEquiv_conj_apply
            (𝒮 := 𝒮) hAbelian F comparisonF compatibilityF φ a]
          rw [fixedReconstructedTerminalSectionEquiv_conj_apply
            (𝒮 := 𝒮) hAbelian F comparisonF compatibilityF φ b]
    _ = ey (ey.symm (ey a + ey b)) := by
          rw [ey.apply_symm_apply]

/-- Helper for Chap08 Lemma 8 11 8/Part16: the explicit transported zero on reconstructed
terminal sections is independent of replacing the chosen fiber object by an isomorphic one. -/
theorem fixedReconstructedTerminalSectionEquiv_zero_transport_eq_of_morphism
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y) :
    let ex := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF x
    let ey := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF y
    ex.symm 0 = ey.symm 0 := by
  let T : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))
  let ex := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF x
  let ey := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF y
  let c := (automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ).hom.1.app T
  apply ey.injective
  calc
    ey (ex.symm 0) = c (ex (ex.symm 0)) := by
      rw [fixedReconstructedTerminalSectionEquiv_conj_apply
        (𝒮 := 𝒮) hAbelian F comparisonF compatibilityF φ (ex.symm 0)]
    _ = c 0 := by
      rw [ex.apply_symm_apply]
    _ = 0 := map_zero c.hom
    _ = ey (ey.symm 0) := by
      rw [ey.apply_symm_apply]

/-- Helper for Chap08 Lemma 8 11 8/Part16: the explicit transported negation on reconstructed
terminal sections is independent of replacing the chosen fiber object by an isomorphic one. -/
theorem fixedReconstructedTerminalSectionEquiv_neg_transport_eq_of_morphism
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (a : (absoluteGlueingReconstruction (J := J) F).1.obj (op U)) :
    let ex := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF x
    let ey := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF y
    ex.symm (-(ex a)) = ey.symm (-(ey a)) := by
  let T : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))
  let ex := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF x
  let ey := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF y
  let c := (automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ).hom.1.app T
  apply ey.injective
  calc
    ey (ex.symm (-(ex a))) =
        c (ex (ex.symm (-(ex a)))) := by
          rw [fixedReconstructedTerminalSectionEquiv_conj_apply
            (𝒮 := 𝒮) hAbelian F comparisonF compatibilityF φ (ex.symm (-(ex a)))]
    _ = c (-(ex a)) := by
      rw [ex.apply_symm_apply]
    _ = -(c (ex a)) := map_neg c.hom (ex a)
    _ = -(ey a) := by
      rw [fixedReconstructedTerminalSectionEquiv_conj_apply
        (𝒮 := 𝒮) hAbelian F comparisonF compatibilityF φ a]
    _ = ey (ey.symm (-(ey a))) := by
      rw [ey.apply_symm_apply]

/-- Helper for Chap08 Lemma 8 11 8/Part16: the transported sum on reconstructed terminal
sections attached to a chosen object of one fiber. -/
noncomputable def fixedReconstructedTerminalSectionSumOfFiber
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C} (x : 𝒮.p.Fiber U)
    (a b : (absoluteGlueingReconstruction (J := J) F).1.obj (op U)) :
    (absoluteGlueingReconstruction (J := J) F).1.obj (op U) :=
  let e := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF x
  e.symm (e a + e b)

/-- Helper for Chap08 Lemma 8 11 8/Part16: the transported zero on reconstructed terminal
sections attached to a chosen object of one fiber. -/
noncomputable def fixedReconstructedTerminalSectionZeroOfFiber
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C} (x : 𝒮.p.Fiber U) :
    (absoluteGlueingReconstruction (J := J) F).1.obj (op U) :=
  let e := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF x
  e.symm 0

/-- Helper for Chap08 Lemma 8 11 8/Part16: the transported negation on reconstructed terminal
sections attached to a chosen object of one fiber. -/
noncomputable def fixedReconstructedTerminalSectionNegOfFiber
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C} (x : 𝒮.p.Fiber U)
    (a : (absoluteGlueingReconstruction (J := J) F).1.obj (op U)) :
    (absoluteGlueingReconstruction (J := J) F).1.obj (op U) :=
  let e := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF x
  e.symm (-(e a))

/-- Helper for Chap08 Lemma 8 11 8/Part16: the transported fiberwise sum is independent of
replacing the fiber object by an isomorphic one. -/
theorem fixedReconstructedTerminalSectionSumOfFiber_eq_of_morphism
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (a b : (absoluteGlueingReconstruction (J := J) F).1.obj (op U)) :
    fixedReconstructedTerminalSectionSumOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF x a b =
      fixedReconstructedTerminalSectionSumOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF y a b := by
  simpa [fixedReconstructedTerminalSectionSumOfFiber] using
    fixedReconstructedTerminalSectionEquiv_add_transport_eq_of_morphism
      (𝒮 := 𝒮) hAbelian F comparisonF compatibilityF φ a b

/-- Helper for Chap08 Lemma 8 11 8/Part16: the transported fiberwise zero is independent of
replacing the fiber object by an isomorphic one. -/
theorem fixedReconstructedTerminalSectionZeroOfFiber_eq_of_morphism
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y) :
    fixedReconstructedTerminalSectionZeroOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF x =
      fixedReconstructedTerminalSectionZeroOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF y := by
  simpa [fixedReconstructedTerminalSectionZeroOfFiber] using
    fixedReconstructedTerminalSectionEquiv_zero_transport_eq_of_morphism
      (𝒮 := 𝒮) hAbelian F comparisonF compatibilityF φ

/-- Helper for Chap08 Lemma 8 11 8/Part16: the transported fiberwise negation is independent of
replacing the fiber object by an isomorphic one. -/
theorem fixedReconstructedTerminalSectionNegOfFiber_eq_of_morphism
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (a : (absoluteGlueingReconstruction (J := J) F).1.obj (op U)) :
    fixedReconstructedTerminalSectionNegOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF x a =
      fixedReconstructedTerminalSectionNegOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF y a := by
  simpa [fixedReconstructedTerminalSectionNegOfFiber] using
    fixedReconstructedTerminalSectionEquiv_neg_transport_eq_of_morphism
      (𝒮 := 𝒮) hAbelian F comparisonF compatibilityF φ a

/-- Helper for Chap08 Lemma 8 11 8/Part16: restriction maps preserve the transported
fiberwise sums after pulling back the fiber object. -/
abbrev fixedReconstructedTerminalSectionSumRestrictionCompatible
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x) : Prop :=
  ∀ {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U)
    (a b : (absoluteGlueingReconstruction (J := J) F).1.obj (op U)),
      (absoluteGlueingReconstruction (J := J) F).1.map f.op
          (fixedReconstructedTerminalSectionSumOfFiber
            (𝒮 := 𝒮) hAbelian F comparisonF x a b) =
        fixedReconstructedTerminalSectionSumOfFiber
          (𝒮 := 𝒮) hAbelian F comparisonF
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)
          ((absoluteGlueingReconstruction (J := J) F).1.map f.op a)
          ((absoluteGlueingReconstruction (J := J) F).1.map f.op b)

/-- Helper for Chap08 Lemma 8 11 8/Part16: restriction maps preserve the transported
fiberwise zeros after pulling back the fiber object. -/
abbrev fixedReconstructedTerminalSectionZeroRestrictionCompatible
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x) : Prop :=
  ∀ {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U),
      (absoluteGlueingReconstruction (J := J) F).1.map f.op
          (fixedReconstructedTerminalSectionZeroOfFiber
            (𝒮 := 𝒮) hAbelian F comparisonF x) =
        fixedReconstructedTerminalSectionZeroOfFiber
          (𝒮 := 𝒮) hAbelian F comparisonF
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)

/-- Helper for Chap08 Lemma 8 11 8/Part16: restriction maps preserve the transported
fiberwise negations after pulling back the fiber object. -/
abbrev fixedReconstructedTerminalSectionNegRestrictionCompatible
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x) : Prop :=
  ∀ {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U)
    (a : (absoluteGlueingReconstruction (J := J) F).1.obj (op U)),
      (absoluteGlueingReconstruction (J := J) F).1.map f.op
          (fixedReconstructedTerminalSectionNegOfFiber
            (𝒮 := 𝒮) hAbelian F comparisonF x a) =
        fixedReconstructedTerminalSectionNegOfFiber
          (𝒮 := 𝒮) hAbelian F comparisonF
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)
          ((absoluteGlueingReconstruction (J := J) F).1.map f.op a)

/-- Helper for Chap08 Lemma 8 11 8/Part16: the exact restriction compatibility package needed
to turn the reconstructed terminal-section operations into a global additive sheaf.  For the
canonical source this is the Lean form of the source proof's characterization
`γ^V_{T,x} ∘ ρ_f|_T = γ^U_{T,x}`. -/
abbrev fixedReconstructedTerminalSectionOperationRestrictionCompatible
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x) : Prop :=
  fixedReconstructedTerminalSectionSumRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF ∧
    fixedReconstructedTerminalSectionZeroRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF ∧
    fixedReconstructedTerminalSectionNegRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF

/-- Helper for Chap08 Lemma 8 11 8/Part16: assemble the three terminal-section restriction
compatibilities into the normalized operation-compatibility package. -/
theorem fixedReconstructedTerminalSectionOperationRestrictionCompatible_of_components
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (hsum : fixedReconstructedTerminalSectionSumRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    (hzero : fixedReconstructedTerminalSectionZeroRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    (hneg : fixedReconstructedTerminalSectionNegRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF) :
    fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF := by
  exact ⟨hsum, hzero, hneg⟩

/-- Helper for Chap08 Lemma 8 11 8/Part16: terminal-section form of the source proof's
transition characterization.  For a map `f : V ⟶ U`, after identifying terminal sections of the
reconstructed sheaf with automorphisms of `x` and of `f ^* x`, restriction is required to be the
underlying map of an additive homomorphism.  This is the Lean shape of
`γ^V_{V,f^*x} ∘ ρ_f = γ^U_{U,x}` needed to prove operation compatibility. -/
abbrev fixedReconstructedTerminalSectionRestrictionTransportCompatible
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x) : Prop :=
  ∀ {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U),
    ∃ g : (𝒮.automorphismAddCommSheaf hAbelian x).1.obj (op (Over.mk (𝟙 U))) ⟶
        (𝒮.automorphismAddCommSheaf hAbelian
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).1.obj
            (op (Over.mk (𝟙 V))),
      ∀ a : (absoluteGlueingReconstruction (J := J) F).1.obj (op U),
        fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)
            ((absoluteGlueingReconstruction (J := J) F).1.map f.op a) =
          g.hom
            (fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF x a)

/-- Helper for Chap08 Lemma 8 11 8/Part16: the terminal-section transition characterization
implies preservation of all transported terminal-section operations.  The source-specific work is
therefore reduced to proving the preceding `γ/ρ` compatibility for the canonical transition
maps. -/
theorem fixedReconstructedTerminalSectionOperationRestrictionCompatible_of_transport
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (htransport :
      fixedReconstructedTerminalSectionRestrictionTransportCompatible
        (𝒮 := 𝒮) hAbelian F comparisonF) :
    fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF := by
  refine fixedReconstructedTerminalSectionOperationRestrictionCompatible_of_components
    (𝒮 := 𝒮) hAbelian F comparisonF ?hsum ?hzero ?hneg
  · intro U V f x a b
    obtain ⟨g, hg⟩ := htransport f x
    let R : Sheaf J (Type (max u v)) := absoluteGlueingReconstruction (J := J) F
    let xV := ((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x
    let eU := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF x
    let eV := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF xV
    apply eV.injective
    calc
      eV (R.1.map f.op
          (fixedReconstructedTerminalSectionSumOfFiber
            (𝒮 := 𝒮) hAbelian F comparisonF x a b)) =
          g.hom (eU (fixedReconstructedTerminalSectionSumOfFiber
            (𝒮 := 𝒮) hAbelian F comparisonF x a b)) := by
            simpa [R, eU, eV, xV] using
              hg (fixedReconstructedTerminalSectionSumOfFiber
                (𝒮 := 𝒮) hAbelian F comparisonF x a b)
      _ = g.hom (eU a + eU b) := by
            congr 1
            simp [fixedReconstructedTerminalSectionSumOfFiber, eU]
      _ = g.hom (eU a) + g.hom (eU b) := by
            exact map_add g.hom (eU a) (eU b)
      _ = eV (R.1.map f.op a) + eV (R.1.map f.op b) := by
            rw [← hg a, ← hg b]
      _ = eV (fixedReconstructedTerminalSectionSumOfFiber
            (𝒮 := 𝒮) hAbelian F comparisonF xV (R.1.map f.op a) (R.1.map f.op b)) := by
            simp [fixedReconstructedTerminalSectionSumOfFiber, eV]
  · intro U V f x
    obtain ⟨g, hg⟩ := htransport f x
    let R : Sheaf J (Type (max u v)) := absoluteGlueingReconstruction (J := J) F
    let xV := ((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x
    let eU := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF x
    let eV := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF xV
    apply eV.injective
    calc
      eV (R.1.map f.op
          (fixedReconstructedTerminalSectionZeroOfFiber
            (𝒮 := 𝒮) hAbelian F comparisonF x)) =
          g.hom (eU (fixedReconstructedTerminalSectionZeroOfFiber
            (𝒮 := 𝒮) hAbelian F comparisonF x)) := by
            simpa [R, eU, eV, xV] using
              hg (fixedReconstructedTerminalSectionZeroOfFiber
                (𝒮 := 𝒮) hAbelian F comparisonF x)
      _ = g.hom 0 := by
            congr 1
            simp [fixedReconstructedTerminalSectionZeroOfFiber, eU]
      _ = 0 := by
            exact map_zero g.hom
      _ = eV (fixedReconstructedTerminalSectionZeroOfFiber
            (𝒮 := 𝒮) hAbelian F comparisonF xV) := by
            simp [fixedReconstructedTerminalSectionZeroOfFiber, eV]
  · intro U V f x a
    obtain ⟨g, hg⟩ := htransport f x
    let R : Sheaf J (Type (max u v)) := absoluteGlueingReconstruction (J := J) F
    let xV := ((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x
    let eU := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF x
    let eV := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF xV
    apply eV.injective
    calc
      eV (R.1.map f.op
          (fixedReconstructedTerminalSectionNegOfFiber
            (𝒮 := 𝒮) hAbelian F comparisonF x a)) =
          g.hom (eU (fixedReconstructedTerminalSectionNegOfFiber
            (𝒮 := 𝒮) hAbelian F comparisonF x a)) := by
            simpa [R, eU, eV, xV] using
              hg (fixedReconstructedTerminalSectionNegOfFiber
                (𝒮 := 𝒮) hAbelian F comparisonF x a)
      _ = g.hom (-(eU a)) := by
            congr 1
            simp [fixedReconstructedTerminalSectionNegOfFiber, eU]
      _ = -(g.hom (eU a)) := by
            exact map_neg g.hom (eU a)
      _ = -(eV (R.1.map f.op a)) := by
            rw [← hg a]
      _ = eV (fixedReconstructedTerminalSectionNegOfFiber
            (𝒮 := 𝒮) hAbelian F comparisonF xV (R.1.map f.op a)) := by
            simp [fixedReconstructedTerminalSectionNegOfFiber, eV]

/-- Helper for Chap08 Lemma 8 11 8/Part16: project the sum restriction compatibility from the
normalized operation-compatibility package. -/
theorem fixedReconstructedTerminalSectionSumRestrictionCompatible_of_operations
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF) :
    fixedReconstructedTerminalSectionSumRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF := by
  exact hops.1

/-- Helper for Chap08 Lemma 8 11 8/Part16: project the zero restriction compatibility from the
normalized operation-compatibility package. -/
theorem fixedReconstructedTerminalSectionZeroRestrictionCompatible_of_operations
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF) :
    fixedReconstructedTerminalSectionZeroRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF := by
  exact hops.2.1

/-- Helper for Chap08 Lemma 8 11 8/Part16: project the negation restriction compatibility from
the normalized operation-compatibility package. -/
theorem fixedReconstructedTerminalSectionNegRestrictionCompatible_of_operations
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF) :
    fixedReconstructedTerminalSectionNegRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF := by
  exact hops.2.2

/-- Helper for Chap08 Lemma 8 11 8/Part16: the additive terminal-section structure on each
object of the fixed gerbe cover of `U`. -/
@[reducible]
noncomputable def fixedChosenGerbeCoverTerminalSectionAddCommGroup
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C} (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    AddCommGroup ((absoluteGlueingReconstruction (J := J) F).1.obj (op I.Y)) :=
  fixedReconstructedTerminalSectionAddCommGroupOfFiber
    (𝒮 := 𝒮) hAbelian F comparisonF
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)

/-- Helper for Chap08 Lemma 8 11 8/Part16: the local sum of two reconstructed terminal sections
on one member of the fixed gerbe cover. -/
noncomputable def fixedChosenGerbeCoverLocalSum
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C}
    (s t : (absoluteGlueingReconstruction (J := J) F).1.obj (op U))
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    (absoluteGlueingReconstruction (J := J) F).1.obj (op I.Y) := by
  letI : AddCommGroup
      ((absoluteGlueingReconstruction (J := J) F).1.obj (op I.Y)) :=
    fixedChosenGerbeCoverTerminalSectionAddCommGroup
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF I
  exact
    (absoluteGlueingReconstruction (J := J) F).1.map I.f.op s +
      (absoluteGlueingReconstruction (J := J) F).1.map I.f.op t

/-- Helper for Chap08 Lemma 8 11 8/Part16: the local zero section of the reconstructed sheaf on
one member of the fixed gerbe cover. -/
noncomputable def fixedChosenGerbeCoverLocalZero
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C}
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    (absoluteGlueingReconstruction (J := J) F).1.obj (op I.Y) := by
  letI : AddCommGroup
      ((absoluteGlueingReconstruction (J := J) F).1.obj (op I.Y)) :=
    fixedChosenGerbeCoverTerminalSectionAddCommGroup
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF I
  exact 0

/-- Helper for Chap08 Lemma 8 11 8/Part16: the local negation of a reconstructed terminal section
on one member of the fixed gerbe cover. -/
noncomputable def fixedChosenGerbeCoverLocalNeg
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C}
    (s : (absoluteGlueingReconstruction (J := J) F).1.obj (op U))
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    (absoluteGlueingReconstruction (J := J) F).1.obj (op I.Y) := by
  letI : AddCommGroup
      ((absoluteGlueingReconstruction (J := J) F).1.obj (op I.Y)) :=
    fixedChosenGerbeCoverTerminalSectionAddCommGroup
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF I
  exact -((absoluteGlueingReconstruction (J := J) F).1.map I.f.op s)

/-- Helper for Chap08 Lemma 8 11 8/Part16: the chosen-cover local sum is the transported
fiberwise sum for the chosen local object. -/
theorem fixedChosenGerbeCoverLocalSum_eq_sumOfFiber
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C}
    (s t : (absoluteGlueingReconstruction (J := J) F).1.obj (op U))
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    fixedChosenGerbeCoverLocalSum
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t I =
      fixedReconstructedTerminalSectionSumOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)
        ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op s)
        ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op t) := by
  rfl

/-- Helper for Chap08 Lemma 8 11 8/Part16: the chosen-cover local zero is the transported
fiberwise zero for the chosen local object. -/
theorem fixedChosenGerbeCoverLocalZero_eq_zeroOfFiber
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C}
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    fixedChosenGerbeCoverLocalZero
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF I =
      fixedReconstructedTerminalSectionZeroOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I) := by
  rfl

/-- Helper for Chap08 Lemma 8 11 8/Part16: the chosen-cover local negation is the transported
fiberwise negation for the chosen local object. -/
theorem fixedChosenGerbeCoverLocalNeg_eq_negOfFiber
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C}
    (s : (absoluteGlueingReconstruction (J := J) F).1.obj (op U))
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    fixedChosenGerbeCoverLocalNeg
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s I =
      fixedReconstructedTerminalSectionNegOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)
        ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op s) := by
  rfl

/-- Helper for Chap08 Lemma 8 11 8/Part16: after a restriction map known to preserve the
transported fiberwise sums, a chosen-cover local sum restricts to the fiberwise sum of the pulled
chosen local object. -/
theorem fixedChosenGerbeCoverLocalSum_map_eq_sumOfFiber
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (hres : fixedReconstructedTerminalSectionSumRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    {U W : C}
    (s t : (absoluteGlueingReconstruction (J := J) F).1.obj (op U))
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (a : W ⟶ I.Y) :
    (absoluteGlueingReconstruction (J := J) F).1.map a.op
        (fixedChosenGerbeCoverLocalSum
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t I) =
      fixedReconstructedTerminalSectionSumOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor a).obj
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I))
        ((absoluteGlueingReconstruction (J := J) F).1.map (a ≫ I.f).op s)
        ((absoluteGlueingReconstruction (J := J) F).1.map (a ≫ I.f).op t) := by
  rw [fixedChosenGerbeCoverLocalSum_eq_sumOfFiber]
  rw [hres a (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)
    ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op s)
    ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op t)]
  simp [FunctorToTypes.map_comp_apply]

/-- Helper for Chap08 Lemma 8 11 8/Part16: after a restriction map known to preserve the
transported fiberwise zeros, a chosen-cover local zero restricts to the fiberwise zero of the
pulled chosen local object. -/
theorem fixedChosenGerbeCoverLocalZero_map_eq_zeroOfFiber
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (hres : fixedReconstructedTerminalSectionZeroRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    {U W : C}
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (a : W ⟶ I.Y) :
    (absoluteGlueingReconstruction (J := J) F).1.map a.op
        (fixedChosenGerbeCoverLocalZero
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF I) =
      fixedReconstructedTerminalSectionZeroOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor a).obj
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)) := by
  rw [fixedChosenGerbeCoverLocalZero_eq_zeroOfFiber]
  exact hres a (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)

/-- Helper for Chap08 Lemma 8 11 8/Part16: after a restriction map known to preserve the
transported fiberwise negations, a chosen-cover local negation restricts to the fiberwise negation
of the pulled chosen local object. -/
theorem fixedChosenGerbeCoverLocalNeg_map_eq_negOfFiber
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (hres : fixedReconstructedTerminalSectionNegRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    {U W : C}
    (s : (absoluteGlueingReconstruction (J := J) F).1.obj (op U))
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (a : W ⟶ I.Y) :
    (absoluteGlueingReconstruction (J := J) F).1.map a.op
        (fixedChosenGerbeCoverLocalNeg
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s I) =
      fixedReconstructedTerminalSectionNegOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor a).obj
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I))
        ((absoluteGlueingReconstruction (J := J) F).1.map (a ≫ I.f).op s) := by
  rw [fixedChosenGerbeCoverLocalNeg_eq_negOfFiber]
  rw [hres a (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)
    ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op s)]
  simp [FunctorToTypes.map_comp_apply]

/-- Helper for Chap08 Lemma 8 11 8/Part16: applying the local comparison equivalence to the
chosen-cover local sum gives the sum in the local automorphism sheaf. -/
theorem fixedChosenGerbeCoverLocalSum_equiv
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C}
    (s t : (absoluteGlueingReconstruction (J := J) F).1.obj (op U))
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)
        (fixedChosenGerbeCoverLocalSum
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t I) =
      fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)
        ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op s) +
      fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)
        ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op t) := by
  letI : AddCommGroup
      ((absoluteGlueingReconstruction (J := J) F).1.obj (op I.Y)) :=
    fixedChosenGerbeCoverTerminalSectionAddCommGroup
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF I
  exact fixedReconstructedTerminalSectionEquiv_map_add
    (𝒮 := 𝒮) hAbelian F comparisonF
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)
    ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op s)
    ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op t)

/-- Helper for Chap08 Lemma 8 11 8/Part16: applying the local comparison equivalence to the
chosen-cover local zero gives zero in the local automorphism sheaf. -/
theorem fixedChosenGerbeCoverLocalZero_equiv
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C}
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)
        (fixedChosenGerbeCoverLocalZero
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF I) =
      0 := by
  letI : AddCommGroup
      ((absoluteGlueingReconstruction (J := J) F).1.obj (op I.Y)) :=
    fixedChosenGerbeCoverTerminalSectionAddCommGroup
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF I
  let e := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)
  change e (e.symm 0) = 0
  exact e.apply_symm_apply 0

/-- Helper for Chap08 Lemma 8 11 8/Part16: applying the local comparison equivalence to the
chosen-cover local negation gives negation in the local automorphism sheaf. -/
theorem fixedChosenGerbeCoverLocalNeg_equiv
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C}
    (s : (absoluteGlueingReconstruction (J := J) F).1.obj (op U))
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)
        (fixedChosenGerbeCoverLocalNeg
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s I) =
      - fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)
        ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op s) := by
  letI : AddCommGroup
      ((absoluteGlueingReconstruction (J := J) F).1.obj (op I.Y)) :=
    fixedChosenGerbeCoverTerminalSectionAddCommGroup
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF I
  let e := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)
  change e (e.symm (-(e ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op s)))) =
    -(e ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op s))
  exact e.apply_symm_apply (-(e ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op s)))

/-- Helper for Chap08 Lemma 8 11 8/Part16: the chosen-cover local sum is unchanged if the
chosen local object is replaced by an isomorphic object of the same fiber. -/
theorem fixedChosenGerbeCoverLocalSum_eq_transport_of_morphism
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    {U : C}
    (s t : (absoluteGlueingReconstruction (J := J) F).1.obj (op U))
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    {y : 𝒮.p.Fiber I.Y}
    (φ : chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I ⟶ y) :
    let ey := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF y
    fixedChosenGerbeCoverLocalSum
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t I =
      ey.symm
        (ey ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op s) +
          ey ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op t)) := by
  let ex := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)
  let ey := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF y
  change ex.symm
      (ex ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op s) +
        ex ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op t)) =
    ey.symm
      (ey ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op s) +
        ey ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op t))
  exact
    fixedReconstructedTerminalSectionEquiv_add_transport_eq_of_morphism
      (𝒮 := 𝒮) hAbelian F comparisonF compatibilityF φ
      ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op s)
      ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op t)

/-- Helper for Chap08 Lemma 8 11 8/Part16: the chosen-cover local zero is unchanged if the
chosen local object is replaced by an isomorphic object of the same fiber. -/
theorem fixedChosenGerbeCoverLocalZero_eq_transport_of_morphism
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    {U : C}
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    {y : 𝒮.p.Fiber I.Y}
    (φ : chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I ⟶ y) :
    let ey := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF y
    fixedChosenGerbeCoverLocalZero
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF I =
      ey.symm 0 := by
  let ex := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)
  let ey := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF y
  change ex.symm 0 = ey.symm 0
  exact
    fixedReconstructedTerminalSectionEquiv_zero_transport_eq_of_morphism
      (𝒮 := 𝒮) hAbelian F comparisonF compatibilityF φ

/-- Helper for Chap08 Lemma 8 11 8/Part16: the chosen-cover local negation is unchanged if the
chosen local object is replaced by an isomorphic object of the same fiber. -/
theorem fixedChosenGerbeCoverLocalNeg_eq_transport_of_morphism
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    {U : C}
    (s : (absoluteGlueingReconstruction (J := J) F).1.obj (op U))
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    {y : 𝒮.p.Fiber I.Y}
    (φ : chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I ⟶ y) :
    let ey := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF y
    fixedChosenGerbeCoverLocalNeg
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s I =
      ey.symm
        (-(ey ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op s))) := by
  let ex := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)
  let ey := fixedReconstructedTerminalSectionEquiv (𝒮 := 𝒮) hAbelian F comparisonF y
  change ex.symm
      (-(ex ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op s))) =
    ey.symm
      (-(ey ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op s)))
  exact
    fixedReconstructedTerminalSectionEquiv_neg_transport_eq_of_morphism
      (𝒮 := 𝒮) hAbelian F comparisonF compatibilityF φ
      ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op s)

/-- Helper for Chap08 Lemma 8 11 8/Part16: compatibility condition for the chosen-cover local
sum sections, in the exact shape consumed by sheaf amalgamation. -/
abbrev fixedChosenGerbeCoverLocalSumCompatible
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C}
    (s t : (absoluteGlueingReconstruction (J := J) F).1.obj (op U)) : Prop :=
  ∀ ⦃W : C⦄
    ⦃I K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow⦄
    (a : W ⟶ I.Y) (b : W ⟶ K.Y),
      a ≫ I.f = b ≫ K.f →
        (absoluteGlueingReconstruction (J := J) F).1.map a.op
            (fixedChosenGerbeCoverLocalSum
              (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t I) =
          (absoluteGlueingReconstruction (J := J) F).1.map b.op
            (fixedChosenGerbeCoverLocalSum
              (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t K)

/-- Helper for Chap08 Lemma 8 11 8/Part16: compatibility condition for the chosen-cover local
zero sections, in the exact shape consumed by sheaf amalgamation. -/
abbrev fixedChosenGerbeCoverLocalZeroCompatible
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C} : Prop :=
  ∀ ⦃W : C⦄
    ⦃I K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow⦄
    (a : W ⟶ I.Y) (b : W ⟶ K.Y),
      a ≫ I.f = b ≫ K.f →
        (absoluteGlueingReconstruction (J := J) F).1.map a.op
            (fixedChosenGerbeCoverLocalZero
              (𝒮 := 𝒮) hGerbe hAbelian F comparisonF I) =
          (absoluteGlueingReconstruction (J := J) F).1.map b.op
            (fixedChosenGerbeCoverLocalZero
              (𝒮 := 𝒮) hGerbe hAbelian F comparisonF K)

/-- Helper for Chap08 Lemma 8 11 8/Part16: compatibility condition for the chosen-cover local
negation sections, in the exact shape consumed by sheaf amalgamation. -/
abbrev fixedChosenGerbeCoverLocalNegCompatible
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C}
    (s : (absoluteGlueingReconstruction (J := J) F).1.obj (op U)) : Prop :=
  ∀ ⦃W : C⦄
    ⦃I K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow⦄
    (a : W ⟶ I.Y) (b : W ⟶ K.Y),
      a ≫ I.f = b ≫ K.f →
        (absoluteGlueingReconstruction (J := J) F).1.map a.op
            (fixedChosenGerbeCoverLocalNeg
              (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s I) =
        (absoluteGlueingReconstruction (J := J) F).1.map b.op
            (fixedChosenGerbeCoverLocalNeg
              (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s K)

/-- Helper for Chap08 Lemma 8 11 8/Part16: once restriction maps preserve transported fiberwise
sums, the chosen-cover local sums satisfy the overlap compatibility needed for sheaf
amalgamation. -/
theorem fixedChosenGerbeCoverLocalSumCompatible_of_restriction
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hres : fixedReconstructedTerminalSectionSumRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    {U : C}
    (s t : (absoluteGlueingReconstruction (J := J) F).1.obj (op U)) :
    fixedChosenGerbeCoverLocalSumCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t := by
  intro W I K a b h
  let R : Sheaf J (Type (max u v)) := absoluteGlueingReconstruction (J := J) F
  let S : J.Cover W :=
    local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
      (I₁ := I) (I₂ := K) a b
  apply fixedSection_eq_of_cover_restrictions R S
  intro L
  have hbase : L.f ≫ a ≫ I.f = L.f ≫ b ≫ K.f := by
    simpa [Category.assoc] using congrArg (fun q ↦ L.f ≫ q) h
  calc
    R.1.map L.f.op
        (R.1.map a.op
          (fixedChosenGerbeCoverLocalSum
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t I)) =
      fixedReconstructedTerminalSectionSumOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).obj
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor a).obj
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)))
        (R.1.map (L.f ≫ a ≫ I.f).op s)
        (R.1.map (L.f ≫ a ≫ I.f).op t) := by
          rw [fixedChosenGerbeCoverLocalSum_map_eq_sumOfFiber
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hres s t I a]
          rw [hres L.f
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor a).obj
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I))
            (R.1.map (a ≫ I.f).op s) (R.1.map (a ≫ I.f).op t)]
          simp [R, FunctorToTypes.map_comp_apply, Category.assoc]
    _ =
      fixedReconstructedTerminalSectionSumOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).obj
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor b).obj
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U K)))
        (R.1.map (L.f ≫ b ≫ K.f).op s)
        (R.1.map (L.f ≫ b ≫ K.f).op t) := by
          rw [← hbase]
          exact
            fixedReconstructedTerminalSectionSumOfFiber_eq_of_morphism
              (𝒮 := 𝒮) hAbelian F comparisonF compatibilityF
              (local_overlap_isomorphism (𝒮 := 𝒮) hGerbe
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
                a b L).hom
              (R.1.map (L.f ≫ a ≫ I.f).op s)
              (R.1.map (L.f ≫ a ≫ I.f).op t)
    _ =
      R.1.map L.f.op
        (R.1.map b.op
          (fixedChosenGerbeCoverLocalSum
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t K)) := by
          rw [fixedChosenGerbeCoverLocalSum_map_eq_sumOfFiber
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hres s t K b]
          rw [hres L.f
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor b).obj
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U K))
            (R.1.map (b ≫ K.f).op s) (R.1.map (b ≫ K.f).op t)]
          simp [R, FunctorToTypes.map_comp_apply, Category.assoc]

/-- Helper for Chap08 Lemma 8 11 8/Part16: once restriction maps preserve transported fiberwise
zeros, the chosen-cover local zero sections satisfy the overlap compatibility needed for sheaf
amalgamation. -/
theorem fixedChosenGerbeCoverLocalZeroCompatible_of_restriction
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hres : fixedReconstructedTerminalSectionZeroRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    {U : C} :
    fixedChosenGerbeCoverLocalZeroCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF (U := U) := by
  intro W I K a b h
  let R : Sheaf J (Type (max u v)) := absoluteGlueingReconstruction (J := J) F
  let S : J.Cover W :=
    local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
      (I₁ := I) (I₂ := K) a b
  apply fixedSection_eq_of_cover_restrictions R S
  intro L
  calc
    R.1.map L.f.op
        (R.1.map a.op
          (fixedChosenGerbeCoverLocalZero
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF I)) =
      fixedReconstructedTerminalSectionZeroOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).obj
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor a).obj
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I))) := by
          rw [fixedChosenGerbeCoverLocalZero_map_eq_zeroOfFiber
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hres I a]
          exact hres L.f
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor a).obj
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I))
    _ =
      fixedReconstructedTerminalSectionZeroOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).obj
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor b).obj
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U K))) := by
          exact
            fixedReconstructedTerminalSectionZeroOfFiber_eq_of_morphism
              (𝒮 := 𝒮) hAbelian F comparisonF compatibilityF
              (local_overlap_isomorphism (𝒮 := 𝒮) hGerbe
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
                a b L).hom
    _ =
      R.1.map L.f.op
        (R.1.map b.op
          (fixedChosenGerbeCoverLocalZero
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF K)) := by
          rw [fixedChosenGerbeCoverLocalZero_map_eq_zeroOfFiber
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hres K b]
          exact (hres L.f
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor b).obj
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U K))).symm

/-- Helper for Chap08 Lemma 8 11 8/Part16: once restriction maps preserve transported fiberwise
negations, the chosen-cover local negations satisfy the overlap compatibility needed for sheaf
amalgamation. -/
theorem fixedChosenGerbeCoverLocalNegCompatible_of_restriction
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hres : fixedReconstructedTerminalSectionNegRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    {U : C}
    (s : (absoluteGlueingReconstruction (J := J) F).1.obj (op U)) :
    fixedChosenGerbeCoverLocalNegCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s := by
  intro W I K a b h
  let R : Sheaf J (Type (max u v)) := absoluteGlueingReconstruction (J := J) F
  let S : J.Cover W :=
    local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
      (I₁ := I) (I₂ := K) a b
  apply fixedSection_eq_of_cover_restrictions R S
  intro L
  have hbase : L.f ≫ a ≫ I.f = L.f ≫ b ≫ K.f := by
    simpa [Category.assoc] using congrArg (fun q ↦ L.f ≫ q) h
  calc
    R.1.map L.f.op
        (R.1.map a.op
          (fixedChosenGerbeCoverLocalNeg
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s I)) =
      fixedReconstructedTerminalSectionNegOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).obj
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor a).obj
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I)))
        (R.1.map (L.f ≫ a ≫ I.f).op s) := by
          rw [fixedChosenGerbeCoverLocalNeg_map_eq_negOfFiber
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hres s I a]
          rw [hres L.f
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor a).obj
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I))
            (R.1.map (a ≫ I.f).op s)]
          simp [R, FunctorToTypes.map_comp_apply, Category.assoc]
    _ =
      fixedReconstructedTerminalSectionNegOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).obj
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor b).obj
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U K)))
        (R.1.map (L.f ≫ b ≫ K.f).op s) := by
          rw [← hbase]
          exact
            fixedReconstructedTerminalSectionNegOfFiber_eq_of_morphism
              (𝒮 := 𝒮) hAbelian F comparisonF compatibilityF
              (local_overlap_isomorphism (𝒮 := 𝒮) hGerbe
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
                a b L).hom
              (R.1.map (L.f ≫ a ≫ I.f).op s)
    _ =
      R.1.map L.f.op
        (R.1.map b.op
          (fixedChosenGerbeCoverLocalNeg
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s K)) := by
          rw [fixedChosenGerbeCoverLocalNeg_map_eq_negOfFiber
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hres s K b]
          rw [hres L.f
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor b).obj
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U K))
            (R.1.map (b ≫ K.f).op s)]
          simp [R, FunctorToTypes.map_comp_apply, Category.assoc]

/-- Helper for Chap08 Lemma 8 11 8/Part16: the normalized terminal-section operation
restriction package implies all chosen-cover local compatibility conditions used for sheaf
amalgamation. -/
theorem fixedChosenGerbeCoverLocalCompatibilities_of_operation_restriction
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    {U : C}
    (s t : (absoluteGlueingReconstruction (J := J) F).1.obj (op U)) :
    fixedChosenGerbeCoverLocalSumCompatible
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t ∧
      fixedChosenGerbeCoverLocalZeroCompatible
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF (U := U) ∧
      fixedChosenGerbeCoverLocalNegCompatible
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      fixedChosenGerbeCoverLocalSumCompatible_of_restriction
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF
        (fixedReconstructedTerminalSectionSumRestrictionCompatible_of_operations
          (𝒮 := 𝒮) hAbelian F comparisonF hops)
        s t
  · exact
      fixedChosenGerbeCoverLocalZeroCompatible_of_restriction
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF
        (fixedReconstructedTerminalSectionZeroRestrictionCompatible_of_operations
          (𝒮 := 𝒮) hAbelian F comparisonF hops)
  · exact
      fixedChosenGerbeCoverLocalNegCompatible_of_restriction
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF
        (fixedReconstructedTerminalSectionNegRestrictionCompatible_of_operations
          (𝒮 := 𝒮) hAbelian F comparisonF hops)
        s

/-- Helper for Chap08 Lemma 8 11 8/Part16: glue the compatible chosen-cover local sums to a
global reconstructed terminal section. -/
noncomputable def fixedReconstructedGlobalSumOfCover
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C}
    (s t : (absoluteGlueingReconstruction (J := J) F).1.obj (op U))
    (hs : fixedChosenGerbeCoverLocalSumCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t) :
    (absoluteGlueingReconstruction (J := J) F).1.obj (op U) :=
  fixedSectionAmalgamateOfCover
    (absoluteGlueingReconstruction (J := J) F)
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (fun I ↦ fixedChosenGerbeCoverLocalSum
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t I)
    hs

/-- Helper for Chap08 Lemma 8 11 8/Part16: the glued global sum restricts to the prescribed
chosen-cover local sum. -/
theorem fixedReconstructedGlobalSumOfCover_map
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C}
    (s t : (absoluteGlueingReconstruction (J := J) F).1.obj (op U))
    (hs : fixedChosenGerbeCoverLocalSumCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    (absoluteGlueingReconstruction (J := J) F).1.map I.f.op
        (fixedReconstructedGlobalSumOfCover
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t hs) =
      fixedChosenGerbeCoverLocalSum
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t I := by
  exact
    fixedSectionAmalgamateOfCover_map
      (absoluteGlueingReconstruction (J := J) F)
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (fun I ↦ fixedChosenGerbeCoverLocalSum
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t I)
      hs I

/-- Helper for Chap08 Lemma 8 11 8/Part16: glue the compatible chosen-cover local zeros to a
global reconstructed terminal section. -/
noncomputable def fixedReconstructedGlobalZeroOfCover
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C}
    (hz : fixedChosenGerbeCoverLocalZeroCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF (U := U)) :
    (absoluteGlueingReconstruction (J := J) F).1.obj (op U) :=
  fixedSectionAmalgamateOfCover
    (absoluteGlueingReconstruction (J := J) F)
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (fun I ↦ fixedChosenGerbeCoverLocalZero
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF I)
    hz

/-- Helper for Chap08 Lemma 8 11 8/Part16: the glued global zero restricts to the prescribed
chosen-cover local zero. -/
theorem fixedReconstructedGlobalZeroOfCover_map
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C}
    (hz : fixedChosenGerbeCoverLocalZeroCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF (U := U))
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    (absoluteGlueingReconstruction (J := J) F).1.map I.f.op
        (fixedReconstructedGlobalZeroOfCover
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hz) =
      fixedChosenGerbeCoverLocalZero
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF I := by
  exact
    fixedSectionAmalgamateOfCover_map
      (absoluteGlueingReconstruction (J := J) F)
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (fun I ↦ fixedChosenGerbeCoverLocalZero
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF I)
      hz I

/-- Helper for Chap08 Lemma 8 11 8/Part16: glue the compatible chosen-cover local negations to a
global reconstructed terminal section. -/
noncomputable def fixedReconstructedGlobalNegOfCover
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C}
    (s : (absoluteGlueingReconstruction (J := J) F).1.obj (op U))
    (hs : fixedChosenGerbeCoverLocalNegCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s) :
    (absoluteGlueingReconstruction (J := J) F).1.obj (op U) :=
  fixedSectionAmalgamateOfCover
    (absoluteGlueingReconstruction (J := J) F)
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (fun I ↦ fixedChosenGerbeCoverLocalNeg
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s I)
    hs

/-- Helper for Chap08 Lemma 8 11 8/Part16: the glued global negation restricts to the prescribed
chosen-cover local negation. -/
theorem fixedReconstructedGlobalNegOfCover_map
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C}
    (s : (absoluteGlueingReconstruction (J := J) F).1.obj (op U))
    (hs : fixedChosenGerbeCoverLocalNegCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    (absoluteGlueingReconstruction (J := J) F).1.map I.f.op
        (fixedReconstructedGlobalNegOfCover
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s hs) =
      fixedChosenGerbeCoverLocalNeg
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s I := by
  exact
    fixedSectionAmalgamateOfCover_map
      (absoluteGlueingReconstruction (J := J) F)
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (fun I ↦ fixedChosenGerbeCoverLocalNeg
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s I)
      hs I

/-- Helper for Chap08 Lemma 8 11 8/Part16: commutativity of the glued global sum follows from
commutativity of the transported local groups on the chosen gerbe cover. -/
theorem fixedReconstructedGlobalSumOfCover_comm
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C}
    (s t : (absoluteGlueingReconstruction (J := J) F).1.obj (op U))
    (hst : fixedChosenGerbeCoverLocalSumCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t)
    (hts : fixedChosenGerbeCoverLocalSumCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF t s) :
    fixedReconstructedGlobalSumOfCover
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t hst =
      fixedReconstructedGlobalSumOfCover
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF t s hts := by
  let R : Sheaf J (Type (max u v)) := absoluteGlueingReconstruction (J := J) F
  apply fixedSection_eq_of_cover_restrictions R (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
  intro I
  letI : AddCommGroup (R.1.obj (op I.Y)) :=
    fixedChosenGerbeCoverTerminalSectionAddCommGroup
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF I
  calc
    R.1.map I.f.op
        (fixedReconstructedGlobalSumOfCover
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t hst) =
      fixedChosenGerbeCoverLocalSum
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t I := by
        exact fixedReconstructedGlobalSumOfCover_map
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t hst I
    _ = fixedChosenGerbeCoverLocalSum
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF t s I := by
        simpa [R, fixedChosenGerbeCoverLocalSum] using
          (add_comm
            ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op s)
            ((absoluteGlueingReconstruction (J := J) F).1.map I.f.op t))
    _ = R.1.map I.f.op
        (fixedReconstructedGlobalSumOfCover
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF t s hts) := by
        exact (fixedReconstructedGlobalSumOfCover_map
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF t s hts I).symm

/-- Helper for Chap08 Lemma 8 11 8/Part16: the glued global zero is a left identity for the
glued global sum. -/
theorem fixedReconstructedGlobalSumOfCover_zero_left
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C}
    (s : (absoluteGlueingReconstruction (J := J) F).1.obj (op U))
    (hz : fixedChosenGerbeCoverLocalZeroCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF (U := U))
    (hs : fixedChosenGerbeCoverLocalSumCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF
      (fixedReconstructedGlobalZeroOfCover
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hz) s) :
    fixedReconstructedGlobalSumOfCover
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF
        (fixedReconstructedGlobalZeroOfCover
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hz) s hs =
      s := by
  let R : Sheaf J (Type (max u v)) := absoluteGlueingReconstruction (J := J) F
  apply fixedSection_eq_of_cover_restrictions R (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
  intro I
  letI : AddCommGroup (R.1.obj (op I.Y)) :=
    fixedChosenGerbeCoverTerminalSectionAddCommGroup
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF I
  calc
    R.1.map I.f.op
        (fixedReconstructedGlobalSumOfCover
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF
          (fixedReconstructedGlobalZeroOfCover
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hz) s hs) =
      fixedChosenGerbeCoverLocalSum
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF
        (fixedReconstructedGlobalZeroOfCover
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hz) s I := by
        exact fixedReconstructedGlobalSumOfCover_map
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF
          (fixedReconstructedGlobalZeroOfCover
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hz) s hs I
    _ = R.1.map I.f.op s := by
        simp [R, fixedChosenGerbeCoverLocalSum, fixedChosenGerbeCoverLocalZero,
          fixedReconstructedGlobalZeroOfCover_map
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hz I]

/-- Helper for Chap08 Lemma 8 11 8/Part16: the glued global zero is a right identity for the
glued global sum. -/
theorem fixedReconstructedGlobalSumOfCover_zero_right
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C}
    (s : (absoluteGlueingReconstruction (J := J) F).1.obj (op U))
    (hz : fixedChosenGerbeCoverLocalZeroCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF (U := U))
    (hs : fixedChosenGerbeCoverLocalSumCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s
      (fixedReconstructedGlobalZeroOfCover
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hz)) :
    fixedReconstructedGlobalSumOfCover
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s
        (fixedReconstructedGlobalZeroOfCover
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hz) hs =
      s := by
  let R : Sheaf J (Type (max u v)) := absoluteGlueingReconstruction (J := J) F
  apply fixedSection_eq_of_cover_restrictions R (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
  intro I
  letI : AddCommGroup (R.1.obj (op I.Y)) :=
    fixedChosenGerbeCoverTerminalSectionAddCommGroup
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF I
  calc
    R.1.map I.f.op
        (fixedReconstructedGlobalSumOfCover
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s
          (fixedReconstructedGlobalZeroOfCover
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hz) hs) =
      fixedChosenGerbeCoverLocalSum
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s
        (fixedReconstructedGlobalZeroOfCover
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hz) I := by
        exact fixedReconstructedGlobalSumOfCover_map
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s
          (fixedReconstructedGlobalZeroOfCover
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hz) hs I
    _ = R.1.map I.f.op s := by
        simp [R, fixedChosenGerbeCoverLocalSum, fixedChosenGerbeCoverLocalZero,
          fixedReconstructedGlobalZeroOfCover_map
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hz I]

/-- Helper for Chap08 Lemma 8 11 8/Part16: associativity of the glued global sum follows from
associativity of the transported local groups on the chosen gerbe cover. -/
theorem fixedReconstructedGlobalSumOfCover_assoc
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C}
    (s t u : (absoluteGlueingReconstruction (J := J) F).1.obj (op U))
    (hst : fixedChosenGerbeCoverLocalSumCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t)
    (htu : fixedChosenGerbeCoverLocalSumCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF t u)
    (hleft : fixedChosenGerbeCoverLocalSumCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF
      (fixedReconstructedGlobalSumOfCover
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t hst) u)
    (hright : fixedChosenGerbeCoverLocalSumCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s
      (fixedReconstructedGlobalSumOfCover
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF t u htu)) :
    fixedReconstructedGlobalSumOfCover
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF
        (fixedReconstructedGlobalSumOfCover
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t hst) u hleft =
      fixedReconstructedGlobalSumOfCover
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s
        (fixedReconstructedGlobalSumOfCover
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF t u htu) hright := by
  let R : Sheaf J (Type (max u v)) := absoluteGlueingReconstruction (J := J) F
  apply fixedSection_eq_of_cover_restrictions R (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
  intro I
  letI : AddCommGroup (R.1.obj (op I.Y)) :=
    fixedChosenGerbeCoverTerminalSectionAddCommGroup
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF I
  calc
    R.1.map I.f.op
        (fixedReconstructedGlobalSumOfCover
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF
          (fixedReconstructedGlobalSumOfCover
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t hst) u hleft) =
      (R.1.map I.f.op s + R.1.map I.f.op t) + R.1.map I.f.op u := by
        simp [R, fixedChosenGerbeCoverLocalSum,
          fixedReconstructedGlobalSumOfCover_map
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t hst I,
          fixedReconstructedGlobalSumOfCover_map
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF
            (fixedReconstructedGlobalSumOfCover
              (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t hst) u hleft I]
    _ = R.1.map I.f.op s + (R.1.map I.f.op t + R.1.map I.f.op u) := by
        exact add_assoc _ _ _
    _ = R.1.map I.f.op
        (fixedReconstructedGlobalSumOfCover
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s
          (fixedReconstructedGlobalSumOfCover
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF t u htu) hright) := by
        simp [R, fixedChosenGerbeCoverLocalSum,
          fixedReconstructedGlobalSumOfCover_map
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF t u htu I,
          fixedReconstructedGlobalSumOfCover_map
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s
            (fixedReconstructedGlobalSumOfCover
              (𝒮 := 𝒮) hGerbe hAbelian F comparisonF t u htu) hright I]

/-- Helper for Chap08 Lemma 8 11 8/Part16: the glued global negation is a left additive inverse
for the glued global sum. -/
theorem fixedReconstructedGlobalNegOfCover_add_cancel
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U : C}
    (s : (absoluteGlueingReconstruction (J := J) F).1.obj (op U))
    (hz : fixedChosenGerbeCoverLocalZeroCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF (U := U))
    (hneg : fixedChosenGerbeCoverLocalNegCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s)
    (hsum : fixedChosenGerbeCoverLocalSumCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF
      (fixedReconstructedGlobalNegOfCover
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s hneg) s) :
    fixedReconstructedGlobalSumOfCover
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF
        (fixedReconstructedGlobalNegOfCover
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s hneg) s hsum =
      fixedReconstructedGlobalZeroOfCover
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hz := by
  let R : Sheaf J (Type (max u v)) := absoluteGlueingReconstruction (J := J) F
  apply fixedSection_eq_of_cover_restrictions R (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
  intro I
  letI : AddCommGroup (R.1.obj (op I.Y)) :=
    fixedChosenGerbeCoverTerminalSectionAddCommGroup
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF I
  calc
    R.1.map I.f.op
        (fixedReconstructedGlobalSumOfCover
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF
          (fixedReconstructedGlobalNegOfCover
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s hneg) s hsum) =
      fixedChosenGerbeCoverLocalSum
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF
        (fixedReconstructedGlobalNegOfCover
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s hneg) s I := by
        exact fixedReconstructedGlobalSumOfCover_map
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF
          (fixedReconstructedGlobalNegOfCover
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s hneg) s hsum I
    _ = fixedChosenGerbeCoverLocalZero
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF I := by
        simp [R, fixedChosenGerbeCoverLocalSum, fixedChosenGerbeCoverLocalNeg,
          fixedChosenGerbeCoverLocalZero,
          fixedReconstructedGlobalNegOfCover_map
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s hneg I]
    _ = R.1.map I.f.op
        (fixedReconstructedGlobalZeroOfCover
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hz) := by
        exact (fixedReconstructedGlobalZeroOfCover_map
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hz I).symm

/-- Helper for Chap08 Lemma 8 11 8/Part16: sum compatibility obtained from the normalized
operation-restriction package. -/
def fixedChosenGerbeCoverLocalSumCompatibleOfOperations
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    {U : C}
    (s t : (absoluteGlueingReconstruction (J := J) F).1.obj (op U)) :
    fixedChosenGerbeCoverLocalSumCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t :=
  fixedChosenGerbeCoverLocalSumCompatible_of_restriction
    (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF
    (fixedReconstructedTerminalSectionSumRestrictionCompatible_of_operations
      (𝒮 := 𝒮) hAbelian F comparisonF hops)
    s t

/-- Helper for Chap08 Lemma 8 11 8/Part16: zero compatibility obtained from the normalized
operation-restriction package. -/
def fixedChosenGerbeCoverLocalZeroCompatibleOfOperations
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    {U : C} :
    fixedChosenGerbeCoverLocalZeroCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF (U := U) :=
  fixedChosenGerbeCoverLocalZeroCompatible_of_restriction
    (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF
    (fixedReconstructedTerminalSectionZeroRestrictionCompatible_of_operations
      (𝒮 := 𝒮) hAbelian F comparisonF hops)

/-- Helper for Chap08 Lemma 8 11 8/Part16: negation compatibility obtained from the normalized
operation-restriction package. -/
def fixedChosenGerbeCoverLocalNegCompatibleOfOperations
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    {U : C}
    (s : (absoluteGlueingReconstruction (J := J) F).1.obj (op U)) :
    fixedChosenGerbeCoverLocalNegCompatible
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s :=
  fixedChosenGerbeCoverLocalNegCompatible_of_restriction
    (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF
    (fixedReconstructedTerminalSectionNegRestrictionCompatible_of_operations
      (𝒮 := 𝒮) hAbelian F comparisonF hops)
    s

/-- Helper for Chap08 Lemma 8 11 8/Part16: the global sum on reconstructed terminal sections
obtained from operation restriction compatibility. -/
noncomputable def fixedReconstructedGlobalSumOfOperations
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    {U : C}
    (s t : (absoluteGlueingReconstruction (J := J) F).1.obj (op U)) :
    (absoluteGlueingReconstruction (J := J) F).1.obj (op U) :=
  fixedReconstructedGlobalSumOfCover
    (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t
    (fixedChosenGerbeCoverLocalSumCompatibleOfOperations
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops s t)

/-- Helper for Chap08 Lemma 8 11 8/Part16: the global zero on reconstructed terminal sections
obtained from operation restriction compatibility. -/
noncomputable def fixedReconstructedGlobalZeroOfOperations
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    {U : C} :
    (absoluteGlueingReconstruction (J := J) F).1.obj (op U) :=
  fixedReconstructedGlobalZeroOfCover
    (𝒮 := 𝒮) hGerbe hAbelian F comparisonF
    (fixedChosenGerbeCoverLocalZeroCompatibleOfOperations
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops)

/-- Helper for Chap08 Lemma 8 11 8/Part16: the global negation on reconstructed terminal
sections obtained from operation restriction compatibility. -/
noncomputable def fixedReconstructedGlobalNegOfOperations
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    {U : C}
    (s : (absoluteGlueingReconstruction (J := J) F).1.obj (op U)) :
    (absoluteGlueingReconstruction (J := J) F).1.obj (op U) :=
  fixedReconstructedGlobalNegOfCover
    (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s
    (fixedChosenGerbeCoverLocalNegCompatibleOfOperations
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops s)

/-- Helper for Chap08 Lemma 8 11 8/Part16: the reconstructed terminal sections over one base
object form an abelian group once the operation restriction package is available. -/
@[reducible]
noncomputable def fixedReconstructedTerminalSectionAddCommGroupOfOperations
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    {U : C} :
    AddCommGroup ((absoluteGlueingReconstruction (J := J) F).1.obj (op U)) := by
  let R : Sheaf J (Type (max u v)) := absoluteGlueingReconstruction (J := J) F
  let α := R.1.obj (op U)
  letI : Add α :=
    ⟨fun s t ↦
      fixedReconstructedGlobalSumOfOperations
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops s t⟩
  letI : Zero α :=
    ⟨fixedReconstructedGlobalZeroOfOperations
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops (U := U)⟩
  letI : Neg α :=
    ⟨fun s ↦
      fixedReconstructedGlobalNegOfOperations
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops s⟩
  have h_assoc : ∀ a b c : α, a + b + c = a + (b + c) := by
    intro a b c
    change
      fixedReconstructedGlobalSumOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
          (fixedReconstructedGlobalSumOfOperations
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops a b) c =
        fixedReconstructedGlobalSumOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
          a
          (fixedReconstructedGlobalSumOfOperations
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops b c)
    simpa [fixedReconstructedGlobalSumOfOperations] using
      fixedReconstructedGlobalSumOfCover_assoc
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF a b c
        (fixedChosenGerbeCoverLocalSumCompatibleOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops a b)
        (fixedChosenGerbeCoverLocalSumCompatibleOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops b c)
        (fixedChosenGerbeCoverLocalSumCompatibleOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
          (fixedReconstructedGlobalSumOfOperations
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops a b) c)
        (fixedChosenGerbeCoverLocalSumCompatibleOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops a
          (fixedReconstructedGlobalSumOfOperations
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops b c))
  have h_zero_add : ∀ a : α, 0 + a = a := by
    intro a
    change
      fixedReconstructedGlobalSumOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
          (fixedReconstructedGlobalZeroOfOperations
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops) a = a
    simpa [fixedReconstructedGlobalSumOfOperations, fixedReconstructedGlobalZeroOfOperations] using
      fixedReconstructedGlobalSumOfCover_zero_left
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF a
        (fixedChosenGerbeCoverLocalZeroCompatibleOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops)
        (fixedChosenGerbeCoverLocalSumCompatibleOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
          (fixedReconstructedGlobalZeroOfOperations
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops) a)
  have h_neg_add_cancel : ∀ a : α, -a + a = 0 := by
    intro a
    change
      fixedReconstructedGlobalSumOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
          (fixedReconstructedGlobalNegOfOperations
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops a) a =
        fixedReconstructedGlobalZeroOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
    simpa [fixedReconstructedGlobalSumOfOperations, fixedReconstructedGlobalZeroOfOperations,
      fixedReconstructedGlobalNegOfOperations] using
      fixedReconstructedGlobalNegOfCover_add_cancel
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF a
        (fixedChosenGerbeCoverLocalZeroCompatibleOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops)
        (fixedChosenGerbeCoverLocalNegCompatibleOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops a)
        (fixedChosenGerbeCoverLocalSumCompatibleOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
          (fixedReconstructedGlobalNegOfOperations
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops a) a)
  have h_comm : ∀ a b : α, a + b = b + a := by
    intro a b
    change
      fixedReconstructedGlobalSumOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops a b =
        fixedReconstructedGlobalSumOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops b a
    simpa [fixedReconstructedGlobalSumOfOperations] using
      fixedReconstructedGlobalSumOfCover_comm
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF a b
        (fixedChosenGerbeCoverLocalSumCompatibleOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops a b)
        (fixedChosenGerbeCoverLocalSumCompatibleOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops b a)
  letI : AddGroup α :=
    AddGroup.ofLeftAxioms h_assoc h_zero_add h_neg_add_cancel
  exact AddCommGroup.mk h_comm

/-- Helper for Chap08 Lemma 8 11 8/Part16: if a fiber over `U` has an object `x`, then the
cover-glued global sum agrees with the sum transported through the comparison to `Aut(x)`. -/
theorem fixedReconstructedGlobalSumOfOperations_eq_sumOfFiber
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    {U : C} (x : 𝒮.p.Fiber U)
    (s t : (absoluteGlueingReconstruction (J := J) F).1.obj (op U)) :
    fixedReconstructedGlobalSumOfOperations
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops s t =
      fixedReconstructedTerminalSectionSumOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF x s t := by
  let R : Sheaf J (Type (max u v)) := absoluteGlueingReconstruction (J := J) F
  let hsum :
      fixedReconstructedTerminalSectionSumRestrictionCompatible
        (𝒮 := 𝒮) hAbelian F comparisonF :=
    hops.1
  apply fixedSection_eq_of_cover_restrictions R (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
  intro I
  let y : 𝒮.p.Fiber I.Y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I
  let xI : 𝒮.p.Fiber I.Y :=
    ((canonicalPullbackChoice 𝒮.p).pullbackFunctor I.f).obj x
  have hlocal :
      fixedChosenGerbeCoverLocalSum
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t I =
        R.1.map I.f.op
          (fixedReconstructedTerminalSectionSumOfFiber
            (𝒮 := 𝒮) hAbelian F comparisonF x s t) := by
    let S : J.Cover I.Y :=
      chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe y xI
    apply fixedSection_eq_of_cover_restrictions R S
    intro L
    let hc := canonicalPullbackChoice 𝒮.p
    calc
      R.1.map L.f.op
          (fixedChosenGerbeCoverLocalSum
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t I) =
        fixedReconstructedTerminalSectionSumOfFiber
          (𝒮 := 𝒮) hAbelian F comparisonF
          ((hc.pullbackFunctor L.f).obj y)
          (R.1.map (L.f ≫ I.f).op s)
          (R.1.map (L.f ≫ I.f).op t) := by
            simpa [R, hc, y, FunctorToTypes.map_comp_apply, Category.assoc] using
              fixedChosenGerbeCoverLocalSum_map_eq_sumOfFiber
                (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hsum s t I L.f
      _ =
        fixedReconstructedTerminalSectionSumOfFiber
          (𝒮 := 𝒮) hAbelian F comparisonF
          ((hc.pullbackFunctor L.f).obj xI)
          (R.1.map (L.f ≫ I.f).op s)
          (R.1.map (L.f ≫ I.f).op t) := by
            exact
              fixedReconstructedTerminalSectionSumOfFiber_eq_of_morphism
                (𝒮 := 𝒮) hAbelian F comparisonF compatibilityF
                (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe y xI L).hom
                (R.1.map (L.f ≫ I.f).op s)
                (R.1.map (L.f ≫ I.f).op t)
      _ =
        fixedReconstructedTerminalSectionSumOfFiber
          (𝒮 := 𝒮) hAbelian F comparisonF
          ((hc.pullbackFunctor (L.f ≫ I.f)).obj x)
          (R.1.map (L.f ≫ I.f).op s)
          (R.1.map (L.f ≫ I.f).op t) := by
            exact
              fixedReconstructedTerminalSectionSumOfFiber_eq_of_morphism
                (𝒮 := 𝒮) hAbelian F comparisonF compatibilityF
                ((hc.pullbackCompComponentIso I.f L.f x).inv)
                (R.1.map (L.f ≫ I.f).op s)
                (R.1.map (L.f ≫ I.f).op t)
      _ =
        R.1.map L.f.op
          (R.1.map I.f.op
            (fixedReconstructedTerminalSectionSumOfFiber
              (𝒮 := 𝒮) hAbelian F comparisonF x s t)) := by
            rw [← hsum (L.f ≫ I.f) x s t]
            simp [R, FunctorToTypes.map_comp_apply]
  calc
    R.1.map I.f.op
        (fixedReconstructedGlobalSumOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops s t) =
      fixedChosenGerbeCoverLocalSum
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t I := by
        simpa [fixedReconstructedGlobalSumOfOperations,
          fixedChosenGerbeCoverLocalSumCompatibleOfOperations] using
          fixedReconstructedGlobalSumOfCover_map
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t
            (fixedChosenGerbeCoverLocalSumCompatibleOfOperations
              (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops s t) I
    _ = R.1.map I.f.op
        (fixedReconstructedTerminalSectionSumOfFiber
          (𝒮 := 𝒮) hAbelian F comparisonF x s t) := hlocal

/-- Helper for Chap08 Lemma 8 11 8/Part16: if a fiber over `U` has an object `x`, then the
cover-glued global zero agrees with the zero transported through the comparison to `Aut(x)`. -/
theorem fixedReconstructedGlobalZeroOfOperations_eq_zeroOfFiber
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    {U : C} (x : 𝒮.p.Fiber U) :
    fixedReconstructedGlobalZeroOfOperations
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops =
      fixedReconstructedTerminalSectionZeroOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF x := by
  let R : Sheaf J (Type (max u v)) := absoluteGlueingReconstruction (J := J) F
  let hzero :
      fixedReconstructedTerminalSectionZeroRestrictionCompatible
        (𝒮 := 𝒮) hAbelian F comparisonF :=
    hops.2.1
  apply fixedSection_eq_of_cover_restrictions R (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
  intro I
  let y : 𝒮.p.Fiber I.Y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I
  let xI : 𝒮.p.Fiber I.Y :=
    ((canonicalPullbackChoice 𝒮.p).pullbackFunctor I.f).obj x
  have hlocal :
      fixedChosenGerbeCoverLocalZero
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF I =
        R.1.map I.f.op
          (fixedReconstructedTerminalSectionZeroOfFiber
            (𝒮 := 𝒮) hAbelian F comparisonF x) := by
    let S : J.Cover I.Y :=
      chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe y xI
    apply fixedSection_eq_of_cover_restrictions R S
    intro L
    let hc := canonicalPullbackChoice 𝒮.p
    calc
      R.1.map L.f.op
          (fixedChosenGerbeCoverLocalZero
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF I) =
        fixedReconstructedTerminalSectionZeroOfFiber
          (𝒮 := 𝒮) hAbelian F comparisonF
          ((hc.pullbackFunctor L.f).obj y) := by
            simpa [R, hc, y] using
              fixedChosenGerbeCoverLocalZero_map_eq_zeroOfFiber
                (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hzero I L.f
      _ =
        fixedReconstructedTerminalSectionZeroOfFiber
          (𝒮 := 𝒮) hAbelian F comparisonF
          ((hc.pullbackFunctor L.f).obj xI) := by
            exact
              fixedReconstructedTerminalSectionZeroOfFiber_eq_of_morphism
                (𝒮 := 𝒮) hAbelian F comparisonF compatibilityF
                (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe y xI L).hom
      _ =
        fixedReconstructedTerminalSectionZeroOfFiber
          (𝒮 := 𝒮) hAbelian F comparisonF
          ((hc.pullbackFunctor (L.f ≫ I.f)).obj x) := by
            exact
              fixedReconstructedTerminalSectionZeroOfFiber_eq_of_morphism
                (𝒮 := 𝒮) hAbelian F comparisonF compatibilityF
                ((hc.pullbackCompComponentIso I.f L.f x).inv)
      _ =
        R.1.map L.f.op
          (R.1.map I.f.op
            (fixedReconstructedTerminalSectionZeroOfFiber
              (𝒮 := 𝒮) hAbelian F comparisonF x)) := by
            rw [← hzero (L.f ≫ I.f) x]
            simp [R, FunctorToTypes.map_comp_apply]
  calc
    R.1.map I.f.op
        (fixedReconstructedGlobalZeroOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops) =
      fixedChosenGerbeCoverLocalZero
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF I := by
        simpa [fixedReconstructedGlobalZeroOfOperations,
          fixedChosenGerbeCoverLocalZeroCompatibleOfOperations] using
          fixedReconstructedGlobalZeroOfCover_map
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF
            (fixedChosenGerbeCoverLocalZeroCompatibleOfOperations
              (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops) I
    _ = R.1.map I.f.op
        (fixedReconstructedTerminalSectionZeroOfFiber
          (𝒮 := 𝒮) hAbelian F comparisonF x) := hlocal

/-- Helper for Chap08 Lemma 8 11 8/Part16: if a fiber over `U` has an object `x`, then the
cover-glued global negation agrees with the negation transported through the comparison to
`Aut(x)`. -/
theorem fixedReconstructedGlobalNegOfOperations_eq_negOfFiber
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    {U : C} (x : 𝒮.p.Fiber U)
    (s : (absoluteGlueingReconstruction (J := J) F).1.obj (op U)) :
    fixedReconstructedGlobalNegOfOperations
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops s =
      fixedReconstructedTerminalSectionNegOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF x s := by
  let R : Sheaf J (Type (max u v)) := absoluteGlueingReconstruction (J := J) F
  let hneg :
      fixedReconstructedTerminalSectionNegRestrictionCompatible
        (𝒮 := 𝒮) hAbelian F comparisonF :=
    hops.2.2
  apply fixedSection_eq_of_cover_restrictions R (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
  intro I
  let y : 𝒮.p.Fiber I.Y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I
  let xI : 𝒮.p.Fiber I.Y :=
    ((canonicalPullbackChoice 𝒮.p).pullbackFunctor I.f).obj x
  have hlocal :
      fixedChosenGerbeCoverLocalNeg
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s I =
        R.1.map I.f.op
          (fixedReconstructedTerminalSectionNegOfFiber
            (𝒮 := 𝒮) hAbelian F comparisonF x s) := by
    let S : J.Cover I.Y :=
      chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe y xI
    apply fixedSection_eq_of_cover_restrictions R S
    intro L
    let hc := canonicalPullbackChoice 𝒮.p
    calc
      R.1.map L.f.op
          (fixedChosenGerbeCoverLocalNeg
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s I) =
        fixedReconstructedTerminalSectionNegOfFiber
          (𝒮 := 𝒮) hAbelian F comparisonF
          ((hc.pullbackFunctor L.f).obj y)
          (R.1.map (L.f ≫ I.f).op s) := by
            simpa [R, hc, y, FunctorToTypes.map_comp_apply, Category.assoc] using
              fixedChosenGerbeCoverLocalNeg_map_eq_negOfFiber
                (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hneg s I L.f
      _ =
        fixedReconstructedTerminalSectionNegOfFiber
          (𝒮 := 𝒮) hAbelian F comparisonF
          ((hc.pullbackFunctor L.f).obj xI)
          (R.1.map (L.f ≫ I.f).op s) := by
            exact
              fixedReconstructedTerminalSectionNegOfFiber_eq_of_morphism
                (𝒮 := 𝒮) hAbelian F comparisonF compatibilityF
                (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe y xI L).hom
                (R.1.map (L.f ≫ I.f).op s)
      _ =
        fixedReconstructedTerminalSectionNegOfFiber
          (𝒮 := 𝒮) hAbelian F comparisonF
          ((hc.pullbackFunctor (L.f ≫ I.f)).obj x)
          (R.1.map (L.f ≫ I.f).op s) := by
            exact
              fixedReconstructedTerminalSectionNegOfFiber_eq_of_morphism
                (𝒮 := 𝒮) hAbelian F comparisonF compatibilityF
                ((hc.pullbackCompComponentIso I.f L.f x).inv)
                (R.1.map (L.f ≫ I.f).op s)
      _ =
        R.1.map L.f.op
          (R.1.map I.f.op
            (fixedReconstructedTerminalSectionNegOfFiber
              (𝒮 := 𝒮) hAbelian F comparisonF x s)) := by
            rw [← hneg (L.f ≫ I.f) x s]
            simp [R, FunctorToTypes.map_comp_apply]
  calc
    R.1.map I.f.op
        (fixedReconstructedGlobalNegOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops s) =
      fixedChosenGerbeCoverLocalNeg
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s I := by
        simpa [fixedReconstructedGlobalNegOfOperations,
          fixedChosenGerbeCoverLocalNegCompatibleOfOperations] using
          fixedReconstructedGlobalNegOfCover_map
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s
            (fixedChosenGerbeCoverLocalNegCompatibleOfOperations
              (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops s) I
    _ = R.1.map I.f.op
        (fixedReconstructedTerminalSectionNegOfFiber
          (𝒮 := 𝒮) hAbelian F comparisonF x s) := hlocal

/-- Helper for Chap08 Lemma 8 11 8/Part16: the cover-glued global sum restricts to the
fiberwise sum for any object living over a local source of the base.  This is the terminal-section
form of the source proof's characterization
`γ^V_{T,x} ∘ ρ_f|_T = γ^U_{T,x}`. -/
theorem fixedReconstructedGlobalSumOfOperations_map_eq_sumOfLocalFiber
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    {U T : C} (a : T ⟶ U) (x : 𝒮.p.Fiber T)
    (s t : (absoluteGlueingReconstruction (J := J) F).1.obj (op U)) :
    (absoluteGlueingReconstruction (J := J) F).1.map a.op
        (fixedReconstructedGlobalSumOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops s t) =
      fixedReconstructedTerminalSectionSumOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF x
        ((absoluteGlueingReconstruction (J := J) F).1.map a.op s)
        ((absoluteGlueingReconstruction (J := J) F).1.map a.op t) := by
  let R : Sheaf J (Type (max u v)) := absoluteGlueingReconstruction (J := J) F
  let hsum :
      fixedReconstructedTerminalSectionSumRestrictionCompatible
        (𝒮 := 𝒮) hAbelian F comparisonF :=
    hops.1
  let S : J.Cover T := (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).pullback a
  apply fixedSection_eq_of_cover_restrictions R S
  intro I
  let y : 𝒮.p.Fiber I.Y :=
    chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base
  let xI : 𝒮.p.Fiber I.Y :=
    ((canonicalPullbackChoice 𝒮.p).pullbackFunctor I.f).obj x
  have hlocal :
      fixedChosenGerbeCoverLocalSum
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t I.base =
        fixedReconstructedTerminalSectionSumOfFiber
          (𝒮 := 𝒮) hAbelian F comparisonF xI
          (R.1.map I.base.f.op s) (R.1.map I.base.f.op t) := by
    let Lcov : J.Cover I.Y :=
      chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe y xI
    apply fixedSection_eq_of_cover_restrictions R Lcov
    intro L
    let hc := canonicalPullbackChoice 𝒮.p
    calc
      R.1.map L.f.op
          (fixedChosenGerbeCoverLocalSum
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t I.base) =
        fixedReconstructedTerminalSectionSumOfFiber
          (𝒮 := 𝒮) hAbelian F comparisonF
          ((hc.pullbackFunctor L.f).obj y)
          (R.1.map (L.f ≫ I.base.f).op s)
          (R.1.map (L.f ≫ I.base.f).op t) := by
            simpa [R, hc, y, FunctorToTypes.map_comp_apply, Category.assoc] using
              fixedChosenGerbeCoverLocalSum_map_eq_sumOfFiber
                (𝒮 := 𝒮) hGerbe hAbelian F comparisonF hsum s t I.base L.f
      _ =
        fixedReconstructedTerminalSectionSumOfFiber
          (𝒮 := 𝒮) hAbelian F comparisonF
          ((hc.pullbackFunctor L.f).obj xI)
          (R.1.map (L.f ≫ I.base.f).op s)
          (R.1.map (L.f ≫ I.base.f).op t) := by
            exact
              fixedReconstructedTerminalSectionSumOfFiber_eq_of_morphism
                (𝒮 := 𝒮) hAbelian F comparisonF compatibilityF
                (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe y xI L).hom
                (R.1.map (L.f ≫ I.base.f).op s)
                (R.1.map (L.f ≫ I.base.f).op t)
      _ =
        fixedReconstructedTerminalSectionSumOfFiber
          (𝒮 := 𝒮) hAbelian F comparisonF
          ((hc.pullbackFunctor L.f).obj xI)
          (R.1.map L.f.op (R.1.map I.base.f.op s))
          (R.1.map L.f.op (R.1.map I.base.f.op t)) := by
            simp [R, FunctorToTypes.map_comp_apply, Category.assoc]
      _ =
        R.1.map L.f.op
          (fixedReconstructedTerminalSectionSumOfFiber
            (𝒮 := 𝒮) hAbelian F comparisonF xI
            (R.1.map I.base.f.op s) (R.1.map I.base.f.op t)) := by
            exact (hsum L.f xI (R.1.map I.base.f.op s)
              (R.1.map I.base.f.op t)).symm
  calc
    R.1.map I.f.op
        (R.1.map a.op
          (fixedReconstructedGlobalSumOfOperations
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops s t)) =
      fixedReconstructedTerminalSectionSumOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF xI
        (R.1.map I.base.f.op s) (R.1.map I.base.f.op t) := by
        have hcover :
            R.1.map I.base.f.op
                (fixedReconstructedGlobalSumOfOperations
                  (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops s t) =
              fixedChosenGerbeCoverLocalSum
                (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t I.base := by
          simpa [R, fixedReconstructedGlobalSumOfOperations,
            fixedChosenGerbeCoverLocalSumCompatibleOfOperations] using
            fixedReconstructedGlobalSumOfCover_map
              (𝒮 := 𝒮) hGerbe hAbelian F comparisonF s t
              (fixedChosenGerbeCoverLocalSumCompatibleOfOperations
                (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops s t) I.base
        have htarget :
            R.1.map I.base.f.op
                (fixedReconstructedGlobalSumOfOperations
                  (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops s t) =
              fixedReconstructedTerminalSectionSumOfFiber
                (𝒮 := 𝒮) hAbelian F comparisonF xI
                (R.1.map I.base.f.op s) (R.1.map I.base.f.op t) :=
          hcover.trans (by simpa [R, xI] using hlocal)
        rw [I.base_f] at htarget
        simpa [R, FunctorToTypes.map_comp_apply, Category.assoc] using htarget
    _ =
      fixedReconstructedTerminalSectionSumOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF xI
        (R.1.map I.f.op (R.1.map a.op s))
        (R.1.map I.f.op (R.1.map a.op t)) := by
        rw [I.base_f]
        simp [R, FunctorToTypes.map_comp_apply]
    _ =
      R.1.map I.f.op
        (fixedReconstructedTerminalSectionSumOfFiber
          (𝒮 := 𝒮) hAbelian F comparisonF x
          (R.1.map a.op s) (R.1.map a.op t)) := by
        rw [← hsum I.f x (R.1.map a.op s) (R.1.map a.op t)]

/-- Helper for Chap08 Lemma 8 11 8/Part16: the reconstructed global sum is preserved by every
restriction map, after checking the claim on a gerbe cover of the target. -/
theorem fixedReconstructedGlobalSumOfOperations_map
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    {U V : C} (f : V ⟶ U)
    (s t : (absoluteGlueingReconstruction (J := J) F).1.obj (op U)) :
    (absoluteGlueingReconstruction (J := J) F).1.map f.op
        (fixedReconstructedGlobalSumOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops s t) =
      fixedReconstructedGlobalSumOfOperations
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
        ((absoluteGlueingReconstruction (J := J) F).1.map f.op s)
        ((absoluteGlueingReconstruction (J := J) F).1.map f.op t) := by
  let R : Sheaf J (Type (max u v)) := absoluteGlueingReconstruction (J := J) F
  apply fixedSection_eq_of_cover_restrictions R (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
  intro I
  let x : 𝒮.p.Fiber I.Y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I
  calc
    R.1.map I.f.op
        (R.1.map f.op
          (fixedReconstructedGlobalSumOfOperations
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops s t)) =
      R.1.map (I.f ≫ f).op
        (fixedReconstructedGlobalSumOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops s t) := by
        simp [R, FunctorToTypes.map_comp_apply]
    _ =
      fixedReconstructedTerminalSectionSumOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF x
        (R.1.map (I.f ≫ f).op s) (R.1.map (I.f ≫ f).op t) := by
        exact
          fixedReconstructedGlobalSumOfOperations_map_eq_sumOfLocalFiber
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
            (I.f ≫ f) x s t
    _ =
      fixedReconstructedTerminalSectionSumOfFiber
        (𝒮 := 𝒮) hAbelian F comparisonF x
        (R.1.map I.f.op (R.1.map f.op s))
        (R.1.map I.f.op (R.1.map f.op t)) := by
        simp [R, FunctorToTypes.map_comp_apply]
    _ =
      R.1.map I.f.op
        (fixedReconstructedGlobalSumOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
          (R.1.map f.op s) (R.1.map f.op t)) := by
        exact
          (fixedReconstructedGlobalSumOfOperations_map_eq_sumOfLocalFiber
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
            I.f x (R.1.map f.op s) (R.1.map f.op t)).symm

/-- Helper for Chap08 Lemma 8 11 8/Part16: over a source object with a fiber object, restriction
maps preserve the reconstructed global sum. -/
theorem fixedReconstructedGlobalSumOfOperations_map_of_fiber
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U)
    (s t : (absoluteGlueingReconstruction (J := J) F).1.obj (op U)) :
    (absoluteGlueingReconstruction (J := J) F).1.map f.op
        (fixedReconstructedGlobalSumOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops s t) =
      fixedReconstructedGlobalSumOfOperations
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
        ((absoluteGlueingReconstruction (J := J) F).1.map f.op s)
        ((absoluteGlueingReconstruction (J := J) F).1.map f.op t) := by
  let hsum :
      fixedReconstructedTerminalSectionSumRestrictionCompatible
        (𝒮 := 𝒮) hAbelian F comparisonF :=
    hops.1
  rw [fixedReconstructedGlobalSumOfOperations_eq_sumOfFiber
    (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops x s t]
  rw [hsum f x s t]
  rw [fixedReconstructedGlobalSumOfOperations_eq_sumOfFiber
    (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
    (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)
    ((absoluteGlueingReconstruction (J := J) F).1.map f.op s)
    ((absoluteGlueingReconstruction (J := J) F).1.map f.op t)]

/-- Helper for Chap08 Lemma 8 11 8/Part16: over a source object with a fiber object, restriction
maps preserve the reconstructed global zero. -/
theorem fixedReconstructedGlobalZeroOfOperations_map_of_fiber
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U) :
    (absoluteGlueingReconstruction (J := J) F).1.map f.op
        (fixedReconstructedGlobalZeroOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops (U := U)) =
      fixedReconstructedGlobalZeroOfOperations
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops (U := V) := by
  let hzero :
      fixedReconstructedTerminalSectionZeroRestrictionCompatible
        (𝒮 := 𝒮) hAbelian F comparisonF :=
    hops.2.1
  rw [fixedReconstructedGlobalZeroOfOperations_eq_zeroOfFiber
    (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops x]
  rw [hzero f x]
  rw [fixedReconstructedGlobalZeroOfOperations_eq_zeroOfFiber
    (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
    (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)]

/-- Helper for Chap08 Lemma 8 11 8/Part16: over a source object with a fiber object, restriction
maps preserve the reconstructed global negation. -/
theorem fixedReconstructedGlobalNegOfOperations_map_of_fiber
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U)
    (s : (absoluteGlueingReconstruction (J := J) F).1.obj (op U)) :
    (absoluteGlueingReconstruction (J := J) F).1.map f.op
        (fixedReconstructedGlobalNegOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops s) =
      fixedReconstructedGlobalNegOfOperations
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
        ((absoluteGlueingReconstruction (J := J) F).1.map f.op s) := by
  let hneg :
      fixedReconstructedTerminalSectionNegRestrictionCompatible
        (𝒮 := 𝒮) hAbelian F comparisonF :=
    hops.2.2
  rw [fixedReconstructedGlobalNegOfOperations_eq_negOfFiber
    (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops x s]
  rw [hneg f x s]
  rw [fixedReconstructedGlobalNegOfOperations_eq_negOfFiber
    (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
    (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)
    ((absoluteGlueingReconstruction (J := J) F).1.map f.op s)]

/-- Helper for Chap08 Lemma 8 11 8/Part16: the reconstructed Type-valued presheaf equipped with
the cover-glued terminal-section operations is a presheaf of abelian groups. -/
noncomputable def fixedReconstructedAddCommPresheafOfOperations
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF) :
    Cᵒᵖ ⥤ AddCommGrpCat.{max u v} where
  obj Uop := by
    let R : Sheaf J (Type (max u v)) := absoluteGlueingReconstruction (J := J) F
    letI : AddCommGroup (R.1.obj Uop) := by
      change AddCommGroup (R.1.obj (op Uop.unop))
      exact
        fixedReconstructedTerminalSectionAddCommGroupOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops (U := Uop.unop)
    exact AddCommGrpCat.of (R.1.obj Uop)
  map {Uop Vop} f := by
    let R : Sheaf J (Type (max u v)) := absoluteGlueingReconstruction (J := J) F
    letI : AddCommGroup (R.1.obj Uop) := by
      change AddCommGroup (R.1.obj (op Uop.unop))
      exact
        fixedReconstructedTerminalSectionAddCommGroupOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops (U := Uop.unop)
    letI : AddCommGroup (R.1.obj Vop) := by
      change AddCommGroup (R.1.obj (op Vop.unop))
      exact
        fixedReconstructedTerminalSectionAddCommGroupOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops (U := Vop.unop)
    exact
      AddCommGrpCat.ofHom <|
        AddMonoidHom.mk' (R.1.map f) (by
          intro s t
          change
            R.1.map f
                (fixedReconstructedGlobalSumOfOperations
                  (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops s t) =
              fixedReconstructedGlobalSumOfOperations
                (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
                (R.1.map f s) (R.1.map f t)
          simpa [R] using
            fixedReconstructedGlobalSumOfOperations_map
              (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
              f.unop s t)
  map_id := by
    intro Uop
    apply AddCommGrpCat.ext
    intro s
    simp
  map_comp := by
    intro Uop Vop Wop f g
    apply AddCommGrpCat.ext
    intro s
    simp

/-- Helper for Chap08 Lemma 8 11 8/Part16: the reconstructed AddComm-valued presheaf from the
operation package is a sheaf because forgetting it recovers the reconstructed Type-valued sheaf.
-/
noncomputable def fixedReconstructedAddCommSheafOfOperations
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF) :
    Sheaf J AddCommGrpCat.{max u v} where
  obj :=
    fixedReconstructedAddCommPresheafOfOperations
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
  property := by
    rw [Presheaf.isSheaf_iff_isSheaf_forget J
      (fixedReconstructedAddCommPresheafOfOperations
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops)
      (forget AddCommGrpCat.{max u v})]
    simpa [fixedReconstructedAddCommPresheafOfOperations] using
      (absoluteGlueingReconstruction (J := J) F).property

/-- Helper for Chap08 Lemma 8 11 8/Part16: forgetting the reconstructed AddComm sheaf from the
operation package gives back the reconstructed Type-valued sheaf. -/
noncomputable def fixedReconstructedAddCommSheafForgetIsoOfOperations
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF) :
    ((fixedReconstructedAddCommSheafOfOperations
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops).1 ⋙
        forget AddCommGrpCat.{max u v}) ≅
      (absoluteGlueingReconstruction (J := J) F).1 where
  hom :=
    { app := fun _ x ↦ x
      naturality := by
        intro X Y f
        rfl }
  inv :=
    { app := fun _ x ↦ x
      naturality := by
        intro X Y f
        rfl }
  hom_inv_id := by
    ext U x
    rfl
  inv_hom_id := by
    ext U x
    rfl

/-- Helper for Chap08 Lemma 8 11 8/Part16: the Type-valued sheaf obtained by restricting the
reconstructed AddComm sheaf to a slice and then forgetting the additive structure. -/
noncomputable def fixedReconstructedAddCommSheafOverForgetOfOperations
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    (U : C) : Sheaf (J.over U) (Type (max u v)) where
  obj :=
    ((fixedReconstructedAddCommSheafOfOperations
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops).over U).1 ⋙
        forget AddCommGrpCat.{max u v}
  property := by
    exact
      (Presheaf.isSheaf_iff_isSheaf_forget (J.over U)
        ((fixedReconstructedAddCommSheafOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops).over U).1
        (forget AddCommGrpCat.{max u v})).mp
        ((fixedReconstructedAddCommSheafOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops).over U).property

/-- Helper for Chap08 Lemma 8 11 8/Part16: after restricting the reconstructed AddComm sheaf
to a slice and forgetting the additive structure, one recovers the slice of the reconstructed
`Type`-valued sheaf. -/
noncomputable def fixedReconstructedAddCommSheafOverForgetIsoOfOperations
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    (U : C) :
    fixedReconstructedAddCommSheafOverForgetOfOperations
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops U ≅
      (absoluteGlueingReconstruction (J := J) F).over U where
  hom :=
    Sheaf.homEquiv.symm
      { app := fun _ x ↦ x
        naturality := by
          intro X Y f
          rfl }
  inv :=
    Sheaf.homEquiv.symm
      { app := fun _ x ↦ x
        naturality := by
          intro X Y f
          rfl }
  hom_inv_id := by
    apply Sheaf.hom_ext
    ext T s
    rfl
  inv_hom_id := by
    apply Sheaf.hom_ext
    ext T s
    rfl

/-- Helper for Chap08 Lemma 8 11 8/Part16: the underlying `Type`-valued local comparison obtained
by forgetting the reconstructed AddComm sheaf, applying the Chapter 7 reconstruction counit on
the slice, and then using the fixed absolute-glueing comparison. -/
noncomputable def fixedReconstructedAddCommSheafLocalUnderlyingComparisonOfOperations
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    {U : C} (x : 𝒮.p.Fiber U) :
    fixedReconstructedAddCommSheafOverForgetOfOperations
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops U ≅
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x :=
  fixedReconstructedAddCommSheafOverForgetIsoOfOperations
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops U ≪≫
    absoluteGlueingReconstructionOverIso (J := J) F U ≪≫
    comparisonF x

/-- Helper for Chap08 Lemma 8 11 8/Part16: the source-specific non-terminal compatibility needed
to upgrade the underlying local comparison to an AddComm-valued comparison.  This is the precise
remaining `γ/ρ` input: the underlying comparison must preserve the reconstructed operations on
every object of the slice site, not only on terminal sections. -/
abbrev fixedReconstructedAddCommSheafLocalUnderlyingComparisonPreservesAdd
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF) : Prop :=
  ∀ {U : C} (x : 𝒮.p.Fiber U) (T : (Over U)ᵒᵖ)
    (s t : (((fixedReconstructedAddCommSheafOfOperations
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops).over U).1.obj T)),
      (show ((𝒮.automorphismAddCommSheaf hAbelian x).1.obj T) from
        (fixedReconstructedAddCommSheafLocalUnderlyingComparisonOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops x).hom.1.app T
            (s + t)) =
        (show ((𝒮.automorphismAddCommSheaf hAbelian x).1.obj T) from
          (fixedReconstructedAddCommSheafLocalUnderlyingComparisonOfOperations
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops x).hom.1.app T s) +
        (show ((𝒮.automorphismAddCommSheaf hAbelian x).1.obj T) from
          (fixedReconstructedAddCommSheafLocalUnderlyingComparisonOfOperations
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops x).hom.1.app T t)

/-- Helper for Chap08 Lemma 8 11 8/Part16: inverse additivity for the local underlying
comparison.  This is separated from the forward direction so later source-specific code can prove
each direction by the most convenient descent argument. -/
abbrev fixedReconstructedAddCommSheafLocalUnderlyingComparisonInvPreservesAdd
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF) : Prop :=
  ∀ {U : C} (x : 𝒮.p.Fiber U) (T : (Over U)ᵒᵖ)
    (s t : ((𝒮.automorphismAddCommSheaf hAbelian x).1.obj T)),
      (show (((fixedReconstructedAddCommSheafOfOperations
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops).over U).1.obj T) from
        (fixedReconstructedAddCommSheafLocalUnderlyingComparisonOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops x).inv.1.app T
            (s + t)) =
        (show (((fixedReconstructedAddCommSheafOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops).over U).1.obj T) from
          (fixedReconstructedAddCommSheafLocalUnderlyingComparisonOfOperations
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops x).inv.1.app T s) +
        (show (((fixedReconstructedAddCommSheafOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops).over U).1.obj T) from
          (fixedReconstructedAddCommSheafLocalUnderlyingComparisonOfOperations
            (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops x).inv.1.app T t)

/-- Helper for Chap08 Lemma 8 11 8/Part16: once the source-specific non-terminal additivity
inputs are known, the underlying local comparison upgrades to an AddComm-valued local comparison.
-/
noncomputable def fixedReconstructedAddCommSheafLocalComparisonOfOperations
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    (hadd :
      fixedReconstructedAddCommSheafLocalUnderlyingComparisonPreservesAdd
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops)
    (hinvadd :
      fixedReconstructedAddCommSheafLocalUnderlyingComparisonInvPreservesAdd
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops)
    {U : C} (x : 𝒮.p.Fiber U) :
    (fixedReconstructedAddCommSheafOfOperations
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops).over U ≅
        𝒮.automorphismAddCommSheaf hAbelian x := by
  let e :=
    fixedReconstructedAddCommSheafLocalUnderlyingComparisonOfOperations
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops x
  refine
    { hom := Sheaf.homEquiv.symm ?hom
      inv := Sheaf.homEquiv.symm ?inv
      hom_inv_id := ?hom_inv_id
      inv_hom_id := ?inv_hom_id }
  · exact
      { app := fun T ↦
          let A : AddCommGrpCat.{max u v} :=
            ((fixedReconstructedAddCommSheafOfOperations
              (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops).over U).1.obj T
          let B : AddCommGrpCat.{max u v} :=
            (𝒮.automorphismAddCommSheaf hAbelian x).1.obj T
          letI : AddCommGroup
              ((absoluteGlueingReconstruction (J := J) F).1.obj ((Over.forget U).op.obj T)) := by
            change AddCommGroup A
            infer_instance
          letI : AddCommGroup (automorphismSection (𝒮 := 𝒮) x (unop T)) := by
            change AddCommGroup B
            infer_instance
          show A ⟶ B from
          AddCommGrpCat.ofHom <|
            AddMonoidHom.mk'
              (fun s : A ↦
                (show B from
                  e.hom.1.app T s))
              (hadd x T)
        naturality := by
          intro T T' f
          apply AddCommGrpCat.ext
          intro s
          exact congrFun (e.hom.1.naturality f) s }
  · exact
      { app := fun T ↦
          let A : AddCommGrpCat.{max u v} :=
            (𝒮.automorphismAddCommSheaf hAbelian x).1.obj T
          let B : AddCommGrpCat.{max u v} :=
            ((fixedReconstructedAddCommSheafOfOperations
              (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops).over U).1.obj T
          letI : AddCommGroup (automorphismSection (𝒮 := 𝒮) x (unop T)) := by
            change AddCommGroup A
            infer_instance
          letI : AddCommGroup
              ((absoluteGlueingReconstruction (J := J) F).1.obj ((Over.forget U).op.obj T)) := by
            change AddCommGroup B
            infer_instance
          show A ⟶ B from
          AddCommGrpCat.ofHom <|
            AddMonoidHom.mk'
              (fun s : A ↦
                (show B from
                  e.inv.1.app T s))
              (hinvadd x T)
        naturality := by
          intro T T' f
          apply AddCommGrpCat.ext
          intro s
          exact congrFun (e.inv.1.naturality f) s }
  · apply Sheaf.hom_ext
    ext T s
    exact congrFun (congrArg (fun η ↦ η.1.app T) e.hom_inv_id) s
  · apply Sheaf.hom_ext
    ext T s
    exact congrFun (congrArg (fun η ↦ η.1.app T) e.inv_hom_id) s

/-- Helper for Chap08 Lemma 8 11 8/Part16: the forward map of the AddComm-valued local
comparison forgets to the previously assembled underlying comparison. -/
theorem fixedReconstructedAddCommSheafLocalComparisonOfOperations_forget_hom
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    (hadd :
      fixedReconstructedAddCommSheafLocalUnderlyingComparisonPreservesAdd
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops)
    (hinvadd :
      fixedReconstructedAddCommSheafLocalUnderlyingComparisonInvPreservesAdd
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops)
    {U : C} (x : 𝒮.p.Fiber U) :
    Functor.whiskerRight
        ((fixedReconstructedAddCommSheafLocalComparisonOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
          hadd hinvadd x).hom.1)
        (forget AddCommGrpCat.{max u v}) =
      (fixedReconstructedAddCommSheafLocalUnderlyingComparisonOfOperations
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops x).hom.1 := by
  ext T s
  rfl

/-- Helper for Chap08 Lemma 8 11 8/Part16: the inverse map of the AddComm-valued local comparison
forgets to the inverse of the underlying comparison. -/
theorem fixedReconstructedAddCommSheafLocalComparisonOfOperations_forget_inv
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    (hadd :
      fixedReconstructedAddCommSheafLocalUnderlyingComparisonPreservesAdd
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops)
    (hinvadd :
      fixedReconstructedAddCommSheafLocalUnderlyingComparisonInvPreservesAdd
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops)
    {U : C} (x : 𝒮.p.Fiber U) :
    Functor.whiskerRight
        ((fixedReconstructedAddCommSheafLocalComparisonOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
          hadd hinvadd x).inv.1)
        (forget AddCommGrpCat.{max u v}) =
      (fixedReconstructedAddCommSheafLocalUnderlyingComparisonOfOperations
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops x).inv.1 := by
  ext T s
  rfl

/-- Helper for Chap08 Lemma 8 11 8/Part16: the underlying local comparisons are compatible with
conjugation, by the existing underlying absolute-glueing compatibility. -/
theorem fixedReconstructedAddCommSheafLocalUnderlyingComparisonOfOperations_conj_apply
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (T : (Over U)ᵒᵖ)
    (s : (((fixedReconstructedAddCommSheafOfOperations
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops).over U).1.obj T)) :
    ((automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ).hom.1.app T)
        ((fixedReconstructedAddCommSheafLocalUnderlyingComparisonOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops x).hom.1.app T s) =
      (fixedReconstructedAddCommSheafLocalUnderlyingComparisonOfOperations
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops y).hom.1.app T s := by
  let z :=
    ((absoluteGlueingReconstructionOverIso (J := J) F U).hom.1.app T)
      ((fixedReconstructedAddCommSheafOverForgetIsoOfOperations
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops U).hom.1.app T s)
  have hcompat :=
    congrFun
      (congrArg (fun η ↦ η.1.app T)
        (congrArg Iso.hom
          (compatibilityF (U := U) (x := x) (y := y) φ)))
      z
  simpa [fixedReconstructedAddCommSheafLocalUnderlyingComparisonOfOperations,
    fixedReconstructedAddCommSheafOverForgetIsoOfOperations, z, Iso.trans_hom,
    automorphismUnderlyingSheafConj, automorphismUnderlyingSheafConj_hom,
    NatTrans.comp_app] using hcompat

/-- Helper for Chap08 Lemma 8 11 8/Part16: after the non-terminal additivity inputs upgrade the
underlying comparisons to AddComm-valued comparisons, their conjugation compatibility is formal
from the underlying absolute-glueing compatibility. -/
theorem fixedReconstructedAddCommSheafLocalComparisonOfOperations_conj
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    (hadd :
      fixedReconstructedAddCommSheafLocalUnderlyingComparisonPreservesAdd
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops)
    (hinvadd :
      fixedReconstructedAddCommSheafLocalUnderlyingComparisonInvPreservesAdd
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y) :
    fixedReconstructedAddCommSheafLocalComparisonOfOperations
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
        hadd hinvadd x ≪≫
      automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
        fixedReconstructedAddCommSheafLocalComparisonOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
          hadd hinvadd y := by
  apply Iso.ext
  apply Sheaf.hom_ext
  ext T s
  exact
    fixedReconstructedAddCommSheafLocalUnderlyingComparisonOfOperations_conj_apply
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops φ T s

/-- Helper for Chap08 Lemma 8 11 8/Part16: once the source-specific route supplies the
AddComm-valued local comparisons for the reconstructed operation sheaf, the fixed additive
absolute-glueing package is just the component assembly. -/
theorem fixedAbsoluteGlueingAddCommSheafDataOfOperationsAndComparisons
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (hops : fixedReconstructedTerminalSectionOperationRestrictionCompatible
      (𝒮 := 𝒮) hAbelian F comparisonF)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      (fixedReconstructedAddCommSheafOfOperations
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops).over U ≅
          𝒮.automorphismAddCommSheaf hAbelian x)
    (compatibility : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparison y) :
    fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F := by
  exact
    fixedAbsoluteGlueingAddCommSheafDataOfComponents (𝒮 := 𝒮) hAbelian F
      (fixedReconstructedAddCommSheafOfOperations
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops)
      (fixedReconstructedAddCommSheafForgetIsoOfOperations
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops)
      comparison compatibility

/-- Helper for Chap08 Lemma 8 11 8/Part16: operations-level strengthened source data.  The
field `hops` is the Lean form of the source proof's transition characterization
`γ^V_{T,x} ∘ ρ_f|_T = γ^U_{T,x}` after translating it to preservation of the transported
terminal-section operations.  The final two fields are the AddComm-valued local comparisons
obtained from the same source construction. -/
abbrev underlyingAbsoluteGlueingBandDataWithOperations
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) : Prop :=
  ∃ F : GrothendieckTopology.AbsoluteGlueing J,
    ∃ comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
        F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
      ∃ compatibilityF :
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparisonF y,
        ∃ hops :
          fixedReconstructedTerminalSectionOperationRestrictionCompatible
            (𝒮 := 𝒮) hAbelian F comparisonF,
          ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
            (fixedReconstructedAddCommSheafOfOperations
              (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops).over U ≅
                𝒮.automorphismAddCommSheaf hAbelian x,
            ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
              comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
                comparison y

/-- Helper for Chap08 Lemma 8 11 8/Part16: the source proof's transport characterization,
together with the resulting AddComm-valued local comparisons, assembles the operations-level
source package.  This is the precise support lemma for the route
`γ^V_{T,x} ∘ ρ_f|_T = γ^U_{T,x}`: the transport statement gives `hops`, and the comparison
family supplies the final band-facing data. -/
theorem underlyingAbsoluteGlueingBandDataWithOperationsOfTransportAndComparisons
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (htransport :
      fixedReconstructedTerminalSectionRestrictionTransportCompatible
        (𝒮 := 𝒮) hAbelian F comparisonF)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      (fixedReconstructedAddCommSheafOfOperations
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF
        (fixedReconstructedTerminalSectionOperationRestrictionCompatible_of_transport
          (𝒮 := 𝒮) hAbelian F comparisonF htransport)).over U ≅
          𝒮.automorphismAddCommSheaf hAbelian x)
    (compatibility : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparison y) :
    underlyingAbsoluteGlueingBandDataWithOperations
      (𝒮 := 𝒮) hGerbe hAbelian := by
  let hops :
      fixedReconstructedTerminalSectionOperationRestrictionCompatible
        (𝒮 := 𝒮) hAbelian F comparisonF :=
    fixedReconstructedTerminalSectionOperationRestrictionCompatible_of_transport
      (𝒮 := 𝒮) hAbelian F comparisonF htransport
  exact ⟨F, comparisonF, compatibilityF, hops, comparison, compatibility⟩

/-- Helper for Chap08 Lemma 8 11 8/Part16: package just the operation and local comparison
part for a fixed absolute-glueing datum. -/
theorem fixedReconstructedOperationsPackageOfTransportAndComparisons
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (compatibilityF : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparisonF y)
    (htransport :
      fixedReconstructedTerminalSectionRestrictionTransportCompatible
        (𝒮 := 𝒮) hAbelian F comparisonF)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      (fixedReconstructedAddCommSheafOfOperations
        (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF
        (fixedReconstructedTerminalSectionOperationRestrictionCompatible_of_transport
          (𝒮 := 𝒮) hAbelian F comparisonF htransport)).over U ≅
          𝒮.automorphismAddCommSheaf hAbelian x)
    (compatibility : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparison y) :
    ∃ hops :
      fixedReconstructedTerminalSectionOperationRestrictionCompatible
        (𝒮 := 𝒮) hAbelian F comparisonF,
      ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
        (fixedReconstructedAddCommSheafOfOperations
          (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops).over U ≅
            𝒮.automorphismAddCommSheaf hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparison y := by
  let hops :
      fixedReconstructedTerminalSectionOperationRestrictionCompatible
        (𝒮 := 𝒮) hAbelian F comparisonF :=
    fixedReconstructedTerminalSectionOperationRestrictionCompatible_of_transport
      (𝒮 := 𝒮) hAbelian F comparisonF htransport
  exact ⟨hops, comparison, compatibility⟩

/-- Helper for Chap08 Lemma 8 11 8/Part16: operations-level source data projects to the weak
underlying absolute-glueing source package. -/
theorem underlyingAbsoluteGlueingBandDataOfOperationsSource
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (data :
      underlyingAbsoluteGlueingBandDataWithOperations
        (𝒮 := 𝒮) hGerbe hAbelian) :
    underlyingAbsoluteGlueingBandData (𝒮 := 𝒮) hAbelian := by
  obtain ⟨F, comparisonF, compatibilityF, _hops, _comparison, _compatibility⟩ := data
  exact ⟨F, comparisonF, compatibilityF⟩

/-- Helper for Chap08 Lemma 8 11 8/Part16: operations-level source data assembles the fixed
absolute-glueing additive sheaf package. -/
theorem fixedAbsoluteGlueingAddCommSheafDataOfOperationsSource
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (data :
      underlyingAbsoluteGlueingBandDataWithOperations
        (𝒮 := 𝒮) hGerbe hAbelian) :
    fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian
      (Classical.choose data) := by
  obtain ⟨comparisonF, compatibilityF, hops, comparison, compatibility⟩ :=
    Classical.choose_spec data
  exact
    fixedAbsoluteGlueingAddCommSheafDataOfOperationsAndComparisons
      (𝒮 := 𝒮) hGerbe hAbelian (Classical.choose data)
      comparisonF compatibilityF hops comparison compatibility

/-- Helper for Chap08 Lemma 8 11 8/Part16: operations-level source data is a strengthened
source-and-fixed package. -/
theorem fixedAddCommSourceOfOperationsSource
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (data :
      underlyingAbsoluteGlueingBandDataWithOperations
        (𝒮 := 𝒮) hGerbe hAbelian) :
    underlyingAbsoluteGlueingBandDataWithFixedAddCommSheafData
      (𝒮 := 𝒮) hAbelian := by
  obtain ⟨F, comparisonF, compatibilityF, hops, comparison, compatibility⟩ := data
  exact ⟨F, comparisonF, compatibilityF,
    fixedAbsoluteGlueingAddCommSheafDataOfOperationsAndComparisons
      (𝒮 := 𝒮) hGerbe hAbelian F comparisonF compatibilityF hops
      comparison compatibility⟩

/-- Helper for Chap08 Lemma 8 11 8/Part16: the local counit isomorphisms from Chapter 7
reconstruction are compatible with the absolute-glueing transition maps. -/
theorem fixedAbsoluteGlueingReconstructionOverIso_hom_naturality
    (F : GrothendieckTopology.AbsoluteGlueing J) {U V : C} (f : V ⟶ U) :
    CommSq
      ((J.overMapPullback (Type (max u v)) f).map
        ((absoluteGlueingReconstructionOverIso (J := J) F U).hom))
      (((GrothendieckTopology.sheafToAbsoluteGlueingFunctor (J := J)).obj
          (absoluteGlueingReconstruction (J := J) F)).transition f).hom
      (F.transition f).hom
      ((absoluteGlueingReconstructionOverIso (J := J) F V).hom) := by
  let E : Sheaf J (Type (max u v)) ≌ GrothendieckTopology.AbsoluteGlueing J :=
    (GrothendieckTopology.sheafToAbsoluteGlueingFunctor (J := J)).asEquivalence
  simpa [E, absoluteGlueingReconstruction, absoluteGlueingReconstructionOverIso,
    absoluteGlueingIsoApp] using
    ((E.counitIso.app F).hom.naturality (f := f))

/-- Helper for Chap08 Lemma 8 11 8/Part16: reassociated form of the reconstruction counit's
transition naturality. -/
theorem fixedAbsoluteGlueingReconstructionOverIso_hom_naturality_assoc
    (F : GrothendieckTopology.AbsoluteGlueing J) {U V : C} (f : V ⟶ U) :
    ((J.overMapPullback (Type (max u v)) f).map
      ((absoluteGlueingReconstructionOverIso (J := J) F U).hom)) ≫
        (F.transition f).hom =
      (((GrothendieckTopology.sheafToAbsoluteGlueingFunctor (J := J)).obj
          (absoluteGlueingReconstruction (J := J) F)).transition f).hom ≫
        (absoluteGlueingReconstructionOverIso (J := J) F V).hom := by
  simpa [CommSq, Category.assoc] using
    (fixedAbsoluteGlueingReconstructionOverIso_hom_naturality
      (J := J) F (f := f)).w

/-- Helper for Chap08 Lemma 8 11 8/Part16: source absolute-glueing data and a fixed-datum
additive reconstruction theorem assemble the exact source-and-fixed package needed for the
remaining frontier. -/
theorem sourceAndFixedAdditiveReconstructionDataOfSourceAndFixed
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (hsource : underlyingAbsoluteGlueingBandData (𝒮 := 𝒮) hAbelian)
    (hfixed :
      ∀ (F : GrothendieckTopology.AbsoluteGlueing J)
        (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
          F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x),
        (∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparisonF y) →
          fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F) :
    ∃ F : GrothendieckTopology.AbsoluteGlueing J,
      ∃ comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
          F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
        ∃ _compatibilityF :
          ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
            comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
              comparisonF y,
          fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F := by
  -- Split the source datum into the absolute-glueing object and its compatible comparisons.
  obtain ⟨F, comparisonF, compatibilityF⟩ := hsource
  -- Apply the fixed-datum reconstruction theorem to that same object, then reuse the existing
  -- packager so the final theorem can consume one normalized source-and-fixed package.
  exact
    sourceAndFixedAdditiveReconstructionDataOfFixedDatum (𝒮 := 𝒮) hAbelian
      F comparisonF compatibilityF (hfixed F comparisonF compatibilityF)

/-- Helper for Chap08 Lemma 8 11 8/Part16: a packaged source comparison for a fixed
absolute-glueing object and fixed additive reconstruction assemble the source-and-fixed data. -/
theorem sourceAndFixedAdditiveReconstructionDataOfFixedSourcePackage
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (sourceF :
      ∃ comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
          F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparisonF y)
    (hfixed : fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F) :
    ∃ F : GrothendieckTopology.AbsoluteGlueing J,
      ∃ comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
          F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
        ∃ _compatibilityF :
          ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
            comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
              comparisonF y,
          fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F := by
  -- Peel the source package into the comparison family and its conjugation law, then reuse the
  -- normalized fixed-datum packager.
  obtain ⟨comparisonF, compatibilityF⟩ := sourceF
  exact
    sourceAndFixedAdditiveReconstructionDataOfFixedDatum (𝒮 := 𝒮) hAbelian
      F comparisonF compatibilityF hfixed

/-- Helper for Chap08 Lemma 8 11 8/Part16: a combined source-and-fixed reconstruction package
projects to the fixed additive reconstruction data for its chosen absolute-glueing object. -/
theorem fixedAbsoluteGlueingAddCommSheafDataOfSourceAndFixedData
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (data :
      ∃ F : GrothendieckTopology.AbsoluteGlueing J,
        ∃ comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
            F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
          ∃ _compatibilityF :
            ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
              comparisonF x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
                comparisonF y,
            fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian F) :
    fixedAbsoluteGlueingAddCommSheafData (𝒮 := 𝒮) hAbelian
      (Classical.choose data) := by
  -- Read the fixed additive reconstruction from the same dependent package that chose the
  -- absolute-glueing object, keeping the owner object definitionally aligned.
  obtain ⟨_comparisonF, _compatibilityF, hfixed⟩ := Classical.choose_spec data
  exact hfixed

end CategoryTheory
