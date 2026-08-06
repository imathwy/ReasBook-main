import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Construction_14_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Theorem_14_4_2

open CategoryTheory Limits
open HomotopicalAlgebra

noncomputable section

universe u

-- Semantic recall via `lean_leansearch` did not surface a canonical library owner for this
-- reconstruction corollary. Local Chapter 14 precedent already provides the pair-side canonical
-- split homomorphism together with its bijectivity theorem, so this file states Corollary 14.4.3
-- as the bridge from an explicit pair/reduced equivalence and an explicit natural comparison on
-- the reduced side.

local notation "BasedSpace" => Under (⊤_ TopCat)
local notation "NBasedSpace" => nondegeneratelyBasedSpace

/-- The reconstructed pair homology theory obtained by transporting a reduced theory `E`
back across a chosen equivalence from pair homology theories to reduced homology theories. -/
abbrev reconstructedPairHomologyTheory
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    (equivalence :
      PairHomologyTheoryWithCoefficients ≃
        ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup)
    (E : ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup) :
    PairHomologyTheory (equivalence.symm E).coefficients :=
  (equivalence.symm E).theory

/-- A chosen family of additive equivalences identifying the reduced homology of the
reconstructed pair theory with the given reduced theory `E`. -/
abbrev reconstructedReducedHomologyComparison
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    (equivalence :
      PairHomologyTheoryWithCoefficients ≃
        ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup)
    (E : ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup)
    (q : ℤ) :=
  ∀ X : NBasedSpace,
    basedReducedHomology (reconstructedPairHomologyTheory equivalence E) q X.obj ≃+
      (E.homology q).obj X

/-- The chosen reduced-side comparison is natural when it forms a commuting square with the
reduced-homology maps induced by every morphism of nondegenerately based spaces. -/
abbrev reconstructedReducedHomologyComparisonNatural
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    (equivalence :
      PairHomologyTheoryWithCoefficients ≃
        ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup)
    (E : ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup)
    (q : ℤ)
    (comparison : reconstructedReducedHomologyComparison equivalence E q) : Prop :=
  ∀ ⦃X Y : NBasedSpace⦄ (f : X ⟶ Y),
    CommSq
      (AddCommGrpCat.ofHom
        (basedHomologyReducedMap
          (reconstructedPairHomologyTheory equivalence E) q f.hom))
      (AddCommGrpCat.ofHom (comparison X).toAddMonoidHom)
      (AddCommGrpCat.ofHom (comparison Y).toAddMonoidHom)
      (AddCommGrpCat.ofHom (((E.homology q).map f).hom))

/-- The naturality square for a reconstructed reduced-homology comparison as an equality of
composites. -/
theorem reconstructedReducedHomologyComparisonNatural_w
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    (equivalence :
      PairHomologyTheoryWithCoefficients ≃
        ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup)
    (E : ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup)
    (q : ℤ)
    (comparison : reconstructedReducedHomologyComparison equivalence E q)
    (comparison_natural :
      reconstructedReducedHomologyComparisonNatural equivalence E q comparison)
    {X Y : NBasedSpace} (f : X ⟶ Y) :
    (comparison Y).toAddMonoidHom.comp
        (basedHomologyReducedMap
          (reconstructedPairHomologyTheory equivalence E) q f.hom) =
      (((E.homology q).map f).hom).comp (comparison X).toAddMonoidHom := by
  simpa using congrArg AddCommGrpCat.Hom.hom (comparison_natural f).w

/-- The additive equivalence on target groups obtained by combining the chosen reduced-side
comparison with the identity on the point summand. -/
abbrev reconstructedUnreducedHomologyTargetEquiv
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    (equivalence :
      PairHomologyTheoryWithCoefficients ≃
        ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup)
    (E : ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup)
    (q : ℤ)
    (comparison : reconstructedReducedHomologyComparison equivalence E q)
    (X : NBasedSpace) :
    basedReducedHomology (reconstructedPairHomologyTheory equivalence E) q X.obj ×
        pointHomology (reconstructedPairHomologyTheory equivalence E) q ≃+
      ((E.homology q).obj X × pointHomology (reconstructedPairHomologyTheory equivalence E) q) :=
  (comparison X).prodCongr
    (AddEquiv.refl (pointHomology (reconstructedPairHomologyTheory equivalence E) q))

/-- The reconstructed unreduced homology map to `E_q(X) × E_q(*)`, obtained by composing the
canonical Chapter 14 split homomorphism with the chosen reduced-side comparison. -/
def reconstructedUnreducedHomologySplitHom
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    (equivalence :
      PairHomologyTheoryWithCoefficients ≃
        ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup)
    (E : ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup)
    (q : ℤ)
    (comparison : reconstructedReducedHomologyComparison equivalence E q)
    (X : NBasedSpace) :
    absoluteHomology (reconstructedPairHomologyTheory equivalence E) q X.obj →+
      ((E.homology q).obj X × pointHomology (reconstructedPairHomologyTheory equivalence E) q) :=
  (reconstructedUnreducedHomologyTargetEquiv equivalence E q comparison X).toAddMonoidHom.comp
    (basedHomologySplitHom (reconstructedPairHomologyTheory equivalence E) q X.obj)

/-- Corollary 14.4.3 (1). Let `E` be a reduced homology theory on nondegenerately based spaces,
and let `equivalence` be an explicit reconstruction equivalence as in Theorem 14.4.2. If the
reduced homology of the reconstructed unreduced theory is identified with `E` by a family of
additive equivalences `comparison`, then the reconstructed split homomorphism to `E_q(X) × E_q(*)`
is bijective for every nondegenerately based space `X`. -/
theorem reconstructedUnreducedHomologySplitHom_bijective
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    (equivalence :
      PairHomologyTheoryWithCoefficients ≃
        ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup)
    (E : ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup)
    (q : ℤ)
    (comparison : reconstructedReducedHomologyComparison equivalence E q)
    (X : NBasedSpace) :
    Function.Bijective (reconstructedUnreducedHomologySplitHom equivalence E q comparison X) := by
  let splitComparison :=
    reconstructedUnreducedHomologyTargetEquiv equivalence E q comparison X
  change Function.Bijective
    (fun x ↦ splitComparison
      (basedHomologySplitHom (reconstructedPairHomologyTheory equivalence E) q X.obj x))
  refine ⟨?_, ?_⟩
  · intro a b hab
    apply (basedHomologySplit (reconstructedPairHomologyTheory equivalence E) q X.obj).injective
    exact splitComparison.injective hab
  · intro z
    rcases splitComparison.surjective z with ⟨y, rfl⟩
    rcases
        (basedHomologySplit (reconstructedPairHomologyTheory equivalence E) q X.obj).surjective y
      with
      ⟨x, rfl⟩
    exact ⟨x, rfl⟩

/-- Corollary 14.4.3 (2). With the naturality hypothesis on `comparison`, the reconstructed split
homomorphism from Corollary 14.4.3 (1) is natural in `X`. -/
theorem reconstructedUnreducedHomologySplit_natural_w
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    (equivalence :
      PairHomologyTheoryWithCoefficients ≃
        ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup)
    (E : ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup)
    (q : ℤ)
    (comparison : reconstructedReducedHomologyComparison equivalence E q)
    (comparison_natural :
      reconstructedReducedHomologyComparisonNatural equivalence E q comparison)
    {X Y : NBasedSpace} (f : X ⟶ Y) :
      (reconstructedUnreducedHomologySplitHom equivalence E q comparison Y).comp
          (basedHomologyAbsoluteMap (reconstructedPairHomologyTheory equivalence E) q f.hom) =
        ((((E.homology q).map f).hom).prodMap
            (AddMonoidHom.id
              (pointHomology (reconstructedPairHomologyTheory equivalence E) q))).comp
          (reconstructedUnreducedHomologySplitHom equivalence E q comparison X) := by
  have htarget :
      (reconstructedUnreducedHomologyTargetEquiv equivalence E q comparison Y).toAddMonoidHom.comp
          ((basedHomologyReducedMap
              (reconstructedPairHomologyTheory equivalence E) q f.hom).prodMap
            (AddMonoidHom.id (pointHomology (reconstructedPairHomologyTheory equivalence E) q))) =
        ((((E.homology q).map f).hom).prodMap
            (AddMonoidHom.id
              (pointHomology (reconstructedPairHomologyTheory equivalence E) q))).comp
          (reconstructedUnreducedHomologyTargetEquiv equivalence E q comparison X).toAddMonoidHom :=
      by
    apply AddMonoidHom.ext
    intro x
    rcases x with ⟨a, b⟩
    refine Prod.ext ?_ ?_
    · simpa [reconstructedUnreducedHomologyTargetEquiv] using
        congrArg (fun g ↦ g a)
          (reconstructedReducedHomologyComparisonNatural_w
            equivalence E q comparison comparison_natural f)
    · rfl
  rw [reconstructedUnreducedHomologySplitHom, AddMonoidHom.comp_assoc,
    basedHomologySplit_natural_w, ← AddMonoidHom.comp_assoc, reconstructedUnreducedHomologySplitHom]
  rw [htarget]
  rw [AddMonoidHom.comp_assoc]

/-- Corollary 14.4.3 (2). With the naturality hypothesis on `comparison`, the reconstructed split
homomorphism from Corollary 14.4.3 (1) is natural in `X`. -/
theorem reconstructedUnreducedHomologySplit_natural
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    (equivalence :
      PairHomologyTheoryWithCoefficients ≃
        ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup)
    (E : ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup)
    (q : ℤ)
    (comparison : reconstructedReducedHomologyComparison equivalence E q)
    (comparison_natural :
      reconstructedReducedHomologyComparisonNatural equivalence E q comparison)
    {X Y : NBasedSpace} (f : X ⟶ Y) :
    CommSq
      (AddCommGrpCat.ofHom
        (basedHomologyAbsoluteMap (reconstructedPairHomologyTheory equivalence E) q f.hom))
      (AddCommGrpCat.ofHom
        (reconstructedUnreducedHomologySplitHom equivalence E q comparison X))
      (AddCommGrpCat.ofHom
        (reconstructedUnreducedHomologySplitHom equivalence E q comparison Y))
      (AddCommGrpCat.ofHom
        ((((E.homology q).map f).hom).prodMap
          (AddMonoidHom.id
            (pointHomology (reconstructedPairHomologyTheory equivalence E) q)))) := by
  refine ⟨?_⟩
  simpa using congrArg AddCommGrpCat.ofHom
    (reconstructedUnreducedHomologySplit_natural_w
      equivalence E q comparison comparison_natural f)
