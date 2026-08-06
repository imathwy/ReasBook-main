import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Theorem_13_1_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Construction_14_1_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Definition_14_4_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Theorem_14_2_1

open CategoryTheory Limits
open HomotopicalAlgebra

noncomputable section

universe u

-- Semantic recall via `lean_leansearch` confirmed that the source phrase "is equivalent to"
-- should be formalized by a type equivalence `≃`. Local Chapter 13 and Chapter 14 precedent
-- already fix the pair-side and reduced-side owners used below.

local notation "BasedSpace" => Under (⊤_ TopCat)

/- The source-facing type of homology theories on CW pairs together with their coefficient
group. -/
abbrev CWPairTheoryWithCoefficients : Type _ :=
  Σ π : AddCommGrpCat.{u}, CWPairHomologyTheory π

/-- The coefficient group of a bundled CW-pair homology theory. -/
abbrev CWPairTheoryWithCoefficients.coefficients
    (H : CWPairTheoryWithCoefficients) : AddCommGrpCat.{u} :=
  H.1

/-- The underlying bundled Chapter 13 CW-pair homology theory of a coefficient-theory pair. -/
abbrev CWPairTheoryWithCoefficients.theory
    (H : CWPairTheoryWithCoefficients) :
    CWPairHomologyTheory H.coefficients :=
  H.2

/-- The underlying graded covariant functor of a bundled CW-pair homology theory. -/
abbrev CWPairTheoryWithCoefficients.homology
    (H : CWPairTheoryWithCoefficients) :
    ℤ → CWPair ⥤ ModuleCat.{u} ℤ :=
  H.theory

/-- A bundled CW-pair homology theory carries the source-facing CW-pair axioms on its underlying
graded functor. -/
instance instIsHomologyTheoryOnCWPairsOfCWPairTheoryWithCoefficients
    (H : CWPairTheoryWithCoefficients) :
    IsHomologyTheoryOnCWPairs H.coefficients H.homology :=
  H.theory.2

/-- A bundled CW-pair homology theory with coefficients exposes the Chapter 13 dimension,
exactness, excision, additivity, and weak-equivalence axioms on its underlying graded functor. -/
theorem CWPairTheoryWithCoefficients.spec
    (H : CWPairTheoryWithCoefficients) :
    (∀ pt : CWPair, Nonempty (pt ≅ IsCWPair.point) →
      Nonempty ((H.homology 0).obj pt ≅ ModuleCat.of ℤ H.coefficients)) ∧
      (∀ pt : CWPair, Nonempty (pt ≅ IsCWPair.point) →
        ∀ q : ℤ, q ≠ 0 → IsZero ((H.homology q).obj pt)) ∧
      (∀ q : ℤ, ∀ P : CWPair,
        (CategoryTheory.ShortComplex.mk
          ((H.homology q).map (IsCWPair.subspaceInclusion P))
          ((H.homology q).map (IsCWPair.absoluteToRelative P))
          (H.theory.2.exact₁_zero q P)).Exact) ∧
      (∀ q : ℤ, ∀ P : CWPair,
        (CategoryTheory.ShortComplex.mk
          ((H.homology q).map (IsCWPair.absoluteToRelative P))
          ((H.theory.2.boundary q).app P)
          (H.theory.2.exact₂_zero q P)).Exact) ∧
      (∀ q : ℤ, ∀ P : CWPair,
        (CategoryTheory.ShortComplex.mk
          ((H.theory.2.boundary q).app P)
          ((H.homology (q - 1)).map (IsCWPair.subspaceInclusion P))
          (H.theory.2.exact₃_zero q P)).Exact) ∧
      (∀ q : ℤ, ∀ P : CWPair, ∀ U : Set (IsCWPair.space P),
        ∀ hU : closure U ⊆ interior (IsCWPair.subspace P),
          IsIso ((H.homology q).map (IsCWPair.removeSubsetInclusion P U hU))) ∧
      (∀ {ι : Type u}, ∀ q : ℤ, ∀ P : ι → CWPair,
        Nonempty (((H.homology q).obj (IsCWPair.sigmaPair P)) ≅
          ∐ fun i : ι ↦ (H.homology q).obj (P i))) ∧
      (∀ q : ℤ, ∀ {P Q : CWPair} (f : P ⟶ Q),
        [WeakEquivalence f] → IsIso ((H.homology q).map f)) := by
  simpa [CWPairTheoryWithCoefficients.homology] using H.theory.spec

/-- Weakly equivalent CW pairs induce isomorphisms on the homology groups of a bundled
`CWPairTheoryWithCoefficients`. -/
instance CWPairTheoryWithCoefficients.map_isIso_of_weakEquivalence
    (H : CWPairTheoryWithCoefficients) (q : ℤ) {P Q : CWPair} (f : P ⟶ Q)
    [WeakEquivalence f] :
    IsIso ((H.homology q).map f) := by
  change IsIso ((H.theory q).map f)
  infer_instance

/-- The source-facing type of reduced homology theories on based CW complexes for a fixed Chapter
14 based-CW reduced suspension/cofiber setup. -/
abbrev ReducedTheoryOnBasedCWComplexes
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    (setup : BasedCWReducedSuspensionCofiberSetup) : Type _ :=
  { E : ℤ → BasedCWComplex ⥤ AddCommGrpCat.{u} //
      ReducedHomologyTheoryOnBasedCWComplexes.{0}
        setup.suspension setup.cofiber setup.cofiberMap E }

/-- The underlying graded covariant functor of a bundled reduced homology theory on based CW
complexes. -/
abbrev ReducedTheoryOnBasedCWComplexes.homology
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    {setup : BasedCWReducedSuspensionCofiberSetup}
    (E : ReducedTheoryOnBasedCWComplexes setup) :
    ℤ → BasedCWComplex ⥤ AddCommGrpCat.{u} :=
  E.1

/-- A bundled reduced theory on based CW complexes carries its defining reduced homology theory
instance on the underlying graded functor. -/
instance instReducedHomologyTheoryOnBasedCWComplexes
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    {setup : BasedCWReducedSuspensionCofiberSetup}
    (E : ReducedTheoryOnBasedCWComplexes setup) :
    ReducedHomologyTheoryOnBasedCWComplexes.{0}
      setup.suspension setup.cofiber setup.cofiberMap
        E.homology := by
  simpa [ReducedTheoryOnBasedCWComplexes.homology] using E.2

/-- A bundled reduced theory on based CW complexes is determined by the source-facing reduced
homology theory structure on its underlying graded functor. -/
theorem ReducedTheoryOnBasedCWComplexes.spec
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    {setup : BasedCWReducedSuspensionCofiberSetup}
    (E : ReducedTheoryOnBasedCWComplexes setup) :
    ReducedHomologyTheoryOnBasedCWComplexes.{0}
      setup.suspension setup.cofiber setup.cofiberMap
        E.homology := by
  simpa [ReducedTheoryOnBasedCWComplexes.homology] using E.2

private abbrev basedCWReducedPairFunctor : BasedCWComplex ⥤ CWPair where
  obj X := ⟨basedReducedPair X.obj, by sorry⟩
  map f := CategoryTheory.ObjectProperty.homMk (basedMapReducedPairHom f.hom)
  map_id := by
    intro X
    apply CategoryTheory.ObjectProperty.hom_ext
    apply SpacePair.hom_ext
    rfl
  map_comp := by
    intro X Y Z f g
    apply CategoryTheory.ObjectProperty.hom_ext
    apply SpacePair.hom_ext
    rfl

private abbrev cwPairReducedTheoryHomology
    (H : CWPairTheoryWithCoefficients) :
    ℤ → BasedCWComplex ⥤ AddCommGrpCat.{u} :=
  fun q ↦ basedCWReducedPairFunctor ⋙ H.homology q ⋙ forget₂ (ModuleCat ℤ) AddCommGrpCat

private theorem cwPairReducedTheoryHomology_isReducedTheory
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    (setup : BasedCWReducedSuspensionCofiberSetup)
    (H : CWPairTheoryWithCoefficients) :
    ReducedHomologyTheoryOnBasedCWComplexes.{0}
      setup.suspension setup.cofiber setup.cofiberMap
        (cwPairReducedTheoryHomology H) := by
  sorry

/-- A bundled CW-pair homology theory determines a reduced homology theory on based CW
complexes by restricting to the canonical based-point pair `X ↦ (X, {x₀})` and forgetting the
ambient `ℤ`-module structure to its underlying additive group. -/
def cwPairTheoryToReducedTheoryOnBasedCWComplexes
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    (setup : BasedCWReducedSuspensionCofiberSetup)
    (H : CWPairTheoryWithCoefficients) :
    ReducedTheoryOnBasedCWComplexes setup :=
  ⟨cwPairReducedTheoryHomology H, cwPairReducedTheoryHomology_isReducedTheory setup H⟩

/-- Theorem 14.4.6: a homology theory on CW pairs is equivalent to a reduced homology theory on
based CW complexes. The pair side is packaged by `CWPairTheoryWithCoefficients`, namely a
coefficient group together with a bundled Chapter 13 owner `CWPairHomologyTheory`, while the
reduced side is packaged by `ReducedTheoryOnBasedCWComplexes setup` for the chosen Chapter 14
based-CW reduced suspension/cofiber setup `setup`. Since the reduced owner records exactness and
suspension only as existence data, the source statement is formalized as the existence of a type
equivalence rather than a chosen inverse construction carrying extra concrete CW-pair boundary
data.
-/
theorem pairHomologyTheoryEquivReducedHomologyTheoryOnBasedCWComplexes
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    (setup : BasedCWReducedSuspensionCofiberSetup) :
    Nonempty (CWPairTheoryWithCoefficients ≃ ReducedTheoryOnBasedCWComplexes setup) := by
  sorry

/-- Any explicit equivalence between CW-pair theories and reduced theories on based CW complexes
yields the expected forward and backward transport identities on the underlying carriers. -/
theorem pairHomologyTheoryEquivReducedHomologyTheoryOnBasedCWComplexes_explicit
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    {setup : BasedCWReducedSuspensionCofiberSetup}
    (equivalence :
      CWPairTheoryWithCoefficients ≃ ReducedTheoryOnBasedCWComplexes setup) :
    (∀ H : CWPairTheoryWithCoefficients, equivalence.symm (equivalence H) = H) ∧
      ∀ E : ReducedTheoryOnBasedCWComplexes setup, equivalence (equivalence.symm E) = E := by
  exact ⟨equivalence.left_inv, equivalence.right_inv⟩
