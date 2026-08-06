import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Construction_17_3_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Definition_17_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Theorem_17_3_4.SubmoduleFree
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.PrincipalIdealDomain

noncomputable section

open CategoryTheory

universe u

/-- The `Ext¹` coefficient functor `M ↦ Ext¹_R(H_(n - 1)(X), M)` appearing on the left of the
universal coefficient sequence for cohomology. -/
abbrev universalCoefficientExtFunctor
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (n : ℤ) :
    ModuleCat R ⥤ AddCommGrpCat :=
  ((Ext R (ModuleCat R) 1).obj (Opposite.op (X.homology (n - 1)))) ⋙
    forget₂ (ModuleCat R) AddCommGrpCat

/-- The `Ext¹` term in the universal coefficient sequence for cohomology, viewed as an abelian
group. -/
abbrev universalCoefficientExtTerm
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    AddCommGrpCat :=
  (universalCoefficientExtFunctor R X n).obj M

/-- `universalCoefficientExtTerm R X M n` is the additive-group object underlying
`Ext¹_R(H_(n - 1)(X), M)`. -/
@[simp] theorem universalCoefficientExtTerm_def
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    universalCoefficientExtTerm R X M n =
      (forget₂ (ModuleCat R) AddCommGrpCat).obj
        (((Ext R (ModuleCat R) 1).obj (Opposite.op (X.homology (n - 1)))).obj M) :=
  rfl

/-- Evaluating `universalCoefficientExtFunctor R X n` at `M` gives
`universalCoefficientExtTerm R X M n`. -/
@[simp] theorem universalCoefficientExtFunctor_obj
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    (universalCoefficientExtFunctor R X n).obj M = universalCoefficientExtTerm R X M n :=
  rfl

/-- The `Hom` coefficient functor `M ↦ Hom(H_n(X), M)` appearing on the right of the universal
coefficient sequence for cohomology. -/
abbrev universalCoefficientHomFunctor
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (n : ℤ) :
    ModuleCat R ⥤ AddCommGrpCat :=
  ((CategoryTheory.linearCoyoneda R (ModuleCat R)).obj (Opposite.op (X.homology n))) ⋙
    forget₂ (ModuleCat R) AddCommGrpCat

/-- The `Hom` term in the universal coefficient sequence for cohomology, viewed as an abelian
group. -/
abbrev universalCoefficientHomTerm
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    AddCommGrpCat :=
  (universalCoefficientHomFunctor R X n).obj M

/-- `universalCoefficientHomTerm R X M n` is the abelian group of `R`-linear maps
`X.homology n ⟶ M`. -/
@[simp] theorem universalCoefficientHomTerm_def
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    universalCoefficientHomTerm R X M n = AddCommGrpCat.of (X.homology n ⟶ M) :=
  rfl

/-- Evaluating `universalCoefficientHomFunctor R X n` at `M` gives
`universalCoefficientHomTerm R X M n`. -/
@[simp] theorem universalCoefficientHomFunctor_obj
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    (universalCoefficientHomFunctor R X n).obj M = universalCoefficientHomTerm R X M n :=
  rfl

-- Semantic recall via `lean_leansearch`: `Ext R (ModuleCat R) 1` and
-- `CategoryTheory.linearCoyoneda R (ModuleCat R)` are the canonical functorial owners for the
-- outer `Ext¹` and `Hom` terms, and short exact sequences of abelian groups are packaged by
-- `ShortComplex` together with `ShortComplex.ShortExact`.

/-- The cohomology term in the universal coefficient sequence for cohomology, viewed as an
abelian group. -/
abbrev universalCoefficientCohomologyTerm
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    AddCommGrpCat :=
  (forget₂ (ModuleCat ℤ) AddCommGrpCat).obj (cohomologyWithCoefficients R X M n)

/-- `universalCoefficientCohomologyTerm R X M n` is the additive-group object underlying
`H^n(Hom(X, M))`. -/
@[simp] theorem universalCoefficientCohomologyTerm_def
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    universalCoefficientCohomologyTerm R X M n =
      (forget₂ (ModuleCat ℤ) AddCommGrpCat).obj (cohomologyWithCoefficients R X M n) :=
  rfl

private def homCochainComplexMap
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ)
    {M N : ModuleCat R} (f : M ⟶ N) :
    homCochainComplex R X M ⟶ homCochainComplex R X N :=
  HomologicalComplex.Hom.mk
    (fun i ↦ ModuleCat.ofHom (Linear.rightComp R (X.X i) f))
    (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      subst hij
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro g
      apply ModuleCat.hom_ext
      ext x
      simp only [homCochainComplex]
      change ModuleCat.Hom.hom
          ((Linear.leftComp ℤ N (X.d (i + 1) i)) ((Linear.rightComp R (X.X i) f) g)) x =
        ModuleCat.Hom.hom
          ((Linear.rightComp R (X.X (i + 1)) f) ((Linear.leftComp ℤ M (X.d (i + 1) i)) g)) x
      rw [CategoryTheory.Linear.leftComp_apply, CategoryTheory.Linear.rightComp_apply,
        CategoryTheory.Linear.rightComp_apply, CategoryTheory.Linear.leftComp_apply]
      rfl
    )

private theorem homCochainComplexMap_id
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) :
    homCochainComplexMap R X (𝟙 M) = 𝟙 (homCochainComplex R X M) := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply ModuleCat.hom_ext
  ext x
  change ModuleCat.Hom.hom (𝟙 M) (ModuleCat.Hom.hom φ x) = ModuleCat.Hom.hom φ x
  simp

private theorem homCochainComplexMap_comp
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ)
    {L M N : ModuleCat R} (f : L ⟶ M) (g : M ⟶ N) :
    homCochainComplexMap R X (f ≫ g) =
      homCochainComplexMap R X f ≫ homCochainComplexMap R X g := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply ModuleCat.hom_ext
  ext x
  change ModuleCat.Hom.hom g (ModuleCat.Hom.hom f (ModuleCat.Hom.hom φ x)) =
    ModuleCat.Hom.hom g (ModuleCat.Hom.hom f (ModuleCat.Hom.hom φ x))
  rfl

/-- The canonical coefficient-change morphism on `H^n(Hom(X, M))` induced by a morphism of
coefficient modules. -/
abbrev universalCoefficientCohomologyCoefficientMap
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (n : ℤ)
    {M N : ModuleCat R} (f : M ⟶ N) :
    universalCoefficientCohomologyTerm R X M n ⟶ universalCoefficientCohomologyTerm R X N n :=
  (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
    (HomologicalComplex.homologyMap (homCochainComplexMap R X f) n)

/-- The canonical coefficient-change morphism on `H^n(Hom(X, M))` respects identities. -/
theorem universalCoefficientCohomologyCoefficientMap_id
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (n : ℤ)
    (M : ModuleCat R) :
    universalCoefficientCohomologyCoefficientMap R X n (𝟙 M) =
      𝟙 (universalCoefficientCohomologyTerm R X M n) := by
  simpa only [universalCoefficientCohomologyCoefficientMap, homCochainComplexMap_id,
    HomologicalComplex.homologyMap_id] using
    (AddCommGrpCat.ofHom_id :
      AddCommGrpCat.ofHom (AddMonoidHom.id (cohomologyWithCoefficients R X M n)) =
        𝟙 (AddCommGrpCat.of (cohomologyWithCoefficients R X M n)))

/-- The canonical coefficient-change morphism on `H^n(Hom(X, M))` respects composition. -/
theorem universalCoefficientCohomologyCoefficientMap_comp
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (n : ℤ)
    {L M N : ModuleCat R} (f : L ⟶ M) (g : M ⟶ N) :
    universalCoefficientCohomologyCoefficientMap R X n (f ≫ g) =
      universalCoefficientCohomologyCoefficientMap R X n f ≫
        universalCoefficientCohomologyCoefficientMap R X n g := by
  simp only [universalCoefficientCohomologyCoefficientMap]
  rw [homCochainComplexMap_comp, HomologicalComplex.homologyMap_comp]
  exact (forget₂ (ModuleCat ℤ) AddCommGrpCat).map_comp
    (HomologicalComplex.homologyMap (homCochainComplexMap R X f) n)
    (HomologicalComplex.homologyMap (homCochainComplexMap R X g) n)

/-- Helper for Theorem 17.3.4: the right-hand `Hom` functor sends `f : M ⟶ N` to postcomposition
by `f` on morphisms `X.homology n ⟶ M`. -/
@[simp] theorem universalCoefficientHomFunctor_map_apply
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (n : ℤ)
    {M N : ModuleCat R} (f : M ⟶ N) (g : X.homology n ⟶ M) :
    (universalCoefficientHomFunctor R X n).map f g = g ≫ f := by
  -- Unfold the `linearCoyoneda` action once so the right edge is visibly postcomposition.
  rfl

/-- Helper for Theorem 17.3.4: the right-hand morphism in the universal coefficient sequence is
the additive-group morphism underlying the Kronecker pairing from Construction 17.3.3. -/
abbrev cohomologyToHomMap
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    universalCoefficientCohomologyTerm R X M n ⟶ universalCoefficientHomTerm R X M n :=
  (forget₂ (ModuleCat ℤ) AddCommGrpCat).map (kroneckerPairing R X M n)

/-- Helper for Theorem 17.3.4: `cohomologyToHomMap` is definitionally the additive-group map
obtained from `kroneckerPairing`. -/
@[simp] theorem cohomologyToHomMap_def
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    cohomologyToHomMap R X M n =
      (forget₂ (ModuleCat ℤ) AddCommGrpCat).map (kroneckerPairing R X M n) :=
  rfl

/-- Helper for Theorem 17.3.4: evaluating `kroneckerCocycleToHom` on a homology class represented
by a cycle is just evaluation of the cocycle on that chosen cycle representative. -/
theorem kroneckerCocycleToHom_apply_homologyπ
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ)
    (φ : ((homCochainComplex R X M).sc n).moduleCatLeftHomologyData.K) (γ : X.cycles n) :
    ModuleCat.Hom.hom (kroneckerCocycleToHom R X M n φ) ((X.homologyπ n) γ) =
      ModuleCat.Hom.hom φ.1 ((X.iCycles n) γ) := by
  -- Compare with the source-side quotient formula and then evaluate both sides on `γ`.
  simpa using congrArg (fun f ↦ ModuleCat.Hom.hom f γ)
    (homologyπ_kroneckerCocycleToHom R X M n φ)

/-- Helper for Theorem 17.3.4: precomposing `cohomologyToHomMap` with the quotient from cocycles
to cohomology recovers the cocycle-level Kronecker map after forgetting to abelian groups. -/
theorem homologyπ_cohomologyToHomMap
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    (forget₂ (ModuleCat ℤ) AddCommGrpCat).map ((homCochainComplex R X M).homologyπ n) ≫
        cohomologyToHomMap R X M n =
      (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
        (((homCochainComplex R X M).sc n).moduleCatCyclesIso.hom ≫
          kroneckerCocycleToHom R X M n) := by
  -- Rewrite the right map back to `kroneckerPairing`, then transport the source theorem through
  -- the forgetful functor to expose the cocycle-level formula.
  simpa [cohomologyToHomMap, Category.assoc] using
    congrArg
      ((forget₂ (ModuleCat ℤ) AddCommGrpCat).map)
      (homologyπ_kroneckerPairing R X M n)

/-- Helper for Theorem 17.3.4: the coefficient-change map on cohomology with coefficients moves
past the quotient from cocycles according to `HomologicalComplex.homologyπ_naturality`. -/
theorem homologyπ_universalCoefficientCohomologyCoefficientMap
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (n : ℤ)
    {M N : ModuleCat R} (f : M ⟶ N) :
    (forget₂ (ModuleCat ℤ) AddCommGrpCat).map ((homCochainComplex R X M).homologyπ n) ≫
        universalCoefficientCohomologyCoefficientMap R X n f =
      (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
        (HomologicalComplex.cyclesMap (homCochainComplexMap R X f) n) ≫
          (forget₂ (ModuleCat ℤ) AddCommGrpCat).map ((homCochainComplex R X N).homologyπ n) := by
  -- Move the homology quotient past `homologyMap` using the standard naturality square.
  rw [universalCoefficientCohomologyCoefficientMap, ← Functor.map_comp]
  exact congrArg
    ((forget₂ (ModuleCat ℤ) AddCommGrpCat).map)
    (HomologicalComplex.homologyπ_naturality (φ := homCochainComplexMap R X f) (i := n))

/-- Helper for Theorem 17.3.4: changing coefficients by `f : M ⟶ N` commutes with the
cocycle-level Kronecker map once both sides are viewed on the abstract cycles objects. -/
theorem kroneckerCocycleToHom_natural
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ)
    {M N : ModuleCat R} (f : M ⟶ N) (n : ℤ) :
    (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
        (HomologicalComplex.cyclesMap (homCochainComplexMap R X f) n) ≫
      (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
        (((homCochainComplex R X N).sc n).moduleCatCyclesIso.hom ≫
          kroneckerCocycleToHom R X N n) =
    (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
        (((homCochainComplex R X M).sc n).moduleCatCyclesIso.hom ≫
          kroneckerCocycleToHom R X M n) ≫
      (universalCoefficientHomFunctor R X n).map f := by
  -- Compare both cocycle-level maps on a represented homology class and rewrite the coefficient
  -- change on cocycles through `HomologicalComplex.cyclesMap_i`.
  ext α
  apply ModuleCat.hom_ext
  ext β
  obtain ⟨γ, rfl⟩ := (ModuleCat.epi_iff_surjective (X.homologyπ n)).1 inferInstance β
  have hcycles :
      ModuleCat.Hom.hom
          (HomologicalComplex.cyclesMap (homCochainComplexMap R X f) n ≫
            (homCochainComplex R X N).iCycles n) α =
        ModuleCat.Hom.hom
          ((homCochainComplex R X M).iCycles n ≫
            (homCochainComplexMap R X f).f n) α := by
    simpa using congrArg
      (fun g ↦ ModuleCat.Hom.hom g α)
      (HomologicalComplex.cyclesMap_i (φ := homCochainComplexMap R X f) (i := n))
  have hleft :
      ModuleCat.Hom.hom
          (((homCochainComplex R X N).sc n).moduleCatCyclesIso.hom ≫
            kroneckerCocycleToHom R X N n)
          (ModuleCat.Hom.hom
            (HomologicalComplex.cyclesMap (homCochainComplexMap R X f) n) α)
        ((X.homologyπ n) γ) =
        ModuleCat.Hom.hom
          f
          (ModuleCat.Hom.hom
            (((homCochainComplex R X M).sc n).moduleCatCyclesIso.hom ≫
              kroneckerCocycleToHom R X M n)
            α ((X.homologyπ n) γ)) := by
    -- Evaluate both cocycle representatives on the chosen cycle representative `γ`.
    let φN : ((homCochainComplex R X N).sc n).moduleCatLeftHomologyData.K :=
      ModuleCat.Hom.hom
        ((homCochainComplex R X N).sc n).moduleCatCyclesIso.hom
        (ModuleCat.Hom.hom (HomologicalComplex.cyclesMap (homCochainComplexMap R X f) n) α)
    let φM : ((homCochainComplex R X M).sc n).moduleCatLeftHomologyData.K :=
      ModuleCat.Hom.hom
        ((homCochainComplex R X M).sc n).moduleCatCyclesIso.hom α
    change ModuleCat.Hom.hom (kroneckerCocycleToHom R X N n φN) ((X.homologyπ n) γ) =
      ModuleCat.Hom.hom f
        (ModuleCat.Hom.hom (kroneckerCocycleToHom R X M n φM) ((X.homologyπ n) γ))
    rw [kroneckerCocycleToHom_apply_homologyπ]
    rw [kroneckerCocycleToHom_apply_homologyπ]
    have hcycles' :
        ModuleCat.Hom.hom
            (((homCochainComplex R X N).sc n).moduleCatCyclesIso.hom ≫
              ((homCochainComplex R X N).sc n).moduleCatLeftHomologyData.i)
            (ModuleCat.Hom.hom
              (HomologicalComplex.cyclesMap (homCochainComplexMap R X f) n) α) =
          ModuleCat.Hom.hom
            (((homCochainComplex R X M).sc n).moduleCatCyclesIso.hom ≫
              ((homCochainComplex R X M).sc n).moduleCatLeftHomologyData.i ≫
                (homCochainComplexMap R X f).f n) α := by
      have hN :
          ModuleCat.Hom.hom
              (((homCochainComplex R X N).sc n).moduleCatCyclesIso.hom ≫
                ((homCochainComplex R X N).sc n).moduleCatLeftHomologyData.i)
              (ModuleCat.Hom.hom
                (HomologicalComplex.cyclesMap (homCochainComplexMap R X f) n) α) =
            ModuleCat.Hom.hom
              ((homCochainComplex R X N).iCycles n)
              (ModuleCat.Hom.hom
                (HomologicalComplex.cyclesMap (homCochainComplexMap R X f) n) α) := by
        simpa [Category.assoc] using congrArg
          (fun g ↦
            ModuleCat.Hom.hom g
              (ModuleCat.Hom.hom
                (HomologicalComplex.cyclesMap (homCochainComplexMap R X f) n) α))
          (CategoryTheory.ShortComplex.moduleCatCyclesIso_hom_i
            (S := (homCochainComplex R X N).sc n))
      have hM :
          ModuleCat.Hom.hom
              ((homCochainComplex R X M).iCycles n ≫
                (homCochainComplexMap R X f).f n) α =
            ModuleCat.Hom.hom
              (((homCochainComplex R X M).sc n).moduleCatCyclesIso.hom ≫
                ((homCochainComplex R X M).sc n).moduleCatLeftHomologyData.i ≫
                  (homCochainComplexMap R X f).f n) α := by
        simpa [Category.assoc] using congrArg
          (fun y ↦ ModuleCat.Hom.hom ((homCochainComplexMap R X f).f n) y)
          (congrArg
            (fun g ↦ ModuleCat.Hom.hom g α)
            (CategoryTheory.ShortComplex.moduleCatCyclesIso_hom_i
              (S := (homCochainComplex R X M).sc n)))
      calc
        ModuleCat.Hom.hom
            (((homCochainComplex R X N).sc n).moduleCatCyclesIso.hom ≫
              ((homCochainComplex R X N).sc n).moduleCatLeftHomologyData.i)
            (ModuleCat.Hom.hom
              (HomologicalComplex.cyclesMap (homCochainComplexMap R X f) n) α) =
          ModuleCat.Hom.hom
            ((homCochainComplex R X N).iCycles n)
            (ModuleCat.Hom.hom
              (HomologicalComplex.cyclesMap (homCochainComplexMap R X f) n) α) := hN
        _ =
          ModuleCat.Hom.hom
            ((homCochainComplex R X M).iCycles n ≫
              (homCochainComplexMap R X f).f n) α := hcycles
        _ =
          ModuleCat.Hom.hom
            (((homCochainComplex R X M).sc n).moduleCatCyclesIso.hom ≫
              ((homCochainComplex R X M).sc n).moduleCatLeftHomologyData.i ≫
                (homCochainComplexMap R X f).f n) α := hM
    simpa [φN, φM, homCochainComplexMap, universalCoefficientHomFunctor_map_apply,
      Category.assoc] using
      congrArg (fun g ↦ ModuleCat.Hom.hom g ((X.iCycles n) γ)) hcycles'
  simpa [universalCoefficientHomFunctor, Functor.map_comp, Category.assoc] using hleft

/-- Helper for Theorem 17.3.4: after precomposing with the quotient from cocycles to cohomology,
the coefficient-change square for `cohomologyToHomMap` reduces to the cocycle-level naturality
of `kroneckerCocycleToHom`. -/
theorem cohomologyToHomMap_natural_afterHomologyPi
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (n : ℤ)
    {M N : ModuleCat R} (f : M ⟶ N) :
    (forget₂ (ModuleCat ℤ) AddCommGrpCat).map ((homCochainComplex R X M).homologyπ n) ≫
        universalCoefficientCohomologyCoefficientMap R X n f ≫
          cohomologyToHomMap R X N n =
      (forget₂ (ModuleCat ℤ) AddCommGrpCat).map ((homCochainComplex R X M).homologyπ n) ≫
        cohomologyToHomMap R X M n ≫
          (universalCoefficientHomFunctor R X n).map f := by
  -- Rewrite both sides to the cocycle-level Kronecker comparison and then apply the previous
  -- naturality lemma.
  have hleft :
      (forget₂ (ModuleCat ℤ) AddCommGrpCat).map ((homCochainComplex R X M).homologyπ n) ≫
          universalCoefficientCohomologyCoefficientMap R X n f ≫
            cohomologyToHomMap R X N n =
        (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
            (HomologicalComplex.cyclesMap (homCochainComplexMap R X f) n) ≫
          (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
            (((homCochainComplex R X N).sc n).moduleCatCyclesIso.hom ≫
              kroneckerCocycleToHom R X N n) := by
    -- First move the quotient map past the coefficient change, then rewrite the right edge back
    -- to the cocycle-level Kronecker comparison.
    calc
      (forget₂ (ModuleCat ℤ) AddCommGrpCat).map ((homCochainComplex R X M).homologyπ n) ≫
            universalCoefficientCohomologyCoefficientMap R X n f ≫
              cohomologyToHomMap R X N n =
          ((forget₂ (ModuleCat ℤ) AddCommGrpCat).map ((homCochainComplex R X M).homologyπ n) ≫
              universalCoefficientCohomologyCoefficientMap R X n f) ≫
            cohomologyToHomMap R X N n := by
              simp [Category.assoc]
      _ =
          ((forget₂ (ModuleCat ℤ) AddCommGrpCat).map
              (HomologicalComplex.cyclesMap (homCochainComplexMap R X f) n) ≫
            (forget₂ (ModuleCat ℤ) AddCommGrpCat).map ((homCochainComplex R X N).homologyπ n)) ≫
              cohomologyToHomMap R X N n := by
                simpa [Category.assoc] using congrArg
                  (fun k ↦ k ≫ cohomologyToHomMap R X N n)
                  (homologyπ_universalCoefficientCohomologyCoefficientMap R X n f)
      _ =
          (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
              (HomologicalComplex.cyclesMap (homCochainComplexMap R X f) n) ≫
            ((forget₂ (ModuleCat ℤ) AddCommGrpCat).map ((homCochainComplex R X N).homologyπ n) ≫
              cohomologyToHomMap R X N n) := by
                simp [Category.assoc]
      _ =
          (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
              (HomologicalComplex.cyclesMap (homCochainComplexMap R X f) n) ≫
            (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
              (((homCochainComplex R X N).sc n).moduleCatCyclesIso.hom ≫
                kroneckerCocycleToHom R X N n) := by
                  simpa [Category.assoc] using congrArg
                    (fun k ↦
                      (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
                        (HomologicalComplex.cyclesMap (homCochainComplexMap R X f) n) ≫ k)
                    (homologyπ_cohomologyToHomMap R X N n)
  have hmiddle :
      (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
          (HomologicalComplex.cyclesMap (homCochainComplexMap R X f) n) ≫
        (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
          (((homCochainComplex R X N).sc n).moduleCatCyclesIso.hom ≫
            kroneckerCocycleToHom R X N n) =
      (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
          (((homCochainComplex R X M).sc n).moduleCatCyclesIso.hom ≫
            kroneckerCocycleToHom R X M n) ≫
        (universalCoefficientHomFunctor R X n).map f :=
    kroneckerCocycleToHom_natural R X f n
  have hright :
      (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
          (((homCochainComplex R X M).sc n).moduleCatCyclesIso.hom ≫
            kroneckerCocycleToHom R X M n) ≫
        (universalCoefficientHomFunctor R X n).map f =
      (forget₂ (ModuleCat ℤ) AddCommGrpCat).map ((homCochainComplex R X M).homologyπ n) ≫
        cohomologyToHomMap R X M n ≫
          (universalCoefficientHomFunctor R X n).map f := by
    -- The left-hand cocycle comparison is exactly the already-normalized right edge, followed by
    -- postcomposition with `f`.
    simpa [Category.assoc] using congrArg
      (fun k ↦ k ≫ (universalCoefficientHomFunctor R X n).map f)
      (homologyπ_cohomologyToHomMap R X M n).symm
  exact hleft.trans (hmiddle.trans hright)

/-- Helper for Theorem 17.3.4: changing coefficients by `f : M ⟶ N` commutes with the descended
Kronecker map `cohomologyToHomMap`. -/
theorem cohomologyToHomMap_natural
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (n : ℤ)
    {M N : ModuleCat R} (f : M ⟶ N) :
    universalCoefficientCohomologyCoefficientMap R X n f ≫ cohomologyToHomMap R X N n =
      cohomologyToHomMap R X M n ≫ (universalCoefficientHomFunctor R X n).map f := by
  -- Cancel the cocycle-to-cohomology quotient map from the left to descend the already-proved
  -- cocycle-level naturality square to cohomology.
  apply (cancel_epi
    ((forget₂ (ModuleCat ℤ) AddCommGrpCat).map ((homCochainComplex R X M).homologyπ n))).1
  simpa [Category.assoc] using
    cohomologyToHomMap_natural_afterHomologyPi R X n f

/-- Helper for Theorem 17.3.4: `boundaryModuleInt R X i` is the textbook boundary module
`B_(i - 1)(X)`, realized as the range of the degree-`i` boundary map
`X_i ⟶ Z_(i - 1)(X)`. -/
abbrev boundaryModuleInt
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (i : ℤ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℤ).next i)] :
    ModuleCat R :=
  ModuleCat.of R
    (LinearMap.range (ModuleCat.Hom.hom (X.toCycles i ((ComplexShape.down ℤ).next i))))

/-- Helper for Theorem 17.3.4: the boundary module `B_i(X)` includes into the cycle module
`Z_i(X)`. -/
abbrev boundaryInclusionInt
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (i : ℤ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℤ).next i)] :
    boundaryModuleInt R X i ⟶ X.cycles ((ComplexShape.down ℤ).next i) :=
  ModuleCat.ofHom
    (LinearMap.range
      (ModuleCat.Hom.hom (X.toCycles i ((ComplexShape.down ℤ).next i)))).subtype

/-- Helper for Theorem 17.3.4: the boundary inclusion is monic because it is the subtype map of a
range. -/
instance boundaryInclusionInt_mono
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (i : ℤ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℤ).next i)] :
    Mono (boundaryInclusionInt R X i) := by
  exact (ModuleCat.mono_iff_injective _).2
    (LinearMap.range
      (ModuleCat.Hom.hom (X.toCycles i ((ComplexShape.down ℤ).next i)))).injective_subtype

/-- Helper for Theorem 17.3.4: the canonical surjection `X_i ⟶ B_(i - 1)(X)` obtained by
factoring the degree-`i` boundary map through its range. -/
def toBoundaryInt
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (i : ℤ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℤ).next i)] :
    X.X i ⟶ boundaryModuleInt R X i :=
  ModuleCat.ofHom
    ((ModuleCat.Hom.hom (X.toCycles i ((ComplexShape.down ℤ).next i))).codRestrict
      (LinearMap.range
        (ModuleCat.Hom.hom (X.toCycles i ((ComplexShape.down ℤ).next i))))
      (fun x ↦ ⟨x, rfl⟩))

/-- Helper for Theorem 17.3.4: composing the boundary projection with the range inclusion recovers
the original boundary map into cycles. -/
@[reassoc, simp] theorem toBoundaryInt_comp_boundaryInclusionInt
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (i : ℤ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℤ).next i)] :
    toBoundaryInt R X i ≫ boundaryInclusionInt R X i =
      X.toCycles i ((ComplexShape.down ℤ).next i) := by
  -- Unfold the range factorization once; `codRestrict` followed by `subtype` is the original map.
  apply ModuleCat.hom_ext
  rfl

/-- Helper for Theorem 17.3.4: the concrete left-boundary map in the short complex `X.sc i`,
followed by the cycles identification, is `X.toCycles (i + 1) i`. -/
private theorem moduleCatLeftHomologyData_f'_moduleCatCyclesIso_inv_int
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (i : ℤ)
    [HomologicalComplex.HasHomology X i] :
    (X.sc i).moduleCatLeftHomologyData.f' ≫ (X.sc i).moduleCatCyclesIso.inv =
      X.toCycles ((ComplexShape.down ℤ).prev i) i := by
  -- Compare both descriptions after postcomposing with the cycle inclusion.
  simpa [Category.assoc] using
    (congrArg (fun f ↦ f ≫ (X.sc i).moduleCatCyclesIso.inv)
      (CategoryTheory.ShortComplex.toCycles_moduleCatCyclesIso_hom (S := X.sc i))).symm

/-- Helper for Theorem 17.3.4: the cycle inclusion `Z_i(X) ⟶ X_i` lands in the kernel of the
boundary projection `X_i ⟶ B_(i - 1)(X)`. -/
@[reassoc, simp] theorem iCycles_comp_toBoundaryInt
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (i : ℤ)
    [HomologicalComplex.HasHomology X i]
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℤ).next i)] :
    X.iCycles i ≫ toBoundaryInt R X i = 0 := by
  -- Recover the genuine boundary map into cycles, then reduce to `iCycles ≫ d = 0`.
  apply (cancel_mono (boundaryInclusionInt R X i)).1
  rw [Category.assoc, toBoundaryInt_comp_boundaryInclusionInt]
  apply (cancel_mono (X.iCycles ((ComplexShape.down ℤ).next i))).1
  simpa [Category.assoc] using
    (HomologicalComplex.iCycles_d (K := X) (i := i) (j := (ComplexShape.down ℤ).next i))

/-- Helper for Theorem 17.3.4: the degreewise cycle-boundary short complex
`0 ⟶ Z_i(X) ⟶ X_i ⟶ B_(i - 1)(X) ⟶ 0`. -/
def cycleBoundaryShortComplexInt
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (i : ℤ)
    [HomologicalComplex.HasHomology X i]
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℤ).next i)] :
    ShortComplex (ModuleCat R) :=
  ShortComplex.mk (X.iCycles i) (toBoundaryInt R X i)
    (iCycles_comp_toBoundaryInt R X i)

/-- Helper for Theorem 17.3.4: the boundary projection `X_i ⟶ B_(i - 1)(X)` is surjective because
`boundaryModuleInt R X i` is defined as the range of `X.toCycles i ((ComplexShape.down ℤ).next i)`.
-/
theorem toBoundaryInt_surjective
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (i : ℤ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℤ).next i)] :
    Function.Surjective (toBoundaryInt R X i) := by
  -- Unpack an element of the range and reuse its defining preimage.
  intro y
  rcases y.2 with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  exact Subtype.ext hx

/-- Helper for Theorem 17.3.4: the kernel of `toBoundaryInt R X i` is exactly the image of the
cycle inclusion `X.iCycles i`. -/
theorem iCycles_exact_toBoundaryInt
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (i : ℤ)
    [HomologicalComplex.HasHomology X i]
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℤ).next i)] :
    Function.Exact (X.iCycles i) (toBoundaryInt R X i) := by
  -- Reduce exactness to the concrete kernel description of `(X.sc i).g`, then transport that
  -- kernel element back to the abstract cycle object via `moduleCatCyclesIso`.
  intro x
  constructor
  · intro hx
    have htoCycles :
        ModuleCat.Hom.hom (X.toCycles i ((ComplexShape.down ℤ).next i)) x = 0 := by
      simpa using congrArg (ModuleCat.Hom.hom (boundaryInclusionInt R X i)) hx
    have hxker' :
        ModuleCat.Hom.hom
            (X.toCycles i ((ComplexShape.down ℤ).next i) ≫
              X.iCycles ((ComplexShape.down ℤ).next i)) x = 0 := by
      change ModuleCat.Hom.hom (X.iCycles ((ComplexShape.down ℤ).next i))
          (ModuleCat.Hom.hom (X.toCycles i ((ComplexShape.down ℤ).next i)) x) = 0
      simpa using congrArg
        (ModuleCat.Hom.hom (X.iCycles ((ComplexShape.down ℤ).next i))) htoCycles
    have hxker : ModuleCat.Hom.hom ((X.sc i).g) x = 0 := by
      simpa [HomologicalComplex.toCycles_i] using hxker'
    let xKer : (X.sc i).moduleCatLeftHomologyData.K := ⟨x, hxker⟩
    refine ⟨ModuleCat.Hom.hom (X.sc i).moduleCatCyclesIso.inv xKer, ?_⟩
    -- Apply the concrete cycles inclusion and use the comparison isomorphism to recover `x`.
    simpa using congrArg
      (fun f ↦ ModuleCat.Hom.hom f xKer)
      (CategoryTheory.ShortComplex.moduleCatCyclesIso_inv_iCycles (S := X.sc i))
  · rintro ⟨γ, rfl⟩
    -- Boundaries vanish on cycles by construction of `cycleBoundaryShortComplexInt`.
    simpa [cycleBoundaryShortComplexInt] using
      (CategoryTheory.ShortComplex.moduleCat_zero_apply
        (S := cycleBoundaryShortComplexInt R X i) γ)

/-- Helper for Theorem 17.3.4: the canonical degreewise sequence
`0 ⟶ Z_i(X) ⟶ X_i ⟶ B_(i - 1)(X) ⟶ 0` is short exact. -/
theorem cycleBoundaryShortComplexInt_shortExact
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (i : ℤ)
    [HomologicalComplex.HasHomology X i]
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℤ).next i)] :
    (cycleBoundaryShortComplexInt R X i).ShortExact := by
  -- Package the already-normalized exactness, injectivity, and surjectivity facts into the
  -- canonical `ModuleCat` short exactness constructor.
  refine ModuleCat.shortComplex_shortExact (cycleBoundaryShortComplexInt R X i) ?_ ?_ ?_
  · simpa [cycleBoundaryShortComplexInt] using iCycles_exact_toBoundaryInt R X i
  · simpa [cycleBoundaryShortComplexInt] using
      (ModuleCat.mono_iff_injective (X.iCycles i)).1 (inferInstance : Mono (X.iCycles i))
  · simpa [cycleBoundaryShortComplexInt] using toBoundaryInt_surjective R X i

/-- Helper for Theorem 17.3.4: once the right-hand boundary term of
`cycleBoundaryShortComplexInt R X i` is projective, the short exact sequence of cycles, chains,
and boundaries splits. This packages the repeated splitting construction used in the main theorem.
-/
theorem cycleBoundaryShortComplexInt_splitting_of_projectiveBoundary
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (i : ℤ)
    [HomologicalComplex.HasHomology X i]
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℤ).next i)]
    [Projective (boundaryModuleInt R X i)] :
    Nonempty ((cycleBoundaryShortComplexInt R X i).Splitting) := by
  -- The short exact sequence already exists, so projectivity of the boundary term gives a
  -- splitting by the standard `ShortComplex` criterion.
  letI : Projective (cycleBoundaryShortComplexInt R X i).X₃ := by
    change Projective (boundaryModuleInt R X i)
    infer_instance
  exact ⟨ShortComplex.ShortExact.splittingOfProjective
    (cycleBoundaryShortComplexInt_shortExact R X i)⟩

/-- Helper for Theorem 17.3.4: if the chain group `X.X i` is free over the domain `R`, then the
cycle object `X.cycles i` is torsion-free, because it injects into `X.X i`. -/
theorem cyclesInt_isTorsionFree_of_free
    (R : Type u) [CommRing R] [IsDomain R]
    (X : ChainComplex (ModuleCat R) ℤ) (i : ℤ)
    [HomologicalComplex.HasHomology X i] [Module.Free R (X.X i)] :
    Module.IsTorsionFree R (X.cycles i) := by
  let f : X.cycles i → X.X i := ModuleCat.Hom.hom (X.iCycles i)
  have hf : Function.Injective f := by
    -- The cycle inclusion is monic, so its underlying linear map is injective.
    exact (ModuleCat.mono_iff_injective _).mp (inferInstance : Mono (X.iCycles i))
  -- Pull torsion-freeness back along the cycle inclusion.
  exact hf.moduleIsTorsionFree f
    (fun r x ↦ (ModuleCat.Hom.hom (X.iCycles i)).map_smul r x)

/-- Helper for Theorem 17.3.4: if the degree-`i` chain group is finite and the degree-`i - 1`
chain group is free, then the boundary module `boundaryModuleInt R X i` is free over the PID `R`.
This isolates the remaining gap in Theorem 17.3.4 to the arbitrary-rank boundary-freeness step. -/
theorem boundaryModuleIntFreeOfPidOfFinite
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℤ) (i : ℤ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℤ).next i)]
    [Module.Finite R (X.X i)] [Module.Free R (X.X ((ComplexShape.down ℤ).next i))] :
    Module.Free R (boundaryModuleInt R X i) := by
  have hsurj : Function.Surjective (toBoundaryInt R X i) := toBoundaryInt_surjective R X i
  have _ : Module.Finite R (boundaryModuleInt R X i) := by
    -- The boundary module is the image of the finite degree-`i` chain group.
    exact Module.Finite.of_surjective (toBoundaryInt R X i).hom hsurj
  let f : boundaryModuleInt R X i → X.cycles ((ComplexShape.down ℤ).next i) :=
    ModuleCat.Hom.hom (boundaryInclusionInt R X i)
  have hf : Function.Injective f := by
    -- The boundary inclusion is the subtype map of a range, hence injective.
    exact (ModuleCat.mono_iff_injective _).mp (inferInstance : Mono (boundaryInclusionInt R X i))
  have _ : Module.IsTorsionFree R (X.cycles ((ComplexShape.down ℤ).next i)) := by
    -- First pull torsion-freeness from the ambient free chain group down to cycles.
    exact cyclesInt_isTorsionFree_of_free R X ((ComplexShape.down ℤ).next i)
  have _ : Module.IsTorsionFree R (boundaryModuleInt R X i) := by
    -- Then pull torsion-freeness from cycles down to the boundary range.
    exact hf.moduleIsTorsionFree f
      (fun r x ↦ (ModuleCat.Hom.hom (boundaryInclusionInt R X i)).map_smul r x)
  -- Over a PID, finite torsion-free modules are free.
  exact Module.free_of_finite_type_torsion_free'

/-- Helper for Theorem 17.3.4: if the degree-`i` chain group is free over the PID `R`, then the
cycle module `X.cycles i` is free as well. -/
theorem cyclesIntFreeOfPid
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℤ) (hX : ∀ i : ℤ, Module.Free R (X.X i)) (i : ℤ) :
    Module.Free R (X.cycles i) := by
  -- Transport cycles to the concrete kernel submodule of the differential and apply the
  -- arbitrary-rank PID submodule theorem there.
  letI : Module.Free R (X.X i) := hX i
  have hKernelFree :
      Module.Free R ((X.sc i).moduleCatLeftHomologyData.K) := by
    change Module.Free R
      (ModuleCat.of R (LinearMap.ker (ModuleCat.Hom.hom ((X.sc i).g))))
    simpa using
      (Submodule.freeOfPidOfFree (R := R)
        (M := X.X i)
        (S := LinearMap.ker (ModuleCat.Hom.hom ((X.sc i).g))))
  letI : Module.Free R ((X.sc i).moduleCatLeftHomologyData.K) := hKernelFree
  exact Module.Free.of_equiv ((X.sc i).moduleCatCyclesIso.symm.toLinearEquiv)

/-- Helper for Theorem 17.3.4: if the chain groups of `X` are free over the PID `R`, then the
boundary module `boundaryModuleInt R X i` is free. -/
theorem boundaryModuleIntFreeOfPid
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℤ) (hX : ∀ i : ℤ, Module.Free R (X.X i)) (i : ℤ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℤ).next i)] :
    Module.Free R (boundaryModuleInt R X i) := by
  -- First make the ambient cycle module free, then apply the same arbitrary-rank submodule
  -- theorem to the range that defines `boundaryModuleInt`.
  letI : Module.Free R (X.cycles ((ComplexShape.down ℤ).next i)) :=
    cyclesIntFreeOfPid R X hX ((ComplexShape.down ℤ).next i)
  simpa [boundaryModuleInt] using
    (Submodule.freeOfPidOfFree (R := R)
      (M := X.cycles ((ComplexShape.down ℤ).next i))
      (S := LinearMap.range
        (ModuleCat.Hom.hom (X.toCycles i ((ComplexShape.down ℤ).next i)))))

/-- Helper for Theorem 17.3.4: under the free/PID hypothesis on the chain groups, both the cycle
module `Z_i(X)` and the boundary module `B_(i - 1)(X)` are free. -/
theorem cycleAndBoundaryFreeOfPid
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℤ) (hX : ∀ i : ℤ, Module.Free R (X.X i)) (i : ℤ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℤ).next i)] :
    Module.Free R (X.cycles i) ∧
      Module.Free R (boundaryModuleInt R X i) := by
  -- Package the two freeness statements in the indexing convention used by the cycle-boundary
  -- short exact sequence.
  exact
    ⟨cyclesIntFreeOfPid R X hX i,
      boundaryModuleIntFreeOfPid R X hX i⟩

/-- Helper for Theorem 17.3.4: the boundary inclusion is killed by the quotient to homology. -/
@[reassoc, simp] theorem boundaryInclusionInt_comp_homologyπ
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (n : ℤ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℤ).next n)] :
    boundaryInclusionInt R X n ≫ X.homologyπ ((ComplexShape.down ℤ).next n) = 0 := by
  -- Boundaries represent the zero homology class, so the quotient map annihilates the boundary
  -- inclusion.
  ext y
  rcases y with ⟨y, ⟨x, hx⟩⟩
  change ModuleCat.Hom.hom (X.homologyπ ((ComplexShape.down ℤ).next n)) y = 0
  rw [← hx]
  have hzero :
      ModuleCat.Hom.hom
          (X.toCycles n ((ComplexShape.down ℤ).next n) ≫
            X.homologyπ ((ComplexShape.down ℤ).next n)) =
        ModuleCat.Hom.hom
          (0 : X.X n ⟶ X.homology ((ComplexShape.down ℤ).next n)) := by
    exact congrArg ModuleCat.Hom.hom
      (HomologicalComplex.toCycles_comp_homologyπ
        (K := X) (i := n) (j := (ComplexShape.down ℤ).next n))
  have hzeroEval :
      ModuleCat.Hom.hom
          (X.toCycles n ((ComplexShape.down ℤ).next n) ≫
            X.homologyπ ((ComplexShape.down ℤ).next n)) x =
        ModuleCat.Hom.hom
          (0 : X.X n ⟶ X.homology ((ComplexShape.down ℤ).next n)) x := by
    exact congrArg (fun f ↦ f x) hzero
  exact hzeroEval

/-- Helper for Theorem 17.3.4: the normalized left-hand short complex
`0 ⟶ B_(n - 1)(X) ⟶ Z_(n - 1)(X) ⟶ H_(n - 1)(X) ⟶ 0`. -/
def boundaryCyclesHomologyShortComplexInt
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (n : ℤ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℤ).next n)] :
    ShortComplex (ModuleCat R) :=
  ShortComplex.mk (boundaryInclusionInt R X n) (X.homologyπ ((ComplexShape.down ℤ).next n))
    (boundaryInclusionInt_comp_homologyπ R X n)

/-- Helper for Theorem 17.3.4: the normalized row
`B_(n - 1)(X) ⟶ Z_(n - 1)(X) ⟶ H_(n - 1)(X)` is exact on underlying modules. -/
private theorem boundaryInclusionInt_exact_homologyπ
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (n : ℤ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℤ).next n)] :
    Function.Exact
      (boundaryInclusionInt R X n)
      (X.homologyπ ((ComplexShape.down ℤ).next n)) := by
  let m : ℤ := (ComplexShape.down ℤ).next n
  let S := X.sc m
  intro z
  constructor
  · intro hz
    -- Move vanishing in homology to the concrete quotient model of `X.sc m`.
    have hzConcrete :
        ModuleCat.Hom.hom S.moduleCatLeftHomologyData.π
          (ModuleCat.Hom.hom S.moduleCatCyclesIso.hom z) = 0 := by
      have hzIso :
          ModuleCat.Hom.hom (X.homologyπ m ≫ S.moduleCatHomologyIso.hom) z = 0 := by
        change ModuleCat.Hom.hom S.moduleCatHomologyIso.hom
            (ModuleCat.Hom.hom (X.homologyπ m) z) = 0
        rw [hz]
        simpa using (LinearMap.map_zero (ModuleCat.Hom.hom S.moduleCatHomologyIso.hom))
      have hπEval :
          ModuleCat.Hom.hom (X.homologyπ m ≫ S.moduleCatHomologyIso.hom) z =
            ModuleCat.Hom.hom (S.moduleCatCyclesIso.hom ≫ S.moduleCatLeftHomologyData.π) z := by
        exact congrArg
          (fun f ↦ ModuleCat.Hom.hom f z)
          (by simpa [S] using
            (CategoryTheory.ShortComplex.π_moduleCatCyclesIso_hom (S := S)))
      rw [hπEval] at hzIso
      simpa using hzIso
    have hzRange :
        ModuleCat.Hom.hom S.moduleCatCyclesIso.hom z ∈ LinearMap.range S.moduleCatToCycles := by
      exact
        (Submodule.Quotient.mk_eq_zero
          (p := LinearMap.range S.moduleCatToCycles)
          (x := ModuleCat.Hom.hom S.moduleCatCyclesIso.hom z)).1 <| by
            simpa [S] using hzConcrete
    rcases hzRange with ⟨x, hx⟩
    have hCyclesIso_injective :
        Function.Injective (ModuleCat.Hom.hom S.moduleCatCyclesIso.hom) :=
      (ModuleCat.mono_iff_injective S.moduleCatCyclesIso.hom).1 inferInstance
    -- Transport the concrete range witness back to the normalized boundary owner.
    have htoCycles :
        ModuleCat.Hom.hom S.toCycles x = z := by
      apply hCyclesIso_injective
      change ModuleCat.Hom.hom (S.toCycles ≫ S.moduleCatCyclesIso.hom) x =
        ModuleCat.Hom.hom S.moduleCatCyclesIso.hom z
      rw [CategoryTheory.ShortComplex.toCycles_moduleCatCyclesIso_hom (S := S)]
      simpa using hx
    have hprev : (ComplexShape.down ℤ).prev m = n := by
      simpa [m]
    let x₀ : X.X ((ComplexShape.down ℤ).prev m) := x
    let x' : X.X n :=
      ModuleCat.Hom.hom (X.XIsoOfEq hprev).hom x₀
    have htoCycles' :
        ModuleCat.Hom.hom (X.toCycles n m) x' = z := by
      apply (ModuleCat.mono_iff_injective (X.iCycles m)).1 inferInstance
      have hleft :
          ModuleCat.Hom.hom (X.iCycles m)
              (ModuleCat.Hom.hom (X.toCycles n m) x') =
            ModuleCat.Hom.hom (X.d n m) x' := by
        change ModuleCat.Hom.hom (X.toCycles n m ≫ X.iCycles m) x' = _
        simpa using congrArg
          (fun f ↦ ModuleCat.Hom.hom f x')
          (HomologicalComplex.toCycles_i (K := X) (i := n) (j := m))
      have htransport :
          ModuleCat.Hom.hom (X.d n m) x' =
            ModuleCat.Hom.hom S.f x := by
        dsimp [x', x₀]
        change ModuleCat.Hom.hom ((X.XIsoOfEq hprev).hom ≫ X.d n m) _ =
          ModuleCat.Hom.hom S.f x
        rw [HomologicalComplex.XIsoOfEq_hom_comp_d (K := X) hprev m]
        rfl
      have hshort :
          ModuleCat.Hom.hom S.f x =
            ModuleCat.Hom.hom S.iCycles (ModuleCat.Hom.hom S.toCycles x) := by
        change ModuleCat.Hom.hom S.f x =
          ModuleCat.Hom.hom (S.toCycles ≫ S.iCycles) x
        simpa using
          (congrArg
            (fun f ↦ ModuleCat.Hom.hom f x)
            (CategoryTheory.ShortComplex.toCycles_i (S := S))).symm
      have hcycles :
          ModuleCat.Hom.hom S.iCycles (ModuleCat.Hom.hom S.toCycles x) =
            ModuleCat.Hom.hom S.iCycles z := by
        simpa using congrArg (ModuleCat.Hom.hom S.iCycles) htoCycles
      have hiCycles :
          ModuleCat.Hom.hom S.iCycles z =
            ModuleCat.Hom.hom (X.iCycles m) z := by
        rfl
      exact hleft.trans (htransport.trans (hshort.trans (hcycles.trans hiCycles)))
    have htoCyclesNext :
        ModuleCat.Hom.hom
            (X.toCycles n ((ComplexShape.down ℤ).next n)) x' = z := by
      simpa [m] using htoCycles'
    refine ⟨⟨z, ?_⟩, rfl⟩
    exact ⟨x', htoCyclesNext⟩
  · rintro ⟨y, rfl⟩
    -- Evaluating the short-complex zero relation shows every boundary class maps to zero.
    simpa [boundaryCyclesHomologyShortComplexInt] using
      (CategoryTheory.ShortComplex.moduleCat_zero_apply
        (S := boundaryCyclesHomologyShortComplexInt R X n)
        y)

/-- Helper for Theorem 17.3.4: the normalized boundary-cycles-homology sequence is short exact. -/
theorem boundaryCyclesHomologyShortExactInt
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (n : ℤ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℤ).next n)] :
    (boundaryCyclesHomologyShortComplexInt R X n).ShortExact := by
  -- Route correction: the UCT left term must use `B_(n - 1) → Z_(n - 1) → H_(n - 1)`, not the
  -- degree-`n - 1` cycle-boundary sequence whose quotient is `B_(n - 2)`.
  refine ModuleCat.shortComplex_shortExact
    (boundaryCyclesHomologyShortComplexInt R X n) ?_ ?_ ?_
  · simpa [boundaryCyclesHomologyShortComplexInt] using
      boundaryInclusionInt_exact_homologyπ R X n
  · simpa [boundaryCyclesHomologyShortComplexInt] using
      (ModuleCat.mono_iff_injective (boundaryInclusionInt R X n)).1 inferInstance
  · have hsurj :
        Function.Surjective (X.homologyπ ((ComplexShape.down ℤ).next n)) := by
      exact (ModuleCat.epi_iff_surjective
        (X.homologyπ ((ComplexShape.down ℤ).next n))).1 inferInstance
    simpa [boundaryCyclesHomologyShortComplexInt] using hsurj

/-- Helper for Theorem 17.3.4: the shared left-hand owner in the UCT argument is precomposition
by the boundary inclusion `B_(n - 1)(X) ⟶ Z_(n - 1)(X)` on coefficient-valued morphisms. -/
abbrev boundaryPrecompMap
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℤ).next n)] :
    ModuleCat.of R (X.cycles ((ComplexShape.down ℤ).next n) ⟶ M) ⟶
      ModuleCat.of R (boundaryModuleInt R X n ⟶ M) :=
  ModuleCat.ofHom (CategoryTheory.Linear.leftComp R M (boundaryInclusionInt R X n))

/-- Helper for Theorem 17.3.4: `boundaryPrecompMap` restricts a coefficient functional on
`Z_(n - 1)(X)` along the inclusion `B_(n - 1)(X) ⟶ Z_(n - 1)(X)`. -/
@[simp] theorem boundaryPrecompMap_apply
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℤ).next n)]
    (φ : X.cycles ((ComplexShape.down ℤ).next n) ⟶ M) :
    ModuleCat.Hom.hom (boundaryPrecompMap R X M n) φ =
      boundaryInclusionInt R X n ≫ φ := by
  -- Unfold the shared owner once so later cokernel transports can rewrite by `simp`.
  rfl

/-- Helper for Theorem 17.3.4: postcomposition by a coefficient morphism commutes with the shared
boundary precomposition map. -/
theorem boundaryPrecompMap_natural
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (n : ℤ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℤ).next n)]
    {M N : ModuleCat R} (f : M ⟶ N) :
    boundaryPrecompMap R X M n ≫
        ModuleCat.ofHom (CategoryTheory.Linear.rightComp R (boundaryModuleInt R X n) f) =
      ModuleCat.ofHom
          (CategoryTheory.Linear.rightComp R (X.cycles ((ComplexShape.down ℤ).next n)) f) ≫
        boundaryPrecompMap R X N n := by
  -- Both composites send `φ : Z_(n - 1)(X) ⟶ M` to `boundaryInclusionInt R X n ≫ φ ≫ f`.
  apply ModuleCat.hom_ext
  ext φ
  rfl

/-- Helper for Theorem 17.3.4: the naturality square for `boundaryPrecompMap` induces the
canonical morphism between the shared cokernel owners for coefficients `M` and `N`. -/
abbrev boundaryPrecompCokernelMap
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (n : ℤ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℤ).next n)]
    {M N : ModuleCat R} (f : M ⟶ N) :
    CategoryTheory.Limits.cokernel (boundaryPrecompMap R X M n) ⟶
      CategoryTheory.Limits.cokernel (boundaryPrecompMap R X N n) :=
  CategoryTheory.Limits.cokernel.map
    (boundaryPrecompMap R X M n)
    (boundaryPrecompMap R X N n)
    (ModuleCat.ofHom
      (CategoryTheory.Linear.rightComp R (X.cycles ((ComplexShape.down ℤ).next n)) f))
    (ModuleCat.ofHom (CategoryTheory.Linear.rightComp R (boundaryModuleInt R X n) f))
    (boundaryPrecompMap_natural R X n f)

/-- Helper for Theorem 17.3.4: the induced morphism on the shared cokernel owner is characterized
by the usual commuting square with the cokernel projections. -/
theorem boundaryPrecompCokernelMap_comm
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (n : ℤ)
    [HomologicalComplex.HasHomology X ((ComplexShape.down ℤ).next n)]
    {M N : ModuleCat R} (f : M ⟶ N) :
    CategoryTheory.Limits.cokernel.π (boundaryPrecompMap R X M n) ≫
        boundaryPrecompCokernelMap R X n f =
      ModuleCat.ofHom (CategoryTheory.Linear.rightComp R (boundaryModuleInt R X n) f) ≫
        CategoryTheory.Limits.cokernel.π (boundaryPrecompMap R X N n) := by
  have hzero :
      boundaryPrecompMap R X M n ≫
          ModuleCat.ofHom (CategoryTheory.Linear.rightComp R (boundaryModuleInt R X n) f) ≫
            CategoryTheory.Limits.cokernel.π (boundaryPrecompMap R X N n) = 0 := by
    -- First rewrite by the naturality square, then the target cokernel projection kills the
    -- remaining `boundaryPrecompMap`.
    calc
      boundaryPrecompMap R X M n ≫
          ModuleCat.ofHom (CategoryTheory.Linear.rightComp R (boundaryModuleInt R X n) f) ≫
            CategoryTheory.Limits.cokernel.π (boundaryPrecompMap R X N n) =
          (ModuleCat.ofHom
              (CategoryTheory.Linear.rightComp R
                (X.cycles ((ComplexShape.down ℤ).next n)) f) ≫
            boundaryPrecompMap R X N n) ≫
              CategoryTheory.Limits.cokernel.π (boundaryPrecompMap R X N n) := by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ k ≫ CategoryTheory.Limits.cokernel.π (boundaryPrecompMap R X N n))
            (boundaryPrecompMap_natural R X n f)
      _ = 0 := by
        calc
          ModuleCat.ofHom
              (CategoryTheory.Linear.rightComp R
                (X.cycles ((ComplexShape.down ℤ).next n)) f) ≫
              boundaryPrecompMap R X N n ≫
                CategoryTheory.Limits.cokernel.π (boundaryPrecompMap R X N n) =
            ModuleCat.ofHom
                (CategoryTheory.Linear.rightComp R
                  (X.cycles ((ComplexShape.down ℤ).next n)) f) ≫
              (boundaryPrecompMap R X N n ≫
                CategoryTheory.Limits.cokernel.π (boundaryPrecompMap R X N n)) := by
              rfl
          _ =
            ModuleCat.ofHom
                (CategoryTheory.Linear.rightComp R
                  (X.cycles ((ComplexShape.down ℤ).next n)) f) ≫ 0 := by
              exact
                congrArg
                  (fun k ↦
                    ModuleCat.ofHom
                        (CategoryTheory.Linear.rightComp R
                          (X.cycles ((ComplexShape.down ℤ).next n)) f) ≫
                      k)
                  (CategoryTheory.Limits.cokernel.condition (boundaryPrecompMap R X N n))
          _ = 0 := by
              simp
  -- Expand the induced cokernel map once, then read off its defining projection equation.
  change
    CategoryTheory.Limits.cokernel.π (boundaryPrecompMap R X M n) ≫
        CategoryTheory.Limits.cokernel.desc
          (boundaryPrecompMap R X M n)
          (ModuleCat.ofHom (CategoryTheory.Linear.rightComp R (boundaryModuleInt R X n) f) ≫
            CategoryTheory.Limits.cokernel.π (boundaryPrecompMap R X N n))
          hzero =
      ModuleCat.ofHom (CategoryTheory.Linear.rightComp R (boundaryModuleInt R X n) f) ≫
        CategoryTheory.Limits.cokernel.π (boundaryPrecompMap R X N n)
  exact CategoryTheory.Limits.cokernel.π_desc _ _ _

/-- A short exact sequence realizing the universal coefficient sequence for cohomology in degree
`n`. -/
structure UniversalCoefficientCohomologySequence
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) where
  extToCohomology :
    universalCoefficientExtTerm R X M n ⟶ universalCoefficientCohomologyTerm R X M n
  cohomologyToHom :
    universalCoefficientCohomologyTerm R X M n ⟶ universalCoefficientHomTerm R X M n
  zero : extToCohomology ≫ cohomologyToHom = 0
  shortExact : (ShortComplex.mk extToCohomology cohomologyToHom zero).ShortExact

namespace UniversalCoefficientCohomologySequence

/-- The underlying short complex of a universal coefficient cohomology sequence. -/
abbrev toShortComplex
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℤ} {M : ModuleCat R} {n : ℤ}
    (S : UniversalCoefficientCohomologySequence R X M n) :
    ShortComplex AddCommGrpCat :=
  ShortComplex.mk S.extToCohomology S.cohomologyToHom S.zero

/-- Coercion from a universal coefficient cohomology sequence to its underlying short complex. -/
instance instCoeOut
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℤ} {M : ModuleCat R} {n : ℤ} :
    CoeOut (UniversalCoefficientCohomologySequence R X M n) (ShortComplex AddCommGrpCat) where
  coe S := S.toShortComplex

end UniversalCoefficientCohomologySequence

/-- A universal coefficient cohomology sequence that is natural in the coefficient module `M`,
using the canonical coefficient-variable maps on the outer `Ext¹` and `Hom` terms. -/
structure UniversalCoefficientCohomologyNaturality
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (n : ℤ) where
  seq : ∀ M : ModuleCat R, UniversalCoefficientCohomologySequence R X M n
  comm₁₂ :
    ∀ {M N : ModuleCat R} (f : M ⟶ N),
      (universalCoefficientExtFunctor R X n).map f ≫ (seq N).extToCohomology =
        (seq M).extToCohomology ≫ universalCoefficientCohomologyCoefficientMap R X n f
  comm₂₃ :
    ∀ {M N : ModuleCat R} (f : M ⟶ N),
      universalCoefficientCohomologyCoefficientMap R X n f ≫ (seq N).cohomologyToHom =
        (seq M).cohomologyToHom ≫ (universalCoefficientHomFunctor R X n).map f

/-- Helper for Theorem 17.3.4: a pointwise family of short exact sequences together with the two
canonical coefficient-change squares packages into `UniversalCoefficientCohomologyNaturality`. -/
def mkUniversalCoefficientCohomologyNaturality
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℤ} {n : ℤ}
    (seq : ∀ M : ModuleCat R, UniversalCoefficientCohomologySequence R X M n)
    (comm₁₂ :
      ∀ {M N : ModuleCat R} (f : M ⟶ N),
        (universalCoefficientExtFunctor R X n).map f ≫ (seq N).extToCohomology =
          (seq M).extToCohomology ≫ universalCoefficientCohomologyCoefficientMap R X n f)
    (comm₂₃ :
      ∀ {M N : ModuleCat R} (f : M ⟶ N),
        universalCoefficientCohomologyCoefficientMap R X n f ≫ (seq N).cohomologyToHom =
          (seq M).cohomologyToHom ≫ (universalCoefficientHomFunctor R X n).map f) :
    UniversalCoefficientCohomologyNaturality R X n where
  -- This isolates the final assembly step so the main theorem only has to produce pointwise
  -- short exact sequences and the two naturality squares.
  seq := seq
  comm₁₂ := comm₁₂
  comm₂₃ := comm₂₃

namespace UniversalCoefficientCohomologyNaturality

/-- Coercion from a natural universal coefficient package to its family of short exact
sequences. -/
instance instCoeFun
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℤ} {n : ℤ} :
    CoeFun (UniversalCoefficientCohomologyNaturality R X n)
      (fun _ ↦ ∀ M : ModuleCat R, UniversalCoefficientCohomologySequence R X M n) where
  coe S := S.seq

/-- The middle morphism induced by a coefficient-module map in a universal coefficient package is
the canonical coefficient-change map on cohomology with coefficients. -/
abbrev cohomologyMap
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℤ} {n : ℤ}
    (S : UniversalCoefficientCohomologyNaturality R X n)
    {M N : ModuleCat R} (f : M ⟶ N) :
    universalCoefficientCohomologyTerm R X M n ⟶ universalCoefficientCohomologyTerm R X N n :=
  let _ := S
  universalCoefficientCohomologyCoefficientMap R X n f

/-- In a universal coefficient cohomology package, the coefficient-change map on the middle term
respects identities. -/
theorem map_id
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℤ} {n : ℤ}
    (S : UniversalCoefficientCohomologyNaturality R X n) (M : ModuleCat R) :
    S.cohomologyMap (𝟙 M) = 𝟙 (universalCoefficientCohomologyTerm R X M n) := by
  change universalCoefficientCohomologyCoefficientMap R X n (𝟙 M) =
    𝟙 (universalCoefficientCohomologyTerm R X M n)
  exact universalCoefficientCohomologyCoefficientMap_id R X n M

/-- In a universal coefficient cohomology package, the coefficient-change map on the middle term
respects composition. -/
theorem map_comp
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℤ} {n : ℤ}
    (S : UniversalCoefficientCohomologyNaturality R X n)
    {L M N : ModuleCat R} (f : L ⟶ M) (g : M ⟶ N) :
    S.cohomologyMap (f ≫ g) = S.cohomologyMap f ≫ S.cohomologyMap g := by
  change universalCoefficientCohomologyCoefficientMap R X n (f ≫ g) =
    universalCoefficientCohomologyCoefficientMap R X n f ≫
      universalCoefficientCohomologyCoefficientMap R X n g
  exact universalCoefficientCohomologyCoefficientMap_comp R X n f g

/-- The morphism of short complexes induced by a coefficient-module morphism. -/
def map
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℤ} {n : ℤ}
    (S : UniversalCoefficientCohomologyNaturality R X n)
    {M N : ModuleCat R} (f : M ⟶ N) :
    (S M).toShortComplex ⟶ (S N).toShortComplex :=
  ShortComplex.homMk
    ((universalCoefficientExtFunctor R X n).map f)
    (S.cohomologyMap f)
    ((universalCoefficientHomFunctor R X n).map f)
    (S.comm₁₂ f) (S.comm₂₃ f)

/-- Each short complex in a universal coefficient cohomology package is short exact. -/
theorem shortExact
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℤ} {n : ℤ}
    (S : UniversalCoefficientCohomologyNaturality R X n) (M : ModuleCat R) :
    ((S M).toShortComplex).ShortExact :=
  (S M).shortExact

end UniversalCoefficientCohomologyNaturality

/-- Helper for Theorem 17.3.4: once the pointwise short exact sequences and the two canonical
coefficient-change squares are constructed, the universal coefficient package exists. -/
theorem nonempty_universalCoefficientCohomologyNaturality_of_data
    {R : Type u} [CommRing R] {X : ChainComplex (ModuleCat R) ℤ} {n : ℤ}
    (seq : ∀ M : ModuleCat R, UniversalCoefficientCohomologySequence R X M n)
    (comm₁₂ :
      ∀ {M N : ModuleCat R} (f : M ⟶ N),
        (universalCoefficientExtFunctor R X n).map f ≫ (seq N).extToCohomology =
          (seq M).extToCohomology ≫ universalCoefficientCohomologyCoefficientMap R X n f)
    (comm₂₃ :
      ∀ {M N : ModuleCat R} (f : M ⟶ N),
        universalCoefficientCohomologyCoefficientMap R X n f ≫ (seq N).cohomologyToHom =
          (seq M).cohomologyToHom ≫ (universalCoefficientHomFunctor R X n).map f) :
    Nonempty (UniversalCoefficientCohomologyNaturality R X n) := by
  -- Package the pointwise data into the naturality structure, then witness nonemptiness.
  exact ⟨mkUniversalCoefficientCohomologyNaturality seq comm₁₂ comm₂₃⟩

/-- Helper for Theorem 17.3.4: once a pointwise family of cohomology sequences uses the canonical
right edge `cohomologyToHomMap`, the right naturality square is exactly
`cohomologyToHomMap_natural`. -/
private theorem fixedCoefficientCohomologyToHomNatural
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (n : ℤ)
    (seq : ∀ M : ModuleCat R, UniversalCoefficientCohomologySequence R X M n)
    (hcohomologyToHom :
      ∀ M : ModuleCat R, (seq M).cohomologyToHom = cohomologyToHomMap R X M n)
    {M N : ModuleCat R} (f : M ⟶ N) :
    universalCoefficientCohomologyCoefficientMap R X n f ≫ (seq N).cohomologyToHom =
      (seq M).cohomologyToHom ≫ (universalCoefficientHomFunctor R X n).map f := by
  -- Rewrite the stored right edges to the canonical Kronecker map, then use its proved
  -- coefficient naturality.
  rw [hcohomologyToHom N, hcohomologyToHom M]
  exact cohomologyToHomMap_natural R X n f

/-- Helper for Theorem 17.3.4: after installing the smallness instance needed for
`EnoughProjectives (ModuleCat R)`, the free cycle module `Z_(n - 1)(X)` is projective, so its
degree-one `Ext` term vanishes. -/
private theorem extOneCyclesIsZeroOfFree
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℤ) (n : ℤ)
    (hFree : Module.Free R (X.cycles (n - 1))) (M : ModuleCat R) :
    Limits.IsZero (((Ext R (ModuleCat R) 1).obj (Opposite.op (X.cycles (n - 1)))).obj M) := by
  -- Install `Small R` explicitly so `ModuleCat R` gets the `EnoughProjectives` owner used by
  -- `Ext`, then upgrade freeness of cycles to projectivity.
  letI : Small.{u} R := inferInstance
  letI : EnoughProjectives (ModuleCat R) := inferInstance
  letI : Module.Free R (X.cycles (n - 1)) := hFree
  letI : Projective (X.cycles (n - 1)) :=
    ModuleCat.projective_of_free (Module.Free.chooseBasis R (X.cycles (n - 1)))
  -- The standard projective-vanishing theorem now applies directly in degree one.
  simpa using
    (isZero_Ext_succ_of_projective (R := R) (C := ModuleCat R) (X.cycles (n - 1)) M 0)

/-- Helper for Theorem 17.3.4: the remaining fixed-coefficient data consists of constructing the
pointwise short exact sequences, the left `Ext¹ → H^n` naturality square, and the fact that the
right edge is the canonical `cohomologyToHomMap`. -/
private theorem fixedCoefficientUniversalCoefficientCohomologyData
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℤ) (n : ℤ)
    (hFree_n :
      Module.Free R (X.cycles n) ∧ Module.Free R (boundaryModuleInt R X n))
    (hFree_nMinusOne :
      Module.Free R (X.cycles (n - 1)) ∧ Module.Free R (boundaryModuleInt R X (n - 1)))
    (hSplit_n : Nonempty ((cycleBoundaryShortComplexInt R X n).Splitting))
    (hSplit_nMinusOne : Nonempty ((cycleBoundaryShortComplexInt R X (n - 1)).Splitting)) :
    ∃ seq : ∀ M : ModuleCat R, UniversalCoefficientCohomologySequence R X M n,
      (∀ {M N : ModuleCat R} (f : M ⟶ N),
        (universalCoefficientExtFunctor R X n).map f ≫ (seq N).extToCohomology =
          (seq M).extToCohomology ≫ universalCoefficientCohomologyCoefficientMap R X n f) ∧
      (∀ M : ModuleCat R, (seq M).cohomologyToHom = cohomologyToHomMap R X M n) := by
  have hExtCyclesZero :
      ∀ M : ModuleCat R,
        Limits.IsZero (((Ext R (ModuleCat R) 1).obj (Opposite.op (X.cycles (n - 1)))).obj M) := by
    -- This isolates the previously failing projective-vanishing step from the later cokernel
    -- transport work.
    intro M
    exact extOneCyclesIsZeroOfFree R X n hFree_nMinusOne.1 M
  -- TODO: package the two short-exact owners from the Agent C plan.
  -- 1. Use `hSplit_n` to build the cocycle row
  --    `0 ⟶ Hom(B_(n - 1)(X), M) ⟶ Z^n(Hom(X, M)) ⟶ Hom(H_n(X), M) ⟶ 0`.
  -- 2. Use `boundaryCyclesHomologyShortExactInt R X n`, `hFree_nMinusOne.1`, and
  --    `Ext.contravariant_sequence_exact₁'`/`Ext.contravariant_sequence_exact₃'` to identify the
  --    cokernel of `Hom(Z_(n - 1)(X), M) → Hom(B_(n - 1)(X), M)` with
  --    `universalCoefficientExtTerm R X M n`.
  -- 3. Normalize the coboundary through `hSplit_nMinusOne` so the cohomology quotient uses that
  --    same cokernel owner; `boundaryPrecompCokernelMap` now supplies the coefficient-change map
  --    on that shared owner, so the remaining work is the two owner identifications and their
  --    transport to `Ext` and cohomology.
  -- Route correction: the first failed execution of Step 2 hits a concrete Lean blocker before
  -- the mathematics starts: `Ext.contravariant_sequence_exact₁'`/`₃'` elaborate here only after
  -- the `HasExt`/`HasSmallLocalizedHom` owner and the `ModuleCat` universe are synchronized.
  sorry

/-- Theorem 17.3.4. If `X` is a chain complex of free `R`-modules over a PID `R`, then in each
degree `n` there exists a `UniversalCoefficientCohomologyNaturality R X n`, i.e. a natural family
of short exact sequences of abelian groups
`0 ⟶ universalCoefficientExtTerm R X M n ⟶ universalCoefficientCohomologyTerm R X M n ⟶
universalCoefficientHomTerm R X M n ⟶ 0` in the coefficient module `M`. -/
theorem universalCoefficientCohomologyShortExact
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℤ) (n : ℤ)
    (hX : ∀ i : ℤ, Module.Free R (X.X i)) :
    Nonempty (UniversalCoefficientCohomologyNaturality R X n) := by
  -- Route correction: the packaging layer is already available in this file, so the remaining
  -- work is to construct the pointwise short exact sequences together with the two canonical
  -- coefficient-change squares.
  have hFree_n :
      Module.Free R (X.cycles n) ∧ Module.Free R (boundaryModuleInt R X n) := by
    simpa using cycleAndBoundaryFreeOfPid R X hX n
  have hFree_nMinusOne :
      Module.Free R (X.cycles (n - 1)) ∧ Module.Free R (boundaryModuleInt R X (n - 1)) := by
    simpa using cycleAndBoundaryFreeOfPid R X hX (n - 1)
  have hSplit_n : Nonempty ((cycleBoundaryShortComplexInt R X n).Splitting) := by
    -- Route correction: package the projective-boundary splitting once and reuse it here.
    letI : Module.Free R (boundaryModuleInt R X n) := hFree_n.2
    letI : Projective (boundaryModuleInt R X n) :=
      ModuleCat.projective_of_free (Module.Free.chooseBasis R (boundaryModuleInt R X n))
    exact cycleBoundaryShortComplexInt_splitting_of_projectiveBoundary R X n
  have hSplit_nMinusOne : Nonempty ((cycleBoundaryShortComplexInt R X (n - 1)).Splitting) := by
    -- The same packaged splitting applies one degree lower for the later `Ext` computation.
    letI : Module.Free R (boundaryModuleInt R X (n - 1)) := hFree_nMinusOne.2
    letI : Projective (boundaryModuleInt R X (n - 1)) :=
      ModuleCat.projective_of_free
        (Module.Free.chooseBasis R (boundaryModuleInt R X (n - 1)))
    exact cycleBoundaryShortComplexInt_splitting_of_projectiveBoundary R X (n - 1)
  rcases fixedCoefficientUniversalCoefficientCohomologyData
      R X n hFree_n hFree_nMinusOne hSplit_n hSplit_nMinusOne with
    ⟨seq, comm₁₂, hcohomologyToHom⟩
  -- Assemble the normalized pointwise data into the target natural family.
  refine nonempty_universalCoefficientCohomologyNaturality_of_data seq comm₁₂ ?_
  intro M N f
  -- The remaining right square is exactly the canonical naturality of `cohomologyToHomMap`.
  exact fixedCoefficientCohomologyToHomNatural R X n seq hcohomologyToHom f
