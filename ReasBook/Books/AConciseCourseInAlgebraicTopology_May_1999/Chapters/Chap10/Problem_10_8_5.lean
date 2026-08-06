import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Homology.EulerCharacteristic
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvarianceTopCat
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Problem_10_8_5.WholeSpaceCountingComplex
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.CWEulerCharacteristic

open AlgebraicTopology CategoryTheory Topology
open scoped BigOperators ContinuousMap

universe u v w

noncomputable section

-- Semantic recall: `ContinuousMap.HomotopyEquiv.refl` is the canonical identity homotopy
-- equivalence, and no dedicated Euler-characteristic invariance API for finite CW complexes was
-- found in the local environment.

open scoped Topology.CWComplex

/-- If all cells of `C` above dimension `N - 1` are empty, then the CW Euler characteristic is
the alternating sum of the cell counts in dimensions `< N`. -/
theorem cwEulerCharacteristic_eq_sum_range_of_isEmpty_cell {X : Type u} [TopologicalSpace X]
    {C : Set X} [CWComplex C] [CWComplex.Finite C] {N : ℕ}
    (hN : ∀ n ≥ N, IsEmpty (Topology.CWComplex.cell C n)) :
    χ(C) =
      Finset.sum (Finset.range N) fun n ↦
        (Int.negOnePow n : ℤ) * Nat.card (Topology.CWComplex.cell C n) := by
  let f : ℕ → ℤ := fun n ↦
    (Int.negOnePow n : ℤ) * Nat.card (Topology.CWComplex.cell C n)
  have hsupport : Function.support f ⊆ Set.Iio N := by
    intro n hn
    by_contra hlt
    have hempty : IsEmpty (Topology.CWComplex.cell C n) := hN n (le_of_not_gt hlt)
    exact hn (by simp [f])
  have hf : Function.HasFiniteSupport f :=
    (Set.finite_lt_nat N).subset hsupport
  rw [cwEulerCharacteristic_def, finsum_eq_sum f hf]
  refine Finset.sum_subset ?_ ?_
  · intro n hn
    exact Finset.mem_range.2 (hsupport (hf.mem_toFinset.1 hn))
  · intro n _ hn
    by_cases hmem : n ∈ Function.support f
    · exact False.elim (hn (hf.mem_toFinset.2 hmem))
    · simpa [Function.mem_support, f] using hmem

theorem cwEulerCharacteristic_eq_sum_range {X : Type u} [TopologicalSpace X] {C : Set X}
    [CWComplex C] [CWComplex.Finite C] :
    ∃ N : ℕ, χ(C) =
      Finset.sum (Finset.range N) fun n ↦
        (Int.negOnePow n : ℤ) * Nat.card (Topology.CWComplex.cell C n) := by
  have hfinite : ∀ᶠ n in Filter.atTop, IsEmpty (Topology.CWComplex.cell C n) :=
    (inferInstance : CWComplex.Finite C).eventually_isEmpty_cell
  simp_rw [Filter.eventually_atTop, ge_iff_le] at hfinite
  rcases hfinite with ⟨N, hN⟩
  exact ⟨N, cwEulerCharacteristic_eq_sum_range_of_isEmpty_cell hN⟩

/-- Helper for Problem 10.8.5: the singular chain complex of `X` with coefficients in the field
`k`. -/
abbrev fieldTopologicalSingularChains (k : Type w) [Field k] (X : TopCat.{u}) :
    ChainComplex (ModuleCat.{max u w} k) ℕ :=
  ((singularChainComplexFunctor.{u} (ModuleCat.{max u w} k)).obj
      (ModuleCat.of k (ULift.{u} k))).obj X

/-- Helper for Problem 10.8.5: the Euler characteristic of singular homology with coefficients in
the field `k`. -/
abbrev fieldTopologicalSingularHomologyEulerChar (k : Type w) [Field k] (X : TopCat.{u}) : ℤ :=
  HomologicalComplex.homologyEulerChar (fieldTopologicalSingularChains k X)

/-- Helper for Problem 10.8.5: a homotopy equivalence of spaces induces a chain-homotopy
equivalence on their singular chain complexes with coefficients in `k`. -/
noncomputable def singularChainHomotopyEquivOfHomotopyEquiv
    {X : Type u} {Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (k : Type w) [Field k] (h : X ≃ₕ Y) :
    HomotopyEquiv
      (fieldTopologicalSingularChains k (TopCat.of X))
      (fieldTopologicalSingularChains k (TopCat.of Y)) := by
  let F : TopCat.{u} ⥤ ChainComplex (ModuleCat.{max u w} k) ℕ :=
    ((singularChainComplexFunctor.{u} (ModuleCat.{max u w} k)).obj
      (ModuleCat.of k (ULift.{u} k)))
  classical
  let hLeft := Classical.choice h.left_inv
  let hRight := Classical.choice h.right_inv
  -- Lift the topological homotopies exhibiting `h` as an equivalence to chain homotopies.
  refine
    { hom := F.map (TopCat.ofHom h.toFun)
      inv := F.map (TopCat.ofHom h.invFun)
      homotopyHomInvId := by
        -- The left inverse homotopy controls the composition on the `X` side.
        simpa [F, Functor.map_comp] using
          TopCat.Homotopy.singularChainComplexFunctorObjMap (C := ModuleCat.{max u w} k)
            (f := TopCat.ofHom (h.invFun.comp h.toFun))
            (g := 𝟙 (TopCat.of X))
            hLeft
            (R := ModuleCat.of k (ULift.{u} k))
      homotopyInvHomId := by
        -- The right inverse homotopy controls the composition on the `Y` side.
        simpa [F, Functor.map_comp] using
          TopCat.Homotopy.singularChainComplexFunctorObjMap (C := ModuleCat.{max u w} k)
            (f := TopCat.ofHom (h.toFun.comp h.invFun))
            (g := 𝟙 (TopCat.of Y))
            hRight
            (R := ModuleCat.of k (ULift.{u} k)) }

/-- Helper for Problem 10.8.5: a homotopy equivalence induces an isomorphism on each singular
homology group with coefficients in `k`. -/
noncomputable def singularHomologyIsoOfHomotopyEquiv
    {X : Type u} {Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (k : Type w) [Field k] (h : X ≃ₕ Y) (n : ℕ) :
    (fieldTopologicalSingularChains k (TopCat.of X)).homology n ≅
      (fieldTopologicalSingularChains k (TopCat.of Y)).homology n :=
  -- Pass from the chain-homotopy equivalence to the induced homology isomorphism in degree `n`.
  (singularChainHomotopyEquivOfHomotopyEquiv k h).toHomologyIso n

/-- Helper for Problem 10.8.5: singular-homology Euler characteristic with field coefficients is
preserved by homotopy equivalence. -/
theorem singularHomologyEulerChar_eq_of_homotopyEquiv
    {X : Type u} {Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (k : Type w) [Field k] (h : X ≃ₕ Y) :
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of X) =
      fieldTopologicalSingularHomologyEulerChar k (TopCat.of Y) := by
  have hFinrank :
      (fun n ↦
        Module.finrank k ((fieldTopologicalSingularChains k (TopCat.of X)).homology n)) =
        fun n ↦ Module.finrank k ((fieldTopologicalSingularChains k (TopCat.of Y)).homology n) :=
    by
      funext n
      -- Compare the singular homology groups degreewise through the induced linear equivalence.
      simpa using
        LinearEquiv.finrank_eq
          (singularHomologyIsoOfHomotopyEquiv (k := k) h n).toLinearEquiv
  -- Unfold the homological Euler characteristic and rewrite the `finsum` summands pointwise.
  simpa [fieldTopologicalSingularHomologyEulerChar, HomologicalComplex.homologyEulerChar] using
    congrArg
      (fun f : ℕ → ℕ ↦
        ∑ᶠ n : ℕ, (((ComplexShape.down ℕ).χ n : ℤ) * f n))
      hFinrank

/-- Helper for Problem 10.8.5: a same-universe `ULift` copy of `X` has the same
singular-homology Euler characteristic as `X`. -/
theorem fieldTopologicalSingularHomologyEulerChar_eq_sameLevelUlift
    {X : Type u} [TopologicalSpace X] (k : Type w) [Field k] :
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of X) =
      fieldTopologicalSingularHomologyEulerChar k (TopCat.of (ULift.{u} X)) := by
  -- The lift `ULift.{u} X` stays in the same universe, so the basic homotopy-invariance theorem
  -- applies directly to the canonical homeomorphism.
  exact singularHomologyEulerChar_eq_of_homotopyEquiv (X := X) (Y := ULift.{u} X) (k := k)
    ((Homeomorph.ulift.symm : X ≃ₜ ULift.{u} X).toHomotopyEquiv)

/-- Helper for Problem 10.8.5: lifting a field-valued chain complex through
`ModuleCat.uliftFunctor` does not change its homological Euler characteristic. -/
theorem homologyEulerChar_eq_of_moduleUlift
    (k : Type w) [Field k] (C : ChainComplex (ModuleCat.{max u w} k) ℕ) :
    HomologicalComplex.homologyEulerChar C =
      HomologicalComplex.homologyEulerChar
        (((ModuleCat.uliftFunctor.{v, max u w} k).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj C) := by
  let F := ModuleCat.uliftFunctor.{v, max u w} k
  let C' := ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C)
  have hFinrank :
      (fun n ↦ Module.finrank k (C.homology n)) =
        fun n ↦ Module.finrank k (C'.homology n) := by
    funext n
    let hMappedHomology :
        C'.homology n ≅ F.obj (C.homology n) :=
      -- Compare the homology of the lifted complex with the lifted homology module degreewise.
      (HomologicalComplex.homologyFunctorIso
          (ModuleCat.{max (max u w) v} k) (ComplexShape.down ℕ) n).app C' ≪≫
        (CategoryTheory.ShortComplex.homologyFunctorIso F).app (C.sc n) ≪≫
        F.mapIso
          ((HomologicalComplex.homologyFunctorIso
            (ModuleCat.{max u w} k) (ComplexShape.down ℕ) n).app C).symm
    have hLiftedFinrank :
        Module.finrank k (C'.homology n) = Module.finrank k (C.homology n) := by
      -- The intermediate module is just a universe lift of `C.homology n`, so finrank is stable.
      simpa [F, hMappedHomology] using
        LinearEquiv.finrank_eq (hMappedHomology.toLinearEquiv.trans ULift.moduleEquiv)
    simpa using hLiftedFinrank.symm
  -- Unfold both Euler characteristics and rewrite the `finsum` summands degreewise.
  simpa [HomologicalComplex.homologyEulerChar] using
    congrArg
      (fun f : ℕ → ℕ ↦
        ∑ᶠ n : ℕ, (((ComplexShape.down ℕ).χ n : ℤ) * f n))
      hFinrank

/-- Helper for Problem 10.8.5: isomorphic chain complexes have the same homological Euler
characteristic over a field. -/
theorem homologyEulerChar_eq_of_iso
    (k : Type w) [Field k] {C D : ChainComplex (ModuleCat.{u} k) ℕ} (e : C ≅ D) :
    HomologicalComplex.homologyEulerChar C = HomologicalComplex.homologyEulerChar D := by
  have hFinrank :
      (fun n ↦ Module.finrank k (C.homology n)) =
        fun n ↦ Module.finrank k (D.homology n) := by
    funext n
    -- Compare each homology group through the isomorphism induced by the chain-complex iso.
    simpa using
      LinearEquiv.finrank_eq
        (((HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) n).mapIso
          e).toLinearEquiv)
  -- Unfold the Euler characteristic and rewrite the degreewise homology ranks.
  simpa [HomologicalComplex.homologyEulerChar] using
    congrArg
      (fun f : ℕ → ℕ ↦
        ∑ᶠ n : ℕ, (((ComplexShape.down ℕ).χ n : ℤ) * f n))
      hFinrank

/-- Helper for Problem 10.8.5: singular chains on `X` computed in the common owner obtained by
lifting the space to `ULift.{v} X`. -/
abbrev fieldTopologicalSingularChainsCommonLevel
    {X : Type u} [TopologicalSpace X] (k : Type w) [Field k] :
    ChainComplex (ModuleCat.{max (max u w) v} k) ℕ :=
  ((singularChainComplexFunctor.{max u v} (ModuleCat.{max (max u w) v} k)).obj
      (ModuleCat.of k (ULift.{max u v} k))).obj (TopCat.of (ULift.{v} X))

/-- Helper for Problem 10.8.5: the common-level singular chains are unchanged when the original
space is first replaced by the equivalent `ULift.{u}` copy. -/
noncomputable abbrev fieldTopologicalSingularChainsCommonLevelIso_of_uliftLevelHomeomorph
    {X : Type u} [TopologicalSpace X] (k : Type w) [Field k] :
    fieldTopologicalSingularChainsCommonLevel k (X := X) ≅
      fieldTopologicalSingularChainsCommonLevel k (X := ULift.{u} X) :=
  let F : TopCat.{max u v} ⥤ ChainComplex (ModuleCat.{max (max u w) v} k) ℕ :=
    ((singularChainComplexFunctor.{max u v} (ModuleCat.{max (max u w) v} k)).obj
      (ModuleCat.of k (ULift.{max u v} k)))
  let hHomeo : TopCat.of (ULift.{v} X) ≅ TopCat.of (ULift.{v} (ULift.{u} X)) :=
    TopCat.isoOfHomeo <|
      (Homeomorph.ulift : ULift.{v} X ≃ₜ X).trans
      ((Homeomorph.ulift.symm : X ≃ₜ ULift.{u} X).trans
        (Homeomorph.ulift.symm : ULift.{u} X ≃ₜ ULift.{v} (ULift.{u} X)))
  F.mapIso hHomeo

/-- Helper for Problem 10.8.5: after lifting both spaces to a common universe, singular-homology
Euler characteristic with field coefficients is still preserved by homotopy equivalence. -/
theorem singularHomologyEulerChar_eq_of_homotopyEquivOnULifts
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (k : Type w) [Field k] (h : X ≃ₕ Y) :
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of (ULift.{v} X)) =
      fieldTopologicalSingularHomologyEulerChar k (TopCat.of (ULift.{u} Y)) := by
  let hLift : ULift.{v} X ≃ₕ ULift.{u} Y :=
    ((Homeomorph.ulift : ULift.{v} X ≃ₜ X).toHomotopyEquiv).trans
      (h.trans (Homeomorph.ulift.symm : Y ≃ₜ ULift.{u} Y).toHomotopyEquiv)
  -- Lift `h` into a common universe so the same-universe singular-homology invariant applies.
  simpa [hLift] using singularHomologyEulerChar_eq_of_homotopyEquiv (k := k) hLift

/-- Helper for Problem 10.8.5: the coefficient object `ULift.{max u v} k` used by the common-level
singular chains is canonically isomorphic to the `ModuleCat.uliftFunctor` image of
`ULift.{u} k`. -/
noncomputable def fieldSingularCoefficientUliftIso
    (k : Type w) [Field k] :
    ModuleCat.of k (ULift.{max u v} k) ≅
      (ModuleCat.uliftFunctor.{v, max u w} k).obj (ModuleCat.of k (ULift.{u} k)) :=
  -- Compose the two evident `ULift.moduleEquiv` maps down to `k`, then lift back to the
  -- common coefficient owner.
  (ULift.moduleEquiv.trans (ULift.moduleEquiv.trans ULift.moduleEquiv.symm)).toModuleIso.symm

/-- Helper for Problem 10.8.5: `TopCat.toSSet` turns `TopCat.uliftFunctor` on spaces into the
corresponding simplicial `ULift` functor. -/
noncomputable def topCatToSSetUliftFunctorIso (Y : TopCat.{u}) :
    TopCat.toSSet.obj (TopCat.uliftFunctor.{v}.obj Y) ≅
      SSet.uliftFunctor.{v}.obj (TopCat.toSSet.obj Y) := by
  refine NatIso.ofComponents (fun n ↦ ?_) ?_
  · -- Compare `n`-simplices through the homeomorphism identifying `Y` with its lifted copy.
    refine Equiv.toIso <|
      (TopCat.toSSetObjEquiv (TopCat.uliftFunctor.{v}.obj Y) n).trans
        ((Homeomorph.continuousMapCongr (Homeomorph.refl _)
            (TopCat.uliftFunctorObjHomeo Y).symm).trans
          ((TopCat.toSSetObjEquiv Y n).symm.trans Equiv.ulift.symm))
  · -- The codomain homeomorphism commutes with precomposition along simplex maps.
    intro n m f
    ext x
    rfl

/-- Helper for Problem 10.8.5: after lifting the source coproduct to the larger module universe,
its concrete `Finsupp` model is the `Finsupp` model on the lifted index and lifted coefficients. -/
noncomputable def sigmaConstUliftFinsuppIso
    (k : Type w) [Field k] (α : Type u) :
    (ModuleCat.uliftFunctor.{v, max u w} k).obj (ModuleCat.of k (α →₀ ULift.{u} k)) ≅
      ModuleCat.of k (ULift.{v} α →₀ ULift.{v} (ULift.{u} k)) :=
  ((ULift.moduleEquiv :
      ULift.{v} (α →₀ ULift.{u} k) ≃ₗ[k] (α →₀ ULift.{u} k)).trans
    (Finsupp.lcongr ((Equiv.ulift : ULift.{v} α ≃ α).symm)
      (ULift.moduleEquiv.symm :
        ULift.{u} k ≃ₗ[k] ULift.{v} (ULift.{u} k)))).toModuleIso

/-- Helper for Problem 10.8.5: the lifted concrete coproduct injections are transported by the
`Finsupp` bridge to the concrete injections on the lifted index type. -/
@[simp] theorem sigmaConstUliftFinsuppIso_toLinearEquiv
    (k : Type w) [Field k] (α : Type u) :
    (sigmaConstUliftFinsuppIso (k := k) α).toLinearEquiv =
      (ULift.moduleEquiv :
          ULift.{v} (α →₀ ULift.{u} k) ≃ₗ[k] (α →₀ ULift.{u} k)).trans
        (Finsupp.lcongr ((Equiv.ulift : ULift.{v} α ≃ α).symm)
          (ULift.moduleEquiv.symm :
            ULift.{u} k ≃ₗ[k] ULift.{v} (ULift.{u} k))) := by
  -- This companion theorem records the exact concrete linear equivalence used by the bundled iso.
  rfl

/-- Helper for Problem 10.8.5: the constant `ModuleCat` coproduct has a concrete `Finsupp`
presentation even when the index and coefficient module live in different universes. -/
noncomputable def moduleCatConstantCoproductCofan
    (R : Type w) [CommRing R] (ι : Type u) (M : Type (max u v))
    [AddCommGroup M] [Module R M] :
    Limits.Cofan fun _ : ι ↦ (ModuleCat.of R M : ModuleCat.{max u v} R) :=
  Limits.Cofan.mk (ModuleCat.of R (ι →₀ M) : ModuleCat.{max u v} R) fun i ↦
    ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := M))

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Problem 10.8.5: the concrete `Finsupp` cofan is colimiting for a constant
`ModuleCat` diagram. -/
noncomputable def moduleCatConstantCoproductIsColimit
    (R : Type w) [CommRing R] (ι : Type u) (M : Type (max u v))
    [AddCommGroup M] [Module R M] :
    Limits.IsColimit (moduleCatConstantCoproductCofan (R := R) ι M) where
  desc s := ModuleCat.ofHom <| Finsupp.lsum R (N := s.pt) (fun i ↦ (s.ι.app ⟨i⟩).hom)
  fac s j := by
    -- Each coproduct injection picks out exactly one summand of the `Finsupp` sum.
    ext x
    simp [moduleCatConstantCoproductCofan]
  uniq s f h := by
    -- Two maps out of a `Finsupp` module agree once they agree on every basis vector.
    ext : 1
    apply Finsupp.lhom_ext'
    intro i
    ext x
    have hi := congrArg ModuleCat.Hom.hom (h ⟨i⟩)
    simpa [moduleCatConstantCoproductCofan] using LinearMap.congr_fun hi x

/-- Helper for Problem 10.8.5: a categorical constant coproduct in `ModuleCat` is canonically
identified with its concrete `Finsupp` owner. -/
noncomputable def moduleCatConstantCoproductIso
    (R : Type w) [CommRing R] (ι : Type u) (M : Type (max u v))
    [AddCommGroup M] [Module R M] :
    (∐ fun _ : ι ↦ (ModuleCat.of R M : ModuleCat.{max u v} R)) ≅
      ModuleCat.of R (ι →₀ M) :=
  Limits.IsColimit.coconePointUniqueUpToIso
    (Limits.coproductIsCoproduct (fun _ : ι ↦ (ModuleCat.of R M : ModuleCat.{max u v} R)))
    (moduleCatConstantCoproductIsColimit (R := R) ι M)

/-- Helper for Problem 10.8.5: under the concrete coproduct identification, the categorical
injection is the usual `Finsupp.lsingle` map. -/
@[simp] theorem sigma_ι_comp_moduleCatConstantCoproductIso_hom
    (R : Type w) [CommRing R] (ι : Type u) (M : Type (max u v))
    [AddCommGroup M] [Module R M] (i : ι) :
    Limits.Sigma.ι (fun _ : ι ↦ (ModuleCat.of R M : ModuleCat.{max u v} R)) i ≫
      (moduleCatConstantCoproductIso (R := R) ι M).hom =
        ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := M)) := by
  -- This is the coproduct comparison map on the universal injections.
  simpa [moduleCatConstantCoproductIso, moduleCatConstantCoproductCofan] using
    Limits.IsColimit.comp_coconePointUniqueUpToIso_hom
      (Limits.coproductIsCoproduct (fun _ : ι ↦ (ModuleCat.of R M : ModuleCat.{max u v} R)))
      (moduleCatConstantCoproductIsColimit (R := R) ι M) ⟨i⟩

/-- Helper for Problem 10.8.5: after passing a categorical constant coproduct to its concrete
`Finsupp` owner, `Sigma.map'` becomes `Finsupp.lmapDomain`. -/
@[simp] theorem sigmaMap_comp_moduleCatConstantCoproductIso_hom
    (R : Type w) [CommRing R] {α β : Type u} (M : Type (max u v))
    [AddCommGroup M] [Module R M] (g : α → β) :
    Limits.Sigma.map' g (fun _ ↦ 𝟙 (ModuleCat.of R M : ModuleCat.{max u v} R)) ≫
      (moduleCatConstantCoproductIso (R := R) β M).hom =
        (moduleCatConstantCoproductIso (R := R) α M).hom ≫
          ModuleCat.ofHom (Finsupp.lmapDomain M R g) := by
  -- The forward naturality check reduces to comparing the coproduct injections on each summand.
  refine Limits.Sigma.hom_ext _ _ fun i ↦ ?_
  calc
    Limits.Sigma.ι (fun _ : α ↦ (ModuleCat.of R M : ModuleCat.{max u v} R)) i ≫
        (Limits.Sigma.map' g (fun _ ↦ 𝟙 (ModuleCat.of R M : ModuleCat.{max u v} R)) ≫
          (moduleCatConstantCoproductIso (R := R) β M).hom) =
      ModuleCat.ofHom (Finsupp.lsingle (g i) (R := R) (M := M)) := by
        simp
    _ = ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := M)) ≫
          ModuleCat.ofHom (Finsupp.lmapDomain M R g) := by
        ext x j
        simp [Finsupp.lmapDomain]
    _ = Limits.Sigma.ι (fun _ : α ↦ (ModuleCat.of R M : ModuleCat.{max u v} R)) i ≫
          ((moduleCatConstantCoproductIso (R := R) α M).hom ≫
            ModuleCat.ofHom (Finsupp.lmapDomain M R g)) := by
        simpa [Category.assoc] using
          congrArg
            (fun f ↦ f ≫ ModuleCat.ofHom (Finsupp.lmapDomain M R g))
            (sigma_ι_comp_moduleCatConstantCoproductIso_hom (R := R) α M i).symm

/-- Helper for Problem 10.8.5: the inverse and forward concrete coproduct identifications turn
the categorical map `Sigma.map'` into `Finsupp.lmapDomain`. -/
@[simp] theorem moduleCatConstantCoproductIso_inv_sigmaMap_hom
    (R : Type w) [CommRing R] {α β : Type u} (M : Type (max u v))
    [AddCommGroup M] [Module R M] (g : α → β) :
    (moduleCatConstantCoproductIso (R := R) α M).inv ≫
        Limits.Sigma.map' g (fun _ ↦ 𝟙 (ModuleCat.of R M : ModuleCat.{max u v} R)) ≫
      (moduleCatConstantCoproductIso (R := R) β M).hom =
        ModuleCat.ofHom (Finsupp.lmapDomain M R g) := by
  -- Cancel the source coproduct comparison iso and reuse the forward naturality theorem.
  apply (cancel_epi (moduleCatConstantCoproductIso (R := R) α M).hom).1
  simpa [Category.assoc] using
    sigmaMap_comp_moduleCatConstantCoproductIso_hom (R := R) (M := M) g

/-- Helper for Problem 10.8.5: degreewise, lifting the coefficient module through
`ModuleCat.uliftFunctor` commutes with the `sigmaConst` coproduct after reindexing the simplex
set along `Equiv.ulift`. -/
noncomputable def sigmaConstUliftCoproductIso
    (k : Type w) [Field k] (α : Type u) :
    (ModuleCat.uliftFunctor.{v, max u w} k).obj
        (∐ fun _ : α ↦ ModuleCat.of k (ULift.{u} k)) ≅
      ∐ fun _ : ULift.{v} α ↦
        (ModuleCat.uliftFunctor.{v, max u w} k).obj (ModuleCat.of k (ULift.{u} k)) :=
  -- Route correction: normalize both categorical coproducts to concrete `Finsupp` owners, apply
  -- the explicit `ULift`/`Finsupp` bridge in the middle, then move back to the target coproduct.
  (ModuleCat.uliftFunctor.{v, max u w} k).mapIso
      (moduleCatConstantCoproductIso (R := k) α (ULift.{u} k)) ≪≫
    sigmaConstUliftFinsuppIso (k := k) α ≪≫
      (moduleCatConstantCoproductIso (R := k) (ULift.{v} α) (ULift.{v} (ULift.{u} k))).symm

/-- Helper for Problem 10.8.5: on a concrete finitely supported function, the middle `ULift`
bridge carries `mapDomain g` to `mapDomain (uliftFunctor.map g)`. -/
theorem sigmaConstUliftFinsuppIsoNaturalityApply
    (k : Type w) [Field k] {α β : Type u} (g : α → β) (x : α →₀ ULift.{u} k) :
    (sigmaConstUliftFinsuppIso (k := k) β).hom.hom ⟨Finsupp.mapDomain g x⟩ =
      Finsupp.mapDomain (CategoryTheory.uliftFunctor.{v, u}.map g)
        ((sigmaConstUliftFinsuppIso (k := k) α).hom.hom ⟨x⟩) := by
  -- Reduce the comparison to `Finsupp` basis vectors, where `mapDomain_single` and
  -- `lcongr_single` compute both sides explicitly.
  let eα :
      ULift.{v} (α →₀ ULift.{u} k) ≃ₗ[k] ULift.{v} α →₀ ULift.{v} (ULift.{u} k) :=
    (ULift.moduleEquiv :
        ULift.{v} (α →₀ ULift.{u} k) ≃ₗ[k] (α →₀ ULift.{u} k)).trans
      (Finsupp.lcongr ((Equiv.ulift : ULift.{v} α ≃ α).symm)
        (ULift.moduleEquiv.symm :
          ULift.{u} k ≃ₗ[k] ULift.{v} (ULift.{u} k)))
  let eβ :
      ULift.{v} (β →₀ ULift.{u} k) ≃ₗ[k] ULift.{v} β →₀ ULift.{v} (ULift.{u} k) :=
    (ULift.moduleEquiv :
        ULift.{v} (β →₀ ULift.{u} k) ≃ₗ[k] (β →₀ ULift.{u} k)).trans
      (Finsupp.lcongr ((Equiv.ulift : ULift.{v} β ≃ β).symm)
        (ULift.moduleEquiv.symm :
          ULift.{u} k ≃ₗ[k] ULift.{v} (ULift.{u} k)))
  -- After naming the two concrete linear equivalences, the naturality statement is a plain
  -- `Finsupp` induction with `zero/add/single` computations.
  change eβ ⟨Finsupp.mapDomain g x⟩ =
    Finsupp.mapDomain (CategoryTheory.uliftFunctor.{v, u}.map g) (eα ⟨x⟩)
  induction x using Finsupp.induction_linear with
  | zero =>
      -- The zero finitely supported function is preserved by every map in the comparison square.
      simp [eα, eβ]
  | add x y hx hy =>
      -- Naturality is additive because every map in the square is linear.
      simpa [eα, eβ, Finsupp.mapDomain_add] using congrArg₂ (· + ·) hx hy
  | single a b =>
      -- On a basis vector, both routes send `single a b` to the lifted basis vector at `g a`.
      simp [eα, eβ, Finsupp.mapDomain_single]

/-- Helper for Problem 10.8.5: after both coproducts are normalized to their concrete
`Finsupp` owners, the middle `ULift` bridge commutes with `Finsupp.lmapDomain`. -/
theorem sigmaConstUliftFinsuppIsoNaturality
    (k : Type w) [Field k] {α β : Type u} (g : α → β) :
    (ModuleCat.uliftFunctor.{v, max u w} k).map
        (ModuleCat.ofHom (Finsupp.lmapDomain (ULift.{u} k) k g)) ≫
      (sigmaConstUliftFinsuppIso (k := k) β).hom =
        (sigmaConstUliftFinsuppIso (k := k) α).hom ≫
          ModuleCat.ofHom
            (Finsupp.lmapDomain (ULift.{v} (ULift.{u} k)) k
              (CategoryTheory.uliftFunctor.{v, u}.map g)) := by
  -- Evaluate the lifted `ModuleCat` morphism on a concrete `Finsupp` input and reuse the
  -- basis-vector computation above.
  apply ModuleCat.hom_ext
  ext x a
  rcases x with ⟨x⟩
  simpa [ModuleCat.uliftFunctor, Finsupp.lmapDomain_apply] using
    congrArg
      (fun f : ULift.{v} β →₀ ULift.{v} (ULift.{u} k) => f a)
      (sigmaConstUliftFinsuppIsoNaturalityApply (k := k) (g := g) x)

/-- Helper for Problem 10.8.5: the degreewise coproduct transport for `sigmaConst` is natural in
the indexing type. -/
theorem sigmaConstUliftCoproductNaturality
    (k : Type w) [Field k] {α β : Type u} (g : α → β) :
    (ModuleCat.uliftFunctor.{v, max u w} k).map
        (Limits.Sigma.map' g (fun _ ↦ 𝟙 (ModuleCat.of k (ULift.{u} k)))) ≫
      (sigmaConstUliftCoproductIso (k := k) β).hom =
        (sigmaConstUliftCoproductIso (k := k) α).hom ≫
          Limits.Sigma.map' (CategoryTheory.uliftFunctor.{v, u}.map g)
            (fun _ ↦
              𝟙 ((ModuleCat.uliftFunctor.{v, max u w} k).obj
                (ModuleCat.of k (ULift.{u} k)))) := by
  -- Route correction: rewrite the categorical coproduct maps to the concrete `Finsupp` owners,
  -- so the goal becomes the middle `Finsupp.lmapDomain` commutation proved above.
  let F := ModuleCat.uliftFunctor.{v, max u w} k
  let sourceIso (γ : Type u) : (∐ fun _ : γ ↦ ModuleCat.of k (ULift.{u} k)) ≅
      ModuleCat.of k (γ →₀ ULift.{u} k) :=
    moduleCatConstantCoproductIso (R := k) γ (ULift.{u} k)
  let targetIso (γ : Type u) : (∐ fun _ : ULift.{v} γ ↦
      F.obj (ModuleCat.of k (ULift.{u} k))) ≅
      ModuleCat.of k (ULift.{v} γ →₀ ULift.{v} (ULift.{u} k)) :=
    moduleCatConstantCoproductIso (R := k) (ULift.{v} γ) (ULift.{v} (ULift.{u} k))
  have hSourceBase :
      (F.mapIso (sourceIso α)).inv ≫
          F.map (Limits.Sigma.map' g (fun _ ↦ 𝟙 (ModuleCat.of k (ULift.{u} k)))) ≫
          (F.mapIso (sourceIso β)).hom =
        F.map (ModuleCat.ofHom (Finsupp.lmapDomain (ULift.{u} k) k g)) := by
    -- Move the source coproduct map through the concrete `Finsupp` normalization before applying
    -- the middle `ULift` bridge.
    simpa [F, sourceIso, Functor.map_comp, Category.assoc] using
      congrArg F.map
        (moduleCatConstantCoproductIso_inv_sigmaMap_hom
          (R := k) (M := ULift.{u} k) (g := g))
  have hSource :
      F.map (Limits.Sigma.map' g (fun _ ↦ 𝟙 (ModuleCat.of k (ULift.{u} k)))) ≫
          (F.mapIso (sourceIso β)).hom =
        (F.mapIso (sourceIso α)).hom ≫
          F.map (ModuleCat.ofHom (Finsupp.lmapDomain (ULift.{u} k) k g)) := by
    -- Cancel the source normalization iso from `hSourceBase`.
    simpa [Category.assoc] using
      congrArg (fun f ↦ (F.mapIso (sourceIso α)).hom ≫ f) hSourceBase
  have hTargetBase :
      (targetIso α).inv ≫
          Limits.Sigma.map' (CategoryTheory.uliftFunctor.{v, u}.map g)
            (fun _ ↦ 𝟙 (F.obj (ModuleCat.of k (ULift.{u} k)))) ≫
          (targetIso β).hom =
        ModuleCat.ofHom
          (Finsupp.lmapDomain (ULift.{v} (ULift.{u} k)) k
            (CategoryTheory.uliftFunctor.{v, u}.map g)) := by
    -- The target coproduct normalization turns the lifted `Sigma.map'` back into the concrete
    -- `Finsupp.lmapDomain` map.
    simpa [targetIso] using
      moduleCatConstantCoproductIso_inv_sigmaMap_hom
        (R := k) (M := ULift.{v} (ULift.{u} k))
        (g := CategoryTheory.uliftFunctor.{v, u}.map g)
  have hTarget :
      ModuleCat.ofHom
          (Finsupp.lmapDomain (ULift.{v} (ULift.{u} k)) k
            (CategoryTheory.uliftFunctor.{v, u}.map g)) ≫
          (targetIso β).inv =
        (targetIso α).inv ≫
          Limits.Sigma.map' (CategoryTheory.uliftFunctor.{v, u}.map g)
            (fun _ ↦ 𝟙 (F.obj (ModuleCat.of k (ULift.{u} k)))) := by
    -- Cancel the target normalization iso from `hTargetBase`.
    simpa [Category.assoc] using
      (congrArg (fun f ↦ f ≫ (targetIso β).inv) hTargetBase).symm
  -- The two normalization lemmas and the middle `Finsupp` naturality square assemble the full
  -- categorical naturality statement.
  calc
    F.map (Limits.Sigma.map' g (fun _ ↦ 𝟙 (ModuleCat.of k (ULift.{u} k)))) ≫
        (sigmaConstUliftCoproductIso (k := k) β).hom =
      F.map (Limits.Sigma.map' g (fun _ ↦ 𝟙 (ModuleCat.of k (ULift.{u} k)))) ≫
          (F.mapIso (sourceIso β)).hom ≫
          (sigmaConstUliftFinsuppIso (k := k) β).hom ≫
          (targetIso β).inv := by
        rw [sigmaConstUliftCoproductIso]
        simp [F, sourceIso, targetIso]
    _ = (F.mapIso (sourceIso α)).hom ≫
          F.map (ModuleCat.ofHom (Finsupp.lmapDomain (ULift.{u} k) k g)) ≫
          (sigmaConstUliftFinsuppIso (k := k) β).hom ≫
          (targetIso β).inv := by
        simpa only [Category.assoc] using
          congrArg
            (fun f ↦ f ≫ (sigmaConstUliftFinsuppIso (k := k) β).hom ≫ (targetIso β).inv)
            hSource
    _ = (F.mapIso (sourceIso α)).hom ≫
          (sigmaConstUliftFinsuppIso (k := k) α).hom ≫
            ModuleCat.ofHom
              (Finsupp.lmapDomain (ULift.{v} (ULift.{u} k)) k
                (CategoryTheory.uliftFunctor.{v, u}.map g)) ≫
            (targetIso β).inv := by
        simpa only [Category.assoc] using
          congrArg
            (fun f ↦ (F.mapIso (sourceIso α)).hom ≫ f ≫ (targetIso β).inv)
            (sigmaConstUliftFinsuppIsoNaturality (k := k) (g := g))
    _ = (F.mapIso (sourceIso α)).hom ≫
          (sigmaConstUliftFinsuppIso (k := k) α).hom ≫
            (targetIso α).inv ≫
              Limits.Sigma.map' (CategoryTheory.uliftFunctor.{v, u}.map g)
                (fun _ ↦ 𝟙 (F.obj (ModuleCat.of k (ULift.{u} k)))) := by
        simpa only [Category.assoc] using
          congrArg
            (fun f ↦ (F.mapIso (sourceIso α)).hom ≫
              (sigmaConstUliftFinsuppIso (k := k) α).hom ≫ f)
            hTarget
    _ = (sigmaConstUliftCoproductIso (k := k) α).hom ≫
          Limits.Sigma.map' (CategoryTheory.uliftFunctor.{v, u}.map g)
            (fun _ ↦ 𝟙 (F.obj (ModuleCat.of k (ULift.{u} k)))) := by
        rw [sigmaConstUliftCoproductIso]
        simp [Category.assoc, F, sourceIso, targetIso]

/-- Helper for Problem 10.8.5: the `sigmaConst` simplicial object commutes with lifting the
coefficient module and lifting the simplicial set. -/
noncomputable def ssetSigmaConstUliftFunctorIso
    (k : Type w) [Field k] (S : SSet.{u}) :
    (((SimplicialObject.whiskering (ModuleCat.{max u w} k) (ModuleCat.{max (max u w) v} k)).obj
        (ModuleCat.uliftFunctor.{v, max u w} k)).obj
      ((((SimplicialObject.whiskering (Type u) (ModuleCat.{max u w} k)).obj
            ((CategoryTheory.Limits.sigmaConst).obj (ModuleCat.of k (ULift.{u} k)))).obj
          S))) ≅
      ((((SimplicialObject.whiskering (Type (max u v)) (ModuleCat.{max (max u w) v} k)).obj
            ((CategoryTheory.Limits.sigmaConst).obj
              ((ModuleCat.uliftFunctor.{v, max u w} k).obj (ModuleCat.of k (ULift.{u} k))))).obj
          (SSet.uliftFunctor.{v}.obj S))) := by
  -- Route correction: the remaining mixed-`ULift` obstruction is no longer in
  -- `alternatingFaceMapComplex`; it is the degreewise `sigmaConst` comparison.
  refine NatIso.ofComponents (fun n ↦ sigmaConstUliftCoproductIso (k := k) (S.obj n)) ?_
  intro n m f
  -- The only nontrivial naturality check is the degreewise coproduct transport proved above.
  simpa [SSet.uliftFunctor] using
    sigmaConstUliftCoproductNaturality (k := k) (g := S.map f)

/-- Helper for Problem 10.8.5: singular chains on simplicial sets commute with lifting the
coefficient module and lifting the simplicial set. -/
noncomputable def ssetSingularChainsUliftFunctorIso
    (k : Type w) [Field k] (S : SSet.{u}) :
    (((ModuleCat.uliftFunctor.{v, max u w} k).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (((AlgebraicTopology.SSet.singularChainComplexFunctor (ModuleCat.{max u w} k)).obj
          (ModuleCat.of k (ULift.{u} k))).obj S)) ≅
      (((AlgebraicTopology.SSet.singularChainComplexFunctor
          (ModuleCat.{max (max u w) v} k)).obj
          ((ModuleCat.uliftFunctor.{v, max u w} k).obj (ModuleCat.of k (ULift.{u} k)))).obj
        (SSet.uliftFunctor.{v}.obj S)) := by
  -- Route correction: first commute `alternatingFaceMapComplex` with
  -- `ModuleCat.uliftFunctor`, then isolate the remaining simplicial `sigmaConst` transport.
  let F := ModuleCat.uliftFunctor.{v, max u w} k
  let R : ModuleCat.{max u w} k := ModuleCat.of k (ULift.{u} k)
  let hAlternating :
      (((ModuleCat.uliftFunctor.{v, max u w} k).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (((AlgebraicTopology.SSet.singularChainComplexFunctor (ModuleCat.{max u w} k)).obj
              (ModuleCat.of k (ULift.{u} k))).obj S)) ≅
        ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max (max u w) v} k)).obj
          ((((SimplicialObject.whiskering (ModuleCat.{max u w} k)
                  (ModuleCat.{max (max u w) v} k)).obj F).obj
              ((((SimplicialObject.whiskering (Type u) (ModuleCat.{max u w} k)).obj
                    ((CategoryTheory.Limits.sigmaConst).obj R)).obj S))))) :=
    -- Compare the alternating-face-map owners after whiskering by `F`.
    eqToIso <|
      by
        simpa [AlgebraicTopology.SSet.singularChainComplexFunctor, F, R, SSet.uliftFunctor] using
          Functor.congr_obj (AlgebraicTopology.map_alternatingFaceMapComplex F)
            ((((SimplicialObject.whiskering _ _).obj ((CategoryTheory.Limits.sigmaConst).obj R)).obj
              S))
  -- Once the `sigmaConst` layer is normalized, `alternatingFaceMapComplex` finishes the bridge.
  exact
    hAlternating ≪≫
      (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max (max u w) v} k)).mapIso
        (ssetSigmaConstUliftFunctorIso (k := k) S)

/-- Helper for Problem 10.8.5: lifting the space argument through `TopCat.uliftFunctor` agrees
with lifting the resulting singular chain complex through `ModuleCat.uliftFunctor`. -/
noncomputable def fieldTopologicalSingularChainsUliftFunctorIso
    {X : Type u} [TopologicalSpace X] (k : Type w) [Field k] :
    (((ModuleCat.uliftFunctor.{v, max u w} k).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (fieldTopologicalSingularChains k (TopCat.of (ULift.{u} X)))) ≅
      (((singularChainComplexFunctor.{max u v} (ModuleCat.{max (max u w) v} k)).obj
          ((ModuleCat.uliftFunctor.{v, max u w} k).obj (ModuleCat.of k (ULift.{u} k)))).obj
        (TopCat.uliftFunctor.{v}.obj (TopCat.of (ULift.{u} X)))) := by
  -- Route correction: separate the space transport from the chain-complex transport.
  -- First move singular chains across the simplicial `ULift`, then rewrite the lifted singular
  -- simplicial set of the space through the thin `TopCat.toSSet` adapter.
  exact
    ssetSingularChainsUliftFunctorIso (k := k) (S := TopCat.toSSet.obj (TopCat.of (ULift.{u} X))) ≪≫
      (((AlgebraicTopology.SSet.singularChainComplexFunctor
          (ModuleCat.{max (max u w) v} k)).obj
          ((ModuleCat.uliftFunctor.{v, max u w} k).obj (ModuleCat.of k (ULift.{u} k)))).mapIso
        (topCatToSSetUliftFunctorIso (Y := TopCat.of (ULift.{u} X))).symm)

/-- Helper for Problem 10.8.5: after lifting the singular chains on `ULift.{u} X` through
`ModuleCat.uliftFunctor`, the resulting chain complex agrees with the common-level singular-chain
owner obtained by lifting both the coefficient object and the space to universe `max u v`. -/
noncomputable abbrev fieldTopologicalSingularChainsCommonLevelIso_of_moduleUlift
    {X : Type u} [TopologicalSpace X] (k : Type w) [Field k] :=
  -- First move the space to `TopCat.uliftFunctor.obj`, then normalize the coefficient object.
  fieldTopologicalSingularChainsUliftFunctorIso (X := X) k ≪≫
    (((singularChainComplexFunctor.{max u v} (ModuleCat.{max (max u w) v} k)).mapIso
        (fieldSingularCoefficientUliftIso k).symm).app
      (TopCat.uliftFunctor.{v}.obj (TopCat.of (ULift.{u} X))))

/-- Helper for Problem 10.8.5: singular-homology Euler characteristic with field coefficients is
preserved by homotopy equivalences even when the spaces live in different universes. -/
theorem fieldTopologicalSingularHomologyEulerChar_eq_betweenUlifts
    {X : Type u} [TopologicalSpace X] (k : Type w) [Field k] :
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of (ULift.{v} X)) =
      fieldTopologicalSingularHomologyEulerChar k (TopCat.of (ULift.{u} X)) := by
  -- Route correction: `ULift.{v} X` and `ULift.{u} X` are homeomorphic, but their singular chain
  -- complexes live in different module universes, so the direct homeomorphism route still needs an
  -- explicit chain-complex comparison across those universes.
  -- Rewrite both sides to the common-level singular-chain owner and compare there.
  calc
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of (ULift.{v} X)) =
        HomologicalComplex.homologyEulerChar
          (fieldTopologicalSingularChainsCommonLevel k (X := X)) := by
      rfl
    _ = HomologicalComplex.homologyEulerChar
          (fieldTopologicalSingularChainsCommonLevel k (X := ULift.{u} X)) := by
      -- The common-level owner is invariant under the canonical `ULift` homeomorphism.
      exact
        homologyEulerChar_eq_of_iso (k := k)
          (fieldTopologicalSingularChainsCommonLevelIso_of_uliftLevelHomeomorph
            (X := X) k)
    _ = HomologicalComplex.homologyEulerChar
          (((ModuleCat.uliftFunctor.{v, max u w} k).mapHomologicalComplex
              (ComplexShape.down ℕ)).obj
            (fieldTopologicalSingularChains k (TopCat.of (ULift.{u} X)))) := by
      -- The new adapter identifies the common-level owner with the lifted singular chains.
      symm
      exact
        homologyEulerChar_eq_of_iso (k := k)
          (fieldTopologicalSingularChainsCommonLevelIso_of_moduleUlift (X := X) k)
    _ = fieldTopologicalSingularHomologyEulerChar k (TopCat.of (ULift.{u} X)) := by
      -- Lifting the module universe does not alter the homological Euler characteristic.
      symm
      exact
        homologyEulerChar_eq_of_moduleUlift (k := k)
          (fieldTopologicalSingularChains k (TopCat.of (ULift.{u} X)))

/-- Helper for Problem 10.8.5: singular-homology Euler characteristic with field coefficients is
preserved by homotopy equivalences even when the spaces live in different universes. -/
theorem singularHomologyEulerChar_eq_of_homotopyEquivMixed
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (k : Type w) [Field k] (h : X ≃ₕ Y) :
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of X) =
      fieldTopologicalSingularHomologyEulerChar k (TopCat.of Y) := by
  -- Route correction: rewrite both endpoints to lifted copies, apply the common-universe theorem
  -- in the middle, and isolate the remaining transport issue in one `ULift`-comparison helper.
  calc
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of X) =
        fieldTopologicalSingularHomologyEulerChar k (TopCat.of (ULift.{u} X)) :=
      fieldTopologicalSingularHomologyEulerChar_eq_sameLevelUlift (k := k)
    _ = fieldTopologicalSingularHomologyEulerChar k (TopCat.of (ULift.{v} X)) := by
      -- The remaining owner/coefficient transport is isolated in a dedicated helper.
      exact
        (fieldTopologicalSingularHomologyEulerChar_eq_betweenUlifts (X := X) (k := k) :
          fieldTopologicalSingularHomologyEulerChar k (TopCat.of (ULift.{v} X)) =
            fieldTopologicalSingularHomologyEulerChar k (TopCat.of (ULift.{u} X))).symm
    _ = fieldTopologicalSingularHomologyEulerChar k (TopCat.of (ULift.{u} Y)) := by
      -- Once both spaces are lifted, the mixed-universe issue disappears.
      exact singularHomologyEulerChar_eq_of_homotopyEquivOnULifts (k := k) h
    _ = fieldTopologicalSingularHomologyEulerChar k (TopCat.of (ULift.{v} Y)) := by
      -- Apply the same `ULift`-comparison helper on the target side.
      exact
        (fieldTopologicalSingularHomologyEulerChar_eq_betweenUlifts (X := Y) (k := k) :
          fieldTopologicalSingularHomologyEulerChar k (TopCat.of (ULift.{u} Y)) =
            fieldTopologicalSingularHomologyEulerChar k (TopCat.of (ULift.{v} Y)))
    _ = fieldTopologicalSingularHomologyEulerChar k (TopCat.of Y) := by
      -- Compare the lifted copy of `Y` back to the original space.
      symm
      exact fieldTopologicalSingularHomologyEulerChar_eq_sameLevelUlift (X := Y) (k := k)

/-- Helper for Problem 10.8.5: the Euler-characteristic sign on `ChainComplex _ ℕ` is
`Int.negOnePow`. -/
theorem downNatEulerSign_eq_negOnePow (n : ℕ) :
    ((ComplexShape.down ℕ).χ n : ℤ) = Int.negOnePow n := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      have hSucc :
          ((ComplexShape.down ℕ).χ (n + 1) : ℤ) = -((ComplexShape.down ℕ).χ n : ℤ) := by
        -- The Euler-characteristic sign alternates by one multiplication with `-1`.
        simpa using
          congrArg (fun u : ℤˣ => (u : ℤ))
            (ComplexShape.χ_prev (c := ComplexShape.down ℕ)
              (show (ComplexShape.down ℕ).Rel (n + 1) n by simp))
      have hNegOnePow : (-(Int.negOnePow n : ℤˣ) : ℤ) = Int.negOnePow (n + 1) := by
        -- The standard `negOnePow` recursion has the same alternating step.
        simpa using congrArg (fun u : ℤˣ => (u : ℤ)) (Int.negOnePow_succ n).symm
      calc
        ((ComplexShape.down ℕ).χ (n + 1) : ℤ) = -((ComplexShape.down ℕ).χ n : ℤ) := hSucc
        _ = -Int.negOnePow n := by rw [ih]
        _ = Int.negOnePow (n + 1) := hNegOnePow

/-- Helper for Problem 10.8.5: a field-valued chain complex on the subtype space `C` whose
graded ranks match the CW cell counts and whose Euler characteristic already equals its
homological Euler characteristic has the expected alternating cell-count formula. -/
theorem homologyEulerChar_eq_sum_range_of_eulerCharOnSubset
    {X : Type u} [TopologicalSpace X] {C : Set X} [CWComplex C]
    (k : Type w) [Field k] (K : ChainComplex (ModuleCat.{max u w} k) ℕ)
    [∀ n : ℕ, K.HasHomology n] {N : ℕ}
    (hEuler : HomologicalComplex.eulerChar K = HomologicalComplex.homologyEulerChar K)
    (hSupport : GradedObject.finrankSupport K.X ⊆ Finset.range N)
    (hFinrank :
      ∀ n : ℕ, Module.finrank k (K.X n) = Nat.card (Topology.CWComplex.cell C n)) :
    HomologicalComplex.homologyEulerChar K =
      Finset.sum (Finset.range N) fun n ↦
        (Int.negOnePow n : ℤ) * Nat.card (Topology.CWComplex.cell C n) := by
  -- First rewrite homological Euler characteristic back to the ordinary Euler characteristic.
  calc
    HomologicalComplex.homologyEulerChar K = HomologicalComplex.eulerChar K := hEuler.symm
    _ = ∑ n ∈ Finset.range N, ((ComplexShape.down ℕ).χ n : ℤ) * Module.finrank k (K.X n) := by
        -- The chain groups outside the cutoff do not contribute because the finrank support is
        -- already contained in `Finset.range N`.
        simpa using
          HomologicalComplex.eulerChar_eq_sum_finSet_of_finrankSupport_subset K (Finset.range N)
            hSupport
    _ = ∑ n ∈ Finset.range N,
          ((ComplexShape.down ℕ).χ n : ℤ) * Nat.card (Topology.CWComplex.cell C n) := by
        -- Replace the degreewise module ranks by the prescribed cell counts.
        refine Finset.sum_congr rfl ?_
        intro n hn
        rw [hFinrank n]
    _ = Finset.sum (Finset.range N) fun n ↦
          (Int.negOnePow n : ℤ) * Nat.card (Topology.CWComplex.cell C n) := by
        -- Finally rewrite the sign convention to the Chapter 10 `(-1)^n` notation.
        refine Finset.sum_congr rfl ?_
        intro n hn
        rw [downNatEulerSign_eq_negOnePow]

/-- Helper for Problem 10.8.5: once a field-valued chain model for `C` is known to compute
singular homology and to have the expected finite CW rank package, the singular-homology Euler
characteristic rewrites to the alternating cell-count sum cut off at `N`. -/
theorem fieldTopologicalSingularHomologyEulerChar_eq_sum_range_of_modelOnSubset
    {X : Type u} [TopologicalSpace X] {C : Set X} [CWComplex C]
    (k : Type w) [Field k] (K : ChainComplex (ModuleCat.{max u w} k) ℕ)
    [∀ n : ℕ, K.HasHomology n] {N : ℕ}
    (hComparison :
      fieldTopologicalSingularHomologyEulerChar k (TopCat.of C) =
        HomologicalComplex.homologyEulerChar K)
    (hEuler : HomologicalComplex.eulerChar K = HomologicalComplex.homologyEulerChar K)
    (hSupport : GradedObject.finrankSupport K.X ⊆ Finset.range N)
    (hFinrank :
      ∀ n : ℕ, Module.finrank k (K.X n) = Nat.card (Topology.CWComplex.cell C n)) :
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of C) =
      Finset.sum (Finset.range N) fun n ↦
        (Int.negOnePow n : ℤ) * Nat.card (Topology.CWComplex.cell C n) := by
  -- First move from singular homology to the chosen chain model `K`.
  calc
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of C) =
        HomologicalComplex.homologyEulerChar K := hComparison
    -- Then normalize the chain model's Euler characteristic by the already-packaged rank data.
    _ = Finset.sum (Finset.range N) fun n ↦
          (Int.negOnePow n : ℤ) * Nat.card (Topology.CWComplex.cell C n) :=
      homologyEulerChar_eq_sum_range_of_eulerCharOnSubset
        (C := C) (k := k) K hEuler hSupport hFinrank

/-- Helper for Problem 10.8.5: singular-homology Euler characteristic is unchanged when the
subset owner `C : Set X` is replaced by the homeomorphic whole-space subtype `(Set.univ : Set C)`.
-/
theorem fieldTopologicalSingularHomologyEulerChar_eq_univSubtype
    {X : Type u} [TopologicalSpace X] {C : Set X} (k : Type w) [Field k] :
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of C) =
      fieldTopologicalSingularHomologyEulerChar k (TopCat.of (Set.univ : Set C)) := by
  -- The subtype `C` and its whole-space owner are canonically homeomorphic, so homotopy
  -- invariance transfers singular-homology Euler characteristic across that owner change.
  symm
  simpa using
    singularHomologyEulerChar_eq_of_homotopyEquiv
      (X := (Set.univ : Set C)) (Y := C) (k := k) (Homeomorph.Set.univ C).toHomotopyEquiv

/-- Helper for Problem 10.8.5: the transported characteristic map on the subtype owner targets the
subtype version of the original characteristic-map target. -/
def subtypeCellTarget
    {X : Type u} [TopologicalSpace X] {C : Set X} [CWComplex C]
    (n : ℕ) (i : Topology.CWComplex.cell C n) : Set C :=
  {x | ((x : C) : X) ∈ (Topology.CWComplex.map (C := C) n i).target}

/-- Helper for Problem 10.8.5: choose a canonical point of the closed cell indexed by `i`, viewed
in the subtype space `C`. -/
noncomputable def subtypeCellBasepoint
    {X : Type u} [TopologicalSpace X] {C : Set X} [CWComplex C]
    (n : ℕ) (i : Topology.CWComplex.cell C n) : C :=
  ⟨Topology.CWComplex.map (C := C) n i 0,
    Topology.CWComplex.closedCell_subset_complex (C := C) n i <|
      Topology.RelCWComplex.map_zero_mem_closedCell (C := C) (D := ∅) n i⟩

/-- Helper for Problem 10.8.5: transport one ambient characteristic map to the whole-space subtype
owner by codrestricting its values to `C` and using a fixed fallback point away from the cell
image. -/
noncomputable def subtypeCellMap
    {X : Type u} [TopologicalSpace X] {C : Set X} [CWComplex C]
    (n : ℕ) (i : Topology.CWComplex.cell C n) : PartialEquiv (Fin n → ℝ) C where
  toFun := by
    classical
    intro x
    exact
      if hx : Topology.CWComplex.map (C := C) n i x ∈ C then
        ⟨Topology.CWComplex.map (C := C) n i x, hx⟩
      else
        subtypeCellBasepoint (C := C) n i
  invFun := fun y ↦ (Topology.CWComplex.map (C := C) n i).symm y.1
  source := Metric.ball 0 1
  target := subtypeCellTarget (C := C) n i
  map_source' := by
    classical
    intro x hx
    have hxSource : x ∈ (Topology.CWComplex.map (C := C) n i).source := by
      simpa [Topology.CWComplex.source_eq (C := C) n i] using hx
    have hxComplex : Topology.CWComplex.map (C := C) n i x ∈ C :=
      Topology.CWComplex.openCell_subset_complex (C := C) n i ⟨x, hx, rfl⟩
    -- On the source ball the codomain restriction follows the original characteristic map.
    simpa [subtypeCellTarget, hxComplex] using
      (Topology.CWComplex.map (C := C) n i).map_source hxSource
  map_target' := by
    intro y hy
    -- The target was defined so that the original inverse lands back in the source ball.
    have hyTarget : ((y : C) : X) ∈ (Topology.CWComplex.map (C := C) n i).target := hy
    have hySource :
        (Topology.CWComplex.map (C := C) n i).symm y.1 ∈
          (Topology.CWComplex.map (C := C) n i).source :=
      (Topology.CWComplex.map (C := C) n i).map_target hyTarget
    simpa [Topology.CWComplex.source_eq (C := C) n i] using hySource
  left_inv' := by
    classical
    intro x hx
    have hxSource : x ∈ (Topology.CWComplex.map (C := C) n i).source := by
      simpa [Topology.CWComplex.source_eq (C := C) n i] using hx
    have hxComplex : Topology.CWComplex.map (C := C) n i x ∈ C :=
      Topology.CWComplex.openCell_subset_complex (C := C) n i ⟨x, hx, rfl⟩
    -- After simplifying the fallback branch away, this is the original left inverse.
    simpa [hxComplex] using
      (Topology.CWComplex.map (C := C) n i).left_inv hxSource
  right_inv' := by
    classical
    intro y hy
    have hyTarget : ((y : C) : X) ∈ (Topology.CWComplex.map (C := C) n i).target := hy
    have hyComplex :
        Topology.CWComplex.map (C := C) n i
            ((Topology.CWComplex.map (C := C) n i).symm y.1) ∈ C := by
      simpa [(Topology.CWComplex.map (C := C) n i).right_inv hyTarget] using y.2
    -- The subtype-valued map agrees with the original characteristic map on the transported target.
    apply Subtype.ext
    simpa [hyComplex] using
      (Topology.CWComplex.map (C := C) n i).right_inv hyTarget

/-- Helper for Problem 10.8.5: whenever the ambient characteristic map already lands in `C`, the
transported subtype-valued characteristic map is that same point viewed in the subtype space. -/
theorem subtypeCellMap_apply_of_mem_complex
    {X : Type u} [TopologicalSpace X] {C : Set X} [CWComplex C]
    {n : ℕ} {i : Topology.CWComplex.cell C n} {x : Fin n → ℝ}
    (hx : Topology.CWComplex.map (C := C) n i x ∈ C) :
    subtypeCellMap (C := C) n i x = ⟨Topology.CWComplex.map (C := C) n i x, hx⟩ := by
  -- This is just the simplifying branch of the codomain restriction.
  classical
  apply Subtype.ext
  simp [subtypeCellMap, hx]

/-- Helper for Problem 10.8.5: on the closed ball, the transported subtype-valued characteristic
map is exactly the original characteristic map with codomain restricted to `C`. -/
theorem subtypeCellMap_apply_of_mem_closedBall
    {X : Type u} [TopologicalSpace X] {C : Set X} [CWComplex C]
    {n : ℕ} {i : Topology.CWComplex.cell C n} {x : Fin n → ℝ}
    (hx : x ∈ Metric.closedBall 0 1) :
    subtypeCellMap (C := C) n i x =
      ⟨Topology.CWComplex.map (C := C) n i x,
        Topology.CWComplex.closedCell_subset_complex (C := C) n i ⟨x, hx, rfl⟩⟩ := by
  -- Closed-ball points already lie in the ambient complex, so the fallback branch disappears.
  exact subtypeCellMap_apply_of_mem_complex (C := C) <|
    Topology.CWComplex.closedCell_subset_complex (C := C) n i ⟨x, hx, rfl⟩

/-- Helper for Problem 10.8.5: the transported open cell is the subtype preimage of the original
open cell. -/
theorem subtypeCellMap_image_ball_eq
    {X : Type u} [TopologicalSpace X] {C : Set X} [CWComplex C]
    (n : ℕ) (i : Topology.CWComplex.cell C n) :
    subtypeCellMap (C := C) n i '' Metric.ball 0 1 =
      Subtype.val ⁻¹' (Topology.CWComplex.map (C := C) n i '' Metric.ball 0 1) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    -- On the source ball, the subtype-valued map is just the original map with codomain restricted.
    exact ⟨x, hx, by
      simpa [subtypeCellMap_apply_of_mem_closedBall (C := C) (n := n) (i := i)
        (Metric.ball_subset_closedBall hx)]⟩
  · rintro ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    -- Matching values in the ambient space identifies the corresponding subtype points.
    apply Subtype.ext
    simpa [subtypeCellMap_apply_of_mem_closedBall (C := C) (n := n) (i := i)
      (Metric.ball_subset_closedBall hx)] using hxy

/-- Helper for Problem 10.8.5: the transported closed cell is the subtype preimage of the original
closed cell. -/
theorem subtypeCellMap_image_closedBall_eq
    {X : Type u} [TopologicalSpace X] {C : Set X} [CWComplex C]
    (n : ℕ) (i : Topology.CWComplex.cell C n) :
    subtypeCellMap (C := C) n i '' Metric.closedBall 0 1 =
      Subtype.val ⁻¹' (Topology.CWComplex.map (C := C) n i '' Metric.closedBall 0 1) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    -- The transported map agrees with the original map throughout the closed ball.
    exact ⟨x, hx, by
      simpa [subtypeCellMap_apply_of_mem_closedBall (C := C) (n := n) (i := i) hx]⟩
  · rintro ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    -- Again equality of ambient values identifies the subtype points.
    apply Subtype.ext
    simpa [subtypeCellMap_apply_of_mem_closedBall (C := C) (n := n) (i := i) hx] using hxy

/-- Helper for Problem 10.8.5: the transported subtype-valued characteristic map is continuous on
the closed ball because the fallback branch never occurs there. -/
theorem subtypeCellMap_continuousOn
    {X : Type u} [TopologicalSpace X] {C : Set X} [CWComplex C]
    (n : ℕ) (i : Topology.CWComplex.cell C n) :
    ContinuousOn (subtypeCellMap (C := C) n i) (Metric.closedBall 0 1) := by
  rw [continuousOn_iff_continuous_restrict]
  let f : Metric.closedBall (0 : Fin n → ℝ) 1 → C := fun x ↦
    ⟨Topology.CWComplex.map (C := C) n i x.1,
      Topology.CWComplex.closedCell_subset_complex (C := C) n i ⟨x.1, x.2, rfl⟩⟩
  have hf : Continuous f := by
    -- Restrict the original continuous characteristic map and then codrestrict to `C`.
    exact Continuous.subtype_mk
      (by
        simpa [continuousOn_iff_continuous_restrict, f] using
          (Topology.CWComplex.continuousOn (C := C) n i).restrict)
      (fun x : Metric.closedBall (0 : Fin n → ℝ) 1 ↦
        Topology.CWComplex.closedCell_subset_complex (C := C) n i ⟨x.1, x.2, rfl⟩)
  have hEq : (Metric.closedBall (0 : Fin n → ℝ) 1).restrict (subtypeCellMap (C := C) n i) = f := by
    funext x
    -- The restriction sees only the closed-ball branch where the codomain restriction is explicit.
    exact subtypeCellMap_apply_of_mem_closedBall (C := C) (n := n) (i := i) x.2
  simpa [hEq] using hf

/-- Helper for Problem 10.8.5: the inverse of the transported subtype-valued characteristic map is
continuous on its target because it is the original inverse precomposed with the subtype
projection. -/
theorem subtypeCellMap_continuousOn_symm
    {X : Type u} [TopologicalSpace X] {C : Set X} [CWComplex C]
    (n : ℕ) (i : Topology.CWComplex.cell C n) :
    ContinuousOn (subtypeCellMap (C := C) n i).symm (subtypeCellTarget (C := C) n i) := by
  rw [continuousOn_iff_continuous_restrict]
  let targetEmbedding :
      subtypeCellTarget (C := C) n i → (Topology.CWComplex.map (C := C) n i).target := fun y ↦
    ⟨((y : C) : X), y.2⟩
  have htargetEmbedding : Continuous targetEmbedding := by
    -- The subtype target only records an extra proof of ambient target membership.
    exact Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun y ↦ y.2)
  have hsymm :
      Continuous (((Topology.CWComplex.map (C := C) n i).target).restrict
        (Topology.CWComplex.map (C := C) n i).symm) :=
    (Topology.CWComplex.continuousOn_symm (C := C) n i).restrict
  have hEq :
      (subtypeCellTarget (C := C) n i).restrict ((subtypeCellMap (C := C) n i).symm) =
        ((Topology.CWComplex.map (C := C) n i).target).restrict
          (Topology.CWComplex.map (C := C) n i).symm ∘ targetEmbedding := by
    rfl
  simpa [hEq] using hsymm.comp htargetEmbedding

/-- Helper for Problem 10.8.5: the transported subtype-valued characteristic maps inherit the
pairwise-disjoint open-cell property from the original CW structure. -/
theorem subtypeCellMap_pairwiseDisjoint
    {X : Type u} [TopologicalSpace X] {C : Set X} [CWComplex C] :
    (Set.univ : Set (Sigma fun n : ℕ => Topology.CWComplex.cell C n)).PairwiseDisjoint
      (fun ni ↦ subtypeCellMap (C := C) ni.1 ni.2 '' Metric.ball 0 1) := by
  intro ⟨n, i⟩ _ ⟨m, j⟩ _ hne
  change Disjoint
    (subtypeCellMap (C := C) n i '' Metric.ball 0 1)
    (subtypeCellMap (C := C) m j '' Metric.ball 0 1)
  have hdisj :
      Disjoint
        (Topology.CWComplex.map (C := C) n i '' Metric.ball 0 1)
        (Topology.CWComplex.map (C := C) m j '' Metric.ball 0 1) :=
    Topology.CWComplex.pairwiseDisjoint' (C := C) (Set.mem_univ _) (Set.mem_univ _) hne
  rw [Set.disjoint_left] at hdisj ⊢
  intro y hyi hyj
  -- Forgetting the subtype point reduces to the original disjoint open-cell statement.
  rw [subtypeCellMap_image_ball_eq] at hyi hyj
  exact hdisj (by simpa using hyi) (by simpa using hyj)

/-- Helper for Problem 10.8.5: the transported characteristic map sends the boundary sphere into a
finite union of lower-dimensional transported closed cells. -/
theorem subtypeCellMap_mapsTo
    {X : Type u} [TopologicalSpace X] {C : Set X} [CWComplex C]
    (n : ℕ) (i : Topology.CWComplex.cell C n) :
    Set.MapsTo (subtypeCellMap (C := C) n i) (Metric.sphere 0 1)
      (⋃ (m < n) (j : Topology.CWComplex.cell C m),
        subtypeCellMap (C := C) m j '' Metric.closedBall 0 1) := by
  intro x hx
  rcases Topology.CWComplex.mapsTo (C := C) n i with ⟨I, hI⟩
  have hOld := hI hx
  simp only [Set.mem_iUnion, Set.mem_image, Metric.mem_closedBall, exists_prop] at hOld
  rcases hOld with ⟨m, hmn, j, hj, z, hz, hEq⟩
  have hxComplex : Topology.CWComplex.map (C := C) n i x ∈ C :=
    Topology.CWComplex.closedCell_subset_complex (C := C) n i ⟨x, Metric.sphere_subset_closedBall hx, rfl⟩
  -- Lift the old lower-cell witness into the subtype-owner closed-cell image.
  refine Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨hmn, Set.mem_iUnion.2 ⟨j, ?_⟩⟩⟩
  refine ⟨z, hz, ?_⟩
  apply Subtype.ext
  simpa [subtypeCellMap_apply_of_mem_closedBall (C := C) (n := m) (i := j) hz,
    subtypeCellMap_apply_of_mem_complex (C := C) (n := n) (i := i) hxComplex] using hEq

/-- Helper for Problem 10.8.5: the transported closed cells still cover the whole subtype owner
`(Set.univ : Set C)`. -/
theorem subtypeCellMap_union
    {X : Type u} [TopologicalSpace X] {C : Set X} [CWComplex C] :
    ⋃ (n : ℕ) (j : Topology.CWComplex.cell C n),
      subtypeCellMap (C := C) n j '' Metric.closedBall 0 1 = (Set.univ : Set C) := by
  ext y
  constructor
  · intro hy
    trivial
  · intro hy
    -- Forget the subtype and use the ambient closed-cell cover of `C`.
    have hyOld :
        ((y : C) : X) ∈
          ⋃ (n : ℕ) (j : Topology.CWComplex.cell C n),
            Topology.CWComplex.map (C := C) n j '' Metric.closedBall 0 1 := by
      have hyC : ((y : C) : X) ∈ C := y.2
      exact (congrArg
        (fun s : Set X =>
          ((y : C) : X) ∈ s)
        (Topology.CWComplex.union (C := C))).symm ▸ hyC
    -- Then rewrite that ambient cover back through the subtype closed-cell image formulas.
    simpa [subtypeCellMap_image_closedBall_eq] using hyOld

/-- Helper for Problem 10.8.5: the original finite CW structure on `C` induces a finite whole-space
CW structure on the subtype type `C`. -/
noncomputable abbrev subtypeUnivCWComplex
    {X : Type u} [TopologicalSpace X] {C : Set X} [CWComplex C] [CWComplex.Finite C] :
    CWComplex (Set.univ : Set C) :=
  Topology.CWComplex.mkFinite
    (Set.univ : Set C)
    (fun n ↦ Topology.CWComplex.cell C n)
    (subtypeCellMap (C := C))
    ((inferInstance : CWComplex.Finite C).eventually_isEmpty_cell)
    (fun n ↦ (inferInstance : CWComplex.Finite C).finite_cell n)
    (fun _ _ ↦ rfl)
    (subtypeCellMap_continuousOn (C := C))
    (subtypeCellMap_continuousOn_symm (C := C))
    (subtypeCellMap_pairwiseDisjoint (C := C))
    (subtypeCellMap_mapsTo (C := C))
    (subtypeCellMap_union (C := C))

/-- Helper for Problem 10.8.5: the transported whole-space subtype CW structure is finite because
it was built by `CWComplex.mkFinite` from the original finite CW structure on `C`. -/
theorem subtypeUnivCWComplex_finite
    {X : Type u} [TopologicalSpace X] {C : Set X} [CWComplex C] [CWComplex.Finite C] :
    letI : CWComplex (Set.univ : Set C) := subtypeUnivCWComplex (C := C)
    CWComplex.Finite (Set.univ : Set C) := by
  -- Reuse the constructor theorem for `CWComplex.mkFinite` with the transported subtype-valued maps.
  simpa [subtypeUnivCWComplex] using
    (Topology.CWComplex.finite_mkFinite
      (C := (Set.univ : Set C))
      (cell := fun n ↦ Topology.CWComplex.cell C n)
      (map := subtypeCellMap (C := C))
      ((inferInstance : CWComplex.Finite C).eventually_isEmpty_cell)
      (fun n ↦ (inferInstance : CWComplex.Finite C).finite_cell n)
      (fun _ _ ↦ rfl)
      (subtypeCellMap_continuousOn (C := C))
      (subtypeCellMap_continuousOn_symm (C := C))
      (subtypeCellMap_pairwiseDisjoint (C := C))
      (subtypeCellMap_mapsTo (C := C))
      (subtypeCellMap_union (C := C)))

/-- Helper for Problem 10.8.5: a point in the transported target maps back into the source ball of
the original characteristic map. -/
theorem cellMap_symm_mem_ball_of_memSubtypeCellTarget
    {X : Type u} [TopologicalSpace X] {C : Set X} [CWComplex C]
    {n : ℕ} {i : Topology.CWComplex.cell C n} {y : C}
    (hy : y ∈ subtypeCellTarget (C := C) n i) :
    (Topology.CWComplex.map (C := C) n i).symm y.1 ∈ Metric.ball 0 1 := by
  -- The transported target remembers exactly the original target membership, and the original
  -- inverse lands back in the source ball.
  simpa [subtypeCellTarget, Topology.CWComplex.source_eq (C := C) n i] using
    (Topology.CWComplex.map (C := C) n i).map_target hy

/-- Helper for Problem 10.8.5: on the source ball, the original characteristic map already lands
in the transported subtype target. -/
theorem cellMap_mem_subtypeCellTarget_of_mem_ball
    {X : Type u} [TopologicalSpace X] {C : Set X} [CWComplex C]
    {n : ℕ} {i : Topology.CWComplex.cell C n} {x : Fin n → ℝ}
    (hx : x ∈ Metric.ball 0 1) :
    (⟨Topology.CWComplex.map (C := C) n i x,
      Topology.CWComplex.openCell_subset_complex (C := C) n i ⟨x, hx, rfl⟩⟩ : C) ∈
      subtypeCellTarget (C := C) n i := by
  have hxSource : x ∈ (Topology.CWComplex.map (C := C) n i).source := by
    simpa [Topology.CWComplex.source_eq (C := C) n i] using hx
  -- This is the forward-direction companion to `cellMap_symm_mem_ball_of_memSubtypeCellTarget`.
  simpa [subtypeCellTarget] using
    (Topology.CWComplex.map (C := C) n i).map_source hxSource

/-- Helper for Problem 10.8.5: a finite CW structure on the subset `C : Set X` induces a finite
whole-space CW structure on the subtype type `C`, and the transported structure keeps the same
cell indexing types in every degree. -/
theorem existsSubtypeUnivFiniteCWStructure
    {X : Type u} [TopologicalSpace X] {C : Set X} [CWComplex C] [CWComplex.Finite C] :
    ∃ cw : CWComplex (Set.univ : Set C),
      letI : CWComplex (Set.univ : Set C) := cw
      CWComplex.Finite (Set.univ : Set C) ∧
        Nonempty (∀ n : ℕ, cw.cell n ≃ Topology.CWComplex.cell C n) := by
  -- Route correction: the owner change to `(Set.univ : Set C)` is now carried by the explicit
  -- subtype-valued characteristic maps above, so the whole theorem is just existential packaging.
  refine ⟨subtypeUnivCWComplex (C := C), ?_⟩
  letI : CWComplex (Set.univ : Set C) := subtypeUnivCWComplex (C := C)
  constructor
  · -- The transported structure is finite by the `mkFinite` constructor theorem.
    exact subtypeUnivCWComplex_finite (C := C)
  · -- The transported owner keeps exactly the same cell indexing types in each degree.
    exact ⟨fun _ ↦ Equiv.refl _⟩

/-- Helper for Problem 10.8.5: once the explicit whole-space cell-counting complex is fixed, its
homological Euler characteristic is the alternating finite sum of whole-space cell counts cut off
by `hN`. -/
theorem wholeSpaceCellCountingComplexHomologyEulerChar_eq_sum_range_of_isEmpty_cell
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    [CWComplex.Finite (Set.univ : Set Z)] (k : Type w) [Field k] {N : ℕ}
    (hN : ∀ n ≥ N, IsEmpty (Topology.CWComplex.cell (Set.univ : Set Z) n)) :
    HomologicalComplex.homologyEulerChar (wholeSpaceCellCountingComplex (Z := Z) k) =
      Finset.sum (Finset.range N) fun n ↦
        (Int.negOnePow n : ℤ) * Nat.card (Topology.CWComplex.cell (Set.univ : Set Z) n) := by
  let K := wholeSpaceCellCountingComplex (Z := Z) k
  -- The explicit zero-differential whole-space model already carries the degreewise homology
  -- and finrank package needed by the generic normalization theorem.
  letI : ∀ n : ℕ, K.HasHomology n := fun n ↦
    wholeSpaceCellCountingComplexHasHomology (Z := Z) (k := k) n
  obtain ⟨hEuler, hSupport, hFinrank⟩ :=
    wholeSpaceCellCountingComplexSpec (Z := Z) (k := k) hN
  -- Normalize the explicit model by the already-proved whole-space support and rank package.
  exact
    homologyEulerChar_eq_sum_range_of_eulerCharOnSubset
      (C := (Set.univ : Set Z)) (k := k) K hEuler hSupport hFinrank

/-- Helper for Problem 10.8.5: the fixed whole-space counting complex already computes the
Chapter 10 Euler characteristic of the whole-space CW owner. -/
theorem wholeSpaceCellCountingComplexHomologyEulerChar_eq_cwEulerCharacteristic
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    [CWComplex.Finite (Set.univ : Set Z)] (k : Type w) [Field k] :
    HomologicalComplex.homologyEulerChar (wholeSpaceCellCountingComplex (Z := Z) k) =
      χ((Set.univ : Set Z)) := by
  have hfinite : ∀ᶠ n in Filter.atTop, IsEmpty (Topology.CWComplex.cell (Set.univ : Set Z) n) :=
    (inferInstance : CWComplex.Finite (Set.univ : Set Z)).eventually_isEmpty_cell
  simp_rw [Filter.eventually_atTop, ge_iff_le] at hfinite
  rcases hfinite with ⟨N, hN⟩
  -- Compare both sides to the same alternating finite cell-count sum cut off at `N`.
  calc
    HomologicalComplex.homologyEulerChar (wholeSpaceCellCountingComplex (Z := Z) k) =
        Finset.sum (Finset.range N) fun n ↦
          (Int.negOnePow n : ℤ) * Nat.card (Topology.CWComplex.cell (Set.univ : Set Z) n) :=
      wholeSpaceCellCountingComplexHomologyEulerChar_eq_sum_range_of_isEmpty_cell
        (Z := Z) (k := k) hN
    _ = χ((Set.univ : Set Z)) := by
      symm
      exact cwEulerCharacteristic_eq_sum_range_of_isEmpty_cell
        (C := (Set.univ : Set Z)) hN

/-- Helper for Problem 10.8.5: a finite whole-space CW owner has a concrete cutoff above which
all cell-indexing types are empty. -/
theorem existsWholeSpaceCellCutoff
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    [CWComplex.Finite (Set.univ : Set Z)] :
    ∃ N : ℕ, ∀ n ≥ N, IsEmpty (Topology.CWComplex.cell (Set.univ : Set Z) n) := by
  have hfinite : ∀ᶠ n in Filter.atTop, IsEmpty (Topology.CWComplex.cell (Set.univ : Set Z) n) :=
    (inferInstance : CWComplex.Finite (Set.univ : Set Z)).eventually_isEmpty_cell
  -- Convert the eventual vanishing package from `CWComplex.Finite` into an explicit cutoff.
  simpa [Filter.eventually_atTop, ge_iff_le] using hfinite

/-- Helper for Problem 10.8.5: the ambient space `Z` and its whole-space subtype
`(Set.univ : Set Z)` have the same singular-homology Euler characteristic over any field. -/
theorem fieldTopologicalSingularHomologyEulerChar_eq_wholeSpaceSubtype
    {Z : Type u} [TopologicalSpace Z] (k : Type w) [Field k] :
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of Z) =
      fieldTopologicalSingularHomologyEulerChar k (TopCat.of (Set.univ : Set Z)) := by
  -- The canonical homeomorphism `Set.univ ≃ Z` lets homotopy invariance transport the Euler
  -- characteristic from the ambient space to the whole-space subtype owner.
  symm
  simpa using
    singularHomologyEulerChar_eq_of_homotopyEquiv
      (X := (Set.univ : Set Z)) (Y := Z) (k := k)
      (Homeomorph.Set.univ Z).toHomotopyEquiv

/-- Helper for Problem 10.8.5: an Euler-characteristic comparison on the ambient space `Z`
immediately transports to the whole-space subtype `(Set.univ : Set Z)`. -/
theorem fieldTopologicalSingularHomologyEulerChar_eq_modelOnWholeSpaceSubtype
    {Z : Type u} [TopologicalSpace Z] (k : Type w) [Field k]
    {K : ChainComplex (ModuleCat.{max u w} k) ℕ}
    (hComparison :
      fieldTopologicalSingularHomologyEulerChar k (TopCat.of Z) =
        HomologicalComplex.homologyEulerChar K) :
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of (Set.univ : Set Z)) =
      HomologicalComplex.homologyEulerChar K := by
  -- First change owners from `Z` to `(Set.univ : Set Z)`, then reuse the given comparison.
  calc
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of (Set.univ : Set Z)) =
        fieldTopologicalSingularHomologyEulerChar k (TopCat.of Z) := by
      symm
      exact fieldTopologicalSingularHomologyEulerChar_eq_wholeSpaceSubtype (Z := Z) (k := k)
    _ = HomologicalComplex.homologyEulerChar K := hComparison

/-- Helper for Problem 10.8.5: any whole-space chain complex carrying the expected Euler/support
package has the same homological Euler characteristic as the fixed counting complex. -/
theorem homologyEulerChar_eq_countingComplex_of_wholeSpaceEulerPackage
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    [CWComplex.Finite (Set.univ : Set Z)] (k : Type w) [Field k]
    {A : ChainComplex (ModuleCat.{max u w} k) ℕ} [∀ n : ℕ, A.HasHomology n] {N : ℕ}
    (hN : ∀ n ≥ N, IsEmpty (Topology.CWComplex.cell (Set.univ : Set Z) n))
    (hEuler : HomologicalComplex.eulerChar A = HomologicalComplex.homologyEulerChar A)
    (hSupport : GradedObject.finrankSupport A.X ⊆ Finset.range N)
    (hFinrank :
      ∀ n : ℕ, Module.finrank k (A.X n) = Nat.card (Topology.CWComplex.cell (Set.univ : Set Z) n)) :
    HomologicalComplex.homologyEulerChar A =
      HomologicalComplex.homologyEulerChar (wholeSpaceCellCountingComplex (Z := Z) k) := by
  -- Normalize the honest model and the fixed counting complex to the same alternating cutoff sum.
  calc
    HomologicalComplex.homologyEulerChar A =
        Finset.sum (Finset.range N) fun n ↦
          (Int.negOnePow n : ℤ) * Nat.card (Topology.CWComplex.cell (Set.univ : Set Z) n) :=
      homologyEulerChar_eq_sum_range_of_eulerCharOnSubset
        (C := (Set.univ : Set Z)) (k := k) A hEuler hSupport hFinrank
    _ = HomologicalComplex.homologyEulerChar (wholeSpaceCellCountingComplex (Z := Z) k) := by
      symm
      exact wholeSpaceCellCountingComplexHomologyEulerChar_eq_sum_range_of_isEmpty_cell
        (Z := Z) (k := k) hN

/-- Helper for Problem 10.8.5: the remaining geometric frontier is an honest field-valued
cellular model on the whole-space subtype owner whose homological Euler characteristic computes
singular homology and whose chain ranks are the cell counts. -/
theorem existsWholeSpaceActualCellularEulerPackage
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    [CWComplex.Finite (Set.univ : Set Z)] (k : Type w) [Field k] {N : ℕ}
    (hN : ∀ n ≥ N, IsEmpty (Topology.CWComplex.cell (Set.univ : Set Z) n)) :
    ∃ A : ChainComplex (ModuleCat.{max u w} k) ℕ,
      fieldTopologicalSingularHomologyEulerChar k (TopCat.of (Set.univ : Set Z)) =
        HomologicalComplex.homologyEulerChar A ∧
      HomologicalComplex.eulerChar A = HomologicalComplex.homologyEulerChar A ∧
      GradedObject.finrankSupport A.X ⊆ Finset.range N ∧
      (∀ n : ℕ,
        Module.finrank k (A.X n) =
          Nat.card (Topology.CWComplex.cell (Set.univ : Set Z) n)) := by
  -- TODO for Problem 10.8.5: supply the honest whole-space cellular chain model on
  -- `TopCat.of (Set.univ : Set Z)` and its singular-to-cellular Euler comparison package.
  sorry

/-- Helper for Problem 10.8.5: once the honest whole-space subtype model is available, singular
homology on that subtype owner agrees with the fixed counting complex. -/
theorem wholeSpaceSubtypeSingularHomologyEulerChar_eq_countingComplex_of_cutoff
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    [CWComplex.Finite (Set.univ : Set Z)] (k : Type w) [Field k] {N : ℕ}
    (hN : ∀ n ≥ N, IsEmpty (Topology.CWComplex.cell (Set.univ : Set Z) n)) :
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of (Set.univ : Set Z)) =
      HomologicalComplex.homologyEulerChar (wholeSpaceCellCountingComplex (Z := Z) k) := by
  rcases existsWholeSpaceActualCellularEulerPackage (Z := Z) (k := k) hN with
    ⟨A, hComparison, hEuler, hSupport, hFinrank⟩
  -- Compare the honest subtype-owner model and the counting complex through the shared cutoff sum.
  calc
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of (Set.univ : Set Z)) =
        HomologicalComplex.homologyEulerChar A := hComparison
    _ = HomologicalComplex.homologyEulerChar (wholeSpaceCellCountingComplex (Z := Z) k) :=
      homologyEulerChar_eq_countingComplex_of_wholeSpaceEulerPackage
        (Z := Z) (k := k) hN hEuler hSupport hFinrank

/-- Helper for Problem 10.8.5: once singular homology is compared with the fixed whole-space
counting complex, the full Euler/support/rank package follows from the counting complex spec. -/
theorem existsWholeSpaceFieldEulerModel_of_countingComplexComparison
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    [CWComplex.Finite (Set.univ : Set Z)] (k : Type w) [Field k] {N : ℕ}
    (hN : ∀ n ≥ N, IsEmpty (Topology.CWComplex.cell (Set.univ : Set Z) n))
    (hComparison :
      fieldTopologicalSingularHomologyEulerChar k (TopCat.of Z) =
        HomologicalComplex.homologyEulerChar (wholeSpaceCellCountingComplex (Z := Z) k)) :
    ∃ K : ChainComplex (ModuleCat.{max u w} k) ℕ,
      fieldTopologicalSingularHomologyEulerChar k (TopCat.of Z) =
        HomologicalComplex.homologyEulerChar K ∧
      HomologicalComplex.eulerChar K = HomologicalComplex.homologyEulerChar K ∧
      GradedObject.finrankSupport K.X ⊆ Finset.range N ∧
      (∀ n : ℕ,
        Module.finrank k (K.X n) =
          Nat.card (Topology.CWComplex.cell (Set.univ : Set Z) n)) := by
  obtain ⟨hEuler, hSupport, hFinrank⟩ :=
    wholeSpaceCellCountingComplexSpec (Z := Z) (k := k) hN
  -- The explicit counting complex already carries the complete algebraic package advertised here.
  exact ⟨wholeSpaceCellCountingComplex (Z := Z) k, hComparison, hEuler, hSupport, hFinrank⟩

/-- Helper for Problem 10.8.5: an honest whole-space field-valued cellular model should compare
the singular-homology Euler characteristic of `Z` with a chain complex whose graded ranks are the
whole-space cell counts below the cutoff `N`. -/
theorem existsWholeSpaceFieldEulerModel
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    [CWComplex.Finite (Set.univ : Set Z)] (k : Type w) [Field k] {N : ℕ}
    (hN : ∀ n ≥ N, IsEmpty (Topology.CWComplex.cell (Set.univ : Set Z) n)) :
    ∃ K : ChainComplex (ModuleCat.{max u w} k) ℕ,
      fieldTopologicalSingularHomologyEulerChar k (TopCat.of Z) =
        HomologicalComplex.homologyEulerChar K ∧
      HomologicalComplex.eulerChar K = HomologicalComplex.homologyEulerChar K ∧
      GradedObject.finrankSupport K.X ⊆ Finset.range N ∧
      (∀ n : ℕ,
        Module.finrank k (K.X n) =
          Nat.card (Topology.CWComplex.cell (Set.univ : Set Z) n)) := by
  -- Route correction: first prove the subtype-owner counting-complex comparison, then package the
  -- public witness through the counting complex's already-proved algebraic spec.
  refine existsWholeSpaceFieldEulerModel_of_countingComplexComparison (Z := Z) (k := k) hN ?_
  -- Transport singular homology from the ambient space to the subtype owner before using the
  -- subtype-owner counting-complex comparison.
  calc
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of Z) =
        fieldTopologicalSingularHomologyEulerChar k (TopCat.of (Set.univ : Set Z)) := by
      exact fieldTopologicalSingularHomologyEulerChar_eq_wholeSpaceSubtype (Z := Z) (k := k)
    _ = HomologicalComplex.homologyEulerChar (wholeSpaceCellCountingComplex (Z := Z) k) :=
      wholeSpaceSubtypeSingularHomologyEulerChar_eq_countingComplex_of_cutoff
        (Z := Z) (k := k) hN

/-- Helper for Problem 10.8.5: once singular homology is identified with the explicit
whole-space counting complex, the full whole-space Euler-comparison package follows from the
already-isolated algebraic spec of that complex. -/
theorem existsCellularFieldEulerComparisonOnWholeSpace_of_countingComplexComparison
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    [CWComplex.Finite (Set.univ : Set Z)] (k : Type w) [Field k] {N : ℕ}
    (hN : ∀ n ≥ N, IsEmpty (Topology.CWComplex.cell (Set.univ : Set Z) n))
    (hComparison :
      fieldTopologicalSingularHomologyEulerChar k (TopCat.of Z) =
        HomologicalComplex.homologyEulerChar (wholeSpaceCellCountingComplex (Z := Z) k)) :
    ∃ K : ChainComplex (ModuleCat.{max u w} k) ℕ,
      fieldTopologicalSingularHomologyEulerChar k (TopCat.of Z) =
        HomologicalComplex.homologyEulerChar K ∧
      HomologicalComplex.eulerChar K = HomologicalComplex.homologyEulerChar K ∧
      GradedObject.finrankSupport K.X ⊆ Finset.range N ∧
      (∀ n : ℕ,
        Module.finrank k (K.X n) =
          Nat.card (Topology.CWComplex.cell (Set.univ : Set Z) n)) := by
  -- Reuse the already-isolated counting-complex packaging theorem.
  simpa using
    existsWholeSpaceFieldEulerModel_of_countingComplexComparison
      (Z := Z) (k := k) hN hComparison

/-- Helper for Problem 10.8.5: a finite whole-space CW owner admits a genuine field-valued
cellular chain model whose homology Euler characteristic agrees with singular homology. -/
theorem existsCellularFieldEulerComparisonOnWholeSpace
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    [CWComplex.Finite (Set.univ : Set Z)] (k : Type w) [Field k] {N : ℕ}
    (hN : ∀ n ≥ N, IsEmpty (Topology.CWComplex.cell (Set.univ : Set Z) n)) :
    ∃ K : ChainComplex (ModuleCat.{max u w} k) ℕ,
      fieldTopologicalSingularHomologyEulerChar k (TopCat.of Z) =
        HomologicalComplex.homologyEulerChar K ∧
      HomologicalComplex.eulerChar K = HomologicalComplex.homologyEulerChar K ∧
      GradedObject.finrankSupport K.X ⊆ Finset.range N ∧
      (∀ n : ℕ,
        Module.finrank k (K.X n) =
          Nat.card (Topology.CWComplex.cell (Set.univ : Set Z) n)) := by
  -- Route correction: the primitive whole-space input is now the honest field-valued cellular
  -- model, not a comparison with the zero-differential counting complex.
  simpa using
    existsWholeSpaceFieldEulerModel (Z := Z) (k := k) hN

/-- Helper for Problem 10.8.5: once the honest singular-to-cellular comparison is available on
the whole-space owner, singular-homology Euler characteristic rewrites to the same finite
alternating cell-count sum as the explicit counting complex. -/
theorem fieldTopologicalSingularHomologyEulerChar_eq_sum_range_of_isEmpty_cell_onWholeSpace_direct
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    [CWComplex.Finite (Set.univ : Set Z)] (k : Type w) [Field k] {N : ℕ}
    (hN : ∀ n ≥ N, IsEmpty (Topology.CWComplex.cell (Set.univ : Set Z) n)) :
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of Z) =
      Finset.sum (Finset.range N) fun n ↦
        (Int.negOnePow n : ℤ) * Nat.card (Topology.CWComplex.cell (Set.univ : Set Z) n) := by
  rcases existsCellularFieldEulerComparisonOnWholeSpace (Z := Z) (k := k) hN with
    ⟨K, hComparison, hEuler, hSupport, hFinrank⟩
  have hComparisonSubtype :
      fieldTopologicalSingularHomologyEulerChar k (TopCat.of (Set.univ : Set Z)) =
        HomologicalComplex.homologyEulerChar K := by
    -- Transport the ambient-space comparison to the whole-space subtype owner once and for all.
    exact
      fieldTopologicalSingularHomologyEulerChar_eq_modelOnWholeSpaceSubtype
        (Z := Z) (k := k) hComparison
  -- Once the existential comparison package is available, the generic subset normalizer computes
  -- the singular-homology Euler characteristic from the same alternating whole-space cell-count
  -- sum.
  calc
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of Z) =
        fieldTopologicalSingularHomologyEulerChar k (TopCat.of (Set.univ : Set Z)) := by
      exact fieldTopologicalSingularHomologyEulerChar_eq_wholeSpaceSubtype (Z := Z) (k := k)
    _ =
        Finset.sum (Finset.range N) fun n ↦
          (Int.negOnePow n : ℤ) * Nat.card (Topology.CWComplex.cell (Set.univ : Set Z) n) :=
      fieldTopologicalSingularHomologyEulerChar_eq_sum_range_of_modelOnSubset
        (C := (Set.univ : Set Z)) (k := k) K hComparisonSubtype hEuler hSupport hFinrank

/-- Helper for Problem 10.8.5: once both whole-space owners are rewritten using the same cutoff,
the singular-homology Euler characteristic agrees with the fixed counting complex. -/
theorem wholeSpaceSingularHomologyEulerChar_eq_countingComplex_of_cutoff
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    [CWComplex.Finite (Set.univ : Set Z)] (k : Type w) [Field k] {N : ℕ}
    (hN : ∀ n ≥ N, IsEmpty (Topology.CWComplex.cell (Set.univ : Set Z) n)) :
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of Z) =
      HomologicalComplex.homologyEulerChar (wholeSpaceCellCountingComplex (Z := Z) k) := by
  -- Compare both sides to the same alternating finite cell-count sum cut off at `N`.
  calc
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of Z) =
        Finset.sum (Finset.range N) fun n ↦
          (Int.negOnePow n : ℤ) * Nat.card (Topology.CWComplex.cell (Set.univ : Set Z) n) :=
      fieldTopologicalSingularHomologyEulerChar_eq_sum_range_of_isEmpty_cell_onWholeSpace_direct
        (Z := Z) (k := k) hN
    _ = HomologicalComplex.homologyEulerChar (wholeSpaceCellCountingComplex (Z := Z) k) := by
      symm
      exact wholeSpaceCellCountingComplexHomologyEulerChar_eq_sum_range_of_isEmpty_cell
        (Z := Z) (k := k) hN

/-- Helper for Problem 10.8.5: the only remaining whole-space frontier is the comparison between
singular homology and the fixed whole-space cell-counting complex. -/
theorem wholeSpaceSingularHomologyEulerChar_eq_countingComplex
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    [CWComplex.Finite (Set.univ : Set Z)] (k : Type w) [Field k] :
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of Z) =
      HomologicalComplex.homologyEulerChar (wholeSpaceCellCountingComplex (Z := Z) k) := by
  rcases existsWholeSpaceCellCutoff (Z := Z) with ⟨N, hN⟩
  -- Once the common cutoff is chosen, both Euler characteristics are already normalized.
  exact wholeSpaceSingularHomologyEulerChar_eq_countingComplex_of_cutoff (Z := Z) (k := k) hN

/-- Helper for Problem 10.8.5: singular-homology Euler characteristic on a finite whole-space CW
owner agrees with the Chapter 10 CW Euler characteristic of that owner. -/
theorem wholeSpaceSingularHomologyEulerChar_eq_cwEulerCharacteristic
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    [CWComplex.Finite (Set.univ : Set Z)] (k : Type w) [Field k] :
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of Z) = χ((Set.univ : Set Z)) := by
  rcases existsWholeSpaceCellCutoff (Z := Z) with ⟨N, hN⟩
  -- Compare singular homology and `χ` to the same alternating finite cell-count sum cut off at
  -- `N`.
  calc
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of Z) =
        Finset.sum (Finset.range N) fun n ↦
          (Int.negOnePow n : ℤ) * Nat.card (Topology.CWComplex.cell (Set.univ : Set Z) n) :=
      fieldTopologicalSingularHomologyEulerChar_eq_sum_range_of_isEmpty_cell_onWholeSpace_direct
        (Z := Z) (k := k) hN
    _ = χ((Set.univ : Set Z)) := by
      symm
      exact cwEulerCharacteristic_eq_sum_range_of_isEmpty_cell
        (C := (Set.univ : Set Z)) hN

/-- Helper for Problem 10.8.5: once the whole-space cellular comparison package is available,
the singular-homology Euler characteristic matches the alternating whole-space cell-count sum. -/
theorem fieldTopologicalSingularHomologyEulerChar_eq_sum_range_of_isEmpty_cell_onWholeSpace
    {Z : Type u} [TopologicalSpace Z] [CWComplex (Set.univ : Set Z)]
    [CWComplex.Finite (Set.univ : Set Z)] (k : Type w) [Field k] {N : ℕ}
    (hN : ∀ n ≥ N, IsEmpty (Topology.CWComplex.cell (Set.univ : Set Z) n)) :
    fieldTopologicalSingularHomologyEulerChar k (TopCat.of Z) =
      Finset.sum (Finset.range N) fun n ↦
        (Int.negOnePow n : ℤ) * Nat.card (Topology.CWComplex.cell (Set.univ : Set Z) n) := by
  -- This public whole-space normalizer is exactly the direct finite-sum frontier isolated above.
  exact
    fieldTopologicalSingularHomologyEulerChar_eq_sum_range_of_isEmpty_cell_onWholeSpace_direct
      (Z := Z) (k := k) hN

/-- Helper for Problem 10.8.5: transporting a finite CW structure on the subtype owner
`(Set.univ : Set C)` back to the original subset owner preserves the degreewise cell counts. -/
theorem transportedCellCard_eq_originalCellCard
    {X : Type u} [TopologicalSpace X] {C : Set X} [CWComplex C]
    (cw : CWComplex (Set.univ : Set C))
    (hcell : ∀ n : ℕ, cw.cell n ≃ Topology.CWComplex.cell C n) :
    ∀ n : ℕ, Nat.card (cw.cell n) = Nat.card (Topology.CWComplex.cell C n) := by
  intro n
  -- Degreewise equivalence of cell-indexing types preserves finite cardinality.
  exact Nat.card_congr (hcell n)

/-- Helper for Problem 10.8.5: the remaining missing premise is a field-valued cellular chain
model on the subtype space `C` whose homology computes singular homology and whose chain-group
ranks are the CW cell counts below the chosen cutoff. -/
theorem existsCellularFieldEulerComparisonOnSubset
    {X : Type u} [TopologicalSpace X] {C : Set X} [CWComplex C] [CWComplex.Finite C]
    (k : Type w) [Field k] {N : ℕ} (hN : ∀ n ≥ N, IsEmpty (Topology.CWComplex.cell C n)) :
    ∃ K : ChainComplex (ModuleCat.{max u w} k) ℕ,
      fieldTopologicalSingularHomologyEulerChar k (TopCat.of C) =
        HomologicalComplex.homologyEulerChar K ∧
      HomologicalComplex.eulerChar K = HomologicalComplex.homologyEulerChar K ∧
      GradedObject.finrankSupport K.X ⊆ Finset.range N ∧
      (∀ n : ℕ, Module.finrank k (K.X n) = Nat.card (Topology.CWComplex.cell C n)) := by
  -- Route correction: first replace the ambient-subset owner by a whole-space CW structure on the
  -- subtype type `C`; the remaining blocker should then be the singular-to-cellular comparison in
  -- that canonical whole-space owner.
  obtain ⟨cw, hfinite, hcell⟩ := existsSubtypeUnivFiniteCWStructure (C := C)
  letI : CWComplex (Set.univ : Set C) := cw
  letI : CWComplex.Finite (Set.univ : Set C) := hfinite
  let hcell := Classical.choice hcell
  have hNSubtype : ∀ n ≥ N, IsEmpty (cw.cell n) := by
    intro n hn
    -- Transport the cutoff along the degreewise identification of cell indexing types.
    exact (hcell n).isEmpty_congr.mpr (hN n hn)
  rcases existsCellularFieldEulerComparisonOnWholeSpace (Z := C) (k := k) hNSubtype with
    ⟨K, hComparisonSubtype, hEuler, hSupport, hFinrankSubtype⟩
  refine ⟨K, ?_, hEuler, hSupport, ?_⟩
  · -- The whole-space comparison on the subtype type `C` already targets the needed singular
    -- homology owner.
    exact hComparisonSubtype
  · intro n
    -- The whole-space model already computes the subtype-owner cell counts, which are identified
    -- degreewise with the original subset-owner cells by `hcell`.
    calc
      Module.finrank k (K.X n) = Nat.card (cw.cell n) := by
        simpa using hFinrankSubtype n
      _ = Nat.card (Topology.CWComplex.cell C n) :=
        transportedCellCard_eq_originalCellCard (cw := cw) hcell n

/-- Helper for Problem 10.8.5: once singular homology on `C` is rewritten using a fixed cutoff
`N`, the Chapter 10 Euler characteristic matches it by the same alternating cell-count sum. -/
theorem finiteCWEulerCharacteristic_eq_fieldTopologicalSingularHomologyEulerChar_of_cutoff
    {X : Type u} [TopologicalSpace X] {C : Set X} [CWComplex C] [CWComplex.Finite C] {N : ℕ}
    (hN : ∀ n ≥ N, IsEmpty (Topology.CWComplex.cell C n))
    (hField :
      fieldTopologicalSingularHomologyEulerChar ℚ (TopCat.of C) =
        Finset.sum (Finset.range N) fun n ↦
          (Int.negOnePow n : ℤ) * Nat.card (Topology.CWComplex.cell C n)) :
    χ(C) = fieldTopologicalSingularHomologyEulerChar ℚ (TopCat.of C) := by
  -- Rewrite the CW Euler characteristic using the same cutoff that already computes homology.
  rw [cwEulerCharacteristic_eq_sum_range_of_isEmpty_cell (C := C) hN]
  exact hField.symm

/-- Helper for Problem 10.8.5: for a finite CW subset, the Chapter 10 Euler characteristic agrees
with the Euler characteristic of singular homology with rational coefficients. -/
theorem finiteCWEulerCharacteristic_eq_fieldTopologicalSingularHomologyEulerChar
    {X : Type u} [TopologicalSpace X] {C : Set X} [CWComplex C] [CWComplex.Finite C] :
    χ(C) = fieldTopologicalSingularHomologyEulerChar ℚ (TopCat.of C) := by
  have hfinite : ∀ᶠ n in Filter.atTop, IsEmpty (Topology.CWComplex.cell C n) :=
    (inferInstance : CWComplex.Finite C).eventually_isEmpty_cell
  simp_rw [Filter.eventually_atTop, ge_iff_le] at hfinite
  rcases hfinite with ⟨N, hN⟩
  rcases existsCellularFieldEulerComparisonOnSubset (C := C) (k := ℚ) hN with
    ⟨K, hComparison, hEuler, hSupport, hFinrank⟩
  -- Collapse the remaining calculation to the shared alternating cell-count sum coming from `K`.
  exact
    finiteCWEulerCharacteristic_eq_fieldTopologicalSingularHomologyEulerChar_of_cutoff
      (C := C) hN
      (fieldTopologicalSingularHomologyEulerChar_eq_sum_range_of_modelOnSubset
        (C := C) (k := ℚ) K hComparison hEuler hSupport hFinrank)

/-- Problem 10.8.5. The Euler characteristic of a finite CW complex depends only on its homotopy
type. In particular, a homotopy equivalence between finite CW complexes preserves
`χ(-)`, so for a fixed space it does not depend on the chosen finite cell decomposition. -/
theorem cwEulerCharacteristic_eq_of_homotopyEquiv
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {C : Set X} {D : Set Y}
    [CWComplex C] [CWComplex.Finite C] [CWComplex D] [CWComplex.Finite D] (h : C ≃ₕ D) :
    χ(C) = χ(D) := by
  -- Route correction: rewrite each CW Euler characteristic to singular homology on the same
  -- subtype owner, then apply mixed-universe homotopy invariance there.
  calc
    χ(C) = fieldTopologicalSingularHomologyEulerChar ℚ (TopCat.of C) :=
      finiteCWEulerCharacteristic_eq_fieldTopologicalSingularHomologyEulerChar (C := C)
    _ = fieldTopologicalSingularHomologyEulerChar ℚ (TopCat.of D) :=
      singularHomologyEulerChar_eq_of_homotopyEquivMixed (k := ℚ) h
    _ = χ(D) := by
      symm
      exact finiteCWEulerCharacteristic_eq_fieldTopologicalSingularHomologyEulerChar (C := D)

namespace Topology.CWComplex

/-- The explicit-structure Euler characteristic is definitionally the source-facing owner `χ(C)`.
-/
@[simp] theorem eulerCharacteristic_eq_cwEulerCharacteristic
    {X : Type u} [TopologicalSpace X] {C : Set X} (c : CWComplex C)
    (hfinite : letI : CWComplex C := c; CWComplex.Finite C) :
    eulerCharacteristic c hfinite = χ(C) :=
  rfl

/-- An explicit finite CW structure preserves its Euler characteristic along a homotopy
equivalence. -/
theorem eulerCharacteristic_eq_of_homotopyEquiv
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {C : Set X} {D : Set Y} (cC : CWComplex C)
    (hC : letI : CWComplex C := cC; CWComplex.Finite C) (cD : CWComplex D)
    (hD : letI : CWComplex D := cD; CWComplex.Finite D)
    (h : C ≃ₕ D) : eulerCharacteristic cC hC = eulerCharacteristic cD hD := by
  letI : CWComplex C := cC
  letI : CWComplex.Finite C := hC
  letI : CWComplex D := cD
  letI : CWComplex.Finite D := hD
  simpa using cwEulerCharacteristic_eq_of_homotopyEquiv h

/-- For a fixed underlying subset, the Euler characteristic attached to an explicit finite CW
structure is independent of the chosen finite cell decomposition. -/
theorem eulerCharacteristic_eq_of_sameSpace
    {X : Type u} [TopologicalSpace X] {C : Set X} (c₁ : CWComplex C)
    (h₁ : letI : CWComplex C := c₁; CWComplex.Finite C) (c₂ : CWComplex C)
    (h₂ : letI : CWComplex C := c₂; CWComplex.Finite C) :
    eulerCharacteristic c₁ h₁ = eulerCharacteristic c₂ h₂ := by
  simpa using
    eulerCharacteristic_eq_of_homotopyEquiv c₁ h₁ c₂ h₂ (ContinuousMap.HomotopyEquiv.refl C)

end Topology.CWComplex
