import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.CWApproximation
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.GammaRealization
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_6_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Remark_9_4_13.BasepointTransport
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.ZerothHomotopyMap
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Topology.Homotopy.HomotopyGroup
open CategoryTheory Limits
open scoped ContinuousMap
open scoped Simplicial Topology Topology.Homotopy

universe u

noncomputable section

-- Semantic recall via `lean_leansearch`: no pre-existing CW-approximation theorem surfaced in the
-- local environment. Chapter 10 therefore records a chosen approximation by the source-facing
-- owner `CWApproximation X`, whose field `isCWApproximation` packages both the CW structure on the
-- source and the weak equivalence condition on the comparison map.

/-- Helper for Theorem 10.5.1: a CW model `Γ`, a comparison map `γ : C(Γ, X)`, and a
weak-equivalence witness on `γ` package into a chosen `CWApproximation X`. -/
lemma cwApproximationOfWitness {X : TopCat.{u}}
    (h :
      ∃ (Γ : TopCat.{u}) (_ : TopCat.CWComplex Γ) (γ : C(Γ, X)), IsWeakEquivalence γ) :
    Nonempty (CWApproximation.{u, u} X) := by
  -- Unpack the chosen CW model and comparison map.
  rcases h with ⟨Γ, hΓ, γ, hγ⟩
  -- The approximation owner is exactly the pair of ambient witnesses already in hand.
  letI : IsWeakEquivalence γ := hγ
  refine ⟨@CWApproximation.mk.{u, u} X Γ γ ?_⟩
  exact IsCWApproximation.mk hΓ

section

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {e : C(Y, Z)}

/-- Helper for Theorem 10.5.1: all-degree HELP data yields the corresponding all-degree
two-stage homotopy-group owner. -/
theorem hasPiInjectiveSurjectiveSuccAllOfHasSphereConeHelpAll
    (hHelp : ∀ n : ℕ, HasSphereConeHelp n e) :
    ∀ n : ℕ, HasPiInjectiveSurjectiveSucc n e := by
  intro n
  -- Convert the HELP witness in degree `n` through Lemma 9.6.6 once and for all.
  exact (hHelp n).hasPiInjectiveSurjectiveSucc

/-- Helper for Theorem 10.5.1: a `0`-equivalence together with the canonical two-degree
homotopy-group control up through stage `n` upgrades to an `(n + 1)`-equivalence. -/
theorem isNEquivalenceSuccOfIsNEquivalenceZeroAndHasPiInjectiveSurjectiveSuccUpTo
    (h0 : IsNEquivalence 0 e) :
    ∀ n : ℕ, (∀ m : ℕ, m ≤ n → HasPiInjectiveSurjectiveSucc m e) → IsNEquivalence (n + 1) e := by
  intro n
  induction n with
  | zero =>
      intro hSteps
      refine ⟨?_, ?_⟩
      · intro y q hq
        -- In degree `< 1`, only `π₀` occurs, so the stage-`0` injectivity closes the goal.
        cases q with
        | zero =>
            simpa using (hSteps 0 le_rfl).injective y
        | succ q =>
            exact False.elim (Nat.not_lt_zero q (Nat.lt_of_succ_lt_succ hq))
      · intro y q hq
        -- Surjectivity up to degree `1` splits into the `π₀` base case and the stage-`0` successor.
        cases q with
        | zero =>
            simpa using h0.surjective y (show 0 ≤ 0 by simp)
        | succ q =>
            have hq0 : q = 0 := Nat.eq_zero_of_le_zero (Nat.succ_le_succ_iff.mp hq)
            subst hq0
            simpa using (hSteps 0 le_rfl).surjectiveSucc y
  | succ n ih =>
      intro hSteps
      have hPrev :
          IsNEquivalence (n + 1) e :=
        ih
          (fun m hm ↦ hSteps m (Nat.le_trans hm (Nat.le_succ _)))
      refine ⟨?_, ?_⟩
      · intro y q hq
        -- Degrees below `n + 2` are either already controlled by the previous stage or equal to
        -- the new boundary degree handled by the stage-`(n + 1)` hypothesis.
        rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq' | rfl
        · exact hPrev.injective y hq'
        · exact (hSteps (n + 1) le_rfl).injective y
      · intro y q hq
        -- Surjectivity up to `n + 2` is the same dichotomy: use the previous stage below the top
        -- degree and the stage-`(n + 1)` successor surjectivity at the new top degree.
        rcases Nat.eq_or_lt_of_le hq with rfl | hq'
        · exact (hSteps (n + 1) le_rfl).surjectiveSucc y
        · exact hPrev.surjective y (Nat.le_of_lt_succ hq')

/-- Helper for Theorem 10.5.1: a `0`-equivalence plus canonical two-degree control in every
degree upgrades to a weak equivalence. -/
theorem isWeakEquivalenceOfIsNEquivalenceZeroAndHasPiInjectiveSurjectiveSuccAll
    (h0 : IsNEquivalence 0 e)
    (hSteps : ∀ n : ℕ, HasPiInjectiveSurjectiveSucc n e) :
    IsWeakEquivalence e := by
  refine ⟨fun n ↦ ?_⟩
  -- Package the `n = 0` base case separately and use the inductive upgrade for positive degrees.
  cases n with
  | zero =>
      exact h0
  | succ n =>
      exact isNEquivalenceSuccOfIsNEquivalenceZeroAndHasPiInjectiveSurjectiveSuccUpTo h0 n
        (fun m _ ↦ hSteps m)

/-- Helper for Theorem 10.5.1: HELP data in every degree upgrades a `0`-equivalence to a weak
equivalence. -/
theorem isWeakEquivalenceOfIsNEquivalenceZeroAndHasSphereConeHelpAll
    (h0 : IsNEquivalence 0 e)
    (hHelp : ∀ n : ℕ, HasSphereConeHelp n e) :
    IsWeakEquivalence e := by
  -- Normalize the HELP hypotheses to the Chapter 9 two-degree owner before assembling the final
  -- weak-equivalence witness.
  exact
    isWeakEquivalenceOfIsNEquivalenceZeroAndHasPiInjectiveSurjectiveSuccAll h0
      (hasPiInjectiveSurjectiveSuccAllOfHasSphereConeHelpAll hHelp)

end

/-- Helper for Theorem 10.5.1: the comparison map `Γ X ⟶ X` given by the realization/singular-set
adjunction counit. -/
abbrev singularRealizationEvaluation (X : TopCat.{u}) : gammaRealization X ⟶ X :=
  sSetTopAdj.counit.app X

/-- Helper for Theorem 10.5.1: the adjoint transpose of the counit `Γ X ⟶ X` is the identity on
the singular simplicial set of `X`. -/
theorem singularRealizationEvaluation_spec (X : TopCat.{u}) :
    sSetTopAdj.homEquiv (TopCat.toSSet.obj X) X (singularRealizationEvaluation X) = 𝟙 _ := by
  -- Move the counit across the adjunction, where the right triangle identifies it with the
  -- identity of `TopCat.toSSet.obj X`.
  rw [Adjunction.homEquiv_unit]
  simpa [singularRealizationEvaluation] using sSetTopAdj.right_triangle_components X

/-- Helper for Theorem 10.5.1: the strict section `X → Γ X` obtained by realizing the constant
`0`-simplex at each point of `X`. -/
noncomputable def singularRealizationVertexSection (X : TopCat.{u}) : X → gammaRealization X :=
  fun x ↦
    SSet.toTop.map (SSet.const (TopCat.toSSetObj₀Equiv.symm x))
      (default : |(Δ[0] : SSet.{u})|)

/-- Helper for Theorem 10.5.1: under the canonical `π₀ ≃ ZerothHomotopy` identifications, the
degree-`0` map induced by the counit is the ordinary map on path components. -/
theorem singularRealizationEvaluation_piZero_commutes (X : TopCat.{u}) (x : gammaRealization X) :
    (HomotopyGroup.pi0EquivZerothHomotopy :
        π_ 0 X ((singularRealizationEvaluation X).hom x) ≃ ZerothHomotopy X).toFun ∘
        ((singularRealizationEvaluation X).hom).eStar 0 x =
      zerothHomotopyMap (singularRealizationEvaluation X).hom ∘
        (HomotopyGroup.pi0EquivZerothHomotopy :
          π_ 0 (gammaRealization X) x ≃ ZerothHomotopy (gammaRealization X)).toFun := by
  -- Both sides take a `π₀` class to the path component of the image endpoint under the counit.
  funext a
  refine Quotient.inductionOn a ?_
  intro γ
  rfl

/-- Helper for Theorem 10.5.1: postcomposition by a continuous map preserves generalized-loop
boundary conditions. -/
theorem genLoopMap_mem_boundary
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] (e : C(Y, Z))
    {q : ℕ} {y : Y} (γ : Ω^ (Fin q) Y y) :
    ∀ t ∈ Cube.boundary (Fin q), (e.comp γ.1) t = e y := by
  intro t ht
  -- Evaluate the generalized-loop boundary condition and then postcompose by `e`.
  simpa using congrArg e (γ.2 t ht)

/-- Helper for Theorem 10.5.1: postcomposition by a continuous map is a continuous map on the
generalized-loop model of homotopy groups. -/
noncomputable def genLoopSpacePostcomp
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] (e : C(Y, Z))
    (q : ℕ) (y : Y) :
    C(Ω^ (Fin q) Y y, Ω^ (Fin q) Z (e y)) where
  toFun γ := ⟨e.comp γ.1, genLoopMap_mem_boundary e γ⟩
  continuous_toFun :=
    Continuous.subtype_mk
      (e.continuous_postcomp.comp continuous_subtype_val)
      (fun γ ↦ genLoopMap_mem_boundary e γ)

/-- Helper for Theorem 10.5.1: under the quotient-model identification of `π_n` with path
components of generalized loops, the counit's induced map is postcomposition on loop
representatives. -/
theorem singularRealizationEvaluation_eStar_commutesGenLoop
    (X : TopCat.{u}) (n : ℕ) (x : gammaRealization X) :
    (homotopyGroupEquivZerothHomotopyGenLoop n (((singularRealizationEvaluation X).hom) x)).toFun ∘
        ((singularRealizationEvaluation X).hom).eStar n x =
      zerothHomotopyMap (genLoopSpacePostcomp ((singularRealizationEvaluation X).hom) n x) ∘
        (homotopyGroupEquivZerothHomotopyGenLoop n x).toFun := by
  funext a
  refine Quotient.inductionOn a ?_
  intro γ
  -- Both sides record the same postcomposed generalized loop in the path-component quotient.
  rfl

/-- Helper for Theorem 10.5.1: evaluating the realized constant `0`-simplex at `x` returns `x`
under the counit `Γ X ⟶ X`. -/
theorem singularRealizationVertexSection_spec (X : TopCat.{u}) (x : X) :
    ((singularRealizationEvaluation X).hom) (singularRealizationVertexSection X x) = x := by
  -- Transport the counit composite back across the adjunction, where it is the chosen constant
  -- `0`-simplex, and then compare the corresponding vertices.
  let σ : Δ[0] ⟶ TopCat.toSSet.obj X :=
    SSet.const (TopCat.toSSetObj₀Equiv.symm x)
  have hAdjoint :
      sSetTopAdj.homEquiv Δ[0] X
          (SSet.toTop.map σ ≫ singularRealizationEvaluation X) =
        SSet.const (TopCat.toSSetObj₀Equiv.symm x) := by
    have hNat :
        sSetTopAdj.homEquiv Δ[0] X
            (SSet.toTop.map σ ≫ singularRealizationEvaluation X) =
          σ ≫ (sSetTopAdj.homEquiv (TopCat.toSSet.obj X) X (singularRealizationEvaluation X)) := by
      simpa using
        (sSetTopAdj.homEquiv_naturality_left
          (X' := Δ[0]) (X := TopCat.toSSet.obj X) (Y := X)
          σ (singularRealizationEvaluation X))
    simpa [σ, singularRealizationEvaluation_spec] using hNat
  have hConst :
      (SSet.const
          (TopCat.toSSetObj₀Equiv.symm
            (((singularRealizationEvaluation X).hom) (singularRealizationVertexSection X x))) :
          Δ[0] ⟶ TopCat.toSSet.obj X) =
        (SSet.const (TopCat.toSSetObj₀Equiv.symm x) : Δ[0] ⟶ TopCat.toSSet.obj X) := by
    simpa [singularRealizationVertexSection, σ, singularRealizationEvaluation,
      sSetTopAdj_homEquiv_stdSimplex_zero] using hAdjoint
  have hValue :
      TopCat.toSSetObj₀Equiv.symm
          (((singularRealizationEvaluation X).hom) (singularRealizationVertexSection X x)) =
        TopCat.toSSetObj₀Equiv.symm x := by
    have hSymm :
        SSet.yonedaEquiv.symm
            (TopCat.toSSetObj₀Equiv.symm
              (((singularRealizationEvaluation X).hom) (singularRealizationVertexSection X x))) =
          SSet.yonedaEquiv.symm (TopCat.toSSetObj₀Equiv.symm x) := by
      simpa using hConst
    exact SSet.yonedaEquiv.symm.injective hSymm
  exact TopCat.toSSetObj₀Equiv.symm.injective hValue

/-- Helper for Theorem 10.5.1: the counit `Γ X ⟶ X` is surjective on path components. -/
theorem singularRealizationEvaluation_surjective_zerothHomotopy (X : TopCat.{u}) :
    Function.Surjective (zerothHomotopyMap (singularRealizationEvaluation X).hom) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  refine ⟨⟦singularRealizationVertexSection X x⟧, ?_⟩
  -- The vertex section is a strict pointwise section of the counit.
  rw [zerothHomotopyMap_mk]
  rw [singularRealizationVertexSection_spec]

/-- Helper for Theorem 10.5.1: the counit `Γ X ⟶ X` is a `0`-equivalence. -/
theorem singularRealizationEvaluation_isNEquivalenceZero (X : TopCat.{u}) :
    IsNEquivalence 0 (singularRealizationEvaluation X).hom := by
  refine ⟨?_, ?_⟩
  · intro x q hq
    -- Degrees below `0` are impossible, so injectivity is vacuous.
    exact False.elim (Nat.not_lt_zero _ hq)
  · intro x q hq
    have hq0 : q = 0 := Nat.eq_zero_of_le_zero hq
    subst hq0
    -- Transport the `π₀` surjectivity statement through the canonical path-component equivalences.
    intro a
    let eDom :
        π_ 0 (gammaRealization X) x ≃ ZerothHomotopy (gammaRealization X) :=
      HomotopyGroup.pi0EquivZerothHomotopy
    let eCod :
        π_ 0 X (((singularRealizationEvaluation X).hom) x) ≃ ZerothHomotopy X :=
      HomotopyGroup.pi0EquivZerothHomotopy
    rcases singularRealizationEvaluation_surjective_zerothHomotopy X (eCod a) with ⟨b, hb⟩
    refine ⟨eDom.symm b, ?_⟩
    apply eCod.injective
    have hComm :
        eCod (((singularRealizationEvaluation X).hom).eStar 0 x (eDom.symm b)) =
          zerothHomotopyMap (singularRealizationEvaluation X).hom b := by
      have hComm' :
          eCod (((singularRealizationEvaluation X).hom).eStar 0 x (eDom.symm b)) =
            zerothHomotopyMap (singularRealizationEvaluation X).hom (eDom (eDom.symm b)) := by
        simpa [eDom, eCod] using
          congrArg (fun f ↦ f (eDom.symm b)) (singularRealizationEvaluation_piZero_commutes X x)
      rw [Equiv.apply_symm_apply] at hComm'
      exact hComm'
    exact hComm.trans hb

/-- Helper for Theorem 10.5.1: the comparison map from the realization of a finite singular
subcomplex to `X`. -/
abbrev finiteSingularRealizationEvaluation (X : TopCat.{u})
    (A : (TopCat.toSSet.obj X).Subcomplex) :
    SSet.toTop.obj A.toSSet ⟶ X :=
  SSet.toTop.map A.ι ≫ singularRealizationEvaluation X

/-- Helper for Theorem 10.5.1: enlarging a finite singular stage along a subcomplex inclusion
does not change the comparison map to `X`. -/
theorem finiteSingularRealizationEvaluation_comp_homOfLE (X : TopCat.{u})
    {A B : (TopCat.toSSet.obj X).Subcomplex} (hAB : A ≤ B) :
    SSet.toTop.map (SSet.Subcomplex.homOfLE hAB) ≫ finiteSingularRealizationEvaluation X B =
      finiteSingularRealizationEvaluation X A := by
  -- Normalize the enlarged finite-stage comparison by collapsing the subcomplex inclusion before
  -- composing with the counit.
  rw [finiteSingularRealizationEvaluation, ← Category.assoc, ← Functor.map_comp,
    SSet.Subcomplex.homOfLE_ι]

/-- Helper for Theorem 10.5.1: the union of two finite singular subcomplexes is still finite. -/
theorem finiteSingularSubcomplex_sup {X : TopCat.{u}}
    (A B : (TopCat.toSSet.obj X).Subcomplex) [SSet.Finite A] [SSet.Finite B] :
    SSet.Finite ((A ⊔ B : (TopCat.toSSet.obj X).Subcomplex)) := by
  classical
  let F : Bool → (TopCat.toSSet.obj X).Subcomplex := fun b ↦ cond b A B
  have hF : ∀ b, SSet.Finite (F b) := by
    intro b
    by_cases hb : b
    · simpa [F, hb] using (inferInstance : SSet.Finite A)
    · simpa [F, hb] using (inferInstance : SSet.Finite B)
  -- Package the binary union as a finite supremum indexed by `Bool`.
  have hFinite : SSet.Finite (⨆ b, F b : (TopCat.toSSet.obj X).Subcomplex) :=
    (SSet.finite_iSup_iff (A := F)).2 hF
  have hSup : (⨆ b, F b : (TopCat.toSSet.obj X).Subcomplex) =
      (A ⊔ B : (TopCat.toSSet.obj X).Subcomplex) := by
    rw [iSup_bool_eq]
    simp [F]
  rw [hSup] at hFinite
  exact hFinite

/-- Helper for Theorem 10.5.1: the supremum of finitely many finite singular subcomplexes is
still finite. -/
theorem finiteSingularSubcomplex_finsetSup {X : TopCat.{u}} {ι : Type*}
    (s : Finset ι) (A : ι → (TopCat.toSSet.obj X).Subcomplex)
    (hA : ∀ i ∈ s, SSet.Finite (A i)) :
    SSet.Finite (s.sup A : (TopCat.toSSet.obj X).Subcomplex) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty finite supremum is the bottom subcomplex.
      let B : SSet.{u} := ((⊥ : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u})
      letI : B.HasDimensionLT 0 := inferInstance
      exact SSet.finite_of_hasDimensionLT (X := B) 0
        (fun i hi ↦ False.elim (Nat.not_lt_zero _ hi))
  | @insert a s ha hs =>
      have hHead : SSet.Finite (A a) := hA a (Finset.mem_insert_self a s)
      have hTail : SSet.Finite (s.sup A : (TopCat.toSSet.obj X).Subcomplex) := by
        -- Restrict the induction hypothesis to the tail of the finite family.
        exact hs (fun i hi ↦ hA i (Finset.mem_insert_of_mem hi))
      letI : SSet.Finite (A a) := hHead
      letI : SSet.Finite (s.sup A : (TopCat.toSSet.obj X).Subcomplex) := hTail
      -- Rebuild the finite owner by adjoining the new head stage to the tail supremum.
      simpa [Finset.sup_insert, ha] using
        (finiteSingularSubcomplex_sup (A a) (s.sup A) :
          SSet.Finite ((A a ⊔ s.sup A : (TopCat.toSSet.obj X).Subcomplex)))

/-- Helper for Theorem 10.5.1: the union of three finite singular subcomplexes is still finite. -/
theorem finiteSingularSubcomplex_sup_sup {X : TopCat.{u}}
    (A B C : (TopCat.toSSet.obj X).Subcomplex)
    [SSet.Finite A] [SSet.Finite B] [SSet.Finite C] :
    SSet.Finite (((A ⊔ B : (TopCat.toSSet.obj X).Subcomplex) ⊔ C :
      (TopCat.toSSet.obj X).Subcomplex)) := by
  -- First merge two finite carriers, then add the remaining finite carrier on top.
  letI : SSet.Finite ((A ⊔ B : (TopCat.toSSet.obj X).Subcomplex)) :=
    finiteSingularSubcomplex_sup A B
  -- The second binary union finishes the three-stage finite enlargement.
  exact finiteSingularSubcomplex_sup (A ⊔ B : (TopCat.toSSet.obj X).Subcomplex) C

/-- Helper for Theorem 10.5.1: every point of `Γ X` comes from the realization of a finite
singular subcomplex of `TopCat.toSSet.obj X`. -/
theorem gammaRealizationPoint_mem_finiteSingularStage (X : TopCat.{u}) (x : gammaRealization X) :
    ∃ (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A })
      (a : SSet.toTop.obj A.1.toSSet),
        ((SSet.toTop.map A.1.ι).hom) a = x := by
  let diag :
      CategoryTheory.CostructuredArrow SSet.stdSimplex (TopCat.toSSet.obj X) ⥤ TopCat :=
    CategoryTheory.CostructuredArrow.proj SSet.stdSimplex (TopCat.toSSet.obj X) ⋙
      SimplexCategory.toTop
  let e :
      gammaRealization X ≅ CategoryTheory.Limits.colimit diag :=
    SSet.stdSimplex.leftKanExtensionObjIsoColimit
      (F := SimplexCategory.toTop) (X := TopCat.toSSet.obj X)
  let hcolim :
      CategoryTheory.Limits.IsColimit ((forget TopCat).mapCocone
        (CategoryTheory.Limits.colimit.cocone diag)) :=
    CategoryTheory.Limits.isColimitOfPreserves (forget TopCat)
      (CategoryTheory.Limits.colimit.isColimit diag)
  obtain ⟨p, y, hy⟩ := CategoryTheory.Limits.Types.jointly_surjective_of_isColimit
    (F := diag ⋙ forget TopCat)
    (t := (forget TopCat).mapCocone (CategoryTheory.Limits.colimit.cocone diag))
    hcolim (e.hom x)
  let A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A } :=
    ⟨SSet.Subcomplex.range p.hom, inferInstance⟩
  let z : SSet.toTop.obj (SSet.stdSimplex.obj p.left) :=
    (SSet.toTopSimplex.app p.left).inv y
  let a : SSet.toTop.obj A.1.toSSet :=
    SSet.toTop.map (SSet.Subcomplex.toRange p.hom) z
  have hColimitLeg :
      (SSet.toTopSimplex.inv.app p.left) ≫ SSet.toTop.map p.hom ≫ e.hom =
        CategoryTheory.Limits.colimit.ι diag p := by
    -- Rewrite the generic left-Kan colimit leg into the concrete realization-of-a-simplex form.
    simpa [diag, e, SSet.toTop, SSet.toTopSimplex] using
      (CategoryTheory.Functor.ι_leftKanExtensionObjIsoColimit_hom
        (L := SSet.stdSimplex) (F := SimplexCategory.toTop) (X := TopCat.toSSet.obj X) p)
  have hx :
      ((SSet.toTop.map p.hom).hom) z = x := by
    have heInj : Function.Injective e.hom := (TopCat.homeoOfIso e).injective
    apply heInj
    have hEval :
        (((SSet.toTopSimplex.inv.app p.left) ≫ SSet.toTop.map p.hom ≫ e.hom).hom) y =
          (CategoryTheory.Limits.colimit.ι diag p) y := by
      exact congrArg (fun f : SimplexCategory.toTop.obj p.left ⟶
          CategoryTheory.Limits.colimit diag ↦ f y) hColimitLeg
    have hy' : (CategoryTheory.Limits.colimit.ι diag p) y = e.hom x := by
      simpa [diag] using hy
    exact (by simpa [z] using hEval.trans hy')
  have ha :
      ((SSet.toTop.map A.1.ι).hom) a = ((SSet.toTop.map p.hom).hom) z := by
    -- Collapse the realization of the simplicial range factorization back to the original simplex.
    have hFactor :
        SSet.toTop.map (SSet.Subcomplex.toRange p.hom) ≫ SSet.toTop.map A.1.ι =
          SSet.toTop.map p.hom := by
      calc
        SSet.toTop.map (SSet.Subcomplex.toRange p.hom) ≫ SSet.toTop.map A.1.ι
            = SSet.toTop.map (SSet.Subcomplex.toRange p.hom ≫ A.1.ι) := by
                rw [← Functor.map_comp]
        _ = SSet.toTop.map p.hom := by
              simpa [A] using
                congrArg (fun ψ ↦ SSet.toTop.map ψ) (SSet.Subcomplex.toRange_ι p.hom)
    exact congrArg (fun f : SSet.toTop.obj (SSet.stdSimplex.obj p.left) ⟶ gammaRealization X ↦
      f z) hFactor
  exact ⟨A, a, ha.trans hx⟩

/-- Helper for Theorem 10.5.1: once the image of `f` lands in the realization of a subcomplex and
that realized inclusion is an embedding, `f` factors exactly through that realized stage. -/
theorem mapFactorsExactlyThroughRealizedSubcomplexOfRangeSubset
    {K : Type*} [TopologicalSpace K] (X : TopCat.{u})
    (A : (TopCat.toSSet.obj X).Subcomplex)
    (hEmbedding : Topology.IsEmbedding ((SSet.toTop.map A.ι).hom))
    (f : C(K, gammaRealization X))
    (hRange : Set.range f ⊆ Set.range ((SSet.toTop.map A.ι).hom)) :
    ∃ fA : C(K, SSet.toTop.obj A.toSSet), (SSet.toTop.map A.ι).hom.comp fA = f := by
  let i : SSet.toTop.obj A.toSSet → gammaRealization X := (SSet.toTop.map A.ι).hom
  let fRange : C(K, Set.range i) :=
    ⟨(Set.range i).codRestrict f (fun k ↦ hRange ⟨k, rfl⟩),
      f.continuous.codRestrict (fun k ↦ hRange ⟨k, rfl⟩)⟩
  let fA : C(K, SSet.toTop.obj A.toSSet) :=
    ⟨fun k ↦ hEmbedding.toHomeomorph.symm (fRange k),
      hEmbedding.toHomeomorph.symm.continuous_toFun.comp fRange.continuous⟩
  refine ⟨fA, ?_⟩
  ext k
  -- Pull the factorization back across the homeomorphism onto the realized image.
  exact congrArg Subtype.val (hEmbedding.toHomeomorph.apply_symm_apply (fRange k))

/-- Helper for Theorem 10.5.1: if a realized singular stage is compact and its inclusion into
`Γ X` is injective, then the inclusion is automatically a closed embedding. -/
theorem finiteSingularStageInclusion_isClosedEmbedding_of_compact_injective
    (X : TopCat.{u}) (A : (TopCat.toSSet.obj X).Subcomplex)
    [CompactSpace (SSet.toTop.obj A.toSSet)] [T2Space (gammaRealization X)]
    (hInj : Function.Injective ((SSet.toTop.map A.ι).hom)) :
    Topology.IsClosedEmbedding ((SSet.toTop.map A.ι).hom) := by
  -- The compact-domain/Hausdorff-codomain criterion packages the geometric input into the exact
  -- factorization interface used later.
  let _ : T2Space (SSet.toTop.obj (TopCat.toSSet.obj X)) := by
    simpa [gammaRealization] using (inferInstance : T2Space (gammaRealization X))
  exact Continuous.isClosedEmbedding ((SSet.toTop.map A.ι).hom).continuous hInj

/-- Helper for Theorem 10.5.1: realized inclusions of singular subcomplexes are injective. -/
theorem realizedSubcomplexInclusion_injective
    (X : TopCat.{u}) (A : (TopCat.toSSet.obj X).Subcomplex) :
    Function.Injective ((SSet.toTop.map A.ι).hom) := by
  -- Route correction: the missing bridge is not the injectivity statement itself but the
  -- realization-level mono-preservation API for simplicial subcomplex inclusions.
  -- TODO: prove that `SSet.toTop.map A.ι` is mono, then read off injectivity with
  -- `TopCat.mono_iff_injective`.
  sorry

/-- Helper for Theorem 10.5.1: realized inclusions of finite singular stages embed into `Γ X`.
-/
theorem finiteSingularStageInclusion_isEmbedding
    (X : TopCat.{u}) (A : (TopCat.toSSet.obj X).Subcomplex) [SSet.Finite A] :
    Topology.IsEmbedding ((SSet.toTop.map A.ι).hom) := by
  -- Route correction: separate the exact factorization interface from the missing compactness
  -- bridge for realizations of finite simplicial sets.
  -- TODO: prove `[SSet.Finite A] -> CompactSpace (SSet.toTop.obj A.toSSet)`, then upgrade the
  -- injective realized inclusion with
  -- `finiteSingularStageInclusion_isClosedEmbedding_of_compact_injective`.
  sorry

/-- Helper for Theorem 10.5.1: the exact range-subset factorization route also accepts a closed
embedding witness on the realized subcomplex inclusion. -/
theorem mapFactorsExactlyThroughRealizedSubcomplexOfClosedRangeSubset
    {K : Type*} [TopologicalSpace K] (X : TopCat.{u})
    (A : (TopCat.toSSet.obj X).Subcomplex)
    (hClosedEmbedding : Topology.IsClosedEmbedding ((SSet.toTop.map A.ι).hom))
    (f : C(K, gammaRealization X))
    (hRange : Set.range f ⊆ Set.range ((SSet.toTop.map A.ι).hom)) :
    ∃ fA : C(K, SSet.toTop.obj A.toSSet), (SSet.toTop.map A.ι).hom.comp fA = f := by
  -- Forget the extra closed-image information and reuse the embedding-level exact factorization.
  exact
    mapFactorsExactlyThroughRealizedSubcomplexOfRangeSubset
      (X := X) A hClosedEmbedding.toIsEmbedding f hRange

/-- Helper for Theorem 10.5.1: a bundled finite-stage range cover is enough to recover an exact
factorization through one realized singular stage. -/
theorem mapFactorsExactlyThroughFiniteSingularStageOfRangeCover
    {K : Type*} [TopologicalSpace K] (X : TopCat.{u})
    (f : C(K, gammaRealization X))
    (hData :
      ∃ (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A }),
        Topology.IsEmbedding ((SSet.toTop.map A.1.ι).hom) ∧
          Set.range f ⊆ Set.range ((SSet.toTop.map A.1.ι).hom)) :
    ∃ (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A })
      (fA : C(K, SSet.toTop.obj A.1.toSSet)),
        (SSet.toTop.map A.1.ι).hom.comp fA = f := by
  rcases hData with ⟨A, hEmbedding, hRange⟩
  -- Consume the bundled range-cover witness through the exact range-subset factorization lemma.
  rcases mapFactorsExactlyThroughRealizedSubcomplexOfRangeSubset
      (X := X) A.1 hEmbedding f hRange with ⟨fA, hfA⟩
  exact ⟨A, fA, hfA⟩

/-- Helper for Theorem 10.5.1: once the range of a source map into `Γ X` is known to lie in a
chosen finite realized singular stage whose inclusion is a closed embedding, the map factors
exactly through that stage. -/
theorem mapFactorsExactlyThroughFiniteSingularStageOfClosedRangeCover
    {K : Type*} [TopologicalSpace K] (X : TopCat.{u})
    (f : C(K, gammaRealization X))
    (hData :
      ∃ (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A }),
        Topology.IsClosedEmbedding ((SSet.toTop.map A.1.ι).hom) ∧
          Set.range f ⊆ Set.range ((SSet.toTop.map A.1.ι).hom)) :
    ∃ (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A })
      (fA : C(K, SSet.toTop.obj A.1.toSSet)),
        (SSet.toTop.map A.1.ι).hom.comp fA = f := by
  rcases hData with ⟨A, hClosedEmbedding, hRange⟩
  -- Consume the closed-embedding witness through the specialized exact factorization wrapper.
  rcases mapFactorsExactlyThroughRealizedSubcomplexOfClosedRangeSubset
      (X := X) A.1 hClosedEmbedding f hRange with ⟨fA, hfA⟩
  exact ⟨A, fA, hfA⟩

/-- Helper for Theorem 10.5.1: enlarging an exact factorization into `Γ X` along a subcomplex
inclusion does not change the resulting map after postcomposition with the stage inclusion. -/
theorem gammaRealizationFactorization_comp_homOfLE {X : TopCat.{u}} {K : Type*}
    [TopologicalSpace K] {A B : (TopCat.toSSet.obj X).Subcomplex} (hAB : A ≤ B)
    (fA : C(K, SSet.toTop.obj A.toSSet)) :
    (SSet.toTop.map B.ι).hom.comp
        ((SSet.toTop.map (SSet.Subcomplex.homOfLE hAB)).hom.comp fA) =
      (SSet.toTop.map A.ι).hom.comp fA := by
  -- Reassociate the realization maps, then collapse the simplicial inclusion chain on the stage
  -- side before evaluating on the source `K`.
  calc
    (SSet.toTop.map B.ι).hom.comp
        ((SSet.toTop.map (SSet.Subcomplex.homOfLE hAB)).hom.comp fA)
      = ((SSet.toTop.map (SSet.Subcomplex.homOfLE hAB) ≫ SSet.toTop.map B.ι).hom.comp fA) := by
          rfl
    _ = (SSet.toTop.map A.ι).hom.comp fA := by
          rw [← Functor.map_comp, SSet.Subcomplex.homOfLE_ι]

/-- Helper for Theorem 10.5.1: enlarging a finite singular stage along a subcomplex inclusion
does not change the induced map to `X` after precomposition. -/
theorem finiteSingularRealizationEvaluationFactorization_comp_homOfLE (X : TopCat.{u})
    {K : Type*} [TopologicalSpace K] {A B : (TopCat.toSSet.obj X).Subcomplex} (hAB : A ≤ B)
    (gA : C(K, SSet.toTop.obj A.toSSet)) :
    ((finiteSingularRealizationEvaluation X B).hom.comp
        ((SSet.toTop.map (SSet.Subcomplex.homOfLE hAB)).hom.comp gA)) =
      (finiteSingularRealizationEvaluation X A).hom.comp gA := by
  -- Reassociate the comparison map with the enlarged stage and invoke the normalization lemma
  -- for the finite-stage evaluation.
  calc
    (finiteSingularRealizationEvaluation X B).hom.comp
        ((SSet.toTop.map (SSet.Subcomplex.homOfLE hAB)).hom.comp gA)
      = ((SSet.toTop.map (SSet.Subcomplex.homOfLE hAB) ≫
            finiteSingularRealizationEvaluation X B).hom.comp gA) := by
          rfl
    _ = (finiteSingularRealizationEvaluation X A).hom.comp gA := by
          rw [finiteSingularRealizationEvaluation_comp_homOfLE]

/-- Helper for Theorem 10.5.1: a simplicial map from a finite domain factors exactly through the
realization of its image subcomplex in `TopCat.toSSet.obj X`. -/
theorem finiteImageSubcomplexFactorization (X : TopCat.{u}) {K : SSet.{u}} [SSet.Finite K]
    (φ : K ⟶ TopCat.toSSet.obj X) :
    ∃ (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A })
      (φA : SSet.toTop.obj K ⟶ SSet.toTop.obj A.1.toSSet),
        φA ≫ SSet.toTop.map A.1.ι = SSet.toTop.map φ ∧
          φA ≫ finiteSingularRealizationEvaluation X A.1 =
            SSet.toTop.map φ ≫ singularRealizationEvaluation X := by
  let A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A } :=
    ⟨SSet.Subcomplex.range φ, inferInstance⟩
  have hFactor :
      SSet.toTop.map (SSet.Subcomplex.toRange φ) ≫ SSet.toTop.map A.1.ι =
        SSet.toTop.map φ := by
    -- Realization preserves the exact simplicial factorization through the image subcomplex.
    calc
      SSet.toTop.map (SSet.Subcomplex.toRange φ) ≫ SSet.toTop.map A.1.ι
          = SSet.toTop.map (SSet.Subcomplex.toRange φ ≫ A.1.ι) := by
              rw [← Functor.map_comp]
      _ = SSet.toTop.map φ := by
            exact by
              simpa [A] using congrArg (fun ψ ↦ SSet.toTop.map ψ) (SSet.Subcomplex.toRange_ι φ)
  refine ⟨A, SSet.toTop.map (SSet.Subcomplex.toRange φ), ?_, ?_⟩
  · exact hFactor
  · -- After postcomposing with the counit, the same factorization becomes the finite-stage
    -- comparison map to `X`.
    calc
      SSet.toTop.map (SSet.Subcomplex.toRange φ) ≫ finiteSingularRealizationEvaluation X A.1
          = (SSet.toTop.map (SSet.Subcomplex.toRange φ) ≫ SSet.toTop.map A.1.ι) ≫
              singularRealizationEvaluation X := by
                exact by
                  simpa [finiteSingularRealizationEvaluation, Category.assoc]
      _ = SSet.toTop.map φ ≫ singularRealizationEvaluation X := by
            rw [hFactor]

/-- Helper for Theorem 10.5.1: evaluating an exact finite-stage factorization in `Γ X` through
the counit recovers the corresponding map in `X`. -/
theorem finiteStageEvaluation_eq (X : TopCat.{u}) {K : Type*} [TopologicalSpace K]
    (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A })
    (f : C(K, gammaRealization X)) (fA : C(K, SSet.toTop.obj A.1.toSSet))
    (hf : (SSet.toTop.map A.1.ι).hom.comp fA = f) :
    ((finiteSingularRealizationEvaluation X A.1).hom.comp fA) =
      ((singularRealizationEvaluation X).hom.comp f) := by
  -- Rewrite the exact finite-stage factorization through the counit so the left endpoint is
  -- expressed on the chosen singular stage.
  calc
    ((finiteSingularRealizationEvaluation X A.1).hom.comp fA)
      = ((singularRealizationEvaluation X).hom.comp ((SSet.toTop.map A.1.ι).hom.comp fA)) := by
          rfl
    _ = ((singularRealizationEvaluation X).hom.comp f) := by
          rw [hf]

/-- Helper for Theorem 10.5.1: an exact boundary-stage factorization turns the original HELP track
into a homotopy whose left endpoint already lies in the chosen finite singular stage. -/
def boundaryHelpHomotopyOnFiniteStage (X : TopCat.{u}) (n : ℕ)
    (f : C(sphereBoundary n, gammaRealization X)) (g : C(unitDisk n, X))
    (H : (((singularRealizationEvaluation X).hom.comp f).Homotopy
      (g.comp (sphereBoundaryInclusion n))))
    (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A })
    (fA : C(sphereBoundary n, SSet.toTop.obj A.1.toSSet))
    (hf : (SSet.toTop.map A.1.ι).hom.comp fA = f) :
    (((finiteSingularRealizationEvaluation X A.1).hom.comp fA).Homotopy
      (g.comp (sphereBoundaryInclusion n))) :=
  -- Cast the original boundary track across the exact finite-stage equality proved just above.
  H.cast
    ((finiteStageEvaluation_eq (X := X) (K := sphereBoundary n) A f fA hf).symm)
    rfl

/-- Helper for Theorem 10.5.1: once the boundary HELP track has been normalized to a finite stage,
it can be transported unchanged along an enlargement of that stage. -/
def boundaryHelpHomotopyOnEnlargedFiniteStage (X : TopCat.{u}) (n : ℕ)
    (g : C(unitDisk n, X))
    {A B : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A }} (hAB : A.1 ≤ B.1)
    (fA : C(sphereBoundary n, SSet.toTop.obj A.1.toSSet))
    (H :
      (((finiteSingularRealizationEvaluation X A.1).hom.comp fA).Homotopy
        (g.comp (sphereBoundaryInclusion n)))) :
    (((finiteSingularRealizationEvaluation X B.1).hom.comp
        ((SSet.toTop.map (SSet.Subcomplex.homOfLE hAB)).hom.comp fA)).Homotopy
      (g.comp (sphereBoundaryInclusion n))) :=
  -- Move the normalized boundary track through the stage enlargement using the already-proved
  -- `homOfLE` comparison identity.
  H.cast
    ((finiteSingularRealizationEvaluationFactorization_comp_homOfLE
      (X := X) (K := sphereBoundary n) hAB fA).symm)
    rfl

/-- Helper for Theorem 10.5.1: if every point of the compact image of `f` has a neighborhood
already contained in the realization of some finite singular stage, then one finite subcover of
those neighborhoods compresses the whole image into a single common finite stage. -/
theorem compactImage_mem_commonFiniteSingularStage_of_localRangeCover
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (X : TopCat.{u}) (f : C(K, gammaRealization X))
    (hLocal :
      ∀ x ∈ Set.range f,
        ∃ (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A })
          (U : Set (gammaRealization X)),
            IsOpen U ∧ x ∈ U ∧ U ⊆ Set.range ((SSet.toTop.map A.1.ι).hom)) :
    ∃ (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A }),
      Set.range f ⊆ Set.range ((SSet.toTop.map A.1.ι).hom) := by
  classical
  let s : Set (gammaRealization X) := Set.range f
  have hs : IsCompact s := by
    -- The compact source forces the image of `f` to be compact.
    simpa [s] using (isCompact_range f.continuous)
  let owner : s → { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A } :=
    fun x ↦ Classical.choose (hLocal x.1 x.2)
  have hNeighborhood :
      ∀ x : s,
        ∃ U : Set (gammaRealization X),
          IsOpen U ∧ x.1 ∈ U ∧ U ⊆ Set.range ((SSet.toTop.map (owner x).1.ι).hom) := by
    intro x
    -- Unpack the local finite-stage neighborhood attached to `x`.
    simpa [owner] using (Classical.choose_spec (hLocal x.1 x.2))
  let cover : s → Set (gammaRealization X) := fun x ↦ Classical.choose (hNeighborhood x)
  have hCoverOpen : ∀ x : s, IsOpen (cover x) := by
    intro x
    -- Each chosen local set is open by construction.
    exact (Classical.choose_spec (hNeighborhood x)).1
  have hCoverMem : ∀ x : s, x.1 ∈ cover x := by
    intro x
    -- The chosen neighborhood still contains its marked point.
    exact (Classical.choose_spec (hNeighborhood x)).2.1
  have hCoverSubset :
      ∀ x : s, cover x ⊆ Set.range ((SSet.toTop.map (owner x).1.ι).hom) := by
    intro x
    -- Each local neighborhood already lands in its attached finite stage.
    exact (Classical.choose_spec (hNeighborhood x)).2.2
  have hSubcover :
      s ⊆ ⋃ x ∈ (Set.univ : Set s), cover x := by
    intro x hx
    -- Cover each image point by the neighborhood chosen at that same point.
    have hxUniv : (⟨x, hx⟩ : s) ∈ (Set.univ : Set s) := by
      exact Set.mem_univ (⟨x, hx⟩ : s)
    refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
    refine Set.mem_iUnion.2 ⟨hxUniv, hCoverMem ⟨x, hx⟩⟩
  rcases hs.elim_finite_subcover_image (b := (Set.univ : Set s)) (c := cover)
      (fun x _ ↦ hCoverOpen x) hSubcover with ⟨b', -, hb'Finite, hb'Cover⟩
  let t : Finset s := hb'Finite.toFinset
  let A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A } :=
    ⟨t.sup (fun x ↦ (owner x).1),
      finiteSingularSubcomplex_finsetSup t (fun x ↦ (owner x).1) (fun x _ ↦ (owner x).2)⟩
  refine ⟨A, ?_⟩
  intro x hx
  have hxCover : x ∈ ⋃ y ∈ b', cover y := hb'Cover hx
  rcases Set.mem_iUnion.1 hxCover with ⟨y, hyCover⟩
  rcases Set.mem_iUnion.1 hyCover with ⟨hyb', hxy⟩
  rcases hCoverSubset y hxy with ⟨a, ha⟩
  have hyt : y ∈ t := hb'Finite.mem_toFinset.2 hyb'
  refine ⟨((SSet.toTop.map (SSet.Subcomplex.homOfLE (Finset.le_sup hyt))).hom) a, ?_⟩
  -- Enlarge the selected local owner into the finite supremum chosen from the compact subcover.
  have hComp :
      SSet.toTop.map (SSet.Subcomplex.homOfLE (Finset.le_sup hyt)) ≫ SSet.toTop.map A.1.ι =
        SSet.toTop.map (owner y).1.ι := by
    rw [← Functor.map_comp, SSet.Subcomplex.homOfLE_ι]
  calc
    ((SSet.toTop.map A.1.ι).hom)
        (((SSet.toTop.map (SSet.Subcomplex.homOfLE (Finset.le_sup hyt))).hom) a)
      = ((SSet.toTop.map ((owner y).1.ι)).hom) a := by
          exact congrArg
            (fun g : SSet.toTop.obj (owner y).1.toSSet ⟶ gammaRealization X ↦ g a) hComp
    _ = x := ha

/-- Helper for Theorem 10.5.1: the image of a compact-source map into `Γ X` lies in one common
finite realized singular stage. -/
theorem compactImage_mem_commonFiniteSingularStage
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (X : TopCat.{u}) (f : C(K, gammaRealization X)) :
    ∃ (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A }),
      Set.range f ⊆ Set.range ((SSet.toTop.map A.1.ι).hom) := by
  -- Route correction: isolate the compactness bookkeeping first; the only remaining frontier is
  -- the local simplex-neighborhood statement for points of `Γ X`.
  refine compactImage_mem_commonFiniteSingularStage_of_localRangeCover (X := X) f ?_
  intro x hx
  -- TODO: refine `gammaRealizationPoint_mem_finiteSingularStage` to a local simplex-chart
  -- neighborhood contained in one realized finite singular stage.
  sorry

/-- Helper for Theorem 10.5.1: a compact-source map into `Γ X` should factor exactly through one
finite realized singular stage. -/
theorem compactMapFactorsExactlyThroughFiniteSingularStage
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (X : TopCat.{u}) (f : C(K, gammaRealization X)) :
    ∃ (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A })
      (fA : C(K, SSet.toTop.obj A.1.toSSet)),
        (SSet.toTop.map A.1.ι).hom.comp fA = f := by
  -- Route correction: keep the exact factorization step thin and expose the two actual missing
  -- bridges separately: compact-image compression and realized-stage embedding.
  rcases compactImage_mem_commonFiniteSingularStage (X := X) f with ⟨A, hRange⟩
  let _ : SSet.Finite A.1 := A.2
  have hEmbedding :
      Topology.IsEmbedding ((SSet.toTop.map A.1.ι).hom) :=
    finiteSingularStageInclusion_isEmbedding X A.1
  rcases mapFactorsExactlyThroughFiniteSingularStageOfRangeCover
      (X := X) f ⟨A, hEmbedding, hRange⟩ with ⟨A', fA, hfA⟩
  exact ⟨A', fA, hfA⟩

/-- Helper for Theorem 10.5.1: a boundary map into `Γ X` factors exactly through one finite
singular stage of `X`. -/
theorem boundaryMapFactorsExactlyThroughFiniteSingularStage
    (X : TopCat.{u}) (n : ℕ) (f : C(sphereBoundary n, gammaRealization X)) :
    ∃ (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A })
      (fA : C(sphereBoundary n, SSet.toTop.obj A.1.toSSet)),
        (SSet.toTop.map A.1.ι).hom.comp fA = f := by
  -- Specialize the compact-source factorization to the sphere-boundary model.
  simpa using compactMapFactorsExactlyThroughFiniteSingularStage (X := X) f

/-- Helper for Theorem 10.5.1: a disk map into `Γ X` factors exactly through one finite singular
stage of `X`. -/
theorem diskMapFactorsExactlyThroughFiniteSingularStage
    (X : TopCat.{u}) (n : ℕ) (g : C(unitDisk n, gammaRealization X)) :
    ∃ (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A })
      (gA : C(unitDisk n, SSet.toTop.obj A.1.toSSet)),
        (SSet.toTop.map A.1.ι).hom.comp gA = g := by
  let _ : CompactSpace (unitDisk n) := by
    rw [unitDisk]
    exact isCompact_iff_compactSpace.mp
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  -- Specialize the same compact-source factorization to the disk model.
  simpa using compactMapFactorsExactlyThroughFiniteSingularStage (X := X) g

/-- Helper for Theorem 10.5.1: once the exact boundary and disk finite-stage factorizations are in
place, the fixed-degree Chapter 9 two-stage homotopy-group package for the counit follows. -/
theorem singularRealizationEvaluation_hasPiInjectiveSurjectiveSucc
    (X : TopCat.{u}) (n : ℕ) :
    HasPiInjectiveSurjectiveSucc n ((singularRealizationEvaluation X).hom) := by
  -- Route correction: stay in the direct Chapter 9 owner `HasPiInjectiveSurjectiveSucc`.
  -- TODO: combine `singularRealizationEvaluation_eStar_commutesGenLoop` with
  -- `boundaryMapFactorsExactlyThroughFiniteSingularStage`,
  -- `diskMapFactorsExactlyThroughFiniteSingularStage`, the existing
  -- `boundaryHelpHomotopyOnFiniteStage` / `boundaryHelpHomotopyOnEnlargedFiniteStage`, and the
  -- finite-stage enlargement lemmas `finiteSingularSubcomplex_sup` and
  -- `finiteSingularSubcomplex_sup_sup` to build the `injective` and `surjectiveSucc` fields.
  sorry

/-- Helper for Theorem 10.5.1: the counit has the required Chapter 9 two-stage homotopy-group
control in every degree. -/
theorem singularRealizationEvaluation_hasPiInjectiveSurjectiveSuccAll (X : TopCat.{u}) :
    ∀ n : ℕ, HasPiInjectiveSurjectiveSucc n ((singularRealizationEvaluation X).hom) := by
  intro n
  -- Reduce the all-degree statement to the fixed-degree theorem above.
  exact singularRealizationEvaluation_hasPiInjectiveSurjectiveSucc X n

/-- Helper for Theorem 10.5.1: the singular-realization counit is a weak equivalence once the
compact finite-stage reduction has supplied all-degree Chapter 9 control. -/
theorem singularRealizationEvaluation_isWeakEquivalenceOfCompactCWFiniteReduction
    (X : TopCat.{u}) :
    IsWeakEquivalence ((singularRealizationEvaluation X).hom) := by
  -- Assemble weak equivalence from the established `0`-equivalence and the direct all-degree
  -- `π_*` control.
  exact
    isWeakEquivalenceOfIsNEquivalenceZeroAndHasPiInjectiveSurjectiveSuccAll
      (singularRealizationEvaluation_isNEquivalenceZero X)
      (singularRealizationEvaluation_hasPiInjectiveSurjectiveSuccAll X)

/-- Helper for Theorem 10.5.1: the realization of the singular simplicial set of `X` should carry
the categorical CW structure used by `CWApproximation`. -/
noncomputable def gammaRealization_hasTopCatCWComplex (X : TopCat.{u}) :
    TopCat.CWComplex (gammaRealization X) :=
  -- Route correction: the source-side CW witness must stay in the categorical
  -- `TopCat.CWComplex` API, not the classical `Topology.CWComplex` API.
  -- TODO: package the realized simplicial skeleta into a `RelativeCellComplex`, proving each
  -- successor inclusion is an `AttachCells (TopCat.RelativeCWComplex.basicCell n)` map and that
  -- their colimit identifies with `gammaRealization X`.
  sorry

/-- Helper for Theorem 10.5.1: the direct singular-realization witness provides the CW model and
weak equivalence promised by the theorem. -/
theorem existsCwWeakEquivalenceWitness_ofSingularCounit (X : TopCat.{u}) :
    ∃ (Γ : TopCat.{u}) (_ : TopCat.CWComplex Γ) (γ : C(Γ, X)), IsWeakEquivalence γ := by
  -- Route correction: assemble the final witness directly from `Γ X = |Sing X|`.
  refine ⟨gammaRealization X, gammaRealization_hasTopCatCWComplex X,
    (singularRealizationEvaluation X).hom, ?_⟩
  exact singularRealizationEvaluation_isWeakEquivalenceOfCompactCWFiniteReduction X

/-- Helper for Theorem 10.5.1: one successor step of the staged CW approximation records the next
space, the inclusion of the current stage, the descended map to the target, and the basic-cell
attachment data for that one step. -/
structure ApproximationSuccessorStage (X : TopCat.{u}) (n : ℕ) (Y : TopCat.{u})
    (f : Y ⟶ X) where
  /-- The next stage obtained after the degree-`n` attachment step. -/
  nextObj : TopCat.{u}
  /-- The inclusion of the current stage into the next stage. -/
  inclusion : Y ⟶ nextObj
  /-- The next-stage map to the target. -/
  nextToTarget : nextObj ⟶ X
  /-- The previous stage map factors through the next stage. -/
  fac : inclusion ≫ nextToTarget = f
  /-- The current-to-next inclusion is built by attaching `n`-cells. -/
  attachCells :
    HomotopicalAlgebra.AttachCells.{u}
      (TopCat.RelativeCWComplex.basicCell n)
      inclusion

namespace ApproximationSuccessorStage

variable {X : TopCat.{u}} {n : ℕ} {Y : TopCat.{u}} {f : Y ⟶ X}

/-- Helper for Theorem 10.5.1: the recorded next-stage map factors the previous stage map exactly
as stored in the successor-stage data. -/
@[simp] theorem inclusion_comp_nextToTarget
    (stage : ApproximationSuccessorStage X n Y f) :
    stage.inclusion ≫ stage.nextToTarget = f := by
  -- Reuse the stored factorization field directly so later proofs can rewrite with a named lemma.
  exact stage.fac

end ApproximationSuccessorStage

/-- Helper for Theorem 10.5.1: a recursive staged approximation sequence records only the concrete
stage objects, successor maps, abstract cell-attachment data, and the compatible maps to the
target. Colimit-level `π_*` control is supplied separately. -/
structure ApproximationStageSequence (X : TopCat.{u}) where
  /-- The stage object in degree `n`. -/
  obj : ℕ → TopCat.{u}
  /-- The stage-zero object is initial, so the sequence starts from the empty stage. -/
  isoBot : obj 0 ≅ ⊥_ TopCat.{u}
  /-- The successor map from stage `n` to stage `n + 1`. -/
  stepMap : ∀ n : ℕ, obj n ⟶ obj (n + 1)
  /-- Each successor map is an abstract `n`-cell attachment. -/
  attachCells :
    ∀ n : ℕ,
      HomotopicalAlgebra.AttachCells.{u}
        (TopCat.RelativeCWComplex.basicCell n)
        (stepMap n)
  /-- The stagewise maps to the target. -/
  stageToTarget : ∀ n : ℕ, obj n ⟶ X
  /-- Each successor map is compatible with the stagewise target maps. -/
  step_fac : ∀ n : ℕ, stepMap n ≫ stageToTarget (n + 1) = stageToTarget n

namespace ApproximationStageSequence

variable {X : TopCat.{u}}

/-- Helper for Theorem 10.5.1: package the `n`th successor step of a recursive staged sequence as
an explicit one-step `ApproximationSuccessorStage`. -/
def successorStage (data : ApproximationStageSequence X) (n : ℕ) :
    ApproximationSuccessorStage X n (data.obj n) (data.stageToTarget n) :=
  { nextObj := data.obj (n + 1)
    inclusion := data.stepMap n
    nextToTarget := data.stageToTarget (n + 1)
    fac := data.step_fac n
    attachCells := data.attachCells n }

/-- Helper for Theorem 10.5.1: the recursive stage sequence determines the underlying sequential
diagram `ℕ ⥤ TopCat`. -/
def functor (data : ApproximationStageSequence X) : ℕ ⥤ TopCat.{u} :=
  Functor.ofSequence data.stepMap

/-- Helper for Theorem 10.5.1: the induced functor computes the successor morphisms by the stored
stage maps. -/
theorem functor_map_succ (data : ApproximationStageSequence X) (n : ℕ) :
    data.functor.map (homOfLE (Nat.le_add_right n 1)) = data.stepMap n := by
  -- `Functor.ofSequence` computes the `n → n + 1` maps definitionally.
  simp [functor]

/-- Helper for Theorem 10.5.1: the stagewise target maps form a cocone over the induced
sequential diagram. -/
theorem stageToTarget_naturality (data : ApproximationStageSequence X) (n : ℕ) :
    data.functor.map (homOfLE (Nat.le_add_right n 1)) ≫ data.stageToTarget (n + 1) =
      data.stageToTarget n ≫
        ((Functor.const ℕ).obj X).map (homOfLE (Nat.le_add_right n 1)) := by
  -- Normalize the successor map of the induced functor and then reuse the stored compatibility.
  rw [data.functor_map_succ]
  simpa using data.step_fac n

end ApproximationStageSequence

/-- Helper for Theorem 10.5.1: theorem-local stagewise approximation data packages a sequential
diagram of spaces, its abstract cell-attachment data, and a compatible cocone to the target. -/
structure StagewiseApproximationData (X : TopCat.{u}) where
  /-- The staged diagram `F₀ ⟶ F₁ ⟶ F₂ ⟶ ⋯` used to approximate `X`. -/
  F : ℕ ⥤ TopCat.{u}
  /-- The stage-zero object is initial, so the staged diagram starts from the empty CW stage. -/
  isoBot : F.obj 0 ≅ ⊥_ TopCat.{u}
  /-- Each successor map is an abstract `n`-cell attachment. -/
  attachCells :
    ∀ n : ℕ,
      HomotopicalAlgebra.AttachCells.{u}
        (TopCat.RelativeCWComplex.basicCell n)
        (F.map (homOfLE (Nat.le_add_right n 1)))
  /-- The staged maps to `X` that descend to the final comparison map. -/
  stageToTarget : ∀ n : ℕ, F.obj n ⟶ X
  /-- The staged maps form a cocone over the sequential diagram. -/
  stageToTarget_naturality :
    ∀ n : ℕ,
      F.map (homOfLE (Nat.le_add_right n 1)) ≫ stageToTarget (n + 1) =
        stageToTarget n ≫
          ((Functor.const ℕ).obj X).map (homOfLE (Nat.le_add_right n 1))
  /-- The descended colimit map already has the required `0`-equivalence input. -/
  zeroEquivalence :
    IsNEquivalence 0
      ((Limits.colimit.desc F
          (Cocone.mk X (NatTrans.ofSequence stageToTarget stageToTarget_naturality))).hom)
  /-- The descended colimit map already has the degreewise Chapter 9 `π_*` control. -/
  piControl :
    ∀ n : ℕ,
      HasPiInjectiveSurjectiveSucc n
        ((Limits.colimit.desc F
            (Cocone.mk X (NatTrans.ofSequence stageToTarget stageToTarget_naturality))).hom)

namespace StagewiseApproximationData

variable {X : TopCat.{u}}

/-- Helper for Theorem 10.5.1: the cocone from the staged approximation diagram to the target. -/
def stageCocone (data : StagewiseApproximationData X) : Cocone data.F :=
  Cocone.mk _ (NatTrans.ofSequence data.stageToTarget data.stageToTarget_naturality)

/-- Helper for Theorem 10.5.1: the source `Γ X` obtained as the colimit of the stagewise diagram.
-/
abbrev colimitSpace (data : StagewiseApproximationData X) : TopCat.{u} :=
  Limits.colimit data.F

/-- Helper for Theorem 10.5.1: the comparison map from the stagewise colimit to `X`. -/
abbrev colimitMap (data : StagewiseApproximationData X) : data.colimitSpace ⟶ X :=
  Limits.colimit.desc data.F data.stageCocone

/-- Helper for Theorem 10.5.1: each stage map factors through the descended colimit map. -/
theorem stageInclusion_comp_colimitMap (data : StagewiseApproximationData X) (n : ℕ) :
    Limits.colimit.ι data.F n ≫ data.colimitMap = data.stageToTarget n := by
  -- The colimit descends the stage cocone by construction.
  simpa [colimitMap, stageCocone] using Limits.colimit.ι_desc data.stageCocone n

/-- Helper for Theorem 10.5.1: the stagewise colimit carries the abstract CW-complex structure
coming from the recorded attachment data. -/
noncomputable def colimitCwComplex (data : StagewiseApproximationData X) :
    TopCat.CWComplex data.colimitSpace :=
  -- Route correction: build the abstract CW owner directly from the staged diagram instead of
  -- routing through the stalled singular-realization bridge.
  { F := data.F
    isoBot := data.isoBot
    incl := Limits.colimit.cocone data.F |>.ι
    isColimit := Limits.colimit.isColimit data.F
    attachCells := by
      intro n hn
      -- Each successor stage already records the required basic-cell attachment.
      simpa using data.attachCells n }

/-- Helper for Theorem 10.5.1: the descended colimit map keeps the stored `0`-equivalence input.
-/
theorem colimitMap_isNEquivalenceZero (data : StagewiseApproximationData X) :
    IsNEquivalence 0 data.colimitMap.hom := by
  -- This is exactly the degree-zero control stored in the stagewise interface.
  simpa [colimitMap, stageCocone] using data.zeroEquivalence

/-- Helper for Theorem 10.5.1: the descended colimit map keeps the stored all-degree Chapter 9
`π_*` control. -/
theorem colimitMap_hasPiInjectiveSurjectiveSuccAll (data : StagewiseApproximationData X) :
    ∀ n : ℕ, HasPiInjectiveSurjectiveSucc n data.colimitMap.hom := by
  intro n
  -- This is exactly the degreewise `π_*` control stored in the stagewise interface.
  simpa [colimitMap, stageCocone] using data.piControl n

end StagewiseApproximationData

namespace ApproximationStageSequence

variable {X : TopCat.{u}}

/-- Helper for Theorem 10.5.1: once a recursive stage sequence has been built and its descended
colimit map is known to satisfy the degree-zero and all-degree Chapter 9 control, the sequence
packages directly into `StagewiseApproximationData`. -/
def toStagewiseApproximationData (data : ApproximationStageSequence X)
    (h0 :
      IsNEquivalence 0
        ((Limits.colimit.desc data.functor
            (Cocone.mk X
              (NatTrans.ofSequence data.stageToTarget data.stageToTarget_naturality))).hom))
    (hPi :
      ∀ n : ℕ,
        HasPiInjectiveSurjectiveSucc n
          ((Limits.colimit.desc data.functor
              (Cocone.mk X
                (NatTrans.ofSequence data.stageToTarget data.stageToTarget_naturality))).hom)) :
    StagewiseApproximationData X :=
  { F := data.functor
    isoBot := data.isoBot
    attachCells := fun n ↦ by
      -- Rewrite the successor morphism of the induced functor back to the stored stage map.
      rw [data.functor_map_succ]
      exact data.attachCells n
    stageToTarget := data.stageToTarget
    stageToTarget_naturality := data.stageToTarget_naturality
    zeroEquivalence := h0
    piControl := hPi }

end ApproximationStageSequence

/-- Helper for Theorem 10.5.1: the colimit comparison map coming from theorem-local stagewise
approximation data is a weak equivalence. -/
theorem stagewiseColimitMap_isWeakEquivalence {X : TopCat.{u}}
    (data : StagewiseApproximationData X) :
    IsWeakEquivalence data.colimitMap.hom := by
  -- Route correction: assemble the final weak-equivalence witness directly from the theorem-local
  -- stagewise API instead of reopening the stalled singular-realization frontier.
  exact
    isWeakEquivalenceOfIsNEquivalenceZeroAndHasPiInjectiveSurjectiveSuccAll
      (data.colimitMap_isNEquivalenceZero)
      (data.colimitMap_hasPiInjectiveSurjectiveSuccAll)

/-- Helper for Theorem 10.5.1: the actual CW-approximation witness comes from the direct singular
realization witness `γ : |Sing X| ⟶ X`. -/
theorem existsCwWeakEquivalenceWitness_ofApproximationStages (X : TopCat.{u}) :
    ∃ (Γ : TopCat.{u}) (_ : TopCat.CWComplex Γ) (γ : C(Γ, X)), IsWeakEquivalence γ := by
  -- Route correction: the main frontier is now the direct singular-realization witness, not the
  -- older theorem-local stagewise wrapper.
  exact existsCwWeakEquivalenceWitness_ofSingularCounit X

/-- Helper for Theorem 10.5.1: existence of a CW model `Γ` and a weak equivalence
`γ : C(Γ, X)`. -/
theorem existsCwWeakEquivalenceWitness (X : TopCat.{u}) :
    ∃ (Γ : TopCat.{u}) (_ : TopCat.CWComplex Γ) (γ : C(Γ, X)), IsWeakEquivalence γ := by
  -- The public witness theorem is now just the stagewise packaging wrapper.
  exact existsCwWeakEquivalenceWitness_ofApproximationStages X

/-- Theorem 10.5.1: every space `X` admits a chosen CW approximation, recorded by
`CWApproximation X`. -/
theorem exists_cwApproximation (X : TopCat.{u}) :
    Nonempty (CWApproximation.{u, u} X) := by
  -- Package the source-facing witness into the Chapter 10 approximation owner.
  exact cwApproximationOfWitness (existsCwWeakEquivalenceWitness X)
