import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Remark_9_4_13.BasepointTransport
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.SphereDiskModel
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.ZerothHomotopyMap
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Construction_16_2_2
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

noncomputable section

universe u

open CategoryTheory
open scoped Topology Topology.Homotopy Simplicial

section

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {e : C(Y, Z)}

/-- Helper for Theorem 16.2.4: a `0`-equivalence plus two-stage homotopy-group control up to
degree `n` upgrades to an `(n + 1)`-equivalence. -/
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
        -- Surjectivity up to degree `1` splits into the `π₀` base case and the stage-`0`
        -- successor case.
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
        ih (fun m hm ↦ hSteps m (Nat.le_trans hm (Nat.le_succ _)))
      refine ⟨?_, ?_⟩
      · intro y q hq
        -- Degrees below `n + 2` are either already controlled by the previous stage or equal to
        -- the new boundary degree handled by the stage-`(n + 1)` hypothesis.
        rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq' | rfl
        · exact hPrev.injective y hq'
        · exact (hSteps (n + 1) le_rfl).injective y
      · intro y q hq
        -- Surjectivity up to `n + 2` is handled either by the previous stage or by the new top
        -- degree.
        rcases Nat.eq_or_lt_of_le hq with rfl | hq'
        · exact (hSteps (n + 1) le_rfl).surjectiveSucc y
        · exact hPrev.surjective y (Nat.le_of_lt_succ hq')

/-- Helper for Theorem 16.2.4: a `0`-equivalence plus two-stage homotopy-group control in every
degree upgrades to a weak equivalence. -/
theorem isWeakEquivalenceOfIsNEquivalenceZeroAndHasPiInjectiveSurjectiveSuccAll
    (h0 : IsNEquivalence 0 e)
    (hSteps : ∀ n : ℕ, HasPiInjectiveSurjectiveSucc n e) :
    IsWeakEquivalence e := by
  refine ⟨fun n ↦ ?_⟩
  -- Separate the `n = 0` base case, then use the inductive upgrade for positive degrees.
  cases n with
  | zero =>
      exact h0
  | succ n =>
      exact isNEquivalenceSuccOfIsNEquivalenceZeroAndHasPiInjectiveSurjectiveSuccUpTo h0 n
        (fun m _ ↦ hSteps m)

end

/-- Helper for Theorem 16.2.4: the canonical section `X → Γ X` obtained by realizing the constant
`0`-simplex at each point of `X`. -/
noncomputable def singularRealizationVertexSection (X : TopCat.{u}) : X → gammaRealization X :=
  fun x ↦
    SSet.toTop.map (SSet.const (TopCat.toSSetObj₀Equiv.symm x))
      (default : |(Δ[0] : SSet.{u})|)

/-- Helper for Theorem 16.2.4: under the canonical `π₀ ≃ ZerothHomotopy` identifications, the
degree-`0` map induced by `sSetTopAdj.counit.app X` is the usual map on path components. -/
theorem singularRealizationEvaluation_piZero_commutes (X : TopCat.{u}) (x : gammaRealization X) :
    (HomotopyGroup.pi0EquivZerothHomotopy :
        π_ 0 X ((sSetTopAdj.counit.app X).hom x) ≃ ZerothHomotopy X).toFun ∘
        ((sSetTopAdj.counit.app X).hom).eStar 0 x =
      zerothHomotopyMap ((sSetTopAdj.counit.app X).hom) ∘
        (HomotopyGroup.pi0EquivZerothHomotopy :
          π_ 0 (gammaRealization X) x ≃ ZerothHomotopy (gammaRealization X)).toFun := by
  -- Both sides send a `π₀` class to the path component of the image endpoint under the counit.
  funext a
  refine Quotient.inductionOn a ?_
  intro γ
  rfl

/-- Helper for Theorem 16.2.4: postcomposition by a continuous map preserves generalized-loop
boundary conditions. -/
theorem genLoopMap_mem_boundary
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] (e : C(Y, Z))
    {q : ℕ} {y : Y} (γ : Ω^ (Fin q) Y y) :
    ∀ t ∈ Cube.boundary (Fin q), (e.comp γ.1) t = e y := by
  intro t ht
  -- Evaluate the generalized-loop boundary condition and then postcompose by `e`.
  simpa using congrArg e (γ.2 t ht)

/-- Helper for Theorem 16.2.4: postcomposition by a continuous map is a continuous map on the
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

/-- Helper for Theorem 16.2.4: under the quotient-model identification of `π_n` with path
components of generalized loops, the counit's induced map is just postcomposition on loop
representatives. -/
theorem singularRealizationEvaluation_eStar_commutesGenLoop
    (X : TopCat.{u}) (n : ℕ) (x : gammaRealization X) :
    (homotopyGroupEquivZerothHomotopyGenLoop n (((sSetTopAdj.counit.app X).hom) x)).toFun ∘
        ((sSetTopAdj.counit.app X).hom).eStar n x =
      zerothHomotopyMap (genLoopSpacePostcomp ((sSetTopAdj.counit.app X).hom) n x) ∘
        (homotopyGroupEquivZerothHomotopyGenLoop n x).toFun := by
  funext a
  refine Quotient.inductionOn a ?_
  intro γ
  -- Both sides record the same postcomposed generalized loop in the path-component quotient.
  rfl

/-- Helper for Theorem 16.2.4: evaluating the realized constant `0`-simplex at `x` returns `x`
under the counit `Γ X ⟶ X`. -/
theorem singularRealizationVertexSection_spec (X : TopCat.{u}) (x : X) :
    ((sSetTopAdj.counit.app X).hom) (singularRealizationVertexSection X x) = x := by
  -- Transport the counit composite back across the adjunction, where it is just the chosen
  -- constant `0`-simplex, and then read off the value at the unique point of `|Δ[0]|`.
  let σ : Δ[0] ⟶ TopCat.toSSet.obj X :=
    SSet.const (TopCat.toSSetObj₀Equiv.symm x)
  have hAdjoint :
      sSetTopAdj.homEquiv Δ[0] X
          (SSet.toTop.map σ ≫ sSetTopAdj.counit.app X) =
        SSet.const (TopCat.toSSetObj₀Equiv.symm x) := by
    have hNat :
        sSetTopAdj.homEquiv Δ[0] X
            (SSet.toTop.map σ ≫ sSetTopAdj.counit.app X) =
          σ ≫ (sSetTopAdj.homEquiv (TopCat.toSSet.obj X) X) (sSetTopAdj.counit.app X) := by
      simpa using
        (sSetTopAdj.homEquiv_naturality_left
          (X' := Δ[0]) (X := TopCat.toSSet.obj X) (Y := X)
          σ (sSetTopAdj.counit.app X))
    simpa [σ, singularRealizationEvaluation_spec] using hNat
  have hConst :
      (SSet.const
          (TopCat.toSSetObj₀Equiv.symm
            (((sSetTopAdj.counit.app X).hom) (singularRealizationVertexSection X x))) :
          Δ[0] ⟶ TopCat.toSSet.obj X) =
        (SSet.const (TopCat.toSSetObj₀Equiv.symm x) : Δ[0] ⟶ TopCat.toSSet.obj X) := by
    simpa [singularRealizationVertexSection, σ, sSetTopAdj_homEquiv_stdSimplex_zero] using hAdjoint
  have hValue :
      TopCat.toSSetObj₀Equiv.symm
          (((sSetTopAdj.counit.app X).hom) (singularRealizationVertexSection X x)) =
        TopCat.toSSetObj₀Equiv.symm x := by
    have hSymm :
        SSet.yonedaEquiv.symm
            (TopCat.toSSetObj₀Equiv.symm
              (((sSetTopAdj.counit.app X).hom) (singularRealizationVertexSection X x))) =
          SSet.yonedaEquiv.symm (TopCat.toSSetObj₀Equiv.symm x) := by
      simpa using hConst
    exact SSet.yonedaEquiv.symm.injective hSymm
  exact TopCat.toSSetObj₀Equiv.symm.injective hValue

/-- Helper for Theorem 16.2.4: the counit `Γ X ⟶ X` is surjective on path components. -/
theorem singularRealizationEvaluation_surjective_zerothHomotopy (X : TopCat.{u}) :
    Function.Surjective (zerothHomotopyMap ((sSetTopAdj.counit.app X).hom)) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  refine ⟨⟦singularRealizationVertexSection X x⟧, ?_⟩
  -- The vertex section is a strict pointwise section of the counit.
  rw [zerothHomotopyMap_mk]
  rw [singularRealizationVertexSection_spec]

/-- Helper for Theorem 16.2.4: the canonical map `Γ X ⟶ X` is a `0`-equivalence. -/
theorem singularRealizationEvaluation_isNEquivalenceZero (X : TopCat.{u}) :
    IsNEquivalence 0 ((sSetTopAdj.counit.app X).hom) := by
  refine ⟨?_, ?_⟩
  · intro x q hq
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
        π_ 0 X (((sSetTopAdj.counit.app X).hom) x) ≃ ZerothHomotopy X :=
      HomotopyGroup.pi0EquivZerothHomotopy
    rcases singularRealizationEvaluation_surjective_zerothHomotopy X (eCod a) with ⟨b, hb⟩
    refine ⟨eDom.symm b, ?_⟩
    apply eCod.injective
    -- The generic `π₀`/`ZerothHomotopy` comparison rewrites the target to the surjective
    -- path-component statement proved above.
    have hComm :
        eCod (((sSetTopAdj.counit.app X).hom).eStar 0 x (eDom.symm b)) =
          zerothHomotopyMap ((sSetTopAdj.counit.app X).hom) b := by
      have hComm' :
          eCod (((sSetTopAdj.counit.app X).hom).eStar 0 x (eDom.symm b)) =
            zerothHomotopyMap ((sSetTopAdj.counit.app X).hom) (eDom (eDom.symm b)) := by
        simpa [eDom, eCod] using
          congrArg (fun f ↦ f (eDom.symm b)) (singularRealizationEvaluation_piZero_commutes X x)
      rw [Equiv.apply_symm_apply] at hComm'
      exact hComm'
    exact hComm.trans hb

/-- Helper for Theorem 16.2.4: the realization of a singular subcomplex of `X` maps to `X`
through the inclusion followed by the counit. -/
abbrev finiteSingularRealizationEvaluation (X : TopCat.{u})
    (A : (TopCat.toSSet.obj X).Subcomplex) :
    SSet.toTop.obj A.toSSet ⟶ X :=
  SSet.toTop.map A.ι ≫ sSetTopAdj.counit.app X

/-- Helper for Theorem 16.2.4: enlarging a finite singular owner along a subcomplex inclusion does
not change the comparison map to `X`. -/
theorem finiteSingularRealizationEvaluation_comp_homOfLE (X : TopCat.{u})
    {A B : (TopCat.toSSet.obj X).Subcomplex} (hAB : A ≤ B) :
    SSet.toTop.map (SSet.Subcomplex.homOfLE hAB) ≫ finiteSingularRealizationEvaluation X B =
      finiteSingularRealizationEvaluation X A := by
  -- Normalize the enlarged finite-owner comparison by collapsing the subcomplex inclusion on the
  -- simplicial side before composing with the counit.
  rw [finiteSingularRealizationEvaluation, ← Category.assoc, ← Functor.map_comp,
    SSet.Subcomplex.homOfLE_ι]

/-- Helper for Theorem 16.2.4: the union of two finite singular subcomplexes is still finite. -/
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

/-- Helper for Theorem 16.2.4: the supremum of finitely many finite singular subcomplexes is
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
      exact SSet.finite_of_hasDimensionLT (X := B) 0 (fun i hi ↦ False.elim (Nat.not_lt_zero _ hi))
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

/-- Helper for Theorem 16.2.4: the union of three finite singular subcomplexes is still finite. -/
theorem finiteSingularSubcomplex_sup_sup {X : TopCat.{u}}
    (A B C : (TopCat.toSSet.obj X).Subcomplex)
    [SSet.Finite A] [SSet.Finite B] [SSet.Finite C] :
    SSet.Finite (((A ⊔ B : (TopCat.toSSet.obj X).Subcomplex) ⊔ C :
      (TopCat.toSSet.obj X).Subcomplex)) := by
  -- First merge the two boundary-side carriers, then add the homotopy-track carrier.
  letI : SSet.Finite ((A ⊔ B : (TopCat.toSSet.obj X).Subcomplex)) :=
    finiteSingularSubcomplex_sup A B
  exact finiteSingularSubcomplex_sup (A ⊔ B : (TopCat.toSSet.obj X).Subcomplex) C

/-- Helper for Theorem 16.2.4: every point of `Γ X` comes from the realization of a finite
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
              simpa [A] using congrArg (fun f ↦ SSet.toTop.map f)
                (SSet.Subcomplex.toRange_ι p.hom)
    exact congrArg (fun f : SSet.toTop.obj (SSet.stdSimplex.obj p.left) ⟶ gammaRealization X ↦
      f z) hFactor
  refine ⟨A, a, ?_⟩
  exact ha.trans hx

/-- Helper for Theorem 16.2.4: every point in the realization of a simplicial set comes from one
simplex leg in the usual colimit presentation. -/
theorem realizationPoint_mem_simplexRange (K : SSet.{u}) (x : SSet.toTop.obj K) :
    ∃ (n : SimplexCategory) (σ : SSet.stdSimplex.obj n ⟶ K)
      (u : SSet.toTop.obj (SSet.stdSimplex.obj n)),
        ((SSet.toTop.map σ).hom) u = x := by
  let diag : CategoryTheory.CostructuredArrow SSet.stdSimplex K ⥤ TopCat :=
    CategoryTheory.CostructuredArrow.proj SSet.stdSimplex K ⋙ SimplexCategory.toTop
  let e : SSet.toTop.obj K ≅ CategoryTheory.Limits.colimit diag :=
    SSet.stdSimplex.leftKanExtensionObjIsoColimit
      (F := SimplexCategory.toTop) (X := K)
  let hcolim :
      CategoryTheory.Limits.IsColimit ((forget TopCat).mapCocone
        (CategoryTheory.Limits.colimit.cocone diag)) :=
    CategoryTheory.Limits.isColimitOfPreserves (forget TopCat)
      (CategoryTheory.Limits.colimit.isColimit diag)
  obtain ⟨p, y, hy⟩ := CategoryTheory.Limits.Types.jointly_surjective_of_isColimit
    (F := diag ⋙ forget TopCat)
    (t := (forget TopCat).mapCocone (CategoryTheory.Limits.colimit.cocone diag))
    hcolim (e.hom x)
  let u : SSet.toTop.obj (SSet.stdSimplex.obj p.left) :=
    (SSet.toTopSimplex.app p.left).inv y
  have hColimitLeg :
      (SSet.toTopSimplex.inv.app p.left) ≫ SSet.toTop.map p.hom ≫ e.hom =
        CategoryTheory.Limits.colimit.ι diag p := by
    -- Rewrite the generic left-Kan colimit leg into the concrete realization of one simplex map.
    simpa [diag, e, SSet.toTop, SSet.toTopSimplex] using
      (CategoryTheory.Functor.ι_leftKanExtensionObjIsoColimit_hom
        (L := SSet.stdSimplex) (F := SimplexCategory.toTop) (X := K) p)
  have hx :
      ((SSet.toTop.map p.hom).hom) u = x := by
    -- Evaluate the chosen colimit leg at the representing point and cancel the realization
    -- isomorphism.
    have heInj : Function.Injective e.hom := (TopCat.homeoOfIso e).injective
    apply heInj
    have hEval :
        (((SSet.toTopSimplex.inv.app p.left) ≫ SSet.toTop.map p.hom ≫ e.hom).hom) y =
          (CategoryTheory.Limits.colimit.ι diag p) y := by
      exact congrArg
        (fun f : SimplexCategory.toTop.obj p.left ⟶ CategoryTheory.Limits.colimit diag ↦ f y)
        hColimitLeg
    have hy' : (CategoryTheory.Limits.colimit.ι diag p) y = e.hom x := by
      simpa [diag] using hy
    exact (by simpa [u] using hEval.trans hy')
  exact ⟨p.left, p.hom, u, hx⟩

/-- Helper for Theorem 16.2.4: every point in the realization of a simplicial set already lies in
the image of a nondegenerate simplex leg. -/
theorem realizationPoint_mem_nondegenerateSimplexRange (K : SSet.{u}) (x : SSet.toTop.obj K) :
    ∃ (s : K.N) (u : SSet.toTop.obj (SSet.stdSimplex.obj ⦋s.dim⦌)),
      ((SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)).hom) u = x := by
  obtain ⟨n, σ, u, hu⟩ := realizationPoint_mem_simplexRange K x
  induction n using SimplexCategory.rec with
  | _ n =>
      let a : K _⦋n⦌ := SSet.yonedaEquiv σ
      obtain ⟨m, f, _, y, ha⟩ := K.exists_nonDegenerate a
      let s : K.N := SSet.N.mk _ y.2
      let τ : SSet.stdSimplex.obj ⦋m⦌ ⟶ K := SSet.yonedaEquiv.symm y.1
      let u' : SSet.toTop.obj (SSet.stdSimplex.obj ⦋m⦌) :=
        SSet.toTop.map (SSet.stdSimplex.map f) u
      have hσ : σ = SSet.stdSimplex.map f ≫ τ := by
        -- Rewrite the original simplex map through its nondegenerate support.
        apply SSet.yonedaEquiv.injective
        rw [SSet.yonedaEquiv_comp, SSet.stdSimplex.yonedaEquiv_map,
          SSet.stdSimplex.yonedaEquiv_symm_app_objEquiv_symm]
        simpa [a, τ] using ha
      refine ⟨s, u', ?_⟩
      -- Realization preserves the simplicial factorization through the nondegenerate owner.
      calc
        ((SSet.toTop.map τ).hom) u'
          = (((SSet.toTop.map (SSet.stdSimplex.map f)) ≫ SSet.toTop.map τ).hom) u := by
              rfl
        _ = ((SSet.toTop.map (SSet.stdSimplex.map f ≫ τ)).hom) u := by
              rw [← Functor.map_comp]
        _ = ((SSet.toTop.map σ).hom) u := by rw [hσ]
        _ = x := hu

/-- Helper for Theorem 16.2.4: finitely many points of `Γ X` lie in the realization of one common
finite singular subcomplex. -/
theorem finiteFamily_mem_commonFiniteSingularStage
    (X : TopCat.{u}) {ι : Type*} (s : Finset ι) (x : ι → gammaRealization X) :
    ∃ (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A }),
      ∀ i ∈ s, x i ∈ Set.range ((SSet.toTop.map A.1.ι).hom) := by
  classical
  let B : ι → { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A } :=
    fun i ↦ Classical.choose (gammaRealizationPoint_mem_finiteSingularStage X (x i))
  have hBx : ∀ i, x i ∈ Set.range ((SSet.toTop.map (B i).1.ι).hom) := by
    intro i
    rcases Classical.choose_spec (gammaRealizationPoint_mem_finiteSingularStage X (x i)) with
      ⟨a, ha⟩
    exact ⟨a, ha⟩
  let A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A } :=
    ⟨s.sup (fun i ↦ (B i).1),
      finiteSingularSubcomplex_finsetSup s (fun i ↦ (B i).1) (fun i hi ↦ (B i).2)⟩
  refine ⟨A, ?_⟩
  intro i hi
  rcases hBx i with ⟨a, ha⟩
  refine ⟨((SSet.toTop.map (SSet.Subcomplex.homOfLE (Finset.le_sup hi))).hom) a, ?_⟩
  -- Enlarge the chosen pointwise finite stage into the common finite owner built from the
  -- finite supremum, then collapse the inclusion chain on the simplicial side.
  have hComp :
      SSet.toTop.map (SSet.Subcomplex.homOfLE (Finset.le_sup hi)) ≫ SSet.toTop.map A.1.ι =
        SSet.toTop.map ((B i).1.ι) := by
    rw [← Functor.map_comp, SSet.Subcomplex.homOfLE_ι]
  calc
    ((SSet.toTop.map A.1.ι).hom)
        (((SSet.toTop.map (SSet.Subcomplex.homOfLE (Finset.le_sup hi))).hom) a)
      = ((SSet.toTop.map ((B i).1.ι)).hom) a := by
          exact congrArg
            (fun f :
              SSet.toTop.obj ((B i).1).toSSet ⟶ gammaRealization X ↦
                f a) hComp
    _ = x i := ha

/-- Helper for Theorem 16.2.4: enlarging an exact factorization into `Γ X` along a subcomplex
inclusion does not change the resulting map after postcomposition with the stage inclusion. -/
theorem gammaRealizationFactorization_comp_homOfLE {X : TopCat.{u}} {K : Type*}
    [TopologicalSpace K] {A B : (TopCat.toSSet.obj X).Subcomplex} (hAB : A ≤ B)
    (fA : C(K, SSet.toTop.obj A.toSSet)) :
    (SSet.toTop.map B.ι).hom.comp
        ((SSet.toTop.map (SSet.Subcomplex.homOfLE hAB)).hom.comp fA) =
      (SSet.toTop.map A.ι).hom.comp fA := by
  -- Reassociate the realization maps, then collapse the simplicial inclusion chain on the owner
  -- side before evaluating on the source `K`.
  calc
    (SSet.toTop.map B.ι).hom.comp
        ((SSet.toTop.map (SSet.Subcomplex.homOfLE hAB)).hom.comp fA)
      = ((SSet.toTop.map (SSet.Subcomplex.homOfLE hAB) ≫ SSet.toTop.map B.ι).hom.comp fA) := by
          rfl
    _ = (SSet.toTop.map A.ι).hom.comp fA := by
          rw [← Functor.map_comp, SSet.Subcomplex.homOfLE_ι]

/-- Helper for Theorem 16.2.4: enlarging a finite singular stage along a subcomplex inclusion does
not change the induced map to `X` after precomposition. -/
theorem finiteSingularRealizationEvaluationFactorization_comp_homOfLE (X : TopCat.{u})
    {K : Type*} [TopologicalSpace K] {A B : (TopCat.toSSet.obj X).Subcomplex} (hAB : A ≤ B)
    (gA : C(K, SSet.toTop.obj A.toSSet)) :
    ((finiteSingularRealizationEvaluation X B).hom.comp
        ((SSet.toTop.map (SSet.Subcomplex.homOfLE hAB)).hom.comp gA)) =
      (finiteSingularRealizationEvaluation X A).hom.comp gA := by
  -- Reassociate the comparison map with the enlarged stage and invoke the owner normalization
  -- lemma proved just above.
  calc
    (finiteSingularRealizationEvaluation X B).hom.comp
        ((SSet.toTop.map (SSet.Subcomplex.homOfLE hAB)).hom.comp gA)
      = ((SSet.toTop.map (SSet.Subcomplex.homOfLE hAB) ≫
            finiteSingularRealizationEvaluation X B).hom.comp gA) := by
          rfl
    _ = (finiteSingularRealizationEvaluation X A).hom.comp gA := by
          rw [finiteSingularRealizationEvaluation_comp_homOfLE]

/-- Helper for Theorem 16.2.4: a simplicial map from a finite domain factors exactly through the
realization of its image subcomplex in `TopCat.toSSet.obj X`. -/
theorem finiteImageSubcomplexFactorization (X : TopCat.{u}) {K : SSet.{u}} [SSet.Finite K]
    (φ : K ⟶ TopCat.toSSet.obj X) :
    ∃ (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A })
      (φA : SSet.toTop.obj K ⟶ SSet.toTop.obj A.1.toSSet),
        φA ≫ SSet.toTop.map A.1.ι = SSet.toTop.map φ ∧
          φA ≫ finiteSingularRealizationEvaluation X A.1 =
            SSet.toTop.map φ ≫ sSetTopAdj.counit.app X := by
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
            simpa [A] using congrArg (fun ψ ↦ SSet.toTop.map ψ) (SSet.Subcomplex.toRange_ι φ)
  refine ⟨A, SSet.toTop.map (SSet.Subcomplex.toRange φ), ?_, ?_⟩
  · exact hFactor
  · -- After postcomposing with the counit, the same factorization becomes the finite-stage
    -- comparison map to `X`.
    calc
      SSet.toTop.map (SSet.Subcomplex.toRange φ) ≫ finiteSingularRealizationEvaluation X A.1
          = (SSet.toTop.map (SSet.Subcomplex.toRange φ) ≫ SSet.toTop.map A.1.ι) ≫
              sSetTopAdj.counit.app X := by
                simpa [finiteSingularRealizationEvaluation, Category.assoc]
      _ = SSet.toTop.map φ ≫ sSetTopAdj.counit.app X := by
            rw [hFactor]

/-- Helper for Theorem 16.2.4: a map `f : C(K, X)` factors through the realization of a finite
singular subcomplex of `X` up to homotopy. -/
def factorsThroughFiniteSingularRealization (K : TopCat.{u}) (X : TopCat.{u}) (f : C(K, X)) :
    Prop :=
  ∃ (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A })
    (g : C(K, SSet.toTop.obj A.1.toSSet)),
      ((finiteSingularRealizationEvaluation X A.1).hom.comp g).Homotopic f

/-- Helper for Theorem 16.2.4: once the image of `f` already lands in the realization of a
subcomplex and that realized inclusion is an embedding, `f` factors exactly through that realized
stage. -/
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

/-- Helper for Theorem 16.2.4: if a realized singular stage is compact and its inclusion into
`Γ X` is injective, then that inclusion is automatically a closed embedding. -/
theorem finiteSingularStageInclusion_isClosedEmbedding_of_compact_injective
    (X : TopCat.{u}) (A : (TopCat.toSSet.obj X).Subcomplex)
    [CompactSpace (SSet.toTop.obj A.toSSet)] [T2Space (gammaRealization X)]
    (hInj : Function.Injective ((SSet.toTop.map A.ι).hom)) :
    Topology.IsClosedEmbedding ((SSet.toTop.map A.ι).hom) := by
  -- Package the compact-domain/Hausdorff-codomain criterion once so the remaining frontier is
  -- only to prove compactness and injectivity for realized finite singular stages.
  let _ : T2Space (SSet.toTop.obj (TopCat.toSSet.obj X)) := by
    simpa [gammaRealization] using (inferInstance : T2Space (gammaRealization X))
  exact Continuous.isClosedEmbedding ((SSet.toTop.map A.ι).hom).continuous hInj

/-- Helper for Theorem 16.2.4: the realization of a finite simplicial set is compact because it
is covered by finitely many images of nondegenerate simplex legs. -/
instance finiteSimplicialRealization_compactSpace (K : SSet.{u}) [SSet.Finite K] :
    CompactSpace (SSet.toTop.obj K) := by
  classical
  rw [← isCompact_univ_iff]
  let simplexRange : K.N → Set (SSet.toTop.obj K) := fun s ↦
    Set.range ((SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)).hom)
  have hcompact : ∀ s : K.N, IsCompact (simplexRange s) := by
    intro s
    -- Each nondegenerate simplex contributes a compact image of one standard simplex.
    dsimp [simplexRange]
    let _ : CompactSpace (SimplexCategory.toTop.obj ⦋s.dim⦌) := by
      change CompactSpace (ULift (stdSimplex ℝ (Fin (s.dim + 1))))
      infer_instance
    let e :
        SSet.toTop.obj (SSet.stdSimplex.obj ⦋s.dim⦌) ≃ₜ SimplexCategory.toTop.obj ⦋s.dim⦌ :=
      TopCat.homeoOfIso (SSet.toTopSimplex.app ⦋s.dim⦌)
    let _ : CompactSpace (SSet.toTop.obj (SSet.stdSimplex.obj ⦋s.dim⦌)) := e.symm.compactSpace
    simpa using
      isCompact_range ((SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)).hom.continuous)
  have hcover : (⋃ s : K.N, simplexRange s) = Set.univ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      rcases realizationPoint_mem_nondegenerateSimplexRange K x with ⟨s, u, hu⟩
      exact Set.mem_iUnion.2 ⟨s, Set.mem_range.2 ⟨u, hu⟩⟩
  -- The finite family of compact simplex images already covers the whole realization.
  simpa [hcover] using isCompact_iUnion hcompact

/-- Helper for Theorem 16.2.4: realized inclusions of finite singular stages are injective. -/
theorem finiteSingularStageInclusion_injective
    (X : TopCat.{u}) (A : (TopCat.toSSet.obj X).Subcomplex) :
    Function.Injective ((SSet.toTop.map A.ι).hom) := by
  -- TODO: prove that realization of a simplicial subcomplex inclusion is injective, either by a
  -- direct quotient-model argument or by importing the missing mono-preservation API for
  -- `SSet.toTop`.
  sorry

/-- Helper for Theorem 16.2.4: realized inclusions of finite singular stages embed into `Γ X`. -/
theorem finiteSingularStageInclusion_isEmbedding
    (X : TopCat.{u}) (A : (TopCat.toSSet.obj X).Subcomplex) [SSet.Finite A] :
    Topology.IsEmbedding ((SSet.toTop.map A.ι).hom) := by
  let _ : CompactSpace (SSet.toTop.obj A.toSSet) :=
    finiteSimplicialRealization_compactSpace (K := A.toSSet)
  -- TODO: the compactness half is now available. The remaining blocker is to prove directly that
  -- realization of `A.ι` is injective, and then package the resulting embedding without relying on
  -- a missing global `T2Space (gammaRealization X)` instance.
  sorry

/-- Helper for Theorem 16.2.4: a closed embedding hypothesis is more than enough for the exact
range-subset factorization route. -/
theorem mapFactorsExactlyThroughRealizedSubcomplexOfClosedRangeSubset
    {K : Type*} [TopologicalSpace K] (X : TopCat.{u})
    (A : (TopCat.toSSet.obj X).Subcomplex)
    (hClosedEmbedding : Topology.IsClosedEmbedding ((SSet.toTop.map A.ι).hom))
    (f : C(K, gammaRealization X))
    (hRange : Set.range f ⊆ Set.range ((SSet.toTop.map A.ι).hom)) :
    ∃ fA : C(K, SSet.toTop.obj A.toSSet), (SSet.toTop.map A.ι).hom.comp fA = f := by
  -- Forget the extra closed-range information and feed the embedding part into the existing
  -- exact factorization lemma.
  exact
    mapFactorsExactlyThroughRealizedSubcomplexOfRangeSubset
      (X := X) A hClosedEmbedding.toIsEmbedding f hRange

/-- Helper for Theorem 16.2.4: once the range of a source map into `Γ X` is known to lie in a
chosen finite realized singular stage whose inclusion is an embedding, the map factors exactly
through that stage. -/
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

/-- Helper for Theorem 16.2.4: the exact finite-stage factorization route also accepts the
closed-embedding interface that naturally appears after the compactness step. -/
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
  -- Consume the closed-embedding owner data through the specialized exact factorization wrapper.
  rcases mapFactorsExactlyThroughRealizedSubcomplexOfClosedRangeSubset
      (X := X) A.1 hClosedEmbedding f hRange with ⟨fA, hfA⟩
  exact ⟨A, fA, hfA⟩

/-- Helper for Theorem 16.2.4: an exact factorization through a fixed target map transports
across a homeomorphism of source spaces. -/
theorem exactFactorization_transportSourceHomeomorph
    {K L W Y : Type*} [TopologicalSpace K] [TopologicalSpace L]
    [TopologicalSpace W] [TopologicalSpace Y]
    (h : K ≃ₜ L) (i : C(W, Y)) (f : C(K, Y)) (g : C(L, W))
    (hg : i.comp g = f.comp ⟨h.symm, h.symm.continuous_toFun⟩) :
    i.comp (g.comp ⟨h, h.continuous_toFun⟩) = f := by
  ext k
  -- Evaluate the transported factorization at `h k`, where the given exact factorization is
  -- already expressed on the `L`-side.
  have hEval : (i.comp g) (h k) = (f.comp ⟨h.symm, h.symm.continuous_toFun⟩) (h k) := by
    exact congrArg (fun m : C(L, Y) ↦ m (h k)) hg
  -- The inverse relation `h.symm (h k) = k` collapses the transported source comparison.
  simpa [ContinuousMap.comp_apply] using hEval

/-- Helper for Theorem 16.2.4: existence of an exact factorization through a fixed target map also
transports across a homeomorphism of source spaces. -/
theorem existsExactFactorization_transportSourceHomeomorph
    {K L W Y : Type*} [TopologicalSpace K] [TopologicalSpace L]
    [TopologicalSpace W] [TopologicalSpace Y]
    (h : K ≃ₜ L) (i : C(W, Y)) (f : C(K, Y))
    (hex :
      ∃ g : C(L, W), i.comp g = f.comp ⟨h.symm, h.symm.continuous_toFun⟩) :
    ∃ gK : C(K, W), i.comp gK = f := by
  rcases hex with ⟨g, hg⟩
  -- Precompose the witness on `L` with the chosen homeomorphism of sources.
  refine ⟨g.comp ⟨h, h.continuous_toFun⟩, ?_⟩
  exact exactFactorization_transportSourceHomeomorph h i f g hg

/-- Helper for Theorem 16.2.4: a sphere-boundary map into `Γ X` factors exactly through a finite
realized singular stage as soon as that stage is known to contain its image and to embed into
`Γ X`. -/
theorem boundaryMapFactorsExactlyThroughFiniteSingularStageOfRangeCover
    (X : TopCat.{u}) (n : ℕ) (f : C(sphereBoundary n, gammaRealization X))
    (hData :
      ∃ (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A }),
        Topology.IsEmbedding ((SSet.toTop.map A.1.ι).hom) ∧
          Set.range f ⊆ Set.range ((SSet.toTop.map A.1.ι).hom)) :
    ∃ (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A })
      (fA : C(sphereBoundary n, SSet.toTop.obj A.1.toSSet)),
        (SSet.toTop.map A.1.ι).hom.comp fA = f := by
  -- This is the sphere-boundary specialization of the generic exact range-cover factorization.
  exact mapFactorsExactlyThroughFiniteSingularStageOfRangeCover X f hData

/-- Helper for Theorem 16.2.4: a disk map into `Γ X` factors exactly through a finite realized
singular stage as soon as that stage is known to contain its image and to embed into `Γ X`. -/
theorem diskMapFactorsExactlyThroughFiniteSingularStageOfRangeCover
    (X : TopCat.{u}) (n : ℕ) (g : C(unitDisk n, gammaRealization X))
    (hData :
      ∃ (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A }),
        Topology.IsEmbedding ((SSet.toTop.map A.1.ι).hom) ∧
          Set.range g ⊆ Set.range ((SSet.toTop.map A.1.ι).hom)) :
    ∃ (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A })
      (gA : C(unitDisk n, SSet.toTop.obj A.1.toSSet)),
        (SSet.toTop.map A.1.ι).hom.comp gA = g := by
  -- This is the disk specialization of the same exact range-cover factorization interface.
  exact mapFactorsExactlyThroughFiniteSingularStageOfRangeCover X g hData

/-- Helper for Theorem 16.2.4: for a fixed compact source `K` and finite singular subcomplex `A`,
the comparison map `|A| ⟶ X` reflects homotopies out of `K`. -/
def finiteSingularRealizationEvaluationReflectsHomotopy (K : TopCat.{u}) (X : TopCat.{u})
    (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A }) : Prop :=
  ∀ {g₀ g₁ : C(K, SSet.toTop.obj A.1.toSSet)},
    (((finiteSingularRealizationEvaluation X A.1).hom.comp g₀).Homotopic
      ((finiteSingularRealizationEvaluation X A.1).hom.comp g₁)) →
      g₀.Homotopic g₁

/-- Helper for Theorem 16.2.4: evaluating an exact boundary-stage factorization in `Γ X` through
the counit recovers the corresponding boundary map in `X`. -/
theorem finiteBoundaryStageEvaluation_eq (X : TopCat.{u}) {K : Type*} [TopologicalSpace K]
    (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A })
    (f : C(K, gammaRealization X)) (fA : C(K, SSet.toTop.obj A.1.toSSet))
    (hf : (SSet.toTop.map A.1.ι).hom.comp fA = f) :
    ((finiteSingularRealizationEvaluation X A.1).hom.comp fA) =
      ((sSetTopAdj.counit.app X).hom.comp f) := by
  -- Rewrite the exact boundary factorization through the counit so the left endpoint is expressed
  -- on the chosen finite singular stage.
  calc
    ((finiteSingularRealizationEvaluation X A.1).hom.comp fA)
      = ((sSetTopAdj.counit.app X).hom.comp ((SSet.toTop.map A.1.ι).hom.comp fA)) := by
          rfl
    _ = ((sSetTopAdj.counit.app X).hom.comp f) := by
          rw [hf]

/-- Helper for Theorem 16.2.4: an exact boundary-stage factorization turns the original HELP track
into a homotopy whose left endpoint already lies in the chosen finite singular stage. -/
def boundaryHelpHomotopyOnFiniteStage (X : TopCat.{u}) (n : ℕ)
    (f : C(sphereBoundary n, gammaRealization X)) (g : C(unitDisk n, X))
    (H : (((sSetTopAdj.counit.app X).hom.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))))
    (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A })
    (fA : C(sphereBoundary n, SSet.toTop.obj A.1.toSSet))
    (hf : (SSet.toTop.map A.1.ι).hom.comp fA = f) :
    (((finiteSingularRealizationEvaluation X A.1).hom.comp fA).Homotopy
      (g.comp (sphereBoundaryInclusion n))) :=
  -- Cast the original boundary track across the exact finite-stage equality proved just above.
  H.cast
    ((finiteBoundaryStageEvaluation_eq (X := X) (K := sphereBoundary n) A f fA hf).symm)
    rfl

/-- Helper for Theorem 16.2.4: once the boundary HELP track has been normalized to a finite stage,
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
  -- Move the normalized boundary track through the stage enlargement by the already-proved
  -- `homOfLE` comparison identity.
  H.cast
    ((finiteSingularRealizationEvaluationFactorization_comp_homOfLE
      (X := X) (K := sphereBoundary n) hAB fA).symm)
    rfl

/-- Helper for Theorem 16.2.4: if every point of the compact image of `f` has a neighborhood
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

/-- Helper for Theorem 16.2.4: the image of a compact-source map into `Γ X` lies in one common
finite realized singular stage. -/
theorem compactImage_mem_commonFiniteSingularStage
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (X : TopCat.{u}) (f : C(K, gammaRealization X)) :
    ∃ (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A }),
      Set.range f ⊆ Set.range ((SSet.toTop.map A.1.ι).hom) := by
  -- Route correction: the compactness bookkeeping has been isolated into
  -- `compactImage_mem_commonFiniteSingularStage_of_localRangeCover`. The only remaining blocker is
  -- the local simplex-neighborhood statement for points of `Γ X`.
  refine compactImage_mem_commonFiniteSingularStage_of_localRangeCover (X := X) f ?_
  intro x hx
  -- TODO: prove that each point of `Γ X` has a neighborhood contained in one realized finite
  -- singular stage by refining `gammaRealizationPoint_mem_finiteSingularStage` to a local
  -- simplex-chart statement for geometric realization.
  sorry

/-- Helper for Theorem 16.2.4: a compact-source map into `Γ X` should factor exactly through one
finite realized singular stage. -/
theorem compactMapFactorsExactlyThroughFiniteSingularStage
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (X : TopCat.{u}) (f : C(K, gammaRealization X)) :
    ∃ (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A })
      (fA : C(K, SSet.toTop.obj A.1.toSSet)),
        (SSet.toTop.map A.1.ι).hom.comp fA = f := by
  -- First compress the compact image to one finite owner, then consume the exact range-cover
  -- interface using the realized-stage embedding theorem proved above.
  rcases compactImage_mem_commonFiniteSingularStage (X := X) f with ⟨A, hRange⟩
  let _ : SSet.Finite A.1 := A.2
  have hEmbedding :
      Topology.IsEmbedding ((SSet.toTop.map A.1.ι).hom) :=
    finiteSingularStageInclusion_isEmbedding X A.1
  rcases mapFactorsExactlyThroughFiniteSingularStageOfRangeCover
      (X := X) f ⟨A, hEmbedding, hRange⟩ with ⟨A', fA, hfA⟩
  exact ⟨A', fA, hfA⟩

/-- Helper for Theorem 16.2.4: a boundary map into `Γ X` should factor exactly through one finite
singular stage of `X`. -/
theorem boundaryMapFactorsExactlyThroughFiniteSingularStage
    (X : TopCat.{u}) (n : ℕ) (f : C(sphereBoundary n, gammaRealization X)) :
    ∃ (A : { A : (TopCat.toSSet.obj X).Subcomplex // SSet.Finite A })
      (fA : C(sphereBoundary n, SSet.toTop.obj A.1.toSSet)),
        (SSet.toTop.map A.1.ι).hom.comp fA = f := by
  -- Specialize the generic compact-source factorization to the sphere-boundary model.
  simpa using compactMapFactorsExactlyThroughFiniteSingularStage (X := X) f

/-- Helper for Theorem 16.2.4: a disk map into `Γ X` should factor exactly through one finite
singular stage of `X`. -/
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

/-- Helper for Theorem 16.2.4: once the exact boundary and disk finite-stage owners are in place,
the fixed-degree Chapter 9 two-stage homotopy-group package for the counit follows. -/
theorem singularRealizationEvaluation_hasPiInjectiveSurjectiveSucc
    (X : TopCat.{u}) (n : ℕ) :
    HasPiInjectiveSurjectiveSucc n ((sSetTopAdj.counit.app X).hom) := by
  -- Route correction: the direct Chapter 9 owner is the fixed-degree
  -- `HasPiInjectiveSurjectiveSucc n` statement. The generalized-loop normalization is already
  -- stable, so the remaining work is to factor the geometric sphere/disk representatives into one
  -- common finite singular stage and then close the injective/surjective fields there.
  -- Route correction: this final assembly is blocked only by the generic compact-source
  -- factorization theorem above; the later `sup`/`homOfLE` normalization lemmas already compile.
  -- TODO: combine `singularRealizationEvaluation_eStar_commutesGenLoop` with
  -- `boundaryMapFactorsExactlyThroughFiniteSingularStage`,
  -- `diskMapFactorsExactlyThroughFiniteSingularStage`, and the existing
  -- `finiteSingularSubcomplex_sup(_sup)` plus `homOfLE` normalization lemmas to build the
  -- `injective` and `surjectiveSucc` fields of `HasPiInjectiveSurjectiveSucc n`.
  sorry

/-- Helper for Theorem 16.2.4: the direct `π`-group control needed for the counit should be proved
from finite simplicial representatives, rather than by extending the older HELP-only middle
layer. -/
theorem singularRealizationEvaluation_hasPiInjectiveSurjectiveSuccAll (X : TopCat.{u}) :
    ∀ n : ℕ, HasPiInjectiveSurjectiveSucc n ((sSetTopAdj.counit.app X).hom) := by
  intro n
  -- Reduce the all-degree statement to the fixed-degree Chapter 9 owner isolated just above.
  exact singularRealizationEvaluation_hasPiInjectiveSurjectiveSucc X n

/-- Helper for Theorem 16.2.4: the weak-equivalence proof for the counit should be organized
through compact-CW finite reduction rather than direct HELP filling. -/
theorem singularRealizationEvaluation_isWeakEquivalenceOfCompactCWFiniteReduction
    (X : TopCat.{u}) :
    IsWeakEquivalence ((sSetTopAdj.counit.app X).hom) := by
  -- Route correction: assemble weak equivalence from the established `0`-equivalence and the
  -- direct all-degree `π`-group control, instead of routing through the stalled HELP translation.
  exact
    isWeakEquivalenceOfIsNEquivalenceZeroAndHasPiInjectiveSurjectiveSuccAll
      (singularRealizationEvaluation_isNEquivalenceZero X)
      (singularRealizationEvaluation_hasPiInjectiveSurjectiveSuccAll X)

/-- Theorem 16.2.4: the canonical map `Γ X ⟶ X`, realized as
`sSetTopAdj.counit.app X : SSet.toTop.obj (TopCat.toSSet.obj X) ⟶ X`, is a weak
equivalence. -/
instance singularRealizationEvaluation_isWeakEquivalence (X : TopCat.{u}) :
    IsWeakEquivalence ((sSetTopAdj.counit.app X).hom) := by
  -- The main theorem now delegates to the compact-CW finite-reduction route isolated above.
  exact singularRealizationEvaluation_isWeakEquivalenceOfCompactCWFiniteReduction X

/-- Companion theorem exposing the weak-equivalence fact for
`sSetTopAdj.counit.app X`. -/
theorem isWeakEquivalence_singularRealizationEvaluation (X : TopCat.{u}) :
    IsWeakEquivalence ((sSetTopAdj.counit.app X).hom) :=
  inferInstance
