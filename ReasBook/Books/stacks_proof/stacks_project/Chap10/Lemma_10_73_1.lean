import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Limits Abelian

universe u

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R')

attribute [local instance] HasDerivedCategory.standard

/-- Helper for Chap10 Lemma 10 73 1: extension of scalars along `R → R'`. -/
private abbrev extScalars :=
  ModuleCat.extendScalars (algebraMap R R')

/-- Helper for Chap10 Lemma 10 73 1: restriction of scalars along `R → R'`. -/
private abbrev resScalars :=
  ModuleCat.restrictScalars (algebraMap R R')

/-- Helper for Chap10 Lemma 10 73 1: the extension/restriction adjunction for `R → R'`. -/
private abbrev baseChangeAdj :=
  ModuleCat.extendRestrictScalarsAdj (algebraMap R R')

/-- Helper for Chap10 Lemma 10 73 1: the cochain-level extension/restriction adjunction
satisfies the left triangle identity componentwise. -/
private lemma cochainBaseChangeAdj_left_triangle_components
    [(extScalars (R := R) (R' := R')).Additive]
    (K : HomologicalComplex (ModuleCat.{u} R) (ComplexShape.up ℤ)) :
    ((extScalars (R := R) (R' := R')).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (baseChangeAdj (R := R) (R' := R')).unit
          (ComplexShape.up ℤ)).app K) ≫
      (NatTrans.mapHomologicalComplex (baseChangeAdj (R := R) (R' := R')).counit
        (ComplexShape.up ℤ)).app
        (((extScalars (R := R) (R' := R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      𝟙 (((extScalars (R := R) (R' := R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  -- The cochain statement is checked degreewise and then reduced to the module-level triangle.
  ext i x
  simpa using LinearMap.congr_fun
    (ModuleCat.hom_ext_iff.mp
      ((baseChangeAdj (R := R) (R' := R')).left_triangle_components (K.X i))) x

/-- Helper for Chap10 Lemma 10 73 1: the cochain-level extension/restriction adjunction
satisfies the right triangle identity componentwise. -/
private lemma cochainBaseChangeAdj_right_triangle_components
    [(extScalars (R := R) (R' := R')).Additive]
    (K : HomologicalComplex (ModuleCat.{u} R') (ComplexShape.up ℤ)) :
    (NatTrans.mapHomologicalComplex (baseChangeAdj (R := R) (R' := R')).unit
        (ComplexShape.up ℤ)).app
        (((resScalars (R := R) (R' := R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      ((resScalars (R := R) (R' := R')).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (baseChangeAdj (R := R) (R' := R')).counit
          (ComplexShape.up ℤ)).app K) =
      𝟙 (((resScalars (R := R) (R' := R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  -- Again, evaluation at each degree turns the cochain goal into the original adjunction triangle.
  ext i x
  simpa using LinearMap.congr_fun
    (ModuleCat.hom_ext_iff.mp
      ((baseChangeAdj (R := R) (R' := R')).right_triangle_components (K.X i))) x

/-- Helper for Chap10 Lemma 10 73 1: extension and restriction of scalars form an adjunction on
cochain complexes. -/
private abbrev cochainBaseChangeAdj
    [(extScalars (R := R) (R' := R')).Additive] :
    (extScalars (R := R) (R' := R')).mapHomologicalComplex (ComplexShape.up ℤ) ⊣
      (resScalars (R := R) (R' := R')).mapHomologicalComplex (ComplexShape.up ℤ) where
  unit := NatTrans.mapHomologicalComplex (baseChangeAdj (R := R) (R' := R')).unit
    (ComplexShape.up ℤ)
  counit := NatTrans.mapHomologicalComplex (baseChangeAdj (R := R) (R' := R')).counit
    (ComplexShape.up ℤ)
  left_triangle_components := cochainBaseChangeAdj_left_triangle_components
  right_triangle_components := cochainBaseChangeAdj_right_triangle_components

/-- Helper for Chap10 Lemma 10 73 1: the cochain-level base-change adjunction localizes to the
derived categories. -/
private abbrev derivedBaseChangeAdj
    [PreservesFiniteLimits (extScalars (R := R) (R' := R'))]
    [(extScalars (R := R) (R' := R')).Additive]
    [(resScalars (R := R) (R' := R')).Additive] :
    (extScalars (R := R) (R' := R')).mapDerivedCategory ⊣
      (resScalars (R := R) (R' := R')).mapDerivedCategory :=
  letI : CatCommSq
      ((extScalars (R := R) (R' := R')).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q (C := ModuleCat.{u} R))
      (DerivedCategory.Q (C := ModuleCat.{u} R'))
      ((extScalars (R := R) (R' := R')).mapDerivedCategory) :=
    ⟨((extScalars (R := R) (R' := R')).mapDerivedCategoryFactors).symm⟩
  letI : CatCommSq
      ((resScalars (R := R) (R' := R')).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q (C := ModuleCat.{u} R'))
      (DerivedCategory.Q (C := ModuleCat.{u} R))
      ((resScalars (R := R) (R' := R')).mapDerivedCategory) :=
    ⟨((resScalars (R := R) (R' := R')).mapDerivedCategoryFactors).symm⟩
  Adjunction.localization (cochainBaseChangeAdj (R := R) (R' := R'))
    (DerivedCategory.Q (C := ModuleCat.{u} R))
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (DerivedCategory.Q (C := ModuleCat.{u} R'))
    (HomologicalComplex.quasiIso (ModuleCat.{u} R') (ComplexShape.up ℤ))
    ((extScalars (R := R) (R' := R')).mapDerivedCategory)
    ((resScalars (R := R) (R' := R')).mapDerivedCategory)

/-- Helper for Chap10 Lemma 10 73 1: the cochain-complex counit for restriction followed by
extension is compatible with the integer shift. -/
private lemma mapHomologicalComplex_comp_counit_commShift
    [(extScalars (R := R) (R' := R')).Additive] :
    NatTrans.CommShift
      (show (resScalars (R := R) (R' := R')).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (extScalars (R := R) (R' := R')).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
          𝟭 (HomologicalComplex (ModuleCat.{u} R') (ComplexShape.up ℤ)) from
        NatTrans.mapHomologicalComplex (baseChangeAdj (R := R) (R' := R')).counit
          (ComplexShape.up ℤ)) ℤ := by
  -- Check shift-compatibility degreewise; the cochain-complex shift comparison is componentwise
  -- the identity, so the counit component is unchanged.
  constructor
  intro a
  ext K i x
  simp [Functor.commShiftIso_comp_hom_app]

/-- Helper for Chap10 Lemma 10 73 1: the cochain-complex unit for extension followed by
restriction is compatible with the integer shift. -/
private lemma mapHomologicalComplex_comp_unit_commShift
    [(extScalars (R := R) (R' := R')).Additive] :
    NatTrans.CommShift
      (show 𝟭 (HomologicalComplex (ModuleCat.{u} R) (ComplexShape.up ℤ)) ⟶
          (extScalars (R := R) (R' := R')).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (resScalars (R := R) (R' := R')).mapHomologicalComplex (ComplexShape.up ℤ) from
        NatTrans.mapHomologicalComplex (baseChangeAdj (R := R) (R' := R')).unit
          (ComplexShape.up ℤ)) ℤ := by
  -- As for the counit, after evaluating in each degree all shift-comparison maps are identities.
  constructor
  intro a
  ext K i x
  simp [Functor.commShiftIso_comp_hom_app]

/-- Helper for Chap10 Lemma 10 73 1: the cochain-level base-change adjunction is compatible
with integer shifts. -/
private lemma cochainBaseChangeAdj_commShift
    [(extScalars (R := R) (R' := R')).Additive] :
    (cochainBaseChangeAdj (R := R) (R' := R')).CommShift ℤ := by
  -- Package the previously checked unit compatibility; the adjunction API supplies counit
  -- compatibility from the triangle identities.
  exact Adjunction.CommShift.mk' (cochainBaseChangeAdj (R := R) (R' := R')) ℤ
    (mapHomologicalComplex_comp_unit_commShift (R := R) (R' := R'))

/-
Domain triage:
- `source-facing`: `moduleCatExtFlatBaseChangeComparison` is the textbook flat base-change map on
  `Ext`.
- `core/canonical`: the owner abstractions are `Functor.mapExtAddHom` for `extScalars` and
  `resScalars`, together with the unit/counit of `ModuleCat.extendRestrictScalarsAdj`.
- `bridge/view`: `moduleCatExtFlatBaseChangeAdjointComparison` is the adjoint transpose of the
  source-facing map, expressed directly from the owner API rather than from a parallel wrapper.

Primitive data are only the ring map and the two modules. The comparison maps are derived from the
change-of-rings adjunction and `Ext` functoriality, so no extra packaged data is introduced.
-/

/-- Helper for Chap10 Lemma 10 73 1: the textbook base-change comparison
`Ext^i_{R'}(R' ⊗[R] M, N') → Ext^i_R(M, N'|_R)`, which is the canonical owner-object form of the
source-facing textbook map `Ext^i_{R'}(M ⊗[R] R', N') → Ext^i_R(M, N'|_R)` via tensor symmetry. -/
def moduleCatExtFlatBaseChangeComparison (i : ℕ) :
    Ext (extScalars.obj M) N' i →+ Ext M (resScalars.obj N') i :=
  AddMonoidHom.comp
    ((Ext.mk₀ (baseChangeAdj.unit.app M)).precomp (resScalars.obj N') (zero_add i))
    (resScalars.mapExtAddHom (extScalars.obj M) N' i)

/-- Helper for Chap10 Lemma 10 73 1: the adjoint-transposed comparison from `Ext_R(M, N'|_R)` to
`Ext_{R'}(R' ⊗[R] M, N')`, obtained by applying `Ext` to extension of scalars and then
postcomposing with the adjunction counit. This is a `bridge/view` companion to the source-facing
map of Lemma `10.73.1`. -/
abbrev moduleCatExtFlatBaseChangeAdjointComparison
    (hf : (algebraMap R R').Flat) (i : ℕ) :
    Ext M (resScalars.obj N') i →+ Ext (extScalars.obj M) N' i :=
  let adj := ModuleCat.extendRestrictScalarsAdj (algebraMap R R')
  letI : PreservesFiniteLimits extScalars :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  letI : extScalars.Additive := adj.left_adjoint_additive
  AddMonoidHom.comp
    ((Ext.mk₀ (adj.counit.app N')).postcomp (extScalars.obj M) (add_zero i))
    (extScalars.mapExtAddHom M (resScalars.obj N') i)

/-- Helper for Chap10 Lemma 10 73 1: the source-facing comparison sends an `Ext` class to the
class obtained by restricting scalars and precomposing with the adjunction unit. -/
private lemma moduleCatExtFlatBaseChangeComparison_apply (i : ℕ)
    (x : Ext (extScalars.obj M) N' i) :
    moduleCatExtFlatBaseChangeComparison M N' i x =
      (Ext.mk₀ (baseChangeAdj.unit.app M)).comp (x.mapExactFunctor resScalars) (zero_add i) := by
  rfl

/-- Helper for Chap10 Lemma 10 73 1: the adjoint-transposed comparison sends an `Ext` class to
the class obtained by extending scalars and postcomposing with the adjunction counit. -/
private lemma moduleCatExtFlatBaseChangeAdjointComparison_apply
    (hf : (algebraMap R R').Flat)
    [PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R R'))]
    [(ModuleCat.extendScalars (algebraMap R R')).Additive]
    (i : ℕ) (x : Ext M (resScalars.obj N') i) :
    moduleCatExtFlatBaseChangeAdjointComparison M N' hf i x =
      (x.mapExactFunctor (ModuleCat.extendScalars (algebraMap R R'))).comp
        (Ext.mk₀ ((baseChangeAdj).counit.app N')) (add_zero i) := by
  rfl

/-- Helper for Chap10 Lemma 10 73 1: on degree-zero generators, restriction followed by
extension and postcomposition with the counit is adjunction counit naturality. -/
private lemma mapExactFunctor_mk₀_extendRestrict_counit_comp
    [PreservesFiniteLimits (extScalars (R := R) (R' := R'))]
    [(extScalars (R := R) (R' := R')).Additive]
    (f : ((ModuleCat.extendScalars (algebraMap R R')).obj M) ⟶ N') :
    (((Ext.mk₀ f : Ext ((ModuleCat.extendScalars (algebraMap R R')).obj M) N' 0).mapExactFunctor
        (ModuleCat.restrictScalars (algebraMap R R'))).mapExactFunctor
        (ModuleCat.extendScalars (algebraMap R R'))).comp
        (Ext.mk₀ (baseChangeAdj.counit.app N')) (add_zero 0) =
      (Ext.mk₀ (baseChangeAdj.counit.app
        ((ModuleCat.extendScalars (algebraMap R R')).obj M))).comp
        (Ext.mk₀ f) (zero_add 0) := by
  -- Normalize both sides to `Ext.mk₀` and use the ordinary counit naturality square.
  rw [Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀]
  rw [Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]
  rw [Adjunction.counit_naturality]
  rfl

/-- Helper for Chap10 Lemma 10 73 1: on degree-zero generators, precomposing after extension and
restriction is adjunction unit naturality. -/
private lemma unit_comp_mapExactFunctor_mk₀_extendRestrict
    [PreservesFiniteLimits (extScalars (R := R) (R' := R'))]
    [(extScalars (R := R) (R' := R')).Additive]
    (f : M ⟶ ((ModuleCat.restrictScalars (algebraMap R R')).obj N')) :
    (Ext.mk₀ (baseChangeAdj.unit.app M)).comp
        (((Ext.mk₀ f : Ext M ((ModuleCat.restrictScalars (algebraMap R R')).obj N') 0).mapExactFunctor
          (ModuleCat.extendScalars (algebraMap R R'))).mapExactFunctor
          (ModuleCat.restrictScalars (algebraMap R R'))) (zero_add 0) =
      (Ext.mk₀ f).comp (Ext.mk₀ (baseChangeAdj.unit.app
        ((ModuleCat.restrictScalars (algebraMap R R')).obj N'))) (add_zero 0) := by
  -- Normalize both sides to `Ext.mk₀` and use the ordinary unit naturality square.
  rw [Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀]
  calc
    (Ext.mk₀ (baseChangeAdj.unit.app M)).comp
        (Ext.mk₀ ((ModuleCat.restrictScalars (algebraMap R R')).map
          ((ModuleCat.extendScalars (algebraMap R R')).map f))) (zero_add 0) =
        Ext.mk₀ (baseChangeAdj.unit.app M ≫
          (ModuleCat.restrictScalars (algebraMap R R')).map
            ((ModuleCat.extendScalars (algebraMap R R')).map f)) := by
      exact Ext.mk₀_comp_mk₀ _ _
    _ = Ext.mk₀ (f ≫ baseChangeAdj.unit.app
        ((ModuleCat.restrictScalars (algebraMap R R')).obj N')) := by
      rw [Adjunction.unit_naturality]
      rfl
    _ = (Ext.mk₀ f).comp (Ext.mk₀ (baseChangeAdj.unit.app
        ((ModuleCat.restrictScalars (algebraMap R R')).obj N'))) (add_zero 0) := by
      simpa using (Ext.mk₀_comp_mk₀ f
        (baseChangeAdj.unit.app
          ((ModuleCat.restrictScalars (algebraMap R R')).obj N'))).symm

/-- Helper for Chap10 Lemma 10 73 1: the counit roundtrip identity propagates across the
connecting `Ext` class of a short exact sequence. -/
private lemma mapExactFunctor_extendRestrict_counit_comp_extClass
    [PreservesFiniteLimits (extScalars (R := R) (R' := R'))]
    [(extScalars (R := R) (R' := R')).Additive]
    (S : ShortComplex (ModuleCat.{u} R')) (hS : S.ShortExact) (n : ℕ)
    (y : Ext (extScalars.obj M) S.X₃ n)
    (hy : ((y.mapExactFunctor (ModuleCat.restrictScalars (algebraMap R R'))).mapExactFunctor
          (ModuleCat.extendScalars (algebraMap R R'))).comp
          (Ext.mk₀ (baseChangeAdj.counit.app S.X₃)) (add_zero n) =
        (Ext.mk₀ (baseChangeAdj.counit.app
          ((ModuleCat.extendScalars (algebraMap R R')).obj M))).comp y (zero_add n)) :
    (((y.comp hS.extClass (show n + 1 = n + 1 by rfl)).mapExactFunctor
          (ModuleCat.restrictScalars (algebraMap R R'))).mapExactFunctor
          (ModuleCat.extendScalars (algebraMap R R'))).comp
          (Ext.mk₀ (baseChangeAdj.counit.app S.X₁)) (add_zero (n + 1)) =
        (Ext.mk₀ (baseChangeAdj.counit.app
          ((ModuleCat.extendScalars (algebraMap R R')).obj M))).comp
          (y.comp hS.extClass (show n + 1 = n + 1 by rfl)) (zero_add (n + 1)) := by
  -- Route correction: instead of comparing localized derived unit/counit transports, use the
  -- naturality of the short-exact extension class for the counit morphism of short complexes.
  let φ : ((S.map (resScalars (R := R) (R' := R'))).map
      (extScalars (R := R) (R' := R'))) ⟶ S :=
    { τ₁ := (baseChangeAdj (R := R) (R' := R')).counit.app S.X₁
      τ₂ := (baseChangeAdj (R := R) (R' := R')).counit.app S.X₂
      τ₃ := (baseChangeAdj (R := R) (R' := R')).counit.app S.X₃
      comm₁₂ := by
        dsimp [ShortComplex.map]
        exact (Adjunction.counit_naturality (baseChangeAdj (R := R) (R' := R')) S.f).symm
      comm₂₃ := by
        dsimp [ShortComplex.map]
        exact (Adjunction.counit_naturality (baseChangeAdj (R := R) (R' := R')) S.g).symm }
  have hnat := ShortComplex.ShortExact.extClass_naturality
    ((hS.map_of_exact (resScalars (R := R) (R' := R'))).map_of_exact
      (extScalars (R := R) (R' := R'))) hS φ
  dsimp [φ] at hnat
  -- Push both exact functors through the composite, then replace the mapped extension class by
  -- the target extension class using the naturality square.
  rw [Ext.mapExactFunctor_comp]
  rw [Ext.mapExactFunctor_comp]
  rw [Ext.mapExactFunctor_extClass (F := resScalars (R := R) (R' := R')) hS]
  have hmapExtClass :
      Ext.mapExactFunctor (ModuleCat.extendScalars (algebraMap R R'))
          ((hS.map_of_exact (ModuleCat.restrictScalars (algebraMap R R'))).extClass) =
        ((hS.map_of_exact (ModuleCat.restrictScalars (algebraMap R R'))).map_of_exact
          (ModuleCat.extendScalars (algebraMap R R'))).extClass := by
    exact Ext.mapExactFunctor_extClass (F := ModuleCat.extendScalars (algebraMap R R'))
      (hS.map_of_exact (ModuleCat.restrictScalars (algebraMap R R')))
  erw [hmapExtClass]
  refine (Ext.comp_assoc
    (Ext.mapExactFunctor (ModuleCat.extendScalars (algebraMap R R'))
      (Ext.mapExactFunctor (ModuleCat.restrictScalars (algebraMap R R')) y))
    ((hS.map_of_exact (ModuleCat.restrictScalars (algebraMap R R'))).map_of_exact
      (ModuleCat.extendScalars (algebraMap R R'))).extClass
    (Ext.mk₀ (baseChangeAdj.counit.app S.X₁))
    (show n + 1 = n + 1 by rfl) (add_zero 1)
    (show n + 1 + 0 = n + 1 by omega)).trans ?_
  erw [hnat]
  refine (Ext.comp_assoc
    (Ext.mapExactFunctor (ModuleCat.extendScalars (algebraMap R R'))
      (Ext.mapExactFunctor (ModuleCat.restrictScalars (algebraMap R R')) y))
    (Ext.mk₀ (baseChangeAdj.counit.app S.X₃)) hS.extClass
    (add_zero n) (zero_add 1) (show n + 0 + 1 = n + 1 by omega)).symm.trans ?_
  rw [hy]
  exact Ext.comp_assoc
    (Ext.mk₀ (baseChangeAdj.counit.app
      ((ModuleCat.extendScalars (algebraMap R R')).obj M))) y hS.extClass
    (zero_add n) (show n + 1 = n + 1 by rfl) (show 0 + n + 1 = n + 1 by omega)

/-- Helper for Chap10 Lemma 10 73 1: double functoriality through restriction and extension,
followed by the counit on the target, is the same as precomposing the original `Ext` class with
the counit on the source. -/
private lemma mapExactFunctor_extendRestrict_counit_comp
    [PreservesFiniteLimits (extScalars (R := R) (R' := R'))]
    [(extScalars (R := R) (R' := R')).Additive]
    (i : ℕ) (x : Ext ((ModuleCat.extendScalars (algebraMap R R')).obj M) N' i) :
    ((x.mapExactFunctor (ModuleCat.restrictScalars (algebraMap R R'))).mapExactFunctor
        (ModuleCat.extendScalars (algebraMap R R'))).comp
        (Ext.mk₀ (baseChangeAdj.counit.app N')) (add_zero i) =
      (Ext.mk₀ (baseChangeAdj.counit.app
        ((ModuleCat.extendScalars (algebraMap R R')).obj M))).comp x (zero_add i) := by
  -- Route correction: prove arbitrary degree by dimension shifting in the second `Ext` variable,
  -- using the degree-zero generator computation as the base case.
  induction i generalizing N' with
  | zero =>
      obtain ⟨f, hf⟩ :=
        (Ext.mk₀_bijective ((ModuleCat.extendScalars (algebraMap R R')).obj M) N').2 x
      rw [← hf]
      exact mapExactFunctor_mk₀_extendRestrict_counit_comp (M := M) (N' := N') f
  | succ n ih =>
      let S := ShortComplex.mk (Injective.ι N') (cokernel.π (Injective.ι N'))
        (cokernel.condition (Injective.ι N'))
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
      have hxzero : x.comp (Ext.mk₀ S.f) (add_zero (n + 1)) = 0 := by
        exact Ext.eq_zero_of_injective (x.comp (Ext.mk₀ S.f) (add_zero (n + 1)))
      obtain ⟨y, hy⟩ :=
        Ext.covariant_sequence_exact₁
          ((ModuleCat.extendScalars (algebraMap R R')).obj M) hS x hxzero (n₀ := n) rfl
      -- Replace the successor class by a connecting class and apply the short-exact step.
      rw [← hy]
      exact mapExactFunctor_extendRestrict_counit_comp_extClass (M := M)
        (S := S) hS n y (ih S.X₃ y)

/-- Helper for Chap10 Lemma 10 73 1: the unit roundtrip identity propagates across the
connecting `Ext` class of a short exact sequence. -/
private lemma unit_comp_mapExactFunctor_extendRestrict_extClass
    [PreservesFiniteLimits (extScalars (R := R) (R' := R'))]
    [(extScalars (R := R) (R' := R')).Additive]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (n : ℕ)
    (y : Ext M S.X₃ n)
    (hy : (Ext.mk₀ (baseChangeAdj.unit.app M)).comp
          ((y.mapExactFunctor (ModuleCat.extendScalars (algebraMap R R'))).mapExactFunctor
          (ModuleCat.restrictScalars (algebraMap R R'))) (zero_add n) =
        y.comp (Ext.mk₀ (baseChangeAdj.unit.app S.X₃)) (add_zero n)) :
    (Ext.mk₀ (baseChangeAdj.unit.app M)).comp
        ((((y.comp hS.extClass (show n + 1 = n + 1 by rfl)).mapExactFunctor
          (ModuleCat.extendScalars (algebraMap R R'))).mapExactFunctor
          (ModuleCat.restrictScalars (algebraMap R R')))) (zero_add (n + 1)) =
      (y.comp hS.extClass (show n + 1 = n + 1 by rfl)).comp
        (Ext.mk₀ (baseChangeAdj.unit.app S.X₁)) (add_zero (n + 1)) := by
  -- Route correction: the successor step is short-exact naturality for the unit morphism of
  -- short complexes, not a localized derived-category transport comparison.
  let φ : S ⟶ ((S.map (extScalars (R := R) (R' := R'))).map
      (resScalars (R := R) (R' := R'))) :=
    { τ₁ := (baseChangeAdj (R := R) (R' := R')).unit.app S.X₁
      τ₂ := (baseChangeAdj (R := R) (R' := R')).unit.app S.X₂
      τ₃ := (baseChangeAdj (R := R) (R' := R')).unit.app S.X₃
      comm₁₂ := by
        dsimp [ShortComplex.map]
        exact Adjunction.unit_naturality (baseChangeAdj (R := R) (R' := R')) S.f
      comm₂₃ := by
        dsimp [ShortComplex.map]
        exact Adjunction.unit_naturality (baseChangeAdj (R := R) (R' := R')) S.g }
  have hnat := ShortComplex.ShortExact.extClass_naturality hS
    ((hS.map_of_exact (extScalars (R := R) (R' := R'))).map_of_exact
      (resScalars (R := R) (R' := R'))) φ
  dsimp [φ] at hnat
  -- Push exact functors through the connecting composite, then use unit naturality of the
  -- extension class and the induction hypothesis at the right endpoint.
  rw [Ext.mapExactFunctor_comp]
  rw [Ext.mapExactFunctor_comp]
  rw [Ext.mapExactFunctor_extClass (F := extScalars (R := R) (R' := R')) hS]
  have hmapExtClass :
      Ext.mapExactFunctor (ModuleCat.restrictScalars (algebraMap R R'))
          ((hS.map_of_exact (ModuleCat.extendScalars (algebraMap R R'))).extClass) =
        ((hS.map_of_exact (ModuleCat.extendScalars (algebraMap R R'))).map_of_exact
          (ModuleCat.restrictScalars (algebraMap R R'))).extClass := by
    exact Ext.mapExactFunctor_extClass (F := ModuleCat.restrictScalars (algebraMap R R'))
      (hS.map_of_exact (ModuleCat.extendScalars (algebraMap R R')))
  erw [hmapExtClass]
  refine (Ext.comp_assoc
    (Ext.mk₀ (baseChangeAdj.unit.app M))
    (Ext.mapExactFunctor (ModuleCat.restrictScalars (algebraMap R R'))
      (Ext.mapExactFunctor (ModuleCat.extendScalars (algebraMap R R')) y))
    ((hS.map_of_exact (ModuleCat.extendScalars (algebraMap R R'))).map_of_exact
      (ModuleCat.restrictScalars (algebraMap R R'))).extClass
    (zero_add n) (show n + 1 = n + 1 by rfl)
    (show 0 + n + 1 = n + 1 by omega)).symm.trans ?_
  rw [hy]
  refine (Ext.comp_assoc y (Ext.mk₀ (baseChangeAdj.unit.app S.X₃))
    ((hS.map_of_exact (ModuleCat.extendScalars (algebraMap R R'))).map_of_exact
      (ModuleCat.restrictScalars (algebraMap R R'))).extClass
    (add_zero n) (show 0 + 1 = 1 by rfl) (show n + 0 + 1 = n + 1 by omega)).trans ?_
  erw [← hnat]
  exact (Ext.comp_assoc y hS.extClass (Ext.mk₀ (baseChangeAdj.unit.app S.X₁))
    (show n + 1 = n + 1 by rfl) (add_zero 1)
    (show n + 1 + 0 = n + 1 by omega)).symm

/-- Helper for Chap10 Lemma 10 73 1: precomposing the double functorial image through extension
and restriction with the unit is the same as postcomposing the original `Ext` class with the unit
on the target. -/
private lemma unit_comp_mapExactFunctor_extendRestrict
    [PreservesFiniteLimits (extScalars (R := R) (R' := R'))]
    [(extScalars (R := R) (R' := R')).Additive]
    (i : ℕ) (x : Ext M ((ModuleCat.restrictScalars (algebraMap R R')).obj N') i) :
    (Ext.mk₀ (baseChangeAdj.unit.app M)).comp
        ((x.mapExactFunctor (ModuleCat.extendScalars (algebraMap R R'))).mapExactFunctor
          (ModuleCat.restrictScalars (algebraMap R R'))) (zero_add i) =
      x.comp (Ext.mk₀ (baseChangeAdj.unit.app
        ((ModuleCat.restrictScalars (algebraMap R R')).obj N'))) (add_zero i) := by
  -- Route correction: strengthen internally to every `R`-module target and use the same
  -- injective dimension-shift argument as for the counit.
  have h :
      ∀ (j : ℕ) (Y : ModuleCat.{u} R) (x : Ext M Y j),
        (Ext.mk₀ (baseChangeAdj.unit.app M)).comp
            ((x.mapExactFunctor (ModuleCat.extendScalars (algebraMap R R'))).mapExactFunctor
              (ModuleCat.restrictScalars (algebraMap R R'))) (zero_add j) =
          x.comp (Ext.mk₀ (baseChangeAdj.unit.app Y)) (add_zero j) := by
    intro j
    induction j with
  | zero =>
      intro Y x
      obtain ⟨f, hf⟩ := (Ext.mk₀_bijective M Y).2 x
      rw [← hf]
      -- Degree zero reduces to the ordinary naturality square for the adjunction unit.
      rw [Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀]
      calc
        (Ext.mk₀ (baseChangeAdj.unit.app M)).comp
            (Ext.mk₀ ((ModuleCat.restrictScalars (algebraMap R R')).map
              ((ModuleCat.extendScalars (algebraMap R R')).map f))) (zero_add 0) =
            Ext.mk₀ (baseChangeAdj.unit.app M ≫
              (ModuleCat.restrictScalars (algebraMap R R')).map
                ((ModuleCat.extendScalars (algebraMap R R')).map f)) := by
          exact Ext.mk₀_comp_mk₀ _ _
        _ = Ext.mk₀ (f ≫ baseChangeAdj.unit.app Y) := by
          rw [Adjunction.unit_naturality]
          rfl
        _ = (Ext.mk₀ f).comp (Ext.mk₀ (baseChangeAdj.unit.app Y)) (add_zero 0) := by
          simpa using (Ext.mk₀_comp_mk₀ f (baseChangeAdj.unit.app Y)).symm
  | succ n ih =>
      intro Y x
      let S := ShortComplex.mk (Injective.ι Y) (cokernel.π (Injective.ι Y))
        (cokernel.condition (Injective.ι Y))
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
      have hxzero : x.comp (Ext.mk₀ S.f) (add_zero (n + 1)) = 0 := by
        exact Ext.eq_zero_of_injective (x.comp (Ext.mk₀ S.f) (add_zero (n + 1)))
      obtain ⟨y, hy⟩ :=
        Ext.covariant_sequence_exact₁ M hS x hxzero (n₀ := n) rfl
      -- Rewrite the successor class as a connecting class and apply the short-exact step.
      rw [← hy]
      exact unit_comp_mapExactFunctor_extendRestrict_extClass (M := M)
        (S := S) hS n y (ih S.X₃ y)
  exact h i ((ModuleCat.restrictScalars (algebraMap R R')).obj N') x

/-- Helper for Chap10 Lemma 10 73 1: on the shifted-Hom representative, the source-facing
comparison followed by its adjoint transpose acts by the identity. -/
private lemma moduleCatExtFlatBaseChange_left_roundtrip_transport
    (hf : (algebraMap R R').Flat) (i : ℕ) (x : Ext (extScalars.obj M) N' i) :
    ((moduleCatExtFlatBaseChangeAdjointComparison M N' hf i)
        ((moduleCatExtFlatBaseChangeComparison M N' i) x)).hom =
      x.hom := by
  -- Route correction: rewrite the whole left roundtrip on `x.hom` once, so the remaining core is
  -- exactly the adjunction `homEquiv` followed by `homEquiv.symm`.
  let adj := baseChangeAdj (R := R) (R' := R')
  letI : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R R')) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  letI : (ModuleCat.extendScalars (algebraMap R R')).Additive := adj.left_adjoint_additive
  letI := HasDerivedCategory.standard (ModuleCat R')
  -- Prove the inverse law at the `Ext` level, then project it to shifted-Hom representatives.
  have hExt :
      (moduleCatExtFlatBaseChangeAdjointComparison M N' hf i)
          ((moduleCatExtFlatBaseChangeComparison M N' i) x) =
        x := by
    rw [moduleCatExtFlatBaseChangeAdjointComparison_apply (M := M) (N' := N') hf,
      moduleCatExtFlatBaseChangeComparison_apply (M := M) (N' := N')]
    have hmap :
        Ext.mapExactFunctor (ModuleCat.extendScalars (algebraMap R R'))
            ((Ext.mk₀ (baseChangeAdj.unit.app M)).comp
              (Ext.mapExactFunctor (resScalars (R := R) (R' := R')) x)
              (zero_add i)) =
          (Ext.mapExactFunctor (ModuleCat.extendScalars (algebraMap R R'))
            (Ext.mk₀ (baseChangeAdj.unit.app M))).comp
            (Ext.mapExactFunctor (ModuleCat.extendScalars (algebraMap R R'))
              (Ext.mapExactFunctor (resScalars (R := R) (R' := R')) x))
            (zero_add i) := by
      simpa [resScalars] using
        (Ext.mapExactFunctor_comp
          (F := ModuleCat.extendScalars (algebraMap R R'))
          (α := Ext.mk₀ (baseChangeAdj.unit.app M))
          (β := Ext.mapExactFunctor (ModuleCat.restrictScalars (algebraMap R R')) x)
          (h := zero_add i))
    refine (congrArg (fun y ↦ y.comp (Ext.mk₀ (baseChangeAdj.counit.app N')) (add_zero i))
      hmap).trans ?_
    rw [Ext.mapExactFunctor_mk₀]
    rw [Ext.comp_assoc]
    rotate_left 3
    · exact i
    swap
    · omega
    swap
    · omega
    refine (congrArg
      (fun y ↦ (Ext.mk₀ ((ModuleCat.extendScalars (algebraMap R R')).map
        (baseChangeAdj.unit.app M))).comp y (zero_add i))
      (mapExactFunctor_extendRestrict_counit_comp (M := M) (N' := N') i x)).trans ?_
    refine (Ext.mk₀_comp_mk₀_assoc
      ((ModuleCat.extendScalars (algebraMap R R')).map (baseChangeAdj.unit.app M))
      (baseChangeAdj.counit.app ((ModuleCat.extendScalars (algebraMap R R')).obj M))
      (α := x)).trans ?_
    refine (congrArg (fun f ↦ (Ext.mk₀ f).comp x (zero_add i))
      ((baseChangeAdj (R := R) (R' := R')).left_triangle_components M)).trans ?_
    rw [Ext.mk₀_id_comp]
  exact congrArg Ext.hom hExt

/-- Helper for Chap10 Lemma 10 73 1: on the shifted-Hom representative, the source-facing
comparison followed by its adjoint transpose acts by the identity. -/
private lemma moduleCatExtFlatBaseChange_leftInverse_hom
    (hf : (algebraMap R R').Flat) (i : ℕ) (x : Ext (extScalars.obj M) N' i) :
    ((moduleCatExtFlatBaseChangeAdjointComparison M N' hf i)
        ((moduleCatExtFlatBaseChangeComparison M N' i) x)).hom =
      x.hom := by
  -- Reduce the left inverse to the cached whole-composite normalization.
  letI := HasDerivedCategory.standard (ModuleCat R')
  simpa using moduleCatExtFlatBaseChange_left_roundtrip_transport
    (M := M) (N' := N') hf i x

/-- Helper for Chap10 Lemma 10 73 1: the hom-level left inverse identity upgrades to an equality
of `Ext` classes. -/
private lemma moduleCatExtFlatBaseChange_leftInverse_pointwise
    (hf : (algebraMap R R').Flat) (i : ℕ) (x : Ext (extScalars.obj M) N' i) :
    (moduleCatExtFlatBaseChangeAdjointComparison M N' hf i)
        ((moduleCatExtFlatBaseChangeComparison M N' i) x) =
      x := by
  -- Repackage the shifted-Hom identity as an equality in `Ext`.
  letI := HasDerivedCategory.standard (ModuleCat R')
  rw [Ext.ext_iff]
  exact moduleCatExtFlatBaseChange_leftInverse_hom (M := M) (N' := N') hf i x

/-- Helper for Chap10 Lemma 10 73 1: on the shifted-Hom representative, the adjoint transpose
followed by the source-facing comparison acts by the identity. -/
private lemma moduleCatExtFlatBaseChange_right_roundtrip_transport
    (hf : (algebraMap R R').Flat) (i : ℕ) (x : Ext M (resScalars.obj N') i) :
    ((moduleCatExtFlatBaseChangeComparison M N' i)
        ((moduleCatExtFlatBaseChangeAdjointComparison M N' hf i) x)).hom =
      x.hom := by
  -- Route correction: rewrite the whole right roundtrip on `x.hom` once, so the remaining core is
  -- exactly the adjunction `homEquiv.symm` followed by `homEquiv`.
  let adj := baseChangeAdj (R := R) (R' := R')
  letI : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R R')) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  letI : (ModuleCat.extendScalars (algebraMap R R')).Additive := adj.left_adjoint_additive
  letI := HasDerivedCategory.standard (ModuleCat R)
  -- Prove the inverse law at the `Ext` level, then project it to shifted-Hom representatives.
  have hExt :
      (moduleCatExtFlatBaseChangeComparison M N' i)
          ((moduleCatExtFlatBaseChangeAdjointComparison M N' hf i) x) =
        x := by
    rw [moduleCatExtFlatBaseChangeComparison_apply (M := M) (N' := N'),
      moduleCatExtFlatBaseChangeAdjointComparison_apply (M := M) (N' := N') hf]
    have hmap :
        Ext.mapExactFunctor (resScalars (R := R) (R' := R'))
            ((Ext.mapExactFunctor (ModuleCat.extendScalars (algebraMap R R')) x).comp
              (Ext.mk₀ (baseChangeAdj.counit.app N'))
              (add_zero i)) =
          (Ext.mapExactFunctor (resScalars (R := R) (R' := R'))
              (Ext.mapExactFunctor (ModuleCat.extendScalars (algebraMap R R')) x)).comp
            (Ext.mapExactFunctor (resScalars (R := R) (R' := R'))
              (Ext.mk₀ (baseChangeAdj.counit.app N')))
            (add_zero i) := by
      simpa [resScalars] using
        (Ext.mapExactFunctor_comp
          (F := ModuleCat.restrictScalars (algebraMap R R'))
          (α := Ext.mapExactFunctor (ModuleCat.extendScalars (algebraMap R R')) x)
          (β := Ext.mk₀ (baseChangeAdj.counit.app N')) (h := add_zero i))
    refine (congrArg (fun y ↦ (Ext.mk₀ (baseChangeAdj.unit.app M)).comp y (zero_add i))
      hmap).trans ?_
    rw [Ext.mapExactFunctor_mk₀]
    have hsum : 0 + i + 0 = i := by omega
    refine (Ext.comp_assoc (Ext.mk₀ (baseChangeAdj.unit.app M))
      (Ext.mapExactFunctor resScalars
        (Ext.mapExactFunctor (ModuleCat.extendScalars (algebraMap R R')) x))
      (Ext.mk₀ (resScalars.map (baseChangeAdj.counit.app N')))
      (zero_add i) (add_zero i) hsum).symm.trans ?_
    refine (congrArg
      (fun y ↦ y.comp (Ext.mk₀ (resScalars.map (baseChangeAdj.counit.app N'))) (add_zero i))
      (unit_comp_mapExactFunctor_extendRestrict (M := M) (N' := N') i x)).trans ?_
    refine (Ext.comp_assoc_of_third_deg_zero x
      (Ext.mk₀ (baseChangeAdj.unit.app ((ModuleCat.restrictScalars (algebraMap R R')).obj N')))
      (Ext.mk₀ (resScalars.map (baseChangeAdj.counit.app N')))
      (add_zero i)).trans ?_
    rw [Ext.mk₀_comp_mk₀]
    refine (congrArg (fun f ↦ x.comp (Ext.mk₀ f) (add_zero i))
      ((baseChangeAdj (R := R) (R' := R')).right_triangle_components N')).trans ?_
    rw [Ext.comp_mk₀_id]
  exact congrArg Ext.hom hExt

/-- Helper for Chap10 Lemma 10 73 1: on the shifted-Hom representative, the adjoint transpose
followed by the source-facing comparison acts by the identity. -/
private lemma moduleCatExtFlatBaseChange_rightInverse_hom
    (hf : (algebraMap R R').Flat) (i : ℕ) (x : Ext M (resScalars.obj N') i) :
    ((moduleCatExtFlatBaseChangeComparison M N' i)
        ((moduleCatExtFlatBaseChangeAdjointComparison M N' hf i) x)).hom =
      x.hom := by
  -- Reduce the right inverse to the cached whole-composite normalization.
  letI := HasDerivedCategory.standard (ModuleCat R)
  simpa using moduleCatExtFlatBaseChange_right_roundtrip_transport
    (M := M) (N' := N') hf i x

/-- Helper for Chap10 Lemma 10 73 1: the hom-level right inverse identity upgrades to an equality
of `Ext` classes. -/
private lemma moduleCatExtFlatBaseChange_rightInverse_pointwise
    (hf : (algebraMap R R').Flat) (i : ℕ) (x : Ext M (resScalars.obj N') i) :
    (moduleCatExtFlatBaseChangeComparison M N' i)
        ((moduleCatExtFlatBaseChangeAdjointComparison M N' hf i) x) =
      x := by
  -- Repackage the shifted-Hom identity as an equality in `Ext`.
  letI := HasDerivedCategory.standard (ModuleCat R)
  rw [Ext.ext_iff]
  exact moduleCatExtFlatBaseChange_rightInverse_hom (M := M) (N' := N') hf i x

/-- Helper for Chap10 Lemma 10 73 1: the adjoint-transposed base-change comparison is a left
inverse to the source-facing base-change comparison. -/
private lemma moduleCatExtFlatBaseChange_leftInverse
    (hf : (algebraMap R R').Flat) (i : ℕ) :
    AddMonoidHom.comp
        (moduleCatExtFlatBaseChangeAdjointComparison M N' hf i)
        (moduleCatExtFlatBaseChangeComparison M N' i) =
      AddMonoidHom.id (Ext (extScalars.obj M) N' i) := by
  -- After the pointwise `Ext` identity is proved, the additive-hom equality is extensional.
  rw [AddMonoidHom.ext_iff]
  intro x
  exact moduleCatExtFlatBaseChange_leftInverse_pointwise (M := M) (N' := N') hf i x

/-- Helper for Chap10 Lemma 10 73 1: the adjoint-transposed base-change comparison is a right
inverse to the source-facing base-change comparison. -/
private lemma moduleCatExtFlatBaseChange_rightInverse
    (hf : (algebraMap R R').Flat) (i : ℕ) :
    AddMonoidHom.comp
        (moduleCatExtFlatBaseChangeComparison M N' i)
        (moduleCatExtFlatBaseChangeAdjointComparison M N' hf i) =
      AddMonoidHom.id (Ext M (resScalars.obj N') i) := by
  -- Again, the additive-hom equality is just the pointwise `Ext` inverse law.
  rw [AddMonoidHom.ext_iff]
  intro x
  exact moduleCatExtFlatBaseChange_rightInverse_pointwise (M := M) (N' := N') hf i x

-- Proof sketch: choose a projective resolution `P• → M`; flatness makes `R' ⊗[R] P•` a
-- projective resolution of `R' ⊗[R] M`, and Lemma `10.14.3` identifies the two Hom complexes
-- `Hom_{R'}(R' ⊗[R] P•, N')` and `Hom_R(P•, N')`, so the induced comparison on homology is
-- bijective in every degree.
/-- Chap10 Lemma 10 73 1: for a flat ring map `R → R'`, an `R`-module `M`, and an
`R'`-module `N'`, the textbook natural map
`Ext^i_{R'}(M ⊗[R] R', N') → Ext^i_R(M, N'|_R)`
is an isomorphism for every `i`; equivalently, the canonical owner-object comparison
`Ext^i_{R'}(R' ⊗[R] M, N') → Ext^i_R(M, N'|_R)` is an isomorphism. -/
@[stacks 087N]
theorem moduleCat_ext_flat_baseChange_isIso
    (hf : (algebraMap R R').Flat) (i : ℕ) :
    IsIso (AddCommGrpCat.ofHom (moduleCatExtFlatBaseChangeComparison M N' i)) := by
  -- The inverse is the adjoint-transposed comparison, and the two compositions are the identity.
  refine ⟨⟨AddCommGrpCat.ofHom (moduleCatExtFlatBaseChangeAdjointComparison M N' hf i), ?_, ?_⟩⟩
  · simpa using congrArg AddCommGrpCat.ofHom
      (moduleCatExtFlatBaseChange_leftInverse (M := M) (N' := N') hf i)
  · simpa using congrArg AddCommGrpCat.ofHom
      (moduleCatExtFlatBaseChange_rightInverse (M := M) (N' := N') hf i)

/-- Companion reformulation of Chap10 Lemma 10 73 1 as bijectivity of the source-facing
textbook map. -/
theorem moduleCat_ext_flat_baseChange_bijective
    (hf : (algebraMap R R').Flat) (i : ℕ) :
    Function.Bijective (moduleCatExtFlatBaseChangeComparison M N' i) := by
  let f := AddCommGrpCat.ofHom (moduleCatExtFlatBaseChangeComparison M N' i)
  letI : IsIso f := moduleCat_ext_flat_baseChange_isIso M N' hf i
  exact ⟨(AddCommGrpCat.mono_iff_injective f).mp inferInstance,
    (AddCommGrpCat.epi_iff_surjective f).mp inferInstance⟩

/-- Companion to Chap10 Lemma 10 73 1: the adjoint-transposed comparison is likewise an
isomorphism under the flatness hypothesis. -/
theorem moduleCat_ext_flat_baseChange_adjoint_isIso
    (hf : (algebraMap R R').Flat) (i : ℕ) :
    IsIso (AddCommGrpCat.ofHom (moduleCatExtFlatBaseChangeAdjointComparison M N' hf i)) := by
  -- Swap the two inverse identities proved above.
  refine ⟨⟨AddCommGrpCat.ofHom (moduleCatExtFlatBaseChangeComparison M N' i), ?_, ?_⟩⟩
  · simpa using congrArg AddCommGrpCat.ofHom
      (moduleCatExtFlatBaseChange_rightInverse (M := M) (N' := N') hf i)
  · simpa using congrArg AddCommGrpCat.ofHom
      (moduleCatExtFlatBaseChange_leftInverse (M := M) (N' := N') hf i)

/-- Companion to Chap10 Lemma 10 73 1: the adjoint-transposed comparison is a bijection. -/
theorem moduleCat_ext_flat_baseChange_adjoint_bijective
    (hf : (algebraMap R R').Flat) (i : ℕ) :
    Function.Bijective (moduleCatExtFlatBaseChangeAdjointComparison M N' hf i) := by
  let f := AddCommGrpCat.ofHom (moduleCatExtFlatBaseChangeAdjointComparison M N' hf i)
  letI : IsIso f := moduleCat_ext_flat_baseChange_adjoint_isIso M N' hf i
  exact ⟨(AddCommGrpCat.mono_iff_injective f).mp inferInstance,
    (AddCommGrpCat.epi_iff_surjective f).mp inferInstance⟩

end
