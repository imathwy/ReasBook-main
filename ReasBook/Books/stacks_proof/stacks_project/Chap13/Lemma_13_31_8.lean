import Mathlib
import StacksProject_2024.Chap12.Definition_12_31_2
import StacksProject_2024.Chap12.Lemma_12_31_1
import StacksProject_2024.Chap12.Lemma_12_31_4
import StacksProject_2024.Chap13.Lemma_13_31_3
import StacksProject_2024.Chap13.Lemma_13_31_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open Opposite
open OrderDual (ofDual toDual)

universe u v

namespace CategoryTheory

namespace SequentialInverseSystem

noncomputable section

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

private abbrev AbSeq := SequentialInverseSystem AddCommGrpCat.{v}

open CochainComplex
open CochainComplex.HomComplex

/-- Helper for Lemma 13.31.8: a compatible section of the underlying `Type`-valued diagram of
abelian groups determines a point of the categorical inverse limit. -/
private noncomputable def limitOfUnderlyingSections
    {J : Type*} [Category J] (F : J ⥤ AddCommGrpCat)
    [HasLimit F] [HasLimit (F ⋙ forget AddCommGrpCat)]
    (s : (F ⋙ forget AddCommGrpCat).sections) :
    ↑(Limits.limit F) :=
  -- Proof comment: transport the compatible underlying family across the preserved-limit
  -- isomorphism for `forget AddCommGrpCat`.
  (preservesLimitIso (forget AddCommGrpCat) F).inv
    ((Types.limitEquivSections (F ⋙ forget AddCommGrpCat)).symm s)

/-- Helper for Lemma 13.31.8: the limit point built from a compatible underlying section has the
expected coordinate at every stage. -/
private theorem limit_π_limitOfUnderlyingSections
    {J : Type*} [Category J] (F : J ⥤ AddCommGrpCat)
    [HasLimit F] [HasLimit (F ⋙ forget AddCommGrpCat)]
    (s : (F ⋙ forget AddCommGrpCat).sections) (j : J) :
    Limits.limit.π F j (limitOfUnderlyingSections F s) = s.val j := by
  -- Proof comment: compute the coordinate after passing to the underlying `Type`-valued limit.
  let t : limit (F ⋙ forget AddCommGrpCat) :=
    (Types.limitEquivSections (F ⋙ forget AddCommGrpCat)).symm s
  have hπ :
      limit.π F j ((preservesLimitIso (forget AddCommGrpCat) F).inv t) =
        limit.π (F ⋙ forget AddCommGrpCat) j t := by
    exact congrArg (fun k => k t) (preservesLimitIso_inv_π (forget AddCommGrpCat) F j)
  simpa [limitOfUnderlyingSections, t] using
    hπ.trans (Types.limitEquivSections_symm_apply (F ⋙ forget AddCommGrpCat) s j)

/-- Helper for Lemma 13.31.8: a point of a categorical inverse limit determines the corresponding
compatible family in the underlying `Type`-valued diagram. -/
private noncomputable def underlyingSectionsOfLimit
    {J : Type*} [Category J] (F : J ⥤ AddCommGrpCat)
    [HasLimit F] [HasLimit (F ⋙ forget AddCommGrpCat)] (x : ↑(Limits.limit F)) :
    (F ⋙ forget AddCommGrpCat).sections :=
  Types.limitEquivSections _ ((preservesLimitIso (forget AddCommGrpCat) F).hom x)

/-- Helper for Lemma 13.31.8: reading off the section attached to a limit point recovers each
limit projection. -/
private theorem limit_π_underlyingSectionsOfLimit
    {J : Type*} [Category J] (F : J ⥤ AddCommGrpCat)
    [HasLimit F] [HasLimit (F ⋙ forget AddCommGrpCat)] (x : ↑(Limits.limit F)) (j : J) :
    Limits.limit.π F j x = (underlyingSectionsOfLimit F x).val j := by
  -- Proof comment: evaluate the preserved-limit comparison at `x` and read off the resulting
  -- underlying compatible family.
  let t : limit (F ⋙ forget AddCommGrpCat) :=
    (preservesLimitIso (forget AddCommGrpCat) F).hom x
  have hπ :
      limit.π F j x =
        limit.π (F ⋙ forget AddCommGrpCat) j t := by
    simpa [t] using
      (congrArg (fun k => k x) (preservesLimitIso_hom_π (forget AddCommGrpCat) F j)).symm
  have ht :
      (Types.limitEquivSections (F ⋙ forget AddCommGrpCat)).symm
          (underlyingSectionsOfLimit F x) = t := by
    simpa [underlyingSectionsOfLimit, t] using
      (Equiv.symm_apply_apply (Types.limitEquivSections (F ⋙ forget AddCommGrpCat))
        ((preservesLimitIso (forget AddCommGrpCat) F).hom x))
  have hsections :
      limit.π (F ⋙ forget AddCommGrpCat) j t =
        (underlyingSectionsOfLimit F x).val j := by
    rw [← ht]
    exact Types.limitEquivSections_symm_apply (F ⋙ forget AddCommGrpCat)
      (underlyingSectionsOfLimit F x) j
  exact hπ.trans hsections

/-- Helper for Lemma 13.31.8: a limit point is determined by its underlying compatible family. -/
private theorem underlyingSectionsOfLimit_injective
    {J : Type*} [Category J] (F : J ⥤ AddCommGrpCat)
    [HasLimit F] [HasLimit (F ⋙ forget AddCommGrpCat)] :
    Function.Injective (underlyingSectionsOfLimit F) := by
  intro x y hxy
  -- Proof comment: compare the underlying `Type`-valued limit points and transport back through
  -- the preserved-limit isomorphism for `forget AddCommGrpCat`.
  have hlimit :
      (preservesLimitIso (forget AddCommGrpCat) F).hom x =
        (preservesLimitIso (forget AddCommGrpCat) F).hom y := by
    exact (Types.limitEquivSections (F ⋙ forget AddCommGrpCat)).injective hxy
  simpa using congrArg ((preservesLimitIso (forget AddCommGrpCat) F).inv) hlimit

/-- Helper for Lemma 13.31.8: equal morphisms in `AddCommGrpCat` agree on each element. -/
private theorem addCommGrpCat_congr_fun
    {A B : AddCommGrpCat.{v}} {f g : A ⟶ B} (h : f = g) (x : A) :
    f x = g x := by
  simpa using congrFun (congrArg (fun t ↦ (AddCommGrpCat.Hom.hom t : A → B)) h) x

/-- Helper for Lemma 13.31.8: taking degree `n` of the inverse limit complex agrees with the
inverse limit of the degree-`n` tower. -/
private noncomputable def limitDegreeIso
    (I : SequentialInverseSystem (CochainComplex 𝒜 ℤ)) (n : ℤ)
    [∀ m : ℤ, HasLimit (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) m)] :
    (limit I).X n ≅ limit (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) n) :=
  -- Proof comment: evaluation preserves the chosen limit of cochain complexes.
  IsLimit.conePointUniqueUpToIso
    (isLimitOfPreserves (HomologicalComplex.eval 𝒜 (up ℤ) n) (limit.isLimit I))
    (limit.isLimit (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) n))

/-- Helper for Lemma 13.31.8: the degreewise limit isomorphism intertwines the stage projections
with the evaluated projections. -/
private theorem limitDegreeIso_hom_π
    (I : SequentialInverseSystem (CochainComplex 𝒜 ℤ)) (n : ℤ)
    [∀ m : ℤ, HasLimit (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) m)] (k : ℕᵒᵖ) :
    (limitDegreeIso (𝒜 := 𝒜) I n).hom ≫
        limit.π (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) n) k =
      (limit.π I k).f n := by
  -- Proof comment: this is exactly the universal property comparison of the preserved limit.
  simpa [limitDegreeIso] using
    IsLimit.conePointUniqueUpToIso_hom_comp
      (isLimitOfPreserves (HomologicalComplex.eval 𝒜 (up ℤ) n) (limit.isLimit I))
      (limit.isLimit (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) n)) k

/-- Helper for Lemma 13.31.8: the inverse of the degreewise limit isomorphism also matches the
evaluated stage projections. -/
private theorem limitDegreeIso_inv_π
    (I : SequentialInverseSystem (CochainComplex 𝒜 ℤ)) (n : ℤ)
    [∀ m : ℤ, HasLimit (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) m)] (k : ℕᵒᵖ) :
    (limitDegreeIso (𝒜 := 𝒜) I n).inv ≫ (limit.π I k).f n =
      limit.π (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) n) k := by
  have h :=
    congrArg
      (fun t ↦ (limitDegreeIso (𝒜 := 𝒜) I n).inv ≫ t)
      (limitDegreeIso_hom_π (𝒜 := 𝒜) I n k)
  simpa [Category.assoc] using h.symm

/-- Helper for Lemma 13.31.8: postcomposition with a target morphism preserves the zero cochain. -/
private theorem homComplexCochainPostcomp_map_zero
    {K L M : CochainComplex 𝒜 ℤ} (σ : L ⟶ M) (n : ℤ) :
    (0 : Cochain K L n).comp (Cochain.ofHom σ) (add_zero n) = 0 := by
  simp

/-- Helper for Lemma 13.31.8: postcomposition with a target morphism is additive on cochains. -/
private theorem homComplexCochainPostcomp_map_add
    {K L M : CochainComplex 𝒜 ℤ} (σ : L ⟶ M) (n : ℤ)
    (z₁ z₂ : Cochain K L n) :
    (z₁ + z₂).comp (Cochain.ofHom σ) (add_zero n) =
      z₁.comp (Cochain.ofHom σ) (add_zero n) +
        z₂.comp (Cochain.ofHom σ) (add_zero n) := by
  simp

/-- Helper for Lemma 13.31.8: postcomposition along `σ` induces an additive map on the degree-`n`
cochains of `HomComplex K L`. -/
private def homComplexCochainPostcomp
    {K L M : CochainComplex 𝒜 ℤ} (σ : L ⟶ M) (n : ℤ) :
    Cochain K L n →+ Cochain K M n where
  toFun z := z.comp (Cochain.ofHom σ) (add_zero n)
  map_zero' := homComplexCochainPostcomp_map_zero σ n
  map_add' := homComplexCochainPostcomp_map_add σ n

/-- Helper for Lemma 13.31.8: postcomposition by the identity map acts trivially on cochains. -/
private theorem homComplexCochainPostcomp_id
    {K L : CochainComplex 𝒜 ℤ} (n : ℤ) :
    homComplexCochainPostcomp (K := K) (L := L) (M := L) (𝟙 L) n = AddMonoidHom.id _ := by
  ext z p q hpq
  simp [homComplexCochainPostcomp]

/-- Helper for Lemma 13.31.8: consecutive postcompositions compose on Hom-complex cochains. -/
private theorem homComplexCochainPostcomp_comp
    {K L M N : CochainComplex 𝒜 ℤ} (σ : L ⟶ M) (τ : M ⟶ N) (n : ℤ) :
    homComplexCochainPostcomp (K := K) (L := L) (M := N) (σ ≫ τ) n =
      (homComplexCochainPostcomp (K := K) (L := M) (M := N) τ n).comp
        (homComplexCochainPostcomp (K := K) (L := L) (M := M) σ n) := by
  ext z p q hpq
  simp [homComplexCochainPostcomp]

/-- Helper for Lemma 13.31.8: evaluating postcomposition on a cochain component composes the
component with the target map. -/
private theorem homComplexCochainPostcomp_v
    {K L M : CochainComplex 𝒜 ℤ} (σ : L ⟶ M) (n p q : ℤ)
    (hpq : p + n = q) (z : Cochain K L n) :
    (homComplexCochainPostcomp (K := K) (L := L) (M := M) σ n z).v p q hpq =
      z.v p q hpq ≫ σ.f q := by
  simpa [homComplexCochainPostcomp]

/-- Helper for Lemma 13.31.8: the degree-`n` Hom-complex tower has transition maps given by
postcomposition with the transition maps of the inverse system. -/
private def homComplexDegreeTower
    (M : CochainComplex 𝒜 ℤ) (I : SequentialInverseSystem (CochainComplex 𝒜 ℤ)) (n : ℤ) :
    AbSeq :=
  { obj := fun k ↦ AddCommGrpCat.of (Cochain M (I.obj k) n)
    map := fun {i j} f ↦
      AddCommGrpCat.ofHom
        (homComplexCochainPostcomp (K := M) (L := I.obj i) (M := I.obj j) (I.map f) n)
    map_id := by
      intro k
      ext z p q hpq
      simp [homComplexCochainPostcomp]
    map_comp := by
      intro i j k f g
      ext z p q hpq
      simp [homComplexCochainPostcomp, Functor.map_comp]
 }

/-- Helper for Lemma 13.31.8: the differential on each Hom complex is natural in the target
complex. -/
private theorem homComplexDegreeTowerDelta_naturality
    (M : CochainComplex 𝒜 ℤ) (I : SequentialInverseSystem (CochainComplex 𝒜 ℤ))
    (n : ℤ) {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (homComplexDegreeTower M I n).map f ≫ (HomComplex M (I.obj j)).d n (n + 1) =
      (HomComplex M (I.obj i)).d n (n + 1) ≫ (homComplexDegreeTower M I (n + 1)).map f := by
  -- Proof comment: both sides are the standard `δ_comp_ofHom` compatibility for postcomposition.
  ext z
  change
    δ n (n + 1)
        (homComplexCochainPostcomp (K := M) (L := I.obj i) (M := I.obj j) (I.map f) n z) =
      homComplexCochainPostcomp (K := M) (L := I.obj i) (M := I.obj j) (I.map f) (n + 1)
        (δ n (n + 1) z)
  simpa [homComplexCochainPostcomp] using
    (CochainComplex.HomComplex.δ_comp_ofHom (n := n) z (I.map f) (n + 1))

/-- Helper for Lemma 13.31.8: the Hom-complex differential defines a natural transformation
between adjacent degree towers. -/
private def homComplexDegreeTowerDelta
    (M : CochainComplex 𝒜 ℤ) (I : SequentialInverseSystem (CochainComplex 𝒜 ℤ)) (n : ℤ) :
    homComplexDegreeTower M I n ⟶ homComplexDegreeTower M I (n + 1) :=
  { app := fun k ↦ (HomComplex M (I.obj k)).d n (n + 1)
    naturality := fun _ _ f ↦ homComplexDegreeTowerDelta_naturality M I n f }

/-- Helper for Lemma 13.31.8: evaluating a compatible section of `homComplexDegreeTower M I (-1)`
on the `(p,q)`-component is natural in the tower index. -/
private theorem homComplexDegreeTowerSectionComponentNaturality
    (M : CochainComplex 𝒜 ℤ) (I : SequentialInverseSystem (CochainComplex 𝒜 ℤ))
    {p q : ℤ} (hpq : p + -1 = q)
    (s : (homComplexDegreeTower M I (-1) ⋙ forget AddCommGrpCat).sections)
    {i j : ℕᵒᵖ} (g : i ⟶ j) :
    Cochain.v (s.val j) p q hpq =
      Cochain.v (s.val i) p q hpq ≫ (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) q).map g := by
  have hs : ((homComplexDegreeTower M I (-1)).map g) (s.val i) = s.val j := by
    exact s.property g
  calc
    Cochain.v (s.val j) p q hpq
        = ((homComplexCochainPostcomp
            (K := M) (L := I.obj i) (M := I.obj j) (I.map g) (-1))
            (s.val i)).v p q hpq := by
              simpa [homComplexDegreeTower] using (Cochain.congr_v hs p q hpq).symm
    _ = Cochain.v (s.val i) p q hpq ≫ (I.map g).f q := by
          simpa using
            (homComplexCochainPostcomp_v
              (K := M) (L := I.obj i) (M := I.obj j) (σ := I.map g)
              (n := -1) (p := p) (q := q) hpq (s.val i))
    _ = Cochain.v (s.val i) p q hpq ≫ (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) q).map g := by
          rfl

/-- Helper for Lemma 13.31.8: degreewise split epimorphy of `σ` gives split epimorphy of
postcomposition on Hom-complex cochains. -/
private theorem homComplexCochainPostcomp_isSplitEpi
    {K L M : CochainComplex 𝒜 ℤ} (σ : L ⟶ M) (hσ : ∀ q : ℤ, IsSplitEpi (σ.f q)) (n : ℤ) :
    IsSplitEpi (AddCommGrpCat.ofHom (homComplexCochainPostcomp (K := K) (L := L) (M := M) σ n)) := by
  -- Route correction: the cochain-level split only needs the termwise sections of `σ`, not a
  -- section of `σ` as a morphism of complexes.
  -- Proof comment: compose each degree-`q` component with the chosen section of `σ.f q`.
  refine IsSplitEpi.mk'
    { section_ :=
        AddCommGrpCat.ofHom
          { toFun := fun z ↦
              Cochain.mk
                (fun p q hpq ↦ z.v p q hpq ≫ @section_ _ _ _ _ (σ.f q) (hσ q))
            map_zero' := by
              ext p q hpq
              simp
            map_add' := by
              intro z₁ z₂
              ext p q hpq
              simp [Preadditive.add_comp] }
      id := ?_ }
  ext z p q hpq
  simp [homComplexCochainPostcomp]

/-- Helper for Lemma 13.31.8: any cocycle in `HomComplex M J` is a coboundary when `M` is acyclic
and `J` is K-injective. -/
private theorem homComplexCocycle_mem_coboundaries_of_isKInjective
    {M J : CochainComplex 𝒜 ℤ} (hM : M.Acyclic) [J.IsKInjective] {n : ℤ}
    (z : Cocycle M J n) :
    z ∈ coboundaries M J n := by
  let φ : M ⟶ J⟦n⟧ := Cocycle.equivHomShift.symm z
  have hzero :
      CohomologyClass.toHom (K := M) (L := J) (n := n) (CohomologyClass.mk z) = 0 := by
    -- Proof comment: K-injectivity of `J⟦n⟧` makes the represented morphism null-homotopic.
    rw [CohomologyClass.toHom_mk, HomotopyCategory.quotient_map_eq_zero_iff]
    exact IsKInjective.nonempty_homotopy_zero φ hM
  exact (CohomologyClass.toHom_mk_eq_zero_iff z).1 hzero

/-- Helper for Lemma 13.31.8: the explicit Hom-complex row in degrees `n,n + 1,n + 2` is exact
when `M` is acyclic and `J` is K-injective. -/
private theorem homComplexExplicitShortComplexExact
    {M J : CochainComplex 𝒜 ℤ} (n : ℤ) (hM : M.Acyclic) [J.IsKInjective] :
    ((HomComplex M J).sc' n (n + 1) (n + 2)).Exact := by
  -- Proof comment: exactness says that every degree-`n + 1` cocycle is a coboundary from degree
  -- `n`.
  let T : ShortComplex AddCommGrpCat :=
    ShortComplex.mk
      ((HomComplex M J).d n (n + 1))
      ((HomComplex M J).d (n + 1) (n + 2))
      (by
        ext z
        simpa using (CochainComplex.HomComplex.δ_δ n (n + 1) (n + 2) z))
  have hT : T.Exact := by
    rw [ShortComplex.ab_exact_iff_function_exact]
    intro z
    constructor
    · intro hz
      let zz : Cocycle M J (n + 1) := Cocycle.mk z (n + 2) (by omega) hz
      rcases (mem_coboundaries_iff zz n rfl).1
          (homComplexCocycle_mem_coboundaries_of_isKInjective hM zz) with ⟨w, hw⟩
      exact ⟨w, hw⟩
    · rintro ⟨w, rfl⟩
      simpa using (CochainComplex.HomComplex.δ_δ n (n + 1) (n + 2) w)
  simpa [T, HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
    using hT

/-- Helper for Lemma 13.31.8: the short complex `sc n` of `HomComplex M J` is exact when `M` is
acyclic and `J` is K-injective. -/
private theorem homComplexStageShortComplexExact
    {M J : CochainComplex 𝒜 ℤ} (n : ℤ) (hM : M.Acyclic) [J.IsKInjective] :
    ((HomComplex M J).sc n).Exact := by
  -- Proof comment: exactness of `sc n` is the same as exactness of the corresponding explicit
  -- short complex via the canonical `isoSc'`.
  let e :
      (HomComplex M J).sc n ≅ (HomComplex M J).sc' (n - 1) n (n + 1) :=
    (HomComplex M J).isoSc' (i := n - 1) (k := n + 1)
      (hi := CochainComplex.prev ℤ n) (hk := CochainComplex.next ℤ n)
  have hsc :
      ((HomComplex M J).sc' (n - 1) n (n + 1)).Exact := by
    have hnext : n - 1 + 2 = n + 1 := by omega
    simpa [hnext] using homComplexExplicitShortComplexExact (M := M) (J := J) (n := n - 1) hM
  exact ShortComplex.exact_of_iso e.symm
    hsc

/-- Helper for Lemma 13.31.8: consecutive Hom-complex differential towers form a complex. -/
private theorem homComplexTowerShortComplexZero
    (M : CochainComplex 𝒜 ℤ) (I : SequentialInverseSystem (CochainComplex 𝒜 ℤ)) (n : ℤ) :
    homComplexDegreeTowerDelta M I n ≫ homComplexDegreeTowerDelta M I (n + 1) = 0 := by
  -- Proof comment: evaluate the composite at each stage and use `δ² = 0` in the Hom complex.
  ext k z
  simpa [NatTrans.comp_app, homComplexDegreeTowerDelta, add_assoc] using
    (CochainComplex.HomComplex.δ_δ n (n + 1) (n + 1 + 1) z)

/-- Helper for Lemma 13.31.8: exactness in a functor category is checked objectwise by
evaluation. -/
private theorem functorShortComplex_exact_iff_exact_app
    {J : Type*} [Category J] {C : Type*} [Category C] [Abelian C]
    (S : ShortComplex (J ⥤ C)) :
    S.Exact ↔ ∀ j : J, (S.map ((evaluation J C).obj j)).Exact := by
  let hEval :
      JointlyReflectIsomorphisms
        ((evaluation J C).obj : J → (J ⥤ C) ⥤ C) := by
    refine ⟨fun {X Y} f hf ↦ ?_⟩
    rw [NatTrans.isIso_iff_isIso_app]
    intro j
    simpa using (inferInstance : IsIso (((evaluation J C).obj j).map f))
  constructor
  · intro hS j
    simpa using (hEval.exact_iff S).1 hS j
  · intro hS
    exact (hEval.exact_iff S).2 hS

/-- Helper for Lemma 13.31.8: the degree `n` and `n + 1` Hom-complex differential towers form a
short complex in inverse systems. -/
private def homComplexTowerShortComplex
    (M : CochainComplex 𝒜 ℤ) (I : SequentialInverseSystem (CochainComplex 𝒜 ℤ)) (n : ℤ) :
    ShortComplex (ℕᵒᵖ ⥤ AddCommGrpCat) :=
  ShortComplex.mk
    (homComplexDegreeTowerDelta M I n)
    (homComplexDegreeTowerDelta M I (n + 1))
    (by simpa using homComplexTowerShortComplexZero M I n)

/-- Helper for Lemma 13.31.8: evaluating the Hom-complex tower row at stage `k` recovers the
explicit Hom-complex row on `I_k`. -/
private def homComplexTowerShortComplexAppIso
    (M : CochainComplex 𝒜 ℤ) (I : SequentialInverseSystem (CochainComplex 𝒜 ℤ))
    (n : ℤ) (k : ℕᵒᵖ) :
    (homComplexTowerShortComplex M I n).map
      ((evaluation ℕᵒᵖ AddCommGrpCat).obj k) ≅
        (HomComplex M (I.obj k)).sc (n + 1) :=
  -- Proof comment: after evaluation at `k`, the tower row already has the same terms and
  -- differentials as the explicit Hom-complex row on `I.obj (op k)`.
  (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)) ≪≫
    ((HomComplex M (I.obj k)).isoSc' (i := n) (j := n + 1) (k := n + 1 + 1)
      (by
        calc
          (up ℤ).prev (n + 1) = n + 1 - 1 := CochainComplex.prev ℤ (n + 1)
          _ = n := by omega)
      (CochainComplex.next ℤ (n + 1))).symm

/-- Helper for Lemma 13.31.8: the degree `n` and `n + 1` Hom-complex differential towers form an
exact short complex. -/
private theorem homComplexTowerShortComplexExact
    (M : CochainComplex 𝒜 ℤ) (I : SequentialInverseSystem (CochainComplex 𝒜 ℤ))
    [∀ k : ℕ, (I.obj (op k)).IsKInjective]
    (n : ℤ) (hM : M.Acyclic) :
    (homComplexTowerShortComplex M I n).Exact := by
  -- Proof comment: exactness in the inverse-system category is checked stagewise, where the row
  -- becomes the explicit Hom-complex row on the stage `I_k`.
  rw [functorShortComplex_exact_iff_exact_app]
  intro k
  simpa using
    (ShortComplex.exact_iff_of_iso
      (homComplexTowerShortComplexAppIso (M := M) (I := I) n k)).mpr
      (homComplexStageShortComplexExact (M := M) (J := I.obj k) (n := n + 1) hM)

/-- Helper for Lemma 13.31.8: transition maps in a sequential inverse system compose as expected. -/
private theorem transitionMap_comp
    {A : Type*} [Category A] (F : SequentialInverseSystem A)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    F.transitionMap (Nat.le_trans hij hjk) = F.transitionMap hjk ≫ F.transitionMap hij := by
  -- Proof comment: this is the functoriality of `F` on the composite in `ℕᵒᵖ`.
  have hh :
      (homOfLE (Nat.le_trans hij hjk)).op = (homOfLE hjk).op ≫ (homOfLE hij).op := by
    subsingleton
  simpa [SequentialInverseSystem.transitionMap, Functor.map_comp] using congrArg F.map hh

/-- Helper for Lemma 13.31.8: in `AddCommGrpCat`, composing on the left with an epimorphism does
not change the image subobject. -/
private theorem imageSubobject_comp_eq_of_epi_left
    {X Y Z : AddCommGrpCat} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi f] :
    imageSubobject (f ≫ g) = imageSubobject g := by
  -- Proof comment: the comparison map between the two image subobjects is both mono and epi.
  let h := imageSubobject_comp_le f g
  let φ := Subobject.ofLE _ _ h
  haveI : Epi φ := by
    dsimp [φ, h]
    infer_instance
  haveI : IsIso φ := isIso_of_mono_of_epi φ
  exact Subobject.eq_of_comm (asIso φ) (by simp [φ])

/-- Helper for Lemma 13.31.8: the degree `n` Hom-complex tower is Mittag-Leffler once each
successor transition map is termwise split epic. -/
private theorem homComplexDegreeTower_transitionMap_epi
    (M : CochainComplex 𝒜 ℤ) (I : SequentialInverseSystem (CochainComplex 𝒜 ℤ))
    (n : ℤ)
    (hTermwiseSplitEpi : ∀ m : ℕ, ∀ q : ℤ, IsSplitEpi ((I.transitionMap (Nat.le_succ m)).f q))
    {i k : ℕ} (hik : i ≤ k) :
    Epi (SequentialInverseSystem.transitionMap (homComplexDegreeTower M I n) hik) := by
  rcases Nat.exists_eq_add_of_le hik with ⟨r, rfl⟩
  induction r with
  | zero =>
      simpa [SequentialInverseSystem.transitionMap] using
        (inferInstance : Epi (𝟙 ((homComplexDegreeTower M I n).obj (op i))))
  | succ r ihr =>
      have hstep :
          IsSplitEpi
            (SequentialInverseSystem.transitionMap (homComplexDegreeTower M I n)
              (show i + r ≤ i + r + 1 by omega)) := by
        -- Proof comment: each successor map in the degree tower is postcomposition by the
        -- corresponding successor map in `I`, hence split epic by the cochain-level section.
        simpa [homComplexDegreeTower, SequentialInverseSystem.transitionMap] using
          homComplexCochainPostcomp_isSplitEpi
            (K := M)
            (L := I.obj (op (i + r + 1)))
            (M := I.obj (op (i + r)))
            (σ := I.transitionMap (Nat.le_succ (i + r)))
            (hσ := hTermwiseSplitEpi (i + r))
            (n := n)
      have hcomp :
          SequentialInverseSystem.transitionMap (homComplexDegreeTower M I n)
              (show i ≤ i + r + 1 by omega) =
            SequentialInverseSystem.transitionMap (homComplexDegreeTower M I n)
                (show i + r ≤ i + r + 1 by omega) ≫
              SequentialInverseSystem.transitionMap (homComplexDegreeTower M I n)
                (show i ≤ i + r by omega) := by
        simpa [Nat.add_assoc] using
          transitionMap_comp
            (F := homComplexDegreeTower M I n)
            (hij := show i ≤ i + r by omega)
            (hjk := show i + r ≤ i + r + 1 by omega)
      letI :
          Epi
            (SequentialInverseSystem.transitionMap (homComplexDegreeTower M I n)
              (show i + r ≤ i + r + 1 by omega)) :=
        by
          letI := hstep
          infer_instance
      letI :
          Epi
            (SequentialInverseSystem.transitionMap (homComplexDegreeTower M I n)
              (show i ≤ i + r by omega)) :=
        ihr (show i ≤ i + r by omega)
      rw [hcomp]
      infer_instance

/-- Helper for Lemma 13.31.8: the degree `n` Hom-complex tower is Mittag-Leffler once each
successor transition map is termwise split epic. -/
private theorem homComplexDegreeTower_isMittagLeffler
    (M : CochainComplex 𝒜 ℤ) (I : SequentialInverseSystem (CochainComplex 𝒜 ℤ))
    (n : ℤ)
    (hTermwiseSplitEpi : ∀ m : ℕ, ∀ q : ℤ, IsSplitEpi ((I.transitionMap (Nat.le_succ m)).f q)) :
    SequentialInverseSystem.IsMittagLeffler (homComplexDegreeTower M I n) := by
  intro i
  refine ⟨i, le_rfl, ?_⟩
  intro k hik
  haveI :
      Epi (SequentialInverseSystem.transitionMap (homComplexDegreeTower M I n) hik) :=
    homComplexDegreeTower_transitionMap_epi
      (M := M) (I := I) (n := n) hTermwiseSplitEpi hik
  have hleft :
      imageSubobject (SequentialInverseSystem.transitionMap (homComplexDegreeTower M I n) hik) = ⊤ := by
    simpa using
      (Limits.imageSubobject_eq_top_of_epi
        (SequentialInverseSystem.transitionMap (homComplexDegreeTower M I n) hik))
  haveI :
      Epi (SequentialInverseSystem.transitionMap (homComplexDegreeTower M I n) (show i ≤ i by rfl)) :=
    homComplexDegreeTower_transitionMap_epi
      (M := M) (I := I) (n := n) hTermwiseSplitEpi (show i ≤ i by rfl)
  have hright :
      imageSubobject
          (SequentialInverseSystem.transitionMap (homComplexDegreeTower M I n)
            (show i ≤ i by rfl)) = ⊤ := by
    simpa using
      (Limits.imageSubobject_eq_top_of_epi
        (SequentialInverseSystem.transitionMap (homComplexDegreeTower M I n)
          (show i ≤ i by rfl)))
  rw [hleft, hright]

/-- Helper for Lemma 13.31.8: evaluating a short exact sequence of sequential inverse systems at a
stage gives a short exact sequence of abelian groups. -/
private theorem shortExactEval {S : ShortComplex AbSeq} {n : ℕ} (hS : S.ShortExact) :
    (S.map ((evaluation ℕᵒᵖ AddCommGrpCat).obj (op n))).ShortExact := by
  let ev := (evaluation ℕᵒᵖ AddCommGrpCat).obj (op n)
  have hExactMono : (S.map ev).Exact ∧ Mono (S.map ev).f := by
    -- Proof comment: evaluation preserves kernels, so left exactness descends to the stagewise
    -- row.
    simpa using
      (S.map ev).exact_and_mono_f_iff_f_is_kernel.2
        ⟨KernelFork.mapIsLimit _ hS.fIsKernel ev⟩
  refine ShortComplex.ShortExact.mk' hExactMono.1 hExactMono.2 ?_
  -- Proof comment: epimorphy of the right map is checked pointwise.
  exact (NatTrans.epi_iff_epi_app S.g).1 hS.epi_g (op n)

/-- Helper for Lemma 13.31.8: inclusion of image subobjects implies inclusion of the underlying
set-theoretic ranges. -/
private theorem rangeSubsetOfImageSubobjectLe
    {X₁ X₂ Y : AddCommGrpCat.{v}} {f : X₁ ⟶ Y} {g : X₂ ⟶ Y}
    (h : imageSubobject f ≤ imageSubobject g) : Set.range f.hom ⊆ Set.range g.hom := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  let z : (imageSubobject g : AddCommGrpCat) :=
    (Subobject.ofLE (imageSubobject f) (imageSubobject g) h)
      (factorThruImageSubobject f x)
  have hz : factorThruImageSubobject g ≫ (imageSubobject g).arrow = g := by
    rw [imageSubobject_arrow_comp]
  obtain ⟨x₂, hx₂⟩ :=
    (AddCommGrpCat.epi_iff_surjective (factorThruImageSubobject g)).1 (inferInstance : Epi (factorThruImageSubobject g)) z
  refine ⟨x₂, ?_⟩
  have hz' : g x₂ = (imageSubobject g).arrow z := by
    simpa [hz] using congrArg (fun t ↦ (imageSubobject g).arrow t) hx₂
  have hfx : f x = (imageSubobject g).arrow z := by
    calc
      f x = (imageSubobject f).arrow (factorThruImageSubobject f x) := by
        simpa using congrArg (fun t ↦ t x) (imageSubobject_arrow_comp (f := f))
      _ = (imageSubobject g).arrow z := by
        rw [← Subobject.ofLE_arrow (X := imageSubobject f) (Y := imageSubobject g) h]
        rfl
  exact (hfx.trans hz'.symm).symm

/-- Helper for Lemma 13.31.8: reindexing a short exact row along the `OrderDual ℕ`/`ℕᵒᵖ`
comparison preserves short exactness. -/
private theorem orderDualShortExactOfShortExact {S : ShortComplex AbSeq}
    (hS : S.ShortExact) :
    let e := CategoryTheory.orderDualEquivalence ℕ
    let W := (Functor.whiskeringLeft (OrderDual ℕ) ℕᵒᵖ AddCommGrpCat).obj e.functor
    (S.map W).ShortExact := by
  let e := CategoryTheory.orderDualEquivalence ℕ
  let W := (Functor.whiskeringLeft (OrderDual ℕ) ℕᵒᵖ AddCommGrpCat).obj e.functor
  -- Proof comment: reindexing only precomposes the row, so exactness and mono/epi are preserved
  -- objectwise.
  simpa [W] using hS.map_of_exact W

/-- Helper for Lemma 13.31.8: the source-facing sequential Mittag-Leffler condition gives the
owner `Type`-valued condition after reindexing from `ℕᵒᵖ` to `OrderDual ℕ`. -/
private theorem orderDualOwnerIsMittagLefflerOfSourceIsMittagLeffler
    (F : AbSeq) (hF : SequentialInverseSystem.IsMittagLeffler F) :
    Functor.IsMittagLeffler (((CategoryTheory.orderDualEquivalence ℕ).functor ⋙ F) ⋙ forget AddCommGrpCat) := by
  let e := CategoryTheory.orderDualEquivalence ℕ
  refine (Functor.isMittagLeffler_iff_subset_range_comp (((e.functor ⋙ F) ⋙ forget AddCommGrpCat))).2 ?_
  intro i
  obtain ⟨c, hic, hstable⟩ := hF (ofDual i)
  refine ⟨toDual c, ?_, ?_⟩
  · simpa using (homOfLE hic : toDual c ⟶ toDual (ofDual i))
  · intro k g
    have hcg : c ≤ ofDual k := leOfHom g
    have hg : g = (homOfLE hcg : k ⟶ toDual c) := Subsingleton.elim _ _
    let f' : F.obj (op c) ⟶ F.obj (op (ofDual i)) := F.transitionMap hic
    let g' : F.obj (op (ofDual k)) ⟶ F.obj (op (ofDual i)) := F.transitionMap (hic.trans hcg)
    have himage : imageSubobject f' ≤ imageSubobject g' := by
      simpa [f', g'] using (hstable hcg).symm.le
    have hsubset : Set.range f'.hom ⊆ Set.range g'.hom := by
      exact
        @rangeSubsetOfImageSubobjectLe
          (F.obj (op c)) (F.obj (op (ofDual k))) (F.obj (op (ofDual i))) f' g' himage
    -- Proof comment: replace stabilized image equality by inclusion of the underlying set-theoretic
    -- ranges.
    simpa [e, hg, SequentialInverseSystem.transitionMap] using hsubset

/-- Helper for Lemma 13.31.8: the first square in the reindexed inverse-limit comparison
commutes. -/
private theorem orderDualLimitMapShortComplexIsoComm₁₂ (S : ShortComplex AbSeq) :
    let e := CategoryTheory.orderDualEquivalence ℕ
    let i₁ : limit (e.functor ⋙ S.X₁) ≅ limit S.X₁ :=
      HasLimit.isoOfEquivalence e (Iso.refl _)
    let i₂ : limit (e.functor ⋙ S.X₂) ≅ limit S.X₂ :=
      HasLimit.isoOfEquivalence e (Iso.refl _)
    i₁.hom ≫ limMap S.f = limMap (e.functor.whiskerLeft S.f) ≫ i₂.hom := by
  let e := CategoryTheory.orderDualEquivalence ℕ
  let i₁ : limit (e.functor ⋙ S.X₁) ≅ limit S.X₁ :=
    HasLimit.isoOfEquivalence e (Iso.refl _)
  let i₂ : limit (e.functor ⋙ S.X₂) ≅ limit S.X₂ :=
    HasLimit.isoOfEquivalence e (Iso.refl _)
  apply limit.hom_ext
  intro k
  simp_rw [Category.assoc]
  have hleft :
      i₁.hom ≫ limit.π S.X₁ k ≫ S.f.app k =
        limit.π (e.functor ⋙ S.X₁) (e.inverse.obj k) ≫
          (Iso.refl (e.functor ⋙ S.X₁)).inv.app (e.inverse.obj k) ≫
            S.X₁.map (e.counit.app k) ≫ S.f.app k := by
    simpa only [Category.assoc] using
      congrArg (fun φ ↦ φ ≫ S.f.app k)
        (HasLimit.isoOfEquivalence_hom_π e (Iso.refl (e.functor ⋙ S.X₁)) k)
  have hright :
      limMap (e.functor.whiskerLeft S.f) ≫
          limit.π (e.functor ⋙ S.X₂) (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₂)).inv.app (e.inverse.obj k) ≫
              S.X₂.map (e.counit.app k) =
        limit.π (e.functor ⋙ S.X₁) (e.inverse.obj k) ≫
          (e.functor.whiskerLeft S.f).app (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₂)).inv.app (e.inverse.obj k) ≫
              S.X₂.map (e.counit.app k) := by
    simpa only [Category.assoc] using
      congrArg
        (fun φ ↦
          φ ≫ (Iso.refl (e.functor ⋙ S.X₂)).inv.app (e.inverse.obj k) ≫
            S.X₂.map (e.counit.app k))
        (Limits.limMap_π (e.functor.whiskerLeft S.f) (e.inverse.obj k))
  have hmiddle :
      limit.π (e.functor ⋙ S.X₁) (e.inverse.obj k) ≫
          (Iso.refl (e.functor ⋙ S.X₁)).inv.app (e.inverse.obj k) ≫
            S.X₁.map (e.counit.app k) ≫ S.f.app k =
        limit.π (e.functor ⋙ S.X₁) (e.inverse.obj k) ≫
          (e.functor.whiskerLeft S.f).app (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₂)).inv.app (e.inverse.obj k) ≫
              S.X₂.map (e.counit.app k) := by
    simpa [CategoryTheory.orderDualEquivalence, Category.assoc] using
      congrArg
        (fun φ ↦
          limit.π (e.functor ⋙ S.X₁) (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₂)).inv.app (e.inverse.obj k) ≫ φ)
        (S.f.naturality (e.counit.app k))
  have hfinal :
      i₁.hom ≫ limit.π S.X₁ k ≫ S.f.app k =
        limMap (e.functor.whiskerLeft S.f) ≫
          limit.π (e.functor ⋙ S.X₂) (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₂)).inv.app (e.inverse.obj k) ≫
              S.X₂.map (e.counit.app k) := by
    exact hleft.trans (hmiddle.trans hright.symm)
  simpa [e, CategoryTheory.orderDualEquivalence, Category.assoc] using hfinal

/-- Helper for Lemma 13.31.8: the second square in the reindexed inverse-limit comparison
commutes. -/
private theorem orderDualLimitMapShortComplexIsoComm₂₃ (S : ShortComplex AbSeq) :
    let e := CategoryTheory.orderDualEquivalence ℕ
    let i₂ : limit (e.functor ⋙ S.X₂) ≅ limit S.X₂ :=
      HasLimit.isoOfEquivalence e (Iso.refl _)
    let i₃ : limit (e.functor ⋙ S.X₃) ≅ limit S.X₃ :=
      HasLimit.isoOfEquivalence e (Iso.refl _)
    i₂.hom ≫ limMap S.g = limMap (e.functor.whiskerLeft S.g) ≫ i₃.hom := by
  let e := CategoryTheory.orderDualEquivalence ℕ
  let i₂ : limit (e.functor ⋙ S.X₂) ≅ limit S.X₂ :=
    HasLimit.isoOfEquivalence e (Iso.refl _)
  let i₃ : limit (e.functor ⋙ S.X₃) ≅ limit S.X₃ :=
    HasLimit.isoOfEquivalence e (Iso.refl _)
  apply limit.hom_ext
  intro k
  simp_rw [Category.assoc]
  have hleft :
      i₂.hom ≫ limit.π S.X₂ k ≫ S.g.app k =
        limit.π (e.functor ⋙ S.X₂) (e.inverse.obj k) ≫
          (Iso.refl (e.functor ⋙ S.X₂)).inv.app (e.inverse.obj k) ≫
            S.X₂.map (e.counit.app k) ≫ S.g.app k := by
    simpa only [Category.assoc] using
      congrArg (fun φ ↦ φ ≫ S.g.app k)
        (HasLimit.isoOfEquivalence_hom_π e (Iso.refl (e.functor ⋙ S.X₂)) k)
  have hright :
      limMap (e.functor.whiskerLeft S.g) ≫
          limit.π (e.functor ⋙ S.X₃) (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₃)).inv.app (e.inverse.obj k) ≫
              S.X₃.map (e.counit.app k) =
        limit.π (e.functor ⋙ S.X₂) (e.inverse.obj k) ≫
          (e.functor.whiskerLeft S.g).app (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₃)).inv.app (e.inverse.obj k) ≫
              S.X₃.map (e.counit.app k) := by
    simpa only [Category.assoc] using
      congrArg
        (fun φ ↦
          φ ≫ (Iso.refl (e.functor ⋙ S.X₃)).inv.app (e.inverse.obj k) ≫
            S.X₃.map (e.counit.app k))
        (Limits.limMap_π (e.functor.whiskerLeft S.g) (e.inverse.obj k))
  have hmiddle :
      limit.π (e.functor ⋙ S.X₂) (e.inverse.obj k) ≫
          (Iso.refl (e.functor ⋙ S.X₂)).inv.app (e.inverse.obj k) ≫
            S.X₂.map (e.counit.app k) ≫ S.g.app k =
        limit.π (e.functor ⋙ S.X₂) (e.inverse.obj k) ≫
          (e.functor.whiskerLeft S.g).app (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₃)).inv.app (e.inverse.obj k) ≫
              S.X₃.map (e.counit.app k) := by
    simpa [CategoryTheory.orderDualEquivalence, Category.assoc] using
      congrArg
        (fun φ ↦
          limit.π (e.functor ⋙ S.X₂) (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₃)).inv.app (e.inverse.obj k) ≫ φ)
        (S.g.naturality (e.counit.app k))
  have hfinal :
      i₂.hom ≫ limit.π S.X₂ k ≫ S.g.app k =
        limMap (e.functor.whiskerLeft S.g) ≫
          limit.π (e.functor ⋙ S.X₃) (e.inverse.obj k) ≫
            (Iso.refl (e.functor ⋙ S.X₃)).inv.app (e.inverse.obj k) ≫
              S.X₃.map (e.counit.app k) := by
    exact hleft.trans (hmiddle.trans hright.symm)
  simpa [e, CategoryTheory.orderDualEquivalence, Category.assoc] using hfinal

/-- Helper for Lemma 13.31.8: after applying `lim`, the reindexed short complex is canonically
isomorphic to the original one. -/
private noncomputable def orderDualLimitMapShortComplexIso (S : ShortComplex AbSeq) :
    let e := CategoryTheory.orderDualEquivalence ℕ
    let W := (Functor.whiskeringLeft (OrderDual ℕ) ℕᵒᵖ AddCommGrpCat).obj e.functor
    ((S.map W).map (lim : (OrderDual ℕ ⥤ AddCommGrpCat) ⥤ AddCommGrpCat)) ≅
      S.map (lim : (ℕᵒᵖ ⥤ AddCommGrpCat) ⥤ AddCommGrpCat) :=
  let e := CategoryTheory.orderDualEquivalence ℕ
  let i₁ : limit (e.functor ⋙ S.X₁) ≅ limit S.X₁ :=
    HasLimit.isoOfEquivalence e (Iso.refl _)
  let i₂ : limit (e.functor ⋙ S.X₂) ≅ limit S.X₂ :=
    HasLimit.isoOfEquivalence e (Iso.refl _)
  let i₃ : limit (e.functor ⋙ S.X₃) ≅ limit S.X₃ :=
    HasLimit.isoOfEquivalence e (Iso.refl _)
  ShortComplex.isoMk i₁ i₂ i₃
    (orderDualLimitMapShortComplexIsoComm₁₂ S)
    (orderDualLimitMapShortComplexIsoComm₂₃ S)

/-- Helper for Lemma 13.31.8: in a short exact sequence of sequential inverse systems of abelian
groups, Mittag-Leffler on the middle term implies Mittag-Leffler on the quotient term. -/
private theorem isMittagLefflerRightOfShortExact {S : ShortComplex AbSeq}
    (hS : S.ShortExact)
    (hML : SequentialInverseSystem.IsMittagLeffler S.X₂) :
    SequentialInverseSystem.IsMittagLeffler S.X₃ := by
  intro i
  obtain ⟨c, hic, hstable⟩ := hML i
  refine ⟨c, hic, ?_⟩
  intro k hck
  have hnat_k :
      S.X₂.transitionMap (hic.trans hck) ≫ S.g.app (op i) =
        S.g.app (op k) ≫ S.X₃.transitionMap (hic.trans hck) := by
    simpa [transitionMap] using S.g.naturality ((homOfLE (hic.trans hck)).op)
  have hnat_c :
      S.X₂.transitionMap hic ≫ S.g.app (op i) =
        S.g.app (op c) ≫ S.X₃.transitionMap hic := by
    simpa [transitionMap] using S.g.naturality ((homOfLE hic).op)
  letI : Epi (S.g.app (op k)) := (shortExactEval hS).epi_g
  letI : Epi (S.g.app (op c)) := (shortExactEval hS).epi_g
  -- Proof comment: transport stabilized images in the middle row across the stagewise quotient
  -- maps.
  calc
    imageSubobject (S.X₃.transitionMap (hic.trans hck))
        = imageSubobject (S.g.app (op k) ≫ S.X₃.transitionMap (hic.trans hck)) := by
            symm
            simpa using
              imageSubobject_comp_eq_of_epi_left
                (S.g.app (op k)) (S.X₃.transitionMap (hic.trans hck))
    _ = imageSubobject (S.X₂.transitionMap (hic.trans hck) ≫ S.g.app (op i)) := by
          rw [← hnat_k]
    _ = imageSubobject
          ((imageSubobject (S.X₂.transitionMap (hic.trans hck))).arrow ≫ S.g.app (op i)) := by
          rw [Limits.imageSubobject_comp_eq_imageSubobject_restriction]
    _ = imageSubobject ((imageSubobject (S.X₂.transitionMap hic)).arrow ≫ S.g.app (op i)) := by
          rw [hstable hck]
    _ = imageSubobject (S.X₂.transitionMap hic ≫ S.g.app (op i)) := by
          rw [← Limits.imageSubobject_comp_eq_imageSubobject_restriction]
    _ = imageSubobject (S.g.app (op c) ≫ S.X₃.transitionMap hic) := by
          rw [hnat_c]
    _ = imageSubobject (S.X₃.transitionMap hic) := by
          simpa using
            imageSubobject_comp_eq_of_epi_left
              (S.g.app (op c)) (S.X₃.transitionMap hic)

/-- Helper for Lemma 13.31.8: if the left term of a short exact sequence of sequential inverse
systems of abelian groups is Mittag-Leffler, then the induced sequence on inverse limits is short
exact. -/
private theorem inverseLimitShortExactOfIsMittagLefflerLeft {S : ShortComplex AbSeq}
    (hS : S.ShortExact)
    (hML : SequentialInverseSystem.IsMittagLeffler S.X₁) :
    (S.map lim).ShortExact := by
  let e := CategoryTheory.orderDualEquivalence ℕ
  let W := (Functor.whiskeringLeft (OrderDual ℕ) ℕᵒᵖ AddCommGrpCat).obj e.functor
  have hReindexed :
      ((S.map W).map (lim : (OrderDual ℕ ⥤ AddCommGrpCat) ⥤ AddCommGrpCat)).ShortExact := by
    simpa using
      inverseSystem_limit_shortExact_of_countable_and_isMittagLeffler_left
        (S := S.map W)
        (orderDualShortExactOfShortExact hS)
        (orderDualOwnerIsMittagLefflerOfSourceIsMittagLeffler (F := S.X₁) hML)
  -- Proof comment: transport the short exactness statement back across the limit comparison
  -- isomorphism.
  exact ShortComplex.shortExact_of_iso
    (orderDualLimitMapShortComplexIso S)
    hReindexed

/-- Helper for Lemma 13.31.8: a four-term exact sequence of sequential inverse systems of abelian
groups remains exact on the tail after taking inverse limits if the leftmost tower is
Mittag-Leffler. -/
private theorem composableArrowsFirstImageIsMittagLeffler
    (S : ComposableArrows (SequentialInverseSystem AddCommGrpCat.{v}) 3)
    (hS : S.Exact)
    (hML : SequentialInverseSystem.IsMittagLeffler S.left) :
    SequentialInverseSystem.IsMittagLeffler (imageSubobject (S.sc hS.toIsComplex 0).f : AbSeq) := by
  let S₀ : ShortComplex AbSeq := S.sc hS.toIsComplex 0
  let T : ShortComplex AbSeq :=
    ShortComplex.mk (kernel.ι (factorThruImageSubobject S₀.f))
      (factorThruImageSubobject S₀.f) (kernel.condition _)
  have hT : T.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
    exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  simpa [T, S₀] using
    isMittagLefflerRightOfShortExact (S := T) hT hML

/-- Helper for Lemma 13.31.8: the composite
`image(A ⟶ B) ⟶ B ⟶ kernel(C ⟶ D)` vanishes in a four-term exact row. -/
private theorem composableArrowsMiddleToTailKernelCompZero
    (S : ComposableArrows (SequentialInverseSystem AddCommGrpCat.{v}) 3)
    (hS : S.Exact) :
    let S₀ : ShortComplex AbSeq := S.sc hS.toIsComplex 0
    let S₁ : ShortComplex AbSeq := S.sc hS.toIsComplex 1
    (imageSubobject S₀.f).arrow ≫ factorThruKernelSubobject S₁.g S₁.f S₁.zero = 0 := by
  let S₀ : ShortComplex AbSeq := S.sc hS.toIsComplex 0
  let S₁ : ShortComplex AbSeq := S.sc hS.toIsComplex 1
  have hzeroImage : (imageSubobject S₀.f).arrow ≫ S₁.f = 0 := by
    apply (cancel_epi (factorThruImageSubobject S₀.f)).1
    simpa [S₀, S₁] using S₀.zero
  apply (cancel_mono (kernelSubobject S₁.g).arrow).1
  rw [Category.assoc, factorThruKernelSubobject_comp_arrow, zero_comp]
  simpa [S₁] using hzeroImage

/-- Helper for Lemma 13.31.8: the row
`image(A ⟶ B) ⟶ B ⟶ kernel(C ⟶ D)` is short exact for a four-term exact sequence. -/
private theorem composableArrowsMiddleToTailKernelShortExact
    (S : ComposableArrows (SequentialInverseSystem AddCommGrpCat.{v}) 3)
    (hS : S.Exact) :
    let S₀ : ShortComplex AbSeq := S.sc hS.toIsComplex 0
    let S₁ : ShortComplex AbSeq := S.sc hS.toIsComplex 1
    (ShortComplex.mk (imageSubobject S₀.f).arrow
      (factorThruKernelSubobject S₁.g S₁.f S₁.zero)
      (composableArrowsMiddleToTailKernelCompZero S hS)).ShortExact := by
  let S₀ : ShortComplex AbSeq := S.sc hS.toIsComplex 0
  let S₁ : ShortComplex AbSeq := S.sc hS.toIsComplex 1
  have hzeroImage : (imageSubobject S₀.f).arrow ≫ S₁.f = 0 := by
    apply (cancel_epi (factorThruImageSubobject S₀.f)).1
    simpa [S₀, S₁] using S₀.zero
  have hzeroKernel :
      (imageSubobject S₀.f).arrow ≫ factorThruKernelSubobject S₁.g S₁.f S₁.zero = 0 := by
    apply (cancel_mono (kernelSubobject S₁.g).arrow).1
    rw [Category.assoc, factorThruKernelSubobject_comp_arrow, zero_comp]
    simpa using hzeroImage
  let T : ShortComplex AbSeq :=
    ShortComplex.mk (imageSubobject S₀.f).arrow
      (factorThruKernelSubobject S₁.g S₁.f S₁.zero) hzeroKernel
  let U : ShortComplex AbSeq := ShortComplex.mk (imageSubobject S₀.f).arrow S₁.f hzeroImage
  have hU : U.Exact := by
    rw [ShortComplex.exact_iff_image_eq_kernel]
    rw [Limits.imageSubobject_mono]
    simpa [U, S₀, S₁] using
      (ShortComplex.exact_iff_image_eq_kernel (S := S₀)).1 (hS.exact 0)
  let hcomm₁₂ : (𝟙 _) ≫ U.f = T.f ≫ (𝟙 _) := by
    simp [T, U]
  let hcomm₂₃ : (𝟙 _) ≫ U.g = T.g ≫ (kernelSubobject S₁.g).arrow := by
    simp [T, U]
  let φ : T ⟶ U :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := (kernelSubobject S₁.g).arrow
      comm₁₂ := hcomm₁₂
      comm₂₃ := hcomm₂₃ }
  have hTExact : T.Exact := by
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hU
  have hTepi : Epi T.g := by
    have hImageToKernel : Epi (imageToKernel S₁.f S₁.g S₁.zero) := by
      exact (ShortComplex.exact_iff_epi_imageToKernel (S := S₁)).1 (hS.exact 1)
    letI : Epi (factorThruImageSubobject S₁.f ≫ imageToKernel S₁.f S₁.g S₁.zero) := by
      infer_instance
    have hfactor :
        factorThruImageSubobject S₁.f ≫ imageToKernel S₁.f S₁.g S₁.zero =
          factorThruKernelSubobject S₁.g S₁.f S₁.zero := by
      simpa using factorThruImageSubobject_comp_imageToKernel (f := S₁.f) (g := S₁.g) S₁.zero
    simpa [T, hfactor] using
      (inferInstance : Epi
        (factorThruImageSubobject S₁.f ≫ imageToKernel S₁.f S₁.g S₁.zero))
  simpa [T, S₀, S₁] using ShortComplex.ShortExact.mk' hTExact inferInstance hTepi

/-- Helper for Lemma 13.31.8: after passing to inverse limits, the image of the first tail map is
the kernel of the second tail map. -/
private theorem inverseLimitTailKernelImageEqKernel
    (S : ComposableArrows (SequentialInverseSystem AddCommGrpCat.{v}) 3)
    (hS : S.Exact)
    (hML : SequentialInverseSystem.IsMittagLeffler S.left) :
    let S₁ : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v}) := S.sc hS.toIsComplex 1
    imageSubobject (lim.map S₁.f) = kernelSubobject (lim.map S₁.g) := by
  let S₀ : ShortComplex AbSeq := S.sc hS.toIsComplex 0
  let S₁ : ShortComplex AbSeq := S.sc hS.toIsComplex 1
  have hImageML : SequentialInverseSystem.IsMittagLeffler (imageSubobject S₀.f : AbSeq) :=
    composableArrowsFirstImageIsMittagLeffler S hS hML
  let hzeroMiddle :
      (imageSubobject S₀.f).arrow ≫ factorThruKernelSubobject S₁.g S₁.f S₁.zero = 0 := by
    simpa [S₀, S₁] using composableArrowsMiddleToTailKernelCompZero S hS
  let T : ShortComplex AbSeq :=
    ShortComplex.mk (imageSubobject S₀.f).arrow
      (factorThruKernelSubobject S₁.g S₁.f S₁.zero) hzeroMiddle
  have hT : T.ShortExact := by
    simpa [T, S₀, S₁] using composableArrowsMiddleToTailKernelShortExact S hS
  have hTlim : (T.map lim).ShortExact := by
    let e := CategoryTheory.orderDualEquivalence ℕ
    let W := (Functor.whiskeringLeft (OrderDual ℕ) ℕᵒᵖ AddCommGrpCat.{v}).obj e.functor
    have hReindexed :
        ((T.map W).map (lim : (OrderDual ℕ ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v})).ShortExact := by
      simpa using
        inverseSystem_limit_shortExact_of_countable_and_isMittagLeffler_left
          (S := T.map W)
          (orderDualShortExactOfShortExact hT)
          (orderDualOwnerIsMittagLefflerOfSourceIsMittagLeffler (F := T.X₁) hImageML)
    have hIso :
        ((T.map W).map (lim : (OrderDual ℕ ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v})) ≅
          T.map (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v}) := by
      let i₁ : limit (e.functor ⋙ T.X₁) ≅ limit T.X₁ :=
        HasLimit.isoOfEquivalence e (Iso.refl _)
      let i₂ : limit (e.functor ⋙ T.X₂) ≅ limit T.X₂ :=
        HasLimit.isoOfEquivalence e (Iso.refl _)
      let i₃ : limit (e.functor ⋙ T.X₃) ≅ limit T.X₃ :=
        HasLimit.isoOfEquivalence e (Iso.refl _)
      have hcomm₁₂ : i₁.hom ≫ limMap T.f = limMap (e.functor.whiskerLeft T.f) ≫ i₂.hom := by
        apply limit.hom_ext
        intro k
        simp_rw [Category.assoc]
        have hleft :
            i₁.hom ≫ limit.π T.X₁ k ≫ T.f.app k =
              limit.π (e.functor ⋙ T.X₁) (e.inverse.obj k) ≫
                (Iso.refl (e.functor ⋙ T.X₁)).inv.app (e.inverse.obj k) ≫
                  T.X₁.map (e.counit.app k) ≫ T.f.app k := by
          simpa only [Category.assoc] using
            congrArg (fun φ ↦ φ ≫ T.f.app k)
              (HasLimit.isoOfEquivalence_hom_π e (Iso.refl (e.functor ⋙ T.X₁)) k)
        have hright :
            limMap (e.functor.whiskerLeft T.f) ≫
                limit.π (e.functor ⋙ T.X₂) (e.inverse.obj k) ≫
                  (Iso.refl (e.functor ⋙ T.X₂)).inv.app (e.inverse.obj k) ≫
                    T.X₂.map (e.counit.app k) =
              limit.π (e.functor ⋙ T.X₁) (e.inverse.obj k) ≫
                (e.functor.whiskerLeft T.f).app (e.inverse.obj k) ≫
                  (Iso.refl (e.functor ⋙ T.X₂)).inv.app (e.inverse.obj k) ≫
                    T.X₂.map (e.counit.app k) := by
          simpa only [Category.assoc] using
            congrArg
              (fun φ ↦
                φ ≫ (Iso.refl (e.functor ⋙ T.X₂)).inv.app (e.inverse.obj k) ≫
                  T.X₂.map (e.counit.app k))
              (Limits.limMap_π (e.functor.whiskerLeft T.f) (e.inverse.obj k))
        have hmiddle :
            limit.π (e.functor ⋙ T.X₁) (e.inverse.obj k) ≫
                (Iso.refl (e.functor ⋙ T.X₁)).inv.app (e.inverse.obj k) ≫
                  T.X₁.map (e.counit.app k) ≫ T.f.app k =
              limit.π (e.functor ⋙ T.X₁) (e.inverse.obj k) ≫
                (e.functor.whiskerLeft T.f).app (e.inverse.obj k) ≫
                  (Iso.refl (e.functor ⋙ T.X₂)).inv.app (e.inverse.obj k) ≫
                    T.X₂.map (e.counit.app k) := by
          simpa [CategoryTheory.orderDualEquivalence, Category.assoc] using
            congrArg
              (fun φ ↦
                limit.π (e.functor ⋙ T.X₁) (e.inverse.obj k) ≫
                  (Iso.refl (e.functor ⋙ T.X₂)).inv.app (e.inverse.obj k) ≫ φ)
              (T.f.naturality (e.counit.app k))
        have hfinal :
            i₁.hom ≫ limit.π T.X₁ k ≫ T.f.app k =
              limMap (e.functor.whiskerLeft T.f) ≫
                limit.π (e.functor ⋙ T.X₂) (e.inverse.obj k) ≫
                  (Iso.refl (e.functor ⋙ T.X₂)).inv.app (e.inverse.obj k) ≫
                    T.X₂.map (e.counit.app k) := by
          exact hleft.trans (hmiddle.trans hright.symm)
        have hsrc :
            i₁.hom ≫ limMap T.f ≫ limit.π T.X₂ k =
              i₁.hom ≫ limit.π T.X₁ k ≫ T.f.app k := by
          simpa [Category.assoc] using
            congrArg (fun φ ↦ i₁.hom ≫ φ) (Limits.limMap_π (α := T.f) (j := k))
        have hproj₂' :
            i₂.hom ≫ limit.π T.X₂ k =
              limit.π (e.functor ⋙ T.X₂) (e.inverse.obj k) ≫
                T.X₂.map (e.counit.app k) := by
          simpa [i₂] using HasLimit.isoOfEquivalence_hom_π e (Iso.refl (e.functor ⋙ T.X₂)) k
        have hproj₂ :
            limMap (e.functor.whiskerLeft T.f) ≫ i₂.hom ≫ limit.π T.X₂ k =
              limMap (e.functor.whiskerLeft T.f) ≫
                limit.π (e.functor ⋙ T.X₂) (e.inverse.obj k) ≫
                  T.X₂.map (e.counit.app k) := by
          simpa [Category.assoc] using
            congrArg
              (fun φ ↦ limMap (e.functor.whiskerLeft T.f) ≫ φ)
              hproj₂'
        exact hsrc.trans (hfinal.trans hproj₂.symm)
      have hcomm₂₃ : i₂.hom ≫ limMap T.g = limMap (e.functor.whiskerLeft T.g) ≫ i₃.hom := by
        apply limit.hom_ext
        intro k
        simp_rw [Category.assoc]
        have hleft :
            i₂.hom ≫ limit.π T.X₂ k ≫ T.g.app k =
              limit.π (e.functor ⋙ T.X₂) (e.inverse.obj k) ≫
                (Iso.refl (e.functor ⋙ T.X₂)).inv.app (e.inverse.obj k) ≫
                  T.X₂.map (e.counit.app k) ≫ T.g.app k := by
          simpa only [Category.assoc] using
            congrArg (fun φ ↦ φ ≫ T.g.app k)
              (HasLimit.isoOfEquivalence_hom_π e (Iso.refl (e.functor ⋙ T.X₂)) k)
        have hright :
            limMap (e.functor.whiskerLeft T.g) ≫
                limit.π (e.functor ⋙ T.X₃) (e.inverse.obj k) ≫
                  (Iso.refl (e.functor ⋙ T.X₃)).inv.app (e.inverse.obj k) ≫
                    T.X₃.map (e.counit.app k) =
              limit.π (e.functor ⋙ T.X₂) (e.inverse.obj k) ≫
                (e.functor.whiskerLeft T.g).app (e.inverse.obj k) ≫
                  (Iso.refl (e.functor ⋙ T.X₃)).inv.app (e.inverse.obj k) ≫
                    T.X₃.map (e.counit.app k) := by
          simpa only [Category.assoc] using
            congrArg
              (fun φ ↦
                φ ≫ (Iso.refl (e.functor ⋙ T.X₃)).inv.app (e.inverse.obj k) ≫
                  T.X₃.map (e.counit.app k))
              (Limits.limMap_π (e.functor.whiskerLeft T.g) (e.inverse.obj k))
        have hmiddle :
            limit.π (e.functor ⋙ T.X₂) (e.inverse.obj k) ≫
                (Iso.refl (e.functor ⋙ T.X₂)).inv.app (e.inverse.obj k) ≫
                  T.X₂.map (e.counit.app k) ≫ T.g.app k =
              limit.π (e.functor ⋙ T.X₂) (e.inverse.obj k) ≫
                (e.functor.whiskerLeft T.g).app (e.inverse.obj k) ≫
                  (Iso.refl (e.functor ⋙ T.X₃)).inv.app (e.inverse.obj k) ≫
                    T.X₃.map (e.counit.app k) := by
          simpa [CategoryTheory.orderDualEquivalence, Category.assoc] using
            congrArg
              (fun φ ↦
                limit.π (e.functor ⋙ T.X₂) (e.inverse.obj k) ≫
                  (Iso.refl (e.functor ⋙ T.X₃)).inv.app (e.inverse.obj k) ≫ φ)
              (T.g.naturality (e.counit.app k))
        have hfinal :
            i₂.hom ≫ limit.π T.X₂ k ≫ T.g.app k =
              limMap (e.functor.whiskerLeft T.g) ≫
                limit.π (e.functor ⋙ T.X₃) (e.inverse.obj k) ≫
                  (Iso.refl (e.functor ⋙ T.X₃)).inv.app (e.inverse.obj k) ≫
                    T.X₃.map (e.counit.app k) := by
          exact hleft.trans (hmiddle.trans hright.symm)
        have hsrc :
            i₂.hom ≫ limMap T.g ≫ limit.π T.X₃ k =
              i₂.hom ≫ limit.π T.X₂ k ≫ T.g.app k := by
          simpa [Category.assoc] using
            congrArg (fun φ ↦ i₂.hom ≫ φ) (Limits.limMap_π (α := T.g) (j := k))
        have hproj₃' :
            i₃.hom ≫ limit.π T.X₃ k =
              limit.π (e.functor ⋙ T.X₃) (e.inverse.obj k) ≫
                T.X₃.map (e.counit.app k) := by
          simpa [i₃] using HasLimit.isoOfEquivalence_hom_π e (Iso.refl (e.functor ⋙ T.X₃)) k
        have hproj₃ :
            limMap (e.functor.whiskerLeft T.g) ≫ i₃.hom ≫ limit.π T.X₃ k =
              limMap (e.functor.whiskerLeft T.g) ≫
                limit.π (e.functor ⋙ T.X₃) (e.inverse.obj k) ≫
                  T.X₃.map (e.counit.app k) := by
          simpa [Category.assoc] using
            congrArg
              (fun φ ↦ limMap (e.functor.whiskerLeft T.g) ≫ φ)
              hproj₃'
        exact hsrc.trans (hfinal.trans hproj₃.symm)
      exact ShortComplex.isoMk i₁ i₂ i₃
        hcomm₁₂
        hcomm₂₃
    exact ShortComplex.shortExact_of_iso hIso hReindexed
  let hzeroKernel : (kernelSubobject S₁.g).arrow ≫ S₁.g = 0 := kernelSubobject_arrow_comp S₁.g
  let K : ShortComplex AbSeq := ShortComplex.mk (kernelSubobject S₁.g).arrow S₁.g hzeroKernel
  let K' : ShortComplex AbSeq := ShortComplex.mk (kernel.ι S₁.g) S₁.g (kernel.condition _)
  have hK' : K'.Exact := by
    simpa [K'] using (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel S₁.g))
  let hkernelComm₁₂ : (kernelSubobjectIso S₁.g).hom ≫ K'.f = K.f ≫ (𝟙 _) := by
    simp [K, K']
  let hkernelComm₂₃ : (𝟙 _) ≫ K'.g = K.g ≫ (𝟙 _) := by
    simp [K, K']
  let ψ : K ⟶ K' :=
    { τ₁ := (kernelSubobjectIso S₁.g).hom
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := hkernelComm₁₂
      comm₂₃ := hkernelComm₂₃ }
  have hK : K.Exact := by
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).2 hK'
  have hKlim : (K.map lim).Exact := by
    exact
      (show (K.map lim).Exact ∧ Mono (K.map lim).f from by
        simpa using
          (K.map lim).exact_and_mono_f_iff_f_is_kernel.2
            ⟨KernelFork.mapIsLimit _ hK.fIsKernel lim⟩).1
  have htailFac : (T.map lim).g ≫ (K.map lim).f = lim.map S₁.f := by
    calc
      (T.map lim).g ≫ (K.map lim).f
          = lim.map
              (factorThruKernelSubobject S₁.g S₁.f S₁.zero ≫ (kernelSubobject S₁.g).arrow) := by
                simpa [T, K] using
                  (Functor.map_comp lim
                    (factorThruKernelSubobject S₁.g S₁.f S₁.zero)
                    ((kernelSubobject S₁.g).arrow)).symm
      _ = lim.map S₁.f := by
            simp
  letI : Epi (T.map lim).g := hTlim.epi_g
  have hkernelEq : imageSubobject (lim.map S₁.f) = kernelSubobject ((K.map lim).g) := by
    calc
      imageSubobject (lim.map S₁.f)
          = imageSubobject ((T.map lim).g ≫ (K.map lim).f) := by
              rw [htailFac]
              rfl
      _ = imageSubobject ((K.map lim).f) := by
            simpa using imageSubobject_comp_eq_of_epi_left ((T.map lim).g) ((K.map lim).f)
      _ = kernelSubobject ((K.map lim).g) := by
            simpa using (ShortComplex.exact_iff_image_eq_kernel (S := K.map lim)).1 hKlim
  simpa [K, S₁] using hkernelEq

/-- Helper for Lemma 13.31.8: a four-term exact sequence of sequential inverse systems of abelian
groups remains exact on the tail after taking inverse limits if the leftmost tower is
Mittag-Leffler. -/
private theorem inverseLimitExactOfFourTermOfIsMittagLefflerLeft
    (S : ComposableArrows AbSeq 3)
    (hS : S.Exact)
    (hML : SequentialInverseSystem.IsMittagLeffler S.left) :
    (ComposableArrows.δ₀ (S ⋙ lim)).Exact := by
  let S₁ : ShortComplex AbSeq := S.sc hS.toIsComplex 1
  have hImageKernel : imageSubobject (lim.map S₁.f) = kernelSubobject (lim.map S₁.g) := by
    simpa [S₁] using inverseLimitTailKernelImageEqKernel S hS hML
  have hzero :
      (ComposableArrows.δ₀ (S ⋙ lim)).map' 0 1 ≫
        (ComposableArrows.δ₀ (S ⋙ lim)).map' 1 2 = 0 := by
    simpa [S₁] using (S₁.map lim).zero
  have hExact : (S₁.map lim).Exact := by
    rw [ShortComplex.exact_iff_image_eq_kernel]
    simpa [S₁] using hImageKernel
  exact ComposableArrows.exact₂_mk (ComposableArrows.δ₀ (S ⋙ lim)) hzero hExact

/- Domain-style sampling for Lemma 13.31.8 in the homological-complex / sequential-limit domain:
- sampled owner declarations:
  * `CochainComplex.IsKInjective`
  * `CategoryTheory.isKInjective_of_product`
  * `HomologicalComplex.isLimitConeOfHasLimitEval`
  * `SequentialInverseSystem.transitionMap`
- best owner abstractions:
  * `CochainComplex.IsKInjective` for the target property on the inverse-limit complex
  * `SequentialInverseSystem` for the sequential tower itself, with `transitionMap` as derived API
- primitive data:
  * the sequential inverse system `I`
  * termwise split-epimorphism hypotheses on the successor transition maps
  * degreewise existence of limits, which canonically induces `HasLimit I` via
    `HomologicalComplex.isLimitConeOfHasLimitEval`
- derived API:
  * the owner instances `∀ n : ℕ, (I.obj (op n)).IsKInjective`
- source/core/bridge triage:
  * `source-facing`: the K-injectivity statement for the inverse-limit complex
  * `core/canonical`: `CochainComplex.IsKInjective`, the chapter product theorem
    `isKInjective_of_product`, and the homological-complex limit owner
  * `bridge/view`: `SequentialInverseSystem.transitionMap`, which replaces the raw
    `I.map ((homOfLE _).op)` spelling

This item should therefore keep the source-facing limit theorem, but express the tower through the
chapter owner `SequentialInverseSystem` and its derived `transitionMap` API rather than by a
parallel coordinate-level map expression. -/

/-- Lemma 13.31.8: for a sequential inverse system of K-injective cochain complexes in an abelian
category, if every successor transition map is termwise split epic and each degreewise
inverse limit exists, then the inverse-limit complex is K-injective. -/
-- Proof sketch: identify the inverse limit degreewise with the kernel of the Milnor difference
-- map on the product of the tower, use `isKInjective_of_product` for the two product complexes,
-- and then apply `CochainComplex.isKInjective_obj₁_of_distinguished_triangle` to the
-- distinguished triangle coming from the resulting degreewise split short exact sequence.
theorem isKInjective_limit_of_termwiseSplitEpi
    (I : SequentialInverseSystem (CochainComplex 𝒜 ℤ))
    [∀ n : ℕ, (I.obj (op n)).IsKInjective]
    [∀ m : ℤ, HasLimit (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) m)]
    (hTermwiseSplitEpi : ∀ n : ℕ, ∀ m : ℤ, IsSplitEpi ((I.transitionMap (Nat.le_succ n)).f m)) :
    (limit I).IsKInjective := by
  refine { nonempty_homotopy_zero := ?_ }
  intro M f hM
  let S : ComposableArrows AbSeq 3 :=
    ComposableArrows.mk₃
      (homComplexDegreeTowerDelta M I (-2))
      (homComplexDegreeTowerDelta M I (-1))
      (homComplexDegreeTowerDelta M I 0)
  have hS : S.Exact := by
    -- Proof comment: exactness of the four-term row is obtained from exactness of the first
    -- short complex together with exactness of the tail row.
    refine ComposableArrows.exact_of_δ₀ ?_ ?_
    · simpa [S, ComposableArrows.mk₃, ComposableArrows.mk₂] using
        (homComplexTowerShortComplexExact M I (-2) hM).exact_toComposableArrows
    · simpa [S, ComposableArrows.mk₃, ComposableArrows.mk₂] using
        (homComplexTowerShortComplexExact M I (-1) hM).exact_toComposableArrows
  have hML : SequentialInverseSystem.IsMittagLeffler S.left := by
    -- Proof comment: the leftmost degree tower is Mittag-Leffler because every successor map is
    -- split epic after postcomposition on cochains.
    simpa [S, ComposableArrows.mk₃] using
      homComplexDegreeTower_isMittagLeffler M I (-2) hTermwiseSplitEpi
  have hlimExact : (ComposableArrows.δ₀ (S ⋙ lim)).Exact := by
    let S₁ : ShortComplex AbSeq := S.sc hS.toIsComplex 1
    have hImageKernel : imageSubobject (lim.map S₁.f) = kernelSubobject (lim.map S₁.g) := by
      simpa [S₁] using inverseLimitTailKernelImageEqKernel S hS hML
    have hzero :
        (ComposableArrows.δ₀ (S ⋙ lim)).map' 0 1 ≫
          (ComposableArrows.δ₀ (S ⋙ lim)).map' 1 2 = 0 := by
      simpa [S₁] using (S₁.map lim).zero
    have hExact : (S₁.map lim).Exact := by
      rw [ShortComplex.exact_iff_image_eq_kernel]
      simpa [S₁] using hImageKernel
    exact ComposableArrows.exact₂_mk (ComposableArrows.δ₀ (S ⋙ lim)) hzero hExact
  have hlimShort :
      (ShortComplex.mk
        ((ComposableArrows.δ₀ (S ⋙ lim)).map' 0 1)
        ((ComposableArrows.δ₀ (S ⋙ lim)).map' 1 2)
        (by simpa using hlimExact.toIsComplex.zero 0 (by omega))).Exact := by
    -- Proof comment: convert the exactness of the composable-arrow row on inverse limits into the
    -- corresponding exact short complex of abelian groups.
    simpa using ((ComposableArrows.δ₀ (S ⋙ lim)).exact₂_iff hlimExact.toIsComplex).1 hlimExact
  rw [ShortComplex.ab_exact_iff_function_exact] at hlimShort
  let s0 : ((homComplexDegreeTower M I 0 ⋙ forget AddCommGrpCat).sections) :=
    { val := fun k ↦ Cochain.ofHom (f ≫ limit.π I k)
      property := by
        intro i j g
        calc
          homComplexCochainPostcomp
              (K := M) (L := I.obj i) (M := I.obj j) (I.map g) 0
              (Cochain.ofHom (f ≫ limit.π I i))
              =
            Cochain.ofHom ((f ≫ limit.π I i) ≫ I.map g) := by
              simpa [homComplexCochainPostcomp] using
                (Cochain.ofHom_comp (f ≫ limit.π I i) (I.map g)).symm
          _ = Cochain.ofHom (f ≫ limit.π I j) := by
              rw [Category.assoc, limit.w I g] }
  let z0 : ↑(limit (homComplexDegreeTower M I 0)) :=
    limitOfUnderlyingSections (homComplexDegreeTower M I 0) s0
  have hz0 : ((ComposableArrows.δ₀ (S ⋙ lim)).map' 1 2) z0 = 0 := by
    -- Proof comment: each stage projection of the inverse-limit degree-`1` cochain is
    -- `δ (Cochain.ofHom (f ≫ π_k))`, which vanishes because `f ≫ π_k` is a morphism of
    -- complexes.
    apply underlyingSectionsOfLimit_injective (F := homComplexDegreeTower M I 1)
    ext k
    apply Cochain.ext
    intro p q hpq
    have hcoord :
        limit.π (homComplexDegreeTower M I 1) k
            (((ComposableArrows.δ₀ (S ⋙ lim)).map' 1 2) z0) = 0 := by
      have hmap :
          limit.π (homComplexDegreeTower M I 1) k
              (((ComposableArrows.δ₀ (S ⋙ lim)).map' 1 2) z0) =
            (homComplexDegreeTowerDelta M I 0).app k
              (limit.π (homComplexDegreeTower M I 0) k z0) := by
        change
          ((Limits.limMap (homComplexDegreeTowerDelta M I 0) ≫
              limit.π (homComplexDegreeTower M I 1) k) z0) =
            ((limit.π (homComplexDegreeTower M I 0) k ≫
                (homComplexDegreeTowerDelta M I 0).app k) z0)
        exact
          addCommGrpCat_congr_fun
            (Limits.limMap_π (α := homComplexDegreeTowerDelta M I 0) (j := k))
            z0
      have hstage :
          (homComplexDegreeTowerDelta M I 0).app k
              (limit.π (homComplexDegreeTower M I 0) k z0) =
            (HomComplex M (I.obj k)).d 0 1 (Cochain.ofHom (f ≫ limit.π I k)) := by
        rw [limit_π_limitOfUnderlyingSections (F := homComplexDegreeTower M I 0) s0 k]
        rfl
      exact hmap.trans <| hstage.trans <| by
        exact CochainComplex.HomComplex.δ_ofHom (p := 1) (f ≫ limit.π I k)
    have hleftπ :=
      limit_π_underlyingSectionsOfLimit
        (F := homComplexDegreeTower M I 1)
        (((ComposableArrows.δ₀ (S ⋙ lim)).map' 1 2) z0) k
    have hrightπ :=
      limit_π_underlyingSectionsOfLimit
        (F := homComplexDegreeTower M I 1)
        (0 : ↑(limit (homComplexDegreeTower M I 1))) k
    rw [← hleftπ]
    calc
      Cochain.v
          ((ConcreteCategory.hom (limit.π (homComplexDegreeTower M I 1) k))
            (((ComposableArrows.δ₀ (S ⋙ lim)).map' 1 2) z0))
          p q hpq
          = Cochain.v 0 p q hpq := Cochain.congr_v hcoord p q hpq
      _ = Cochain.v ((underlyingSectionsOfLimit (homComplexDegreeTower M I 1) 0).val k) p q hpq := by
            simpa using Cochain.congr_v hrightπ p q hpq
  rcases (hlimShort z0).1 hz0 with ⟨xNegOneRaw, hxNegOneRaw⟩
  let xNegOne : ↑(limit (homComplexDegreeTower M I (-1))) := by
    simpa [S, ComposableArrows.mk₄, ComposableArrows.mk₃, ComposableArrows.mk₂] using xNegOneRaw
  have hxNegOne :
      ((ComposableArrows.δ₀ (S ⋙ lim)).map' 0 1) xNegOne = z0 := by
    simpa [xNegOne, S, ComposableArrows.mk₄, ComposableArrows.mk₃, ComposableArrows.mk₂] using
      hxNegOneRaw
  let sNegOne :
      ((homComplexDegreeTower M I (-1) ⋙ forget AddCommGrpCat).sections) :=
    underlyingSectionsOfLimit (homComplexDegreeTower M I (-1)) xNegOne
  have hsNegOne (k : ℕᵒᵖ) :
      δ (-1) 0 (sNegOne.val k) = Cochain.ofHom (f ≫ limit.π I k) := by
    -- Proof comment: project the exactness witness `xNegOne` to stage `k`; it records exactly
    -- that the degree-`0` family attached to `f` is a coboundary there.
    have hproj := congrArg (fun t ↦ limit.π (homComplexDegreeTower M I 0) k t) hxNegOne
    have hleft :
        limit.π (homComplexDegreeTower M I 0) k
            (((ComposableArrows.δ₀ (S ⋙ lim)).map' 0 1) xNegOne) =
          (HomComplex M (I.obj k)).d (-1) 0 (sNegOne.val k) := by
      have hmap :
          limit.π (homComplexDegreeTower M I 0) k
              (((ComposableArrows.δ₀ (S ⋙ lim)).map' 0 1) xNegOne) =
            (homComplexDegreeTowerDelta M I (-1)).app k
              (limit.π (homComplexDegreeTower M I (-1)) k xNegOne) := by
        change
          ((Limits.limMap (homComplexDegreeTowerDelta M I (-1)) ≫
              limit.π (homComplexDegreeTower M I 0) k) xNegOne) =
            ((limit.π (homComplexDegreeTower M I (-1)) k ≫
                (homComplexDegreeTowerDelta M I (-1)).app k) xNegOne)
        exact
          addCommGrpCat_congr_fun
            (Limits.limMap_π (α := homComplexDegreeTowerDelta M I (-1)) (j := k))
            xNegOne
      have hstage :
          (homComplexDegreeTowerDelta M I (-1)).app k
              (limit.π (homComplexDegreeTower M I (-1)) k xNegOne) =
            (HomComplex M (I.obj k)).d (-1) 0 (sNegOne.val k) := by
        rw [limit_π_underlyingSectionsOfLimit (F := homComplexDegreeTower M I (-1)) xNegOne k]
        rfl
      exact hmap.trans hstage
    have hright :
        limit.π (homComplexDegreeTower M I 0) k z0 =
          Cochain.ofHom (f ≫ limit.π I k) := by
      simpa [z0, s0] using
        limit_π_limitOfUnderlyingSections (F := homComplexDegreeTower M I 0) s0 k
    exact hleft.symm.trans (hproj.trans hright)
  let β : Cochain M (limit I) (-1) :=
    Cochain.mk fun p q hpq ↦
      let τ : (Functor.const ℕᵒᵖ).obj (M.X p) ⟶ I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) q :=
        { app := fun k ↦ (sNegOne.val k).v p q hpq
          naturality := by
            intro i j g
            simpa using homComplexDegreeTowerSectionComponentNaturality M I hpq sNegOne g }
      (limit.isLimit (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) q)).lift
        { pt := M.X p
          π := τ } ≫
        (limitDegreeIso (𝒜 := 𝒜) I q).symm.hom
  have hβπ (k : ℕᵒᵖ) :
      β.comp (Cochain.ofHom (limit.π I k)) (add_zero (-1)) = sNegOne.val k := by
    -- Proof comment: by construction, the degree-`-1` cochain `β` was assembled so that each of
    -- its projections to stage `k` recovers the chosen compatible family `sNegOne`.
    ext p q hpq
    let τ : (Functor.const ℕᵒᵖ).obj (M.X p) ⟶ I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) q :=
      { app := fun j ↦ (sNegOne.val j).v p q hpq
        naturality := by
          intro i j g
          simpa using homComplexDegreeTowerSectionComponentNaturality M I hpq sNegOne g }
    have hπ :
        (limit.isLimit (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) q)).lift
            { pt := M.X p
              π := τ } ≫
            (limitDegreeIso (𝒜 := 𝒜) I q).symm.hom ≫
              (limit.π I k).f q =
          (limit.isLimit (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) q)).lift
            { pt := M.X p
              π := τ } ≫
            limit.π (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) q) k := by
      simpa [Category.assoc] using
        congrArg
          (fun t ↦
            (limit.isLimit (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) q)).lift
              { pt := M.X p
                π := τ } ≫ t)
          (limitDegreeIso_inv_π (𝒜 := 𝒜) I q k)
    have hcomp :
        (β.comp (Cochain.ofHom (limit.π I k)) (add_zero (-1))).v p q hpq =
          β.v p q hpq ≫ (limit.π I k).f q := by
      simp
    have hβdef :
        β.v p q hpq =
          (limit.isLimit (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) q)).lift
            { pt := M.X p
              π := τ } ≫
            (limitDegreeIso (𝒜 := 𝒜) I q).symm.hom := by
      simp [β, τ]
    have hβdef' :
        β.v p q hpq ≫ (limit.π I k).f q =
          (limit.isLimit (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) q)).lift
            { pt := M.X p
              π := τ } ≫
            (limitDegreeIso (𝒜 := 𝒜) I q).symm.hom ≫
              (limit.π I k).f q := by
      simpa [Category.assoc] using congrArg (fun t ↦ t ≫ (limit.π I k).f q) hβdef
    have hfac :
        (limit.isLimit (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) q)).lift
            { pt := M.X p
              π := τ } ≫
            limit.π (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) q) k =
          τ.app k := by
      simpa [τ] using
        (limit.isLimit (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) q)).fac
          { pt := M.X p
            π := τ } k
    exact hcomp.trans <| hβdef'.trans <| hπ.trans <| hfac.trans rfl
  have hδβ : δ (-1) 0 β = Cochain.ofHom f := by
    -- Proof comment: after composing with every stage projection, the differential of `β`
    -- reproduces the stagewise coboundary identities `hsNegOne`; the degreewise limit comparison
    -- then upgrades these identities to the limit complex itself.
    apply Cochain.ext₀
    intro p
    apply (cancel_mono ((limitDegreeIso (𝒜 := 𝒜) I p).hom)).1
    apply limit.hom_ext
    intro k
    have hδcomp :
        (δ (-1) 0 β).comp (Cochain.ofHom (limit.π I k)) (add_zero 0) =
          Cochain.ofHom (f ≫ limit.π I k) := by
      calc
        (δ (-1) 0 β).comp (Cochain.ofHom (limit.π I k)) (add_zero 0)
            = δ (-1) 0 (β.comp (Cochain.ofHom (limit.π I k)) (add_zero (-1))) := by
                symm
                simpa using
                  (CochainComplex.HomComplex.δ_comp_ofHom (n := -1) β (limit.π I k) 0)
        _ = δ (-1) 0 (sNegOne.val k) := by rw [hβπ k]
        _ = Cochain.ofHom (f ≫ limit.π I k) := hsNegOne k
    have hδcomp_v := Cochain.congr_v hδcomp p p (add_zero p)
    have hδcomp_v' :
        (δ (-1) 0 β).v p p (add_zero p) ≫ (limit.π I k).f p =
          f.f p ≫ (limit.π I k).f p := by
      simpa [Cochain.ofHom, Category.assoc] using hδcomp_v
    have hleft :
        (δ (-1) 0 β).v p p (add_zero p) ≫
            (limitDegreeIso (𝒜 := 𝒜) I p).hom ≫
              limit.π (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) p) k =
          (δ (-1) 0 β).v p p (add_zero p) ≫ (limit.π I k).f p := by
      simpa [Category.assoc] using
        congrArg
          (fun t ↦ (δ (-1) 0 β).v p p (add_zero p) ≫ t)
          (limitDegreeIso_hom_π (𝒜 := 𝒜) I p k)
    have hright :
        f.f p ≫ (limitDegreeIso (𝒜 := 𝒜) I p).hom ≫
            limit.π (I ⋙ HomologicalComplex.eval 𝒜 (up ℤ) p) k =
          f.f p ≫ (limit.π I k).f p := by
      simpa [Category.assoc] using
        congrArg (fun t ↦ f.f p ≫ t) (limitDegreeIso_hom_π (𝒜 := 𝒜) I p k)
    simpa [Category.assoc, Cochain.ofHom] using hleft.trans (hδcomp_v'.trans hright.symm)
  refine ⟨(Cochain.equivHomotopy f 0).symm ?_⟩
  refine ⟨β, ?_⟩
  simpa [Cochain.ofHom_zero, add_zero] using hδβ.symm

end

end

end SequentialInverseSystem

end CategoryTheory
