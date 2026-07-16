import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_55_6
import StacksProject_2024.stacks_project.Chap15.Lemma_15_79_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "K₀" => projectiveGrothendieckGroup R

variable (R) in
/-- Helper for Lemma 15.120.1: the zero object of the finite-projective module category. -/
private abbrev zeroFiniteProjectiveModule : FiniteProjectiveModuleCat R :=
  ⟨ModuleCat.of R PUnit, ⟨inferInstance, inferInstance⟩⟩

/-- Helper for Lemma 15.120.1: the zero finite projective module has trivial class in `K₀(R)`.
-/
theorem projectiveGrothendieckGroupOf_zero :
    projectiveGrothendieckGroupOf R (zeroFiniteProjectiveModule (R := R)) = 0 := by
  let Z : FiniteProjectiveModuleCat R := zeroFiniteProjectiveModule (R := R)
  let S : ShortComplex (FiniteProjectiveModuleCat R) :=
    ShortComplex.mk (0 : Z ⟶ Z) (𝟙 Z) (by simp)
  have hS : (S.map (finiteProjectiveModuleProperty R).ι).ShortExact := by
    -- The zero short exact sequence gives the defining relation `[0] - [0] - [0] = 0`.
    let s : (S.map (finiteProjectiveModuleProperty R).ι).Splitting :=
      ShortComplex.Splitting.ofIsZeroOfIsIso
        (S := S.map (finiteProjectiveModuleProperty R).ι)
        (by
          simpa [S, Z, zeroFiniteProjectiveModule] using
            (ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)))
        (by
          simpa [S] using
            (show IsIso (((finiteProjectiveModuleProperty R).ι).map (𝟙 Z)) by infer_instance))
    simpa using s.shortExact
  have hrel :
      FreeAbelianGroup.of Z - FreeAbelianGroup.of Z - FreeAbelianGroup.of Z ∈
        modulePropertyK0Relations R (finiteProjectiveModuleProperty R) := by
    -- Record the generator contributed by the zero short exact sequence.
    refine AddSubgroup.subset_closure ?_
    exact Set.mem_range.2 ⟨⟨S, hS⟩, rfl⟩
  change
    QuotientAddGroup.mk' (modulePropertyK0Relations R (finiteProjectiveModuleProperty R))
      (FreeAbelianGroup.of Z) =
      QuotientAddGroup.mk' (modulePropertyK0Relations R (finiteProjectiveModuleProperty R)) 0
  rw [QuotientAddGroup.mk'_eq_mk']
  refine ⟨FreeAbelianGroup.of Z - FreeAbelianGroup.of Z - FreeAbelianGroup.of Z, hrel, by abel⟩

/-- Helper for Lemma 15.120.1: isomorphic finite projective modules determine the same class in
`K₀(R)`. -/
theorem projectiveGrothendieckGroupOf_eq_of_iso
    {M N : FiniteProjectiveModuleCat R} (e : M ≅ N) :
    projectiveGrothendieckGroupOf R M = projectiveGrothendieckGroupOf R N := by
  let Z : FiniteProjectiveModuleCat R := zeroFiniteProjectiveModule (R := R)
  let S : ShortComplex (FiniteProjectiveModuleCat R) :=
    ShortComplex.mk e.hom (0 : N ⟶ Z) (by simp)
  have hS : (S.map (finiteProjectiveModuleProperty R).ι).ShortExact := by
    -- The split exact sequence `0 ⟶ M ⟶ N ⟶ 0` identifies the two generator classes.
    let s : (S.map (finiteProjectiveModuleProperty R).ι).Splitting :=
      ShortComplex.Splitting.ofIsIsoOfIsZero
        (S := S.map (finiteProjectiveModuleProperty R).ι)
        (by
          simpa [S] using
            (show IsIso (((finiteProjectiveModuleProperty R).ι).map e.hom) by infer_instance))
        (by
          simpa [S, Z, zeroFiniteProjectiveModule] using
            (ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)))
    simpa using s.shortExact
  have hrel :
      FreeAbelianGroup.of N - FreeAbelianGroup.of M - FreeAbelianGroup.of Z ∈
        modulePropertyK0Relations R (finiteProjectiveModuleProperty R) := by
    -- This is the defining short-exact-sequence relation attached to `M ≅ N`.
    refine AddSubgroup.subset_closure ?_
    exact Set.mem_range.2 ⟨⟨S, hS⟩, rfl⟩
  have hsum :
      projectiveGrothendieckGroupOf R N =
        projectiveGrothendieckGroupOf R M +
          projectiveGrothendieckGroupOf R Z := by
    change
      QuotientAddGroup.mk' (modulePropertyK0Relations R (finiteProjectiveModuleProperty R))
        (FreeAbelianGroup.of N) =
        QuotientAddGroup.mk' (modulePropertyK0Relations R (finiteProjectiveModuleProperty R))
          (FreeAbelianGroup.of M + FreeAbelianGroup.of Z)
    rw [QuotientAddGroup.mk'_eq_mk']
    refine
      ⟨-(FreeAbelianGroup.of N - FreeAbelianGroup.of M - FreeAbelianGroup.of Z), ?_, by abel⟩
    exact AddSubgroup.neg_mem _ hrel
  -- Eliminate the zero summand coming from the terminal object.
  calc
    projectiveGrothendieckGroupOf R M =
        projectiveGrothendieckGroupOf R M +
          projectiveGrothendieckGroupOf R Z := by
          rw [projectiveGrothendieckGroupOf_zero (R := R)]
          simp
    _ = projectiveGrothendieckGroupOf R N := hsum.symm

/-- Helper for Lemma 15.120.1: a finite projective module that is zero in `ModuleCat R` has
trivial class in `K₀(R)`. -/
theorem projectiveGrothendieckGroupOf_eq_zero_of_isZero
    (M : FiniteProjectiveModuleCat R) (hM : IsZero M.obj) :
    projectiveGrothendieckGroupOf R M = 0 := by
  let Z : FiniteProjectiveModuleCat R := zeroFiniteProjectiveModule (R := R)
  have e : M ≅ Z := by
    -- Turn the underlying zero-object isomorphism into an isomorphism in the full subcategory.
    exact (finiteProjectiveModuleProperty R).isoMk
      (hM.isoZero ≪≫ (ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)).isoZero.symm)
  calc
    projectiveGrothendieckGroupOf R M =
        projectiveGrothendieckGroupOf R Z :=
      projectiveGrothendieckGroupOf_eq_of_iso (R := R) e
    _ = 0 := projectiveGrothendieckGroupOf_zero (R := R)

/-- Helper for Lemma 15.120.1: a short exact sequence of finite projective modules gives the
defining additivity relation in `K₀(R)`. -/
theorem projectiveGrothendieckGroupOf_add_of_shortExact
    {S : ShortComplex (FiniteProjectiveModuleCat R)}
    (hS : (S.map (finiteProjectiveModuleProperty R).ι).ShortExact) :
    projectiveGrothendieckGroupOf R S.X₂ =
      projectiveGrothendieckGroupOf R S.X₁ + projectiveGrothendieckGroupOf R S.X₃ := by
  -- Apply the quotient relation contributed by this exact row in the finite-projective category.
  change
    QuotientAddGroup.mk' (modulePropertyK0Relations R (finiteProjectiveModuleProperty R))
      (FreeAbelianGroup.of S.X₂) =
      QuotientAddGroup.mk' (modulePropertyK0Relations R (finiteProjectiveModuleProperty R))
        (FreeAbelianGroup.of S.X₁ + FreeAbelianGroup.of S.X₃)
  rw [QuotientAddGroup.mk'_eq_mk']
  refine
    ⟨-(FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃), ?_, by
      abel⟩
  refine AddSubgroup.neg_mem _ ?_
  refine AddSubgroup.subset_closure ?_
  exact Set.mem_range.2 ⟨⟨S, hS⟩, rfl⟩

/- Domain-style sampling for Lemma 15.120.1:
- primary domain: Euler characteristics of perfect objects in the derived category, valued in the
  Grothendieck group of finite projective modules;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `CategoryTheory.DPerf`,
  `projectiveGrothendieckGroup`,
  `CategoryTheory.TriangulatedK0`;
- best owner abstraction:
  the source-facing notion here is an Euler-characteristic value attached to an object of the
  perfect derived category `DPerf R`, while the canonical later owner for the comparison theorem is
  the additive `K₀`-equivalence in Lemma `15.120.2`;
- primitive vs. derived:
  primitive data are a bounded finite-projective representative together with its canonical
  complex-level alternating sum in `K₀(R)`;
  interval formulas, the perfect-complex value predicate, and the canonical Euler characteristic
  with its shift/additivity lemmas are derived API built from that owner and the uniqueness
  statement;
- source/core/bridge triage:
  `source-facing`: the value predicate and its uniqueness statement for a perfect complex;
  `core/canonical`: `DPerf`, `projectiveGrothendieckGroup`, and later `TriangulatedK0`;
  `bridge/view`: the bounded finite-projective representative witnessing a source-facing value,
    together with its complex-level Euler characteristic.

The public source-facing predicate should therefore live on the chapter owner `DPerf` rather than
as a parallel global "perfect complex" wrapper name. -/

namespace CochainComplex

/-- The alternating-sum Euler-characteristic class of a bounded finite-projective cochain complex,
written canonically as a `finsum` in `K₀(R)`. -/
noncomputable def eulerCharacteristic
    (L : Cpx) [hL : IsBoundedFiniteProjective L] : projectiveGrothendieckGroup R :=
  ∑ᶠ i : ℤ,
    i.negOnePow •
      projectiveGrothendieckGroupOf R
        ⟨L.X i, ⟨hL.finite i, hL.projective i⟩⟩

/-- If an interval `[a, b]` contains all nonzero terms of a bounded finite-projective complex,
its canonical Euler-characteristic class is the corresponding finite alternating sum. -/
theorem eulerCharacteristic_eq_sum_Icc
    (L : Cpx) [hL : IsBoundedFiniteProjective L] {a b : ℤ}
    (hge : L.IsStrictlyGE a) (hle : L.IsStrictlyLE b) :
    L.eulerCharacteristic =
      Finset.sum (Finset.Icc a b) fun i ↦
        i.negOnePow •
          projectiveGrothendieckGroupOf R
            ⟨L.X i, ⟨hL.finite i, hL.projective i⟩⟩ := by
  let f : ℤ → K₀ := fun i ↦
    i.negOnePow •
      projectiveGrothendieckGroupOf R
        ⟨L.X i, ⟨hL.finite i, hL.projective i⟩⟩
  -- Turn the global `finsum` into a finite sum by showing all terms outside `[a, b]` vanish.
  change ∑ᶠ i : ℤ, f i = Finset.sum (Finset.Icc a b) f
  rw [finsum_eq_sum_of_support_subset]
  intro i hi
  have hmem : a ≤ i ∧ i ≤ b := by
    constructor
    · by_contra hia
      have hlt : i < a := by omega
      let M : FiniteProjectiveModuleCat R := ⟨L.X i, ⟨hL.finite i, hL.projective i⟩⟩
      have hXi : IsZero M.obj := by
        letI : L.IsStrictlyGE a := hge
        simpa [M] using L.isZero_of_isStrictlyGE a i hlt
      have hi0 : f i = 0 := by
        -- The `K₀(R)`-class of a zero term vanishes, so the whole summand is zero.
        change i.negOnePow • projectiveGrothendieckGroupOf R M = 0
        rw [projectiveGrothendieckGroupOf_eq_zero_of_isZero (R := R) M hXi, smul_zero]
      exact hi hi0
    · by_contra hib
      have hgt : b < i := by omega
      let M : FiniteProjectiveModuleCat R := ⟨L.X i, ⟨hL.finite i, hL.projective i⟩⟩
      have hXi : IsZero M.obj := by
        letI : L.IsStrictlyLE b := hle
        simpa [M] using L.isZero_of_isStrictlyLE b i hgt
      have hi0 : f i = 0 := by
        -- The same zero-term argument handles indices above the support interval.
        change i.negOnePow • projectiveGrothendieckGroupOf R M = 0
        rw [projectiveGrothendieckGroupOf_eq_zero_of_isZero (R := R) M hXi, smul_zero]
      exact hi hi0
  simpa [Finset.mem_Icc] using hmem

/-- Helper for Lemma 15.120.1: negating an index does not change the parity sign `(-1)^n`. -/
private theorem negOnePow_neg (n : ℤ) :
    (-n).negOnePow = n.negOnePow := by
  -- Compare both sides through the square, where `(-n)^2 = n^2`.
  calc
    (-n).negOnePow = ((-n) * (-n)).negOnePow := by
      rw [← Int.negOnePow_mul_self]
    _ = (n * n).negOnePow := by
      congr 1
      ring
    _ = n.negOnePow := by
      rw [Int.negOnePow_mul_self]

/-- Helper for Lemma 15.120.1: translating the degree by `n` pulls out the sign `(-1)^n`. -/
private theorem negOnePow_sub
    (i n : ℤ) :
    (i - n).negOnePow = n.negOnePow * i.negOnePow := by
  -- Rewrite the shifted index as `i + (-n)` and separate the two parity contributions.
  calc
    (i - n).negOnePow = (i + (-n)).negOnePow := by
      rw [sub_eq_add_neg]
    _ = i.negOnePow * (-n).negOnePow := by
      rw [Int.negOnePow_add]
    _ = i.negOnePow * n.negOnePow := by
      rw [negOnePow_neg]
    _ = n.negOnePow * i.negOnePow := by
      rw [mul_comm]

/-- Helper for Lemma 15.120.1: translating an integer interval by `n` matches the shifted support
interval used for `L⟦n⟧`. -/
private theorem mem_Icc_sub_right_iff
    {a b i n : ℤ} :
    i ∈ Finset.Icc (a - n) (b - n) ↔ i + n ∈ Finset.Icc a b := by
  -- Interval membership is just the pair of translated inequalities.
  simp [Finset.mem_Icc]
  omega

/-- Helper for Lemma 15.120.1: adding `n` identifies the shifted support interval with the
original support interval. -/
private theorem map_add_right_Icc
    (a b n : ℤ) :
    (Finset.Icc (a - n) (b - n)).map
        ⟨fun i ↦ i + n, by
          intro i j hij
          simpa using add_right_cancel hij⟩ =
      Finset.Icc a b := by
  -- Extensionality reduces the map statement to translated interval membership.
  ext i
  constructor
  · intro hi
    simp only [Finset.mem_map] at hi
    rcases hi with ⟨j, hj, rfl⟩
    exact (mem_Icc_sub_right_iff (a := a) (b := b) (i := j) (n := n)).1 hj
  · intro hi
    simp only [Finset.mem_map]
    refine ⟨i - n, ?_, by simp⟩
    have hi' : i - n + n ∈ Finset.Icc a b := by
      simpa using hi
    exact (mem_Icc_sub_right_iff (a := a) (b := b) (i := i - n) (n := n)).2 hi'

/-- Helper for Lemma 15.120.1: after shifting a bounded finite-projective complex, each degree
term has the same `K₀(R)`-class as the corresponding translated original term. -/
private theorem projectiveGrothendieckGroupOf_shift_term_eq
    (L : Cpx) [hL : IsBoundedFiniteProjective L] (n i : ℤ)
    [hShift : IsBoundedFiniteProjective (L⟦n⟧)] :
    projectiveGrothendieckGroupOf R
      ⟨(L⟦n⟧).X i, ⟨hShift.finite i, hShift.projective i⟩⟩ =
        projectiveGrothendieckGroupOf R
          ⟨L.X (i + n), ⟨hL.finite (i + n), hL.projective (i + n)⟩⟩ := by
  let Mshift : FiniteProjectiveModuleCat R :=
    ⟨(L⟦n⟧).X i, ⟨hShift.finite i, hShift.projective i⟩⟩
  let Morig : FiniteProjectiveModuleCat R :=
    ⟨L.X (i + n), ⟨hL.finite (i + n), hL.projective (i + n)⟩⟩
  have e : Mshift ≅ Morig := by
    -- Lift the canonical shift degree identification into the finite-projective subcategory.
    exact (finiteProjectiveModuleProperty R).isoMk
      (L.shiftFunctorObjXIso n i (i + n) rfl)
  -- Isomorphic finite projective modules contribute the same generator class to `K₀(R)`.
  exact projectiveGrothendieckGroupOf_eq_of_iso (R := R) e

/-- Helper for Lemma 15.120.1: shifting a bounded finite-projective complex preserves bounded
finite-projectivity. -/
theorem isBoundedFiniteProjective_shift
    (L : Cpx) [hL : IsBoundedFiniteProjective L] (n : ℤ) :
    IsBoundedFiniteProjective (L⟦n⟧) := by
  rcases hL.bounded with ⟨a, b, hge, hle⟩
  letI : L.IsStrictlyGE a := hge
  letI : L.IsStrictlyLE b := hle
  refine ⟨?_, ?_, ?_⟩
  · -- Shift translates any support interval `[a, b]` to `[a - n, b - n]`.
    refine ⟨a - n, b - n, ?_, ?_⟩
    · simpa using L.isStrictlyGE_shift a n (a - n) (by omega)
    · simpa using L.isStrictlyLE_shift b n (b - n) (by omega)
  · -- Each shifted degree is definitionally the translated original degree.
    intro i
    simpa using hL.finite (i + n)
  · -- Projectivity is preserved for the same translated term.
    intro i
    simpa using hL.projective (i + n)

/-- Helper for Lemma 15.120.1: bounded finite-projectivity shifts canonically along the complex
shift functor. -/
instance (L : Cpx) [IsBoundedFiniteProjective L] (n : ℤ) :
    IsBoundedFiniteProjective (L⟦n⟧) :=
  isBoundedFiniteProjective_shift (R := R) L n

/-- Helper for Lemma 15.120.1: shifting a bounded finite-projective complex multiplies its Euler
characteristic by the canonical sign `(-1)^n`. -/
theorem eulerCharacteristic_shift
    (L : Cpx) [hL : IsBoundedFiniteProjective L] (n : ℤ) :
    (L⟦n⟧).eulerCharacteristic = n.negOnePow • L.eulerCharacteristic := by
  rcases hL.bounded with ⟨a, b, hge, hle⟩
  letI : L.IsStrictlyGE a := hge
  letI : L.IsStrictlyLE b := hle
  have hShiftGE : (L⟦n⟧).IsStrictlyGE (a - n) := by
    simpa using L.isStrictlyGE_shift a n (a - n) (by omega)
  have hShiftLE : (L⟦n⟧).IsStrictlyLE (b - n) := by
    simpa using L.isStrictlyLE_shift b n (b - n) (by omega)
  -- Compute both Euler characteristics on matching finite support intervals.
  rw [eulerCharacteristic_eq_sum_Icc (R := R) (L := L⟦n⟧) hShiftGE hShiftLE]
  rw [eulerCharacteristic_eq_sum_Icc (R := R) (L := L) hge hle]
  rw [Finset.smul_sum]
  -- Reindex the shifted interval by translation `i ↦ i + n`.
  refine Finset.sum_bij (fun i _ ↦ i + n) ?_ ?_ ?_ ?_
  · intro i hi
    exact (mem_Icc_sub_right_iff (a := a) (b := b) (i := i) (n := n)).1 hi
  · intro i hi j hj hij
    simpa using add_right_cancel hij
  · intro j hj
    refine ⟨j - n, ?_, by simp⟩
    have hj' : j - n + n ∈ Finset.Icc a b := by
      simpa using hj
    exact (mem_Icc_sub_right_iff (a := a) (b := b) (i := j - n) (n := n)).2 hj'
  · intro i hi
    calc
      i.negOnePow •
          projectiveGrothendieckGroupOf R
            ⟨(L⟦n⟧).X i, ⟨inferInstance, inferInstance⟩⟩ =
          i.negOnePow •
            projectiveGrothendieckGroupOf R
              ⟨L.X (i + n), ⟨hL.finite (i + n), hL.projective (i + n)⟩⟩ := by
            rw [projectiveGrothendieckGroupOf_shift_term_eq (R := R) (L := L) n i]
      _ = n.negOnePow •
            ((i + n).negOnePow •
              projectiveGrothendieckGroupOf R
                ⟨L.X (i + n), ⟨hL.finite (i + n), hL.projective (i + n)⟩⟩) := by
            have hsign : i.negOnePow = n.negOnePow * (i + n).negOnePow := by
              simpa using (negOnePow_sub (i := i + n) (n := n))
            simp [hsign, smul_smul]

/-- Helper for Lemma 15.120.1: the mapping cone of a morphism between bounded finite-projective
complexes is again bounded finite-projective. -/
theorem isBoundedFiniteProjective_mappingCone
    {L M : Cpx} (f : L ⟶ M)
    [hL : IsBoundedFiniteProjective L] [hM : IsBoundedFiniteProjective M] :
    IsBoundedFiniteProjective (CochainComplex.mappingCone f) := by
  rcases hL.bounded with ⟨aL, bL, hLGE, hLLE⟩
  rcases hM.bounded with ⟨aM, bM, hMGE, hMLE⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Bound the cone on a single interval containing the translated source and the target.
    refine ⟨min (aL - 1) aM, max (bL - 1) bM, ?_, ?_⟩
    · rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      have hLi : i + 1 < aL := by omega
      have hMi : i < aM := by omega
      have hLzero : IsZero (L.X (i + 1)) := by
        letI : L.IsStrictlyGE aL := hLGE
        simpa using L.isZero_of_isStrictlyGE aL (i + 1) hLi
      have hMzero : IsZero (M.X i) := by
        letI : M.IsStrictlyGE aM := hMGE
        simpa using M.isZero_of_isStrictlyGE aM i hMi
      -- `mappingCone.isZero_X_iff` turns the degreewise cone term into its two summands.
      rw [CochainComplex.mappingCone.isZero_X_iff (φ := f) i]
      exact ⟨hLzero, hMzero⟩
    · rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      have hLi : bL < i + 1 := by omega
      have hMi : bM < i := by omega
      have hLzero : IsZero (L.X (i + 1)) := by
        letI : L.IsStrictlyLE bL := hLLE
        simpa using L.isZero_of_isStrictlyLE bL (i + 1) hLi
      have hMzero : IsZero (M.X i) := by
        letI : M.IsStrictlyLE bM := hMLE
        simpa using M.isZero_of_isStrictlyLE bM i hMi
      -- The same cone decomposition handles the upper support bound.
      rw [CochainComplex.mappingCone.isZero_X_iff (φ := f) i]
      exact ⟨hLzero, hMzero⟩
  · -- Each cone term is the biproduct of two finite modules.
    intro i
    let e :
        (CochainComplex.mappingCone f).X i ≅ ModuleCat.of R (L.X (i + 1) × M.X i) :=
      (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1)
          (ComplexShape.up_mk i (i + 1) rfl)) ≪≫
        ModuleCat.biprodIsoProd _ _
    exact Module.Finite.equiv e.symm.toLinearEquiv
  · -- Projectivity is preserved by the same biproduct description.
    intro i
    let e :
        (CochainComplex.mappingCone f).X i ≅ ModuleCat.of R (L.X (i + 1) × M.X i) :=
      (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1)
          (ComplexShape.up_mk i (i + 1) rfl)) ≪≫
        ModuleCat.biprodIsoProd _ _
    exact Module.Projective.of_equiv e.symm.toLinearEquiv

/-- Helper for Lemma 15.120.1: bounded finite-projectivity is stable under mapping cones. -/
instance {L M : Cpx} (f : L ⟶ M)
    [IsBoundedFiniteProjective L] [IsBoundedFiniteProjective M] :
    IsBoundedFiniteProjective (CochainComplex.mappingCone f) :=
  isBoundedFiniteProjective_mappingCone (R := R) f

/-- Helper for Lemma 15.120.1: a placeholder adapter recording that bounded finite-projective
complexes are intended to be used through a bounded-above API. -/
theorem minus_of_isBoundedFiniteProjective
    (L : Cpx) [_hL : IsBoundedFiniteProjective L] :
    True := by
  -- TODO: reintroduce the actual `CochainComplex.minus` owner once the bounded-above import layer
  -- is stabilized for this file.
  trivial

/-- Helper for Lemma 15.120.1: an acyclic bounded finite-projective complex has trivial Euler
class in `K₀(R)`. -/
theorem eulerCharacteristic_eq_zero_of_acyclic
    (L : Cpx) [hL : IsBoundedFiniteProjective L] (hAcyclic : L.Acyclic) :
    L.eulerCharacteristic = 0 := sorry

/-- Helper for Lemma 15.120.1: the mapping cone satisfies the expected Euler-class formula. -/
theorem eulerCharacteristic_add_of_mappingCone
    {L M : Cpx} (f : L ⟶ M)
    [hL : IsBoundedFiniteProjective L] [hM : IsBoundedFiniteProjective M] :
    M.eulerCharacteristic =
      L.eulerCharacteristic + (CochainComplex.mappingCone f).eulerCharacteristic := sorry

/-- Helper for Lemma 15.120.1: quasi-isomorphic bounded finite-projective complexes have the same
Euler class. -/
theorem eulerCharacteristic_eq_of_quasiIso
    {L M : Cpx} (f : L ⟶ M)
    [hL : IsBoundedFiniteProjective L] [hM : IsBoundedFiniteProjective M] [QuasiIso f] :
    L.eulerCharacteristic = M.eulerCharacteristic := by
  let Qh := HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
  have hq :
      HomotopyCategory.quasiIso (ModuleCat R) (ComplexShape.up ℤ) (Qh.map f) :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff
      (C := ModuleCat R) (c := ComplexShape.up ℤ) f).2
        (show QuasiIso f from inferInstance)
  have hq' :
      (HomotopyCategory.subcategoryAcyclic (ModuleCat R)).trW (Qh.map f) := by
    -- Convert the quasi-isomorphism into the acyclic mapping-cone witness in the homotopy
    -- category.
    simpa [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W (C := ModuleCat R)] using hq
  have hCone_mem :
      HomotopyCategory.subcategoryAcyclic (ModuleCat R)
        (Qh.obj (CochainComplex.mappingCone f)) := by
    -- The standard mapping-cone triangle identifies the cone object with the `trW` condition.
    simpa using
      ((HomotopyCategory.subcategoryAcyclic (ModuleCat R)).trW_iff_of_distinguished
        (CochainComplex.mappingCone.triangleh f)
        (HomotopyCategory.mappingCone_triangleh_distinguished f)).1 hq'
  have hCone : (CochainComplex.mappingCone f).Acyclic := by
    -- Return from the homotopy-category acyclic subcategory to ordinary acyclicity of complexes.
    exact
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
        (C := ModuleCat R) (CochainComplex.mappingCone f)).1 hCone_mem
  -- The cone contributes zero Euler class, so the cone additivity formula becomes equality.
  calc
    L.eulerCharacteristic = L.eulerCharacteristic +
        (CochainComplex.mappingCone f).eulerCharacteristic := by
          rw [eulerCharacteristic_eq_zero_of_acyclic
            (R := R) (L := CochainComplex.mappingCone f) hCone]
          simp
    _ = M.eulerCharacteristic :=
      (eulerCharacteristic_add_of_mappingCone (R := R) f).symm

end CochainComplex

namespace CategoryTheory.DPerf

open CochainComplex DerivedCategory

/-- A class `c ∈ K₀(R)` is an Euler-characteristic value of a perfect derived `R`-complex `K`
if `K` is represented by a bounded finite-projective complex and `c` is the canonical
Euler-characteristic class of that representative. Equivalently, by
`CochainComplex.eulerCharacteristic_eq_sum_Icc`, `c` is the finite alternating sum over any
interval containing all nonzero terms of the representative. -/
def IsEulerCharacteristicValue
    (K : DPerf R) (c : K₀) : Prop :=
  ∃ (L : Cpx) (_ : K.obj ≅ DerivedCategory.Q.obj L) (_ : IsBoundedFiniteProjective L),
    c = L.eulerCharacteristic

/-- Helper for Lemma 15.120.1: every perfect object admits at least one Euler-characteristic
value, obtained from any bounded finite-projective representative. -/
private theorem exists_isEulerCharacteristicValue
    (K : DPerf R) :
    ∃ c : K₀, K.IsEulerCharacteristicValue c := by
  -- Unpack the perfect representative carried by the object-property witness on `K`.
  rcases K.property with ⟨L, e, hL⟩
  refine ⟨L.eulerCharacteristic, L, e, hL, rfl⟩

/-- Helper for Lemma 15.120.1: shifting a bounded finite-projective complex preserves bounded
finite-projectivity. -/
private theorem isBoundedFiniteProjective_shift
    (L : Cpx) [hL : IsBoundedFiniteProjective L] (n : ℤ) :
    IsBoundedFiniteProjective (L⟦n⟧) := by
  -- Reuse the complex-level boundedness theorem so the derived proof only tracks representation.
  exact CochainComplex.isBoundedFiniteProjective_shift (R := R) L n

/-- Helper for Lemma 15.120.1: after choosing bounded finite-projective representatives for the
first two vertices of a distinguished triangle, the third vertex is represented by the mapping
cone of a strict lift of the first map. -/
private theorem exists_mappingCone_representative_of_distinguishedTriangle
    (T : Triangle (DPerf R)) (hT : T ∈ distTriang (DPerf R))
    (L M : Cpx) (e₁ : T.obj₁.obj ≅ DerivedCategory.Q.obj L)
    (e₂ : T.obj₂.obj ≅ DerivedCategory.Q.obj M)
    [IsBoundedFiniteProjective L] [IsBoundedFiniteProjective M] :
    ∃ f : L ⟶ M,
      T.obj₃.IsEulerCharacteristicValue (CochainComplex.mappingCone f).eulerCharacteristic := sorry

/-- Helper for Lemma 15.120.1: uniqueness of Euler-characteristic values reduces to the
representative-independence statement for bounded finite-projective complexes. -/
private theorem isEulerCharacteristicValue_unique
    {K : DPerf R} {c₁ c₂ : K₀}
    (hc₁ : K.IsEulerCharacteristicValue c₁)
    (hc₂ : K.IsEulerCharacteristicValue c₂) :
    c₁ = c₂ := by
  rcases hc₁ with ⟨L, e₁, hL, rfl⟩
  rcases hc₂ with ⟨M, e₂, hM, rfl⟩
  let Q := HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
  let e : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj M := e₁.symm ≪≫ e₂
  letI : IsBoundedFiniteProjective L := hL
  rcases hL.bounded with ⟨_a, b, _hLGE, hLLE⟩
  letI : L.IsStrictlyLE b := hLLE
  letI : ∀ n : ℤ, Projective (L.X n) := fun n ↦ inferInstance
  letI : CochainComplex.IsKProjective L :=
    CochainComplex.isKProjective_of_projective L b
  let c :=
    Iso.homCongr
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app L)
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app M)
  obtain ⟨g, hg⟩ :=
    (CochainComplex.IsKProjective.Qh_map_bijective L (Q.obj M)).surjective (c.symm e.hom)
  obtain ⟨f, hf⟩ := Q.map_surjective g
  have hQ : DerivedCategory.Q.map f = e.hom := by
    -- The homotopy representative `g` and the comparison isomorphism `quotient ⋙ Qh ≅ Q`
    -- recover the original derived isomorphism.
    calc
      DerivedCategory.Q.map f =
          c (DerivedCategory.Qh.map (Q.map f)) := by
            symm
            change
              (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app L ≫
                  DerivedCategory.Qh.map (Q.map f) ≫
                (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app M =
                DerivedCategory.Q.map f
            have hnat :
                DerivedCategory.Qh.map (Q.map f) ≫
                    (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app M =
                  (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app L ≫
                    DerivedCategory.Q.map f := by
              simpa [Functor.comp_map] using
                (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.naturality f
            calc
              (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app L ≫
                  DerivedCategory.Qh.map (Q.map f) ≫
                (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app M =
                  (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app L ≫
                    ((DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app L ≫
                      DerivedCategory.Q.map f) := by
                        simpa [Category.assoc] using
                          congrArg
                            (fun k ↦
                              (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app L ≫ k)
                            hnat
              _ = DerivedCategory.Q.map f := by
                    simpa using
                      (Iso.inv_hom_id_assoc
                        ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app L)
                        (DerivedCategory.Q.map f))
      _ = c (DerivedCategory.Qh.map g) := by
            simpa [hf]
      _ = c (c.symm e.hom) := by
            simpa using congrArg c hg
      _ = e.hom := by
            exact c.apply_symm_apply e.hom
  haveI : IsIso (DerivedCategory.Q.map f) := by
    -- The chosen strict representative of the derived isomorphism is still an isomorphism after
    -- applying `Q`.
    simpa [hQ] using (show IsIso e.hom by infer_instance)
  haveI : QuasiIso f := by
    -- Route correction: use the existing `Q.map`/quasi-isomorphism bridge directly instead of
    -- introducing a separate bounded-above replacement route.
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) f).1 inferInstance
  -- Representative-independence is exactly quasi-isomorphism invariance on the chosen models.
  exact CochainComplex.eulerCharacteristic_eq_of_quasiIso (R := R) f

-- Proof sketch: existence comes from choosing any bounded finite-projective representative of the
-- perfect complex and taking the alternating sum of its terms in `K₀(R)`. Uniqueness is the
-- well-definedness argument from the textbook: quasi-isomorphic bounded finite-projective
-- representatives have acyclic cone, and acyclic bounded finite-projective complexes contribute
-- zero in `K₀(R)`.
/-- Lemma 15.120.1: every perfect complex over `R` has a unique Euler-characteristic class in
`K₀(R)`, namely the alternating sum of the terms of any bounded finite-projective representative. -/
theorem existsUnique_isEulerCharacteristicValue
    (K : DPerf R) :
    ∃! c : K₀, K.IsEulerCharacteristicValue c := by
  -- Existence is immediate from any perfect representative; uniqueness is the remaining
  -- representative-independence statement isolated in `isEulerCharacteristicValue_unique`.
  obtain ⟨c, hc⟩ := exists_isEulerCharacteristicValue (R := R) K
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  exact (isEulerCharacteristicValue_unique (R := R) (K := K) (c₁ := c) (c₂ := c') hc hc').symm

/-- The canonical Euler-characteristic class in `K₀(R)` attached to a perfect derived
`R`-complex. -/
noncomputable def eulerCharacteristic
    (K : DPerf R) : K₀ :=
  (K.existsUnique_isEulerCharacteristicValue).choose

/-- The canonical Euler-characteristic class satisfies the defining alternating-sum formula. -/
theorem eulerCharacteristic_spec
    (K : DPerf R) :
    K.IsEulerCharacteristicValue K.eulerCharacteristic := by
  exact (K.existsUnique_isEulerCharacteristicValue).choose_spec.1

/-- Any Euler-characteristic value of a perfect complex agrees with its canonical
Euler-characteristic class. -/
theorem eq_eulerCharacteristic
    {K : DPerf R} {c : K₀}
    (hc : K.IsEulerCharacteristicValue c) :
    c = K.eulerCharacteristic := by
  exact (K.existsUnique_isEulerCharacteristicValue).choose_spec.2 c hc

-- Proof sketch: shift a bounded finite-projective representative by `n`; its terms are the same
-- modules with all degrees translated by `n`, so the alternating sum is multiplied by the
-- canonical sign `(-1)^n`.
/-- Shifting a perfect complex multiplies its Euler-characteristic class by the canonical sign
`(-1)^n`. -/
theorem isEulerCharacteristicValue_shift
    {K : DPerf R} {c : K₀}
    (hc : K.IsEulerCharacteristicValue c) (n : ℤ) :
    (K⟦n⟧).IsEulerCharacteristicValue (n.negOnePow • c) := by
  rcases hc with ⟨L, e, hL, rfl⟩
  refine ⟨L⟦n⟧, ?_, ?_, ?_⟩
  · -- Shift the chosen representative and transport the comparison isomorphism through `Q`.
    let P : ObjectProperty (DerivedCategory (ModuleCat R)) := DerivedCategory.IsPerfect
    exact (((P.ι).commShiftIso n).app K) ≪≫
      (shiftFunctor _ n).mapIso e ≪≫
        ((DerivedCategory.Q.commShiftIso n).app L).symm
  · -- The shift stays bounded finite-projective, so it still represents a perfect object.
    exact isBoundedFiniteProjective_shift (R := R) L n
  · -- Apply the already established complex-level shift formula to the chosen representative.
    simpa using (CochainComplex.eulerCharacteristic_shift (R := R) L n).symm

-- Proof sketch: the source-facing shift statement applied to the canonical value of `K` produces
-- a value for `K⟦n⟧`; uniqueness for `K⟦n⟧` then identifies that value with the canonical Euler
-- characteristic of the shift.
/-- Shifting a perfect complex multiplies its canonical Euler-characteristic class by the canonical
sign `(-1)^n`. -/
theorem eulerCharacteristic_shift
    (K : DPerf R) (n : ℤ) :
    (K⟦n⟧).eulerCharacteristic = n.negOnePow • K.eulerCharacteristic := by
  -- Push the source-facing shift statement to the canonical class by uniqueness.
  exact (eq_eulerCharacteristic (isEulerCharacteristicValue_shift (eulerCharacteristic_spec K) n)).symm

-- Proof sketch: represent a distinguished triangle of perfect complexes by a short exact sequence
-- of bounded finite-projective complexes up to quasi-isomorphism. The termwise short exact
-- sequences split because the terms are projective, so the alternating sums satisfy the desired
-- additivity in `K₀(R)`.
/-- In a distinguished triangle of perfect complexes, the middle Euler-characteristic class is the
sum of the outer two classes. -/
theorem isEulerCharacteristicValue_add_of_distinguishedTriangle
    {T : Triangle (DPerf R)} (hT : T ∈ distTriang (DPerf R))
    {c₁ c₂ c₃ : K₀}
    (hc₁ : T.obj₁.IsEulerCharacteristicValue c₁)
    (hc₂ : T.obj₂.IsEulerCharacteristicValue c₂)
    (hc₃ : T.obj₃.IsEulerCharacteristicValue c₃) :
    c₂ = c₁ + c₃ := by
  -- TODO: choose representatives for the first two vertices, identify the third with a mapping
  -- cone representative, and then apply `CochainComplex.eulerCharacteristic_add_of_mappingCone`.
  sorry

-- Proof sketch: apply the source-facing additivity statement to the canonical values of the
-- three vertices and use uniqueness on each object to identify those values with the owner-level
-- Euler characteristics.
/-- In a distinguished triangle of perfect complexes, the canonical Euler-characteristic classes
are additive. -/
theorem eulerCharacteristic_add_of_distinguishedTriangle
    {T : Triangle (DPerf R)} (hT : T ∈ distTriang (DPerf R)) :
    T.obj₂.eulerCharacteristic = T.obj₁.eulerCharacteristic + T.obj₃.eulerCharacteristic := by
  -- Reduce to the source-facing additivity statement on the canonical Euler-characteristic values.
  exact isEulerCharacteristicValue_add_of_distinguishedTriangle hT
    (eulerCharacteristic_spec T.obj₁)
    (eulerCharacteristic_spec T.obj₂)
    (eulerCharacteristic_spec T.obj₃)

end CategoryTheory.DPerf

end
