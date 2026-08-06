import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.EulerCharacteristic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open CategoryTheory

universe u

-- Semantic recall: `Mathlib.Algebra.Homology.EulerCharacteristic` provides
-- `HomologicalComplex.eulerChar` and `HomologicalComplex.homologyEulerChar`.

namespace HomologicalComplex

/-- Helper for Problem 12.5.2: in a short complex of finite-dimensional vector spaces,
the dimension of the middle object splits into the dimension of homology and the dimensions of the
two adjacent boundary images. -/
lemma finrankX₂_eq_finrankHomology_add_finrankRangeToCycles_add_finrankRangeG
    {k : Type u} [Field k] (S : ShortComplex (ModuleCat k))
    [S.HasHomology] [FiniteDimensional k S.X₂] :
    Module.finrank k S.X₂ =
      Module.finrank k S.homology + Module.finrank k (LinearMap.range S.moduleCatToCycles) +
        Module.finrank k (LinearMap.range S.g.hom) := by
  -- The concrete quotient model identifies cycles modulo boundaries with homology.
  have hCycles :
      Module.finrank k (LinearMap.ker S.g.hom) =
        Module.finrank k S.homology + Module.finrank k (LinearMap.range S.moduleCatToCycles) := by
    have hQuot :
        Module.finrank k (LinearMap.ker S.g.hom) =
          Module.finrank k S.moduleCatLeftHomologyData.H +
            Module.finrank k (LinearMap.range S.moduleCatToCycles) := by
      simpa [ShortComplex.moduleCatLeftHomologyData] using
        (Submodule.finrank_quotient_add_finrank
          (R := k) (LinearMap.range S.moduleCatToCycles)).symm
    have hHomology :
        Module.finrank k S.homology = Module.finrank k S.moduleCatLeftHomologyData.H := by
      simpa using LinearEquiv.finrank_eq S.moduleCatHomologyIso.toLinearEquiv
    calc
      Module.finrank k (LinearMap.ker S.g.hom)
          = Module.finrank k S.moduleCatLeftHomologyData.H +
              Module.finrank k (LinearMap.range S.moduleCatToCycles) := hQuot
      _ = Module.finrank k S.homology + Module.finrank k (LinearMap.range S.moduleCatToCycles) := by
            rw [hHomology]
  -- Rank-nullity for the right differential finishes the degreewise decomposition.
  calc
    Module.finrank k S.X₂
        = Module.finrank k (LinearMap.ker S.g.hom) +
            Module.finrank k (LinearMap.range S.g.hom) := by
            simpa [add_comm] using
              (LinearMap.finrank_range_add_finrank_ker S.g.hom).symm
    _ = (Module.finrank k S.homology +
          Module.finrank k (LinearMap.range S.moduleCatToCycles)) +
          Module.finrank k (LinearMap.range S.g.hom) := by
          rw [hCycles]
    _ = Module.finrank k S.homology + Module.finrank k (LinearMap.range S.moduleCatToCycles) +
          Module.finrank k (LinearMap.range S.g.hom) := by
          ac_rfl

/-- Helper for Problem 12.5.2: in the explicit short-complex model
`V.X (i + 1) ⟶ V.X i ⟶ V.X (i - 1)`, the concrete boundary subspace in cycles has the same
finite rank as the image of `V.d (i + 1) i`. -/
lemma finrankRange_moduleCatToCycles_eq_finrankRange_d
    {k : Type u} [Field k] (V : HomologicalComplex (ModuleCat k) (ComplexShape.down ℤ))
    [∀ i : ℤ, V.HasHomology i] (i : ℤ) :
    Module.finrank k (LinearMap.range ((V.sc' (i + 1) i (i - 1)).moduleCatToCycles)) =
      Module.finrank k (LinearMap.range ((V.d (i + 1) i).hom)) := by
  -- Map the range from the kernel subtype back into `V.X i`, then use `d ∘ d = 0`.
  calc
    Module.finrank k (LinearMap.range ((V.sc' (i + 1) i (i - 1)).moduleCatToCycles))
        = Module.finrank k
            (((LinearMap.range ((V.sc' (i + 1) i (i - 1)).moduleCatToCycles)).map
              ((LinearMap.ker ((V.sc' (i + 1) i (i - 1)).g.hom)).subtype))) := by
            symm
            simpa using (Submodule.finrank_map_subtype_eq (R := k)
              (p := LinearMap.ker ((V.sc' (i + 1) i (i - 1)).g.hom))
              (q := LinearMap.range ((V.sc' (i + 1) i (i - 1)).moduleCatToCycles)))
    _ = Module.finrank k
          ↥((LinearMap.ker ((V.d i (i - 1)).hom)) ⊓ Submodule.map ((V.d (i + 1) i).hom) ⊤) := by
          rw [show (V.sc' (i + 1) i (i - 1)).moduleCatToCycles =
            (V.sc' (i + 1) i (i - 1)).f.hom.codRestrict _
              ((V.sc' (i + 1) i (i - 1)).moduleCat_zero_apply) by
              rfl]
          rw [LinearMap.range_codRestrict, LinearMap.range_eq_map, Submodule.map_comap_subtype]
          rfl
    _ = Module.finrank k (Submodule.map ((V.d (i + 1) i).hom) ⊤) := by
          have hle : Submodule.map ((V.d (i + 1) i).hom) ⊤ ≤
              LinearMap.ker ((V.d i (i - 1)).hom) := by
            rw [← LinearMap.range_eq_map]
            exact LinearMap.range_le_ker_iff.2 <|
              ModuleCat.hom_ext_iff.mp (V.d_comp_d (i + 1) i (i - 1))
          rw [inf_eq_right.mpr hle]
    _ = Module.finrank k (LinearMap.range ((V.d (i + 1) i).hom)) := by
          rw [LinearMap.range_eq_map]

/-- Helper for Problem 12.5.2: the degreewise dimension of a chain complex splits as the
dimension of homology plus the dimensions of the incoming and outgoing boundary images. -/
lemma finrank_eq_finrankHomology_add_finrankRange_d_add_finrankRange_prevD
    {k : Type u} [Field k] (V : HomologicalComplex (ModuleCat k) (ComplexShape.down ℤ))
    [∀ i : ℤ, V.HasHomology i]
    [∀ i : ℤ, FiniteDimensional k (V.X i)] (i : ℤ) :
    Module.finrank k (V.X i) =
      Module.finrank k (V.homology i) +
        Module.finrank k (LinearMap.range ((V.d i (i - 1)).hom)) +
        Module.finrank k (LinearMap.range ((V.d (i + 1) i).hom)) := by
  let e : V.sc i ≅ V.sc' (i + 1) i (i - 1) := by
    simpa using V.isoSc' (i := i + 1) (j := i) (k := i - 1) (by simp) (by simp)
  let S : ShortComplex (ModuleCat k) := V.sc' (i + 1) i (i - 1)
  haveI : S.HasHomology := ShortComplex.hasHomology_of_iso e
  haveI : FiniteDimensional k S.X₂ := by
    simpa [S] using (inferInstance : FiniteDimensional k (V.X i))
  have hMiddle :
      Module.finrank k S.X₂ =
        Module.finrank k S.homology +
          Module.finrank k (LinearMap.range S.moduleCatToCycles) +
          Module.finrank k (LinearMap.range S.g.hom) :=
    finrankX₂_eq_finrankHomology_add_finrankRangeToCycles_add_finrankRangeG (k := k) S
  have hHomology :
      Module.finrank k S.homology = Module.finrank k (V.homology i) := by
    simpa [S] using
      (LinearEquiv.finrank_eq (ShortComplex.homologyMapIso e).toLinearEquiv).symm
  -- Replace the explicit short-complex terms with the chain-complex terms of degree `i`.
  calc
    Module.finrank k (V.X i)
        = Module.finrank k S.homology +
            Module.finrank k (LinearMap.range S.moduleCatToCycles) +
            Module.finrank k (LinearMap.range S.g.hom) := by
            simpa [S] using hMiddle
    _ = Module.finrank k (V.homology i) +
          Module.finrank k (LinearMap.range ((V.d (i + 1) i).hom)) +
          Module.finrank k (LinearMap.range ((V.d i (i - 1)).hom)) := by
          rw [hHomology, finrankRange_moduleCatToCycles_eq_finrankRange_d (V := V) (i := i)]
          rfl
    _ = Module.finrank k (V.homology i) +
          Module.finrank k (LinearMap.range ((V.d i (i - 1)).hom)) +
          Module.finrank k (LinearMap.range ((V.d (i + 1) i).hom)) := by
          ac_rfl

/-- Helper for Problem 12.5.2: homology can only be supported where the original complex has
nonzero finite rank. -/
lemma homologyFinrankSupport_subset
    {k : Type u} [Field k] (V : HomologicalComplex (ModuleCat k) (ComplexShape.down ℤ))
    [∀ i : ℤ, V.HasHomology i]
    [∀ i : ℤ, FiniteDimensional k (V.X i)] :
    GradedObject.finrankSupport (fun i => V.homology i) ⊆ GradedObject.finrankSupport V.X := by
  intro i hi
  by_contra hXi
  have hXi0 : Module.finrank k (V.X i) = 0 := by
    simpa [GradedObject.finrankSupport, Function.mem_support] using hXi
  have hle : Module.finrank k (V.homology i) ≤ Module.finrank k (V.X i) := by
    rw [finrank_eq_finrankHomology_add_finrankRange_d_add_finrankRange_prevD
      (V := V) (i := i)]
    simpa [add_assoc] using
      (Nat.le_add_right (Module.finrank k (V.homology i))
        (Module.finrank k (LinearMap.range ((V.d i (i - 1)).hom)) +
          Module.finrank k (LinearMap.range ((V.d (i + 1) i).hom))))
  have hH0 : Module.finrank k (V.homology i) = 0 :=
    Nat.eq_zero_of_le_zero (hXi0 ▸ hle)
  exact hi <| by
    simpa [hH0]

/-- Helper for Problem 12.5.2: if the source term `V.X i` has zero finite rank, then the
boundary image of `V.d i (i - 1)` also has zero finite rank. -/
lemma finrankRange_d_eq_zero_of_not_memSupport
    {k : Type u} [Field k] (V : HomologicalComplex (ModuleCat k) (ComplexShape.down ℤ))
    [∀ i : ℤ, FiniteDimensional k (V.X i)]
    {i : ℤ} (hi : i ∉ GradedObject.finrankSupport V.X) :
    Module.finrank k (LinearMap.range ((V.d i (i - 1)).hom)) = 0 := by
  -- The image cannot have larger finite rank than the source.
  have hXi0 : Module.finrank k (V.X i) = 0 := by
    simpa [GradedObject.finrankSupport, Function.mem_support] using hi
  exact Nat.eq_zero_of_le_zero <| hXi0 ▸ LinearMap.finrank_range_le ((V.d i (i - 1)).hom)

/-- Helper for Problem 12.5.2: if the target term `V.X (i - 1)` has zero finite rank, then the
boundary image of `V.d i (i - 1)` also has zero finite rank. -/
lemma finrankRange_d_eq_zero_of_prev_not_memSupport
    {k : Type u} [Field k] (V : HomologicalComplex (ModuleCat k) (ComplexShape.down ℤ))
    [∀ i : ℤ, FiniteDimensional k (V.X i)]
    {i : ℤ} (hi : i - 1 ∉ GradedObject.finrankSupport V.X) :
    Module.finrank k (LinearMap.range ((V.d i (i - 1)).hom)) = 0 := by
  -- The image sits inside the zero-dimensional target.
  have hXi0 : Module.finrank k (V.X (i - 1)) = 0 := by
    simpa [GradedObject.finrankSupport, Function.mem_support] using hi
  exact Nat.eq_zero_of_le_zero <| hXi0 ▸ (LinearMap.range ((V.d i (i - 1)).hom)).finrank_le

/-- Helper for Problem 12.5.2: the two boundary-image contributions in the finite Euler sum cancel
after reindexing by `i ↦ i + 1`. -/
lemma alternatingSum_boundaryRanges_cancel
    {k : Type u} [Field k] (V : HomologicalComplex (ModuleCat k) (ComplexShape.down ℤ))
    [∀ i : ℤ, FiniteDimensional k (V.X i)]
    (s : Finset ℤ) (hs : GradedObject.finrankSupport V.X ⊆ s) :
    (∑ i ∈ s, ((ComplexShape.down ℤ).χ i : ℤ) *
        Module.finrank k (LinearMap.range ((V.d i (i - 1)).hom))) +
      (∑ i ∈ s, ((ComplexShape.down ℤ).χ i : ℤ) *
        Module.finrank k (LinearMap.range ((V.d (i + 1) i).hom))) = 0 := by
  classical
  let u : Finset ℤ := s ∪ s.image (fun i : ℤ => i + 1)
  let term : ℤ → ℤ := fun i =>
    ((ComplexShape.down ℤ).χ i : ℤ) *
      Module.finrank k (LinearMap.range ((V.d i (i - 1)).hom))
  have hs_u : s ⊆ u := by
    intro i hi
    exact Finset.mem_union.mpr (Or.inl hi)
  have himage_u : s.image (fun i : ℤ => i + 1) ⊆ u := by
    intro i hi
    exact Finset.mem_union.mpr (Or.inr hi)
  have hsum_s :
      ∑ i ∈ s, term i = ∑ i ∈ u, term i := by
    -- Terms in `u \ s` vanish because their source lies outside the complex support.
    refine Finset.sum_subset hs_u ?_
    intro i hiU hiS
    have hiSupport : i ∉ GradedObject.finrankSupport V.X := by
      exact fun hiMem => hiS (hs hiMem)
    simp [term, finrankRange_d_eq_zero_of_not_memSupport (V := V) hiSupport]
  have hshift :
      ∑ i ∈ s, ((ComplexShape.down ℤ).χ i : ℤ) *
          Module.finrank k (LinearMap.range ((V.d (i + 1) i).hom)) =
        -∑ j ∈ s.image (fun i : ℤ => i + 1), term j := by
    -- Reindex the outgoing-boundary sum by `j = i + 1` and use the alternating sign rule.
    calc
      ∑ i ∈ s, ((ComplexShape.down ℤ).χ i : ℤ) *
          Module.finrank k (LinearMap.range ((V.d (i + 1) i).hom))
          = ∑ j ∈ s.image (fun i : ℤ => i + 1),
              ((ComplexShape.down ℤ).χ (j - 1) : ℤ) *
                Module.finrank k (LinearMap.range ((V.d j (j - 1)).hom)) := by
              refine Finset.sum_bijective (fun i : ℤ => i + 1) (Equiv.addRight 1).bijective ?_ ?_
              · intro i
                constructor
                · intro hi
                  exact Finset.mem_image.mpr ⟨i, hi, by simp⟩
                · intro hi
                  rcases Finset.mem_image.mp hi with ⟨j, hj, hji⟩
                  have : j = i := by simpa using add_right_cancel hji
                  simpa [this] using hj
              · intro i hi
                rw [add_sub_cancel_right i 1]
      _ = ∑ j ∈ s.image (fun i : ℤ => i + 1),
            (-((ComplexShape.down ℤ).χ j : ℤ)) *
              Module.finrank k (LinearMap.range ((V.d j (j - 1)).hom)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            have hsign :
                ((ComplexShape.down ℤ).χ (j - 1) : ℤ) = -((ComplexShape.down ℤ).χ j : ℤ) := by
              simpa using congrArg (fun z : ℤˣ => (z : ℤ))
                ((ComplexShape.down ℤ).χ_next (i := j) (j := j - 1) (by simp))
            rw [hsign]
      _ = ∑ j ∈ s.image (fun i : ℤ => i + 1), -(term j) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [term]
      _ = -∑ j ∈ s.image (fun i : ℤ => i + 1), term j := by
            rw [Finset.sum_neg_distrib]
  have hsum_image :
      ∑ j ∈ s.image (fun i : ℤ => i + 1), term j = ∑ j ∈ u, term j := by
    -- Terms in `u \ image(+1)` vanish because their targets lie outside the complex support.
    refine Finset.sum_subset himage_u ?_
    intro i hiU hiImage
    have hiPrevSupport : i - 1 ∉ GradedObject.finrankSupport V.X := by
      intro hiPrev
      exact hiImage <| Finset.mem_image.mpr ⟨i - 1, hs hiPrev, by simp⟩
    have hRangeZero :=
      finrankRange_d_eq_zero_of_prev_not_memSupport (V := V) hiPrevSupport
    simp [term, hRangeZero]
  -- Both boundary sums are the same finite sum with opposite signs.
  calc
    (∑ i ∈ s, term i) +
        (∑ i ∈ s, ((ComplexShape.down ℤ).χ i : ℤ) *
          Module.finrank k (LinearMap.range ((V.d (i + 1) i).hom)))
        = (∑ i ∈ u, term i) + (-∑ i ∈ u, term i) := by
            rw [hsum_s, hshift, hsum_image]
    _ = 0 := by
          ring

/-- For a `ℤ`-indexed homological complex of finite-dimensional vector spaces with only finitely
many nonzero graded pieces, the Euler characteristic agrees with the Euler characteristic of its
homology. This is the canonical `HomologicalComplex` owner underlying Problem 12.5.2. -/
theorem eulerChar_eq_homologyEulerChar_of_finrankSupport_finite
    {k : Type u} [Field k] (V : HomologicalComplex (ModuleCat k) (ComplexShape.down ℤ))
    [∀ i : ℤ, V.HasHomology i]
    [∀ i : ℤ, FiniteDimensional k (V.X i)]
    (h_support : Set.Finite (GradedObject.finrankSupport V.X)) :
    eulerChar V = homologyEulerChar V := by
  classical
  let s : Finset ℤ := h_support.toFinset
  have hs : GradedObject.finrankSupport V.X ⊆ s := by
    simpa [s] using h_support.subset_toFinset
  -- Reduce both Euler characteristics to finite sums over the support of the complex.
  have hEuler :
      eulerChar V = ∑ i ∈ s, ((ComplexShape.down ℤ).χ i : ℤ) * Module.finrank k (V.X i) := by
    simpa [s] using eulerChar_eq_sum_finSet_of_finrankSupport_subset V s hs
  have hHomologyEuler :
      homologyEulerChar V =
        ∑ i ∈ s, ((ComplexShape.down ℤ).χ i : ℤ) * Module.finrank k (V.homology i) := by
    simpa [s] using
      homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset (C := V) s
        (Set.Subset.trans (homologyFinrankSupport_subset (V := V)) hs)
  have hDecomp :
      ∑ i ∈ s, ((ComplexShape.down ℤ).χ i : ℤ) * Module.finrank k (V.X i) =
        (∑ i ∈ s, ((ComplexShape.down ℤ).χ i : ℤ) * Module.finrank k (V.homology i)) +
          (∑ i ∈ s, ((ComplexShape.down ℤ).χ i : ℤ) *
            Module.finrank k (LinearMap.range ((V.d i (i - 1)).hom))) +
          (∑ i ∈ s, ((ComplexShape.down ℤ).χ i : ℤ) *
            Module.finrank k (LinearMap.range ((V.d (i + 1) i).hom))) := by
    -- Rewrite each degree using the rank decomposition and then separate the sums.
    calc
      ∑ i ∈ s, ((ComplexShape.down ℤ).χ i : ℤ) * Module.finrank k (V.X i)
          = ∑ i ∈ s,
              (((ComplexShape.down ℤ).χ i : ℤ) * Module.finrank k (V.homology i) +
                (((ComplexShape.down ℤ).χ i : ℤ) *
                    Module.finrank k (LinearMap.range ((V.d i (i - 1)).hom)) +
                  ((ComplexShape.down ℤ).χ i : ℤ) *
                    Module.finrank k (LinearMap.range ((V.d (i + 1) i).hom)))) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hDegree :
                  (Module.finrank k (V.X i) : ℤ) =
                    Module.finrank k (V.homology i) +
                      Module.finrank k (LinearMap.range ((V.d i (i - 1)).hom)) +
                      Module.finrank k (LinearMap.range ((V.d (i + 1) i).hom)) := by
                exact_mod_cast
                  finrank_eq_finrankHomology_add_finrankRange_d_add_finrankRange_prevD
                    (V := V) (i := i)
              calc
                ((ComplexShape.down ℤ).χ i : ℤ) * Module.finrank k (V.X i)
                    = ((ComplexShape.down ℤ).χ i : ℤ) *
                        (Module.finrank k (V.homology i) +
                          Module.finrank k (LinearMap.range ((V.d i (i - 1)).hom)) +
                          Module.finrank k (LinearMap.range ((V.d (i + 1) i).hom))) := by
                            rw [hDegree]
                _ = ((ComplexShape.down ℤ).χ i : ℤ) * Module.finrank k (V.homology i) +
                      (((ComplexShape.down ℤ).χ i : ℤ) *
                          Module.finrank k (LinearMap.range ((V.d i (i - 1)).hom)) +
                        ((ComplexShape.down ℤ).χ i : ℤ) *
                          Module.finrank k (LinearMap.range ((V.d (i + 1) i).hom))) := by
                      ring
      _ = (∑ i ∈ s, ((ComplexShape.down ℤ).χ i : ℤ) * Module.finrank k (V.homology i)) +
            (∑ i ∈ s, ((ComplexShape.down ℤ).χ i : ℤ) *
              Module.finrank k (LinearMap.range ((V.d i (i - 1)).hom))) +
            (∑ i ∈ s, ((ComplexShape.down ℤ).χ i : ℤ) *
              Module.finrank k (LinearMap.range ((V.d (i + 1) i).hom))) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
            ac_rfl
  have hCancel := alternatingSum_boundaryRanges_cancel (V := V) s hs
  -- The two boundary sums cancel after the index shift, leaving exactly the homology sum.
  calc
    eulerChar V
        = ∑ i ∈ s, ((ComplexShape.down ℤ).χ i : ℤ) * Module.finrank k (V.X i) := hEuler
    _ = (∑ i ∈ s, ((ComplexShape.down ℤ).χ i : ℤ) * Module.finrank k (V.homology i)) +
          (∑ i ∈ s, ((ComplexShape.down ℤ).χ i : ℤ) *
            Module.finrank k (LinearMap.range ((V.d i (i - 1)).hom))) +
          (∑ i ∈ s, ((ComplexShape.down ℤ).χ i : ℤ) *
            Module.finrank k (LinearMap.range ((V.d (i + 1) i).hom))) := hDecomp
    _ = ∑ i ∈ s, ((ComplexShape.down ℤ).χ i : ℤ) * Module.finrank k (V.homology i) := by
          simpa [add_assoc] using
            congrArg
              (fun t : ℤ =>
                (∑ i ∈ s, ((ComplexShape.down ℤ).χ i : ℤ) * Module.finrank k (V.homology i)) + t)
              hCancel
    _ = homologyEulerChar V := by
          symm
          exact hHomologyEuler

end HomologicalComplex

/-- Problem 12.5.2. For a chain complex of finite-dimensional graded vector spaces,
with only finitely many nonzero graded pieces, `χ(V) = χ(H_*(V))`. -/
theorem chainComplex_eulerChar_eq_homologyEulerChar
    {k : Type u} [Field k] (V : ChainComplex (ModuleCat k) ℤ)
    [∀ i : ℤ, FiniteDimensional k (V.X i)]
    (h_support : Set.Finite (GradedObject.finrankSupport V.X)) :
    HomologicalComplex.eulerChar V = HomologicalComplex.homologyEulerChar V := by
  simpa using HomologicalComplex.eulerChar_eq_homologyEulerChar_of_finrankSupport_finite V h_support
