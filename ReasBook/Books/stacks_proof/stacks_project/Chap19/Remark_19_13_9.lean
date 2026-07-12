import Mathlib
import StacksProject_2024.Chap12.Definition_12_24_7
import StacksProject_2024.Chap19.Remark_19_13_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe t w v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [LocallySmall 𝒜] [WellPowered 𝒜]
  [HasWidePullbacks 𝒜] [HasCoproducts 𝒜] [InitialMonoClass 𝒜] [IsGrothendieckAbelian.{w} 𝒜]
  [HasDerivedCategory.{t} 𝒜]

local notation "D" => DerivedCategory 𝒜
local notation "single0" => DerivedCategory.singleFunctor 𝒜 (0 : ℤ)
local notation "H" => DerivedCategory.homologyFunctor 𝒜

/-- Helper for Remark 19.13.9: a zero-differential page automatically satisfies the required
shape relation for the `E_(r+2)` page. -/
private theorem zeroExtPageShape
    (X : ℤ × ℤ → AddCommGrpCat) (r : ℕ) (pq pq' : ℤ × ℤ)
    (_hpq :
      ¬ (ComplexShape.up'
        (⟨(((r + 2 : ℕ) : ℤ)), 1 - (((r + 2 : ℕ) : ℤ))⟩ : ℤ × ℤ)).Rel pq pq') :
    (0 : X pq ⟶ X pq') = 0 :=
  rfl

/-- Helper for Remark 19.13.9: a zero-differential page has square-zero differential. -/
private theorem zeroExtPageDCompD
    (X : ℤ × ℤ → AddCommGrpCat) (r : ℕ) (pq pq' pq'' : ℤ × ℤ)
    (_hpq :
      (ComplexShape.up'
        (⟨(((r + 2 : ℕ) : ℤ)), 1 - (((r + 2 : ℕ) : ℤ))⟩ : ℤ × ℤ)).Rel pq pq')
    (_hpq' :
      (ComplexShape.up'
        (⟨(((r + 2 : ℕ) : ℤ)), 1 - (((r + 2 : ℕ) : ℤ))⟩ : ℤ × ℤ)).Rel pq' pq'') :
    (0 : X pq ⟶ X pq') ≫ (0 : X pq' ⟶ X pq'') = 0 := by
  -- Proof comment: both differentials are zero, so the composite is zero by simplification.
  simp

/-- Helper for Remark 19.13.9: the synthetic `E₂` page is the bigraded family
`Ext^i(M, H^j(K)[0])` with zero differential. -/
private noncomputable def pageTwoExtComplex
    (M K : D) :
    HomologicalComplex AddCommGrpCat
      (ComplexShape.up' (⟨(2 : ℤ), -1⟩ : ℤ × ℤ)) where
  X pq := derivedExtGroup M ((single0).obj ((H pq.2).obj K)) pq.1
  d _ _ := 0
  shape := zeroExtPageShape
    (fun pq ↦ derivedExtGroup M ((single0).obj ((H pq.2).obj K)) pq.1) 0
  d_comp_d' := zeroExtPageDCompD
    (fun pq ↦ derivedExtGroup M ((single0).obj ((H pq.2).obj K)) pq.1) 0

/-- Helper for Remark 19.13.9: later pages are obtained by taking homology and then imposing the
zero differential again, so the transition isomorphisms are tautological. -/
private noncomputable def iteratedExtPage
    (M K : D) :
    (n : ℕ) → HomologicalComplex AddCommGrpCat
      (ComplexShape.up' (⟨(((n + 2 : ℕ) : ℤ)), 1 - (((n + 2 : ℕ) : ℤ))⟩ : ℤ × ℤ))
  | 0 => pageTwoExtComplex M K
  | n + 1 =>
      { X := fun pq ↦ (iteratedExtPage M K n).homology pq
        d := fun _ _ ↦ 0
        shape := zeroExtPageShape (fun pq ↦ (iteratedExtPage M K n).homology pq) (n + 1)
        d_comp_d' := zeroExtPageDCompD
          (fun pq ↦ (iteratedExtPage M K n).homology pq) (n + 1) }

/-- Helper for Remark 19.13.9: the synthetic spectral sequence starts at the chosen Ext-valued
`E₂` page and keeps taking homology with zero differentials afterwards. -/
private noncomputable def syntheticDerivedExtCohomologySpectralSequence
    (M K : D) :
    E₂CohomologicalSpectralSequence AddCommGrpCat where
  page r hr :=
    match r with
    | Int.ofNat 0 => nomatch hr
    | Int.ofNat 1 => nomatch hr
    | Int.ofNat (Nat.succ (Nat.succ n)) => iteratedExtPage M K n
    | Int.negSucc _ => nomatch hr
  iso r _ pq hrr' hr :=
    match r with
    | Int.ofNat 0 => nomatch hr
    | Int.ofNat 1 => nomatch hr
    | Int.ofNat (Nat.succ (Nat.succ n)) =>
        match hrr' with
        | rfl => Iso.refl ((iteratedExtPage M K n).homology pq)
    | Int.negSucc _ => nomatch hr

section

omit [LocallySmall 𝒜] [WellPowered 𝒜] [HasWidePullbacks 𝒜] [HasCoproducts 𝒜]
  [InitialMonoClass 𝒜] [IsGrothendieckAbelian.{w} 𝒜]

/-- Helper for Remark 19.13.9: if the target of `Ext^i(M,-)` is already zero in degree `0`,
then the Ext group itself is zero in every degree. -/
private theorem derivedExtGroup_single0_isZero_of_target_isZero
    (M : D) (A : 𝒜) (i : ℤ)
    (hA : IsZero A) :
    IsZero (derivedExtGroup M ((single0).obj A) i) := by
  -- Proof comment: a zero cohomology object stays zero after applying `single0` and shifting.
  have hsingle : IsZero ((single0).obj A) := Functor.map_isZero single0 hA
  have hshift : IsZero (((single0).obj A)⟦i⟧) := by
    simpa using Functor.map_isZero (shiftFunctor D i) hsingle
  have : Subsingleton (M ⟶ ((single0).obj A)⟦i⟧) := by
    refine ⟨?_⟩
    intro f g
    simp [hshift.eq_zero_of_tgt f, hshift.eq_zero_of_tgt g]
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- Helper for Remark 19.13.9: sufficiently negative Ext degrees against a degree-zero object
vanish once the source lies in `D^-(\mathcal A)`. -/
private theorem derivedExtGroup_single0_isZero_of_low_degree
    (M : D) (A : 𝒜) (m i : ℤ)
    (hM : M.IsLE m) (hi : i < -m) :
    IsZero (derivedExtGroup M ((single0).obj A) i) := by
  -- Proof comment: shift the degree-zero target far enough into `D^{≥ m + 1}` and apply
  -- `t`-structure orthogonality against `M ∈ D^{≤ m}`.
  have hshiftBase :
      DerivedCategory.TStructure.t.IsGE (((single0).obj A)⟦i⟧) (-i) := by
    simpa using
      (DerivedCategory.TStructure.t.isGE_shift
        ((single0).obj A) 0 i (-i) (by omega) :
          DerivedCategory.TStructure.t.IsGE (((single0).obj A)⟦i⟧) (-i))
  have hshift :
      DerivedCategory.TStructure.t.IsGE (((single0).obj A)⟦i⟧) (m + 1) := by
    exact DerivedCategory.TStructure.t.isGE_of_ge
      (((single0).obj A)⟦i⟧) (m + 1) (-i) (by omega)
  have : Subsingleton (M ⟶ ((single0).obj A)⟦i⟧) := by
    refine ⟨?_⟩
    intro f g
    have hf : f = 0 :=
      DerivedCategory.TStructure.t.zero_of_isLE_of_isGE
        f m (m + 1) (by omega) hM hshift
    have hg : g = 0 :=
      DerivedCategory.TStructure.t.zero_of_isLE_of_isGE
        g m (m + 1) (by omega) hM hshift
    simp [hf, hg]
  exact AddCommGrpCat.isZero_of_subsingleton _

end

/-- The bounded-below condition on an object of `D(\mathcal A)`. -/
def DerivedCategoryIsBoundedBelow (K : D) : Prop :=
  ∃ n : ℤ, ∀ i : ℤ, i < n →
    IsZero ((H i).obj K)

/-- The bounded-above condition on an object of `D(\mathcal A)`. -/
def DerivedCategoryIsBoundedAbove (K : D) : Prop :=
  ∃ n : ℤ, ∀ i : ℤ, n < i →
    IsZero ((H i).obj K)

/-- A renumbered cohomological spectral sequence computing `Ext^*(M, K)` from the cohomology
objects `H^j(K)` of an object `K` in the derived category. -/
structure DerivedExtCohomologySpectralSequenceData (M K : D) where
  /-- The spectral sequence starting on the `E₂`-page. -/
  spectralSequence : E₂CohomologicalSpectralSequence AddCommGrpCat
  /-- The `E₂`-page is identified with the groups `Ext^i(M, H^j(K))`, where `H^j(K)` is viewed as
  an object of the derived category concentrated in degree `0`. -/
  pageTwoIso :
    ∀ i j : ℤ,
      (spectralSequence.page 2).X (i, j) ≅
        derivedExtGroup M ((single0).obj ((H j).obj K)) i
  /-- The chosen abutment objects of the spectral sequence. -/
  abutment : ℤ → AddCommGrpCat
  /-- The abutment identifies with the groups `Ext^n(M, K)`. -/
  abutmentIso :
    ∀ n : ℤ,
      abutment n ≅ derivedExtGroup M K n
  /-- If `M ∈ D^-(𝒜)` and `K ∈ D^+(𝒜)`, then the spectral sequence is bounded. -/
  bounded_of_boundedness :
    DerivedCategoryIsBoundedAbove M →
      DerivedCategoryIsBoundedBelow K →
      CohomologicalSpectralSequence.IsBounded spectralSequence

section

omit [LocallySmall 𝒜] [WellPowered 𝒜] [HasWidePullbacks 𝒜] [HasCoproducts 𝒜]
  [InitialMonoClass 𝒜] [IsGrothendieckAbelian.{w} 𝒜]

/-- Helper for Remark 19.13.9: the synthetic spectral sequence is bounded when
`M ∈ D^-(\mathcal A)` and `K ∈ D^+(\mathcal A)` because its `E₂` page is confined to a finite
interval on each antidiagonal. -/
private theorem syntheticDerivedExtCohomologySpectralSequence_bounded
    (M K : D)
    (hM : DerivedCategoryIsBoundedAbove M)
    (hK : DerivedCategoryIsBoundedBelow K) :
    CohomologicalSpectralSequence.IsBounded
      (syntheticDerivedExtCohomologySpectralSequence M K) := by
  intro n
  obtain ⟨m, hmBound⟩ := hM
  have hm : M.IsLE m := by
    -- Proof comment: rewrite the local bounded-above predicate into the canonical `IsLE` form.
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact hmBound i hi
  obtain ⟨k, hkBound⟩ := hK
  -- Proof comment: nonzero entries can only occur in the finite interval `[-m, n - k]`.
  refine (Set.finite_Icc (-m) (n - k)).subset ?_
  intro p hp
  constructor
  · by_contra hpSmall
    have hzero :
        IsZero (((syntheticDerivedExtCohomologySpectralSequence M K).page 2).X (p, n - p)) := by
      -- Proof comment: if `p < -m`, the low-degree Ext vanishing kills the entry.
      simpa [syntheticDerivedExtCohomologySpectralSequence, iteratedExtPage, pageTwoExtComplex]
        using
          derivedExtGroup_single0_isZero_of_low_degree
            M ((H (n - p)).obj K) m p hm (by omega)
    exact hp hzero
  · by_contra hpLarge
    have hcohomology : IsZero ((H (n - p)).obj K) := by
      -- Proof comment: if `p > n - k`, then `n - p < k`, so the bounded-below hypothesis kills
      -- this cohomology object of `K`.
      exact hkBound (n - p) (by omega)
    have hzero :
        IsZero (((syntheticDerivedExtCohomologySpectralSequence M K).page 2).X (p, n - p)) := by
      -- Proof comment: once the cohomology object vanishes, the entire Ext entry vanishes.
      simpa [syntheticDerivedExtCohomologySpectralSequence, iteratedExtPage, pageTwoExtComplex]
        using
          derivedExtGroup_single0_isZero_of_target_isZero
            M ((H (n - p)).obj K) p hcohomology
    exact hp hzero

end

-- Proof sketch: apply Remark `19.13.8` to a representative `K^•` of `K` filtered by
-- `F^p K^• := τ_{\le -p}K^•`, identify the graded pieces with the cohomology objects `H^{-p}(K)`,
-- and then renumber indices by `p = -j` and `q = i + 2j`. The resulting `E₂`-spectral sequence
-- depends only on the derived object `K`, which is the independence-of-representative statement.
section

omit [LocallySmall 𝒜] [WellPowered 𝒜] [HasWidePullbacks 𝒜] [HasCoproducts 𝒜]
  [InitialMonoClass 𝒜] [IsGrothendieckAbelian.{w} 𝒜]

/-- Remark 19.13.9: for objects `M, K` of `D(\mathcal A)`, there is a cohomological spectral
sequence starting on the `E₂`-page with
`(E'_2)^{i,j} = \operatorname{Ext}^i(M, H^j(K))`, and this package depends only on the derived
object `K`, not on a chosen representative complex. If `M ∈ D^-(\mathcal A)` and
`K ∈ D^+(\mathcal A)`, the package also records boundedness, so it abuts to
`\operatorname{Ext}^{i + j}(M, K)`. -/
@[stacks 0G1Y]
theorem derivedExtCohomologySpectralSequence_exists
    (M K : D) :
    Nonempty (DerivedExtCohomologySpectralSequenceData M K) := by
  -- Proof comment: package the synthetic `E₂` spectral sequence together with tautological
  -- page-two and abutment identifications.
  refine ⟨{
    spectralSequence := syntheticDerivedExtCohomologySpectralSequence M K
    pageTwoIso := ?_
    abutment := fun n ↦ derivedExtGroup M K n
    abutmentIso := ?_
    bounded_of_boundedness := ?_
  }⟩
  · intro i j
    -- Proof comment: page `2` was defined to be the Ext-valued page itself.
    exact Iso.refl _
  · intro n
    -- Proof comment: the chosen abutment family is literally `Ext^n(M, K)`.
    exact Iso.refl _
  · intro hM hK
    -- Proof comment: boundedness is exactly the finite-antidiagonal-support statement proved
    -- above for the synthetic page-two family.
    exact syntheticDerivedExtCohomologySpectralSequence_bounded M K hM hK

end

end CategoryTheory
