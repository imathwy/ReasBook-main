import Mathlib
import StacksProject_2024.Chap12.Definition_12_11_1
import StacksProject_2024.Chap12.Lemma_12_11_3
import StacksProject_2024.Chap12.Lemma_12_10_3
import StacksProject_2024.Chap13.Lemma_13_4_9
import StacksProject_2024.Chap13.Lemma_13_17_1
import StacksProject_2024.Chap13.Lemma_13_27_9
import StacksProject_2024.Chap13.Definition_13_28_1
import StacksProject_2024.Chap13.Lemma_13_6_4
import StacksProject_2024.Chap13.Remark_13_12_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open DerivedCategory
open DerivedCategory.TStructure
open scoped DerivedCategoryWithCohomologyIn
open scoped ZeroObject

noncomputable section

universe v u

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]

local notation "H" => DerivedCategory.homologyFunctor A
local notation "single₀" => singleFunctor A (0 : ℤ)

section LocalEulerInfrastructure

/-- Helper for Lemma 13.28.5: the degree-zero complex of an object of `A` is bounded. -/
theorem singleFunctor_obj_mem_boundedDerivedCategory (X : A) :
    t.bounded ((single₀).obj X) := by
  -- The degree-zero complex has no cohomology outside degree `0`.
  rw [derivedCategory_t_bounded_iff]
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩⟩
  · intro i hi
    let _ : ((single₀).obj X).IsGE 0 := inferInstance
    exact DerivedCategory.isZero_of_isGE _ 0 i hi
  · intro i hi
    let _ : ((single₀).obj X).IsLE 0 := inferInstance
    exact DerivedCategory.isZero_of_isLE _ 0 i hi

/-- Helper for Lemma 13.28.5: the canonical degree-zero embedding `A ⥤ Dᵇ(A)`. -/
abbrev singleFunctorToBoundedDerived :
    A ⥤ Dᵇ(A) :=
  ObjectProperty.lift
    t.bounded
    single₀
    (singleFunctor_obj_mem_boundedDerivedCategory (A := A))

/-- Helper for Lemma 13.28.5: the cohomology of a degree-zero complex vanishes away from degree
`0`. -/
theorem single_zero_complex_homology_isZero_of_ne
    (X : A) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((H i).obj ((single₀).obj X)) := by
  -- Proof comment: a degree-zero complex is bounded both below and above by `0`, so all other
  -- cohomology groups vanish by the standard `t`-structure bounds.
  by_cases hlt : i < 0
  · let _ : ((single₀).obj X).IsGE 0 := inferInstance
    exact DerivedCategory.isZero_of_isGE _ 0 i hlt
  · have hgt : 0 < i := by
      omega
    let _ : ((single₀).obj X).IsLE 0 := inferInstance
    exact DerivedCategory.isZero_of_isLE _ 0 i hgt

end LocalEulerInfrastructure

namespace Functor

section LocalEulerK0Map

universe u₁ u₂ v₁ v₂

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (F : D ⥤ B) [F.IsHomological] [F.ShiftSequence ℤ]

/-- Helper for Lemma 13.28.5: the alternating Euler class attached to a shifted homological
functor. -/
def eulerClass (X : D) : AbelianK0 B :=
  ∑ᶠ i : ℤ, i.negOnePow • K₀[(F.shift i).obj X]

/-- Helper for Lemma 13.28.5: the zero object has trivial class in the abelian Grothendieck
group of the target category. -/
private theorem abelian_k0_zero_eq :
    K₀[(0 : B)] = 0 := by
  -- Proof comment: evaluate the Grothendieck relation for the zero short exact sequence and
  -- cancel one copy of the zero class.
  let S : ShortComplex B := ShortComplex.mk (0 : (0 : B) ⟶ 0) (0 : (0 : B) ⟶ 0) (by simp)
  have hExact : S.Exact := by
    exact (S.exact_iff_epi (by simp [S])).2 inferInstance
  have hShort : S.ShortExact := ShortComplex.ShortExact.mk' hExact inferInstance inferInstance
  have hK0 : K₀[(0 : B)] = K₀[(0 : B)] + K₀[(0 : B)] := by
    simpa [S] using (AbelianK0.of_shortExact S hShort)
  have hSub := congrArg (fun z : AbelianK0 B ↦ z - K₀[(0 : B)]) hK0
  have hZero : (0 : AbelianK0 B) = K₀[(0 : B)] := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hSub
  simpa using hZero.symm

/-- Helper for Lemma 13.28.5: isomorphic objects define the same class in the abelian
Grothendieck group of the target category. -/
private theorem abelian_k0_eq_of_iso {X Y : B} (e : X ≅ Y) :
    K₀[X] = K₀[Y] := by
  -- Proof comment: delegate to the canonical Chapter 12 `K₀` invariance under isomorphism.
  exact _root_.CategoryTheory.ObjectProperty.k0_eq_of_iso (A := B) e

/-- Helper for Lemma 13.28.5: the difference of target and source classes equals the difference
of cokernel and kernel classes. -/
private theorem k0_sub_eq_cokernel_sub_kernel {X Y : B} (f : X ⟶ Y) :
    K₀[Y] - K₀[X] = K₀[Limits.cokernel f] - K₀[Limits.kernel f] := by
  -- Proof comment: this is the canonical Chapter 12 kernel-cokernel identity in `K₀(B)`.
  exact _root_.CategoryTheory.ObjectProperty.k0_sub_eq_cokernel_sub_kernel (A := B) f

/-- Helper for Lemma 13.28.5: composing with the lift into `kernel f` preserves the kernel class
in `K₀(B)`. -/
private theorem k0_kernel_of_kernel_lift
    {X Y Z : B} (f : Y ⟶ Z) (g : X ⟶ Y) (h : g ≫ f = 0) :
    K₀[Limits.kernel (Limits.kernel.lift f g h)] = K₀[Limits.kernel g] := by
  -- Proof comment: use the Chapter 12 comparison between the two kernels attached to
  -- `kernel.lift`.
  exact _root_.CategoryTheory.ObjectProperty.k0_kernel_of_kernel_lift (A := B) f g h

/-- Helper for Lemma 13.28.5: if the source of a morphism in the abelian target is zero, then
the class of its kernel vanishes in `K₀(B)`. -/
private lemma k0_kernel_eq_zero_of_isZero_source {X Y : B} (f : X ⟶ Y) (hX : IsZero X) :
    K₀[Limits.kernel f] = 0 := by
  -- Proof comment: a morphism out of a zero object is mono, so its kernel is zero.
  let e : X ≅ 0 := hX.isoZero
  let _ : Mono f := Limits.mono_of_source_iso_zero f e
  calc
    K₀[Limits.kernel f] = K₀[(0 : B)] := by
      exact abelian_k0_eq_of_iso (kernel.ofMono f)
    _ = 0 := abelian_k0_zero_eq (B := B)

/-- Helper for Lemma 13.28.5: exactness at two consecutive spots expresses the middle class as
the sum of the adjacent kernel classes. -/
private lemma k0_eq_kernel_add_kernel_of_exact
    {X₀ X₁ X₂ X₃ : B} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃)
    (hfg : f ≫ g = 0) (hgh : g ≫ h = 0)
    (_hex₁ : (ShortComplex.mk f g hfg).Exact) (hex₂ : (ShortComplex.mk g h hgh).Exact) :
    K₀[X₁] = K₀[Limits.kernel g] + K₀[Limits.kernel h] := by
  -- Proof comment: identify `X₁ ⟶ kernel h` with a kernel-cokernel presentation and then
  -- replace its kernel by `kernel g`.
  let u : X₁ ⟶ Limits.kernel h := Limits.kernel.lift h g hgh
  haveI : Epi u := (ShortComplex.Exact.epi_kernelLift (S := ShortComplex.mk g h hgh) hex₂)
  have hcokernel :
      K₀[Limits.cokernel u] = 0 := by
    calc
      K₀[Limits.cokernel u] = K₀[(0 : B)] := by
        exact abelian_k0_eq_of_iso (Limits.cokernel.ofEpi u)
      _ = 0 := abelian_k0_zero_eq (B := B)
  have hkernel :
      K₀[Limits.kernel u] = K₀[Limits.kernel g] := by
    simpa [u] using
      (k0_kernel_of_kernel_lift (f := h) (g := g) hgh)
  have hsub :
      K₀[Limits.kernel h] - K₀[X₁] = -K₀[Limits.kernel g] := by
    rw [k0_sub_eq_cokernel_sub_kernel u, hcokernel, hkernel]
    abel
  have hsum := congrArg (fun z : AbelianK0 B ↦ z + K₀[X₁] + K₀[Limits.kernel g]) hsub
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum.symm

omit [HasZeroObject D] [Preadditive D] [∀ n : ℤ, Functor.Additive (shiftFunctor D n)]
  [Pretriangulated D] [F.IsHomological] in
/-- Helper for Lemma 13.28.5: once the shifted values of `F` vanish outside a finite interval,
the Euler `finsum` reduces to the corresponding finite sum. -/
private lemma eulerClass_eq_sum_of_vanishingOutside (X : D) {a b : ℤ}
    (hX : ∀ n : ℤ, n ∉ Set.Icc a b → IsZero ((F.shift n).obj X)) :
    F.eulerClass X =
      Finset.sum (Finset.Icc a b) (fun i ↦ i.negOnePow • K₀[(F.shift i).obj X]) := by
  -- Proof comment: outside the interval every Euler summand is zero, so the `finsum`
  -- collapses to the finite interval sum.
  let f : ℤ → AbelianK0 B := fun i ↦ i.negOnePow • K₀[(F.shift i).obj X]
  change ∑ᶠ i : ℤ, f i = Finset.sum (Finset.Icc a b) f
  have hsupp : Function.support f ⊆ ↑(Finset.Icc a b) := by
    intro i hi
    by_contra hnot
    have hzeroObj : IsZero ((F.shift i).obj X) := hX i <| by simpa using hnot
    have hk0 :
        K₀[(F.shift i).obj X] = 0 := by
      calc
        K₀[(F.shift i).obj X] = K₀[(0 : B)] := by
          exact abelian_k0_eq_of_iso hzeroObj.isoZero
        _ = 0 := abelian_k0_zero_eq (B := B)
    have hfi : f i = 0 := by
      rw [show f i = i.negOnePow • K₀[(F.shift i).obj X] by rfl, hk0, smul_zero]
    exact hi hfi
  rw [finsum_eq_sum_of_support_subset (s := Finset.Icc a b) f hsupp]

/-- Helper for Lemma 13.28.5: the distinguished-triangle relations are killed by the local
Euler-class map. -/
private theorem relations_le_ker_eulerClass
    (hF : ∀ X : D, F.shiftVanishingBounded X) :
    TriangulatedK0.relations D ≤
      (FreeAbelianGroup.lift fun X ↦ F.eulerClass X).ker := by
  -- Proof comment: rewrite the three Euler classes over one common finite interval, express each
  -- degreewise relation through adjacent kernels in the long exact sequence, and telescope the
  -- boundary terms.
  rw [TriangulatedK0.relations, AddSubgroup.closure_le]
  rintro _ ⟨T, rfl⟩
  rcases T with ⟨T, hT⟩
  change
    (FreeAbelianGroup.lift fun X ↦ F.eulerClass X)
        (FreeAbelianGroup.of T.obj₂ - FreeAbelianGroup.of T.obj₁ - FreeAbelianGroup.of T.obj₃) = 0
  rw [(FreeAbelianGroup.lift fun X ↦ F.eulerClass X).map_sub]
  rw [(FreeAbelianGroup.lift fun X ↦ F.eulerClass X).map_sub]
  simp only [FreeAbelianGroup.lift_apply_of]
  rcases (Functor.mem_shiftVanishingBounded_iff F T.obj₁).1 (hF T.obj₁) with ⟨N₁, h₁⟩
  rcases (Functor.mem_shiftVanishingBounded_iff F T.obj₂).1 (hF T.obj₂) with ⟨N₂, h₂⟩
  rcases (Functor.mem_shiftVanishingBounded_iff F T.obj₃).1 (hF T.obj₃) with ⟨N₃, h₃⟩
  let N : ℕ := max N₁ (max N₂ N₃)
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) ((N : ℤ) - 1)
  let α := fun i : ℤ ↦ (F.shift i).map T.mor₁
  let β := fun i : ℤ ↦ (F.shift i).map T.mor₂
  let δ := fun i : ℤ ↦ F.homologySequenceδ T i (i + 1) rfl
  let boundary : ℤ → AbelianK0 B := fun i ↦ -i.negOnePow • K₀[Limits.kernel (α i)]
  have hN₁ : N₁ ≤ N := by
    dsimp [N]
    exact le_max_left _ _
  have hN₂ : N₂ ≤ N := by
    dsimp [N]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hN₃ : N₃ ≤ N := by
    dsimp [N]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hnatAbs_of_not_mem :
      ∀ {n : ℤ}, n ∉ Set.Icc (-(N : ℤ)) ((N : ℤ) - 1) → N ≤ Int.natAbs n := by
    intro n hn
    have hnatAbs' : (N : ℤ) ≤ (Int.natAbs n : ℤ) := by
      have hn' : ¬ (-(N : ℤ) ≤ n ∧ n ≤ (N : ℤ) - 1) := by
        simpa [Set.mem_Icc] using hn
      by_cases hnonneg : 0 ≤ n
      · rw [Int.ofNat_natAbs_of_nonneg hnonneg]
        omega
      · have hnonpos : n ≤ 0 := by
          omega
        rw [Int.ofNat_natAbs_of_nonpos hnonpos]
        omega
    exact_mod_cast hnatAbs'
  have hvanish₁ :
      ∀ n : ℤ, n ∉ Set.Icc (-(N : ℤ)) ((N : ℤ) - 1) → IsZero ((F.shift n).obj T.obj₁) := by
    intro n hn
    exact (h₁ n (le_trans hN₁ (hnatAbs_of_not_mem hn))).of_iso ((F.isoShift n).app T.obj₁).symm
  have hvanish₂ :
      ∀ n : ℤ, n ∉ Set.Icc (-(N : ℤ)) ((N : ℤ) - 1) → IsZero ((F.shift n).obj T.obj₂) := by
    intro n hn
    exact (h₂ n (le_trans hN₂ (hnatAbs_of_not_mem hn))).of_iso ((F.isoShift n).app T.obj₂).symm
  have hvanish₃ :
      ∀ n : ℤ, n ∉ Set.Icc (-(N : ℤ)) ((N : ℤ) - 1) → IsZero ((F.shift n).obj T.obj₃) := by
    intro n hn
    exact (h₃ n (le_trans hN₃ (hnatAbs_of_not_mem hn))).of_iso ((F.isoShift n).app T.obj₃).symm
  have hleft_zero :
      IsZero ((F.shift (-(N : ℤ))).obj T.obj₁) := by
    exact (h₁ (-(N : ℤ)) (le_trans hN₁ (by simpa))).of_iso
      ((F.isoShift (-(N : ℤ))).app T.obj₁).symm
  have hright_zero :
      IsZero ((F.shift (N : ℤ)).obj T.obj₁) := by
    exact (h₁ (N : ℤ) (le_trans hN₁ (by simpa))).of_iso ((F.isoShift (N : ℤ)).app T.obj₁).symm
  have hA :
      ∀ i : ℤ,
        K₀[(F.shift i).obj T.obj₁] = K₀[Limits.kernel (α i)] + K₀[Limits.kernel (β i)] := by
    intro i
    have hi_succ : i - 1 + 1 = i := by
      omega
    dsimp [α, β, δ]
    let hex_prev := F.homologySequenceComposableArrows₅_exact T hT (i - 1) i hi_succ
    let hex_curr := F.homologySequenceComposableArrows₅_exact T hT i (i + 1) rfl
    exact
      k0_eq_kernel_add_kernel_of_exact (B := B)
        (F.homologySequenceδ T (i - 1) i hi_succ)
        ((F.shift i).map T.mor₁)
        ((F.shift i).map T.mor₂)
        (by simpa using hex_prev.toIsComplex.zero 2)
        (by simpa using hex_curr.toIsComplex.zero 0)
        (by simpa using hex_prev.exact 2)
        (by simpa using hex_curr.exact 0)
  have hB :
      ∀ i : ℤ,
        K₀[(F.shift i).obj T.obj₂] = K₀[Limits.kernel (β i)] + K₀[Limits.kernel (δ i)] := by
    intro i
    dsimp [β, δ]
    let hex := F.homologySequenceComposableArrows₅_exact T hT i (i + 1) rfl
    exact
      k0_eq_kernel_add_kernel_of_exact (B := B)
        ((F.shift i).map T.mor₁)
        ((F.shift i).map T.mor₂)
        (F.homologySequenceδ T i (i + 1) rfl)
        (by simpa using hex.toIsComplex.zero 0)
        (by simpa using hex.toIsComplex.zero 1)
        (by simpa using hex.exact 0)
        (by simpa using hex.exact 1)
  have hC :
      ∀ i : ℤ,
        K₀[(F.shift i).obj T.obj₃] =
          K₀[Limits.kernel (δ i)] + K₀[Limits.kernel (α (i + 1))] := by
    intro i
    dsimp [α, δ]
    let hex := F.homologySequenceComposableArrows₅_exact T hT i (i + 1) rfl
    exact
      k0_eq_kernel_add_kernel_of_exact (B := B)
        ((F.shift i).map T.mor₂)
        (F.homologySequenceδ T i (i + 1) rfl)
        ((F.shift (i + 1)).map T.mor₁)
        (by simpa using hex.toIsComplex.zero 1)
        (by simpa using hex.toIsComplex.zero 2)
        (by simpa using hex.exact 1)
        (by simpa using hex.exact 2)
  have hterm :
      ∀ i : ℤ,
        i.negOnePow • K₀[(F.shift i).obj T.obj₂]
          - i.negOnePow • K₀[(F.shift i).obj T.obj₁]
          - i.negOnePow • K₀[(F.shift i).obj T.obj₃] =
            boundary i - boundary (i + 1) := by
    intro i
    have hsign : (i + 1).negOnePow = -i.negOnePow := by
      rw [Int.negOnePow_add, Int.negOnePow_one]
      simp
    change
      i.negOnePow • K₀[(F.shift i).obj T.obj₂]
          - i.negOnePow • K₀[(F.shift i).obj T.obj₁]
          - i.negOnePow • K₀[(F.shift i).obj T.obj₃] =
        -i.negOnePow • K₀[Limits.kernel (α i)] -
          -(i + 1).negOnePow • K₀[Limits.kernel (α (i + 1))]
    rw [hB i, hA i, hC i, hsign]
    simp [smul_add, sub_eq_add_neg, add_assoc, add_comm]
  have hs₁ :
      F.eulerClass T.obj₁ =
        Finset.sum s (fun i ↦ i.negOnePow • K₀[(F.shift i).obj T.obj₁]) := by
    simpa [s] using eulerClass_eq_sum_of_vanishingOutside (F := F) T.obj₁ hvanish₁
  have hs₂ :
      F.eulerClass T.obj₂ =
        Finset.sum s (fun i ↦ i.negOnePow • K₀[(F.shift i).obj T.obj₂]) := by
    simpa [s] using eulerClass_eq_sum_of_vanishingOutside (F := F) T.obj₂ hvanish₂
  have hs₃ :
      F.eulerClass T.obj₃ =
        Finset.sum s (fun i ↦ i.negOnePow • K₀[(F.shift i).obj T.obj₃]) := by
    simpa [s] using eulerClass_eq_sum_of_vanishingOutside (F := F) T.obj₃ hvanish₃
  have hsums :
      Finset.sum s (fun i ↦ i.negOnePow • K₀[(F.shift i).obj T.obj₂]) -
          Finset.sum s (fun i ↦ i.negOnePow • K₀[(F.shift i).obj T.obj₁]) -
          Finset.sum s (fun i ↦ i.negOnePow • K₀[(F.shift i).obj T.obj₃]) =
        Finset.sum s (fun i ↦
          i.negOnePow • K₀[(F.shift i).obj T.obj₂]
            - i.negOnePow • K₀[(F.shift i).obj T.obj₁]
            - i.negOnePow • K₀[(F.shift i).obj T.obj₃]) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  have hsIco :
      s = Finset.Ico (-(N : ℤ)) (N : ℤ) := by
    dsimp [s]
    symm
    simpa using
      (Finset.Ico_succ_right_eq_Icc_of_not_isMax
        (a := -(N : ℤ)) (b := (N : ℤ) - 1) (not_isMax _))
  have htel :
      Finset.sum s (fun i ↦ boundary i - boundary (i + 1)) =
        boundary (-(N : ℤ)) - boundary (N : ℤ) := by
    rw [hsIco]
    simpa using (Finset.sum_Ico_int_sub N boundary)
  have hboundary_left : boundary (-(N : ℤ)) = 0 := by
    change -(-(N : ℤ)).negOnePow • K₀[Limits.kernel (α (-(N : ℤ)))] = 0
    simp [k0_kernel_eq_zero_of_isZero_source (B := B) (α (-(N : ℤ))) hleft_zero]
  have hboundary_right : boundary (N : ℤ) = 0 := by
    change -(N : ℤ).negOnePow • K₀[Limits.kernel (α (N : ℤ))] = 0
    simp [k0_kernel_eq_zero_of_isZero_source (B := B) (α (N : ℤ)) hright_zero]
  calc
    F.eulerClass T.obj₂ - F.eulerClass T.obj₁ - F.eulerClass T.obj₃
        = Finset.sum s (fun i ↦ i.negOnePow • K₀[(F.shift i).obj T.obj₂]) -
            Finset.sum s (fun i ↦ i.negOnePow • K₀[(F.shift i).obj T.obj₁]) -
            Finset.sum s (fun i ↦ i.negOnePow • K₀[(F.shift i).obj T.obj₃]) := by
              rw [hs₂, hs₁, hs₃]
    _ = Finset.sum s (fun i ↦
          i.negOnePow • K₀[(F.shift i).obj T.obj₂]
            - i.negOnePow • K₀[(F.shift i).obj T.obj₁]
            - i.negOnePow • K₀[(F.shift i).obj T.obj₃]) := hsums
    _ = Finset.sum s (fun i ↦ boundary i - boundary (i + 1)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact hterm i
    _ = boundary (-(N : ℤ)) - boundary (N : ℤ) := htel
    _ = 0 := by
          simp [hboundary_left, hboundary_right]

/-- Helper for Lemma 13.28.5: the induced Euler-characteristic map on the triangulated `K₀`. -/
def eulerK0Map (hF : ∀ X : D, F.shiftVanishingBounded X) :
    TriangulatedK0 D →+ AbelianK0 B :=
  TriangulatedK0.lift
    (fun X ↦ F.eulerClass X)
    (relations_le_ker_eulerClass F hF)

/-- Helper for Lemma 13.28.5: evaluation of the Euler-characteristic map on a generator. -/
@[simp] theorem eulerK0Map_apply_of
    (hF : ∀ X : D, F.shiftVanishingBounded X) (X : D) :
    F.eulerK0Map hF (TriangulatedK0.of X) = F.eulerClass X := by
  simpa using
    TriangulatedK0.lift_of
      (fun Y ↦ F.eulerClass Y)
      (relations_le_ker_eulerClass F hF)
      X

end LocalEulerK0Map

end Functor

section WeakSerreSingleBridge

variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]

/- Domain-style sampling for Lemma 13.28.5:
- primary domain: the bounded derived subcategory cut out by a weak Serre object property and the
  induced Grothendieck-group comparison map;
- sampled owner declarations:
  `derivedCategoryCohomologyInProperty`,
  `derivedCategoryBoundedCohomologyInProperty`,
  `Dᵇ_{P}`,
  `ObjectProperty.IsTriangulated`,
  `Functor.eulerK0Map`,
  `Functor.shiftVanishingBounded`;
- best owner abstraction: the Chapter 13 owner object property on `DerivedCategory A` together
  with its canonical full subcategory `Dᵇ_{P}`; the Euler map on `K₀(Dᵇ_{P})` should be routed
  through the owner-functor construction
  `(derivedBoundedWithCohomologyInZeroHomologyFunctor P).eulerK0Map`;
- primitive-vs-derived split:
  primitive data: the object property `P`, its zero-object and iso-stability owners used by the
    degree-zero bridge, and the chapter owner
    `derivedCategoryBoundedCohomologyInProperty P`, whose full subcategory owner is the chapter
    notation `Dᵇ_{P}`;
  derived API: the degree-zero embedding obtained by restricting the Chapter 13 owner
    `singleFunctorToBoundedDerived A` along `P.ι`, the induced maps on `K₀`, and the Euler
    characteristic inverse;
- source/core/bridge triage:
  `source-facing`: the `K₀` comparison between `P` and `Dᵇ_{P}`;
  `core/canonical`: the owner declarations from `Lemma_13_17_1`;
  `bridge/view`: the restricted degree-zero functor
    `P.FullSubcategory ⥤ Dᵇ(A) ⥤ Dᵇ_{P}` and the resulting additive maps.

This file therefore reuses the Chapter 13 owner API rather than redeclaring a second bounded
cohomology-in-`P` object property. -/

/-- The degree-zero complex attached to an object of `P.FullSubcategory` lies in
`Dᵇ_{P}`. -/
theorem weakSerreSingle_obj_mem_derivedCategoryBoundedCohomologyInProperty
    (X : P.FullSubcategory) :
    derivedCategoryBoundedCohomologyInProperty P
      ((P.ι ⋙ singleFunctorToBoundedDerived (A := A)).obj X) := by
  intro i
  by_cases hi : i = 0
  · subst hi
    simpa [derivedCategoryBoundedCohomologyInProperty, derivedCategoryCohomologyInProperty,
      Functor.comp_obj] using
        P.prop_of_iso ((singleFunctorCompHomologyFunctorIso A 0).app X.obj).symm X.property
  · have hzero :
        IsZero
          ((H i).obj
            ((ObjectProperty.ι t.bounded).obj
              ((P.ι ⋙ singleFunctorToBoundedDerived (A := A)).obj X))) := by
      by_cases hlt : i < 0
      · change IsZero ((H i).obj ((singleFunctor A 0).obj X.obj))
        letI : ((singleFunctor A 0).obj X.obj).IsGE 0 := inferInstance
        exact DerivedCategory.isZero_of_isGE _ 0 i hlt
      · have hgt : 0 < i := by omega
        change IsZero ((H i).obj ((singleFunctor A 0).obj X.obj))
        letI : ((singleFunctor A 0).obj X.obj).IsLE 0 := inferInstance
        exact DerivedCategory.isZero_of_isLE _ 0 i hgt
    simpa [derivedCategoryBoundedCohomologyInProperty, derivedCategoryCohomologyInProperty,
      Functor.comp_obj] using P.prop_of_isZero hzero

/-- The canonical functor `P.FullSubcategory ⥤ Dᵇ_{P}` sending `X` to the degree-zero object
`X[0]` in the ambient derived category. -/
abbrev weakSerreSingleFunctorToDerivedBounded :
    P.FullSubcategory ⥤ Dᵇ_{P} :=
  ObjectProperty.lift
    (derivedCategoryBoundedCohomologyInProperty P)
    (P.ι ⋙ singleFunctorToBoundedDerived (A := A))
    (weakSerreSingle_obj_mem_derivedCategoryBoundedCohomologyInProperty P)

end WeakSerreSingleBridge

section WeakSerreBoundedDerivedBridge

variable (P : ObjectProperty A)

/-- The `i`-th cohomology functor on `Dᵇ_{P}` lifted to the weak Serre full subcategory
`P.FullSubcategory`. -/
abbrev derivedBoundedWithCohomologyInHomologyFunctor (i : ℤ) :
    Dᵇ_{P} ⥤ P.FullSubcategory :=
  P.lift
    ((derivedCategoryBoundedCohomologyInProperty P).ι ⋙
      ObjectProperty.ι (t.bounded : ObjectProperty (D(A))) ⋙ H i)
    (fun X ↦ X.property i)

/-- The degree-zero cohomology functor on `Dᵇ_{P}` lifted to `P.FullSubcategory`. -/
abbrev derivedBoundedWithCohomologyInZeroHomologyFunctor :
    Dᵇ_{P} ⥤ P.FullSubcategory :=
  derivedBoundedWithCohomologyInHomologyFunctor P 0

end WeakSerreBoundedDerivedBridge

section WeakSerreBoundedDerivedK0

variable (P : ObjectProperty A) [P.IsWeakSerreClass]

noncomputable local instance derivedBoundedWithCohomologyInZeroHomologyFunctor_shiftSequence :
    (derivedBoundedWithCohomologyInZeroHomologyFunctor P).ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ _

/-- Helper for Lemma 13.28.5: exactness of a mapped short complex is unchanged under a natural
isomorphism of functors. -/
private theorem shortComplex_exact_iff_of_functor_iso
    {C B : Type*} [Category C] [Category B]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms B]
    {F G : C ⥤ B} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (e : F ≅ G) (S : ShortComplex C) :
    (S.map F).Exact ↔ (S.map G).Exact := by
  -- Proof comment: compare the mapped short complexes degreewise using the components of `e`,
  -- and then transport exactness across the resulting isomorphism.
  let i : S.map F ≅ S.map G :=
    ShortComplex.isoMk (e.app S.X₁) (e.app S.X₂) (e.app S.X₃)
      (by simp)
      (by simp)
  exact ShortComplex.exact_iff_of_iso i

/-- Helper for Lemma 13.28.5: mapping a short exact sequence in `P.FullSubcategory` along the
inclusion `P.ι` keeps it short exact in `A`. -/
private theorem weakSerreSingleFunctor_mapped_shortExact
    {S : ShortComplex P.FullSubcategory} (hS : S.ShortExact) :
    (S.map P.ι).ShortExact := by
  -- The weak Serre inclusion is exact, so the ambient sequence remains short exact after
  -- forgetting from `P.FullSubcategory` to `A`.
  letI : PreservesFiniteLimits P.ι :=
    ObjectProperty.weakSerreSubcategory_inclusion_preservesFiniteLimits P
  letI : PreservesFiniteColimits P.ι :=
    ObjectProperty.weakSerreSubcategory_inclusion_preservesFiniteColimits P
  simpa using hS.map_of_exact P.ι

/-- Helper for Lemma 13.28.5: after forgetting from `Dᵇ_{P}` to `Dᵇ(A)`, the weak-Serre
degree-zero embedding is the usual degree-zero bounded-derived embedding. -/
private noncomputable def weakSerreSingleFunctorToBoundedDerivedCompIso :
    weakSerreSingleFunctorToDerivedBounded P ⋙
      (derivedCategoryBoundedCohomologyInProperty P).ι ≅
    P.ι ⋙ singleFunctorToBoundedDerived (A := A) :=
  (derivedCategoryBoundedCohomologyInProperty P).liftCompιIso
    (P.ι ⋙ singleFunctorToBoundedDerived (A := A))
    (weakSerreSingle_obj_mem_derivedCategoryBoundedCohomologyInProperty (A := A) P)

/-- Helper for Lemma 13.28.5: the ambient bounded-derived triangle attached to the mapped short
exact sequence `S.map P.ι`. -/
private def weakSerreSingleFunctor_mappedBoundedDerivedTriangle
    {S : ShortComplex P.FullSubcategory} (hS : S.ShortExact) :
    Triangle (Dᵇ(A)) :=
  Triangle.mk
    ((singleFunctorToBoundedDerived (A := A)).map (S.map P.ι).f)
    ((singleFunctorToBoundedDerived (A := A)).map (S.map P.ι).g)
    ((ObjectProperty.ι t.bounded).preimage
      ((weakSerreSingleFunctor_mapped_shortExact (P := P) hS).singleδ ≫
        ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).inv.app
          ((singleFunctorToBoundedDerived (A := A)).obj S.X₁.obj)))

/-- Helper for Lemma 13.28.5: the mapped short exact sequence gives the canonical distinguished
triangle in `Dᵇ(A)`. -/
private theorem weakSerreSingleFunctor_mappedBoundedDerivedTriangle_distinguished
    {S : ShortComplex P.FullSubcategory} (hS : S.ShortExact) :
    weakSerreSingleFunctor_mappedBoundedDerivedTriangle (A := A) (P := P) hS ∈
      distTriang (Dᵇ(A)) := by
  -- Proof comment: this is exactly the bounded-derived short-exact-sequence triangle of
  -- `S.map P.ι`, so the proof is the same as in `Lemma_13_28_2`.
  rw [← (ObjectProperty.ι t.bounded).map_distinguished_iff]
  change
    Triangle.mk
        ((ObjectProperty.ι t.bounded).map
          ((singleFunctorToBoundedDerived (A := A)).map (S.map P.ι).f))
        ((ObjectProperty.ι t.bounded).map
          ((singleFunctorToBoundedDerived (A := A)).map (S.map P.ι).g))
        ((ObjectProperty.ι t.bounded).map
            ((ObjectProperty.ι t.bounded).preimage
              ((weakSerreSingleFunctor_mapped_shortExact (P := P) hS).singleδ ≫
                ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).inv.app
                  ((singleFunctorToBoundedDerived (A := A)).obj S.X₁.obj))) ≫
          ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).hom.app
            ((singleFunctorToBoundedDerived (A := A)).obj S.X₁.obj)) ∈
      distTriang (D(A))
  rw [(ObjectProperty.ι t.bounded).map_preimage]
  refine isomorphic_distinguished _
    (weakSerreSingleFunctor_mapped_shortExact (P := P) hS).singleTriangle_distinguished _ ?_
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simp [singleFunctorToBoundedDerived]
  · simp [singleFunctorToBoundedDerived]
  · simpa [Category.assoc] using
      congrArg (fun k ↦ (weakSerreSingleFunctor_mapped_shortExact (P := P) hS).singleδ ≫ k)
        (((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).inv_hom_id_app
          ((singleFunctorToBoundedDerived (A := A)).obj S.X₁.obj))

/-- Helper for Lemma 13.28.5: the degree-zero images of a short exact sequence in
`P.FullSubcategory` form the canonical triangle in `Dᵇ_{P}`. -/
private def weakSerreSingleFunctorToDerivedBoundedTriangle {S : ShortComplex P.FullSubcategory}
    (hS : S.ShortExact) :
    Triangle (Dᵇ_{P}) :=
  Triangle.mk
    ((weakSerreSingleFunctorToDerivedBounded P).map S.f)
    ((weakSerreSingleFunctorToDerivedBounded P).map S.g)
    (((derivedCategoryBoundedCohomologyInProperty P).ι).preimage
      (((weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).hom.app S.X₃) ≫
        (weakSerreSingleFunctor_mappedBoundedDerivedTriangle (A := A) (P := P) hS).mor₃ ≫
          (((weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).inv.app S.X₁)⟦
            (1 : ℤ)⟧') ≫
            (((derivedCategoryBoundedCohomologyInProperty P).ι).commShiftIso (1 : ℤ)).inv.app
              ((weakSerreSingleFunctorToDerivedBounded P).obj S.X₁)))

/-- Helper for Lemma 13.28.5: the canonical triangle attached to a short exact sequence in the
weak Serre subcategory is distinguished in `Dᵇ_{P}`. -/
private theorem weakSerreSingleFunctorToDerivedBoundedTriangle_distinguished
    {S : ShortComplex P.FullSubcategory} (hS : S.ShortExact) :
    weakSerreSingleFunctorToDerivedBoundedTriangle P hS ∈ distTriang (Dᵇ_{P}) := by
  -- Proof comment: forget the local triangle to `Dᵇ(A)`, compare it with the ambient transported
  -- short-exact-sequence triangle, and then use invariance of distinguished triangles under
  -- isomorphism.
  rw [← ((derivedCategoryBoundedCohomologyInProperty P).ι).map_distinguished_iff]
  change
    Triangle.mk
        (((derivedCategoryBoundedCohomologyInProperty P).ι).map
          ((weakSerreSingleFunctorToDerivedBounded P).map S.f))
        (((derivedCategoryBoundedCohomologyInProperty P).ι).map
          ((weakSerreSingleFunctorToDerivedBounded P).map S.g))
        (((derivedCategoryBoundedCohomologyInProperty P).ι).map
            (((derivedCategoryBoundedCohomologyInProperty P).ι).preimage
              (((weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).hom.app S.X₃) ≫
                (weakSerreSingleFunctor_mappedBoundedDerivedTriangle (A := A) (P := P) hS).mor₃ ≫
                  (((weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).inv.app
                    S.X₁)⟦(1 : ℤ)⟧') ≫
                    (((derivedCategoryBoundedCohomologyInProperty P).ι).commShiftIso (1 : ℤ)).inv.app
                      ((weakSerreSingleFunctorToDerivedBounded P).obj S.X₁))) ≫
          (((derivedCategoryBoundedCohomologyInProperty P).ι).commShiftIso (1 : ℤ)).hom.app
            ((weakSerreSingleFunctorToDerivedBounded P).obj S.X₁)) ∈
      distTriang (Dᵇ(A))
  rw [((derivedCategoryBoundedCohomologyInProperty P).ι).map_preimage]
  refine isomorphic_distinguished _
    (weakSerreSingleFunctor_mappedBoundedDerivedTriangle_distinguished (A := A) (P := P) hS) _ ?_
  refine Triangle.isoMk _ _
    ((weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).app S.X₁)
    ((weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).app S.X₂)
    ((weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).app S.X₃)
    ?_ ?_ ?_
  · simpa using
      (weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).hom.naturality S.f
  · simpa using
      (weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).hom.naturality S.g
  · have hshift :
        (shiftFunctor (Dᵇ(A)) (1 : ℤ)).map
            ((weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).inv.app S.X₁) ≫
              (shiftFunctor (Dᵇ(A)) (1 : ℤ)).map
                ((weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).hom.app S.X₁) =
          𝟙 (((P.ι ⋙ singleFunctorToBoundedDerived (A := A)).obj S.X₁)⟦(1 : ℤ)⟧) := by
      simpa using
        congrArg
          (fun k ↦ (shiftFunctor (Dᵇ(A)) (1 : ℤ)).map k)
          ((weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).inv_hom_id_app S.X₁)
    have hthird :
        (weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).hom.app S.X₃ ≫
            (weakSerreSingleFunctor_mappedBoundedDerivedTriangle (A := A) (P := P) hS).mor₃ ≫
              (shiftFunctor (Dᵇ(A)) (1 : ℤ)).map
                ((weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).inv.app S.X₁) ≫
                (Functor.commShiftIso ((derivedCategoryBoundedCohomologyInProperty P).ι)
                  (1 : ℤ)).inv.app ((weakSerreSingleFunctorToDerivedBounded P).obj S.X₁) ≫
                  (Functor.commShiftIso ((derivedCategoryBoundedCohomologyInProperty P).ι)
                    (1 : ℤ)).hom.app ((weakSerreSingleFunctorToDerivedBounded P).obj S.X₁) ≫
                    (shiftFunctor (Dᵇ(A)) (1 : ℤ)).map
                      ((weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).hom.app
                        S.X₁)
            =
          (weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).hom.app S.X₃ ≫
            (weakSerreSingleFunctor_mappedBoundedDerivedTriangle (A := A) (P := P) hS).mor₃ := by
      calc
        (weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).hom.app S.X₃ ≫
            (weakSerreSingleFunctor_mappedBoundedDerivedTriangle (A := A) (P := P) hS).mor₃ ≫
              (shiftFunctor (Dᵇ(A)) (1 : ℤ)).map
                ((weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).inv.app S.X₁) ≫
                (Functor.commShiftIso ((derivedCategoryBoundedCohomologyInProperty P).ι)
                  (1 : ℤ)).inv.app ((weakSerreSingleFunctorToDerivedBounded P).obj S.X₁) ≫
                  (Functor.commShiftIso ((derivedCategoryBoundedCohomologyInProperty P).ι)
                    (1 : ℤ)).hom.app ((weakSerreSingleFunctorToDerivedBounded P).obj S.X₁) ≫
                    (shiftFunctor (Dᵇ(A)) (1 : ℤ)).map
                      ((weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).hom.app
                        S.X₁)
            =
          (weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).hom.app S.X₃ ≫
            (weakSerreSingleFunctor_mappedBoundedDerivedTriangle (A := A) (P := P) hS).mor₃ ≫
              (shiftFunctor (Dᵇ(A)) (1 : ℤ)).map
                ((weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).inv.app S.X₁) ≫
                  (shiftFunctor (Dᵇ(A)) (1 : ℤ)).map
                    ((weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).hom.app
                      S.X₁) := by
                simpa [Category.assoc] using
                  congrArg
                    (fun k ↦
                      (weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).hom.app
                          S.X₃ ≫
                        (weakSerreSingleFunctor_mappedBoundedDerivedTriangle (A := A) (P := P)
                          hS).mor₃ ≫
                          (shiftFunctor (Dᵇ(A)) (1 : ℤ)).map
                            ((weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).inv.app
                              S.X₁) ≫
                            k ≫
                              (shiftFunctor (Dᵇ(A)) (1 : ℤ)).map
                                ((weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).hom.app
                                  S.X₁))
                    ((Functor.commShiftIso ((derivedCategoryBoundedCohomologyInProperty P).ι)
                      (1 : ℤ)).inv_hom_id_app ((weakSerreSingleFunctorToDerivedBounded P).obj S.X₁))
        _ =
          (weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).hom.app S.X₃ ≫
            (weakSerreSingleFunctor_mappedBoundedDerivedTriangle (A := A) (P := P) hS).mor₃ := by
              calc
                (weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).hom.app S.X₃ ≫
                    (weakSerreSingleFunctor_mappedBoundedDerivedTriangle (A := A) (P := P)
                      hS).mor₃ ≫
                      (shiftFunctor (Dᵇ(A)) (1 : ℤ)).map
                        ((weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).inv.app
                          S.X₁) ≫
                        (shiftFunctor (Dᵇ(A)) (1 : ℤ)).map
                          ((weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).hom.app
                            S.X₁) =
                  (weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).hom.app S.X₃ ≫
                    (weakSerreSingleFunctor_mappedBoundedDerivedTriangle (A := A) (P := P)
                      hS).mor₃ ≫
                      𝟙 (((P.ι ⋙ singleFunctorToBoundedDerived (A := A)).obj S.X₁)⟦(1 : ℤ)⟧) := by
                        simpa [Category.assoc] using
                          congrArg
                            (fun k ↦
                              (weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).hom.app
                                  S.X₃ ≫
                                (weakSerreSingleFunctor_mappedBoundedDerivedTriangle (A := A)
                                  (P := P) hS).mor₃ ≫
                                  k)
                            hshift
                _ =
                  (weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).hom.app S.X₃ ≫
                    (weakSerreSingleFunctor_mappedBoundedDerivedTriangle (A := A) (P := P)
                      hS).mor₃ := by
                        simpa [weakSerreSingleFunctor_mappedBoundedDerivedTriangle] using
                          (Category.comp_id
                            ((weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).hom.app
                              S.X₃ ≫
                                (weakSerreSingleFunctor_mappedBoundedDerivedTriangle (A := A)
                                  (P := P) hS).mor₃))
    simpa [weakSerreSingleFunctorToDerivedBoundedTriangle, Category.assoc] using hthird

/-- Helper for Lemma 13.28.5: the degree-zero embedding sends `X` to its class in
`TriangulatedK0 (Dᵇ_{P})`. -/
private def weakSerreSingleDerivedClass (X : P.FullSubcategory) :
    TriangulatedK0 (Dᵇ_{P}) :=
  TriangulatedK0.of ((weakSerreSingleFunctorToDerivedBounded P).obj X)

/-- Helper for Lemma 13.28.5: a short exact sequence in `P.FullSubcategory` gives the expected
triangulated `K₀` relation after applying the degree-zero embedding into `Dᵇ_{P}`. -/
private theorem weakSerreSingleDerivedClass_of_shortExact
    {S : ShortComplex P.FullSubcategory} (hS : S.ShortExact) :
    weakSerreSingleDerivedClass (P := P) S.X₂ =
      weakSerreSingleDerivedClass (P := P) S.X₁ +
        weakSerreSingleDerivedClass (P := P) S.X₃ := by
  -- Proof comment: the degree-zero images of a short exact sequence form the canonical
  -- distinguished triangle in `Dᵇ_{P}`, so the triangulated `K₀` relation is immediate.
  simpa [weakSerreSingleDerivedClass] using
    TriangulatedK0.of_distinguished
      (weakSerreSingleFunctorToDerivedBoundedTriangle P hS)
      (weakSerreSingleFunctorToDerivedBoundedTriangle_distinguished (A := A) (P := P) hS)

-- Proof sketch: a short exact sequence in `P.FullSubcategory` gives the canonical distinguished
-- triangle of degree-zero objects in `D(A)`, and each vertex lies in `Dᵇ_{P}`. Hence the
-- corresponding Grothendieck relation vanishes in the triangulated `K₀`.
private theorem relations_le_ker_weakSerreToDerivedBoundedK0 :
    AbelianK0.relations P.FullSubcategory ≤
      (FreeAbelianGroup.lift (weakSerreSingleDerivedClass (P := P))).ker := by
  -- Proof comment: expand a short-exact generator of `AbelianK0.relations`, then rewrite it by
  -- the distinguished triangle relation proved in `weakSerreSingleDerivedClass_of_shortExact`.
  rw [AbelianK0.relations, AddSubgroup.closure_le]
  rintro _ ⟨S, rfl⟩
  rcases S with ⟨S, hS⟩
  change
    (FreeAbelianGroup.lift (weakSerreSingleDerivedClass (P := P)))
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  simp only [FreeAbelianGroup.lift_apply_of, map_sub]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    sub_eq_zero.mpr (weakSerreSingleDerivedClass_of_shortExact (A := A) (P := P) hS)

/-- The canonical map `K₀(P) → K₀(Dᵇ_{P})` induced by `X ↦ X[0]`. -/
def weakSerreToDerivedBoundedK0 :
    AbelianK0 P.FullSubcategory →+ TriangulatedK0 (Dᵇ_{P}) :=
  AbelianK0.lift
    (weakSerreSingleDerivedClass (P := P))
    (relations_le_ker_weakSerreToDerivedBoundedK0 P)

-- Proof sketch: `weakSerreToDerivedBoundedK0` is the owner lift `AbelianK0.lift` applied to the
-- object-level formula `X ↦ [X[0]]`, so evaluation on `AbelianK0.of X` is the canonical owner
-- lemma `AbelianK0.lift_of`.
/-- The canonical map on `K₀` sends `[X]` to the class of `X[0]` in `Dᵇ_{P}`. -/
@[simp] theorem weakSerreToDerivedBoundedK0_apply_of
    (X : P.FullSubcategory) :
    weakSerreToDerivedBoundedK0 P K₀[X] =
      weakSerreSingleDerivedClass (P := P) X := by
  simpa using
    AbelianK0.lift_of
      (weakSerreSingleDerivedClass (P := P))
      (relations_le_ker_weakSerreToDerivedBoundedK0 P)
      X

-- Proof sketch: `Dᵇ_P(A)` inherits its triangulated structure from the ambient derived category,
-- and the lifted degree-zero cohomology functor is the source-facing `H⁰` functor valued in the
-- weak Serre full subcategory. Exactness is therefore the same long exact cohomology sequence as
-- for `DerivedCategory.homologyFunctor A 0`, viewed inside `P.FullSubcategory`.
local instance derivedBoundedWithCohomologyInZeroHomologyFunctor_isHomological :
    (derivedBoundedWithCohomologyInZeroHomologyFunctor P).IsHomological := by
  -- Proof comment: compare the lifted `H⁰` functor with the ambient homological composite after
  -- forgetting to `A`, then reflect exactness back along the faithful weak-Serre inclusion.
  let F : Dᵇ_{P} ⥤ P.FullSubcategory :=
    derivedBoundedWithCohomologyInZeroHomologyFunctor P
  let G : Dᵇ_{P} ⥤ A :=
    (derivedCategoryBoundedCohomologyInProperty P).ι ⋙
      ObjectProperty.ι (t.bounded : ObjectProperty (D(A))) ⋙ H 0
  let e : F ⋙ P.ι ≅ G :=
    P.liftCompιIso G (fun X ↦ X.property 0)
  letI : P.ι.Faithful := inferInstance
  letI : P.ι.PreservesZeroMorphisms := by
    infer_instance
  letI : PreservesFiniteLimits P.ι :=
    ObjectProperty.weakSerreSubcategory_inclusion_preservesFiniteLimits P
  letI : PreservesFiniteColimits P.ι :=
    ObjectProperty.weakSerreSubcategory_inclusion_preservesFiniteColimits P
  refine ⟨fun T hT ↦ ?_⟩
  have hG : ((Pretriangulated.shortComplexOfDistTriangle T hT).map G).Exact := by
    exact (inferInstance : G.IsHomological).exact T hT
  have hFG : ((Pretriangulated.shortComplexOfDistTriangle T hT).map (F ⋙ P.ι)).Exact := by
    exact (shortComplex_exact_iff_of_functor_iso e
      (Pretriangulated.shortComplexOfDistTriangle T hT)).2 hG
  exact P.ι.reflects_exact_of_faithful _ hFG

/-- Helper for Lemma 13.28.5: on a shifted object of `Dᵇ_{P}`, the lifted degree-zero cohomology
functor computes the ambient `i`-th cohomology object. -/
noncomputable def derivedBoundedWithCohomologyIn_zero_homology_shift_obj_iso
    (X : Dᵇ_{P}) (i : ℤ) :
    ((derivedBoundedWithCohomologyInZeroHomologyFunctor P).obj
      ((shiftFunctor (Dᵇ_{P}) i).obj X)) ≅
      ((derivedBoundedWithCohomologyInHomologyFunctor P i).obj X) := by
  -- Proof comment: commute both inclusion functors past the shift, then rewrite `H⁰(X[i])` as
  -- `Hⁱ(X)` using the canonical shift comparison for derived-category cohomology.
  dsimp [derivedBoundedWithCohomologyInZeroHomologyFunctor,
    derivedBoundedWithCohomologyInHomologyFunctor]
  refine P.isoMk ?_
  refine ((H 0).mapIso ?_) ≪≫ (((H 0).isoShift i).app X.obj.obj) ≪≫ ?_
  · exact
      ((ObjectProperty.ι t.bounded).mapIso
        ((((derivedCategoryBoundedCohomologyInProperty P).ι).commShiftIso i).app X)) ≪≫
          (((ObjectProperty.ι t.bounded).commShiftIso i).app X.obj)
  · exact
      eqToIso
        (congrArg (fun F : DerivedCategory A ⥤ A => F.obj X.obj.obj)
          (DerivedCategory.shift_homologyFunctor A i))

/-- On generators, the Euler-characteristic map sends a bounded derived object with cohomology in
`P` to the alternating sum of the classes of its cohomology objects in `K₀(P)`. -/
noncomputable abbrev derivedBoundedWithCohomologyInEulerClass
    (X : Dᵇ_{P}) :
    AbelianK0 P.FullSubcategory :=
  ∑ᶠ i : ℤ, i.negOnePow •
    K₀[((derivedBoundedWithCohomologyInHomologyFunctor P i).obj X)]

/-- Helper for Lemma 13.28.5: any zero object of `P.FullSubcategory` has trivial class in
`K₀(P)`. -/
private theorem weakSerre_k0_zero_eq (Z : P.FullSubcategory) (hZ : IsZero Z) :
    K₀[Z] = 0 := by
  -- Proof comment: evaluate the Grothendieck relation for the zero short exact sequence in the
  -- weak Serre full subcategory and cancel one copy of the zero class.
  let S : ShortComplex P.FullSubcategory :=
    ShortComplex.mk (0 : (0 : P.FullSubcategory) ⟶ 0) (0 : (0 : P.FullSubcategory) ⟶ 0) (by simp)
  have hExact : S.Exact := by
    exact (S.exact_iff_epi (by simp [S])).2 inferInstance
  have hShort : S.ShortExact := ShortComplex.ShortExact.mk' hExact inferInstance inferInstance
  have hK0 : K₀[(0 : P.FullSubcategory)] = K₀[(0 : P.FullSubcategory)] + K₀[(0 : P.FullSubcategory)] := by
    simpa [S] using (AbelianK0.of_shortExact S hShort)
  have hSub := congrArg (fun z : AbelianK0 P.FullSubcategory ↦ z - K₀[(0 : P.FullSubcategory)]) hK0
  have hZero : (0 : AbelianK0 P.FullSubcategory) = K₀[(0 : P.FullSubcategory)] := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hSub
  let S' : ShortComplex P.FullSubcategory :=
    ShortComplex.mk hZ.isoZero.hom (0 : (0 : P.FullSubcategory) ⟶ 0) (by simp)
  have hExact' : S'.Exact := by
    exact (S'.exact_iff_epi (by simp [S'])).2 inferInstance
  have hShort' : S'.ShortExact := ShortComplex.ShortExact.mk' hExact' inferInstance inferInstance
  have hEq : K₀[Z] = K₀[(0 : P.FullSubcategory)] := by
    simpa [S', hZero.symm, add_comm] using
      (AbelianK0.of_shortExact S' hShort').symm
  calc
    K₀[Z] = K₀[(0 : P.FullSubcategory)] := hEq
    _ = 0 := by
      simpa using hZero.symm

/-- Helper for Lemma 13.28.5: isomorphic objects in `P.FullSubcategory` define the same
Grothendieck class. -/
private theorem weakSerre_k0_eq_of_iso {X Y : P.FullSubcategory} (e : X ≅ Y) :
    K₀[X] = K₀[Y] := by
  -- Proof comment: route the isomorphism through the short exact sequence `0 → X → Y → 0` in
  -- the weak Serre full subcategory.
  let S : ShortComplex P.FullSubcategory := ShortComplex.mk e.hom (0 : Y ⟶ 0) (by simp)
  have hExact : S.Exact := by
    exact (S.exact_iff_epi (by simp [S])).2 inferInstance
  have hShort : S.ShortExact := ShortComplex.ShortExact.mk' hExact inferInstance inferInstance
  simpa [S, weakSerre_k0_zero_eq (P := P) 0 (isZero_zero _), add_comm] using
    (AbelianK0.of_shortExact S hShort).symm

/-- Helper for Lemma 13.28.5: an object of the weak Serre full subcategory is zero whenever its
underlying ambient object is zero. -/
private theorem weakSerre_isZero_of_underlying_isZero
    (X : P.FullSubcategory) (hX : IsZero X.obj) :
    IsZero X := by
  -- Proof comment: lift the ambient isomorphism `X.obj ≅ 0` into the full subcategory `P`.
  have hzero_obj : (0 : A) ≅ (0 : P.FullSubcategory).obj := by
    simpa using (P.ι.mapZeroObject).symm
  let e : X ≅ (0 : P.FullSubcategory) := P.isoMk (hX.isoZero ≪≫ hzero_obj)
  exact IsZero.of_iso (isZero_zero _) e

/-- Helper for Lemma 13.28.5: the degree-zero cohomology of the degree-zero object `X[0]` in
`Dᵇ_{P}` is canonically `X`. -/
private noncomputable def derivedBoundedWithCohomologyInHomology_zero_single_iso
    (X : P.FullSubcategory) :
    ((derivedBoundedWithCohomologyInHomologyFunctor P (0 : ℤ)).obj
      ((weakSerreSingleFunctorToDerivedBounded P).obj X)) ≅ X := by
  -- Proof comment: forget to the ambient bounded derived category, compare with the usual degree-
  -- zero embedding, and then apply the standard derived-category identification `H⁰(X[0]) ≅ X`.
  refine P.isoMk ?_
  exact
    ((H 0).mapIso
      ((ObjectProperty.ι (t.bounded : ObjectProperty (D(A)))).mapIso
        ((weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).app X))) ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso A (0 : ℤ)).app X.obj

/-- Helper for Lemma 13.28.5: the Euler class of a degree-zero object is its original class in
`K₀(P)`. -/
theorem derivedBoundedWithCohomologyInEulerClass_single_zero
    (X : P.FullSubcategory) :
    derivedBoundedWithCohomologyInEulerClass P
        ((weakSerreSingleFunctorToDerivedBounded P).obj X) =
      K₀[X] := by
  -- Proof comment: only the degree-zero cohomology term survives for the degree-zero object
  -- `X[0]`; the surviving term is identified with `X` by the canonical `H⁰(X[0]) ≅ X`.
  let Y := (weakSerreSingleFunctorToDerivedBounded P).obj X
  let f : ℤ → AbelianK0 P.FullSubcategory :=
    fun i ↦ i.negOnePow • K₀[((derivedBoundedWithCohomologyInHomologyFunctor P i).obj Y)]
  have hsupport :
      ∀ i : ℤ, i ∉ Set.Icc (0 : ℤ) 0 → f i = 0 := by
    intro i hi
    have hi0 : i ≠ 0 := by
      simpa using hi
    have hzeroHomology :
        IsZero ((derivedBoundedWithCohomologyInHomologyFunctor P i).obj Y) := by
      refine weakSerre_isZero_of_underlying_isZero (P := P) _ ?_
      change IsZero ((H i).obj ((single₀).obj X.obj))
      exact single_zero_complex_homology_isZero_of_ne (A := A) X.obj i hi0
    have hk0 :
        K₀[((derivedBoundedWithCohomologyInHomologyFunctor P i).obj Y)] = 0 := by
      calc
        K₀[((derivedBoundedWithCohomologyInHomologyFunctor P i).obj Y)] =
            K₀[(0 : P.FullSubcategory)] := by
              exact weakSerre_k0_eq_of_iso (P := P) hzeroHomology.isoZero
        _ = 0 := weakSerre_k0_zero_eq (P := P) 0 (isZero_zero _)
    change i.negOnePow • K₀[((derivedBoundedWithCohomologyInHomologyFunctor P i).obj Y)] = 0
    rw [hk0]
    simp
  have hsum :
      derivedBoundedWithCohomologyInEulerClass P Y =
        Finset.sum (Finset.Icc (0 : ℤ) 0) f := by
    have hsupp :
        Function.support f ⊆ ↑(Finset.Icc (0 : ℤ) 0) := by
      intro i hi
      by_contra hnot
      exact hi (hsupport i (by simpa using hnot))
    simpa [derivedBoundedWithCohomologyInEulerClass, f] using
      (finsum_eq_sum_of_support_subset (s := Finset.Icc (0 : ℤ) 0) f hsupp)
  have hzero :
      K₀[((derivedBoundedWithCohomologyInHomologyFunctor P (0 : ℤ)).obj Y)] = K₀[X] := by
    -- Proof comment: the unique surviving degree-zero cohomology object is canonically `X`.
    exact weakSerre_k0_eq_of_iso (P := P)
      (derivedBoundedWithCohomologyInHomology_zero_single_iso (A := A) P X)
  calc
    derivedBoundedWithCohomologyInEulerClass P Y = Finset.sum (Finset.Icc (0 : ℤ) 0) f := hsum
    _ = f 0 := by simp
    _ = K₀[X] := by simpa [f, hzero]

-- Proof sketch: boundedness gives integers `a ≤ b` such that `H^i(X) = 0` outside `[a, b]`.
-- Since the tautological shift sequence on the lifted degree-zero cohomology functor computes the
-- degree-`i` cohomology objects up to the standard derived-category shift identification, only
-- finitely many shifts contribute.
/-- The lifted degree-zero cohomology functor has finite shift support on `Dᵇ_{P}`. -/
theorem derivedBoundedWithCohomologyInZeroHomologyFunctor_hasFiniteShiftSupport :
    ∀ X : Dᵇ_{P},
      (derivedBoundedWithCohomologyInZeroHomologyFunctor P).shiftVanishingBounded X := by
  -- Proof comment: boundedness of the ambient derived object gives vanishing of `Hⁱ(X)` outside
  -- a finite interval, and `H⁰(X[i]) ≅ Hⁱ(X)` transports that vanishing back to `P`.
  intro X
  rcases (derivedCategory_t_bounded_iff X.obj.obj).1 X.obj.property with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  refine ⟨⟨a - 1, ?_⟩, ⟨b + 1, ?_⟩⟩
  · intro n hn
    have hzero :
        IsZero ((derivedBoundedWithCohomologyInHomologyFunctor P n).obj X) := by
      refine weakSerre_isZero_of_underlying_isZero (P := P) _ ?_
      simpa [derivedBoundedWithCohomologyInHomologyFunctor] using ha n (by omega)
    exact IsZero.of_iso
      hzero
      (derivedBoundedWithCohomologyIn_zero_homology_shift_obj_iso (A := A) P X n)
  · intro n hn
    have hzero :
        IsZero ((derivedBoundedWithCohomologyInHomologyFunctor P n).obj X) := by
      refine weakSerre_isZero_of_underlying_isZero (P := P) _ ?_
      simpa [derivedBoundedWithCohomologyInHomologyFunctor] using hb n (by omega)
    exact IsZero.of_iso
      hzero
      (derivedBoundedWithCohomologyIn_zero_homology_shift_obj_iso (A := A) P X n)

-- Proof sketch: with the tautological shift sequence on the lifted degree-zero cohomology
-- functor, the `i`-th shifted value is `H⁰(X[i])`, canonically identified with `H^i(X)`. The
-- Euler class from `Lemma 13.28.4` is therefore exactly the textbook alternating sum of the
-- cohomology classes.
/-- The Euler class coming from the general homological-functor owner for the lifted degree-zero
cohomology functor agrees with the textbook alternating sum of the cohomology objects. -/
theorem derivedBoundedWithCohomologyInZeroHomologyFunctor_eulerClass_eq
    (X : Dᵇ_{P}) :
    (derivedBoundedWithCohomologyInZeroHomologyFunctor P).eulerClass X =
      derivedBoundedWithCohomologyInEulerClass P X := by
  -- Proof comment: compare each Euler summand through the tautological shift on the lifted
  -- degree-zero functor and the canonical identification `H⁰(X[i]) ≅ Hⁱ(X)`.
  refine finsum_congr ?_
  intro i
  have hIso :
      ((derivedBoundedWithCohomologyInZeroHomologyFunctor P).shift i).obj X ≅
        ((derivedBoundedWithCohomologyInHomologyFunctor P i).obj X) := by
    exact
      ((derivedBoundedWithCohomologyInZeroHomologyFunctor P).isoShift i).app X ≪≫
        derivedBoundedWithCohomologyIn_zero_homology_shift_obj_iso (A := A) P X i
  -- Rewrite the `K₀` class of each shifted `H⁰` value by the comparison isomorphism.
  exact congrArg (fun z : AbelianK0 P.FullSubcategory ↦ i.negOnePow • z)
    (by
      calc
        K₀[((derivedBoundedWithCohomologyInZeroHomologyFunctor P).shift i).obj X] =
            K₀[((derivedBoundedWithCohomologyInHomologyFunctor P i).obj X)] := by
              exact weakSerre_k0_eq_of_iso (P := P) hIso)

/-- The Euler-characteristic map `K₀(Dᵇ_{P}) → K₀(P)`. -/
def derivedBoundedWithCohomologyInEulerK0 :
    TriangulatedK0 (Dᵇ_{P}) →+ AbelianK0 P.FullSubcategory :=
  (derivedBoundedWithCohomologyInZeroHomologyFunctor P).eulerK0Map
    (derivedBoundedWithCohomologyInZeroHomologyFunctor_hasFiniteShiftSupport P)

-- Proof sketch: `derivedBoundedWithCohomologyInEulerK0` is the general owner
-- `H0.eulerK0Map` applied to the lifted degree-zero cohomology functor on `Dᵇ_P(A)`;
-- the companion comparison theorem identifies the resulting Euler class with the textbook
-- alternating sum of cohomology classes.
/-- The Euler-characteristic map sends the class of `X` to the alternating sum of the classes of
its cohomology objects. -/
@[simp] theorem derivedBoundedWithCohomologyInEulerK0_apply_of
    (X : Dᵇ_{P}) :
    derivedBoundedWithCohomologyInEulerK0 P (TriangulatedK0.of X) =
      derivedBoundedWithCohomologyInEulerClass P X := by
  simpa [derivedBoundedWithCohomologyInEulerK0] using
    (Functor.eulerK0Map_apply_of (derivedBoundedWithCohomologyInZeroHomologyFunctor P)
      (derivedBoundedWithCohomologyInZeroHomologyFunctor_hasFiniteShiftSupport P) X).trans
        (derivedBoundedWithCohomologyInZeroHomologyFunctor_eulerClass_eq P X)

-- Proof sketch: evaluate the Euler characteristic of the degree-zero object `X[0]`; all
-- cohomology groups vanish except in degree `0`, where the cohomology object is `X` itself.
/-- The Euler-characteristic map is a left inverse to the degree-zero embedding on `K₀(P)`. -/
theorem weakSerreToDerivedBoundedK0_leftInverse :
    Function.LeftInverse
      (derivedBoundedWithCohomologyInEulerK0 P)
      (weakSerreToDerivedBoundedK0 P) := by
  -- Proof comment: descend the generator computation for `X[0]` through the quotient
  -- presentation of `AbelianK0 P.FullSubcategory`.
  intro x
  refine Quotient.inductionOn x ?_
  intro z
  induction z using FreeAbelianGroup.induction_on with
  | zero =>
      simp
  | of X =>
      -- Proof comment: compute the composite on the generator `[X]` using the explicit Euler
      -- class of the degree-zero object.
      calc
        derivedBoundedWithCohomologyInEulerK0 P (weakSerreToDerivedBoundedK0 P K₀[X]) =
            derivedBoundedWithCohomologyInEulerK0 P
              (weakSerreSingleDerivedClass (P := P) X) := by
                rw [weakSerreToDerivedBoundedK0_apply_of]
        _ = derivedBoundedWithCohomologyInEulerK0 P
              (TriangulatedK0.of ((weakSerreSingleFunctorToDerivedBounded P).obj X)) := by
                rfl
        _ = derivedBoundedWithCohomologyInEulerClass P
              ((weakSerreSingleFunctorToDerivedBounded P).obj X) := by
                rw [derivedBoundedWithCohomologyInEulerK0_apply_of]
        _ = K₀[X] := derivedBoundedWithCohomologyInEulerClass_single_zero (A := A) P X
  | neg z ih =>
      simpa using congrArg Neg.neg ih
  | add z w ihz ihw =>
      simpa [map_add] using congrArg₂ HAdd.hAdd ihz ihw

/-- Helper for Lemma 13.28.5: the zero object has trivial class in
`TriangulatedK0 (Dᵇ_{P})`. -/
private theorem triangulatedK0_of_zero_eq :
    TriangulatedK0.of (0 : Dᵇ_{P}) = 0 := by
  -- Proof comment: apply the distinguished zero-cone relation to the identity of the zero object
  -- and cancel one copy of the zero class.
  have hT :
      Triangle.mk (𝟙 (0 : Dᵇ_{P})) (0 : (0 : Dᵇ_{P}) ⟶ 0) 0 ∈ distTriang (Dᵇ_{P}) := by
    exact
      (isIso_iff_zero_cone_triangle_distinguished (D := Dᵇ_{P}) (𝟙 (0 : Dᵇ_{P}))).1
        (by infer_instance)
  have hK0 :
      TriangulatedK0.of (0 : Dᵇ_{P}) =
        TriangulatedK0.of (0 : Dᵇ_{P}) + TriangulatedK0.of (0 : Dᵇ_{P}) := by
    simpa using
      TriangulatedK0.of_distinguished
        (Triangle.mk (𝟙 (0 : Dᵇ_{P})) (0 : (0 : Dᵇ_{P}) ⟶ 0) 0) hT
  have hSub := congrArg (fun z : TriangulatedK0 (Dᵇ_{P}) ↦ z - TriangulatedK0.of (0 : Dᵇ_{P})) hK0
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hSub.symm

/-- Helper for Lemma 13.28.5: isomorphic objects of `Dᵇ_{P}` define the same triangulated
Grothendieck class. -/
private theorem triangulatedK0_of_eq_of_iso
    {X Y : Dᵇ_{P}} (e : X ≅ Y) :
    TriangulatedK0.of X = TriangulatedK0.of Y := by
  -- Proof comment: the zero-cone triangle on an isomorphism is distinguished, so its relation
  -- reduces to `[Y] = [X] + [0]`.
  have hT :
      Triangle.mk e.hom (0 : Y ⟶ 0) 0 ∈ distTriang (Dᵇ_{P}) := by
    exact
      (isIso_iff_zero_cone_triangle_distinguished (D := Dᵇ_{P}) e.hom).1
        (by infer_instance)
  have hK0 :
      TriangulatedK0.of Y = TriangulatedK0.of X + TriangulatedK0.of (0 : Dᵇ_{P}) := by
    simpa using TriangulatedK0.of_distinguished (Triangle.mk e.hom (0 : Y ⟶ 0) 0) hT
  simpa [triangulatedK0_of_zero_eq (A := A) (P := P)] using hK0.symm

/-- Helper for Lemma 13.28.5: the contractible triangle `X ⟶ 0 ⟶ X[1]` inside `Dᵇ_{P}`. -/
private def shiftOneContractibleTriangle (X : Dᵇ_{P}) :
    Triangle (Dᵇ_{P}) :=
  Triangle.mk (0 : X ⟶ 0) 0 (𝟙 (X⟦(1 : ℤ)⟧))

/-- Helper for Lemma 13.28.5: the contractible triangle `X ⟶ 0 ⟶ X[1]` is distinguished. -/
private theorem shiftOneContractibleTriangle_distinguished (X : Dᵇ_{P}) :
    shiftOneContractibleTriangle (P := P) X ∈ distTriang (Dᵇ_{P}) := by
  -- Proof comment: this is the standard contractible distinguished triangle provided by the
  -- pretriangulated structure.
  simpa [shiftOneContractibleTriangle] using contractible_distinguished₂ X

/-- Helper for Lemma 13.28.5: shifting by one negates the triangulated Grothendieck class in
`Dᵇ_{P}`. -/
private theorem triangulatedK0_of_shift_one_eq_neg
    (X : Dᵇ_{P}) :
    TriangulatedK0.of (X⟦(1 : ℤ)⟧) = -TriangulatedK0.of X := by
  -- Proof comment: the contractible triangle yields the relation `[0] = [X] + [X[1]]`.
  have hK0 :
      TriangulatedK0.of (0 : Dᵇ_{P}) =
        TriangulatedK0.of X + TriangulatedK0.of (X⟦(1 : ℤ)⟧) := by
    simpa using
      TriangulatedK0.of_distinguished
        (shiftOneContractibleTriangle (P := P) X)
        (shiftOneContractibleTriangle_distinguished (A := A) (P := P) X)
  have hZero :
      (0 : TriangulatedK0 (Dᵇ_{P})) =
        TriangulatedK0.of X + TriangulatedK0.of (X⟦(1 : ℤ)⟧) := by
    simpa [triangulatedK0_of_zero_eq (A := A) (P := P)] using hK0
  have hsum :
      TriangulatedK0.of X + TriangulatedK0.of (X⟦(1 : ℤ)⟧) = 0 := by
    simpa using hZero.symm
  have hsum' :
      TriangulatedK0.of (X⟦(1 : ℤ)⟧) + TriangulatedK0.of X = 0 := by
    simpa [add_comm] using hsum
  exact eq_neg_of_add_eq_zero_left hsum'

/-- Helper for Lemma 13.28.5: shifting by `i` multiplies the triangulated Grothendieck class by
`(-1)^i`. -/
private theorem triangulatedK0_of_shift_eq_negOnePow_smul
    (X : Dᵇ_{P}) (i : ℤ) :
    TriangulatedK0.of (X⟦i⟧) = i.negOnePow • TriangulatedK0.of X := by
  -- Proof comment: the one-step shift formula propagates to all integers by the same induction
  -- on `ℤ` used in the ambient bounded-derived case.
  let Q : ℤ → Prop := fun j ↦
    TriangulatedK0.of (X⟦j⟧) = j.negOnePow • TriangulatedK0.of X
  have hstep : ∀ m : ℤ, Q (m + 1) ↔ Q m := by
    intro m
    have hshift :
        TriangulatedK0.of (X⟦m + 1⟧) = -TriangulatedK0.of (X⟦m⟧) := by
      -- Proof comment: rewrite the `(m + 1)` shift as the iterated shift by `m` and then by `1`.
      calc
        TriangulatedK0.of (X⟦m + 1⟧) = TriangulatedK0.of ((X⟦m⟧)⟦(1 : ℤ)⟧) := by
          exact triangulatedK0_of_eq_of_iso (A := A) (P := P) (shiftAdd X m (1 : ℤ))
        _ = -TriangulatedK0.of (X⟦m⟧) := by
          exact triangulatedK0_of_shift_one_eq_neg (A := A) (P := P) (X := X⟦m⟧)
    have hsign : (m + 1).negOnePow = -m.negOnePow := by
      calc
        (m + 1).negOnePow = m.negOnePow * (1 : ℤ).negOnePow := by
          rw [Int.negOnePow_add]
        _ = m.negOnePow * (-1) := by simp
        _ = -m.negOnePow := by simp
    constructor
    · intro hm
      -- Proof comment: invert the successor relation and then rewrite the sign.
      calc
        TriangulatedK0.of (X⟦m⟧) = -TriangulatedK0.of (X⟦m + 1⟧) := by
          simpa using (congrArg Neg.neg hshift).symm
        _ = -((m + 1).negOnePow • TriangulatedK0.of X) := by
          rw [hm]
        _ = m.negOnePow • TriangulatedK0.of X := by
          rw [hsign]
          simp
    · intro hm
      -- Proof comment: the successor class is the negative of the predecessor class.
      calc
        TriangulatedK0.of (X⟦m + 1⟧) = -TriangulatedK0.of (X⟦m⟧) := hshift
        _ = -(m.negOnePow • TriangulatedK0.of X) := by
          rw [hm]
        _ = (m + 1).negOnePow • TriangulatedK0.of X := by
          rw [hsign]
          simp
  change Q i
  refine Int.induction_on i ?_ ?_ ?_
  · -- Proof comment: shift by `0` is canonically the identity.
    calc
      TriangulatedK0.of (X⟦(0 : ℤ)⟧) = TriangulatedK0.of X := by
        exact triangulatedK0_of_eq_of_iso (A := A) (P := P)
          ((shiftFunctorZero (Dᵇ_{P}) ℤ).app X)
      _ = (0 : ℤ).negOnePow • TriangulatedK0.of X := by
        simp
  · intro m hm
    exact (hstep m).2 hm
  · intro m hm
    -- Proof comment: the negative branch is the predecessor case of the same one-step
    -- equivalence.
    have hpred : Q (-(m : ℤ)) ↔ Q (-(m : ℤ) - 1) := by
      have hm' : (-(m : ℤ) - 1) + 1 = -(m : ℤ) := by
        omega
      simpa [hm'] using hstep (-(m : ℤ) - 1)
    exact hpred.mp hm

/-- Helper for Lemma 13.28.5: once the cohomology objects vanish outside an interval, the Euler
class of an object of `Dᵇ_{P}` is the corresponding finite sum. -/
private lemma derivedBoundedWithCohomologyInEulerClass_eq_sum_of_vanishingOutside
    (X : Dᵇ_{P}) {a b : ℤ}
    (hX : ∀ n : ℤ, n ∉ Set.Icc a b →
      IsZero ((derivedBoundedWithCohomologyInHomologyFunctor P n).obj X)) :
    derivedBoundedWithCohomologyInEulerClass P X =
      Finset.sum (Finset.Icc a b)
        (fun i ↦ i.negOnePow • K₀[((derivedBoundedWithCohomologyInHomologyFunctor P i).obj X)]) := by
  -- Proof comment: outside the chosen interval every cohomology object is zero, so the `finsum`
  -- reduces to the corresponding finite sum.
  let f : ℤ → AbelianK0 P.FullSubcategory :=
    fun i ↦ i.negOnePow • K₀[((derivedBoundedWithCohomologyInHomologyFunctor P i).obj X)]
  change ∑ᶠ i : ℤ, f i = Finset.sum (Finset.Icc a b) f
  have hsupp : Function.support f ⊆ ↑(Finset.Icc a b) := by
    intro i hi
    by_contra hnot
    have hzeroObj :
        IsZero ((derivedBoundedWithCohomologyInHomologyFunctor P i).obj X) := hX i <| by
          simpa using hnot
    have hk0 :
        K₀[((derivedBoundedWithCohomologyInHomologyFunctor P i).obj X)] = 0 := by
      calc
        K₀[((derivedBoundedWithCohomologyInHomologyFunctor P i).obj X)] =
            K₀[(0 : P.FullSubcategory)] := by
              exact weakSerre_k0_eq_of_iso (P := P) hzeroObj.isoZero
        _ = 0 := weakSerre_k0_zero_eq (P := P) 0 (isZero_zero _)
    have hfi : f i = 0 := by
      rw [show f i =
        i.negOnePow • K₀[((derivedBoundedWithCohomologyInHomologyFunctor P i).obj X)] by rfl]
      rw [hk0, smul_zero]
    exact hi hfi
  rw [finsum_eq_sum_of_support_subset (s := Finset.Icc a b) f hsupp]

/-- Helper for Lemma 13.28.5: the degree-`i` single complex of an object of `A` is bounded. -/
private theorem singleFunctor_obj_mem_boundedDerivedCategory_degree
    (X : A) (i : ℤ) :
    t.bounded ((DerivedCategory.singleFunctor A i).obj X) := by
  -- Proof comment: the degree-`i` single complex has no cohomology below or above `i`.
  rw [derivedCategory_t_bounded_iff]
  refine ⟨⟨i, ?_⟩, ⟨i, ?_⟩⟩
  · intro j hj
    let _ : ((DerivedCategory.singleFunctor A i).obj X).IsGE i := inferInstance
    exact DerivedCategory.isZero_of_isGE _ i j hj
  · intro j hj
    let _ : ((DerivedCategory.singleFunctor A i).obj X).IsLE i := inferInstance
    exact DerivedCategory.isZero_of_isLE _ i j hj

/-- Helper for Lemma 13.28.5: the cohomology of a degree-`i` single complex vanishes away from
degree `i`. -/
private theorem single_degree_complex_homology_isZero_of_ne
    (X : A) (i j : ℤ) (hij : j ≠ i) :
    IsZero ((H j).obj ((DerivedCategory.singleFunctor A i).obj X)) := by
  -- Proof comment: a degree-`i` single complex is bounded below and above by `i`, so all other
  -- cohomology groups vanish by the standard `t`-structure bounds.
  by_cases hjlt : j < i
  · let _ : ((DerivedCategory.singleFunctor A i).obj X).IsGE i := inferInstance
    exact DerivedCategory.isZero_of_isGE _ i j hjlt
  · have hij' : i < j := by
      omega
    let _ : ((DerivedCategory.singleFunctor A i).obj X).IsLE i := inferInstance
    exact DerivedCategory.isZero_of_isLE _ i j hij'

omit [P.IsWeakSerreClass] in
/-- Helper for Lemma 13.28.5: upper truncations of objects of `Dᵇ_{P}` stay bounded in the
ambient bounded derived category. -/
private theorem truncLT_obj_mem_boundedDerivedCategory
    (X : Dᵇ_{P}) (n : ℤ) :
    t.bounded ((t.truncLT n).obj X.obj.obj) := by
  rcases (derivedCategory_t_bounded_iff X.obj.obj).1 X.obj.property with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  let _ : X.obj.obj.IsGE a := by
    rw [DerivedCategory.isGE_iff]
    exact ha
  let _ : X.obj.obj.IsLE b := by
    rw [DerivedCategory.isLE_iff]
    exact hb
  rw [derivedCategory_t_bounded_iff]
  refine ⟨⟨a, ?_⟩, ⟨n - 1, ?_⟩⟩
  · intro i hi
    let _ : ((t.truncLT n).obj X.obj.obj).IsGE a := inferInstance
    exact DerivedCategory.isZero_of_isGE _ a i hi
  · intro i hi
    let _ : ((t.truncLT n).obj X.obj.obj).IsLE (n - 1) := by
      simpa using (inferInstance : ((t.truncLT n).obj X.obj.obj).IsLE (n - 1))
    exact DerivedCategory.isZero_of_isLE _ (n - 1) i hi

/-- Helper for Lemma 13.28.5: the degree-`i` single complex of an object of
`P.FullSubcategory` lies in `Dᵇ_{P}`. -/
private theorem weakSerreSingle_obj_mem_derivedCategoryBoundedCohomologyInProperty_degree
    (X : P.FullSubcategory) (i : ℤ) :
    derivedCategoryBoundedCohomologyInProperty P
      ⟨(DerivedCategory.singleFunctor A i).obj X.obj,
        singleFunctor_obj_mem_boundedDerivedCategory_degree (A := A) X.obj i⟩ := by
  intro j
  by_cases hij : j = i
  · subst j
    simpa [derivedCategoryBoundedCohomologyInProperty, derivedCategoryCohomologyInProperty,
      Functor.comp_obj] using
        P.prop_of_iso ((singleFunctorCompHomologyFunctorIso A i).app X.obj).symm X.property
  · have hzero :
        IsZero ((H j).obj ((DerivedCategory.singleFunctor A i).obj X.obj)) := by
      exact single_degree_complex_homology_isZero_of_ne (A := A) X.obj i j hij
    simpa [derivedCategoryBoundedCohomologyInProperty, derivedCategoryCohomologyInProperty,
      Functor.comp_obj] using P.prop_of_isZero hzero

/-- Helper for Lemma 13.28.5: the degree-`i` single object on `X` regarded as an object of
`Dᵇ_{P}`. -/
private abbrev weakSerreSingleDerivedDegree
    (X : P.FullSubcategory) (i : ℤ) :
    Dᵇ_{P} :=
  ⟨⟨(DerivedCategory.singleFunctor A i).obj X.obj,
      singleFunctor_obj_mem_boundedDerivedCategory_degree (A := A) X.obj i⟩,
    weakSerreSingle_obj_mem_derivedCategoryBoundedCohomologyInProperty_degree
      (A := A) (P := P) X i⟩

/-- Helper for Lemma 13.28.5: in `Dᵇ(A)`, the degree-`i` single object is the `(-i)`-shift of
the degree-zero bounded object. -/
private noncomputable def boundedDerivedSingleObjIsoShiftedSingleZero
    (X : A) (i : ℤ) :
    ⟨(DerivedCategory.singleFunctor A i).obj X,
      singleFunctor_obj_mem_boundedDerivedCategory_degree (A := A) X i⟩ ≅
      ((singleFunctorToBoundedDerived (A := A)).obj X)⟦-i⟧ := by
  let eAmbient :
      (ObjectProperty.ι t.bounded).obj
          ⟨(DerivedCategory.singleFunctor A i).obj X,
            singleFunctor_obj_mem_boundedDerivedCategory_degree (A := A) X i⟩ ≅
        (ObjectProperty.ι t.bounded).obj (((singleFunctorToBoundedDerived (A := A)).obj X)⟦-i⟧) :=
    (shiftShiftNeg ((DerivedCategory.singleFunctor A i).obj X) i).symm ≪≫
      (shiftFunctor (D(A)) (-i)).mapIso
        (singleFunctor_shifted_single0_iso_canonical (𝒜 := A) X i) ≪≫
      (((ObjectProperty.ι t.bounded).commShiftIso (-i)).app
        ((singleFunctorToBoundedDerived (A := A)).obj X)).symm
  -- Proof comment: recover the bounded-derived isomorphism from its image under the fully
  -- faithful inclusion `Dᵇ(A) ⥤ D(A)`.
  exact
    (Functor.FullyFaithful.ofFullyFaithful (ObjectProperty.ι t.bounded)).preimageIso eAmbient

/-- Helper for Lemma 13.28.5: the raw degree-`i` local single object is the `(-i)`-shift of the
local degree-zero image. -/
private noncomputable def weakSerreSingleDerivedDegreeIsoShiftedSingleZero
    (X : P.FullSubcategory) (i : ℤ) :
    weakSerreSingleDerivedDegree (A := A) (P := P) X i ≅
      ((weakSerreSingleFunctorToDerivedBounded P).obj X)⟦-i⟧ :=
  let eAmbient :
      ((derivedCategoryBoundedCohomologyInProperty P).ι).obj
          (weakSerreSingleDerivedDegree (A := A) (P := P) X i) ≅
        ((derivedCategoryBoundedCohomologyInProperty P).ι).obj
          (((weakSerreSingleFunctorToDerivedBounded P).obj X)⟦-i⟧) :=
    (boundedDerivedSingleObjIsoShiftedSingleZero (A := A) X.obj i) ≪≫
      ((shiftFunctor (Dᵇ(A)) (-i)).mapIso
        ((weakSerreSingleFunctorToBoundedDerivedCompIso (A := A) (P := P)).app X)).symm ≪≫
      ((((derivedCategoryBoundedCohomologyInProperty P).ι).commShiftIso (-i)).app
        ((weakSerreSingleFunctorToDerivedBounded P).obj X)).symm
  -- Proof comment: pull the ambient comparison back once through the fully faithful inclusion
  -- `Dᵇ_{P} ⥤ Dᵇ(A)`.
  (Functor.FullyFaithful.ofFullyFaithful
      ((derivedCategoryBoundedCohomologyInProperty P).ι)).preimageIso eAmbient

/-- Helper for Lemma 13.28.5: the class of the degree-`i` local single object is the signed
class of its underlying object embedded in degree `0`. -/
private theorem triangulatedK0_of_weakSerreSingleDerivedDegree
    (X : P.FullSubcategory) (i : ℤ) :
    TriangulatedK0.of (weakSerreSingleDerivedDegree (A := A) (P := P) X i) =
      weakSerreToDerivedBoundedK0 P (i.negOnePow • K₀[X]) := by
  -- Proof comment: first rewrite the raw degree-`i` local single object as a shift of the
  -- degree-zero embedding, then convert that shift into the textbook sign `(-1)^i`.
  calc
    TriangulatedK0.of (weakSerreSingleDerivedDegree (A := A) (P := P) X i) =
        TriangulatedK0.of (((weakSerreSingleFunctorToDerivedBounded P).obj X)⟦-i⟧) := by
          exact triangulatedK0_of_eq_of_iso (A := A) (P := P)
            (weakSerreSingleDerivedDegreeIsoShiftedSingleZero (A := A) (P := P) X i)
    _ = (-i).negOnePow • TriangulatedK0.of ((weakSerreSingleFunctorToDerivedBounded P).obj X) := by
      exact triangulatedK0_of_shift_eq_negOnePow_smul (A := A) (P := P)
        ((weakSerreSingleFunctorToDerivedBounded P).obj X) (-i)
    _ = i.negOnePow • TriangulatedK0.of ((weakSerreSingleFunctorToDerivedBounded P).obj X) := by
      rw [Int.negOnePow_neg]
    _ = i.negOnePow • weakSerreToDerivedBoundedK0 P K₀[X] := by
      exact congrArg (fun z : TriangulatedK0 (Dᵇ_{P}) ↦ i.negOnePow • z)
        (weakSerreToDerivedBoundedK0_apply_of (P := P) X).symm
    _ = weakSerreToDerivedBoundedK0 P (i.negOnePow • K₀[X]) := by
      exact ((weakSerreToDerivedBoundedK0 P).map_zsmul K₀[X] i.negOnePow).symm

/-- Helper for Lemma 13.28.5: the upper truncation of a local bounded-derived object, viewed in
`Dᵇ(A)`. -/
private abbrev weakSerreBoundedTruncLTObject
    (X : Dᵇ_{P}) (i : ℤ) : Dᵇ(A) :=
  ⟨(t.truncLT i).obj X.obj.obj,
    truncLT_obj_mem_boundedDerivedCategory (A := A) (P := P) X i⟩

omit [P.IsWeakSerreClass] in
/-- Helper for Lemma 13.28.5: the canonical inclusion `τ_{< i + 1} K ⟶ K` is a homology
isomorphism in degree `i`. -/
private theorem truncLTHomologyMapIsIsoStep
    (K : DerivedCategory A) (i c : ℤ) (hc : i + 1 = c) :
    IsIso ((H i).map ((t.truncLTι c).app K)) := by
  subst hc
  let T : Triangle (DerivedCategory A) := (t.triangleLTGE (i + 1)).obj K
  have hT : T ∈ distTriang (DerivedCategory A) := by
    simpa [T] using t.triangleLTGE_distinguished (i + 1) K
  have h₃ : T.obj₃.IsGE (i + 1) := by
    dsimp [T]
    infer_instance
  have hmor₂_zero : (H i).map T.mor₂ = 0 := by
    letI := h₃
    exact (DerivedCategory.isZero_of_isGE T.obj₃ (i + 1) i (by omega)).eq_of_tgt _ _
  have hδ_zero : HomologySequence.δ T (i - 1) i (by omega) = 0 := by
    letI := h₃
    exact (DerivedCategory.isZero_of_isGE T.obj₃ (i + 1) (i - 1) (by omega)).eq_of_src _ _
  letI : Epi ((H i).map T.mor₁) :=
    (HomologySequence.epi_homologyMap_mor₁_iff T hT i).2 hmor₂_zero
  letI : Mono ((H i).map T.mor₁) :=
    (HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)).2 hδ_zero
  simpa [T] using (isIso_of_mono_of_epi ((H i).map T.mor₁))

omit [P.IsWeakSerreClass] in
/-- Helper for Lemma 13.28.5: the canonical inclusion `τ_{< n} K ⟶ K` induces an isomorphism on
degree-`i` homology whenever `i < n`. -/
private theorem truncLTHomologyMapIsIsoOfLt
    (K : DerivedCategory A) (i n : ℤ) (hi : i < n) :
    IsIso ((H i).map ((t.truncLTι n).app K)) := by
  let f : (t.truncLT n).obj K ⟶ K := (t.truncLTι n).app K
  let Y : DerivedCategory A := (t.truncLT n).obj K
  letI : IsIso ((H i).map ((t.truncLTι (i + 1)).app K)) :=
    truncLTHomologyMapIsIsoStep (A := A) K i (i + 1) rfl
  letI : IsIso ((H i).map ((t.truncLTι (i + 1)).app Y)) :=
    truncLTHomologyMapIsIsoStep (A := A) Y i (i + 1) rfl
  let eK : (H i).obj K ≅ (H i).obj ((t.truncLT (i + 1)).obj K) :=
    (asIso ((H i).map ((t.truncLTι (i + 1)).app K))).symm
  let eY : (H i).obj Y ≅ (H i).obj ((t.truncLT (i + 1)).obj Y) :=
    (asIso ((H i).map ((t.truncLTι (i + 1)).app Y))).symm
  -- Proof comment: compare the desired map with its image under the further truncation `τ_{< i+1}`.
  have hnat :
      (H i).map ((t.truncLT (i + 1)).map f) ≫ (H i).map ((t.truncLTι (i + 1)).app K) =
        (H i).map ((t.truncLTι (i + 1)).app Y) ≫ (H i).map f := by
    simpa [Functor.map_comp, f, Y] using
      congrArg ((H i).map) (NatTrans.naturality (t.truncLTι (i + 1)) f)
  have hYinv :
      eY.hom ≫ (H i).map ((t.truncLTι (i + 1)).app Y) = 𝟙 _ := by
    simp [eY]
  have hKinv :
      eK.hom ≫ (H i).map ((t.truncLTι (i + 1)).app K) = 𝟙 _ := by
    simp [eK]
  have hf :
      eY.hom ≫ (H i).map ((t.truncLT (i + 1)).map f) =
        (H i).map f ≫ eK.hom := by
    apply (cancel_mono ((H i).map ((t.truncLTι (i + 1)).app K))).1
    have h₁ :
        eY.hom ≫ (H i).map ((t.truncLT (i + 1)).map f) ≫
            (H i).map ((t.truncLTι (i + 1)).app K) =
          eY.hom ≫ (H i).map ((t.truncLTι (i + 1)).app Y) ≫ (H i).map f := by
      simpa [Category.assoc] using congrArg (fun m ↦ eY.hom ≫ m) hnat
    have h₂ :
        eY.hom ≫ (H i).map ((t.truncLTι (i + 1)).app Y) ≫ (H i).map f =
          (H i).map f := by
      simpa [Category.assoc] using congrArg (fun m ↦ m ≫ (H i).map f) hYinv
    have h₃ :
        (H i).map f =
          (H i).map f ≫ eK.hom ≫ (H i).map ((t.truncLTι (i + 1)).app K) := by
      symm
      simpa [Category.assoc] using congrArg (fun m ↦ (H i).map f ≫ m) hKinv
    simpa [Category.assoc] using h₁.trans (h₂.trans h₃)
  have hmiddle : IsIso ((H i).map ((t.truncLT (i + 1)).map f)) := by
    letI : IsIso ((t.truncLT (i + 1)).map f) :=
      t.isIso_truncLT_map_truncLTι_app (i + 1) n (by omega) K
    exact Functor.map_isIso (H i) ((t.truncLT (i + 1)).map f)
  have hcomp : IsIso ((H i).map f ≫ eK.hom) := by
    rw [← hf]
    letI : IsIso ((H i).map ((t.truncLT (i + 1)).map f)) := hmiddle
    infer_instance
  letI : IsIso ((H i).map f ≫ eK.hom) := hcomp
  exact IsIso.of_isIso_comp_right ((H i).map f) eK.hom

omit [P.IsWeakSerreClass] in
/-- Helper for Lemma 13.28.5: upper truncations of objects of `Dᵇ_{P}` still have all cohomology
objects in `P`. -/
private noncomputable def truncLTHomologyIsoOfLt
    (X : Dᵇ_{P}) (n i : ℤ) (hi : i < n) :
    (H i).obj ((t.truncLT n).obj X.obj.obj) ≅ (H i).obj X.obj.obj := by
  -- Proof comment: below the truncation bound, the canonical map `τ_{< n} X ⟶ X` is a
  -- homology isomorphism in degree `i`.
  letI :
      IsIso ((H i).map ((t.truncLTι n).app X.obj.obj)) :=
    truncLTHomologyMapIsIsoOfLt (A := A) X.obj.obj i n hi
  exact asIso ((H i).map ((t.truncLTι n).app X.obj.obj))

omit [P.IsWeakSerreClass] in
/-- Helper for Lemma 13.28.5: upper truncations of local bounded-derived objects have zero
cohomology in degrees at or above the cutoff. -/
private theorem truncLTHomologyIsZeroOfGe
    (X : Dᵇ_{P}) (n i : ℤ) (hni : n ≤ i) :
    IsZero ((H i).obj ((t.truncLT n).obj X.obj.obj)) := by
  -- Proof comment: `τ_{< n} X` is always bounded above by `n - 1`, so degree `i ≥ n`
  -- cohomology vanishes.
  let _ : ((t.truncLT n).obj X.obj.obj).IsLE (n - 1) := by
    simpa using (inferInstance : ((t.truncLT n).obj X.obj.obj).IsLE (n - 1))
  exact DerivedCategory.isZero_of_isLE _ (n - 1) i (by omega)

/-- Helper for Lemma 13.28.5: upper truncations of objects of `Dᵇ_{P}` still have all cohomology
objects in `P`. -/
private theorem truncLT_obj_mem_derivedCategoryBoundedCohomologyInProperty
    (X : Dᵇ_{P}) (n : ℤ) :
    derivedCategoryBoundedCohomologyInProperty P
      (weakSerreBoundedTruncLTObject (A := A) (P := P) X n) := by
  -- Route correction: isolate the ambient truncation-homology comparison before proving the
  -- object-property target, so the local `Dᵇ_{P}` packaging stays out of the transport step.
  intro i
  by_cases hi : i < n
  · -- Proof comment: below the cutoff, compare `H^i(τ_{< n} X)` with `H^i(X)` and transport
    -- the existing `P`-membership of `X`.
    have hXi : P ((H i).obj X.obj.obj) := by
      simpa [derivedCategoryBoundedCohomologyInProperty, derivedCategoryCohomologyInProperty,
        Functor.comp_obj] using X.property i
    simpa [derivedCategoryBoundedCohomologyInProperty, derivedCategoryCohomologyInProperty,
      Functor.comp_obj, weakSerreBoundedTruncLTObject] using
        P.prop_of_iso
          (truncLTHomologyIsoOfLt (A := A) (P := P) X n i hi).symm hXi
  · have hni : n ≤ i := by
      omega
    -- Proof comment: at or above the cutoff, the truncation has zero cohomology, hence lies in
    -- any weak Serre subcategory via `prop_of_isZero`.
    simpa [derivedCategoryBoundedCohomologyInProperty, derivedCategoryCohomologyInProperty,
      Functor.comp_obj, weakSerreBoundedTruncLTObject] using
        P.prop_of_isZero
          (truncLTHomologyIsZeroOfGe (A := A) (P := P) X n i hni)

/-- Helper for Lemma 13.28.5: the upper truncation of a local bounded-derived object, viewed again
inside `Dᵇ_{P}`. -/
private abbrev weakSerreTruncLTObject
    (X : Dᵇ_{P}) (i : ℤ) : Dᵇ_{P} :=
  ⟨weakSerreBoundedTruncLTObject (A := A) (P := P) X i,
    truncLT_obj_mem_derivedCategoryBoundedCohomologyInProperty (A := A) (P := P) X i⟩

/-- Helper for Lemma 13.28.5: the bounded truncation-step triangle attached to an object of
`Dᵇ_{P}`, viewed in `Dᵇ(A)`. -/
private noncomputable def weakSerreBoundedTruncLTStepTriangle
    (X : Dᵇ_{P}) (c : ℤ) :
    Triangle (Dᵇ(A)) :=
  let T := _root_.truncLE_step_homologyTriangle (𝒜 := A) X.obj.obj c
  let X₁ : Dᵇ(A) := weakSerreBoundedTruncLTObject (A := A) (P := P) X (c + 1)
  let X₂ : Dᵇ(A) := weakSerreBoundedTruncLTObject (A := A) (P := P) X (c + 2)
  let X₃ : Dᵇ(A) :=
    ⟨(DerivedCategory.singleFunctor A (c + 1)).obj
        ((derivedBoundedWithCohomologyInHomologyFunctor P (c + 1)).obj X).obj,
      singleFunctor_obj_mem_boundedDerivedCategory_degree (A := A)
        (((derivedBoundedWithCohomologyInHomologyFunctor P (c + 1)).obj X).obj) (c + 1)⟩
  Triangle.mk
    ((ObjectProperty.homMk (X := X₁) (Y := X₂) T.mor₁) : X₁ ⟶ X₂)
    ((ObjectProperty.homMk (X := X₂) (Y := X₃) T.mor₂) : X₂ ⟶ X₃)
    ((ObjectProperty.homMk
        (X := X₃) (Y := X₁⟦(1 : ℤ)⟧)
        (T.mor₃ ≫ ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).inv.app X₁)) :
      X₃ ⟶ X₁⟦(1 : ℤ)⟧)

omit [P.IsWeakSerreClass] in
/-- Helper for Lemma 13.28.5: after forgetting the bounded truncation-step triangle to `D(A)`,
the inserted bounded `commShiftIso` on the third edge cancels. -/
private theorem boundedTruncLTStepTriangleThirdEdgeFlatten
    (X : Dᵇ_{P}) (c : ℤ) :
    (((truncLE_step_homologyTriangle X.obj.obj c).mor₃ ≫
          ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).inv.app
            ⟨(t.truncLT (c + 1)).obj X.obj.obj,
              truncLT_obj_mem_boundedDerivedCategory (A := A) (P := P) X (c + 1)⟩) ≫
        ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).hom.app
          ⟨(t.truncLT (c + 1)).obj X.obj.obj,
            truncLT_obj_mem_boundedDerivedCategory (A := A) (P := P) X (c + 1)⟩) ≫
      (shiftFunctor (D(A)) (1 : ℤ)).map (𝟙 ((t.truncLT (c + 1)).obj X.obj.obj)) =
        𝟙 ((DerivedCategory.singleFunctor A (c + 1)).obj
          ((homologyFunctor A (c + 1)).obj X.obj.obj)) ≫
            (truncLE_step_homologyTriangle X.obj.obj c).mor₃ := by
  let T := _root_.truncLE_step_homologyTriangle (𝒜 := A) X.obj.obj c
  let X₁ : Dᵇ(A) := weakSerreBoundedTruncLTObject (A := A) (P := P) X (c + 1)
  -- Proof comment: first cancel the bounded `commShiftIso`, then rewrite the remaining identity
  -- morphism as a left identity on the raw third morphism.
  have hcomm :
      T.mor₃ ≫
          ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).inv.app X₁ ≫
            ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).hom.app X₁ ≫
            (shiftFunctor (D(A)) (1 : ℤ)).map (𝟙 X₁.obj) =
        T.mor₃ ≫ 𝟙 ((shiftFunctor (D(A)) (1 : ℤ)).obj X₁.obj) := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ T.mor₃ ≫ k ≫ (shiftFunctor (D(A)) (1 : ℤ)).map (𝟙 X₁.obj))
        (((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).inv_hom_id_app X₁)
  have hcomm' :
      (truncLE_step_homologyTriangle X.obj.obj c).mor₃ ≫
          ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).inv.app X₁ ≫
            ((ObjectProperty.ι t.bounded).commShiftIso (1 : ℤ)).hom.app X₁ ≫
            (shiftFunctor (D(A)) (1 : ℤ)).map (𝟙 X₁.obj) =
        (truncLE_step_homologyTriangle X.obj.obj c).mor₃ ≫
          𝟙 ((shiftFunctor (D(A)) (1 : ℤ)).obj X₁.obj) := by
    simpa [T, Category.assoc] using hcomm
  have htail' :
      (truncLE_step_homologyTriangle X.obj.obj c).mor₃ ≫
          𝟙 ((shiftFunctor (D(A)) (1 : ℤ)).obj X₁.obj) =
        𝟙 ((DerivedCategory.singleFunctor A (c + 1)).obj
          ((homologyFunctor A (c + 1)).obj X.obj.obj)) ≫
            (truncLE_step_homologyTriangle X.obj.obj c).mor₃ := by
    have hid :
        (truncLE_step_homologyTriangle X.obj.obj c).mor₃ =
          𝟙 ((DerivedCategory.singleFunctor A (c + 1)).obj
            ((homologyFunctor A (c + 1)).obj X.obj.obj)) ≫
              (truncLE_step_homologyTriangle X.obj.obj c).mor₃ := by
      simpa [T, X₁, weakSerreBoundedTruncLTObject,
        derivedBoundedWithCohomologyInHomologyFunctor] using
        (Category.id_comp (truncLE_step_homologyTriangle X.obj.obj c).mor₃).symm
    exact (Category.comp_id (truncLE_step_homologyTriangle X.obj.obj c).mor₃).trans hid
  simpa [X₁] using hcomm'.trans htail'

omit [P.IsWeakSerreClass] in
/-- Helper for Lemma 13.28.5: the bounded truncation-step triangle attached to an object of
`Dᵇ_{P}` is distinguished in `Dᵇ(A)`. -/
private theorem weakSerreBoundedTruncLTStepTriangle_distinguished
    (X : Dᵇ_{P}) (c : ℤ) :
    weakSerreBoundedTruncLTStepTriangle (A := A) (P := P) X c ∈ distTriang (Dᵇ(A)) := by
  let T := _root_.truncLE_step_homologyTriangle (𝒜 := A) X.obj.obj c
  -- Route correction: transport the owner truncation-step triangle to `Dᵇ(A)` first, then
  -- cancel only the inserted bounded `commShiftIso` on the third edge.
  rw [← (ObjectProperty.ι t.bounded).map_distinguished_iff]
  refine isomorphic_distinguished _
    (_root_.truncLE_step_homology_triangle (𝒜 := A) X.obj.obj c) _ ?_
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · -- Proof comment: the first edge is the truncation inclusion itself.
    exact (Category.comp_id T.mor₁).trans (Category.id_comp T.mor₁).symm
  · -- Proof comment: the second edge is the owner morphism to the single-degree term.
    exact (Category.comp_id T.mor₂).trans (Category.id_comp T.mor₂).symm
  · -- Proof comment: the third edge differs only by the bounded shift-commutation isomorphism.
    exact boundedTruncLTStepTriangleThirdEdgeFlatten (A := A) (P := P) X c

/-- Helper for Lemma 13.28.5: the truncation-step triangle for `X` inside the local category
`Dᵇ_{P}`. -/
private noncomputable def derivedBoundedWithCohomologyInTruncLTStepTriangle
    (X : Dᵇ_{P}) (c : ℤ) :
    Triangle (Dᵇ_{P}) :=
  let T := weakSerreBoundedTruncLTStepTriangle (A := A) (P := P) X c
  let X₁ : Dᵇ_{P} := weakSerreTruncLTObject (A := A) (P := P) X (c + 1)
  let X₂ : Dᵇ_{P} := weakSerreTruncLTObject (A := A) (P := P) X (c + 2)
  let X₃ : Dᵇ_{P} :=
    weakSerreSingleDerivedDegree (A := A) (P := P)
      ((derivedBoundedWithCohomologyInHomologyFunctor P (c + 1)).obj X) (c + 1)
  Triangle.mk
    ((ObjectProperty.homMk (X := X₁) (Y := X₂) T.mor₁) : X₁ ⟶ X₂)
    ((ObjectProperty.homMk (X := X₂) (Y := X₃) T.mor₂) : X₂ ⟶ X₃)
    ((((derivedCategoryBoundedCohomologyInProperty P).ι).preimage
        (T.mor₃ ≫ (((derivedCategoryBoundedCohomologyInProperty P).ι).commShiftIso
          (1 : ℤ)).inv.app X₁)) : X₃ ⟶ X₁⟦(1 : ℤ)⟧)

/-- Helper for Lemma 13.28.5: after forgetting the local truncation-step triangle to `Dᵇ(A)`,
the inserted local `commShiftIso` on the third edge cancels. -/
private theorem localTruncLTStepTriangleThirdEdgeFlatten
    (X : Dᵇ_{P}) (c : ℤ) :
    let T := weakSerreBoundedTruncLTStepTriangle (A := A) (P := P) X c
    T.mor₃ ≫
        (((derivedCategoryBoundedCohomologyInProperty P).ι).commShiftIso
          (1 : ℤ)).inv.app
            (weakSerreTruncLTObject (A := A) (P := P) X (c + 1)) ≫
          (((derivedCategoryBoundedCohomologyInProperty P).ι).commShiftIso
            (1 : ℤ)).hom.app
              (weakSerreTruncLTObject (A := A) (P := P) X (c + 1)) ≫
          (shiftFunctor (Dᵇ(A)) (1 : ℤ)).map
            (𝟙 (weakSerreBoundedTruncLTObject (A := A) (P := P) X (c + 1))) =
      𝟙 ((weakSerreBoundedTruncLTStepTriangle (A := A) (P := P) X c).obj₃) ≫ T.mor₃ := by
  let T := weakSerreBoundedTruncLTStepTriangle (A := A) (P := P) X c
  let X₁ : Dᵇ_{P} := weakSerreTruncLTObject (A := A) (P := P) X (c + 1)
  -- Proof comment: first cancel the local `commShiftIso`, then replace the remaining identity by
  -- a left identity on the ambient third edge.
  have hcomm :
      T.mor₃ ≫
          (((derivedCategoryBoundedCohomologyInProperty P).ι).commShiftIso
            (1 : ℤ)).inv.app X₁ ≫
            (((derivedCategoryBoundedCohomologyInProperty P).ι).commShiftIso
              (1 : ℤ)).hom.app X₁ ≫
            (shiftFunctor (Dᵇ(A)) (1 : ℤ)).map (𝟙 X₁.obj) =
        T.mor₃ ≫ 𝟙 ((shiftFunctor (Dᵇ(A)) (1 : ℤ)).obj X₁.obj) := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ T.mor₃ ≫ k ≫ (shiftFunctor (Dᵇ(A)) (1 : ℤ)).map (𝟙 X₁.obj))
        ((((derivedCategoryBoundedCohomologyInProperty P).ι).commShiftIso
          (1 : ℤ)).inv_hom_id_app X₁)
  have htail :
      T.mor₃ ≫ 𝟙 ((shiftFunctor (Dᵇ(A)) (1 : ℤ)).obj X₁.obj) =
        𝟙 ((weakSerreBoundedTruncLTStepTriangle (A := A) (P := P) X c).obj₃) ≫ T.mor₃ := by
    calc
      T.mor₃ ≫ 𝟙 ((shiftFunctor (Dᵇ(A)) (1 : ℤ)).obj X₁.obj) = T.mor₃ := by
        exact Category.comp_id T.mor₃
      _ = 𝟙 ((weakSerreBoundedTruncLTStepTriangle (A := A) (P := P) X c).obj₃) ≫ T.mor₃ := by
        simpa [weakSerreBoundedTruncLTStepTriangle] using (Category.id_comp T.mor₃).symm
  simpa [X₁, weakSerreTruncLTObject] using hcomm.trans htail

/-- Helper for Lemma 13.28.5: the local truncation-step triangle is distinguished in `Dᵇ_{P}`. -/
private theorem derivedBoundedWithCohomologyInTruncLTStepTriangle_distinguished
    (X : Dᵇ_{P}) (c : ℤ) :
    derivedBoundedWithCohomologyInTruncLTStepTriangle (A := A) (P := P) X c ∈
      distTriang (Dᵇ_{P}) := by
  let T := weakSerreBoundedTruncLTStepTriangle (A := A) (P := P) X c
  let X₁ : Dᵇ_{P} := weakSerreTruncLTObject (A := A) (P := P) X (c + 1)
  let X₂ : Dᵇ_{P} := weakSerreTruncLTObject (A := A) (P := P) X (c + 2)
  let X₃ : Dᵇ_{P} :=
    weakSerreSingleDerivedDegree (A := A) (P := P)
      ((derivedBoundedWithCohomologyInHomologyFunctor P (c + 1)).obj X) (c + 1)
  -- Proof comment: forget the local triangle to `Dᵇ(A)`, compare it with the ambient bounded
  -- truncation-step triangle, and express the third edge in the exact `Triangle.isoMk` spelling.
  rw [← ((derivedCategoryBoundedCohomologyInProperty P).ι).map_distinguished_iff]
  dsimp [derivedBoundedWithCohomologyInTruncLTStepTriangle]
  refine isomorphic_distinguished _
    (weakSerreBoundedTruncLTStepTriangle_distinguished (A := A) (P := P) X c) _ ?_
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · -- Proof comment: the first edge is the ambient truncation inclusion.
    exact (Category.comp_id T.mor₁).trans (Category.id_comp T.mor₁).symm
  · -- Proof comment: the second edge is the ambient map to the single-degree cohomology term.
    exact (Category.comp_id T.mor₂).trans (Category.id_comp T.mor₂).symm
  · -- Proof comment: the third edge is the transported ambient third edge with the local
    -- `commShiftIso` cancelled once after rewriting through `map_preimage`.
    simpa using
      localTruncLTStepTriangleThirdEdgeFlatten (A := A) (P := P) X c

/-- Helper for Lemma 13.28.5: one local truncation-step triangle rewrites the next truncation
class as the previous truncation class plus the signed degree-`c+1` cohomology term. -/
private theorem triangulatedK0_of_weakSerreTruncLT_step_homMk
    (X : Dᵇ_{P}) (c : ℤ) :
    TriangulatedK0.of (weakSerreTruncLTObject (A := A) (P := P) X (c + 2)) =
      TriangulatedK0.of (weakSerreTruncLTObject (A := A) (P := P) X (c + 1)) +
        weakSerreToDerivedBoundedK0 P
          ((c + 1).negOnePow •
            K₀[((derivedBoundedWithCohomologyInHomologyFunctor P (c + 1)).obj X)]) := by
  have hT :
      TriangulatedK0.of
          ((derivedBoundedWithCohomologyInTruncLTStepTriangle (A := A) (P := P) X c).obj₂) =
        TriangulatedK0.of
            ((derivedBoundedWithCohomologyInTruncLTStepTriangle (A := A) (P := P) X c).obj₁) +
          TriangulatedK0.of
            ((derivedBoundedWithCohomologyInTruncLTStepTriangle (A := A) (P := P) X c).obj₃) := by
    exact
      TriangulatedK0.of_distinguished
        (derivedBoundedWithCohomologyInTruncLTStepTriangle (A := A) (P := P) X c)
        (derivedBoundedWithCohomologyInTruncLTStepTriangle_distinguished (A := A) (P := P) X c)
  -- Proof comment: apply the distinguished-triangle relation to the local truncation step and
  -- rewrite the single-degree third vertex via the signed degree-zero embedding formula.
  calc
    TriangulatedK0.of (weakSerreTruncLTObject (A := A) (P := P) X (c + 2)) =
      TriangulatedK0.of (weakSerreTruncLTObject (A := A) (P := P) X (c + 1)) +
        TriangulatedK0.of
          (weakSerreSingleDerivedDegree (A := A) (P := P)
            ((derivedBoundedWithCohomologyInHomologyFunctor P (c + 1)).obj X) (c + 1)) := by
            simpa [derivedBoundedWithCohomologyInTruncLTStepTriangle] using hT
    _ =
      TriangulatedK0.of (weakSerreTruncLTObject (A := A) (P := P) X (c + 1)) +
        weakSerreToDerivedBoundedK0 P
          ((c + 1).negOnePow •
            K₀[((derivedBoundedWithCohomologyInHomologyFunctor P (c + 1)).obj X)]) := by
              rw [triangulatedK0_of_weakSerreSingleDerivedDegree]

/-- Helper for Lemma 13.28.5: one truncation step contributes the signed degree-`i` cohomology
class in `K₀(Dᵇ_{P})`. -/
private theorem weakSerreToDerivedBoundedK0_homologyStep
    (X : Dᵇ_{P}) (i : ℤ) :
    weakSerreToDerivedBoundedK0 P
        (i.negOnePow • K₀[((derivedBoundedWithCohomologyInHomologyFunctor P i).obj X)]) =
      TriangulatedK0.of (weakSerreTruncLTObject (A := A) (P := P) X (i + 1)) -
        TriangulatedK0.of (weakSerreTruncLTObject (A := A) (P := P) X i) := by
  let F₀ : TriangulatedK0 (Dᵇ_{P}) :=
    TriangulatedK0.of (weakSerreTruncLTObject (A := A) (P := P) X i)
  let F₁ : TriangulatedK0 (Dᵇ_{P}) :=
    TriangulatedK0.of (weakSerreTruncLTObject (A := A) (P := P) X (i + 1))
  let G : TriangulatedK0 (Dᵇ_{P}) :=
    weakSerreToDerivedBoundedK0 P
      (i.negOnePow • K₀[((derivedBoundedWithCohomologyInHomologyFunctor P i).obj X)])
  have hStep : F₁ = F₀ + G := by
    simpa [F₀, F₁, G, show i - 1 + 2 = i + 1 by omega, show i - 1 + 1 = i by omega] using
      triangulatedK0_of_weakSerreTruncLT_step_homMk (A := A) (P := P) X (i - 1)
  have hCancel : G = F₁ - F₀ := by
    calc
      G = (F₀ + G) - F₀ := by
        dsimp [F₀]
        abel
      _ = F₁ - F₀ := by
        rw [hStep]
  -- Proof comment: rewrite the step relation in difference form by canceling the previous
  -- truncation class.
  simpa [F₀, F₁, G] using hCancel

/-- Helper for Lemma 13.28.5: a consecutive sum of truncation-step differences telescopes. -/
private theorem sum_Icc_truncLT_steps
    {G : Type*} [AddCommGroup G] (F : ℤ → G) {a b : ℤ} (hab : a ≤ b) :
    Finset.sum (Finset.Icc a b) (fun i ↦ F (i + 1) - F i) = F (b + 1) - F a := by
  let n : ℕ := Int.toNat (b - a)
  have hb : b = a + n := by
    dsimp [n]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
    omega
  rw [hb]
  induction n with
  | zero =>
      -- Proof comment: the singleton interval contributes exactly the base step.
      simp
  | succ n ih =>
      -- Proof comment: split off the top endpoint and telescope the remaining interval by the
      -- induction hypothesis.
      have hIco :
          Finset.Ico a (a + ↑(n + 1)) = Finset.Icc a (a + ↑n) := by
        rw [show a + ↑(n + 1) = a + ↑n + 1 by omega, Finset.Ico_add_one_right_eq_Icc]
      have hs : a + ↑n + 1 = a + ↑(n + 1) := by
        omega
      rw [Finset.Icc_eq_cons_Ico (by omega), Finset.sum_cons, hIco]
      calc
        (F (a + ↑(n + 1) + 1) - F (a + ↑(n + 1))) +
            Finset.sum (Finset.Icc a (a + ↑n)) (fun i ↦ F (i + 1) - F i) =
          (F (a + ↑(n + 1) + 1) - F (a + ↑(n + 1))) +
            (F (a + ↑n + 1) - F a) := by
              rw [ih]
        _ = (F (a + ↑(n + 1) + 1) - F (a + ↑(n + 1))) +
              (F (a + ↑(n + 1)) - F a) := by
                rw [hs]
        _ = F (a + ↑(n + 1) + 1) - F a := by
              abel

/-- Helper for Lemma 13.28.5: applying the degree-zero embedding to the Euler class of an object
of `Dᵇ_{P}` recovers its class in `K₀(Dᵇ_{P})`. -/
private theorem derivedBoundedWithCohomologyInEulerClass_embedsBack
    (X : Dᵇ_{P}) :
    weakSerreToDerivedBoundedK0 P (derivedBoundedWithCohomologyInEulerClass P X) =
      TriangulatedK0.of X := by
  -- Route correction: mirror the bounded-derived telescope proof, but pull the two endpoint
  -- identifications back through the local fully faithful inclusion only once.
  rcases (derivedCategory_t_bounded_iff X.obj.obj).1 X.obj.property with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  let a' : ℤ := min a b
  let b' : ℤ := max a b
  let F : ℤ → TriangulatedK0 (Dᵇ_{P}) := fun i ↦
    TriangulatedK0.of (weakSerreTruncLTObject (A := A) (P := P) X i)
  have hab' : a' ≤ b' := by
    dsimp [a', b']
    exact min_le_max
  have hvanish :
      ∀ n : ℤ, n ∉ Set.Icc a' b' →
        IsZero ((derivedBoundedWithCohomologyInHomologyFunctor P n).obj X) := by
    intro n hn
    by_cases hna : n < a'
    · -- Proof comment: below the lower bound, ambient cohomology vanishes and so does its
      -- weak-Serre lift.
      have hna_a : n < a := by
        dsimp [a'] at hna
        omega
      exact weakSerre_isZero_of_underlying_isZero (P := P) _ (ha n hna_a)
    · have hna' : a' ≤ n := by
        omega
      have hnb' : b' < n := by
        by_contra hle
        exact hn ⟨hna', by omega⟩
      -- Proof comment: above the upper bound, the same ambient vanishing argument applies.
      have hnb_b : b < n := by
        dsimp [b'] at hnb'
        omega
      exact weakSerre_isZero_of_underlying_isZero (P := P) _ (hb n hnb_b)
  have hsum :
      derivedBoundedWithCohomologyInEulerClass P X =
        Finset.sum (Finset.Icc a' b')
          (fun i ↦ i.negOnePow •
            K₀[((derivedBoundedWithCohomologyInHomologyFunctor P i).obj X)]) := by
    exact
      derivedBoundedWithCohomologyInEulerClass_eq_sum_of_vanishingOutside
        (A := A) (P := P) X hvanish
  have hGE' : X.obj.obj.IsGE a' := by
    rw [DerivedCategory.isGE_iff]
    intro n hn
    have hna : n < a := by
      dsimp [a'] at hn
      omega
    exact ha n hna
  have hLE' : X.obj.obj.IsLE b' := by
    rw [DerivedCategory.isLE_iff]
    intro n hn
    have hnb : b < n := by
      dsimp [b'] at hn
      omega
    exact hb n hnb
  have hleftZeroObj :
      IsZero ((t.truncLT a').obj X.obj.obj) := by
    exact (t.isGE_iff_isZero_truncLT_obj a' X.obj.obj).1 hGE'
  have hleftZero :
      F a' = 0 := by
    have hzeroSub :
        IsZero (((derivedCategoryBoundedCohomologyInProperty P).ι).obj (0 : Dᵇ_{P})) :=
      Functor.map_isZero ((derivedCategoryBoundedCohomologyInProperty P).ι) (isZero_zero (Dᵇ_{P}))
    let eAmbient :
        ((derivedCategoryBoundedCohomologyInProperty P).ι).obj
            (weakSerreTruncLTObject (A := A) (P := P) X a') ≅
          ((derivedCategoryBoundedCohomologyInProperty P).ι).obj (0 : Dᵇ_{P}) := by
      exact
        (Functor.FullyFaithful.ofFullyFaithful (ObjectProperty.ι t.bounded)).preimageIso
            (hleftZeroObj.isoZero ≪≫
              (Functor.map_isZero (ObjectProperty.ι t.bounded)
                (isZero_zero (Dᵇ(A)))).isoZero.symm) ≪≫
          hzeroSub.isoZero.symm
    let e :
        weakSerreTruncLTObject (A := A) (P := P) X a' ≅ (0 : Dᵇ_{P}) :=
      (Functor.FullyFaithful.ofFullyFaithful
        ((derivedCategoryBoundedCohomologyInProperty P).ι)).preimageIso eAmbient
    -- Proof comment: the lower truncation is zero once `X` is already bounded below by `a'`.
    calc
      F a' = TriangulatedK0.of (0 : Dᵇ_{P}) := by
        exact triangulatedK0_of_eq_of_iso (A := A) (P := P) e
      _ = 0 := triangulatedK0_of_zero_eq (A := A) (P := P)
  have hright :
      F (b' + 1) = TriangulatedK0.of X := by
    let eBoundedAmbient :
        (ObjectProperty.ι t.bounded).obj
            (weakSerreBoundedTruncLTObject (A := A) (P := P) X (b' + 1)) ≅
          (ObjectProperty.ι t.bounded).obj X.obj :=
      @asIso _ _ _ _
        ((t.truncLTι (b' + 1)).app X.obj.obj)
        ((t.isLE_iff_isIso_truncLTι_app b' (b' + 1) (by omega) X.obj.obj).1 hLE')
    let eBounded :
        weakSerreBoundedTruncLTObject (A := A) (P := P) X (b' + 1) ≅ X.obj :=
      (Functor.FullyFaithful.ofFullyFaithful (ObjectProperty.ι t.bounded)).preimageIso
        eBoundedAmbient
    let e :
        weakSerreTruncLTObject (A := A) (P := P) X (b' + 1) ≅ X :=
      (Functor.FullyFaithful.ofFullyFaithful
        ((derivedCategoryBoundedCohomologyInProperty P).ι)).preimageIso eBounded
    -- Proof comment: the upper truncation agrees with `X` once `X` is already bounded above by
    -- `b'`.
    exact triangulatedK0_of_eq_of_iso (A := A) (P := P) e
  calc
    weakSerreToDerivedBoundedK0 P (derivedBoundedWithCohomologyInEulerClass P X) =
      weakSerreToDerivedBoundedK0 P
        (Finset.sum (Finset.Icc a' b')
          (fun i ↦ i.negOnePow •
            K₀[((derivedBoundedWithCohomologyInHomologyFunctor P i).obj X)])) := by
              rw [hsum]
    _ = Finset.sum (Finset.Icc a' b')
          (fun i ↦ weakSerreToDerivedBoundedK0 P
            (i.negOnePow • K₀[((derivedBoundedWithCohomologyInHomologyFunctor P i).obj X)])) := by
              simp [map_sum]
    _ = Finset.sum (Finset.Icc a' b') (fun i ↦ F (i + 1) - F i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact weakSerreToDerivedBoundedK0_homologyStep (A := A) (P := P) X i
    _ = F (b' + 1) - F a' := sum_Icc_truncLT_steps F hab'
    _ = TriangulatedK0.of X - 0 := by
          rw [hright, hleftZero]
    _ = TriangulatedK0.of X := by
          simp

-- Proof sketch: use the truncation triangles from Remark 13.12.4 to express the class of a
-- bounded derived object as the alternating sum of the classes of its shifted cohomology objects;
-- this is the same expression used by `derivedBoundedWithCohomologyInEulerK0`.
/-- The degree-zero embedding on `K₀(P)` is a right inverse to the Euler-characteristic map on
`K₀(Dᵇ_{P})`. -/
theorem weakSerreToDerivedBoundedK0_rightInverse :
    Function.RightInverse
      (derivedBoundedWithCohomologyInEulerK0 P)
      (weakSerreToDerivedBoundedK0 P) := by
  -- Proof comment: once the objectwise truncation telescope is proved, descend it through the
  -- quotient presentation of `TriangulatedK0 (Dᵇ_{P})`.
  intro x
  refine Quotient.inductionOn x ?_
  intro z
  induction z using FreeAbelianGroup.induction_on with
  | zero =>
      simp
  | of X =>
      -- Proof comment: evaluate the Euler map on the generator `[X]` and apply the objectwise
      -- truncation theorem.
      calc
        weakSerreToDerivedBoundedK0 P
            (derivedBoundedWithCohomologyInEulerK0 P (TriangulatedK0.of X)) =
              weakSerreToDerivedBoundedK0 P
                (derivedBoundedWithCohomologyInEulerClass P X) := by
                  rw [derivedBoundedWithCohomologyInEulerK0_apply_of]
        _ = TriangulatedK0.of X :=
          derivedBoundedWithCohomologyInEulerClass_embedsBack (A := A) (P := P) X
  | neg z ih =>
      simpa using congrArg Neg.neg ih
  | add z w ihz ihw =>
      simpa [map_add] using congrArg₂ HAdd.hAdd ihz ihw

/-- Lemma 13.28.5: for a weak Serre subcategory `P` of an abelian category `A`, the canonical map
`K₀(P) → K₀(Dᵇ_{P})` sending `[X]` to `[X[0]]` is an isomorphism. Its inverse sends the class
of `X` to the alternating sum `\sum_i (-1)^i [H^i(X)]`. -/
@[stacks 0FCS]
noncomputable def weakSerreSubcategoryK0EquivDerivedBoundedWithCohomologyIn :
    AbelianK0 P.FullSubcategory ≃+ TriangulatedK0 (Dᵇ_{P}) where
  toFun := weakSerreToDerivedBoundedK0 P
  invFun := derivedBoundedWithCohomologyInEulerK0 P
  left_inv := weakSerreToDerivedBoundedK0_leftInverse P
  right_inv := weakSerreToDerivedBoundedK0_rightInverse P
  map_add' := (weakSerreToDerivedBoundedK0 P).map_add

-- Proof sketch: this is the `toFun` field of
-- `weakSerreSubcategoryK0EquivDerivedBoundedWithCohomologyIn`, evaluated on the generator class
-- `AbelianK0.of X`.
/-- The canonical equivalence sends the class of `X` to the class of the degree-zero object
`X[0]` in `Dᵇ_{P}`. -/
theorem weakSerreSubcategoryK0EquivDerivedBoundedWithCohomologyIn_apply_of
    (X : P.FullSubcategory) :
    weakSerreSubcategoryK0EquivDerivedBoundedWithCohomologyIn P K₀[X] =
      TriangulatedK0.of ((weakSerreSingleFunctorToDerivedBounded P).obj X) :=
  weakSerreToDerivedBoundedK0_apply_of P X

-- Proof sketch: this is the `invFun` field of
-- `weakSerreSubcategoryK0EquivDerivedBoundedWithCohomologyIn`, evaluated on the class of `X`;
-- the value is exactly the defining Euler characteristic formula.
/-- The inverse equivalence sends the class of `X` to the alternating sum of the classes of the
cohomology objects `H^i(X)`. -/
theorem weakSerreSubcategoryK0EquivDerivedBoundedWithCohomologyIn_symm_apply_of
    (X : Dᵇ_{P}) :
    (weakSerreSubcategoryK0EquivDerivedBoundedWithCohomologyIn P).symm (TriangulatedK0.of X) =
      derivedBoundedWithCohomologyInEulerClass P X :=
  derivedBoundedWithCohomologyInEulerK0_apply_of P X

end WeakSerreBoundedDerivedK0

end CategoryTheory
