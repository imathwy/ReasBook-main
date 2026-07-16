import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_11_1
import StacksProject_2024.stacks_project.Chap12.Lemma_12_11_3
import StacksProject_2024.stacks_project.Chap13.Definition_13_28_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_6_4

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling for Lemma 13.28.4:
- primary domain: triangulated Grothendieck groups and homological functors to abelian categories;
- sampled owner declarations:
  `Functor.IsHomological`,
  `Functor.shiftVanishingBounded`,
  `Functor.mem_shiftVanishingBounded_iff`,
  `Functor.ShiftSequence.tautological`,
  `CategoryTheory.TriangulatedK0`,
  `CategoryTheory.TriangulatedK0.of`,
  `CategoryTheory.TriangulatedK0.lift`;
- source-facing layer: Lemma 13.28.4 constructs the Euler-characteristic map on `K₀` attached to a
  homological functor with finite shift support;
- core/canonical owners: the owner functor `H`, the chapter-level object property
  `H.shiftVanishingBounded`, the global pointwise boundedness hypothesis
  `∀ X, H.shiftVanishingBounded X`, the quotient owner
  `CategoryTheory.TriangulatedK0`, and its class map `CategoryTheory.TriangulatedK0.of`;
- bridge/view: the passage from the global boundedness hypothesis to the finite support of the
  alternating Euler summand, and then to the class-evaluation formula for the induced map.

Primitive data split into two layers:
- source-facing global input for the `K₀` map: the pointwise boundedness hypothesis
  `∀ X, H.shiftVanishingBounded X`;
- objectwise support control is derived API, expressed canonically by the companion theorem
  `eulerClass_hasFiniteSupport` for the alternating summand
  `fun i ↦ i.negOnePow • K₀[(H.shift i).obj X]`.
The raw free-abelian-group lift and the quotient-descending kernel argument are derived
implementation data, so they should not remain part of the public surface. Since the main
constructions are attached to the functor itself, the public API should live under the owner
namespace `Functor`, with the object-level Euler class given intrinsically by `∑ᶠ` and the `K₀`
map consuming the global containment hypothesis.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ZeroObject
open scoped BigOperators

noncomputable section

namespace CategoryTheory

universe u₁ u₂ v₁ v₂

namespace Functor

section EulerClass

variable {D : Type u₁} [Category.{v₁} D] [HasShift D ℤ]
variable {A : Type u₂} [Category.{v₂} A] [Abelian A]
variable (H : D ⥤ A) [H.ShiftSequence ℤ]

/-- If `X` lies in the bounded shift-vanishing owner for `H`, then the corresponding alternating
Euler-class summand has finite support. -/
theorem eulerClass_hasFiniteSupport (X : D) (hX : H.shiftVanishingBounded X) :
    Function.HasFiniteSupport
      (fun i : ℤ ↦ i.negOnePow • K₀[(H.shift i).obj X]) := by
  -- Proof comment: bounded shift-vanishing gives a symmetric finite interval containing every
  -- potentially nonzero Euler summand.
  rcases (Functor.mem_shiftVanishingBounded_iff H X).1 hX with ⟨N, hN⟩
  rw [Function.HasFiniteSupport]
  refine (Finset.Icc (-(N : ℤ)) N).finite_toSet.subset ?_
  intro i hi
  by_contra hmem
  have hnatAbs : N ≤ Int.natAbs i := by
    have hnatAbs' : (N : ℤ) ≤ (Int.natAbs i : ℤ) := by
      have hmem' : ¬ (-(N : ℤ) ≤ i ∧ i ≤ (N : ℤ)) := by
        simpa [Set.mem_Icc] using hmem
      by_cases hnonneg : 0 ≤ i
      · rw [Int.ofNat_natAbs_of_nonneg hnonneg]
        omega
      · have hnonpos : i ≤ 0 := by omega
        rw [Int.ofNat_natAbs_of_nonpos hnonpos]
        omega
    exact_mod_cast hnatAbs'
  have hzeroObj : IsZero ((H.shift i).obj X) := by
    exact (hN i hnatAbs).of_iso ((H.isoShift i).app X).symm
  have hk0 :
      K₀[(H.shift i).obj X] = 0 := by
    calc
      K₀[(H.shift i).obj X] = K₀[(0 : A)] := by
        exact _root_.CategoryTheory.ObjectProperty.k0_eq_of_iso (A := A) hzeroObj.isoZero
      _ = 0 := _root_.CategoryTheory.ObjectProperty.k0_zero_eq (A := A)
  have hi_ne :
      i.negOnePow • K₀[(H.shift i).obj X] ≠ 0 := by
    simpa [Function.mem_support] using hi
  have hi_zero : i.negOnePow • K₀[(H.shift i).obj X] = 0 := by
    simp [hk0]
  exact hi_ne hi_zero

/-- The alternating-sum Euler class attached to an object `X` and a shifted homological functor
`H`, expressed canonically as a `finsum`; finite support is supplied separately by
`eulerClass_hasFiniteSupport` when needed. -/
def eulerClass (X : D) : AbelianK0 A :=
  ∑ᶠ i : ℤ, i.negOnePow • K₀[(H.shift i).obj X]

end EulerClass

section EulerK0Map

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {A : Type u₂} [Category.{v₂} A] [Abelian A]
variable (H : D ⥤ A) [H.IsHomological] [H.ShiftSequence ℤ]

/-- Helper for Lemma 13.28.4: the zero object has trivial class in the abelian Grothendieck
group. -/
private theorem abelian_k0_zero_eq :
    K₀[(0 : A)] = 0 := by
  -- Proof comment: delegate to the canonical Chapter 12 computation of the zero class in `K₀`.
  exact _root_.CategoryTheory.ObjectProperty.k0_zero_eq (A := A)

/-- Helper for Lemma 13.28.4: isomorphic objects define the same class in the abelian
Grothendieck group. -/
private theorem abelian_k0_eq_of_iso {X Y : A} (e : X ≅ Y) :
    K₀[X] = K₀[Y] := by
  -- Proof comment: delegate to the canonical Chapter 12 invariance of `K₀` under isomorphism.
  exact _root_.CategoryTheory.ObjectProperty.k0_eq_of_iso (A := A) e

/-- Helper for Lemma 13.28.4: for any morphism, the difference of its target and source classes is
the difference of the cokernel and kernel classes. -/
private theorem k0_sub_eq_cokernel_sub_kernel {X Y : A} (f : X ⟶ Y) :
    K₀[Y] - K₀[X] = K₀[Limits.cokernel f] - K₀[Limits.kernel f] := by
  -- Proof comment: use the canonical Chapter 12 kernel-cokernel identity in `K₀(A)`.
  exact _root_.CategoryTheory.ObjectProperty.k0_sub_eq_cokernel_sub_kernel (A := A) f

/-- Helper for Lemma 13.28.4: composing with the lift into `kernel f` preserves the kernel class
in `K₀`. -/
private theorem k0_kernel_of_kernel_lift
    {X Y Z : A} (f : Y ⟶ Z) (g : X ⟶ Y) (h : g ≫ f = 0) :
    K₀[Limits.kernel (Limits.kernel.lift f g h)] = K₀[Limits.kernel g] := by
  -- Proof comment: use the canonical Chapter 12 comparison between the two kernels.
  exact _root_.CategoryTheory.ObjectProperty.k0_kernel_of_kernel_lift (A := A) f g h

/-- Helper for Lemma 13.28.4: if the source object of a morphism is zero, then the class of its
kernel vanishes in `K₀(A)`. -/
private lemma k0_kernel_eq_zero_of_isZero_source {X Y : A} (f : X ⟶ Y) (hX : IsZero X) :
    K₀[Limits.kernel f] = 0 := by
  -- Proof comment: a morphism out of a zero object is mono, so its kernel is itself zero.
  let e : X ≅ 0 := hX.isoZero
  let _ : Mono f := Limits.mono_of_source_iso_zero f e
  calc
    K₀[Limits.kernel f] = K₀[(0 : A)] := by
      exact abelian_k0_eq_of_iso (A := A) (Limits.kernel.ofMono f)
    _ = 0 := abelian_k0_zero_eq (A := A)

/-- Helper for Lemma 13.28.4: if a morphism `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₄` is exact at `X₁` and `X₂`, then
the class of `X₁` is the sum of the classes of the adjacent kernels. -/
private lemma k0_eq_kernel_add_kernel_of_exact
    {X₀ X₁ X₂ X₃ : A} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃)
    (hfg : f ≫ g = 0) (hgh : g ≫ h = 0)
    (_hex₁ : (ShortComplex.mk f g hfg).Exact) (hex₂ : (ShortComplex.mk g h hgh).Exact) :
    K₀[X₁] = K₀[Limits.kernel g] + K₀[Limits.kernel h] := by
  -- Proof comment: replace `X₁ ⟶ kernel h` by its kernel-cokernel presentation, then identify its
  -- kernel with `kernel g`.
  let u : X₁ ⟶ Limits.kernel h := Limits.kernel.lift h g hgh
  let _ : Epi u := (ShortComplex.Exact.epi_kernelLift (S := ShortComplex.mk g h hgh) hex₂)
  have hcokernel :
      K₀[Limits.cokernel u] = 0 := by
    calc
      K₀[Limits.cokernel u] = K₀[(0 : A)] := by
        exact abelian_k0_eq_of_iso (A := A) (Limits.cokernel.ofEpi u)
      _ = 0 := abelian_k0_zero_eq (A := A)
  have hkernel :
      K₀[Limits.kernel u] = K₀[Limits.kernel g] := by
    simpa [u] using
      (k0_kernel_of_kernel_lift (A := A) h g hgh)
  have hsub :
      K₀[Limits.kernel h] - K₀[X₁] = -K₀[Limits.kernel g] := by
    rw [k0_sub_eq_cokernel_sub_kernel (A := A) u, hcokernel, hkernel]
    abel
  have hsum := congrArg (fun z : AbelianK0 A ↦ z + K₀[X₁] + K₀[Limits.kernel g]) hsub
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum.symm

/-- Helper for Lemma 13.28.4: once the shifted values of `H` vanish outside an interval, the Euler
class is the corresponding finite interval sum. -/
private lemma eulerClass_eq_sum_of_vanishingOutside (X : D) {a b : ℤ}
    (hX : ∀ n : ℤ, n ∉ Set.Icc a b → IsZero ((H.shift n).obj X)) :
    H.eulerClass X =
      Finset.sum (Finset.Icc a b) (fun i ↦ i.negOnePow • K₀[(H.shift i).obj X]) := by
  -- Proof comment: outside the interval every summand is zero, so the `finsum` reduces to the
  -- finite interval support.
  let f : ℤ → AbelianK0 A := fun i ↦ i.negOnePow • K₀[(H.shift i).obj X]
  change ∑ᶠ i : ℤ, f i = Finset.sum (Finset.Icc a b) f
  have hsupp : Function.support f ⊆ ↑(Finset.Icc a b) := by
    intro i hi
    by_contra hnot
    have hzeroObj : IsZero ((H.shift i).obj X) := hX i <| by simpa using hnot
    have hk0 :
        K₀[(H.shift i).obj X] = 0 := by
      calc
        K₀[(H.shift i).obj X] = K₀[(0 : A)] := by
          exact abelian_k0_eq_of_iso (A := A) hzeroObj.isoZero
        _ = 0 := abelian_k0_zero_eq (A := A)
    have hfi : f i = 0 := by
      rw [show f i = i.negOnePow • K₀[(H.shift i).obj X] by rfl, hk0, smul_zero]
    exact hi hfi
  rw [finsum_eq_sum_of_support_subset (s := Finset.Icc a b) f hsupp]

-- Proof sketch: for a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁[1]`, the long exact homology
-- sequence of the homological functor breaks into short exact pieces in `A`. Additivity in the
-- abelian Grothendieck group then gives
-- `∑ (-1)^i [H(X₂[i])] = ∑ (-1)^i [H(X₁[i])] + ∑ (-1)^i [H(X₃[i])]`, and the finite-support
-- hypothesis ensures the alternating sums are genuine finite sums.
/-- Distinguished-triangle relations are killed by the alternating-sum map attached to a
homological functor whose values lie in `H.shiftVanishingBounded` on every object. -/
private theorem relations_le_ker_eulerClass
    (hH : ∀ X : D, H.shiftVanishingBounded X) :
    TriangulatedK0.relations D ≤
      (FreeAbelianGroup.lift
        fun X ↦ H.eulerClass X).ker := by
  -- Proof comment: rewrite the three Euler classes as one common finite interval sum, express each
  -- degreewise Grothendieck relation through adjacent kernels in the long exact sequence, and
  -- telescope the resulting alternating boundary terms.
  rw [TriangulatedK0.relations, AddSubgroup.closure_le]
  rintro _ ⟨T, rfl⟩
  rcases T with ⟨T, hT⟩
  change
    (FreeAbelianGroup.lift fun X ↦ H.eulerClass X)
        (FreeAbelianGroup.of T.obj₂ - FreeAbelianGroup.of T.obj₁ - FreeAbelianGroup.of T.obj₃) = 0
  rw [(FreeAbelianGroup.lift fun X ↦ H.eulerClass X).map_sub]
  rw [(FreeAbelianGroup.lift fun X ↦ H.eulerClass X).map_sub]
  simp only [FreeAbelianGroup.lift_apply_of]
  rcases (Functor.mem_shiftVanishingBounded_iff H T.obj₁).1 (hH T.obj₁) with ⟨N₁, h₁⟩
  rcases (Functor.mem_shiftVanishingBounded_iff H T.obj₂).1 (hH T.obj₂) with ⟨N₂, h₂⟩
  rcases (Functor.mem_shiftVanishingBounded_iff H T.obj₃).1 (hH T.obj₃) with ⟨N₃, h₃⟩
  let N : ℕ := max N₁ (max N₂ N₃)
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) ((N : ℤ) - 1)
  let α := fun i : ℤ ↦ (H.shift i).map T.mor₁
  let β := fun i : ℤ ↦ (H.shift i).map T.mor₂
  let δ := fun i : ℤ ↦ H.homologySequenceδ T i (i + 1) rfl
  let boundary : ℤ → AbelianK0 A := fun i ↦ -i.negOnePow • K₀[Limits.kernel (α i)]
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
      · have hnonpos : n ≤ 0 := by omega
        rw [Int.ofNat_natAbs_of_nonpos hnonpos]
        omega
    exact_mod_cast hnatAbs'
  have hvanish₁ :
      ∀ n : ℤ, n ∉ Set.Icc (-(N : ℤ)) ((N : ℤ) - 1) → IsZero ((H.shift n).obj T.obj₁) := by
    intro n hn
    exact (h₁ n (le_trans hN₁ (hnatAbs_of_not_mem hn))).of_iso ((H.isoShift n).app T.obj₁).symm
  have hvanish₂ :
      ∀ n : ℤ, n ∉ Set.Icc (-(N : ℤ)) ((N : ℤ) - 1) → IsZero ((H.shift n).obj T.obj₂) := by
    intro n hn
    exact (h₂ n (le_trans hN₂ (hnatAbs_of_not_mem hn))).of_iso ((H.isoShift n).app T.obj₂).symm
  have hvanish₃ :
      ∀ n : ℤ, n ∉ Set.Icc (-(N : ℤ)) ((N : ℤ) - 1) → IsZero ((H.shift n).obj T.obj₃) := by
    intro n hn
    exact (h₃ n (le_trans hN₃ (hnatAbs_of_not_mem hn))).of_iso ((H.isoShift n).app T.obj₃).symm
  have hleft_zero :
      IsZero ((H.shift (-(N : ℤ))).obj T.obj₁) := by
    exact (h₁ (-(N : ℤ)) (le_trans hN₁ (by simpa))).of_iso
      ((H.isoShift (-(N : ℤ))).app T.obj₁).symm
  have hright_zero :
      IsZero ((H.shift (N : ℤ)).obj T.obj₁) := by
    exact (h₁ (N : ℤ) (le_trans hN₁ (by simpa))).of_iso ((H.isoShift (N : ℤ)).app T.obj₁).symm
  have hA :
      ∀ i : ℤ,
        K₀[(H.shift i).obj T.obj₁] = K₀[Limits.kernel (α i)] + K₀[Limits.kernel (β i)] := by
    intro i
    have hi_succ : i - 1 + 1 = i := by omega
    dsimp [α, β, δ]
    let hex_prev := H.homologySequenceComposableArrows₅_exact T hT (i - 1) i hi_succ
    let hex_curr := H.homologySequenceComposableArrows₅_exact T hT i (i + 1) rfl
    exact
      k0_eq_kernel_add_kernel_of_exact (A := A)
        (H.homologySequenceδ T (i - 1) i hi_succ)
        ((H.shift i).map T.mor₁)
        ((H.shift i).map T.mor₂)
        (by simpa using hex_prev.toIsComplex.zero 2)
        (by simpa using hex_curr.toIsComplex.zero 0)
        (by simpa using hex_prev.exact 2)
        (by simpa using hex_curr.exact 0)
  have hB :
      ∀ i : ℤ,
        K₀[(H.shift i).obj T.obj₂] = K₀[Limits.kernel (β i)] + K₀[Limits.kernel (δ i)] := by
    intro i
    dsimp [β, δ]
    let hex := H.homologySequenceComposableArrows₅_exact T hT i (i + 1) rfl
    exact
      k0_eq_kernel_add_kernel_of_exact (A := A)
        ((H.shift i).map T.mor₁)
        ((H.shift i).map T.mor₂)
        (H.homologySequenceδ T i (i + 1) rfl)
        (by simpa using hex.toIsComplex.zero 0)
        (by simpa using hex.toIsComplex.zero 1)
        (by simpa using hex.exact 0)
        (by simpa using hex.exact 1)
  have hC :
      ∀ i : ℤ,
        K₀[(H.shift i).obj T.obj₃] =
          K₀[Limits.kernel (δ i)] + K₀[Limits.kernel (α (i + 1))] := by
    intro i
    dsimp [α, δ]
    let hex := H.homologySequenceComposableArrows₅_exact T hT i (i + 1) rfl
    exact
      k0_eq_kernel_add_kernel_of_exact (A := A)
        ((H.shift i).map T.mor₂)
        (H.homologySequenceδ T i (i + 1) rfl)
        ((H.shift (i + 1)).map T.mor₁)
        (by simpa using hex.toIsComplex.zero 1)
        (by simpa using hex.toIsComplex.zero 2)
        (by simpa using hex.exact 1)
        (by simpa using hex.exact 2)
  have hterm :
      ∀ i : ℤ,
        i.negOnePow • K₀[(H.shift i).obj T.obj₂]
          - i.negOnePow • K₀[(H.shift i).obj T.obj₁]
          - i.negOnePow • K₀[(H.shift i).obj T.obj₃] =
            boundary i - boundary (i + 1) := by
    intro i
    have hsign : (i + 1).negOnePow = -i.negOnePow := by
      rw [Int.negOnePow_add, Int.negOnePow_one]
      simp
    change
      i.negOnePow • K₀[(H.shift i).obj T.obj₂]
          - i.negOnePow • K₀[(H.shift i).obj T.obj₁]
          - i.negOnePow • K₀[(H.shift i).obj T.obj₃] =
        -i.negOnePow • K₀[Limits.kernel (α i)] -
          -(i + 1).negOnePow • K₀[Limits.kernel (α (i + 1))]
    rw [hB i, hA i, hC i, hsign]
    simp [smul_add, sub_eq_add_neg, add_assoc, add_comm]
    abel
  have hs₁ :
      H.eulerClass T.obj₁ =
        Finset.sum s (fun i ↦ i.negOnePow • K₀[(H.shift i).obj T.obj₁]) := by
    simpa [s] using eulerClass_eq_sum_of_vanishingOutside (H := H) T.obj₁ hvanish₁
  have hs₂ :
      H.eulerClass T.obj₂ =
        Finset.sum s (fun i ↦ i.negOnePow • K₀[(H.shift i).obj T.obj₂]) := by
    simpa [s] using eulerClass_eq_sum_of_vanishingOutside (H := H) T.obj₂ hvanish₂
  have hs₃ :
      H.eulerClass T.obj₃ =
        Finset.sum s (fun i ↦ i.negOnePow • K₀[(H.shift i).obj T.obj₃]) := by
    simpa [s] using eulerClass_eq_sum_of_vanishingOutside (H := H) T.obj₃ hvanish₃
  have hsums :
      Finset.sum s (fun i ↦ i.negOnePow • K₀[(H.shift i).obj T.obj₂]) -
          Finset.sum s (fun i ↦ i.negOnePow • K₀[(H.shift i).obj T.obj₁]) -
          Finset.sum s (fun i ↦ i.negOnePow • K₀[(H.shift i).obj T.obj₃]) =
        Finset.sum s (fun i ↦
          i.negOnePow • K₀[(H.shift i).obj T.obj₂]
            - i.negOnePow • K₀[(H.shift i).obj T.obj₁]
            - i.negOnePow • K₀[(H.shift i).obj T.obj₃]) := by
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
    simp [k0_kernel_eq_zero_of_isZero_source (A := A) (α (-(N : ℤ))) hleft_zero]
  have hboundary_right : boundary (N : ℤ) = 0 := by
    change -(N : ℤ).negOnePow • K₀[Limits.kernel (α (N : ℤ))] = 0
    simp [k0_kernel_eq_zero_of_isZero_source (A := A) (α (N : ℤ)) hright_zero]
  calc
    H.eulerClass T.obj₂ - H.eulerClass T.obj₁ - H.eulerClass T.obj₃
        = Finset.sum s (fun i ↦ i.negOnePow • K₀[(H.shift i).obj T.obj₂]) -
            Finset.sum s (fun i ↦ i.negOnePow • K₀[(H.shift i).obj T.obj₁]) -
            Finset.sum s (fun i ↦ i.negOnePow • K₀[(H.shift i).obj T.obj₃]) := by
              rw [hs₂, hs₁, hs₃]
    _ = Finset.sum s (fun i ↦
          i.negOnePow • K₀[(H.shift i).obj T.obj₂]
            - i.negOnePow • K₀[(H.shift i).obj T.obj₁]
            - i.negOnePow • K₀[(H.shift i).obj T.obj₃]) := hsums
    _ = Finset.sum s (fun i ↦ boundary i - boundary (i + 1)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact hterm i
    _ = boundary (-(N : ℤ)) - boundary (N : ℤ) := htel
    _ = 0 := by simp [hboundary_left, hboundary_right]

/-- Lemma 13.28.4: a homological functor from a triangulated category to an abelian category,
whose shifted values are nonzero in only finitely many degrees on each object, induces a canonical
homomorphism `K₀(\mathcal D) → K₀(\mathcal A)` sending `[X]` to the alternating sum
`∑ (-1)^i [H(X[i])]`. -/
def eulerK0Map (hH : ∀ X : D, H.shiftVanishingBounded X) :
    TriangulatedK0 D →+ AbelianK0 A :=
  TriangulatedK0.lift
    (fun X ↦ H.eulerClass X)
    (relations_le_ker_eulerClass H hH)

-- Proof sketch: `eulerK0Map` is the quotient lift of the objectwise Euler-class function
-- `X ↦ H.eulerClass X`, so evaluating it on the class of an
-- object `X` reduces to
-- the defining alternating-sum formula on generators.
/-- The induced map on `K₀` sends the class of `X` to the alternating sum of the classes of the
shifted objects `H(X[i])`. -/
@[simp] theorem eulerK0Map_apply_of
    (hH : ∀ X : D, H.shiftVanishingBounded X) (X : D) :
    H.eulerK0Map hH (TriangulatedK0.of X) = H.eulerClass X := by
  simpa using
    TriangulatedK0.lift_of
      (fun Y ↦ H.eulerClass Y)
      (relations_le_ker_eulerClass H hH)
      X

end EulerK0Map

end Functor
end CategoryTheory
