import Mathlib
import Mathlib.Algebra.Category.Grp.AB
import StacksProject_2024.stacks_project.Chap04.Lemma_4_19_5
import StacksProject_2024.stacks_project.Chap13.Definition_13_36_3
import StacksProject_2024.stacks_project.Chap13.Definition_13_33_1
import StacksProject_2024.stacks_project.Chap13.Definition_13_37_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_37_2
import StacksProject_2024.stacks_project.Chap13.Lemma_13_33_6
import StacksProject_2024.stacks_project.Chap13.Remark_13_33_2
import StacksProject_2024.stacks_project.Chap13.Lemma_13_33_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open Opposite

noncomputable section

universe w v u

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  [HasCoproducts.{max u v w} D]
variable {I : Type w} (E : I → D)

/-- The object property of objects that are isomorphic to a coproduct of shifts of the family
`E : I → D`. -/
def IsDirectSumOfShifts : ObjectProperty D := fun A ↦
  ∃ (J : Type (max u v w)) (ι : J → I) (shift : J → ℤ),
    Nonempty ((∐ fun j : J ↦ E (ι j)⟦shift j⟧) ≅ A)

instance isDirectSumOfShifts_isClosedUnderIsomorphisms :
    (IsDirectSumOfShifts E).IsClosedUnderIsomorphisms where
  of_iso e hA := by
    rcases hA with ⟨J, ι, shift, ⟨h⟩⟩
    exact ⟨J, ι, shift, ⟨h.trans e⟩⟩

/-- A recursive generating-family approximation tower by direct sums of shifts of the family `E`.
The natural-number index `0` corresponds to the textbook term `X₁`. -/
def IsGeneratingFamilyApproximation
    (X : ℕ → D) (map : ∀ n : ℕ, X n ⟶ X (n + 1))
    (Y : ℕ → D) (triangleHom : ∀ n : ℕ, Y n ⟶ X n)
    (triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧) : Prop :=
  IsDirectSumOfShifts E (X 0) ∧
    (∀ n : ℕ, IsDirectSumOfShifts E (Y n)) ∧
    (∀ n : ℕ, Triangle.mk (triangleHom n) (map n) (triangleConnecting n) ∈ distTriang D)

namespace IsGeneratingFamilyApproximation

omit [IsTriangulated D] in
theorem initial {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    (h :
      IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting) :
    IsDirectSumOfShifts E (X 0) :=
  h.1

omit [IsTriangulated D] in
theorem pieces {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    (h :
      IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting) (n : ℕ) :
    IsDirectSumOfShifts E (Y n) :=
  h.2.1 n

omit [IsTriangulated D] in
theorem triangleDistinguished {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    (h :
      IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting) (n : ℕ) :
    Triangle.mk (triangleHom n) (map n) (triangleConnecting n) ∈ distTriang D :=
  h.2.2 n

end IsGeneratingFamilyApproximation

/-- Helper for Lemma 13.37.3: the universal initial stage is the coproduct of all shifted
generators mapping to the target object. -/
theorem exists_initial_shift_cover (A : D) :
    ∃ X0 : D, ∃ toA0 : X0 ⟶ A,
      IsDirectSumOfShifts E X0 ∧
        ∀ (i : I) (m : ℤ) (φ : E i⟦m⟧ ⟶ A), ∃ ψ : E i⟦m⟧ ⟶ X0, ψ ≫ toA0 = φ := by
  classical
  let J : Type (max u v w) :=
    ULift.{max u v w, max w v} (Σ i : I, Σ m : ℤ, (E i⟦m⟧ ⟶ A))
  let X0 : D := ∐ fun j : J ↦ E j.down.1⟦j.down.2.1⟧
  let toA0 : X0 ⟶ A := Sigma.desc fun j : J ↦ j.down.2.2
  refine ⟨X0, toA0, ?_, ?_⟩
  · exact ⟨J, fun j ↦ j.down.1, fun j ↦ j.down.2.1, ⟨Iso.refl _⟩⟩
  · intro i m φ
    refine ⟨Sigma.ι (fun j : J ↦ E j.down.1⟦j.down.2.1⟧) ⟨⟨i, m, φ⟩⟩, ?_⟩
    simpa [toA0] using
      (Limits.Sigma.ι_desc (fun j : J ↦ j.down.2.2) ⟨⟨i, m, φ⟩⟩)

/-- Helper for Lemma 13.37.3: from a stage `X ⟶ A`, kill all shifted-generator maps landing in
the kernel by taking the coproduct of those kernel maps and completing it to a distinguished
triangle. -/
theorem exists_next_approximation_step {X A : D} (p : X ⟶ A) :
    ∃ (Y : D) (y : Y ⟶ X) (X' : D) (f : X ⟶ X') (δ : X' ⟶ Y⟦(1 : ℤ)⟧) (p' : X' ⟶ A),
      IsDirectSumOfShifts E Y ∧
        Triangle.mk y f δ ∈ distTriang D ∧
          f ≫ p' = p ∧
            ∀ (i : I) (m : ℤ) (φ : E i⟦m⟧ ⟶ X), φ ≫ p = 0 →
              ∃ ψ : E i⟦m⟧ ⟶ Y, ψ ≫ y = φ := by
  classical
  let J : Type (max u v w) :=
    ULift.{max u v w, max w v}
      (Σ i : I, Σ m : ℤ, { φ : E i⟦m⟧ ⟶ X // φ ≫ p = 0 })
  let Y : D := ∐ fun j : J ↦ E j.down.1⟦j.down.2.1⟧
  let y : Y ⟶ X := Sigma.desc fun j : J ↦ j.down.2.2.1
  obtain ⟨X', f, δ, hT⟩ := distinguished_cocone_triangle y
  have hy_zero : y ≫ p = 0 := by
    apply Limits.Sigma.hom_ext
    intro j
    rw [Limits.Sigma.ι_desc_assoc]
    simpa using j.down.2.2.2
  obtain ⟨p', hp'⟩ := Triangle.yoneda_exact₂ (T := Triangle.mk y f δ) hT p hy_zero
  refine ⟨Y, y, X', f, δ, p', ?_, hT, ?_, ?_⟩
  · exact ⟨J, fun j ↦ j.down.1, fun j ↦ j.down.2.1, ⟨Iso.refl _⟩⟩
  · simpa [Triangle.mk] using hp'.symm
  · intro i m φ hφ
    refine ⟨Sigma.ι (fun j : J ↦ E j.down.1⟦j.down.2.1⟧) ⟨⟨i, m, ⟨φ, hφ⟩⟩⟩, ?_⟩
    simpa [y] using
      (Limits.Sigma.ι_desc (fun j : J ↦ j.down.2.2.1) ⟨⟨i, m, ⟨φ, hφ⟩⟩⟩)

/-- Helper for Lemma 13.37.3: one source-style successor step in the recursive approximation
tower over `A`. -/
private structure ApproximationStep {X A : D} (p : X ⟶ A) where
  Y : D
  triangleHom : Y ⟶ X
  nextX : D
  map : X ⟶ nextX
  triangleConnecting : nextX ⟶ Y⟦(1 : ℤ)⟧
  toA : nextX ⟶ A
  isDirectSum : IsDirectSumOfShifts E Y
  distinguished : Triangle.mk triangleHom map triangleConnecting ∈ distTriang D
  comp_toA : map ≫ toA = p
  kernel_lift :
    ∀ (i : I) (m : ℤ) (φ : E i⟦m⟧ ⟶ X), φ ≫ p = 0 →
      ∃ ψ : E i⟦m⟧ ⟶ Y, ψ ≫ triangleHom = φ

/-- Helper for Lemma 13.37.3: package `exists_next_approximation_step` as a reusable successor-step
record for the tower recursion. -/
private theorem exists_approximation_step {X A : D} (p : X ⟶ A) :
    Nonempty (ApproximationStep (E := E) p) := by
  obtain ⟨Y, y, X', f, δ, p', hY, hT, hcomp, hkernel⟩ :=
    exists_next_approximation_step (E := E) p
  exact ⟨⟨Y, y, X', f, δ, p', hY, hT, hcomp, hkernel⟩⟩

/-- Helper for Lemma 13.37.3: in one approximation step, a shifted-generator map lying in the
kernel of the comparison to `A` is killed by the transition morphism. -/
private theorem ApproximationStep.kernel_map_zero {X A : D} {p : X ⟶ A}
    (s : ApproximationStep (E := E) p) (i : I) (m : ℤ) (φ : E i⟦m⟧ ⟶ X)
    (hφ : φ ≫ p = 0) :
    φ ≫ s.map = 0 := by
  -- Lift the kernel map through the first morphism in the distinguished triangle.
  obtain ⟨ψ, hψ⟩ := s.kernel_lift i m φ hφ
  have hzero : s.triangleHom ≫ s.map = 0 := by
    simpa [Triangle.mk] using comp_distTriang_mor_zero₁₂ _ s.distinguished
  -- The middle composite vanishes in every distinguished triangle.
  calc
    φ ≫ s.map = (ψ ≫ s.triangleHom) ≫ s.map := by rw [hψ]
    _ = ψ ≫ (s.triangleHom ≫ s.map) := by simp [Category.assoc]
    _ = 0 := by simp [hzero]

/-- Helper for Lemma 13.37.3: recursively package the source-style approximation tower together
with the stage maps to the target object `A`, the initial surjectivity on shifted generators, and
the kernel-killing property for each transition map. -/
private theorem exists_recursive_approximation_tower (A : D) :
    ∃ (X : ℕ → D) (map : ∀ n : ℕ, X n ⟶ X (n + 1))
      (Y : ℕ → D) (triangleHom : ∀ n : ℕ, Y n ⟶ X n)
      (triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧)
      (toA : ∀ n : ℕ, X n ⟶ A),
        IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting ∧
          (∀ n : ℕ, map n ≫ toA (n + 1) = toA n) ∧
          (∀ (i : I) (m : ℤ) (φ : E i⟦m⟧ ⟶ A),
            ∃ ψ : E i⟦m⟧ ⟶ X 0, ψ ≫ toA 0 = φ) ∧
          (∀ (n : ℕ) (i : I) (m : ℤ) (φ : E i⟦m⟧ ⟶ X n),
            φ ≫ toA n = 0 → φ ≫ map n = 0) := by
  classical
  obtain ⟨X0, toA0, hX0, hsurj0⟩ := exists_initial_shift_cover (E := E) A
  let stage : ℕ → Σ X : D, X ⟶ A :=
    Nat.rec
      ⟨X0, toA0⟩
      (fun _ prev ↦
        let s : ApproximationStep (E := E) prev.2 :=
          Classical.choice (exists_approximation_step (E := E) prev.2)
        ⟨s.nextX, s.toA⟩)
  let X : ℕ → D := fun n ↦ (stage n).1
  let toA : ∀ n : ℕ, X n ⟶ A := fun n ↦ (stage n).2
  let step : ∀ n : ℕ, ApproximationStep (E := E) (toA n) := fun n ↦
    Classical.choice (exists_approximation_step (E := E) (toA n))
  let Y : ℕ → D := fun n ↦ (step n).Y
  let triangleHom : ∀ n : ℕ, Y n ⟶ X n := fun n ↦ (step n).triangleHom
  let map : ∀ n : ℕ, X n ⟶ X (n + 1) := fun n ↦ (step n).map
  let triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧ := fun n ↦
    (step n).triangleConnecting
  have hApprox : IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting := by
    refine ⟨?_, ?_, ?_⟩
    · -- The initial stage is the universal coproduct of all shifted-generator maps into `A`.
      simpa [X, stage] using hX0
    · -- Every auxiliary object `Y n` is built as a coproduct of shifted generators.
      intro n
      exact (step n).isDirectSum
    · -- Each transition is chosen from a distinguished triangle by construction.
      intro n
      exact (step n).distinguished
  have hcompat : ∀ n : ℕ, map n ≫ toA (n + 1) = toA n := by
    -- The recursive step stores compatibility of the new stage map with the previous one.
    intro n
    exact (step n).comp_toA
  have hkernel :
      ∀ (n : ℕ) (i : I) (m : ℤ) (φ : E i⟦m⟧ ⟶ X n),
        φ ≫ toA n = 0 → φ ≫ map n = 0 := by
    -- The distinguished-triangle relation turns each kernel lift into a killed transition map.
    intro n i m φ hφ
    exact ApproximationStep.kernel_map_zero (E := E) (step n) i m φ hφ
  have hsurj :
      ∀ (i : I) (m : ℤ) (φ : E i⟦m⟧ ⟶ A), ∃ ψ : E i⟦m⟧ ⟶ X 0, ψ ≫ toA 0 = φ := by
    -- Stage `0` is exactly the universal source covering all maps from shifted generators to `A`.
    intro i m φ
    simpa [X, toA, stage] using hsurj0 i m φ
  refine ⟨X, map, Y, triangleHom, triangleConnecting, toA, hApprox, hcompat, hsurj, hkernel⟩

/-- Helper for Lemma 13.37.3: every sequential system admits a chosen telescope presentation of a
homotopy colimit. -/
private theorem exists_homotopyColimit_of_sequence {X : ℕ → D}
    (map : ∀ n : ℕ, X n ⟶ X (n + 1)) :
    ∃ Khocolim : D, IsHomotopyColimitOf (Functor.ofSequence map) Khocolim := by
  -- Choose the canonical cone on the telescope map of the sequence.
  obtain ⟨Khocolim, g, h, htriangle⟩ :=
    distinguished_cocone_triangle (sequentialTelescopeMap (Functor.ofSequence map))
  exact ⟨Khocolim, g, h, htriangle⟩

/-- Helper for Lemma 13.37.3: every element of the sequential colimit in `AddCommGrpCat` is
already represented at a single stage. -/
private theorem exists_stage_representative_of_sequential_addCommGrp_colimit
    (G : ℕ ⥤ AddCommGrpCat.{max u v}) (z : (colimit G : AddCommGrpCat.{max u v})) :
    ∃ n : ℕ, ∃ x : G.obj n, colimit.ι G n x = z := by
  -- TODO for Lemma 13.37.3: reuse the sequential `AddCommGrpCat` representative argument from the
  -- standard colimit comparison owner and then apply it to the Hom-colimit corridor below.
  sorry

/-- Helper for Lemma 13.37.3: a compatible family of stage maps `X n ⟶ A` descends to the chosen
homotopy colimit of the sequence. -/
private theorem exists_comparison_map_from_hocolim
    {A : D} {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1)) {Khocolim : D}
    (hKhocolim : IsHomotopyColimitOf (Functor.ofSequence map) Khocolim)
    (toA : ∀ n : ℕ, X n ⟶ A) (hcompat : ∀ n : ℕ, map n ≫ toA (n + 1) = toA n) :
    ∃ (ι : ∀ n : ℕ, X n ⟶ Khocolim) (c : Khocolim ⟶ ∐ fun n ↦ X n⟦(1 : ℤ)⟧)
      (q : Khocolim ⟶ A),
      (∀ n : ℕ, map n ≫ ι (n + 1) = ι n) ∧
        Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) (Limits.Sigma.desc ι)
          (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) ∈ distTriang D ∧
          (∀ n : ℕ, ι n ≫ q = toA n) := by
  -- TODO for Lemma 13.37.3: extract `ι, c` from `hKhocolim.exists_presentation`, prove the
  -- telescope composite with `Sigma.desc toA` is zero from `hcompat`, and descend `q` via
  -- `Triangle.yoneda_exact₂`.
  sorry

/-- Helper for Lemma 13.37.3: after applying `Hom(K, -)`, the compatible maps `X n ⟶ A` form a
sequential cocone. -/
private theorem hom_colimit_cocone_naturality
    {K A : D} {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1)) (toA : ∀ n : ℕ, X n ⟶ A)
    (hcompat : ∀ n : ℕ, map n ≫ toA (n + 1) = toA n) (n : ℕ) :
    (preadditiveCoyoneda.obj (op K)).map (map n) ≫
        (preadditiveCoyoneda.obj (op K)).map (toA (n + 1)) =
      (preadditiveCoyoneda.obj (op K)).map (toA n) := by
  -- TODO for Lemma 13.37.3: rewrite this as `Functor.map (map n ≫ toA (n + 1))` and simplify
  -- using `Functor.map_comp` together with `hcompat n`.
  sorry

/-- Helper for Lemma 13.37.3: the stage maps `X n ⟶ A` induce the canonical cocone on
`Hom_D(K, X n)`. -/
private abbrev hom_colimit_cocone
    {K A : D} {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1)) (toA : ∀ n : ℕ, X n ⟶ A)
    (hcompat : ∀ n : ℕ, map n ≫ toA (n + 1) = toA n) :
    Cocone (Functor.ofSequence (fun n ↦ (preadditiveCoyoneda.obj (op K)).map (map n))) :=
  Cocone.mk _ <|
    NatTrans.ofSequence
      (fun n ↦ (preadditiveCoyoneda.obj (op K)).map (toA n))
      (fun n ↦ by
        simpa [Functor.ofSequence_map_homOfLE_succ] using
          hom_colimit_cocone_naturality (K := K) map toA hcompat n)

/-- Helper for Lemma 13.37.3: the stagewise cocone induces the canonical map from the sequential
colimit of `Hom_D(K, X n)` to `Hom_D(K, A)`. -/
private abbrev hom_colimit_desc
    {K A : D} {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1)) (toA : ∀ n : ℕ, X n ⟶ A)
    (hcompat : ∀ n : ℕ, map n ≫ toA (n + 1) = toA n) :
    colimit (Functor.ofSequence (fun n ↦ (preadditiveCoyoneda.obj (op K)).map (map n))) ⟶
      (preadditiveCoyoneda.obj (op K)).obj A :=
  colimit.desc _ (hom_colimit_cocone (K := K) map toA hcompat)

/-- Helper for Lemma 13.37.3: if every map `K ⟶ A` already comes from stage `0`, then the
canonical descent map from the sequential `Hom`-colimit to `Hom_D(K, A)` is surjective. -/
private theorem hom_colimit_desc_surjective_of_stage0_surjective
    {K A : D} {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1)) (toA : ∀ n : ℕ, X n ⟶ A)
    (hcompat : ∀ n : ℕ, map n ≫ toA (n + 1) = toA n)
    (hsurj : ∀ φ : K ⟶ A, ∃ ψ : K ⟶ X 0, ψ ≫ toA 0 = φ) :
    Function.Surjective (hom_colimit_desc (K := K) map toA hcompat).hom := by
  -- TODO for Lemma 13.37.3: evaluate the descended colimit map on the stage-`0` coprojection and
  -- use the chosen lift `ψ` of `φ`.
  sorry

/-- Helper for Lemma 13.37.3: if every generator map killed in `Hom_D(K, A)` already dies after
one transition, then any element of the sequential `Hom`-colimit mapping to zero is already zero. -/
private theorem hom_colimit_desc_eq_zero_of_kernel_killed
    {K A : D} {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1)) (toA : ∀ n : ℕ, X n ⟶ A)
    (hcompat : ∀ n : ℕ, map n ≫ toA (n + 1) = toA n)
    (hkernel : ∀ (n : ℕ) (ψ : K ⟶ X n), ψ ≫ toA n = 0 → ψ ≫ map n = 0)
    {z :
      (colimit (Functor.ofSequence (fun n ↦ (preadditiveCoyoneda.obj (op K)).map (map n))) :
        AddCommGrpCat.{v})}
    (hz : (hom_colimit_desc (K := K) map toA hcompat).hom z = 0) :
    z = 0 := by
  -- TODO for Lemma 13.37.3: represent `z` at a single stage, rewrite `hz` via `colimit.ι_desc`,
  -- apply `hkernel`, and use the sequential colimit relation `colimit.w` to move to stage `n+1`.
  sorry

/-- Helper for Lemma 13.37.3: the one-step kernel-killing hypothesis makes the canonical map
from the sequential `Hom`-colimit to `Hom_D(K, A)` injective. -/
private theorem hom_colimit_desc_injective_of_kernel_killed
    {K A : D} {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1)) (toA : ∀ n : ℕ, X n ⟶ A)
    (hcompat : ∀ n : ℕ, map n ≫ toA (n + 1) = toA n)
    (hkernel : ∀ (n : ℕ) (ψ : K ⟶ X n), ψ ≫ toA n = 0 → ψ ≫ map n = 0) :
    Function.Injective (hom_colimit_desc (K := K) map toA hcompat).hom := by
  -- TODO for Lemma 13.37.3: reduce injectivity to the previous zero-kernel lemma by applying it
  -- to `z₁ - z₂`.
  sorry

/-- Helper for Lemma 13.37.3: every shifted generator still represents a functor preserving
countable coproducts. -/
private theorem shifted_generator_preserves_countable_coproducts
    (hcompact : ∀ i : I, IsCompactObject (E i)) (i : I) (m : ℤ) :
    PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op (E i⟦m⟧))) := by
  let P : ObjectProperty D := IsCompactObject
  have hshift : P (E i⟦m⟧) := P.le_shift m _ (hcompact i)
  -- Compactness is stable under shifts, so the represented Hom functor still preserves
  -- countable coproducts at every shifted generator.
  letI : IsCompactObject (E i⟦m⟧) := hshift
  infer_instance

/-- Helper for Lemma 13.37.3: the hocolim `Hom` comparison followed by `Hom(K, q)` is the same
as the direct descent map from the sequential `Hom`-colimit to `Hom_D(K, A)`. -/
private theorem preadditiveCoyoneda_hocolim_comparison_comp_map_eq_hom_colimit_desc
    {K A Khocolim : D} {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1))
    (ι : ∀ n : ℕ, X n ⟶ Khocolim) (c : Khocolim ⟶ ∐ fun n ↦ X n⟦(1 : ℤ)⟧)
    (hT :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) (Limits.Sigma.desc ι)
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) ∈ distTriang D)
    (q : Khocolim ⟶ A) (toA : ∀ n : ℕ, X n ⟶ A)
    (hcompat : ∀ n : ℕ, map n ≫ toA (n + 1) = toA n)
    (hq : ∀ n : ℕ, ι n ≫ q = toA n) :
    homologicalFunctor_hocolim_comparison (preadditiveCoyoneda.obj (op K)) map
        (Limits.Sigma.desc ι) (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) hT ≫
      (preadditiveCoyoneda.obj (op K)).map q =
        hom_colimit_desc (K := K) map toA hcompat := by
  -- TODO for Lemma 13.37.3: use `colimit.hom_ext`, rewrite both sides with `colimit.ι_desc`, and
  -- compare them via `congrArg ((preadditiveCoyoneda.obj (op K)).map) (hq n)`.
  sorry

/-- Helper for Lemma 13.37.3: the comparison map from the chosen hocolim to `A` is an
isomorphism on `Hom(E i⟦m⟧, -)` for every shifted generator. -/
private theorem shifted_generator_map_comparison_isIso
    (hcompact : ∀ i : I, IsCompactObject (E i))
    {A Khocolim : D} {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1))
    (toA : ∀ n : ℕ, X n ⟶ A) (hcompat : ∀ n : ℕ, map n ≫ toA (n + 1) = toA n)
    (hsurj : ∀ (i : I) (m : ℤ) (φ : E i⟦m⟧ ⟶ A),
      ∃ ψ : E i⟦m⟧ ⟶ X 0, ψ ≫ toA 0 = φ)
    (hkernel : ∀ (n : ℕ) (i : I) (m : ℤ) (φ : E i⟦m⟧ ⟶ X n),
      φ ≫ toA n = 0 → φ ≫ map n = 0)
    (ι : ∀ n : ℕ, X n ⟶ Khocolim) (c : Khocolim ⟶ ∐ fun n ↦ X n⟦(1 : ℤ)⟧)
    (q : Khocolim ⟶ A)
    (hT :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) (Limits.Sigma.desc ι)
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) ∈ distTriang D)
    (hq : ∀ n : ℕ, ι n ≫ q = toA n) :
    ∀ i : I, ∀ m : ℤ, IsIso ((preadditiveCoyoneda.obj (op (E i⟦m⟧))).map q) := by
  -- TODO for Lemma 13.37.3: compare `Hom(E i⟦m⟧, Khocolim)` and `Hom(E i⟦m⟧, A)` with the same
  -- sequential colimit, using Lemma 13.33.9 for the left comparison and the stage-0
  -- surjectivity/kernel-killing corridor for the right comparison.
  sorry

/-- Helper for Lemma 13.37.3: if `Hom(E i⟦m⟧, q)` is an isomorphism for every shifted generator,
then postcomposition with `q` is bijective for every source in the shift-closure of the family. -/
private theorem shifted_generator_postcompose_bijective
    {A B X : D} (q : A ⟶ B)
    (hqIso : ∀ i : I, ∀ m : ℤ, IsIso ((preadditiveCoyoneda.obj (op (E i⟦m⟧))).map q))
    (hX : ((ObjectProperty.ofObj E).shiftClosure ℤ) X) :
    Function.Bijective (fun f : X ⟶ A ↦ f ≫ q) := by
  rcases hX with ⟨Y, n, e, hY⟩
  rw [ObjectProperty.ofObj_iff] at hY
  rcases hY with ⟨i, rfl⟩
  have hbij :
      Function.Bijective (fun f : E i⟦n⟧ ⟶ A ↦ f ≫ q) := by
    simpa using
      (ConcreteCategory.isIso_iff_bijective
        ((preadditiveCoyoneda.obj (op (E i⟦n⟧))).map q)).1 (hqIso i n)
  refine ⟨?_, ?_⟩
  · intro f₁ f₂ hEq
    have hEq' : (e.inv ≫ f₁) ≫ q = (e.inv ≫ f₂) ≫ q := by
      simpa [Category.assoc] using congrArg (fun t ↦ e.inv ≫ t) hEq
    have hsrc : e.inv ≫ f₁ = e.inv ≫ f₂ := hbij.1 hEq'
    calc
      f₁ = e.hom ≫ (e.inv ≫ f₁) := by simp [Category.assoc]
      _ = e.hom ≫ (e.inv ≫ f₂) := by rw [hsrc]
      _ = f₂ := by simp [Category.assoc]
  · intro g
    obtain ⟨ψ, hψ⟩ := hbij.2 (e.inv ≫ g)
    refine ⟨e.hom ≫ ψ, ?_⟩
    calc
      (e.hom ≫ ψ) ≫ q = e.hom ≫ (ψ ≫ q) := by simp [Category.assoc]
      _ = e.hom ≫ ((fun f ↦ f ≫ q) ψ) := by rfl
      _ = e.hom ≫ (e.inv ≫ g) := by rw [hψ]
      _ = g := by simp [Category.assoc]

/-- Helper for Lemma 13.37.3: once `q` is generatorwise an isomorphism on `Hom`, the cone of a
distinguished triangle on `q` is right-orthogonal to the entire shift-closure of the family. -/
private theorem comparison_cone_rightOrthogonal
    {Khocolim A C : D} (q : Khocolim ⟶ A) (v : A ⟶ C) (δ : C ⟶ Khocolim⟦(1 : ℤ)⟧)
    (hT : Triangle.mk q v δ ∈ distTriang D)
    (hqIso : ∀ i : I, ∀ m : ℤ, IsIso ((preadditiveCoyoneda.obj (op (E i⟦m⟧))).map q)) :
    ((ObjectProperty.ofObj E).shiftClosure ℤ).rightOrthogonal C := by
  -- TODO for Lemma 13.37.3: run the local exact-sequence cone argument on each object of the
  -- shift-closure, using postcomposition bijectivity for `q` on `Z` and on `Z⟦-1⟧`.
  sorry

-- Proof sketch: choose the canonical approximation tower built from all maps from shifts of the
-- compact generators into `X` and into the successive kernels of the maps to `X`. Lemma 13.33.9
-- identifies maps from each compact generator into the homotopy colimit with the colimit of maps
-- into the stages, so the cone of the comparison map to `X` is right-orthogonal to all shifts of
-- the family. The generating hypothesis then forces that cone to be zero.
/-- Lemma 13.37.3: if each `E i` is compact and the shifts of the family `E` generate `D`, then
every object `X` admits a sequential resolution whose initial term and successive cones are direct
sums of shifts of the `E i`, and whose chosen homotopy colimit is equipped with an isomorphism to
`X`. The index `0` of the resolution corresponds to the textbook term `X₁`. -/
theorem exists_generating_family_resolution
    (hcompact : ∀ i : I, IsCompactObject (E i)) (hgenerate : IsGeneratingFamily E) (A : D) :
    ∃ (X : ℕ → D) (map : ∀ n : ℕ, X n ⟶ X (n + 1))
      (Y : ℕ → D) (triangleHom : ∀ n : ℕ, Y n ⟶ X n)
      (triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧) (Khocolim : D)
      (e : Khocolim ≅ A),
          IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting ∧
          IsHomotopyColimitOf (Functor.ofSequence map) Khocolim := by
  classical
  obtain ⟨X, map, Y, triangleHom, triangleConnecting, toA, hApprox, hcompat, hsurj, hkernel⟩ :=
    exists_recursive_approximation_tower (E := E) A
  obtain ⟨Khocolim, hKhocolim⟩ := exists_homotopyColimit_of_sequence (map := map)
  obtain ⟨ι, c, q, hιcompat, hT, hq⟩ :=
    exists_comparison_map_from_hocolim (map := map) hKhocolim toA hcompat
  have hqIso :
      ∀ i : I, ∀ m : ℤ, IsIso ((preadditiveCoyoneda.obj (op (E i⟦m⟧))).map q) := by
    -- Route correction: the remaining source-faithful blocker is the compact-generator `Hom`
    -- comparison for the chosen `q : Khocolim ⟶ A`.
    exact shifted_generator_map_comparison_isIso (E := E) hcompact map toA hcompat
      hsurj hkernel ι c q hT hq
  obtain ⟨C, v, δ, hCone⟩ := distinguished_cocone_triangle q
  have horth : ((ObjectProperty.ofObj E).shiftClosure ℤ).rightOrthogonal C := by
    -- The cone-killing step is the textbook exact-sequence argument packaged on the whole
    -- shift-closure of the generating family.
    exact comparison_cone_rightOrthogonal (E := E) q v δ hCone hqIso
  rw [IsGeneratingFamily] at hgenerate
  have hzeroC : IsZero C := by
    simpa [hgenerate] using horth
  have hq_iso : IsIso q := by
    simpa using (Triangle.isZero₃_iff_isIso₁ _ hCone).1 hzeroC
  letI : IsIso q := hq_iso
  refine ⟨X, map, Y, triangleHom, triangleConnecting, Khocolim, asIso q, hApprox, hKhocolim⟩

end
