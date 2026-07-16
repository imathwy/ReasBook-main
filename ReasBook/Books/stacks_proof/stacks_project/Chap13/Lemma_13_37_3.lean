import Mathlib
import Mathlib.Algebra.Category.Grp.AB
import stacks_proof.stacks_project.Chap04.Lemma_4_19_5
import stacks_proof.stacks_project.Chap13.Definition_13_36_3
import stacks_proof.stacks_project.Chap13.Definition_13_33_1
import stacks_proof.stacks_project.Chap13.Definition_13_37_1
import stacks_proof.stacks_project.Chap13.Lemma_13_37_2
import stacks_proof.stacks_project.Chap13.Lemma_13_33_6
import stacks_proof.stacks_project.Chap13.Remark_13_33_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open Opposite

noncomputable section

universe w v u

local instance : HasCountableCoproducts AddCommGrpCat.{v} :=
  hasCountableCoproducts_of_sequentialColimits

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

omit [HasZeroObject D] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] in
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

omit [IsTriangulated D] in
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

omit [IsTriangulated D] in
/-- Helper for Lemma 13.37.3: package `exists_next_approximation_step` as a reusable successor-step
record for the tower recursion. -/
private theorem exists_approximation_step {X A : D} (p : X ⟶ A) :
    Nonempty (ApproximationStep (E := E) p) := by
  obtain ⟨Y, y, X', f, δ, p', hY, hT, hcomp, hkernel⟩ :=
    exists_next_approximation_step (E := E) p
  exact ⟨⟨Y, y, X', f, δ, p', hY, hT, hcomp, hkernel⟩⟩

omit [IsTriangulated D] in
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

omit [IsTriangulated D] in
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

omit [IsTriangulated D] in
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
    (G : ℕ ⥤ AddCommGrpCat.{v}) (z : (colimit G : AddCommGrpCat.{v})) :
    ∃ n : ℕ, ∃ x : G.obj n, colimit.ι G n x = z := by
  -- Concrete filtered colimits in `AddCommGrpCat` are jointly covered by the stage inclusions.
  letI : IsFiltered ℕ := inferInstance
  letI : PreservesFilteredColimits (forget AddCommGrpCat) :=
    AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
  letI : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat) :=
    preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat)
  letI : PreservesColimit G (forget AddCommGrpCat) := by
    infer_instance
  exact Concrete.colimit_exists_rep G z

omit [IsTriangulated D] in
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
  obtain ⟨ι, c, hιcompat, hT⟩ :=
    IsHomotopyColimitOf.exists_presentation (S := Functor.ofSequence map) hKhocolim
  have hιcompat' : ∀ n : ℕ, map n ≫ ι (n + 1) = ι n := by
    intro n
    simpa [Functor.ofSequence_map_homOfLE_succ] using hιcompat n
  -- The compatible stage maps to `A` kill the telescope map.
  have hzero :
      sequentialTelescopeMap (Functor.ofSequence map) ≫ Limits.Sigma.desc toA = 0 := by
    exact sequentialTelescopeMap_comp_sigmaDesc
      (Functor.ofSequence map) toA (fun n ↦ by
        simpa [Functor.ofSequence_map_homOfLE_succ] using hcompat n)
  -- Exactness of the distinguished telescope triangle descends the cocone to `Khocolim`.
  obtain ⟨q, hq⟩ := Triangle.yoneda_exact₂
    (T := Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) (Limits.Sigma.desc ι)
      (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv))
    hT (Limits.Sigma.desc toA) hzero
  refine ⟨ι, c, q, hιcompat', hT, ?_⟩
  intro n
  -- Evaluating the descended equality on the `n`th coproduct summand recovers the stage map.
  have hq' := congrArg (fun f ↦ Limits.Sigma.ι X n ≫ f) hq
  calc
    ι n ≫ q = (Limits.Sigma.ι X n ≫ Limits.Sigma.desc ι) ≫ q := by
      simpa [Category.assoc] using congrArg (fun t ↦ t ≫ q) (Limits.Sigma.ι_desc ι n).symm
    _ = Limits.Sigma.ι X n ≫ Limits.Sigma.desc toA := by
      simpa [Category.assoc] using hq'.symm
    _ = toA n := by simp [Limits.Sigma.ι_desc]

omit [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] [HasCoproducts.{max u v w} D] in
/-- Helper for Lemma 13.37.3: after applying `Hom(K, -)`, the compatible maps `X n ⟶ A` form a
sequential cocone. -/
private theorem hom_colimit_cocone_naturality
    {K A : D} {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1)) (toA : ∀ n : ℕ, X n ⟶ A)
    (hcompat : ∀ n : ℕ, map n ≫ toA (n + 1) = toA n) (n : ℕ) :
    (preadditiveCoyoneda.obj (op K)).map (map n) ≫
        (preadditiveCoyoneda.obj (op K)).map (toA (n + 1)) =
      (preadditiveCoyoneda.obj (op K)).map (toA n) := by
  -- Applying `Hom(K, -)` to the stage compatibility gives the cocone relation.
  rw [← Functor.map_comp]
  rw [hcompat n]

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

omit [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] [HasCoproducts.{max u v w} D] in
/-- Helper for Lemma 13.37.3: if every map `K ⟶ A` already comes from stage `0`, then the
canonical descent map from the sequential `Hom`-colimit to `Hom_D(K, A)` is surjective. -/
private theorem hom_colimit_desc_surjective_of_stage0_surjective
    {K A : D} {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1)) (toA : ∀ n : ℕ, X n ⟶ A)
    (hcompat : ∀ n : ℕ, map n ≫ toA (n + 1) = toA n)
    (hsurj : ∀ φ : K ⟶ A, ∃ ψ : K ⟶ X 0, ψ ≫ toA 0 = φ) :
    Function.Surjective (hom_colimit_desc (K := K) map toA hcompat).hom := by
  let G : ℕ ⥤ AddCommGrpCat.{v} :=
    Functor.ofSequence (fun n ↦ (preadditiveCoyoneda.obj (op K)).map (map n))
  intro φ
  obtain ⟨ψ, hψ⟩ := hsurj φ
  refine ⟨(colimit.ι G 0).hom ψ, ?_⟩
  -- Evaluating the descended map on the stage-`0` representative recovers the chosen lift.
  have hleg :
      (((colimit.ι G 0) ≫ hom_colimit_desc (K := K) map toA hcompat).hom ψ) =
        (((hom_colimit_cocone (K := K) map toA hcompat).ι.app 0).hom ψ) := by
    simpa [hom_colimit_desc] using
      congrArg (fun k ↦ k.hom ψ)
        (colimit.ι_desc (F := G) (c := hom_colimit_cocone (K := K) map toA hcompat) (j := 0))
  exact hleg.trans (by simpa [hom_colimit_cocone] using hψ)

omit [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] [HasCoproducts.{max u v w} D] in
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
  let G : ℕ ⥤ AddCommGrpCat.{v} :=
    Functor.ofSequence (fun n ↦ (preadditiveCoyoneda.obj (op K)).map (map n))
  obtain ⟨n, ψ, rfl⟩ := exists_stage_representative_of_sequential_addCommGrp_colimit G z
  have hψtoA : ψ ≫ toA n = 0 := by
    -- Vanishing of the colimit element means the chosen stage representative already maps to `0`.
    have hleg :
        (((colimit.ι G n) ≫ hom_colimit_desc (K := K) map toA hcompat).hom ψ) =
          (((hom_colimit_cocone (K := K) map toA hcompat).ι.app n).hom ψ) := by
      simpa [hom_colimit_desc] using
        congrArg (fun k ↦ k.hom ψ)
          (colimit.ι_desc (F := G) (c := hom_colimit_cocone (K := K) map toA hcompat) (j := n))
    simpa [hom_colimit_cocone] using hleg.symm.trans hz
  have hψmap : ψ ≫ map n = 0 := hkernel n ψ hψtoA
  have hzeroStage : colimit.ι G (n + 1) ((G.map (homOfLE (Nat.le_succ n))).hom ψ) = 0 := by
    -- The next-stage representative is zero because the one-step kernel is killed.
    rw [show (G.map (homOfLE (Nat.le_succ n))).hom ψ = 0 by
      simpa [G, Functor.ofSequence_map_homOfLE_succ] using hψmap]
    change (colimit.ι G (n + 1)).hom 0 = 0
    simp
  have htransport :
      colimit.ι G n ψ = colimit.ι G (n + 1) ((G.map (homOfLE (Nat.le_succ n))).hom ψ) := by
    -- The sequential colimit identifies each stage element with its image in the next stage.
    have hw := congrArg (fun k ↦ k.hom ψ) (colimit.w G (homOfLE (Nat.le_succ n)))
    simpa [G, Functor.ofSequence_map_homOfLE_succ] using hw.symm
  exact htransport.trans hzeroStage

omit [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] [HasCoproducts.{max u v w} D] in
/-- Helper for Lemma 13.37.3: the one-step kernel-killing hypothesis makes the canonical map
from the sequential `Hom`-colimit to `Hom_D(K, A)` injective. -/
private theorem hom_colimit_desc_injective_of_kernel_killed
    {K A : D} {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1)) (toA : ∀ n : ℕ, X n ⟶ A)
    (hcompat : ∀ n : ℕ, map n ≫ toA (n + 1) = toA n)
    (hkernel : ∀ (n : ℕ) (ψ : K ⟶ X n), ψ ≫ toA n = 0 → ψ ≫ map n = 0) :
    Function.Injective (hom_colimit_desc (K := K) map toA hcompat).hom := by
  intro z₁ z₂ hEq
  -- Injectivity reduces to the zero-kernel statement by subtracting the two colimit elements.
  apply sub_eq_zero.mp
  apply hom_colimit_desc_eq_zero_of_kernel_killed map toA hcompat hkernel
  have hmap :
      (hom_colimit_desc (K := K) map toA hcompat).hom (z₁ - z₂) =
        (hom_colimit_desc (K := K) map toA hcompat).hom z₁ -
          (hom_colimit_desc (K := K) map toA hcompat).hom z₂ := by
    simpa using map_sub (hom_colimit_desc (K := K) map toA hcompat).hom z₁ z₂
  rw [hmap, hEq, sub_self]

/-- Helper for Lemma 13.37.3: the explicit image sequence under a functor is canonically the
same sequential diagram as the composite with that functor. -/
private def ofSequenceMapIsoComp {B : Type*} [Category B] {L : ℕ → D}
    (f : ∀ n : ℕ, L n ⟶ L (n + 1)) (F : D ⥤ B) :
    Functor.ofSequence (fun n ↦ F.map (f n)) ≅ Functor.ofSequence f ⋙ F where
  hom := NatTrans.ofSequence (fun n ↦ 𝟙 _) (fun n ↦ by
    -- Proof comment: the explicit image sequence and the composite sequence have the same
    -- successor maps stagewise.
    simp [Functor.ofSequence_map_homOfLE_succ])
  inv := NatTrans.ofSequence (fun n ↦ 𝟙 _) (fun n ↦ by
    -- Proof comment: the inverse uses the same identity components on every stage.
    simp [Functor.ofSequence_map_homOfLE_succ])
  hom_inv_id := by
    ext n
    simp
  inv_hom_id := by
    ext n
    simp

omit [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] in
/-- Helper for Lemma 13.37.3: the inverse coproduct comparison sends each summand inclusion to the
image of the original inclusion under an additive functor preserving countable coproducts. -/
private theorem coproductComparisonInv_ι
    {H : D ⥤ AddCommGrpCat.{v}} [PreservesColimitsOfShape (Discrete ℕ) H]
    {L : ℕ → D} (n : ℕ) :
    Sigma.ι (fun i ↦ H.obj (L i)) n ≫ (PreservesCoproduct.iso H L).inv =
      H.map (Sigma.ι L n) := by
  -- Proof comment: rewrite the preservation isomorphism through `sigmaComparison`, then cancel
  -- the inverse comparison on the right summand inclusion.
  have hhom :
      (PreservesCoproduct.iso H L).hom =
        inv (sigmaComparison H L) := by
    apply IsIso.eq_inv_of_hom_inv_id
    simpa [PreservesCoproduct.inv_hom] using
      (Iso.inv_hom_id (PreservesCoproduct.iso H L))
  have hι :
      H.map (Sigma.ι L n) ≫ (PreservesCoproduct.iso H L).hom =
        Sigma.ι (fun i ↦ H.obj (L i)) n := by
    rw [hhom]
    change H.map (Sigma.ι L n) ≫ inv (sigmaComparison H L) =
      Sigma.ι (fun i ↦ H.obj (L i)) n
    exact Limits.map_ι_comp_inv_sigmaComparison H L n
  calc
    Sigma.ι (fun i ↦ H.obj (L i)) n ≫ (PreservesCoproduct.iso H L).inv =
      (H.map (Sigma.ι L n) ≫ (PreservesCoproduct.iso H L).hom) ≫
        (PreservesCoproduct.iso H L).inv := by
          simpa [Category.assoc] using
            congrArg (fun t ↦ t ≫ (PreservesCoproduct.iso H L).inv) hι.symm
    _ = H.map (Sigma.ι L n) := by
          rw [hhom]
          simp

omit [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] in
/-- Helper for Lemma 13.37.3: the coproduct map built from the image structure maps is the
transport of the mapped coproduct desc along the inverse coproduct comparison. -/
private theorem sigmaDescEq
    {H : D ⥤ AddCommGrpCat.{v}} [PreservesColimitsOfShape (Discrete ℕ) H]
    {L : ℕ → D} {A : D} (g : ∐ L ⟶ A) :
    Limits.Sigma.desc (fun n ↦ H.map (Sigma.ι L n ≫ g)) =
      (PreservesCoproduct.iso H L).inv ≫ H.map g := by
  -- Proof comment: both coproduct maps agree on each summand after transporting the chosen
  -- inclusion through the inverse coproduct comparison.
  apply Limits.Sigma.hom_ext
  intro n
  calc
    Sigma.ι (fun i ↦ H.obj (L i)) n ≫ Limits.Sigma.desc (fun i ↦ H.map (Sigma.ι L i ≫ g)) =
      H.map (Sigma.ι L n ≫ g) := by
        rw [Limits.Sigma.ι_desc]
    _ = H.map (Sigma.ι L n) ≫ H.map g := by
        rw [Functor.map_comp]
    _ = (Sigma.ι (fun i ↦ H.obj (L i)) n ≫ (PreservesCoproduct.iso H L).inv) ≫ H.map g := by
        rw [coproductComparisonInv_ι (H := H) (L := L) (n := n)]
    _ = Sigma.ι (fun i ↦ H.obj (L i)) n ≫ ((PreservesCoproduct.iso H L).inv ≫ H.map g) := by
        simp

omit [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] in
/-- Helper for Lemma 13.37.3: the inverse coproduct comparison transports the represented-Hom
telescope map of the image sequence to the represented image of the original telescope map. -/
private theorem preadditiveCoyonedaOfSequenceTelescopeMapCompatInv
    (K : D) [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op K))]
    {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1)) :
    sequentialTelescopeMap
        (Functor.ofSequence (fun n ↦ (preadditiveCoyoneda.obj (op K)).map (map n))) ≫
        (PreservesCoproduct.iso (preadditiveCoyoneda.obj (op K)) X).inv =
      (PreservesCoproduct.iso (preadditiveCoyoneda.obj (op K)) X).inv ≫
        (preadditiveCoyoneda.obj (op K)).map
          (sequentialTelescopeMap (Functor.ofSequence map)) := by
  let H : D ⥤ AddCommGrpCat.{v} := preadditiveCoyoneda.obj (op K)
  let G : ℕ ⥤ AddCommGrpCat.{v} := Functor.ofSequence (fun m ↦ H.map (map m))
  -- Proof comment: compare both telescope maps on each coproduct summand and rewrite the summand
  -- inclusions through the inverse coproduct comparison.
  apply Limits.Sigma.hom_ext
  intro n
  have hMap :
      G.map (homOfLE (Nat.le_succ n)) =
        H.map (map n) := by
    simp [G, H, Functor.ofSequence_map_homOfLE_succ]
  have hι :
      Sigma.ι G.obj n ≫ (PreservesCoproduct.iso H X).inv =
        H.map (Sigma.ι X n) := by
    exact coproductComparisonInv_ι (H := H) (L := X) (n := n)
  have hιNext :
      Sigma.ι G.obj (n + 1) ≫ (PreservesCoproduct.iso H X).inv =
        H.map (Sigma.ι X (n + 1)) := by
    exact coproductComparisonInv_ι (H := H) (L := X) (n := n + 1)
  rw [Sigma.ι_comp_sequentialTelescopeMap_assoc (K := G) n
      (h := (PreservesCoproduct.iso H X).inv), Preadditive.sub_comp]
  rw [hι]
  rw [hMap]
  rw [Category.assoc, hιNext]
  have hRight :
      Sigma.ι (Functor.ofSequence fun m ↦ (preadditiveCoyoneda.obj (op K)).map (map m)).obj n ≫
          (PreservesCoproduct.iso (preadditiveCoyoneda.obj (op K)) X).inv ≫
            (preadditiveCoyoneda.obj (op K)).map
              (sequentialTelescopeMap (Functor.ofSequence map)) =
        H.map (Sigma.ι X n) ≫ H.map (sequentialTelescopeMap (Functor.ofSequence map)) := by
    simpa [H, G, Category.assoc] using
      congrArg
        (fun t ↦ t ≫ H.map (sequentialTelescopeMap (Functor.ofSequence map)))
        hι
  have hCore :
      H.map (Sigma.ι X n) - H.map (map n) ≫ H.map (Sigma.ι X (n + 1)) =
        H.map (Sigma.ι X n) ≫ H.map (sequentialTelescopeMap (Functor.ofSequence map)) := by
    calc
      H.map (Sigma.ι X n) - H.map (map n) ≫ H.map (Sigma.ι X (n + 1)) =
        H.map (Sigma.ι X n) - H.map (map n ≫ Sigma.ι X (n + 1)) := by
          rw [← Functor.map_comp]
      _ = H.map (Sigma.ι X n - map n ≫ Sigma.ι X (n + 1)) := by
          rw [← Functor.map_sub]
      _ = H.map (Sigma.ι X n ≫ sequentialTelescopeMap (Functor.ofSequence map)) := by
          have hSigma :
              Sigma.ι X n - map n ≫ Sigma.ι X (n + 1) =
                Sigma.ι X n ≫ sequentialTelescopeMap (Functor.ofSequence map) := by
            simpa [Functor.ofSequence_map_homOfLE_succ] using
              (Sigma.ι_comp_sequentialTelescopeMap
                (K := Functor.ofSequence map) n).symm
          exact congrArg H.map hSigma
      _ = H.map (Sigma.ι X n) ≫ H.map (sequentialTelescopeMap (Functor.ofSequence map)) := by
          simpa using
            (Functor.map_comp H (Sigma.ι X n)
              (sequentialTelescopeMap (Functor.ofSequence map)))
  exact hCore.trans hRight.symm

omit [IsTriangulated D] in
/-- Helper for Lemma 13.37.3: a distinguished telescope triangle presents the stage maps to the
homotopy colimit by the coproduct summand inclusions. -/
private theorem preadditiveCoyonedaHocolimPresentation_compat
    {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1)) {Khocolim : D}
    (g : ∐ X ⟶ Khocolim) (c : Khocolim ⟶ ∐ fun n ↦ X n⟦(1 : ℤ)⟧)
    (hT :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) g
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) ∈ distTriang D)
    (n : ℕ) :
    map n ≫ Sigma.ι X (n + 1) ≫ g = Sigma.ι X n ≫ g := by
  let S : ℕ ⥤ D := Functor.ofSequence map
  let ι : ∀ n : ℕ, S.obj n ⟶ Khocolim := fun m ↦ Sigma.ι X m ≫ g
  have hdesc : Limits.Sigma.desc ι = g := by
    apply Limits.Sigma.hom_ext
    intro m
    simpa [ι] using Limits.Sigma.ι_desc ι m
  have htriangle :
      Triangle.mk (sequentialTelescopeMap S) (Limits.Sigma.desc ι)
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) ∈ distTriang D := by
    simpa [S, hdesc] using hT
  simpa [S, Functor.ofSequence_map_homOfLE_succ, ι, Category.assoc] using
    telescopePresentation_compat (S := S) ι c htriangle n

/-- Helper for Lemma 13.37.3: the canonical stage maps into a chosen telescope presentation are the
composites `Sigma.ι X n ≫ g`. -/
private abbrev preadditiveCoyonedaHocolimLegs
    {X : ℕ → D} {Khocolim : D} (g : ∐ X ⟶ Khocolim) :
    ∀ n : ℕ, X n ⟶ Khocolim :=
  fun n ↦ Sigma.ι X n ≫ g

omit [IsTriangulated D] in
/-- Helper for Lemma 13.37.3: the stage maps of a telescope presentation satisfy the sequential
compatibility relation. -/
private theorem preadditiveCoyonedaHocolimLegsCompat
    {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1)) {Khocolim : D}
    (g : ∐ X ⟶ Khocolim) (c : Khocolim ⟶ ∐ fun n ↦ X n⟦(1 : ℤ)⟧)
    (hT :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) g
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) ∈ distTriang D) :
    ∀ n : ℕ,
      map n ≫ preadditiveCoyonedaHocolimLegs (X := X) g (n + 1) =
        preadditiveCoyonedaHocolimLegs (X := X) g n := by
  intro n
  exact preadditiveCoyonedaHocolimPresentation_compat (map := map) g c hT n

/-- Helper for Lemma 13.37.3: the represented-Hom groups on a sequential system form the canonical
sequential diagram in `AddCommGrpCat`. -/
private abbrev preadditiveCoyonedaSequence
    (K : D) {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1)) :
    ℕ ⥤ AddCommGrpCat.{v} :=
  Functor.ofSequence (fun n ↦ (preadditiveCoyoneda.obj (op K)).map (map n))

omit [IsTriangulated D] in
/-- Helper for Lemma 13.37.3: the represented-Hom maps coming from the coproduct legs of a
telescope presentation satisfy the cocone relation on the sequential image diagram. -/
private theorem preadditiveCoyonedaHocolimCoconeNaturality
    (K : D) {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1)) {Khocolim : D}
    (g : ∐ X ⟶ Khocolim) (c : Khocolim ⟶ ∐ fun n ↦ X n⟦(1 : ℤ)⟧)
    (hT :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) g
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) ∈ distTriang D)
    (n : ℕ) :
    (preadditiveCoyonedaSequence K map).map (homOfLE (Nat.le_succ n)) ≫
        (preadditiveCoyoneda.obj (op K)).map
          (preadditiveCoyonedaHocolimLegs (X := X) g (n + 1)) =
      (preadditiveCoyoneda.obj (op K)).map
        (preadditiveCoyonedaHocolimLegs (X := X) g n) := by
  simpa [preadditiveCoyonedaSequence, preadditiveCoyonedaHocolimLegs,
    Functor.ofSequence_map_homOfLE_succ] using
    hom_colimit_cocone_naturality
      (K := K) map (preadditiveCoyonedaHocolimLegs (X := X) g)
      (preadditiveCoyonedaHocolimLegsCompat (map := map) g c hT) n

/-- Helper for Lemma 13.37.3: the source-facing coproduct map of a telescope presentation is the
coproduct desc of the represented-Hom legs. -/
private abbrev preadditiveCoyonedaSigmaDesc
    (K : D) {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1)) {Khocolim : D}
    (g : ∐ X ⟶ Khocolim) :
    ∐ (preadditiveCoyonedaSequence K map).obj ⟶
      (preadditiveCoyoneda.obj (op K)).obj Khocolim :=
  Limits.Sigma.desc
    (fun n ↦
      (preadditiveCoyoneda.obj (op K)).map
        (preadditiveCoyonedaHocolimLegs (X := X) g n))

omit [IsTriangulated D] in
/-- Helper for Lemma 13.37.3: the source-facing coproduct desc of a telescope presentation kills
the represented-Hom telescope map. -/
private theorem preadditiveCoyonedaSigmaDescZero
    (K : D) {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1)) {Khocolim : D}
    (g : ∐ X ⟶ Khocolim) (c : Khocolim ⟶ ∐ fun n ↦ X n⟦(1 : ℤ)⟧)
    (hT :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) g
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) ∈ distTriang D) :
    sequentialTelescopeMap (preadditiveCoyonedaSequence K map) ≫
      preadditiveCoyonedaSigmaDesc K map g = 0 := by
  simpa [preadditiveCoyonedaSequence, preadditiveCoyonedaSigmaDesc] using
    sequentialTelescopeMap_comp_sigmaDesc
      (preadditiveCoyonedaSequence K map)
      (fun n ↦
        (preadditiveCoyoneda.obj (op K)).map
          (preadditiveCoyonedaHocolimLegs (X := X) g n))
      (preadditiveCoyonedaHocolimCoconeNaturality K map g c hT)

/-- Helper for Lemma 13.37.3: the distinguished telescope triangle induces a short complex on the
represented-Hom sequence and the source-facing coproduct desc. -/
private abbrev preadditiveCoyonedaHocolimShortComplex
    (K : D) {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1)) {Khocolim : D}
    (g : ∐ X ⟶ Khocolim) (c : Khocolim ⟶ ∐ fun n ↦ X n⟦(1 : ℤ)⟧)
    (hT :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) g
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) ∈ distTriang D) :
    ShortComplex AddCommGrpCat.{v} :=
  ShortComplex.mk
    (sequentialTelescopeMap (preadditiveCoyonedaSequence K map))
    (preadditiveCoyonedaSigmaDesc K map g)
    (preadditiveCoyonedaSigmaDescZero K map g c hT)

omit [IsTriangulated D] in
/-- Helper for Lemma 13.37.3: applying `Hom_D(K,-)` to the chosen telescope triangle makes the
source-facing represented-Hom short complex exact. -/
private theorem preadditiveCoyonedaHocolimShortComplex_exact
    (K : D) [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op K))]
    {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1)) {Khocolim : D}
    (g : ∐ X ⟶ Khocolim) (c : Khocolim ⟶ ∐ fun n ↦ X n⟦(1 : ℤ)⟧)
    (hT :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) g
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) ∈ distTriang D) :
    (preadditiveCoyonedaHocolimShortComplex K map g c hT).Exact := by
  let H : D ⥤ AddCommGrpCat.{v} := preadditiveCoyoneda.obj (op K)
  have hExact :
      ((shortComplexOfDistTriangle
        (Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) g
          (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv)) hT).map H).Exact := by
    -- Applying the represented Hom functor to the distinguished telescope triangle yields an
    -- exact short complex in `AddCommGrpCat`.
    simpa using H.map_distinguished_exact
      (Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) g
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv)) hT
  have e :
      preadditiveCoyonedaHocolimShortComplex K map g c hT ≅
        ((shortComplexOfDistTriangle
          (Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) g
            (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv)) hT).map H) := by
    refine ShortComplex.isoMk
      (PreservesCoproduct.iso H X).symm
      (PreservesCoproduct.iso H X).symm
      (Iso.refl _)
      ?_
      ?_
    · -- The first square is the inverse-oriented telescope comparison on the represented sequence.
      simpa [preadditiveCoyonedaHocolimShortComplex, preadditiveCoyonedaSequence, H,
        Category.assoc] using
        (preadditiveCoyonedaOfSequenceTelescopeMapCompatInv (K := K) map).symm
    · -- The second square rewrites the mapped coproduct desc to the source-facing sigma desc.
      simpa [preadditiveCoyonedaHocolimShortComplex, preadditiveCoyonedaSigmaDesc, H,
        Category.assoc] using
        (sigmaDescEq (H := H) (L := X) g).symm
  exact (ShortComplex.exact_iff_of_iso e).2 hExact

/-- Helper for Lemma 13.37.3: the chosen telescope presentation carries the canonical
represented-Hom comparison from the sequential colimit to `Hom_D(K, Khocolim)`. -/
private abbrev preadditiveCoyonedaHocolimComparison
    {K Khocolim : D} {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1))
    (ι : ∀ n : ℕ, X n ⟶ Khocolim)
    (hιcompat : ∀ n : ℕ, map n ≫ ι (n + 1) = ι n) :
    colimit (preadditiveCoyonedaSequence K map) ⟶
      (preadditiveCoyoneda.obj (op K)).obj Khocolim :=
  hom_colimit_desc (K := K) map ι hιcompat

omit [HasZeroObject D] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] in
/-- Helper for Lemma 13.37.3: the shift/coproduct comparison identifies each shifted coproduct
summand with the shift of the corresponding original summand. -/
private theorem shiftedFamilyCoproductComparison_ι
    {X : ℕ → D} (n : ℕ) :
    Sigma.ι (fun i ↦ X i⟦(1 : ℤ)⟧) n ≫
        sigmaComparison (shiftFunctor D (1 : ℤ)) X =
      (Sigma.ι X n)⟦(1 : ℤ)⟧' := by
  -- Proof comment: cancel the inverse shift/coproduct comparison and rewrite with the standard
  -- summand formula for `sigmaComparison`.
  apply (cancel_mono (inv (sigmaComparison (shiftFunctor D (1 : ℤ)) X))).1
  simpa [Category.assoc] using
    (Limits.map_ι_comp_inv_sigmaComparison (shiftFunctor D (1 : ℤ)) X n).symm

omit [HasZeroObject D] [Pretriangulated D] [IsTriangulated D] in
/-- Helper for Lemma 13.37.3: after transporting along the shift/coproduct comparison, the
shifted telescope map is exactly the shift of the original telescope map. -/
private theorem shiftedTelescopeMapCompatInv
    {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1)) :
    sequentialTelescopeMap (Functor.ofSequence (fun n ↦ (map n)⟦(1 : ℤ)⟧')) ≫
        sigmaComparison (shiftFunctor D (1 : ℤ)) X =
      sigmaComparison (shiftFunctor D (1 : ℤ)) X ≫
        ((sequentialTelescopeMap (Functor.ofSequence map))⟦(1 : ℤ)⟧') := by
  -- Proof comment: compare both telescope morphisms on each shifted summand before consuming the
  -- shift/coproduct comparison on the right.
  apply Limits.Sigma.hom_ext
  intro n
  have hSigmaShift :
      Sigma.ι (fun i ↦ X i⟦(1 : ℤ)⟧) n ≫
          sequentialTelescopeMap (Functor.ofSequence (fun m ↦ (map m)⟦(1 : ℤ)⟧')) =
        Sigma.ι (fun i ↦ X i⟦(1 : ℤ)⟧) n -
          (map n)⟦(1 : ℤ)⟧' ≫ Sigma.ι (fun i ↦ X i⟦(1 : ℤ)⟧) (n + 1) := by
    simpa [Functor.ofSequence_map_homOfLE_succ] using
      (Sigma.ι_comp_sequentialTelescopeMap
        (K := Functor.ofSequence (fun m ↦ (map m)⟦(1 : ℤ)⟧')) n)
  have hSigma :
      Sigma.ι X n - map n ≫ Sigma.ι X (n + 1) =
        Sigma.ι X n ≫ sequentialTelescopeMap (Functor.ofSequence map) := by
    simpa [Functor.ofSequence_map_homOfLE_succ] using
      (Sigma.ι_comp_sequentialTelescopeMap (K := Functor.ofSequence map) n).symm
  calc
    Sigma.ι (fun i ↦ X i⟦(1 : ℤ)⟧) n ≫
        sequentialTelescopeMap (Functor.ofSequence (fun m ↦ (map m)⟦(1 : ℤ)⟧')) ≫
          sigmaComparison (shiftFunctor D (1 : ℤ)) X =
      (Sigma.ι (fun i ↦ X i⟦(1 : ℤ)⟧) n ≫
          sequentialTelescopeMap (Functor.ofSequence (fun m ↦ (map m)⟦(1 : ℤ)⟧'))) ≫
            sigmaComparison (shiftFunctor D (1 : ℤ)) X := by
          rw [Category.assoc]
    _ =
      (Sigma.ι (fun i ↦ X i⟦(1 : ℤ)⟧) n -
          (map n)⟦(1 : ℤ)⟧' ≫ Sigma.ι (fun i ↦ X i⟦(1 : ℤ)⟧) (n + 1)) ≫
            sigmaComparison (shiftFunctor D (1 : ℤ)) X := by
          exact congrArg (fun t ↦ t ≫ sigmaComparison (shiftFunctor D (1 : ℤ)) X) hSigmaShift
    _ =
      (Sigma.ι (fun i ↦ X i⟦(1 : ℤ)⟧) n ≫ sigmaComparison (shiftFunctor D (1 : ℤ)) X) -
        ((map n)⟦(1 : ℤ)⟧' ≫ Sigma.ι (fun i ↦ X i⟦(1 : ℤ)⟧) (n + 1) ≫
          sigmaComparison (shiftFunctor D (1 : ℤ)) X) := by
            simp [Preadditive.sub_comp, Category.assoc]
    _ =
      (Sigma.ι X n)⟦(1 : ℤ)⟧' -
        ((map n)⟦(1 : ℤ)⟧' ≫ (Sigma.ι X (n + 1))⟦(1 : ℤ)⟧') := by
            rw [shiftedFamilyCoproductComparison_ι (X := X) (n := n)]
            have hNext :
                (map n)⟦(1 : ℤ)⟧' ≫ Sigma.ι (fun i ↦ X i⟦(1 : ℤ)⟧) (n + 1) ≫
                    sigmaComparison (shiftFunctor D (1 : ℤ)) X =
                  (map n)⟦(1 : ℤ)⟧' ≫ (Sigma.ι X (n + 1))⟦(1 : ℤ)⟧' := by
              simpa [Category.assoc] using
                congrArg (fun t ↦ (map n)⟦(1 : ℤ)⟧' ≫ t)
                  (shiftedFamilyCoproductComparison_ι (X := X) (n := n + 1))
            rw [hNext]
    _ =
      ((Sigma.ι X n - map n ≫ Sigma.ι X (n + 1))⟦(1 : ℤ)⟧') := by
          rw [Functor.map_sub, Functor.map_comp]
    _ = (Sigma.ι X n ≫ sequentialTelescopeMap (Functor.ofSequence map))⟦(1 : ℤ)⟧' := by
          rw [hSigma]
          rfl
    _ =
      Sigma.ι (fun i ↦ X i⟦(1 : ℤ)⟧) n ≫
        (sigmaComparison (shiftFunctor D (1 : ℤ)) X ≫
          ((sequentialTelescopeMap (Functor.ofSequence map))⟦(1 : ℤ)⟧')) := by
          rw [Functor.map_comp]
          rw [← shiftedFamilyCoproductComparison_ι (X := X) (n := n)]
          simp

omit [IsTriangulated D] in
/-- Helper for Lemma 13.37.3: composing a stage inclusion in the represented-Hom sequential
colimit with the hocolim comparison recovers the corresponding stage leg into `Khocolim`. -/
private theorem preadditiveCoyonedaHocolimComparison_ι
    (K : D)
    {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1))
    {Khocolim : D} (ι : ∀ n : ℕ, X n ⟶ Khocolim)
    (c : Khocolim ⟶ ∐ fun n ↦ X n⟦(1 : ℤ)⟧)
    (hT :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) (Limits.Sigma.desc ι)
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) ∈ distTriang D)
    (n : ℕ) :
    colimit.ι (preadditiveCoyonedaSequence K map) n ≫
        preadditiveCoyonedaHocolimComparison (K := K) map ι
        (fun n ↦ by
          simpa [Functor.ofSequence_map_homOfLE_succ] using
            telescopePresentation_compat (S := Functor.ofSequence map) ι c hT n) =
      (preadditiveCoyoneda.obj (op K)).map (ι n) := by
  let G : ℕ ⥤ AddCommGrpCat.{v} := preadditiveCoyonedaSequence K map
  -- The local comparison is the colimit descent for the cocone with legs `Hom(K, ι n)`.
  simpa [preadditiveCoyonedaHocolimComparison, hom_colimit_desc, hom_colimit_cocone, G] using
    (colimit.ι_desc (F := G)
      (c := hom_colimit_cocone (K := K) map ι
        (fun n ↦ by
          simpa [Functor.ofSequence_map_homOfLE_succ] using
            telescopePresentation_compat (S := Functor.ofSequence map) ι c hT n))
      (j := n))

omit [IsTriangulated D] in
/-- Helper for Lemma 13.37.3: the source-facing represented-Hom coproduct desc kills the mapped
connecting morphism in the telescope triangle. -/
private theorem preadditiveCoyonedaSigmaDescMapZero
    (K : D) [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op K))]
    {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1))
    {Khocolim : D} (ι : ∀ n : ℕ, X n ⟶ Khocolim)
    (c : Khocolim ⟶ ∐ fun n ↦ X n⟦(1 : ℤ)⟧)
    (hT :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) (Limits.Sigma.desc ι)
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) ∈ distTriang D) :
    preadditiveCoyonedaSigmaDesc K map (Limits.Sigma.desc ι) ≫
        (preadditiveCoyoneda.obj (op K)).map
          (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) =
      0 := by
  let H : D ⥤ AddCommGrpCat.{v} := preadditiveCoyoneda.obj (op K)
  -- Proof comment: rewrite the source-facing sigma desc as the transported map of
  -- `Limits.Sigma.desc ι`, then use that the second and third maps in a distinguished triangle
  -- compose to zero.
  have hSigmaDesc :
      preadditiveCoyonedaSigmaDesc K map (Limits.Sigma.desc ι) =
        (PreservesCoproduct.iso H X).inv ≫ H.map (Limits.Sigma.desc ι) := by
    apply Limits.Sigma.hom_ext
    intro n
    calc
      Sigma.ι (fun i ↦ H.obj (X i)) n ≫ preadditiveCoyonedaSigmaDesc K map (Limits.Sigma.desc ι) =
          H.map (ι n) := by
            have hιdesc :
                Sigma.ι (fun i ↦ (preadditiveCoyoneda.obj (op K)).obj (X i)) n ≫
                    preadditiveCoyonedaSigmaDesc K map (Limits.Sigma.desc ι) =
                  (preadditiveCoyoneda.obj (op K)).map
                    (preadditiveCoyonedaHocolimLegs (X := X) (Limits.Sigma.desc ι) n) := by
              simpa [preadditiveCoyonedaSigmaDesc] using
                (Limits.Sigma.ι_desc
                  (fun m ↦
                    (preadditiveCoyoneda.obj (op K)).map
                      (preadditiveCoyonedaHocolimLegs (X := X) (Limits.Sigma.desc ι) m))
                  n)
            have hLeg :
                (preadditiveCoyoneda.obj (op K)).map
                    (preadditiveCoyonedaHocolimLegs (X := X) (Limits.Sigma.desc ι) n) =
                  H.map (ι n) := by
              ext φ
              change φ ≫ Sigma.ι X n ≫ Limits.Sigma.desc ι = φ ≫ ι n
              simpa [preadditiveCoyonedaHocolimLegs, Category.assoc] using
                congrArg (fun t ↦ φ ≫ t) (Limits.Sigma.ι_desc ι n)
            rw [hιdesc]
            exact hLeg
      _ =
          Sigma.ι (fun i ↦ H.obj (X i)) n ≫
            ((PreservesCoproduct.iso H X).inv ≫ H.map (Limits.Sigma.desc ι)) := by
            symm
            calc
              Sigma.ι (fun i ↦ H.obj (X i)) n ≫
                  ((PreservesCoproduct.iso H X).inv ≫ H.map (Limits.Sigma.desc ι)) =
                Sigma.ι (fun i ↦ H.obj (X i)) n ≫
                  Limits.Sigma.desc (fun j ↦ H.map (ι j)) := by
                  simpa [Functor.map_comp, Category.assoc] using
                    congrArg (fun t ↦ Sigma.ι (fun i ↦ H.obj (X i)) n ≫ t)
                      (sigmaDescEq (H := H) (L := X) (g := Limits.Sigma.desc ι)).symm
              _ = H.map (ι n) := by
                  rw [Limits.Sigma.ι_desc]
  change preadditiveCoyonedaSigmaDesc K map (Limits.Sigma.desc ι) ≫
      H.map (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) = 0
  rw [hSigmaDesc]
  calc
    _ =
      (PreservesCoproduct.iso H X).inv ≫
        (H.map (Limits.Sigma.desc ι) ≫
          H.map (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv)) := by
          rfl
    _ =
      (PreservesCoproduct.iso H X).inv ≫
        H.map
          (Limits.Sigma.desc ι ≫
            (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv)) := by
          simpa [Functor.map_comp]
    _ = 0 := by
          rw [show Limits.Sigma.desc ι ≫
              (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) = 0 by
                simpa using comp_distTriang_mor_zero₂₃ _ hT]
          simp

omit [IsTriangulated D] in
/-- Helper for Lemma 13.37.3: rotating the distinguished telescope triangle gives exactness of
the represented-Hom source-facing coproduct desc followed by the mapped connecting morphism. -/
private theorem preadditiveCoyonedaSigmaDescMapExact
    (K : D) [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op K))]
    {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1))
    {Khocolim : D} (ι : ∀ n : ℕ, X n ⟶ Khocolim)
    (c : Khocolim ⟶ ∐ fun n ↦ X n⟦(1 : ℤ)⟧)
    (hT :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) (Limits.Sigma.desc ι)
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) ∈ distTriang D) :
    (ShortComplex.mk
      (preadditiveCoyonedaSigmaDesc K map (Limits.Sigma.desc ι))
      ((preadditiveCoyoneda.obj (op K)).map
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv))
      (preadditiveCoyonedaSigmaDescMapZero (K := K) map ι c hT)).Exact := by
  let H : D ⥤ AddCommGrpCat.{v} := preadditiveCoyoneda.obj (op K)
  have hExact :
      ((shortComplexOfDistTriangle
        (Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) (Limits.Sigma.desc ι)
          (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv)).rotate
        (rot_of_distTriang _ hT)).map H).Exact := by
    -- Proof comment: rotate the distinguished telescope triangle so the source-facing coproduct
    -- map and the connecting morphism become the first two arrows.
    simpa using H.map_distinguished_exact
      (Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) (Limits.Sigma.desc ι)
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv)).rotate
      (rot_of_distTriang _ hT)
  have e :
      ShortComplex.mk
          (preadditiveCoyonedaSigmaDesc K map (Limits.Sigma.desc ι))
          (H.map (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv))
          (preadditiveCoyonedaSigmaDescMapZero (K := K) map ι c hT) ≅
        ((shortComplexOfDistTriangle
          (Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) (Limits.Sigma.desc ι)
            (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv)).rotate
          (rot_of_distTriang _ hT)).map H) := by
    refine ShortComplex.isoMk
      (PreservesCoproduct.iso H X).symm
      (Iso.refl _)
      (Iso.refl _)
      ?_
      ?_
    · -- Proof comment: the first square is exactly the sigma-desc transport rewrite.
      apply Limits.Sigma.hom_ext
      intro n
      calc
        Sigma.ι (fun i ↦ H.obj (X i)) n ≫
            ((PreservesCoproduct.iso H X).inv ≫ H.map (Limits.Sigma.desc ι)) =
          H.map (ι n) := by
            calc
              Sigma.ι (fun i ↦ H.obj (X i)) n ≫
                  ((PreservesCoproduct.iso H X).inv ≫ H.map (Limits.Sigma.desc ι)) =
                Sigma.ι (fun i ↦ H.obj (X i)) n ≫
                  Limits.Sigma.desc (fun j ↦ H.map (ι j)) := by
                  simpa [Functor.map_comp, Category.assoc] using
                    congrArg (fun t ↦ Sigma.ι (fun i ↦ H.obj (X i)) n ≫ t)
                      (sigmaDescEq (H := H) (L := X) (g := Limits.Sigma.desc ι)).symm
            _ = H.map (ι n) := by
                  rw [Limits.Sigma.ι_desc]
        _ =
          Sigma.ι (fun i ↦ H.obj (X i)) n ≫
            (preadditiveCoyonedaSigmaDesc K map (Limits.Sigma.desc ι) ≫ 𝟙 (H.obj Khocolim)) := by
            symm
            calc
              Sigma.ι (fun i ↦ H.obj (X i)) n ≫
                  (preadditiveCoyonedaSigmaDesc K map (Limits.Sigma.desc ι) ≫
                    𝟙 (H.obj Khocolim)) =
                (Sigma.ι (fun i ↦ H.obj (X i)) n ≫
                    preadditiveCoyonedaSigmaDesc K map (Limits.Sigma.desc ι)) ≫
                  𝟙 (H.obj Khocolim) := by
                    simp [Category.assoc]
              _ = H.map (ι n) := by
                  have hιdesc :
                      Sigma.ι (fun i ↦ (preadditiveCoyoneda.obj (op K)).obj (X i)) n ≫
                          preadditiveCoyonedaSigmaDesc K map (Limits.Sigma.desc ι) =
                        (preadditiveCoyoneda.obj (op K)).map
                          (preadditiveCoyonedaHocolimLegs (X := X) (Limits.Sigma.desc ι) n) := by
                    simpa [preadditiveCoyonedaSigmaDesc] using
                      (Limits.Sigma.ι_desc
                        (fun m ↦
                          (preadditiveCoyoneda.obj (op K)).map
                            (preadditiveCoyonedaHocolimLegs (X := X) (Limits.Sigma.desc ι) m))
                        n)
                  have hLeg :
                      (preadditiveCoyoneda.obj (op K)).map
                          (preadditiveCoyonedaHocolimLegs (X := X) (Limits.Sigma.desc ι) n) =
                        H.map (ι n) := by
                    ext φ
                    change φ ≫ Sigma.ι X n ≫ Limits.Sigma.desc ι = φ ≫ ι n
                    simpa [preadditiveCoyonedaHocolimLegs, Category.assoc] using
                      congrArg (fun t ↦ φ ≫ t) (Limits.Sigma.ι_desc ι n)
                  rw [hιdesc]
                  exact hLeg
    · -- Proof comment: the second square is the identity on the mapped connecting morphism.
      change 𝟙 (H.obj Khocolim) ≫ H.map (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) =
        H.map (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) ≫
          𝟙 (H.obj ((∐ X)⟦(1 : ℤ)⟧))
      simp
  exact (ShortComplex.exact_iff_of_iso e).2 hExact

omit [HasZeroObject D] [Pretriangulated D] [IsTriangulated D] in
/-- Helper for Lemma 13.37.3: after applying represented Hom, the shifted telescope map becomes
mono by transport to the ordinary telescope map of the shifted image sequence. -/
private theorem preadditiveCoyonedaShiftedTelescopeMapMono
    (K : D) [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op K))]
    {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1)) :
    Mono ((preadditiveCoyoneda.obj (op K)).map
      ((sequentialTelescopeMap (Functor.ofSequence map))⟦(1 : ℤ)⟧')) := by
  let H : D ⥤ AddCommGrpCat.{v} := preadditiveCoyoneda.obj (op K)
  let S : ℕ ⥤ D := Functor.ofSequence (fun n ↦ (map n)⟦(1 : ℤ)⟧')
  let G : ℕ ⥤ AddCommGrpCat.{v} :=
    Functor.ofSequence (fun n ↦ H.map ((map n)⟦(1 : ℤ)⟧'))
  let e : ∐ G.obj ≅ H.obj ((∐ X)⟦(1 : ℤ)⟧) :=
    (PreservesCoproduct.iso H S.obj).symm ≪≫
      H.mapIso (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).symm
  have hMonoSeq : Mono (sequentialTelescopeMap G) := by
    -- Proof comment: port the finite-prefix mono argument from the telescope short-exact owner
    -- proof, which does not need the exact-colimit hypothesis.
    let _ : HasFiniteBiproducts AddCommGrpCat.{v} := Abelian.hasFiniteBiproducts
    let _ : IsFiltered ℕ := by
      infer_instance
    let _ : AB5 AddCommGrpCat.{v} := by
      infer_instance
    let _ : AB5OfSize.{0, 0} AddCommGrpCat.{v} :=
      AB5OfSize_shrink (C := AddCommGrpCat.{v})
    let _ : HasExactColimitsOfShape ℕ AddCommGrpCat.{v} :=
      AB5OfSize.ofShape (C := AddCommGrpCat.{v}) ℕ
    let _ : (colim : (ℕ ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v}).PreservesMonomorphisms := by
      infer_instance
    have hMonoNat : Mono (finite_prefix_stage_natTrans G) := by
      have hApp : ∀ n, Mono ((finite_prefix_stage_natTrans G).app n) := by
        intro n
        change Mono (finite_prefix_stage_map G n)
        exact finite_prefix_stage_mono G n
      exact NatTrans.mono_of_mono_app (finite_prefix_stage_natTrans G)
    let _ : Mono (finite_prefix_stage_natTrans G) := hMonoNat
    exact Limits.colim.map_mono' (finite_prefix_stage_natTrans G)
      (finite_prefix_left_isColimit G) (finite_prefix_middle_isColimit G)
      (sequentialTelescopeMap G) (finite_prefix_cocone_compat G)
  let _ : Mono (sequentialTelescopeMap G) := hMonoSeq
  have hCoproduct :
      sequentialTelescopeMap G ≫ (PreservesCoproduct.iso H S.obj).inv =
        (PreservesCoproduct.iso H S.obj).inv ≫ H.map (sequentialTelescopeMap S) := by
    -- Proof comment: first transport the shifted represented telescope map across the inverse
    -- coproduct comparison for the shifted sequence itself.
    simpa [G, H, S] using
      (preadditiveCoyonedaOfSequenceTelescopeMapCompatInv
        (K := K) (X := fun n ↦ X n⟦(1 : ℤ)⟧) (map := fun n ↦ (map n)⟦(1 : ℤ)⟧'))
  have hShiftIsoInv :
      (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv =
        sigmaComparison (shiftFunctor D (1 : ℤ)) X := by
    simpa [PreservesCoproduct.inv_hom]
  have heHom :
      e.hom =
        (PreservesCoproduct.iso H S.obj).inv ≫
          H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) X) := by
    rw [show e.hom =
        (PreservesCoproduct.iso H S.obj).inv ≫
          H.map ((PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) by
      rfl]
    rw [hShiftIsoInv]
  have hShiftMap :
      H.map (sequentialTelescopeMap S) ≫ H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) X) =
        H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) X) ≫
          H.map ((sequentialTelescopeMap (Functor.ofSequence map))⟦(1 : ℤ)⟧') := by
    have hRaw :
        sequentialTelescopeMap S ≫ sigmaComparison (shiftFunctor D (1 : ℤ)) X =
          sigmaComparison (shiftFunctor D (1 : ℤ)) X ≫
            ((sequentialTelescopeMap (Functor.ofSequence map))⟦(1 : ℤ)⟧') := by
      simpa [S] using shiftedTelescopeMapCompatInv (X := X) map
    calc
      H.map (sequentialTelescopeMap S) ≫ H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) X) =
          H.map (sequentialTelescopeMap S ≫ sigmaComparison (shiftFunctor D (1 : ℤ)) X) := by
            rw [← Functor.map_comp]
      _ =
          H.map
            (sigmaComparison (shiftFunctor D (1 : ℤ)) X ≫
              ((sequentialTelescopeMap (Functor.ofSequence map))⟦(1 : ℤ)⟧')) := by
            exact congrArg H.map hRaw
      _ =
          H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) X) ≫
            H.map ((sequentialTelescopeMap (Functor.ofSequence map))⟦(1 : ℤ)⟧') := by
            rw [Functor.map_comp]
  have hTransport :
      sequentialTelescopeMap G ≫ e.hom =
        e.hom ≫ H.map ((sequentialTelescopeMap (Functor.ofSequence map))⟦(1 : ℤ)⟧') := by
    have hCoproductAssoc :
        (sequentialTelescopeMap G ≫ (PreservesCoproduct.iso H S.obj).inv) ≫
            H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) X) =
          ((PreservesCoproduct.iso H S.obj).inv ≫ H.map (sequentialTelescopeMap S)) ≫
            H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) X) := by
      exact congrArg (fun t ↦ t ≫ H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) X)) hCoproduct
    have hCoproduct' :
        sequentialTelescopeMap G ≫ (PreservesCoproduct.iso H S.obj).inv ≫
            H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) X) =
          (PreservesCoproduct.iso H S.obj).inv ≫ H.map (sequentialTelescopeMap S) ≫
            H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) X) := by
      simpa [Category.assoc] using hCoproductAssoc
    have hTransport' :
        sequentialTelescopeMap G ≫ (PreservesCoproduct.iso H S.obj).inv ≫
            H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) X) =
          (PreservesCoproduct.iso H S.obj).inv ≫
              H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) X) ≫
            H.map ((sequentialTelescopeMap (Functor.ofSequence map))⟦(1 : ℤ)⟧') := by
      have hShiftMapAssoc :
          (PreservesCoproduct.iso H S.obj).inv ≫
              (H.map (sequentialTelescopeMap S) ≫
                H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) X)) =
            (PreservesCoproduct.iso H S.obj).inv ≫
              (H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) X) ≫
                H.map ((sequentialTelescopeMap (Functor.ofSequence map))⟦(1 : ℤ)⟧')) := by
        exact congrArg (fun t ↦ (PreservesCoproduct.iso H S.obj).inv ≫ t) hShiftMap
      have hShiftMap' :
          (PreservesCoproduct.iso H S.obj).inv ≫ H.map (sequentialTelescopeMap S) ≫
              H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) X) =
            (PreservesCoproduct.iso H S.obj).inv ≫
                H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) X) ≫
              H.map ((sequentialTelescopeMap (Functor.ofSequence map))⟦(1 : ℤ)⟧') := by
        simpa [Category.assoc] using hShiftMapAssoc
      exact hCoproduct'.trans hShiftMap'
    have hTransportExpanded :
        sequentialTelescopeMap G ≫
            ((PreservesCoproduct.iso H S.obj).inv ≫
              H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) X)) =
          ((PreservesCoproduct.iso H S.obj).inv ≫
              H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) X)) ≫
            H.map ((sequentialTelescopeMap (Functor.ofSequence map))⟦(1 : ℤ)⟧') := by
      simpa [Category.assoc] using hTransport'
    have hLeft :
        sequentialTelescopeMap G ≫ e.hom =
          sequentialTelescopeMap G ≫
            ((PreservesCoproduct.iso H S.obj).inv ≫
              H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) X)) := by
      exact congrArg (fun t ↦ sequentialTelescopeMap G ≫ t) heHom
    have hRight :
        ((PreservesCoproduct.iso H S.obj).inv ≫
            H.map (sigmaComparison (shiftFunctor D (1 : ℤ)) X)) ≫
          H.map ((sequentialTelescopeMap (Functor.ofSequence map))⟦(1 : ℤ)⟧') =
        e.hom ≫ H.map ((sequentialTelescopeMap (Functor.ofSequence map))⟦(1 : ℤ)⟧') := by
      exact congrArg
        (fun t ↦ t ≫ H.map ((sequentialTelescopeMap (Functor.ofSequence map))⟦(1 : ℤ)⟧'))
        heHom.symm
    exact hLeft.trans (hTransportExpanded.trans hRight)
  have hConj' :
      e.inv ≫ sequentialTelescopeMap G ≫ e.hom =
        H.map ((sequentialTelescopeMap (Functor.ofSequence map))⟦(1 : ℤ)⟧') := by
    -- Proof comment: conjugate the ordinary telescope mono on the shifted image sequence back to
    -- the mapped shifted telescope morphism on `H.obj ((∐ X)⟦1⟧)`.
    simpa [Category.assoc] using congrArg (fun t ↦ e.inv ≫ t) hTransport
  have hConj :
      H.map ((sequentialTelescopeMap (Functor.ofSequence map))⟦(1 : ℤ)⟧') =
        e.inv ≫ sequentialTelescopeMap G ≫ e.hom := by
    simpa using hConj'.symm
  let _ : Mono e.inv := by
    infer_instance
  let _ : Mono e.hom := by
    infer_instance
  have hCompMonoLeft : Mono (e.inv ≫ sequentialTelescopeMap G) := by
    exact mono_comp e.inv (sequentialTelescopeMap G)
  have hCompMono : Mono (e.inv ≫ sequentialTelescopeMap G ≫ e.hom) := by
    let _ : Mono (e.inv ≫ sequentialTelescopeMap G) := hCompMonoLeft
    simpa [Category.assoc] using
      (show Mono ((e.inv ≫ sequentialTelescopeMap G) ≫ e.hom) from
        mono_comp (e.inv ≫ sequentialTelescopeMap G) e.hom)
  simpa only [H, hConj] using hCompMono

omit [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] in
/-- Helper for Lemma 13.37.3: applying represented Hom to the negative shifted telescope map
simply negates the mapped shifted telescope map. -/
private theorem preadditiveCoyonedaShiftedTelescopeMapNeg
    (K : D) {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1)) :
    (preadditiveCoyoneda.obj (op K)).map
        (-((sequentialTelescopeMap (Functor.ofSequence map))⟦(1 : ℤ)⟧')) =
      -(preadditiveCoyoneda.obj (op K)).map
        ((sequentialTelescopeMap (Functor.ofSequence map))⟦(1 : ℤ)⟧') := by
  -- Proof comment: represented Hom is additive, so the unique minus sign is preserved.
  rw [Functor.map_neg]

omit [IsTriangulated D] in
/-- Helper for Lemma 13.37.3: exactness of the twice-rotated mapped telescope triangle forces the
mapped connecting morphism to vanish. -/
private theorem preadditiveCoyonedaHocolimMapZero
    (K : D) [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op K))]
    {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1))
    {Khocolim : D} (ι : ∀ n : ℕ, X n ⟶ Khocolim)
    (c : Khocolim ⟶ ∐ fun n ↦ X n⟦(1 : ℤ)⟧)
    (hT :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) (Limits.Sigma.desc ι)
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) ∈ distTriang D) :
    (preadditiveCoyoneda.obj (op K)).map
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) =
      0 := by
  let H : D ⥤ AddCommGrpCat.{v} := preadditiveCoyoneda.obj (op K)
  let T : Triangle D :=
    Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) (Limits.Sigma.desc ι)
      (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv)
  -- Proof comment: exactness of the twice-rotated mapped triangle shows the second map vanishes
  -- once the negative shifted telescope map is mono.
  have hTrotrot : T.rotate.rotate ∈ distTriang D := by
    exact rot_of_distTriang _ (rot_of_distTriang _ hT)
  let shiftedMap := ((sequentialTelescopeMap (Functor.ofSequence map))⟦(1 : ℤ)⟧')
  let _ : Mono (H.map shiftedMap) := by
    simpa [H, shiftedMap] using
      (preadditiveCoyonedaShiftedTelescopeMapMono (K := K) map)
  have hMonoNeg :
      Mono (H.map (-shiftedMap)) := by
    rw [show H.map (-shiftedMap) = -H.map shiftedMap by
      simpa [H, shiftedMap] using
        (preadditiveCoyonedaShiftedTelescopeMapNeg (K := K) map)]
    infer_instance
  have hExact :
      ((shortComplexOfDistTriangle T.rotate.rotate hTrotrot).map H).Exact := by
    simpa using H.map_distinguished_exact T.rotate.rotate hTrotrot
  have hMonoG : Mono (((shortComplexOfDistTriangle T.rotate.rotate hTrotrot).map H).g) := by
    change Mono (H.map (-shiftedMap))
    exact hMonoNeg
  exact hExact.mono_g_iff.1 hMonoG

omit [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] in
/-- Helper for Lemma 13.37.3: precomposing the source-facing represented-Hom coproduct desc with
the `n`th summand recovers the represented map induced by the `n`th stage leg. -/
private theorem preadditiveCoyonedaSigmaDesc_ι
    (K : D) {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1))
    {Khocolim : D} (ι : ∀ n : ℕ, X n ⟶ Khocolim) (n : ℕ) :
    Sigma.ι (fun i ↦ (preadditiveCoyoneda.obj (op K)).obj (X i)) n ≫
        preadditiveCoyonedaSigmaDesc K map (Limits.Sigma.desc ι) =
      (preadditiveCoyoneda.obj (op K)).map (ι n) := by
  let H : D ⥤ AddCommGrpCat.{v} := preadditiveCoyoneda.obj (op K)
  -- Proof comment: evaluate the source-facing coproduct desc on the `n`th summand and then use
  -- the coproduct leg formula `Sigma.ι X n ≫ Limits.Sigma.desc ι = ι n`.
  change Sigma.ι (fun i ↦ H.obj (X i)) n ≫
      Limits.Sigma.desc (fun m ↦ H.map (Sigma.ι X m ≫ Limits.Sigma.desc ι)) =
    H.map (ι n)
  rw [Limits.Sigma.ι_desc]
  simpa using congrArg H.map (Limits.Sigma.ι_desc ι n)

omit [IsTriangulated D] in
/-- Helper for Lemma 13.37.3: once the mapped connecting morphism vanishes, the source-facing
represented-Hom coproduct desc is a cokernel of the represented telescope map. -/
private theorem preadditiveCoyonedaSigmaDescCokernel
    (K : D) [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op K))]
    {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1))
    {Khocolim : D} (ι : ∀ n : ℕ, X n ⟶ Khocolim)
    (c : Khocolim ⟶ ∐ fun n ↦ X n⟦(1 : ℤ)⟧)
    (hT :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) (Limits.Sigma.desc ι)
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) ∈ distTriang D) :
    Nonempty
      (IsColimit
        (CokernelCofork.ofπ
          (preadditiveCoyonedaSigmaDesc K map (Limits.Sigma.desc ι))
          (preadditiveCoyonedaSigmaDescZero K map (Limits.Sigma.desc ι) c hT))) := by
  let S : ShortComplex AddCommGrpCat.{v} :=
    ShortComplex.mk
      (sequentialTelescopeMap (preadditiveCoyonedaSequence K map))
      (preadditiveCoyonedaSigmaDesc K map (Limits.Sigma.desc ι))
      (preadditiveCoyonedaSigmaDescZero K map (Limits.Sigma.desc ι) c hT)
  -- Proof comment: the unrotated represented-Hom short complex is exact, and the rotated exactness
  -- plus vanishing of the mapped connecting morphism make the coproduct desc epimorphic.
  have hExact : S.Exact := by
    simpa [S] using
      preadditiveCoyonedaHocolimShortComplex_exact (K := K) map (Limits.Sigma.desc ι) c hT
  letI : Epi S.g :=
    (preadditiveCoyonedaSigmaDescMapExact (K := K) map ι c hT).epi_f_iff.2
      (preadditiveCoyonedaHocolimMapZero (K := K) map ι c hT)
  simpa [S] using
    (show Nonempty (IsColimit (CokernelCofork.ofπ S.g S.zero)) from ⟨hExact.gIsCokernel⟩)

omit [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] [HasCoproducts.{max u v w} D] in
/-- Helper for Lemma 13.37.3: every cocone on the represented sequential diagram kills the
represented telescope map. -/
private theorem preadditiveCoyonedaTargetCoconeSigmaDescZero
    (K : D) {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1))
    (s : Cocone (preadditiveCoyonedaSequence K map)) :
    sequentialTelescopeMap (preadditiveCoyonedaSequence K map) ≫
        Limits.Sigma.desc (fun n ↦ s.ι.app n) =
      0 := by
  -- Proof comment: a cocone on a sequential diagram satisfies the standard telescope relation on
  -- each successor morphism, so the telescope map factors to zero.
  simpa [preadditiveCoyonedaSequence, Functor.ofSequence_map_homOfLE_succ] using
    sequentialTelescopeMap_comp_sigmaDesc
      (preadditiveCoyonedaSequence K map)
      (fun n ↦ s.ι.app n)
      (fun n ↦ s.w (homOfLE (Nat.le_succ n)))

/-- Helper for Lemma 13.37.3: the cokernel witness on the source-facing represented-Hom coproduct
desc gives the universal morphism from `Hom_D(K, Khocolim)` to any cocone point. -/
private noncomputable def preadditiveCoyonedaHocolimCoconeDesc
    (K : D) [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op K))]
    {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1))
    {Khocolim : D} (ι : ∀ n : ℕ, X n ⟶ Khocolim)
    (c : Khocolim ⟶ ∐ fun n ↦ X n⟦(1 : ℤ)⟧)
    (hT :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) (Limits.Sigma.desc ι)
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) ∈ distTriang D)
    (s : Cocone (preadditiveCoyonedaSequence K map)) :
    (preadditiveCoyoneda.obj (op K)).obj Khocolim ⟶ s.pt :=
  let hCok := Classical.choice
    (preadditiveCoyonedaSigmaDescCokernel (K := K) map ι c hT)
  -- Proof comment: descend the target cocone through the source-facing cokernel identified above.
  hCok.desc
    (CokernelCofork.ofπ
      (Limits.Sigma.desc (fun n ↦ s.ι.app n))
      (preadditiveCoyonedaTargetCoconeSigmaDescZero (K := K) map s))

omit [IsTriangulated D] in
/-- Helper for Lemma 13.37.3: the morphism descended from the cokernel witness satisfies the
cocone-leg equations on the represented sequential diagram. -/
private theorem preadditiveCoyonedaHocolimCoconeDesc_fac
    (K : D) [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op K))]
    {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1))
    {Khocolim : D} (ι : ∀ n : ℕ, X n ⟶ Khocolim)
    (c : Khocolim ⟶ ∐ fun n ↦ X n⟦(1 : ℤ)⟧)
    (hT :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) (Limits.Sigma.desc ι)
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) ∈ distTriang D)
    (s : Cocone (preadditiveCoyonedaSequence K map)) (n : ℕ) :
    (hom_colimit_cocone (K := K) map ι
        (fun n ↦ by
          simpa [Functor.ofSequence_map_homOfLE_succ] using
            telescopePresentation_compat (S := Functor.ofSequence map) ι c hT n)).ι.app n ≫
        preadditiveCoyonedaHocolimCoconeDesc (K := K) map ι c hT s =
      s.ι.app n := by
  let hCok := Classical.choice
    (preadditiveCoyonedaSigmaDescCokernel (K := K) map ι c hT)
  have hfac :
      preadditiveCoyonedaSigmaDesc K map (Limits.Sigma.desc ι) ≫
          preadditiveCoyonedaHocolimCoconeDesc (K := K) map ι c hT s =
        Limits.Sigma.desc (fun n ↦ s.ι.app n) := by
    simpa [preadditiveCoyonedaHocolimCoconeDesc, hCok] using
      hCok.fac
        (CokernelCofork.ofπ
          (Limits.Sigma.desc (fun n ↦ s.ι.app n))
          (preadditiveCoyonedaTargetCoconeSigmaDescZero (K := K) map s))
        WalkingParallelPair.one
  have hpre :
      Sigma.ι (fun i ↦ (preadditiveCoyoneda.obj (op K)).obj (X i)) n ≫
          (preadditiveCoyonedaSigmaDesc K map (Limits.Sigma.desc ι) ≫
            preadditiveCoyonedaHocolimCoconeDesc (K := K) map ι c hT s) =
        Sigma.ι (fun i ↦ (preadditiveCoyoneda.obj (op K)).obj (X i)) n ≫
          Limits.Sigma.desc (fun n ↦ s.ι.app n) := by
    simpa [Category.assoc] using
      congrArg (fun t ↦ Sigma.ι (fun i ↦ (preadditiveCoyoneda.obj (op K)).obj (X i)) n ≫ t) hfac
  have hιleg :
      (hom_colimit_cocone (K := K) map ι
          (fun n ↦ by
            simpa [Functor.ofSequence_map_homOfLE_succ] using
              telescopePresentation_compat (S := Functor.ofSequence map) ι c hT n)).ι.app n =
        (preadditiveCoyoneda.obj (op K)).map (ι n) := by
    simp [hom_colimit_cocone]
  have hleft :
      (hom_colimit_cocone (K := K) map ι
          (fun n ↦ by
            simpa [Functor.ofSequence_map_homOfLE_succ] using
              telescopePresentation_compat (S := Functor.ofSequence map) ι c hT n)).ι.app n ≫
          preadditiveCoyonedaHocolimCoconeDesc (K := K) map ι c hT s =
        (preadditiveCoyoneda.obj (op K)).map (ι n) ≫
          preadditiveCoyonedaHocolimCoconeDesc (K := K) map ι c hT s := by
    simpa [hιleg]
  have hright :
      (preadditiveCoyoneda.obj (op K)).map (ι n) ≫
          preadditiveCoyonedaHocolimCoconeDesc (K := K) map ι c hT s =
        Sigma.ι (fun i ↦ (preadditiveCoyoneda.obj (op K)).obj (X i)) n ≫
          Limits.Sigma.desc (fun n ↦ s.ι.app n) := by
    calc
      (preadditiveCoyoneda.obj (op K)).map (ι n) ≫
          preadditiveCoyonedaHocolimCoconeDesc (K := K) map ι c hT s =
        Sigma.ι (fun i ↦ (preadditiveCoyoneda.obj (op K)).obj (X i)) n ≫
          (preadditiveCoyonedaSigmaDesc K map (Limits.Sigma.desc ι) ≫
            preadditiveCoyonedaHocolimCoconeDesc (K := K) map ι c hT s) := by
              simpa [Category.assoc] using
                congrArg
                  (fun t ↦ t ≫ preadditiveCoyonedaHocolimCoconeDesc (K := K) map ι c hT s)
                  (preadditiveCoyonedaSigmaDesc_ι (K := K) map ι n).symm
      _ = Sigma.ι (fun i ↦ (preadditiveCoyoneda.obj (op K)).obj (X i)) n ≫
            Limits.Sigma.desc (fun n ↦ s.ι.app n) := hpre
  exact hleft.trans (hright.trans (by rw [Limits.Sigma.ι_desc]))

omit [IsTriangulated D] in
/-- Helper for Lemma 13.37.3: the morphism descended from the cokernel witness is the unique map
to a target cocone point satisfying the cocone-leg equations. -/
private theorem preadditiveCoyonedaHocolimCoconeDesc_uniq
    (K : D) [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op K))]
    {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1))
    {Khocolim : D} (ι : ∀ n : ℕ, X n ⟶ Khocolim)
    (c : Khocolim ⟶ ∐ fun n ↦ X n⟦(1 : ℤ)⟧)
    (hT :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) (Limits.Sigma.desc ι)
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) ∈ distTriang D)
    (s : Cocone (preadditiveCoyonedaSequence K map))
    (m : (preadditiveCoyoneda.obj (op K)).obj Khocolim ⟶ s.pt)
    (hm :
      ∀ n : ℕ,
        (hom_colimit_cocone (K := K) map ι
            (fun n ↦ by
              simpa [Functor.ofSequence_map_homOfLE_succ] using
                telescopePresentation_compat (S := Functor.ofSequence map) ι c hT n)).ι.app n ≫
            m =
          s.ι.app n) :
    m = preadditiveCoyonedaHocolimCoconeDesc (K := K) map ι c hT s := by
  let hCok := Classical.choice
    (preadditiveCoyonedaSigmaDescCokernel (K := K) map ι c hT)
  -- Proof comment: cokernel-descended morphisms are unique once they agree after precomposition
  -- with the source-facing coproduct desc, and that agreement is checked summandwise.
  apply Cofork.IsColimit.hom_ext hCok
  apply Limits.Sigma.hom_ext
  intro n
  have hm' :
      Sigma.ι (fun i ↦ (preadditiveCoyoneda.obj (op K)).obj (X i)) n ≫
          (preadditiveCoyonedaSigmaDesc K map (Limits.Sigma.desc ι) ≫ m) =
        s.ι.app n := by
    have hιleg :
        (hom_colimit_cocone (K := K) map ι
            (fun n ↦ by
              simpa [Functor.ofSequence_map_homOfLE_succ] using
                telescopePresentation_compat (S := Functor.ofSequence map) ι c hT n)).ι.app n =
          (preadditiveCoyoneda.obj (op K)).map (ι n) := by
      simp [hom_colimit_cocone]
    calc
      Sigma.ι (fun i ↦ (preadditiveCoyoneda.obj (op K)).obj (X i)) n ≫
          (preadditiveCoyonedaSigmaDesc K map (Limits.Sigma.desc ι) ≫ m) =
        (preadditiveCoyoneda.obj (op K)).map (ι n) ≫ m := by
          simpa [Category.assoc] using
            congrArg (fun t ↦ t ≫ m) (preadditiveCoyonedaSigmaDesc_ι (K := K) map ι n)
      _ = s.ι.app n := by
          simpa [hιleg] using hm n
  have hdesc' :
      Sigma.ι (fun i ↦ (preadditiveCoyoneda.obj (op K)).obj (X i)) n ≫
          (preadditiveCoyonedaSigmaDesc K map (Limits.Sigma.desc ι) ≫
            preadditiveCoyonedaHocolimCoconeDesc (K := K) map ι c hT s) =
        s.ι.app n := by
    have hιleg :
        (hom_colimit_cocone (K := K) map ι
            (fun n ↦ by
              simpa [Functor.ofSequence_map_homOfLE_succ] using
                telescopePresentation_compat (S := Functor.ofSequence map) ι c hT n)).ι.app n =
          (preadditiveCoyoneda.obj (op K)).map (ι n) := by
      simp [hom_colimit_cocone]
    calc
      Sigma.ι (fun i ↦ (preadditiveCoyoneda.obj (op K)).obj (X i)) n ≫
          (preadditiveCoyonedaSigmaDesc K map (Limits.Sigma.desc ι) ≫
            preadditiveCoyonedaHocolimCoconeDesc (K := K) map ι c hT s) =
        (preadditiveCoyoneda.obj (op K)).map (ι n) ≫
          preadditiveCoyonedaHocolimCoconeDesc (K := K) map ι c hT s := by
            simpa [Category.assoc] using
              congrArg
                (fun t ↦ t ≫ preadditiveCoyonedaHocolimCoconeDesc (K := K) map ι c hT s)
                (preadditiveCoyonedaSigmaDesc_ι (K := K) map ι n)
      _ = s.ι.app n := by
            simpa [hιleg] using
              preadditiveCoyonedaHocolimCoconeDesc_fac (K := K) map ι c hT s n
  exact hm'.trans hdesc'.symm

/-- Helper for Lemma 13.37.3: the explicit represented-Hom cocone on `Khocolim` is a colimit
cocone for the represented sequential diagram. -/
private noncomputable def preadditiveCoyonedaHocolimCocone_isColimit
    (K : D) [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op K))]
    {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1))
    {Khocolim : D} (ι : ∀ n : ℕ, X n ⟶ Khocolim)
    (c : Khocolim ⟶ ∐ fun n ↦ X n⟦(1 : ℤ)⟧)
    (hT :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) (Limits.Sigma.desc ι)
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) ∈ distTriang D) :
    IsColimit
      (hom_colimit_cocone (K := K) map ι
        (fun n ↦ by
          simpa [Functor.ofSequence_map_homOfLE_succ] using
            telescopePresentation_compat (S := Functor.ofSequence map) ι c hT n)) :=
  -- Proof comment: package the descended morphism together with its leg equations and uniqueness
  -- as the explicit colimit witness on the represented sequential cocone.
  IsColimit.mk
    (preadditiveCoyonedaHocolimCoconeDesc (K := K) map ι c hT)
    (preadditiveCoyonedaHocolimCoconeDesc_fac (K := K) map ι c hT)
    (preadditiveCoyonedaHocolimCoconeDesc_uniq (K := K) map ι c hT)

omit [IsTriangulated D] in
/-- Helper for Lemma 13.37.3: compactness of `K` identifies the represented Hom out of the chosen
homotopy colimit with the sequential colimit of represented Hom groups. -/
private theorem preadditiveCoyonedaHocolimComparison_isIsoAdapter
    (K : D) [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op K))]
    {X : ℕ → D} (map : ∀ n : ℕ, X n ⟶ X (n + 1))
    {Khocolim : D} (ι : ∀ n : ℕ, X n ⟶ Khocolim)
    (c : Khocolim ⟶ ∐ fun n ↦ X n⟦(1 : ℤ)⟧)
    (hT :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence map)) (Limits.Sigma.desc ι)
        (c ≫ (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) X).inv) ∈ distTriang D) :
    IsIso (preadditiveCoyonedaHocolimComparison (K := K) map ι
      (fun n ↦ by
        simpa [Functor.ofSequence_map_homOfLE_succ] using
          telescopePresentation_compat (S := Functor.ofSequence map) ι c hT n)) := by
  let G : ℕ ⥤ AddCommGrpCat.{v} := preadditiveCoyonedaSequence K map
  let hColim :=
    preadditiveCoyonedaHocolimCocone_isColimit (K := K) map ι c hT
  -- Proof comment: both the standard colimit cocone and the explicit represented-Hom cocone on
  -- `Khocolim` are colimiting, so the comparison is their unique cocone-point isomorphism.
  let e :
      colimit G ≅ (preadditiveCoyoneda.obj (op K)).obj Khocolim :=
    (colimit.isColimit G).coconePointUniqueUpToIso hColim
  have hcomparison :
      preadditiveCoyonedaHocolimComparison (K := K) map ι
          (fun n ↦ by
            simpa [Functor.ofSequence_map_homOfLE_succ] using
              telescopePresentation_compat (S := Functor.ofSequence map) ι c hT n) =
        e.hom := by
    apply colimit.hom_ext
    intro n
    have hleft :
        colimit.ι G n ≫
            preadditiveCoyonedaHocolimComparison (K := K) map ι
              (fun n ↦ by
                simpa [Functor.ofSequence_map_homOfLE_succ] using
                  telescopePresentation_compat (S := Functor.ofSequence map) ι c hT n) =
          (hom_colimit_cocone (K := K) map ι
              (fun n ↦ by
                simpa [Functor.ofSequence_map_homOfLE_succ] using
                  telescopePresentation_compat (S := Functor.ofSequence map) ι c hT n)).ι.app n := by
      simpa [preadditiveCoyonedaHocolimComparison, hom_colimit_desc, hom_colimit_cocone, G] using
        (colimit.ι_desc
          (hom_colimit_cocone (K := K) map ι
            (fun n ↦ by
              simpa [Functor.ofSequence_map_homOfLE_succ] using
                telescopePresentation_compat (S := Functor.ofSequence map) ι c hT n))
          (j := n))
    have hright :
        colimit.ι G n ≫ e.hom =
          (hom_colimit_cocone (K := K) map ι
              (fun n ↦ by
                simpa [Functor.ofSequence_map_homOfLE_succ] using
                  telescopePresentation_compat (S := Functor.ofSequence map) ι c hT n)).ι.app n := by
      simpa [e] using
        IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit G) hColim n
    exact hleft.trans hright.symm
  rw [hcomparison]
  infer_instance

omit [IsTriangulated D] [HasCoproducts.{max u v w} D] in
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

omit [IsTriangulated D] in
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
    preadditiveCoyonedaHocolimComparison (K := K) map ι
        (fun n ↦ by
          simpa [Functor.ofSequence_map_homOfLE_succ] using
            telescopePresentation_compat (S := Functor.ofSequence map) ι c hT n) ≫
      (preadditiveCoyoneda.obj (op K)).map q =
        hom_colimit_desc (K := K) map toA hcompat := by
  let G : ℕ ⥤ AddCommGrpCat.{v} :=
    preadditiveCoyonedaSequence K map
  -- Compare the two colimit-desc maps on each stage inclusion of the sequential `Hom` colimit.
  apply colimit.hom_ext
  intro n
  have hcomparisonLeg :
      colimit.ι G n ≫
          preadditiveCoyonedaHocolimComparison (K := K) map ι
            (fun n ↦ by
              simpa [Functor.ofSequence_map_homOfLE_succ] using
                telescopePresentation_compat (S := Functor.ofSequence map) ι c hT n) =
        (preadditiveCoyoneda.obj (op K)).map (ι n) := by
    -- Reuse the stage-leg computation for the hocolim comparison instead of re-expanding it.
    simpa [G] using preadditiveCoyonedaHocolimComparison_ι (K := K) map ι c hT n
  have hcomparison :
      colimit.ι G n ≫
          preadditiveCoyonedaHocolimComparison (K := K) map ι
            (fun n ↦ by
              simpa [Functor.ofSequence_map_homOfLE_succ] using
                telescopePresentation_compat (S := Functor.ofSequence map) ι c hT n) ≫
              (preadditiveCoyoneda.obj (op K)).map q =
        (preadditiveCoyoneda.obj (op K)).map (toA n) := by
    -- Postcomposing the `n`th stage leg with `q` gives `Hom(K, toA n)` by the stagewise
    -- compatibility `hq`.
    calc
      colimit.ι G n ≫
          preadditiveCoyonedaHocolimComparison (K := K) map ι
            (fun n ↦ by
              simpa [Functor.ofSequence_map_homOfLE_succ] using
                telescopePresentation_compat (S := Functor.ofSequence map) ι c hT n) ≫
              (preadditiveCoyoneda.obj (op K)).map q =
        (preadditiveCoyoneda.obj (op K)).map (ι n) ≫ (preadditiveCoyoneda.obj (op K)).map q := by
          simpa [Category.assoc] using
            congrArg (fun t ↦ t ≫ (preadditiveCoyoneda.obj (op K)).map q) hcomparisonLeg
      _ = (preadditiveCoyoneda.obj (op K)).map (ι n ≫ q) := by
          rw [← Functor.map_comp]
      _ = (preadditiveCoyoneda.obj (op K)).map (toA n) := by rw [hq n]
  have hdesc :
      colimit.ι G n ≫ hom_colimit_desc (K := K) map toA hcompat =
        (preadditiveCoyoneda.obj (op K)).map (toA n) := by
    -- The local descent map is the colimit descent for the cocone with legs `Hom(K, toA n)`.
    simpa [hom_colimit_desc, hom_colimit_cocone, G] using
      (colimit.ι_desc (F := G) (c := hom_colimit_cocone (K := K) map toA hcompat) (j := n))
  exact hcomparison.trans hdesc.symm

omit [IsTriangulated D] in
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
  intro i m
  let G : ℕ ⥤ AddCommGrpCat.{v} :=
    preadditiveCoyonedaSequence (E i⟦m⟧) map
  let hcompat' : ∀ n : ℕ, map n ≫ ι (n + 1) = ι n := fun n ↦ by
    simpa [Functor.ofSequence_map_homOfLE_succ] using
      telescopePresentation_compat (S := Functor.ofSequence map) ι c hT n
  let comparison :
      colimit G ⟶ (preadditiveCoyoneda.obj (op (E i⟦m⟧))).obj Khocolim :=
    preadditiveCoyonedaHocolimComparison (K := E i⟦m⟧) map ι hcompat'
  letI : PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op (E i⟦m⟧))) :=
    shifted_generator_preserves_countable_coproducts (E := E) hcompact i m
  have hcomparison : IsIso comparison := by
    simpa [comparison] using
      preadditiveCoyonedaHocolimComparison_isIsoAdapter (E i⟦m⟧) map ι c hT
  have hcomparisonBij : Function.Bijective comparison.hom :=
    (ConcreteCategory.isIso_iff_bijective comparison).1 hcomparison
  have hdescSurj :
      Function.Surjective (hom_colimit_desc (K := E i⟦m⟧) map toA hcompat).hom := by
    exact hom_colimit_desc_surjective_of_stage0_surjective
      (K := E i⟦m⟧) map toA hcompat (hsurj i m)
  have hdescInj :
      Function.Injective (hom_colimit_desc (K := E i⟦m⟧) map toA hcompat).hom := by
    refine hom_colimit_desc_injective_of_kernel_killed map toA hcompat ?_
    intro n ψ hψ
    exact hkernel n i m ψ hψ
  have hdescBij :
      Function.Bijective (hom_colimit_desc (K := E i⟦m⟧) map toA hcompat).hom :=
    ⟨hdescInj, hdescSurj⟩
  have hcompEq :
      comparison ≫ (preadditiveCoyoneda.obj (op (E i⟦m⟧))).map q =
        hom_colimit_desc (K := E i⟦m⟧) map toA hcompat :=
    preadditiveCoyoneda_hocolim_comparison_comp_map_eq_hom_colimit_desc
      map ι c hT q toA hcompat hq
  have hqBij :
      Function.Bijective (((preadditiveCoyoneda.obj (op (E i⟦m⟧))).map q).hom) := by
    constructor
    · intro f₁ f₂ hEq
      obtain ⟨z₁, rfl⟩ := hcomparisonBij.2 f₁
      obtain ⟨z₂, rfl⟩ := hcomparisonBij.2 f₂
      have hz :
          ((comparison ≫ (preadditiveCoyoneda.obj (op (E i⟦m⟧))).map q).hom z₁) =
            ((comparison ≫ (preadditiveCoyoneda.obj (op (E i⟦m⟧))).map q).hom z₂) := hEq
      rw [hcompEq] at hz
      have hz' : z₁ = z₂ := hdescBij.1 hz
      simpa [hz']
    · intro φ
      obtain ⟨z, hz⟩ := hdescBij.2 φ
      refine ⟨comparison.hom z, ?_⟩
      change ((comparison ≫ (preadditiveCoyoneda.obj (op (E i⟦m⟧))).map q).hom z) = φ
      rw [hcompEq]
      exact hz
  exact (ConcreteCategory.isIso_iff_bijective _).2 hqBij

omit [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D] [HasCoproducts.{max u v w} D] in
/-- Helper for Lemma 13.37.3: if `Hom(E i⟦m⟧, q)` is an isomorphism for every shifted generator,
then postcomposition with `q` is bijective for every source in the shift-closure of the family. -/
private theorem shifted_generator_postcompose_bijective
    {A B X : D} (q : A ⟶ B)
    (hqIso : ∀ i : I, ∀ m : ℤ, IsIso ((preadditiveCoyoneda.obj (op (E i⟦m⟧))).map q))
    (hX : ((ObjectProperty.ofObj E).shiftClosure ℤ) X) :
    Function.Bijective (fun f : X ⟶ A ↦ f ≫ q) := by
  rcases hX with ⟨_, n, e, hY⟩
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
      f₁ = e.hom ≫ (e.inv ≫ f₁) := by simp
      _ = e.hom ≫ (e.inv ≫ f₂) := by rw [hsrc]
      _ = f₂ := by simp
  · intro g
    obtain ⟨ψ, hψ⟩ := hbij.2 (e.inv ≫ g)
    refine ⟨e.hom ≫ ψ, ?_⟩
    calc
      (e.hom ≫ ψ) ≫ q = e.hom ≫ (ψ ≫ q) := by simp
      _ = e.hom ≫ ((fun f ↦ f ≫ q) ψ) := by rfl
      _ = e.hom ≫ (e.inv ≫ g) := by rw [hψ]
      _ = g := by simp

omit [IsTriangulated D] [HasCoproducts.{max u v w} D] in
/-- Helper for Lemma 13.37.3: once `q` is generatorwise an isomorphism on `Hom`, the cone of a
distinguished triangle on `q` is right-orthogonal to the entire shift-closure of the family. -/
private theorem comparison_cone_rightOrthogonal
    {Khocolim A C : D} (q : Khocolim ⟶ A) (v : A ⟶ C) (δ : C ⟶ Khocolim⟦(1 : ℤ)⟧)
    (hT : Triangle.mk q v δ ∈ distTriang D)
    (hqIso : ∀ i : I, ∀ m : ℤ, IsIso ((preadditiveCoyoneda.obj (op (E i⟦m⟧))).map q)) :
    ((ObjectProperty.ofObj E).shiftClosure ℤ).rightOrthogonal C := by
  let P : ObjectProperty D := (ObjectProperty.ofObj E).shiftClosure ℤ
  have hcol : P.isColocal q := by
    intro Z hZ
    exact shifted_generator_postcompose_bijective (E := E) q hqIso hZ
  rw [P.rightOrthogonal_iff]
  intro B f hB
  have hinjShift :
      Function.Injective (fun h : B ⟶ Khocolim⟦(1 : ℤ)⟧ ↦ h ≫ q⟦(1 : ℤ)⟧') := by
    intro h₁ h₂ hh
    let adj := (shiftEquiv D (1 : ℤ)).symm.toAdjunction
    let e₁ := adj.homEquiv B Khocolim
    let e₂ := adj.homEquiv B A
    obtain ⟨g₁, rfl⟩ := e₁.surjective h₁
    obtain ⟨g₂, rfl⟩ := e₁.surjective h₂
    have hg : g₁ ≫ q = g₂ ≫ q := by
      apply e₂.injective
      change e₂ (g₁ ≫ q) = e₂ (g₂ ≫ q)
      rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_right]
      exact hh
    have hg' : g₁ = g₂ := (hcol _ (P.le_shift (-1) _ hB)).1 hg
    change e₁ g₁ = e₁ g₂
    exact congrArg e₁ hg'
  have hf_zero : f ≫ δ = 0 := by
    -- Shifted injectivity kills the connecting morphism out of every object of the shift-closure.
    have hδq : δ ≫ q⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
    apply hinjShift
    simpa [Category.assoc] using congrArg (fun h ↦ f ≫ h) hδq
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₃ (T := Triangle.mk q v δ) hT f hf_zero
  obtain ⟨k, hk⟩ := (hcol _ hB).2 g
  -- Surjectivity for postcomposition by `q` reduces `f` to the zero composite in the triangle.
  calc
    f = g ≫ v := hg
    _ = (k ≫ q) ≫ v := by
          simpa using congrArg (fun t ↦ t ≫ v) hk.symm
    _ = k ≫ (q ≫ v) := by simp [Category.assoc]
    _ = 0 := by
          have hqv0 : k ≫ q ≫ v = 0 := by
            calc
              k ≫ q ≫ v = k ≫ 0 := by
                exact congrArg (fun t ↦ k ≫ t) (comp_distTriang_mor_zero₁₂ _ hT)
              _ = 0 := by simp
          simpa [Category.assoc] using hqv0

-- Proof sketch: choose the canonical approximation tower built from all maps from shifts of the
-- compact generators into `X` and into the successive kernels of the maps to `X`. Lemma 13.33.9
-- identifies maps from each compact generator into the homotopy colimit with the colimit of maps
-- into the stages, so the cone of the comparison map to `X` is right-orthogonal to all shifts of
-- the family. The generating hypothesis then forces that cone to be zero.
omit [IsTriangulated D] in
/-- Lemma 13.37.3: if each `E i` is compact and the shifts of the family `E` generate `D`, then
every object `X` admits a sequential resolution whose initial term and successive cones are direct
sums of shifts of the `E i`, and whose chosen homotopy colimit is equipped with an isomorphism to
`X`. The index `0` of the resolution corresponds to the textbook term `X₁`. -/
@[stacks 09SN]
theorem exists_generating_family_resolution
    (hcompact : ∀ i : I, IsCompactObject (E i)) (hgenerate : IsGeneratingFamily E) (A : D) :
    ∃ (X : ℕ → D) (map : ∀ n : ℕ, X n ⟶ X (n + 1))
      (Y : ℕ → D) (triangleHom : ∀ n : ℕ, Y n ⟶ X n)
      (triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧) (Khocolim : D)
      (_e : Khocolim ≅ A),
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
