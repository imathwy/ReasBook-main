import Mathlib
import StacksProject_2024.stacks_project.Chap11.Definition_11_5_2
import StacksProject_2024.stacks_project.Chap11.Definition_11_8_1
import StacksProject_2024.stacks_project.Chap11.Lemma_11_5_1
import StacksProject_2024.stacks_project.Chap11.Theorem_11_7_1
import StacksProject_2024.stacks_project.Chap11.Lemma_11_7_4
import StacksProject_2024.stacks_project.Chap11.Lemma_11_8_3
import StacksProject_2024.stacks_project.Chap11.Theorem_11_8_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

/- Domain-style sampling for Proposition 11.8.5:
- primary domain: separable maximal subfields and finite separable splitting fields for finite
  central simple algebras and their Brauer classes;
- sampled owner declarations:
  `Br`,
  `IsMaximalSubfield`,
  `CSA.IsSplitBy`,
  `CSA.isSplitBy_iff_of_isBrauerEquivalent`,
  `BrauerGroup.IsSplitBy`;
- best owner abstraction: the representative-level splitting notion is canonically owned by
  `CSA.IsSplitBy`, while the source-facing Brauer-class surface in this chapter is `Br(k)`;
  the Brauer-group statement should therefore be a quotient-level bridge on `Br(k)` built from
  the representative owner, rather than a parallel wrapper vocabulary;
- primitive data: a maximal subfield `K : Subalgebra k D` in the division-algebra case, and the
  owner predicate `A.IsSplitBy L` for scalar extensions of a representative `A : CSA k`;
- derived API: the quotient-level bridge `BrauerGroup.IsSplitBy` and the induced existence theorem
  for classes `A : Br(k)`.

Source/core/bridge triage:
- `source-facing`: existence of a separable maximal subfield and existence of a finite separable
  splitting field;
- `core/canonical`: `CSA.IsSplitBy`;
- `bridge/view`: the quotient-level predicate `BrauerGroup.IsSplitBy` and the descent from
  representatives to Brauer classes. -/

section

open JacobsonNoether
open Subalgebra

variable {k : Type u} [Field k]
variable {D : Type v} [DivisionRing D] [Algebra k D] [FiniteDimensional k D]
  [Algebra.IsCentral k D]

/-- Helper for Proposition 11.8.5: inverses stay in the centralizer of a subalgebra. -/
lemma inv_mem_centralizer_of_mem_centralizer (K : Subalgebra k D) {x : D}
    (hx : x ∈ Subalgebra.centralizer k (K : Set D)) :
    x⁻¹ ∈ Subalgebra.centralizer k (K : Set D) := by
  -- The centralizer is stable under inversion because commuting with `x` is equivalent to
  -- commuting with `x⁻¹`.
  rw [Subalgebra.mem_centralizer_iff] at hx ⊢
  intro y hy
  by_cases hx0 : x = 0
  · simp [hx0]
  · calc
      y * x⁻¹ = (x⁻¹ * x) * y * x⁻¹ := by rw [inv_mul_cancel₀ hx0, one_mul]
      _ = x⁻¹ * (x * y) * x⁻¹ := by simp [mul_assoc]
      _ = x⁻¹ * (y * x) * x⁻¹ := by rw [hx y hy]
      _ = x⁻¹ * y * (x * x⁻¹) := by simp [mul_assoc]
      _ = x⁻¹ * y := by rw [mul_inv_cancel₀ hx0, mul_one]

/-- Helper for Proposition 11.8.5: choose a separable `k`-subfield of maximal `k`-dimension. -/
lemma exists_finrank_maximal_separable_subfield :
    ∃ K : Subalgebra k D, IsField K ∧ Algebra.IsSeparable k K ∧
      ∀ L : Subalgebra k D, IsField L → Algebra.IsSeparable k L →
        Module.finrank k L ≤ Module.finrank k K := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ K : Subalgebra k D, IsField K ∧ Algebra.IsSeparable k K ∧ Module.finrank k K = n
  have hbotField : IsField (⊥ : Subalgebra k D) := by
    -- The bottom subalgebra is just a copy of the base field.
    exact (Algebra.botEquiv k D).symm.toMulEquiv.isField (Field.toIsField k)
  have hbotSep : Algebra.IsSeparable k (⊥ : Subalgebra k D) := by
    -- Separable self-extensions are preserved by the canonical bottom equivalence.
    exact (AlgEquiv.Algebra.isSeparable_iff (Algebra.botEquiv k D)).2 inferInstance
  have hP : P 1 := by
    refine ⟨⊥, hbotField, hbotSep, ?_⟩
    simpa using (Subalgebra.finrank_bot : Module.finrank k (⊥ : Subalgebra k D) = 1)
  let n := Nat.findGreatest P (Module.finrank k D)
  have hnP : P n := by
    exact Nat.findGreatest_spec (Module.finrank_pos : 1 ≤ Module.finrank k D) hP
  rcases hnP with ⟨K, hKfield, hKsep, rfl⟩
  refine ⟨K, hKfield, hKsep, ?_⟩
  intro L hLfield hLsep
  have hbound : Module.finrank k L ≤ Module.finrank k D := by
    simpa using Submodule.finrank_le (Subalgebra.toSubmodule L)
  exact Nat.le_findGreatest hbound ⟨L, hLfield, hLsep, rfl⟩

/-- Helper for Proposition 11.8.5: a commutative subfield lies in its own centralizer. -/
lemma self_le_centralizer_of_isField
    (K : Subalgebra k D) (hKfield : IsField K) :
    K ≤ Subalgebra.centralizer k (K : Set D) := by
  -- Elements of a field subalgebra commute with each other, so each lies in the centralizer.
  intro x hx
  rw [Subalgebra.mem_centralizer_iff]
  intro y hy
  simpa using mul_comm (⟨x, hx⟩ : K) (⟨y, hy⟩ : K)

/-- Helper for Proposition 11.8.5: the chosen subfield includes into its centralizer. -/
noncomputable def centralizerSubfieldInclusion
    (K : Subalgebra k D) (hKfield : IsField K) :
    K →ₐ[k] Subalgebra.centralizer k (K : Set D) :=
  Subalgebra.inclusion (self_le_centralizer_of_isField (k := k) (D := D) K hKfield)

/-- Helper for Proposition 11.8.5: the centralizer of a subfield is central over that subfield. -/
lemma centralizer_isCentral_over_subfield
    (K : Subalgebra k D) (hKfield : IsField K) :
    let C := Subalgebra.centralizer k (K : Set D)
    letI : Algebra K C :=
      (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
    Algebra.IsCentral K C := by
  let C := Subalgebra.centralizer k (K : Set D)
  let iKC := centralizerSubfieldInclusion (k := k) (D := D) K hKfield
  letI : Field K := hKfield.toField
  letI : Algebra K C := iKC.toRingHom.toAlgebra
  let A : CSA.{u, v} k := CSA.mk (AlgCat.of k D)
  have hCC : Subalgebra.centralizer k (C : Set D) = K := by
    -- The double-centralizer theorem identifies the center of `C` with the original subfield `K`.
    simpa [A, C] using
      (Subalgebra.centralizer_centralizer_eq (k := k) (A := A) (B := K))
  refine ⟨fun x hx ↦ ?_⟩
  have hxC :
      x.1 ∈ Subalgebra.centralizer k (C : Set D) := by
    -- A central element of `C` commutes with every element of `C` when viewed inside `D`.
    rw [Subalgebra.mem_centralizer_iff]
    rw [Subalgebra.mem_center_iff] at hx
    intro y hy
    exact congrArg Subtype.val (hx ⟨y, hy⟩)
  have hxK : x.1 ∈ K := by
    simpa [hCC] using hxC
  rw [Algebra.mem_bot]
  refine ⟨⟨x.1, hxK⟩, ?_⟩
  -- The bottom `K`-subalgebra of `C` is exactly the image of the inclusion `K ↪ C`.
  ext
  rfl

/-- Helper for Proposition 11.8.5: if the ambient centralizer is strictly larger than `K`, then
the induced `K`-algebra structure on the centralizer is proper. -/
lemma centralizer_bot_ne_top_of_nontrivial
    (K : Subalgebra k D) (hKfield : IsField K)
    (hCK : Subalgebra.centralizer k (K : Set D) ≠ K) :
    let C := Subalgebra.centralizer k (K : Set D)
    letI : Algebra K C :=
      (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
    (⊥ : Subalgebra K C) ≠ ⊤ := by
  let C := Subalgebra.centralizer k (K : Set D)
  let iKC := centralizerSubfieldInclusion (k := k) (D := D) K hKfield
  letI : Field K := hKfield.toField
  letI : Algebra K C := iKC.toRingHom.toAlgebra
  have hlt : K < C := by
    -- Properness of the ambient centralizer gives an element of `C` outside `K`.
    refine lt_of_le_of_ne
      (self_le_centralizer_of_isField (k := k) (D := D) K hKfield) ?_
    simpa [C] using hCK.symm
  rcases SetLike.exists_of_lt hlt with ⟨x, hxC, hxK⟩
  let xC : C := ⟨x, hxC⟩
  intro hbot
  have hxbot : xC ∈ (⊥ : Subalgebra K C) := by
    simpa [hbot] using (show xC ∈ (⊤ : Subalgebra K C) from by simp)
  rw [Algebra.mem_bot] at hxbot
  rcases hxbot with ⟨a, ha⟩
  have hxa : x = (a : K) := congrArg Subtype.val ha
  exact hxK (hxa ▸ a.2)

/-- Helper for Proposition 11.8.5: adjoining a centralizer element over `K` gives a canonical
`k`-algebra map back to the ambient division ring. -/
noncomputable def adjoinRootToAmbient_of_centralizer_element
    (K : Subalgebra k D) (hKfield : IsField K) :
    let C := Subalgebra.centralizer k (K : Set D)
    letI : Field K := hKfield.toField
    letI : Algebra K C :=
      (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
    (x : C) → AdjoinRoot (minpoly K x) →ₐ[k] D :=
  let C := Subalgebra.centralizer k (K : Set D)
  letI : Field K := hKfield.toField
  letI : Algebra K C :=
    (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
  fun x ↦
    C.val.comp <|
      AlgHom.restrictScalars k <|
        AdjoinRoot.liftAlgHom (minpoly K x) (algebraMap K C) x (minpoly.aeval K x)

/-- Helper for Proposition 11.8.5: the distinguished root of the simple extension is sent to the
chosen centralizer element. -/
lemma adjoinRootToAmbient_of_centralizer_element_root
    (K : Subalgebra k D) (hKfield : IsField K) :
    let C := Subalgebra.centralizer k (K : Set D)
    letI : Field K := hKfield.toField
    letI : Algebra K C :=
      (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
    ∀ x : C,
      adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x
          (AdjoinRoot.root (minpoly K x)) = x.1 := by
  let C := Subalgebra.centralizer k (K : Set D)
  letI : Field K := hKfield.toField
  letI : Algebra K C :=
    (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
  intro x
  -- The `AdjoinRoot` lift is defined by sending the distinguished root to `x`.
  simp [adjoinRootToAmbient_of_centralizer_element, AdjoinRoot.liftAlgHom_root]

/-- Helper for Proposition 11.8.5: the simple-extension range still contains the original
subfield `K`. -/
lemma subfield_le_adjoinRoot_range_of_centralizer_element
    (K : Subalgebra k D) (hKfield : IsField K) :
    let C := Subalgebra.centralizer k (K : Set D)
    letI : Field K := hKfield.toField
    letI : Algebra K C :=
      (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
    ∀ x : C,
      K ≤ (adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range := by
  let C := Subalgebra.centralizer k (K : Set D)
  letI : Field K := hKfield.toField
  letI : Algebra K C :=
    (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
  intro x a ha
  refine ⟨algebraMap K (AdjoinRoot (minpoly K x)) ⟨a, ha⟩, ?_⟩
  -- Coefficients from `K` land in the range by the defining formula of the lift.
  simp [adjoinRootToAmbient_of_centralizer_element]

/-- Helper for Proposition 11.8.5: the chosen centralizer element itself belongs to the
simple-extension range in `D`. -/
lemma centralizer_element_mem_adjoinRoot_range_of_centralizer_element
    (K : Subalgebra k D) (hKfield : IsField K) :
    let C := Subalgebra.centralizer k (K : Set D)
    letI : Field K := hKfield.toField
    letI : Algebra K C :=
      (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
    ∀ x : C,
      x.1 ∈ (adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range := by
  let C := Subalgebra.centralizer k (K : Set D)
  letI : Field K := hKfield.toField
  letI : Algebra K C :=
    (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
  intro x
  refine ⟨AdjoinRoot.root (minpoly K x), ?_⟩
  -- The generator of the simple extension maps to `x` itself.
  simpa using
    adjoinRootToAmbient_of_centralizer_element_root (k := k) (D := D) K hKfield x

/-- Helper for Proposition 11.8.5: non-scalarity in the centralizer makes the transported
simple-extension range strictly larger than `K`. -/
lemma adjoinRoot_range_strict_of_nontrivial_centralizer_element
    (K : Subalgebra k D) (hKfield : IsField K) :
    let C := Subalgebra.centralizer k (K : Set D)
    letI : Field K := hKfield.toField
    letI : Algebra K C :=
      (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
    ∀ x : C, x ∉ (⊥ : Subalgebra K C) →
      K < (adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range := by
  let C := Subalgebra.centralizer k (K : Set D)
  letI : Field K := hKfield.toField
  letI : Algebra K C :=
    (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
  intro x hx
  refine lt_of_le_of_ne
    (subfield_le_adjoinRoot_range_of_centralizer_element (k := k) (D := D) K hKfield x) ?_
  intro hEq
  have hxrange :
      x.1 ∈ (adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range :=
    centralizer_element_mem_adjoinRoot_range_of_centralizer_element
      (k := k) (D := D) K hKfield x
  have hxK : x.1 ∈ K := by
    simpa [hEq] using hxrange
  apply hx
  rw [Algebra.mem_bot]
  refine ⟨⟨x.1, hxK⟩, ?_⟩
  ext
  rfl

/-- Helper for Proposition 11.8.5: the centralizer of a field subalgebra is finite dimensional
over that subfield. -/
lemma finiteDimensional_centralizer_over_subfield
    (K : Subalgebra k D) (hKfield : IsField K) :
    let C := Subalgebra.centralizer k (K : Set D)
    letI : Field K := hKfield.toField
    letI : Algebra K C :=
      (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
    FiniteDimensional K C := by
  let C := Subalgebra.centralizer k (K : Set D)
  letI : Field K := hKfield.toField
  letI : FiniteDimensional k K := FiniteDimensional.of_injective K.val K.val_injective
  letI : Algebra K C :=
    (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
  letI : FiniteDimensional K D := FiniteDimensional.right K k D
  let iCD : C →ₗ[K] D where
    toFun := Subtype.val
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
  -- The centralizer is a `K`-subspace of the finite-dimensional `K`-vector space `D`.
  exact FiniteDimensional.of_injective iCD fun x y hxy ↦ Subtype.ext hxy

/-- Helper for Proposition 11.8.5: the simple-extension map onto the ambient range is a
`k`-algebra equivalence. -/
noncomputable lemma adjoinRoot_range_algEquiv_of_centralizer_element
    (K : Subalgebra k D) (hKfield : IsField K) :
    let C := Subalgebra.centralizer k (K : Set D)
    letI : Field K := hKfield.toField
    letI : Algebra K C :=
      (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
    ∀ x : C,
      AdjoinRoot (minpoly K x) ≃ₐ[k]
        (adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range := by
  let C := Subalgebra.centralizer k (K : Set D)
  letI : Field K := hKfield.toField
  letI : Algebra K C :=
    (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
  letI : FiniteDimensional K C :=
    finiteDimensional_centralizer_over_subfield (k := k) (D := D) K hKfield
  letI : Algebra.IsAlgebraic K C := Algebra.IsAlgebraic.of_finite K C
  intro x
  let hxalg : IsAlgebraic K x := Algebra.IsAlgebraic.isAlgebraic (R := K) x
  letI : Fact (Irreducible (minpoly K x)) := ⟨minpoly.irreducible hxalg.isIntegral⟩
  let φx := adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x
  -- The range of an algebra hom from a field into a division ring is canonically equivalent to the
  -- source field.
  exact (Subalgebra.ofInjectiveField φx).restrictScalars k

/-- Helper for Proposition 11.8.5: the transported simple-extension range is a field. -/
lemma adjoinRoot_range_isField_of_centralizer_element
    (K : Subalgebra k D) (hKfield : IsField K) :
    let C := Subalgebra.centralizer k (K : Set D)
    letI : Field K := hKfield.toField
    letI : Algebra K C :=
      (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
    ∀ x : C,
      IsField
        ((adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range) := by
  let C := Subalgebra.centralizer k (K : Set D)
  letI : Field K := hKfield.toField
  letI : Algebra K C :=
    (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
  intro x
  letI : FiniteDimensional K C :=
    finiteDimensional_centralizer_over_subfield (k := k) (D := D) K hKfield
  letI : Algebra.IsAlgebraic K C := Algebra.IsAlgebraic.of_finite K C
  let hxalg : IsAlgebraic K x := Algebra.IsAlgebraic.isAlgebraic (R := K) x
  letI : Fact (Irreducible (minpoly K x)) := ⟨minpoly.irreducible hxalg.isIntegral⟩
  let e :=
    adjoinRoot_range_algEquiv_of_centralizer_element (k := k) (D := D) K hKfield x
  -- Fieldness transfers across the range equivalence from the `AdjoinRoot` source.
  exact e.toMulEquiv.isField (Field.toIsField (AdjoinRoot (minpoly K x)))

/-- Helper for Proposition 11.8.5: the transported simple-extension range is separable over `k`
once the chosen centralizer element is separable over `K`. -/
lemma adjoinRoot_range_isSeparable_of_centralizer_element
    (K : Subalgebra k D) (hKfield : IsField K) (hKsep : Algebra.IsSeparable k K) :
    let C := Subalgebra.centralizer k (K : Set D)
    letI : Field K := hKfield.toField
    letI : Algebra K C :=
      (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
    ∀ x : C, IsSeparable K x →
      Algebra.IsSeparable k
        ((adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range) := by
  let C := Subalgebra.centralizer k (K : Set D)
  letI : Field K := hKfield.toField
  letI : Algebra K C :=
    (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra
  intro x hxsep
  let e :=
    adjoinRoot_range_algEquiv_of_centralizer_element (k := k) (D := D) K hKfield x
  let hxint : IsIntegral K x := IsSeparable.isIntegral hxsep
  letI : Fact (Irreducible (minpoly K x)) := ⟨minpoly.irreducible hxint⟩
  let y : AdjoinRoot (minpoly K x) := AdjoinRoot.root (minpoly K x)
  have hysep : IsSeparable K y := by
    -- The distinguished root has the same minimal polynomial as `x`.
    simpa [IsSeparable, AdjoinRoot.minpoly_root (minpoly.ne_zero hxint), minpoly.monic hxint]
      using hxsep
  have hsimple :
      Algebra.IsSeparable K K⟮y⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
      (F := K) (E := AdjoinRoot (minpoly K x))).2 hysep
  have htop : K⟮y⟯ = ⊤ := IntermediateField.adjoin_root_eq_top (p := minpoly K x)
  have hsourceK :
      Algebra.IsSeparable K (AdjoinRoot (minpoly K x)) := by
    have hsourceTop : Algebra.IsSeparable K (⊤ : IntermediateField K (AdjoinRoot (minpoly K x))) := by
      simpa [htop] using hsimple
    exact AlgEquiv.Algebra.isSeparable (IntermediateField.topEquiv :
      (⊤ : IntermediateField K (AdjoinRoot (minpoly K x))) ≃ₐ[K] AdjoinRoot (minpoly K x))
  let _ : Algebra.IsSeparable K (AdjoinRoot (minpoly K x)) := hsourceK
  let _ : Algebra.IsSeparable k (AdjoinRoot (minpoly K x)) :=
    Algebra.IsSeparable.trans k K (AdjoinRoot (minpoly K x))
  -- Separability now transfers from the `AdjoinRoot` owner to the range.
  exact AlgEquiv.Algebra.isSeparable e

/-- Helper for Proposition 11.8.5: a proper centralizer produces a strictly larger separable
`k`-subfield. -/
lemma exists_larger_separable_subfield_of_nontrivial_centralizer
    (K : Subalgebra k D) (hKfield : IsField K) (hKsep : Algebra.IsSeparable k K)
    (hCK : Subalgebra.centralizer k (K : Set D) ≠ K) :
    ∃ L : Subalgebra k D, IsField L ∧ Algebra.IsSeparable k L ∧ K < L := by
  let C := Subalgebra.centralizer k (K : Set D)
  have hKC : K ≤ C := self_le_centralizer_of_isField (k := k) (D := D) K hKfield
  let iKC := centralizerSubfieldInclusion (k := k) (D := D) K hKfield
  let C₀ : Subfield D :=
    C.toSubring.toSubfield fun x hx ↦
      inv_mem_centralizer_of_mem_centralizer (k := k) (D := D) K hx
  let iKC₀ : K →ₐ[k] C₀ where
    toFun a := ⟨a.1, hKC a.2⟩
    map_zero' := rfl
    map_one' := rfl
    map_add' _ _ := rfl
    map_mul' _ _ := rfl
    commutes' _ := rfl
  letI : Field K := hKfield.toField
  letI : Algebra K C := iKC.toRingHom.toAlgebra
  letI : Algebra K C₀ := iKC₀.toRingHom.toAlgebra
  letI : FiniteDimensional k K := FiniteDimensional.of_injective K.val K.val_injective
  letI : FiniteDimensional K D := FiniteDimensional.right K k D
  let iC₀D : C₀ →ₗ[K] D where
    toFun := Subtype.val
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
  letI : FiniteDimensional K C₀ := FiniteDimensional.of_injective iC₀D fun x y hxy ↦
    Subtype.ext hxy
  letI : Algebra.IsAlgebraic K C₀ := Algebra.IsAlgebraic.of_finite K C₀
  have hCproper₀ : (⊥ : Subalgebra K C₀) ≠ ⊤ := by
    intro hbot
    have hEq : C = K := by
      apply le_antisymm
      · intro x hx
        have hxbot : (⟨x, hx⟩ : C₀) ∈ (⊥ : Subalgebra K C₀) := by
          simpa [hbot] using (show (⟨x, hx⟩ : C₀) ∈ (⊤ : Subalgebra K C₀) from by simp)
        rw [Algebra.mem_bot] at hxbot
        rcases hxbot with ⟨a, ha⟩
        exact (congrArg Subtype.val ha) ▸ a.2
      · exact hKC
    exact hCK (by simpa [C] using hEq)
  have hCcentral₀ : Algebra.IsCentral K C₀ := by
    let A : CSA.{u, v} k := CSA.mk (AlgCat.of k D)
    have hCC : Subalgebra.centralizer k (C : Set D) = K := by
      -- The double-centralizer theorem identifies the center of the centralizer with `K`.
      simpa [A, C] using
        (Subalgebra.centralizer_centralizer_eq (k := k) (A := A) (B := K))
    refine ⟨fun x hx ↦ ?_⟩
    have hxC :
        x.1 ∈ Subalgebra.centralizer k (C : Set D) := by
      -- A central element of `C₀` commutes with every element of the ambient centralizer `C`.
      rw [Subalgebra.mem_centralizer_iff]
      rw [Subalgebra.mem_center_iff] at hx
      intro y hy
      exact congrArg Subtype.val (hx ⟨y, hy⟩)
    have hxK : x.1 ∈ K := by
      simpa [hCC] using hxC
    rw [Algebra.mem_bot]
    refine ⟨⟨x.1, hxK⟩, ?_⟩
    ext
    rfl
  letI : Algebra.IsCentral K C₀ := hCcentral₀
  -- Route correction: the Jacobson-Noether route was the wrong seam. The verified prefix now
  -- packages the source centralizer `C` as a proper central `K`-algebra before adjoining any new
  -- element.
  have htransport_strict :
      ∀ x : C, x ∉ (⊥ : Subalgebra K C) →
        K < (adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range :=
    adjoinRoot_range_strict_of_nontrivial_centralizer_element
      (k := k) (D := D) K hKfield
  obtain ⟨x₀, hx₀bot, hx₀sep⟩ :=
    JacobsonNoether.exists_separable_and_not_isCentral' (L := K) (D := C₀) hCproper₀
  let x : C := ⟨x₀.1, x₀.2⟩
  let fCC₀ : C →ₐ[K] C₀ where
    toFun z := ⟨z.1, z.2⟩
    map_zero' := rfl
    map_one' := rfl
    map_add' _ _ := rfl
    map_mul' _ _ := rfl
    commutes' _ := rfl
  have hxbot : x ∉ (⊥ : Subalgebra K C) := by
    intro hx
    apply hx₀bot
    rw [Algebra.mem_bot] at hx ⊢
    rcases hx with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    ext
    exact congrArg Subtype.val ha
  have hxsep : IsSeparable K x := by
    have hfx : fCC₀ x = x₀ := by
      ext
      rfl
    -- Transfer separability back along the identity inclusion between the two centralizer models.
    exact hfx ▸ IsSeparable.of_algHom (f := fCC₀) hx₀sep
  let L :=
    (adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range
  have hLfield : IsField L :=
    adjoinRoot_range_isField_of_centralizer_element (k := k) (D := D) K hKfield x
  have hLsep : Algebra.IsSeparable k L :=
    adjoinRoot_range_isSeparable_of_centralizer_element
      (k := k) (D := D) K hKfield hKsep x hxsep
  have hKL : K < L := htransport_strict x hxbot
  -- Adjoin the nonscalar separable centralizer element and transfer the owner-level field and
  -- separability properties along the canonical simple-extension map.
  exact ⟨L, hLfield, hLsep, hKL⟩

-- Proof sketch: among the separable `k`-subfields of `D`, choose one maximal by inclusion. If it
-- were not maximal among commutative `k`-subalgebras, enlarging it would produce an element of `D`
-- separable over `k`, contradicting maximality of the separable subfield.
/-- Proposition 11.8.5 (1): a finite central skew field over `k` contains a maximal subfield that
is separable over `k`. -/
theorem exists_separable_maximal_subfield :
    ∃ K : Subalgebra k D, Algebra.IsSeparable k K ∧ IsMaximalSubfield K := by
  classical
  rcases exists_finrank_maximal_separable_subfield (k := k) (D := D) with
    ⟨K, hKfield, hKsep, hmax⟩
  have hCeq : Subalgebra.centralizer k (K : Set D) = K := by
    by_contra hCK
    rcases exists_larger_separable_subfield_of_nontrivial_centralizer
      (k := k) (D := D) K hKfield hKsep hCK with
      ⟨L, hLfield, hLsep, hKL⟩
    have hfinKL : Module.finrank k K ≤ Module.finrank k L := by
      exact Submodule.finrank_mono hKL.le
    have hfinLK : Module.finrank k L ≤ Module.finrank k K := hmax L hLfield hLsep
    have hEq : K = L := Subalgebra.eq_of_le_of_finrank_eq hKL.le (Nat.le_antisymm hfinLK hfinKL)
    exact hKL.ne hEq
  have hKmax : K.IsMaximalCommutative :=
    (K.centralizer_eq_iff_isMaximalCommutative).1 hCeq
  -- The maximal-finrank separable field is maximal commutative once its centralizer collapses.
  exact ⟨K, hKsep, { toIsMaximalCommutative := hKmax }⟩

namespace CSA

variable (A : CSA.{u, v} k)

-- Proof sketch: choose a Brauer-equivalent finite central skew field representing `A`, apply the
-- first part to obtain a separable maximal subfield, and then use Lemma 11.8.3 to see that this
-- maximal subfield splits the division algebra. Brauer equivalence preserves the splitting-field
-- condition, so the same finite separable extension splits `A`.
/-- Proposition 11.8.5 (2), representative form: every finite central simple `k`-algebra is split
by some finite separable extension of `k`. -/
theorem exists_finite_separable_splitting_field :
    ∃ (L : Type w) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L)
      (_ : Algebra.IsSeparable k L),
      A.IsSplitBy L := by
  -- We descend to a Brauer-equivalent division representative and split it by a separable maximal
  -- subfield from part (1).
  rcases A.exists_division_algebra_representative with
    ⟨D, _, _, _, _, hAD⟩
  rcases exists_separable_maximal_subfield (k := k) (D := D) with ⟨L, hLsep, hLmax⟩
  letI : IsMaximalSubfield L := hLmax
  have hsplitD : (CSA.mk (AlgCat.of k D)).IsSplitBy L := maximal_subfield_splits L
  exact ⟨L, inferInstance, inferInstance, inferInstance, hLsep,
    (A.isSplitBy_iff_of_isBrauerEquivalent L hAD).2 hsplitD⟩

end CSA

namespace BrauerGroup

variable (A : Br(k))
variable (L : Type w) [Field L] [Algebra k L]

/-- A Brauer class is split by `L` if it admits a finite central simple representative split by
`L`. -/
def IsSplitBy : Prop :=
  ∃ B : CSA.{u, max u v} k, (Quotient.mk _ B : Br(k)) = A ∧ B.IsSplitBy L

@[simp] theorem isSplitBy_mk [FiniteDimensional k L] (A : CSA.{u, max u v} k) :
    BrauerGroup.IsSplitBy (Quotient.mk _ A : Br(k)) L ↔ A.IsSplitBy L := by
  constructor
  · rintro ⟨B, hBA, hB⟩
    have hiff : A.IsSplitBy L ↔ B.IsSplitBy L := by
      exact A.isSplitBy_iff_of_isBrauerEquivalent L <| Quotient.exact hBA.symm
    exact hiff.2 hB
  · intro hA
    exact ⟨A, rfl, hA⟩

/- Layer note: Proposition 11.8.5 (2) is `source-facing`, but its owner abstraction is
`BrauerGroup k`; the representative-level `CSA` statement is retained only as a bridge. -/
/-- Proposition 11.8.5 (2): every Brauer class over `k` admits a finite separable splitting
field. -/
theorem exists_finite_separable_splitting_field :
    ∃ (L : Type w) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L)
      (_ : Algebra.IsSeparable k L), A.IsSplitBy L := by
  refine Quotient.inductionOn A fun B ↦ ?_
  rcases B.exists_finite_separable_splitting_field with ⟨L, _, _, _, _, hL⟩
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨B, rfl, hL⟩⟩

end BrauerGroup

end
