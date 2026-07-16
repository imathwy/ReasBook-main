import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_107_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_107_6
import StacksProject_2024.stacks_project.Chap15.Definition_15_105_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_105_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/- Domain-style sampling:
- primary domain: commutative algebra of integrally closed extensions and flat epimorphisms of
  rings;
- sampled owner declarations:
  `IsIntegrallyClosedIn`,
  `HasWeakDimensionLE`,
  `Algebra.IsEpi`,
  `RingHom.surjective_iff_epi_and_finite`;
- best owner abstraction: this lemma is `source-facing`, but its epimorphism input should use the
  algebra-level owner `Algebra.IsEpi A B`; the category-theoretic condition
  `Epi (CommRingCat.ofHom (algebraMap A B))` is only a bridge, via `CommRingCat.epi_iff_epi`;
- primitive vs. derived:
  primitive data is the weak-dimension hypothesis on `A`, flatness of `B` over `A`, injectivity
  of `algebraMap A B`, and the owner predicate `Algebra.IsEpi A B`;
  derived API is the conclusion `IsIntegrallyClosedIn A B`, so no extra local wrapper around ring
  epimorphisms is warranted here.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting integral closedness of `A` inside `B`;
- `core/canonical`: `IsIntegrallyClosedIn`, `HasWeakDimensionLE`, `Module.Flat`, `Algebra.IsEpi`;
- `bridge/view`: the category-theoretic epimorphism formulation in `CommRingCat`, used only when a
  categorical pushout/pullback argument is needed.
-/

-- Proof sketch: if `x : B` is integral over `A`, let `A' := A[x] ⊆ B`. By finite generation of
-- simple integral extensions, `A'` is finite over `A`. Since `A` has weak dimension at most `1`
-- and `B` is flat over `A`, Lemma `15.105.18` gives flatness of the finite `A`-submodule `A'`.
-- The multiplication map `A' ⊗[A] A' → A'` factors through `B`, and injectivity of `A → B`
-- together with the ring-epimorphism hypothesis forces `A → A'` to be an epimorphism. Then
-- `RingHom.surjective_iff_epi_and_finite` makes `A → A'` surjective, so `x` comes from `A`.
/-- Helper for Lemma 15.105.21: the singly generated subalgebra `A[x]` is flat over `A` because
it is a submodule of the flat `A`-module `B`. -/
lemma flat_adjoin_singleton_of_hasWeakDimensionLEOne
    [HasWeakDimensionLE A 1] [Module.Flat A B] (x : B) :
    Module.Flat A (Algebra.adjoin A ({x} : Set B)) := by
  let S : Subalgebra A B := Algebra.adjoin A ({x} : Set B)
  have hvaluation :
      ∀ p : PrimeSpectrum A,
        ∃ (_ : IsDomain (Localization.AtPrime p.asIdeal)),
          ValuationRing (Localization.AtPrime p.asIdeal) :=
    ((weakDimensionLEOne_idealFlat_fgIdealFlat_submoduleFlat_localizations_valuationRing_tfae
      (A := A)).out 0 4).mp (show HasWeakDimensionLE A 1 from inferInstance)
  let _ : Module.Flat A (ModuleCat.of A B) := by
    simpa using (inferInstance : Module.Flat A B)
  have hflatSubmodule : Module.Flat A S.toSubmodule :=
    submodule_flat_of_localizations_valuationRing (A := A) hvaluation (ModuleCat.of A B)
      S.toSubmodule
  simpa [S] using hflatSubmodule

/-- Helper for Lemma 15.105.21: tensoring the inclusion `A[x] ↪ B` on both sides stays injective,
because both the source factor `A[x]` and the target factor `B` are flat over `A`. -/
lemma adjoin_tensor_square_map_injective
    [HasWeakDimensionLE A 1] [Module.Flat A B] (x : B) :
    let S : Subalgebra A B := Algebra.adjoin A ({x} : Set B)
    Function.Injective (Algebra.TensorProduct.map S.val S.val : S ⊗[A] S →ₐ[A] B ⊗[A] B) := by
  let S : Subalgebra A B := Algebra.adjoin A ({x} : Set B)
  let _ : Module.Flat A S := flat_adjoin_singleton_of_hasWeakDimensionLEOne (A := A) (B := B) x
  -- Use the standard injectivity theorem for tensor products over flat modules.
  simpa [S] using
    (TensorProduct.map_injective_of_flat_flat
      S.val.toLinearMap
      S.val.toLinearMap
      Subtype.val_injective
      Subtype.val_injective)

/-- Helper for Lemma 15.105.21: mapping the left tensor-factor inclusion of a subalgebra into the
ambient tensor square agrees with first including into the ambient algebra and then using the
ambient left tensor-factor map. -/
lemma subalgebra_tensor_square_map_comp_includeLeft (S : Subalgebra A B) :
    (Algebra.TensorProduct.map S.val S.val).comp
        (Algebra.TensorProduct.includeLeft : S →ₐ[A] S ⊗[A] S) =
      (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).comp S.val := by
  -- Both composites send `s` to the same pure tensor `s ⊗ₜ 1` in `B ⊗[A] B`.
  ext s
  simp [Algebra.TensorProduct.includeLeft_apply]

/-- Helper for Lemma 15.105.21: mapping the right tensor-factor inclusion of a subalgebra into the
ambient tensor square agrees with first including into the ambient algebra and then using the
ambient right tensor-factor map. -/
lemma subalgebra_tensor_square_map_comp_includeRight (S : Subalgebra A B) :
    (Algebra.TensorProduct.map S.val S.val).comp
        (Algebra.TensorProduct.includeRight : S →ₐ[A] S ⊗[A] S) =
      (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).comp S.val := by
  -- Both composites send `s` to the same pure tensor `1 ⊗ₜ s` in `B ⊗[A] B`.
  ext s
  simp [Algebra.TensorProduct.includeRight_apply]

/-- Helper for Lemma 15.105.21: an `A`-subalgebra of an epimorphic `A`-algebra is itself
epimorphic once its tensor-square comparison map into the ambient tensor square is injective. -/
lemma subalgebra_isEpi_of_tensor_square_map_injective (S : Subalgebra A B)
    (hTensor :
      Function.Injective (Algebra.TensorProduct.map S.val S.val :
        S ⊗[A] S →ₐ[A] B ⊗[A] B))
    [Algebra.IsEpi A B] :
    Algebra.IsEpi A S := by
  -- Route correction: descend the canonical equality `includeLeft = includeRight` from `B` to `S`
  -- through the injective tensor-square comparison map.
  have hB :
      (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) =
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) :=
    (algebra_isEpi_iff_includeLeft_eq_includeRight (R := A) (S := B)).mp inferInstance
  have hMapped :
      (Algebra.TensorProduct.map S.val S.val).comp
          (Algebra.TensorProduct.includeLeft : S →ₐ[A] S ⊗[A] S) =
        (Algebra.TensorProduct.map S.val S.val).comp
          (Algebra.TensorProduct.includeRight : S →ₐ[A] S ⊗[A] S) := by
    calc
      (Algebra.TensorProduct.map S.val S.val).comp
          (Algebra.TensorProduct.includeLeft : S →ₐ[A] S ⊗[A] S) =
          (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).comp S.val := by
            rw [subalgebra_tensor_square_map_comp_includeLeft]
      _ = (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).comp S.val := by
            rw [hB]
      _ = (Algebra.TensorProduct.map S.val S.val).comp
          (Algebra.TensorProduct.includeRight : S →ₐ[A] S ⊗[A] S) := by
            rw [subalgebra_tensor_square_map_comp_includeRight]
  have hS :
      (Algebra.TensorProduct.includeLeft : S →ₐ[A] S ⊗[A] S) =
        (Algebra.TensorProduct.includeRight : S →ₐ[A] S ⊗[A] S) := by
    -- Evaluate the mapped equality on each element of `S` and descend it through injectivity.
    ext s
    apply hTensor
    exact congrArg (fun f : S →ₐ[A] B ⊗[A] B ↦ f s) hMapped
  exact (algebra_isEpi_iff_includeLeft_eq_includeRight (R := A) (S := S)).mpr hS

/-- Helper for Lemma 15.105.21: the simple subalgebra `A[x]` is an epimorphic `A`-algebra once
the ambient map `A → B` is epimorphic. -/
lemma adjoin_singleton_isEpi_of_epi
    [HasWeakDimensionLE A 1] [Module.Flat A B] (x : B) [Algebra.IsEpi A B] :
    let S : Subalgebra A B := Algebra.adjoin A ({x} : Set B)
    Algebra.IsEpi A S := by
  let S : Subalgebra A B := Algebra.adjoin A ({x} : Set B)
  have htensor_inj :
      Function.Injective (Algebra.TensorProduct.map S.val S.val : S ⊗[A] S →ₐ[A] B ⊗[A] B) :=
    adjoin_tensor_square_map_injective (A := A) (B := B) x
  -- Descend epimorphy from `B` to `A[x]` using the injective tensor-square comparison.
  simpa [S] using
    (subalgebra_isEpi_of_tensor_square_map_injective (A := A) (B := B) S htensor_inj)

/-- Lemma 15.105.21: if `A` has weak dimension at most `1` and `A → B` is a flat, injective
epimorphism of commutative rings, then `A` is integrally closed in `B`. -/
theorem isIntegrallyClosedIn_of_hasWeakDimensionLEOne_of_flat_of_injective_of_epi
    [HasWeakDimensionLE A 1] [Module.Flat A B]
    (hinj : Function.Injective (algebraMap A B)) [Algebra.IsEpi A B] :
    IsIntegrallyClosedIn A B := by
  rw [isIntegrallyClosedIn_iff]
  refine ⟨hinj, ?_⟩
  intro x hx
  let S : Subalgebra A B := Algebra.adjoin A ({x} : Set B)
  have hfiniteS : Module.Finite A S := by
    -- A simple integral extension is finite over the base ring.
    exact
      Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_singleton x)
        (fun y hy ↦ by
          simpa [Set.mem_singleton_iff.mp hy] using hx)
  letI : Module.Finite A S := hfiniteS
  letI : Algebra.IsEpi A S := adjoin_singleton_isEpi_of_epi (A := A) (B := B) x
  have hsurj : Function.Surjective (algebraMap A S) := by
    -- Finite epimorphic algebras are already surjective on the algebra map.
    exact
      (Algebra.isEpi_iff_surjective_algebraMap_of_finite (R := A) (A := S)).mp
        (inferInstance : Algebra.IsEpi A S)
  have hx_mem : x ∈ S := by
    -- The chosen element lies in the subalgebra it generates.
    exact Algebra.subset_adjoin (by simp)
  let xS : S := ⟨x, hx_mem⟩
  obtain ⟨a, ha⟩ := hsurj xS
  -- Apply the subalgebra inclusion to the surjective preimage equation to recover `x` in `B`.
  exact ⟨a, by
    simpa [xS] using congrArg S.val ha⟩

end
