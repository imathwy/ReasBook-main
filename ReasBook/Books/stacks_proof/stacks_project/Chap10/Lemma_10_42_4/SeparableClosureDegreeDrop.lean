import Mathlib.FieldTheory.IsPerfectClosure
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import StacksProject_2024.Chap09.Lemma_9_14_5
import StacksProject_2024.Chap09.Lemma_9_26_11
import StacksProject_2024.Chap09.Lemma_9_28_2
import StacksProject_2024.Chap10.Definition_10_42_1
import StacksProject_2024.Chap10.Lemma_10_42_3
import Mathlib.Tactic.StacksAttribute


section

open Algebra

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- Helper for Lemma 10.42.4: in a finite-dimensional tower, any intermediate step of relative
degree `p` strictly lowers the ambient degree. This isolates the later source induction drop from
the concrete base-change construction that produces the degree-`p` step. -/
lemma finrank_lt_of_relfinrank_eq_prime
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]
    {A B : IntermediateField F E} [FiniteDimensional A E]
    {p : ℕ} [Fact p.Prime] (hAB : A ≤ B) (hdeg : A.relfinrank B = p) :
    Module.finrank B E < Module.finrank A E := by
  letI : Algebra A B := (IntermediateField.inclusion hAB).toAlgebra
  letI : IsScalarTower A B E := IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  letI : FiniteDimensional B E := FiniteDimensional.right A B E
  -- Rewrite the ambient degree through the relative tower law for `A ≤ B ≤ E`.
  have hmul : A.relfinrank B * Module.finrank B E = Module.finrank A E :=
    IntermediateField.relfinrank_mul_finrank_top (E := E) hAB
  rw [hdeg] at hmul
  have hp : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hpos : 0 < Module.finrank B E := Module.finrank_pos
  -- Since the relative degree is strictly larger than `1`, the tail degree must decrease.
  calc
    Module.finrank B E < p * Module.finrank B E := by
      simpa [Nat.mul_comm] using (lt_mul_of_one_lt_right hpos hp)
    _ = Module.finrank A E := by
      simpa [Nat.mul_comm] using hmul

/-- Helper for Lemma 10.42.4: mapping a degree-`p` simple adjunction across a field embedding
preserves the relative degree of the resulting intermediate extension. -/
lemma relfinrank_map_restrictScalars_adjoin_simple_eq
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]
    {L : Type*} [Field L] [Algebra F L]
    (A : IntermediateField F E) (σ : E →ₐ[F] L) {β : E} {p : ℕ}
    (hdeg : Module.finrank A (IntermediateField.adjoin A ({β} : Set E)) = p) :
    (A.map σ).relfinrank
        (((IntermediateField.adjoin A ({β} : Set E)).restrictScalars F).map σ) = p := by
  let b : E := β
  let B : IntermediateField F E := IntermediateField.adjoin F ((A : Set E) ∪ ({b} : Set E))
  have hA : A ≤ B := by
    -- The source base field is contained in the larger field obtained by adjoining `β`.
    intro x hx
    exact IntermediateField.subset_adjoin (F := F) (S := ((A : Set E) ∪ ({b} : Set E))) (Or.inl hx)
  have hB :
      (IntermediateField.adjoin A ({β} : Set E)).restrictScalars F = B := by
    -- Restricting scalars rewrites the simple adjunction as adjoining `β` over `F`.
    simpa [B, b] using
      (IntermediateField.restrictScalars_adjoin (F := F) (K := A) (S := ({β} : Set E)))
  have hrel : A.relfinrank B = p := by
    -- Compute the relative finrank before mapping and simplify the extended field back to the
    -- original degree-`p` simple adjunction over `A`.
    rw [IntermediateField.relfinrank_eq_finrank_of_le hA]
    rw [IntermediateField.extendScalars_adjoin hA]
    rw [show ((A : Set E) ∪ ({b} : Set E)) = insert b (A : Set E) by
      ext x
      simp]
    have hinsert :
        IntermediateField.adjoin A (insert b (A : Set E)) =
          IntermediateField.adjoin A ({b} : Set E) := by
      refine le_antisymm ?_ ?_
      · rw [IntermediateField.adjoin_le_iff]
        intro y hy
        rcases Set.mem_insert_iff.mp hy with hyb | hyA
        · exact IntermediateField.mem_adjoin_of_mem (F := A) (S := ({b} : Set E)) (by
            simpa [hyb])
        · exact
            IntermediateField.adjoin_contains_field_as_subfield
              (F := A.toSubfield) (S := ({b} : Set E)) hyA
      · exact
          IntermediateField.adjoin.mono (F := A) ({b} : Set E) (insert b (A : Set E))
            (by
              intro y hy
              left
              simpa using hy)
    rw [hinsert]
    simpa [b] using hdeg
  -- The field embedding preserves relative finrank for mapped intermediate fields.
  calc
    (A.map σ).relfinrank (((IntermediateField.adjoin A ({β} : Set E)).restrictScalars F).map σ)
        = (A.map σ).relfinrank (B.map σ) := by rw [hB]
    _ = A.relfinrank B := by
          simpa using IntermediateField.relfinrank_map_map (A := A) (B := B) σ
    _ = p := hrel

/-- Helper for Lemma 10.42.4: after an algebraic base change of the ground field, adjoining the
old separable closure produces the new separable closure. This is the owner-level replacement for
the source compositum identity. -/
lemma adjoin_separableClosure_eq_separableClosure_of_isAlgebraic
    {F : Type*} {B : Type*} {E : Type*}
    [Field F] [Field B] [Field E]
    [Algebra F B] [Algebra F E] [Algebra B E] [IsScalarTower F B E]
    [Algebra.IsAlgebraic F B] :
    IntermediateField.adjoin B (separableClosure F E : Set E) = separableClosure B E := by
  -- This is exactly the canonical mathlib base-change identity for separable closures.
  simpa using separableClosure.adjoin_eq_of_isAlgebraic (F := F) (E := B) (K := E)

/-- Helper for Lemma 10.42.4: after an algebraic base change of the ground field, the image of an
element already lying in the old separable closure lands in the new separable closure. -/
lemma map_mem_separableClosure_of_isAlgebraic_base
    {F : Type*} {B : Type*} {E : Type*} {L : Type*}
    [Field F] [Field B] [Field E] [Field L]
    [Algebra F E] [Algebra F B] [Algebra F L] [Algebra B L] [IsScalarTower F B L]
    [Algebra.IsAlgebraic F B]
    (σ : E →ₐ[F] L) {x : E} (hx : x ∈ separableClosure F E) :
    σ x ∈ separableClosure B L := by
  have hx_sepF : σ x ∈ separableClosure F L :=
    separableClosure.map_le_of_algHom σ (show σ x ∈ (separableClosure F E).map σ from ⟨x, hx, rfl⟩)
  -- The old separable closure is contained in the new one after the algebraic base change.
  exact (separableClosure.le_restrictScalars (F := F) (E := B) (K := L)) hx_sepF

/-- Helper for Lemma 10.42.4: if `α` lies in an intermediate field and is a root of a separable
polynomial in the Frobenius image, then any chosen `p`th root of `α` already lies in that
intermediate field. -/
lemma mem_intermediateField_of_pow_eq_of_aeval_zero_of_separable_of_mem_map_frobenius_range
    {F : Type*} {A : Type*}
    [Field F] [Field A] [Algebra F A]
    (L : IntermediateField F A)
    {p : ℕ} [Fact p.Prime] [CharP F p]
    {α β : A} {P : Polynomial F}
    (hβ : β ^ p = α)
    (hαL : α ∈ L)
    (hPsep : P.Separable)
    (hPα : Polynomial.aeval α P = 0)
    (hmap : P ∈ Set.range (Polynomial.map (frobenius F p))) :
    β ∈ L := by
  letI : CharP A p := charP_of_injective_algebraMap (algebraMap F A).injective p
  let αL : L := ⟨α, hαL⟩
  have hPαL : Polynomial.aeval αL P = 0 := by
    apply (algebraMap L A).injective
    -- Evaluating in the intermediate field and then in the ambient field recovers the same root.
    have h_eval :
        (algebraMap L A) ((Polynomial.aeval αL) P) = Polynomial.aeval α P := by
      simpa [αL] using
        (Polynomial.aeval_algHom_apply (L.val.restrictScalars F) αL P).symm
    exact h_eval.trans hPα
  obtain ⟨γ, hγ⟩ :=
    exists_pth_root_of_aeval_zero_of_separable_of_mem_map_frobenius_range
      (K := F) (L := L) hPsep hPαL hmap
  have hγA : (γ : A) ^ p = α := by
    -- The extracted root in `L` is also a `p`th root of `α` in the ambient field.
    simpa [αL] using congrArg (fun z : L ↦ (z : A)) hγ
  have hβ_eq : β = γ := by
    -- Frobenius is injective on fields of characteristic `p`, so the two `p`th roots coincide.
    exact (frobenius A p).injective (by simpa [frobenius_def, hβ, hγA])
  simpa [hβ_eq] using γ.2

/-- Helper for Lemma 10.42.4: after the source algebraic base change, the image of `β ^ p`
already lies in the new separable closure. -/
lemma mapped_beta_pow_mem_new_separableClosure
    {F : Type*} {B : Type*} {E : Type*} {L : Type*}
    [Field F] [Field B] [Field E] [Field L]
    [Algebra F E] [Algebra F B] [Algebra F L] [Algebra B L] [IsScalarTower F B L]
    [Algebra.IsAlgebraic F B]
    {p : ℕ} (σ : E →ₐ[F] L) {β : E}
    (hβ_pow_mem : β ^ p ∈ separableClosure F E) :
    σ (β ^ p) ∈ separableClosure B L := by
  -- This is exactly the old-separable-closure transport applied to the source element `β ^ p`.
  exact
    map_mem_separableClosure_of_isAlgebraic_base
      (F := F) (B := B) (E := E) (L := L) σ hβ_pow_mem

/-- Helper for Lemma 10.42.4: once the image of the new degree-`p` generator lands in the
separable closure after the purely inseparable base change, the whole mapped simple step already
lies in that new separable closure. -/
lemma mapped_simple_step_le_new_separableClosure
    {F : Type*} {B : Type*} {E : Type*} {L : Type*}
    [Field F] [Field B] [Field E] [Field L]
    [Algebra F E] [Algebra F B] [Algebra F L] [Algebra B L] [IsScalarTower F B L]
    [Algebra.IsAlgebraic F B]
    (σ : E →ₐ[F] L) {β : E}
    (hβ : σ β ∈ separableClosure B L) :
    (((IntermediateField.adjoin (separableClosure F E) ({β} : Set E)).restrictScalars F).map σ) ≤
      (separableClosure B L).restrictScalars F := by
  let A : IntermediateField F E := separableClosure F E
  let M : IntermediateField F E := IntermediateField.adjoin F ((A : Set E) ∪ ({β} : Set E))
  have hM :
      ((IntermediateField.adjoin A ({β} : Set E)).restrictScalars F) = M := by
    -- Normalize the simple adjunction back to one `F`-adjoin so the mapped generators are
    -- exactly the old separable closure together with `β`.
    simpa [M] using
      (IntermediateField.restrictScalars_adjoin (F := F) (K := A) (S := ({β} : Set E)))
  have hAmap :
      A.map σ ≤ (separableClosure B L).restrictScalars F := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx_sepF : σ x ∈ separableClosure F L :=
      separableClosure.map_le_of_algHom σ (show σ x ∈ A.map σ from ⟨x, hx, rfl⟩)
    have hx_adjoin :
        σ x ∈ IntermediateField.adjoin B (separableClosure F L : Set L) := by
      exact IntermediateField.subset_adjoin (F := B) (S := (separableClosure F L : Set L)) hx_sepF
    -- Algebraic base change identifies adjoining the old separable closure with the new one.
    rw [adjoin_separableClosure_eq_separableClosure_of_isAlgebraic (F := F) (B := B) (E := L)] at hx_adjoin
    exact hx_adjoin
  rw [hM]
  unfold M
  rw [IntermediateField.adjoin_map, Set.image_union, Set.image_singleton, IntermediateField.adjoin_union]
  -- The mapped stage is generated by the mapped old separable closure and the one new element.
  refine sup_le ?_ ?_
  · rw [IntermediateField.adjoin_le_iff]
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hAmap (show σ x ∈ A.map σ from ⟨x, hx, rfl⟩)
  · rw [IntermediateField.adjoin_le_iff]
    intro y hy
    have hy' : y = σ β := by simpa using hy
    simpa [hy'] using hβ

/-- Helper for Lemma 10.42.4: an `F`-algebra equivalence transports the finite-dimensional tail
over the relative separable closure to the target field. -/
lemma finiteDimensional_over_separableClosure_of_algEquiv
    {F : Type*} {E : Type*} {L : Type*}
    [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra F L]
    [FiniteDimensional F E]
    (e : E ≃ₐ[F] L) :
    FiniteDimensional (separableClosure F L) L := by
  -- The algebra equivalence transports the finite-dimensional ambient extension to `L / F`.
  letI : FiniteDimensional F L := e.toLinearEquiv.finiteDimensional
  -- The relative separable closure is an intermediate field of that finite extension.
  infer_instance

/-- Helper for Lemma 10.42.4: once the mapped degree-`p` simple step is absorbed into the new
separable closure, the inseparable-degree measure strictly decreases. -/
lemma finInsepDegree_drop_after_absorbing_degree_p_step
    {F : Type*} {B : Type*} {E : Type*} {L : Type*}
    [Field F] [Field B] [Field E] [Field L]
    [Algebra F E] [Algebra F B] [Algebra F L] [Algebra B L] [IsScalarTower F B L]
    [Algebra.IsAlgebraic F B]
    [FiniteDimensional F E]
    [FiniteDimensional (separableClosure F E) E]
    {β : E} {p : ℕ} [Fact p.Prime]
    (e : E ≃ₐ[F] L)
    (hdeg :
      Module.finrank (separableClosure F E)
        (IntermediateField.adjoin (separableClosure F E) ({β} : Set E)) = p)
    (hcontain :
      (((IntermediateField.adjoin (separableClosure F E) ({β} : Set E)).restrictScalars F).map
          e.toAlgHom) ≤ (separableClosure B L).restrictScalars F) :
    Field.finInsepDegree B L < Field.finInsepDegree F E := by
  let A : IntermediateField F E := separableClosure F E
  let S : IntermediateField F L :=
    (((IntermediateField.adjoin A ({β} : Set E)).restrictScalars F).map e.toAlgHom)
  letI : FiniteDimensional F L := e.toLinearEquiv.finiteDimensional
  letI : FiniteDimensional (separableClosure F L) L :=
    finiteDimensional_over_separableClosure_of_algEquiv (F := F) (E := E) (L := L) e
  letI : FiniteDimensional (A.map e.toAlgHom) L := by infer_instance
  letI : FiniteDimensional S L := by infer_instance
  have hAmap : A.map e.toAlgHom = separableClosure F L := by
    -- The field-range equivalence carries the old separable closure to the new one.
    simpa [A] using (separableClosure.map_eq_of_algEquiv (F := F) e)
  have hAleS : A.map e.toAlgHom ≤ S := by
    -- The mapped source separable closure sits inside the mapped simple adjunction.
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x,
      IntermediateField.adjoin_contains_field_as_subfield
        (F := A.toSubfield) (S := ({β} : Set E)) hx,
      rfl⟩
  have hmap_deg :
      (A.map e.toAlgHom).relfinrank S = p := by
    -- Mapping the degree-`p` source step preserves its relative degree.
    simpa [A, S] using
      relfinrank_map_restrictScalars_adjoin_simple_eq
        (F := F) (E := E) (L := L) A e.toAlgHom (β := β) (p := p) hdeg
  have hstrict_step :
      Module.finrank S L < Module.finrank (A.map e.toAlgHom) L := by
    -- A relative degree `p > 1` forces the remaining tail degree to shrink strictly.
    exact finrank_lt_of_relfinrank_eq_prime (A := A.map e.toAlgHom) (B := S) hAleS hmap_deg
  have hmono :
      Module.finrank ((separableClosure B L).restrictScalars F) L ≤ Module.finrank S L := by
    -- Enlarging the intermediate field can only decrease the remaining top degree.
    exact IntermediateField.finrank_le_of_le_left hcontain
  have hstrict_target :
      Module.finrank ((separableClosure B L).restrictScalars F) L < Field.finInsepDegree F E := by
    -- Compare first with the mapped degree-`p` step and then rewrite via the field equivalence.
    calc
      Module.finrank ((separableClosure B L).restrictScalars F) L ≤ Module.finrank S L := hmono
      _ < Module.finrank (A.map e.toAlgHom) L := hstrict_step
      _ = Module.finrank (separableClosure F L) L := by rw [hAmap]
      _ = Field.finInsepDegree F L := rfl
      _ = Field.finInsepDegree F E := by
            simpa using (Field.finInsepDegree_eq_of_equiv (F := F) (E := E) (K := L) e).symm
  -- Finally rewrite the left-hand finrank as the inseparable-degree measure over `B`.
  simpa using hstrict_target

/-- Helper for Lemma 10.42.4: it is enough to show that the transported degree-`p` generator
itself lands in the new separable closure; the mapped simple adjunction and strict
inseparable-degree drop then follow from the owner lemmas above. -/
lemma finInsepDegree_drop_after_mapped_generator_mem_separableClosure
    {F : Type*} {B : Type*} {E : Type*} {L : Type*}
    [Field F] [Field B] [Field E] [Field L]
    [Algebra F E] [Algebra F B] [Algebra F L] [Algebra B L] [IsScalarTower F B L]
    [Algebra.IsAlgebraic F B]
    [FiniteDimensional F E]
    [FiniteDimensional (separableClosure F E) E]
    {β : E} {p : ℕ} [Fact p.Prime]
    (e : E ≃ₐ[F] L)
    (hdeg :
      Module.finrank (separableClosure F E)
        (IntermediateField.adjoin (separableClosure F E) ({β} : Set E)) = p)
    (hβ : e β ∈ separableClosure B L) :
    Field.finInsepDegree B L < Field.finInsepDegree F E := by
  -- First promote membership of the transported generator to containment of the whole mapped
  -- simple step in the new separable closure.
  have hcontain :
      (((IntermediateField.adjoin (separableClosure F E) ({β} : Set E)).restrictScalars F).map
          e.toAlgHom) ≤ (separableClosure B L).restrictScalars F :=
    mapped_simple_step_le_new_separableClosure (F := F) (B := B) (E := E) (L := L)
      e.toAlgHom hβ
  -- The previously isolated degree-drop lemma now finishes the final numerical comparison.
  exact
    finInsepDegree_drop_after_absorbing_degree_p_step
      (F := F) (B := B) (E := E) (L := L) e hdeg hcontain

/-- Helper for Chap10 Lemma 10 42 4: if `L` is generated over `E` by elements already in an
intermediate field `T`, then `L` is generated over `T` by the image of `E`. -/
lemma adjoin_range_eq_top_of_adjoin_eq_top_of_subset
    {B : Type*} {E : Type*} {L : Type*} [Field B] [Field E] [Field L]
    [Algebra B L] [Algebra E L]
    (T : IntermediateField B L) {S : Set L}
    (hS : S ⊆ T)
    (hL : IntermediateField.adjoin E S = ⊤) :
    IntermediateField.adjoin T (Set.range (algebraMap E L)) = ⊤ := by
  let U : IntermediateField T L := IntermediateField.adjoin T (Set.range (algebraMap E L))
  refine eq_top_iff.2 ?_
  intro z _hz
  have hz : z ∈ IntermediateField.adjoin E S := by
    rw [hL]
    trivial
  -- The `E`-adjoin is contained in `U`: `U` contains all `E`-scalars by construction and
  -- contains the chosen generators because they already lie in `T`.
  refine IntermediateField.adjoin_induction (F := E) (E := L) (s := S)
    (p := fun x _ => x ∈ U) ?mem ?alg ?add ?inv ?mul hz
  · intro x hx
    exact U.algebraMap_mem ⟨x, hS hx⟩
  · intro a
    exact IntermediateField.subset_adjoin (F := T) (S := Set.range (algebraMap E L)) ⟨a, rfl⟩
  · intro x y _ _ hx hy
    exact U.add_mem hx hy
  · intro x _ hx
    exact U.inv_mem hx
  · intro x y _ _ hx hy
    exact U.mul_mem hx hy

/-- Helper for Lemma 10.42.4: an `F`-algebra embedding of a finite-dimensional field extension has
finite-dimensional field range. This isolates the finite part of the source compositum square from
the later purely inseparable argument. -/
lemma finiteDimensional_fieldRange_of_finiteDimensional
    {F : Type*} {E : Type*} {L : Type*}
    [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra F L]
    [FiniteDimensional F E]
    (σ : E →ₐ[F] L) :
    FiniteDimensional F σ.fieldRange := by
  -- Transport the finite-dimensional structure across the canonical equivalence with the field
  -- range.
  let e : E ≃ₐ[F] σ.fieldRange := AlgEquiv.ofInjectiveField σ
  exact e.toLinearEquiv.finiteDimensional

/-- Helper for Lemma 10.42.4: after transporting the minimal polynomial through one coefficient
base change, the mapped root still annihilates the transported polynomial. This is the `aeval`
adapter needed after the source Frobenius-style coefficient descent. -/
lemma transported_minpoly_aeval_zero_after_base_change
    {F : Type*} {E : Type*} {B : Type*} {L : Type*}
    [Field F] [Field E] [Field B] [Field L]
    [Algebra F E] [Algebra F L] [Algebra B L]
    (σ : E →ₐ[F] L) (φ : F →+* B) {α : E}
    (hφ : (algebraMap B L).comp φ = algebraMap F L) :
    Polynomial.aeval (σ α) ((minpoly F α).map φ) = 0 := by
  -- First rewrite evaluation of the mapped polynomial back to evaluation of the original one.
  have hmap :
      Polynomial.aeval (σ α) ((minpoly F α).map φ) =
        Polynomial.aeval (σ α) (minpoly F α) := by
    symm
    exact Polynomial.aeval_eq_aeval_map (S := L) (T := B) hφ (minpoly F α) (σ α)
  rw [hmap]
  -- Then use the standard `minpoly` root relation transported along the embedding `σ`.
  simpa using (minpoly.aeval_algHom (A := F) (B := E) (B' := L) σ α)

/-- Helper for Lemma 10.42.4: separability of a minimal polynomial over the old base is preserved
after any coefficient field map, provided the element lies in the old separable closure. -/
lemma minpoly_map_separable_of_mem_separableClosure
    {F : Type*} {B : Type*} {E : Type*}
    [Field F] [Field B] [Field E] [Algebra F E]
    (φ : F →+* B) {α : E} (hα : α ∈ separableClosure F E) :
    ((minpoly F α).map φ).Separable := by
  -- Membership in `separableClosure` is precisely separability of the old minimal polynomial.
  exact
    Polynomial.Separable.map (p := minpoly F α) (f := φ)
      (mem_separableClosure_iff.1 hα)

/-- Helper for Lemma 10.42.4: if the transported minimal polynomial of `β ^ p` is separable and
lies in the Frobenius image over the new base, then membership of the transported `β ^ p` in the
new separable closure forces membership of the transported `β` itself. -/
lemma mapped_beta_mem_separableClosure_of_minpoly_frobenius_range
    {F : Type*} {B : Type*} {E : Type*} {L : Type*}
    [Field F] [Field B] [Field E] [Field L]
    [Algebra F E] [Algebra F L] [Algebra B L]
    {p : ℕ} [Fact p.Prime] [CharP B p]
    (σ : E →ₐ[F] L) (φ : F →+* B) {β : E}
    (hφ : (algebraMap B L).comp φ = algebraMap F L)
    (hβ_pow_mem : σ (β ^ p) ∈ separableClosure B L)
    (hsep : ((minpoly F (β ^ p)).map φ).Separable)
    (hmap :
      ((minpoly F (β ^ p)).map φ) ∈
        Set.range (Polynomial.map (frobenius B p))) :
    σ β ∈ separableClosure B L := by
  -- Transport the root equation for the minimal polynomial across the coefficient base change.
  have hroot :
      Polynomial.aeval (σ (β ^ p)) ((minpoly F (β ^ p)).map φ) = 0 :=
    transported_minpoly_aeval_zero_after_base_change (F := F) (E := E) (B := B) (L := L)
      σ φ hφ
  -- Lemma 9.28.2, in its intermediate-field form, pulls the `p`th root into the new separable
  -- closure once the coefficient polynomial is in the Frobenius image.
  exact
    mem_intermediateField_of_pow_eq_of_aeval_zero_of_separable_of_mem_map_frobenius_range
      (F := B) (A := L) (L := separableClosure B L)
      (α := σ (β ^ p)) (β := σ β)
      (P := (minpoly F (β ^ p)).map φ)
      (by simpa using (map_pow σ β p).symm) hβ_pow_mem hsep hroot hmap

/-- Helper for Lemma 10.42.4: the source successor-step membership input can stay in the old
separable closure. After an algebraic base change, Frobenius-range membership of the transported
minimal polynomial forces the transported degree-`p` generator into the new separable closure. -/
lemma mapped_beta_mem_separableClosure_of_old_pow_mem_and_minpoly_frobenius_range
    {F : Type*} {B : Type*} {E : Type*} {L : Type*}
    [Field F] [Field B] [Field E] [Field L]
    [Algebra F E] [Algebra F B] [Algebra F L] [Algebra B L] [IsScalarTower F B L]
    [Algebra.IsAlgebraic F B]
    {p : ℕ} [Fact p.Prime] [CharP B p]
    (σ : E →ₐ[F] L) (φ : F →+* B) {β : E}
    (hφ : (algebraMap B L).comp φ = algebraMap F L)
    (hβ_pow_mem : β ^ p ∈ separableClosure F E)
    (hmap :
      ((minpoly F (β ^ p)).map φ) ∈
        Set.range (Polynomial.map (frobenius B p))) :
    σ β ∈ separableClosure B L := by
  -- First transport `β ^ p` from the old separable closure to the new one after algebraic
  -- base change.
  have hβ_pow_mem_new : σ (β ^ p) ∈ separableClosure B L :=
    mapped_beta_pow_mem_new_separableClosure (F := F) (B := B) (E := E) (L := L)
      σ hβ_pow_mem
  have hsep : ((minpoly F (β ^ p)).map φ).Separable :=
    minpoly_map_separable_of_mem_separableClosure (F := F) (B := B) (E := E)
      φ hβ_pow_mem
  -- The previous lemma now applies the Frobenius-root criterion inside the new separable closure.
  exact
    mapped_beta_mem_separableClosure_of_minpoly_frobenius_range
      (F := F) (B := B) (E := E) (L := L) σ φ hφ hβ_pow_mem_new hsep hmap

/-- Helper for Chap10 Lemma 10 42 4: if `L` is generated over `B` by the image of `E`, and an
intermediate field `T` contains the image of an intermediate field `M`, then the `T`-dimension of
`L` is bounded by the `M`-dimension of `E`. -/
lemma finrank_le_of_generated_top_and_mapped_subfield_le
    {F : Type*} {B : Type*} {E : Type*} {L : Type*}
    [Field F] [Field B] [Field E] [Field L]
    [Algebra F E] [Algebra F B] [Algebra F L] [Algebra B L] [IsScalarTower F B L]
    (σ : E →ₐ[F] L)
    (M : IntermediateField F E) (T : IntermediateField B L)
    [FiniteDimensional M E]
    (hgen : IntermediateField.adjoin B (Set.range σ) = ⊤)
    (hmap : M.map σ ≤ T.restrictScalars F) :
    Module.finrank T L ≤ Module.finrank M E := by
  classical
  let τ : M →+* T := ((σ.toRingHom.comp M.val.toRingHom).codRestrict T (by
    intro m
    exact hmap ⟨m, m.2, rfl⟩))
  letI : Algebra M T := τ.toAlgebra
  letI : Algebra M L := (T.val.toRingHom.comp τ).toAlgebra
  letI : IsScalarTower M T L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let σM : E →ₐ[M] L :=
    { toRingHom := σ.toRingHom
      commutes' := by
        intro m
        rfl }
  let e : E ≃ₐ[M] σM.fieldRange := AlgEquiv.ofInjectiveField σM
  let b : Module.Basis (Fin (Module.finrank M E)) M E := Module.finBasis M E
  let bR : Module.Basis (Fin (Module.finrank M E)) M σM.fieldRange := b.map e.toLinearEquiv
  have hspan_fieldRange :
      (Algebra.adjoin T (σM.fieldRange : Set L)).toSubmodule =
        Submodule.span T (Set.range fun i : Fin (Module.finrank M E) =>
          (bR i : L)) := by
    -- The image of an `M`-basis of `E` is a basis for the embedded field range, and adjoining
    -- that field range over `T` has exactly the corresponding `T`-span as underlying module.
    simpa using
      (Subalgebra.adjoin_eq_span_basis (F := M) T (K := L)
        σM.fieldRange.toSubalgebra bR)
  have htop_ifield : IntermediateField.adjoin T (σM.fieldRange : Set L) = ⊤ := by
    apply top_unique
    intro z hz
    have hzB : z ∈ IntermediateField.adjoin B (Set.range σ) := by
      rw [hgen]
      trivial
    -- Since `T` contains `B` and the field range contains the image of `E`, the old generated-top
    -- statement promotes to a generated-top statement over `T`.
    refine IntermediateField.adjoin_induction (F := B) (E := L) (s := Set.range σ)
      (p := fun z _ ↦ z ∈ IntermediateField.adjoin T (σM.fieldRange : Set L))
      ?mem ?alg ?add ?inv ?mul hzB
    · intro z hz
      rcases hz with ⟨e0, rfl⟩
      exact IntermediateField.subset_adjoin (F := T) (S := (σM.fieldRange : Set L)) ⟨e0, rfl⟩
    · intro b
      exact (IntermediateField.adjoin T (σM.fieldRange : Set L)).algebraMap_mem
        (algebraMap B T b)
    · intro x y _ _ hx hy
      exact (IntermediateField.adjoin T (σM.fieldRange : Set L)).add_mem hx hy
    · intro x _ hx
      exact (IntermediateField.adjoin T (σM.fieldRange : Set L)).inv_mem hx
    · intro x y _ _ hx hy
      exact (IntermediateField.adjoin T (σM.fieldRange : Set L)).mul_mem hx hy
  have htop_adjoin : Algebra.adjoin T (σM.fieldRange : Set L) = ⊤ := by
    apply Algebra.adjoin_eq_top_of_intermediateField
    · intro z hz
      rcases hz with ⟨e0, rfl⟩
      have he0 : IsAlgebraic M e0 := Algebra.IsAlgebraic.isAlgebraic e0
      exact IsAlgebraic.tower_top T (IsAlgebraic.algHom σM he0)
    · exact htop_ifield
  have hspan_top :
      Submodule.span T (Set.range fun i : Fin (Module.finrank M E) =>
          (bR i : L)) = ⊤ := by
    rw [← hspan_fieldRange, htop_adjoin]
    rfl
  -- A spanning family with `finrank M E` elements bounds the target finrank.
  simpa only [Fintype.card_fin] using finrank_le_of_span_eq_top hspan_top

/-- Helper for Chap10 Lemma 10 42 4: if the generated top extension absorbs the mapped
degree-`p` generator into the new separable closure, then the inseparable-degree measure strictly
drops. -/
lemma finInsepDegree_drop_of_generated_top_absorbs_mapped_generator
    {F : Type*} {B : Type*} {E : Type*} {L : Type*}
    [Field F] [Field B] [Field E] [Field L]
    [Algebra F E] [Algebra F B] [Algebra F L] [Algebra E L] [Algebra B L]
    [IsScalarTower F E L] [IsScalarTower F B L]
    [Algebra.IsAlgebraic F B]
    [FiniteDimensional (separableClosure F E) E]
    {β : E} {p : ℕ} [Fact p.Prime]
    (hgen : IntermediateField.adjoin B (Set.range (algebraMap E L)) = ⊤)
    (hβ : algebraMap E L β ∈ separableClosure B L)
    (hdeg :
      Module.finrank (separableClosure F E)
        (IntermediateField.adjoin (separableClosure F E) ({β} : Set E)) = p) :
    Field.finInsepDegree B L < Field.finInsepDegree F E := by
  let A : IntermediateField F E := separableClosure F E
  let M : IntermediateField F E :=
    (IntermediateField.adjoin A ({β} : Set E)).restrictScalars F
  have hA_le_M : A ≤ M := by
    intro z hz
    exact IntermediateField.adjoin_contains_field_as_subfield
      (F := A.toSubfield) (S := ({β} : Set E)) hz
  letI : Algebra A M := (IntermediateField.inclusion hA_le_M).toAlgebra
  letI : IsScalarTower A M E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : FiniteDimensional M E := FiniteDimensional.right A M E
  have hmap : M.map (IsScalarTower.toAlgHom F E L) ≤
      (separableClosure B L).restrictScalars F := by
    -- The mapped simple adjunction is contained in the new separable closure once the generator
    -- itself has landed there.
    simpa [A, M] using
      mapped_simple_step_le_new_separableClosure
        (F := F) (B := B) (E := E) (L := L)
        (IsScalarTower.toAlgHom F E L) hβ
  have hle : Module.finrank (separableClosure B L) L ≤ Module.finrank M E :=
    finrank_le_of_generated_top_and_mapped_subfield_le
      (F := F) (B := B) (E := E) (L := L)
      (IsScalarTower.toAlgHom F E L) M (separableClosure B L) hgen hmap
  have hrel_map :=
    relfinrank_map_restrictScalars_adjoin_simple_eq
      (F := F) (E := E) (L := E) A (AlgHom.id F E) (β := β) (p := p) hdeg
  rw [IntermediateField.map_id, IntermediateField.map_id] at hrel_map
  have hrel : A.relfinrank M = p := by
    simpa [M] using hrel_map
  have hstrict : Module.finrank M E < Module.finrank A E :=
    finrank_lt_of_relfinrank_eq_prime (A := A) (B := M) hA_le_M hrel
  -- Compare the new inseparable degree with the source tail after the degree-`p` step.
  calc
    Field.finInsepDegree B L = Module.finrank (separableClosure B L) L := rfl
    _ ≤ Module.finrank M E := hle
    _ < Module.finrank A E := hstrict
    _ = Field.finInsepDegree F E := rfl


end
