import Mathlib
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver
import LinearRepresentations_Serre_1977.Serre.Chap02.Theorem_2_2_3_5
import LinearRepresentations_Serre_1977.Serre.Chap18.Remark_18_18_6_1
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_6_3.A5Generators
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_6_3.RankOneSL2F4
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_6_3.Shared
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_6_3.SourceReductionOwners

open scoped TensorProduct MatrixGroups

noncomputable section

universe u v

namespace Representation

open AlternatingGroupFive

local notation "A5" => alternatingGroup (Fin 5)
local notation "𝔽₄" => FiniteField.Extension (ZMod 2) 2 2

/-- Helper for Exercise 18-18.6-3: source-faithful construction of one irreducible degree-`2`
`𝔽₄[A₅]` slot. This is the first owner-level input missing from the current formal route. -/
theorem a5_degree_two_source_slot_owner_over_f4 :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module 𝔽₄ W) (_ : FiniteDimensional 𝔽₄ W)
      (ρ : Representation 𝔽₄ A5 W),
      ρ.IsIrreducible ∧ Module.finrank 𝔽₄ W = 2 := by
  -- The source-reduction support package already exposes the descended simple degree-`2`
  -- constituent.  We only unbundle it from `FDRep` into the existential shape used downstream.
  rcases a5_source_degree_three_phi_owner_over_f4_support with
    ⟨E2, hE2simple, hE2dim⟩
  letI : CategoryTheory.Simple E2 := hE2simple
  let eLift : E2 ≃ₗ[𝔽₄] ULift.{u} E2 := ULift.moduleEquiv.symm
  let ρLift : Representation 𝔽₄ A5 (ULift.{u} E2) :=
    { toFun := fun g ↦ eLift.conj (E2.ρ g)
      map_one' := by
        -- Conjugation transports the identity action to the lifted carrier.
        ext x
        simp [eLift, LinearEquiv.conj_apply_apply]
      map_mul' := by
        -- Conjugation also transports the representation multiplication law.
        intro g h
        ext x
        simp [eLift, LinearEquiv.conj_apply_apply, map_mul] }
  have hEquiv : Representation.Equiv E2.ρ ρLift := by
    -- The lifting equivalence intertwines the original and transported actions by definition.
    refine Representation.Equiv.mk eLift ?_
    intro g
    ext x
    simp [ρLift, eLift, LinearEquiv.conj_apply_apply]
  have hLiftIrreducible : ρLift.IsIrreducible := by
    -- Simplicity of the bundled source constituent gives irreducibility before transport, and
    -- representation equivalence carries it to the lifted universe.
    letI : Representation.IsIrreducible E2.ρ := FDRep.isIrreducible_of_simple E2
    exact Representation.isIrreducible_of_nonempty_equiv ⟨hEquiv⟩
  have hLiftDim : Module.finrank 𝔽₄ (ULift.{u} E2) = 2 := by
    -- `ULift` is linearly equivalent to the original carrier, so the degree remains `2`.
    calc
      Module.finrank 𝔽₄ (ULift.{u} E2) = Module.finrank 𝔽₄ E2 :=
        (ULift.moduleEquiv : ULift.{u} E2 ≃ₗ[𝔽₄] E2).finrank_eq
      _ = 2 := by
        simpa using hE2dim
  refine ⟨ULift.{u} E2, inferInstance, inferInstance, inferInstance, ρLift, ?_, hLiftDim⟩
  exact hLiftIrreducible

/-- Helper for Exercise 18-18.6-3: a classification by scalar-extended source models supplies
the universal realizability owner. -/
theorem a5_irreducible_degree_two_realizable_owner_over_f4_of_scalarExtension_classification
    (hclass :
      ∀ {K : Type u} [Field K] [Algebra 𝔽₄ K]
        {V : Type v} [AddCommGroup V] [Module K V]
        (ρ : Representation K A5 V) [ρ.IsIrreducible],
        Module.finrank K V = 2 →
          ∃ (W₀ : Type v) (_ : AddCommGroup W₀) (_ : Module 𝔽₄ W₀)
            (_ : FiniteDimensional 𝔽₄ W₀) (ρ₀ : Representation 𝔽₄ A5 W₀),
            Nonempty (ρ.Equiv (Representation.scalarExtension ρ₀))) :
    ∀ {K : Type u} [Field K] [Algebra 𝔽₄ K]
      {V : Type v} [AddCommGroup V] [Module K V]
      (ρ : Representation K A5 V) [ρ.IsIrreducible],
      Module.finrank K V = 2 → Representation.IsRealizableOver 𝔽₄ ρ := by
  intro K _ _ V _ _ ρ _ hV
  -- Apply the classification theorem, then turn the concrete scalar-extension equivalence into
  -- the definition of realizability over `𝔽₄`.
  rcases hclass ρ hV with ⟨W₀, _, _, _, ρ₀, ⟨e⟩⟩
  exact Representation.isRealizableOver_of_equiv_scalarExtension ρ₀ e

/-- Helper for Exercise 18-18.6-3: scalar extension along the identity field map gives an
equivariantly isomorphic representation. -/
theorem nonempty_equiv_scalarExtension_self
    {k : Type u} [Field k] {G : Type u} [Group G]
    {V : Type v} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    Nonempty (ρ.Equiv (Representation.scalarExtension ρ)) := by
  -- The tensor left unitor is the comparison map; checking equivariance reduces to pure tensors.
  refine ⟨Representation.Equiv.mk (_root_.TensorProduct.lid k V).symm ?_⟩
  intro g
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  change (1 : k) ⊗ₜ[k] (ρ g x) =
    LinearMap.baseChange k (ρ g) ((1 : k) ⊗ₜ[k] x)
  rw [LinearMap.baseChange_tmul]

/-- Helper for Exercise 18-18.6-3: over the source field itself, the scalar-extension
classification is just the identity scalar-extension equivalence. -/
theorem a5_irreducible_degree_two_scalarExtension_classification_self_over_f4
    {V : Type v} [AddCommGroup V] [Module 𝔽₄ V]
    (ρ : Representation 𝔽₄ A5 V) [ρ.IsIrreducible]
    (hV : Module.finrank 𝔽₄ V = 2) :
    ∃ (W₀ : Type v) (_ : AddCommGroup W₀) (_ : Module 𝔽₄ W₀)
      (_ : FiniteDimensional 𝔽₄ W₀) (ρ₀ : Representation 𝔽₄ A5 W₀),
      Nonempty (ρ.Equiv (Representation.scalarExtension ρ₀)) := by
  -- A positive finite rank supplies the finite-dimensional source model, namely `ρ` itself.
  letI : FiniteDimensional 𝔽₄ V := .of_finrank_pos (by simp [hV])
  exact ⟨V, inferInstance, inferInstance, inferInstance, ρ,
    nonempty_equiv_scalarExtension_self ρ⟩

/-- Helper for Exercise 18-18.6-3: the realizability assertion is immediate over the source
field itself. -/
theorem a5_irreducible_degree_two_realizable_self_over_f4
    {V : Type v} [AddCommGroup V] [Module 𝔽₄ V]
    (ρ : Representation 𝔽₄ A5 V) [ρ.IsIrreducible]
    (hV : Module.finrank 𝔽₄ V = 2) :
    Representation.IsRealizableOver 𝔽₄ ρ := by
  -- Convert the identity scalar-extension classification into the `IsRealizableOver` package.
  rcases a5_irreducible_degree_two_scalarExtension_classification_self_over_f4 ρ hV with
    ⟨W₀, _, _, _, ρ₀, ⟨e⟩⟩
  exact Representation.isRealizableOver_of_equiv_scalarExtension ρ₀ e

/-- Helper for Exercise 18-18.6-3: an equivalence of source representations remains an
equivalence after scalar extension from `𝔽₄` to an extension field. -/
theorem a5_scalarExtensionEquiv_of_equiv
    {K : Type u} [Field K] [Algebra 𝔽₄ K]
    {W W' : Type*} [AddCommGroup W] [Module 𝔽₄ W]
    [AddCommGroup W'] [Module 𝔽₄ W']
    {ρ : Representation 𝔽₄ A5 W} {σ : Representation 𝔽₄ A5 W'}
    (e : ρ.Equiv σ) :
    Nonempty
      ((Representation.scalarExtension (k := K) ρ).Equiv
        (Representation.scalarExtension (k := K) σ)) := by
  -- Base-change the intertwining linear equivalence and verify equivariance on pure tensors.
  refine ⟨Representation.Equiv.mk (e.toLinearEquiv.baseChange 𝔽₄ K W W') ?_⟩
  intro g
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  have hx := LinearMap.congr_fun (e.isIntertwining' g) x
  simpa [Representation.scalarExtension]
    using congrArg (fun y ↦ a ⊗ₜ[𝔽₄] y) hx

/-- Helper for Exercise 18-18.6-3: a bundled source model equivalence unpacks to the
scalar-extension classification existential used by the target-facing theorem. -/
theorem a5_scalarExtension_classification_of_sourceModelEquiv
    {K : Type u} [Field K] [Algebra 𝔽₄ K]
    {V : Type v} [AddCommGroup V] [Module K V]
    (ρ : Representation K A5 V)
    (hsrc :
      ∃ E : FDRep 𝔽₄ A5,
        CategoryTheory.Simple E ∧ Module.finrank 𝔽₄ E.V = 2 ∧
          Nonempty (ρ.Equiv (Representation.scalarExtension E.ρ))) :
    ∃ (W₀ : Type v) (_ : AddCommGroup W₀) (_ : Module 𝔽₄ W₀)
      (_ : FiniteDimensional 𝔽₄ W₀) (ρ₀ : Representation 𝔽₄ A5 W₀),
      Nonempty (ρ.Equiv (Representation.scalarExtension ρ₀)) := by
  -- Move the source model into the target universe by conjugating the action across `ULift`,
  -- then scalar-extend that equivalence and compose it with the classified target equivalence.
  rcases hsrc with ⟨E, _hE_simple, _hE_dim, ⟨eρE⟩⟩
  let eLift : E ≃ₗ[𝔽₄] ULift.{v} E := ULift.moduleEquiv.symm
  let ρLift : Representation 𝔽₄ A5 (ULift.{v} E) :=
    { toFun := fun g ↦ eLift.conj (E.ρ g)
      map_one' := by
        ext x
        simp [eLift, LinearEquiv.conj_apply_apply]
      map_mul' := by
        intro g h
        ext x
        simp [eLift, LinearEquiv.conj_apply_apply, map_mul] }
  have hELift : Representation.Equiv E.ρ ρLift := by
    -- The lifting equivalence intertwines the original and transported source actions.
    refine Representation.Equiv.mk eLift ?_
    intro g
    ext x
    simp [ρLift, eLift, LinearEquiv.conj_apply_apply]
  rcases a5_scalarExtensionEquiv_of_equiv (K := K) hELift with ⟨hScalarLift⟩
  have hScalarLift' :
      (Representation.scalarExtension (k := K) E.ρ).Equiv
        (Representation.scalarExtension (k := K) ρLift) := hScalarLift
  exact ⟨ULift.{v} E, inferInstance, inferInstance, inferInstance, ρLift,
    ⟨eρE.trans hScalarLift'⟩⟩

/-- Helper for Exercise 18-18.6-3: a bundled source model equivalence is already a
realizability witness over `𝔽₄`. -/
theorem a5_isRealizableOver_of_sourceModelEquiv
    {K : Type u} [Field K] [Algebra 𝔽₄ K]
    {V : Type v} [AddCommGroup V] [Module K V]
    (ρ : Representation K A5 V)
    (hsrc :
      ∃ E : FDRep 𝔽₄ A5,
        CategoryTheory.Simple E ∧ Module.finrank 𝔽₄ E.V = 2 ∧
          Nonempty (ρ.Equiv (Representation.scalarExtension E.ρ))) :
    Representation.IsRealizableOver 𝔽₄ ρ := by
  -- First move the bundled source carrier into the target universe, then repackage the resulting
  -- scalar-extension equivalence as the definition of realizability.
  rcases a5_scalarExtension_classification_of_sourceModelEquiv ρ hsrc with
    ⟨W₀, _, _, _, ρ₀, ⟨e⟩⟩
  exact Representation.isRealizableOver_of_equiv_scalarExtension ρ₀ e

/-- Helper for Exercise 18-18.6-3: conjugating a representation action by a linear equivalence
sends the identity action to the identity action. -/
private theorem conjugateRepresentation_map_one
    {k G V W : Type*} [CommSemiring k] [Monoid G]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    (e : V ≃ₗ[k] W) (ρ : Representation k G V) :
    e.conj (ρ 1) = 1 := by
  -- The representation sends `1` to the identity, and conjugation preserves the identity map.
  calc
    e.conj (ρ 1) = e.conj 1 := by rw [map_one]
    _ = 1 := LinearEquiv.conj_id e

/-- Helper for Exercise 18-18.6-3: conjugating a representation action by a linear equivalence
preserves multiplication of group actions. -/
private theorem conjugateRepresentation_map_mul
    {k G V W : Type*} [CommSemiring k] [Monoid G]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    (e : V ≃ₗ[k] W) (ρ : Representation k G V) (g h : G) :
    e.conj (ρ (g * h)) = e.conj (ρ g) * e.conj (ρ h) := by
  -- Expand conjugation on vectors and use the multiplication law for `ρ`.
  ext x
  simp [LinearEquiv.conj_apply_apply, map_mul]

/-- Helper for Exercise 18-18.6-3: transport a representation across a linear equivalence by
conjugating every group action. -/
private def conjugateRepresentation
    {k G V W : Type*} [CommSemiring k] [Monoid G]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    (e : V ≃ₗ[k] W) (ρ : Representation k G V) :
    Representation k G W where
  toFun := fun g ↦ e.conj (ρ g)
  map_one' := conjugateRepresentation_map_one e ρ
  map_mul' := conjugateRepresentation_map_mul e ρ

/-- Helper for Exercise 18-18.6-3: the transporting linear equivalence intertwines a
representation with its conjugate transport. -/
private theorem conjugateRepresentation_intertwining
    {k G V W : Type*} [CommSemiring k] [Monoid G]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    (e : V ≃ₗ[k] W) (ρ : Representation k G V) (g : G) :
    e ∘ₗ (ρ g) = ((conjugateRepresentation e ρ) g) ∘ₗ e := by
  -- Equivariance is exactly the defining conjugation formula, checked after evaluation.
  ext x
  simp [conjugateRepresentation, LinearEquiv.conj_apply_apply]

/-- Helper for Exercise 18-18.6-3: the transporting linear equivalence gives a representation
equivalence to the conjugate transport. -/
private def equiv_conjugateRepresentation
    {k G V W : Type*} [CommSemiring k] [Monoid G]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    (e : V ≃ₗ[k] W) (ρ : Representation k G V) :
    ρ.Equiv (conjugateRepresentation e ρ) :=
  Representation.Equiv.mk e (conjugateRepresentation_intertwining e ρ)

/-- Helper for Exercise 18-18.6-3: over `𝔽₄` itself, the source-model frontier is witnessed by a
small `FDRep` obtained by transporting the target to the standard two-dimensional plane. -/
theorem a5_degree_two_source_model_scalarExtension_equiv_self_over_f4
    {V : Type v} [AddCommGroup V] [Module 𝔽₄ V]
    (ρ : Representation 𝔽₄ A5 V) [ρ.IsIrreducible]
    (hV : Module.finrank 𝔽₄ V = 2) :
    ∃ E : FDRep 𝔽₄ A5,
      CategoryTheory.Simple E ∧ Module.finrank 𝔽₄ E.V = 2 ∧
        Nonempty (ρ.Equiv (Representation.scalarExtension E.ρ)) := by
  -- Positive finite rank gives a basis, which identifies the carrier with the small standard
  -- plane used by `FDRep 𝔽₄ A5`.
  letI : FiniteDimensional 𝔽₄ V := .of_finrank_pos (by simp [hV])
  let eFin : Fin (Module.finrank 𝔽₄ V) ≃ Fin 2 := by
    simpa [hV] using (_root_.Equiv.refl (Fin 2))
  let b : Module.Basis (Fin 2) 𝔽₄ V := (Module.finBasis 𝔽₄ V).reindex eFin
  let eV : V ≃ₗ[𝔽₄] (Fin 2 → 𝔽₄) := b.equivFun
  let ρstd : Representation 𝔽₄ A5 (Fin 2 → 𝔽₄) := conjugateRepresentation eV ρ
  have hEquiv : ρ.Equiv ρstd := by
    -- The basis equivalence intertwines `ρ` with the conjugated standard-plane action.
    exact equiv_conjugateRepresentation eV ρ
  have hρstd_irreducible : ρstd.IsIrreducible := by
    -- Irreducibility is invariant under the just-constructed representation equivalence.
    exact Representation.isIrreducible_of_nonempty_equiv ⟨hEquiv⟩
  letI : ρstd.IsIrreducible := hρstd_irreducible
  refine ⟨FDRep.of ρstd, ?_, ?_, ?_⟩
  · -- Bundle the irreducible standard-plane model as a simple `FDRep`.
    letI : Representation.IsIrreducible (FDRep.of ρstd).ρ := by
      simpa using hρstd_irreducible
    exact FDRep.simple_of_isIrreducible (FDRep.of ρstd)
  · -- The standard plane has dimension `2` over `𝔽₄`.
    simp [ρstd]
  · -- Compose the coordinate-change equivalence with identity scalar extension over `𝔽₄`.
    rcases nonempty_equiv_scalarExtension_self ρstd with ⟨eSelf⟩
    exact ⟨hEquiv.trans eSelf⟩

/-- Helper for Exercise 18-18.6-3: once a target is known to be the scalar extension of a
simple degree-`2` source slot, the bundled source-model frontier is already closed. -/
theorem a5_source_model_scalarExtension_equiv_of_source_slot
    {K : Type u} [Field K] [Algebra 𝔽₄ K]
    (E : FDRep 𝔽₄ A5) (hE_simple : CategoryTheory.Simple E)
    (hE_dim : Module.finrank 𝔽₄ E.V = 2) :
    ∃ E₀ : FDRep 𝔽₄ A5,
      CategoryTheory.Simple E₀ ∧ Module.finrank 𝔽₄ E₀.V = 2 ∧
        Nonempty
          ((Representation.scalarExtension (k := K) E.ρ).Equiv
            (Representation.scalarExtension E₀.ρ)) := by
  -- Reuse the same source slot; the remaining equivalence is reflexivity after scalar extension.
  exact ⟨E, hE_simple, hE_dim, ⟨Representation.Equiv.refl _⟩⟩

/-- Helper for Exercise 18-18.6-3: the direct `SL₂(𝔽₄)` source slot keeps degree `2`
after scalar extension to any extension field of `𝔽₄`. -/
theorem a5_natural_source_slot_scalarExtension_finrank_data
    {K : Type u} [Field K] [Algebra 𝔽₄ K] :
    ∃ E : FDRep 𝔽₄ A5,
      CategoryTheory.Simple E ∧ Module.finrank 𝔽₄ E.V = 2 ∧
        Module.finrank K (K ⊗[𝔽₄] E.V) = 2 := by
  -- Start from the already-constructed direct `A₅ ≃ SL₂(𝔽₄)` source model.
  rcases a5_natural_sl2_f4_source_slot with ⟨E, hE_simple, hE_dim⟩
  refine ⟨E, hE_simple, hE_dim, ?_⟩
  -- Scalar extension preserves the finite dimension of the underlying source carrier.
  simp [hE_dim, Module.finrank_baseChange (R := K) (S := 𝔽₄) (M' := E.V)]

/-- Helper for Exercise 18-18.6-3: scalar extension acts on pure tensors by applying the
source action to the second tensor factor. -/
private theorem scalarExtension_apply_tmul
    {k₀ k G W : Type*} [Field k₀] [Field k] [Algebra k₀ k]
    [Group G] [AddCommGroup W] [Module k₀ W]
    (ρ : Representation k₀ G W) (g : G) (a : k) (x : W) :
    (Representation.scalarExtension (k := k) ρ g) (a ⊗ₜ[k₀] x) =
      a ⊗ₜ[k₀] (ρ g x) := by
  -- The scalar-extension representation is the endomorphism base-change hom.
  change ((Module.End.baseChangeHom k₀ k W) (ρ g)) (a ⊗ₜ[k₀] x) = _
  exact LinearMap.baseChange_tmul (ρ g) a x

/-- Helper for Exercise 18-18.6-3: base-change a source subrepresentation to a
subrepresentation of the scalar-extended representation. -/
private def scalarExtensionSubrepresentation
    {k₀ k G W : Type*} [Field k₀] [Field k] [Algebra k₀ k]
    [Group G] [AddCommGroup W] [Module k₀ W]
    {ρ : Representation k₀ G W} (σ : Subrepresentation ρ) :
    Subrepresentation (Representation.scalarExtension (k := k) ρ) where
  toSubmodule := σ.toSubmodule.baseChange k
  apply_mem_toSubmodule := by
    intro g x hx
    rcases hx with ⟨y, rfl⟩
    refine ⟨((σ.toRepresentation g).baseChange k) y, ?_⟩
    -- The base-changed action preserves the base-changed subspace, checked on pure tensors.
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a s =>
        simp only [LinearMap.baseChange_tmul, Submodule.subtype_apply]
        exact congrArg (fun z : σ.toSubmodule ↦ a ⊗ₜ[k₀] (z : W)) (Subtype.ext rfl)
    | add y z hy hz =>
        simp [map_add, hy, hz]

/-- Helper for Exercise 18-18.6-3: the base-changed bottom subrepresentation is bottom. -/
private theorem scalarExtensionSubrepresentation_bot
    {k₀ k G W : Type*} [Field k₀] [Field k] [Algebra k₀ k]
    [Group G] [AddCommGroup W] [Module k₀ W]
    {ρ : Representation k₀ G W} :
    scalarExtensionSubrepresentation (k := k) (ρ := ρ) (⊥ : Subrepresentation ρ) = ⊥ := by
  -- Push the equality to submodules, where `Submodule.baseChange_bot` applies directly.
  apply Subrepresentation.toSubmodule_injective
  change (⊥ : Submodule k₀ W).baseChange k = (⊥ : Submodule k (k ⊗[k₀] W))
  rw [Submodule.baseChange_bot]

/-- Helper for Exercise 18-18.6-3: the base-changed top subrepresentation is top. -/
private theorem scalarExtensionSubrepresentation_top
    {k₀ k G W : Type*} [Field k₀] [Field k] [Algebra k₀ k]
    [Group G] [AddCommGroup W] [Module k₀ W]
    {ρ : Representation k₀ G W} :
    scalarExtensionSubrepresentation (k := k) (ρ := ρ) (⊤ : Subrepresentation ρ) = ⊤ := by
  -- Push the equality to submodules, where `Submodule.baseChange_top` applies directly.
  apply Subrepresentation.toSubmodule_injective
  change (⊤ : Submodule k₀ W).baseChange k = (⊤ : Submodule k (k ⊗[k₀] W))
  rw [Submodule.baseChange_top]

/-- Helper for Exercise 18-18.6-3: irreducibility descends from a scalar extension over fields. -/
theorem isIrreducible_of_scalarExtension
    {k₀ k G W : Type*} [Field k₀] [Field k] [Algebra k₀ k]
    [Group G] [AddCommGroup W] [Module k₀ W]
    (ρ : Representation k₀ G W)
    [Representation.IsIrreducible (Representation.scalarExtension (k := k) ρ)] :
    ρ.IsIrreducible := by
  have hbot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro hbt
    have hbtK :
        scalarExtensionSubrepresentation (k := k) (ρ := ρ) (⊥ : Subrepresentation ρ) =
          (⊤ : Subrepresentation (Representation.scalarExtension (k := k) ρ)) := by
      calc
        scalarExtensionSubrepresentation (k := k) (ρ := ρ) (⊥ : Subrepresentation ρ)
            = scalarExtensionSubrepresentation (k := k) (ρ := ρ)
                (⊤ : Subrepresentation ρ) := by
              rw [hbt]
        _ = ⊤ := scalarExtensionSubrepresentation_top
    -- The scalar extension is irreducible, so its bottom and top subrepresentations differ.
    exact bot_ne_top (scalarExtensionSubrepresentation_bot.symm.trans hbtK)
  letI : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hbot_ne_top⟩⟩
  rw [Representation.IsIrreducible]
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro σ hσ
  have hσK_top : scalarExtensionSubrepresentation (k := k) σ = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top
        (scalarExtensionSubrepresentation (k := k) σ) with hbot | htop
    · exfalso
      apply hσ
      apply Subrepresentation.toSubmodule_injective
      exact Submodule.baseChange_injective (A := k) (p := σ.toSubmodule) (q := ⊥) (by
        simpa [scalarExtensionSubrepresentation] using
          congrArg Subrepresentation.toSubmodule hbot)
    · exact htop
  -- Faithful flatness of a field extension reflects the top equality of submodules.
  apply Subrepresentation.toSubmodule_injective
  exact Submodule.baseChange_injective (A := k) (p := σ.toSubmodule) (q := ⊤) (by
    simpa [scalarExtensionSubrepresentation] using
      congrArg Subrepresentation.toSubmodule hσK_top)

/-- Helper for Exercise 18-18.6-3: a direct realizability witness with an irreducible degree-`2`
target supplies the bundled simple degree-`2` source-model package. -/
theorem a5_sourceModelEquiv_of_isRealizableOver_degree_two
    {K : Type u} [Field K] [Algebra 𝔽₄ K]
    {V : Type v} [AddCommGroup V] [Module K V]
    (ρ : Representation K A5 V) [ρ.IsIrreducible]
    (hV : Module.finrank K V = 2) (hreal : Representation.IsRealizableOver 𝔽₄ ρ) :
    ∃ E : FDRep 𝔽₄ A5,
      CategoryTheory.Simple E ∧ Module.finrank 𝔽₄ E.V = 2 ∧
        Nonempty (ρ.Equiv (Representation.scalarExtension E.ρ)) := by
  -- Unpack realizability into a finite source representation and an equivariant scalar-extension
  -- comparison with the target.
  rcases exists_equiv_scalarExtension_of_isRealizableOver hreal with
    ⟨W₀, _instAddCommGroupW₀, _instModuleW₀, _instFiniteDimensionalW₀, ρ₀, ⟨eρ₀⟩⟩
  have hρ₀_scalar_irreducible :
      (Representation.scalarExtension (k := K) ρ₀).IsIrreducible := by
    exact Representation.isIrreducible_of_nonempty_equiv ⟨eρ₀⟩
  have hρ₀_irreducible : ρ₀.IsIrreducible := by
    -- Reflect irreducibility from the scalar extension back to the source field.
    letI : (Representation.scalarExtension (k := K) ρ₀).IsIrreducible :=
      hρ₀_scalar_irreducible
    exact isIrreducible_of_scalarExtension (k := K) ρ₀
  letI : ρ₀.IsIrreducible := hρ₀_irreducible
  have hρ₀_dim : Module.finrank 𝔽₄ W₀ = 2 := by
    -- Compare dimensions across the scalar-extension equivalence and base-change formula.
    calc
      Module.finrank 𝔽₄ W₀ = Module.finrank K (K ⊗[𝔽₄] W₀) := by
        symm
        exact Module.finrank_baseChange (R := K) (S := 𝔽₄) (M' := W₀)
      _ = Module.finrank K V := eρ₀.toLinearEquiv.finrank_eq.symm
      _ = 2 := hV
  let eFin : Fin (Module.finrank 𝔽₄ W₀) ≃ Fin 2 := by
    simpa [hρ₀_dim] using (_root_.Equiv.refl (Fin 2))
  let b : Module.Basis (Fin 2) 𝔽₄ W₀ := (Module.finBasis 𝔽₄ W₀).reindex eFin
  let eW₀ : W₀ ≃ₗ[𝔽₄] (Fin 2 → 𝔽₄) := b.equivFun
  let ρstd : Representation 𝔽₄ A5 (Fin 2 → 𝔽₄) := conjugateRepresentation eW₀ ρ₀
  have hρstd_equiv : ρ₀.Equiv ρstd := by
    -- Move the finite source witness to the small standard plane before bundling it as `FDRep`.
    exact equiv_conjugateRepresentation eW₀ ρ₀
  have hρstd_irreducible : ρstd.IsIrreducible := by
    -- Irreducibility follows across the coordinate-change equivalence.
    exact Representation.isIrreducible_of_nonempty_equiv ⟨hρstd_equiv⟩
  letI : ρstd.IsIrreducible := hρstd_irreducible
  rcases a5_scalarExtensionEquiv_of_equiv (K := K) hρstd_equiv with ⟨hScalarStd⟩
  have hScalarStd' :
      (Representation.scalarExtension (k := K) ρ₀).Equiv
        (Representation.scalarExtension (k := K) ρstd) := hScalarStd
  refine ⟨FDRep.of ρstd, ?_, ?_, ?_⟩
  · -- Irreducibility of the standard-plane source is exactly simplicity of the bundled owner.
    letI : Representation.IsIrreducible (FDRep.of ρstd).ρ := by
      simpa using hρstd_irreducible
    exact FDRep.simple_of_isIrreducible (FDRep.of ρstd)
  · -- The standard source plane has degree `2` over `𝔽₄`.
    simp [ρstd]
  · -- Compose the original realizability equivalence with the scalar-extended coordinate change.
    exact ⟨eρ₀.trans hScalarStd'⟩

/-- Helper for Exercise 18-18.6-3: a direct realizability descent theorem supplies the bundled
simple source-model package used by the source-route wrappers. -/
theorem a5_sourceModelEquiv_of_realizability_descent
    (hdesc :
      ∀ {K : Type u} [Field K] [Algebra 𝔽₄ K]
        {V : Type v} [AddCommGroup V] [Module K V]
        (ρ : Representation K A5 V) [ρ.IsIrreducible],
        Module.finrank K V = 2 → Representation.IsRealizableOver 𝔽₄ ρ) :
    ∀ {K : Type u} [Field K] [Algebra 𝔽₄ K]
      {V : Type v} [AddCommGroup V] [Module K V]
      (ρ : Representation K A5 V) [ρ.IsIrreducible],
      Module.finrank K V = 2 →
        ∃ E : FDRep 𝔽₄ A5,
          CategoryTheory.Simple E ∧ Module.finrank 𝔽₄ E.V = 2 ∧
            Nonempty (ρ.Equiv (Representation.scalarExtension E.ρ)) := by
  intro K _ _ V _ _ ρ _ hV
  -- First obtain the direct smaller-field model, then use the proved packaging lemma to
  -- convert it into the simple finite-dimensional source owner expected downstream.
  exact a5_sourceModelEquiv_of_isRealizableOver_degree_two ρ hV (hdesc ρ hV)

/-- Helper for Exercise 18-18.6-3: a direct realizability descent theorem supplies the
unbundled scalar-extension classification statement. -/
theorem a5_scalarExtension_classification_of_realizability_descent
    (hdesc :
      ∀ {K : Type u} [Field K] [Algebra 𝔽₄ K]
        {V : Type v} [AddCommGroup V] [Module K V]
        (ρ : Representation K A5 V) [ρ.IsIrreducible],
        Module.finrank K V = 2 → Representation.IsRealizableOver 𝔽₄ ρ) :
    ∀ {K : Type u} [Field K] [Algebra 𝔽₄ K]
      {V : Type v} [AddCommGroup V] [Module K V]
      (ρ : Representation K A5 V) [ρ.IsIrreducible],
      Module.finrank K V = 2 →
        ∃ (W₀ : Type v) (_ : AddCommGroup W₀) (_ : Module 𝔽₄ W₀)
          (_ : FiniteDimensional 𝔽₄ W₀) (ρ₀ : Representation 𝔽₄ A5 W₀),
          Nonempty (ρ.Equiv (Representation.scalarExtension ρ₀)) := by
  intro K _ _ V _ _ ρ _ hV
  -- Unpack the direct realizability witness in the orientation required by the classification
  -- theorem, without redoing any finite-rank or irreducibility bookkeeping.
  exact exists_equiv_scalarExtension_of_isRealizableOver (hdesc ρ hV)

/-- Helper for Exercise 18-18.6-3: a rank-one realizability theorem for `SL(2,𝔽₄)` transports
back across the exceptional equivalence `A₅ ≃ SL(2,𝔽₄)`. -/
theorem a5_realizableOver_of_sl2F4_realizableOver
    (hSL :
      ∀ {K : Type u} [Field K] [Algebra 𝔽₄ K]
        {V : Type v} [AddCommGroup V] [Module K V]
        (σ : Representation K (SL(2, 𝔽₄)) V) [σ.IsIrreducible],
        Module.finrank K V = 2 → Representation.IsRealizableOver 𝔽₄ σ) :
    ∀ {K : Type u} [Field K] [Algebra 𝔽₄ K]
      {V : Type v} [AddCommGroup V] [Module K V]
      (ρ : Representation K A5 V) [ρ.IsIrreducible],
      Module.finrank K V = 2 → Representation.IsRealizableOver 𝔽₄ ρ := by
  intro K _ _ V _ _ ρ _ hV
  rcases _root_.alternatingGroup_fin5_mulEquiv_sl2_f4_direct with ⟨e⟩
  let σ : Representation K (SL(2, 𝔽₄)) V := ρ.comp e.symm.toMonoidHom
  have hσirr : σ.IsIrreducible := by
    -- Precompose the `A₅` action by the inverse group equivalence to get an irreducible `SL₂`
    -- action on the same carrier.
    exact isIrreducible_comp_of_mulEquiv_six_three e.symm ρ
  letI : σ.IsIrreducible := hσirr
  have hσreal : Representation.IsRealizableOver 𝔽₄ σ := hSL σ hV
  have hσcomp : Representation.IsRealizableOver 𝔽₄ (σ.comp e.toMonoidHom) :=
    isRealizableOver_comp_of_mulEquiv e σ hσreal
  rcases nonempty_equiv_comp_symm_comp_mulEquiv e ρ with ⟨eρ⟩
  -- The double precomposition is equivalent to the original `A₅` representation, so pull the
  -- realizability witness back along that equivalence.
  exact Representation.isRealizableOver_of_equiv hσcomp eρ

/-- Helper for Exercise 18-18.6-3: the source-faithful descent frontier says that every
irreducible degree-`2` representation over an extension field of `𝔽₄` is realizable over `𝔽₄`.
This isolates the only remaining mathematical classification input from the scalar-extension
packaging below. -/
theorem a5_irreducible_degree_two_realizable_descent_over_f4 :
    ∀ {K : Type u} [Field K] [Algebra 𝔽₄ K]
      {V : Type v} [AddCommGroup V] [Module K V]
      (ρ : Representation K A5 V) [ρ.IsIrreducible],
      Module.finrank K V = 2 → Representation.IsRealizableOver 𝔽₄ ρ := by
  -- Route correction: the A5-to-SL2 transport is now formal; the only remaining mathematical
  -- input is the rank-one `SL₂(𝔽₄)` classifier isolated in `RankOneSL2F4.lean`.
  exact a5_realizableOver_of_sl2F4_realizableOver
    sl2F4_irreducible_degreeTwo_realizableOver_f4_core

/-- Helper for Exercise 18-18.6-3: the source-model package is a formal consequence of the
direct realizability descent frontier. -/
theorem a5_degree_two_source_model_scalarExtension_equiv :
    ∀ {K : Type u} [Field K] [Algebra 𝔽₄ K]
      {V : Type v} [AddCommGroup V] [Module K V]
      (ρ : Representation K A5 V) [ρ.IsIrreducible],
      Module.finrank K V = 2 →
        ∃ E : FDRep 𝔽₄ A5,
          CategoryTheory.Simple E ∧ Module.finrank 𝔽₄ E.V = 2 ∧
            Nonempty (ρ.Equiv (Representation.scalarExtension E.ρ)) := by
  intro K _ _ V _ _ ρ _ hV
  -- Route correction: the old proof made this source-model statement the primitive
  -- classification input.  It is now just a packaging consequence of direct realizability.
  exact
    a5_sourceModelEquiv_of_realizability_descent
      a5_irreducible_degree_two_realizable_descent_over_f4 ρ hV

/-- Helper for Exercise 18-18.6-3: every irreducible degree-`2` representation over an
extension field is equivalent to the scalar extension of a finite-dimensional `𝔽₄[A₅]` model.
This is the single remaining source/classification frontier. -/
theorem a5_irreducible_degree_two_scalarExtension_classification_over_f4 :
    ∀ {K : Type u} [Field K] [Algebra 𝔽₄ K]
      {V : Type v} [AddCommGroup V] [Module K V]
      (ρ : Representation K A5 V) [ρ.IsIrreducible],
      Module.finrank K V = 2 →
        ∃ (W₀ : Type v) (_ : AddCommGroup W₀) (_ : Module 𝔽₄ W₀)
          (_ : FiniteDimensional 𝔽₄ W₀) (ρ₀ : Representation 𝔽₄ A5 W₀),
          Nonempty (ρ.Equiv (Representation.scalarExtension ρ₀)) := by
  intro K _ _ V _ _ ρ _ hV
  -- The hard descent statement gives `IsRealizableOver`; the shared adapter unpacks that witness
  -- into the scalar-extension equivalence orientation required by this classification theorem.
  exact
    a5_scalarExtension_classification_of_realizability_descent
      a5_irreducible_degree_two_realizable_descent_over_f4 ρ hV

/-- Helper for Exercise 18-18.6-3: classification/descent of all irreducible degree-`2`
representations over extension fields of `𝔽₄`. This is the second owner-level input missing from
the current formal route. -/
theorem a5_irreducible_degree_two_realizable_owner_over_f4 :
    ∀ {K : Type u} [Field K] [Algebra 𝔽₄ K]
      {V : Type v} [AddCommGroup V] [Module K V]
      (ρ : Representation K A5 V) [ρ.IsIrreducible],
      Module.finrank K V = 2 → Representation.IsRealizableOver 𝔽₄ ρ := by
  -- Reuse the isolated descent frontier directly; the scalar-extension classification theorem
  -- above is now only the orientation/unpacking companion.
  exact a5_irreducible_degree_two_realizable_descent_over_f4

/-- Helper for Exercise 18-18.6-3: Serre's source route for the two degree-`2` Brauer slots of
`A₅` in characteristic `2`. The missing owner-level input is exactly that one gets a descended
irreducible degree-`2` `𝔽₄[A₅]`-module from the `χ₃` reductions, and that every irreducible
degree-`2` representation over an extension of `𝔽₄` is realizable over `𝔽₄`. -/
theorem a5_degree_two_source_route_over_f4 :
    (∃ (W : Type u) (_ : AddCommGroup W) (_ : Module 𝔽₄ W) (_ : FiniteDimensional 𝔽₄ W)
        (ρ : Representation 𝔽₄ A5 W),
        ρ.IsIrreducible ∧ Module.finrank 𝔽₄ W = 2) ∧
      (∀ {K : Type u} [Field K] [Algebra 𝔽₄ K]
          {V : Type v} [AddCommGroup V] [Module K V]
          (ρ : Representation K A5 V) [ρ.IsIrreducible],
          Module.finrank K V = 2 → Representation.IsRealizableOver 𝔽₄ ρ) := by
  -- Route correction: the blocker is not an ad hoc explicit matrix model. Serre's proof first
  -- identifies the two degree-`2` Brauer slots by reducing the ordinary degree-`3` rows
  -- `χ₂, χ₃`, then uses that those modular characters take values in `𝔽₄` on the `5`-cycle
  -- classes. Packaging that source-faithful argument here leaves the target file with only the
  -- formal descent and `SL₂(𝔽₄)` consequences.
  -- TODO for Exercise 18-18.6-3: the stabilized frontier is now explicit.
  -- 1. The p-regular/Brauer-label bridge and the two source rows are now public in
  --    `SourceCharacters.lean`, via
  --    `alternating_group_fin5_pRegularConjClass_modTwo_equiv_brauer_labels`,
  --    `a5_source_degree_two_character_function_phi_modTwo`, and
  --    `a5_source_degree_two_character_function_psi_modTwo`.
  -- 2. The remaining missing owner is source-faithful: construct actual simple degree-`2`
  --    `𝔽₄[A₅]` modules from the reductions of Serre's two ordinary degree-`3` rows.
  -- 3. Once those two owners exist, compare their scalar extensions with the algebraically
  --    closed Brauer-labeled degree-`2` slots and descend realizability by
  --    `Representation.isRealizableOver_of_equiv`.
  -- The formal source route now separates the two owner-level inputs from the target-facing
  -- conjunction: one source slot supplies the existence half, and the classification/descent
  -- owner supplies the universal realizability half.
  exact ⟨a5_degree_two_source_slot_owner_over_f4,
    a5_irreducible_degree_two_realizable_owner_over_f4⟩

/-- Helper for Exercise 18-18.6-3: extract one descended irreducible degree-`2` `𝔽₄[A₅]`-slot
from the full source-faithful characteristic-`2` package. -/
theorem a5_degree_two_source_slot_exists_over_f4 :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module 𝔽₄ W) (_ : FiniteDimensional 𝔽₄ W)
      (ρ : Representation 𝔽₄ A5 W),
      ρ.IsIrreducible ∧ Module.finrank 𝔽₄ W = 2 := by
  -- The group-isomorphism consequence only needs the source slot, so avoid routing this
  -- extraction through the still-open universal realizability classification.
  exact a5_degree_two_source_slot_owner_over_f4

/-- Helper for Exercise 18-18.6-3: every irreducible degree-`2` representation of `A₅` over an
extension of `𝔽₄` is realizable over `𝔽₄`. -/
theorem a5_irreducible_degree_two_realizable_over_f4
    {K : Type u} [Field K] [Algebra 𝔽₄ K]
    {V : Type v} [AddCommGroup V] [Module K V]
    (ρ : Representation K A5 V) [ρ.IsIrreducible]
    (hV : Module.finrank K V = 2) :
    Representation.IsRealizableOver 𝔽₄ ρ := by
  -- Reuse the realizability component of the same source-faithful package.
  exact a5_degree_two_source_route_over_f4.2 ρ hV

end Representation
