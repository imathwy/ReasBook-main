import Mathlib
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver

noncomputable section

universe u v w u₀

namespace Representation

local notation "A5" => alternatingGroup (Fin 5)

/-- Helper for Exercise 18-18.6-3: an explicit equivariant identification with a scalar
extension is exactly a realizability witness over the smaller field. -/
theorem isRealizableOver_of_equiv_scalarExtension
    {k : Type v} [Field k]
    {k₀ : Type u₀} [Field k₀] [Algebra k₀ k]
    {G : Type w} [Group G]
    {W₀ : Type u} [AddCommGroup W₀] [Module k₀ W₀] [FiniteDimensional k₀ W₀]
    {V : Type u} [AddCommGroup V] [Module k V]
    {ρ : Representation k G V} (ρ₀ : Representation k₀ G W₀)
    (e : ρ.Equiv (Representation.scalarExtension ρ₀)) :
    IsRealizableOver k₀ ρ := by
  -- Package the smaller-field model and reverse the supplied equivalence to match the definition.
  refine ⟨W₀, inferInstance, inferInstance, inferInstance, ρ₀, ?_⟩
  exact ⟨e.symm⟩

/-- Helper for Exercise 18-18.6-3: unpacking realizability gives the same source model with the
equivariant isomorphism oriented toward the scalar extension. -/
theorem exists_equiv_scalarExtension_of_isRealizableOver
    {k : Type v} [Field k]
    {k₀ : Type u₀} [Field k₀] [Algebra k₀ k]
    {G : Type w} [Group G]
    {V : Type u} [AddCommGroup V] [Module k V]
    {ρ : Representation k G V}
    (hρ : IsRealizableOver k₀ ρ) :
    ∃ (W₀ : Type u) (_ : AddCommGroup W₀) (_ : Module k₀ W₀)
      (_ : FiniteDimensional k₀ W₀) (ρ₀ : Representation k₀ G W₀),
      Nonempty (ρ.Equiv (Representation.scalarExtension ρ₀)) := by
  -- The definition stores the same equivalence in the opposite direction; reverse it once here.
  rcases hρ with ⟨W₀, _instAddCommGroupW₀, _instModuleW₀, _instFiniteDimensionalW₀,
    ρ₀, ⟨e⟩⟩
  exact ⟨W₀, inferInstance, inferInstance, inferInstance, ρ₀, ⟨e.symm⟩⟩

/-- Helper for Exercise 18-18.6-3: realizability is equivalent to having a finite-dimensional
source representation whose scalar extension is equivariantly isomorphic to the target. -/
theorem isRealizableOver_iff_exists_equiv_scalarExtension
    {k : Type v} [Field k]
    {k₀ : Type u₀} [Field k₀] [Algebra k₀ k]
    {G : Type w} [Group G]
    {V : Type u} [AddCommGroup V] [Module k V]
    {ρ : Representation k G V} :
    IsRealizableOver k₀ ρ ↔
      ∃ (W₀ : Type u) (_ : AddCommGroup W₀) (_ : Module k₀ W₀)
        (_ : FiniteDimensional k₀ W₀) (ρ₀ : Representation k₀ G W₀),
        Nonempty (ρ.Equiv (Representation.scalarExtension ρ₀)) := by
  constructor
  · -- The forward implication is the oriented unpacking lemma above.
    exact exists_equiv_scalarExtension_of_isRealizableOver
  · -- The reverse implication repackages the oriented equivalence into the definition.
    rintro ⟨W₀, _instAddCommGroupW₀, _instModuleW₀, _instFiniteDimensionalW₀, ρ₀, ⟨e⟩⟩
    exact isRealizableOver_of_equiv_scalarExtension ρ₀ e

/-- Helper for Exercise 18-18.6-3: realizability over a smaller field is preserved by
equivariant isomorphism. -/
theorem isRealizableOver_of_equiv
    {k : Type*} [Field k]
    {k₀ : Type*} [Field k₀] [Algebra k₀ k]
    {G : Type*} [Group G]
    {V : Type u} [AddCommGroup V] [Module k V]
    {W : Type u} [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W}
    (hσ : IsRealizableOver k₀ σ) (e : ρ.Equiv σ) :
    IsRealizableOver k₀ ρ := by
  -- Pull the chosen smaller-field model for `σ` back along the equivariant equivalence.
  rcases hσ with ⟨W₀, _, _, _, σ₀, ⟨e₀⟩⟩
  refine ⟨W₀, inferInstance, inferInstance, inferInstance, σ₀, ?_⟩
  exact ⟨e₀.trans e.symm⟩

/-- Helper for Exercise 18-18.6-3: precomposing an irreducible representation with a group
equivalence preserves irreducibility. -/
theorem isIrreducible_comp_of_mulEquiv_six_three
    {K : Type*} [Field K] {G H : Type*} [Group G] [Group H]
    {W : Type*} [AddCommGroup W] [Module K W]
    (e : G ≃* H) (σ : Representation K H W) [σ.IsIrreducible] :
    Representation.IsIrreducible (σ.comp e.toMonoidHom) := by
  classical
  letI : Nontrivial (Subrepresentation (σ.comp e.toMonoidHom)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation σ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h'
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro W hW
  let W' : Subrepresentation σ :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro h x hx
        -- Stability for `σ` follows by pulling the acting element back across the equivalence.
        simpa using W.apply_mem_toSubmodule (e.symm h) hx }
  have hW'_ne_bot : W' ≠ ⊥ := by
    intro hW'
    apply hW
    apply Subrepresentation.toSubmodule_injective
    simpa [W'] using congrArg Subrepresentation.toSubmodule hW'
  have hW'_top : W' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W').resolve_left hW'_ne_bot
  -- The transported stable subspace is top, so the original one is top as well.
  apply Subrepresentation.toSubmodule_injective
  simpa [W'] using congrArg Subrepresentation.toSubmodule hW'_top

/-- Helper for Exercise 18-18.6-3: realizability over a smaller field is preserved by
precomposition with a group equivalence. -/
theorem isRealizableOver_comp_of_mulEquiv
    {k : Type*} [Field k]
    {k₀ : Type*} [Field k₀] [Algebra k₀ k]
    {G H : Type*} [Group G] [Group H]
    {V : Type*} [AddCommGroup V] [Module k V]
    (e : G ≃* H) (σ : Representation k H V)
    (hσ : Representation.IsRealizableOver k₀ σ) :
    Representation.IsRealizableOver k₀ (σ.comp e.toMonoidHom) := by
  rcases hσ with ⟨W₀, _instAddCommGroupW₀, _instModuleW₀, _instFiniteDimensionalW₀,
    σ₀, ⟨eσ⟩⟩
  refine ⟨W₀, inferInstance, inferInstance, inferInstance, σ₀.comp e.toMonoidHom, ?_⟩
  refine ⟨Representation.Equiv.mk eσ.toLinearEquiv ?_⟩
  intro g
  -- Scalar extension commutes with this precomposition, so the old intertwiner applies at
  -- the image of `g`.
  simpa [Representation.scalarExtension] using eσ.isIntertwining' (e g)

/-- Helper for Exercise 18-18.6-3: precomposing by an equivalence and then by its inverse gives
an equivalent representation. -/
theorem nonempty_equiv_comp_symm_comp_mulEquiv
    {k : Type*} [Field k]
    {G H : Type*} [Group G] [Group H]
    {V : Type*} [AddCommGroup V] [Module k V]
    (e : G ≃* H) (ρ : Representation k G V) :
    Nonempty (ρ.Equiv ((ρ.comp e.symm.toMonoidHom).comp e.toMonoidHom)) := by
  refine ⟨Representation.Equiv.mk (LinearEquiv.refl k V) ?_⟩
  intro g
  -- The group equivalence cancels on the acting element, leaving the identity linear map as the
  -- intertwiner.
  ext x
  simp

/-- Helper for Exercise 18-18.6-3: every multiplicative character `A₅ → Lˣ` is trivial over any
field. -/
theorem alternatingGroup_fin5_units_hom_eq_one_over_any_field
    {L : Type*} [Field L] (χ : A5 →* Lˣ) :
    χ = 1 := by
  -- Route correction: the determinant argument later needs a field-independent trivial-character
  -- owner, so use that `A₅` is perfect rather than a finite-cardinality argument over one field.
  ext g
  have hcomm_top : commutator A5 = ⊤ := by
    simpa using
      (commutator_alternatingGroup_eq_top (α := Fin 5) (by decide :
        5 ≤ Fintype.card (Fin 5)))
  have hker_top : (⊤ : Subgroup A5) ≤ χ.ker := by
    -- Any homomorphism to the abelian group `Lˣ` kills the commutator subgroup.
    rw [← hcomm_top]
    exact Abelianization.commutator_subset_ker χ
  have hgker : g ∈ χ.ker := hker_top (by simp)
  simpa using hgker

end Representation
