import Mathlib.Data.List.TFAE
import StacksProject_2024.stacks_project.Chap10.Lemma_10_101_1
import StacksProject_2024.stacks_project.Chap10.Theorem_10_85_4

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

local notation "𝔪" => maximalIdeal R
local notation "M̄" => M ⧸ (𝔪 • (⊤ : Submodule R M))
local notation "mkQ𝔪" => Submodule.mkQ (𝔪 • (⊤ : Submodule R M))

/- Domain triage:
- primary domain: modules over a local ring with nilpotent maximal ideal;
- sampled owner declarations:
  `basis_iff_basis_mod_maximalIdeal_of_flat_of_nilpotent_maximalIdeal`,
  `projective_module_free_of_isLocalRing`,
  `Module.Projective.of_free`,
  `Module.Flat.of_free`;
- owner abstraction: the canonical owner notions are the standard predicates
  `Module.Flat R M`, `Module.Free R M`, and `Module.Projective R M`;
- layer: `bridge/view`, since this file only packages existing owner-form implications into a
  `List.TFAE`;
- primitive data vs derived API: there is no extra primitive data here beyond the ambient module;
  the residue-field basis choice is an internal proof device for deriving freeness from flatness.
-/

-- Proof sketch: choose a basis of the residue-field vector space `M / maximalIdeal R • M`, lift
-- it across the quotient map, and apply Lemma `10.101.1` to obtain a basis of `M`. The remaining
-- equivalence between freeness and projectivity uses the canonical owner declarations
-- `Module.Projective.of_free` and Theorem `10.85.4`.
/-- Lemma 10.101.2: for a module over a local ring with nilpotent maximal ideal, flatness, freeness,
and projectivity are equivalent. -/
theorem flat_free_projective_tfae_of_nilpotent_maximalIdeal
    (h_nil : IsNilpotent 𝔪) :
    List.TFAE [Module.Flat R M, Module.Free R M, Module.Projective R M] := by
  tfae_have 1 ↔ 2 := by
    constructor
    · intro h_flat
      letI := h_flat
      classical
      letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
      let bbar := Module.Free.chooseBasis (R ⧸ 𝔪) M̄
      let x := fun a ↦ Classical.choose (Submodule.mkQ_surjective (𝔪 • (⊤ : Submodule R M)) (bbar a))
      obtain ⟨b, _⟩ :=
        (basis_iff_basis_mod_maximalIdeal_of_flat_of_nilpotent_maximalIdeal h_nil x).mp
          ⟨bbar, fun a ↦ (Classical.choose_spec
            (Submodule.mkQ_surjective (𝔪 • (⊤ : Submodule R M)) (bbar a))).symm⟩
      exact Module.Free.of_basis b
    · intro h_free
      letI := h_free
      infer_instance
  tfae_have 2 ↔ 3 := by
    constructor
    · intro h_free
      letI := h_free
      infer_instance
    · intro h_projective
      letI := h_projective
      exact projective_module_free_of_isLocalRing
  tfae_finish

end
