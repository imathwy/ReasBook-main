import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology
open AlgEquiv Filter

universe u v w

section

variable {F : Type u} {E : Type v}
variable [Field F] [Field E] [Algebra F E] [Algebra.IsIntegral F E]
variable [TopologicalSpace E] [DiscreteTopology E]

instance : ContinuousSMul Gal(E / F) E :=
  (continuousSMul_iff_stabilizer_isOpen).2 stabilizer_isOpen_of_isIntegral

end

section

variable {F : Type u} {E : Type v} {X : Type w}
variable [Field F] [Field E] [Algebra F E]
variable [TopologicalSpace E] [DiscreteTopology E]
variable [TopologicalSpace X]

/-
Domain-style sampling:
* primary domain: Krull-topological Galois groups and continuity of their action on the ambient
  field;
* sampled owner declarations:
  `krullTopology_mem_nhds_one_iff`,
  `continuousSMul_iff_stabilizer_isOpen`,
  `stabilizer_isOpen_of_isIntegral`,
  `InfiniteGalois.profiniteGalGrp`;
* best owner abstractions: the action side is owned by `ContinuousSMul Gal(E / F) E`, while the
  profinite-group side is owned by `InfiniteGalois.profiniteGalGrp F E`;
* primitive data: the forward continuity criterion uses only the Krull-topology neighborhood basis
  through finite intermediate fields and the discrete topology on `E`, while the converse
  direction is primitive at the `ContinuousSMul` layer;
* derived API: `stabilizer_isOpen_of_isIntegral` gives the canonical open-stabilizer criterion used
  to build the needed `ContinuousSMul` proof in algebraic situations, and `profiniteGalGrp`
  packages the profinite structure.

Layer triage:
* `source-facing`: continuity of `g : X → Gal(E / F)` from continuity of the action map
  `X × E → E`;
* `core/canonical`: the owner class `ContinuousSMul Gal(E / F) E` and the bundled profinite group
  `InfiniteGalois.profiniteGalGrp F E`;
* `bridge/view`: the algebraicity bridge from `stabilizer_isOpen_of_isIntegral` to
  `ContinuousSMul`.
-/
/-- Helper for Lemma 9.22.1: if every evaluation map `x ↦ g x • y` is continuous, then
`g : X → Gal(E / F)` is continuous. This is the pointwise-evaluation bridge behind
Lemma 9.22.1 (1), and the source-facing action-map formulation follows by
`continuous_prod_of_discrete_right`. -/
theorem continuous_of_continuous_galois_eval
    (g : X → Gal(E/F))
    (hg_eval : ∀ y : E, Continuous fun x ↦ g x • y) :
    Continuous g := by
  -- Continuity into the Krull-topological Galois group is checked at each point.
  rw [continuous_iff_continuousAt]
  intro x₀
  let δ : X → Gal(E/F) := fun x ↦ (g x₀)⁻¹ * g x
  -- Translate continuity at `x₀` into convergence of the normalized cocycle `δ` to the identity.
  have hmul : Tendsto δ (𝓝 x₀) (𝓝 (1 : Gal(E/F))) := by
    rw [tendsto_def]
    intro U hU
    rcases (krullTopology_mem_nhds_one_iff F E U).1 hU with ⟨L, hLfin, hL⟩
    letI : FiniteDimensional F L := hLfin
    let b := Module.Basis.ofVectorSpace F L
    have hbasis : (⋂ i, {x : X | g x • (b i : E) = g x₀ • (b i : E)}) ∈ 𝓝 x₀ := by
      rw [iInter_mem]
      intro i
      let V : Set X := {x : X | g x • (b i : E) = g x₀ • (b i : E)}
      have hV : IsOpen V := by
        change IsOpen ((fun x : X ↦ g x • (b i : E)) ⁻¹' {g x₀ • (b i : E)})
        exact (isOpen_discrete _).preimage (hg_eval (b i : E))
      exact hV.mem_nhds rfl
    refine mem_of_superset hbasis ?_
    intro x hx
    -- Membership in the Krull neighborhood is reduced to fixing a finite intermediate field.
    apply hL
    change δ x ∈ L.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hfix : ∀ i, δ x (b i : E) = (b i : E) := by
      intro i
      have hi : g x • (b i : E) = g x₀ • (b i : E) := Set.mem_iInter.mp hx i
      calc
        δ x (b i : E) = (g x₀)⁻¹ • (g x • (b i : E)) := rfl
        _ = (g x₀)⁻¹ • (g x₀ • (b i : E)) := by rw [hi]
        _ = (b i : E) := by simp
    let incl : L →ₗ[F] E := (IsScalarTower.toAlgHom F L E).toLinearMap
    let φ : L →ₗ[F] E := (δ x).toLinearMap.comp incl
    have hlin : φ = incl := by
      apply b.ext
      intro i
      exact hfix i
    let yL : L := ⟨y, hy⟩
    have hy_fix : δ x y = y := by
      have h := congrArg (fun f : L →ₗ[F] E ↦ f yL) hlin
      simpa [φ, incl] using h
    exact hy_fix
  -- Undo the normalization by left multiplication with `g x₀`.
  simpa [ContinuousAt, mul_assoc, δ] using hmul.const_mul (g x₀)

/-- Lemma 9.22.1 (1): the source Galois statement is a specialization of this Krull-topological
result. The Krull topology on `Gal(E/F)` is the
coarsest topology for which the action on the discrete space `E` is continuous. Hence, for a
family `g : X → Gal(E/F)`, continuity of the action map `X × E → E` forces continuity of `g`. -/
@[stacks 0BMJ]
theorem continuous_of_continuous_galois_action
    (g : X → Gal(E/F))
    (hact : Continuous fun p : X × E ↦ g p.1 • p.2) :
    Continuous g := by
  -- On a discrete right factor, continuity of the action map is equivalent to pointwise continuity.
  exact continuous_of_continuous_galois_eval g <| continuous_prod_of_discrete_right.mp hact

end

section

variable {F : Type u} {E : Type v}
variable [Field F] [Field E] [Algebra F E]

variable [IsGalois F E]

/- Lemma 9.22.1 (2): for a Galois extension, the Krull-topological Galois group `Gal(E/F)` is the
canonical profinite group `InfiniteGalois.profiniteGalGrp F E`. -/
recall InfiniteGalois.profiniteGalGrp

end
