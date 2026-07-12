import StacksProject_2024.Chap15.Definition_15_28_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open CategoryTheory ModuleCat ExteriorAlgebra
open ModuleCat.exteriorPower

section

variable {R : Type u} {E : Type v} {E' : Type v}
variable [CommRing R] [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E']
variable {φ : E →ₗ[R] R} {φ' : E' →ₗ[R] R} {ψ : E →ₗ[R] E'}

/- Domain-style sampling:
- primary domain: Koszul differentials as derivations on exterior algebras, with chain-complex
  realization on the graded pieces;
- sampled owner declarations:
  `ExteriorAlgebra.map`,
  `CliffordAlgebra.contractLeft`,
  `koszulComplex`,
  `ModuleCat.exteriorPower.map`;
- best owner abstraction: the source-facing DGA map is the canonical algebra morphism
  `ExteriorAlgebra.map ψ`, and the induced chain map on `koszulComplex` is the derived bridge
  `KoszulComplex.map` on graded pieces;
- primitive data: a linear map `ψ : E →ₗ[R] E'` together with the compatibility
  `φ'.comp ψ = φ`;
- derived API: the differential-compatibility theorem for `ExteriorAlgebra.map ψ` and the
  induced chain map, with the degreewise commutative square kept as private bridge data;
- layer triage: the owner-level theorem on `ExteriorAlgebra.map ψ` is `source-facing`, while
  `KoszulComplex.map` is the derived `bridge/view` on the canonical chain complexes.
-/

namespace ExteriorAlgebra

/-- Lemma 15.28.3: the algebra map on exterior algebras induced by a compatible linear map
`ψ : E →ₗ[R] E'` commutes with the Koszul differential `CliffordAlgebra.contractLeft`. This is
the source-facing differential graded algebra morphism; `KoszulComplex.map` below is its
chain-map realization on the graded pieces. -/
@[stacks 0624]
theorem map_contractLeft (ψ : E →ₗ[R] E') (hψ : φ'.comp ψ = φ) :
    (CliffordAlgebra.contractLeft φ').comp (ExteriorAlgebra.map ψ).toLinearMap =
      (ExteriorAlgebra.map ψ).toLinearMap.comp (CliffordAlgebra.contractLeft φ) := by
  apply LinearMap.ext
  intro x
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp [LinearMap.comp_apply]
  | add x y hx hy =>
      simpa [LinearMap.comp_apply] using congrArg₂ (fun a b ↦ a + b) hx hy
  | ι_mul x e hx =>
      have hψe : φ' (ψ e) = φ e := by
        simpa using LinearMap.congr_fun hψ e
      simpa [LinearMap.comp_apply, CliffordAlgebra.contractLeft_ι_mul, hψe] using
        congrArg (fun z ↦ ι R (ψ e) * z) hx

end ExteriorAlgebra

/-- Helper for Lemma 15.28.3: after coercing to the ambient exterior algebra, the degreewise map
on exterior powers induced by `ψ` agrees with the ambient algebra map `ExteriorAlgebra.map ψ`. -/
private theorem exteriorPower_map_coe (ψ : E →ₗ[R] E') (n : ℕ) (x : ⋀[R]^n E) :
    ((exteriorPower.map n ψ x : ⋀[R]^n E') : ExteriorAlgebra R E') = ExteriorAlgebra.map ψ x := by
  -- Identify the degreewise exterior-power map with the ambient algebra map on generators.
  have hsubtype :
      (Submodule.subtype (⋀[R]^n E')).comp (exteriorPower.map n ψ) =
        (ExteriorAlgebra.map ψ).toLinearMap.comp (Submodule.subtype (⋀[R]^n E)) := by
    -- The universal property of exterior powers reduces the comparison to `ιMulti` generators.
    apply exteriorPower.linearMap_ext
    ext m
    simp [LinearMap.comp_apply]
  exact LinearMap.congr_fun hsubtype x

/-- Helper for Lemma 15.28.3: the Koszul differential commutes degreewise with the map induced by
`ψ` on exterior powers. -/
private theorem koszulDifferentialLinearMap_comm
    (ψ : E →ₗ[R] E') (hψ : φ'.comp ψ = φ) (n : ℕ) :
    (koszulDifferentialLinearMap φ' n).comp (exteriorPower.map (n + 1) ψ) =
      (exteriorPower.map n ψ).comp (koszulDifferentialLinearMap φ n) := by
  -- Compare both sides on `ιMulti` generators of `⋀^(n+1) E`.
  apply exteriorPower.linearMap_ext
  ext m
  -- The ambient exterior-algebra compatibility is exactly `ExteriorAlgebra.map_contractLeft`.
  have hcompat :=
    LinearMap.congr_fun (ExteriorAlgebra.map_contractLeft (φ := φ) (φ' := φ') ψ hψ)
      (ExteriorAlgebra.ιMulti R (n + 1) m)
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
    exteriorPower.map_apply_ιMulti, koszulDifferentialLinearMap, Function.comp_def] at hcompat ⊢
  rw [exteriorPower_map_coe (ψ := ψ) (n := n)]
  simpa [Matrix.vecTail, Function.comp_def] using hcompat

/-- Helper for Lemma 15.28.3: the degreewise exterior-power maps induced by `ψ` form a
commutative square with the Koszul differentials. -/
private theorem koszulDifferential_comm (ψ : E →ₗ[R] E') (hψ : φ'.comp ψ = φ) (n : ℕ) :
    CommSq (ModuleCat.exteriorPower.map (ofHom ψ) (n + 1)) (koszulDifferential φ n)
      (koszulDifferential φ' n) (ModuleCat.exteriorPower.map (ofHom ψ) n) := by
  -- Package the degreewise linear-map equality as the square used by `ChainComplex.ofHom`.
  refine CommSq.mk ?_
  simpa [koszulDifferential, ModuleCat.exteriorPower.map] using
    congrArg ModuleCat.ofHom (koszulDifferentialLinearMap_comm (φ := φ) (φ' := φ') ψ hψ n)

namespace KoszulComplex

/-- Lemma 15.28.3: an `R`-linear map `ψ : E →ₗ[R] E'` satisfying `φ' ∘ ψ = φ` induces the
underlying chain map of the source-facing differential graded algebra morphism
`ExteriorAlgebra.map ψ`. -/
@[stacks 0624]
noncomputable abbrev map (ψ : E →ₗ[R] E') (hψ : φ'.comp ψ = φ) :
    koszulComplex φ ⟶ koszulComplex φ' :=
  ChainComplex.ofHom
    ((ModuleCat.of R E).exteriorPower)
    (koszulDifferential φ)
    (fun n ↦ by
      simpa [koszulComplex, koszulDifferential, ChainComplex.of_d, Nat.add_assoc] using
        HomologicalComplex.d_comp_d (koszulComplex φ) ((n + 1) + 1) (n + 1) n)
    ((ModuleCat.of R E').exteriorPower)
    (koszulDifferential φ')
    (fun n ↦ by
      simpa [koszulComplex, koszulDifferential, ChainComplex.of_d, Nat.add_assoc] using
        HomologicalComplex.d_comp_d (koszulComplex φ') ((n + 1) + 1) (n + 1) n)
    (fun n ↦ ModuleCat.exteriorPower.map (ofHom ψ) n)
    (fun n ↦ by
      simpa using (koszulDifferential_comm ψ hψ n).w)

end KoszulComplex

end
