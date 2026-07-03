import stacks_project.Chap15.Definition_15_28_1

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

private theorem koszulDifferential_comm (ψ : E →ₗ[R] E') (hψ : φ'.comp ψ = φ) (n : ℕ) :
    CommSq (ModuleCat.exteriorPower.map (ofHom ψ) (n + 1)) (koszulDifferential φ n)
      (koszulDifferential φ' n) (ModuleCat.exteriorPower.map (ofHom ψ) n) := sorry

namespace KoszulComplex

/-- Lemma 15.28.3: an `R`-linear map `ψ : E →ₗ[R] E'` satisfying `φ' ∘ ψ = φ` induces the
underlying chain map of the source-facing differential graded algebra morphism
`ExteriorAlgebra.map ψ`. -/
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
