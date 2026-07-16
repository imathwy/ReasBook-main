import StacksProject_2024.stacks_project.Chap10.Definition_10_65_2
import StacksProject_2024.stacks_project.Chap31.Definition_31_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent]

/-- The affine-open section module `Γ(U, \mathcal F)` lies in the relative assassin over the
induced affine ring map `Γ(S, V) → Γ(X, U)`. -/
def relativeAssassinSections
    (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V) : Set (PrimeSpectrum (Γ(X, U))) :=
  let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let _ : Module Γ(S, V) Γ(ℱ, U) := Module.compHom (Γ(ℱ, U)) (f.appLE V U e).hom
  let _ : IsScalarTower Γ(S, V) Γ(X, U) Γ(ℱ, U) :=
    SMul.comp.isScalarTower (algebraMap Γ(S, V) Γ(X, U))
  _root_.relativeAssassin (Γ(S, V)) (Γ(X, U)) (Γ(ℱ, U))

/-- The affine-open relative-assassin bridge is the Chapter 10 relative-assassin predicate for the
section algebra `Γ(S, V) → Γ(X, U)` and section module `Γ(U, \mathcal F)`. -/
@[simp] theorem mem_relativeAssassinSections_iff
    (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V) (p : PrimeSpectrum (Γ(X, U))) :
    p ∈ relativeAssassinSections f ℱ U V e ↔
      p.asIdeal ∈
        associatedPrimesOfModule
          (Γ(X, U))
          (TensorProduct
            (Γ(S, V))
            (Γ(ℱ, U))
            ((p.asIdeal.under (Γ(S, V))).ResidueField)) := by
  let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let _ : Module Γ(S, V) Γ(ℱ, U) := Module.compHom (Γ(ℱ, U)) (f.appLE V U e).hom
  let _ : IsScalarTower Γ(S, V) Γ(X, U) Γ(ℱ, U) :=
    SMul.comp.isScalarTower (algebraMap Γ(S, V) Γ(X, U))
  simpa [relativeAssassinSections] using
    (_root_.mem_relativeAssassin_iff
      (R := Γ(S, V)) (S := Γ(X, U)) (N := Γ(ℱ, U)) p)

/-- Fiber-module form of `mem_relativeAssassinSections_iff`, specialized to the affine-open section
algebra `Γ(S, V) → Γ(X, U)`. -/
theorem mem_relativeAssassinSections_iff_fiber
    (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V) (p : PrimeSpectrum (Γ(X, U))) :
    p ∈ relativeAssassinSections f ℱ U V e ↔
      p.asIdeal ∈
        associatedPrimesOfModule
          (Γ(X, U))
          (TensorProduct
          (Γ(X, U))
          ((p.asIdeal.under (Γ(S, V))).Fiber (Γ(X, U)))
          (Γ(ℱ, U))) := by
  let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let _ : Module Γ(S, V) Γ(ℱ, U) := Module.compHom (Γ(ℱ, U)) (f.appLE V U e).hom
  let _ : IsScalarTower Γ(S, V) Γ(X, U) Γ(ℱ, U) :=
    SMul.comp.isScalarTower (algebraMap Γ(S, V) Γ(X, U))
  simpa [relativeAssassinSections] using
    (_root_.mem_relativeAssassin_iff_fiber
      (R := Γ(S, V)) (S := Γ(X, U)) (N := Γ(ℱ, U)) p)

-- Semantic recall: `lean_leansearch` surfaced the scheme-theoretic fiber owner
-- `Scheme.Hom.fiber` and the locally Noetherian owner `IsLocallyNoetherian`. Local Chapter 31
-- precedent fixes the scheme-side owner as `Scheme.Modules.relativeAssassin`, while the affine
-- section-module source clause `Ass_{A/R}(M)` is the Chapter 10 ring-level owner
-- `_root_.relativeAssassin` after instantiating the affine section algebra `Γ(S, V) → Γ(X, U)`.

/-- Lemma 31.7.2 (1): let `f : X ⟶ S` be a morphism of schemes, let `ℱ` be a quasi-coherent
`\mathcal O_X`-module, and let `U ⊆ X`, `V ⊆ S` be affine opens with `f(U) ⊆ V`. If the prime
`\mathfrak p` of `A = Γ(X, U)` corresponding to `x ∈ U` lies in the affine relative assassin
`Ass_{A/R}(M)` for `R = Γ(S, V)` and `M = Γ(U, \mathcal F)`, then the corresponding point of `U`
lies in the relative assassin `Ass_{X/S}(\mathcal F)`. -/
@[stacks 0CU5]
theorem fromSpec_mem_relativeAssassin_of_mem_relativeAssassin_sections
    {U : X.Opens} {V : S.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) (p : PrimeSpectrum (Γ(X, U)))
    (hp : p ∈ relativeAssassinSections f ℱ U V e) :
    hU.fromSpec p ∈ relativeAssassin f ℱ := sorry

/-- Pointwise affine form of Lemma 31.7.2 (1), using the associated-prime predicate on the
base-changed section module instead of relative-assassin set membership. -/
theorem fromSpec_mem_relativeAssassin_of_isAssociatedToModule_sections
    {U : X.Opens} {V : S.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) (p : PrimeSpectrum (Γ(X, U)))
    (hp : Ideal.IsAssociatedToModule
      (Γ(X, U))
      (TensorProduct
        (Γ(S, V))
        (Γ(ℱ, U))
        ((p.asIdeal.under (Γ(S, V))).ResidueField))
      p.asIdeal) :
    hU.fromSpec p ∈ relativeAssassin f ℱ := by
  have hp' :
      p.asIdeal ∈
        associatedPrimesOfModule
          (Γ(X, U))
          (TensorProduct
            (Γ(S, V))
            (Γ(ℱ, U))
            ((p.asIdeal.under (Γ(S, V))).ResidueField)) := by
    simpa [mem_associatedPrimesOfModule_iff] using hp
  exact fromSpec_mem_relativeAssassin_of_mem_relativeAssassin_sections
    f ℱ hU hV e p ((mem_relativeAssassinSections_iff f ℱ U V e p).2 hp')

/-- Lemma 31.7.2 (2): with the affine setup of Lemma `31.7.2 (1)`, if every scheme-theoretic
fiber `X_s` of `f` is locally Noetherian, then the affine relative assassin condition
`\mathfrak p ∈ Ass_{A/R}(M)` is equivalent to the corresponding point lying in the relative
assassin `Ass_{X/S}(\mathcal F)`. -/
@[stacks 0CU5]
theorem mem_relativeAssassin_sections_iff_fromSpec_mem_relativeAssassin_of_isLocallyNoetherian_fibers
    {U : X.Opens} {V : S.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) (hfib : ∀ s : S, IsLocallyNoetherian (Scheme.Hom.fiber f s))
    (p : PrimeSpectrum (Γ(X, U))) :
    p ∈ relativeAssassinSections f ℱ U V e ↔
      hU.fromSpec p ∈ relativeAssassin f ℱ := sorry

/-- Pointwise affine form of Lemma 31.7.2 (2), using the associated-prime predicate on the
base-changed section module instead of relative-assassin set membership. -/
theorem isAssociatedToModule_sections_iff_fromSpec_mem_relativeAssassin_of_isLocallyNoetherian_fibers
    {U : X.Opens} {V : S.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) (hfib : ∀ s : S, IsLocallyNoetherian (Scheme.Hom.fiber f s))
    (p : PrimeSpectrum (Γ(X, U))) :
    Ideal.IsAssociatedToModule
      (Γ(X, U))
      (TensorProduct
        (Γ(S, V))
        (Γ(ℱ, U))
        ((p.asIdeal.under (Γ(S, V))).ResidueField))
      p.asIdeal ↔
      hU.fromSpec p ∈ relativeAssassin f ℱ := by
  constructor
  · intro hp
    exact fromSpec_mem_relativeAssassin_of_isAssociatedToModule_sections f ℱ hU hV e p hp
  · intro hx
    have hmem :
        p ∈ relativeAssassinSections f ℱ U V e :=
      (mem_relativeAssassin_sections_iff_fromSpec_mem_relativeAssassin_of_isLocallyNoetherian_fibers
        f ℱ hU hV e hfib p).2 hx
    have hassoc :
        p.asIdeal ∈
          associatedPrimesOfModule
            (Γ(X, U))
            (TensorProduct
              (Γ(S, V))
              (Γ(ℱ, U))
              ((p.asIdeal.under (Γ(S, V))).ResidueField)) :=
      (mem_relativeAssassinSections_iff f ℱ U V e p).1 hmem
    simpa [mem_associatedPrimesOfModule_iff] using hassoc

end AlgebraicGeometry.Scheme.Modules
