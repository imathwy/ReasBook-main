import Mathlib
import stacks_project.LinearAlgebra.PowerOperations
import stacks_project.Chap10.Definition_10_133_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain triage:
* primary domain: algebraic de Rham differentials on exterior powers of Kähler differentials;
* sampled canonical API: `KaehlerDifferential.D`, `LinearMap.compDer`, `exteriorPower.ιMulti`,
  and `exteriorPower.map`;
* source-facing owner layer: the canonical recursive family `deRhamDifferentialFamily A B` on
  `Ω[B⁄A]`, characterized by `IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B)`;
* primitive data: the graded term family `deRhamForm B M p`, written `Ω^[p]_[B](M)`, and the
  degreewise maps `δ`;
* derived bridge/view API: the induced degreewise map `exteriorPowerDeRhamMap` and the descent
  compatibility predicate `DescendsExteriorPowerDifferential`.
-/

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable {M : Type v} [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]

local instance exteriorPowerModule (n : ℕ) : Module A (⋀[B]^n M) :=
  Module.compHom _ (algebraMap A B)

local instance exteriorPowerIsScalarTower (n : ℕ) : IsScalarTower A B (⋀[B]^n M) := by
  let _ : Module A (⋀[B]^n M) := exteriorPowerModule n
  exact IsScalarTower.of_compHom A B _

/-- The degree-`p` term in the algebraic de Rham complex built from a `B`-module `M`: degree `0`
is `B`, degree `1` is `M`, and higher degrees are the exterior powers of `M`. -/
def deRhamForm
    (B : Type v) [CommRing B]
    (M : Type v) [AddCommGroup M] [Module B M] : ℕ → Type v
  | 0 => B
  | 1 => M
  | p + 2 => ⋀[B]^(p + 2) M

notation3:max "Ω^[" p "]_[" B "](" M ")" => deRhamForm B M p

notation3:max "Ω^[" p "][" B "⁄" A "]" => deRhamForm B Ω[B⁄A] p

namespace deRhamForm

instance addCommGroup (p : ℕ) : AddCommGroup (Ω^[p]_[B](M)) := by
  match p with
  | 0 =>
      simpa [deRhamForm] using (inferInstance : AddCommGroup B)
  | 1 =>
      simpa [deRhamForm] using (inferInstance : AddCommGroup M)
  | q + 2 =>
      simpa [deRhamForm] using
        (inferInstance : AddCommGroup (⋀[B]^(q + 2) M))

instance module (p : ℕ) : Module B (Ω^[p]_[B](M)) := by
  match p with
  | 0 =>
      simpa [deRhamForm] using (inferInstance : Module B B)
  | 1 =>
      simpa [deRhamForm] using (inferInstance : Module B M)
  | q + 2 =>
      simpa [deRhamForm] using
        (inferInstance : Module B (⋀[B]^(q + 2) M))

instance moduleCompHom (p : ℕ) : Module A (Ω^[p]_[B](M)) := by
  match p with
  | 0 =>
      simpa [deRhamForm] using (inferInstance : Module A B)
  | 1 =>
      simpa [deRhamForm] using (inferInstance : Module A M)
  | q + 2 =>
      simpa [deRhamForm] using
        (inferInstance : Module A (⋀[B]^(q + 2) M))

instance isScalarTower (p : ℕ) : IsScalarTower A B (Ω^[p]_[B](M)) := by
  match p with
  | 0 =>
      simpa [deRhamForm] using (inferInstance : IsScalarTower A B B)
  | 1 =>
      simpa [deRhamForm] using (inferInstance : IsScalarTower A B M)
  | q + 2 =>
      simpa [deRhamForm] using
        (inferInstance : IsScalarTower A B (⋀[B]^(q + 2) M))

end deRhamForm

/-- A recursive de Rham differential family on the graded terms built from a `B`-module `M`. -/
abbrev DeRhamFamily
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (M : Type v) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M] :=
  ∀ p : ℕ, Ω^[p]_[B](M) →ₗ[A] Ω^[p + 1]_[B](M)

variable {N : Type v} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]

/-- The degreewise map on de Rham forms induced by a `B`-linear map `π : M → N`. In degree `0`
this is the identity on `B`, in degree `1` it is `π`, and in higher degrees it is the induced map
on exterior powers. -/
noncomputable def exteriorPowerDeRhamMap
    (A : Type u) [CommRing A] [Algebra A B]
    [Module A M] [IsScalarTower A B M]
    [Module A N] [IsScalarTower A B N]
    (π : M →ₗ[B] N) :
    ∀ p : ℕ, Ω^[p]_[B](M) →ₗ[A] Ω^[p]_[B](N)
  | 0 => LinearMap.id
  | 1 => π.restrictScalars A
  | p + 2 => (exteriorPower.map (p + 2) π).restrictScalars A

/-- A de Rham differential on the graded exterior powers of a `B`-module extending the
`A`-derivation `D : B → M`. The source-facing owner is the single recursive family
`δ p : Ω^[p]_[B](M) → Ω^[p + 1]_[B](M)`. -/
structure IsExteriorPowerDeRhamDifferential
    (D : Derivation A B M)
    (δ : DeRhamFamily A B M) : Prop where
  /-- In degree `0`, the de Rham differential is the underlying `A`-linear map of the
  derivation `D`. -/
  degree_zero :
    δ 0 = D.toLinearMap
  /-- On degree-one basic forms, the differential is given by the usual de Rham rule
  `d(f₀ \, df₁) = df₀ ∧ df₁`. -/
  degree_one (f₀ f₁ : B) :
    δ 1 (f₀ • D f₁) =
      exteriorPower.ιMulti B 2 (Fin.cases (D f₀) fun _ ↦ D f₁)
  /-- On higher basic forms, the differential is given by the usual left-wedge rule
  `d(f₀ \, df₁ ∧ \cdots ∧ df_{p + 2}) = df₀ ∧ df₁ ∧ \cdots ∧ df_{p + 2}`. -/
  higher (p : ℕ) (f₀ : B) (fs : Fin (p + 2) → B) :
    δ (p + 2) (f₀ • exteriorPower.ιMulti B (p + 2) (fun i ↦ D (fs i))) =
      exteriorPower.ιMulti B (p + 3) (Fin.cases (D f₀) fun i ↦ D (fs i))
  /-- Consecutive de Rham differentials compose to zero. -/
  square_zero (p : ℕ) :
    (δ (p + 1)).comp (δ p) = 0

variable (A B)

/-- The canonical de Rham differential family on the exterior powers of `Ω[B⁄A]` exists and is
uniquely characterized by the usual de Rham formulas on basic forms together with `d ∘ d = 0`. -/
theorem existsUnique_deRhamDifferentialFamily :
    ∃! δ : DeRhamFamily A B Ω[B⁄A],
      IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δ := by
  sorry

/-- The canonical de Rham differential family on the graded forms `Ω^[p][B⁄A]`. -/
noncomputable def deRhamDifferentialFamily : DeRhamFamily A B Ω[B⁄A] :=
  Classical.choose (ExistsUnique.exists (existsUnique_deRhamDifferentialFamily A B))

/-- The canonical de Rham differential family satisfies the defining de Rham formulas and squares
to zero. -/
theorem isExteriorPowerDeRhamDifferential_deRhamDifferentialFamily :
    IsExteriorPowerDeRhamDifferential
      (KaehlerDifferential.D A B)
      (deRhamDifferentialFamily A B) := by
  exact Classical.choose_spec (ExistsUnique.exists (existsUnique_deRhamDifferentialFamily A B))

variable {A B}

/-- A de Rham differential family descends along `π : M → N` when every degreewise square
commutes with the induced map on forms. -/
def DescendsExteriorPowerDifferential
    (π : M →ₗ[B] N)
    (δM : DeRhamFamily A B M)
    (δN : DeRhamFamily A B N) : Prop :=
  ∀ p : ℕ,
    (δN p).comp (exteriorPowerDeRhamMap A π p) =
      (exteriorPowerDeRhamMap A π (p + 1)).comp (δM p)

variable {Ω : Type v} [AddCommGroup Ω] [Module B Ω] [Module A Ω] [IsScalarTower A B Ω]

/-- The kernel of a quotient map is generated by one-forms whose descended degree-two differential
vanishes, relative to a chosen de Rham differential family on `Ω[B⁄A]`. -/
def SatisfiesExteriorPowerDeRhamKernelCondition
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (δBA : DeRhamFamily A B Ω[B⁄A]) : Prop :=
  Submodule.span B
      {ω : Ω[B⁄A] |
        π ω = 0 ∧
          exteriorPowerDeRhamMap A π 2 (δBA 1 ω) = (0 : ⋀[B]^2 Ω)} =
    LinearMap.ker π

variable (A B)

/-- The canonical kernel condition for descending the de Rham differential through a quotient of
Kähler differentials. -/
def ExteriorPowerDeRhamKernelCondition
    (π : Ω[B⁄A] →ₗ[B] Ω) : Prop :=
  SatisfiesExteriorPowerDeRhamKernelCondition π (deRhamDifferentialFamily A B)

variable {A B}

/-- Helper for Lemma 10.132.2: when `π` is surjective, the induced map on degree-`p` de Rham
forms is also surjective. -/
theorem exteriorPowerDeRhamMap_surjective
    (π : M →ₗ[B] N)
    (hπ : Function.Surjective π)
    (p : ℕ) :
    Function.Surjective (exteriorPowerDeRhamMap A π p) := by
  cases p with
  | zero =>
      -- In degree `0`, the induced map is the identity on `B`.
      intro b
      exact ⟨b, rfl⟩
  | succ p =>
      cases p with
      | zero =>
          -- In degree `1`, the induced map is exactly `π`.
          simpa [exteriorPowerDeRhamMap] using hπ
      | succ p =>
          -- In higher degrees, surjectivity is inherited from exterior powers.
          simpa [exteriorPowerDeRhamMap] using
            (exteriorPower.map_surjective (n := p + 2) hπ)

/-- Helper for Lemma 10.132.2: wedging on the left by a fixed one-form gives a `B`-linear map on
the second factor. -/
noncomputable def degree_two_left_wedge_map
    (η : Ω) : Ω →ₗ[B] ⋀[B]^2 Ω :=
  (AlternatingMap.ofSubsingleton B Ω (⋀[B]^2 Ω) (0 : Fin 1)).symm
    ((exteriorPower.alternatingMapLinearEquiv.symm
      (LinearMap.id : ⋀[B]^2 Ω →ₗ[B] ⋀[B]^2 Ω)).curryLeft η)

/-- Helper for Lemma 10.132.2: the left-wedge map evaluates to the expected basic two-form. -/
@[simp] theorem degree_two_left_wedge_map_apply
    (η ξ : Ω) :
    degree_two_left_wedge_map (B := B) η ξ =
      exteriorPower.ιMulti B 2 (Fin.cases η fun _ ↦ ξ) := by
  -- Unfold the `1`-variable alternating-map equivalence and evaluate the wedge on the basic
  -- vector with entries `η` and `ξ`.
  change (LinearMap.id : ⋀[B]^2 Ω →ₗ[B] ⋀[B]^2 Ω)
      (exteriorPower.ιMulti B 2 (Fin.cons η fun _ ↦ ξ)) =
    exteriorPower.ιMulti B 2 (Fin.cons η fun _ ↦ ξ)
  rfl

/-- Helper for Lemma 10.132.2: on exact one-forms, the descended degree-one scalar commutator is
left wedging by `d b`. -/
theorem descended_degree_one_scalar_commutator_smul_D
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hdBA : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δBA)
    (b c x : B) :
    (((exteriorPowerDeRhamMap A π 2).comp (δBA 1)).scalarCommutator b)
        (c • KaehlerDifferential.D A B x) =
      c • degree_two_left_wedge_map (B := B)
        ((π.compDer (KaehlerDifferential.D A B)) b)
        ((π.compDer (KaehlerDifferential.D A B)) x) := by
  -- TODO: apply `hdBA.degree_one` to the two commutator terms after normalizing the first input to
  -- the exact-generator shape `(b * c) • d x`, push `∧² π` through `ιMulti`, and then cancel the
  -- `b • d c ∧ d x` term using the Leibniz rule for `π.compDer (KaehlerDifferential.D A B)`.
  sorry

/-- Helper for Lemma 10.132.2: after descending degree `1`, the scalar commutator with a scalar
is `B`-linear on all one-forms. -/
theorem descended_degree_one_scalar_commutator_commutes_smul
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hdBA : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δBA)
    (b c : B)
    (ω : Ω[B⁄A]) :
    (((exteriorPowerDeRhamMap A π 2).comp (δBA 1)).scalarCommutator b) (c • ω) =
      c • (((exteriorPowerDeRhamMap A π 2).comp (δBA 1)).scalarCommutator b) ω := by
  -- TODO: the source proof next upgrades the exact-generator computation to all one-forms by
  -- showing this commutator factors through `π` as a `B`-linear map. The remaining blocker is a
  -- clean canonical bridge from the generator formula to a `B`-linear map on `Ω[B⁄A]`.
  sorry

/-- Helper for Lemma 10.132.2: the descended degree-one scalar commutator is exactly wedging by
the descended exact form `d b` after applying `π`. -/
theorem descended_degree_one_scalar_commutator_eq_left_wedge
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hdBA : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δBA)
    (b : B)
    (ω : Ω[B⁄A]) :
    (((exteriorPowerDeRhamMap A π 2).comp (δBA 1)).scalarCommutator b) ω =
      degree_two_left_wedge_map (B := B)
        ((π.compDer (KaehlerDifferential.D A B)) b) (π ω) := by
  -- TODO: once the previous `B`-linearity step is formalized, compare the resulting `B`-linear
  -- commutator map with left wedge after `π` on exact forms and apply the Kähler universal
  -- property.
  sorry

/-- Helper for Lemma 10.132.2: applying the degree-one differential to a scalar multiple differs
from `b • dω` by wedging with the descended exact form `d b`. -/
theorem descended_degree_one_smul_formula
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hdBA : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δBA)
    (b : B)
    (ω : Ω[B⁄A]) :
    ((exteriorPowerDeRhamMap A π 2) (δBA 1 (b • ω)) : ⋀[B]^2 Ω) -
        (b • (((exteriorPowerDeRhamMap A π 2) (δBA 1 ω) : ⋀[B]^2 Ω)) : ⋀[B]^2 Ω) =
      degree_two_left_wedge_map (B := B)
        ((π.compDer (KaehlerDifferential.D A B)) b) (π ω) := by
  -- TODO: this becomes a one-line rewrite from
  -- `descended_degree_one_scalar_commutator_eq_left_wedge`.
  sorry

/-- Helper for Lemma 10.132.2: if each `δBA p` preserves the kernel of the induced degree-`p`
map, then the whole de Rham family descends degreewise through the quotient by `π`. -/
theorem exists_descended_exterior_power_differential_of_kernel_preservation
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hdBA : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δBA)
    (hpres :
      ∀ p : ℕ,
        LinearMap.ker (exteriorPowerDeRhamMap A π p) ≤
          Submodule.comap (δBA p) (LinearMap.ker (exteriorPowerDeRhamMap A π (p + 1)))) :
    ∃ δΩ : DeRhamFamily A B Ω,
      IsExteriorPowerDeRhamDifferential (π.compDer (KaehlerDifferential.D A B)) δΩ ∧
        DescendsExteriorPowerDifferential π δBA δΩ := by
  -- TODO: construct the descended family by quotienting each degree with `Submodule.mapQ`,
  -- transport along `LinearMap.quotKerEquivOfSurjective`, and verify the de Rham formulas from
  -- the commuting squares. The current blocker is only Lean bookkeeping for this quotient
  -- transport; the mathematical route is already fixed by `hpres`.
  sorry

/-- Helper for Lemma 10.132.2: in degree `0`, kernel preservation is automatic because the
induced degree-zero map is the identity. -/
theorem degree_zero_exterior_power_kernel_preserved
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (δBA : DeRhamFamily A B Ω[B⁄A]) :
    LinearMap.ker (exteriorPowerDeRhamMap A π 0) ≤
      Submodule.comap (δBA 0) (LinearMap.ker (exteriorPowerDeRhamMap A π 1)) := by
  intro b hb
  change exteriorPowerDeRhamMap A π 1 ((δBA 0) b) = 0
  have hb0 : b = 0 := by
    simpa [LinearMap.mem_ker, exteriorPowerDeRhamMap] using hb
  simp [hb0]

/-- Helper for Lemma 10.132.2: the kernel condition already gives the degree-one square in the
source proof, namely that `δBA 1` sends `ker π` into `ker (∧² π)`. -/
theorem degree_one_exterior_power_kernel_preserved
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hdBA : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δBA)
    (hker : SatisfiesExteriorPowerDeRhamKernelCondition π δBA) :
    LinearMap.ker (exteriorPowerDeRhamMap A π 1) ≤
      Submodule.comap (δBA 1) (LinearMap.ker (exteriorPowerDeRhamMap A π 2)) := by
  -- TODO: rewrite `hker` as the source span description of `ker π`, then run
  -- `Submodule.span_induction`. The generator case is already in `hker`; the scalar step is the
  -- first place where the missing descended degree-one Leibniz formula is needed.
  sorry

/-- Helper for Lemma 10.132.2: for a surjective quotient map, the higher kernel of `∧^(p + 2) π`
is exactly the range of the canonical left-tensor map with one factor in `ker π`. -/
theorem ker_exterior_power_map_eq_range_leftTensorMap
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (p : ℕ) :
    LinearMap.ker (exteriorPower.map (p + 2) π) =
      LinearMap.range (exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype) := by
  -- TODO: this is the source-faithful higher-kernel exactness statement. It should be obtained by
  -- applying the earlier exactness theorem for exterior powers to `pi.shortComplexKer`. At the
  -- moment the canonical owner file `Lemma_10_13_2` does not build when imported, so this exact
  -- formal bridge must wait on that earlier dependency being repaired instead of being reproved
  -- locally here.
  sorry

/-- Helper for Lemma 10.132.2: once the higher-degree kernel description is supplied, the source
proof gives kernel preservation in every degree. -/
theorem delta_preserves_exterior_power_kernels
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hdBA : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δBA)
    (hker : SatisfiesExteriorPowerDeRhamKernelCondition π δBA) :
    ∀ p : ℕ,
      LinearMap.ker (exteriorPowerDeRhamMap A π p) ≤
        Submodule.comap (δBA p) (LinearMap.ker (exteriorPowerDeRhamMap A π (p + 1))) := by
  intro p
  cases p with
  | zero =>
      simpa using degree_zero_exterior_power_kernel_preserved (A := A) (π := π) δBA
  | succ p =>
      cases p with
      | zero =>
          simpa [exteriorPowerDeRhamMap] using
            degree_one_exterior_power_kernel_preserved (A := A) π δBA hdBA hker
      | succ p =>
          -- TODO: complete the source-proof induction for `p + 2` by proving the kernel of
          -- `exteriorPowerDeRhamMap A π (p + 3)` is spanned by wedges with one factor in `ker π`,
          -- then apply the Leibniz rule from `hdBA.higher` to those generators.
          sorry

-- Proof sketch: descend the recursive differential family degree by degree through the quotient
-- map `π`, starting from the induced derivation in degree `0`, use the kernel hypothesis to
-- obtain the descended map in degree `1`, and then descend the higher pieces through the induced
-- exterior-power maps while preserving the defining de Rham rule and the square-zero relation.
/-- Lemma 10.132.2: if a surjective quotient `π : Ω[B⁄A] → Ω` has kernel generated by one-forms
whose descended degree-two differential vanishes, then the de Rham differential on
`Ω^\bullet_{B/A}` descends to a single recursive differential family on the exterior powers of
`Ω`. -/
theorem exists_descended_exterior_power_de_rham_differential_of_isExteriorPowerDeRhamDifferential
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hdBA : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δBA)
    (hker : SatisfiesExteriorPowerDeRhamKernelCondition π δBA) :
    ∃ δΩ : DeRhamFamily A B Ω,
      IsExteriorPowerDeRhamDifferential (π.compDer (KaehlerDifferential.D A B)) δΩ ∧
        DescendsExteriorPowerDifferential π δBA δΩ := by
  -- Route correction: the quotient-descent construction itself is explicit; the only missing
  -- ingredient is the higher-degree statement that `δBA p` preserves the kernels of `∧^p π`.
  exact
    exists_descended_exterior_power_differential_of_kernel_preservation
      (A := A)
      π
      hπ
      δBA
      hdBA
      (delta_preserves_exterior_power_kernels (A := A) π δBA hdBA hker)

/-- Lemma 10.132.2: if a surjective quotient `π : Ω[B⁄A] → Ω` has kernel generated by one-forms
whose descended degree-two differential vanishes, then the canonical de Rham differential on
`Ω^\bullet_{B/A}` descends to a single recursive differential family on the exterior powers of
`Ω`. -/
theorem exists_descended_exterior_power_de_rham_differential
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (hker : ExteriorPowerDeRhamKernelCondition A B π) :
    ∃ δΩ : DeRhamFamily A B Ω,
      IsExteriorPowerDeRhamDifferential (π.compDer (KaehlerDifferential.D A B)) δΩ ∧
        DescendsExteriorPowerDifferential π (deRhamDifferentialFamily A B) δΩ := by
  exact
    exists_descended_exterior_power_de_rham_differential_of_isExteriorPowerDeRhamDifferential
      π
      hπ
      (deRhamDifferentialFamily A B)
      (isExteriorPowerDeRhamDifferential_deRhamDifferentialFamily A B)
      hker

end
