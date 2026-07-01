import Mathlib

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
        DescendsExteriorPowerDifferential π δBA δΩ := sorry

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
