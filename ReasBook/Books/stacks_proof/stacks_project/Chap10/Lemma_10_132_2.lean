import Mathlib
import stacks_proof.stacks_project.LinearAlgebra.PowerOperations
import stacks_proof.stacks_project.Chap10.Lemma_10_13_2
import stacks_proof.stacks_project.Chap10.Definition_10_133_1

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

/-- Helper for Chap10 Lemma 10 132 2: exterior powers of Kähler differentials are spanned by
wedges of exact one-forms. -/
theorem deRhamExactExteriorPower_span (n : ℕ) :
    Submodule.span B
      (exteriorPower.ιMulti B n ''
        {m : Fin n → Ω[B⁄A] | Set.range m ⊆ Set.range (KaehlerDifferential.D A B)}) =
      ⊤ := by
  -- The universal derivation spans one-forms, and exterior powers preserve that spanning set.
  exact
    exteriorPower.ιMulti_span_of_span
      (R := B) (n := n) (M := Ω[B⁄A])
      (by
        simpa using
          (KaehlerDifferential.span_range_derivation (R := A) (S := B)))

/-- Helper for Chap10 Lemma 10 132 2: two degree-one differentials satisfying the de Rham rule
agree pointwise on all one-forms. -/
theorem deRhamDifferentialFamily_degree_one_apply_eq
    {δ δ' : DeRhamFamily A B Ω[B⁄A]}
    (hδ : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δ)
    (hδ' : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δ')
    (ω : Ω[B⁄A]) :
    δ 1 ω = δ' 1 ω := by
  -- Keep the leading scalar explicit so B-span induction works for A-linear maps.
  let F : Ω[B⁄A] →ₗ[A] ⋀[B]^2 Ω[B⁄A] := δ 1
  let G : Ω[B⁄A] →ₗ[A] ⋀[B]^2 Ω[B⁄A] := δ' 1
  change F ω = G ω
  have hω :
      ω ∈ Submodule.span B (Set.range (KaehlerDifferential.D A B)) := by
    rw [KaehlerDifferential.span_range_derivation]
    exact Submodule.mem_top
  have hscaled :
      ∀ c : B, F (c • ω) = G (c • ω) := by
    induction hω using Submodule.span_induction with
    | mem y hy =>
        intro c
        rcases hy with ⟨x, rfl⟩
        simpa [F, G] using (hδ.degree_one c x).trans (hδ'.degree_one c x).symm
    | zero =>
        intro c
        calc
          F (c • 0) = F 0 := by
            exact congrArg F (smul_zero c)
          _ = G 0 := (map_zero F).trans (map_zero G).symm
          _ = G (c • 0) := by
            exact congrArg G (smul_zero c).symm
    | add y z _ _ hy hz =>
        intro c
        calc
          F (c • (y + z)) = F (c • y + c • z) := by
            exact congrArg F (smul_add c y z)
          _ = F (c • y) + F (c • z) := map_add F (c • y) (c • z)
          _ = G (c • y) + G (c • z) := by
            rw [hy c, hz c]
          _ = G (c • y + c • z) := (map_add G (c • y) (c • z)).symm
          _ = G (c • (y + z)) := by
            exact congrArg G (smul_add c y z).symm
    | smul d y _ hy =>
        intro c
        calc
          F (c • (d • y)) = F ((c * d) • y) := by
            exact congrArg F (smul_smul c d y)
          _ = G ((c * d) • y) := hy (c * d)
          _ = G (c • (d • y)) := by
            exact congrArg G (smul_smul c d y).symm
  simpa using hscaled 1

/-- Helper for Chap10 Lemma 10 132 2: two higher differentials satisfying the de Rham rule
agree pointwise on each exterior-power degree. -/
theorem deRhamDifferentialFamily_higher_apply_eq
    {δ δ' : DeRhamFamily A B Ω[B⁄A]}
    (hδ : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δ)
    (hδ' : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δ')
    (p : ℕ)
    (ω : ⋀[B]^(p + 2) Ω[B⁄A]) :
    δ (p + 2) ω = δ' (p + 2) ω := by
  -- Exact wedges span the source exterior power; again keep a leading scalar coefficient.
  let F : ⋀[B]^(p + 2) Ω[B⁄A] →ₗ[A] ⋀[B]^(p + 3) Ω[B⁄A] := δ (p + 2)
  let G : ⋀[B]^(p + 2) Ω[B⁄A] →ₗ[A] ⋀[B]^(p + 3) Ω[B⁄A] := δ' (p + 2)
  change F ω = G ω
  have hω :
      ω ∈ Submodule.span B
        (exteriorPower.ιMulti B (p + 2) ''
          {m : Fin (p + 2) → Ω[B⁄A] |
            Set.range m ⊆ Set.range (KaehlerDifferential.D A B)}) := by
    rw [deRhamExactExteriorPower_span (A := A) (B := B) (p + 2)]
    exact Submodule.mem_top
  have hscaled :
      ∀ c : B, F (c • ω) = G (c • ω) := by
    induction hω using Submodule.span_induction with
    | mem y hy =>
        intro c
        rcases hy with ⟨m, hm, rfl⟩
        let fs : Fin (p + 2) → B := fun i ↦ Classical.choose (hm ⟨i, rfl⟩)
        have hm_eq :
            m = fun i ↦ KaehlerDifferential.D A B (fs i) := by
          ext i
          exact (Classical.choose_spec (hm ⟨i, rfl⟩)).symm
        rw [hm_eq]
        simpa [F, G] using (hδ.higher p c fs).trans (hδ'.higher p c fs).symm
    | zero =>
        intro c
        calc
          F (c • 0) = F 0 := by
            exact congrArg F (smul_zero c)
          _ = G 0 := (map_zero F).trans (map_zero G).symm
          _ = G (c • 0) := by
            exact congrArg G (smul_zero c).symm
    | add y z _ _ hy hz =>
        intro c
        calc
          F (c • (y + z)) = F (c • y + c • z) := by
            exact congrArg F (smul_add c y z)
          _ = F (c • y) + F (c • z) := map_add F (c • y) (c • z)
          _ = G (c • y) + G (c • z) := by
            rw [hy c, hz c]
          _ = G (c • y + c • z) := (map_add G (c • y) (c • z)).symm
          _ = G (c • (y + z)) := by
            exact congrArg G (smul_add c y z).symm
    | smul d y _ hy =>
        intro c
        calc
          F (c • (d • y)) = F ((c * d) • y) := by
            exact congrArg F (smul_smul c d y)
          _ = G ((c * d) • y) := hy (c * d)
          _ = G (c • (d • y)) := by
            exact congrArg G (smul_smul c d y).symm
  exact (congrArg F (one_smul B ω)).symm.trans ((hscaled 1).trans (congrArg G (one_smul B ω)))

/-- Helper for Chap10 Lemma 10 132 2: the defining de Rham formulas determine the whole
recursive differential family uniquely. -/
theorem isExteriorPowerDeRhamDifferential_ext
    {δ δ' : DeRhamFamily A B Ω[B⁄A]}
    (hδ : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δ)
    (hδ' : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δ') :
    δ = δ' := by
  -- Check the three degree shapes separately: functions, one-forms, and higher exterior powers.
  funext p
  cases p with
  | zero =>
      exact hδ.degree_zero.trans hδ'.degree_zero.symm
  | succ p =>
      cases p with
      | zero =>
          ext ω
          exact deRhamDifferentialFamily_degree_one_apply_eq
            (A := A) (B := B) hδ hδ' ω
      | succ p =>
          ext ω
          exact deRhamDifferentialFamily_higher_apply_eq
            (A := A) (B := B) hδ hδ' p ω

/-- The canonical de Rham differential family on the exterior powers of `Ω[B⁄A]` exists and is
uniquely characterized by the usual de Rham formulas on basic forms together with `d ∘ d = 0`. -/
theorem existsUnique_deRhamDifferentialFamily :
    ∃! δ : DeRhamFamily A B Ω[B⁄A],
      IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δ := by
  -- The uniqueness half is generator-extensionality on exact one-forms and exact wedges; the
  -- remaining construction must build one family from the Kähler/exterior-power presentations.
  have hexists :
      ∃ δ : DeRhamFamily A B Ω[B⁄A],
        IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δ := by
    -- TODO: construct the canonical family from the Kähler/exterior-power presentations.
    -- A sufficient next step is a basic-form-compatible family, upgraded to square-zero by
    -- exact-wedge spanning.
    sorry
  rcases hexists with ⟨δ, hδ⟩
  refine ⟨δ, hδ, ?_⟩
  intro δ' hδ'
  exact isExteriorPowerDeRhamDifferential_ext (A := A) (B := B) hδ' hδ

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
      -- In degree zero the induced map is the identity on `B`.
      intro b
      exact ⟨b, rfl⟩
  | succ p =>
      cases p with
      | zero =>
          -- In degree one this is just the original surjection `π`.
          simpa [exteriorPowerDeRhamMap] using hπ
      | succ p =>
          -- Exterior powers preserve surjectivity in the higher degrees.
          simpa [exteriorPowerDeRhamMap] using
            (exteriorPower.map_surjective (n := p + 2) hπ)

/-- Helper for Chap10 Lemma 10 132 2: a linear map preserving kernels descends through two
surjective quotient presentations by using the canonical quotient-by-kernel equivalences. -/
noncomputable def descendedLinearMapOfSurjectiveKerLe
    {R V W V' W' : Type*} [Ring R]
    [AddCommGroup V] [AddCommGroup W] [AddCommGroup V'] [AddCommGroup W']
    [Module R V] [Module R W] [Module R V'] [Module R W']
    (q : V →ₗ[R] W) (q' : V' →ₗ[R] W') (f : V →ₗ[R] V')
    (hq : Function.Surjective q) (hq' : Function.Surjective q')
    (hker : LinearMap.ker q ≤ Submodule.comap f (LinearMap.ker q')) :
    W →ₗ[R] W' :=
  (q'.quotKerEquivOfSurjective hq').toLinearMap.comp
    ((Submodule.mapQ (LinearMap.ker q) (LinearMap.ker q') f hker).comp
      (q.quotKerEquivOfSurjective hq).symm.toLinearMap)

/-- Helper for Chap10 Lemma 10 132 2: the descended map is characterized by its commuting
square with the two quotient presentations. -/
theorem descendedLinearMapOfSurjectiveKerLe_comp
    {R V W V' W' : Type*} [Ring R]
    [AddCommGroup V] [AddCommGroup W] [AddCommGroup V'] [AddCommGroup W']
    [Module R V] [Module R W] [Module R V'] [Module R W']
    (q : V →ₗ[R] W) (q' : V' →ₗ[R] W') (f : V →ₗ[R] V')
    (hq : Function.Surjective q) (hq' : Function.Surjective q')
    (hker : LinearMap.ker q ≤ Submodule.comap f (LinearMap.ker q')) :
    (descendedLinearMapOfSurjectiveKerLe q q' f hq hq' hker).comp q = q'.comp f := by
  -- Evaluate the quotient construction on representatives.
  ext x
  have hsymm :
      (q.quotKerEquivOfSurjective hq).symm.toLinearMap (q x) =
        Submodule.Quotient.mk x :=
    LinearMap.quotKerEquivOfSurjective_symm_apply (f := q) hq x
  simpa [descendedLinearMapOfSurjectiveKerLe, LinearMap.comp_apply, hsymm,
    Submodule.mapQ_apply, LinearMap.quotKerEquivOfSurjective_apply_mk] using
    (rfl : ((descendedLinearMapOfSurjectiveKerLe q q' f hq hq' hker).comp q) x =
      (q'.comp f) x)

/-- Helper for Chap10 Lemma 10 132 2: the quotient-descended map sends the class of a
representative to the image of that representative. -/
theorem descendedLinearMapOfSurjectiveKerLe_apply
    {R V W V' W' : Type*} [Ring R]
    [AddCommGroup V] [AddCommGroup W] [AddCommGroup V'] [AddCommGroup W']
    [Module R V] [Module R W] [Module R V'] [Module R W']
    (q : V →ₗ[R] W) (q' : V' →ₗ[R] W') (f : V →ₗ[R] V')
    (hq : Function.Surjective q) (hq' : Function.Surjective q')
    (hker : LinearMap.ker q ≤ Submodule.comap f (LinearMap.ker q'))
    (x : V) :
    descendedLinearMapOfSurjectiveKerLe q q' f hq hq' hker (q x) = q' (f x) := by
  -- This is the pointwise form of the quotient-square characterization.
  simpa [LinearMap.comp_apply] using
    congrArg (fun g ↦ g x)
      (descendedLinearMapOfSurjectiveKerLe_comp q q' f hq hq' hker)

/-- Helper for Chap10 Lemma 10 132 2: membership in the degree-one kernel is exactly the
ordinary kernel condition for the map on one-forms. -/
theorem mem_ker_exteriorPowerDeRhamMap_one_iff
    (π : M →ₗ[B] N)
    (ω : M) :
    ω ∈ LinearMap.ker (exteriorPowerDeRhamMap A π 1) ↔ π ω = 0 := by
  -- In degree one, the induced de Rham-form map is `π` with scalars restricted to `A`.
  change (π.restrictScalars A) ω = 0 ↔ π ω = 0
  rfl

/-- Helper for Chap10 Lemma 10 132 2: in degree two, the de Rham-form map sends a basic wedge
to the wedge of the mapped one-forms. -/
theorem exteriorPowerDeRhamMap_two_apply_ιMulti
    (π : M →ₗ[B] N)
    (m : Fin 2 → M) :
    exteriorPowerDeRhamMap A π 2 (exteriorPower.ιMulti B 2 m) =
      exteriorPower.ιMulti B 2 (fun i ↦ π (m i)) := by
  -- Strip the scalar restriction, then apply the exterior-power computation rule.
  change (exteriorPower.map 2 π) (exteriorPower.ιMulti B 2 m) =
    exteriorPower.ιMulti B 2 (fun i ↦ π (m i))
  rw [exteriorPower.map_apply_ιMulti]
  rfl

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
  -- The singleton alternating-map equivalence evaluates the curried exterior generator.
  change (LinearMap.id : ⋀[B]^2 Ω →ₗ[B] ⋀[B]^2 Ω)
      (exteriorPower.ιMulti B 2 (Fin.cons η fun _ ↦ ξ)) =
    exteriorPower.ιMulti B 2 (Fin.cons η fun _ ↦ ξ)
  rfl

/-- Helper for Chap10 Lemma 10 132 2: multilinearity in the first exterior coordinate separates
the Leibniz summands and cancels the scalar multiple already present in a commutator. -/
private theorem iMulti_fin_cases_smul_add_smul_sub
    {M : Type*} [AddCommGroup M] [Module B M]
    (n : ℕ) (b c : B) (η ξ : M) (tail : Fin n → M) :
    exteriorPower.ιMulti B (n + 1) (Fin.cases (b • η + c • ξ) tail) -
        b • exteriorPower.ιMulti B (n + 1) (Fin.cases η tail) =
      c • exteriorPower.ιMulti B (n + 1) (Fin.cases ξ tail) := by
  -- Rephrase the first coordinate as a `Function.update` so multilinearity applies directly.
  let base : Fin (n + 1) → M := Fin.cases 0 tail
  have hsum :
      Fin.cases (b • η + c • ξ) tail =
        Function.update base 0 (b • η + c • ξ) := by
    ext i
    cases i using Fin.cases with
    | zero =>
        simp [base]
    | succ i =>
        simp [base]
  have hη :
      Fin.cases η tail = Function.update base 0 η := by
    ext i
    cases i using Fin.cases with
    | zero =>
        simp [base]
    | succ i =>
        simp [base]
  have hξ :
      Fin.cases ξ tail = Function.update base 0 ξ := by
    ext i
    cases i using Fin.cases with
    | zero =>
        simp [base]
    | succ i =>
        simp [base]
  rw [hsum, hη, hξ]
  rw [(exteriorPower.ιMulti B (n + 1)).map_update_add base 0 (b • η) (c • ξ),
    (exteriorPower.ιMulti B (n + 1)).map_update_smul base 0 b η,
    (exteriorPower.ιMulti B (n + 1)).map_update_smul base 0 c ξ]
  abel

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
  -- Expand the commutator and reduce both degree-one differentials to exact-generator formulas.
  have hsmul :
      b • (c • KaehlerDifferential.D A B x) =
        (b * c) • KaehlerDifferential.D A B x := by
    rw [smul_smul]
  have hbc := hdBA.degree_one (b * c) x
  have hc := hdBA.degree_one c x
  have hfinal :
      exteriorPowerDeRhamMap A π 2
            (exteriorPower.ιMulti B 2
              (Fin.cases ((KaehlerDifferential.D A B) (b * c))
                fun _ ↦ (KaehlerDifferential.D A B) x)) -
          b • exteriorPowerDeRhamMap A π 2
            (exteriorPower.ιMulti B 2
              (Fin.cases ((KaehlerDifferential.D A B) c)
                fun _ ↦ (KaehlerDifferential.D A B) x)) =
        c • degree_two_left_wedge_map (B := B)
          ((π.compDer (KaehlerDifferential.D A B)) b)
          ((π.compDer (KaehlerDifferential.D A B)) x) := by
    -- Push the exterior-power map through generators, then cancel the Leibniz `b • d c` term.
    rw [(KaehlerDifferential.D A B).leibniz b c]
    rw [exteriorPowerDeRhamMap_two_apply_ιMulti (A := A) (π := π),
      exteriorPowerDeRhamMap_two_apply_ιMulti (A := A) (π := π)]
    have hfirst :
        exteriorPower.ιMulti B 2
            (fun i ↦
              π (Fin.cases (b • (KaehlerDifferential.D A B) c +
                c • (KaehlerDifferential.D A B) b)
                  (fun _ ↦ (KaehlerDifferential.D A B) x) i)) =
          exteriorPower.ιMulti B 2
            (Fin.cases
              (b • π ((KaehlerDifferential.D A B) c) +
                c • π ((KaehlerDifferential.D A B) b))
              (fun _ ↦ π ((KaehlerDifferential.D A B) x))) := by
      congr 1
      ext i
      cases i using Fin.cases with
      | zero =>
          simp
      | succ i =>
          simp
    have hsecond :
        exteriorPower.ιMulti B 2
            (fun i ↦
              π (Fin.cases ((KaehlerDifferential.D A B) c)
                (fun _ ↦ (KaehlerDifferential.D A B) x) i)) =
          exteriorPower.ιMulti B 2
            (Fin.cases (π ((KaehlerDifferential.D A B) c))
              (fun _ ↦ π ((KaehlerDifferential.D A B) x))) := by
      congr 1
      ext i
      cases i using Fin.cases with
      | zero =>
          simp
      | succ i =>
          simp
    rw [hfirst, hsecond]
    simpa [Derivation.coe_comp, LinearMap.comp_apply, degree_two_left_wedge_map_apply] using
      iMulti_fin_cases_smul_add_smul_sub (B := B) 1 b c
      (π (KaehlerDifferential.D A B c)) (π (KaehlerDifferential.D A B b))
      (fun _ ↦ π (KaehlerDifferential.D A B x))
  calc
    (((exteriorPowerDeRhamMap A π 2).comp (δBA 1)).scalarCommutator b)
        (c • KaehlerDifferential.D A B x) =
      exteriorPowerDeRhamMap A π 2 (δBA 1 (b • (c • KaehlerDifferential.D A B x))) -
          b • exteriorPowerDeRhamMap A π 2 (δBA 1 (c • KaehlerDifferential.D A B x)) := by
        rw [LinearMap.scalarCommutator_apply]
        rfl
    _ =
      exteriorPowerDeRhamMap A π 2 (δBA 1 ((b * c) • KaehlerDifferential.D A B x)) -
          b • exteriorPowerDeRhamMap A π 2 (δBA 1 (c • KaehlerDifferential.D A B x)) := by
        rw [hsmul]
    _ =
      exteriorPowerDeRhamMap A π 2
            (exteriorPower.ιMulti B 2
              (Fin.cases ((KaehlerDifferential.D A B) (b * c))
                fun _ ↦ (KaehlerDifferential.D A B) x)) -
          b • exteriorPowerDeRhamMap A π 2
            (exteriorPower.ιMulti B 2
              (Fin.cases ((KaehlerDifferential.D A B) c)
                fun _ ↦ (KaehlerDifferential.D A B) x)) := by
        rw [hbc, hc]
    _ =
      c • degree_two_left_wedge_map (B := B)
        ((π.compDer (KaehlerDifferential.D A B)) b)
        ((π.compDer (KaehlerDifferential.D A B)) x) := hfinal

/-- Helper for Chap10 Lemma 10 132 2: on an exact one-form, the descended scalar commutator is
left wedge by the descended exact form `d b`. -/
theorem descended_degree_one_scalar_commutator_D
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hdBA : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δBA)
    (b x : B) :
    (((exteriorPowerDeRhamMap A π 2).comp (δBA 1)).scalarCommutator b)
        (KaehlerDifferential.D A B x) =
      degree_two_left_wedge_map (B := B)
        ((π.compDer (KaehlerDifferential.D A B)) b)
        ((π.compDer (KaehlerDifferential.D A B)) x) := by
  -- Specialize the scalar-generator calculation at coefficient `1`.
  have hone :=
    descended_degree_one_scalar_commutator_smul_D
      (A := A) (π := π) (δBA := δBA) hdBA b 1 x
  calc
    (((exteriorPowerDeRhamMap A π 2).comp (δBA 1)).scalarCommutator b)
        (KaehlerDifferential.D A B x) =
      (((exteriorPowerDeRhamMap A π 2).comp (δBA 1)).scalarCommutator b)
        (1 • KaehlerDifferential.D A B x) := by
        exact congrArg
          (((exteriorPowerDeRhamMap A π 2).comp (δBA 1)).scalarCommutator b)
          (one_smul B (KaehlerDifferential.D A B x)).symm
    _ =
      1 • degree_two_left_wedge_map (B := B)
        ((π.compDer (KaehlerDifferential.D A B)) b)
        ((π.compDer (KaehlerDifferential.D A B)) x) := hone
    _ =
      degree_two_left_wedge_map (B := B)
        ((π.compDer (KaehlerDifferential.D A B)) b)
        ((π.compDer (KaehlerDifferential.D A B)) x) := by
        exact one_smul B
          (degree_two_left_wedge_map (B := B)
            ((π.compDer (KaehlerDifferential.D A B)) b)
            ((π.compDer (KaehlerDifferential.D A B)) x))

/-- Helper for Chap10 Lemma 10 132 2: an `A`-linear map out of Kähler differentials that
commutes with `B`-scalars on exact one-forms commutes with `B`-scalars on every one-form. -/
private theorem kaehlerDifferential_linearMap_smul_of_smul_derivation
    {P : Type v} [AddCommGroup P] [Module A P] [Module B P]
    (F : Ω[B⁄A] →ₗ[A] P)
    (hF :
      ∀ c x : B,
        F (c • KaehlerDifferential.D A B x) =
          c • F (KaehlerDifferential.D A B x))
    (c : B)
    (ω : Ω[B⁄A]) :
    F (c • ω) = c • F ω := by
  -- Exact differentials span `Ω[B⁄A]`; carry scalar compatibility through span induction.
  have hω :
      ω ∈ Submodule.span B (Set.range (KaehlerDifferential.D A B)) := by
    rw [KaehlerDifferential.span_range_derivation]
    exact Submodule.mem_top
  revert c
  induction hω using Submodule.span_induction with
  | mem y hy =>
      rintro c
      rcases hy with ⟨x, rfl⟩
      exact hF c x
  | zero =>
      intro c
      simp
  | add y z _ _ hy hz =>
      intro c
      rw [smul_add, map_add, map_add, hy c, hz c, smul_add]
  | smul d y _ hy =>
      intro c
      calc
        F (c • (d • y)) = F ((c * d) • y) := by
          rw [smul_smul]
        _ = (c * d) • F y := hy (c * d)
        _ = c • (d • F y) := by
          rw [smul_smul]
        _ = c • F (d • y) := by
          rw [hy d]

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
  -- Reduce `B`-linearity of the commutator to exact one-form generators.
  refine kaehlerDifferential_linearMap_smul_of_smul_derivation
    (A := A)
    (((exteriorPowerDeRhamMap A π 2).comp (δBA 1)).scalarCommutator b)
    ?_ c ω
  intro d x
  have hd :=
    descended_degree_one_scalar_commutator_smul_D
      (A := A) (π := π) (δBA := δBA) hdBA b d x
  have hbase :
      (((exteriorPowerDeRhamMap A π 2).comp (δBA 1)).scalarCommutator b)
          (KaehlerDifferential.D A B x) =
        degree_two_left_wedge_map (B := B)
          ((π.compDer (KaehlerDifferential.D A B)) b)
          ((π.compDer (KaehlerDifferential.D A B)) x) :=
    descended_degree_one_scalar_commutator_D
      (A := A) (π := π) (δBA := δBA) hdBA b x
  -- Rewrite both sides through the generator computation and the exact-form base case.
  exact hd.trans (congrArg (fun y ↦ d • y) hbase.symm)

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
  -- Compare the two scalar-compatible maps on the exact differentials that span `Ω[B⁄A]`.
  let F : Ω[B⁄A] →ₗ[A] ⋀[B]^2 Ω :=
    (((exteriorPowerDeRhamMap A π 2).comp (δBA 1)).scalarCommutator b)
  let G : Ω[B⁄A] →ₗ[B] ⋀[B]^2 Ω :=
    (degree_two_left_wedge_map (B := B)
      ((π.compDer (KaehlerDifferential.D A B)) b)).comp π
  have hω :
      ω ∈ Submodule.span B (Set.range (KaehlerDifferential.D A B)) := by
    rw [KaehlerDifferential.span_range_derivation]
    exact Submodule.mem_top
  have hmain : F ω = G ω := by
    induction hω using Submodule.span_induction with
    | mem y hy =>
        rcases hy with ⟨x, rfl⟩
        simpa [F, G] using
          descended_degree_one_scalar_commutator_D
            (A := A) (π := π) (δBA := δBA) hdBA b x
    | zero =>
        rw [map_zero F, map_zero G]
    | add y z _ _ hy hz =>
        calc
          F (y + z) = F y + F z := map_add F y z
          _ = G y + G z := by
            rw [hy, hz]
          _ = G (y + z) := (map_add G y z).symm
    | smul c y _ hy =>
        calc
          F (c • y) = c • F y := by
            exact descended_degree_one_scalar_commutator_commutes_smul
              (A := A) (π := π) (δBA := δBA) hdBA b c y
          _ = c • G y := by
            rw [hy]
          _ = G (c • y) := by
            exact (map_smul G c y).symm
  simpa [F, G] using hmain

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
  -- The scalar commutator is precisely the difference between `d(b • ω)` and `b • dω`.
  simpa [LinearMap.scalarCommutator_apply] using
    descended_degree_one_scalar_commutator_eq_left_wedge
      (A := A) (π := π) (δBA := δBA) hdBA b ω

/-- Helper for Chap10 Lemma 10 132 2: the degreewise quotient descent of a source de Rham
family whose differentials preserve the induced exterior-power kernels. -/
noncomputable def descendedExteriorPowerDifferential
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hpres :
      ∀ p : ℕ,
        LinearMap.ker (exteriorPowerDeRhamMap A π p) ≤
          Submodule.comap (δBA p) (LinearMap.ker (exteriorPowerDeRhamMap A π (p + 1)))) :
    DeRhamFamily A B Ω :=
  fun p ↦
    descendedLinearMapOfSurjectiveKerLe
      (exteriorPowerDeRhamMap A π p)
      (exteriorPowerDeRhamMap A π (p + 1))
      (δBA p)
      (exteriorPowerDeRhamMap_surjective π hπ p)
      (exteriorPowerDeRhamMap_surjective π hπ (p + 1))
      (hpres p)

/-- Helper for Chap10 Lemma 10 132 2: the degreewise descended differential is characterized by
the commuting square with the source differential and the induced exterior-power quotient maps. -/
theorem descendedExteriorPowerDifferential_comp
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hpres :
      ∀ p : ℕ,
        LinearMap.ker (exteriorPowerDeRhamMap A π p) ≤
          Submodule.comap (δBA p) (LinearMap.ker (exteriorPowerDeRhamMap A π (p + 1))))
    (p : ℕ) :
    ((descendedExteriorPowerDifferential (A := A) π hπ δBA hpres) p).comp
        (exteriorPowerDeRhamMap A π p) =
      (exteriorPowerDeRhamMap A π (p + 1)).comp (δBA p) := by
  -- The quotient construction is characterized by the universal quotient-by-kernel square.
  exact descendedLinearMapOfSurjectiveKerLe_comp
    (exteriorPowerDeRhamMap A π p)
    (exteriorPowerDeRhamMap A π (p + 1))
    (δBA p)
    (exteriorPowerDeRhamMap_surjective π hπ p)
    (exteriorPowerDeRhamMap_surjective π hπ (p + 1))
    (hpres p)

/-- Helper for Chap10 Lemma 10 132 2: the descended differential has the expected degree-zero
formula. -/
theorem descendedExteriorPowerDifferential_degree_zero
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hdBA : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δBA)
    (hpres :
      ∀ p : ℕ,
        LinearMap.ker (exteriorPowerDeRhamMap A π p) ≤
          Submodule.comap (δBA p) (LinearMap.ker (exteriorPowerDeRhamMap A π (p + 1)))) :
    descendedExteriorPowerDifferential (A := A) π hπ δBA hpres 0 =
      (π.compDer (KaehlerDifferential.D A B)).toLinearMap := by
  -- Precompose the descended map with the identity degree-zero quotient map.
  ext b
  have hcomp :=
    congrArg (fun f => f b)
      (descendedExteriorPowerDifferential_comp
        (A := A) π hπ δBA hpres 0)
  simpa [exteriorPowerDeRhamMap, LinearMap.comp_apply, hdBA.degree_zero,
    Derivation.coe_comp] using hcomp

/-- Helper for Chap10 Lemma 10 132 2: the descended differential has the expected degree-one
formula on exact generators. -/
theorem descendedExteriorPowerDifferential_degree_one
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hdBA : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δBA)
    (hpres :
      ∀ p : ℕ,
        LinearMap.ker (exteriorPowerDeRhamMap A π p) ≤
          Submodule.comap (δBA p) (LinearMap.ker (exteriorPowerDeRhamMap A π (p + 1))))
    (f₀ f₁ : B) :
    descendedExteriorPowerDifferential (A := A) π hπ δBA hpres 1
        (f₀ • (π.compDer (KaehlerDifferential.D A B)) f₁) =
      exteriorPower.ιMulti B 2
        (Fin.cases ((π.compDer (KaehlerDifferential.D A B)) f₀)
          fun _ ↦ (π.compDer (KaehlerDifferential.D A B)) f₁) := by
  -- Lift a descended exact degree-one generator to the corresponding source generator.
  have hcomp :=
    congrArg (fun f => f (f₀ • KaehlerDifferential.D A B f₁))
      (descendedExteriorPowerDifferential_comp
        (A := A) π hπ δBA hpres 1)
  have hleft :
      exteriorPowerDeRhamMap A π 1 (f₀ • KaehlerDifferential.D A B f₁) =
        f₀ • π (KaehlerDifferential.D A B f₁) := by
    exact π.map_smul f₀ (KaehlerDifferential.D A B f₁)
  have hright :
      exteriorPowerDeRhamMap A π 2
          (exteriorPower.ιMulti B 2
            (Fin.cases (KaehlerDifferential.D A B f₀)
              fun _ ↦ KaehlerDifferential.D A B f₁)) =
        exteriorPower.ιMulti B 2
          (Fin.cases (π (KaehlerDifferential.D A B f₀))
            fun _ ↦ π (KaehlerDifferential.D A B f₁)) := by
    have hraw :
        (exteriorPower.map 2 π)
            (exteriorPower.ιMulti B 2
              (Fin.cases (KaehlerDifferential.D A B f₀)
                fun _ ↦ KaehlerDifferential.D A B f₁)) =
          exteriorPower.ιMulti B 2
            (fun i ↦
              π (Fin.cases (KaehlerDifferential.D A B f₀)
                (fun _ ↦ KaehlerDifferential.D A B f₁) i)) :=
      exteriorPower.map_apply_ιMulti (R := B) (n := 2) (f := π) _
    have hcoord :
        (fun i : Fin 2 ↦
            π (Fin.cases (KaehlerDifferential.D A B f₀)
              (fun _ ↦ KaehlerDifferential.D A B f₁) i)) =
          Fin.cases (π (KaehlerDifferential.D A B f₀))
            (fun _ ↦ π (KaehlerDifferential.D A B f₁)) := by
      ext i
      cases i using Fin.cases with
      | zero =>
          simp
      | succ i =>
          simp
    exact hraw.trans (congrArg (exteriorPower.ιMulti B 2) hcoord)
  simpa [Derivation.coe_comp] using
    calc
      descendedExteriorPowerDifferential (A := A) π hπ δBA hpres 1
          (f₀ • π (KaehlerDifferential.D A B f₁)) =
        descendedExteriorPowerDifferential (A := A) π hπ δBA hpres 1
          (exteriorPowerDeRhamMap A π 1
            (f₀ • KaehlerDifferential.D A B f₁)) := by
          rw [hleft]
      _ = exteriorPowerDeRhamMap A π 2
          (δBA 1 (f₀ • KaehlerDifferential.D A B f₁)) := by
          simpa [LinearMap.comp_apply] using hcomp
      _ = exteriorPowerDeRhamMap A π 2
          (exteriorPower.ιMulti B 2
            (Fin.cases (KaehlerDifferential.D A B f₀)
              fun _ ↦ KaehlerDifferential.D A B f₁)) := by
          rw [hdBA.degree_one]
      _ = exteriorPower.ιMulti B 2
          (Fin.cases (π (KaehlerDifferential.D A B f₀))
            fun _ ↦ π (KaehlerDifferential.D A B f₁)) := hright

/-- Helper for Chap10 Lemma 10 132 2: the induced higher de Rham-form map sends a scalar
multiple of an exact exterior generator to the corresponding scalar multiple after applying
`π` to each one-form. -/
theorem exteriorPowerDeRhamMap_smul_exact_iMulti
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (p : ℕ) (f₀ : B) (fs : Fin (p + 2) → B) :
    exteriorPowerDeRhamMap A π (p + 2)
        (f₀ • exteriorPower.ιMulti B (p + 2)
          (fun i ↦ KaehlerDifferential.D A B (fs i))) =
      f₀ • exteriorPower.ιMulti B (p + 2)
        (fun i ↦ π (KaehlerDifferential.D A B (fs i))) := by
  -- Combine scalar compatibility of the exterior-power map with its generator formula.
  have hraw :=
    (exteriorPower.map (p + 2) π).map_smul f₀
      (exteriorPower.ιMulti B (p + 2)
        (fun i ↦ KaehlerDifferential.D A B (fs i)))
  have hmap :
      (exteriorPower.map (p + 2) π)
          (exteriorPower.ιMulti B (p + 2)
            (fun i ↦ KaehlerDifferential.D A B (fs i))) =
        exteriorPower.ιMulti B (p + 2)
          (fun i ↦ π (KaehlerDifferential.D A B (fs i))) :=
    exteriorPower.map_apply_ιMulti (R := B) (n := p + 2) (f := π) _
  exact hraw.trans (congrArg (fun y ↦ f₀ • y) hmap)

/-- Helper for Chap10 Lemma 10 132 2: the induced higher de Rham-form map sends a left-extended
exact exterior generator to the corresponding generator after applying `π` coordinatewise. -/
theorem exteriorPowerDeRhamMap_iMulti_fin_cases_exact
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (p : ℕ) (f₀ : B) (fs : Fin (p + 2) → B) :
    exteriorPowerDeRhamMap A π (p + 3)
        (exteriorPower.ιMulti B (p + 3)
          (Fin.cases (KaehlerDifferential.D A B f₀)
            fun i ↦ KaehlerDifferential.D A B (fs i))) =
      exteriorPower.ιMulti B (p + 3)
        (Fin.cases (π (KaehlerDifferential.D A B f₀))
          fun i ↦ π (KaehlerDifferential.D A B (fs i))) := by
  -- Apply the exterior-power generator formula and identify the coordinate functions.
  have hraw :
      (exteriorPower.map (p + 3) π)
          (exteriorPower.ιMulti B (p + 3)
            (Fin.cases (KaehlerDifferential.D A B f₀)
              fun i ↦ KaehlerDifferential.D A B (fs i))) =
        exteriorPower.ιMulti B (p + 3)
          (fun i ↦
            π (Fin.cases (KaehlerDifferential.D A B f₀)
              (fun i ↦ KaehlerDifferential.D A B (fs i)) i)) :=
    exteriorPower.map_apply_ιMulti (R := B) (n := p + 3) (f := π) _
  have hcoord :
      (fun i : Fin (p + 3) ↦
          π (Fin.cases (KaehlerDifferential.D A B f₀)
            (fun i ↦ KaehlerDifferential.D A B (fs i)) i)) =
        Fin.cases (π (KaehlerDifferential.D A B f₀))
          (fun i ↦ π (KaehlerDifferential.D A B (fs i))) := by
    ext i
    cases i using Fin.cases with
    | zero =>
        simp
    | succ i =>
        simp
  exact hraw.trans (congrArg (exteriorPower.ιMulti B (p + 3)) hcoord)

/-- Helper for Chap10 Lemma 10 132 2: the higher descended differential on a lifted exact
generator is transported through the quotient square to the source differential. -/
theorem descendedExteriorPowerDifferential_higher_transport
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hpres :
      ∀ p : ℕ,
        LinearMap.ker (exteriorPowerDeRhamMap A π p) ≤
          Submodule.comap (δBA p) (LinearMap.ker (exteriorPowerDeRhamMap A π (p + 1))))
    (p : ℕ) (f₀ : B) (fs : Fin (p + 2) → B) :
    descendedExteriorPowerDifferential (A := A) π hπ δBA hpres (p + 2)
        (f₀ • exteriorPower.ιMulti B (p + 2)
          (fun i ↦ π (KaehlerDifferential.D A B (fs i)))) =
      exteriorPowerDeRhamMap A π (p + 3)
        (δBA (p + 2)
          (f₀ • exteriorPower.ιMulti B (p + 2)
            (fun i ↦ KaehlerDifferential.D A B (fs i)))) := by
  -- Rewrite the descended generator as the image of its source lift.
  rw [← exteriorPowerDeRhamMap_smul_exact_iMulti (A := A) (π := π) p f₀ fs]
  -- The quotient construction is characterized by the commuting square.
  exact
    descendedLinearMapOfSurjectiveKerLe_apply
      (exteriorPowerDeRhamMap A π (p + 2))
      (exteriorPowerDeRhamMap A π (p + 3))
      (δBA (p + 2))
      (exteriorPowerDeRhamMap_surjective π hπ (p + 2))
      (exteriorPowerDeRhamMap_surjective π hπ (p + 3))
      (hpres (p + 2))
      (f₀ • exteriorPower.ιMulti B (p + 2)
        (fun i ↦ KaehlerDifferential.D A B (fs i)))

/-- Helper for Chap10 Lemma 10 132 2: after applying the source higher de Rham formula, the
exterior-power map carries the exact source generator to the descended exact generator. -/
theorem exteriorPowerDeRhamMap_delta_higher_exact
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hdBA : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δBA)
    (p : ℕ) (f₀ : B) (fs : Fin (p + 2) → B) :
    exteriorPowerDeRhamMap A π (p + 3)
        (δBA (p + 2)
          (f₀ • exteriorPower.ιMulti B (p + 2)
            (fun i ↦ KaehlerDifferential.D A B (fs i)))) =
      exteriorPower.ιMulti B (p + 3)
        (Fin.cases (π (KaehlerDifferential.D A B f₀))
          fun i ↦ π (KaehlerDifferential.D A B (fs i))) := by
  -- Use the defining higher formula in the source, then map each exterior coordinate by `π`.
  rw [hdBA.higher]
  exact exteriorPowerDeRhamMap_iMulti_fin_cases_exact (A := A) (π := π) p f₀ fs

/-- Helper for Chap10 Lemma 10 132 2: the descended differential has the expected higher-degree
formula on exact exterior generators. -/
theorem descendedExteriorPowerDifferential_higher
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hdBA : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δBA)
    (hpres :
      ∀ p : ℕ,
        LinearMap.ker (exteriorPowerDeRhamMap A π p) ≤
          Submodule.comap (δBA p) (LinearMap.ker (exteriorPowerDeRhamMap A π (p + 1))))
    (p : ℕ) (f₀ : B) (fs : Fin (p + 2) → B) :
    descendedExteriorPowerDifferential (A := A) π hπ δBA hpres (p + 2)
        (f₀ • exteriorPower.ιMulti B (p + 2)
          (fun i ↦ π (KaehlerDifferential.D A B (fs i)))) =
      exteriorPower.ιMulti B (p + 3)
        (Fin.cases (π (KaehlerDifferential.D A B f₀))
          fun i ↦ π (KaehlerDifferential.D A B (fs i))) := by
  -- Compose the cached quotient-square transport with the source-side computation.
  exact
    (descendedExteriorPowerDifferential_higher_transport
      (A := A) π hπ δBA hpres p f₀ fs).trans
      (exteriorPowerDeRhamMap_delta_higher_exact
        (A := A) (π := π) δBA hdBA p f₀ fs)

/-- Helper for Chap10 Lemma 10 132 2: consecutive descended differentials compose to zero. -/
theorem descendedExteriorPowerDifferential_square_zero
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hdBA : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δBA)
    (hpres :
      ∀ p : ℕ,
        LinearMap.ker (exteriorPowerDeRhamMap A π p) ≤
          Submodule.comap (δBA p) (LinearMap.ker (exteriorPowerDeRhamMap A π (p + 1))))
    (p : ℕ) :
    (descendedExteriorPowerDifferential (A := A) π hπ δBA hpres (p + 1)).comp
        (descendedExteriorPowerDifferential (A := A) π hπ δBA hpres p) =
      0 := by
  -- Lift to the source family, use its square-zero relation, and map back down.
  ext y
  obtain ⟨x, rfl⟩ := exteriorPowerDeRhamMap_surjective (A := A) π hπ p y
  have hcomp_p :
      (descendedExteriorPowerDifferential (A := A) π hπ δBA hpres p)
          (exteriorPowerDeRhamMap A π p x) =
        exteriorPowerDeRhamMap A π (p + 1) (δBA p x) := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun f => f x)
        (descendedExteriorPowerDifferential_comp
          (A := A) π hπ δBA hpres p)
  have hcomp_succ :
      (descendedExteriorPowerDifferential (A := A) π hπ δBA hpres (p + 1))
          (exteriorPowerDeRhamMap A π (p + 1) (δBA p x)) =
        exteriorPowerDeRhamMap A π (p + 2) (δBA (p + 1) (δBA p x)) := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun f => f (δBA p x))
        (descendedExteriorPowerDifferential_comp
          (A := A) π hπ δBA hpres (p + 1))
  have hsquare : δBA (p + 1) (δBA p x) = 0 := by
    simpa [LinearMap.comp_apply] using congrArg (fun f => f x) (hdBA.square_zero p)
  calc
    (descendedExteriorPowerDifferential (A := A) π hπ δBA hpres (p + 1))
        ((descendedExteriorPowerDifferential (A := A) π hπ δBA hpres p)
          (exteriorPowerDeRhamMap A π p x)) =
      (descendedExteriorPowerDifferential (A := A) π hπ δBA hpres (p + 1))
        (exteriorPowerDeRhamMap A π (p + 1) (δBA p x)) := by
        rw [hcomp_p]
    _ = exteriorPowerDeRhamMap A π (p + 2) (δBA (p + 1) (δBA p x)) := by
        rw [hcomp_succ]
    _ = 0 := by
        simpa [LinearMap.comp_apply] using congrArg (exteriorPowerDeRhamMap A π (p + 2)) hsquare

/-- Helper for Chap10 Lemma 10 132 2: the degreewise descended family inherits the de Rham
formulas and square-zero relation from the source family. -/
theorem descendedExteriorPowerDifferential_isExteriorPower
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hdBA : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δBA)
    (hpres :
      ∀ p : ℕ,
        LinearMap.ker (exteriorPowerDeRhamMap A π p) ≤
          Submodule.comap (δBA p) (LinearMap.ker (exteriorPowerDeRhamMap A π (p + 1)))) :
    IsExteriorPowerDeRhamDifferential
      (π.compDer (KaehlerDifferential.D A B))
      (descendedExteriorPowerDifferential (A := A) π hπ δBA hpres) := by
  constructor
  · exact descendedExteriorPowerDifferential_degree_zero (A := A) π hπ δBA hdBA hpres
  · exact descendedExteriorPowerDifferential_degree_one (A := A) π hπ δBA hdBA hpres
  · intro p f₀ fs
    simpa [Derivation.coe_comp] using
      descendedExteriorPowerDifferential_higher (A := A) π hπ δBA hdBA hpres p f₀ fs
  · exact descendedExteriorPowerDifferential_square_zero (A := A) π hπ δBA hdBA hpres

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
  -- Assemble the descended family from the degreewise quotient construction and its
  -- characterization square.
  refine ⟨descendedExteriorPowerDifferential (A := A) π hπ δBA hpres, ?_, ?_⟩
  · exact descendedExteriorPowerDifferential_isExteriorPower
      (A := A) π hπ δBA hdBA hpres
  · exact descendedExteriorPowerDifferential_comp
      (A := A) π hπ δBA hpres

/-- Helper for Lemma 10.132.2: in degree `0`, kernel preservation is automatic because the
induced degree-zero map is the identity. -/
theorem degree_zero_exterior_power_kernel_preserved
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (δBA : DeRhamFamily A B Ω[B⁄A]) :
    LinearMap.ker (exteriorPowerDeRhamMap A π 0) ≤
      Submodule.comap (δBA 0) (LinearMap.ker (exteriorPowerDeRhamMap A π 1)) := by
  intro b hb
  -- In degree zero the quotient map is the identity, so its kernel contains only zero.
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
  intro ω hω
  -- Rewrite the degree-one kernel as the ordinary kernel of `π`, then use the stated kernel
  -- generation condition.
  have hπω : π ω = 0 :=
    (mem_ker_exteriorPowerDeRhamMap_one_iff (A := A) π ω).mp hω
  have hspan :
      ω ∈ Submodule.span B
        {η : Ω[B⁄A] |
          π η = 0 ∧
            exteriorPowerDeRhamMap A π 2 (δBA 1 η) = (0 : ⋀[B]^2 Ω)} := by
    rw [hker]
    simpa [LinearMap.mem_ker] using hπω
  -- The generator property is stable under addition and scalar multiplication; the scalar case
  -- uses the cached degree-one Leibniz commutator formula.
  have hclosed :
      π ω = 0 ∧
        exteriorPowerDeRhamMap A π 2 (δBA 1 ω) = (0 : ⋀[B]^2 Ω) := by
    refine Submodule.span_induction (p := fun η _ ↦
      π η = 0 ∧
        exteriorPowerDeRhamMap A π 2 (δBA 1 η) = (0 : ⋀[B]^2 Ω))
      ?mem ?zero ?add ?smul hspan
    · intro η hη
      exact hη
    · constructor
      · exact map_zero π
      · exact map_zero ((exteriorPowerDeRhamMap A π 2).comp (δBA 1))
    · intro η ξ _ _ hη hξ
      constructor
      · simp [map_add, hη.1, hξ.1]
      · have hmap :
            exteriorPowerDeRhamMap A π 2 (δBA 1 (η + ξ)) =
              exteriorPowerDeRhamMap A π 2 (δBA 1 η) +
                exteriorPowerDeRhamMap A π 2 (δBA 1 ξ) := by
          exact map_add ((exteriorPowerDeRhamMap A π 2).comp (δBA 1)) η ξ
        rw [hmap, hη.2, hξ.2]
        exact add_zero (0 : ⋀[B]^2 Ω)
    · intro b η _ hη
      constructor
      · simp [hη.1]
      · have hformula :=
          descended_degree_one_smul_formula
            (A := A) (π := π) (δBA := δBA) hdBA b η
        have hleft :
            degree_two_left_wedge_map (B := B)
                ((π.compDer (KaehlerDifferential.D A B)) b) (π η) = 0 := by
          simpa [hη.1] using
            map_zero (degree_two_left_wedge_map (B := B)
              ((π.compDer (KaehlerDifferential.D A B)) b))
        have hmain :
            exteriorPowerDeRhamMap A π 2 (δBA 1 (b • η)) -
                b • exteriorPowerDeRhamMap A π 2 (δBA 1 η) = 0 := by
          rw [hformula, hleft]
          rfl
        have hsmul :
            b • exteriorPowerDeRhamMap A π 2 (δBA 1 η) = 0 := by
          rw [hη.2]
          change b • (0 : ⋀[B]^2 Ω) = 0
          exact smul_zero b
        have htarget := sub_eq_zero.mp hmain
        simpa [hsmul] using htarget
  simpa [Submodule.mem_comap, LinearMap.mem_ker] using hclosed.2

/-- Helper for Lemma 10.132.2: for a surjective quotient map, the higher kernel of `∧^(p + 2) π`
is exactly the range of the canonical left-tensor map with one factor in `ker π`. -/
theorem ker_exterior_power_map_eq_range_leftTensorMap
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (p : ℕ) :
    LinearMap.ker (exteriorPower.map (p + 2) π) =
      LinearMap.range (exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype) := by
  -- Use the exterior-power exactness theorem on the short exact sequence
  -- `ker π ⟶ Ω[B⁄A] ⟶ Ω`.
  have hexact :
      Function.Exact
        (exteriorPower.leftTensorMap (p + 1)
          (LinearMap.shortComplexKer π).f.hom)
        (exteriorPower.map (p + 2) (LinearMap.shortComplexKer π).g.hom) :=
    (exterior_power_exact_of_exact
      (S := LinearMap.shortComplexKer π)
      (LinearMap.shortExact_shortComplexKer hπ)
      (p + 1)).1
  simpa [LinearMap.shortComplexKer] using (LinearMap.exact_iff.mp hexact)

/-- Helper for Chap10 Lemma 10 132 2: the higher `A`-linear de Rham-form kernel is the
restriction of the corresponding `B`-linear exterior-power kernel. -/
theorem ker_exteriorPowerDeRhamMap_higher_eq_restrictScalars
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (p : ℕ) :
    LinearMap.ker (exteriorPowerDeRhamMap A π (p + 2)) =
      (LinearMap.ker (exteriorPower.map (p + 2) π)).restrictScalars A := by
  -- In degrees at least two, `exteriorPowerDeRhamMap` is just the exterior-power map with
  -- scalars restricted from `B` to `A`.
  ext x
  rfl

/-- Helper for Chap10 Lemma 10 132 2: the higher kernel of the de Rham-form quotient map is the
`A`-restricted range of the left-tensor map with one factor in `ker π`. -/
theorem ker_exteriorPowerDeRhamMap_higher_eq_restrictScalars_range_leftTensorMap
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (p : ℕ) :
    LinearMap.ker (exteriorPowerDeRhamMap A π (p + 2)) =
      (LinearMap.range
        (exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype)).restrictScalars A := by
  -- First move from the `A`-linear presentation to the `B`-linear exterior-power map, then use
  -- the exactness normal form already proved over `B`.
  calc
    LinearMap.ker (exteriorPowerDeRhamMap A π (p + 2)) =
        (LinearMap.ker (exteriorPower.map (p + 2) π)).restrictScalars A := by
          exact ker_exteriorPowerDeRhamMap_higher_eq_restrictScalars (A := A) π p
    _ =
        (LinearMap.range
          (exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype)).restrictScalars A := by
          exact congrArg (Submodule.restrictScalars A)
            (ker_exterior_power_map_eq_range_leftTensorMap (A := A) π hπ p)

/-- Helper for Chap10 Lemma 10 132 2: on basic higher-degree exact wedges, the scalar
commutator of any de Rham differential family satisfying the defining formulas retains only the
new leftmost exact factor. -/
theorem higher_scalar_commutator_smul_iMulti
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hdBA : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δBA)
    (q : ℕ) (b c : B) (fs : Fin (q + 2) → B) :
    (δBA (q + 2)).scalarCommutator b
        (c • exteriorPower.ιMulti B (q + 2)
          (fun i ↦ KaehlerDifferential.D A B (fs i))) =
      c • exteriorPower.ιMulti B (q + 3)
        (Fin.cases (KaehlerDifferential.D A B b) fun i ↦ KaehlerDifferential.D A B (fs i)) := by
  -- Expand the commutator and use the higher exact-form rule on the two scalar multiples.
  rw [LinearMap.scalarCommutator_apply]
  have hsmul :
      b • (c • exteriorPower.ιMulti B (q + 2)
          (fun i ↦ KaehlerDifferential.D A B (fs i))) =
        (b * c) • exteriorPower.ιMulti B (q + 2)
          (fun i ↦ KaehlerDifferential.D A B (fs i)) := by
    exact smul_smul b c
      (exteriorPower.ιMulti B (q + 2)
        (fun i ↦ KaehlerDifferential.D A B (fs i)))
  have hbc := hdBA.higher q (b * c) fs
  have hc := hdBA.higher q c fs
  change δBA (q + 2)
        (b • (c • exteriorPower.ιMulti B (q + 2)
          (fun i ↦ KaehlerDifferential.D A B (fs i)))) -
      b • δBA (q + 2)
        (c • exteriorPower.ιMulti B (q + 2)
          (fun i ↦ KaehlerDifferential.D A B (fs i))) =
    c • exteriorPower.ιMulti B (q + 3)
      (Fin.cases (KaehlerDifferential.D A B b) fun i ↦ KaehlerDifferential.D A B (fs i))
  rw [hsmul, hbc, hc]
  -- The Leibniz expansion splits the first coordinate and cancels the commutator term.
  rw [(KaehlerDifferential.D A B).leibniz b c]
  exact iMulti_fin_cases_smul_add_smul_sub (B := B) (q + 2) b c
    (KaehlerDifferential.D A B c) (KaehlerDifferential.D A B b)
    (fun i ↦ KaehlerDifferential.D A B (fs i))

/-- Helper for Chap10 Lemma 10 132 2: an exterior generator with a zero first coordinate is
zero. -/
private theorem iMulti_fin_cases_zero
    {M : Type*} [AddCommGroup M] [Module B M]
    (n : ℕ) (tail : Fin n → M) :
    exteriorPower.ιMulti B (n + 1) (Fin.cases (0 : M) tail) = 0 := by
  -- Rewrite the leading zero as an update of the first coordinate, then use alternation's
  -- coordinate-zero rule.
  let base : Fin (n + 1) → M := Fin.cases 0 tail
  have hupdate :
      Fin.cases (0 : M) tail = Function.update base 0 0 := by
    ext i
    cases i using Fin.cases with
    | zero =>
        simp [base]
    | succ i =>
        simp [base]
  rw [hupdate]
  exact (exteriorPower.ιMulti B (n + 1)).map_update_zero base 0

/-- Helper for Chap10 Lemma 10 132 2: after applying `π`, a left exterior wedge whose first
coordinate maps to zero vanishes, even with a fixed scalar on the right exterior factor. -/
theorem exteriorPowerDeRhamMap_leftTensor_exact_zero_left
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (p : ℕ)
    (η : Ω[B⁄A])
    (hη : π η = 0)
    (c : B)
    (tail : Fin (p + 1) → Ω[B⁄A]) :
    exteriorPowerDeRhamMap A π (p + 2)
        ((exteriorPower.leftTensorMap (p + 1)
          (LinearMap.id : Ω[B⁄A] →ₗ[B] Ω[B⁄A]))
          (η ⊗ₜ[B] (c • exteriorPower.ιMulti B (p + 1) tail))) =
      0 := by
  -- Work at the underlying `B`-linear exterior-power map so scalar transport by `c` is direct.
  let L := exteriorPower.leftTensorMap (p + 1)
    (LinearMap.id : Ω[B⁄A] →ₗ[B] Ω[B⁄A])
  let E := exteriorPower.map (p + 2) π
  let m : Fin (p + 2) → Ω[B⁄A] := Fin.cons (c • η) tail
  change E (L (η ⊗ₜ[B] (c • exteriorPower.ιMulti B (p + 1) tail))) = 0
  have htmul :
      η ⊗ₜ[B] (c • exteriorPower.ιMulti B (p + 1) tail) =
        (c • η) ⊗ₜ[B] exteriorPower.ιMulti B (p + 1) tail := by
    exact TensorProduct.tmul_smul c η (exteriorPower.ιMulti B (p + 1) tail)
  have hmap :
      E (exteriorPower.ιMulti B (p + 2) m) =
        exteriorPower.ιMulti B (p + 2)
          (fun i ↦ π (m i)) := by
    exact exteriorPower.map_apply_ιMulti π m
  have hcoord :
      (fun i : Fin (p + 2) ↦ π (m i)) =
        Fin.cases (0 : Ω) (fun i ↦ π (tail i)) := by
    ext i
    cases i using Fin.cases with
    | zero =>
        simp [m, hη]
    | succ i =>
        simp [m]
  calc
    E (L (η ⊗ₜ[B] (c • exteriorPower.ιMulti B (p + 1) tail))) =
        E (L ((c • η) ⊗ₜ[B] exteriorPower.ιMulti B (p + 1) tail)) := by
          exact congrArg (fun t ↦ E (L t)) htmul
    _ = E (exteriorPower.ιMulti B (p + 2) (Fin.cons (c • η) tail)) := by
          exact congrArg E
            (exteriorPower.leftTensorMap_tmul_ιMulti (p + 1)
              (LinearMap.id : Ω[B⁄A] →ₗ[B] Ω[B⁄A]) (c • η) tail)
    _ = E (exteriorPower.ιMulti B (p + 2) m) := by
          rfl
    _ = exteriorPower.ιMulti B (p + 2)
          (fun i ↦ π (m i)) := by
          rw [hmap]
    _ = exteriorPower.ιMulti B (p + 2)
          (Fin.cases (0 : Ω) (fun i ↦ π (tail i))) := by
          rw [hcoord]
    _ = 0 := by
          exact iMulti_fin_cases_zero (B := B) (p + 1) (fun i ↦ π (tail i))

/-- Helper for Chap10 Lemma 10 132 2: there is a linear map appending a fixed right tail to a
degree-two exterior form. -/
theorem exists_rightWedgeTailMap
    {M : Type v} [AddCommGroup M] [Module B M]
    (n : ℕ) (tail : Fin n → M) :
    ∃ F : ⋀[B]^2 M →ₗ[B] ⋀[B]^(n + 2) M,
      ∀ u v : M,
        F (degree_two_left_wedge_map (B := B) u v) =
          exteriorPower.ιMulti B (n + 2) (Fin.cons u (Fin.cons v tail)) := by
  -- Build the map from the exterior-power universal property applied to the alternating
  -- two-variable map that appends the fixed tail.
  refine ⟨?F, ?hF⟩
  · refine exteriorPower.alternatingMapLinearEquiv ?alt
    refine
      ({ toFun := (fun m ↦
          exteriorPower.ιMulti B (n + 2) (Fin.cons (m 0) (Fin.cons (m 1) tail)))
        map_update_add' m i x y := by
          fin_cases i
          · simp [Function.update]
          · simp [Function.update]
        map_update_smul' m i c x := by
          fin_cases i
          · simp [Function.update]
          · simp [Function.update]
        map_eq_zero_of_eq' m i j hij hne := by
          fin_cases i <;> fin_cases j
          · exact (hne rfl).elim
          ·
            have hm : m 0 = m 1 := hij
            let w : Fin (n + 2) → M := Fin.cons (m 0) (Fin.cons (m 1) tail)
            have hw :
                Fin.cons (m 0) (Fin.cons (m 1) tail) = Function.update w 1 (m 0) := by
              ext k
              fin_cases k
              · simp [w]
              · simp [w, hm]
              · simp [w]
            rw [hw]
            exact (exteriorPower.ιMulti B (n + 2)).map_update_eq_zero w 0 1 rfl (by decide)
          ·
            have hm : m 1 = m 0 := hij
            let w : Fin (n + 2) → M := Fin.cons (m 0) (Fin.cons (m 1) tail)
            have hw :
                Fin.cons (m 0) (Fin.cons (m 1) tail) = Function.update w 0 (m 1) := by
              ext k
              fin_cases k
              · simp [w, hm]
              · simp [w]
              · simp [w]
            rw [hw]
            exact (exteriorPower.ιMulti B (n + 2)).map_update_eq_zero w 1 0 rfl (by decide)
          · exact (hne rfl).elim } :
        M [⋀^Fin 2]→ₗ[B] ⋀[B]^(n + 2) M)
  · intro u v
    -- The chosen alternating map computes on the basic two-form as the appended generator.
    simp [degree_two_left_wedge_map_apply]

/-- Helper for Chap10 Lemma 10 132 2: the canonical map appending a fixed right tail to a
degree-two exterior form. -/
noncomputable def rightWedgeTailMap
    {M : Type v} [AddCommGroup M] [Module B M]
    (n : ℕ) (tail : Fin n → M) :
    ⋀[B]^2 M →ₗ[B] ⋀[B]^(n + 2) M :=
  Classical.choose (exists_rightWedgeTailMap (B := B) n tail)

/-- Helper for Chap10 Lemma 10 132 2: appending a fixed tail to a basic degree-two left wedge
gives the corresponding higher exterior generator. -/
theorem rightWedgeTailMap_apply_degree_two_left_wedge
    {M : Type v} [AddCommGroup M] [Module B M]
    (n : ℕ) (tail : Fin n → M) (u v : M) :
    rightWedgeTailMap (B := B) n tail (degree_two_left_wedge_map (B := B) u v) =
      exteriorPower.ιMulti B (n + 2) (Fin.cons u (Fin.cons v tail)) := by
  -- Unpack the computation rule supplied by the existence theorem used in the definition.
  exact Classical.choose_spec (exists_rightWedgeTailMap (B := B) n tail) u v

/-- Helper for Chap10 Lemma 10 132 2: a basic exterior generator whose second coordinate is zero
vanishes. -/
private theorem iMulti_fin_cons_cons_zero
    {M : Type v} [AddCommGroup M] [Module B M]
    (n : ℕ) (u : M) (tail : Fin n → M) :
    exteriorPower.ιMulti B (n + 2) (Fin.cons u (Fin.cons (0 : M) tail)) = 0 := by
  -- Put the zero second coordinate into `Function.update` form and use multilinearity.
  let w : Fin (n + 2) → M := Fin.cons u (Fin.cons (0 : M) tail)
  have hw_one : w 1 = 0 := by
    simp [w]
  have hupdate : Function.update w 1 0 = w := by
    rw [← hw_one]
    exact Function.update_eq_self 1 w
  have hzero := (exteriorPower.ιMulti B (n + 2)).map_update_zero w 1
  rw [hupdate] at hzero
  exact hzero

/-- Helper for Chap10 Lemma 10 132 2: after applying the quotient exterior-power map, the
source differential of a left wedge with an exact right tail splits into the `dη` summand and the
`dc ∧ η` summand. -/
theorem exteriorPowerDeRhamMap_delta_leftTensor_exact_formula
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hdBA : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δBA)
    (p : ℕ)
    (η : Ω[B⁄A])
    (c : B)
    (fs : Fin (p + 1) → B) :
    exteriorPowerDeRhamMap A π (p + 3)
        (δBA (p + 2)
          ((exteriorPower.leftTensorMap (p + 1)
            (LinearMap.id : Ω[B⁄A] →ₗ[B] Ω[B⁄A]))
            (η ⊗ₜ[B]
              (c • exteriorPower.ιMulti B (p + 1)
                (fun i ↦ KaehlerDifferential.D A B (fs i)))))) =
      c • rightWedgeTailMap (B := B) (p + 1)
          (fun i ↦ π (KaehlerDifferential.D A B (fs i)))
          (exteriorPowerDeRhamMap A π 2 (δBA 1 η)) +
        rightWedgeTailMap (B := B) (p + 1)
          (fun i ↦ π (KaehlerDifferential.D A B (fs i)))
          (degree_two_left_wedge_map (B := B)
            ((π.compDer (KaehlerDifferential.D A B)) c) (π η)) := by
  -- TODO: prove this by `B`-span induction on `η`. On exact generators it is the `higher`
  -- de Rham rule plus the first-coordinate Leibniz split; the induction steps follow by
  -- linearity of `δBA`, `exteriorPowerDeRhamMap`, and `rightWedgeTailMap`.
  sorry

/-- Helper for Chap10 Lemma 10 132 2: the source product rule, after applying `π`, kills a
left wedge with an exact right tail when the left one-form and its degree-one differential already
lie in the corresponding kernels. -/
theorem exteriorPowerDeRhamMap_delta_leftTensor_exact_of_degree_one_kernel
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hdBA : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δBA)
    (p : ℕ)
    (η : Ω[B⁄A])
    (hπη : π η = 0)
    (hdη : exteriorPowerDeRhamMap A π 2 (δBA 1 η) = (0 : ⋀[B]^2 Ω))
    (c : B)
    (fs : Fin (p + 1) → B) :
    exteriorPowerDeRhamMap A π (p + 3)
        (δBA (p + 2)
          ((exteriorPower.leftTensorMap (p + 1)
            (LinearMap.id : Ω[B⁄A] →ₗ[B] Ω[B⁄A]))
            (η ⊗ₜ[B]
              (c • exteriorPower.ιMulti B (p + 1)
                (fun i ↦ KaehlerDifferential.D A B (fs i)))))) =
      0 := by
  -- Route correction: the zero statement is not additive in `η` by itself, so first rewrite via
  -- the explicit product-rule formula whose two summands match the two kernel hypotheses.
  rw [exteriorPowerDeRhamMap_delta_leftTensor_exact_formula
    (A := A) (π := π) (δBA := δBA) hdBA p η c fs]
  have htail :
      rightWedgeTailMap (B := B) (p + 1)
          (fun i ↦ π (KaehlerDifferential.D A B (fs i)))
          (exteriorPowerDeRhamMap A π 2 (δBA 1 η)) = 0 := by
    rw [hdη]
    exact map_zero
      (rightWedgeTailMap (B := B) (p + 1)
        (fun i ↦ π (KaehlerDifferential.D A B (fs i))))
  have hleft :
      rightWedgeTailMap (B := B) (p + 1)
          (fun i ↦ π (KaehlerDifferential.D A B (fs i)))
          (degree_two_left_wedge_map (B := B)
            ((π.compDer (KaehlerDifferential.D A B)) c) (π η)) = 0 := by
    have hdegree :
        degree_two_left_wedge_map (B := B)
            ((π.compDer (KaehlerDifferential.D A B)) c) (π η) = 0 := by
      rw [hπη]
      exact map_zero
        (degree_two_left_wedge_map (B := B)
          ((π.compDer (KaehlerDifferential.D A B)) c))
    rw [hdegree]
    exact map_zero
      (rightWedgeTailMap (B := B) (p + 1)
        (fun i ↦ π (KaehlerDifferential.D A B (fs i))))
  rw [htail, hleft]
  exact (smul_zero c : c • (0 : ⋀[B]^(p + 3) Ω) = 0)

/-- Helper for Chap10 Lemma 10 132 2: exact right exterior generators are preserved by the
source differential after left wedging with a one-form in `ker π`. -/
theorem deRhamDifferential_leftTensor_exact_mem_kernel
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hdBA : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δBA)
    (hker : SatisfiesExteriorPowerDeRhamKernelCondition π δBA)
    (p : ℕ)
    (η : LinearMap.ker π)
    (c : B)
    (fs : Fin (p + 1) → B) :
    exteriorPowerDeRhamMap A π (p + 3)
        (δBA (p + 2)
          ((exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype)
            (η ⊗ₜ[B]
              (c • exteriorPower.ιMulti B (p + 1)
                (fun i ↦ KaehlerDifferential.D A B (fs i)))))) =
      0 := by
  -- Route correction: the previous zero-only route hid the Leibniz split. The remaining
  -- source-facing step is the exact-generator product rule: the `dη` summand dies by the
  -- degree-one kernel condition and the `η ∧ dc` summand dies because `π η = 0`.
  let α : ⋀[B]^(p + 1) Ω[B⁄A] :=
    c • exteriorPower.ιMulti B (p + 1)
      (fun i ↦ KaehlerDifferential.D A B (fs i))
  let Lker := exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype
  let Lid := exteriorPower.leftTensorMap (p + 1)
    (LinearMap.id : Ω[B⁄A] →ₗ[B] Ω[B⁄A])
  have hπη : π (η : Ω[B⁄A]) = 0 := η.property
  have hdegree :
      exteriorPowerDeRhamMap A π 2 (δBA 1 (η : Ω[B⁄A])) = (0 : ⋀[B]^2 Ω) := by
    have hmem :
        (η : Ω[B⁄A]) ∈ LinearMap.ker (exteriorPowerDeRhamMap A π 1) := by
      exact (mem_ker_exteriorPowerDeRhamMap_one_iff (A := A) π (η : Ω[B⁄A])).mpr hπη
    simpa [Submodule.mem_comap, LinearMap.mem_ker] using
      degree_one_exterior_power_kernel_preserved
        (A := A) (π := π) (δBA := δBA) hdBA hker hmem
  have hleft :
      Lker (η ⊗ₜ[B] α) = Lid ((η : Ω[B⁄A]) ⊗ₜ[B] α) := by
    -- Compare the two left-tensor maps on the exact right generator after moving the scalar
    -- coefficient to the left tensor factor.
    have hker_tmul :
        η ⊗ₜ[B] α =
          (c • η) ⊗ₜ[B]
            exteriorPower.ιMulti B (p + 1)
              (fun i ↦ KaehlerDifferential.D A B (fs i)) := by
      exact TensorProduct.tmul_smul c η
        (exteriorPower.ιMulti B (p + 1)
          (fun i ↦ KaehlerDifferential.D A B (fs i)))
    have hid_tmul :
        (η : Ω[B⁄A]) ⊗ₜ[B] α =
          (c • (η : Ω[B⁄A])) ⊗ₜ[B]
            exteriorPower.ιMulti B (p + 1)
              (fun i ↦ KaehlerDifferential.D A B (fs i)) := by
      exact TensorProduct.tmul_smul c (η : Ω[B⁄A])
        (exteriorPower.ιMulti B (p + 1)
          (fun i ↦ KaehlerDifferential.D A B (fs i)))
    calc
      Lker (η ⊗ₜ[B] α) =
          Lker ((c • η) ⊗ₜ[B]
            exteriorPower.ιMulti B (p + 1)
              (fun i ↦ KaehlerDifferential.D A B (fs i))) := by
            exact congrArg Lker hker_tmul
      _ =
          exteriorPower.ιMulti B (p + 2)
            (Fin.cons ((LinearMap.ker π).subtype (c • η))
              (fun i ↦ KaehlerDifferential.D A B (fs i))) := by
            exact exteriorPower.leftTensorMap_tmul_ιMulti (p + 1)
              (LinearMap.ker π).subtype (c • η)
              (fun i ↦ KaehlerDifferential.D A B (fs i))
      _ =
          exteriorPower.ιMulti B (p + 2)
            (Fin.cons (c • (η : Ω[B⁄A]))
              (fun i ↦ KaehlerDifferential.D A B (fs i))) := by
            rfl
      _ =
          Lid ((c • (η : Ω[B⁄A])) ⊗ₜ[B]
            exteriorPower.ιMulti B (p + 1)
              (fun i ↦ KaehlerDifferential.D A B (fs i))) := by
            exact (exteriorPower.leftTensorMap_tmul_ιMulti (p + 1)
              (LinearMap.id : Ω[B⁄A] →ₗ[B] Ω[B⁄A]) (c • (η : Ω[B⁄A]))
              (fun i ↦ KaehlerDifferential.D A B (fs i))).symm
      _ =
          Lid ((η : Ω[B⁄A]) ⊗ₜ[B] α) := by
            exact congrArg Lid hid_tmul.symm
  calc
    exteriorPowerDeRhamMap A π (p + 3)
        (δBA (p + 2) (Lker (η ⊗ₜ[B] α))) =
      exteriorPowerDeRhamMap A π (p + 3)
        (δBA (p + 2) (Lid ((η : Ω[B⁄A]) ⊗ₜ[B] α))) := by
        rw [hleft]
    _ = 0 := by
        exact exteriorPowerDeRhamMap_delta_leftTensor_exact_of_degree_one_kernel
          (A := A) (π := π) (δBA := δBA) hdBA p (η : Ω[B⁄A]) hπη hdegree c fs

/-- Helper for Chap10 Lemma 10 132 2: the de Rham differential sends a left wedge whose first
factor lies in `ker π` into the next exterior-power kernel. -/
theorem deRhamDifferential_leftTensor_mem_kernel
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hdBA : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δBA)
    (hker : SatisfiesExteriorPowerDeRhamKernelCondition π δBA)
    (p : ℕ)
    (η : LinearMap.ker π)
    (α : ⋀[B]^(p + 1) Ω[B⁄A]) :
    exteriorPowerDeRhamMap A π (p + 3)
        (δBA (p + 2)
          ((exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype)
            (η ⊗ₜ[B] α))) =
      0 := by
  -- Exact wedges span the right exterior-power factor. Since `δBA` is only `A`-linear, the
  -- induction predicate keeps an arbitrary leading `B`-scalar on the right factor.
  have hα :
      α ∈ Submodule.span B
        (exteriorPower.ιMulti B (p + 1) ''
          {m : Fin (p + 1) → Ω[B⁄A] |
            Set.range m ⊆ Set.range (KaehlerDifferential.D A B)}) := by
    rw [deRhamExactExteriorPower_span (A := A) (B := B) (p + 1)]
    exact Submodule.mem_top
  have hscaled :
      ∀ c : B,
        exteriorPowerDeRhamMap A π (p + 3)
            (δBA (p + 2)
              ((exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype)
                (η ⊗ₜ[B] (c • α)))) =
          0 := by
    refine Submodule.span_induction
      (p := fun β _ ↦
        ∀ c : B,
          exteriorPowerDeRhamMap A π (p + 3)
              (δBA (p + 2)
                ((exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype)
                  (η ⊗ₜ[B] (c • β)))) =
            0)
      ?mem ?zero ?add ?smul hα
    · intro β hβ c
      -- On exact generators, the remaining work is exactly the source Leibniz/product-rule
      -- computation isolated in `deRhamDifferential_leftTensor_exact_mem_kernel`.
      rcases hβ with ⟨m, hm, rfl⟩
      let fs : Fin (p + 1) → B := fun i ↦ Classical.choose (hm ⟨i, rfl⟩)
      have hm_eq :
          m = fun i ↦ KaehlerDifferential.D A B (fs i) := by
        ext i
        exact (Classical.choose_spec (hm ⟨i, rfl⟩)).symm
      rw [hm_eq]
      exact deRhamDifferential_leftTensor_exact_mem_kernel
        (A := A) (π := π) (δBA := δBA) hdBA hker p η c fs
    · intro c
      -- The zero right factor maps to zero through the tensor, wedge, source differential,
      -- and quotient exterior-power maps.
      let L := exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype
      let E := exteriorPowerDeRhamMap A π (p + 3)
      have htmul : η ⊗ₜ[B] (c • (0 : ⋀[B]^(p + 1) Ω[B⁄A])) = 0 := by
        calc
          η ⊗ₜ[B] (c • (0 : ⋀[B]^(p + 1) Ω[B⁄A])) =
              η ⊗ₜ[B] (0 : ⋀[B]^(p + 1) Ω[B⁄A]) := by
                exact congrArg (fun β ↦ η ⊗ₜ[B] β) (smul_zero c)
          _ = 0 :=
                TensorProduct.tmul_zero
                  (N := ⋀[B]^(p + 1) Ω[B⁄A]) η
      calc
        E (δBA (p + 2) (L (η ⊗ₜ[B] (c • (0 : ⋀[B]^(p + 1) Ω[B⁄A]))))) =
            E (δBA (p + 2) (L 0)) := by
              exact congrArg (fun t ↦ E (δBA (p + 2) (L t))) htmul
        _ = E (δBA (p + 2) 0) := by
              exact congrArg (fun x ↦ E (δBA (p + 2) x)) (map_zero L)
        _ = E 0 := by
              exact congrArg E (map_zero (δBA (p + 2)))
        _ = 0 := map_zero E
    · intro β γ _ _ hβ hγ c
      -- Additivity of the tensor presentation and both linear maps reduces to the two
      -- induction hypotheses at the same scalar.
      let L := exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype
      let E := exteriorPowerDeRhamMap A π (p + 3)
      have htmul :
          η ⊗ₜ[B] (c • (β + γ)) =
            η ⊗ₜ[B] (c • β) + η ⊗ₜ[B] (c • γ) := by
        calc
          η ⊗ₜ[B] (c • (β + γ)) =
              η ⊗ₜ[B] (c • β + c • γ) := by
                exact congrArg (fun ξ ↦ η ⊗ₜ[B] ξ) (smul_add c β γ)
          _ = η ⊗ₜ[B] (c • β) + η ⊗ₜ[B] (c • γ) :=
                TensorProduct.tmul_add η (c • β) (c • γ)
      have hleft :
          L (η ⊗ₜ[B] (c • (β + γ))) =
            L (η ⊗ₜ[B] (c • β)) + L (η ⊗ₜ[B] (c • γ)) := by
        exact (congrArg L htmul).trans
          (map_add L
          (η ⊗ₜ[B] (c • β)) (η ⊗ₜ[B] (c • γ))
          )
      have hδ :
          δBA (p + 2)
              (L (η ⊗ₜ[B] (c • (β + γ)))) =
            δBA (p + 2)
                (L (η ⊗ₜ[B] (c • β))) +
              δBA (p + 2)
                (L (η ⊗ₜ[B] (c • γ))) := by
        exact (congrArg (δBA (p + 2)) hleft).trans
          (map_add (δBA (p + 2))
            (L (η ⊗ₜ[B] (c • β)))
            (L (η ⊗ₜ[B] (c • γ))))
      have hmap :
          E (δBA (p + 2) (L (η ⊗ₜ[B] (c • (β + γ))))) =
            E (δBA (p + 2) (L (η ⊗ₜ[B] (c • β)))) +
              E (δBA (p + 2) (L (η ⊗ₜ[B] (c • γ)))) := by
        exact (congrArg E hδ).trans
          (map_add E
            (δBA (p + 2) (L (η ⊗ₜ[B] (c • β))))
            (δBA (p + 2) (L (η ⊗ₜ[B] (c • γ)))))
      rw [hmap, hβ c, hγ c]
      exact add_zero 0
    · intro b β _ hβ c
      -- The remembered scalar absorbs the span scalar, avoiding any false `B`-linearity claim
      -- about the de Rham differential.
      let F :=
        fun β' : ⋀[B]^(p + 1) Ω[B⁄A] ↦
          exteriorPowerDeRhamMap A π (p + 3)
            (δBA (p + 2)
              ((exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype)
                (η ⊗ₜ[B] β')))
      have hscalar : c • b • β = (c * b) • β := smul_smul c b β
      exact (congrArg F hscalar).trans (hβ (c * b))
  -- Specialize the scalar-aware span induction to the scalar `1`.
  let F :=
    fun β : ⋀[B]^(p + 1) Ω[B⁄A] ↦
      exteriorPowerDeRhamMap A π (p + 3)
        (δBA (p + 2)
          ((exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype)
            (η ⊗ₜ[B] β)))
  have hone : (1 : B) • α = α := one_smul B α
  exact (congrArg F hone).symm.trans (hscaled 1)

/-- Helper for Chap10 Lemma 10 132 2: the whole range of the left-tensor kernel presentation is
preserved by the source de Rham differential. -/
theorem deRhamDifferential_leftTensorMap_range_le_kernel
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hdBA : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δBA)
    (hker : SatisfiesExteriorPowerDeRhamKernelCondition π δBA)
    (p : ℕ) :
    (LinearMap.range
      (exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype)).restrictScalars A ≤
      Submodule.comap (δBA (p + 2))
        (LinearMap.ker (exteriorPowerDeRhamMap A π (p + 3))) := by
  intro x hx
  -- Unpack the range presentation and reduce to pure tensors in the source tensor product.
  rcases hx with ⟨t, rfl⟩
  change exteriorPowerDeRhamMap A π (p + 3)
      (δBA (p + 2)
        ((exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype) t)) = 0
  -- Tensor induction leaves the single pure-tensor preservation lemma as the only
  -- mathematical input.
  induction t using TensorProduct.induction_on with
  | zero =>
      -- The zero tensor maps to zero, and both degreewise maps are additive.
      have hδ :
          δBA (p + 2)
              ((exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype) 0) = 0 := by
        have hleft :
            (exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype) 0 = 0 :=
          map_zero (exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype)
        rw [hleft]
        exact map_zero (δBA (p + 2))
      simpa using congrArg (exteriorPowerDeRhamMap A π (p + 3)) hδ
  | tmul η α =>
      exact deRhamDifferential_leftTensor_mem_kernel
        (A := A) (π := π) (δBA := δBA) hdBA hker p η α
  | add t₁ t₂ ht₁ ht₂ =>
      -- Additivity of the two linear maps reduces the sum case to the induction hypotheses.
      have hδ :
          δBA (p + 2)
              ((exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype) (t₁ + t₂)) =
            δBA (p + 2)
              ((exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype) t₁) +
              δBA (p + 2)
                ((exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype) t₂) := by
        have hleft :
            (exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype) (t₁ + t₂) =
              (exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype) t₁ +
                (exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype) t₂ :=
          map_add (exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype) t₁ t₂
        rw [hleft]
        exact map_add (δBA (p + 2))
          ((exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype) t₁)
          ((exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype) t₂)
      have hmap :
          exteriorPowerDeRhamMap A π (p + 3)
              (δBA (p + 2)
                ((exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype) t₁) +
                δBA (p + 2)
                  ((exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype) t₂)) =
            exteriorPowerDeRhamMap A π (p + 3)
                (δBA (p + 2)
                  ((exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype) t₁)) +
              exteriorPowerDeRhamMap A π (p + 3)
                (δBA (p + 2)
                  ((exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype) t₂)) :=
        map_add (exteriorPowerDeRhamMap A π (p + 3))
          (δBA (p + 2)
            ((exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype) t₁))
          (δBA (p + 2)
            ((exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype) t₂))
      rw [hδ, hmap, ht₁, ht₂]
      exact add_zero 0

/-- Helper for Lemma 10.132.2: once the higher-degree kernel description is supplied, the source
proof gives kernel preservation in every degree. -/
theorem delta_preserves_exterior_power_kernels
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hdBA : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δBA)
    (hker : SatisfiesExteriorPowerDeRhamKernelCondition π δBA) :
    ∀ p : ℕ,
      LinearMap.ker (exteriorPowerDeRhamMap A π p) ≤
        Submodule.comap (δBA p) (LinearMap.ker (exteriorPowerDeRhamMap A π (p + 1))) := by
  intro p
  cases p with
  | zero =>
      -- Degree zero is immediate because the degree-zero quotient map is the identity.
      exact degree_zero_exterior_power_kernel_preserved (A := A) π δBA
  | succ p =>
      cases p with
      | zero =>
          -- Degree one is exactly the stated kernel-generation condition plus the scalar
          -- commutator calculation already proved above.
          exact degree_one_exterior_power_kernel_preserved
            (A := A) π δBA hdBA hker
      | succ p =>
          -- Higher-degree kernels have already been normalized to the restricted range of the
          -- left-tensor map. The only missing step is preservation of that range by `δBA`.
          rw [ker_exteriorPowerDeRhamMap_higher_eq_restrictScalars_range_leftTensorMap
            (A := A) π hπ p]
          -- TODO: prove this range-preservation statement by reducing the right tensor factor
          -- to exact wedges and using `hker` for the left one-form generator.
          have hleftTensorRange :
              (LinearMap.range
                (exteriorPower.leftTensorMap (p + 1) (LinearMap.ker π).subtype)).restrictScalars A ≤
                Submodule.comap (δBA (p + 2))
                  (LinearMap.ker (exteriorPowerDeRhamMap A π (p + 3))) := by
            exact deRhamDifferential_leftTensorMap_range_le_kernel
              (A := A) π δBA hdBA hker p
          exact hleftTensorRange

-- Proof sketch: descend the recursive differential family degree by degree through the quotient
-- map `π`, starting from the induced derivation in degree `0`, use the kernel hypothesis to
-- obtain the descended map in degree `1`, and then descend the higher pieces through the induced
-- exterior-power maps while preserving the defining de Rham rule and the square-zero relation.
/-- Lemma 10.132.2: if a surjective quotient `π : Ω[B⁄A] → Ω` has kernel generated by one-forms
whose descended degree-two differential vanishes, then the de Rham differential on
`Ω^\bullet_{B/A}` descends to a single recursive differential family on the exterior powers of
`Ω`. -/
@[stacks 07HY]
theorem exists_descended_exterior_power_de_rham_differential_of_isExteriorPowerDeRhamDifferential
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (δBA : DeRhamFamily A B Ω[B⁄A])
    (hdBA : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D A B) δBA)
    (hker : SatisfiesExteriorPowerDeRhamKernelCondition π δBA) :
    ∃ δΩ : DeRhamFamily A B Ω,
      IsExteriorPowerDeRhamDifferential (π.compDer (KaehlerDifferential.D A B)) δΩ ∧
        DescendsExteriorPowerDifferential π δBA δΩ := by
  -- The remaining work is exactly the kernel-preservation theorem for the source family.
  exact
    exists_descended_exterior_power_differential_of_kernel_preservation
      (A := A)
      π
      hπ
      δBA
      hdBA
      (delta_preserves_exterior_power_kernels (A := A) π hπ δBA hdBA hker)

/-- Lemma 10.132.2: if a surjective quotient `π : Ω[B⁄A] → Ω` has kernel generated by one-forms
whose descended degree-two differential vanishes, then the canonical de Rham differential on
`Ω^\bullet_{B/A}` descends to a single recursive differential family on the exterior powers of
`Ω`. -/
@[stacks 07HY]
theorem exists_descended_exterior_power_de_rham_differential
    (π : Ω[B⁄A] →ₗ[B] Ω)
    (hπ : Function.Surjective π)
    (hker : ExteriorPowerDeRhamKernelCondition A B π) :
    ∃ δΩ : DeRhamFamily A B Ω,
      IsExteriorPowerDeRhamDifferential (π.compDer (KaehlerDifferential.D A B)) δΩ ∧
        DescendsExteriorPowerDifferential π (deRhamDifferentialFamily A B) δΩ := by
  -- Specialize the arbitrary-family descent theorem to the canonical Kähler de Rham family.
  exact
    exists_descended_exterior_power_de_rham_differential_of_isExteriorPowerDeRhamDifferential
      π
      hπ
      (deRhamDifferentialFamily A B)
      (isExteriorPowerDeRhamDifferential_deRhamDifferentialFamily A B)
      hker

end
