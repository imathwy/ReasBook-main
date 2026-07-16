import StacksProject_2024.stacks_project.Chap10.«10_69_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling for Lemma 20.35.3:
- primary domain: inverse-limit topologies on sequential systems of `A`-modules, compared with
  `I`-adic module topologies via the kernel filtration on the limit;
- sampled owner declarations:
  * `Ideal.Filtration`;
  * `_root_.idealAssociatedGradedRing`;
  * `Ideal.adicModuleTopology`;
  * `LinearMap.ker`;
  * `TopologicalSpace.induced`;
  * `CategoryTheory.Limits.limit.π`.
- owner choice:
  * `source-facing`: the kernel filtration together with the compatibility condition
    `I • F^n ≤ F^(n + 1)` needed to view its associated graded canonically as a
    `gr_I(A)`-module;
  * `core/canonical`: `Ideal.Filtration`, instantiated below by the intrinsic kernel filtration on
    `limit cohomologySystem`, together with `CategoryTheory.inverseLimitTopology`, defined from
    `TopologicalSpace.induced` and `limit.π`;
  * `bridge/view`: the downstream comparison from source cohomology groups
    `H^p(X, I^n 𝓕_{n + 1})` or their eventual images to the associated graded of that
    kernel filtration.
- primitive data: the ideal `I`, the inverse system `cohomologySystem`, and the compatibility
  witness `I • F^n ≤ F^(n + 1)` for the kernel filtration;
  `inverseLimitKernelFiltration cohomologySystem`, and the canonical filtration owner
  `inverseLimitKernelIdealFiltration I cohomologySystem hI` together with its associated graded
  object `(inverseLimitKernelIdealFiltration I cohomologySystem hI).associatedGraded`.
-/

noncomputable section

universe u

namespace Ideal.Filtration

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {I : Ideal R}

/-- The degree-`n` piece `F^n / F^(n + 1)` of an `I`-filtration `F`. -/
abbrev gradedPiece (F : I.Filtration M) (n : ℕ) : Type _ :=
  F.N n ⧸ (F.N (n + 1)).submoduleOf (F.N n)

/-- The associated graded object `⨁_{n ≥ 0} F^n / F^(n + 1)` of an `I`-filtration `F`. -/
def associatedGraded (F : I.Filtration M) : Type _ :=
  DirectSum ℕ (fun n ↦ F.gradedPiece n)

instance (F : I.Filtration M) : AddCommGroup F.associatedGraded := by
  change AddCommGroup (DirectSum ℕ (fun n ↦ F.gradedPiece n))
  infer_instance

instance (F : I.Filtration M) : Module R F.associatedGraded := by
  change Module R (DirectSum ℕ (fun n ↦ F.gradedPiece n))
  infer_instance

end Ideal.Filtration

namespace CategoryTheory

open Limits Opposite TopologicalSpace
open scoped BigOperators

section

variable {A : Type u} [CommRing A]

/-- The inverse-limit module of a sequential system of `A`-modules. This bundled owner keeps the
public API over the canonical `ModuleCat` object instead of repeatedly spelling the raw limit
carrier. -/
abbrev inverseLimitModule (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A) : ModuleCat.{u} A :=
  limit cohomologySystem

/-- The topology on the inverse limit of a sequential system of `A`-modules induced from the
product of the discrete quotient modules. -/
abbrev inverseLimitTopology (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A) :
    TopologicalSpace (inverseLimitModule cohomologySystem) :=
  let _ : (n : ℕ) → TopologicalSpace (cohomologySystem.obj (op n)) := fun _ ↦ ⊥
  TopologicalSpace.induced
    (fun x : inverseLimitModule cohomologySystem ↦
      fun n : ℕ ↦ ((limit.π cohomologySystem (op n)).hom x : cohomologySystem.obj (op n)))
    inferInstance

/-- The `n`-th step of the kernel filtration on the inverse limit, given by the kernel of the
projection to stage `n`. -/
def inverseLimitKernelFiltration (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A) (n : ℕ) :
    Submodule A (inverseLimitModule cohomologySystem) :=
  LinearMap.ker ((limit.π cohomologySystem (op n)).hom)

/-- Membership in the `n`-th step of the inverse-limit kernel filtration is equivalent to
vanishing of the stage-`n` projection. -/
@[simp] theorem mem_inverseLimitKernelFiltration_iff
    (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A) (n : ℕ)
    (x : inverseLimitModule cohomologySystem) :
    x ∈ inverseLimitKernelFiltration cohomologySystem n ↔
      (((limit.π cohomologySystem (op n)).hom x : cohomologySystem.obj (op n)) = 0) := sorry

/-- The kernel filtration is decreasing: the kernel of the projection to stage `n + 1` lies in the
kernel of the projection to stage `n`. -/
theorem inverseLimitKernelFiltration_succ_le
    (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A) (n : ℕ) :
    inverseLimitKernelFiltration cohomologySystem (n + 1) ≤
      inverseLimitKernelFiltration cohomologySystem n := sorry

/-- The kernel filtration on the inverse limit is antitone in the stage index. -/
theorem inverseLimitKernelFiltration_antitone
    (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A) :
    Antitone (inverseLimitKernelFiltration cohomologySystem) :=
  sorry

/-- A later stage of the kernel filtration is contained in every earlier stage. -/
theorem inverseLimitKernelFiltration_le
    (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A) {m n : ℕ} (hmn : m ≤ n) :
    inverseLimitKernelFiltration cohomologySystem n ≤
      inverseLimitKernelFiltration cohomologySystem m := sorry

/-- The kernel filtration is `I`-compatible when multiplication by `I` moves the `n`-th kernel
step into the next one. This is the source-facing input needed for the canonical
`gr_I(A)`-module structure on the associated graded of the filtration. -/
def inverseLimitKernelFiltrationIdealCompatible
    (I : Ideal A) (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A) : Prop :=
  ∀ n : ℕ,
    I • inverseLimitKernelFiltration cohomologySystem n ≤
      inverseLimitKernelFiltration cohomologySystem (n + 1)

/-- The source quotient condition `M_(n + 1) = M_(n + 2) / I^(n + 1) M_(n + 2)` for a sequential
inverse system of `A`-modules, expressed by requiring each successor map
`M_(n + 2) ⟶ M_(n + 1)` to be surjective with kernel `I^(n + 1) M_(n + 2)`. -/
def inverseSystemSuccessiveQuotientsByIdealPowers
    (I : Ideal A) (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A) : Prop :=
  ∀ n : ℕ,
    LinearMap.ker ((cohomologySystem.map (homOfLE (Nat.le_succ (n + 1))).op).hom) =
        I ^ (n + 1) • (⊤ : Submodule A (cohomologySystem.obj (op (n + 2)))) ∧
      Function.Surjective ((cohomologySystem.map (homOfLE (Nat.le_succ (n + 1))).op).hom)

/-- The source quotient condition identifies the kernel of the successor map `M_(n + 2) ⟶
M_(n + 1)` with `I^(n + 1) M_(n + 2)`. -/
theorem inverseSystemSuccessiveQuotientsByIdealPowers_kernel
    (I : Ideal A) (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hquot : inverseSystemSuccessiveQuotientsByIdealPowers I cohomologySystem) (n : ℕ) :
    LinearMap.ker ((cohomologySystem.map (homOfLE (Nat.le_succ (n + 1))).op).hom) =
      I ^ (n + 1) • (⊤ : Submodule A (cohomologySystem.obj (op (n + 2)))) := sorry

/-- The source quotient condition makes each successor map `M_(n + 2) ⟶ M_(n + 1)` surjective. -/
theorem inverseSystemSuccessiveQuotientsByIdealPowers_surjective
    (I : Ideal A) (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hquot : inverseSystemSuccessiveQuotientsByIdealPowers I cohomologySystem) (n : ℕ) :
    Function.Surjective ((cohomologySystem.map (homOfLE (Nat.le_succ (n + 1))).op).hom) := sorry

/-- Helper for Lemma 20.35.3: the source quotient condition implies the `I`-compatibility of the
kernel filtration on the inverse limit. -/
theorem inverseLimitKernelFiltrationIdealCompatible_of_successiveQuotientsByIdealPowers
    (I : Ideal A) (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hquot : inverseSystemSuccessiveQuotientsByIdealPowers I cohomologySystem) :
    inverseLimitKernelFiltrationIdealCompatible I cohomologySystem := sorry

/-- Helper for Lemma 20.35.3: the specialized `I`-compatibility witness on the inverse-limit
kernel filtration coming from the source quotient condition. -/
abbrev inverseLimitKernelFiltrationIdealCompatibilityOfSuccessiveQuotientsByIdealPowers
    (I : Ideal A) (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hquot : inverseSystemSuccessiveQuotientsByIdealPowers I cohomologySystem) :
    inverseLimitKernelFiltrationIdealCompatible I cohomologySystem :=
  inverseLimitKernelFiltrationIdealCompatible_of_successiveQuotientsByIdealPowers
    I cohomologySystem hquot

/-- The compatibility hypothesis on the kernel filtration packaged in the canonical owner
`Ideal.Filtration`. -/
def inverseLimitKernelIdealFiltration
    (I : Ideal A) (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hI : inverseLimitKernelFiltrationIdealCompatible I cohomologySystem) :
    I.Filtration (inverseLimitModule cohomologySystem) where
  N := inverseLimitKernelFiltration cohomologySystem
  mono := inverseLimitKernelFiltration_succ_le cohomologySystem
  smul_le := hI

@[simp] theorem inverseLimitKernelIdealFiltration_apply
    (I : Ideal A) (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hI : inverseLimitKernelFiltrationIdealCompatible I cohomologySystem) (n : ℕ) :
    (inverseLimitKernelIdealFiltration I cohomologySystem hI).N n =
      inverseLimitKernelFiltration cohomologySystem n := sorry

/-- The associated graded object `⨁_{n ≥ 0} F^n / F^(n + 1)` of the inverse-limit kernel
filtration. Later source-facing statements treat any chosen `gr_I(A)`-module structure on this
owner as an explicit hypothesis, rather than manufacturing sorry-backed public data in this file.
-/
def inverseLimitKernelAssociatedGraded
    (I : Ideal A) (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hI : inverseLimitKernelFiltrationIdealCompatible I cohomologySystem) : Type u :=
  (inverseLimitKernelIdealFiltration I cohomologySystem hI).associatedGraded

instance inverseLimitKernelAssociatedGraded_addCommGroup
    (I : Ideal A) (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hI : inverseLimitKernelFiltrationIdealCompatible I cohomologySystem) :
    AddCommGroup (inverseLimitKernelAssociatedGraded I cohomologySystem hI) := by
  delta inverseLimitKernelAssociatedGraded
  infer_instance

/-- Helper for Lemma 20.35.3: an explicit scalar action on the inverse-limit kernel associated
graded obtained from any chosen `gr_I(A)`-module structure. Keeping this instance named avoids
reconstructing the same coercion path during later elaboration. -/
instance inverseLimitKernelAssociatedGraded_smul
    (I : Ideal A) (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hI : inverseLimitKernelFiltrationIdealCompatible I cohomologySystem)
    [Module (idealAssociatedGradedRing I)
      (inverseLimitKernelAssociatedGraded I cohomologySystem hI)] :
    SMul (idealAssociatedGradedRing I)
      (inverseLimitKernelAssociatedGraded I cohomologySystem hI) := by
  infer_instance

/-- The degree-`n` homogeneous subgroup of the inverse-limit kernel associated graded. This keeps
the canonical grading tied to the source kernel filtration `F^n / F^(n + 1)`. -/
def inverseLimitKernelAssociatedGradedGrading
    (I : Ideal A) (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hI : inverseLimitKernelFiltrationIdealCompatible I cohomologySystem) (n : ℕ) :
    AddSubgroup (inverseLimitKernelAssociatedGraded I cohomologySystem hI) :=
  AddMonoidHom.range
    (DirectSum.of
      (fun n ↦
        (inverseLimitKernelIdealFiltration I cohomologySystem hI).gradedPiece n)
      n)

/-- The degree-`n` summand of the inverse-limit kernel associated graded lands in its canonical
homogeneous subgroup. -/
@[simp] theorem inverseLimitKernelAssociatedGradedGrading_of
    (I : Ideal A) (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hI : inverseLimitKernelFiltrationIdealCompatible I cohomologySystem) (n : ℕ)
    (x : (inverseLimitKernelIdealFiltration I cohomologySystem hI).gradedPiece n) :
    DirectSum.of
        (fun n ↦
          (inverseLimitKernelIdealFiltration I cohomologySystem hI).gradedPiece n)
        n x ∈
      inverseLimitKernelAssociatedGradedGrading I cohomologySystem hI n := sorry

/-- `gr_I(A)`-linear maps into the inverse-limit kernel associated graded, for a chosen module
structure on the target. Source-facing applications use the canonical instance surface
`[SetLike.GradedSMul (idealAssociatedGradedRingGrade I)
  (inverseLimitKernelAssociatedGradedGrading I cohomologySystem hI)]` when this target action is
the one attached to the kernel filtration. -/
abbrev inverseLimitKernelAssociatedGradedHom
    (I : Ideal A) (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hI : inverseLimitKernelFiltrationIdealCompatible I cohomologySystem)
    [Module (idealAssociatedGradedRing I)
      (inverseLimitKernelAssociatedGraded I cohomologySystem hI)]
    (N : Type*) [AddCommGroup N] [Module (idealAssociatedGradedRing I) N] : Type _ :=
  N →ₗ[idealAssociatedGradedRing I] inverseLimitKernelAssociatedGraded I cohomologySystem hI

/-- Helper for Lemma 20.35.3: the inverse-limit kernel associated graded specialized using the
source quotient condition `M_(n + 1) = M_(n + 2) / I^(n + 1) M_(n + 2)`. -/
abbrev inverseLimitKernelAssociatedGradedOfSuccessiveQuotientsByIdealPowers
    (I : Ideal A) (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hquot : inverseSystemSuccessiveQuotientsByIdealPowers I cohomologySystem) : Type u :=
  inverseLimitKernelAssociatedGraded I cohomologySystem
    (inverseLimitKernelFiltrationIdealCompatibilityOfSuccessiveQuotientsByIdealPowers
      I cohomologySystem hquot)

/-- Helper for Lemma 20.35.3: the specialized associated graded inherits its additive group
structure from the underlying kernel-filtration owner. -/
instance inverseLimitKernelAssociatedGradedOfSuccessiveQuotientsByIdealPowers_addCommGroup
    (I : Ideal A) (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hquot : inverseSystemSuccessiveQuotientsByIdealPowers I cohomologySystem) :
    AddCommGroup
      (inverseLimitKernelAssociatedGradedOfSuccessiveQuotientsByIdealPowers
        I cohomologySystem hquot) := by
  delta inverseLimitKernelAssociatedGradedOfSuccessiveQuotientsByIdealPowers
  infer_instance

/-- Helper for Lemma 20.35.3: an explicit scalar action on the associated graded specialized by
the source quotient condition. Keeping this instance named avoids repeated typeclass search through
the compatibility witness built from `hquot`. -/
instance inverseLimitKernelAssociatedGradedOfSuccessiveQuotientsByIdealPowers_smul
    (I : Ideal A) (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hquot : inverseSystemSuccessiveQuotientsByIdealPowers I cohomologySystem)
    [Module (idealAssociatedGradedRing I)
      (inverseLimitKernelAssociatedGradedOfSuccessiveQuotientsByIdealPowers
        I cohomologySystem hquot)] :
    SMul (idealAssociatedGradedRing I)
      (inverseLimitKernelAssociatedGradedOfSuccessiveQuotientsByIdealPowers
        I cohomologySystem hquot) := by
  infer_instance

/-- Helper for Lemma 20.35.3: the canonical grading on the inverse-limit kernel associated graded
specialized using the source quotient condition. -/
abbrev inverseLimitKernelAssociatedGradedGradingOfSuccessiveQuotientsByIdealPowers
    (I : Ideal A) (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hquot : inverseSystemSuccessiveQuotientsByIdealPowers I cohomologySystem) :
    ℕ → AddSubgroup
      (inverseLimitKernelAssociatedGradedOfSuccessiveQuotientsByIdealPowers
        I cohomologySystem hquot) :=
  inverseLimitKernelAssociatedGradedGrading I cohomologySystem
    (inverseLimitKernelFiltrationIdealCompatibilityOfSuccessiveQuotientsByIdealPowers
      I cohomologySystem hquot)

/-- In the inverse-limit topology, the neighborhoods of `0` are generated by the kernels of the
stage projections. -/
theorem inverseLimitTopology_nhds_zero_hasBasis_kernelFiltration
    (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A) :
    let _ : TopologicalSpace (inverseLimitModule cohomologySystem) :=
      inverseLimitTopology cohomologySystem
    (nhds (0 : inverseLimitModule cohomologySystem)).HasBasis
      (fun _ : ℕ ↦ True)
      (fun n ↦
        (inverseLimitKernelFiltration cohomologySystem n :
          Set (inverseLimitModule cohomologySystem))) := sorry

-- Proof sketch: let `F^n` be the kernel of the projection from `lim_n M_n` to `M_n`. If the
-- kernel filtration is `I`-compatible, then its associated graded carries the canonical
-- `gr_I(A)`-action induced by multiplication on the limit, owned by
-- `inverseLimitKernelAssociatedGraded I cohomologySystem hI`. Noetherianity of that module forces
-- the kernel filtration to satisfy the
-- stabilization required in the source argument, so the neighborhoods defined by the inverse-limit
-- topology agree with the `I`-power neighborhoods. The downstream cohomological lemmas are
-- responsible for constructing the source comparison that proves this compatibility and the
-- corresponding Noetherian hypothesis.
/-- Lemma 20.35.3: let `F^n` be the kernel of the projection
`lim_n M_n → M_n` for a sequential inverse system `cohomologySystem = (M_n)_n` of `A`-modules.
Assume the source quotient condition that each successor map `M_(n + 2) ⟶ M_(n + 1)` identifies
`M_(n + 1)` with the quotient `M_(n + 2) / I^(n + 1) M_(n + 2)`. Then the induced kernel
filtration is `I`-compatible, so the associated graded module
`⊕_{n ≥ 0} F^n / F^{n + 1}` carries its canonical action of the associated graded ring
`⊕_{n ≥ 0} I^n / I^(n + 1)`, formalized by the canonical owner
`inverseLimitKernelAssociatedGraded I cohomologySystem
  (inverseLimitKernelFiltrationIdealCompatible_of_successiveQuotientsByIdealPowers
    I cohomologySystem hquot)` together with the instance surface
`[SetLike.GradedSMul (idealAssociatedGradedRingGrade I)
  (inverseLimitKernelAssociatedGradedGrading I cohomologySystem
    (inverseLimitKernelFiltrationIdealCompatible_of_successiveQuotientsByIdealPowers
      I cohomologySystem hquot))]`,
and if this associated graded module is Noetherian over `gr_I(A)`,
then the inverse-limit topology on `lim_n M_n` is the `I`-adic topology. In later source-facing
applications, the relevant cohomology groups `H^p(X, I^n 𝓕_{n + 1})` are used only
through a comparison with this intrinsic associated graded module. -/
@[stacks 0GYM]
lemma inverseLimitTopology_eq_adicModuleTopology_of_noetherian_kernelAssociatedGraded
    (I : Ideal A)
    (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hquot : inverseSystemSuccessiveQuotientsByIdealPowers I cohomologySystem)
    [Module (idealAssociatedGradedRing I)
      (inverseLimitKernelAssociatedGradedOfSuccessiveQuotientsByIdealPowers
        I cohomologySystem hquot)]
    [SetLike.GradedSMul (idealAssociatedGradedRingGrade I)
      (inverseLimitKernelAssociatedGradedGradingOfSuccessiveQuotientsByIdealPowers
        I cohomologySystem hquot)]
    [IsNoetherian (idealAssociatedGradedRing I)
      (inverseLimitKernelAssociatedGradedOfSuccessiveQuotientsByIdealPowers
        I cohomologySystem hquot)] :
    inverseLimitTopology cohomologySystem =
      Ideal.adicModuleTopology I (inverseLimitModule cohomologySystem) := sorry

end

end CategoryTheory
