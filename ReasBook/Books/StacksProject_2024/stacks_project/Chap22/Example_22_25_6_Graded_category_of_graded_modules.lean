import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Ring.Opposite
import Mathlib.CategoryTheory.Category.Basic
import StacksProject_2024.stacks_project.Chap22.Definition_22_25_3
import StacksProject_2024.stacks_project.Chap22.Definition_22_28_1

open scoped DirectSum

universe u v w

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]

namespace ZGradedAlgebra

end ZGradedAlgebra

namespace GradedAlgebraBimodule

variable (𝒜 : ZGradedAlgebra R A)

/- Source/core/bridge triage for Example 22.25.6:
- source-facing: right graded `A`-modules, homogeneous maps of degree `n`, and their graded Hom
  direct sums;
- core/canonical: the Chapter 22 owners `ZGradedAlgebra` and `GradedAlgebraBimodule`;
- bridge/view: `RightModule` below is only the thin bundle needed to form the category of right
  graded modules from the existing graded-bimodule owner, with the ground ring concentrated in
  degree `0` on the left. -/

/-- A right graded `A`-module is the canonical Chapter 22 graded-bimodule owner specialized to the
ground ring `R` on the left, bundled only so the category of graded modules can be formed. -/
structure RightModule where
  carrier : Type w
  [instAddCommGroup : AddCommGroup carrier]
  [instModule : Module R carrier]
  toGradedAlgebraBimodule :
    GradedAlgebraBimodule R R A carrier (ZGradedAlgebra.ground R) 𝒜

namespace RightModule

variable {𝒜}

attribute [instance] RightModule.instAddCommGroup RightModule.instModule

/-- A right graded module can be used through its underlying carrier type. -/
instance instCoeSort : CoeSort (RightModule 𝒜) (Type w) where
  coe M := M.carrier

/-- The underlying right `A`-module structure of a bundled graded module. -/
instance instModuleAOp (M : RightModule 𝒜) : Module Aᵐᵒᵖ M :=
  M.toGradedAlgebraBimodule.moduleBOp

/-- The right `A`-action commutes with the ground `R`-scalar action. -/
instance instSMulCommClass (M : RightModule 𝒜) : SMulCommClass R Aᵐᵒᵖ M :=
  M.toGradedAlgebraBimodule.instSMulCommClassRight

/-- The right `A`-action is compatible with the ambient `R`-module structure. -/
instance instIsScalarTower (M : RightModule 𝒜) : IsScalarTower R Aᵐᵒᵖ M :=
  M.toGradedAlgebraBimodule.instIsScalarTowerRight

/-- The grading on the underlying right graded module. -/
abbrev grading (M : RightModule 𝒜) : ℤ → Submodule R M :=
  M.toGradedAlgebraBimodule.grading

/-- Right multiplication in the bundled right graded module. -/
abbrev rightMul (M : RightModule 𝒜) (x : M) (a : A) : M :=
  M.toGradedAlgebraBimodule.rightMul x a

/-- Scalar multiplication on right-`A`-linear maps is defined pointwise on the codomain. -/
instance instSMulLinearMap (L M : RightModule 𝒜) :
    SMul R (L →ₗ[Aᵐᵒᵖ] M) where
  smul r f :=
    { toFun := fun x ↦ r • f x
      map_add' := by
        intro x y
        simp [smul_add]
      map_smul' := by
        intro a x
        simpa using (smul_comm r a (f x)) }

/-- The underlying right-`A`-linear maps between graded modules form an `R`-module. -/
instance instModuleLinearMap (L M : RightModule 𝒜) :
    Module R (L →ₗ[Aᵐᵒᵖ] M) :=
  Function.Injective.module R
    { toFun := fun f ↦ (f : L → M)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
    DFunLike.coe_injective
    (fun _ _ ↦ rfl)

/-- The degree-`n` homogeneous right-`A`-linear maps between graded modules. -/
def homDegree (L M : RightModule 𝒜) (n : ℤ) :
    Submodule R (L →ₗ[Aᵐᵒᵖ] M) where
  carrier := { f | ∀ i (x : L), x ∈ L.grading i → f x ∈ M.grading (i + n) }
  zero_mem' := by
    intro i x hx
    simpa using (M.grading (i + n)).zero_mem
  add_mem' := by
    intro f g hf hg i x hx
    exact (M.grading (i + n)).add_mem (hf i x hx) (hg i x hx)
  smul_mem' := by
    intro r f hf i x hx
    simpa using (M.grading (i + n)).smul_mem r (hf i x hx)

/-- Example 22.25.6 (1): the Hom object from `L` to `M` is the direct sum of the degree-`n`
homogeneous right-`A`-linear maps. -/
@[stacks 09MN]
abbrev homSpace (L M : RightModule 𝒜) :=
  ⨁ n : ℤ, homDegree L M n

/-- `homSpace` is definitionally the direct sum of the homogeneous degree pieces. -/
theorem homSpace_def (L M : RightModule 𝒜) :
    homSpace L M = ⨁ n : ℤ, homDegree L M n :=
  rfl

/-- The homogeneous degree-`n` summand inside the total graded Hom module. -/
abbrev gradedHomDegree (L M : RightModule 𝒜) (n : ℤ) : Submodule R (homSpace L M) :=
  (DirectSum.lof R ℤ (fun i ↦ homDegree L M i) n).range

private def gradedHomDegreeOf (L M : RightModule 𝒜) (n : ℤ) :
    homDegree L M n →ₗ[R] gradedHomDegree L M n where
  toFun f := ⟨DirectSum.lof R ℤ (fun i ↦ homDegree L M i) n f, ⟨f, rfl⟩⟩
  map_add' := by
    intro f g
    ext
    simp
  map_smul' := by
    intro r f
    ext
    simp

/-- The degree-`n` source-facing homogeneous maps identify canonically with the degree-`n`
summand in the graded Hom object. -/
def gradedHomDegreeEquiv (L M : RightModule 𝒜) (n : ℤ) :
    homDegree L M n ≃ₗ[R] gradedHomDegree L M n where
  toFun := gradedHomDegreeOf L M n
  invFun x := DirectSum.component R ℤ (fun i ↦ homDegree L M i) n x.1
  left_inv := by
    intro f
    ext x
    simp [gradedHomDegreeOf]
  right_inv := by
    intro x
    rcases x.2 with ⟨f, hf⟩
    have hx : x = gradedHomDegreeOf L M n f := by
      apply Subtype.ext
      exact hf.symm
    rw [hx]
    ext
    simp [gradedHomDegreeOf]
  map_add' := by
    intro x y
    ext
    simp
  map_smul' := by
    intro r x
    ext
    simp

@[simp] theorem gradedHomDegreeEquiv_apply
    (L M : RightModule 𝒜) (n : ℤ) (f : homDegree L M n) :
    ((gradedHomDegreeEquiv L M n f : gradedHomDegree L M n) : homSpace L M) =
      DirectSum.lof R ℤ (fun i ↦ homDegree L M i) n f :=
  rfl

private def homSpaceDecompose (L M : RightModule 𝒜) :
    homSpace L M →ₗ[R] ⨁ n : ℤ, gradedHomDegree L M n :=
  DirectSum.toModule R ℤ (⨁ n : ℤ, gradedHomDegree L M n)
    (fun n ↦
      (DirectSum.lof R ℤ (fun i ↦ gradedHomDegree L M i) n).comp
        (gradedHomDegreeEquiv L M n).toLinearMap)

private instance instHomSpaceDecomposition (L M : RightModule 𝒜) :
    DirectSum.Decomposition (gradedHomDegree L M) :=
  DirectSum.Decomposition.ofLinearMap (gradedHomDegree L M) (homSpaceDecompose L M)
    (by
      apply DirectSum.linearMap_ext
      intro n
      ext f
      simp [homSpaceDecompose])
    (by
      apply DirectSum.linearMap_ext
      intro n
      apply LinearMap.ext
      intro x
      rcases x.2 with ⟨f, hf⟩
      have hx : x = gradedHomDegreeOf L M n f := by
        apply Subtype.ext
        exact hf.symm
      rw [hx]
      simp [homSpaceDecompose, gradedHomDegreeEquiv, gradedHomDegreeOf])

/-- Summing the homogeneous components of a graded morphism yields the underlying right-`A`-linear
map between graded modules. -/
def homToLinearMap (L M : RightModule 𝒜) :
    homSpace L M →ₗ[R] (L →ₗ[Aᵐᵒᵖ] M) :=
  DirectSum.toModule R ℤ (L →ₗ[Aᵐᵒᵖ] M) (fun n ↦ (homDegree L M n).subtype)

@[simp] theorem homToLinearMap_lof
    (L M : RightModule 𝒜) (n : ℤ) (f : homDegree L M n) :
    homToLinearMap L M ((DirectSum.lof R ℤ (fun i ↦ homDegree L M i) n) f) = f :=
  by simp [homToLinearMap]

/-- The identity map of a graded module is homogeneous of degree `0`. -/
def idHom (L : RightModule 𝒜) :
    homDegree L L 0 :=
  ⟨LinearMap.id, by
    intro i x hx
    simpa using hx⟩

/-- Applying `idHom` does nothing. -/
@[simp] theorem idHom_apply (L : RightModule 𝒜) (x : L) :
    ((idHom L : L →ₗ[Aᵐᵒᵖ] L) x) = x :=
  rfl

/-- The identity morphism of the graded Hom category, concentrated in degree `0`. -/
def idSpace (L : RightModule 𝒜) : homSpace L L :=
  (DirectSum.lof R ℤ (fun n ↦ homDegree L L n) 0) (idHom L)

@[simp] theorem homToLinearMap_idSpace (L : RightModule 𝒜) :
    homToLinearMap L L (idSpace L) = LinearMap.id :=
  by simpa [idSpace, idHom] using homToLinearMap_lof L L 0 (idHom L)

/-- Example 22.25.6 (2): composing a degree-`m` homogeneous map with a degree-`n` homogeneous
map gives a degree-`n + m` homogeneous map. -/
@[stacks 09MN]
def compHom
    {K L M : RightModule 𝒜} {m n : ℤ}
    (g : homDegree L M m)
    (f : homDegree K L n) :
    homDegree K M (n + m) :=
  ⟨g.1.comp f.1, by
    intro i x hx
    simpa [add_assoc] using g.2 (i + n) (f.1 x) (f.2 i x hx)⟩

/-- `compHom` is given by composing the underlying homogeneous linear maps. -/
theorem compHom_def
    {K L M : RightModule 𝒜} {m n : ℤ}
    (g : homDegree L M m)
    (f : homDegree K L n) :
    ((compHom g f : homDegree K M (n + m)) : K →ₗ[Aᵐᵒᵖ] M) =
      g.1.comp f.1 :=
  rfl

/-- Applying `compHom` is pointwise composition of the underlying homogeneous maps. -/
@[simp] theorem compHom_apply
    {K L M : RightModule 𝒜} {m n : ℤ}
    (g : homDegree L M m)
    (f : homDegree K L n) (x : K) :
    ((compHom g f : K →ₗ[Aᵐᵒᵖ] M) x) =
      (g : L →ₗ[Aᵐᵒᵖ] M) ((f : K →ₗ[Aᵐᵒᵖ] L) x) :=
  rfl

@[simp] theorem compHom_add_left
    {K L M : RightModule 𝒜} {m n : ℤ}
    (g₁ g₂ : homDegree L M m) (f : homDegree K L n) :
    compHom (g₁ + g₂) f = compHom g₁ f + compHom g₂ f := by
  ext x
  simp [compHom, LinearMap.add_apply]

@[simp] theorem compHom_add_right
    {K L M : RightModule 𝒜} {m n : ℤ}
    (g : homDegree L M m) (f₁ f₂ : homDegree K L n) :
    compHom g (f₁ + f₂) = compHom g f₁ + compHom g f₂ := by
  ext x
  simp [compHom, LinearMap.comp_apply, LinearMap.map_add]

@[simp] theorem compHom_smul_left
    {K L M : RightModule 𝒜} {m n : ℤ}
    (r : R) (g : homDegree L M m) (f : homDegree K L n) :
    compHom (r • g) f = r • compHom g f := by
  ext x
  rfl

@[simp] theorem compHom_smul_right
    {K L M : RightModule 𝒜} {m n : ℤ}
    (r : R) (g : homDegree L M m) (f : homDegree K L n) :
    compHom g (r • f) = r • compHom g f := by
  ext x
  change (g : L →ₗ[Aᵐᵒᵖ] M) (r • (f : K →ₗ[Aᵐᵒᵖ] L) x) =
      r • (g : L →ₗ[Aᵐᵒᵖ] M) ((f : K →ₗ[Aᵐᵒᵖ] L) x)
  simpa using
    (g : L →ₗ[Aᵐᵒᵖ] M).map_smul_of_tower r ((f : K →ₗ[Aᵐᵒᵖ] L) x)

@[simp] theorem compHom_id_right
    {K L : RightModule 𝒜} {n : ℤ} (f : homDegree K L n) :
    (compHom f (idHom K) : K →ₗ[Aᵐᵒᵖ] L) = f := by
  ext x
  rfl

@[simp] theorem compHom_id_left
    {K L : RightModule 𝒜} {n : ℤ} (f : homDegree K L n) :
    (compHom (idHom L) f : K →ₗ[Aᵐᵒᵖ] L) = f := by
  ext x
  rfl

private def compHomLinear
    {K L M : RightModule 𝒜} {m n : ℤ}
    (g : homDegree L M m) :
    homDegree K L n →ₗ[R] homDegree K M (n + m) where
  toFun := compHom g
  map_add' := by
    intro f₁ f₂
    simpa using compHom_add_right g f₁ f₂
  map_smul' := by
    intro r f
    simpa using compHom_smul_right r g f

private def postcomposeHom
    {K L M : RightModule 𝒜} {m : ℤ}
    (g : homDegree L M m) :
    homSpace K L →ₗ[R] homSpace K M :=
  DirectSum.toModule R ℤ (homSpace K M)
    (fun n ↦
      (DirectSum.lof R ℤ (fun i ↦ homDegree K M i) (n + m)).comp (compHomLinear g))

private def compLinear
    {K L M : RightModule 𝒜} :
    homSpace L M →ₗ[R] homSpace K L →ₗ[R] homSpace K M :=
  DirectSum.toModule R ℤ (homSpace K L →ₗ[R] homSpace K M)
    (fun m ↦
      { toFun := fun g ↦ postcomposeHom g
        map_add' := by
          intro g₁ g₂
          apply DirectSum.linearMap_ext
          intro n
          ext f
          simpa [postcomposeHom, compHomLinear] using
            congrArg
              (DirectSum.lof R ℤ (fun i ↦ homDegree K M i) (n + m))
              (compHom_add_left g₁ g₂ f)
        map_smul' := by
          intro r g
          apply DirectSum.linearMap_ext
          intro n
          ext f
          simpa [postcomposeHom, compHomLinear] using
            congrArg
              (DirectSum.lof R ℤ (fun i ↦ homDegree K M i) (n + m))
              (compHom_smul_left r g f) })

/-- Composition in the graded Hom category is induced by graded composition on homogeneous pieces.
-/
def compSpace
    {K L M : RightModule 𝒜}
    (g : homSpace L M) (f : homSpace K L) :
    homSpace K M :=
  compLinear g f

@[simp] theorem compSpace_lof_lof
    {K L M : RightModule 𝒜} {m n : ℤ}
    (g : homDegree L M m)
    (f : homDegree K L n) :
    compSpace
        ((DirectSum.lof R ℤ (fun i ↦ homDegree L M i) m) g)
        ((DirectSum.lof R ℤ (fun i ↦ homDegree K L i) n) f) =
      (DirectSum.lof R ℤ (fun i ↦ homDegree K M i) (n + m)) (compHom g f) := by
  simp [compSpace, compLinear, postcomposeHom, compHomLinear]

@[simp] theorem compSpace_zero_left
    {K L M : RightModule 𝒜} (f : homSpace K L) :
    compSpace (0 : homSpace L M) f = 0 := by
  simpa [compSpace] using compLinear.map_zero f

@[simp] theorem compSpace_zero_right
    {K L M : RightModule 𝒜} (g : homSpace L M) :
    compSpace g (0 : homSpace K L) = 0 := by
  simpa [compSpace] using (compLinear g).map_zero

@[simp] theorem compSpace_add_left
    {K L M : RightModule 𝒜} (g₁ g₂ : homSpace L M) (f : homSpace K L) :
    compSpace (g₁ + g₂) f = compSpace g₁ f + compSpace g₂ f := by
  simpa [compSpace] using compLinear.map_add g₁ g₂ f

@[simp] theorem compSpace_add_right
    {K L M : RightModule 𝒜} (g : homSpace L M) (f₁ f₂ : homSpace K L) :
    compSpace g (f₁ + f₂) = compSpace g f₁ + compSpace g f₂ := by
  simpa [compSpace] using (compLinear g).map_add f₁ f₂

@[simp] theorem compSpace_smul_left
    {K L M : RightModule 𝒜} (r : R) (g : homSpace L M) (f : homSpace K L) :
    compSpace (r • g) f = r • compSpace g f := by
  simpa [compSpace] using compLinear.map_smul r g f

@[simp] theorem compSpace_smul_right
    {K L M : RightModule 𝒜} (r : R) (g : homSpace L M) (f : homSpace K L) :
    compSpace g (r • f) = r • compSpace g f := by
  simpa [compSpace] using (compLinear g).map_smul r f

/-- Helper for Example 22.25.6 (Graded category of graded modules): if a homogeneous term
transports along an equality of degrees, then the corresponding direct-sum generators coincide. -/
private theorem directSumLof_eq_of_transport
    {β : ℤ → Type*} [∀ i, AddCommMonoid (β i)] [∀ i, Module R (β i)]
    {i j : ℤ} (hij : i = j) (x : β i) (y : β j)
    (hxy : hij ▸ x = y) :
    DirectSum.lof R ℤ β i x = DirectSum.lof R ℤ β j y := by
  -- Proof comment: after eliminating the degree equality, both generators live in the same
  -- summand and ordinary congruence closes the goal.
  cases hij
  simpa [DirectSum.lof_eq_of] using congrArg (DirectSum.of β i) hxy

/-- Helper for Example 22.25.6 (Graded category of graded modules): transporting a homogeneous
map between degree pieces does not change its underlying right-`A`-linear map. -/
private theorem homDegree_cast_val
    {K L : RightModule 𝒜} {i j : ℤ} (hij : i = j) (f : homDegree K L i) :
    (((hij ▸ f : homDegree K L j) : K →ₗ[Aᵐᵒᵖ] L)) = f := by
  -- Proof comment: the degree equality only changes the proof of homogeneity, not the map.
  cases hij
  rfl

/-- Helper for Example 22.25.6 (Graded category of graded modules): composing a homogeneous
generator with the degree-`0` identity on the source leaves the direct-sum generator unchanged. -/
@[simp] private theorem compHom_idSource_lof
    {K L : RightModule 𝒜} {n : ℤ}
    (f : homDegree K L n) :
    DirectSum.lof R ℤ (fun i ↦ homDegree K L i) (0 + n) (compHom f (idHom K)) =
      DirectSum.lof R ℤ (fun i ↦ homDegree K L i) n f := by
  -- Proof comment: package the degree transport `0 + n = n` into the direct-sum owner.
  exact directSumLof_eq_of_transport (β := fun i ↦ homDegree K L i)
    (hij := zero_add n) _ _ (by
      apply Subtype.ext
      rw [homDegree_cast_val (K := K) (L := L) (hij := zero_add n) (f := compHom f (idHom K))]
      exact compHom_id_right f)

/-- Helper for Example 22.25.6 (Graded category of graded modules): composing a homogeneous
generator with the degree-`0` identity on the target leaves the direct-sum generator unchanged. -/
@[simp] private theorem compHom_idTarget_lof
    {K L : RightModule 𝒜} {n : ℤ}
    (f : homDegree K L n) :
    DirectSum.lof R ℤ (fun i ↦ homDegree K L i) (n + 0) (compHom (idHom L) f) =
      DirectSum.lof R ℤ (fun i ↦ homDegree K L i) n f := by
  -- Proof comment: package the degree transport `n + 0 = n` into the direct-sum owner.
  exact directSumLof_eq_of_transport (β := fun i ↦ homDegree K L i)
    (hij := add_zero n) _ _ (by
      apply Subtype.ext
      rw [homDegree_cast_val (K := K) (L := L) (hij := add_zero n) (f := compHom (idHom L) f)]
      exact compHom_id_left f)

/-- Helper for Example 22.25.6 (Graded category of graded modules): homogeneous composition is
associative on direct-sum generators after normalizing the total degree. -/
private theorem compHom_assoc_lof
    {J K L M : RightModule 𝒜} {l m n : ℤ}
    (h : homDegree L M l)
    (g : homDegree K L m)
    (f : homDegree J K n) :
    DirectSum.lof R ℤ (fun i ↦ homDegree J M i) ((n + m) + l) (compHom h (compHom g f)) =
      DirectSum.lof R ℤ (fun i ↦ homDegree J M i) (n + (m + l))
        (compHom (compHom h g) f) := by
  -- Proof comment: after transporting along `add_assoc`, the two homogeneous composites have the
  -- same underlying linear map by ordinary associativity of composition.
  exact directSumLof_eq_of_transport (β := fun i ↦ homDegree J M i)
    (hij := add_assoc n m l) _ _ (by
      apply Subtype.ext
      rw [homDegree_cast_val (K := J) (L := M) (hij := add_assoc n m l)
        (f := compHom h (compHom g f))]
      ext x
      rfl)

/-- Right graded modules form a category whose morphisms are finite sums of homogeneous maps. -/
instance instCategory : Category (RightModule 𝒜) where
  Hom L M := homSpace L M
  id := idSpace
  comp f g := compSpace g f
  id_comp := by
    intro K L f
    -- Proof comment: reduce left identity to homogeneous generators of the graded Hom direct sum.
    refine DirectSum.induction_on f ?_ ?_ ?_
    · simp
    · intro n φ
      -- Proof comment: on a single generator, the left identity law is the degree-transport
      -- normalization encoded in `compHom_idSource_lof`.
      simpa [DirectSum.lof_eq_of, idSpace] using
        (compSpace_lof_lof (g := φ) (f := idHom K)).trans
          (compHom_idSource_lof (𝒜 := 𝒜) (K := K) (L := L) (n := n) φ)
    · intro x y hx hy
      -- Proof comment: additivity in the outer composition slot propagates the induction step.
      simpa [compSpace_add_left, hx, hy]
  comp_id := by
    intro K L f
    -- Proof comment: reduce right identity to homogeneous generators of the graded Hom direct
    -- sum and use the target-identity generator lemma.
    refine DirectSum.induction_on f ?_ ?_ ?_
    · simp
    · intro n φ
      -- Proof comment: the generator case is exactly `compHom_idTarget_lof`.
      simpa [DirectSum.lof_eq_of, idSpace] using
        (compSpace_lof_lof (g := idHom L) (f := φ)).trans
          (compHom_idTarget_lof (𝒜 := 𝒜) (K := K) (L := L) (n := n) φ)
    · intro x y hx hy
      -- Proof comment: additivity in the inner composition slot propagates the induction step.
      simpa [compSpace_add_right, hx, hy]
  assoc := by
    intro J K L M f g h
    -- Proof comment: reduce associativity successively to homogeneous generators in each direct
    -- sum, then apply the generator-level associativity bridge.
    refine DirectSum.induction_on h ?_ ?_ ?_
    · simp
    · intro l χ
      refine DirectSum.induction_on g ?_ ?_ ?_
      · simp
      · intro m ψ
        refine DirectSum.induction_on f ?_ ?_ ?_
        · simp
        · intro n φ
          -- Proof comment: on triple generators, only the normalized homogeneous associativity
          -- statement remains.
          have hleft :
              compSpace (DirectSum.of (fun i ↦ homDegree L M i) l χ)
                  (compSpace (DirectSum.of (fun i ↦ homDegree K L i) m ψ)
                    (DirectSum.of (fun i ↦ homDegree J K i) n φ)) =
                DirectSum.of (fun i ↦ homDegree J M i) ((n + m) + l)
                  (compHom χ (compHom ψ φ)) := by
            calc
              compSpace (DirectSum.of (fun i ↦ homDegree L M i) l χ)
                  (compSpace (DirectSum.of (fun i ↦ homDegree K L i) m ψ)
                    (DirectSum.of (fun i ↦ homDegree J K i) n φ)) =
                compSpace (DirectSum.of (fun i ↦ homDegree L M i) l χ)
                  (DirectSum.of (fun i ↦ homDegree J L i) (n + m) (compHom ψ φ)) := by
                    simpa [DirectSum.lof_eq_of] using
                      congrArg (compSpace (DirectSum.of (fun i ↦ homDegree L M i) l χ))
                        (compSpace_lof_lof (g := ψ) (f := φ))
              _ = DirectSum.of (fun i ↦ homDegree J M i) ((n + m) + l)
                    (compHom χ (compHom ψ φ)) := by
                    simpa [DirectSum.lof_eq_of] using
                      (compSpace_lof_lof (g := χ) (f := compHom ψ φ))
          have hright :
              compSpace
                  (compSpace (DirectSum.of (fun i ↦ homDegree L M i) l χ)
                    (DirectSum.of (fun i ↦ homDegree K L i) m ψ))
                  (DirectSum.of (fun i ↦ homDegree J K i) n φ) =
                DirectSum.of (fun i ↦ homDegree J M i) (n + (m + l))
                  (compHom (compHom χ ψ) φ) := by
            calc
              compSpace
                  (compSpace (DirectSum.of (fun i ↦ homDegree L M i) l χ)
                    (DirectSum.of (fun i ↦ homDegree K L i) m ψ))
                  (DirectSum.of (fun i ↦ homDegree J K i) n φ) =
                compSpace (DirectSum.of (fun i ↦ homDegree K M i) (m + l) (compHom χ ψ))
                  (DirectSum.of (fun i ↦ homDegree J K i) n φ) := by
                    simpa [DirectSum.lof_eq_of] using
                      congrArg (fun z ↦ compSpace z (DirectSum.of (fun i ↦ homDegree J K i) n φ))
                        (compSpace_lof_lof (g := χ) (f := ψ))
              _ = DirectSum.of (fun i ↦ homDegree J M i) (n + (m + l))
                    (compHom (compHom χ ψ) φ) := by
                    simpa [DirectSum.lof_eq_of] using
                      (compSpace_lof_lof (g := compHom χ ψ) (f := φ))
          have hmid :
              DirectSum.of (fun i ↦ homDegree J M i) ((n + m) + l) (compHom χ (compHom ψ φ)) =
                DirectSum.of (fun i ↦ homDegree J M i) (n + (m + l))
                  (compHom (compHom χ ψ) φ) := by
            simpa [DirectSum.lof_eq_of] using
              compHom_assoc_lof (𝒜 := 𝒜) (J := J) (K := K) (L := L) (M := M)
                (l := l) (m := m) (n := n) χ ψ φ
          exact hleft.trans (hmid.trans hright.symm)
        · intro x y hx hy
          -- Proof comment: additivity in the innermost slot propagates the induction step.
          simpa [compSpace_add_right, hx, hy]
      · intro x y hx hy
        -- Proof comment: bilinearity handles additivity in the middle slot.
        simpa [compSpace_add_left, compSpace_add_right, hx, hy]
    · intro x y hx hy
      -- Proof comment: additivity in the outermost slot finishes the induction.
      simpa [compSpace_add_left, hx, hy]

instance instPreadditive : Preadditive (RightModule 𝒜) where
  homGroup L M := by
    change AddCommGroup (homSpace L M)
    infer_instance
  add_comp := by
    intro K L M f g h
    -- Proof comment: category composition is additive in its source-morphism slot.
    let f' : homSpace K L := f
    let g' : homSpace K L := g
    let h' : homSpace L M := h
    change compSpace h' (f' + g') = compSpace h' f' + compSpace h' g'
    simpa [compSpace] using
      ((compLinear : homSpace L M →ₗ[R] homSpace K L →ₗ[R] homSpace K M) h').map_add f' g'
  comp_add := by
    intro K L M f g h
    -- Proof comment: category composition is additive in its target-morphism slot.
    let f' : homSpace K L := f
    let g' : homSpace L M := g
    let h' : homSpace L M := h
    change compSpace (g' + h') f' = compSpace g' f' + compSpace h' f'
    simpa [compSpace] using
      ((compLinear : homSpace L M →ₗ[R] homSpace K L →ₗ[R] homSpace K M).map_add g' h' f')

instance instLinear : Linear R (RightModule 𝒜) where
  homModule L M := by
    change Module R (homSpace L M)
    infer_instance
  smul_comp := by
    intro K L M r f g
    -- Proof comment: scalar multiplication on the source morphism is handled by right-linearity
    -- of `compSpace`.
    let f' : homSpace K L := f
    let g' : homSpace L M := g
    change compSpace g' (r • f') = r • compSpace g' f'
    simpa [compSpace] using
      ((compLinear : homSpace L M →ₗ[R] homSpace K L →ₗ[R] homSpace K M) g').map_smul r f'
  comp_smul := by
    intro K L M f r g
    -- Proof comment: scalar multiplication on the target morphism is handled by left-linearity
    -- of `compSpace`.
    let f' : homSpace K L := f
    let g' : homSpace L M := g
    change compSpace (r • g') f' = r • compSpace g' f'
    simpa [compSpace] using
      ((compLinear : homSpace L M →ₗ[R] homSpace K L →ₗ[R] homSpace K M).map_smul r g' f')

/-- Example 22.25.6 (Graded category of graded modules): right graded modules over `𝒜` form a
graded category whose degree-`n` piece is the `n`-th homogeneous summand of the total graded Hom
module. -/
instance instGradedCategory : GradedCategory R (RightModule 𝒜) where
  homDegree := gradedHomDegree
  homDecomposition := instHomSpaceDecomposition
  id_mem_homDegree_zero := by
    intro L
    -- Proof comment: the identity is already the degree-`0` generator used to define `idSpace`.
    exact ⟨idHom L, rfl⟩
  comp_mem := by
    intro J K L i j f g hf hg
    -- Proof comment: unpack both graded-piece witnesses and repackage their homogeneous
    -- composite using `compSpace_lof_lof`.
    rcases hf with ⟨f', rfl⟩
    rcases hg with ⟨g', rfl⟩
    exact ⟨compHom g' f', (compSpace_lof_lof g' f').symm⟩

/- Example 22.25.6 (3): the ordinary category of right graded modules is the degree-`0`
subcategory of the ambient graded category of right graded modules. -/

private theorem hom_mem_gradedHomDegree_zero_preserves_grading
    {L M : RightModule 𝒜}
    (f : homSpace L M) (hf : f ∈ gradedHomDegree L M 0)
    {i : ℤ} {x : L} (hx : x ∈ L.grading i) :
    homToLinearMap L M f x ∈ M.grading i := by
  let g : homDegree L M 0 := (gradedHomDegreeEquiv L M 0).symm ⟨f, hf⟩
  have hg :
      ((DirectSum.lof R ℤ (fun n ↦ homDegree L M n) 0) g : homSpace L M) = f := by
    have hsub : gradedHomDegreeEquiv L M 0 g = ⟨f, hf⟩ := by
      simpa [g] using (gradedHomDegreeEquiv L M 0).apply_symm_apply ⟨f, hf⟩
    simpa [gradedHomDegreeEquiv_apply] using congrArg Subtype.val hsub
  have hlinear : (g : L →ₗ[Aᵐᵒᵖ] M) = homToLinearMap L M f := by
    simpa [homToLinearMap_lof] using congrArg (homToLinearMap L M) hg
  simpa [hlinear] using g.2 i x hx

/-- Degree-`0` morphisms in the degree-`0` subcategory of right graded modules preserve the
grading on right graded modules. -/
theorem degreeZero_hom_preserves_grading
    {L M : GradedCategory.DegreeZero (RightModule 𝒜)}
    (f : L ⟶ M) {i : ℤ} {x : L.obj} (hx : x ∈ L.obj.grading i) :
    homToLinearMap L.obj M.obj f.hom x ∈ M.obj.grading i := by
  exact hom_mem_gradedHomDegree_zero_preserves_grading f.hom
    (GradedCategory.DegreeZero.hom_mem_homDegree_zero f) hx

end RightModule

end GradedAlgebraBimodule

end

end CategoryTheory
