import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u𝕜 uEG uHG uG uEH uHH uH

-- Semantic recall tool unavailable in this session; verified mathlib owners:
-- `ContMDiffMonoidMorphism` for smooth group homomorphisms and `Diffeomorph` for smooth
-- equivalences.

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH]
variable {HH : Type uHH} [TopologicalSpace HH]
variable {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {H : Type uH} [Group H] [TopologicalSpace H] [ChartedSpace HH H]

/- Definition 7.47-extra-1 (1): For Lie groups `G` and `H`, a Lie group homomorphism is exactly a
smooth group homomorphism; the canonical mathlib owner is
`ContMDiffMonoidMorphism I J ∞ G H`. -/
#check (ContMDiffMonoidMorphism I J ∞ G H)

namespace ContMDiffMonoidMorphism

variable {K : Type*} [Group K] [TopologicalSpace K]
variable {EK : Type*} [NormedAddCommGroup EK] [NormedSpace 𝕜 EK]
variable {HK : Type*} [TopologicalSpace HK]
variable {K' : ModelWithCorners 𝕜 EK HK}
variable [ChartedSpace HK K] {n : ℕ∞ω}

/-- The identity smooth group homomorphism. -/
def id : ContMDiffMonoidMorphism I I n G G where
  toMonoidHom := MonoidHom.id G
  contMDiff_toFun := contMDiff_id

@[simp] theorem id_apply (g : G) :
    (id : ContMDiffMonoidMorphism I I n G G) g = g :=
  rfl

/-- Composition of smooth group homomorphisms. -/
def comp (F₂ : ContMDiffMonoidMorphism J K' n H K)
    (F₁ : ContMDiffMonoidMorphism I J n G H) :
    ContMDiffMonoidMorphism I K' n G K where
  toMonoidHom := F₂.toMonoidHom.comp F₁.toMonoidHom
  contMDiff_toFun := F₂.contMDiff_toFun.comp F₁.contMDiff_toFun

@[simp] theorem comp_apply (F₂ : ContMDiffMonoidMorphism J K' n H K)
    (F₁ : ContMDiffMonoidMorphism I J n G H) (g : G) :
    F₂.comp F₁ g = F₂ (F₁ g) :=
  rfl

@[simp] theorem comp_id (F : ContMDiffMonoidMorphism I J n G H) :
    F.comp (id : ContMDiffMonoidMorphism I I n G G) = F := by
  apply DFunLike.ext
  intro g
  rfl

@[simp] theorem id_comp (F : ContMDiffMonoidMorphism I J n G H) :
    ((id : ContMDiffMonoidMorphism J J n H H)).comp F = F := by
  apply DFunLike.ext
  intro g
  rfl

end ContMDiffMonoidMorphism

/-- Definition 7.47-extra-1 (2): a Lie group isomorphism is a diffeomorphism whose underlying map
is a group homomorphism. -/
structure LieGroupIsomorphism
    (I : ModelWithCorners 𝕜 EG HG) (J : ModelWithCorners 𝕜 EH HH)
    (G : Type uG) [Group G] [TopologicalSpace G] [ChartedSpace HG G]
    (H : Type uH) [Group H] [TopologicalSpace H] [ChartedSpace HH H]
    extends G ≃ₘ⟮I, J⟯ H where
  map_mul' (g h : G) : toFun (g * h) = toFun g * toFun h

namespace LieGroupIsomorphism

/-- A Lie group isomorphism can be used as its underlying map. -/
instance : CoeFun (LieGroupIsomorphism I J G H) (fun _ ↦ G → H) where
  coe F := F.toDiffeomorph

/-- A Lie group isomorphism is multiplicative. -/
@[simp] theorem map_mul (F : LieGroupIsomorphism I J G H) (g h : G) :
    F (g * h) = F g * F h :=
  F.map_mul' g h

/-- Every Lie group isomorphism is a group isomorphism. -/
def toMulEquiv (F : LieGroupIsomorphism I J G H) : G ≃* H where
  toEquiv := F.toDiffeomorph.toEquiv
  map_mul' := F.map_mul'

/-- A Lie group isomorphism preserves the identity element. -/
@[simp] theorem map_one (F : LieGroupIsomorphism I J G H) : F (1 : G) = 1 := by
  have h := F.map_mul' (1 : G) 1
  simpa using h

/-- Every Lie group isomorphism is a smooth group homomorphism. -/
def toContMDiffMonoidMorphism (F : LieGroupIsomorphism I J G H) :
    ContMDiffMonoidMorphism I J ∞ G H where
  toMonoidHom := (toMulEquiv F).toMonoidHom
  contMDiff_toFun := F.toDiffeomorph.contMDiff_toFun

/-- The inverse of a Lie group isomorphism is again a Lie group isomorphism. -/
def symm (F : LieGroupIsomorphism I J G H) : LieGroupIsomorphism J I H G where
  toDiffeomorph := F.toDiffeomorph.symm
  map_mul' := by
    intro g h
    change F.toDiffeomorph.symm (g * h) = F.toDiffeomorph.symm g * F.toDiffeomorph.symm h
    exact (toMulEquiv F).symm.map_mul g h

/-- Every Lie group isomorphism is a continuous group isomorphism. -/
def toContinuousMulEquiv (F : LieGroupIsomorphism I J G H) : G ≃ₜ* H where
  toMulEquiv := toMulEquiv F
  continuous_toFun := F.toDiffeomorph.continuous
  continuous_invFun := by
    let Φ : G ≃ₘ⟮I, J⟯ H := F.toDiffeomorph
    simpa using Φ.symm.continuous

end LieGroupIsomorphism
