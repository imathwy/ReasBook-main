import Mathlib
import StacksProject_2024.stacks_project.Chap07.Definition_7_8_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Presheaf
open CategoryTheory.SemiRepresentableFamily.Over

universe v u

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable {F G : Cᵒᵖ ⥤ Type (max u v)} (η : F ⟶ G)

/- Domain-style sampling for Lemma 7.10.17:
- primary domain: Grothendieck-topology local bijectivity and sheafification for set-valued
  presheaves;
- sampled owner API:
  `Presheaf.IsLocallyInjective`,
  `Presheaf.IsLocallySurjective`,
  `GrothendieckTopology.W_iff_isLocallyBijective`,
  `GrothendieckTopology.W_iff`,
  `SemiRepresentableFamily.Over.toSieve`;
- source-facing layer: the covering-family hypothesis that `η` is componentwise bijective on some
  cover of each object;
- core/canonical owner: `J.W η`, equivalently the sheafification map of `η` is an isomorphism;
- bridge/view: the two local proofs turning the source-facing covering hypothesis into the
  canonical local injectivity and local surjectivity predicates.

Primitive data are only the explicit covering-family hypothesis:
for each `U`, a family `𝒰 : SemiRepresentableFamily.Over.{v, u, max u v} U` whose generated sieve
lies in `J U`, together with the componentwise bijectivity of `η.app (op (𝒰.obj i).left)`.
The local injective/surjective facts and the `J.W` conclusion are derived API and should not be
repackaged as a second owner.
-/

private theorem isLocallyInjective_of_cover_by_componentwise_bijective :
    (∀ U : C, ∃ 𝒰 : SemiRepresentableFamily.Over.{v, u, max u v} U,
      𝒰.toSieve ∈ J U ∧
        ∀ i, Function.Bijective (η.app (op (𝒰.obj i).left))) →
    IsLocallyInjective J η := by
  intro hcover
  refine ⟨fun {X} x y hxy ↦ ?_⟩
  obtain ⟨𝒰, h𝒰, hbij⟩ := hcover X.unop
  refine J.superset_covering ?_ h𝒰
  intro Y g hg
  change 𝒰.toSieve g at hg
  let i : 𝒰.index := Sieve.ofArrows.i hg
  let k : Y ⟶ (𝒰.obj i).left := Sieve.ofArrows.h hg
  have hk : k ≫ (𝒰.obj i).hom = g := by
    dsimp [i, k]
    exact Sieve.ofArrows.fac hg
  have hfg : F.map ((𝒰.obj i).hom).op x = F.map ((𝒰.obj i).hom).op y := by
    apply (hbij i).injective
    exact
      (FunctorToTypes.naturality _ _ η ((𝒰.obj i).hom).op x).trans <|
        (congrArg (G.map ((𝒰.obj i).hom).op) hxy).trans
          (FunctorToTypes.naturality _ _ η ((𝒰.obj i).hom).op y).symm
  dsimp [equalizerSieve]
  calc
    F.map g.op x
        = F.map k.op (F.map ((𝒰.obj i).hom).op x) := by
            rw [← hk]
            simp [op_comp]
    _ = F.map k.op (F.map ((𝒰.obj i).hom).op y) := by rw [hfg]
    _ = F.map g.op y := by
          rw [← hk]
          simp [op_comp]

private theorem isLocallySurjective_of_cover_by_componentwise_bijective :
    (∀ U : C, ∃ 𝒰 : SemiRepresentableFamily.Over.{v, u, max u v} U,
      𝒰.toSieve ∈ J U ∧
        ∀ i, Function.Bijective (η.app (op (𝒰.obj i).left))) →
    IsLocallySurjective J η := by
  intro hcover
  refine ⟨fun {U} s ↦ ?_⟩
  obtain ⟨𝒰, h𝒰, hbij⟩ := hcover U
  refine J.superset_covering ?_ h𝒰
  intro Y g hg
  change 𝒰.toSieve g at hg
  let i : 𝒰.index := Sieve.ofArrows.i hg
  let k : Y ⟶ (𝒰.obj i).left := Sieve.ofArrows.h hg
  have hk : k ≫ (𝒰.obj i).hom = g := by
    dsimp [i, k]
    exact Sieve.ofArrows.fac hg
  obtain ⟨t, ht⟩ := (hbij i).surjective (G.map ((𝒰.obj i).hom).op s)
  refine ⟨F.map k.op t, ?_⟩
  calc
    η.app (op Y) (F.map k.op t)
        = G.map k.op (η.app (op ((𝒰.obj i).left)) t) :=
          FunctorToTypes.naturality _ _ η _ t
    _ = G.map k.op (G.map ((𝒰.obj i).hom).op s) := by rw [ht]
    _ = G.map g.op s := by
          rw [← hk]
          simp [op_comp]

-- Proof sketch: the covering hypothesis makes `η` locally injective and locally surjective in
-- the canonical mathlib sense, so `η` belongs to `J.W`, i.e. it becomes an isomorphism after
-- sheafification.
/-- Lemma 7.10.17: if every object admits a covering by objects on which a morphism of set-valued
presheaves is componentwise bijective, then the morphism lies in `J.W`, equivalently it becomes an
isomorphism after sheafification. -/
theorem w_of_cover_by_componentwise_bijective
    (hcover :
      ∀ U : C, ∃ 𝒰 : SemiRepresentableFamily.Over.{v, u, max u v} U,
        𝒰.toSieve ∈ J U ∧
          ∀ i, Function.Bijective (η.app (op (𝒰.obj i).left))) :
    J.W η := by
  exact (J.W_iff_isLocallyBijective η).2
    ⟨isLocallyInjective_of_cover_by_componentwise_bijective J η hcover,
      isLocallySurjective_of_cover_by_componentwise_bijective J η hcover⟩
