import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_23.Theorem_4_14
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap07.Sec07_47.Theorem_7_5

-- Declarations for this item will be appended below by the statement pipeline.

-- Owner abstractions used here: `ContMDiffMonoidMorphism.hasConstantRank`,
-- `constant_rank_bijective_is_diffeomorphism`, `LieGroupIsomorphism`, and the canonical bridge
-- `LieGroupIsomorphism.toContMDiffMonoidMorphism`.

open scoped Manifold ContDiff

section LieGroupHomomorphisms

universe uG uH

variable {m n : ℕ}
variable {G : Type uG} [Group G] [TopologicalSpace G]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) G] [LieGroup (𝓡 m) ∞ G]
variable {H : Type uH} [Group H] [TopologicalSpace H]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) H] [LieGroup (𝓡 n) ∞ H]

namespace LieGroupIsomorphism

/-- A Lie group isomorphism is bijective as a smooth Lie group homomorphism. -/
theorem toContMDiffMonoidMorphism_bijective
    (F : LieGroupIsomorphism (𝓡 m) (𝓡 n) G H) :
    Function.Bijective F.toContMDiffMonoidMorphism :=
  ⟨F.toMulEquiv.injective, F.toMulEquiv.surjective⟩

end LieGroupIsomorphism

variable [T2Space G] [SecondCountableTopology G] [T2Space H] [SecondCountableTopology H]

/-- A bijective Lie group homomorphism comes from a Lie group isomorphism. -/
theorem exists_lieGroupIsomorphism_of_bijective
    (f : ContMDiffMonoidMorphism (𝓡 m) (𝓡 n) ∞ G H) (hf : Function.Bijective f) :
    ∃ F : LieGroupIsomorphism (𝓡 m) (𝓡 n) G H, F.toContMDiffMonoidMorphism = f := by
  rcases constant_rank_bijective_is_diffeomorphism
      f.contMDiff_toFun f.hasConstantRank hf with
    ⟨Φ, hΦ⟩
  refine ⟨{ toDiffeomorph := Φ, map_mul' := ?_ }, ?_⟩
  · intro g h
    calc
      Φ (g * h) = f (g * h) := hΦ _
      _ = f g * f h := f.map_mul g h
      _ = Φ g * Φ h := by
        exact congrArg₂ (fun x y ↦ x * y) (hΦ g).symm (hΦ h).symm
  · exact DFunLike.ext _ _ hΦ

/-- Corollary 7.6: A Lie group homomorphism is a Lie group isomorphism if and only if it is
bijective. -/
theorem exists_lie_group_isomorphism_iff_bijective
    (f : ContMDiffMonoidMorphism (𝓡 m) (𝓡 n) ∞ G H) :
    (∃ F : LieGroupIsomorphism (𝓡 m) (𝓡 n) G H, F.toContMDiffMonoidMorphism = f) ↔
      Function.Bijective f := by
  constructor
  · rintro ⟨F, rfl⟩
    exact F.toContMDiffMonoidMorphism_bijective
  · exact exists_lieGroupIsomorphism_of_bijective f

end LieGroupHomomorphisms
