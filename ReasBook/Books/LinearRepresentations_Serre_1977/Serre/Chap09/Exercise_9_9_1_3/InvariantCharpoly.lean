import LinearRepresentations_Serre_1977.Serre.Chap09.Exercise_9_9_1_3.BaseChangeAndExteriorBasics

open scoped Representation

noncomputable section

universe u v w

namespace Representation

open PowerSeries

section

variable {k : Type} [Field k]
variable {G : Type u} [Monoid G]
variable {V : Type v}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem charpoly_eq_charpoly_restrict_mul_charpoly_mapQ
    (f : V →ₗ[k] V) (W : Submodule k V) (hW : W ≤ W.comap f) :
    f.charpoly = (f.restrict hW).charpoly * (W.mapQ W f hW).charpoly := by
  classical
  let m := Module.Free.ChooseBasisIndex k W
  let bW : Module.Basis m k W := Module.Free.chooseBasis k W
  let n := Module.Free.ChooseBasisIndex k (V ⧸ W)
  let bQ : Module.Basis n k (V ⧸ W) := Module.Free.chooseBasis k (V ⧸ W)
  let b := Module.Basis.sumQuot bW bQ
  let A : Matrix m m k := LinearMap.toMatrix bW bW (f.restrict hW)
  let B : Matrix m n k := Matrix.of fun i j ↦
    (b.repr (f (b (Sum.inr j)))) (Sum.inl i)
  let D : Matrix n n k := LinearMap.toMatrix bQ bQ (W.mapQ W f hW)
  have hmat : LinearMap.toMatrix b b f = Matrix.fromBlocks A B 0 D := by
    -- In the basis adapted to `W` and `V ⧸ W`, the matrix is block upper triangular.
    ext u v
    cases u with
    | inl i =>
        cases v with
        | inl j =>
            simp only [b, Module.Basis.sumQuot_inl, Matrix.fromBlocks_apply₁₁, A,
              LinearMap.toMatrix_apply]
            apply Module.Basis.sumQuot_repr_inl_of_mem
        | inr j =>
            simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
    | inr i =>
        cases v with
        | inl j =>
            suffices W.mkQ (f (bW j)) = 0 by
              simp [LinearMap.toMatrix_apply, b, this]
            rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
            exact hW (Submodule.coe_mem (bW j))
        | inr j =>
            simp only [LinearMap.toMatrix_apply, Module.Basis.sumQuot_repr_inr,
              Matrix.fromBlocks_apply₂₂, b, D]
            rw [← Module.Basis.sumQuot_inr bW bQ j, W.mapQ_apply]
            simp
  -- The block-upper-triangular matrix formula gives the desired factorization.
  rw [← LinearMap.charpoly_toMatrix f b, hmat, Matrix.charpoly_fromBlocks_zero₂₁,
    ← LinearMap.charpoly_toMatrix (f.restrict hW) bW,
    ← LinearMap.charpoly_toMatrix (W.mapQ W f hW) bQ]

end

end Representation
