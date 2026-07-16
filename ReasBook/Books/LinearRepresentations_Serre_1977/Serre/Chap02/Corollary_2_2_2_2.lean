import LinearRepresentations_Serre_1977.Serre.Chap02.Proposition_2_2_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
noncomputable section

universe u v w u₁ u₂

namespace Representation

section

variable {k : Type*} [Field k]
variable {G : Type u} [Group G] [Fintype G]
variable [Invertible (Fintype.card G : k)]
variable {V1 : Type v} [AddCommGroup V1] [Module k V1]
variable {V2 : Type w} [AddCommGroup V2] [Module k V2]
variable {ι1 : Type u₁} [Fintype ι1]
variable {ι2 : Type u₂} [Fintype ι2]

/- Layer triage for Corollary 2-2.2-2 (1):
* core/canonical: the owner abstractions are `(ρ1.linHom ρ2).averageMap`,
  `invariantsEquivIntertwiningMap`, and `IntertwiningMap`.
* source-facing: the averaged conjugates of an arbitrary linear map vanish under irreducibility
  and nonisomorphism.
* bridge/view: the basis-entry formula below is only a coordinate expression of the canonical
  averaged intertwiner. -/
-- Proof sketch: `(ρ1.linHom ρ2).averageMap h` is invariant in `ρ1.linHom ρ2`, hence
-- `invariantsEquivIntertwiningMap` turns it into an intertwining map. Under irreducibility and
-- nonisomorphism, the owner instance `Subsingleton (IntertwiningMap ρ1 ρ2)` forces that map to
-- vanish.
/-- Corollary 2-2.2-2 (1): if `ρ1` and `ρ2` are nonisomorphic irreducible representations over a
field in which `|G|` is invertible, then the average of the conjugates of any linear map
`h : V1 →ₗ[k] V2` is zero. -/
theorem averageMap_linHom_eq_zero_of_not_isomorphic
    (ρ1 : Representation k G V1) (ρ2 : Representation k G V2)
    [ρ1.IsIrreducible] [ρ2.IsIrreducible]
    (h : V1 →ₗ[k] V2) (hρ : ¬ Nonempty (ρ1.Equiv ρ2)) :
    (ρ1.linHom ρ2).averageMap h = 0 := by
  have hinter :
      ρ1.invariantsEquivIntertwiningMap ρ2
          ⟨(ρ1.linHom ρ2).averageMap h, (ρ1.linHom ρ2).averageMap_invariant h⟩ = 0 := by
    exact intertwiningMap_eq_zero_of_not_isomorphic ρ1 ρ2 _ hρ
  simpa using congrArg IntertwiningMap.toLinearMap hinter

/- Bridge/view from the canonical averaged intertwiner to the source-facing matrix-coefficient
formula: this computes the matrix entry of the averaged canonical basis vector
`b1.linearMap b2 (j2, j1)` of `V1 →ₗ[k] V2`. -/
open scoped Classical in
/-- The `(i2, i1)` matrix entry of the averaged basis map `b1.linearMap b2 (j2, j1)` is the
normalized sum of the corresponding matrix-coefficient products. -/
theorem averageMap_linHom_basis_entry_eq
    (ρ1 : Representation k G V1) (ρ2 : Representation k G V2)
    (b1 : Module.Basis ι1 k V1) (b2 : Module.Basis ι2 k V2)
    (i1 j1 : ι1) (i2 j2 : ι2) :
    (((ρ1.linHom ρ2).averageMap (b1.linearMap b2 (j2, j1))).toMatrix b1 b2 i2 i1) =
      (Fintype.card G : k)⁻¹ *
        ∑ t : G, (ρ2 t⁻¹).toMatrix b2 b2 i2 j2 * (ρ1 t).toMatrix b1 b1 j1 i1 := by
  let τ : Representation k G (V1 →ₗ[k] V2) := ρ1.linHom ρ2
  let e : V1 →ₗ[k] V2 := b1.linearMap b2 (j2, j1)
  have he_apply (x : V1) : e x = (b1.repr x j1) • b2 j2 := by
    dsimp [e]
    rw [← b1.sum_repr x, map_sum]
    simp [Module.Basis.linearMap_apply_apply]
  have havg_apply :
      (τ.averageMap e) (b1 i1) =
        (Fintype.card G : k)⁻¹ •
          ∑ d : G, ((τ.asAlgebraHom (MonoidAlgebra.of k G d)) e) (b1 i1) := by
    rw [averageMap, GroupAlgebra.average, map_smul, map_sum]
    simp [LinearMap.smul_apply, LinearMap.sum_apply, invOf_eq_inv]
  have hentry_fun :
      b2.repr ((τ.averageMap e) (b1 i1)) =
        (Fintype.card G : k)⁻¹ •
          ∑ d : G,
            b2.repr (((τ.asAlgebraHom (MonoidAlgebra.of k G d)) e) (b1 i1)) := by
    simpa [map_smul, map_sum] using congrArg b2.repr havg_apply
  have hentry :
      ((τ.averageMap e).toMatrix b1 b2 i2 i1) =
        (Fintype.card G : k)⁻¹ *
          ∑ d : G,
            b2.repr (((τ.asAlgebraHom (MonoidAlgebra.of k G d)) e) (b1 i1)) i2 := by
    rw [LinearMap.toMatrix_apply]
    simpa using congrArg (fun f ↦ f i2) hentry_fun
  have hsum_terms :
      ∑ d : G, (ρ2 d).toMatrix b2 b2 i2 j2 * (ρ1 d⁻¹).toMatrix b1 b1 j1 i1 =
        ∑ d : G,
          b2.repr (((τ.asAlgebraHom (MonoidAlgebra.of k G d)) e) (b1 i1)) i2 := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [asAlgebraHom_of, linHom_apply, LinearMap.comp_apply, LinearMap.comp_apply, he_apply,
      LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
    simp [map_smul, mul_comm]
  have hreindex :
      ∑ t : G, (ρ2 t⁻¹).toMatrix b2 b2 i2 j2 * (ρ1 t).toMatrix b1 b1 j1 i1 =
        ∑ t : G, (ρ2 t).toMatrix b2 b2 i2 j2 * (ρ1 t⁻¹).toMatrix b1 b1 j1 i1 := by
    simpa [inv_inv] using
      (Equiv.sum_comp (Equiv.inv G)
        (fun t : G ↦ (ρ2 t⁻¹).toMatrix b2 b2 i2 j2 * (ρ1 t).toMatrix b1 b1 j1 i1)).symm
  calc
    ((ρ1.linHom ρ2).averageMap (b1.linearMap b2 (j2, j1))).toMatrix b1 b2 i2 i1
      = (Fintype.card G : k)⁻¹ *
          ∑ d : G, b2.repr (((τ.asAlgebraHom (MonoidAlgebra.of k G d)) e) (b1 i1)) i2 := by
            simpa [τ, e] using hentry
    _ = (Fintype.card G : k)⁻¹ *
          ∑ d : G, (ρ2 d).toMatrix b2 b2 i2 j2 * (ρ1 d⁻¹).toMatrix b1 b1 j1 i1 := by
            rw [← hsum_terms]
    _ = (Fintype.card G : k)⁻¹ *
          ∑ t : G, (ρ2 t⁻¹).toMatrix b2 b2 i2 j2 * (ρ1 t).toMatrix b1 b1 j1 i1 := by
            rw [← hreindex]

end

section

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Type u} [Group G] [Fintype G]
variable [Invertible (Fintype.card G : k)]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [Invertible (Module.finrank k V : k)]

/- Layer triage for Corollary 2-2.2-2 (2):
* core/canonical: `IntertwiningMap ρ ρ`, the averaged projector `(ρ.linHom ρ).averageMap`, and
  Schur's lemma in Proposition `2-2.2-1`.
* source-facing: the average of the conjugates of `h` is the scalar homothety with ratio
  `(1 / dim V) * Tr(h)`.
* bridge/view: the proof identifies the scalar through the canonical trace invariance under
  conjugation. -/
-- Proof sketch: send `(ρ.linHom ρ).averageMap h` through
-- `invariantsEquivIntertwiningMap` to obtain an equivariant endomorphism, apply Proposition
-- `2-2.2-1 (2)` to see it is scalar, then identify that scalar by comparing traces, using trace
-- invariance under conjugation, and dividing by `dim V`.
/-- Corollary 2-2.2-2 (2): for an irreducible finite-dimensional representation over an
algebraically closed field in which `|G|` and `dim V` are invertible, the average of the
conjugates of an endomorphism is the homothety of ratio `(1 / n) Tr(h)`, where `n = dim V`. -/
theorem averageMap_linHom_self_eq_trace_smul_id
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (h : V →ₗ[k] V) :
    (ρ.linHom ρ).averageMap h =
      ((Module.finrank k V : k)⁻¹ * LinearMap.trace k V h) • LinearMap.id := by
  let τ : Representation k G (V →ₗ[k] V) := ρ.linHom ρ
  obtain ⟨c, hc⟩ := intertwiningMap_eq_smul_id ρ
    (ρ.invariantsEquivIntertwiningMap ρ ⟨τ.averageMap h, τ.averageMap_invariant h⟩)
  have havg : τ.averageMap h = c • LinearMap.id := by
    simpa [τ] using congrArg IntertwiningMap.toLinearMap hc
  have htrace_conj (g : G) :
      LinearMap.trace k V ((τ.asAlgebraHom (MonoidAlgebra.of k G g)) h) =
        LinearMap.trace k V h := by
    let u : (V →ₗ[k] V)ˣ :=
      { val := ρ g
        inv := ρ g⁻¹
        val_inv := by simpa using (ρ.map_mul g g⁻¹).symm
        inv_val := by simpa using (ρ.map_mul g⁻¹ g).symm }
    simpa [u, asAlgebraHom_of, linHom_apply, mul_assoc] using
      (LinearMap.trace_conj k h u)
  have htrace_avg :
      LinearMap.trace k V (τ.averageMap h) = LinearMap.trace k V h := by
    rw [averageMap, GroupAlgebra.average, map_smul, map_sum,
      LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
    simp_rw [htrace_conj]
    rw [Finset.sum_const, Finset.card_univ]
    simpa [smul_eq_mul, mul_assoc] using
      (invOf_mul_cancel_left (Fintype.card G : k) (LinearMap.trace k V h))
  have hc_trace : c * (Module.finrank k V : k) = LinearMap.trace k V h := by
    calc
      c * (Module.finrank k V : k) = LinearMap.trace k V (c • (LinearMap.id : V →ₗ[k] V)) := by
        simp [LinearMap.trace_id, smul_eq_mul]
      _ = LinearMap.trace k V (τ.averageMap h) := by rw [havg]
      _ = LinearMap.trace k V h := htrace_avg
  calc
    (ρ.linHom ρ).averageMap h = c • LinearMap.id := by simpa [τ] using havg
    _ = ((Module.finrank k V : k)⁻¹ * LinearMap.trace k V h) • LinearMap.id := by
          congr 1
          calc
            c = ⅟(Module.finrank k V : k) * ((Module.finrank k V : k) * c) := by
                  symm
                  exact invOf_mul_cancel_left (Module.finrank k V : k) c
            _ = (Module.finrank k V : k)⁻¹ * LinearMap.trace k V h := by
                  rw [mul_comm (Module.finrank k V : k) c, hc_trace, invOf_eq_inv]

end

end Representation
