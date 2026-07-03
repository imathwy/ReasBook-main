import Mathlib
import LinearRepresentations_Serre_1977.Chap11.Theorem_11_11_2_1
import LinearRepresentations_Serre_1977.RepresentationTheory.SymmetricExterior

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

theorem trace_eq_trace_restrict_add_trace_mapQ
    (f : V →ₗ[k] V) (W : Submodule k V) (hW : W ≤ W.comap f) :
    LinearMap.trace k V f =
      LinearMap.trace k W (f.restrict hW) +
        LinearMap.trace k (V ⧸ W) (W.mapQ W f hW) := by
  classical
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl W
  let e : (W × Q) ≃ₗ[k] V := W.prodEquivOfIsCompl Q hQ
  let qEquiv : (V ⧸ W) ≃ₗ[k] Q := W.quotientEquivOfIsCompl Q hQ
  let qBlock : Q →ₗ[k] Q := Q.linearProjOfIsCompl W hQ.symm ∘ₗ f ∘ₗ Q.subtype
  let cross : Q →ₗ[k] W :=
    LinearMap.fst k W Q ∘ₗ (e.symm.conj f) ∘ₗ LinearMap.inr k W Q
  let offdiag : (W × Q) →ₗ[k] (W × Q) :=
    LinearMap.inl k W Q ∘ₗ cross ∘ₗ LinearMap.snd k W Q
  let block : (W × Q) →ₗ[k] (W × Q) := LinearMap.prodMap (f.restrict hW) qBlock
  have hq : ∀ q : Q,
      (Submodule.Quotient.mk ((qBlock q : Q) : V) : V ⧸ W) =
        Submodule.Quotient.mk (f (q : V)) := by
    intro q
    -- The quotient only remembers the `Q`-component modulo the `W`-component.
    rw [Submodule.Quotient.eq']
    have hEq :
        -((Submodule.IsCompl.projection hQ.symm) (f q)) + f q =
          (Submodule.IsCompl.projection hQ) (f q) := by
      rw [Submodule.IsCompl.projection_eq_self_sub_projection hQ]
      abel
    suffices
        -((Submodule.IsCompl.projection hQ.symm) (f q)) + f q ∈ W by
      simpa [qBlock]
    rw [hEq]
    exact (Submodule.IsCompl.projection_apply_mem hQ) (f q)
  have hqBlock : qBlock = qEquiv.conj (W.mapQ W f hW) := by
    ext q
    -- Transport the quotient action across the chosen complement equivalence.
    exact congrArg (fun x : Q => (x : V)) <| by
      apply qEquiv.symm.injective
      simpa [LinearEquiv.conj_apply_apply] using hq q
  have hleft : ∀ w : W, e.symm.conj f (w, 0) = block (w, 0) := by
    intro w
    have hwmem : f (w : V) ∈ W := hW w.2
    -- On the stable summand `W`, the conjugated map is exactly the restricted action.
    ext <;> simp [LinearEquiv.symm_conj_apply, e, block, qBlock, hwmem]
  have hright : ∀ q : Q, e.symm.conj f (0, q) = offdiag (0, q) + block (0, q) := by
    intro q
    -- On the complement `Q`, the conjugated map splits into the quotient block and an upper-right
    -- correction term landing in `W`.
    ext <;> simp [LinearEquiv.symm_conj_apply, e, block, offdiag, cross, qBlock]
  have hsplit : e.symm.conj f = block + offdiag := by
    -- Every vector in `W × Q` is the sum of its `W`-part and `Q`-part, so the two previous
    -- computations determine the full conjugated operator.
    apply LinearMap.ext
    intro x
    rcases x with ⟨w, q⟩
    have hpair : (w, q) = (w, 0) + (0, q) := by
      ext <;> simp
    have hblock_split : block (w, q) = block (w, 0) + block (0, q) := by
      rw [hpair, map_add]
    have hoffdiag_eq : offdiag (w, q) = offdiag (0, q) := by
      ext <;> simp [offdiag, cross]
    calc
      e.symm.conj f (w, q) = e.symm.conj f (w, 0) + e.symm.conj f (0, q) := by
        rw [hpair, map_add]
      _ = block (w, 0) + (offdiag (0, q) + block (0, q)) := by
        rw [hleft, hright]
      _ = block (w, q) + offdiag (w, q) := by
        rw [hblock_split, hoffdiag_eq]
        abel
      _ = (block + offdiag) (w, q) := rfl
  have hsq : offdiag * offdiag = 0 := by
    -- The off-diagonal operator lands in `W × 0`, so a second application vanishes.
    apply LinearMap.ext
    intro x
    rcases x with ⟨w, q⟩
    have hoff : offdiag (w, q) = (cross q, 0) := by
      ext <;> simp [offdiag, cross]
    rw [show (offdiag * offdiag) (w, q) = offdiag (offdiag (w, q)) by rfl, hoff]
    simp [offdiag]
  have hnil : IsNilpotent offdiag := by
    refine ⟨2, ?_⟩
    simpa [pow_two] using hsq
  have htr_block :
      LinearMap.trace k (W × Q) block =
        LinearMap.trace k W (f.restrict hW) + LinearMap.trace k Q qBlock := by
    simpa [block] using LinearMap.trace_prodMap' (f.restrict hW) qBlock
  have htr_q :
      LinearMap.trace k Q qBlock = LinearMap.trace k (V ⧸ W) (W.mapQ W f hW) := by
    rw [hqBlock]
    simpa using (LinearMap.trace_conj' (W.mapQ W f hW) qEquiv)
  have htr_off : LinearMap.trace k (W × Q) offdiag = 0 := by
    -- A square-zero endomorphism has nilpotent trace, hence zero over a field.
    exact IsNilpotent.eq_zero <|
      LinearMap.isNilpotent_trace_of_isNilpotent (R := k) (M := W × Q) hnil
  -- Conjugation transfers the trace computation back to the original endomorphism.
  calc
    LinearMap.trace k V f = LinearMap.trace k (W × Q) (e.symm.conj f) := by
      simpa [e] using (LinearMap.trace_conj' f e.symm)
    _ = LinearMap.trace k (W × Q) block + LinearMap.trace k (W × Q) offdiag := by
      rw [hsplit, map_add]
    _ = LinearMap.trace k W (f.restrict hW) + LinearMap.trace k Q qBlock := by
      rw [htr_block, htr_off, add_zero]
    _ = LinearMap.trace k W (f.restrict hW) + LinearMap.trace k (V ⧸ W) (W.mapQ W f hW) := by
      rw [htr_q]

end

end Representation
