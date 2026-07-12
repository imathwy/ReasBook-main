import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (k : Type u) [Field k]

/- The canonical subextension `perfectClosure k (AlgebraicClosure k)` of an algebraic closure is
purely inseparable over `k`. -/
recall perfectClosure.isPurelyInseparable

/- The canonical subextension `perfectClosure k (AlgebraicClosure k)` is a perfect field. -/
recall perfectClosure.perfectField

-- Proof sketch: the canonical field `perfectClosure k (AlgebraicClosure k)` is a perfect closure
-- of `k`, and any perfect purely inseparable extension of `k` is also a perfect closure in the
-- sense of `IsPerfectClosure`. Existence of the `k`-algebra isomorphism comes from the owner
-- equivalence `IsPerfectClosure.equiv`, while uniqueness follows from the uniqueness of lifts from
-- a purely inseparable extension into a reduced `k`-algebra.

/-- Lemma 10.45.4: any perfect purely inseparable extension of `k` is uniquely `k`-isomorphic
to the canonical perfect closure `perfectClosure k (AlgebraicClosure k)`. -/
theorem perfectClosure_algebraicClosure_existsUnique_algEquiv
    (k' : Type v) [Field k'] [Algebra k k'] [PerfectField k'] [IsPurelyInseparable k k'] :
    ∃ e : perfectClosure k (AlgebraicClosure k) ≃ₐ[k] k', ∀ e', e' = e := by
  let p := ringExpChar k
  let kperf := perfectClosure k (AlgebraicClosure k)
  letI : ExpChar k' p := expChar_of_injective_algebraMap (algebraMap k k').injective p
  let e : kperf ≃ₐ[k] k' :=
    { IsPerfectClosure.equiv (algebraMap k kperf) (algebraMap k k') p with
      commutes' := IsPerfectClosure.equiv_comp_apply
        (algebraMap k kperf) (algebraMap k k') p }
  refine ⟨e, ?_⟩
  intro e'
  exact AlgEquiv.ext fun x ↦ DFunLike.congr_fun (Subsingleton.elim e'.toAlgHom e.toAlgHom) x

end
