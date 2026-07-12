import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

section

variable {R : Type u} [Ring R]
variable {P : Type v} [AddCommGroup P] [Module R P]
variable {Q : Type w} [AddCommMonoid Q] [Module R Q]
variable {F : Type x} [AddCommMonoid F] [Module R F]

/- Domain sampling:
- primary domain: infinitely generated free modules and absorption of direct summands;
- owner abstractions inspected upstream: `Module.Projective.iff_split`, `Module.Projective.of_split`,
  `LinearMap.inl`/`LinearMap.fst`, and `LinearEquiv.prodCongr`;
- source-facing layer: the complement-based hypothesis `(P × Q) ≃ₗ[R] F`;
- core/canonical layer: the retract data `i : P →ₗ[R] F`, `s : F →ₗ[R] P` with `s.comp i = id`;
- bridge/view below: recover that retract canonically from the given product equivalence. -/

/-- Helper for Lemma 15.129.1 (Eilenberg's lemma): a split retraction identifies `F` with the
product of `P` and the kernel of the retraction. -/
theorem split_linearEquiv_prod_ker
    (i : P →ₗ[R] F) (s : F →ₗ[R] P) (hs : s.comp i = LinearMap.id) :
    Nonempty (F ≃ₗ[R] (P × LinearMap.ker s)) := by
  letI : AddCommGroup F := Module.addCommMonoidToAddCommGroup R
  let g : P × LinearMap.ker s →ₗ[R] F := LinearMap.coprod i (LinearMap.ker s).subtype
  have hs_apply : ∀ p : P, s (i p) = p := by
    intro p
    have h := congrArg (fun t : P →ₗ[R] P => t p) hs
    simpa [LinearMap.comp_apply] using h
  have hg : Function.Bijective g := by
    constructor
    · intro x y hxy
      rcases x with ⟨px, kx⟩
      rcases y with ⟨py, ky⟩
      -- Applying the retraction kills the kernel terms and recovers the `P`-coordinate.
      have hfst : px = py := by
        have h := congrArg s hxy
        simpa [g, hs_apply, LinearMap.mem_ker.mp kx.property, LinearMap.mem_ker.mp ky.property]
          using h
      subst hfst
      -- After the `P`-coordinates match, add-cancellation identifies the kernel terms.
      have hsnd : (kx : F) = ky := by
        exact add_left_cancel hxy
      exact Prod.ext rfl (Subtype.ext hsnd)
    · intro x
      -- The inverse sends `x` to its image in `P` together with the kernel correction.
      refine ⟨(s x, ⟨x - i (s x), ?_⟩), ?_⟩
      · rw [LinearMap.mem_ker]
        simp [LinearMap.map_sub, hs_apply]
      · simp [g, sub_eq_add_neg, add_left_comm]
  refine ⟨(LinearEquiv.ofBijective g hg).symm⟩

variable [Module.Free R F]

/-- Helper for Lemma 15.129.1 (Eilenberg's lemma): non-finite generation of a free module forces
its chosen basis index type to be infinite. -/
theorem chooseBasisIndex_infinite_of_not_finite
    (hF : ¬ Module.Finite R F) :
    Infinite (Module.Free.ChooseBasisIndex R F) := by
  classical
  by_contra hι
  let b : Module.Basis (Module.Free.ChooseBasisIndex R F) R F := Module.Free.chooseBasis R F
  letI : Finite (Module.Free.ChooseBasisIndex R F) := Finite.of_not_infinite hι
  exact hF (Module.Finite.of_basis b)

/-- Helper for Lemma 15.129.1 (Eilenberg's lemma): an infinite type is equivalent to its product
with `ℕ`. -/
noncomputable def nat_prod_equiv_self_of_infinite {ι : Type*} [Infinite ι] :
    (ℕ × ι) ≃ ι := by
  have hcard : Cardinal.mk (ℕ × ι) = Cardinal.mk ι := by
    rw [Cardinal.mk_prod, Cardinal.mk_nat]
    simpa [mul_comm] using (Cardinal.mk_mul_aleph0_eq (α := ULift.{0} ι))
  exact Classical.choice (Cardinal.eq.mp hcard)

/-- Helper for Lemma 15.129.1 (Eilenberg's lemma): `Option ℕ` is equivalent to `ℕ` by reserving
`0` for `none` and shifting the remaining indices. -/
noncomputable def option_nat_equiv_nat : Option ℕ ≃ ℕ := by
  refine
    { toFun := fun o =>
        match o with
        | none => 0
        | some n => n + 1
      invFun := fun n =>
        match n with
        | 0 => none
        | m + 1 => some m
      left_inv := ?_
      right_inv := ?_ }
  · intro o
    cases o <;> rfl
  · intro n
    cases n <;> rfl

/-- Helper for Lemma 15.129.1 (Eilenberg's lemma): finitely supported functions on `Option α`
split into the distinguished coordinate together with the tail on `α`. -/
noncomputable def finsupp_option_linearEquiv {α : Type*} {M : Type*}
    [AddCommMonoid M] [Module R M] :
    (Option α →₀ M) ≃ₗ[R] (M × (α →₀ M)) := by
  let ePUnit : (PUnit.{1} →₀ M) ≃ₗ[R] M :=
    (Finsupp.linearEquivFunOnFinite R M PUnit.{1}).trans
      (LinearEquiv.funUnique PUnit.{1} R M)
  -- Reindex `Option α` as `α ⊕ PUnit`, split the sum support, and identify the `PUnit` part with
  -- the distinguished coefficient.
  exact
    (Finsupp.domLCongr (Equiv.optionEquivSumPUnit.{0} α)).trans
      ((Finsupp.sumFinsuppLEquivProdFinsupp (M := M) R).trans
        ((LinearEquiv.prodCongr (LinearEquiv.refl R (α →₀ M)) ePUnit).trans
          (LinearEquiv.prodComm R (α →₀ M) M)))

/-- Helper for Lemma 15.129.1 (Eilenberg's lemma): a finitely supported sequence splits into its
head term and the remaining tail sequence. -/
noncomputable def finsupp_nat_head_linearEquiv {M : Type*}
    [AddCommMonoid M] [Module R M] :
    (ℕ →₀ M) ≃ₗ[R] (M × (ℕ →₀ M)) := by
  -- Reindex by `Option ℕ ≃ ℕ`, then split off the `none` coordinate.
  exact
    (Finsupp.mapDomain.linearEquiv M R (option_nat_equiv_nat).symm).trans
      (finsupp_option_linearEquiv (R := R) (M := M))

/-- Helper for Lemma 15.129.1 (Eilenberg's lemma): finitely supported functions into a product
split pointwise into finitely supported functions into each factor. -/
noncomputable def finsupp_codomain_prod_linearEquiv {α : Type*} :
    (α →₀ (P × Q)) ≃ₗ[R] ((α →₀ P) × (α →₀ Q)) := by
  let toMap : (α →₀ (P × Q)) →ₗ[R] ((α →₀ P) × (α →₀ Q)) :=
    LinearMap.prod
      (Finsupp.mapRange.linearMap (LinearMap.fst R P Q))
      (Finsupp.mapRange.linearMap (LinearMap.snd R P Q))
  let invMap : ((α →₀ P) × (α →₀ Q)) →ₗ[R] (α →₀ (P × Q)) :=
    LinearMap.coprod
      (Finsupp.mapRange.linearMap (LinearMap.inl R P Q))
      (Finsupp.mapRange.linearMap (LinearMap.inr R P Q))
  -- Split each coordinate of the `Finsupp` into its `P` and `Q` entries, and reassemble them
  -- pointwise using the standard product inclusions.
  refine LinearEquiv.ofLinear toMap invMap ?_ ?_
  · apply LinearMap.ext
    intro fg
    rcases fg with ⟨f, g⟩
    refine Prod.ext ?_ ?_
    · ext a
      simp [toMap, invMap]
    · ext a
      simp [toMap, invMap]
  · apply LinearMap.ext
    intro f
    ext a <;> simp [toMap, invMap]

/-- Helper for Lemma 15.129.1 (Eilenberg's lemma): the countable copower of a free module with an
infinite basis is linearly equivalent to the original free module. -/
noncomputable def free_countable_copower_linearEquiv_self {ι : Type*} [Infinite ι] :
    (ℕ →₀ (ι →₀ R)) ≃ₗ[R] (ι →₀ R) := by
  -- Curry finitely supported functions on `ℕ × ι`, then reindex the infinite basis by
  -- `ℕ × ι ≃ ι`.
  exact
    (Finsupp.curryLinearEquiv R).symm.trans
      (Finsupp.domLCongr (nat_prod_equiv_self_of_infinite (ι := ι)))

/-- Helper for Lemma 15.129.1 (Eilenberg's lemma): countably many copies of `P × Q` absorb a
single extra copy of `P`. -/
noncomputable def finsupp_pair_swindle :
    (ℕ →₀ (P × Q)) ≃ₗ[R] (P × (ℕ →₀ (P × Q))) := by
  let eSplit : (ℕ →₀ (P × Q)) ≃ₗ[R] ((ℕ →₀ P) × (ℕ →₀ Q)) :=
    finsupp_codomain_prod_linearEquiv (R := R) (P := P) (Q := Q)
  let eHead : (ℕ →₀ P) ≃ₗ[R] (P × (ℕ →₀ P)) :=
    finsupp_nat_head_linearEquiv (R := R) (M := P)
  -- First split the countable family coordinatewise into a `P`-family and a `Q`-family, peel off
  -- the head `P`, and then reassemble the remaining countable product.
  exact
    eSplit.trans
      ((LinearEquiv.prodCongr eHead (LinearEquiv.refl R (ℕ →₀ Q))).trans
        ((LinearEquiv.prodAssoc R P (ℕ →₀ P) (ℕ →₀ Q)).trans
          (LinearEquiv.prodCongr (LinearEquiv.refl R P) eSplit.symm)))

/-- Canonical split-data form of Eilenberg absorption: a direct summand of a non-finitely generated
free module is absorbed by that free module. -/
theorem nonfinitely_generated_free_absorption_of_split
    (hF : ¬ Module.Finite R F) (i : P →ₗ[R] F) (s : F →ₗ[R] P)
    (hs : s.comp i = LinearMap.id) :
    Nonempty ((P × F) ≃ₗ[R] F) := by
  letI : AddCommGroup F := Module.addCommMonoidToAddCommGroup R
  let ι := Module.Free.ChooseBasisIndex R F
  let b : Module.Basis ι R F := Module.Free.chooseBasis R F
  letI : Infinite ι := chooseBasisIndex_infinite_of_not_finite (R := R) (F := F) hF
  obtain ⟨eSplit⟩ := split_linearEquiv_prod_ker (R := R) (P := P) (F := F) i s hs
  let eBasis : F ≃ₗ[R] (ι →₀ R) := b.repr
  let eCount : (ℕ →₀ F) ≃ₗ[R] F :=
    (Finsupp.mapRange.linearEquiv eBasis).trans
      ((free_countable_copower_linearEquiv_self (R := R) (ι := ι)).trans eBasis.symm)
  let eStart : (P × F) ≃ₗ[R] (P × (ℕ →₀ F)) :=
    LinearEquiv.prodCongr (LinearEquiv.refl R P) eCount.symm
  let eMiddle : (P × (ℕ →₀ F)) ≃ₗ[R] F :=
    (LinearEquiv.prodCongr
      (LinearEquiv.refl R P)
      (Finsupp.mapRange.linearEquiv eSplit)).trans
      ((finsupp_pair_swindle (R := R) (P := P) (Q := LinearMap.ker s)).symm.trans
        ((Finsupp.mapRange.linearEquiv eSplit.symm).trans eCount))
  -- Follow the source proof literally: replace `F` by a countable copower of itself, rewrite
  -- each copy using the split `F ≃ P × ker s`, peel off one `P`, and transport back.
  exact ⟨eStart.trans eMiddle⟩

-- Proof sketch: extract the canonical retract `P ↪ F ↠ P` from the chosen equivalence
-- `(P × Q) ≃ₗ[R] F`, then apply the split-data form above.
/-- Lemma 15.129.1 (Eilenberg's lemma): if `F` is a free `R`-module that is not finitely
generated and `P ⊕ Q ≅ F`, then `P ⊕ F ≅ F`; in Lean, the binary direct sums are modeled by the
product modules `P × Q` and `P × F`. -/
theorem prod_nonfinitely_generated_free_absorption
    (hF : ¬ Module.Finite R F) (e : (P × Q) ≃ₗ[R] F) :
    Nonempty ((P × F) ≃ₗ[R] F) := by
  let i : P →ₗ[R] F := e.toLinearMap ∘ₗ LinearMap.inl R P Q
  let s : F →ₗ[R] P := LinearMap.fst R P Q ∘ₗ e.symm.toLinearMap
  have hs : s.comp i = LinearMap.id := by
    ext p
    simp [i, s]
  simpa [i, s] using nonfinitely_generated_free_absorption_of_split hF i s hs

end
