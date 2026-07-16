import Mathlib
import StacksProject_2024.stacks_project.Chap23.Lemma_23_12_1

-- Declarations for this item will be appended below by the statement pipeline.

universe uR uK uA uι

section

variable {R : Type uR} [CommRing R]
variable {r : ℕ} {f : Fin r → R}

/- Semantic search note: `lean_leansearch` only returned the generic inverse-system owners from
`Mathlib.Order.DirectedInverseSystem`; local Chapter 23 precedent is the explicit approximation
owner from `Lemma_23_12_1`, so this file keeps the remark as a source-facing choice of a
strictly increasing approximation sequence rather than forcing a new categorical pro-object API. -/

/-- A source-facing choice of the Tate approximation sequence from Remark 23.12.2: a strictly
increasing sequence `1 = n₀ < n₁ < n₂ < ...` together with, for each `i`, a Tate approximation of
`K_(n_i)` whose larger stage is exactly `n_(i + 1)`. The maps recorded inside
`PoweredKoszulTateApproximation` are the data used in the remark to read off the commuting diagram
and the resulting pro-isomorphism witness. -/
structure PoweredKoszulTateApproximationSequence
    (ctx : PoweredKoszulApproximationContext.{uR, uK} f) where
  /-- The chosen strictly increasing subsequence `1 = n₀ < n₁ < n₂ < ...`. -/
  index : ℕ → ℕ
  /-- The sequence starts at the first Koszul stage. -/
  index_zero : index 0 = 1
  /-- The chosen stages are strictly increasing. -/
  index_strictMono : StrictMono index
  /-- The `i`th Tate approximation of the powered Koszul stage `K_(n_i)`. -/
  approx : ∀ i : ℕ, PoweredKoszulTateApproximation.{uR, uK, uA, uι} ctx (index i)
  /-- The larger Koszul stage attached to the `i`th approximation is the next chosen stage. -/
  next_stage : ∀ i : ℕ, (approx i).N = index (i + 1)

/-- A Tate approximation sequence can be used as its chosen index function `i ↦ n_i`. -/
instance
    (ctx : PoweredKoszulApproximationContext.{uR, uK} f) :
    CoeFun (PoweredKoszulTateApproximationSequence.{uR, uK, uA, uι} ctx) (fun _ ↦ ℕ → ℕ) where
  coe T := T.index

/-- The strict monotonicity of a Tate approximation sequence, viewed through the coercion
`T : ℕ → ℕ`. -/
abbrev PoweredKoszulTateApproximationSequence.indexStrictMono
    {ctx : PoweredKoszulApproximationContext.{uR, uK} f}
    (T : PoweredKoszulTateApproximationSequence.{uR, uK, uA, uι} ctx) :
    StrictMono T :=
  T.index_strictMono

/-- The `i`th intermediate differential graded algebra in a Tate approximation sequence. -/
abbrev PoweredKoszulTateApproximationSequence.approximationStage
    {ctx : PoweredKoszulApproximationContext.{uR, uK} f}
    (T : PoweredKoszulTateApproximationSequence.{uR, uK, uA, uι} ctx) (i : ℕ) :
    GradedDividedPowerDGAlgebra.{uR, uA} R :=
  (T.approx i).A

/-- The equality identifying the larger Koszul stage of the `i`th approximation with the next
chosen index `n_(i + 1)`. -/
abbrev PoweredKoszulTateApproximationSequence.nextStageEq
    {ctx : PoweredKoszulApproximationContext.{uR, uK} f}
    (T : PoweredKoszulTateApproximationSequence.{uR, uK, uA, uι} ctx) (i : ℕ) :
    (T.approx i).N = T (i + 1) :=
  T.next_stage i

/-- The map `K_(N_i) → A_i` supplied by the `i`th Tate approximation in the sequence; the
companion equality `T.nextStageEq i` identifies `N_i` with `n_(i + 1)`. -/
abbrev PoweredKoszulTateApproximationSequence.koszulToApproximation
    {ctx : PoweredKoszulApproximationContext.{uR, uK} f}
    (T : PoweredKoszulTateApproximationSequence.{uR, uK, uA, uι} ctx) (i : ℕ) :
    ctx.koszul ((T.approx i).N) →ₐ[R] T.approximationStage i :=
  (T.approx i).fromKoszul

/-- The map `A_i → K_(n_i)` supplied by the `i`th Tate approximation in the sequence. -/
abbrev PoweredKoszulTateApproximationSequence.approximationToKoszul
    {ctx : PoweredKoszulApproximationContext.{uR, uK} f}
    (T : PoweredKoszulTateApproximationSequence.{uR, uK, uA, uι} ctx) (i : ℕ) :
    GradedDividedPowerDGAlgebraHom R (T.approximationStage i) (ctx.koszul (T i)) :=
  (T.approx i).toKoszul

/-- In a Tate approximation sequence, the composite `K_(n_(i + 1)) → A_i → K_(n_i)` is the
canonical transition map in the powered Koszul tower. This is the basic commuting square used in
Remark 23.12.2. -/
theorem PoweredKoszulTateApproximationSequence.approximationToKoszul_comp_koszulToApproximation
    {ctx : PoweredKoszulApproximationContext.{uR, uK} f}
    (T : PoweredKoszulTateApproximationSequence.{uR, uK, uA, uι} ctx) (i : ℕ) :
    (T.approximationToKoszul i).toAlgHom.comp (T.koszulToApproximation i) =
      ctx.transitionAlgHom (T.approx i).hnN := sorry

/-- Remark 23.12.2: if `R` is Noetherian, then one can choose a strictly increasing sequence
`1 = n₀ < n₁ < n₂ < ...` and, for each `i`, a Tate approximation of `K_(n_i)` whose larger stage
is `n_(i + 1)`. The maps packaged by this sequence are exactly the source-facing data used in the
remark to build the commuting diagram
`K_(n_1) ← K_(n_2) ← K_(n_3) ← ...`,
`A_1 ← A_2 ← A_3 ← ...`,
`K_1 ← K_(n_1) ← K_(n_2) ← ...`
and hence to regard the powered Koszul tower and the Tate tower as pro-isomorphic. -/
theorem exists_poweredKoszulTateApproximationSequence
    [IsNoetherianRing R]
    (ctx : PoweredKoszulApproximationContext.{uR, uK} f) :
    Nonempty (PoweredKoszulTateApproximationSequence.{uR, uK, uA, uι} ctx) := sorry

end
