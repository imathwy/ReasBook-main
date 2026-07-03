import StacksProject_2024.Chap15.Lemma_15_96_8
import StacksProject_2024.Chap15.Lemma_15_96_4
import StacksProject_2024.Chap15.Lemma_15_97_5
import StacksProject_2024.Chap15.Lemma_15_97_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape
open BerthelotOgusEtaReduction.Nat
open scoped TensorProduct nonZeroDivisors

universe u

section

variable {A : Type u} [CommRing A]

attribute [local instance] HasDerivedCategory.standard

local notation "CpxA" => NatModuleCochainComplex A
local notation "Q" => natComplexToDerived

/- Domain-style sampling:
- primary domain: splitting loci in commutative algebra for the reduced Berthelot-Ogus pair map
  `(1, d^i)` on `η_f M^•`;
- sampled owner declarations:
  `LinearMap.identifiesWithProdSubmodules`,
  `LinearMap.baseChangeIdentifiesWithProdSubmodules`,
  `exists_fgIdeal_iff_baseChangeIdentifiesWithProdSubmodules_of_splitInjection`,
  `BerthelotOgusEtaReduction.Nat.etaReductionPairMap`;
- best owner abstraction:
  `source-facing`: the degree-`i` ideal `J_i(M^•, f)` attached to a bounded-above
    `M : NatModuleCochainComplex A`, available only under the principal-ideal and splitting
    hypotheses that produce it;
  `core/canonical`: the reduced pair map `etaReductionPairMap f M i` together with the generic
    owner predicate `LinearMap.baseChangeIdentifiesWithProdSubmodules`;
  `bridge/view`: the universal-property predicate on ideals of `A ⧸ principalIdeal f`, together
    with the conditional chosen witness obtained after existence and uniqueness are established;
- primitive data vs derived API: the primitive public data are the complex `M`, the degree `i`,
  and the reduced pair map; the universal-property predicate and the conditional canonical ideal are
  derived API on that owner. -/

namespace NatModuleCochainComplex

/-- An ideal of `A / fA` has the universal property of `J_i(M^\bullet, f)` if its quotient cuts
out exactly the base changes where the reduced map `(1, d^i)` splits as a product of submodules. -/
abbrev etaReductionDecompositionIdealProperty
    (M : CpxA) (f : A) (i : ℕ) (J : Ideal (A ⧸ principalIdeal f)) : Prop :=
  ∀ (B : Type*) [CommRing B] [Algebra (A ⧸ principalIdeal f) B],
    J ≤ RingHom.ker (algebraMap (A ⧸ principalIdeal f) B) ↔
      (etaReductionPairMap f M i).baseChangeIdentifiesWithProdSubmodules B

private abbrev etaReductionDecompositionIdealPropertySelf
    (M : CpxA) (f : A) (i : ℕ) (J : Ideal (A ⧸ principalIdeal f)) : Prop :=
  ∀ (B : Type u) [CommRing B] [Algebra (A ⧸ principalIdeal f) B],
    J ≤ RingHom.ker (algebraMap (A ⧸ principalIdeal f) B) ↔
      (etaReductionPairMap f M i).baseChangeIdentifiesWithProdSubmodules B

/-- The universal property of `J_i(M^\bullet, f)` determines the ideal uniquely whenever such an
ideal exists. -/
theorem etaReductionDecompositionIdeal_eq_of_property
    (M : CpxA) (f : A) (i : ℕ)
    {J J' : Ideal (A ⧸ principalIdeal f)}
    (hJ : M.etaReductionDecompositionIdealProperty f i J)
    (hJ' : M.etaReductionDecompositionIdealProperty f i J') :
    J = J' := sorry

-- Proof sketch: Lemma `15.97.5` makes the degree-`i` unreduced pair map `(1, d^i)` a split
-- monomorphism with finite projective source over `A ⧸ (f)`, and Lemma `15.97.7` then supplies
-- the finitely generated ideal cutting out exactly the base changes where the reduced map
-- identifies its source with a product of submodules.
/-- Under the principal-ideal hypothesis on `I_i(M^\bullet, f)`, there exists a finitely
generated ideal `J_i(M^\bullet, f)` in `A / fA` with the universal splitting property for the
reduced map `(1, d^i)`. -/
theorem exists_fg_etaReductionDecompositionIdeal_of_determinantalIdeal_isPrincipal
    (M : CpxA) (f : A) (i : ℕ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    ∃ J : Ideal (A ⧸ principalIdeal f),
      J.FG ∧ M.etaReductionDecompositionIdealProperty f i J := sorry

private theorem exists_fg_etaReductionDecompositionIdealSelf_of_determinantalIdeal_isPrincipal
    (M : CpxA) (f : A) (i : ℕ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    ∃ J : Ideal (A ⧸ principalIdeal f),
      J.FG ∧ etaReductionDecompositionIdealPropertySelf M f i J := sorry

/-- The degree-`i` ideal `J_i(M^\bullet, f)` in `A / fA`, defined only under the principal-ideal
hypothesis that guarantees its existence. -/
noncomputable def etaReductionDecompositionIdeal
    (M : CpxA) (f : A) (i : ℕ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    Ideal (A ⧸ principalIdeal f) :=
  Classical.choose
    (exists_fg_etaReductionDecompositionIdealSelf_of_determinantalIdeal_isPrincipal
      M f i hf hI)

/-- The ideal `J_i(M^\bullet, f)` satisfies its defining universal splitting property. -/
theorem etaReductionDecompositionIdeal_property
    (M : CpxA) (f : A) (i : ℕ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    M.etaReductionDecompositionIdealProperty f i
      (M.etaReductionDecompositionIdeal f i hf hI) := sorry

/-- The degree-`i` ideal `J_i(M^\bullet, f)` is finitely generated. -/
theorem etaReductionDecompositionIdeal_fg
    (M : CpxA) (f : A) (i : ℕ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    (M.etaReductionDecompositionIdeal f i hf hI).FG :=
  (Classical.choose_spec
    (exists_fg_etaReductionDecompositionIdealSelf_of_determinantalIdeal_isPrincipal
      M f i hf hI)).1

end NatModuleCochainComplex

namespace EtaReductionDecompositionIdeal

scoped notation "J[" f "]_(" i ")(" M " ; " hf ", " hI ")" =>
  NatModuleCochainComplex.etaReductionDecompositionIdeal M f i hf hI

end EtaReductionDecompositionIdeal

open scoped EtaReductionDecompositionIdeal

-- Proof sketch: apply Lemma `15.97.1` to the bounded-above extensions by zero of `M` and `N`.
-- After balancing the alternating-rank tails by suitable powers of `f`, the resulting equality
-- `f^m I_i(M^•, f) = f^n I_i(N^•, f)` and regularity of `f` show that principality of
-- `I_i(M^•, f)` forces principality of `I_i(N^•, f)`.
/-- The degree-`i` determinantal ideal is principal for `N^\bullet` as soon as it is principal for
`M^\bullet` and the two bounded-above finite free complexes represent the same derived object. This
is the bounded-below bridge/view of Lemma `15.97.1`, used below so that the source-facing equality
of the ideals `J_i` needs only the principality hypothesis on the `M`-side; the comparison
hypothesis stays on the chapter’s canonical theorem-level owner `CategoryTheory.IsIsomorphic`. -/
theorem etaDeterminantalIdeal_isPrincipal_of_same_derivedObject
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M N : CpxA)
    [∀ j : ℕ, Module.Free A (M.X j)] [∀ j : ℕ, Module.Finite A (M.X j)]
    [∀ j : ℕ, Module.Free A (N.X j)] [∀ j : ℕ, Module.Finite A (N.X j)]
    (hMbounded : M.IsBoundedAbove)
    (hNbounded : N.IsBoundedAbove)
    (hMN : IsIsomorphic ((Q).obj M) ((Q).obj N))
    (i : ℕ)
    (hIM : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    (N.etaDeterminantalIdeal f i).IsPrincipal := sorry

-- Proof sketch: use the principal-ideal hypothesis together with Lemma `15.97.5` to see that the
-- reduced maps attached to `M` and `N` are split injections of finite projective modules over
-- `A / fA`. Lemma `15.97.7` identifies the corresponding universal splitting loci, while the
-- derived equivalence transports the reduced `η_f` complexes and their degree-`i` maps. The
-- source-facing ideals with that universal property are therefore equal.
/-- If `M^\bullet` and `N^\bullet` represent the same derived object, then any degree-`i` ideals
of `A / fA` satisfying the universal property of `J_i(M^\bullet, f)` and `J_i(N^\bullet, f)`
agree; the derived comparison is expressed through `CategoryTheory.IsIsomorphic`, not through a
chosen `Iso`. -/
theorem etaReductionDecompositionIdeal_eq_of_same_derivedObject_of_property
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M N : CpxA)
    [∀ j : ℕ, Module.Free A (M.X j)] [∀ j : ℕ, Module.Finite A (M.X j)]
    [∀ j : ℕ, Module.Free A (N.X j)] [∀ j : ℕ, Module.Finite A (N.X j)]
    (hMbounded : M.IsBoundedAbove)
    (hNbounded : N.IsBoundedAbove)
    (hMN : IsIsomorphic ((Q).obj M) ((Q).obj N))
    (i : ℕ)
    {JM JN : Ideal (A ⧸ principalIdeal f)}
    (hJM : M.etaReductionDecompositionIdealProperty f i JM)
    (hJN : N.etaReductionDecompositionIdealProperty f i JN) :
    JM = JN := sorry

-- Proof sketch: apply the preceding witness-equality theorem to the canonical ideals
-- `J_i(M^\bullet, f)` and `J_i(N^\bullet, f)`, using their defining universal properties from the
-- existence-and-uniqueness construction above. The principality hypothesis needed to define the
-- `N`-side ideal is derived internally from Lemma `15.97.1` via the bridge theorem just above.
/-- Lemma 15.97.8: if `f` is a nonzerodivisor in `A` and `M^\bullet`, `N^\bullet` are bounded
complexes of finite free `A`-modules representing the same derived object, then the canonical
degree-`i` ideals `J_i(M^\bullet, f)` and `J_i(N^\bullet, f)` of `A / fA` are equal whenever the
degree-`i` determinantal ideal for `M^\bullet` is principal; the corresponding principality for
`N^\bullet` follows from Lemma `15.97.1`. -/
theorem etaReductionDecompositionIdeal_eq_of_same_derivedObject
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (M N : CpxA)
    [∀ j : ℕ, Module.Free A (M.X j)] [∀ j : ℕ, Module.Finite A (M.X j)]
    [∀ j : ℕ, Module.Free A (N.X j)] [∀ j : ℕ, Module.Finite A (N.X j)]
    (hMbounded : M.IsBoundedAbove)
    (hNbounded : N.IsBoundedAbove)
    (hMN : IsIsomorphic ((Q).obj M) ((Q).obj N))
    (i : ℕ)
    (hIM : (M.etaDeterminantalIdeal f i).IsPrincipal) :
    J[f]_(i)(M ; hf, hIM) =
      J[f]_(i)(N ; hf,
        etaDeterminantalIdeal_isPrincipal_of_same_derivedObject
          f hf M N hMbounded hNbounded hMN i hIM) := sorry

end
