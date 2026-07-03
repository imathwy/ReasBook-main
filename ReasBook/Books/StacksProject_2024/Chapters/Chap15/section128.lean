import Mathlib
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.Away

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_128_2 (from Chap15) -/
open scoped TensorProduct
open scoped ClosedPointFiber

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-
Domain triage:
- primary domain: fibrewise linear algebra on the quotient fibre `M(x) = M / xM` at a closed point;
- owner declarations sampled for this file:
  `closedPointFiber`,
  `LocalizedModule.Away`,
  `LocalizedModule.map`,
  `closedPointFiberVisibleQuotient`,
  `closedPointFiberVisibleClass`;
- source-facing layer: the localized splitting-after-inverting predicate from the source statement,
  expressed against the chapter owner `V(x)` for the visible quotient of the fibre;
- core/canonical layer: the owner localization map `LocalizedModule.map` and the visible quotient
  owner declarations imported from `Situation_15_128_1`;
- bridge/view: the free localized source `LocalizedModule.Away f (Fin r → R)` is canonically a
  finite free `Localization.Away f`-module, but the source predicate is best phrased as a left
  inverse to the localized owner map rather than through a tensor-product presentation;
- primitive data: the closed point `x`, the chosen sections `s`, and the localization parameter
  `f`;
- derived API: the visible classes supplied by the chapter owner file and the localized splitting
  predicate below.
-/

local notation "Ω" => closedPoints (PrimeSpectrum R)

/-- The `R`-linear map sending the standard basis of `R^r` to the chosen sections. -/
private noncomputable abbrev selectedSectionsMap {r : ℕ} (s : Fin r → M) : (Fin r → R) →ₗ[R] M :=
  (Pi.basisFun R (Fin r)).constr R s

/-- The textbook condition that the sections `s₁, …, s_r` become the inclusion of a direct summand
after inverting some element away from the closed point `x`. -/
def selectedSectionsSplitAfterInverting {r : ℕ} (x : Ω) (s : Fin r → M) : Prop :=
  ∃ f : R, f ∉ x.1.asIdeal ∧
    ∃ ρ : LocalizedModule.Away f M →ₗ[Localization.Away f] LocalizedModule.Away f (Fin r → R),
      Function.LeftInverse ρ (LocalizedModule.map (Submonoid.powers f) (selectedSectionsMap s))

section

variable [Module.FinitePresentation R M]

-- Proof sketch: identify `B(x)` with the orthogonal of the image of `Hom_R(M, R)` in the dual of
-- the fibre `M(x)`. If the localized section map splits, pull the dual basis back to obtain
-- functionals whose classes separate the images of the chosen sections, giving linear independence
-- in `V(x)`. Conversely, lift independent classes in `V(x)` to fibrewise linear forms, use finite
-- presentation together with the localization statement from Algebra, Lemma 10.10.2, and recover a
-- retraction after inverting an element outside `x`.
/-- Lemma 15.128.2: for a closed point `x`, the canonical quotient `V(x)` of the fibre by the
subspace `B(x)` detects when finitely many sections split off a free summand after inverting an
element away from `x`; equivalently, the corresponding classes in `V(x)` are linearly independent
over `κ(x)`. -/
theorem selectedSections_splitAfterInverting_iff_linearIndependent_visibleClasses
    (x : Ω) {r : ℕ} (s : Fin r → M) :
    selectedSectionsSplitAfterInverting x s ↔
      LinearIndependent (κ(x)) (closedPointFiberVisibleClass x ∘ s) :=
  sorry

end

end

/-! ### Lemma_15_128_3 (from Chap15) -/
universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

open Ideal TensorProduct
open scoped ClosedPointFiber

/-
Domain-style sampling:
- primary domain: visible quotient classes `V(x)` of closed-point fibres and the Chinese remainder
  lifting used to realize prescribed visible values by a global section;
- inspected owner-style declarations:
  `closedPointFiberVisibleQuotient`,
  `closedPointFiberVisibleClass`,
  `Submodule.mkQ_surjective`,
  `TensorProduct.quotTensorEquivQuotSMul`,
  `Ideal.pi_tensorProductMk_quotient_surjective`,
  `Ideal.isCoprime_of_isMaximal`;
- best owner abstraction: the source-facing owner for this lemma is the chapter visible quotient
  `V(x)`, with visible classes `closedPointFiberVisibleClass x s`; the full fibre `M﹙x﹚` is only
  an internal bridge used to invoke the CRT surjectivity statement for the ideal family
  `i ↦ (pts i).1.asIdeal`;
- layer triage: `source-facing` for the prescribed visible-value theorem, `core/canonical` for the
  pairwise-coprime ideal family and quotient/tensor equivalence, `bridge/view` for the quotient
  map `M﹙x﹚ → V(x)`;
- primitive data: the finite family of closed points `pts` and the prescribed visible classes `v`;
- derived API: maximality of each closed-point ideal, the surjectivity of the simultaneous
  quotient map on fibres, and the quotient projection `M﹙x﹚ → V(x)`.
-/
local notation "Ω" => closedPoints (PrimeSpectrum R)

-- Proof sketch: choose representatives of the prescribed visible classes in the full fibres
-- `M(xᵢ)`, use the Chinese remainder theorem on the pairwise comaximal closed-point ideals to lift
-- those representatives simultaneously to a global section, and then pass to the visible
-- quotients via the canonical maps `M(xᵢ) → V(xᵢ)`.
/-- Lemma 15.128.3: for pairwise distinct closed points `x₁, ..., xₙ ∈ Ω` and prescribed visible
classes `vᵢ ∈ V(xᵢ)`, there exists a section `s : M` whose fibre image `s(xᵢ)` maps to `vᵢ` in the
visible quotient `V(xᵢ)`. -/
lemma exists_section_with_prescribed_values_at_pairwise_distinct_closed_points
    {n : ℕ} (pts : Fin n → Ω)
    (hpts : Pairwise fun i j ↦ pts i ≠ pts j)
    (v : ∀ i, V((pts i))) :
    ∃ s : M, ∀ i, closedPointFiberVisibleClass (pts i) s = v i := by
  have hcoprime : Pairwise (fun i j ↦ IsCoprime ((pts i).1.asIdeal) ((pts j).1.asIdeal)) := by
    intro i j hij
    exact isCoprime_of_isMaximal fun hEq ↦
      hpts hij <| Subtype.ext <| PrimeSpectrum.ext hEq
  classical
  have hw' : ∀ i, ∃ s : M, closedPointFiberVisibleClass (pts i) s = v i := fun i ↦
    closedPointFiberVisibleClass_surjective M (pts i) (v i)
  choose w hw using hw'
  obtain ⟨s, hs⟩ :=
    pi_tensorProductMk_quotient_surjective M
      (fun i ↦ (pts i).1.asIdeal)
      hcoprime
      (fun i ↦ (quotTensorEquivQuotSMul M ((pts i).1.asIdeal)).symm ((w i)⟮(pts i)⟯))
  refine ⟨s, fun i ↦ ?_⟩
  have hs' : s⟮(pts i)⟯ = (w i)⟮(pts i)⟯ := by
    have hs'' :=
      congrArg (quotTensorEquivQuotSMul M ((pts i).1.asIdeal)) (congrFun hs i)
    simpa [closedPointFiber] using hs''
  calc
    closedPointFiberVisibleClass (pts i) s =
        closedPointFiberVisibleClass (pts i) (w i) := by
          simpa [closedPointFiberVisibleClass] using congrArg ((B((pts i))).mkQ) hs'
    _ = v i := hw i

end

/-! ### Proposition_15_128_4 (from Chap15) -/
open Order Set TopologicalSpace
open scoped ClosedPointFiber

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-
Domain-style sampling:
- primary domain: fibrewise linear independence of section classes in the visible quotient `V(x)`
  at closed points, together with codimension control on irreducible closed subsets;
- inspected owner-style declarations:
  `closedPointFiberVisibleQuotient`,
  `closedPointFiberVisibleClass`,
  `selectedSections_splitAfterInverting_iff_linearIndependent_visibleClasses`,
  `IrreducibleCloseds`,
  `Order.coheight`;
- best owner abstraction: the chapter owner for the source-visible fibre data is
  `closedPointFiberVisibleQuotient` together with `closedPointFiberVisibleClass`; this file should
  build its bad-locus predicate from that owner rather than from the full fibre `M(x)`, and the
  codimension predicate should quantify directly over the canonical owner `IrreducibleCloseds Ω`
  rather than re-encoding irreducible closed subsets as raw sets;
- layer: `source-facing` for `section_dependence_locus sections`,
  `irreducible_components_codim_at_least k F`, and the proposition's existential conclusion;
  `core/canonical` for the visible quotient owner, `IrreducibleCloseds`, and `Order.coheight`;
- primitive data: `sections`, `k`, `F`, the prescribed visible classes, the added section `s`,
  and the auxiliary set `F'`;
- derived API: the proposition statement itself; the two local predicates are small owner-level
  definitions and do not need separate unfold-only public wrappers.
-/
local notation "Ω" => closedPoints (PrimeSpectrum R)
local notation "V(" x ")" => closedPointFiberVisibleQuotient M x

/-- The locus of closed points where a finite family of sections fails to be linearly independent
in the visible quotient `V(x)`. -/
def section_dependence_locus {h : ℕ} (sections : Fin h → M) : Set Ω :=
  {x | ¬ LinearIndependent (κ(x)) (closedPointFiberVisibleClass x ∘ sections)}

/-- A subset of `Ω` has irreducible components of codimension at least `k` if every maximal
irreducible closed subset contained in it has `coheight` at least `k`. -/
def irreducible_components_codim_at_least (k : ℕ) (F : Set Ω) : Prop :=
  ∀ Z : IrreducibleCloseds Ω,
    Maximal (fun Y : IrreducibleCloseds Ω ↦ (Y : Set Ω) ⊆ F) Z →
      (k : ℕ∞) ≤ coheight Z

variable [Module.FinitePresentation R M]

-- Proof sketch: argue by induction on `k`. The case `k = 0` is Lemma `15.128.3`. For the
-- induction step, first apply the induction hypothesis to obtain a section `u` and an error set
-- `G`; choose one point on each irreducible component of `G \ F` together with a visible class
-- outside the span of the existing visible classes, enlarge the family `(s₁, …, s_h, u)`, and
-- use the Chinese remainder theorem to splice the resulting sections. These choices remove
-- irreducible components of codimension `< k`, leaving only components of codimension at least
-- `k`.
/-- Proposition 15.128.4: in the Noetherian closed-point space `Ω`, if a family of `h` sections is
already fibrewise independent in the visible quotient `V(x)` away from a closed subset `F`, if
one prescribes visible classes at finitely many pairwise distinct points of `F`, and if every
visible quotient `V(x)` has dimension at least `h + k`, then one can add one more section meeting
the prescribed visible classes so that the new dependence locus is contained in `F ∪ F'` for some
closed subset `F'` whose irreducible components all have codimension at least `k`. -/
theorem exists_section_with_prescribed_values_and_codim_controlled_dependence_locus
    [NoetherianSpace Ω] {h n k : ℕ} (sections : Fin h → M) {F : Set Ω} (hFclosed : IsClosed F)
    (hzero : section_dependence_locus sections ⊆ F)
    (pts : Fin n → Ω)
    (hpts : Pairwise fun i j ↦ pts i ≠ pts j)
    (hptsF : ∀ i, pts i ∈ F)
    (v : ∀ i, V((pts i)))
    (hdim : ∀ x : Ω, h + k ≤ Module.finrank (κ(x)) (V(x))) :
    ∃ s : M, ∃ F' : Set Ω,
      IsClosed F' ∧
      (∀ i, closedPointFiberVisibleClass (pts i) s = v i) ∧
      section_dependence_locus (Fin.snoc sections s) ⊆ F ∪ F' ∧
      irreducible_components_codim_at_least k F' := sorry

end

/-! ### Theorem_15_128_5 (from Chap15) -/
open TopologicalSpace
open scoped ClosedPointFiber

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]

/- Domain-style sampling:
- primary domain: closed-point fibres of finitely presented modules, their visible quotients `V(x)`,
  and the codimension-controlled section-construction of Proposition `15.128.4`;
- inspected owner declarations in this domain:
  `closedPointFiberVisibleQuotient`,
  `selectedSections_splitAfterInverting_iff_linearIndependent_visibleClasses`,
  `section_dependence_locus`,
  `exists_section_with_prescribed_values_and_codim_controlled_dependence_locus`;
- best owner abstraction: the local free-summand hypothesis of the source theorem is canonically
  consumed in this chapter through the visible quotient owner `V(x)` and the numerical bound
  `Module.finrank (κ(x)) (V(x))`; the explicit localized split-map package is therefore a
  bridge/view, not the right public core for this file;
- inspected ambient-dimension owner declarations:
  `topologicalKrullDim`,
  `Order.coheight_le_krullDim`,
  `topologicalKrullDim_eq_iSup_topologicalKrullDimAt`;
- source/core/bridge triage:
  `source-facing`: the global conclusion that `R` splits off `M`;
  `core/canonical`: the visible quotient `V(x)` and its fibre dimension;
  `bridge/view`: the equivalence from Lemma `15.128.2` between local split free summands and
  linear independence in `V(x)`.
- primitive data: the upper dimension bound `topologicalKrullDim Ω ≤ d` and the pointwise
  fibre-dimension inequality;
- derived API: the codimension-controlled section from Proposition `15.128.4`, followed by the
  split-inclusion conclusion. -/

local notation "Ω" => closedPoints (PrimeSpectrum R)
local notation "V(" x ")" => closedPointFiberVisibleQuotient M x

-- Proof sketch: this is the chapter's canonical reformulation of the source local-splitting
-- hypothesis via Lemma `15.128.2`, so the input is stated directly as `d < finrank V(x)`. Apply
-- Proposition `15.128.4` with `h = 0`, `k = d + 1`, no prescribed values, and empty bad locus to
-- obtain a section `s : M` whose dependence locus is contained in a closed subset all of whose
-- irreducible components have codimension at least `d + 1`. Since `topologicalKrullDim Ω ≤ d`,
-- that closed subset is empty, so `s` is fibrewise visible at every closed point. The resulting map
-- `R → M` is therefore split after localizing at every closed point, hence universally injective,
-- and the algebra lemmas cited in the text upgrade it to a split inclusion.
/-- Theorem 15.128.5: let `Ω` be the closed-point space of `Spec R`. If `Ω` is a Noetherian
topological space of dimension at most `d`, `M` is finitely presented, and equivalently to the source
local-splitting hypothesis every visible quotient `V(x)` has dimension `> d`, then there exists a
split `R`-linear inclusion `R → M`; equivalently, `M ≅ R ⊕ M'` for some `R`-module `M'`. -/
theorem exists_split_inclusion_of_visibleQuotient_finrank_gt_dimension
    {d : ℕ} [NoetherianSpace Ω] (hdim : topologicalKrullDim Ω ≤ d)
    (hV : ∀ x : Ω, d < Module.finrank (κ(x)) (V(x))) :
    ∃ (s : R →ₗ[R] M) (ρ : M →ₗ[R] R), ρ.comp s = LinearMap.id := sorry

end
