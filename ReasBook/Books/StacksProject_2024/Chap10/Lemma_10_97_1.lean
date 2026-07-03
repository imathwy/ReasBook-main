import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

-- Domain-style sampling for Lemma 10.97.1:
-- * primary domain: adic-completion exactness for short exact sequences of finite modules over a
--   Noetherian ring, together with the tensor-product description of completion.
-- * sampled owner declarations in this domain:
--   `AdicCompletion.map_injective`,
--   `AdicCompletion.map_exact`,
--   `AdicCompletion.map_surjective`,
--   `CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact`,
--   `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`.
-- * best owner abstractions: the short-complex owner `S : ShortComplex (ModuleCat R)` with
--   `hS : S.ShortExact`, the induced completed short complex `completionShortComplex I S`, and the
--   tensor comparison equivalence
--   `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`.
-- * primitive data: the short complex owner and the finite middle-term hypothesis for part `(2)`,
--   together with the module input for the tensor-comparison owner in part `(3)`.
-- * derived API: the restricted-scalars `ModuleCat R` form in part `(2)` is only a bridge;
--   parts `(1)` and `(3)` are direct owner recalls.

section injective

variable {R : Type u} [CommRing R] (I : Ideal R) [IsNoetherianRing R]
variable {K N : Type u} [AddCommGroup K] [Module R K] [AddCommGroup N] [Module R N]
variable [Module.Finite R N]

/- Lemma 10.97.1 (1): completion preserves injectivity for maps into a finite module over a
Noetherian ring. This is exactly the canonical theorem `AdicCompletion.map_injective`. -/
recall AdicCompletion.map_injective

end injective

section shortExact

variable {R : Type u} [CommRing R] (I : Ideal R) [IsNoetherianRing R]

namespace CategoryTheory.ShortComplex

variable {S : ShortComplex (ModuleCat.{u} R)}
variable [Module.Finite R S.X₂]

-- Domain-style sampling for Lemma 10.97.1 (2):
-- * primary domain: short exact sequences of modules and exactness of adic completion.
-- * sampled owner declarations:
--   `CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact`,
--   `ModuleCat.shortComplex_shortExact`,
--   `AdicCompletion.map_exact`,
--   `AdicCompletion.map_injective`.
-- * best owner abstraction: a short complex `S : ShortComplex (ModuleCat R)` with
--   `hS : S.ShortExact`, and the induced completed short complex `completionShortComplex I S`.
-- * primitive data: the owner short complex and the finite middle-term hypothesis
--   `[Module.Finite R S.X₂]`.
-- * derived API: the restricted-scalars `ModuleCat R` presentation is only a bridge.

/-- The short complex of completed modules attached to `S`. -/
abbrev completionShortComplex (S : ShortComplex (ModuleCat.{u} R)) :
    ShortComplex (ModuleCat.{u} (AdicCompletion I R)) :=
  ShortComplex.moduleCatMk
    (AdicCompletion.map I S.f.hom)
    (AdicCompletion.map I S.g.hom)
    (by
      have hzero : S.g.hom ∘ₗ S.f.hom = 0 := by
        ext x
        exact S.zero_apply x
      rw [AdicCompletion.map_comp, hzero, AdicCompletion.map_zero])

-- Proof sketch: convert the short exact owner hypothesis `hS` into injectivity, exactness, and
-- surjectivity of the underlying linear maps, then apply the owner theorems
-- `AdicCompletion.map_injective`, `AdicCompletion.map_exact`, and `AdicCompletion.map_surjective`
-- to the two structure maps of `S`.
/-- Lemma 10.97.1 (2): over a Noetherian ring, if `S` is a short exact sequence of `R`-modules and
its middle term is finite, then the completed sequence `completionShortComplex I S` is short exact
over `AdicCompletion I R`. -/
theorem completionShortComplex_shortExact (hS : S.ShortExact) :
    (completionShortComplex I S).ShortExact := by
  let f : S.X₁ →ₗ[R] S.X₂ := S.f.hom
  let g : S.X₂ →ₗ[R] S.X₃ := S.g.hom
  have hf : Function.Injective f := by
    simpa using hS.moduleCat_injective_f
  have hfg : Function.Exact f g := by
    simpa using (ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact
  have hg : Function.Surjective g := by
    simpa using hS.moduleCat_surjective_g
  refine ModuleCat.shortComplex_shortExact (completionShortComplex I S) ?_ ?_ ?_
  · simpa [completionShortComplex] using
      (show Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) from
        AdicCompletion.map_exact hf hfg hg)
  · simpa [completionShortComplex] using
      (AdicCompletion.map_injective I hf)
  · simpa [completionShortComplex] using
      (AdicCompletion.map_surjective I hg)

/-- Companion bridge: after restricting scalars along `R → AdicCompletion I R`, the completed
short complex is still short exact as a short complex in `ModuleCat R`. -/
theorem completionShortComplex_restrictScalars_shortExact (hS : S.ShortExact) :
    (ShortComplex.moduleCatMk
      ((AdicCompletion.map I S.f.hom).restrictScalars R)
      ((AdicCompletion.map I S.g.hom).restrictScalars R)
      (by
        have hzero :
            AdicCompletion.map I S.g.hom ∘ₗ AdicCompletion.map I S.f.hom = 0 := by
          rw [AdicCompletion.map_comp]
          have hzero : S.g.hom ∘ₗ S.f.hom = 0 := by
            ext x
            exact S.zero_apply x
          rw [hzero, AdicCompletion.map_zero]
        simpa using congrArg
          (fun φ : AdicCompletion I S.X₁ →ₗ[AdicCompletion I R] AdicCompletion I S.X₃ ↦
            φ.restrictScalars R)
          hzero)).ShortExact := by
  let T : ShortComplex (ModuleCat (AdicCompletion I R)) := completionShortComplex I S
  have hT : T.ShortExact := completionShortComplex_shortExact I hS
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · simpa using (ShortExact.moduleCat_exact_iff_function_exact T).1 hT.exact
  · simpa using hT.moduleCat_injective_f
  · simpa using hT.moduleCat_surjective_g

end CategoryTheory.ShortComplex

end shortExact

section tensorProduct

variable {R : Type u} [CommRing R] (I : Ideal R) [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

/- Lemma 10.97.1 (3): for a finite module over a Noetherian ring, its `I`-adic completion is
canonically identified with the completed ring tensored with the module. This is exactly the
canonical equivalence `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`. -/
recall AdicCompletion.ofTensorProductEquivOfFiniteNoetherian

end tensorProduct
