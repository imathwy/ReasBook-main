import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
open scoped IntermediateField

/- Domain-style sampling:
* primary domain: finite purely inseparable towers built by successive simple adjunctions;
* sampled owner declarations:
  `IntermediateField.adjoin`,
  `F⟮α⟯`,
  `IsPurelyInseparable.minpoly_eq_X_sub_C_pow`,
  `finrank_adjoin_simple_eq_one_iff`;
* best owner abstraction: the source-facing finite stage tower formed by adjoining the prefix of a
  tuple of generators, built directly from `IntermediateField.adjoin`;
* primitive data: a finite generator family `α : Fin n → E` and its induced intermediate-field
  tower;
* derived API: the degree-`p` conclusion and the “not already a `p`th power in the previous stage”
  clause for each successive simple adjunction.

Layer triage:
* `source-facing`: this theorem's existence of a finite generator tower with successive degree-`p`
  steps;
* `core/canonical`: mathlib's purely inseparable simple-extension owners and finrank lemmas;
* `bridge/view`: the theorem packages those single-step canonical facts along the prefix-adjoin
  tower, without introducing a separate generated-extension package.
-/

/-- The subset of `E` consisting of the entries of `α` whose indices are strictly before `i`. -/
def finiteGeneratorPrefix {n : ℕ} (α : Fin n → E) (i : Fin (n + 1)) : Set E :=
  {x | ∃ j : Fin n, j.1 < i.1 ∧ α j = x}

/-- The intermediate field generated over `F` by the entries of `α` strictly before `i`. -/
def finiteGeneratorStage (F : Type u) {E : Type v} [Field F] [Field E] [Algebra F E]
    {n : ℕ} (α : Fin n → E) (i : Fin (n + 1)) : IntermediateField F E :=
  IntermediateField.adjoin F (finiteGeneratorPrefix α i)

/-- A finite generator family whose prefix-adjoin stages form successive degree-`p` purely
inseparable simple extensions and generate all of `E`. -/
class IsPthRootTower (F : Type u) {E : Type v} [Field F] [Field E] [Algebra F E]
    (p : ℕ) {n : ℕ} (α : Fin n → E) : Prop where
  /-- The full generator family spans the whole extension field. -/
  stage_top :
    finiteGeneratorStage F α (Fin.last n) = ⊤
  /-- Each successive simple adjunction has relative degree `p`. -/
  relfinrank_eq (i : Fin n) :
    (finiteGeneratorStage F α (Fin.castSucc i)).relfinrank
      (finiteGeneratorStage F α (Fin.succ i)) = p
  /-- Each chosen generator has its `p`th power in the previous stage. -/
  pth_power_mem (i : Fin n) :
    α i ^ p ∈ finiteGeneratorStage F α (Fin.castSucc i)
  /-- No chosen generator is already a `p`th power in the previous stage. -/
  not_pth_power (i : Fin n) :
    ¬ ∃ β : finiteGeneratorStage F α (Fin.castSucc i),
      (β : E) ^ p = α i ^ p

-- Proof sketch: argue by induction on `[E : F]`. If `E = F`, take the empty generating family.
-- Otherwise choose `α ∈ E \ F` with `α ^ p ∈ F` but `α` not a `p`th power in `F`, so
-- `F⟮α⟯ / F` has degree `p`; then apply the induction hypothesis to `E / F⟮α⟯` and concatenate
-- the resulting generators.
/-- Lemma 9.14.5: a finite purely inseparable extension of characteristic `p > 0` admits a finite
generating family whose successive stages are degree-`p` extensions obtained by adjoining
`p`th roots of elements from the previous stage that are not already `p`th powers there. -/
theorem exists_pthRoot_tower_of_finite_purelyInseparable
    (p : ℕ) [Fact p.Prime] [CharP F p] [FiniteDimensional F E] [IsPurelyInseparable F E] :
    ∃ (n : ℕ) (α : Fin n → E), IsPthRootTower F p α := sorry

end
