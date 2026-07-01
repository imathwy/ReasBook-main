import Mathlib
import stacks_project.Chap12.Lemma_12_31_3
import stacks_project.Chap13.Definition_13_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComposableArrows
open Opposite
open SequentialInverseSystem

noncomputable section

local notation "AbSeq" => SequentialInverseSystem AddCommGrpCat

/- Domain-style sampling for Lemma 15.87.2:
- primary domain: the Milnor `lim` / `lim¹` exact sequence for a short exact sequence of
  sequential inverse systems of abelian groups;
- sampled owner declarations:
  `SequentialInverseSystem.firstDerivedLimit`,
  `SequentialInverseSystem.inverseLimit_exact_and_mono_of_shortExact`,
  `CategoryTheory.derivedLimitDifferenceMap`,
  `ShortComplex.SnakeInput.δ`,
  `ShortComplex.SnakeInput.snake_lemma`;
- best owner abstraction on this theorem surface: the degree-zero term is the canonical inverse
  limit object `limit A`, while the degree-one obstruction is the chapter owner
  `A.firstDerivedLimit`; the connecting morphism should therefore be the snake-lemma boundary map
  on the canonical Milnor difference-map diagram whose kernel row is `S.map lim` and whose
  cokernel row is expressed by `firstDerivedLimit`;
- primitive data: only the short exact sequence `S : ShortComplex AbSeq`;
- derived API: the canonical map on `firstDerivedLimit`, the named connecting morphism
  `lim C ⟶ lim¹ A`, the five-term exact segment for `lim`, and the endpoint mono/epi
  consequences.

Source/core/bridge triage:
  `source-facing`: the exact five-term segment and six-term endpoint consequences for
  `lim` / `lim¹`;
  `core/canonical`: `limit`, `firstDerivedLimit`, `derivedLimitDifferenceMap`, and the snake-lemma
  owner `ShortComplex.SnakeInput`;
  `bridge/view`: the Milnor ambient-product diagram attached to `S`, whose top kernel row is
  `S.map lim` and whose bottom cokernel row is the induced short complex on `firstDerivedLimit`.
  -/

namespace SequentialInverseSystem

private abbrev productMap {A B : AbSeq} (φ : A ⟶ B) :
    ∏ᶜ inverseSystemFamily A ⟶ ∏ᶜ inverseSystemFamily B :=
  Pi.lift fun n ↦
    Pi.π (inverseSystemFamily A) n ≫ φ.app (op n)

private theorem productMap_π {A B : AbSeq} (φ : A ⟶ B) (n : ℕ) :
    productMap φ ≫ Pi.π (inverseSystemFamily B) n =
      Pi.π (inverseSystemFamily A) n ≫ φ.app (op n) := by
  rw [productMap, Pi.lift_π]

private theorem productMap_zero (S : ShortComplex AbSeq) :
    productMap S.f ≫ productMap S.g = 0 := by
  sorry

private theorem productMap_comm {A B : AbSeq} (φ : A ⟶ B) :
    derivedLimitDifferenceMap A ≫ productMap φ =
      productMap φ ≫ derivedLimitDifferenceMap B := by
  sorry

/-- The canonical map on `R^1 \!\varprojlim` induced by a morphism of sequential inverse systems
of abelian groups. -/
abbrev firstDerivedLimitMap {A B : AbSeq} (φ : A ⟶ B) :
    A.firstDerivedLimit ⟶ B.firstDerivedLimit :=
  cokernel.map (derivedLimitDifferenceMap A) (derivedLimitDifferenceMap B)
    (productMap φ) (productMap φ) (productMap_comm φ)

private abbrev productShortComplex (S : ShortComplex AbSeq) :
    ShortComplex AddCommGrpCat :=
  ShortComplex.mk (productMap S.f) (productMap S.g) (productMap_zero S)

private abbrev limitToProduct (A : AbSeq) :
    limit A ⟶ ∏ᶜ inverseSystemFamily A :=
  Pi.lift fun n ↦ limit.π A (op n)

private theorem limitToProduct_π (A : AbSeq) (n : ℕ) :
    limitToProduct A ≫ Pi.π (inverseSystemFamily A) n =
      limit.π A (op n) := by
  rw [limitToProduct, Pi.lift_π]

private theorem limitToProduct_comp_difference (A : AbSeq) :
    limitToProduct A ≫ derivedLimitDifferenceMap A = 0 := by
  sorry

private abbrev limitToProductHom (S : ShortComplex AbSeq) :
    S.map lim ⟶ productShortComplex S where
  τ₁ := limitToProduct S.X₁
  τ₂ := limitToProduct S.X₂
  τ₃ := limitToProduct S.X₃
  comm₁₂ := by
    sorry
  comm₂₃ := by
    sorry

private abbrev milnorDifferenceHom (S : ShortComplex AbSeq) :
    productShortComplex S ⟶ productShortComplex S where
  τ₁ := derivedLimitDifferenceMap S.X₁
  τ₂ := derivedLimitDifferenceMap S.X₂
  τ₃ := derivedLimitDifferenceMap S.X₃
  comm₁₂ := productMap_comm S.f
  comm₂₃ := productMap_comm S.g

private abbrev firstDerivedLimitShortComplex (S : ShortComplex AbSeq) :
    ShortComplex AddCommGrpCat :=
  ShortComplex.mk (firstDerivedLimitMap S.f) (firstDerivedLimitMap S.g) (by
    sorry)

private theorem productToFirstDerivedLimit_comm_f (S : ShortComplex AbSeq) :
    cokernel.π (derivedLimitDifferenceMap S.X₁) ≫ firstDerivedLimitMap S.f =
      productMap S.f ≫ cokernel.π (derivedLimitDifferenceMap S.X₂) := by
  sorry

private theorem productToFirstDerivedLimit_comm_g (S : ShortComplex AbSeq) :
    cokernel.π (derivedLimitDifferenceMap S.X₂) ≫ firstDerivedLimitMap S.g =
      productMap S.g ≫ cokernel.π (derivedLimitDifferenceMap S.X₃) := by
  sorry

private abbrev productToFirstDerivedLimitHom (S : ShortComplex AbSeq) :
    productShortComplex S ⟶ firstDerivedLimitShortComplex S where
  τ₁ := cokernel.π (derivedLimitDifferenceMap S.X₁)
  τ₂ := cokernel.π (derivedLimitDifferenceMap S.X₂)
  τ₃ := cokernel.π (derivedLimitDifferenceMap S.X₃)
  comm₁₂ := productToFirstDerivedLimit_comm_f S
  comm₂₃ := productToFirstDerivedLimit_comm_g S

private noncomputable def limitSnakeInput
    (S : ShortComplex AbSeq) (hS : S.ShortExact) :
    ShortComplex.SnakeInput AddCommGrpCat where
  L₀ := S.map lim
  L₁ := productShortComplex S
  L₂ := productShortComplex S
  L₃ := firstDerivedLimitShortComplex S
  v₀₁ := limitToProductHom S
  v₁₂ := milnorDifferenceHom S
  v₂₃ := productToFirstDerivedLimitHom S
  w₀₂ := by
    sorry
  w₁₃ := by
    sorry
  h₀ := by
    -- `\varprojlim` is the kernel of the Milnor difference map.
    sorry
  h₃ := by
    -- `R^1 \!\varprojlim` is the cokernel of the Milnor difference map.
    sorry
  L₁_exact := by
    -- Products preserve short exact sequences in abelian groups.
    sorry
  epi_L₁_g := by
    -- Products of epimorphisms in `AddCommGrpCat` are epimorphisms.
    sorry
  L₂_exact := by
    -- `L₂` is the same product row as `L₁`.
    sorry
  mono_L₂_f := by
    -- Products of monomorphisms in `AddCommGrpCat` are monomorphisms.
    sorry

end SequentialInverseSystem

/-- The canonical connecting morphism
`lim C_i ⟶ lim¹ A_i` attached to a short exact sequence of sequential inverse systems of abelian
groups. -/
noncomputable abbrev sequentialAbelianGroupLimitδ
    (S : ShortComplex AbSeq) (hS : S.ShortExact) :
    limit S.X₃ ⟶ S.X₁.firstDerivedLimit :=
  (SequentialInverseSystem.limitSnakeInput S hS).δ

/-- Lemma 15.87.2: a short exact sequence of sequential inverse systems of abelian groups induces
an exact five-term segment
`lim A_i ⟶ lim B_i ⟶ lim C_i ⟶ lim¹ A_i ⟶ lim¹ B_i`,
where the connecting morphism is the canonical snake-lemma boundary map on the Milnor
difference-map diagram and the degree-one terms are expressed by the chapter owner
`SequentialInverseSystem.firstDerivedLimit`. -/
theorem sequentialAbelianGroupLimit_exact₅
    (S : ShortComplex AbSeq) (hS : S.ShortExact) :
    (mk₅
      (lim.map S.f)
      (lim.map S.g)
      (sequentialAbelianGroupLimitδ S hS)
      (SequentialInverseSystem.firstDerivedLimitMap S.f)
      (SequentialInverseSystem.firstDerivedLimitMap S.g)).Exact := by
  sorry

/-- In the six-term exact sequence of Lemma 15.87.2, the first map
`lim A_i ⟶ lim B_i` is monic. -/
theorem sequentialAbelianGroupLimit_mono_map_f
    (S : ShortComplex AbSeq) (hS : S.ShortExact) :
    Mono (lim.map S.f) := by
  exact (SequentialInverseSystem.inverseLimit_exact_and_mono_of_shortExact S hS).2

/-- In the six-term exact sequence of Lemma 15.87.2, the last displayed map
`lim¹ B_i ⟶ lim¹ C_i` is epic. -/
theorem sequentialAbelianGroupLimit_epi_map_g
    (S : ShortComplex AbSeq) (hS : S.ShortExact) :
    Epi (SequentialInverseSystem.firstDerivedLimitMap S.g) := by
  sorry
