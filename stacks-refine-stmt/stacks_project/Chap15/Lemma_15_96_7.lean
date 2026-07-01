import stacks_project.Chap15.Remark_15_96_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CochainComplex
open HomologicalComplex

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: short exact sequences and connecting morphisms for cochain complexes of
  `A`-modules;
  `NatModuleCochainComplex`, `CochainComplex.reduceModIdealA`,
  together with the owner boundary `ShortComplex.ShortExact.δ` and the mathlib owner
  `Submodule.torsionBy`;
- best owner abstraction:
  `source-facing`: the bounded-below Berthelot-Ogus Bockstein operator and the surjectivity
    criterion on cycles;
  `core/canonical`: the `ModuleComplex A` short exact sequence
    `K/fK --f→ K/f²K → K/fK`, its connecting morphism, and the induced cycles map;
  `bridge/view`: the nonnegative `NatModuleCochainComplex A` surface used by the source-facing
    statements below;
- primitive data vs derived API: the primitive owner data are the quotient complexes, the
  short exact sequence, and the standard `a`-torsion owner `Submodule.torsionBy`. The Bockstein
  map and the cycle-surjectivity predicate are derived from those owners, so the bounded-below
  bridge should not expose a second public copy of the reduction-sequence data. -/

-- Proof sketch: if `x = f ^ 2 • y`, then also `x = f • (f • y)`, so every element of `f²M`
-- already lies in `fM`.
/-- The quotient submodule `(f²)M` is contained in `fM`. -/
private theorem principalIdeal_sq_smul_top_le
    {M : Type*} [AddCommGroup M] [Module A M] (f : A) :
    principalIdeal (f ^ 2) • (⊤ : Submodule A M) ≤
      Submodule.comap (LinearMap.id : M →ₗ[A] M) (principalIdeal f • (⊤ : Submodule A M)) :=
  sorry

-- Proof sketch: if `x = f • y`, then multiplying by `f` gives `f • x = f² • y`, so the
-- multiplication-by-`f` map carries `fM` into `f²M`.
/-- Multiplication by `f` sends `fM` into `f²M`. -/
private theorem principalIdeal_smul_top_le_sq_preimage
    {M : Type*} [AddCommGroup M] [Module A M] (f : A) :
    principalIdeal f • (⊤ : Submodule A M) ≤
      Submodule.comap (f • (LinearMap.id : M →ₗ[A] M))
        (principalIdeal (f ^ 2) • (⊤ : Submodule A M)) := sorry

namespace ModFSquared

open BerthelotOgusInt

/- The canonical owner for the `f²`-to-`f` reduction sequence lives on the chapter's
`ModuleComplex A` owner. The bounded-below `Nat` API below is the bridge/view used by the
source-facing lemmas in this file, while downstream `ℤ`-indexed files should reuse the owner
declarations in this namespace directly. -/

/-- The reduction `K^\bullet / fK^\bullet` on the `ModuleComplex A` owner. -/
private abbrev modFComplex (f : A) (K : ModuleComplex A) :=
  reduceModIdealA (principalIdeal f) K

/-- The reduction `K^\bullet / f²K^\bullet` on the `ModuleComplex A` owner. -/
private abbrev modFSquaredComplex (f : A) (K : ModuleComplex A) :=
  reduceModIdealA (principalIdeal (f ^ 2)) K

/-- The termwise reduction map `K/f²K → K/fK`. -/
private abbrev reductionComponent (f : A) (K : ModuleComplex A) (i : ℤ) :
    (modFSquaredComplex f K).X i ⟶ (modFComplex f K).X i :=
  let _ : Module A ↑((reduceModIdeal (principalIdeal (f ^ 2)) K).X i) :=
    Module.compHom _ (Ideal.Quotient.mk (principalIdeal (f ^ 2)))
  let _ : Module A ↑((reduceModIdeal (principalIdeal f) K).X i) :=
    Module.compHom _ (Ideal.Quotient.mk (principalIdeal f))
  ModuleCat.ofHom <|
    Submodule.mapQ
      (principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X i)))
      (principalIdeal f • (⊤ : Submodule A (K.X i)))
      (LinearMap.id : K.X i →ₗ[A] K.X i)
      (principalIdeal_sq_smul_top_le f)

/-- The termwise multiplication map `K/fK → K/f²K` induced by `x ↦ f x`. -/
private abbrev multiplicationComponent (f : A) (K : ModuleComplex A) (i : ℤ) :
    (modFComplex f K).X i ⟶ (modFSquaredComplex f K).X i :=
  let _ : Module A ↑((reduceModIdeal (principalIdeal f) K).X i) :=
    Module.compHom _ (Ideal.Quotient.mk (principalIdeal f))
  let _ : Module A ↑((reduceModIdeal (principalIdeal (f ^ 2)) K).X i) :=
    Module.compHom _ (Ideal.Quotient.mk (principalIdeal (f ^ 2)))
  ModuleCat.ofHom <|
    Submodule.mapQ
      (principalIdeal f • (⊤ : Submodule A (K.X i)))
      (principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X i)))
      (f • (LinearMap.id : K.X i →ₗ[A] K.X i))
      (principalIdeal_smul_top_le_sq_preimage f)

/-- The reduction maps `K/f²K → K/fK` commute with the reduced differentials. -/
private theorem reductionComponent_comm
    (f : A) (K : ModuleComplex A) (i j : ℤ) :
    CommSq
      (reductionComponent f K i)
      ((modFSquaredComplex f K).d i j)
      ((modFComplex f K).d i j)
      (reductionComponent f K j) := sorry

/-- The multiplication maps `K/fK → K/f²K` commute with the reduced differentials. -/
private theorem multiplicationComponent_comm
    (f : A) (K : ModuleComplex A) (i j : ℤ) :
    CommSq
      (multiplicationComponent f K i)
      ((modFComplex f K).d i j)
      ((modFSquaredComplex f K).d i j)
      (multiplicationComponent f K j) := sorry

/-- The cochain map `K^\bullet/f²K^\bullet → K^\bullet/fK^\bullet`. -/
private def reductionMap (f : A) (K : ModuleComplex A) :
    modFSquaredComplex f K ⟶ modFComplex f K where
  f i := reductionComponent f K i
  comm' i j _ := (reductionComponent_comm f K i j).w

/-- The cochain map `K^\bullet/fK^\bullet → K^\bullet/f²K^\bullet` induced by multiplication by
`f`. -/
private def multiplicationMap (f : A) (K : ModuleComplex A) :
    modFComplex f K ⟶ modFSquaredComplex f K where
  f i := multiplicationComponent f K i
  comm' i j _ := (multiplicationComponent_comm f K i j).w

/-- The composite `K/fK → K/f²K → K/fK` is zero. -/
private theorem multiplicationMap_comp_reductionMap
    (f : A) (K : ModuleComplex A) :
    multiplicationMap f K ≫ reductionMap f K = 0 := sorry

/-- The short complex
`0 → K^\bullet/fK^\bullet → K^\bullet/f²K^\bullet → K^\bullet/fK^\bullet`. -/
private abbrev shortComplex (f : A) (K : ModuleComplex A) :
    ShortComplex (ModuleComplex A) :=
  ShortComplex.mk (multiplicationMap f K) (reductionMap f K)
    (multiplicationMap_comp_reductionMap f K)

/-- The reduction sequence
`0 → K^\bullet/fK^\bullet → K^\bullet/f²K^\bullet → K^\bullet/fK^\bullet → 0`
is short exact when `K^\bullet` is termwise `f`-torsion free. -/
private theorem shortExact (f : A) (K : ModuleComplex A)
    (hK : IsTermwiseFTorsionFree f K) :
    (shortComplex f K).ShortExact := sorry

/-- The Berthelot-Ogus Bockstein morphism on the canonical `ModuleComplex A` owner, obtained as
the connecting morphism of
`0 → K^\bullet/fK^\bullet → K^\bullet/f²K^\bullet → K^\bullet/fK^\bullet → 0`. -/
noncomputable abbrev bockstein
    (f : A) (K : ModuleComplex A) (i : ℤ)
    (hK : IsTermwiseFTorsionFree f K) :
    (reduceModIdealA (principalIdeal f) K).homology i ⟶
      (reduceModIdealA (principalIdeal f) K).homology (i + 1) :=
  (shortExact f K hK).δ i (i + 1) (ComplexShape.up_mk i (i + 1) rfl)

/-- The condition that `Ker(d^i mod f²) → Ker(d^i mod f)` is surjective, expressed as the
epimorphy of the induced map on cycles on the canonical `ModuleComplex` owner. -/
abbrev cyclesReductionSurjective (f : A) (K : ModuleComplex A) (i : ℤ) : Prop :=
  Epi (cyclesMap (reductionMap f K) i)

-- Proof sketch: identify the owner-level Berthelot-Ogus `β` with the connecting morphism of the
-- canonical short exact sequence above and apply exactness of the long exact homology sequence.
/-- Owner-level form of Lemma `15.96.7`: surjectivity of
`Ker(d^i mod f²) → Ker(d^i mod f)` is equivalent to vanishing of the canonical Bockstein
morphism. -/
theorem cyclesReductionSurjective_iff_bockstein_eq_zero
    (f : A) (K : ModuleComplex A) (hK : IsTermwiseFTorsionFree f K)
    (i : ℤ) :
    cyclesReductionSurjective f K i ↔ bockstein f K i hK = 0 := sorry

-- Proof sketch: the factorization from `15.96.5.1` shows that the owner-level Bockstein factors
-- through the `f`-torsion in homology.
/-- If `H^{i+1}(K^\bullet)[f] = 0`, then the owner-level cycles map
`Ker(d^i mod f²) → Ker(d^i mod f)` is surjective. -/
theorem cyclesReductionSurjective_of_homology_f_torsion_eq_bot
    (f : A) (K : ModuleComplex A) (hK : IsTermwiseFTorsionFree f K)
    (i : ℤ) (hH : Submodule.torsionBy A (K.homology (i + 1)) f = ⊥) :
    cyclesReductionSurjective f K i := sorry

namespace Nat

/-- The bounded-below bridge/view of the Berthelot-Ogus Bockstein morphism
`H^i(M^\bullet/fM^\bullet) → H^{i+1}(M^\bullet/fM^\bullet)` coming from the short exact
sequence on the owner complex `M.extend ComplexShape.embeddingUpNat`, transported back to the
bounded-below model along the canonical reduction homology identifications from
`Remark_15_96_5`. In the textbook Berthelot-Ogus setting, this is the map
`β : H^i(M^\bullet ⊗_A f^iA/f^{i+1}A) → H^{i+1}(M^\bullet ⊗_A f^{i+1}A/f^{i+2}A)`. -/
noncomputable abbrev bockstein
    (f : A) (M : NatModuleCochainComplex A) (i : ℕ)
    (hM : IsTermwiseFTorsionFree f M) :
    (reduceModIdealA (principalIdeal f) M).homology i ⟶
      (reduceModIdealA (principalIdeal f) M).homology (i + 1) :=
  (reduceModIdealAHomologyIso (principalIdeal f) M i).inv ≫
    ModFSquared.bockstein f (M.extend ComplexShape.embeddingUpNat) (i : ℤ)
      hM.toIsTermwiseFTorsionFree ≫
      (reduceModIdealAHomologyIso (principalIdeal f) M (i + 1)).hom

/-- The bounded-below bridge/view of the condition that
`Ker(d^i mod f²) → Ker(d^i mod f)` is surjective, expressed as the epimorphy of the induced map
on cycles. This is the bounded-below bridge/view of the owner predicate
`ModFSquared.cyclesReductionSurjective` on `M.extend ComplexShape.embeddingUpNat`. -/
abbrev cyclesReductionSurjective
    (f : A) (M : NatModuleCochainComplex A) (i : ℕ) : Prop :=
  ModFSquared.cyclesReductionSurjective f (M.extend ComplexShape.embeddingUpNat) (i : ℤ)

-- Proof sketch: identify the textbook `β` with the connecting morphism of
-- `0 → M^\bullet/fM^\bullet → M^\bullet/f²M^\bullet → M^\bullet/fM^\bullet → 0`; exactness of
-- the long exact homology sequence then says that surjectivity on cycles is equivalent to the
-- vanishing of this connecting morphism.
/-- Lemma 15.96.7, bounded-below bridge/view: for a cochain complex of `f`-torsion-free
`A`-modules, surjectivity of `Ker(d^i mod f²) → Ker(d^i mod f)` is equivalent to the vanishing of
the Berthelot-Ogus Bockstein morphism
`β : H^i(M^\bullet ⊗_A f^iA/f^{i+1}A) → H^{i+1}(M^\bullet ⊗_A f^{i+1}A/f^{i+2}A)`. -/
theorem cyclesReductionSurjective_iff_bockstein_eq_zero
    (f : A) (M : NatModuleCochainComplex A) (hM : IsTermwiseFTorsionFree f M)
    (i : ℕ) :
    cyclesReductionSurjective f M i ↔ bockstein f M i hM = 0 := sorry

-- Proof sketch: by the factorization from `15.96.5.1`, the Bockstein map factors through the
-- `f`-torsion in `H^{i+1}(M^\bullet)`. If that torsion submodule is zero, then the Bockstein map
-- vanishes; the equivalence above then gives surjectivity on cycles.
/-- If `H^{i+1}(M^\bullet)[f] = 0`, then `Ker(d^i mod f²) → Ker(d^i mod f)` is surjective. -/
theorem cyclesReductionSurjective_of_homology_f_torsion_eq_bot
    (f : A) (M : NatModuleCochainComplex A) (hM : IsTermwiseFTorsionFree f M)
    (i : ℕ) (hH : Submodule.torsionBy A (M.homology (i + 1)) f = ⊥) :
    cyclesReductionSurjective f M i := sorry

end Nat

end ModFSquared

end
