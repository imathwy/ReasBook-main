import Mathlib
import StacksProject_2024.Chap15.Situation_15_7_1
import StacksProject_2024.Chap15.Lemma_15_5_4

open CategoryTheory
open CategoryTheory.Limits

universe u

noncomputable section

section

variable {R S : Type u} [CommRing R] [CommRing S]

/- Domain-style sampling for Lemma 15.7.6:
- primary domain: commutative algebra of flat/finitely presented factorizations of ring maps and
  finite presentation of fibre-product modules in a tensor-base-change square;
- sampled owner declarations:
  `RingHom.Flat`,
  `RingHom.FinitePresentation`,
  `module_tensor_pullback_right_adjoint`,
  `Module.FinitePresentation`;
- best owner abstraction: the factorization hypothesis should use the canonical ring-map owners
  `g.Flat` and `h.FinitePresentation`, while the fibre-product module itself is owned by
  `module_tensor_pullback_right_adjoint`;
- primitive data: the relative pullback object `X` and a factorization `B' → P → D'`;
- derived API: finite presentation of the induced fibre-product module over `D'`.

Source/core/bridge triage:
- `source-facing`: the finite-presentation theorem for the fibre-product module;
- `core/canonical`: `RingHom.Flat`, `RingHom.FinitePresentation`,
  `Module.FinitePresentation`, and `module_tensor_pullback_right_adjoint`;
- `bridge/view`: the explicit existential factorization hypothesis on `S.bprimeToDp`. -/

section

variable {B A A' Dp : Type u}
variable [CommRing B] [CommRing A] [CommRing A'] [CommRing Dp]

namespace FiberProductBaseChangeSituation

local notation "Situation" => @FiberProductBaseChangeSituation B A A' Dp _ _ _ _
variable (S : Situation)

local notation "fiberProductFunctor" =>
  module_tensor_pullback_right_adjoint
    S.dprimeToD
    S.dprimeToCPrime
    S.tensor_square_commutes

/-- Restricting scalars along `B → D` gives the first component of a relative pullback object its
canonical `B`-module structure. -/
private instance instModuleFstOverB
    (X : S.relativeModuleCategory) : Module B X.fst :=
  Module.compHom X.fst (algebraMap B S.D)

/-- Restricting scalars along `A' → C'` gives the second component of a relative pullback object
its canonical `A'`-module structure. -/
private instance instModuleSndOverAprime
    (X : S.relativeModuleCategory) : Module A' X.snd :=
  Module.compHom X.snd (algebraMap A' S.CPrime)

-- Proof sketch: factor `B' → D'` through a flat intermediate ring `D''` over which `D'` is
-- finitely presented, replace the original tensor square by the corresponding flat base-changed
-- one, and then combine Lemmas `15.7.4`, `15.6.8`, and the standard finite-presentation
-- criterion via a presentation of the kernel of a finite free cover.
/-- Lemma 15.7.6: in the fibre-product base-change situation of Lemma `15.7.2`, if the `D`-module
`N` is finitely presented and flat over `B`, the `C'`-module `M'` is finitely presented and flat
over `A'`, and the map `B' → D'` factors as a flat ring map followed by a finitely presented ring
map, then the fibre-product module `N ×_M M'` is finitely presented over `D'`. -/
theorem relativeModuleFiberProduct_finitePresentation_of_flat_of_factorization
    (X : S.relativeModuleCategory)
    [Module.FinitePresentation S.D X.fst]
    [Module.Flat B X.fst]
    [Module.FinitePresentation S.CPrime X.snd]
    [Module.Flat A' X.snd]
    (hfactor :
      ∃ (P : Type u) (_ : CommRing P) (g : S.Bprime →+* P) (h : P →+* Dp),
        g.Flat ∧ h.FinitePresentation ∧ S.bprimeToDp = h.comp g) :
    Module.FinitePresentation Dp (fiberProductFunctor.obj X) := sorry

end FiberProductBaseChangeSituation

end

end
