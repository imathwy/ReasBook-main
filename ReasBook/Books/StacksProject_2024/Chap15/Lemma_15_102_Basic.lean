import Mathlib
import StacksProject_2024.Chap04.Example_4_22_6
import StacksProject_2024.Chap15.Definition_15_61_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext

attribute [local instance] CategoryTheory.HasExt.standard

section

variable {A : Type u} [CommRing A]

/-- The `n`th `I`-power submodule `I^n X`. -/
abbrev idealPowerSubmodule (I : Ideal A) (n : ℕ) (X : Type v)
    [AddCommGroup X] [Module A X] : Submodule A X :=
  I ^ n • (⊤ : Submodule A X)

end

namespace IdealPowerSubmodule

/- Textbook notation for the `n`th ideal-power submodule `I^n X`. -/
scoped notation:max I "^[" n "]" => idealPowerSubmodule I n

end IdealPowerSubmodule

section

variable {A : Type u} [CommRing A]

open scoped IdealPowerSubmodule

/-- The canonical inclusion `I^[n] X ↪ X`. -/
abbrev idealPowerSubtype (I : Ideal A) (n : ℕ) (X : Type v)
    [AddCommGroup X] [Module A X] : (I^[n] X) →ₗ[A] X :=
  (I^[n] X).subtype

-- Proof sketch: if `m ≤ n`, then `I^n ≤ I^m`; smul monotonicity on submodules gives
-- `I^n X ⊆ I^m X`.
/-- Higher ideal-power submodules are contained in lower ones. -/
theorem idealPowerSubmodule_mono
    (I : Ideal A) {X : Type v} [AddCommGroup X] [Module A X] {m n : ℕ} (h : m ≤ n) :
    I^[n] X ≤ I^[m] X := by
  have smul_top_mono {J K : Ideal A} (hJK : J ≤ K) :
      J • (⊤ : Submodule A X) ≤ K • (⊤ : Submodule A X) := by
    intro y hy
    exact Submodule.smul_induction_on hy
      (fun r hr x hx ↦ Submodule.smul_mem_smul (hJK hr) hx)
      (fun y z hy hz ↦ by simpa using Submodule.add_mem _ hy hz)
  exact smul_top_mono (Ideal.pow_le_pow_right h)

/-- Restriction of a linear map to the `n`th ideal-power submodules. -/
abbrev idealPowerSubmoduleMap
    {X Y : Type v} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (I : Ideal A) (f : X →ₗ[A] Y) (n : ℕ) :
    I^[n] X →ₗ[A] I^[n] Y :=
  f.restrict fun x hx ↦ by
    have hmap : Submodule.map f (I^[n] X) ≤ I^[n] Y := by
      rw [idealPowerSubmodule, idealPowerSubmodule, Submodule.map_smul'', Submodule.map_top]
      exact smul_mono_right _ le_top
    exact hmap (Submodule.mem_map_of_mem hx)

/-- Passage to the `n`th ideal-power submodule as an endofunctor of `Mod_A`. -/
abbrev idealPowerSubmoduleFunctor
    (I : Ideal A) (n : ℕ) :
    ModuleCat A ⥤ ModuleCat A where
  obj M := ModuleCat.of A ↥(I^[n] M)
  map f := ModuleCat.ofHom (idealPowerSubmoduleMap I f.hom n)
  map_id M := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

instance (I : Ideal A) (n : ℕ) :
    (idealPowerSubmoduleFunctor (A := A) I n).PreservesZeroMorphisms where
  map_zero X Y := by
    ext x
    rfl

/-- Inclusion of higher ideal-power stages into lower ones as a natural transformation. -/
abbrev idealPowerSubmoduleInclusionNatTrans
    (I : Ideal A) {m n : ℕ} (h : m ≤ n) :
    idealPowerSubmoduleFunctor I n ⟶ idealPowerSubmoduleFunctor I m where
  app M := ModuleCat.ofHom (Submodule.inclusion (idealPowerSubmodule_mono I h))
  naturality {X} {Y} f := by
    ext x
    rfl

/-- Inclusion of the `n`th ideal-power stage into the ambient module as a natural
transformation. -/
abbrev idealPowerSubtypeNatTrans
    (I : Ideal A) (n : ℕ) :
    idealPowerSubmoduleFunctor I n ⟶ 𝟭 (ModuleCat A) where
  app M := ModuleCat.ofHom (idealPowerSubtype I n M)
  naturality {X} {Y} f := by
    ext x
    rfl

local notation "Mod" => ModuleCat A

/-- The `n`th ideal-power stage of a module, viewed as an object of `Mod_A`. -/
def idealPowerStage (I : Ideal A) (n : ℕ) (M : Mod) : Mod :=
  ModuleCat.of A (I^[n] M)

/-- The map on `Tor_p^A(-, N)` induced by the inclusion `I^[n] M ↪ M`. -/
abbrev idealPowerSubtypeTorMap
    (I : Ideal A) (n : ℕ) (M N : Mod) (p : ℕ) :
    Tor[A, p](↥(I^[n] M), N) ⟶ Tor[A, p](M, N) :=
  (((Tor (ModuleCat A) p).flip.obj N).map (ModuleCat.ofHom (idealPowerSubtype I n M)))

/-- The restriction map on `Ext^p_A(-, N)` induced by the inclusion `I^[n] M ↪ M`. -/
abbrev idealPowerSubtypeExtPrecomp
    (I : Ideal A) (n : ℕ) (M N : Mod) (p : ℕ) :
    Ext M N p →ₗ[A] Ext (idealPowerStage I n M) N p :=
  (mk₀ (ModuleCat.ofHom (idealPowerSubtype I n M))).precompOfLinear A N (zero_add p)

/-- The map on `Ext^p_A(M, -)` induced by the inclusion `I^[n] N ↪ N`. -/
abbrev idealPowerSubtypeExtPostcomp
    (I : Ideal A) (n : ℕ) (M N : Mod) (p : ℕ) :
    Ext M (idealPowerStage I n N) p →ₗ[A] Ext M N p :=
  (mk₀ (ModuleCat.ofHom (idealPowerSubtype I n N))).postcompOfLinear A M (add_zero p)

end
