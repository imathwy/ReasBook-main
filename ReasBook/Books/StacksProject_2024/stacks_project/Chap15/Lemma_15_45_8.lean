import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_112_8
import StacksProject_2024.stacks_project.Chap10.Lemma_10_130_3
import StacksProject_2024.stacks_project.Chap10.Lemma_10_163_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_45_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_45_3

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

section

variable {R : Type u}
variable [CommRing R] [IsLocalRing R]

/- Domain-style sampling:
- primary domain: local commutative algebra of depth under flat local base change through
  henselization and strict henselization;
- sampled owner declarations:
  `moduleDepth`,
  `depth_target_eq_depth_source_add_depth_closed_fiber`,
  `closedFiberQuotAlgEquiv`,
  `henselizationMap_faithfullyFlat`,
  `strictHenselizationMap_faithfullyFlat`,
  `isNoetherianRing_tfae_of_henselization_and_strictHenselization`;
- best owner abstraction: the public statements should be the atomic equalities on the owner
  `moduleDepth`; the closed fiber belongs on the canonical owner
  `Ideal.Fiber (maximalIdeal R) S`, and the quotient by the extended maximal ideal is only an
  internal bridge used to show that fiber is a field;
- primitive data: the Noetherian local ring `R` and the chosen henselization and strict
  henselization owner instances;
- derived API: faithful flatness of the structural maps, Noetherianity of the target local rings,
  and the field structure on the closed fibers coming from the maximal-ideal image equalities.

Source/core/bridge triage:
- `source-facing`: the two depth equalities for henselization and strict henselization;
- `core/canonical`: `moduleDepth` and the closed-fiber owner `Ideal.Fiber`;
- `bridge/view`: `closedFiberQuotAlgEquiv` and the maximal-ideal image equalities from
  `IsHenselizationOf` and `IsStrictHenselizationOf`.
-/

private theorem moduleDepth_self_eq_zero_of_field (K : Type u) [Field K] :
    moduleDepth K K = 0 := by
  let _ : Ring.KrullDimLE 0 K :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr <| ringKrullDim_eq_zero_of_field K
  have hCM : Module.CohenMacaulay K K := self_cohenMacaulay_of_krullDimLE_zero K
  have hdepth : ringKrullDim K = .some (moduleDepth K K) :=
    (Module.supportDim_self_eq_ringKrullDim K).symm.trans hCM.supportDim_eq_moduleDepth
  rw [ringKrullDim_eq_zero_of_field K] at hdepth
  simpa using hdepth.symm

private noncomputable def closedFiberMaximalIdealQuotEquiv
    {S : Type u} [CommRing S] [Algebra R S] [IsLocalRing S]
    (hmap : Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S) :
    Ideal.Fiber (maximalIdeal R) S ≃+* S ⧸ maximalIdeal S :=
  (closedFiberQuotAlgEquiv :
      Ideal.Fiber (maximalIdeal R) S ≃ₐ[R]
        S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)).toRingEquiv.trans <|
    Ideal.quotEquivOfEq hmap

private theorem closedFiber_isLocalRing_aux
    {S : Type u} [CommRing S] [Algebra R S] [IsLocalRing S] [IsLocalHom (algebraMap R S)] :
    IsLocalRing (Ideal.Fiber (maximalIdeal R) S) := by
  let e :
      Ideal.Fiber (maximalIdeal R) S ≃ₐ[R]
        S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R) :=
    closedFiberQuotAlgEquiv
  letI : IsLocalRing (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) := by
    have hmap : Ideal.map (algebraMap R S) (maximalIdeal R) < (⊤ : Ideal S) :=
      IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)
    have : Nontrivial (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) :=
      Ideal.Quotient.nontrivial_iff.2 hmap.ne
    exact IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (maximalIdeal R)))
      Ideal.Quotient.mk_surjective
  exact
    (e.toRingEquiv.symm :
      S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R) ≃+*
        Ideal.Fiber (maximalIdeal R) S).isLocalRing

private theorem moduleDepth_closedFiber_eq_zero_of_map_maximalIdeal
    {S : Type u} [CommRing S] [Algebra R S] [IsLocalRing S]
    [IsLocalRing (Ideal.Fiber (maximalIdeal R) S)]
    (hmap : Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S) :
    moduleDepth (Ideal.Fiber (maximalIdeal R) S) (Ideal.Fiber (maximalIdeal R) S) = 0 := by
  let e : Ideal.Fiber (maximalIdeal R) S ≃+* S ⧸ maximalIdeal S :=
    closedFiberMaximalIdealQuotEquiv hmap
  letI : Field (S ⧸ maximalIdeal S) := Ideal.Quotient.field (maximalIdeal S)
  letI : Field (Ideal.Fiber (maximalIdeal R) S) :=
    IsField.toField <| e.toMulEquiv.isField (Field.toIsField _)
  simpa using moduleDepth_self_eq_zero_of_field (Ideal.Fiber (maximalIdeal R) S)

section Henselization

variable {Rh : Type u}
variable [IsNoetherianRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]

-- Proof sketch: apply the flat local depth formula of Lemma `10.163.2` to `R → Rh`. By
-- Lemma `15.45.3`, the chosen henselization is Noetherian, and Lemma `15.45.1` gives flatness of
-- the structural map. The defining maximal-ideal equality for a henselization identifies the
-- closed fiber with the residue-field quotient of `Rh`, hence with a field, so its depth is `0`.
/-- Lemma 15.45.8 (1): if `R` is a Noetherian local ring, then the depth of `R` equals the depth
of any chosen henselization `Rh`. -/
theorem moduleDepth_henselization_eq :
    moduleDepth R R = moduleDepth Rh Rh := by
  obtain ⟨Rsh, _, _, _⟩ := exists_strictHenselization R
  have hTFAE : List.TFAE [IsNoetherianRing R, IsNoetherianRing Rh, IsNoetherianRing Rsh] :=
    isNoetherianRing_tfae_of_henselization_and_strictHenselization
  have hR : IsNoetherianRing R := inferInstance
  let _ : IsNoetherianRing Rh :=
    (hTFAE.out 0 1).mp hR
  have hflat : (algebraMap R Rh).Flat :=
    (henselizationMap_faithfullyFlat : (algebraMap R Rh).FaithfullyFlat).flat
  letI : Module.Flat R Rh := RingHom.flat_algebraMap_iff.mp hflat
  let _ : IsLocalRing (Ideal.Fiber (maximalIdeal R) Rh) := closedFiber_isLocalRing_aux
  have hdepth :
      moduleDepth Rh Rh =
        moduleDepth R R +
          moduleDepth (Ideal.Fiber (maximalIdeal R) Rh) (Ideal.Fiber (maximalIdeal R) Rh) :=
    depth_target_eq_depth_source_add_depth_closed_fiber
  simpa [moduleDepth_closedFiber_eq_zero_of_map_maximalIdeal
      IsHenselizationOf.map_maximalIdeal] using hdepth.symm

end Henselization

section StrictHenselization

variable {Rsh : Type u}
variable [IsNoetherianRing R]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

-- Proof sketch: as in part `(1)`, apply Lemma `10.163.2` to `R → Rsh`. Lemma `15.45.3` supplies
-- Noetherianity of the strict henselization and Lemma `15.45.1` gives flatness. The defining
-- equality `Ideal.map (algebraMap R Rsh) (maximalIdeal R) = maximalIdeal Rsh` makes the closed
-- fiber a residue-field quotient of `Rsh`, hence a field of depth `0`.
/-- Lemma 15.45.8 (2): if `R` is a Noetherian local ring, then the depth of `R` equals the depth
of any chosen strict henselization `Rsh`. -/
theorem moduleDepth_strictHenselization_eq :
    moduleDepth R R = moduleDepth Rsh Rsh := by
  obtain ⟨Rh, _, _, _⟩ := exists_henselization R
  have hTFAE : List.TFAE [IsNoetherianRing R, IsNoetherianRing Rh, IsNoetherianRing Rsh] :=
    isNoetherianRing_tfae_of_henselization_and_strictHenselization
  have hR : IsNoetherianRing R := inferInstance
  let _ : IsNoetherianRing Rsh :=
    (hTFAE.out 0 2).mp hR
  have hflat : (algebraMap R Rsh).Flat :=
    (strictHenselizationMap_faithfullyFlat : (algebraMap R Rsh).FaithfullyFlat).flat
  letI : Module.Flat R Rsh := RingHom.flat_algebraMap_iff.mp hflat
  let _ : IsLocalRing (Ideal.Fiber (maximalIdeal R) Rsh) := closedFiber_isLocalRing_aux
  have hdepth :
      moduleDepth Rsh Rsh =
        moduleDepth R R +
          moduleDepth (Ideal.Fiber (maximalIdeal R) Rsh) (Ideal.Fiber (maximalIdeal R) Rsh) :=
    depth_target_eq_depth_source_add_depth_closed_fiber
  simpa [moduleDepth_closedFiber_eq_zero_of_map_maximalIdeal
      IsStrictHenselizationOf.map_maximalIdeal] using hdepth.symm

end StrictHenselization

end
