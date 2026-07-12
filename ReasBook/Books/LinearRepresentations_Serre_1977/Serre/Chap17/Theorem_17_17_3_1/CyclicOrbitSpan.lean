import Mathlib
import LinearRepresentations_Serre_1977.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_1
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_3
import LinearRepresentations_Serre_1977.Chap07.Remark_7_7_1_4
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_4_1.IdentityProjectionRepresentativeSeeds
import LinearRepresentations_Serre_1977.Chap08.Corollary_8_8_3_8
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_5_3.Index
import LinearRepresentations_Serre_1977.GroupTheory.PSolvable
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ResidueFieldLiftTransport

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace Representation

section

variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable {G : Type v} [Group G] [Finite G]
variable {p : ℕ}

variable [CharP (IsLocalRing.ResidueField A) p]
variable {V : Type w} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
variable [FiniteDimensional (IsLocalRing.ResidueField A) V]
variable {C P : Subgroup G}

local notation "k" => IsLocalRing.ResidueField A
noncomputable local instance cyclicOrbitSpanResidueFieldModule : Module A V :=
  Module.compHom V (algebraMap A k)
local instance cyclicOrbitSpanResidueFieldIsScalarTower : IsScalarTower A k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.3-1: a nonzero `P`-fixed vector has `C`-orbit spanning all of `V`
once `C` is normal, `G = C * P`, and the ambient representation is irreducible. -/
lemma c_orbit_span_eq_top_of_fixed_vector
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (hC : C.Normal) (hCP : C.IsComplement' P)
    (ν : V) (hν0 : ν ≠ 0)
    (hνfixed : ∀ s : P, ρ s ν = ν) :
    Submodule.span k (Set.range fun c : C ↦ ρ c ν) = ⊤ := by
  let S : Submodule k V := Submodule.span k (Set.range fun c : C ↦ ρ c ν)
  have hCstable : ∀ c : C, S.map (ρ c) ≤ S := by
    intro c
    refine (Submodule.map_span_le (ρ c) (Set.range fun c : C ↦ ρ c ν) S).2 ?_
    intro y hy
    rcases hy with ⟨c', rfl⟩
    exact Submodule.subset_span ⟨c * c', by simp⟩
  have hPstable : ∀ s : P, S.map (ρ s) ≤ S := by
    intro s
    refine (Submodule.map_span_le (ρ s) (Set.range fun c : C ↦ ρ c ν) S).2 ?_
    intro y hy
    rcases hy with ⟨c, rfl⟩
    let c' : C := ⟨(s : G) * c * ↑s⁻¹, hC.conj_mem (c : G) c.2 s⟩
    refine Submodule.subset_span ?_
    refine ⟨c', ?_⟩
    have hmul : (((s : G) * c * ↑s⁻¹) * s : G) = (s : G) * c := by
      simp [mul_assoc]
    calc
      ρ ((s : G) * c * ↑s⁻¹) ν = ρ ((s : G) * c * ↑s⁻¹) (ρ s ν) := by
        rw [hνfixed s]
      _ = ρ (((s : G) * c * ↑s⁻¹) * s) ν := by
        simpa [Module.End.mul_apply] using
          (LinearMap.congr_fun (ρ.map_mul ((s : G) * c * ↑s⁻¹) (s : G)) ν).symm
      _ = ρ ((s : G) * c) ν := by
        rw [hmul]
      _ = ρ s (ρ c ν) := by
        simpa [Module.End.mul_apply] using
          (LinearMap.congr_fun (ρ.map_mul (s : G) (c : G)) ν)
  let Sρ : Subrepresentation ρ :=
    { toSubmodule := S
      apply_mem_toSubmodule := by
        intro g x hx
        obtain ⟨⟨c, s⟩, hgs⟩ := hCP.2 g
        have hsx : ρ s x ∈ S := by
          have hsx_map : ρ s x ∈ S.map (ρ s) := by
            exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
          exact hPstable s hsx_map
        have hcx : ρ c (ρ s x) ∈ S := by
          have hcx_map : ρ c (ρ s x) ∈ S.map (ρ c) := by
            exact Submodule.mem_map.mpr ⟨ρ s x, hsx, rfl⟩
          exact hCstable c hcx_map
        have hgx : ρ g x = ρ c (ρ s x) := by
          calc
            ρ g x = ρ (((c : C) : G) * (s : G)) x := by simpa [hgs]
            _ = ρ c (ρ s x) := by
              simpa [Module.End.mul_apply] using
                (LinearMap.congr_fun (ρ.map_mul (c : G) (s : G)) x)
        exact hgx ▸ hcx }
  have hS_ne_bot : S ≠ ⊥ := by
    intro hSbot
    apply hν0
    have hνS : ν ∈ S := by
      refine Submodule.subset_span ?_
      exact ⟨1, by simpa using (LinearMap.congr_fun ρ.map_one ν).symm⟩
    simpa [S, hSbot] using hνS
  have hSρ_ne_bot : Sρ ≠ ⊥ := by
    intro hbot
    apply hS_ne_bot
    simpa [Sρ] using congrArg Subrepresentation.toSubmodule hbot
  have hSρ_top : Sρ = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top Sρ).resolve_left hSρ_ne_bot
  simpa [S, Sρ] using congrArg Subrepresentation.toSubmodule hSρ_top

/-- Helper for Theorem 17-17.3-1: the residue-field `C`-orbit span of `ν` is contained in the
image of the lifted `C`-orbit span of any chosen lift `w0`. This is Serre's orbit-span step before
the final essentiality argument upgrades image-surjectivity to equality of spans. -/
lemma cyclic_lift_orbit_span_maps_into_lifted_span
    (ρ : Representation k G V)
    {W : Type x} [AddCommGroup W] [Module A W]
    [Module.Free A W] [Module.Finite A W]
    (ρA_C : Representation A C W)
    (red_C : W →ₗ[A] V)
    (hLiftC : IsResidueFieldLift (ρ.comp C.subtype) ρA_C red_C)
    (w0 : W) (ν : V)
    (hw0 : red_C w0 = ν)
    :
    ∀ y ∈ Submodule.span k (Set.range fun c : C ↦ ρ c ν),
      y ∈ (Submodule.span A (Set.range fun c : C ↦ ρA_C c w0)).map red_C := by
  let N : Submodule A W := Submodule.span A (Set.range fun c : C ↦ ρA_C c w0)
  have hred :
      ρA_C.IsIntertwiningMap (Representation.restrictScalars A (ρ.comp C.subtype)) red_C :=
    residueFieldLift_isIntertwining_restrictScalars (A := A) hLiftC
  rw [Representation.isIntertwiningMap_iff] at hred
  intro y hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
      rcases hz with ⟨c, rfl⟩
      refine Submodule.mem_map.mpr ⟨ρA_C c w0, Submodule.subset_span ⟨c, rfl⟩, ?_⟩
      calc
        red_C (ρA_C c w0) = (Representation.restrictScalars A (ρ.comp C.subtype)) c (red_C w0) := by
          exact hred c w0
        _ = ρ c ν := by
          change ρ c (red_C w0) = ρ c ν
          rw [hw0]
  | zero =>
      simpa using (Submodule.zero_mem (N.map red_C))
  | add y z _ _ hy hz =>
      simpa using (Submodule.add_mem (N.map red_C) hy hz)
  | smul a z _ hz =>
      rcases Submodule.mem_map.mp hz with ⟨x, hx, rfl⟩
      rcases Ideal.Quotient.mk_surjective a with ⟨b, hb⟩
      refine Submodule.mem_map.mpr ⟨b • x, N.smul_mem b hx, ?_⟩
      calc
        red_C (b • x) = b • red_C x := by
          simp
        _ = a • red_C x := by
          simpa [IsLocalRing.ResidueField.algebraMap_eq] using
            congrArg (fun c : k ↦ c • red_C x) hb

/-- Helper for Theorem 17-17.3-1: an irreducible representation has nontrivial underlying space. -/
theorem nontrivial_of_isIrreducible_local_c17
    (ρ : Representation k G V) [ρ.IsIrreducible] :
    Nontrivial V := by
  by_contra hV
  letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
  have hbot_top : (⊥ : Subrepresentation ρ) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro _
      trivial
    · intro _
      simpa using (Subsingleton.elim x 0)
  exact IsSimpleOrder.bot_ne_top hbot_top

/-- Helper for Theorem 17-17.3-1: once the residue-field `C`-orbit of `ν` spans all of `V`, the
chosen lift `w0` already generates the lifted `C`-module over `A`. This is the local
base-change/Nakayama upgrade of Serre's `k' · ν = E` step. -/
lemma cyclic_lift_span_top_of_fixed_lift
    (ρ : Representation k G V)
    {W : Type x} [AddCommGroup W] [Module A W]
    [Module.Free A W] [Module.Finite A W]
    (ρA_C : Representation A C W)
    (red_C : W →ₗ[A] V)
    (hLiftC : IsResidueFieldLift (ρ.comp C.subtype) ρA_C red_C)
    (w0 : W) (ν : V)
    (hw0 : red_C w0 = ν)
    (hOrbitSpan : Submodule.span k (Set.range fun c : C ↦ ρ c ν) = ⊤) :
    Submodule.span A (Set.range fun c : C ↦ ρA_C c w0) = ⊤ := by
  letI : Module A k := Algebra.toModule
  let N : Submodule A W := Submodule.span A (Set.range fun c : C ↦ ρA_C c w0)
  have hmapRed : N.map red_C = ⊤ := by
    rw [eq_top_iff]
    intro y hy
    have hyOrbit : y ∈ Submodule.span k (Set.range fun c : C ↦ ρ c ν) := by
      simpa [hOrbitSpan] using (show y ∈ (⊤ : Submodule k V) from trivial)
    exact
      cyclic_lift_orbit_span_maps_into_lifted_span
        (A := A) (G := G) (ρ := ρ) ρA_C red_C hLiftC w0 ν hw0 y hyOrbit
  have hmapTensor :
      N.map (TensorProduct.mk A k W 1) = ⊤ := by
    rw [eq_top_iff]
    intro t ht
    have htImage : hLiftC.1.equiv t ∈ N.map red_C := by
      simpa [hmapRed] using (show hLiftC.1.equiv t ∈ (⊤ : Submodule A V) from trivial)
    rcases Submodule.mem_map.mp htImage with ⟨x, hxN, hxred⟩
    refine Submodule.mem_map.mpr ⟨x, hxN, ?_⟩
    apply hLiftC.1.equiv.injective
    calc
      hLiftC.1.equiv (TensorProduct.mk A k W 1 x) = red_C x := by
        simpa using hLiftC.1.equiv_tmul (1 : k) x
      _ = hLiftC.1.equiv t := hxred
  simpa [N] using
    (IsLocalRing.map_tensorProduct_mk_eq_top (R := A) (M := W) (N := N)).1 hmapTensor

/-- Helper for Theorem 17-17.3-1: on a lifted cyclic `C`-module generated by one orbit vector, a
`C`-equivariant endomorphism is determined by the image of that generator. -/
theorem c_equivariant_endomorphism_ext_of_generator
    {W : Type x} [AddCommGroup W] [Module A W]
    (ρA_C : Representation A C W)
    (w0 : W)
    (hspan : Submodule.span A (Set.range fun c : C ↦ ρA_C c w0) = ⊤)
    {f g : W →ₗ[A] W}
    (hf : ρA_C.IsIntertwiningMap ρA_C f)
    (hg : ρA_C.IsIntertwiningMap ρA_C g)
    (hw0 : f w0 = g w0) :
    f = g := by
  let S : Set W := Set.range fun c : C ↦ ρA_C c w0
  rw [Representation.isIntertwiningMap_iff] at hf hg
  have hEqOnSpan : ∀ y ∈ Submodule.span A S, f y = g y := by
    intro y hy
    refine
      (Submodule.span_induction (s := S) (p := fun z _ ↦ f z = g z) ?_ ?_ ?_ ?_ hy)
    · intro z hz
      rcases hz with ⟨c, rfl⟩
      calc
        f (ρA_C c w0) = ρA_C c (f w0) := by
          simpa using hf c w0
        _ = ρA_C c (g w0) := by
          rw [hw0]
        _ = g (ρA_C c w0) := by
          simpa using (hg c w0).symm
    · simp
    · intro y z hy hz hyEq hzEq
      simp [hyEq, hzEq]
    · intro a y hy hyEq
      simp [hyEq]
  ext y
  have hy : y ∈ Submodule.span A S := by
    simpa [S, hspan] using (show y ∈ (⊤ : Submodule A W) from trivial)
  exact hEqOnSpan y hy

end

end Representation
