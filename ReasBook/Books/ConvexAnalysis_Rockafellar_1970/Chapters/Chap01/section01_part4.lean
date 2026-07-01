/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Pengfei Hao, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section01_part3

section Chap01
section Section01

/-- A translate of a submodule can be written using a projection onto the submodule. -/
lemma translate_eq_exists_add_of_isCompl (n : Nat)
    (L W : Submodule Real (Fin n → Real)) (hLW : IsCompl L W) (x0 : Fin n → Real) :
    SetTranslate n (L : Set (Fin n → Real)) x0 =
      {x : Fin n → Real | ∃ y : Fin n → Real,
        x = x0 + (Submodule.IsCompl.projection hLW) y} := by
  ext x
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l, ?_⟩
    have hproj : (Submodule.IsCompl.projection hLW) l = l := by
      simpa using
        (Submodule.IsCompl.projection_apply_left (hpq:=hLW) (x:=⟨l, hl⟩))
    simp [hproj, add_comm]
  · rintro ⟨y, rfl⟩
    refine ⟨(Submodule.IsCompl.projection hLW) y,
      (Submodule.IsCompl.projection_apply_mem (hpq:=hLW) y), ?_⟩
    simp [add_comm]

/-- Convert a graph description in submodule coordinates to one in `Fin` coordinates. -/
lemma graph_of_affineMap_exists_fin (n : Nat) (C : Set (Fin n → Real))
    (L W : Submodule Real (Fin n → Real))
    (Φ : (Fin n → Real) ≃ₗ[Real] (L × W)) (f : AffineMap Real L W)
    (hgraph : Φ '' C = {p : L × W | p.2 = f p.1}) :
    ∃ (n1 n2 : Nat) (f' : AffineMap Real (Fin n1 → Real) (Fin n2 → Real))
      (e : (Fin n1 → Real) × (Fin n2 → Real) →ₗ[Real] (Fin n → Real)),
        C = {x : Fin n → Real | ∃ y1 : Fin n1 → Real, x = e (y1, f' y1)} := by
  classical
  let n1 : Nat := Module.finrank Real L
  let n2 : Nat := Module.finrank Real W
  let eL : (Fin n1 → Real) ≃ₗ[Real] L := (Module.finBasis Real L).equivFun.symm
  let eW : (Fin n2 → Real) ≃ₗ[Real] W := (Module.finBasis Real W).equivFun.symm
  let e : ((Fin n1 → Real) × (Fin n2 → Real)) ≃ₗ[Real] (Fin n → Real) :=
    (LinearEquiv.prodCongr eL eW).trans Φ.symm
  let eLmap : (Fin n1 → Real) →ₗ[Real] L := eL.toLinearMap
  let eWmapInv : W →ₗ[Real] (Fin n2 → Real) := eW.symm.toLinearMap
  let f' : AffineMap Real (Fin n1 → Real) (Fin n2 → Real) :=
    eWmapInv.toAffineMap.comp (f.comp eLmap.toAffineMap)
  refine ⟨n1, n2, f', e.toLinearMap, ?_⟩
  have hC : C = {x : Fin n → Real | ∃ l : L, x = Φ.symm (l, f l)} := by
    ext x
    constructor
    · intro hx
      have hmem : Φ x ∈ {p : L × W | p.2 = f p.1} := by
        have hmem' : Φ x ∈ Φ '' C := ⟨x, hx, rfl⟩
        simpa [hgraph] using hmem'
      have hx' : (Φ x).2 = f (Φ x).1 := by
        simpa using hmem
      refine ⟨(Φ x).1, ?_⟩
      have hpair : (Φ x) = ((Φ x).1, f (Φ x).1) := by
        ext <;> simp [hx']
      calc
        x = Φ.symm (Φ x) := by
          simp
        _ = Φ.symm ((Φ x).1, f (Φ x).1) := by
          simpa using congrArg Φ.symm hpair
    · rintro ⟨l, rfl⟩
      have hmem : (l, f l) ∈ Φ '' C := by
        simp [hgraph]
      rcases hmem with ⟨x, hx, hxΦ⟩
      have hx' : x = Φ.symm (l, f l) := by
        have := congrArg Φ.symm hxΦ
        simpa using this
      simpa [hx'] using hx
  ext x
  constructor
  · intro hx
    have hx' := hx
    rw [hC] at hx'
    change (∃ l : L, x = Φ.symm (l, f l)) at hx'
    rcases hx' with ⟨l, rfl⟩
    refine ⟨eL.symm l, ?_⟩
    have hf' : eW (f' (eL.symm l)) = f l := by
      simp [f', eWmapInv, eLmap, AffineMap.comp_apply]
    calc
      Φ.symm (l, f l) =
          Φ.symm (eL (eL.symm l), eW (f' (eL.symm l))) := by
            simp [hf']
      _ = e (eL.symm l, f' (eL.symm l)) := by
            simp [e]
  · rintro ⟨y1, rfl⟩
    have hf' : eW (f' y1) = f (eL y1) := by
      simp [f', eWmapInv, eLmap, AffineMap.comp_apply]
    have hx' : e (y1, f' y1) = Φ.symm (eL y1, f (eL y1)) := by
      simp [e, hf']
    have : Φ.symm (eL y1, f (eL y1)) ∈ C := by
      rw [hC]
      change (∃ l : L, Φ.symm (eL y1, f (eL y1)) = Φ.symm (l, f l))
      exact ⟨eL y1, rfl⟩
    simpa [hx'] using this

/-- Text 1.13.1: Affine sets are affine images and graphs of affine maps (existence forms). -/
theorem affineSet_eq_image_submodule_translate_and_graph (n : Nat)
    (C : Set (Fin n → Real)) :
    IsAffineSet n C → Set.Nonempty C → C ≠ Set.univ →
      (∃ (m k : Nat) (L : Submodule Real (Fin m → Real))
          (T : ContinuousAffineMap Real (Fin m → Real) (Fin k → Real))
          (y0 : Fin m → Real)
          (e : (Fin k → Real) ≃ₗ[Real] (Fin n → Real)),
        C = {x : Fin n → Real | ∃ y : Fin m → Real,
          y ∈ Set.image (fun l : Fin m → Real => l + y0) (L : Set (Fin m → Real)) ∧
          x = e (T y)}) ∧
      (∃ (m : Nat) (A : (Fin m → Real) →ₗ[Real] (Fin n → Real)) (x0 : Fin n → Real),
        C = {x : Fin n → Real | ∃ y : Fin m → Real, x = x0 + A y} ∧
        ∃ (n1 n2 : Nat) (f : AffineMap Real (Fin n1 → Real) (Fin n2 → Real))
          (e : (Fin n1 → Real) × (Fin n2 → Real) →ₗ[Real] (Fin n → Real)),
            C = {x : Fin n → Real | ∃ y1 : Fin n1 → Real, x = e (y1, f y1)}) := by
  intro hC hne hne_univ
  classical
  rcases affineSet_eq_translate_submodule n C hC hne with ⟨L, x0, hCeq⟩
  refine ⟨?_, ?_⟩
  · refine ⟨n, n, L,
      (ContinuousAffineMap.id (R := Real) (P := Fin n → Real) :
        (Fin n → Real) →ᴬ[Real] (Fin n → Real)),
      x0, LinearEquiv.refl (R := Real) (M := Fin n → Real), ?_⟩
    have hCeq' :
        C = {x : Fin n → Real | ∃ y : Fin n → Real,
          y ∈ Set.image (fun l : Fin n → Real => l + x0) (L : Set (Fin n → Real)) ∧
          x = y} := by
      calc
        C = SetTranslate n (L : Set (Fin n → Real)) x0 := hCeq
        _ = {x : Fin n → Real | ∃ y : Fin n → Real,
              y ∈ Set.image (fun l : Fin n → Real => l + x0) (L : Set (Fin n → Real)) ∧
              x = y} := by
            ext x
            constructor
            · rintro ⟨y, hy, rfl⟩
              exact ⟨y + x0, ⟨y, hy, rfl⟩, rfl⟩
            · rintro ⟨y, hy, rfl⟩
              exact hy
    simpa using hCeq'
  · rcases exists_isCompl_submodule n L with ⟨W, hLW⟩
    refine ⟨n, Submodule.IsCompl.projection hLW, x0, ?_, ?_⟩
    · calc
        C = SetTranslate n (L : Set (Fin n → Real)) x0 := hCeq
        _ = {x : Fin n → Real | ∃ y : Fin n → Real,
              x = x0 + (Submodule.IsCompl.projection hLW) y} := by
            simpa using
              (translate_eq_exists_add_of_isCompl (n:=n) (L:=L) (W:=W) hLW x0)
    · rcases affineSet_is_graph_of_affineMap n C hC hne with ⟨L', W', Φ, f, hgraph⟩
      exact
        graph_of_affineMap_exists_fin (n:=n) (C:=C) (L:=L') (W:=W') Φ f hgraph

end Section01
end Chap01
