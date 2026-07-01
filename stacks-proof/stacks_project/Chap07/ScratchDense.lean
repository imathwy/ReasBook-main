import Mathlib

universe v₁ u₁ v₂ u₂ v₃ u₃

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {Cx : Type u₁} [Category.{v₁} Cx] {Dx : Type u₂} [Category.{v₂} Dx]
variable {Ex : Type u₃} [Category.{v₃} Ex]
variable {Jx : GrothendieckTopology Cx} {Kx : GrothendieckTopology Dx}
variable {Lx : GrothendieckTopology Ex}

/-- Composition of dense subsites when the right factor is fully faithful (the source-faithful
case: the special cocontinuous functor `v` is fully faithful, while the first replacement leg
need not be). -/
theorem isDenseSubsite_comp_right_ff (F : Cx ⥤ Dx) (G : Dx ⥤ Ex)
    [F.IsDenseSubsite Jx Kx] [G.IsDenseSubsite Kx Lx] [G.Full] [G.Faithful] :
    (F ⋙ G).IsDenseSubsite Jx Lx := by
  haveI hFcd : F.IsCoverDense Kx := Functor.IsDenseSubsite.isCoverDense (J := Jx) (K := Kx) (G := F)
  haveI hGcd : G.IsCoverDense Lx := Functor.IsDenseSubsite.isCoverDense (J := Kx) (K := Lx) (G := G)
  haveI hFlf : F.IsLocallyFull Kx := Functor.IsDenseSubsite.isLocallyFull (J := Jx) (K := Kx) (G := F)
  haveI hFlfa : F.IsLocallyFaithful Kx :=
    Functor.IsDenseSubsite.isLocallyFaithful (J := Jx) (K := Kx) (G := F)
  have hGcp : CoverPreserving Kx Lx G :=
    Functor.IsDenseSubsite.coverPreserving (J := Kx) (K := Lx) (G := G)
  refine { isCoverDense' := ⟨fun U => ?_⟩
           isLocallyFull' := ⟨fun {U V} h => ?_⟩
           isLocallyFaithful' := ⟨fun {U V} f₁ f₂ e => ?_⟩
           functorPushforward_mem_iff := ?_ }
  · -- cover-dense by transitivity (independent of full faithfulness).
    apply Lx.transitive (G.is_cover_of_isCoverDense Lx U)
    intro Y h hh
    obtain ⟨d, lift, map, fac⟩ := hh
    have hpf : (Sieve.coverByImage F d).functorPushforward G ∈ Lx (G.obj d) :=
      hGcp.cover_preserve (F.is_cover_of_isCoverDense Kx d)
    apply Lx.superset_covering _ (Lx.pullback_stable lift hpf)
    intro W k hk
    obtain ⟨c, p, g, hp, e⟩ := Presieve.getFunctorPushforwardStructure hk
    obtain ⟨⟨c', l, m, lf⟩⟩ := hp
    refine ⟨⟨c', g ≫ G.map l, G.map m ≫ map, ?_⟩⟩
    have key : G.map l ≫ G.map m = G.map p := by rw [← G.map_comp, lf]
    calc (g ≫ G.map l) ≫ G.map m ≫ map
        = g ≫ (G.map l ≫ G.map m) ≫ map := by simp only [Category.assoc]
      _ = g ≫ G.map p ≫ map := by rw [key]
      _ = (k ≫ lift) ≫ map := by rw [← Category.assoc, ← e]
      _ = k ≫ h := by rw [Category.assoc, fac]
  · -- locally full: reduce the composite image sieve to `F`'s, using `G` fully faithful.
    have himg : (F ⋙ G).imageSieve h = F.imageSieve (G.preimage h) := by
      ext W i
      constructor
      · rintro ⟨l, hl⟩
        exact ⟨l, G.map_injective (by simpa [G.map_preimage] using hl)⟩
      · rintro ⟨l, hl⟩
        exact ⟨l, by simp [Functor.comp_map, ← G.map_comp, hl, G.map_preimage]⟩
    rw [himg, Sieve.functorPushforward_comp]
    exact hGcp.cover_preserve (Functor.IsLocallyFull.functorPushforward_imageSieve_mem _)
  · -- locally faithful: `G` faithful pushes the equality down to `F`.
    rw [Sieve.functorPushforward_comp]
    exact hGcp.cover_preserve
      (Functor.IsLocallyFaithful.functorPushforward_equalizer_mem _ _
        (G.map_injective (by simpa using e)))
  · intro X S
    have h1 := Functor.IsDenseSubsite.functorPushforward_mem_iff (J := Jx) (K := Kx) (G := F)
      (X := X) (S := S)
    have h2 := Functor.IsDenseSubsite.functorPushforward_mem_iff (J := Kx) (K := Lx) (G := G)
      (S := S.functorPushforward F)
    rw [Sieve.functorPushforward_comp]
    exact h2.trans h1

end CategoryTheory
