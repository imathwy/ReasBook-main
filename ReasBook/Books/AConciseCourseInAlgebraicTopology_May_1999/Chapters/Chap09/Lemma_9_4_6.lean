import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Homotopy.Product

open scoped Topology Topology.Homotopy

noncomputable section

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Generalized loops in a product space are equivalent to pairs of generalized loops in the
factors. -/
def genLoopProdEquiv {n : ℕ} {x : X} {y : Y} :
    Ω^ (Fin n) (X × Y) (x, y) ≃ Ω^ (Fin n) X x × Ω^ (Fin n) Y y where
  toFun p :=
    (⟨ContinuousMap.fst.comp p.1, fun t ht ↦ congrArg Prod.fst (p.2 t ht)⟩,
      ⟨ContinuousMap.snd.comp p.1, fun t ht ↦ congrArg Prod.snd (p.2 t ht)⟩)
  invFun pq :=
    ⟨ContinuousMap.prodMk pq.1.1 pq.2.1, fun t ht ↦ Prod.ext (pq.1.2 t ht) (pq.2.2 t ht)⟩
  left_inv p := by
    ext t <;> rfl
  right_inv pq := by
    rcases pq with ⟨p, q⟩
    apply Prod.ext <;> ext t <;> rfl

/-- The product generalized-loop equivalence identifies homotopies in `X × Y` with coordinatewise
homotopies in `X` and `Y`. -/
theorem genLoopProdEquiv_homotopic_iff {n : ℕ} {x : X} {y : Y}
    (p q : Ω^ (Fin n) (X × Y) (x, y)) :
    GenLoop.Homotopic p q ↔
      GenLoop.Homotopic (genLoopProdEquiv p).1 (genLoopProdEquiv q).1 ∧
        GenLoop.Homotopic (genLoopProdEquiv p).2 (genLoopProdEquiv q).2 := by
  constructor
  · intro hp
    constructor
    · -- Project the product homotopy to the first coordinate.
      simpa [GenLoop.Homotopic, genLoopProdEquiv] using
        ContinuousMap.HomotopicRel.comp_continuousMap hp ContinuousMap.fst
    · -- Project the product homotopy to the second coordinate.
      simpa [GenLoop.Homotopic, genLoopProdEquiv] using
        ContinuousMap.HomotopicRel.comp_continuousMap hp ContinuousMap.snd
  · rintro ⟨hp, hq⟩
    -- Reassemble the coordinate homotopies into a homotopy of product loops.
    simpa [GenLoop.Homotopic, genLoopProdEquiv] using
      Nonempty.map2 ContinuousMap.HomotopyRel.prod hp hq

/-- Coordinatewise homotopies assemble to a homotopy between the corresponding generalized loops in
the product space. -/
theorem genLoopProdEquiv_symm_homotopic {n : ℕ} {x : X} {y : Y}
    {p p' : Ω^ (Fin n) X x} {q q' : Ω^ (Fin n) Y y}
    (hp : GenLoop.Homotopic p p') (hq : GenLoop.Homotopic q q') :
    GenLoop.Homotopic (genLoopProdEquiv.symm (p, q)) (genLoopProdEquiv.symm (p', q')) := by
  -- Assemble the two coordinate homotopies into a homotopy of product maps.
  simpa [GenLoop.Homotopic, genLoopProdEquiv] using
    Nonempty.map2 ContinuousMap.HomotopyRel.prod hp hq

/-- Lemma 9.4.6: for chosen basepoints `x : X` and `y : Y`, the based homotopy group of the
product is naturally equivalent to the product of the based homotopy groups. -/
def homotopyGroupProdEquiv {n : ℕ} {x : X} {y : Y} :
    π_ n (X × Y) (x, y) ≃ π_ n X x × π_ n Y y where
  toFun :=
    Quotient.lift
      (fun p ↦ ((⟦(genLoopProdEquiv p).1⟧ : π_ n X x), (⟦(genLoopProdEquiv p).2⟧ : π_ n Y y)))
      (fun p q hpq ↦ by
        have hpq' := (genLoopProdEquiv_homotopic_iff p q).mp hpq
        exact Prod.ext (Quotient.sound hpq'.1) (Quotient.sound hpq'.2))
  invFun pq :=
    Quotient.liftOn₂ pq.1 pq.2
      (fun p q ↦ (⟦genLoopProdEquiv.symm (p, q)⟧ : π_ n (X × Y) (x, y)))
      (fun p q p' q' hp hq ↦ Quotient.sound (genLoopProdEquiv_symm_homotopic hp hq))
  left_inv := by
    intro p
    refine Quotient.inductionOn p ?_
    intro γ
    change Quotient.mk' (genLoopProdEquiv.symm (genLoopProdEquiv γ)) = Quotient.mk' γ
    simpa using congrArg Quotient.mk' (genLoopProdEquiv.left_inv γ)
  right_inv := by
    intro pq
    rcases pq with ⟨p, q⟩
    refine Quotient.inductionOn₂ p q ?_
    intro γ δ
    change
      (((⟦(genLoopProdEquiv (genLoopProdEquiv.symm (γ, δ))).1⟧ : π_ n X x),
          (⟦(genLoopProdEquiv (genLoopProdEquiv.symm (γ, δ))).2⟧ : π_ n Y y)) =
        (⟦γ⟧, ⟦δ⟧))
    refine Prod.ext ?_ ?_
    · simpa using congrArg Quotient.mk' (congrArg Prod.fst (genLoopProdEquiv.right_inv (γ, δ)))
    · simpa using congrArg Quotient.mk' (congrArg Prod.snd (genLoopProdEquiv.right_inv (γ, δ)))

/-- The product equivalence on homotopy groups sends a class to the pair of the coordinatewise
classes. -/
@[simp] theorem homotopyGroupProdEquiv_apply {n : ℕ} {x : X} {y : Y}
    (γ : Ω^ (Fin n) (X × Y) (x, y)) :
    homotopyGroupProdEquiv ⟦γ⟧ =
      ((⟦(genLoopProdEquiv γ).1⟧ : π_ n X x), (⟦(genLoopProdEquiv γ).2⟧ : π_ n Y y)) :=
  rfl

/-- The inverse product equivalence on homotopy groups sends a pair of classes to the class of the
assembled generalized loop. -/
@[simp] theorem homotopyGroupProdEquiv_symm_apply {n : ℕ} {x : X} {y : Y}
    (γ : Ω^ (Fin n) X x) (δ : Ω^ (Fin n) Y y) :
    homotopyGroupProdEquiv.symm ((⟦γ⟧ : π_ n X x), (⟦δ⟧ : π_ n Y y)) =
      (⟦genLoopProdEquiv.symm (γ, δ)⟧ : π_ n (X × Y) (x, y)) :=
  rfl
