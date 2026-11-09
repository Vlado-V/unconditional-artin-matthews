module

public import ArtinMatthews.GiantSignedFixedLifespanChronology


set_option backward.privateInPublic true
@[expose] public section

/-! The original ordered path data are recovered uniquely from the
actual chronological choices, including each ghost birth order. -/

namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {κ : Fin n → ℤ} {q : Fin (n+1) → ℝ}

private theorem fixedChoice_eq
    (hP : ∀ (g : S ⊕ B) p, p ∈ Sum.elim PS PB g → p.Prime)
    (hdis : Pairwise (fun i j : S ⊕ B => Disjoint (Sum.elim PS PB i) (Sum.elim PS PB j)))
    (hκ : ∀ i, 0 < (κ i).natAbs)
    (hsize : ∀ i g p, p ∈ Sum.elim PS PB g → (κ i).natAbs < p)
    (path : GiantSignedLifespanOriginalPath PS PB (ell := ell) C κ)
    (c c' : GiantSignedFixedLifespanChoices path q)
    (order : GiantSignedLifespanBirthOrderSchedule c.val) (order' : GiantSignedLifespanBirthOrderSchedule c'.val)
    (he : giantSignedFixedOrderedLifespan_chronology hP hdis hκ hsize ⟨path,c,order⟩ = giantSignedFixedOrderedLifespan_chronology hP hdis hκ hsize ⟨path,c',order'⟩) : c = c' := by
  let x : GiantSignedFixedPackedChronology PS PB ell C := giantSignedFixedOrderedLifespan_chronology hP hdis hκ hsize ⟨path,c,order⟩
  let y : GiantSignedFixedPackedChronology PS PB ell C := giantSignedFixedOrderedLifespan_chronology hP hdis hκ hsize ⟨path,c',order'⟩
  let D (a : GiantSignedFixedLifespanChoices path q) (z : GiantSignedFixedPackedChronology PS PB ell C) :=
    GiantSignedChronologicalLifespanCoefficientData (A := path.visits) a.val z.2 path.offset
  let dx : D c x := giantSignedLifespanPath_coefficientData path hP hdis hκ hsize c.property order
  let dy : D c' y := giantSignedLifespanPath_coefficientData path hP hdis hκ hsize c'.property order'
  have dy' : D c' x := (show y = x from he.symm) ▸ dy
  apply Subtype.ext
  exact giantSignedChronologicalGhostMatch_choice_unique x.2 c.val c'.val path.offset
    dx.before dy'.before dx.ghostMatch dy'.ghostMatch

private theorem fixedOrder_eq
    (hP : ∀ (g : S ⊕ B) p, p ∈ Sum.elim PS PB g → p.Prime)
    (hdis : Pairwise (fun i j : S ⊕ B => Disjoint (Sum.elim PS PB i) (Sum.elim PS PB j)))
    (hκ : ∀ i, 0 < (κ i).natAbs)
    (hsize : ∀ i g p, p ∈ Sum.elim PS PB g → (κ i).natAbs < p)
    (path : GiantSignedLifespanOriginalPath PS PB (ell := ell) C κ)
    (c : GiantSignedFixedLifespanChoices path q)
    (order order' : GiantSignedLifespanBirthOrderSchedule c.val)
    (he : giantSignedFixedOrderedLifespan_chronology hP hdis hκ hsize ⟨path,c,order⟩ = giantSignedFixedOrderedLifespan_chronology hP hdis hκ hsize ⟨path,c,order'⟩) : order = order' := by
  let x : GiantSignedFixedPackedChronology PS PB ell C := giantSignedFixedOrderedLifespan_chronology hP hdis hκ hsize ⟨path,c,order⟩
  let y : GiantSignedFixedPackedChronology PS PB ell C := giantSignedFixedOrderedLifespan_chronology hP hdis hκ hsize ⟨path,c,order'⟩
  let M (z : GiantSignedFixedPackedChronology PS PB ell C) (i : Fin (n+1)) (g : B) (o : GiantSignedLifespanBirthOrderSchedule c.val) :=
    giantSignedFixedGhostMove (z.2.state i).2.2 (z.1 i) (z.2.deleted i) (z.2.born i) g =
      giantSignedGhostVisitMove (c.val g) i (giantSignedMemoryGroupEquiv PB (z.2.state i).2.2 g) (o i g)
  funext i g
  have hm : M x i g order := rfl
  have hm' : M y i g order' := rfl
  have hm'' : M x i g order' := (show y = x from he.symm) ▸ hm'
  exact giantSignedChronologicalGhostMatch_order_unique x.2 c.val i g (order i g) (order' i g) hm hm''

theorem giantSignedFixedOrderedLifespan_chronology_injective
    (hP : ∀ (g : S ⊕ B) p, p ∈ Sum.elim PS PB g → p.Prime)
    (hdis : Pairwise (fun i j : S ⊕ B => Disjoint (Sum.elim PS PB i) (Sum.elim PS PB j)))
    (hκ : ∀ i, 0 < (κ i).natAbs)
    (hsize : ∀ i g p, p ∈ Sum.elim PS PB g → (κ i).natAbs < p)
    :
    Function.Injective (giantSignedFixedOrderedLifespan_chronology (C := C) (ell := ell) hP hdis hκ hsize (q := q)) := by
  rintro ⟨p,c,order⟩ ⟨p',c',order'⟩ he
  have hp : p = p' := giantSignedFixedOrderedLifespan_chronology_path hP hdis hκ hsize he
  subst p'
  have hc : c = c' := fixedChoice_eq hP hdis hκ hsize p c c' order order' he
  subst c'
  have ho : order = order' := fixedOrder_eq hP hdis hκ hsize p c order order' he
  cases ho
  rfl

def giantSignedFixedLifespanEquiv
    (hP : ∀ (g : S ⊕ B) p, p ∈ Sum.elim PS PB g → p.Prime)
    (hdis : Pairwise (fun i j : S ⊕ B => Disjoint (Sum.elim PS PB i) (Sum.elim PS PB j)))
    (hκ : ∀ i, 0 < (κ i).natAbs)
    (hsize : ∀ i g p, p ∈ Sum.elim PS PB g → (κ i).natAbs < p)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (hb : ∀ g (p : PB g), giantSignedPrimeResidueBaseline p.val q ≠ 0) :
    GiantSignedFixedOrderedLifespan PS PB ell C κ q ≃
      GiantSignedFixedAdmissibleChronology PS PB ell C κ :=
  Equiv.ofBijective (giantSignedFixedOrderedLifespan_admissible (C := C) (ell := ell) (q := q) hP hdis hκ hsize)
    ⟨fun _ _ he => giantSignedFixedOrderedLifespan_chronology_injective (C := C) (ell := ell) (q := q) hP hdis hκ hsize (congrArg Subtype.val he),
      giantSignedFixedOrderedLifespan_admissible_surjective (C := C) (ell := ell) (q := q) hP hdis hκ hsize hq0 hq1 hb⟩

end
end ArtinMatthews
