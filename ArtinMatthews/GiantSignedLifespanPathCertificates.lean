module

public import ArtinMatthews.GiantSignedLifespanBirthOrderSchedule
public import ArtinMatthews.GiantSignedLifespanOriginalPath
public import ArtinMatthews.GiantSignedLifespanBirthDistinct
public import ArtinMatthews.GiantSignedLifespanPathSlots
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The reconstructed chronological terms have the original
birth-distinct guard and literal lifespan coefficient certificate. -/

namespace ArtinMatthews
open Finset
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {κ : Fin n → ℤ}

def giantSignedLifespanPath_coefficientData
    (path : GiantSignedLifespanOriginalPath PS PB (ell := ell) C κ)
    {q : Fin (n+1) → ℝ} {c : ∀ (g : B) (p : PB g), GiantSignedResidueLifespanChoice (path.visits g p)}
    (hP : ∀ (g : S ⊕ B) p, p ∈ Sum.elim PS PB g → p.Prime)
    (hdis : Pairwise (fun i j : S ⊕ B => Disjoint (Sum.elim PS PB i) (Sum.elim PS PB j)))
    (hκ : ∀ i, 0 < (κ i).natAbs)
    (hsize : ∀ i g p, p ∈ Sum.elim PS PB g → (κ i).natAbs < p)
    (hw : ∀ g p, giantSignedResidueLifespanWeight p.val path.offset q (path.visits g p) (c g p) ≠ 0)
    (order : GiantSignedLifespanBirthOrderSchedule c) :
    let data := path.schedule hP hdis hκ hsize hw order
    GiantSignedChronologicalLifespanCoefficientData (A := path.visits) c (path.chronology data) path.offset := by
  let data := path.schedule hP hdis hκ hsize hw order
  exact {
    before v := (data.memory v).2
    after v := data.after_certificate v (data.memory v)
    initialInjective g := path.static.1 0 (Sum.inr g : S ⊕ B)
    initialRange g p := giantSignedActiveVisits_iff_group_slot hdis path.labels 0 (Sum.inr g : S ⊕ B) p
    targetInjective := data.target_injective
    targetRange i g p := (giantSignedLifespanPath_free_slots hP hdis hκ hsize path.static path.compatible
      i (Sum.inr g : S ⊕ B) p).2
    ghostMatch i g := ⟨order i g,rfl⟩
    edgeMatch _ := rfl }

theorem giantSignedLifespanPath_birthDistinct
    (path : GiantSignedLifespanOriginalPath PS PB (ell := ell) C κ)
    {q : Fin (n+1) → ℝ} {c : ∀ (g : B) (p : PB g), GiantSignedResidueLifespanChoice (path.visits g p)}
    (hP : ∀ (g : S ⊕ B) p, p ∈ Sum.elim PS PB g → p.Prime)
    (hdis : Pairwise (fun i j : S ⊕ B => Disjoint (Sum.elim PS PB i) (Sum.elim PS PB j)))
    (hκ : ∀ i, 0 < (κ i).natAbs)
    (hsize : ∀ i g p, p ∈ Sum.elim PS PB g → (κ i).natAbs < p)
    (hw : ∀ g p, giantSignedResidueLifespanWeight p.val path.offset q (path.visits g p) (c g p) ≠ 0)
    (order : GiantSignedLifespanBirthOrderSchedule c) :
    let data := path.schedule hP hdis hκ hsize hw order
    GiantSignedBirthDistinct (giantSignedChronologicalBirthData (path.chronology data)) := by
  let data := path.schedule hP hdis hκ hsize hw order
  let h := path.chronology data
  let coeff := giantSignedLifespanPath_coefficientData path hP hdis hκ hsize hw order
  change GiantSignedBirthDistinct (giantSignedChronologicalBirthData h)
  refine giantSignedLifespanBirthDistinct h (A := path.visits) c (fun _ _ hne => hdis (fun he => hne (Sum.inr.inj he)))
    coeff.initialInjective coeff.targetInjective
    (fun i g => Subtype.val_injective.comp (data.birthOrder i g).injective) ?_ ?_ ?_
  · intro g j
    let p := (h.state 0).2.1 g j
    have ha : (0 : Fin (n+1)) ∈ path.visits g p := (coeff.initialRange g p).mpr ⟨j,rfl⟩
    obtain ⟨L,hL,hlo,_⟩ := giantSignedPrimeLifespanView_of_active (path.visits g p) (c g p) 0 ha
    have he : L.start = 0 := Fin.ext (Nat.eq_zero_of_le_zero hlo)
    change giantSignedPrimeFreshAt (c g p) 0
    rw [giantSignedPrimeFreshAt,hL,Option.elim_some]
    exact ⟨he,ha⟩
  · intro i g j hj
    let p := data.target i g j
    have ha : i.succ ∈ path.visits g p ∧ i.castSucc ∉ path.visits g p :=
      (coeff.targetRange i g p).mp ⟨j,rfl⟩
    rcases (giantSignedPrimeNewActive_adjacent (c g p) i.castSucc i.succ rfl).mp ha with hPromote | hFresh
    · exact (hj ((giantSignedLifespanPromoteSlots_mem (c g) i.castSucc i.succ (data.target i g) j).mpr hPromote)).elim
    · exact hFresh
  · intro i g j
    exact (mem_giantSignedGhostVisitBorn (c g) i _).mp (data.birthOrder i g j).property

end
end ArtinMatthews
