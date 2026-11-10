module

public import ArtinMatthews.MarkedMemoryIndependentPathChoices
public import ArtinMatthews.MarkedMemoryActivePathFinite
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

/-! Prime-valued path and interval-choice coordinates are invariant
under genuine particle-ID relabeling. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A A' : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  [∀ j,Fintype (A' j)] [∀ j,DecidableEq (A' j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (e : (j : J) → A j ≃ A' j)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (hinj : Function.Injective (markedMemoryIndependentPrime hZ d))

include hinj in
theorem markedMemoryIndependentPrime_relabel_injective :
    Function.Injective (markedMemoryIndependentPrime hZ (markedMemoryIndependentRelabel hZ e d)) := by
  intro a b he
  have hh : (Equiv.sigmaCongrRight (fun j => (e j).symm)) a=
      (Equiv.sigmaCongrRight (fun j => (e j).symm)) b := hinj he
  exact (Equiv.sigmaCongrRight (fun j => (e j).symm)).injective hh

theorem markedMemoryIndependentActivePath_relabel :
    markedMemoryIndependentActivePath hZ (markedMemoryIndependentRelabel hZ e d)
      (markedMemoryIndependentPrime_relabel_injective hZ e d hinj)=
        markedMemoryIndependentActivePath hZ d hinj := by
  apply markedMemoryActivePath_ext
  · rfl
  · funext v j
    apply Function.Embedding.ext
    intro k
    change (d.particle j ((e j).symm (e j (d.activeId v.val j k)))).1=_
    rw [Equiv.symm_apply_apply]
    rfl
  · funext v j
    change (d.particle j ((e j).symm (e j ((d.lifespan j).incoming (2*v.val+1))))).1=_
    rw [Equiv.symm_apply_apply]
    rfl
  · funext v j
    change (d.particle j ((e j).symm (e j ((d.lifespan j).outgoing (2*v.val+1))))).1=_
    rw [Equiv.symm_apply_apply]
    rfl

include hinj in
theorem markedMemoryIndependentPathChoices_relabel :
    markedMemoryIndependentPathChoices hZ (markedMemoryIndependentRelabel hZ e d)=
      markedMemoryIndependentPathChoices hZ d := by
  funext j p
  by_cases hp : ∃ a : A j,(d.particle j a).1=p
  · obtain ⟨a,rfl⟩ := hp
    have he := markedMemoryIndependentPathChoices_at hZ (markedMemoryIndependentRelabel hZ e d)
      (markedMemoryIndependentPrime_relabel_injective hZ e d hinj) j (e j a)
    have hf := markedMemoryIndependentPathChoices_at hZ d hinj j a
    have he' : markedMemoryIndependentPathChoices hZ (markedMemoryIndependentRelabel hZ e d)
        j (d.particle j a).1=markedMemoryIndependentIntervalChoice hZ d j a := by
      simpa only [markedMemoryIndependentRelabel,Equiv.symm_apply_apply,markedMemoryQueueRelabel,
        markedMemoryIndependentIntervalChoice] using he
    exact he'.trans hf.symm
  · have hn : ¬∃ a : A' j,((markedMemoryIndependentRelabel hZ e d).particle j a).1=p := by
      rintro ⟨a,ha⟩
      exact hp ⟨(e j).symm a,ha⟩
    simp only [markedMemoryIndependentPathChoices,dite_eq_right hp,dite_eq_right hn]

end
end ArtinMatthews
