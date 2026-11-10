module

public import ArtinMatthews.MarkedMinorArcDirtySecondGood
public import ArtinMatthews.MarkedTypeIIGoodSecondDecay
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

/-! The beta trial set is exactly the checked second-good trial model,
under a genuine finite reindex of the full source omission tuple. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

theorem markedRawDirtyFullTrials_eq_second {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ)
    (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x)) (I : Finset J) :
    markedRawDirtyFullTrials e x source I =
      markedSecondTrialValues (Fintype.card J) (fun j : I => e j.1) x
        (fun o => markedSourceCopiedProduct (markedRawNumericActive source)
          (fun j => o (Fintype.equivFin J j))) := by
  classical
  unfold markedRawDirtyFullTrials markedSecondTrialValues markedGoodTrialValues
  rw [Finset.image_image]
  ext q
  constructor
  · intro hq
    obtain ⟨⟨o,p⟩,_,hq⟩ := Finset.mem_image.mp hq
    apply Finset.mem_image.mpr
    refine ⟨((fun k => o ((Fintype.equivFin J).symm k)),p),Finset.mem_univ _,?_⟩
    have heq : (fun j => o ((Fintype.equivFin J).symm (Fintype.equivFin J j)))=o := by
      funext j
      rw [Equiv.symm_apply_apply]
    change Int.ofNat (markedSourceCopiedProduct (markedRawNumericActive source)
      (fun j => o ((Fintype.equivFin J).symm (Fintype.equivFin J j))) * ∏ j : I,(p j:ℕ))=q
    rw [heq]
    exact hq
  · intro hq
    obtain ⟨⟨o,p⟩,_,hq⟩ := Finset.mem_image.mp hq
    apply Finset.mem_image.mpr
    exact ⟨((fun j => o (Fintype.equivFin J j)),p),Finset.mem_univ _,hq⟩

theorem markedRawDirty_other_exponents_lt {J : Type*} [DecidableEq J]
    (e : J → ℝ) (hinj : Function.Injective e) (I : Finset J) (jstar : J)
    (hmax : ∀ j ∈ I,e j ≤ e jstar) (j : ↥(I.erase jstar)) : e j.1<e jstar := by
  apply lt_of_le_of_ne (hmax j.1 (Finset.mem_of_mem_erase j.2))
  intro he
  exact (Finset.mem_erase.mp j.2).1 (hinj he)

end
end ArtinMatthews
