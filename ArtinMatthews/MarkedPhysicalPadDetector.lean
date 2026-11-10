module

public import ArtinMatthews.MarkedPhysicalDetectorReindex
public import ArtinMatthews.MarkedPhysicalDetectorArithmetic
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual shared-pad detector block. Physical state validity and
the full cross-edge ban remain in the residual, while the exact dyad
factor and original physical normalization are factored outside. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (pads : ℕ)

def markedPhysicalPadRawSource (c : MarkedPhysicalMarking P pads) (b : (j : J) → ↥(P j)) :=
  (markedPhysicalMarkingEquiv P hP (pads+1)).symm ((markedPhysicalMarkingSplit pads).symm (c,b))

omit [Fintype J] [DecidableEq J] in
theorem markedPhysicalPadRawSource_split (c : MarkedPhysicalMarking P pads) (b : (j : J) → ↥(P j)) :
    (markedRawActiveSplit pads) (markedPhysicalPadRawSource P hP pads c b)=
      ((markedPhysicalMarkingEquiv P hP pads).symm c,
        fun j => (markedRawPrimeBandEquiv (P j) (hP j)).symm (b j)) := by
  ext j k <;> simp [markedPhysicalPadRawSource,markedRawActiveSplit,
    markedPhysicalMarkingEquiv,markedPhysicalMarkingSplit]

omit [DecidableEq J] in
theorem markedPhysicalPadRawSource_copied (c : MarkedPhysicalMarking P pads) (b : (j : J) → ↥(P j)) :
    markedRawCopiedProduct ((markedRawActiveSplit pads) (markedPhysicalPadRawSource P hP pads c b)).1=
      markedPhysicalMarkingProduct c := by
  rw [markedPhysicalPadRawSource_split]
  rfl

omit [DecidableEq J] in
theorem markedPhysicalPadRawSource_last (c : MarkedPhysicalMarking P pads) (b : (j : J) → ↥(P j)) :
    markedRawLastProduct ((markedRawActiveSplit pads) (markedPhysicalPadRawSource P hP pads c b)).2=
      ∏ j,(b j:ℕ) := by
  rw [markedPhysicalPadRawSource_split]
  rfl

omit [Fintype J] [DecidableEq J] in
theorem markedPhysicalPadRawSource_crossBan (c : MarkedPhysicalMarking P pads)
    (b a : (j : J) → ↥(P j)) :
    MarkedRawFullCrossBan (markedPhysicalPadRawSource P hP pads c b)
      ((markedRawActiveSplit pads) (markedPhysicalPadRawSource P hP pads c a)).2 ↔
      MarkedPhysicalCrossBan ((markedPhysicalMarkingSplit pads).symm (c,b)) a := by
  rw [markedPhysicalPadRawSource_split]
  have h := markedPhysicalCrossBan_raw P hP (markedPhysicalPadRawSource P hP pads c b)
    (fun j => (markedRawPrimeBandEquiv (P j) (hP j)).symm (a j))
  simpa only [markedPhysicalPadRawSource,Equiv.apply_symm_apply] using h

variable (Z : Finset (ℤ × ℤ))
  (η : ℝ → ℂ) (Y : ℝ) (detector : ℤ → ℤ → ℤ → ℂ)
  (f g : MarkedPhysicalState P (pads+1) Z → ℂ)

def markedPhysicalPadDetectorResidual (c : MarkedPhysicalMarking P pads)
    (b a : (j : J) → ↥(P j)) (z w : Z) : ℂ :=
  let source := (markedPhysicalMarkingSplit pads).symm (c,b)
  let target := (markedPhysicalMarkingSplit pads).symm (c,a)
  let D := markedPhysicalMarkingProduct c
  if hs : MarkedPhysicalStateCondition z.1 source then
    if ht : MarkedPhysicalStateCondition w.1 target then
      if (D:ℤ) ∣ markedMinorIntegerDet z.1 w.1 then
        if MarkedPhysicalCrossBan source a then 0 else
          η (((∏ j,(b j:ℕ)):ℝ)/Y)*η (((∏ j,(a j:ℕ)):ℝ)/Y)*
            detector (∏ j,(b j:ℕ)) (∏ j,(a j:ℕ)) (markedMinorIntegerDet z.1 w.1/(D:ℤ))*
            star (f ⟨(z,source),hs⟩)*g ⟨(w,target),ht⟩
      else 0 else 0 else 0

theorem markedPhysicalDetectorPairTerm_pad_factor
    (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (V : J → ℝ) (d₀ : ℝ)
    (c : MarkedPhysicalMarking P pads) (b a : (j : J) → ↥(P j)) (z w : Z) :
    markedPhysicalDetectorPairTerm P hP V pads Z hZ η d₀ Y 1 detector f g
      (z,(markedPhysicalMarkingSplit pads).symm (c,b))
      (w,(markedPhysicalMarkingSplit pads).symm (c,a))=
      if d₀ ≤ (markedPhysicalMarkingProduct c:ℝ) ∧ (markedPhysicalMarkingProduct c:ℝ)<2*d₀ then
        (markedPhysicalMass V (pads+2):ℂ)*((d₀/(markedPhysicalMarkingProduct c:ℝ):ℝ):ℂ)*
          markedPhysicalPadDetectorResidual P pads Z η Y detector f g c b a z w
      else 0 := by
  unfold markedPhysicalDetectorPairTerm markedPhysicalStateExtend
  by_cases hs : MarkedPhysicalStateCondition z.1 ((markedPhysicalMarkingSplit pads).symm (c,b))
  · rw [dite_eq_left hs]
    dsimp only
    by_cases ht : MarkedPhysicalStateCondition w.1 ((markedPhysicalMarkingSplit pads).symm (c,a))
    · rw [dite_eq_left ht]
      let ss : MarkedPhysicalState P (pads+1) Z := ⟨(z,(markedPhysicalMarkingSplit pads).symm (c,b)),hs⟩
      let tt : MarkedPhysicalState P (pads+1) Z := ⟨(w,(markedPhysicalMarkingSplit pads).symm (c,a)),ht⟩
      rw [markedPhysicalEdgeDetectorCoefficient_arithmetic]
      have hp : ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z ss).2.1).1=
          ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z tt).2.1).1 := by
        apply (markedPhysicalStateToRaw_copied_eq_iff P hP pads Z ss tt).mpr
        exact (congrArg Prod.fst ((markedPhysicalMarkingSplit pads).apply_symm_apply (c,b))).trans
          (congrArg Prod.fst ((markedPhysicalMarkingSplit pads).apply_symm_apply (c,a))).symm
      rw [ite_eq_left hp]
      have hD : markedRawCopiedProduct ((markedRawActiveSplit pads)
          (markedPhysicalStateToRaw P hP (pads+1) Z ss).2.1).1=markedPhysicalMarkingProduct c :=
        markedPhysicalPadRawSource_copied P hP pads c b
      have hb : markedRawLastProduct ((markedRawActiveSplit pads)
          (markedPhysicalStateToRaw P hP (pads+1) Z ss).2.1).2=∏ j,(b j:ℕ) :=
        markedPhysicalPadRawSource_last P hP pads c b
      have ha : markedRawLastProduct ((markedRawActiveSplit pads)
          (markedPhysicalStateToRaw P hP (pads+1) Z tt).2.1).2=∏ j,(a j:ℕ) :=
        markedPhysicalPadRawSource_last P hP pads c a
      have hban : MarkedRawFullCrossBan (markedPhysicalStateToRaw P hP (pads+1) Z ss).2.1
          ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z tt).2.1).2 ↔
          MarkedPhysicalCrossBan ((markedPhysicalMarkingSplit pads).symm (c,b)) a :=
        markedPhysicalPadRawSource_crossBan P hP pads c b a
      rw [hD,hb,ha,propext hban]
      unfold markedPhysicalDetectorArithmetic
      unfold markedPhysicalPadDetectorResidual
      dsimp only
      rw [dite_eq_left hs,dite_eq_left ht]
      simp only [Nat.cast_prod]
      split_ifs <;> ring
    · rw [dite_eq_right ht]
      simp only [markedPhysicalPadDetectorResidual,dite_eq_left hs,dite_eq_right ht,mul_zero,ite_self]
  · rw [dite_eq_right hs]
    simp only [markedPhysicalPadDetectorResidual,dite_eq_right hs,mul_zero,ite_self]

end
end ArtinMatthews
