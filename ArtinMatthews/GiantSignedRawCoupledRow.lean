module

public import ArtinMatthews.GiantSignedEdgeCoupledPairing
public import ArtinMatthews.GiantSignedRawPositiveAverage
public import ArtinMatthews.GiantSignedEdgeCoupledChoice
public import ArtinMatthews.GiantSignedRawSourceGateMass
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

/-! Exact coupled raw rows on the original endpoint and auxiliary law. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]
    {C : B → Finset (Fin k)}

abbrev GiantSignedRawCoupledTest (PS : S → Finset ℕ) (PB : B → Finset ℕ)
    (C : B → Finset (Fin k)) (ell : ℕ) :=
  ((j : B) → Finset (Fin (ell + (C j).card))) →
    ((j : B) → Finset (Fin (ell + (C j).card))) →
      GiantSignedState PS PB (k+ell) → GiantSignedState PS PB (k+ell) → ℝ

def giantSignedRawCoupledRow (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : ℤ) (q ρ : ℝ) (F : GiantSignedRawCoupledTest PS PB C ell)
    (s : GiantSignedState PS PB (k+ell)) : ℝ :=
  ∑ r : GiantSignedRawEdgeMove PS PB ell C s.2.2,
    giantSignedRawPositiveCoefficient ν V κ q ρ s r *
      if GiantSignedEdgePromotionBan (giantSignedRawEdgeProduct s r) r.choice.1
          (giantSignedPatternFreeLabels C (giantSignedRawEdgeBigSource s r)) then
        F r.choice.1 r.choice.2.1 s (giantSignedRawEdgeTarget κ s r)
      else 0

def giantSignedRawCoupledFiberTest
    (F : GiantSignedRawCoupledTest PS PB C ell)
    (i : GiantSignedRawOuterChoice (S := S) PB C ell)
    (x z : GiantTwoSidedResidueState PS (k+ell)) (D : ℕ)
    (inflate : GiantSignedPrimeTuple PB (fun j => ell + (C j).card) →
      MarkedPhysicalMarking PB (k+ell)) :
    GiantSignedEdgeCoupledTest PB (fun j => ell + (C j).card) ℝ :=
  fun X Y a b old out =>
    if GiantSignedEdgePromotionBan D X a ∧ GiantSignedEdgePromotionBan D Y b then
      F X Y ((giantSignedStatePermute PS i.1.1 i.1.2).symm (x, inflate a, old))
        ((giantSignedStatePermute PS i.2.1.1 i.2.1.2).symm (z, inflate b, out))
    else 0

def giantSignedRawCoupledSection (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : ℤ) (q ρ : ℝ) (F : GiantSignedRawCoupledTest PS PB C ell)
    (i : GiantSignedRawOuterChoice (S := S) PB C ell)
    (x : GiantTwoSidedResidueState PS (k+ell))
    (a : MarkedPhysicalMarking PB (k+ell)) (m : GiantSignedMemory PB) : ℝ :=
  let DBig := giantTwoSidedPatternCopiedProduct C a *
    giantTwoSidedPatternAuxiliaryProduct i.2.2
  let D := giantSignedSmallPrefixProduct x * DBig
  ∑ z : GiantTwoSidedResidueState PS (k+ell),
    giantSignedSmallEdgeWeight κ DBig q x z *
      giantSignedEdgeCoupledApply ν V ρ (κ * (D : ℤ))
        (giantSignedRawCoupledFiberTest F i x z D (giantSignedPatternFill C a))
        (giantSignedPatternFreeLabels C a) m

private theorem patternFill_self (a : MarkedPhysicalMarking PB (k+ell)) :
    giantSignedPatternFill C a (giantSignedPatternFreeLabels C a) = a := by
  let e := giantSignedPatternSourceEquiv (P := PB) (ell := ell) C
  have ha : giantSignedPatternSourceFill C (e a).1 (e a).2 = a := e.symm_apply_apply a
  change giantSignedPatternFill C a (e a).2 = a
  calc
    _ = giantSignedPatternFill C (giantSignedPatternSourceFill C (e a).1 (e a).2) (e a).2 :=
      congrArg (fun a' => giantSignedPatternFill C a' (e a).2) ha.symm
    _ = _ := (giantSignedPatternSourceFill_patternFill C (e a).1 (e a).2 (e a).2).trans ha

theorem giantSignedRawCoupledSection_choice_sum
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (V : B → ℝ) (hV : ∀ g, 0 < V g)
    (κ : ℤ) (q : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (F : GiantSignedRawCoupledTest PS PB C ell)
    (i : GiantSignedRawOuterChoice (S := S) PB C ell)
    (x : GiantTwoSidedResidueState PS (k+ell))
    (a : MarkedPhysicalMarking PB (k+ell)) (m : GiantSignedMemory PB) :
    giantSignedRawCoupledSection ν V κ q ρ F i x a m =
      let DBig := giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct i.2.2
      let D := giantSignedSmallPrefixProduct x * DBig
      ∑ z : GiantTwoSidedResidueState PS (k+ell), giantSignedSmallEdgeWeight κ DBig q x z *
        ∑ c : GiantSignedEdgeChoice (fun j => ell + (C j).card) m.1,
          ∑ b : MarkedPhysicalMarking PB (k+ell),
            if IdealCopied C a b then
              ‖giantSignedEdgeMoveCoefficient (fun j p => (ν j p : ℂ)) V ρ (κ * (D : ℤ)) D
                (giantSignedPatternFreeLabels C a) (giantSignedPatternFreeLabels C b) m c‖ *
                if GiantSignedEdgePromotionBan D c.1 (giantSignedPatternFreeLabels C a) then
                  F c.1 c.2.1 ((giantSignedStatePermute PS i.1.1 i.1.2).symm (x,a,m))
                    ((giantSignedStatePermute PS i.2.1.1 i.2.1.2).symm
                      (z,b,giantSignedEdgeTarget (κ * (D : ℤ)) m (giantSignedPatternFreeLabels C a) c))
                else 0
            else 0 := by
  unfold giantSignedRawCoupledSection giantSignedRawCoupledFiberTest
  dsimp only
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  rw [giantSignedEdgeCoupledApply_bothBans_choice_sum ν hν V hV hρ]
  apply Finset.sum_congr rfl
  intro c _
  rw [← giantSignedCopiedTarget_plain_sum C a]
  simp only [giantSignedPatternFreeLabels_fill, patternFill_self]

theorem giantSignedRawCoupledRow_average
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (V : B → ℝ) (hV : ∀ g, 0 < V g)
    (κ : ℤ) (q : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (F : GiantSignedRawCoupledTest PS PB C ell)
    (s : GiantSignedState PS PB (k+ell)) :
    giantSignedRawCoupledRow ν V κ q ρ F s =
      ∑ i : GiantSignedRawOuterChoice (S := S) PB C ell, giantSignedRawOuterWeight i *
        giantSignedRawCoupledSection ν V κ q ρ F i
          (giantTwoSidedResiduePermute i.1.1 s.1)
          (giantSignedGroupedTuplePermutation i.1.2 s.2.1) s.2.2 := by
  let I := GiantSignedRawOuterChoice (S := S) PB C ell
  let T := GiantSignedEdgeChoice (fun j => ell + (C j).card) s.2.2.1 ×
    (GiantTwoSidedResidueState PS (k+ell) × MarkedPhysicalMarking PB (k+ell))
  let e : GiantSignedRawEdgeMove PS PB ell C s.2.2 ≃ I × T :=
    { toFun := fun r => (giantSignedRawMoveOuter r, r.choice, r.smallTarget, r.bigTarget)
      invFun := fun p => ⟨p.1.1.1,p.1.1.2,p.1.2.1.1,p.1.2.1.2,p.1.2.2,
        p.2.1,p.2.2.1,p.2.2.2⟩
      left_inv := by intro r; cases r; rfl
      right_inv := by rintro ⟨⟨⟨a,b⟩,⟨c,d⟩,f⟩,g,h,j⟩; rfl }
  unfold giantSignedRawCoupledRow
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [giantSignedRawCoupledSection_choice_sum ν hν V hV κ q hρ F i]
  simp only [T, Fintype.sum_prod_type, e, Equiv.coe_fn_symm_mk,
    giantSignedRawPositiveCoefficient, giantSignedRawEdgeProduct, giantSignedRawEdgeSmallSource,
    giantSignedRawEdgeBigSource, giantSignedRawEdgeTarget, giantSignedSmallPrefixProduct]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro b _
  have he : (giantSignedStatePermute PS i.1.1 i.1.2).symm
      (giantTwoSidedResiduePermute i.1.1 s.1, giantSignedGroupedTuplePermutation i.1.2 s.2.1,
        s.2.2) = s :=
    (giantSignedStatePermute PS i.1.1 i.1.2).symm_apply_apply s
  rw [he]
  by_cases hc : IdealCopied C (giantSignedGroupedTuplePermutation i.1.2 s.2.1) b
  · have hw : giantSignedRawOuterWeight ((i.1.1,i.1.2),(i.2.1.1,i.2.1.2),i.2.2) =
        giantSignedRawOuterWeight i := rfl
    rw [hw]
    simp only [hc, ite_true, giantSignedStatePermute, Equiv.prodCongr_symm,
      Equiv.prodCongr_apply, Equiv.refl_symm, Prod.map, Equiv.refl_apply]
    ac_rfl
  · simp only [hc, ite_false, mul_zero, zero_mul]

end
end ArtinMatthews
