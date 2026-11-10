module

public import ArtinMatthews.SpectralCuspEisensteinSigns
public import ArtinMatthews.SpectralCuspEisensteinIntegral
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import OAI.MathematicalPhysics.BFSS.RellichSmoothing
public import Std.Tactic.BVDecide.Normalize.BitVec


set_option backward.privateInPublic true
@[expose] public section

/-! The zero-lower-entry sector is exactly the actual cusp-equivalence
indicator, with both signs counted before the factor one half. -/
noncomputable section
open Set Matrix MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

def gamma0EisensteinCuspsEquivalent (N : ℕ) (r a : SL(2,ℤ)) : Prop :=
  ![(0:ℤ),1] ∈ range (gamma0CuspEisensteinRow N r a)

local instance cuspEquivalent_decidable (N : ℕ) (r a : SL(2,ℤ)) :
    Decidable (gamma0EisensteinCuspsEquivalent N r a) := Classical.propDecidable _

theorem cuspEisensteinZeroRow_implies_equivalent (N : ℕ) (r a : SL(2,ℤ))
    (v : CuspEisensteinZeroRows N r a) : gamma0EisensteinCuspsEquivalent N r a := by
  rcases cuspEisensteinZeroRows_unit N r a v with h | h
  · have he : v.val.val= ![(0:ℤ),1] := by
      funext i
      fin_cases i
      · exact v.property
      · exact h
    change ![(0:ℤ),1] ∈ range (gamma0CuspEisensteinRow N r a)
    rw [← he]
    exact v.val.property
  · have he : (gamma0CuspEisensteinNegRow N r a v.val).val= ![(0:ℤ),1] := by
      funext i
      fin_cases i <;> simp [gamma0CuspEisensteinNegRow,v.property,h]
    change ![(0:ℤ),1] ∈ range (gamma0CuspEisensteinRow N r a)
    rw [← he]
    exact (gamma0CuspEisensteinNegRow N r a v.val).property

theorem gamma0EisensteinCuspsEquivalent_iff (N : ℕ) (r a : SL(2,ℤ)) :
    gamma0EisensteinCuspsEquivalent N r a ↔
      ∃ M : gamma0CuspCorrespondence N r a, M.val 1 0=0 := by
  constructor
  · rintro ⟨M,hM⟩
    exact ⟨M,congrFun hM 0⟩
  · rintro ⟨M,hM⟩
    exact cuspEisensteinZeroRow_implies_equivalent N r a
      ⟨⟨M.val 1,⟨M,rfl⟩⟩,hM⟩

def cuspEisensteinZeroRow (N : ℕ) (r a : SL(2,ℤ))
    (h : gamma0EisensteinCuspsEquivalent N r a) (b : Bool) : CuspEisensteinZeroRows N r a :=
  if b then ⟨⟨![(0:ℤ),1],h⟩,rfl⟩
  else ⟨gamma0CuspEisensteinNegRow N r a ⟨![(0:ℤ),1],h⟩,rfl⟩

theorem cuspEisensteinZeroRows_sign_injective (N : ℕ) (r a : SL(2,ℤ)) :
    Function.Injective (fun v : CuspEisensteinZeroRows N r a => decide (v.val.val 1=1)) := by
  intro v w h
  rcases cuspEisensteinZeroRows_unit N r a v with hv | hv <;>
    rcases cuspEisensteinZeroRows_unit N r a w with hw | hw
  all_goals try {simp only [hv,hw] at h; contradiction}
  all_goals
    apply Subtype.ext
    apply Subtype.ext
    funext i
    fin_cases i
    · exact v.property.trans w.property.symm
    · exact hv.trans hw.symm

instance cuspEisensteinZeroRows_finite (N : ℕ) (r a : SL(2,ℤ)) :
    Finite (CuspEisensteinZeroRows N r a) :=
  Finite.of_injective _ (cuspEisensteinZeroRows_sign_injective N r a)

instance cuspEisensteinZeroRows_fintype (N : ℕ) (r a : SL(2,ℤ)) :
    Fintype (CuspEisensteinZeroRows N r a) := Fintype.ofFinite _

def cuspEisensteinZeroRowEquiv (N : ℕ) (r a : SL(2,ℤ))
    (h : gamma0EisensteinCuspsEquivalent N r a) : Bool ≃ CuspEisensteinZeroRows N r a where
  toFun := cuspEisensteinZeroRow N r a h
  invFun v := decide (v.val.val 1=1)
  left_inv b := by cases b <;> simp [cuspEisensteinZeroRow,gamma0CuspEisensteinNegRow]
  right_inv v := by
    apply cuspEisensteinZeroRows_sign_injective N r a
    rcases cuspEisensteinZeroRows_unit N r a v with hv | hv <;>
      simp [hv,cuspEisensteinZeroRow,gamma0CuspEisensteinNegRow]

theorem cuspEisensteinZeroRows_card (N : ℕ) (r a : SL(2,ℤ)) :
    Fintype.card (CuspEisensteinZeroRows N r a)=
      if gamma0EisensteinCuspsEquivalent N r a then 2 else 0 := by
  classical
  by_cases h : gamma0EisensteinCuspsEquivalent N r a
  · simpa only [h,ite_true,Fintype.card_bool] using
      (Fintype.card_congr (cuspEisensteinZeroRowEquiv N r a h)).symm
  · have he : IsEmpty (CuspEisensteinZeroRows N r a) :=
      ⟨fun v => h (cuspEisensteinZeroRow_implies_equivalent N r a v)⟩
    have := he
    simp [h]

theorem cuspEisensteinRowIntegral_zero (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (y : ℝ) (hy : 0 < y) (v : CuspEisensteinZeroRows N r a) :
    cuspEisensteinRowIntegral N r a s y hy v.val =
      (gamma0CuspTrueWidth N r:ℂ)^s*(y:ℂ)^s := by
  unfold cuspEisensteinRowIntegral
  simp_rw [cuspEisensteinRowTerm_zero]
  have him (x : ℝ) : (cuspEisensteinTargetPoint N r y hy x).im=
      (gamma0CuspTrueWidth N r:ℝ)*y := cuspWidthDilation_im_smul _ _ _
  simp_rw [him,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg
    (show (0:ℝ) ≤ gamma0CuspTrueWidth N r by positivity) hy.le]
  simp

theorem cuspEisensteinZeroIntegral_sum (N : ℕ) [NeZero N] (r a : SL(2,ℤ))
    (s : ℂ) (y : ℝ) (hy : 0 < y) :
    (∑' v : CuspEisensteinZeroRows N r a, cuspEisensteinRowIntegral N r a s y hy v.val)=
      (if gamma0EisensteinCuspsEquivalent N r a then 2 else 0 : ℂ)*
        (gamma0CuspTrueWidth N r:ℂ)^s*(y:ℂ)^s := by
  classical
  simp_rw [cuspEisensteinRowIntegral_zero]
  rw [tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,cuspEisensteinZeroRows_card]
  push_cast
  ring

end ArtinMatthews
