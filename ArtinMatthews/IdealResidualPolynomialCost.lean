module

public import ArtinMatthews.IdealResidualFamily
public import ArtinMatthews.IdealResidualCost
public import ArtinMatthews.IdealResidualNumerics
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The actual comparison coefficient budget is a fixed power of L.
Its exponent does not involve the copied-list dimension. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealResidualScalarCost_bound (L B a X : ℝ) (P : ℕ)
    (hL : 2 ≤ L) (hB : 0 ≤ B) (ha : 0 ≤ a) (hX : 0 ≤ X)
    (hP : (P:ℝ) ≤ B*Real.log L) :
    (1+(2:ℝ)^P)*(1+(((⌊L^a⌋₊:ℕ):ℝ)^2/L^(-X))^2) ≤
      L^(B*Real.log 2+4*a+2*X+2) := by
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hb : 0 ≤ B*Real.log 2 := mul_nonneg hB (Real.log_nonneg (by norm_num))
  have hq : ((⌊L^a⌋₊:ℕ):ℝ) ≤ L^a := Nat.floor_le (Real.rpow_nonneg hLpos.le a)
  have hfrac : ((⌊L^a⌋₊:ℕ):ℝ)^2/L^(-X) ≤ L^(2*a+X) := by
    rw [Real.rpow_neg hLpos.le X,div_inv_eq_mul]
    calc
      _ ≤ (L^a)^2*L^X := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hq 2) (Real.rpow_nonneg hLpos.le X)
      _ = _ := by
        rw [← Real.rpow_two,← Real.rpow_mul hLpos.le,← Real.rpow_add hLpos]
        congr 1
        ring
  have hsq : (((⌊L^a⌋₊:ℕ):ℝ)^2/L^(-X))^2 ≤ L^(4*a+2*X) := by
    calc
      _ ≤ (L^(2*a+X))^2 := pow_le_pow_left₀ (by positivity) hfrac 2
      _ = _ := by
        rw [← Real.rpow_two,← Real.rpow_mul hLpos.le]
        congr 1
        ring
  have hfirst : 1+(2:ℝ)^P ≤ 2*L^(B*Real.log 2) := by
    have hpow := Real.one_le_rpow hL1 hb
    have hc := idealComparison_count_power L B P hL1 hP
    linarith
  have hsecond : 1+(((⌊L^a⌋₊:ℕ):ℝ)^2/L^(-X))^2 ≤ 2*L^(4*a+2*X) := by
    have hpow := Real.one_le_rpow hL1 (by linarith : 0 ≤ 4*a+2*X)
    linarith
  calc
    _ ≤ (2*L^(B*Real.log 2))*(2*L^(4*a+2*X)) :=
      mul_le_mul hfirst hsecond (by positivity) (by positivity)
    _ = 4*L^(B*Real.log 2+4*a+2*X) := by
      rw [show B*Real.log 2+4*a+2*X=B*Real.log 2+(4*a+2*X) by ring,
        Real.rpow_add hLpos (B*Real.log 2) (4*a+2*X)]
      ring
    _ ≤ L^2*L^(B*Real.log 2+4*a+2*X) :=
      mul_le_mul_of_nonneg_right (by nlinarith : (4:ℝ) ≤ L^2) (Real.rpow_nonneg hLpos.le _)
    _ = _ := by
      rw [← Real.rpow_two,← Real.rpow_add hLpos]
      congr 1
      ring

theorem idealResidualCoefficient_polynomial_cost {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (S T : Finset (G × Fin k))
    (L B a X h : ℝ) (hL : 2 ≤ L) (hB : 0 ≤ B) (ha : 0 ≤ a) (hX : 0 ≤ X)
    (hST : ((S.card+T.card:ℕ):ℝ) ≤ B*Real.log L)
    (s t : IdealResidualPattern G k → MarkedPhysicalMarking P (k+ell))
    (aux : ∀ ν,GiantTwoSidedPatternAuxiliary P (idealResidualCopied ν)) :
    (∑ ν∈idealResidualPatterns S T,
      ‖idealResidualCoefficient P ⌊L^a⌋₊ h (L^(-X)) ν (s ν) (t ν) (aux ν)‖) ≤
      L^(B*Real.log 2+4*a+2*X+2) := by
  have hLpos : 0 < L := by linarith
  have hc := idealResidualCoefficient_total_cost P S T ⌊L^a⌋₊ h
    (Real.rpow_pos_of_pos hLpos (-X)) s t aux
  push_cast at hc
  exact hc.trans (idealResidualScalarCost_bound L B a X (S.card+T.card) hL hB ha hX hST)

end
end ArtinMatthews
