module

public import ArtinMatthews.MarkedMemoryPathCapacityExpansion
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

/-! Multiplying the exact independent-line identity by an arbitrary
complex geometric coefficient retains the original baseline and the
literal omitted-cap scalar. No geometric norm bound is assumed. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (d : MarkedMemoryActivePathData P pads Z n)
  (q : ℝ) (B : ℕ)

def markedMemoryPathCappedLineContribution (z : ℂ) : ℂ :=
  ((∏ j,∏ p : P j,markedMemoryBaseline q n p.1 : ℝ):ℂ)*
    (markedMemoryPathCappedChoiceSum hZ d q B:ℂ)*z

def markedMemoryPathCapacityCorrection (z : ℂ) : ℂ :=
  ((∏ j,∏ p : P j,markedMemoryBaseline q n p.1 : ℝ):ℂ)*
    (markedMemoryPathCapacitySignedError hZ d q B:ℂ)*z

theorem markedMemoryPathLineContribution_cap_split
    (hP : ∀ i j,i≠j → Disjoint (P i) (P j))
    (hb : ∀ j (p : P j),markedMemoryBaseline q n p.1≠0) (z : ℂ) :
    (markedMemoryPathIndependentExpectation hZ d q:ℂ)*z=
      markedMemoryPathCappedLineContribution hZ d q B z+markedMemoryPathCapacityCorrection hZ d q B z := by
  rw [markedMemoryPathIndependentExpectation_capped hZ d q hP hb B]
  simp only [Complex.ofReal_mul,Complex.ofReal_add,markedMemoryPathCappedLineContribution,
    markedMemoryPathCapacityCorrection]
  ring

theorem markedMemoryPathCapacityCorrection_norm (z : ℂ) :
    ‖markedMemoryPathCapacityCorrection hZ d q B z‖=
      |∏ j,∏ p : P j,markedMemoryBaseline q n p.1| *
        |markedMemoryPathCapacitySignedError hZ d q B| * ‖z‖ := by
  simp only [markedMemoryPathCapacityCorrection,norm_mul,Complex.norm_real,Real.norm_eq_abs]

theorem markedMemoryPathBaselineProduct_bounds (hq0 : 0≤q) (hq1 : q≤1)
    (hlarge : ∀ j (p : P j),2*(n+1)≤(p.1:ℕ)+1) :
    0≤(∏ j,∏ p : P j,markedMemoryBaseline q n p.1) ∧
      (∏ j,∏ p : P j,markedMemoryBaseline q n p.1)≤1 := by
  have hb (j : J) (p : P j) := markedMemoryBaseline_bounds hq0 hq1 (hlarge j p)
  have h0 (j : J) (p : P j) : 0 ≤ markedMemoryBaseline q n p.1 := by linarith [(hb j p).1]
  exact ⟨Finset.prod_nonneg (fun j _ => Finset.prod_nonneg (fun p _ => h0 j p)),
    Finset.prod_le_one₀ (fun j _ => Finset.prod_nonneg (fun p _ => h0 j p))
      (fun j _ => Finset.prod_le_one₀ (fun p _ => h0 j p) (fun p _ => (hb j p).2))⟩

theorem markedMemoryPathCapacityCorrection_le (hq0 : 0≤q) (hq1 : q≤1)
    (hlarge : ∀ j (p : P j),2*(n+1)≤(p.1:ℕ)+1) (z : ℂ) :
    ‖markedMemoryPathCapacityCorrection hZ d q B z‖≤
      |markedMemoryPathCapacitySignedError hZ d q B| * ‖z‖ := by
  rw [markedMemoryPathCapacityCorrection_norm]
  have hb := markedMemoryPathBaselineProduct_bounds (P := P) q hq0 hq1 hlarge
  rw [abs_of_nonneg hb.1]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_left (abs_nonneg _) hb.2) (norm_nonneg z)

end
end ArtinMatthews
