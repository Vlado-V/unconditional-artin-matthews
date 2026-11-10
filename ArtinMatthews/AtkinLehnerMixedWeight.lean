module

public import ArtinMatthews.AtkinLehnerMixedPhase
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact phase cancellation and modulus normalization in ABL (DI 1.6). -/
namespace ArtinMatthews

theorem atkinPhase_zero : atkinPhase 0 = 1 := by simp [atkinPhase]

theorem atkinPhase_norm (x : ℝ) : ‖atkinPhase x‖ = 1 := by
  simp [atkinPhase,Complex.norm_exp,Complex.mul_re]

/-- The source compensating inverse-s phase removes the lower-triangular
scaling phase exactly, including both signs of the fixed frequency. -/
theorem lowerTriMixed_compensated_eq_ordinary {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (c : ℕ) [NeZero (s*c)]
    (hrq : r.Coprime (s*c)) (m n : ℤ) :
    atkinPhase ((n : ℝ)*(b : ℝ)/(r : ℝ))*lowerTriMixedResidueSum hr hab c m n =
      OAI.Erdos970.ErdosKloosterman.sum ZMod.stdAddChar
        ((m : ZMod (s*c))*(↑(ZMod.unitOfCoprime r hrq)⁻¹ : ZMod (s*c))) (n : ZMod (s*c)) := by
  rw [lowerTriMixedResidueSum_eq_ordinary hr hab c hrq,← mul_assoc,← atkinPhase_add]
  have he : (n : ℝ)*(b : ℝ)/(r : ℝ)+(-(n : ℝ)*(b : ℝ)/(r : ℝ)) = 0 := by ring
  rw [he,atkinPhase_zero,one_mul]

theorem lowerTriMixed_norm_eq_ordinary {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (c : ℕ) [NeZero (s*c)]
    (hrq : r.Coprime (s*c)) (m n : ℤ) :
    ‖lowerTriMixedResidueSum hr hab c m n‖ =
      ‖OAI.Erdos970.ErdosKloosterman.sum ZMod.stdAddChar
        ((m : ZMod (s*c))*(↑(ZMod.unitOfCoprime r hrq)⁻¹ : ZMod (s*c))) (n : ZMod (s*c))‖ := by
  rw [lowerTriMixedResidueSum_eq_ordinary hr hab c hrq,norm_mul,atkinPhase_norm,one_mul]

/-- The actual cusp modulus weight is `1/c`, with no extra square-root-r loss. -/
theorem atkinMixed_modulus_weight {r s c : ℕ} (hr : 0 < r) (hs : 0 < s) (hc : 0 < c) :
    ((s : ℝ)*Real.sqrt (r : ℝ))/((s : ℝ)*Real.sqrt (r : ℝ)*(c : ℝ)) = 1/(c : ℝ) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have ht : Real.sqrt (r : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hrR).ne'
  field_simp

end ArtinMatthews
