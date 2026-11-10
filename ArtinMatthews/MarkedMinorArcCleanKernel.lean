module

public import ArtinMatthews.MarkedMinorArcProductOperator
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact identification with PD (mem:clean-kernel). -/
namespace ArtinMatthews
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The checked compression is exactly the source clean kernel, with the
actual determinant cutoff and integer product difference. -/
theorem markedMinorCleanProductMatrix_apply (ψ : SchwartzMap ℝ ℂ)
    (L T : ℤ) (M N : ℕ) (Y Q : ℝ) (S : Finset ℤ)
    (h l : MarkedMinorBoxIndex L T M N) (b a : S) :
    markedMinorCleanProductMatrix ψ L T M N Y Q S (h,b) (l,a) =
      ((Y : ℂ)⁻¹)*ψ (((h.1.1*l.1.2-h.1.2*l.1.1 : ℤ) : ℝ)/Y) *
      ∫ θ : AddCircle (1:ℝ) in (markedMinorCircleMajor Q Y)ᶜ,
        fourier ((h.1.1*l.1.2-h.1.2*l.1.1)-b.1+a.1) θ ∂AddCircle.haarAddCircle := by
  classical
  unfold markedMinorCleanProductMatrix markedProductCompressionMatrix
  rw [← integral_const_mul,← integral_indicator (markedMinorCircleMajor_measurable Q Y).compl]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun θ => by
    by_cases hθ : θ ∈ markedMinorCircleMajor Q Y
    · simp [Set.indicator,markedMinorCircleFiber,hθ]
    · simp only [markedMinorCircleFiber,markedMinorSmoothCircleMatrix,
        Set.indicator,Set.mem_compl_iff,hθ,ite_false,not_false_eq_true,ite_true,
        sub_eq_add_neg,fourier_add]
      ring)

end ArtinMatthews
