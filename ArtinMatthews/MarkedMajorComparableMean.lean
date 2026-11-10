module

public import ArtinMatthews.MarkedMajorFourierWeight
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.MarkedMajorMellinLocalMean
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

namespace ArtinMatthews
open Filter MeasureTheory Set
noncomputable section

theorem markedMajorFourierWeight_mono_scale {V W : ℝ} (hV : 0 < V) (hVW : V ≤ W)
    (n : ℕ) (t : ℝ) : markedMajorFourierWeight V n t ≤ markedMajorFourierWeight W n t := by
  have hW : 0 < W := hV.trans_le hVW
  unfold markedMajorFourierWeight
  apply inv_anti₀
  · positivity
  · exact pow_le_pow_left₀ (by positivity)
      (add_le_add_right (div_le_div_of_nonneg_left (abs_nonneg t) hV hVW) 1) n

theorem markedMajorLocalMean_mono_scale (Q : ℝ → ℂ) (hQ : Continuous Q)
    (hB : ∃ B, ∀ t, ‖Q t‖ ≤ B) {V W : ℝ} (hV : 0 < V) (hVW : V ≤ W) (c : ℝ) :
    (∫ t, markedMajorFourierWeight V 2 (t-c)*‖Q t‖^2) ≤
      ∫ t, markedMajorFourierWeight W 2 (t-c)*‖Q t‖^2 := by
  obtain ⟨B,hB⟩ := hB
  exact integral_mono (markedMajorLocalMean_integrable Q hQ B hB hV c)
    (markedMajorLocalMean_integrable Q hQ B hB (hV.trans_le hVW) c)
    (fun t => mul_le_mul_of_nonneg_right (markedMajorFourierWeight_mono_scale hV hVW 2 (t-c)) (sq_nonneg _))

theorem markedMajorLocalMean_mono_radius (Q : ℝ → ℂ) (hQ : Continuous Q)
    {S T : ℝ} (hST : S ≤ T) :
    (∫ t in Icc (-S) S, ‖Q t‖^2) ≤ ∫ t in Icc (-T) T, ‖Q t‖^2 := by
  exact setIntegral_mono_set ((hQ.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (Filter.Eventually.of_forall (fun _ h => ⟨(neg_le_neg hST).trans h.1,h.2.trans hST⟩))

theorem markedMajorComparable_central_radius {L X X' B : ℝ}
    (hL : 2 ≤ L) (hX' : 0 ≤ X') (hXX' : X ≤ 2*X') :
    2*X*L^B ≤ 2*X'*L^(B+1) := by
  have hLp : 0 < L := by linarith
  rw [Real.rpow_add hLp,Real.rpow_one]
  have hpow : 0 ≤ L^B := Real.rpow_nonneg hLp.le B
  nlinarith [mul_le_mul_of_nonneg_right hXX' hpow,
    mul_nonneg hX' hpow, mul_nonneg (mul_nonneg hX' hpow) (sub_nonneg.mpr hL)]

end
end ArtinMatthews
