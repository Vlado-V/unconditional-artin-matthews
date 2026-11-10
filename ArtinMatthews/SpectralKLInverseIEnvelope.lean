module

public import ArtinMatthews.SpectralBesselI
public import ArtinMatthews.SpectralKLCompactOrder
public import ArtinMatthews.SpectralBesselIStripBound
public import ArtinMatthews.SpectralKLCompactRapid
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory OAI.CubicEisenstein
open scoped ContDiff
noncomputable section

def spectralKLWindowData (h : ℂ → ℂ) (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  h (t : ℂ) * spectralKLCompactOrderTransform g ((t : ℂ) * Complex.I)

def spectralKLWindowSynthesis (h : ℂ → ℂ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0 < x then spectralKLWeightedSynthesis (spectralKLWindowData h g) x else 0

def spectralKLInverseIIntegrand (h : ℂ → ℂ) (g : ℝ → ℂ) (x : ℝ) (z : ℂ) : ℂ :=
  z * h z * spectralKLCompactOrderTransform g (Complex.I * z) * spectralBesselI (-Complex.I * z) x

theorem spectralKLInverseIEnvelope_scalar (t E H K J X Z a b c d : ℝ)
    (hE : 0 < E) (hH : 0 ≤ H) (hK : 0 ≤ K) (hJ : 0 ≤ J) (hX : 0 ≤ X) (hZ : 0 ≤ Z)
    (_ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hza : a ≤ 1 + |t|) (hhb : b ≤ H * (1 + t ^ 2))
    (hkc : (1 + t ^ 2) ^ 3 * E * c ≤ K)
    (hid : d ≤ J * (1 + |t|) * X * E * Z) :
    a * b * c * d ≤ (2 * H * K * J * X) * Z / (1 + t ^ 2) := by
  have hu : 0 < 1 + t ^ 2 := by positivity
  have hk : c ≤ K / ((1 + t ^ 2) ^ 3 * E) :=
    (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hkc)
  have hsquare : (1 + |t|) ^ 2 ≤ 2 * (1 + t ^ 2) := by
    nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
  calc
    _ ≤ (1 + |t|) * (H * (1 + t ^ 2)) * (K / ((1 + t ^ 2) ^ 3 * E)) *
        (J * (1 + |t|) * X * E * Z) := by gcongr
    _ = (H * K * J * X * Z) * ((1 + |t|) ^ 2 / (1 + t ^ 2) ^ 2) := by
      field_simp
    _ ≤ (H * K * J * X * Z) * ((2 * (1 + t ^ 2)) / (1 + t ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsquare (by positivity)) (by positivity)
    _ = _ := by field_simp

theorem spectralKLInverseIIntegrand_strip_bound (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ))
    (H : ℝ) (hH : 0 ≤ H)
    (hh : ∀ t y : ℝ, 0 ≤ y → y ≤ 3 / 4 →
      ‖h ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤ H * (1 + t ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t y x : ℝ, 0 ≤ y → y ≤ 3 / 4 → 0 < x →
      ‖spectralKLInverseIIntegrand h g x ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        C * Real.exp x * x ^ y / (1 + t ^ 2) := by
  obtain ⟨K, hK, hk⟩ := spectralKLCompactOrderTransform_strip_rapid g hg hc hp 3
  obtain ⟨J, hJ, hI⟩ := spectralBesselI_closed_strip_exp_bound (3 / 4) (by norm_num)
  refine ⟨2 * H * K * J, by positivity, ?_⟩
  intro t y x hy0 hyB hx
  let z : ℂ := (t : ℂ) + (y : ℂ) * Complex.I
  have hiorder : -Complex.I * z = (y : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by dsimp [z]; push_cast; linear_combination -(y : ℂ) * Complex.I_sq
  have hkorder : Complex.I * z = -(y : ℂ) + (t : ℂ) * Complex.I := by dsimp [z]; linear_combination (y : ℂ) * Complex.I_sq
  have hz : ‖z‖ ≤ 1 + |t| := by
    calc
      _ ≤ ‖(t : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |t| + y := by rw [norm_mul]; simp [abs_of_nonneg hy0]
      _ ≤ _ := by linarith
  have hk' := hk y t (by rw [abs_of_nonneg hy0]; exact hyB)
  have hi := hI y (-t) x hy0 hyB hx
  rw [abs_neg, Real.exp_add] at hi
  rw [← hiorder] at hi
  rw [← hkorder] at hk'
  have hb := spectralKLInverseIEnvelope_scalar t (Real.exp (Real.pi * |t| / 2))
    H K J (Real.exp x) (x ^ y) ‖z‖ ‖h z‖
    ‖spectralKLCompactOrderTransform g (Complex.I * z)‖ ‖spectralBesselI (-Complex.I * z) x‖
    (Real.exp_pos _) hH hK hJ.le (Real.exp_nonneg _) (Real.rpow_nonneg hx.le _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    hz (hh t y hy0 hyB) hk' (by simpa only [mul_assoc] using hi)
  simpa only [spectralKLInverseIIntegrand, norm_mul, z, mul_assoc] using hb

end
end ArtinMatthews
