module

public import ArtinMatthews.SpectralCuspTrueWidthPhysicalMoment
public import ArtinMatthews.SpectralKExceptionalPhysicalTest
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

/-! The real-order lower bound controls a literal finite exceptional
moment of the actual normalized cusp amplitudes. -/

noncomputable section
open Set MeasureTheory
open OAI.CubicEisenstein
open scoped MatrixGroups BigOperators ComplexOrder

namespace ArtinMatthews

theorem spectralComplexSqrt_quarter_sub_nonneg (eig : ℝ) (heig : eig ≤ 1/4) :
    Complex.sqrt (1/4-(eig : ℂ)) = (Real.sqrt (1/4-eig) : ℂ) := by
  have hp : (0 : ℂ) ≤ ((1/4-eig : ℝ) : ℂ) :=
    RCLike.nonneg_iff_exists_ofReal.mpr ⟨1/4-eig,sub_nonneg.mpr heig,rfl⟩
  rw [show (1/4 : ℂ)-(eig : ℂ) = ((1/4-eig : ℝ) : ℂ) by push_cast; ring,
    Complex.sqrt_of_nonneg hp,Complex.ofReal_re]

def gamma0CuspExceptionalMoment (N : ℕ) [NeZero N]
    (u : Finset (Gamma0AllHeightSpectralIndex N)) (a : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (n : ℤ) (hn : n ≠ 0) (A : ℝ) : ℝ :=
  let w := (gamma0CuspTrueWidth N a : ℝ)
  let nN := (gamma0CuspFrequencyStep N a : ℤ)*n
  let ν (i : Gamma0AllHeightSpectralIndex N) : ℝ := Real.sqrt (1/4-gamma0AllHeightGradientSpectralValue N i)
  ∑ i ∈ u, A^(-2*ν i)*‖(Real.sqrt w : ℂ)*gamma0CuspBesselAmplitude N i a Y hY nN
    (gamma0CuspFrequencyStep_mul_ne_zero N a hn)‖^2

theorem gamma0CuspExceptionalMoment_le_physical (N : ℕ) [NeZero N]
    (u : Finset (Gamma0AllHeightSpectralIndex N)) (a : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (n : ℤ) (hn : n ≠ 0) (F : ℝ → ℝ) (hF : Continuous F)
    {A : ℝ} (hA : 0 < A) (hA₁ : 2*A ≤ 1) (hSF : tsupport F ⊆ Icc A (2*A))
    (hF₀ : ∀ x, 0 ≤ F x) (hOne : ∀ x ∈ Icc (5*A/4) (7*A/4), F x = 1)
    (heig : ∀ i ∈ u, gamma0AllHeightGradientSpectralValue N i ≤ 1/4) :
    (Real.exp (-Real.exp 1)/16)^2*gamma0CuspExceptionalMoment N u a Y hY n hn A ≤
      gamma0CuspPhysicalBesselMoment N u a Y hY n hn F := by
  let κ := Real.exp (-Real.exp 1)/16
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  unfold gamma0CuspExceptionalMoment gamma0CuspPhysicalBesselMoment
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  let eig := gamma0AllHeightGradientSpectralValue N i
  let ν := Real.sqrt (1/4-eig)
  have hν₀ : 0 ≤ ν := Real.sqrt_nonneg _
  have hν₁ : ν ≤ 1/2 := Real.sqrt_le_iff.mpr ⟨by norm_num,by
    change 1/4-gamma0AllHeightGradientSpectralValue N i ≤ (1/2 : ℝ)^2
    nlinarith only [gamma0AllHeightGradientSpectralValue_nonneg N i]⟩
  rw [spectralComplexSqrt_quarter_sub_nonneg eig (heig i hi)]
  have h := spectralKExceptionalPhysicalTest_transform_lower F hF hA hA₁
    hSF hF₀ hOne hν₀ hν₁
  have hPow : (A^(-ν))^2 = A^(-2*ν) := by
    rw [← Real.rpow_mul_natCast hA.le]
    congr 1
    push_cast
    ring
  change κ^2*A^(-2*ν) ≤ _
  rw [← hPow,← mul_pow]
  exact pow_le_pow_left₀ (mul_nonneg hκ.le (Real.rpow_nonneg hA.le _)) h 2

end ArtinMatthews
