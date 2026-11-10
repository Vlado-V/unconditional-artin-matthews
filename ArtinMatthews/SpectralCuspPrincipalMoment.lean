module

public import ArtinMatthews.SpectralCuspTrueWidthPhysicalMoment
public import ArtinMatthews.SpectralKFrameCompactProfiles
public import ArtinMatthews.SpectralGamma0PoincareKL
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The true-width compact principal moment in finite spectral windows. -/
noncomputable section
open scoped MatrixGroups BigOperators
namespace ArtinMatthews

def gamma0CuspUnitAmplitude (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N)
    (b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) : ℂ :=
  (Real.sqrt (gamma0CuspTrueWidth N b : ℝ) : ℂ)*
    gamma0CuspBesselAmplitude N i b Y hY ((gamma0CuspFrequencyStep N b : ℤ)*n)
      (gamma0CuspFrequencyStep_mul_ne_zero N b hn)

def gamma0CuspPrincipalParameter (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N) : ℝ :=
  Real.sqrt (gamma0AllHeightGradientSpectralValue N i-1/4)

def gamma0CuspPrincipalMoment (N : ℕ) [NeZero N]
    (u : Finset (Gamma0AllHeightSpectralIndex N)) (b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (n : ℤ) (hn : n ≠ 0) : ℝ :=
  u.sum fun i : Gamma0AllHeightSpectralIndex N =>
    ‖gamma0CuspUnitAmplitude N i b Y hY n hn‖^2 / Real.cosh (Real.pi*gamma0CuspPrincipalParameter N i)

theorem gamma0CuspPhysicalBesselMoment_principal_eq (N : ℕ) [NeZero N]
    (u : Finset (Gamma0AllHeightSpectralIndex N)) (b : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (n : ℤ) (hn : n ≠ 0) (F : ℝ → ℝ)
    (hprincipal : ∀ i ∈ u, 1/4 ≤ gamma0AllHeightGradientSpectralValue N i) :
    gamma0CuspPhysicalBesselMoment N u b Y hY n hn F =
      u.sum fun i : Gamma0AllHeightSpectralIndex N =>
        ‖gamma0CuspUnitAmplitude N i b Y hY n hn‖^2*
          ‖spectralCompactRealKTransform F (gamma0CuspPrincipalParameter N i)‖^2 := by
  unfold gamma0CuspPhysicalBesselMoment
  dsimp only
  apply Finset.sum_congr rfl
  intro i hi
  rw [spectralComplexSqrt_quarter_sub_real _ (hprincipal i hi)]
  exact mul_comm _ _

theorem spectral_principal_orbit_growth_le {C T q N : ℝ} (hC : 0 ≤ C)
    (hT : 0 < T) (hN : 0 < N) :
    C*T^2*(6*(1+2*q/(N*(T/16)))) ≤ 192*C*(T^2+q*T/N) := by
  calc
    _ = (6*C)*(T^2+32*(q*T/N)) := by
      field_simp [hN.ne',hT.ne']
      ring
    _ ≤ (6*C)*(32*(T^2+q*T/N)) :=
      mul_le_mul_of_nonneg_left (by linarith only [sq_nonneg T]) (by positivity)
    _ = _ := by ring

end ArtinMatthews
