module

public import ArtinMatthews.SpectralJPrincipalMass
public import ArtinMatthews.SpectralCuspEisensteinInfinity
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
public import ArtinMatthews.SpectralInfinityPrincipalCutoffBessel
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
open Set
open scoped MatrixGroups BigOperators
noncomputable section

theorem gamma0Infinity_nativePrincipal_summable (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (hsmall : Y < (1 / 16) / |cuspFourierFrequency 1 n|) :
    Summable (fun i : Gamma0HeatPrincipalCuspidalIndex N =>
      gamma0NativePrincipalDensity N 1 Y hY n hn i /
        (1 + |gamma0CuspPrincipalParameter N i.val|) ^ 4) := by
  obtain ⟨C, hC, hBound⟩ := gamma0Infinity_principal_cutoff_orbit_bessel
  let B := |cuspFourierFrequency 1 n|
  have hB : 0 < B := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos n hn)
  let D := C * (1 + B / (N : ℝ))
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  apply gamma0NativePrincipalDensity_summable_of_moment N 1 Y hY n hn D hD
  intro u R hR hprincipal hcap
  have h := hBound N u ({()} : Finset Unit) (fun _ => (1 : ℂ)) (fun _ => n)
    (fun _ _ _ => Subsingleton.elim _ _) (fun _ => hn) hR hB hY hsmall
    (fun _ => le_rfl) hprincipal hcap
  have hm : gamma0CuspPrincipalMoment N u 1 Y hY n hn ≤ C * (R ^ 2 + B * R / (N : ℝ)) := by
    simpa only [gamma0CuspPrincipalMoment, gamma0CuspUnitAmplitude, gamma0CuspTrueWidth_identity,
      Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, one_mul, gamma0CuspPrincipalParameter, Finset.sum_singleton,
      star_one, norm_one, one_pow, mul_one] using h
  apply hm.trans
  have hq : 0 ≤ B / (N : ℝ) := by positivity
  have hR₂ : R ≤ R ^ 2 := by nlinarith only [hR]
  have hmul := mul_le_mul_of_nonneg_left hR₂ hq
  dsimp only [D]
  have hquad : R ^ 2 + B * R / (N : ℝ) ≤ (1 + B / (N : ℝ)) * R ^ 2 := by
    rw [show B * R / (N : ℝ) = (B / (N : ℝ)) * R by ring]
    nlinarith only [hmul]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hquad hC.le

end
end ArtinMatthews
