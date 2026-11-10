module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import ArtinMatthews.SpectralBesselPoissonSeries
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


set_option backward.privateInPublic true
@[expose] public section

/-! Complex conjugation of the actual J order at a positive real argument. -/
noncomputable section
open Complex
open scoped ComplexConjugate

namespace ArtinMatthews

theorem spectral_besselJ_order_conj_positive (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    conj (Complex.besselJ ν (x : ℂ)) = Complex.besselJ (conj ν) (x : ℂ) := by
  let b := (x : ℂ)/2
  have hb : b = ((x/2 : ℝ) : ℂ) := by dsimp [b]; push_cast; rfl
  have hArg : b.arg ≠ Real.pi := by
    rw [hb, Complex.arg_ofReal_of_nonneg (half_pos hx).le]
    exact Real.pi_pos.ne
  have hc : conj b = b := by rw [hb,Complex.conj_ofReal]
  have hp : b^(conj ν) = conj (b^ν) := by
    simpa only [hc] using Complex.cpow_conj b ν hArg
  let a (w : ℂ) (n : ℕ) := (-b^2)^n / ((n.factorial : ℂ)*Complex.Gamma (w+1+n))
  have hs : Summable (a ν) := besselJ_hypergeometric_summable ν (x : ℂ)
  have he : conj (∑' n, a ν n) = ∑' n, conj (a ν n) := by
    simpa only [ContinuousLinearEquiv.coe_coe,Complex.conjCLE_apply] using
      Complex.conjCLE.toContinuousLinearMap.map_tsum hs
  rw [besselJ_eq_hypergeometric_tsum ν, besselJ_eq_hypergeometric_tsum (conj ν)]
  change conj (b^ν*(∑' n, a ν n)) = b^(conj ν)*(∑' n, a (conj ν) n)
  rw [map_mul,← hp,he]
  congr 1
  apply tsum_congr
  intro n
  simp only [a,map_div₀,map_pow,map_neg,map_mul,hc,Complex.conj_natCast,
    ← Complex.Gamma_conj,map_add,map_one]

end ArtinMatthews
