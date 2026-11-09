module

public import ArtinMatthews.VaryingKummerAnalyticMixedXiLogDerivBase
public import ArtinMatthews.VaryingKummerAnalyticDedekindNonvanishing


set_option backward.privateInPublic true
@[expose] public section

/-! The unconditional logarithmic derivative formula for the actual
mixed-signature completed Dedekind xi function. -/
noncomputable section
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped Topology

variable (K : Type*) [Field K] [NumberField K]

/-- Every factor is genuinely nonzero in Re(s)>1 by the actual Euler-product
and Gamma theorems; no nonvanishing hypothesis is required here. -/
theorem mixedCompletedDedekindXi_logDeriv {s : ℂ} (hs : 1 < s.re) :
    logDeriv (mixedCompletedDedekindXi K) s =
      1 / s + 1 / (s - 1) + (Real.log (mixedDiscriminantScale K) : ℂ) +
        logDeriv (mixedGammaFactor K) s + logDeriv (NumberField.dedekindZeta K) s :=
  mixedCompletedDedekindXi_logDeriv_of_zeta_ne_zero K hs
    (dedekindZeta_ne_zero_of_one_lt_re K hs)

/-- The corresponding exact real-part identity, suitable for the pole-sum
and Gamma estimates. -/
theorem mixedCompletedDedekindXi_logDeriv_re {s : ℂ} (hs : 1 < s.re) :
    (logDeriv (mixedCompletedDedekindXi K) s).re =
      (1 / s).re + (1 / (s - 1)).re + Real.log (mixedDiscriminantScale K) +
        (logDeriv (mixedGammaFactor K) s).re +
          (logDeriv (NumberField.dedekindZeta K) s).re := by
  rw [mixedCompletedDedekindXi_logDeriv K hs]
  simp only [Complex.add_re, Complex.ofReal_re]

end ArtinMatthews.VaryingKummerAnalytic
