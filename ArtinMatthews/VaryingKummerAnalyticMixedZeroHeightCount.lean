module

public import ArtinMatthews.VaryingKummerAnalyticMixedXiZeroStrip
public import ArtinMatthews.VaryingKummerAnalyticZeroHeightWindow


set_option backward.privateInPublic true
@[expose] public section

/-! Actual mixed-signature Dedekind zero-pole identity and height-window
multiplicity bounds, with no assumed zero-strip or growth property. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField Complex
open OAI.PrimeDegreePackets.AnalyticGrowth
open scoped BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem mixedCompletedDedekindXi_hasSum_complexZeroPole {s : ℂ} (hs : 1 < s.re) :
    HasSum (complexZeroPole (mixedCompletedDedekindXi K) s)
      (logDeriv (mixedCompletedDedekindXi K) s).re :=
  hasSum_complexZeroPole (mixedCompletedDedekindXi_entire K)
    (mixedCompletedDedekindXi_zero_ne_zero K)
    (mixedCompletedDedekindXi_hasSubquadraticGrowth K)
    (fun z => (mixedCompletedDedekindXi_functional_equation K z).symm)
    (fun ρ hρ => (mixedCompletedDedekindXi_zeros_in_strip K ρ hρ).2) hs

theorem mixedCompletedDedekindXi_finite_height_window_bound
    (S : Finset ℂ) (T : ℝ) (hT : ∀ ρ ∈ S, |T-ρ.im| ≤ 1) :
    (∑ ρ ∈ S, (zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℝ)) ≤
      5*(logDeriv (mixedCompletedDedekindXi K) (⟨2,T⟩ : ℂ)).re :=
  finite_zero_height_window_bound (mixedCompletedDedekindXi_entire K)
    (mixedCompletedDedekindXi_zero_ne_zero K)
    (mixedCompletedDedekindXi_hasSubquadraticGrowth K)
    (fun z => (mixedCompletedDedekindXi_functional_equation K z).symm)
    (fun ρ hρ => (mixedCompletedDedekindXi_zeros_in_strip K ρ hρ).2) S T hT

theorem mixedCompletedDedekindXi_zeroHeightCount_le_logDeriv (T : ℝ) :
    zeroHeightCount (mixedCompletedDedekindXi K) T ≤
      5*(logDeriv (mixedCompletedDedekindXi K) (⟨2,T⟩ : ℂ)).re :=
  zeroHeightCount_le_logDeriv (mixedCompletedDedekindXi_entire K)
    (mixedCompletedDedekindXi_zero_ne_zero K)
    (mixedCompletedDedekindXi_hasSubquadraticGrowth K)
    (fun z => (mixedCompletedDedekindXi_functional_equation K z).symm)
    (fun ρ hρ => (mixedCompletedDedekindXi_zeros_in_strip K ρ hρ).2) T

end
end ArtinMatthews.VaryingKummerAnalytic
