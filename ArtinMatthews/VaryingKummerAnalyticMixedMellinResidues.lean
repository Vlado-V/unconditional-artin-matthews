module

public import ArtinMatthews.VaryingKummerAnalyticMixedZetaOrders
public import ArtinMatthews.VaryingKummerAnalyticLogarithmicResidue
public import ArtinMatthews.VaryingKummerAnalyticSmoothMellin


set_option backward.privateInPublic true
@[expose] public section

/-! Actual residues of the smoothed prime-ideal Mellin integrand. The
contribution at one is positive, nontrivial zeros retain their multiplicities,
and the contribution at zero is exactly -(r₁+r₂−1)Φ(0). -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex MeasureTheory Set Filter
open OAI.PrimeDegreePackets.AnalyticGrowth
open scoped Classical Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Literal Mellin integrand of the negative logarithmic derivative. -/
def mixedExplicitFormulaIntegrand (f : ℝ → ℂ) (x : ℝ) (s : ℂ) : ℂ :=
  -(mellin f s * (x : ℂ)^s) * logDeriv (mixedDedekindZeta K) s

variable (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
  (hpositive : tsupport f ⊆ Ioi 0) (hcontinuous : Continuous f)
  {x : ℝ} (hx : 0 < x)
include hcompact hpositive hcontinuous hx

theorem mixedExplicitFormulaIntegrand_residue {ρ : ℂ} {n : ℤ}
    (ho : meromorphicOrderAt (mixedDedekindZeta K) ρ = n) :
    Tendsto (fun s => (s-ρ)*mixedExplicitFormulaIntegrand K f x s) (𝓝[≠] ρ)
      (𝓝 (-(mellin f ρ*(x : ℂ)^ρ)*(n : ℂ))) := by
  have hw : ContinuousAt (fun s : ℂ => -(mellin f s*(x : ℂ)^s)) ρ :=
    (((smoothMellin_entire f hcompact hpositive hcontinuous ρ).mul
      (differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne')))).neg).continuousAt
  exact meromorphic_weighted_logDeriv_residue (mixedDedekindZeta_meromorphic K ρ) ho hw

theorem mixedExplicitFormulaIntegrand_residue_one :
    Tendsto (fun s => (s-1)*mixedExplicitFormulaIntegrand K f x s) (𝓝[≠] 1)
      (𝓝 ((x : ℂ)*mellin f 1)) := by
  have H := mixedExplicitFormulaIntegrand_residue K f hcompact hpositive hcontinuous hx
    (mixedDedekindZeta_order_one K)
  simpa only [cpow_one,Int.cast_neg,Int.cast_one,neg_mul_neg,mul_one,one_mul,mul_comm] using H

theorem mixedExplicitFormulaIntegrand_residue_zero :
    Tendsto (fun s => s*mixedExplicitFormulaIntegrand K f x s) (𝓝[≠] 0)
      (𝓝 (-(((InfinitePlace.nrRealPlaces K : ℤ)+InfinitePlace.nrComplexPlaces K-1 : ℤ) : ℂ)*
        mellin f 0)) := by
  have H := mixedExplicitFormulaIntegrand_residue K f hcompact hpositive hcontinuous hx
    (mixedDedekindZeta_meromorphicOrder_zero K)
  simpa only [sub_zero,cpow_zero,mul_one,neg_mul,mul_neg,mul_comm] using H

theorem mixedExplicitFormulaIntegrand_residue_nontrivial {ρ : ℂ}
    (hρ : mixedCompletedDedekindXi K ρ = 0) :
    Tendsto (fun s => (s-ρ)*mixedExplicitFormulaIntegrand K f x s) (𝓝[≠] ρ)
      (𝓝 (-((zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*
        mellin f ρ*(x : ℂ)^ρ))) := by
  have H := mixedExplicitFormulaIntegrand_residue K f hcompact hpositive hcontinuous hx
    (mixedDedekindZeta_order_at_xi_zero K hρ)
  convert H using 1
  congr 1
  ring

end
end ArtinMatthews.VaryingKummerAnalytic
