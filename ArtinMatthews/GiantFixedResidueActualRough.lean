module

public import ArtinMatthews.GiantFixedResidueCentering
public import ArtinMatthews.GiantFixedResidueProgressions
public import ArtinMatthews.GiantBoundedProgression


set_option backward.privateInPublic true
@[expose] public section

/-! The fixed-residue rough estimate for the literal centered giant
statistic and the original marking mean. -/
namespace ArtinMatthews
open Filter MeasureTheory
open scoped Topology BigOperators
noncomputable section

def giantFixedResidueCenteredRoughSum {J : Type*} [Fintype J]
    (M a : ℕ) (e : J → ℝ) (ε : ℝ) (Φ : ℝ → ℝ) (T x γ : ℝ) : ℝ :=
  giantFixedResidueRoughSum M a
    (fun u => (((giantPrimeFactors u x ε).card:ℝ)-giantPrimeReciprocalSum x ε)*
      literalMarkedArrayWeight e x u) Φ T x γ

def giantFixedResidueRoughError (M : ℕ) (Φ : ℝ → ℝ) (T c : ℝ) (m : ℕ) : ℝ :=
  giantRoughSieveError Φ T c m/(M.totient:ℝ)

theorem giantFixedResidueRoughError_tendsto (M : ℕ) (Φ : ℝ → ℝ) (T c : ℝ) :
    Tendsto (fun m : ℕ => giantFixedResidueRoughError M Φ T c m) atTop (𝓝 0) := by
  simpa only [giantFixedResidueRoughError,zero_div] using
    (giantRoughSieveError_tendsto Φ T c).div_const (M.totient:ℝ)

theorem giantFixedResidue_actual_centered_rough_bound {J : Type*} [Fintype J] [DecidableEq J]
    (M a : ℕ) (hM : 0 < M) (ha : a.Coprime M)
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ)<e j ∧ e j<1/5) (hinj : Function.Injective e)
    (ε c : ℝ) (m : ℕ) (hε : 0<ε) (hεq : ε<1/4) (hc : 0<c) (hcε : c<ε/2)
    (hm : 20000 ≤ m) (Φ : ℝ → ℝ) {T : ℝ}
    (hT : 0≤T) (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ))
    (hΦT : Φ T=0) (hΦ0 : ∀ t,0≤Φ t) (hΦzero : Φ 0=0) {η : ℝ} (hη : 0<η) :
    ∀ᶠ x : ℝ in atTop,
      Real.log x/(x*literalMarkedArrayMean e x)*
        |giantFixedResidueCenteredRoughSum M a e ε Φ T x (markedSieveExponent c m)| ≤
        giantFixedResidueRoughError M Φ T c m+η := by
  have he0 : ∀ j,0<e j := fun j => lt_trans (by norm_num) (he j).1
  have hlevel : markedSieveExponent c m * ((12*(m+1):ℕ):ℝ) ≤ c := by
    calc
      _ = (12*((m:ℝ)+1))*markedSieveExponent c m := by push_cast; ring
      _ = c/2 := markedSieveExponent_level c m
      _ ≤ c := by linarith
  have hprogF := giantFixedResidue_actual_giant_progression_isLittleO M a hM ha e he hinj ε c 1
    hε hεq hc.le hcε Φ hT hΦ hderiv hΦT hΦ0 hΦzero
  have hprogH := giantFixedResidue_actual_array_progression_isLittleO M a hM ha e he hinj c 1
    hc.le (by linarith) Φ hT hΦ hderiv hΦT hΦ0
  have h := giantFixedResidue_centered_rough_asymptotic M a hM
    (fun x u => ((giantPrimeFactors u x ε).card:ℝ)) (literalMarkedArrayWeight e)
    (fun x => giantPrimeReciprocalSum x ε) (literalMarkedArrayMean e) Φ T
    (markedSieveExponent c m) c m hΦ0
    (Filter.Eventually.of_forall (fun _ _ => Nat.cast_nonneg _))
    (Filter.Eventually.of_forall (fun x u => literalMarkedArrayWeight_nonneg e x u))
    (giantPrimeReciprocalSum_bounds_eventually hε hεq)
    (show 0<(1/2:ℝ)^Fintype.card J by positivity) (literalMarkedArrayMean_lower_eventually e he0)
    (markedSieveExponent_pos hc m) hm hlevel hprogF hprogH hη
  have hE : 2*(∫ t in Set.Ioc 0 T,Φ t)*Real.exp (-Real.eulerMascheroniConstant)/
        (markedSieveExponent c m*(M.totient:ℝ))*Real.exp (-(m:ℝ)/2) =
      giantFixedResidueRoughError M Φ T c m := by
    unfold giantFixedResidueRoughError giantRoughSieveError
    ring
  simpa only [giantFixedResidueCenteredRoughSum,hE] using h

end
end ArtinMatthews
