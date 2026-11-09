module

public import ArtinMatthews.GiantProgressionGlobalMean
public import ArtinMatthews.GiantArrayRemoval


set_option backward.privateInPublic true
@[expose] public section

/-! The uncentered main term follows from the actual smooth progression
prime mean and the proved C_x limit once the centered law is supplied.
The centered law itself remains an explicit separate input. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators Topology Asymptotics

theorem giant_prime_successor_sum (N : ℕ) (F : ℕ → ℂ) :
    (∑ u ∈ (Finset.Icc 0 N).filter (fun u => (u+1).Prime), F (u+1)) =
      ∑ p ∈ (Finset.Icc 0 (N+1)).filter Nat.Prime, F p := by
  classical
  apply Finset.sum_bij (fun u _ => u+1)
  · intro u hu
    obtain ⟨hu,hp⟩ := Finset.mem_filter.mp hu
    have huN := (Finset.mem_Icc.mp hu).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩,hp⟩
  · intro u _ v _ huv
    omega
  · intro p hp
    obtain ⟨hpI,hpP⟩ := Finset.mem_filter.mp hp
    have hp2 := hpP.two_le
    have hpN := (Finset.mem_Icc.mp hpI).2
    refine ⟨p-1,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _,by omega⟩,?_⟩,by omega⟩
    simpa only [Nat.sub_add_cancel (by omega : 1≤p)] using hpP
  · intro u _
    rfl

def giantCenteredPrimeTest {M : ℕ} (U : Finset (ZMod M)ˣ)
    (ε : ℝ) (Φ : ℝ → ℝ) (T x : ℝ) : ℂ :=
  ∑ p ∈ giantPrimeMeanRange T x,
    (Φ (((p : ℝ)-1)/x) : ℂ) * giantUnitResidueIndicator U p *
      ((((giantPrimeFactors (p-1) x ε).card : ℝ)-giantPrimeReciprocalSum x ε : ℝ) : ℂ)

def giantUncenteredPrimeTest {M : ℕ} (U : Finset (ZMod M)ˣ)
    (ε : ℝ) (Φ : ℝ → ℝ) (T x : ℝ) : ℂ :=
  ∑ p ∈ giantPrimeMeanRange T x,
    (Φ (((p : ℝ)-1)/x) : ℂ) * giantUnitResidueIndicator U p *
      (((giantPrimeFactors (p-1) x ε).card : ℝ) : ℂ)

theorem giant_centered_prime_test_eq {M : ℕ} (U : Finset (ZMod M)ˣ)
    (ε : ℝ) (Φ : ℝ → ℝ) (T x : ℝ) :
    giantCenteredPrimeTest U ε Φ T x = giantFixedProgressionPrimeSum U ε Φ T x := by
  unfold giantCenteredPrimeTest giantPrimeMeanRange
  rw [← giant_prime_successor_sum]
  unfold giantFixedProgressionPrimeSum markedPrimeCorrelation
  apply Finset.sum_congr rfl
  intro u _
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
    giantFixedResidueLiteralCoefficient]
  ring_nf

theorem giant_uncentered_prime_test_eq {M : ℕ} (U : Finset (ZMod M)ˣ)
    (ε : ℝ) (Φ : ℝ → ℝ) (T x : ℝ) :
    giantUncenteredPrimeTest U ε Φ T x = giantCenteredPrimeTest U ε Φ T x +
      (giantPrimeReciprocalSum x ε : ℂ)*giantShiftedPrimeTest U Φ T x := by
  unfold giantUncenteredPrimeTest giantCenteredPrimeTest giantShiftedPrimeTest
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  push_cast
  ring_nf

/-- The literal main-term consequence (3.2), conditional only on the
centered progression law (3.1), with its original f_x and C_x. -/
theorem giant_uncentered_prime_mean_of_centered {M : ℕ} [NeZero M]
    (U : Finset (ZMod M)ˣ) (ε : ℝ) (hε : 0<ε) (hεq : ε<1/4)
    (Φ : ℝ → ℝ) (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ))
    (hc : HasCompactSupport Φ) {a b : ℝ} (ha : 0<a) (hab : a≤b)
    (hsupp : Function.support Φ ⊆ Set.Ioo a b)
    (hcentered : giantFixedProgressionPrimeSum U ε Φ b =o[atTop]
      (fun x : ℝ => x/Real.log x)) :
    Tendsto (fun x : ℝ => ((Real.log x/x : ℝ) : ℂ)*giantUncenteredPrimeTest U ε Φ b x) atTop
      (𝓝 (((U.card : ℝ)/M.totient * giantPrimeConstant ε * ∫ t : ℝ, Φ t : ℝ) : ℂ)) := by
  have hc' : (fun x => giantCenteredPrimeTest U ε Φ b x) =o[atTop]
      (fun x : ℝ => x/Real.log x) :=
    hcentered.congr' (Filter.Eventually.of_forall (fun x => (giant_centered_prime_test_eq U ε Φ b x).symm))
      Filter.EventuallyEq.rfl
  have hzero := giant_normalized_complex_of_isLittleO _ hc'
  have hmean := giant_shifted_prime_mean U Φ hΦ hderiv hc ha hab hsupp
  have hC := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (giantPrimeReciprocalSum_tendsto hε (by linarith : ε<1))
  have h := hzero.add (hC.mul hmean)
  simp only [Function.comp_apply] at h
  convert h using 1
  · funext x
    rw [giant_uncentered_prime_test_eq]
    ring_nf
  · push_cast
    ring_nf

def giantUncenteredPrimeSeries {M : ℕ} (U : Finset (ZMod M)ˣ)
    (ε : ℝ) (Φ : ℝ → ℝ) (x : ℝ) : ℂ :=
  ∑' p : ℕ, (if p.Prime then
    (Φ (((p : ℝ)-1)/x) : ℂ)*giantUnitResidueIndicator U p else 0) *
      (((giantPrimeFactors (p-1) x ε).card : ℝ) : ℂ)

theorem giant_uncentered_prime_series_eq {M : ℕ} (U : Finset (ZMod M)ˣ)
    (ε : ℝ) (Φ : ℝ → ℝ) {a b x : ℝ} (ha : 0<a) (hab : a≤b)
    (hsupp : Function.support Φ ⊆ Set.Ioo a b) (hx : 0<x) :
    giantUncenteredPrimeSeries U ε Φ x = giantUncenteredPrimeTest U ε Φ b x := by
  classical
  have hs := giant_shifted_prime_term_support U Φ ha hab hsupp hx
  unfold giantUncenteredPrimeSeries
  rw [tsum_eq_sum (s := giantPrimeMeanRange b x) (fun p hp => by
    have hz : (if p.Prime then (Φ (((p : ℝ)-1)/x) : ℂ)*giantUnitResidueIndicator U p else 0)=0 := by
      by_contra h
      exact hp (hs h)
    rw [hz,zero_mul])]
  unfold giantUncenteredPrimeTest
  apply Finset.sum_congr rfl
  intro p hp
  rw [ite_eq_left (Finset.mem_filter.mp hp).2]

theorem giant_uncentered_prime_series_mean_of_centered {M : ℕ} [NeZero M]
    (U : Finset (ZMod M)ˣ) (ε : ℝ) (hε : 0<ε) (hεq : ε<1/4)
    (Φ : ℝ → ℝ) (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ))
    (hc : HasCompactSupport Φ) {a b : ℝ} (ha : 0<a) (hab : a≤b)
    (hsupp : Function.support Φ ⊆ Set.Ioo a b)
    (hcentered : giantFixedProgressionPrimeSum U ε Φ b =o[atTop]
      (fun x : ℝ => x/Real.log x)) :
    Tendsto (fun x : ℝ => ((Real.log x/x : ℝ) : ℂ)*giantUncenteredPrimeSeries U ε Φ x) atTop
      (𝓝 (((U.card : ℝ)/M.totient * giantPrimeConstant ε * ∫ t : ℝ, Φ t : ℝ) : ℂ)) := by
  have h := giant_uncentered_prime_mean_of_centered U ε hε hεq Φ hΦ hderiv hc ha hab hsupp hcentered
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [giant_uncentered_prime_series_eq U ε Φ ha hab hsupp hx]

end
end ArtinMatthews
