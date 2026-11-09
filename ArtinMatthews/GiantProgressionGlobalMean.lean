module

public import ArtinMatthews.GiantProgressionSmoothMean


set_option backward.privateInPublic true
@[expose] public section

/-! The literal all-prime shifted smooth progression mean. Compact support
is used to prove its equality with the finite prime range, including after
deleting any fixed finite ramification set. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators Topology

def giantShiftedPrimeSeries {M : ℕ} (U : Finset (ZMod M)ˣ)
    (Φ : ℝ → ℝ) (x : ℝ) : ℂ :=
  ∑' p : ℕ, if p.Prime then
    (Φ (((p : ℝ)-1)/x) : ℂ)*giantUnitResidueIndicator U p else 0

theorem giant_shifted_prime_term_support {M : ℕ} (U : Finset (ZMod M)ˣ)
    (Φ : ℝ → ℝ) {a b x : ℝ} (ha : 0<a) (hab : a≤b)
    (hsupp : Function.support Φ ⊆ Set.Ioo a b) (hx : 0<x) :
    Function.support (fun p : ℕ => if p.Prime then
      (Φ (((p : ℝ)-1)/x) : ℂ)*giantUnitResidueIndicator U p else 0) ⊆
        (↑(giantPrimeMeanRange b x) : Set ℕ) := by
  intro p hp
  change (if p.Prime then (Φ (((p : ℝ)-1)/x) : ℂ)*giantUnitResidueIndicator U p else 0) ≠ 0 at hp
  by_cases hpp : p.Prime
  · rw [ite_eq_left hpp] at hp
    have hΦp : Φ (((p : ℝ)-1)/x) ≠ 0 := by
      intro h
      rw [h,Complex.ofReal_zero,zero_mul] at hp
      exact hp rfl
    have hs := (hsupp hΦp).2
    have hp1 : 1≤p := hpp.one_le
    have hpred : p-1 ≤ ⌊b*x⌋₊ :=
      (Nat.le_floor_iff (mul_nonneg (ha.le.trans hab) hx.le)).mpr (by
        rw [Nat.cast_sub hp1, Nat.cast_one]
        have h := (div_lt_iff₀ hx).mp hs
        nlinarith)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _,by omega⟩,hpp⟩
  · simp only [ite_eq_right hpp, ne_self_iff_false] at hp

theorem giant_shifted_prime_series_eq {M : ℕ} (U : Finset (ZMod M)ˣ)
    (Φ : ℝ → ℝ) {a b x : ℝ} (ha : 0<a) (hab : a≤b)
    (hsupp : Function.support Φ ⊆ Set.Ioo a b) (hx : 0<x) :
    giantShiftedPrimeSeries U Φ x = giantShiftedPrimeTest U Φ b x := by
  classical
  have hs := giant_shifted_prime_term_support U Φ ha hab hsupp hx
  unfold giantShiftedPrimeSeries
  rw [tsum_eq_sum (s := giantPrimeMeanRange b x) (fun p hp => by
    by_contra h
    exact hp (hs h))]
  unfold giantShiftedPrimeTest
  apply Finset.sum_congr rfl
  intro p hp
  rw [ite_eq_left (Finset.mem_filter.mp hp).2]

/-- The actual fixed-M,U smooth prime mean, without any centered-law input. -/
theorem giant_shifted_prime_series_mean {M : ℕ} [NeZero M] (U : Finset (ZMod M)ˣ)
    (Φ : ℝ → ℝ) (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ))
    (hc : HasCompactSupport Φ) (hp : tsupport Φ ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ => ((Real.log x/x : ℝ) : ℂ)*giantShiftedPrimeSeries U Φ x) atTop
      (𝓝 (((U.card : ℝ)/M.totient * ∫ t : ℝ, Φ t : ℝ) : ℂ)) := by
  obtain ⟨a,b,ha,hab,hsupp⟩ :=
    OAI.SevenEighths.PNT.AnnularPrimeMass.exists_positive_support_annulus Φ hc hp
  have h := giant_shifted_prime_mean U Φ hΦ hderiv hc ha hab.le hsupp
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [giant_shifted_prime_series_eq U Φ ha hab.le hsupp hx]

def giantShiftedPrimeSeriesDeleted {M : ℕ} (U : Finset (ZMod M)ˣ) (E : Finset ℕ)
    (Φ : ℝ → ℝ) (x : ℝ) : ℂ :=
  ∑' p : ℕ, if p ∈ E then 0 else if p.Prime then
    (Φ (((p : ℝ)-1)/x) : ℂ)*giantUnitResidueIndicator U p else 0

theorem giant_shifted_prime_series_deleted_eq {M : ℕ} (U : Finset (ZMod M)ˣ) (E : Finset ℕ)
    (Φ : ℝ → ℝ) {a b x : ℝ} (ha : 0<a) (hab : a≤b)
    (hsupp : Function.support Φ ⊆ Set.Ioo a b) (hx : 0<x) :
    giantShiftedPrimeSeriesDeleted U E Φ x = giantShiftedPrimeTestDeleted U E Φ b x := by
  classical
  have hs := giant_shifted_prime_term_support U Φ ha hab hsupp hx
  have hsupport : Function.support (fun p : ℕ => if p ∈ E then (0 : ℂ) else if p.Prime then
      (Φ (((p : ℝ)-1)/x) : ℂ)*giantUnitResidueIndicator U p else 0) ⊆
      (↑(giantPrimeMeanRange b x \ E) : Set ℕ) := by
    intro p hp
    by_cases hpE : p∈E
    · simp only [ite_eq_left hpE, Function.mem_support, ne_self_iff_false] at hp
    · rw [Function.mem_support, ite_eq_right hpE] at hp
      exact Finset.mem_sdiff.mpr ⟨hs hp,hpE⟩
  unfold giantShiftedPrimeSeriesDeleted
  rw [tsum_eq_sum (s := giantPrimeMeanRange b x \ E) (fun p hp => by
    by_contra h
    exact hp (hsupport h))]
  unfold giantShiftedPrimeTestDeleted
  apply Finset.sum_congr rfl
  intro p hp
  rw [ite_eq_right (Finset.mem_sdiff.mp hp).2,
    ite_eq_left (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2]

theorem giant_shifted_prime_series_mean_delete_fixed {M : ℕ} [NeZero M]
    (U : Finset (ZMod M)ˣ) (E : Finset ℕ)
    (Φ : ℝ → ℝ) (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ))
    (hc : HasCompactSupport Φ) (hp : tsupport Φ ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ => ((Real.log x/x : ℝ) : ℂ)*giantShiftedPrimeSeriesDeleted U E Φ x) atTop
      (𝓝 (((U.card : ℝ)/M.totient * ∫ t : ℝ, Φ t : ℝ) : ℂ)) := by
  obtain ⟨a,b,ha,hab,hsupp⟩ :=
    OAI.SevenEighths.PNT.AnnularPrimeMass.exists_positive_support_annulus Φ hc hp
  have h := giant_shifted_prime_mean_delete_fixed U E Φ hΦ hderiv hc ha hab.le hsupp
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [giant_shifted_prime_series_deleted_eq U E Φ ha hab.le hsupp hx]

end
end ArtinMatthews
