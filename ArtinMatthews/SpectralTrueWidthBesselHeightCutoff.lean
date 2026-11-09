module

public import ArtinMatthews.SpectralSameCuspZeroFourierPairing


set_option backward.privateInPublic true
@[expose] public section

/-! The geometric height cutoff in actual primitive cusp coordinates.
The two width factors in the squared normalized modulus cancel those
in the scaled lower height supports. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem gamma0TrueWidthBesselOrbital_zero_of_large_lower_entry (N q : ℕ) [NeZero N] [NeZero q]
    (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hρlo : ∀ y ∈ tsupport ρ, A ≤ y) (hηlo : ∀ z ∈ tsupport η, B ≤ z)
    (hcut : 1 < (q : ℝ)^2*A*B) :
    gamma0TrueWidthBesselOrbital N r s q m n ρ η = 0 := by
  let w : ℝ := gamma0CuspTrueWidth N r
  let v : ℝ := gamma0CuspTrueWidth N s
  let C := gamma0TrueWidthModulus N r s (q : ℝ)
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hv : 0 < v := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N s)
  have hC : 0 < C := gamma0TrueWidthModulus_pos N r s (Nat.cast_pos.mpr (NeZero.pos q))
  have he : C^2*(A/w)*(B/v) = (q : ℝ)^2*A*B := by
    change ((q : ℝ)*Real.sqrt w*Real.sqrt v)^2*(A/w)*(B/v) = _
    rw [mul_pow,mul_pow,Real.sq_sqrt hw.le,Real.sq_sqrt hv.le]
    field_simp [hw.ne',hv.ne']
  have hR : Function.support (fun y => ρ (w*y)) ⊆ Ici (A/w) := by
    intro y hy
    have hwy : w*y ∈ tsupport ρ := subset_tsupport _ hy
    exact (div_le_iff₀ hw).mpr (by simpa only [mul_comm] using hρlo (w*y) hwy)
  have hE : Function.support (fun y => η (v*y)) ⊆ Ici (B/v) := by
    intro y hy
    have hvy : v*y ∈ tsupport η := subset_tsupport _ hy
    exact (div_le_iff₀ hv).mpr (by simpa only [mul_comm] using hηlo (v*y) hvy)
  rw [← gamma0TrueWidthOrbitalKernel_nonzero_bessel N r s q m n hm hn ρ η hρ hη hcρ hcη hpρ hpη]
  exact cuspWeylOrbitalKernel_eq_zero_of_large_modulus 1 m n _ _ (A/w) (B/v)
    (div_pos hA hw) (div_pos hB hv) hR hE C hC.ne' (by rwa [he])

theorem gamma0TrueWidthBesselGeometricFibre_zero_of_large_lower_entry (N q : ℕ)
    [NeZero N] [NeZero q] (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hρlo : ∀ y ∈ tsupport ρ, A ≤ y) (hηlo : ∀ z ∈ tsupport η, B ≤ z)
    (hcut : 1 < (q : ℝ)^2*A*B) :
    gamma0TrueWidthBesselGeometricFibre N r s q m n ρ η = 0 := by
  rw [gamma0TrueWidthBesselGeometricFibre,
    gamma0TrueWidthBesselOrbital_zero_of_large_lower_entry N q r s m n hm hn ρ η hρ hη hcρ hcη hpρ hpη
      hA hB hρlo hηlo hcut,mul_zero,mul_zero]

theorem gamma0PositiveGeometricSum_identity_zero_of_high_support (N : ℕ) [NeZero N]
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hρlo : ∀ y ∈ tsupport ρ, A ≤ y) (hηlo : ∀ z ∈ tsupport η, B ≤ z)
    (hcut : 1 < (N : ℝ)^2*A*B) :
    gamma0PositiveGeometricSum N 1 1
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
        ((gamma0CuspFrequencyStep N 1 : ℤ)*m) ρ hρ hcρ hpρ)
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
        ((gamma0CuspFrequencyStep N 1 : ℤ)*n) η hη hcη hpη) = 0 := by
  rw [(gamma0PositiveGeometricSum_trueWidth_bessel N 1 1 m n hm hn ρ η hρ hη hcρ hcη hpρ hpη).2]
  have hz (q : Ioi (0 : ℕ)) : gamma0TrueWidthPositiveBesselFibre N 1 1 q m n ρ η = 0 := by
    let _ : NeZero q.val := ⟨(show 0 < q.val from q.property).ne'⟩
    by_cases hNq : N ∣ q.val
    · have hle : (N : ℝ) ≤ (q.val : ℝ) := Nat.cast_le.mpr (Nat.le_of_dvd q.property hNq)
      have hcut' := hcut.trans_le (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg N) hle 2) hA.le) hB.le)
      exact gamma0TrueWidthBesselGeometricFibre_zero_of_large_lower_entry N q.val 1 1 m n hm hn
        ρ η hρ hη hcρ hcη hpρ hpη hA hB hρlo hηlo hcut'
    · exact gamma0TrueWidthBesselGeometricFibre_identity_zero_of_not_dvd N q.val m n ρ η hNq
  simp only [hz,finsum_zero]

end ArtinMatthews
