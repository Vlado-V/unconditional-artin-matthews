module

public import ArtinMatthews.SpectralInfinityOrbitalWeil
public import ArtinMatthews.SpectralPositiveMultipleSum


set_option backward.privateInPublic true
@[expose] public section

/-! Actual level-uniform summation of the infinity-cusp positive compact
orbital sector. Its literal period-N multiplicity is retained and the
zero sector and noncuspidal pairing are not estimated here. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem gamma0PositiveGeometricSum_identity_weil_bound {ε : ℝ}
    (hε : 0 < ε) (hεlt : ε < 3/2) :
    ∃ D : ℝ, 0 < D ∧ ∀ (N : ℕ) [NeZero N] (m n : ℤ), m ≠ 0 → n ≠ 0 →
      ∀ (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
        (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
        (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
        (A B M : ℝ), 0 < A → 0 < B → (∀ y ∈ tsupport ρ, A ≤ y) → (∀ z ∈ tsupport η, B ≤ z) →
          (∀ z : ℝ, ‖spectralKLHeightBaseTest η z‖ ≤ M) →
          ‖gamma0PositiveGeometricSum N 1 1
            (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
              ((gamma0CuspFrequencyStep N 1 : ℤ)*m) ρ hρ hcρ hpρ)
            (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
              ((gamma0CuspFrequencyStep N 1 : ℤ)*n) η hη hcη hpη)‖ ≤
            D*spectralWeylCompactHeightBudget A B M ρ*(N : ℝ)^(-(1/2 : ℝ)+ε)*
              ((Int.gcd m n : ℕ) : ℝ)^(1/2 : ℝ)*
                (∑' k : ℕ, ((k+1 : ℕ) : ℝ)^(-(5/2 : ℝ)+ε)) := by
  obtain ⟨D,hD,hW⟩ := gamma0TrueWidthBesselGeometricFibre_identity_weil_bound hε
  refine ⟨D,hD,?_⟩
  intro N _ m n hm hn ρ η hρ hη hcρ hcη hpρ hpη A B M hA hB hρlo hηlo hM
  let F (c : Ioi (0 : ℕ)) : ℂ := gamma0TrueWidthPositiveBesselFibre N 1 1 c m n ρ η
  let Q := spectralWeylCompactHeightBudget A B M ρ
  let G := ((Int.gcd m n : ℕ) : ℝ)^(1/2 : ℝ)
  let p := -(5/2 : ℝ)+ε
  let A₀ := D*Q*(N : ℝ)^2*G
  have hP := gamma0PositiveGeometricSum_trueWidth_bessel N 1 1 m n hm hn ρ η hρ hη hcρ hcη hpρ hpη
  have hF : Function.HasFiniteSupport F := hP.1
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hQ : 0 ≤ Q := spectralWeylCompactHeightBudget_nonneg hA hB ((norm_nonneg _).trans (hM 0)) ρ
  have hG : 0 ≤ G := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hA₀ : 0 ≤ A₀ := by dsimp only [A₀]; positivity
  have hp : p < -1 := by dsimp [p]; linarith
  have hzero (c : Ioi (0 : ℕ)) (hc : ¬ N ∣ c.val) : F c = 0 := by
    let _ : NeZero c.val := ⟨(show 0 < c.val from c.property).ne'⟩
    exact gamma0TrueWidthBesselGeometricFibre_identity_zero_of_not_dvd N c.val m n ρ η hc
  have hBnd (c : Ioi (0 : ℕ)) : ‖F c‖ ≤ A₀*(c.val : ℝ)^p := by
    let _ : NeZero c.val := ⟨(show 0 < c.val from c.property).ne'⟩
    have hterm := hW N c.val m n hm hn ρ η hρ hη hcρ hcη hpρ hpη A B M hA hB hρlo hηlo hM
    have hgc : Nat.gcd c.val (Int.gcd m n) ≤ Int.gcd m n :=
      Nat.gcd_le_right _ (Int.gcd_pos_of_ne_zero_left n hm)
    have hgp : ((Nat.gcd c.val (Int.gcd m n) : ℕ) : ℝ)^(1/2 : ℝ) ≤ G :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hgc) (by norm_num)
    have hcoef : 0 ≤ D*Q*(N : ℝ)^2*(c.val : ℝ)^p := by positivity
    calc
      _ ≤ D*Q*(N : ℝ)^2*(c.val : ℝ)^p*G := hterm.trans (mul_le_mul_of_nonneg_left hgp hcoef)
      _ = _ := by dsimp only [A₀]; ring_nf
  have hPow : (N : ℝ)^2*(N : ℝ)^p = (N : ℝ)^(-(1/2 : ℝ)+ε) := by
    rw [← Real.rpow_natCast (N : ℝ) 2,← Real.rpow_add hN]
    congr 1
    dsimp [p]
    ring_nf
  rw [hP.2]
  change ‖∑ᶠ c : Ioi (0 : ℕ), F c‖ ≤ D*Q*(N : ℝ)^(-(1/2 : ℝ)+ε)*G*
    (∑' k : ℕ, ((k+1 : ℕ) : ℝ)^p)
  calc
    _ ≤ A₀*(N : ℝ)^p*(∑' k : ℕ, ((k+1 : ℕ) : ℝ)^p) :=
      spectral_positive_multiple_finsum_norm_bound N F hF hzero hp hA₀ hBnd
    _ = D*Q*((N : ℝ)^2*(N : ℝ)^p)*G*(∑' k : ℕ, ((k+1 : ℕ) : ℝ)^p) := by
      dsimp only [A₀]
      ring_nf
    _ = _ := by rw [hPow]

end ArtinMatthews
