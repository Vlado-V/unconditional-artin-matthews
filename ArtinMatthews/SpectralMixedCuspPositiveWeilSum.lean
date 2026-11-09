module

public import ArtinMatthews.SpectralMixedCuspOrbitalWeil


set_option backward.privateInPublic true
@[expose] public section

/-! Actual level-uniform positive mixed cusp compact orbital bound.
The positive integral lower entries are divisible by s, with the
stronger exact ABL coprimality condition proved separately. The zero
and noncuspidal contributions are not included in this estimate. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem gamma0PositiveGeometricSum_mixed_weil_bound {ε : ℝ}
    (hε : 0 < ε) (hεlt : ε < 3/2) :
    ∃ D : ℝ, 0 < D ∧ ∀ (r s : ℕ) [NeZero r] [NeZero s], r.Coprime s →
      ∀ (m n : ℤ), m ≠ 0 → n ≠ 0 →
      ∀ (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
        (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
        (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
        (A B M : ℝ), 0 < A → 0 < B → (∀ y ∈ tsupport ρ, A ≤ y) → (∀ z ∈ tsupport η, B ≤ z) →
          (∀ z : ℝ, ‖spectralKLHeightBaseTest η z‖ ≤ M) →
          ‖gamma0PositiveGeometricSum (r*s) (gamma0CuspOneOver s) 1
            (cuspFourierTestSeed ((r*s : ℕ) : ℝ) (Nat.cast_pos.mpr (NeZero.pos (r*s)))
              ((gamma0CuspFrequencyStep (r*s) (gamma0CuspOneOver s) : ℤ)*n) ρ hρ hcρ hpρ)
            (cuspFourierTestSeed ((r*s : ℕ) : ℝ) (Nat.cast_pos.mpr (NeZero.pos (r*s)))
              ((gamma0CuspFrequencyStep (r*s) 1 : ℤ)*m) η hη hcη hpη)‖ ≤
            D*spectralWeylCompactHeightBudget A B M ρ*(r : ℝ)*(s : ℝ)^(-(1/2 : ℝ)+ε)*
              ((Int.gcd m n : ℕ) : ℝ)^(1/2 : ℝ)*
                (∑' k : ℕ, ((k+1 : ℕ) : ℝ)^(-(5/2 : ℝ)+ε)) := by
  obtain ⟨D,hD,hW⟩ := gamma0MixedBesselGeometricFibre_weil_bound hε
  refine ⟨D,hD,?_⟩
  intro r s _ _ hcop m n hm hn ρ η hρ hη hcρ hcη hpρ hpη A B M hA hB hρlo hηlo hM
  let F (q : Ioi (0 : ℕ)) : ℂ :=
    gamma0TrueWidthPositiveBesselFibre (r*s) (gamma0CuspOneOver s) 1 q n m ρ η
  let Q := spectralWeylCompactHeightBudget A B M ρ
  let G := ((Int.gcd m n : ℕ) : ℝ)^(1/2 : ℝ)
  let p := -(5/2 : ℝ)+ε
  let L := (r : ℝ)*(s : ℝ)^2
  let A₀ := D*Q*L*G
  have hP := gamma0PositiveGeometricSum_trueWidth_bessel (r*s) (gamma0CuspOneOver s) 1 n m hn hm
    ρ η hρ hη hcρ hcη hpρ hpη
  have hF : Function.HasFiniteSupport F := hP.1
  have hs : 0 < (s : ℝ) := Nat.cast_pos.mpr (NeZero.pos s)
  have hQ : 0 ≤ Q := spectralWeylCompactHeightBudget_nonneg hA hB ((norm_nonneg _).trans (hM 0)) ρ
  have hG : 0 ≤ G := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hA₀ : 0 ≤ A₀ := by dsimp only [A₀,L]; positivity
  have hp : p < -1 := by dsimp [p]; linarith
  obtain ⟨a,b,hab⟩ := exists_atkin_bezout hcop
  have hzero (q : Ioi (0 : ℕ)) (hq : ¬ s ∣ q.val) : F q = 0 := by
    let _ : NeZero q.val := ⟨(show 0 < q.val from q.property).ne'⟩
    apply gamma0MixedBesselGeometricFibre_zero_off_source_moduli r s q.val hcop hab m n ρ η
    rintro ⟨c,_,he,_⟩
    exact hq ⟨c,he⟩
  have hBnd (q : Ioi (0 : ℕ)) : ‖F q‖ ≤ A₀*(q.val : ℝ)^p := by
    let _ : NeZero q.val := ⟨(show 0 < q.val from q.property).ne'⟩
    have hterm := hW r s q.val hcop m n hm hn ρ η hρ hη hcρ hcη hpρ hpη A B M hA hB hρlo hηlo hM
    have hgc : Nat.gcd q.val (Int.gcd m n) ≤ Int.gcd m n :=
      Nat.gcd_le_right _ (Int.gcd_pos_of_ne_zero_left n hm)
    have hgp : ((Nat.gcd q.val (Int.gcd m n) : ℕ) : ℝ)^(1/2 : ℝ) ≤ G :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hgc) (by norm_num)
    have hcoef : 0 ≤ D*Q*L*(q.val : ℝ)^p := by dsimp only [L]; positivity
    calc
      _ ≤ D*Q*L*(q.val : ℝ)^p*G := hterm.trans (mul_le_mul_of_nonneg_left hgp hcoef)
      _ = _ := by dsimp only [A₀]; ring_nf
  have hPow : (s : ℝ)^2*(s : ℝ)^p = (s : ℝ)^(-(1/2 : ℝ)+ε) := by
    rw [← Real.rpow_natCast (s : ℝ) 2,← Real.rpow_add hs]
    congr 1
    dsimp [p]
    ring_nf
  rw [hP.2]
  change ‖∑ᶠ q : Ioi (0 : ℕ), F q‖ ≤ D*Q*(r : ℝ)*(s : ℝ)^(-(1/2 : ℝ)+ε)*G*
    (∑' k : ℕ, ((k+1 : ℕ) : ℝ)^p)
  calc
    _ ≤ A₀*(s : ℝ)^p*(∑' k : ℕ, ((k+1 : ℕ) : ℝ)^p) :=
      spectral_positive_multiple_finsum_norm_bound s F hF hzero hp hA₀ hBnd
    _ = D*Q*(r : ℝ)*((s : ℝ)^2*(s : ℝ)^p)*G*(∑' k : ℕ, ((k+1 : ℕ) : ℝ)^p) := by
      dsimp only [A₀,L]
      ring_nf
    _ = _ := by rw [hPow]

end ArtinMatthews
