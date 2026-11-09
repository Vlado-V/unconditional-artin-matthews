module

public import ArtinMatthews.SpectralWeylCompactNormBound
public import ArtinMatthews.SpectralInfinityKloostermanWeil


set_option backward.privateInPublic true
@[expose] public section

/-! Height-explicit Weil control of the actual infinity-cusp positive
Bessel fiber. Both period-N multiplicities and the full gcd factor are
kept; no bound for the noncuspidal remainder is inferred. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

def spectralWeylCompactHeightBudget (A B M : ℝ) (ρ : ℝ → ℝ) : ℝ :=
  (2/(A*B))*M*(∫ y : ℝ, ‖spectralKLHeightBaseTest ρ y‖ ∂spectralKLPhysicalMeasure)

theorem spectralWeylCompactHeightBudget_nonneg {A B M : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hM : 0 ≤ M) (ρ : ℝ → ℝ) : 0 ≤ spectralWeylCompactHeightBudget A B M ρ := by
  unfold spectralWeylCompactHeightBudget
  exact mul_nonneg (mul_nonneg (by positivity) hM) (integral_nonneg (fun _ => norm_nonneg _))

theorem gamma0CuspFrequencyStep_identity (N : ℕ) [NeZero N] :
    gamma0CuspFrequencyStep N (1 : SL(2, ℤ)) = N := by
  have h := gamma0CuspFrequencyStep_mul_width N (1 : SL(2, ℤ))
  simpa only [gamma0CuspTrueWidth_identity,one_mul] using h

theorem gamma0TrueWidthBesselOrbital_identity_eq_kernel (N c : ℕ) [NeZero N] [NeZero c]
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ)) :
    gamma0TrueWidthBesselOrbital N 1 1 c m n ρ η =
      cuspWeylOrbitalKernel 1 m n ρ η (c : ℝ) (by exact_mod_cast NeZero.ne c) := by
  symm
  simpa only [gamma0CuspTrueWidth_identity,Nat.cast_one,one_mul,mul_one,Real.sqrt_one,gamma0TrueWidthModulus] using!
    gamma0TrueWidthOrbitalKernel_nonzero_bessel N 1 1 c m n hm hn ρ η hρ hη hcρ hcη hpρ hpη

theorem gamma0TrueWidthBesselOrbital_identity_height_bound (N c : ℕ) [NeZero N] [NeZero c]
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    {A B M : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hρlo : ∀ y ∈ tsupport ρ, A ≤ y) (hηlo : ∀ z ∈ tsupport η, B ≤ z)
    (hM : ∀ z : ℝ, ‖spectralKLHeightBaseTest η z‖ ≤ M) :
    ‖gamma0TrueWidthBesselOrbital N 1 1 c m n ρ η‖ ≤ spectralWeylCompactHeightBudget A B M ρ/(c : ℝ)^3 := by
  have hc : 0 < (c : ℝ) := Nat.cast_pos.mpr (NeZero.pos c)
  have hcz : (c : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne c
  have hi : IntegrableOn (weylPlanarDensity 1 m n ρ η (c : ℝ)) {p : ℝ × ℝ | 0 < p.2} := by
    simpa only [Int.cast_natCast] using!
      weylPlanarDensity_integrable 1 m n ρ η hρ hη hcρ hcη hpρ hpη (c : ℤ) hcz
  rw [gamma0TrueWidthBesselOrbital_identity_eq_kernel N c m n hm hn ρ η hρ hη hcρ hcη hpρ hpη]
  refine (cuspWeylOrbitalKernel_compact_norm_bound 1 m n ρ η hρ.continuous hcρ hpρ hη.continuous hcη hpη
    hA hB hc hρlo hηlo hM hi).trans_eq ?_
  unfold spectralWeylCompactHeightBudget
  field_simp [hc.ne',hA.ne',hB.ne']

theorem gamma0TrueWidthBesselGeometricFibre_identity_zero_of_not_dvd (N c : ℕ)
    [NeZero N] [NeZero c] (m n : ℤ) (ρ η : ℝ → ℝ) (hNc : ¬ N ∣ c) :
    gamma0TrueWidthBesselGeometricFibre N 1 1 c m n ρ η = 0 := by
  rw [gamma0TrueWidthBesselGeometricFibre,gamma0TrueWidthKloostermanSum_identity_eq_standard,
    ite_eq_right hNc,zero_mul,mul_zero]

theorem gamma0TrueWidthBesselGeometricFibre_identity_height_bound (N c : ℕ) [NeZero N] [NeZero c]
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    {A B M : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hρlo : ∀ y ∈ tsupport ρ, A ≤ y) (hηlo : ∀ z ∈ tsupport η, B ≤ z)
    (hM : ∀ z : ℝ, ‖spectralKLHeightBaseTest η z‖ ≤ M) :
    ‖gamma0TrueWidthBesselGeometricFibre N 1 1 c m n ρ η‖ ≤
      (N : ℝ)^2*‖gamma0TrueWidthKloostermanSum N 1 1 c m n‖*(spectralWeylCompactHeightBudget A B M ρ/(c : ℝ)^3) := by
  have he : ‖gamma0TrueWidthBesselGeometricFibre N 1 1 c m n ρ η‖ =
      (N : ℝ)^2*‖gamma0TrueWidthKloostermanSum N 1 1 c m n‖*‖gamma0TrueWidthBesselOrbital N 1 1 c m n ρ η‖ := by
    simp only [gamma0TrueWidthBesselGeometricFibre,gamma0CuspFrequencyStep_identity,
      norm_mul,Complex.norm_natCast,pow_two,mul_assoc]
  rw [he]
  exact mul_le_mul_of_nonneg_left
    (gamma0TrueWidthBesselOrbital_identity_height_bound N c m n hm hn ρ η hρ hη hcρ hcη hpρ hpη hA hB hρlo hηlo hM)
    (mul_nonneg (sq_nonneg _) (norm_nonneg _))

theorem gamma0TrueWidthBesselGeometricFibre_identity_weil_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (N c : ℕ) [NeZero N] [NeZero c] (m n : ℤ), m ≠ 0 → n ≠ 0 →
      ∀ (ρ η : ℝ → ℝ), ContDiff ℝ ∞ ρ → ContDiff ℝ ∞ η → HasCompactSupport ρ → HasCompactSupport η →
        tsupport ρ ⊆ Ioi (0 : ℝ) → tsupport η ⊆ Ioi (0 : ℝ) →
        ∀ (A B M : ℝ), 0 < A → 0 < B → (∀ y ∈ tsupport ρ, A ≤ y) → (∀ z ∈ tsupport η, B ≤ z) →
          (∀ z : ℝ, ‖spectralKLHeightBaseTest η z‖ ≤ M) →
          ‖gamma0TrueWidthBesselGeometricFibre N 1 1 c m n ρ η‖ ≤
            D*spectralWeylCompactHeightBudget A B M ρ*(N : ℝ)^2*(c : ℝ)^(-(5/2 : ℝ)+ε)*
              ((Nat.gcd c (Int.gcd m n) : ℕ) : ℝ)^(1/2 : ℝ) := by
  obtain ⟨D,hD,hW⟩ := gamma0TrueWidthKloostermanSum_identity_weil hε
  refine ⟨D,hD,?_⟩
  intro N c _ _ m n hm hn ρ η hρ hη hcρ hcη hpρ hpη A B M hA hB hρlo hηlo hM
  let Q := spectralWeylCompactHeightBudget A B M ρ
  let G := ((Nat.gcd c (Int.gcd m n) : ℕ) : ℝ)^(1/2 : ℝ)
  have hQ : 0 ≤ Q := spectralWeylCompactHeightBudget_nonneg hA hB ((norm_nonneg _).trans (hM 0)) ρ
  have hc : 0 < (c : ℝ) := Nat.cast_pos.mpr (NeZero.pos c)
  have hBnd := gamma0TrueWidthBesselGeometricFibre_identity_height_bound N c m n hm hn ρ η hρ hη hcρ hcη hpρ hpη
    hA hB hρlo hηlo hM
  have hK : ‖gamma0TrueWidthKloostermanSum N 1 1 c m n‖ ≤ D*(c : ℝ)^((1/2 : ℝ)+ε)*G := hW N c m n
  have hcPow : ((c : ℝ)^3)⁻¹ = (c : ℝ)^(-(3 : ℝ)) := by
    rw [Real.rpow_neg hc.le]
    norm_num
  have hExp : (c : ℝ)^((1/2 : ℝ)+ε)*(c : ℝ)^(-(3 : ℝ)) = (c : ℝ)^(-(5/2 : ℝ)+ε) := by
    rw [← Real.rpow_add hc]
    congr 1
    ring_nf
  change _ ≤ D*Q*(N : ℝ)^2*(c : ℝ)^(-(5/2 : ℝ)+ε)*G
  calc
    _ ≤ (N : ℝ)^2*(D*(c : ℝ)^((1/2 : ℝ)+ε)*G)*(Q/(c : ℝ)^3) :=
      hBnd.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (sq_nonneg _))
        (div_nonneg hQ (pow_nonneg hc.le _)))
    _ = D*Q*(N : ℝ)^2*((c : ℝ)^((1/2 : ℝ)+ε)*(c : ℝ)^(-(3 : ℝ)))*G := by
      rw [div_eq_mul_inv Q ((c : ℝ)^3),hcPow]
      ring_nf
    _ = _ := by rw [hExp]

end ArtinMatthews
