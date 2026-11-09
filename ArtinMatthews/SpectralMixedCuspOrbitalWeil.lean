module

public import ArtinMatthews.SpectralTrueWidthOrbitalBudget


set_option backward.privateInPublic true
@[expose] public section

/-! Height-explicit Weil control of the actual mixed cusp positive
Bessel fiber, with the literal common-period multiplicity `r*s*s`. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem gamma0MixedBesselGeometricFibre_weil_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (r s q : ℕ) [NeZero r] [NeZero s] [NeZero q], r.Coprime s →
      ∀ (m n : ℤ), m ≠ 0 → n ≠ 0 →
      ∀ (ρ η : ℝ → ℝ), ContDiff ℝ ∞ ρ → ContDiff ℝ ∞ η → HasCompactSupport ρ → HasCompactSupport η →
        tsupport ρ ⊆ Ioi (0 : ℝ) → tsupport η ⊆ Ioi (0 : ℝ) →
        ∀ (A B M : ℝ), 0 < A → 0 < B → (∀ y ∈ tsupport ρ, A ≤ y) → (∀ z ∈ tsupport η, B ≤ z) →
          (∀ z : ℝ, ‖spectralKLHeightBaseTest η z‖ ≤ M) →
          ‖gamma0TrueWidthBesselGeometricFibre (r*s) (gamma0CuspOneOver s) 1 q n m ρ η‖ ≤
            D*spectralWeylCompactHeightBudget A B M ρ*((r : ℝ)*(s : ℝ)^2)*(q : ℝ)^(-(5/2 : ℝ)+ε)*
              ((Nat.gcd q (Int.gcd m n) : ℕ) : ℝ)^(1/2 : ℝ) := by
  obtain ⟨D,hD,hW⟩ := gamma0MixedKloosterman_weil hε
  refine ⟨D,hD,?_⟩
  intro r s q _ _ _ hcop m n hm hn ρ η hρ hη hcρ hcη hpρ hpη A B M hA hB hρlo hηlo hM
  let Q := spectralWeylCompactHeightBudget A B M ρ
  let G := ((Nat.gcd q (Int.gcd m n) : ℕ) : ℝ)^(1/2 : ℝ)
  let L := (r : ℝ)*(s : ℝ)^2
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hQ : 0 ≤ Q := spectralWeylCompactHeightBudget_nonneg hA hB ((norm_nonneg _).trans (hM 0)) ρ
  have hq : 0 < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hBnd := gamma0TrueWidthBesselGeometricFibre_height_bound (r*s) q (gamma0CuspOneOver s) 1
    n m hn hm ρ η hρ hη hcρ hcη hpρ hpη hA hB hρlo hηlo hM
  have hLe : ((gamma0CuspFrequencyStep (r*s) 1 : ℝ)*(gamma0CuspFrequencyStep (r*s) (gamma0CuspOneOver s) : ℝ)) = L := by
    rw [gamma0CuspFrequencyStep_identity,gamma0MixedCuspFrequencyStep r s hcop,Nat.cast_mul]
    change (r : ℝ)*(s : ℝ)*(s : ℝ) = (r : ℝ)*(s : ℝ)^2
    rw [pow_two,mul_assoc]
  rw [hLe] at hBnd
  have hK : ‖gamma0TrueWidthKloostermanSum (r*s) (gamma0CuspOneOver s) 1 q n m‖ ≤ D*(q : ℝ)^((1/2 : ℝ)+ε)*G :=
    hW r s q hcop m n
  have hqPow : ((q : ℝ)^3)⁻¹ = (q : ℝ)^(-(3 : ℝ)) := by
    rw [Real.rpow_neg hq.le]
    norm_num
  have hExp : (q : ℝ)^((1/2 : ℝ)+ε)*(q : ℝ)^(-(3 : ℝ)) = (q : ℝ)^(-(5/2 : ℝ)+ε) := by
    rw [← Real.rpow_add hq]
    congr 1
    ring_nf
  change _ ≤ D*Q*L*(q : ℝ)^(-(5/2 : ℝ)+ε)*G
  calc
    _ ≤ L*(D*(q : ℝ)^((1/2 : ℝ)+ε)*G)*(Q/(q : ℝ)^3) :=
      hBnd.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK hL)
        (div_nonneg hQ (pow_nonneg hq.le _)))
    _ = D*Q*L*((q : ℝ)^((1/2 : ℝ)+ε)*(q : ℝ)^(-(3 : ℝ)))*G := by
      rw [div_eq_mul_inv Q ((q : ℝ)^3),hqPow]
      ring_nf
    _ = _ := by rw [hExp]

end ArtinMatthews
