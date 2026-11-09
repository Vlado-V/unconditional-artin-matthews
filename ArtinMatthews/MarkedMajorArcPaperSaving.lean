module

public import ArtinMatthews.MarkedMajorArcPaperSource


set_option backward.privateInPublic true
@[expose] public section

/-! Arbitrary logarithmic saving for the literal sixfold determinant major
sum of PD05, with its actual conjugated coefficients and original major set. -/
namespace ArtinMatthews
open Filter Finset ComplexConjugate
open scoped ContDiff

 theorem markedMajorLabelMass_sq {J : Type*} [Fintype J] (bands : J → Finset ℕ) :
    (markedMajorLabelMass bands)^2 = ∏ j,((bandReciprocalMass (bands j))^2)⁻¹ := by
  unfold markedMajorLabelMass
  rw [← Finset.prod_pow]
  simp only [inv_pow]

 theorem markedMajor_determinant_major_all_log
    (cfg : MarkedMajorLabelEnergyConfig) (σ Kx : ℝ) (hσ : 0 ≤ σ)
    (cutoff : ℝ → ℂ) (hcutoff : ContDiff ℝ ∞ cutoff) (hnorm : ∀ y, ‖cutoff y‖ ≤ 1)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) (hinterval : lo < 4*hi)
    (hsupp : Function.support cutoff ⊆ Set.Icc lo hi)
    (ψ : SchwartzMap ℝ ℂ) {R : ℝ} (hψ : tsupport ψ ⊆ Set.Icc (-R) R) (P : ℝ) (hP : 0 ≤ P) :
    ∀ᶠ L : ℝ in atTop, ∀ X : ℝ, 1 ≤ X → X ≤ Real.exp (σ*L) → X ≤ Kx*Real.exp L →
      ∀ {J : Type} [Fintype J] [DecidableEq J]
      (z : MarkedMajorLabelEnergyData J cfg L X),
      ∀ Q : ℝ, 0 ≤ Q → Q ≤ L^cfg.a → 2*Q ≤ cfg.Kθ*L^cfg.A₀ →
      (∀ j p,p ∈ z.allBands j → Q < (p:ℝ)) →
      (∀ n ∈ Icc z.l z.r,z.β n ≠ 0 → ∀ p ∈ Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊,¬p∣n) →
      ‖markedMajorDeterminantPaperSum z.allBands cutoff ψ Q z.Y (Real.exp (L^(6/25:ℝ)))
        z.modulation z.u z.v z.l z.r z.β‖ ≤ (z.Y*X)*L^(-P) := by
  filter_upwards [markedMajor_majorSource_all_log cfg σ Kx hσ cutoff hcutoff hnorm
    hlo hhi hinterval hsupp ψ hψ P hP] with L hs
  intro X hX1 hupper hcomp J _ _ z Q hQ hQa hQθ hband hrough
  have hr' : ∀ n ∈ Icc z.l z.r,z.conjugateBeta.β n ≠ 0 →
      ∀ p ∈ Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊,¬p∣n := by
    intro n hn hne
    apply hrough n hn
    intro hzero
    apply hne
    simp only [MarkedMajorLabelEnergyData.conjugateBeta,hzero,map_zero]
  have hb := hs X hX1 hupper hcomp z z.conjugateBeta rfl Q hQ hQa hQθ hband hband hrough hr'
  rwa [markedMajor_paper_source_eq] at hb

end ArtinMatthews
