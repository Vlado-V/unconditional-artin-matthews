module

public import ArtinMatthews.MarkedMajorMellinLabelEnergyCentral
public import ArtinMatthews.MarkedMajorMellinLabelEnergyMean
public import ArtinMatthews.MarkedMajorMellinLabelEnergyLog
public import ArtinMatthews.MarkedMajorMellinEnergyAssembly


set_option backward.privateInPublic true
@[expose] public section

/-! Arbitrary logarithmic saving for the full actual two-endpoint major
Mellin integral. The endpoint records carry only literal arithmetic data;
all central cancellation and weighted means are proved inputs. -/
namespace ArtinMatthews
open Filter MeasureTheory Set
open scoped ContDiff

theorem markedMajorMellinLabelEnergy_all_log
    (cfg : MarkedMajorLabelEnergyConfig) (σ Kx : ℝ) (hσ : 0 ≤ σ)
    (cutoff : ℝ → ℂ) (hcutoff : ContDiff ℝ ∞ cutoff) (hnorm : ∀ y, ‖cutoff y‖ ≤ 1)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) (hsupp : Function.support cutoff ⊆ Icc lo hi)
    (ψ : SchwartzMap ℝ ℂ) {a b R : ℝ} (ha : 0 < a) (hab : a < b)
    (hψ : tsupport ψ ⊆ Icc (-R) R) (P : ℝ) (hP : 0 ≤ P) :
    ∀ᶠ L : ℝ in atTop, ∀ (X : ℝ), 1 ≤ X → ∀ hX : 0 < X,
      X ≤ Real.exp (σ*L) → X ≤ Kx*Real.exp L →
      ∀ {J J' : Type} [Fintype J] [DecidableEq J] [Fintype J'] [DecidableEq J']
      (z : MarkedMajorLabelEnergyData J cfg L X) (z' : MarkedMajorLabelEnergyData J' cfg L X)
      (θ : ℝ), |θ| ≤ cfg.Kθ*L^cfg.A₀ →
      (∫ p : ℝ × ℝ, ‖markedMajorConstructedCoefficient ψ ha hab hψ hX θ (p.1/X,p.2)*
        (z.endpoint cutoff p.1*z'.conjugateEndpoint cutoff (p.2-p.1))‖) ≤ L^(-P) := by
  obtain ⟨n,hn⟩ := exists_nat_ge (P+2*cfg.A₀+2*cfg.D+9)
  obtain ⟨CF,hCF,hkernel⟩ := markedMajor_constructed_endpoint_L1_energy ψ ha hab hψ n
  obtain ⟨CM,hCM,hmean⟩ := markedMajorLabelEnergy_weighted cfg σ hi hσ hhi cutoff hnorm
    (fun y hy => (hsupp hy).2)
  have hcentral := markedMajorLabelEnergy_central cfg cutoff hcutoff hlo hhi hsupp
    σ Kx (cfg.A₀+2) (cfg.A₀+2+P+2) hσ (by linarith [cfg.hA₀]) (by linarith [cfg.hA₀])
  filter_upwards [hcentral,hmean,
    markedMajorLabelEnergy_log_budget cfg.A₀ cfg.D P cfg.Kθ CF CM markedMajorFourierWeightMass
      hCF.le hCM.le markedMajorFourierWeightMass_nonneg n hn,
    eventually_ge_atTop (1:ℝ)] with L hc hm hbudget hL
  intro X hX1 hX hupper hcomp J J' _ _ _ _ z z' θ hθ
  have hcent := hc X hX1 hupper hcomp z
  have hcent' := hc X hX1 hupper hcomp z'
  have hW : 1 ≤ 1+|θ| := le_add_of_nonneg_right (abs_nonneg θ)
  have hscaled (c : ℝ) := hm X hX1 hupper z (1+|θ|) c hW
  have hscaled' (c : ℝ) := hm X hX1 hupper z' (1+|θ|) c hW
  have henergy := hkernel X hX1 hX θ (L^(cfg.A₀+2)) (L^(-(cfg.A₀+2+P+2)))
    (CM*(1+|θ|)*L^(2*cfg.D+5)) (Real.rpow_nonneg (by linarith : 0 ≤ L) _)
    (z.endpoint cutoff) (z'.conjugateEndpoint cutoff)
    (z.endpoint_continuous cutoff) (z'.conjugateEndpoint_continuous cutoff)
    (z.endpoint_bounded cutoff) (z'.conjugateEndpoint_bounded cutoff)
    hcent.1 hcent'.2 (fun c => (hscaled c).1) (fun c => (hscaled' c).2)
  exact henergy.trans (hbudget (1+|θ|) hW (markedMajorLabelEnergy_theta_scale hL cfg.hA₀ hθ))

end ArtinMatthews
