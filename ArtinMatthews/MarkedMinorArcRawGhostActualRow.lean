module

public import ArtinMatthews.MarkedMinorArcRawGhostFullRow
public import ArtinMatthews.MarkedMemoryTiltActual


set_option backward.privateInPublic true
@[expose] public section

/-! The actual source ghost has a weighted absolute row bound independent
of every pending cutoff and band exponent. Its fixed Schur parameter
depends only on q and rho, and applies uniformly to every actual path stage. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators

noncomputable def markedRawGhostSchurParameter (q ρ : ℝ) : ℝ :=
  max 1 (1/(ρ*(1-Real.sqrt q/ρ^2)))

theorem markedRawGhostSchurParameter_ge_one (q ρ : ℝ) : 1 ≤ markedRawGhostSchurParameter q ρ :=
  le_max_left _ _

/-- One fixed numeric Schur parameter makes every genuine stage survival
factor at most one; its choice contains no band exponent or state size. -/
theorem markedRawGhostSchurParameter_survival {q ρ : ℝ} (hρ : 0 < ρ)
    (hgap : Real.sqrt q < ρ^2) {qStage : ℝ} (hqStage₀ : 0 ≤ qStage)
    (hqStage : qStage ≤ Real.sqrt q) :
    qStage/ρ^2+(1-qStage)/(ρ*markedRawGhostSchurParameter q ρ) ≤ 1 := by
  let r := Real.sqrt q/ρ^2
  let v₀ := markedRawGhostSchurParameter q ρ
  have hr : r < 1 := (div_lt_one (sq_pos_of_pos hρ)).mpr hgap
  have hv₀ : 0 < v₀ := (by norm_num : (0:ℝ)<1).trans_le (markedRawGhostSchurParameter_ge_one q ρ)
  have hden : 0 < ρ*(1-r) := mul_pos hρ (by linarith)
  have hbound : 1/(ρ*(1-r)) ≤ v₀ := le_max_right _ _
  have hprod : 1 ≤ (ρ*(1-r))*v₀ := by
    have hh := mul_le_mul_of_nonneg_left hbound hden.le
    simpa only [one_div,mul_inv_cancel₀ hden.ne'] using hh
  have hi : 1/(ρ*v₀) ≤ 1-r := (div_le_iff₀ (mul_pos hρ hv₀)).mpr (by nlinarith [hprod])
  have hfirst : qStage/ρ^2 ≤ r := div_le_div_of_nonneg_right hqStage (sq_nonneg _)
  have hsecond : (1-qStage)/(ρ*v₀) ≤ 1/(ρ*v₀) :=
    div_le_div_of_nonneg_right (by linarith) (mul_pos hρ hv₀).le
  change qStage/ρ^2+(1-qStage)/(ρ*v₀) ≤ 1
  linarith

/-- The true typed tilted band mass is at most two, uniformly in the actual
baseline q. This follows from the proved harmonic-law comparison. -/
theorem markedRawGhost_actual_band_mass_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ q : ℝ, 0 ≤ q → q ≤ 1 → ∀ j,
      (∑ p : ↥(markedRawActualPrimeBand e x j), markedRawActualPrimeAtom e q x j p) ≤ 2 := by
  have hV := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually
    (show 0 < e j by linarith [he j]))
  filter_upwards [marked_actual_tilted_atom_comparison_eventually e he,hV] with x hx hV
  intro q hq₀ hq₁ j
  rw [markedRawActualPrimeAtom_sum_eq]
  calc
    _ ≤ ∑ p : ↥(markedLogPowerBand (e j) x), 2*markedHarmonicAtom _ p :=
      Finset.sum_le_sum (fun p _ => (hx q hq₀ hq₁ j p).2)
    _ = _ := by
      rw [← Finset.mul_sum,markedHarmonicAtom_sum _
        ((by positivity : 0 < Real.log 2/2).trans (hV j).1),mul_one]

set_option maxHeartbeats 1000000 in
/-- Genuine uniform actual ghost absolute row bound. It uses the literal
ν atoms and total-truncated indexed choices; the bound depends only on
K,q,rho, uniformly in the actual path stage, memory size, position and all
band exponents. The latter affect only the eventual threshold. -/
theorem markedRawGhost_actual_weighted_row_eventually {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) {q ρ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hρ : 0 < ρ) (hgap : Real.sqrt q < ρ^2) :
    ∀ᶠ x : ℝ in atTop, ∀ (qStage : ℝ), 0 ≤ qStage → qStage ≤ Real.sqrt q →
      ∀ (B : ℕ) (m : MarkedRawMemory (markedRawActualPrimeBand e x) B)
        (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2),
      markedRawGhostWeightedAbsRow (markedRawActualPrimeAtom e q x)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) qStage ρ
        (markedRawGhostSchurParameter q ρ) m z hz ≤
        Real.exp ((Fintype.card J : ℝ)*(2*markedRawGhostSchurParameter q ρ/ρ)) := by
  classical
  let v₀ := markedRawGhostSchurParameter q ρ
  have hv₀ : 0 < v₀ := (by norm_num : (0:ℝ)<1).trans_le (markedRawGhostSchurParameter_ge_one q ρ)
  have hsqrt : Real.sqrt q ≤ 1 := by nlinarith [Real.sq_sqrt hq₀,Real.sqrt_nonneg q]
  have hV := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually
    (show 0 < e j by linarith [he j]))
  filter_upwards [hV,marked_actual_tilted_atom_comparison_eventually e he,
    markedRawGhost_actual_band_mass_eventually e he] with x hV hν hs
  intro qStage hqStage₀ hqStage B m z hz
  have hqStage₁ : qStage ≤ 1 := hqStage.trans hsqrt
  have hνpos : ∀ j p, 0 ≤ markedRawActualPrimeAtom e q x j p := by
    intro j p
    rw [markedRawActualPrimeAtom_eq_tilted]
    exact (hν q hq₀ hq₁ j _).1
  have hVp : ∀ j, 0 ≤ bandReciprocalMass (markedLogPowerBand (e j) x) :=
    fun j => ((by positivity : 0 < Real.log 2/2).trans (hV j).1).le
  have hpol : ∏ j, (qStage/ρ^2+(1-qStage)/(ρ*v₀))^(markedRawGroupHitIndices m j z hz).card ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro j _
      exact pow_nonneg (add_nonneg (div_nonneg hqStage₀ (sq_nonneg _))
        (div_nonneg (sub_nonneg.mpr hqStage₁) (mul_pos hρ hv₀).le)) _
    · intro j _
      exact pow_le_one₀ (add_nonneg (div_nonneg hqStage₀ (sq_nonneg _))
        (div_nonneg (sub_nonneg.mpr hqStage₁) (mul_pos hρ hv₀).le))
        (markedRawGhostSchurParameter_survival hρ hgap hqStage₀ hqStage)
  have hExp : (∏ j, Real.exp ((v₀*(1-qStage)*bandReciprocalMass (markedLogPowerBand (e j) x)/ρ)*
      (∑ p : ↥(markedRawActualPrimeBand e x j), markedRawActualPrimeAtom e q x j p))) ≤
      Real.exp ((Fintype.card J : ℝ)*(2*v₀/ρ)) := by
    calc
      _ ≤ ∏ _j : J, Real.exp (2*v₀/ρ) := by
        apply Finset.prod_le_prod₀ (fun j _ => (Real.exp_pos _).le)
        intro j _
        apply Real.exp_le_exp.mpr
        have hs₀ : 0 ≤ ∑ p : ↥(markedRawActualPrimeBand e x j), markedRawActualPrimeAtom e q x j p :=
          Finset.sum_nonneg (fun p _ => hνpos j p)
        have hc : 0 ≤ v₀*(1-qStage)*bandReciprocalMass (markedLogPowerBand (e j) x)/ρ :=
          div_nonneg (mul_nonneg (mul_nonneg hv₀.le (sub_nonneg.mpr hqStage₁)) (hVp j)) hρ.le
        have hc₁ : v₀*(1-qStage)*bandReciprocalMass (markedLogPowerBand (e j) x)/ρ ≤ v₀/ρ := by
          apply div_le_div_of_nonneg_right _ hρ.le
          calc
            _ ≤ v₀*1*bandReciprocalMass (markedLogPowerBand (e j) x) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : 1-qStage ≤ 1) hv₀.le) (hVp j)
            _ ≤ v₀*1*1 := mul_le_mul_of_nonneg_left (hV j).2.le (by linarith : 0 ≤ v₀*1)
            _ = _ := by ring
        calc
          _ ≤ (v₀/ρ)*2 := mul_le_mul hc₁ (hs q hq₀ hq₁ j) hs₀ (div_nonneg hv₀.le hρ.le)
          _ = _ := by ring
      _ = _ := by simp only [Finset.prod_const,Finset.card_univ,← Real.exp_nat_mul]
  exact (markedRawGhost_actual_weighted_row (markedRawActualPrimeAtom e q x) hνpos _ hVp
    hqStage₀ hqStage₁ hρ hv₀ m z hz).trans
      ((mul_le_of_le_one_right (Finset.prod_nonneg (fun j _ => (Real.exp_pos _).le)) hpol).trans hExp)

end ArtinMatthews
