module

public import ArtinMatthews.MarkedMajorArcFrequencyBudget
public import ArtinMatthews.MarkedMajorArcErrorAbsorption
public import ArtinMatthews.MarkedMajorArcPrimePowerAbsorption


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine arbitrary-log-power high-height prime cancellation. The proof
uses the actual Hurwitz/Vinogradov estimate, character Perron contour,
sharp-interval smoothing, prime-power removal and partial summation. -/
namespace ArtinMatthews

open Filter
open scoped Topology

/-- Uniform high-height cancellation for every Dirichlet character and every
sharp dyadic subinterval in the full polynomial frequency range. -/
theorem marked_major_high_prime_cancellation (A η τ P : ℝ)
    (hA : 0 ≤ A) (hη : 0 < η) (hτ : 0 < τ) (hP : 0 ≤ P) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q], (q:ℝ) ≤ L^A →
      ∀ (χ : DirichletCharacter ℂ q) (t u v : ℝ),
      L^B₀ ≤ |t| → |t| ≤ Real.exp (2*L) →
      Real.exp (τ*L) ≤ u → u ≤ v → v ≤ 2*u → v ≤ Real.exp (η*L) →
      ‖markedMajorPrimeSum χ t u v‖ ≤ L^(-P) := by
  obtain ⟨K,C,T₀,hK,hC,hT₀,hactual⟩ :=
    marked_major_mangoldt_interval_error A 3 hA (by norm_num)
  let D := P+4
  let B := P+D+6
  have hD : P+3 < D := by dsimp [D]; linarith
  have hB : P+D+5 < B := by dsimp [B]; linarith
  have hB0 : 0 ≤ B := by dsimp [B,D]; linarith
  have hErr := marked_major_interval_uniform_power K C η τ P D B (1/6)
    hK.le hC hη hτ hP hD hB (by norm_num)
  have hPP := marked_major_prime_power_uniform_power P η τ (1/6)
    hP hτ hη (by norm_num)
  have hFreq := marked_major_frequency_budget B T₀ τ hB0 hτ
  refine ⟨B+2,by linarith,?_⟩
  filter_upwards [hactual,hErr,hPP,hFreq,eventually_gt_atTop (0:ℝ)] with
    L hactual hErr hPP hFreq hLp
  intro q _ hq χ t u v htlo hthi hulo huv hvu hvhi
  obtain ⟨hH,hHt,hTlo,hThi,hu1,hlogu⟩ := hFreq t u htlo hthi hulo
  have hε : 0 < L^(-D) := Real.rpow_pos_of_pos hLp _
  have hprefix (w : ℝ) (hw : w ∈ Set.Icc u v) :
      ‖∑ n ∈ Finset.Ioc ⌊u⌋₊ ⌊w⌋₊, markedMajorMangoldt χ t n‖ ≤ (1/6)*L^(-P) := by
    apply (hactual q hq χ (L^(-D)) u w t (L^B) hε hu1 hw.1
      hH hHt hTlo hThi).trans
    exact hErr u w hulo hw.1 (hw.2.trans hvu) (hw.2.trans hvhi)
  have hp := marked_major_prime_interval_of_mangoldt_prefix χ t hu1 hlogu huv hvu
    (by positivity : 0 ≤ (1/6:ℝ)*L^(-P)) hprefix
  have hpower := hPP u v hulo huv hvu hvhi
  exact hp.trans (by nlinarith)

end ArtinMatthews
