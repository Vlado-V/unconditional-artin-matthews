module

public import ArtinMatthews.SpectralJMixedSourceTrace
public import ArtinMatthews.SourceJHolomorphicTrace


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set Complex MeasureTheory
open scoped ContDiff MatrixGroups
noncomputable section

def sourceJHolomorphicIndexMagnitude (m : ℤ) (hm : m ≠ 0) : ℕ+ :=
  ⟨m.natAbs, Int.natAbs_pos.mpr hm⟩

private theorem signedIndex_magnitude (m : ℤ) (hm : m ≠ 0) :
    sourceJHolomorphicSignedIndex (decide (m < 0)) (sourceJHolomorphicIndexMagnitude m hm) = m := by
  by_cases h : m < 0
  · simp [sourceJHolomorphicSignedIndex, sourceJHolomorphicIndexMagnitude, h,
      Int.ofNat_natAbs_of_nonpos h.le]
  · simp [sourceJHolomorphicSignedIndex, sourceJHolomorphicIndexMagnitude, h,
      Int.natAbs_of_nonneg (le_of_not_gt h)]

def sourceJHolomorphicSameSignGramSeries (f : ℝ → ℂ)
    (r s : ℕ) [NeZero r] [NeZero s]
    {a b : ℤ} (hab : (r : ℤ) * a - (s : ℤ) * b = 1)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (_hmn : 0 < m * n) : ℂ :=
  sourceJHolomorphicMixedGramSeries f r s hab (decide (m < 0))
    (sourceJHolomorphicIndexMagnitude m hm) (sourceJHolomorphicIndexMagnitude n hn)

theorem sourceJHolomorphicSameSignGramTerm_summable
    (f : ℝ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (r s : ℕ) [NeZero r] [NeZero s] (hr : 1 < r) (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ) * a - (s : ℤ) * b = 1)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    Summable (fun j : ℕ => ‖sourceJHolomorphicMixedGramTerm f r s hab (decide (m < 0))
      (sourceJHolomorphicIndexMagnitude m hm) (sourceJHolomorphicIndexMagnitude n hn) j‖) :=
  sourceJHolomorphicMixedGramTerm_summable f hf hc hp r s hr hcop hab (decide (m < 0))
    (sourceJHolomorphicIndexMagnitude m hm) (sourceJHolomorphicIndexMagnitude n hn)

theorem gamma0MixedABLJ_source_forward_trace
    (r s : ℕ) [NeZero r] [NeZero s] (hr : 1 < r) (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ) * a - (s : ℤ) * b = 1)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : 0 < m * n)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    let F := fun C : ℝ => f (4 * Real.pi * Real.sqrt (|(m : ℝ) * (n : ℝ)|) / C)
    Summable (gamma0MixedSourceModulusTerm r s hcop m n F) ∧
    Summable (fun i => ‖gamma0BareCuspidalTerm (r * s) (spectralJClippedEnergyTest f hf hc hp)
      (gamma0CuspOneOver s) 1 Y hY n m hn hm i‖) ∧
    IntegrableOn (gamma0BareContinuousRhoIntegrand (r * s) (spectralJClippedEnergyTest f hf hc hp)
      (gamma0CuspOneOver s) 1 Y hY n m hn hm) (Ioi (0 : ℝ)) ∧
    (∑' c, gamma0MixedSourceModulusTerm r s hcop m n F c) =
      gamma0MixedSourceCompensation r s b n *
        (4 * gamma0BareSourceSpectralSide (r * s) (spectralJClippedEnergyTest f hf hc hp)
          (gamma0CuspOneOver s) 1 Y hY n m hn hm +
        sourceJHolomorphicSameSignGramSeries f r s hab m n hm hn hmn) := by
  have hsame : (m < 0 ↔ n < 0) := by
    rcases mul_pos_iff.mp hmn with ⟨hmp, hnp⟩ | ⟨hmn, hnn⟩
    · exact iff_of_false (not_lt_of_ge hmp.le) (not_lt_of_ge hnp.le)
    · exact iff_of_true hmn hnn
  have hsign : decide (m < 0) = decide (n < 0) := by
    by_cases hnegative : m < 0
    · simp [hnegative, hsame.mp hnegative]
    · have hnnegative : ¬n < 0 := fun hn => hnegative (hsame.mpr hn)
      simp [hnegative, hnnegative]
  have hmagnitude := signedIndex_magnitude m hm
  have hnmagnitude :
      sourceJHolomorphicSignedIndex (decide (m < 0)) (sourceJHolomorphicIndexMagnitude n hn) = n := by
    rw [hsign]
    exact signedIndex_magnitude n hn
  have hholo := sourceJHolomorphicMixedGramSeries_eq_odd f hf.continuous hc hp
    r s hr hcop hab (decide (m < 0))
    (sourceJHolomorphicIndexMagnitude m hm) (sourceJHolomorphicIndexMagnitude n hn)
  rw [hmagnitude, hnmagnitude] at hholo
  obtain ⟨hs, hC, hI, htrace⟩ := gamma0MixedABLJ_source_modulus_trace
    r s hr hcop hab Y hY m n hm hn hmn f hf hc hp
  refine ⟨hs, hC, hI, ?_⟩
  rw [← hholo] at htrace
  exact htrace

end
end ArtinMatthews
