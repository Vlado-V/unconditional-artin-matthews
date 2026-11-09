module

public import ArtinMatthews.SpectralJMixedComplexTrace
public import ArtinMatthews.SpectralABLMixedScalarReindex


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set Complex MeasureTheory
open scoped ContDiff MatrixGroups
noncomputable section

theorem gamma0MixedABLJ_source_modulus_trace
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
        ∑' q : Ioi (0 : ℕ),
          gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
            (spectralJOddSynthesis f)) := by
  let F := fun C : ℝ => f (4 * Real.pi * Real.sqrt (|(m : ℝ) * (n : ℝ)|) / C)
  let G (q : Ioi (0 : ℕ)) :=
    gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m f
  have hG : Summable G :=
    (gamma0MixedJ_geometric_reconstruction f hf hc hp r s hcop m n hm hn hmn).1.of_norm
  have hterm : gamma0MixedNativeModulusTerm r s m n F = G := by
    funext q
    simp only [gamma0MixedNativeModulusTerm, G, gamma0ABLOppositeGeometricTerm, F,
      mul_comm (n : ℝ) (m : ℝ)]
  obtain ⟨hs, he⟩ := gamma0MixedSourceModulus_tsum_reindex r s hcop hab m n F
  rw [hterm] at hs he
  obtain ⟨hC, hI⟩ := gamma0JSource_absolute f hf hc hp r s hcop Y hY m n hm hn
  obtain ⟨hC', hI'⟩ := gamma0BareSource_absolute_swap (r * s)
    (spectralJClippedEnergyTest f hf hc hp) 1 (gamma0CuspOneOver s) Y hY m n hm hn hC hI
  refine ⟨hs.mp hG, hC', hI', ?_⟩
  rw [he]
  change gamma0MixedSourceCompensation r s b n * (∑' q, G q) = _
  rw [gamma0MixedJ_modulus_trace f hf hc hp r s hr hcop Y hY m n hm hn hmn]

end
end ArtinMatthews
