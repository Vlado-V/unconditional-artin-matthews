module

public import ArtinMatthews.SpectralABLMixedScalarReindex
public import ArtinMatthews.SpectralABLOppositeComplexTrace
public import ArtinMatthews.SpectralMixedCuspInequivalent


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory
open scoped MatrixGroups ContDiff
noncomputable section

/-- The original mixed-cusp opposite-sign modulus sum with the actual
native spectral terms and the literal source compensation. -/
theorem gamma0MixedABLOpposite_source_forward_trace (r s : ℕ) [NeZero r] [NeZero s]
    (hr : 1 < r) (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m*n < 0)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    let F := fun C : ℝ => f (4*Real.pi*Real.sqrt (|(m : ℝ)*(n : ℝ)|)/C)
    let h := spectralABLOppositeEnergyTest f hf hc hp
    Summable (gamma0MixedSourceModulusTerm r s hcop m n F) ∧
    Summable (fun i => ‖gamma0BareCuspidalTerm (r*s) h (gamma0CuspOneOver s) 1 Y hY n m hn hm i‖) ∧
    IntegrableOn (gamma0BareContinuousRhoIntegrand (r*s) h (gamma0CuspOneOver s) 1 Y hY n m hn hm)
      (Ioi (0 : ℝ)) ∧
    (∑' c, gamma0MixedSourceModulusTerm r s hcop m n F c) =
      (4*(Real.pi : ℂ))*gamma0MixedSourceCompensation r s b n*
        gamma0BareSourceSpectralSide (r*s) h (gamma0CuspOneOver s) 1 Y hY n m hn hm := by
  let F := fun C : ℝ => f (4*Real.pi*Real.sqrt (|(m : ℝ)*(n : ℝ)|)/C)
  let h := spectralABLOppositeEnergyTest f hf hc hp
  let G (q : Ioi (0 : ℕ)) := gamma0ABLOppositeGeometricTerm (r*s) (gamma0CuspOneOver s) 1 q n m f
  obtain ⟨hG,hS,hI,htrace⟩ := gamma0ABLOpposite_forward_trace (r*s) (gamma0CuspOneOver s) 1
    (Or.inr (gamma0MixedCusps_inequivalent_of_one_lt r s hr)) Y hY n m hn hm
    (by simpa only [mul_comm n m] using hmn) f hf hc hp
  have hterm : gamma0MixedNativeModulusTerm r s m n F = G := by
    funext q
    simp only [gamma0MixedNativeModulusTerm,G,gamma0ABLOppositeGeometricTerm,F,mul_comm (n : ℝ) (m : ℝ)]
  obtain ⟨hs,he⟩ := gamma0MixedSourceModulus_tsum_reindex r s hcop hab m n F
  rw [hterm] at hs he
  refine ⟨hs.mp hG,hS,hI,?_⟩
  change (∑' c, gamma0MixedSourceModulusTerm r s hcop m n F c) =
    (4*(Real.pi : ℂ))*gamma0MixedSourceCompensation r s b n*
      gamma0BareSourceSpectralSide (r*s) h (gamma0CuspOneOver s) 1 Y hY n m hn hm
  rw [he,htrace]
  change _ = (4*(Real.pi : ℂ))*gamma0MixedSourceCompensation r s b n*
    ((1/(4*(Real.pi : ℂ)))*(∑' q, G q))
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring

end
end ArtinMatthews
