module

public import ArtinMatthews.SpectralJNativeLimit
public import ArtinMatthews.SpectralJClippedReality


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set Filter
open scoped ContDiff MatrixGroups Topology ComplexConjugate
noncomputable section

theorem gamma0JSource_regularization_tendsto_swapped (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (hReal : ∀ x : ℝ, conj (f x) = f x)
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    Tendsto (fun k : ℕ => gamma0BareSourceSpectralSide (r * s)
      (spectralJRegularizedEnergyTest f hf hc hp (k : ℝ) (Nat.cast_nonneg k))
        (gamma0CuspOneOver s) 1 Y hY n m hn hm) atTop
      (𝓝 (gamma0BareSourceSpectralSide (r * s) (spectralJClippedEnergyTest f hf hc hp)
        (gamma0CuspOneOver s) 1 Y hY n m hn hm)) := by
  have h := continuous_star.continuousAt.tendsto.comp
    (gamma0JSource_regularization_tendsto f hf hc hp r s hcop Y hY m n hm hn)
  have hfun : (fun k : ℕ => star (gamma0BareSourceSpectralSide (r * s)
      (spectralJRegularizedEnergyTest f hf hc hp (k : ℝ) (Nat.cast_nonneg k))
        1 (gamma0CuspOneOver s) Y hY m n hm hn)) =
      (fun k : ℕ => gamma0BareSourceSpectralSide (r * s)
        (spectralJRegularizedEnergyTest f hf hc hp (k : ℝ) (Nat.cast_nonneg k))
          (gamma0CuspOneOver s) 1 Y hY n m hn hm) := by
    funext k
    exact (gamma0BareSourceSpectralSide_real_swap (r * s) _
      (spectralJRegularizedEnergyTest_real f hf hc hp hReal _ (Nat.cast_nonneg k))
      (gamma0CuspOneOver s) 1 Y hY n m hn hm).symm
  have htarget :
      star (gamma0BareSourceSpectralSide (r * s) (spectralJClippedEnergyTest f hf hc hp)
        1 (gamma0CuspOneOver s) Y hY m n hm hn) =
      gamma0BareSourceSpectralSide (r * s) (spectralJClippedEnergyTest f hf hc hp)
        (gamma0CuspOneOver s) 1 Y hY n m hn hm :=
    (gamma0BareSourceSpectralSide_real_swap (r * s) _
      (spectralJClippedEnergyTest_real f hf hc hp hReal)
      (gamma0CuspOneOver s) 1 Y hY n m hn hm).symm
  simpa only [Function.comp_def, hfun, htarget] using h

end
end ArtinMatthews
