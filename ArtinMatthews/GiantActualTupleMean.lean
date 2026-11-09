module

public import ArtinMatthews.GiantFixedProgressionExtractionLimit


set_option backward.privateInPublic true
@[expose] public section

/-! The actual composite-tuple cancellation input gives the finite
prime mean used by the positive-density assembly. -/
namespace ArtinMatthews

open Filter
open scoped Topology BigOperators Asymptotics

noncomputable section

theorem giant_uncentered_prime_mean_of_actual_tuples {M : ℕ} [NeZero M]
    (U : Finset (ZMod M)ˣ) (ε : ℝ) (hε : 0 < ε) (hεq : ε < 1 / 4)
    (Φ : ℝ → ℝ) {a T : ℝ} (ha : 0 < a) (haT : a ≤ T)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ))
    (hcompact : HasCompactSupport Φ)
    (hsupp : Function.support Φ ⊆ Set.Ioo a T) (hΦ0 : ∀ t, 0 ≤ Φ t)
    (c : ℝ) (hc : 0 < c) (hcε : c < ε / 2)
    (htuple : ∀ m ≥ 20000, ∃ K : ℕ, ∀ e : Fin K → ℝ,
      (∀ j, (1 / 10 : ℝ) < e j ∧ e j < 1 / 5) → Function.Injective e →
      ∀ (χ : DirichletCharacter ℂ M) j,
        j ∈ Finset.Icc 2 ⌈2 / markedSieveExponent c m⌉₊ →
        giantOrdinaryTupleSum e χ (giantMarkedCenteredCore ε) Φ
          (T + 1) (markedSieveExponent c m) j
            =o[atTop] (fun x : ℝ => x / Real.log x)) :
    Tendsto (fun x : ℝ => ((Real.log x / x : ℝ) : ℂ) *
      giantUncenteredPrimeTest U ε Φ T x) atTop
      (𝓝 (((U.card : ℝ) / M.totient * giantPrimeConstant ε *
        ∫ t : ℝ, Φ t : ℝ) : ℂ)) := by
  exact giant_uncentered_prime_mean_of_centered U ε hε hεq Φ hΦ hderiv
    hcompact ha haT hsupp
    (giant_fixed_progression_prime_isLittleO_of_actual_tuples U ε hε hεq Φ
      ha (ha.le.trans haT) hΦ hderiv hsupp hΦ0 c hc hcε htuple)

end
end ArtinMatthews
