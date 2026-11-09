module

public import ArtinMatthews.GiantArrayRemoval
public import ArtinMatthews.MarkedCorrelationEndpoint


set_option backward.privateInPublic true
@[expose] public section

/-! The final ordered array-removal implication for the original fixed-
progression giant statistic. Each depth chooses its number of bands first;
the prime limit is then taken before the array count and depth limits.
The remaining hypothesis is explicitly the actual marked-prime bound. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped Topology Asymptotics

theorem giant_fixed_progression_isLittleO_of_marked_prime_bounds
    {M : ℕ} (U : Finset (ZMod M)ˣ) (ε : ℝ) (hε : 0<ε) (hεq : ε<1/4)
    (Φ : ℝ → ℝ) {T a : ℝ} (hT : 0≤T) (ha : 0<a)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ)) (hΦT : Φ T=0)
    (hΦ0 : ∀ t, 0≤Φ t) (hlow : ∀ t<a, Φ t=0)
    (c A : ℝ) (n₀ : ℕ)
    (hmarked : ∀ n≥n₀, ∃ K : ℕ, ∀ e : Fin K → ℝ,
      (∀ i, (1/10 : ℝ)<e i ∧ e i<1/5) → Function.Injective e →
      ∀ δ : ℝ, 0<δ → ∀ᶠ x : ℝ in atTop,
        Real.log x / x * ‖giantFixedProgressionArrayPrimeSum U e ε Φ T x‖ ≤
          A * Real.exp (-(2*(n : ℝ))) /
            (markedCorrelationSieveExponent c (2*n))^2 + δ) :
    giantFixedProgressionPrimeSum U ε Φ T =o[atTop]
      (fun x : ℝ => x / Real.log x) := by
  have hzero : Φ 0=0 := hlow 0 ha
  have hF : ∀ᶠ x : ℝ in atTop, ∀ u, (u+1).Prime →
      ‖giantFixedResidueCenteredCoefficient U ε x u‖ ≤ 1 :=
    (giant_fixed_residue_coefficient_bound U hε hεq).mono (fun _ hx u _ => hx u)
  have hmarked' : ∀ n≥n₀, ∃ K : ℕ, ∀ e : Fin K → ℝ,
      (∀ i, (1/10 : ℝ)<e i ∧ e i<1/5) → Function.Injective e →
      ∀ δ : ℝ, 0<δ → ∀ᶠ x : ℝ in atTop,
        Real.log x / x * ‖markedPrimeSingleArrayCorrelation e Φ T
          (giantFixedResidueCenteredCoefficient U ε) x‖ ≤
          A * Real.exp (-(2*(n : ℝ))) /
            (markedCorrelationSieveExponent c (2*n))^2 + δ := by
    intro n hn
    obtain ⟨K,hK⟩ := hmarked n hn
    refine ⟨K,?_⟩
    intro e he hinj δ hδ
    filter_upwards [hK e he hinj δ hδ,
      giant_fixed_progression_array_eq_bounded U ε T hεq.le hT Φ hzero] with x hx heq
    rwa [heq e] at hx
  have h := marked_actual_correlation_isLittleO_of_marked Φ hT ha hΦ hderiv hΦT hΦ0 hlow
    (giantFixedResidueCenteredCoefficient U ε) (by norm_num : (0 : ℝ)≤1) hF c A n₀ hmarked'
  have heq : giantFixedProgressionPrimeSum U ε Φ T =ᶠ[atTop]
      markedPrimeCorrelation Φ T (giantFixedResidueCenteredCoefficient U ε) :=
    giant_fixed_progression_prime_eq_bounded U ε T hεq.le hT Φ hzero
  exact h.congr' heq.symm Filter.EventuallyEq.rfl

end
end ArtinMatthews
