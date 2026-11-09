module

public import ArtinMatthews.SpectralPolynomialC2Approximation
public import ArtinMatthews.SpectralExpPullback
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial


set_option backward.privateInPublic true
@[expose] public section

/-! Finite positive-rate exponential approximation with one common pointwise envelope. -/
namespace ArtinMatthews
open Set Polynomial
open scoped ContDiff Polynomial BigOperators
noncomputable section

def spectralExpPolynomial (p : ℂ[X]) (s : ℝ) : ℂ :=
  spectralExpPullback (fun u => p.eval (u : ℂ)) s

theorem spectralExpPolynomial_contDiff (p : ℂ[X]) :
    ContDiff ℝ ∞ (spectralExpPolynomial p) := by
  have hp : ContDiff ℂ ∞ (fun z : ℂ => p.eval z) := by
    simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using
      p.contDiff_aeval (𝕜 := ℂ) ∞
  have he : ContDiff ℝ ∞ (fun s : ℝ => Real.exp (-s)) := contDiff_neg.exp
  have hc : ContDiff ℝ ∞ (fun s : ℝ => (Real.exp (-s) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp he
  exact hc.mul ((hp.restrict_scalars ℝ).comp hc)

theorem spectralExpPolynomial_eq_sum (p : ℂ[X]) (s : ℝ) :
    spectralExpPolynomial p s =
      ∑ n ∈ p.support, p.coeff n * (Real.exp (-((n + 1 : ℕ) : ℝ) * s) : ℂ) := by
  classical
  unfold spectralExpPolynomial spectralExpPullback
  dsimp only
  rw [Polynomial.eval_eq_sum]
  unfold Polynomial.sum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  dsimp only
  have he : -((n + 1 : ℕ) : ℝ) * s = ((n + 1 : ℕ) : ℝ) * (-s) := by ring
  rw [he, Real.exp_nat_mul, Complex.ofReal_pow, pow_succ']
  ring

theorem spectralExpPolynomial_gaussian_sum (p : ℂ[X]) (x : ℝ) :
    (x : ℂ) * spectralExpPolynomial p (x ^ 2) =
      ∑ n ∈ p.support, p.coeff n *
        ((x : ℂ) * (Real.exp (-((n + 1 : ℕ) : ℝ) * x ^ 2) : ℂ)) := by
  rw [spectralExpPolynomial_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem exists_spectralExpPolynomial_C2_near
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ s : ℝ, 0 ≤ s →
      ‖spectralExpPolynomial p s - g s‖ ≤ ε * Real.exp (-s) ∧
      ‖deriv (spectralExpPolynomial p) s - deriv g s‖ ≤ ε * Real.exp (-s) ∧
      ‖deriv (deriv (spectralExpPolynomial p)) s - deriv (deriv g) s‖ ≤ ε * Real.exp (-s) := by
  let G := spectralLogCompactProfile g
  let δ := ε / 5
  have hδ : 0 < δ := div_pos hε (by norm_num)
  have hG : ContDiff ℝ ∞ G := spectralLogCompactProfile_contDiff hg hc
  have hG' := (contDiff_infty_iff_deriv.mp hG).2
  obtain ⟨p, hp⟩ := exists_complexPolynomial_C2_near G (hG.of_le (by simp)) hδ
  let d (u : ℝ) := p.eval (u : ℂ) - G u
  have hD (u : ℝ) : HasDerivAt d (p.derivative.eval (u : ℂ) - deriv G u) u :=
    (p.hasDerivAt (u : ℂ)).comp_ofReal.sub ((hG.differentiable (by simp)) u).hasDerivAt
  have hd : Differentiable ℝ d := fun u => (hD u).differentiableAt
  have hD₁ : deriv d = fun u : ℝ => p.derivative.eval (u : ℂ) - deriv G u :=
    funext fun u => (hD u).deriv
  have hD' (u : ℝ) : HasDerivAt (deriv d)
      (p.derivative.derivative.eval (u : ℂ) - deriv (deriv G) u) u := by
    rw [hD₁]
    exact (p.derivative.hasDerivAt (u : ℂ)).comp_ofReal.sub
      ((hG'.differentiable (by simp)) u).hasDerivAt
  have hd' : Differentiable ℝ (deriv d) := fun u => (hD' u).differentiableAt
  have hEq : (fun s => spectralExpPolynomial p s - g s) = spectralExpPullback d := by
    funext s
    rw [← congrFun (spectralExpPullback_logCompactProfile g) s]
    unfold spectralExpPolynomial spectralExpPullback d
    change _ = _ * (p.eval (Real.exp (-s) : ℂ) - spectralLogCompactProfile g (Real.exp (-s)))
    ring
  have hP := spectralExpPolynomial_contDiff p
  have hP' := (contDiff_infty_iff_deriv.mp hP).2
  have hg' := (contDiff_infty_iff_deriv.mp hg).2
  have h₁ : deriv (fun s => spectralExpPolynomial p s - g s) =
      fun s => deriv (spectralExpPolynomial p) s - deriv g s := by
    funext s
    exact deriv_fun_sub ((hP.differentiable (by simp)) s) ((hg.differentiable (by simp)) s)
  have h₂ : deriv (deriv (fun s => spectralExpPolynomial p s - g s)) =
      fun s => deriv (deriv (spectralExpPolynomial p)) s - deriv (deriv g) s := by
    rw [h₁]
    funext s
    exact deriv_fun_sub ((hP'.differentiable (by simp)) s) ((hg'.differentiable (by simp)) s)
  refine ⟨p, fun s hs => ?_⟩
  let u := Real.exp (-s)
  have hu0 : 0 ≤ u := (Real.exp_pos _).le
  have hu1 : u ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs)
  have hPu := hp u ⟨hu0, hu1⟩
  have h0 : ‖d u‖ ≤ δ := hPu.1
  have h1 : ‖deriv d u‖ ≤ δ := by rw [hD₁]; exact hPu.2.1
  have h2 : ‖deriv (deriv d) u‖ ≤ δ := by rw [(hD' u).deriv]; exact hPu.2.2
  have huNorm : ‖(u : ℂ)‖ = u := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
  have hfirst : ‖(u : ℂ) * deriv d u‖ ≤ δ := by
    rw [norm_mul, huNorm]
    exact (mul_le_mul_of_nonneg_left h1 hu0).trans (mul_le_of_le_one_left hδ.le hu1)
  have hsecond : ‖(u : ℂ) ^ 2 * deriv (deriv d) u‖ ≤ δ := by
    rw [norm_mul, norm_pow, huNorm]
    exact (mul_le_mul_of_nonneg_left h2 (sq_nonneg u)).trans
      (mul_le_of_le_one_left hδ.le (pow_le_one₀ hu0 hu1))
  have hthird : ‖3 * (u : ℂ) * deriv d u‖ ≤ 3 * δ := by
    have h3 : ‖(3 : ℂ)‖ = 3 := by norm_num
    rw [mul_assoc, norm_mul, h3]
    exact mul_le_mul_of_nonneg_left hfirst (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [congrFun hEq s, spectralExpPullback, norm_mul]
    change ‖(u : ℂ)‖ * ‖d u‖ ≤ ε * u
    rw [huNorm, mul_comm ε]
    exact mul_le_mul_of_nonneg_left (h0.trans (by dsimp only [δ]; linarith)) hu0
  · rw [← congrFun h₁ s, hEq, spectralExpPullback_deriv hd, norm_mul, norm_neg]
    change ‖(u : ℂ)‖ * ‖d u + (u : ℂ) * deriv d u‖ ≤ ε * u
    rw [huNorm, mul_comm ε]
    apply mul_le_mul_of_nonneg_left _ hu0
    exact (norm_add_le _ _).trans ((add_le_add h0 hfirst).trans (by dsimp only [δ]; linarith))
  · rw [← congrFun h₂ s, hEq, spectralExpPullback_deriv_two hd hd', norm_mul]
    change ‖(u : ℂ)‖ * ‖d u + 3 * (u : ℂ) * deriv d u +
      (u : ℂ)^2 * deriv (deriv d) u‖ ≤ ε * u
    rw [huNorm, mul_comm ε]
    apply mul_le_mul_of_nonneg_left _ hu0
    exact (norm_add_le _ _).trans
      ((add_le_add ((norm_add_le _ _).trans (add_le_add h0 hthird)) hsecond).trans
        (by dsimp only [δ]; linarith))

end
end ArtinMatthews
