module

public import ArtinMatthews.ProbeBadPrimeNormalSeries
public import ArtinMatthews.ProbeEulerHolomorphy


set_option backward.privateInPublic true
@[expose] public section

/-! Joint holomorphy of the literal bad-prime source correction. A
summable bound for the entire summands gives a summable derivative bound
by the complex Cauchy estimate on smaller balls. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField Set Filter Metric
open scoped NumberField Classical BigOperators Topology
noncomputable section

theorem probeCoordinates_tsum_differentiableOn {ι : Type*}
    (f : ι → ArtinMatthews.ProbeCoordinates → ℂ) (u : ι → ℝ)
    (hu : Summable u) (hf : ∀ i, Differentiable ℂ (f i))
    (s : Set ArtinMatthews.ProbeCoordinates) (hs : IsOpen s)
    (hb : ∀ i q, q ∈ s → ‖f i q‖ ≤ u i) :
    DifferentiableOn ℂ (fun q => ∑' i, f i q) s := by
  intro p hp
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hp)
  have hr : 0 < R / 2 := by positivity
  have hqsub {q : ArtinMatthews.ProbeCoordinates} (hq : q ∈ ball p (R / 2)) :
      ball q (R / 2) ⊆ s := by
    intro y hy
    apply hball
    have hdist := dist_triangle y q p
    have hy' := Metric.mem_ball.mp hy
    have hq' := Metric.mem_ball.mp hq
    apply Metric.mem_ball.mpr
    linarith
  have hqmem {q : ArtinMatthews.ProbeCoordinates} (hq : q ∈ ball p (R / 2)) : q ∈ s :=
    hqsub hq (mem_ball_self hr)
  have hd (i : ι) (q : ArtinMatthews.ProbeCoordinates) (_hq : q ∈ ball p (R / 2)) :
      HasFDerivAt (f i) (fderiv ℂ (f i) q) q := (hf i q).hasFDerivAt
  have hderiv (i : ι) (q : ArtinMatthews.ProbeCoordinates) (hq : q ∈ ball p (R / 2)) :
      ‖fderiv ℂ (f i) q‖ ≤ (2 * u i) / (R / 2) := by
    apply Complex.norm_fderiv_le_div_of_mapsTo_ball
      (fun y _ => (hf i y).differentiableWithinAt) ?_ hr
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc
      _ ≤ ‖f i y‖ + ‖f i q‖ := norm_sub_le _ _
      _ ≤ u i + u i := add_le_add (hb i y (hqsub hq hy)) (hb i q (hqmem hq))
      _ = _ := by ring
  exact (hasFDerivAt_tsum_of_isPreconnected ((hu.mul_left 2).div_const (R / 2))
    isOpen_ball (convex_ball p (R / 2)).isPreconnected hd hderiv (mem_ball_self hr)
    (Summable.of_norm_bounded hu (fun i => hb i p hp))
    (mem_ball_self hr)).differentiableAt.differentiableWithinAt

variable (K : Type*) [Field K] [NumberField K]

theorem probeBadPrimeSourceSeries_differentiableOn (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (hj : 0 < j)
    (γ ν θ : ℂ) (hγ : ‖γ‖ = 1) (hν : ‖ν‖ = 1) (hθ : ‖θ‖ = 1)
    (hcut : (ArtinMatthews.probeEulerCutoff : ℝ) ≤ Ideal.absNorm (Ideal.span {p})) :
    DifferentiableOn ℂ (fun q : ArtinMatthews.ProbeCoordinates =>
      probeBadPrimeSourceSeries K p hp.ne_zero χ j γ ν θ q.1 q.2.1 q.2.2)
      (interior ArtinMatthews.probeEulerDomain) := by
  unfold probeBadPrimeSourceSeries
  apply DifferentiableOn.fun_sum
  intro e _
  apply probeCoordinates_tsum_differentiableOn _
    (probeBadPrimeMajorant (Ideal.absNorm (Ideal.span {p})))
    (probeBadPrimeMajorant_summable (by positivity))
    (fun i => probeBadPrimeSourceTerm_differentiable K p hp.ne_zero χ j γ ν θ e i)
    _ isOpen_interior
  intro i q hq
  have hq' : q ∈ ArtinMatthews.probeEulerDomain := interior_subset hq
  exact probeBadPrimeSourceTerm_norm_le_majorant K p hp χ hχ hminus j hj γ ν θ
    q.1 q.2.1 q.2.2 hγ hν hθ hcut hq' e i

theorem probeBadPrimeSourceSeries_differentiableOn_open (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (hj : 0 < j)
    (γ ν θ : ℂ) (hγ : ‖γ‖ = 1) (hν : ‖ν‖ = 1) (hθ : ‖θ‖ = 1)
    (hcut : (ArtinMatthews.probeEulerCutoff : ℝ) ≤ Ideal.absNorm (Ideal.span {p})) :
    DifferentiableOn ℂ (fun q : ArtinMatthews.ProbeCoordinates =>
      probeBadPrimeSourceSeries K p hp.ne_zero χ j γ ν θ q.1 q.2.1 q.2.2)
      ArtinMatthews.probeEulerOpenDomain :=
  (probeBadPrimeSourceSeries_differentiableOn K p hp χ hχ hminus j hj γ ν θ hγ hν hθ hcut).mono
    ArtinMatthews.probeEulerOpenDomain_subset_interior

namespace ProbeBadPrimeData

variable {K : Type*} [Field K] [NumberField K] {P : Ideal (𝓞 K)}
variable (D : ProbeBadPrimeData K P)

theorem correction_differentiableOn :
    DifferentiableOn ℂ (fun q : ArtinMatthews.ProbeCoordinates => D.correction q.1 q.2.1 q.2.2)
      (interior ArtinMatthews.probeEulerDomain) := by
  obtain ⟨hγ, hν, hθ⟩ := D.phase_norms
  have hcut : (ArtinMatthews.probeEulerCutoff : ℝ) ≤
      Ideal.absNorm (Ideal.span {D.prime}) := by rw [D.span_eq]; exact D.norm_large
  have hQ : (Ideal.absNorm (Ideal.span {D.prime}) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr D.prime_isPrime.ne_zero)
  have hV : Differentiable ℂ (fun q : ArtinMatthews.ProbeCoordinates =>
      ArtinMatthews.probeLocalV (Ideal.absNorm (Ideal.span {D.prime})) q.2.2) := by
    intro q
    exact ((differentiableAt_id.snd.snd.const_mul 6).neg.const_cpow (Or.inl hQ))
  exact ((differentiableOn_const (c := (1 : ℂ))).sub hV.differentiableOn).mul
    (probeBadPrimeSourceSeries_differentiableOn K D.prime D.prime_isPrime D.character D.order_six
      D.minus_one D.valuation D.valuation_pos D.gamma D.vartheta D.theta hγ hν hθ hcut)

theorem correction_differentiableOn_open :
    DifferentiableOn ℂ (fun q : ArtinMatthews.ProbeCoordinates => D.correction q.1 q.2.1 q.2.2)
      ArtinMatthews.probeEulerOpenDomain :=
  D.correction_differentiableOn.mono ArtinMatthews.probeEulerOpenDomain_subset_interior

theorem correction_continuousOn_open :
    ContinuousOn (fun q : ArtinMatthews.ProbeCoordinates => D.correction q.1 q.2.1 q.2.2)
      ArtinMatthews.probeEulerOpenDomain :=
  D.correction_differentiableOn_open.continuousOn

end ProbeBadPrimeData

end
end ArtinMatthews.VaryingKummerAnalytic
