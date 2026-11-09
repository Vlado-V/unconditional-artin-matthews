module

public import ArtinMatthews.SpectralGamma0GreenPointSeries
public import ArtinMatthews.SpectralGamma0GreenSquaredExpansion


set_option backward.privateInPublic true
@[expose] public section

/-! The full point kernel, with genuine gradient-cutoff convergence. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

theorem gamma0GreenSquaredPointKernel_term (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (i : Gamma0AllHeightSpectralIndex N)
    (p q : ℝ × ℝ) :
    gamma0GreenPointCoefficient N r Y hY i p * star (gamma0GreenPointCoefficient N r Y hY i q) =
      (i.1.re : ℂ)^2 * gamma0FullCuspidalPlaneRepresentative N r Y hY i p *
        star (gamma0FullCuspidalPlaneRepresentative N r Y hY i q) := by
  unfold gamma0GreenPointCoefficient
  rw [star_mul]
  have hr : star (i.1.re : ℂ) = (i.1.re : ℂ) := Complex.conj_ofReal _
  rw [hr]
  ring

theorem gamma0GreenSquaredPointKernel_absolute_summable (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (p q : ℝ × ℝ)
    (hp : 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2)
    (hq : 0 < q.1 ∧ q.1 < 2*(N:ℝ) ∧ Y < q.2) :
    Summable (fun i => ‖gamma0GreenPointCoefficient N r Y hY i p *
      star (gamma0GreenPointCoefficient N r Y hY i q)‖) := by
  have hK : IsCompact ({p,q} : Set (ℝ × ℝ)) := isCompact_singleton.insert p
  have hKΩ : ({p,q} : Set (ℝ × ℝ)) ⊆ {z | 0 < z.1 ∧ z.1 < 2*(N:ℝ) ∧ Y < z.2} := by
    intro z hz
    simp only [mem_insert_iff,mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hp
    · exact hq
  obtain ⟨_,_,hb⟩ := gamma0GreenSquaredPointKernel_compact_absolute_bound N r Y hY hK hKΩ
  exact (hb p (by simp) q (by simp)).1

theorem gamma0GreenSquaredPointKernel_hasSum (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (p q : ℝ × ℝ)
    (hp : 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2)
    (hq : 0 < q.1 ∧ q.1 < 2*(N:ℝ) ∧ Y < q.2) :
    HasSum (fun i => (i.1.re : ℂ)^2 * gamma0FullCuspidalPlaneRepresentative N r Y hY i p *
      star (gamma0FullCuspidalPlaneRepresentative N r Y hY i q))
      (gamma0GreenSquaredPointKernel N r Y hY p q) := by
  unfold gamma0GreenSquaredPointKernel
  have h := (gamma0GreenSquaredPointKernel_absolute_summable N r Y hY p q hp hq).of_norm.hasSum
  simpa only [gamma0GreenSquaredPointKernel_term] using h

theorem gamma0GreenSquaredPointKernel_eq_series (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (p q : ℝ × ℝ) :
    gamma0GreenSquaredPointKernel N r Y hY p q =
      ∑' i : Gamma0AllHeightSpectralIndex N,
        (i.1.re : ℂ)^2 * gamma0FullCuspidalPlaneRepresentative N r Y hY i p *
          star (gamma0FullCuspidalPlaneRepresentative N r Y hY i q) := by
  exact tsum_congr (fun i => gamma0GreenSquaredPointKernel_term N r Y hY i p q)

theorem gamma0GreenSquaredPointKernel_cutoff_tendsto (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (p q : ℝ × ℝ)
    (hp : 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2)
    (hq : 0 < q.1 ∧ q.1 < 2*(N:ℝ) ∧ Y < q.2) :
    Tendsto (fun R : ℝ => ∑ i ∈ gamma0AllHeightGradientSpectralCutoff N R,
      (i.1.re : ℂ)^2 * gamma0FullCuspidalPlaneRepresentative N r Y hY i p *
        star (gamma0FullCuspidalPlaneRepresentative N r Y hY i q))
      atTop (nhds (gamma0GreenSquaredPointKernel N r Y hY p q)) :=
  (gamma0GreenSquaredPointKernel_hasSum N r Y hY p q hp hq).comp
    (gamma0AllHeightGradientSpectralCutoff_tendsto N)

theorem gamma0GreenSquaredPointKernel_hermitian (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (p q : ℝ × ℝ) :
    star (gamma0GreenSquaredPointKernel N r Y hY p q) =
      gamma0GreenSquaredPointKernel N r Y hY q p := by
  unfold gamma0GreenSquaredPointKernel
  rw [tsum_star]
  apply tsum_congr
  intro i
  simp only [star_mul,star_star]

end ArtinMatthews
