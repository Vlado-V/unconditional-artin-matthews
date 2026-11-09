module

public import ArtinMatthews.SpectralGamma0GreenPointKernel
public import ArtinMatthews.SpectralGamma0GreenEvaluationVector


set_option backward.privateInPublic true
@[expose] public section

/-! The point kernel is the limit of genuine Green-squared mass pairings. -/
noncomputable section
open Set Filter
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

local instance greenSquaredPretrace_inner (N : ℕ) [NeZero N] :
    InnerProductSpace ℂ (gamma0AllHeightCuspidalMassSpace N) :=
  Submodule.innerProductSpace (𝕜 := ℂ) (E := Gamma0RegionL2 N) _

def gamma0SpectralPointCutoff (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y)
    (s : Finset (Gamma0AllHeightSpectralIndex N)) (p : ℝ × ℝ) :
    gamma0AllHeightCuspidalMassSpace N :=
  ∑ i ∈ s, star (gamma0FullCuspidalPlaneRepresentative N r Y hY i p) •
    gamma0FullCuspidalSpectralBasis N i

theorem gamma0CuspidalGreen_point_cutoff (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y)
    (s : Finset (Gamma0AllHeightSpectralIndex N)) (p : ℝ × ℝ) :
    gamma0CuspidalGreen N (gamma0SpectralPointCutoff N r Y hY s p) =
      ∑ i ∈ s, star (gamma0GreenPointCoefficient N r Y hY i p) •
        gamma0FullCuspidalSpectralBasis N i := by
  simp only [gamma0SpectralPointCutoff,map_sum,map_smul,gamma0CuspidalGreen_basis_eigen,smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  unfold gamma0GreenPointCoefficient
  have hr : star (i.1.re : ℂ) = (i.1.re : ℂ) := Complex.conj_ofReal _
  calc
    _ = star (gamma0FullCuspidalPlaneRepresentative N r Y hY i p) * (i.1.re : ℂ) :=
      congrArg (fun z : ℂ => star (gamma0FullCuspidalPlaneRepresentative N r Y hY i p) * z)
        (gamma0AllHeightSpectralValue_real N i).symm
    _ = _ := by rw [star_mul,hr]

theorem gamma0CuspidalGreen_point_cutoff_inner (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y)
    (s : Finset (Gamma0AllHeightSpectralIndex N)) (p q : ℝ × ℝ) :
    inner ℂ (gamma0CuspidalGreen N (gamma0SpectralPointCutoff N r Y hY s p))
      (gamma0CuspidalGreen N (gamma0SpectralPointCutoff N r Y hY s q)) =
      ∑ i ∈ s, gamma0GreenPointCoefficient N r Y hY i p *
        star (gamma0GreenPointCoefficient N r Y hY i q) := by
  rw [gamma0CuspidalGreen_point_cutoff,gamma0CuspidalGreen_point_cutoff]
  have h := (gamma0FullCuspidalSpectralBasis N).orthonormal.inner_sum
    (fun i => star (gamma0GreenPointCoefficient N r Y hY i p))
    (fun i => star (gamma0GreenPointCoefficient N r Y hY i q)) s
  simpa only [starRingEnd_apply,star_star] using h

theorem gamma0CuspidalGreen_squared_point_cutoff_pairing (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y)
    (s : Finset (Gamma0AllHeightSpectralIndex N)) (p q : ℝ × ℝ) :
    inner ℂ (gamma0SpectralPointCutoff N r Y hY s p)
      (gamma0CuspidalGreen N (gamma0CuspidalGreen N (gamma0SpectralPointCutoff N r Y hY s q))) =
      ∑ i ∈ s, gamma0GreenPointCoefficient N r Y hY i p *
        star (gamma0GreenPointCoefficient N r Y hY i q) := by
  have he : inner ℂ (gamma0CuspidalGreen N (gamma0SpectralPointCutoff N r Y hY s p))
      (gamma0CuspidalGreen N (gamma0SpectralPointCutoff N r Y hY s q)) =
      inner ℂ (gamma0SpectralPointCutoff N r Y hY s p)
        (gamma0CuspidalGreen N (gamma0CuspidalGreen N (gamma0SpectralPointCutoff N r Y hY s q))) := by
    change inner ℂ (gamma0Green N (gamma0SpectralPointCutoff N r Y hY s p).val)
      (gamma0Green N (gamma0SpectralPointCutoff N r Y hY s q).val) =
        inner ℂ (gamma0SpectralPointCutoff N r Y hY s p).val
          (gamma0Green N (gamma0Green N (gamma0SpectralPointCutoff N r Y hY s q).val))
    exact gamma0Green_symmetric N _ _
  exact he.symm.trans (gamma0CuspidalGreen_point_cutoff_inner N r Y hY s p q)

theorem gamma0CuspidalGreen_point_cutoff_tendsto (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (p : ℝ × ℝ)
    (hp : 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2) :
    Tendsto (fun R : ℝ => gamma0CuspidalGreen N
      (gamma0SpectralPointCutoff N r Y hY (gamma0AllHeightGradientSpectralCutoff N R) p))
      atTop (nhds (gamma0GreenEvaluationVector N r Y hY p hp)) := by
  simpa only [gamma0CuspidalGreen_point_cutoff,Function.comp_def] using
    (gamma0GreenEvaluationVector_hasSum N r Y hY p hp).comp
      (gamma0AllHeightGradientSpectralCutoff_tendsto N)

theorem gamma0GreenSquaredPointKernel_pretrace_limit (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (p q : ℝ × ℝ)
    (hp : 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2)
    (hq : 0 < q.1 ∧ q.1 < 2*(N:ℝ) ∧ Y < q.2) :
    Tendsto (fun R : ℝ =>
      inner ℂ (gamma0SpectralPointCutoff N r Y hY (gamma0AllHeightGradientSpectralCutoff N R) p)
        (gamma0CuspidalGreen N (gamma0CuspidalGreen N
          (gamma0SpectralPointCutoff N r Y hY (gamma0AllHeightGradientSpectralCutoff N R) q))))
      atTop (nhds (gamma0GreenSquaredPointKernel N r Y hY p q)) := by
  have h := (gamma0GreenSquaredPointKernel_absolute_summable N r Y hY p q hp hq).of_norm.hasSum.comp
    (gamma0AllHeightGradientSpectralCutoff_tendsto N)
  simpa only [gamma0CuspidalGreen_squared_point_cutoff_pairing,Function.comp_def,
    gamma0GreenSquaredPointKernel] using h

theorem gamma0GreenSquaredPointKernel_diagonal (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (p : ℝ × ℝ)
    (hp : 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2) :
    gamma0GreenSquaredPointKernel N r Y hY p p =
      (‖gamma0GreenEvaluationVector N r Y hY p hp‖ : ℂ)^2 := by
  rw [gamma0GreenSquaredPointKernel_eq_inner N r Y hY p p hp hp]
  exact inner_self_eq_norm_sq_to_K (gamma0GreenEvaluationVector N r Y hY p hp)

end ArtinMatthews
