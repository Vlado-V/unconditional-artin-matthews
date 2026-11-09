module

public import ArtinMatthews.SpectralCuspLocalFourier


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine Fourier ODE from a smooth, locally periodic two-cell
section, using only an interior full period. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace ArtinMatthews

theorem spectralPlaneSecond_vertical_deriv (G : ℝ × ℝ → ℂ) (hG : ContDiff ℝ ∞ G)
    (p : ℝ × ℝ) :
    spectralPlaneSecond G 1 p = deriv (deriv (fun y => G (p.1, y))) p.2 := by
  have hd : ContDiff ℝ ∞ (fun p => fderiv ℝ G p (0, 1)) :=
    (hG.fderiv_right (by simp)).clm_apply contDiff_const
  change fderiv ℝ (fun p => fderiv ℝ G p (0, 1)) p (0, 1) = _
  rw [← spectralPlanePartialY_eq_fderiv (hd.differentiable (by simp) p)]
  unfold spectralPlanePartialY
  have he : (fun t => fderiv ℝ G (p.1, t) (0, 1)) = deriv (fun y => G (p.1, y)) := by
    funext t
    exact (spectralPlanePartialY_eq_fderiv (hG.differentiable (by simp) (p.1, t))).symm
  rw [he]

theorem spectralPlaneSecond_shiftX (G : ℝ × ℝ → ℂ) (hG : ContDiff ℝ ∞ G)
    (a : ℝ) (i : Fin 2) (p : ℝ × ℝ) :
    spectralPlaneSecond (fun q => G (q.1 + a, q.2)) i p =
      spectralPlaneSecond G i (p.1 + a, p.2) := by
  have hH : ContDiff ℝ ∞ (fun q : ℝ × ℝ => G (q.1 + a, q.2)) :=
    hG.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)
  fin_cases i
  · change spectralPlaneSecond (fun q => G (q.1 + a, q.2)) 0 p =
      spectralPlaneSecond G 0 (p.1 + a, p.2)
    rw [spectralPlaneSecond_horizontal_deriv _ hH, spectralPlaneSecond_horizontal_deriv G hG]
    have he : deriv (fun x => G (x + a, p.2)) = fun x => deriv (fun x => G (x, p.2)) (x + a) := by
      funext x
      exact deriv_comp_add_const (f := fun x => G (x, p.2)) (a := a) (x := x)
    change deriv (deriv (fun x => G (x + a, p.2))) p.1 = _
    rw [he]
    exact deriv_comp_add_const (f := deriv (fun x => G (x, p.2))) (a := a) (x := p.1)
  · change spectralPlaneSecond (fun q => G (q.1 + a, q.2)) 1 p =
      spectralPlaneSecond G 1 (p.1 + a, p.2)
    rw [spectralPlaneSecond_vertical_deriv _ hH, spectralPlaneSecond_vertical_deriv G hG]

theorem spectralLocalPeriod_deriv (N Y y : ℝ) (hN : 0 < N) (hy : Y < y)
    (u : ℝ × ℝ → ℂ)
    (hp : ∀ x t, 0 < x → x < N → Y < t → u (x + N, t) = u (x, t)) :
    deriv (fun x => u (x, y)) (N / 2 + N) = deriv (fun x => u (x, y)) (N / 2) := by
  have he : (fun x => u (x + N, y)) =ᶠ[𝓝 (N / 2)] fun x => u (x, y) := by
    filter_upwards [Ioo_mem_nhds (by linarith : 0 < N / 2) (by linarith : N / 2 < N)] with x hx
    exact hp x y hx.1 hx.2 hy
  have hd := he.deriv_eq
  exact (deriv_comp_add_const (f := fun x => u (x, y)) (a := N) (x := N / 2)).symm.trans hd

theorem cuspInteriorFourierCoefficient_whittakerODE (N Y : ℝ) (hN : 0 < N) (hY : 0 ≤ Y)
    (n : ℤ) (u : ℝ × ℝ → ℂ) (hu : ContDiffOn ℝ ∞ u (spectralOpenTwoCell N Y))
    (hp : ∀ x t, 0 < x → x < N → Y < t → u (x + N, t) = u (x, t))
    (eig : ℝ)
    (hEq : ∀ p ∈ spectralOpenTwoCell N Y,
      -(p.2 ^ 2) • (spectralPlaneSecond u 0 p + spectralPlaneSecond u 1 p) = (eig : ℂ) * u p)
    (y : ℝ) (hy : Y < y) :
    -(y ^ 2) • (deriv (deriv (cuspInteriorFourierCoefficient N n u)) y -
      ((cuspFourierFrequency N n : ℝ) : ℂ) ^ 2 * cuspInteriorFourierCoefficient N n u y) =
      (eig : ℂ) * cuspInteriorFourierCoefficient N n u y := by
  obtain ⟨G,hG,he⟩ := spectralLocalTwoCell_smooth_extension_uniform N Y y hN hy u hu
  have hrad : |y - y| < (y - Y) / 4 := by simp only [sub_self, abs_zero]; linarith
  let H : ℝ × ℝ → ℂ := fun p => G (p.1 + N / 2, p.2)
  have hH : ContDiff ℝ ∞ H := hG.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)
  have hG0 := he y hrad (N / 2) (by constructor <;> linarith)
  have hGN := he y hrad (N + N / 2) (by constructor <;> linarith)
  have hend : H (N, y) = H (0, y) := by
    change G (N + N / 2, y) = G (0 + N / 2, y)
    rw [hGN.eq_of_nhds, zero_add, hG0.eq_of_nhds]
    simpa only [add_comm] using hp (N / 2) y (by linarith) (by linarith) hy
  have hG0' : deriv (fun x => G (x, y)) (N / 2) = deriv (fun x => u (x, y)) (N / 2) :=
    (hG0.comp_tendsto (continuousAt_id.prodMk continuousAt_const).tendsto).deriv_eq
  have hGN' : deriv (fun x => G (x, y)) (N + N / 2) = deriv (fun x => u (x, y)) (N + N / 2) :=
    (hGN.comp_tendsto (continuousAt_id.prodMk continuousAt_const).tendsto).deriv_eq
  have hdend : deriv (fun x => H (x, y)) N = deriv (fun x => H (x, y)) 0 := by
    change deriv (fun x => G (x + N / 2, y)) N = deriv (fun x => G (x + N / 2, y)) 0
    rw [deriv_comp_add_const (f := fun x => G (x, y)) (a := N / 2) (x := N),
      deriv_comp_add_const (f := fun x => G (x, y)) (a := N / 2) (x := 0),
      zero_add, hG0', hGN']
    simpa only [add_comm] using spectralLocalPeriod_deriv N Y y hN hy u hp
  have hEqH : ∀ x ∈ uIcc (0 : ℝ) N,
      -(y ^ 2) • (spectralPlaneSecond H 0 (x, y) + spectralPlaneSecond H 1 (x, y)) =
        (eig : ℂ) * H (x, y) := by
    intro x hx
    rw [uIcc_of_le hN.le] at hx
    have hxp : x + N / 2 ∈ Icc (N / 2) (3 * N / 2) := by constructor <;> linarith [hx.1, hx.2]
    have hloc := he y hrad (x + N / 2) hxp
    rw [spectralPlaneSecond_shiftX G hG (N / 2) 0 (x, y),
      spectralPlaneSecond_shiftX G hG (N / 2) 1 (x, y),
      spectralPlaneSecond_congr_of_eventuallyEq G u hloc 0,
      spectralPlaneSecond_congr_of_eventuallyEq G u hloc 1]
    change -(y ^ 2) • (spectralPlaneSecond u 0 (x + N / 2, y) +
      spectralPlaneSecond u 1 (x + N / 2, y)) = (eig : ℂ) * G (x + N / 2, y)
    rw [hloc.eq_of_nhds]
    exact hEq (x + N / 2, y) ⟨by linarith [hx.1], by linarith [hx.2], hy⟩
  have hode := cuspFourierMean_laplacian_projection_on_cell N hN n H hH y eig hEqH
  rw [cuspFourierMean_second_horizontal_endpoints N hN n H hH y hend hdend,
    ← cuspHorizontalWeightedMean_second_deriv N (cuspFourierPhase N n)
      (cuspFourierPhase_contDiff N n) H hH y (hY.trans_lt hy)] at hode
  have hcg := cuspInteriorFourierCoefficient_germ (n := n) N Y y hN hy u G he
  rw [← hcg.deriv.deriv_eq, ← hcg.eq_of_nhds]
  unfold cuspInteriorFourierCoefficient
  rw [deriv_const_mul_field', deriv_const_mul_field]
  change -(y ^ 2) • (cuspFourierPhase N n (N / 2) *
      deriv (deriv (cuspHorizontalWeightedMean N (cuspFourierPhase N n) H)) y -
      ((cuspFourierFrequency N n : ℝ) : ℂ) ^ 2 *
        (cuspFourierPhase N n (N / 2) * cuspHorizontalWeightedMean N (cuspFourierPhase N n) H y)) = _
  simp only [Complex.real_smul] at hode ⊢
  linear_combination cuspFourierPhase N n (N / 2) * hode

theorem cuspInteriorFourierCoefficient_normalODE (N Y : ℝ) (hN : 0 < N) (hY : 0 ≤ Y)
    (n : ℤ) (u : ℝ × ℝ → ℂ) (hu : ContDiffOn ℝ ∞ u (spectralOpenTwoCell N Y))
    (hp : ∀ x t, 0 < x → x < N → Y < t → u (x + N, t) = u (x, t))
    (eig : ℝ)
    (hEq : ∀ p ∈ spectralOpenTwoCell N Y,
      -(p.2 ^ 2) • (spectralPlaneSecond u 0 p + spectralPlaneSecond u 1 p) = (eig : ℂ) * u p)
    (y : ℝ) (hy : Y < y) :
    deriv (deriv (cuspInteriorFourierCoefficient N n u)) y =
      (((cuspFourierFrequency N n : ℝ) : ℂ) ^ 2 - (eig : ℂ) / (y : ℂ) ^ 2) *
        cuspInteriorFourierCoefficient N n u y := by
  have h := cuspInteriorFourierCoefficient_whittakerODE N Y hN hY n u hu hp eig hEq y hy
  simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_pow] at h
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hY.trans_lt hy).ne'
  field_simp [hyc]
  linear_combination -h

theorem cuspInteriorFourierCoefficient_deriv_normal_hasDerivAt
    (N Y : ℝ) (hN : 0 < N) (hY : 0 ≤ Y)
    (n : ℤ) (u : ℝ × ℝ → ℂ) (hu : ContDiffOn ℝ ∞ u (spectralOpenTwoCell N Y))
    (hp : ∀ x t, 0 < x → x < N → Y < t → u (x + N, t) = u (x, t))
    (eig : ℝ)
    (hEq : ∀ p ∈ spectralOpenTwoCell N Y,
      -(p.2 ^ 2) • (spectralPlaneSecond u 0 p + spectralPlaneSecond u 1 p) = (eig : ℂ) * u p)
    (y : ℝ) (hy : Y < y) :
    HasDerivAt (deriv (cuspInteriorFourierCoefficient N n u))
      ((((cuspFourierFrequency N n : ℝ) : ℂ) ^ 2 - (eig : ℂ) / (y : ℂ) ^ 2) *
        cuspInteriorFourierCoefficient N n u y) y := by
  have hd := cuspInteriorFourierCoefficient_deriv_hasDerivAt N Y hN hY n u hu y hy
  rw [cuspInteriorFourierCoefficient_normalODE N Y hN hY n u hu hp eig hEq y hy] at hd
  exact hd

end ArtinMatthews
