module

public import ArtinMatthews.SpectralKAdjacentOrderMoment
public import ArtinMatthews.SpectralKSquareMomentRecurrence


set_option backward.privateInPublic true
@[expose] public section

/-! Exact weighted square moments of the genuine K kernel on a vertical
order line. Conjugation and the four-Gamma Mellin identity retain the
real order shift throughout. -/

noncomputable section
open Set MeasureTheory
open OAI.CubicEisenstein
open scoped ComplexConjugate

namespace ArtinMatthews

def spectralKShiftedMoment (k : ℕ) (δ t : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ),x^(2*k)*‖schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I) x‖^2

theorem spectralKShiftedMoment_integrand (k : ℕ) (δ t x : ℝ) (hx : 0 < x) :
    (x : ℂ)^((2*(k : ℂ)+1)-1)*
        schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I) x*
        schlafliBesselK ((δ : ℂ)-(t : ℂ)*Complex.I) x =
      ((x^(2*k)*‖schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I) x‖^2 : ℝ) : ℂ) := by
  have hc : star ((δ : ℂ)+(t : ℂ)*Complex.I) = (δ : ℂ)-(t : ℂ)*Complex.I := by
    change conj ((δ : ℂ)+(t : ℂ)*Complex.I) = _
    simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I,mul_neg,sub_eq_add_neg]
  rw [show (2*(k : ℂ)+1)-1 = ((2*k : ℕ) : ℂ) by push_cast;ring,
    Complex.cpow_natCast,← hc,← schlafliBesselK_star_order _ hx,mul_assoc]
  have he (z : ℂ) : z*star z = ((‖z‖^2 : ℝ) : ℂ) := by
    rw [mul_comm]
    change conj z*z = _
    rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  rw [he]
  push_cast
  rfl

theorem spectralKShiftedMoment_integrable (k : ℕ) (δ t : ℝ)
    (hδ : |δ| < (k : ℝ)+1/2) :
    IntegrableOn (fun x : ℝ => x^(2*k)*‖schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I) x‖^2) (Ioi 0) := by
  have h : |((δ : ℂ)+(t : ℂ)*Complex.I).re|+|((δ : ℂ)-(t : ℂ)*Complex.I).re| <
      (2*(k : ℂ)+1).re := by
    simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,
      Complex.natCast_re,Complex.one_re]
    norm_num
    linarith
  have hi := (schlafliBesselK_product_mellin_integrable_of_re_gt
    ((δ : ℂ)+(t : ℂ)*Complex.I) ((δ : ℂ)-(t : ℂ)*Complex.I) (2*(k : ℂ)+1) h).re
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [spectralKShiftedMoment_integrand k δ t x hx]
  rfl

theorem spectralKShiftedMoment_closed (k : ℕ) (δ t : ℝ)
    (hδ : |δ| < (k : ℝ)+1/2) :
    let a : ℂ := (k : ℂ)+1/2
    let s : ℂ := 2*(k : ℂ)+1
    (spectralKShiftedMoment k δ t : ℂ) =
      (2 : ℂ)^(s-3)*Complex.Gamma (a-δ)*Complex.Gamma (a-(t : ℂ)*Complex.I)*
        Complex.Gamma (a+(t : ℂ)*Complex.I)*Complex.Gamma (a+δ)/Complex.Gamma s := by
  dsimp only
  let a : ℂ := (k : ℂ)+1/2
  let s : ℂ := 2*(k : ℂ)+1
  let ν : ℂ := (δ : ℂ)+(t : ℂ)*Complex.I
  let μ : ℂ := (δ : ℂ)-(t : ℂ)*Complex.I
  have h : |ν.re|+|μ.re| < s.re := by
    dsimp only [ν,μ,s]
    norm_num [Complex.add_re,Complex.sub_re,Complex.mul_re]
    linarith
  have hI : (spectralKShiftedMoment k δ t : ℂ) =
      ∫ x in Ioi (0 : ℝ),(x : ℂ)^(s-1)*schlafliBesselK ν x*schlafliBesselK μ x := by
    unfold spectralKShiftedMoment
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact (spectralKShiftedMoment_integrand k δ t x hx).symm
  rw [hI,schlafliBesselK_product_mellin_closed ν μ s h]
  rw [show (s-ν-μ)/2 = a-δ by dsimp only [s,ν,μ,a];ring,
    show (s+ν-μ)/2 = a+(t : ℂ)*Complex.I by dsimp only [s,ν,μ,a];ring,
    show (s-ν+μ)/2 = a-(t : ℂ)*Complex.I by dsimp only [s,ν,μ,a];ring,
    show (s+ν+μ)/2 = a+δ by dsimp only [s,ν,μ,a];ring]
  ring

end ArtinMatthews
