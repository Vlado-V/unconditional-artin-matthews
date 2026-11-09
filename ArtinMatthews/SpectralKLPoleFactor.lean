module

public import ArtinMatthews.SpectralPoissonApproximation


set_option backward.privateInPublic true
@[expose] public section

/-! Removal of the two Gamma poles at the positive spectral diagonal.
The remaining amplitude is continuous there, with its exact reflection
formula normalization. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

def spectralKLRegularAmplitude (t : ℝ) (p : ℝ × ℝ) : ℂ :=
  (2 : ℂ)^((p.1 : ℂ)-1) *
    Complex.Gamma (((p.1 : ℂ)-(t : ℂ)*Complex.I-(p.2 : ℂ)*Complex.I)/2) *
    Complex.Gamma (((p.1 : ℂ)+(t : ℂ)*Complex.I+(p.2 : ℂ)*Complex.I)/2) *
    Complex.Gamma (1+((p.1 : ℂ)+(t : ℂ)*Complex.I-(p.2 : ℂ)*Complex.I)/2) *
    Complex.Gamma (1+((p.1 : ℂ)-(t : ℂ)*Complex.I+(p.2 : ℂ)*Complex.I)/2) *
    (Complex.Gamma ((p.1 : ℂ)+1))⁻¹

theorem spectralKLRegularAmplitude_factor (t ε v : ℝ) (hε : 0 < ε) :
    spectralKProductClosedValue ((t : ℂ)*Complex.I) ((v : ℂ)*Complex.I) (ε : ℂ) =
      spectralPoissonPeak ε (v-t) • spectralKLRegularAmplitude t (ε,v) := by
  let b : ℂ := ((ε : ℂ)+(t : ℂ)*Complex.I-(v : ℂ)*Complex.I)/2
  let c : ℂ := ((ε : ℂ)-(t : ℂ)*Complex.I+(v : ℂ)*Complex.I)/2
  have hb : b ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [b] at this
    linarith
  have hc : c ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [c] at this
    linarith
  have hD : ((ε : ℂ)^2+((v : ℂ)-(t : ℂ))^2) ≠ 0 := by
    have h : ε^2+(v-t)^2 > 0 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hε) (sq_nonneg _)
    exact_mod_cast h.ne'
  have hbc : b*c = ((ε : ℂ)^2+((v : ℂ)-(t : ℂ))^2)/4 := by
    dsimp [b,c]
    ring_nf
    simp [Complex.I_sq]
    ring
  have hp : (2 : ℂ)^((ε : ℂ)-1) = (2 : ℂ)^((ε : ℂ)-3)*4 := by
    have he : (ε : ℂ)-1 = ((ε : ℂ)-3)+2 := by ring
    rw [he, Complex.cpow_add _ _ (by norm_num)]
    norm_num
  have hgb := Complex.Gamma_add_one b hb
  have hgc := Complex.Gamma_add_one c hc
  rw [show b+1 = 1+b by ring] at hgb
  rw [show c+1 = 1+c by ring] at hgc
  unfold spectralKProductClosedValue spectralKLRegularAmplitude spectralPoissonPeak
  rw [div_eq_mul_inv, Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one, hp]
  change _ = (↑(ε / (ε^2+(v-t)^2)) : ℂ) *
    (_ * _ * _ * Complex.Gamma (1+b) * Complex.Gamma (1+c) * _)
  rw [hgb,hgc]
  push_cast
  let a : ℂ := ((ε : ℂ)-(t : ℂ)*Complex.I-(v : ℂ)*Complex.I)/2
  let d : ℂ := ((ε : ℂ)+(t : ℂ)*Complex.I+(v : ℂ)*Complex.I)/2
  let P : ℂ := (2 : ℂ)^((ε : ℂ)-3)
  let R : ℂ := (Complex.Gamma ((ε : ℂ)+1))⁻¹
  change P*Complex.Gamma a*Complex.Gamma b*Complex.Gamma c*Complex.Gamma d*((ε : ℂ)*R) =
    (ε : ℂ)/((ε : ℂ)^2+((v : ℂ)-(t : ℂ))^2)*
      (P*4*Complex.Gamma a*Complex.Gamma d*(b*Complex.Gamma b)*(c*Complex.Gamma c)*R)
  calc
    _ = (ε : ℂ)*(P*Complex.Gamma a*Complex.Gamma d*(Complex.Gamma b*Complex.Gamma c)*R) := by ring
    _ = (ε : ℂ)/((ε : ℂ)^2+((v : ℂ)-(t : ℂ))^2)*
        (P*4*Complex.Gamma a*Complex.Gamma d*(b*c)*(Complex.Gamma b*Complex.Gamma c)*R) := by
      rw [hbc]
      field_simp
    _ = _ := by ring

theorem spectral_Gamma_continuousAt_nonneg_re {z : ℂ} (hz : 0 ≤ z.re)
    (hn : z ≠ 0) : ContinuousAt Complex.Gamma z := by
  apply Complex.continuousAt_Gamma z
  intro m hm
  have hr := congrArg Complex.re hm
  simp only [Complex.neg_re,Complex.natCast_re] at hr
  have hm0 : m = 0 := by
    have : (m : ℝ) ≤ 0 := by linarith
    exact_mod_cast le_antisymm this (Nat.cast_nonneg m)
  apply hn
  simpa only [hm0,Nat.cast_zero,neg_zero] using hm

theorem spectralKLRegularAmplitude_continuousAt (t ε v : ℝ) (hε : 0 ≤ ε)
    (hn : 0 < ε ∨ t+v ≠ 0) : ContinuousAt (spectralKLRegularAmplitude t) (ε,v) := by
  have hsum (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
      ContinuousAt (fun p : ℝ × ℝ =>
        Complex.Gamma (((p.1 : ℂ)+(σ : ℂ)*((t : ℂ)*Complex.I+(p.2 : ℂ)*Complex.I))/2)) (ε,v) := by
    apply ContinuousAt.comp (g := Complex.Gamma)
    · apply spectral_Gamma_continuousAt_nonneg_re
      · rcases hσ with rfl | rfl <;> simp <;> positivity
      · intro h
        rcases hn with he | hv
        · have hr := congrArg Complex.re h
          rcases hσ with rfl | rfl <;> simp at hr <;> linarith
        · have hi := congrArg Complex.im h
          rcases hσ with rfl | rfl <;> simp at hi <;> apply hv <;> linarith
    · fun_prop
  have hm := hsum (-1) (Or.inr rfl)
  have hp := hsum 1 (Or.inl rfl)
  have hm' : ContinuousAt (fun p : ℝ × ℝ =>
      Complex.Gamma (((p.1 : ℂ)-(t : ℂ)*Complex.I-(p.2 : ℂ)*Complex.I)/2)) (ε,v) := by
    convert hm using 1
    funext p
    congr 1
    push_cast
    ring
  have hp' : ContinuousAt (fun p : ℝ × ℝ =>
      Complex.Gamma (((p.1 : ℂ)+(t : ℂ)*Complex.I+(p.2 : ℂ)*Complex.I)/2)) (ε,v) := by
    convert hp using 1
    funext p
    congr 1
    push_cast
    ring
  have hshift (σ : ℝ) : ContinuousAt (fun p : ℝ × ℝ =>
      Complex.Gamma (1+((p.1 : ℂ)+(σ : ℂ)*((t : ℂ)*Complex.I-(p.2 : ℂ)*Complex.I))/2)) (ε,v) := by
    apply ContinuousAt.comp (g := Complex.Gamma)
    · apply spectral_Gamma_continuousAt_nonneg_re
      · simp
        positivity
      · intro h
        have hr := congrArg Complex.re h
        simp at hr
        linarith
    · fun_prop
  have hs1 := hshift 1
  have hs2 := hshift (-1)
  have hs1' : ContinuousAt (fun p : ℝ × ℝ =>
      Complex.Gamma (1+((p.1 : ℂ)+(t : ℂ)*Complex.I-(p.2 : ℂ)*Complex.I)/2)) (ε,v) := by
    convert hs1 using 1
    funext p
    congr 1
    push_cast
    ring
  have hs2' : ContinuousAt (fun p : ℝ × ℝ =>
      Complex.Gamma (1+((p.1 : ℂ)-(t : ℂ)*Complex.I+(p.2 : ℂ)*Complex.I)/2)) (ε,v) := by
    convert hs2 using 1
    funext p
    congr 1
    push_cast
    ring
  have hpow : ContinuousAt (fun p : ℝ × ℝ => (2 : ℂ)^((p.1 : ℂ)-1)) (ε,v) := by
    exact (by fun_prop : ContinuousAt (fun p : ℝ × ℝ => (p.1 : ℂ)-1) (ε,v)).const_cpow
      (Or.inl (by norm_num))
  have hi : ContinuousAt (fun p : ℝ × ℝ => (Complex.Gamma ((p.1 : ℂ)+1))⁻¹) (ε,v) := by
    exact Complex.differentiable_one_div_Gamma.continuous.continuousAt.comp (by fun_prop)
  exact (((((hpow.mul hm').mul hp').mul hs1').mul hs2').mul hi)

theorem spectral_Gamma_imaginary_product (t : ℝ) (ht : 0 < t) :
    Complex.Gamma ((t : ℂ)*Complex.I)*Complex.Gamma (-(t : ℂ)*Complex.I) =
      (Real.pi / (t*Real.sinh (Real.pi*t)) : ℝ) := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have htn : -(t : ℂ)*Complex.I ≠ 0 := mul_ne_zero (neg_ne_zero.mpr ht0) Complex.I_ne_zero
  have hs : (Real.sinh (Real.pi*t) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht)))
  have hg := Complex.Gamma_mul_Gamma_one_sub ((t : ℂ)*Complex.I)
  have hr := Complex.Gamma_add_one (-(t : ℂ)*Complex.I) htn
  rw [show -(t : ℂ)*Complex.I+1 = 1-(t : ℂ)*Complex.I by ring] at hr
  rw [hr,show (Real.pi : ℂ)*((t : ℂ)*Complex.I) = ((Real.pi*t : ℝ) : ℂ)*Complex.I by push_cast; ring,
    Complex.sin_mul_I, ← Complex.ofReal_sinh] at hg
  have hg' := (eq_div_iff (mul_ne_zero hs Complex.I_ne_zero)).mp hg
  push_cast only [Complex.ofReal_div,Complex.ofReal_mul]
  change Complex.Gamma ((t : ℂ)*Complex.I)*Complex.Gamma (-(t : ℂ)*Complex.I) =
    (Real.pi : ℂ)/((t : ℂ)*(Real.sinh (Real.pi*t) : ℂ))
  apply (eq_div_iff (mul_ne_zero ht0 hs)).mpr
  calc
    _ = (Complex.Gamma ((t : ℂ)*Complex.I)*
        ((-(t : ℂ)*Complex.I)*Complex.Gamma (-(t : ℂ)*Complex.I)))*
        ((Real.sinh (Real.pi*t) : ℂ)*Complex.I) := by
      ring_nf
      simp [Complex.I_sq]
    _ = _ := hg'

theorem spectralKLRegularAmplitude_diagonal (t : ℝ) (ht : 0 < t) :
    spectralKLRegularAmplitude t (0,t) = (Real.pi / (2*t*Real.sinh (Real.pi*t)) : ℝ) := by
  have hminus : ((0 : ℂ)-(t : ℂ)*Complex.I-(t : ℂ)*Complex.I)/2 = -(t : ℂ)*Complex.I := by ring
  have hplus : ((0 : ℂ)+(t : ℂ)*Complex.I+(t : ℂ)*Complex.I)/2 = (t : ℂ)*Complex.I := by ring
  have hdiff1 : ((0 : ℂ)+(t : ℂ)*Complex.I-(t : ℂ)*Complex.I)/2 = 0 := by ring
  have hdiff2 : ((0 : ℂ)-(t : ℂ)*Complex.I+(t : ℂ)*Complex.I)/2 = 0 := by ring
  unfold spectralKLRegularAmplitude
  rw [Complex.ofReal_zero,hminus,hplus,hdiff1,hdiff2]
  simp only [add_zero,zero_add,Complex.Gamma_one,inv_one,mul_one,zero_sub,Complex.cpow_neg_one]
  rw [show (2 : ℂ)⁻¹*Complex.Gamma (-↑t*Complex.I)*Complex.Gamma (↑t*Complex.I) =
    (2 : ℂ)⁻¹*(Complex.Gamma (↑t*Complex.I)*Complex.Gamma (-↑t*Complex.I)) by ring,
    spectral_Gamma_imaginary_product t ht]
  push_cast only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat]
  ring

end ArtinMatthews
