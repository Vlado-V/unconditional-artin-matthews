module

public import ArtinMatthews.SpectralGamma0EisensteinConstantTerm
public import Mathlib.NumberTheory.LSeries.Dirichlet


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine totient Dirichlet series is a zeta quotient, via its divisor convolution. -/
noncomputable section
open Set
namespace ArtinMatthews

def spectralTotientArithmetic : ArithmeticFunction ℂ := ⟨fun n => (n.totient:ℂ),by simp⟩
def spectralIdentityArithmetic : ArithmeticFunction ℂ := ⟨fun n => (n:ℂ),by simp⟩

theorem spectralTotientArithmetic_zeta_convolution :
    (ArithmeticFunction.zeta:ArithmeticFunction ℂ)*spectralTotientArithmetic = spectralIdentityArithmetic := by
  ext n
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  change (∑ d ∈ n.divisors, (d.totient:ℂ))=(n:ℂ)
  exact_mod_cast Nat.sum_totient n

theorem spectralTotientArithmetic_LSeriesSummable (w : ℂ) (hw : 2<w.re) :
    LSeriesSummable spectralTotientArithmetic w := by
  apply LSeriesSummable_of_le_const_mul_rpow (x := 2) hw
  refine ⟨1,fun n hn => ?_⟩
  change ‖(n.totient:ℂ)‖≤1*(n:ℝ)^((2:ℝ)-1)
  norm_num
  exact_mod_cast Nat.totient_le n

theorem spectralIdentityArithmetic_LSeries (w : ℂ) (hw : 2<w.re) :
    LSeries spectralIdentityArithmetic w = riemannZeta (w-1) := by
  rw [← LSeries_one_eq_riemannZeta (by simp; linarith : 1<(w-1).re)]
  unfold LSeries
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · simp [hn]
  · rw [LSeries.term_of_ne_zero hn,LSeries.term_of_ne_zero hn]
    change (n:ℂ)/(n:ℂ)^w=1/(n:ℂ)^(w-1)
    rw [Complex.cpow_sub _ _ (by exact_mod_cast hn),Complex.cpow_one]
    simp

theorem spectralTotientArithmetic_LSeries (w : ℂ) (hw : 2<w.re) :
    LSeries spectralTotientArithmetic w = riemannZeta (w-1)/riemannZeta w := by
  have hz : 1<w.re := by linarith
  have h := ArithmeticFunction.LSeries_mul'
    (f := (ArithmeticFunction.zeta:ArithmeticFunction ℂ)) (g := spectralTotientArithmetic)
    (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hz) (spectralTotientArithmetic_LSeriesSummable w hw)
  have hzeta : LSeries (ArithmeticFunction.zeta:ArithmeticFunction ℂ) w=riemannZeta w := by
    rw [← LSeries_one_eq_riemannZeta hz]
    apply LSeries_congr
    intro n hn
    simp [ArithmeticFunction.natCoe_apply,ArithmeticFunction.zeta_apply_ne hn]
  rw [spectralTotientArithmetic_zeta_convolution,spectralIdentityArithmetic_LSeries w hw,hzeta] at h
  exact (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hz)).mpr (by simpa only [mul_comm] using h.symm)

theorem spectralEisenstein_positive_tsum (f : ℕ → ℂ) (hf : f 0=0) :
    (∑' c : {c : ℕ // 0<c ∧ 1∣c}, f c.val)=∑' n : ℕ, f n := by
  let e : {c : ℕ // 0<c ∧ 1∣c} ≃ {n : ℕ // n≠0} :=
    { toFun := fun c => ⟨c.val,c.property.1.ne'⟩
      invFun := fun c => ⟨c.val,Nat.pos_of_ne_zero c.property,one_dvd _⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    _ = ∑' n : {n : ℕ // n≠0}, f n.val := e.tsum_eq (fun n => f n.val)
    _ = _ := tsum_subtype_eq_of_support_subset (by
      intro n hn
      exact fun hn0 => hn (by simpa only [hn0] using hf))

theorem gamma0EisensteinTotientSeries_one (s : ℂ) (hs : 1<s.re) :
    gamma0EisensteinTotientSeries 1 s = riemannZeta (2*s-1)/riemannZeta (2*s) := by
  have he : gamma0EisensteinTotientSeries 1 s=LSeries spectralTotientArithmetic (2*s) := by
    unfold gamma0EisensteinTotientSeries
    rw [spectralEisenstein_positive_tsum (fun n => (n.totient:ℂ)*(n:ℂ)^(-2*s)) (by simp)]
    rw [LSeries_def₀ (show spectralTotientArithmetic 0=0 by simp [spectralTotientArithmetic])]
    apply tsum_congr
    intro n
    simp only [spectralTotientArithmetic,show -2*s= -(2*s) by ring,
      Complex.cpow_neg,div_eq_mul_inv]
    rfl
  rw [he,spectralTotientArithmetic_LSeries (2*s) (by simp; linarith)]

end ArtinMatthews
