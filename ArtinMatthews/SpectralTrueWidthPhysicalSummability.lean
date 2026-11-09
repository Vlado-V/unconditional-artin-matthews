module

public import ArtinMatthews.SpectralWeylPowerNorm
public import ArtinMatthews.SpectralTrueWidthLinearCount
public import Mathlib.Analysis.PSeries


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute summability of the actual true-width Kloosterman fibres with
one power-decaying physical profile. All widths and frequencies remain
in the literal normalized modulus. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

def gamma0TrueWidthPhysicalFibre (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (c : Ioi (0 : ℕ)) (m n : ℤ) (f g : ℝ → ℂ) : ℂ :=
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  let a := |cuspFourierFrequency 1 m|
  let b := |cuspFourierFrequency 1 n|
  let C := gamma0TrueWidthModulus N r s (c.val : ℝ)
  gamma0TrueWidthKloostermanSum N r s c.val m n * ((Real.sqrt (a*b)/C^2 : ℝ) : ℂ) *
    spectralWeylPhysicalBilinear (cuspFourierFrequency 1 m/a) (cuspFourierFrequency 1 n/b)
      f g (Real.sqrt (a*b)*(2/C))

theorem spectralWeyl_modulus_power_factor {c K W : ℝ}
    (hc : 0 < c) (hK : 0 < K) (hW : 0 < W) (B D : ℝ) :
    W^2*c*(K/(c*W)^2)*(D*(K*(2/(c*W)))^(2*B-1)) =
      (K*D*(2*K/W)^(2*B-1))/c^(2*B) := by
  have he : K*(2/(c*W)) = (2*K/W)/c := by field_simp
  rw [he,Real.div_rpow (by positivity) hc.le,Real.rpow_sub_one hc.ne']
  field_simp

theorem gamma0TrueWidthPhysicalFibre_uniform_bound (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    {B M : ℝ} (hB : 0 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (g : ℝ → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ f : ℝ → ℂ, Measurable f →
      (∀ z, 0 < z → ‖f z‖ ≤ M*z^B) → ∀ c : Ioi (0 : ℕ),
      ‖gamma0TrueWidthPhysicalFibre N r s c m n f g‖ ≤ L/(c.val : ℝ)^(2*B) := by
  obtain ⟨D,hD,hbound⟩ := spectralWeylPhysicalBilinear_uniform_power_bound hB hB₁ hM g hg hgc hgp
  let a := |cuspFourierFrequency 1 m|
  let b := |cuspFourierFrequency 1 n|
  let K := Real.sqrt (a*b)
  let W := Real.sqrt (gamma0CuspTrueWidth N r : ℝ)*Real.sqrt (gamma0CuspTrueWidth N s : ℝ)
  have ha : 0 < a := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one m hm)
  have hb : 0 < b := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)
  have hK : 0 < K := Real.sqrt_pos.mpr (mul_pos ha hb)
  have hr : 0 < (gamma0CuspTrueWidth N r : ℝ) := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hs : 0 < (gamma0CuspTrueWidth N s : ℝ) := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N s)
  have hW : 0 < W := mul_pos (Real.sqrt_pos.mpr hr) (Real.sqrt_pos.mpr hs)
  have hWsq : W^2 = (gamma0CuspTrueWidth N r : ℝ)*gamma0CuspTrueWidth N s := by
    dsimp only [W]
    rw [mul_pow,Real.sq_sqrt hr.le,Real.sq_sqrt hs.le]
  refine ⟨K*D*(2*K/W)^(2*B-1),by positivity,?_⟩
  intro f hfm hf c
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  have hc : 0 < (c.val : ℝ) := Nat.cast_pos.mpr c.property
  have hC : 0 < (c.val : ℝ)*W := mul_pos hc hW
  have hS : ‖gamma0TrueWidthKloostermanSum N r s c.val m n‖ ≤ W^2*(c.val : ℝ) := by
    rw [hWsq]
    exact gamma0TrueWidthKloostermanSum_linear_bound N r s c.val m n
  have hF := hbound (K*(2/((c.val : ℝ)*W))) (mul_pos hK (div_pos two_pos hC))
    (cuspFourierFrequency 1 m/a) (cuspFourierFrequency 1 n/b) f hfm hf
  have hmod : gamma0TrueWidthModulus N r s (c.val : ℝ) = (c.val : ℝ)*W := by
    dsimp only [gamma0TrueWidthModulus,W]
    ring
  change ‖gamma0TrueWidthKloostermanSum N r s c.val m n * ((K/(gamma0TrueWidthModulus N r s (c.val : ℝ))^2 : ℝ) : ℂ) *
    spectralWeylPhysicalBilinear (cuspFourierFrequency 1 m/a) (cuspFourierFrequency 1 n/b)
      f g (K*(2/gamma0TrueWidthModulus N r s (c.val : ℝ)))‖ ≤ _
  rw [hmod,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (W^2*(c.val : ℝ))*(K/((c.val : ℝ)*W)^2)*
        (D*(K*(2/((c.val : ℝ)*W)))^(2*B-1)) := by gcongr
    _ = _ := spectralWeyl_modulus_power_factor hc hK hW B D

theorem gamma0TrueWidthPhysicalFibre_summable (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    {B M : ℝ} (hB : 1/2 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (f g : ℝ → ℂ) (hfm : Measurable f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ))
    (hf : ∀ z, 0 < z → ‖f z‖ ≤ M*z^B) :
    Summable (fun c : Ioi (0 : ℕ) => gamma0TrueWidthPhysicalFibre N r s c m n f g) := by
  obtain ⟨L,_,hL⟩ := gamma0TrueWidthPhysicalFibre_uniform_bound N r s m n hm hn (by linarith) hB₁ hM g hg hgc hgp
  have hp : Summable (fun c : ℕ => 1/(c : ℝ)^(2*B)) := Real.summable_one_div_nat_rpow.mpr (by linarith)
  have hs := (hp.mul_left L).subtype (fun c : ℕ => 0 < c)
  apply hs.of_norm_bounded
  intro c
  simpa only [mul_one_div,Function.comp_def] using hL f hfm hf c

end ArtinMatthews
