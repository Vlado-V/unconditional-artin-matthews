module

public import OAI.NumberTheory.EgyptianFractions.VaughanBilinear


set_option backward.privateInPublic true
@[expose] public section

/-! Finite weighted character frames. Their operator bound is derived
from the Gram row sums with the original weights retained. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {Ω C : Type*} [Fintype Ω] [Fintype C]

def idealFrameEnergy (μ : Ω → ℝ) (f : Ω → ℂ) : ℝ :=
  ∑ x, μ x * ‖f x‖^2

def idealFrameGram (μ : Ω → ℝ) (φ : C → Ω → ℂ) (c d : C) : ℂ :=
  ∑ x, (μ x : ℂ) * φ c x * star (φ d x)

def idealFrameCoefficient (μ : Ω → ℝ) (φ : C → Ω → ℂ) (f : Ω → ℂ) (c : C) : ℂ :=
  ∑ x, (μ x : ℂ) * star (φ c x) * f x

def idealFrameSynthesis (φ : C → Ω → ℂ) (a : C → ℂ) (x : Ω) : ℂ :=
  ∑ c, a c * φ c x

theorem idealFrameEnergy_nonneg (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (f : Ω → ℂ) :
    0 ≤ idealFrameEnergy μ f :=
  sum_nonneg fun x _ => mul_nonneg (hμ x) (sq_nonneg _)

omit [Fintype C] in
theorem idealFrameGram_norm_symm (μ : Ω → ℝ) (φ : C → Ω → ℂ) (c d : C) :
    ‖idealFrameGram μ φ c d‖ = ‖idealFrameGram μ φ d c‖ := by
  have he : star (idealFrameGram μ φ c d) = idealFrameGram μ φ d c := by
    simp only [idealFrameGram, star_sum, star_mul, Complex.star_def,
      Complex.conj_ofReal, Complex.conj_conj]
    apply sum_congr rfl
    intro x _
    ring
  rw [← he, norm_star]

theorem idealFrameSynthesis_energy_le (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (φ : C → Ω → ℂ) (B : ℝ)
    (hrow : ∀ c, (∑ d, ‖idealFrameGram μ φ c d‖) ≤ B) (a : C → ℂ) :
    idealFrameEnergy μ (idealFrameSynthesis φ a) ≤ B * ∑ c, ‖a c‖^2 := by
  let z : Ω → C → ℂ := fun x c => (Real.sqrt (μ x) : ℂ) * φ c x
  have hz (c d : C) :
      (∑ x, z x c * (starRingEnd ℂ) (z x d)) = idealFrameGram μ φ c d := by
    apply sum_congr rfl
    intro x _
    dsimp only [z]
    rw [map_mul, Complex.conj_ofReal]
    change (Real.sqrt (μ x) : ℂ) * φ c x *
        ((Real.sqrt (μ x) : ℂ) * star (φ d x)) = _
    calc
      _ = ((Real.sqrt (μ x) * Real.sqrt (μ x) : ℝ) : ℂ) * φ c x * star (φ d x) := by
        push_cast
        ring
      _ = _ := by rw [Real.mul_self_sqrt (hμ x)]
  have he : (∑ x, ‖∑ c, a c * z x c‖^2) =
      idealFrameEnergy μ (idealFrameSynthesis φ a) := by
    apply sum_congr rfl
    intro x _
    have hs : (∑ c, a c * z x c) =
        (Real.sqrt (μ x) : ℂ) * idealFrameSynthesis φ a x := by
      rw [idealFrameSynthesis, mul_sum]
      apply sum_congr rfl
      intro c _
      dsimp only [z]
      ring
    rw [hs, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hμ x)]
  have hb := OAI.Problem337.VaughanBilinear.energy_le_correlations univ univ a z
  simp_rw [hz] at hb
  rw [he] at hb
  have hs := OAI.Problem337.VaughanBilinear.symmetric_weighted_sum_le univ
    (fun c => ‖a c‖) (fun c d => ‖idealFrameGram μ φ c d‖)
    (fun _ _ _ _ => norm_nonneg _)
    (fun c _ d _ => idealFrameGram_norm_symm μ φ c d)
  refine hb.trans (hs.trans ?_)
  rw [mul_sum]
  apply sum_le_sum
  intro c _
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hrow c) (sq_nonneg ‖a c‖)

theorem idealFrame_weighted_cauchy (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (f g : Ω → ℂ) :
    ‖∑ x, (μ x : ℂ) * star (f x) * g x‖^2 ≤
      idealFrameEnergy μ f * idealFrameEnergy μ g := by
  have hn : ‖∑ x, (μ x : ℂ) * star (f x) * g x‖ ≤
      ∑ x, μ x * ‖f x‖ * ‖g x‖ := by
    refine (norm_sum_le _ _).trans_eq ?_
    apply sum_congr rfl
    intro x _
    rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hμ x)]
  have hc := sum_sq_le_sum_mul_sum_of_sq_le_mul univ
    (fun x _ => mul_nonneg (hμ x) (sq_nonneg ‖f x‖))
    (fun x _ => mul_nonneg (hμ x) (sq_nonneg ‖g x‖))
    (fun x _ => show (μ x * ‖f x‖ * ‖g x‖)^2 ≤
      (μ x * ‖f x‖^2) * (μ x * ‖g x‖^2) by nlinarith)
  refine (sq_le_sq₀ (norm_nonneg _) (sum_nonneg fun x _ =>
    mul_nonneg (mul_nonneg (hμ x) (norm_nonneg _)) (norm_nonneg _))).mpr hn |>.trans hc

end
end ArtinMatthews
