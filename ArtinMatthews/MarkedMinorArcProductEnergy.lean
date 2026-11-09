module

public import ArtinMatthews.MarkedMinorArcProductFourier


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine finite product-variable Fourier compression. Parseval and Bessel
transport a fiber estimate to counting measure on arbitrary integer supports. -/
namespace ArtinMatthews
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The actual spatial fiber applied to the product Fourier polynomial. -/
noncomputable def markedProductFiberOutput {ι : Type*} [Fintype ι]
    (S : Finset ℤ) (F : AddCircle (1:ℝ) → Matrix ι ι ℂ)
    (c : ι → S → ℂ) (h : ι) (θ : AddCircle (1:ℝ)) : ℂ :=
  (F θ *ᵥ (fun l => markedProductFourierPolynomial S (c l) θ)) h

/-- True L² energy of a matrix fiber, in coordinate form. -/
theorem markedProductFiberOutput_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ℤ) (F : AddCircle (1:ℝ) → Matrix ι ι ℂ)
    (c : ι → S → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ θ, ‖F θ‖ ≤ C) (θ : AddCircle (1:ℝ)) :
    (∑ h, ‖markedProductFiberOutput S F c h θ‖^2) ≤
      C^2*(∑ l, ‖markedProductFourierPolynomial S (c l) θ‖^2) := by
  let x : EuclideanSpace ℂ ι := WithLp.toLp 2
    (fun l => markedProductFourierPolynomial S (c l) θ)
  have hh := Matrix.l2_opNorm_mulVec (F θ) x
  have hb : ‖(EuclideanSpace.equiv ι ℂ).symm (F θ *ᵥ x)‖ ≤ C*‖x‖ :=
    hh.trans (mul_le_mul_of_nonneg_right (hF θ) (norm_nonneg _))
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hC (norm_nonneg x))).mpr hb
  rw [mul_pow,EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq] at hs
  exact hs

set_option maxHeartbeats 1000000 in
/-- Actual Fourier compression preserves a uniform L² fiber bound. Both
product supports can be arbitrary; there is no loss depending on their size. -/
theorem markedProductFiberOutput_fourier_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S B : Finset ℤ) (F : AddCircle (1:ℝ) → Matrix ι ι ℂ)
    (c : ι → S → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hFmeas : ∀ h l, AEStronglyMeasurable (fun θ => F θ h l) AddCircle.haarAddCircle)
    (hF : ∀ θ, ‖F θ‖ ≤ C) :
    (∑ h, ∑ b : B, ‖∫ θ : AddCircle (1:ℝ), fourier (-b.1) θ *
      markedProductFiberOutput S F c h θ ∂AddCircle.haarAddCircle‖^2) ≤
      C^2*(∑ l, ∑ a : S, ‖c l a‖^2) := by
  classical
  let p := fun l => markedProductFourierPolynomial S (c l)
  let g := markedProductFiberOutput S F c
  have hpint (l : ι) : Integrable (fun θ : AddCircle (1:ℝ) => ‖p l θ‖^2)
      AddCircle.haarAddCircle :=
    ((p l).continuous.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hgin (h : ι) : AEStronglyMeasurable (g h) AddCircle.haarAddCircle := by
    change AEStronglyMeasurable (fun θ : AddCircle (1:ℝ) =>
      ∑ l : ι, F θ h l * p l θ) AddCircle.haarAddCircle
    have hh := Finset.aestronglyMeasurable_sum Finset.univ (fun l _ =>
      (hFmeas h l).mul (p l).continuous.aestronglyMeasurable)
    apply hh.congr
    exact Filter.Eventually.of_forall (fun θ => by simp only [Finset.sum_apply,Pi.mul_apply])
  have hd : Integrable (fun θ : AddCircle (1:ℝ) => C^2*∑ l, ‖p l θ‖^2)
      AddCircle.haarAddCircle :=
    (integrable_finsetSum _ (fun l _ => hpint l)).const_mul _
  have hge (θ : AddCircle (1:ℝ)) := markedProductFiberOutput_energy S F c hC hF θ
  have hgint (h : ι) : Integrable (fun θ : AddCircle (1:ℝ) => ‖g h θ‖^2)
      AddCircle.haarAddCircle := by
    apply hd.mono' ((hgin h).norm.pow 2)
    exact Filter.Eventually.of_forall (fun θ => by
      change ‖‖g h θ‖^2‖ ≤ C^2*∑ l, ‖p l θ‖^2
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact (Finset.single_le_sum (fun i _ => sq_nonneg ‖g i θ‖) (Finset.mem_univ h)).trans (hge θ))
  have hgmem (h : ι) : MemLp (g h) 2 AddCircle.haarAddCircle :=
    (memLp_two_iff_integrable_sq_norm (hgin h)).mpr (hgint h)
  calc
    _ ≤ ∑ h, ∫ θ : AddCircle (1:ℝ), ‖g h θ‖^2 ∂AddCircle.haarAddCircle :=
      Finset.sum_le_sum (fun h _ => markedProductFourier_bessel B (hgmem h))
    _ = ∫ θ : AddCircle (1:ℝ), ∑ h, ‖g h θ‖^2 ∂AddCircle.haarAddCircle :=
      (integral_finsetSum _ (fun h _ => hgint h)).symm
    _ ≤ ∫ θ : AddCircle (1:ℝ), C^2*∑ l, ‖p l θ‖^2 ∂AddCircle.haarAddCircle :=
      integral_mono (integrable_finsetSum _ (fun h _ => hgint h)) hd hge
    _ = C^2*(∑ l, ∫ θ : AddCircle (1:ℝ), ‖p l θ‖^2 ∂AddCircle.haarAddCircle) := by
      rw [integral_const_mul,integral_finsetSum _ (fun l _ => hpint l)]
    _ = _ := by simp only [p,markedProductFourierPolynomial_parseval]

end ArtinMatthews
