module

public import ArtinMatthews.ShiftedABLMellinKernels
public import ArtinMatthews.ShiftedABLDualFrequency
public import ArtinMatthews.ShiftedABLThetaSourceDecay
public import Mathlib.MeasureTheory.Integral.Prod


set_option backward.privateInPublic true
@[expose] public section

/-! The literal congruence-constrained coefficient is separated from the
modulus by a finite sum and an absolutely integrable product integral. -/

noncomputable section
open Complex MeasureTheory Set OAI
open scoped ContDiff BigOperators

namespace ArtinMatthews

private theorem shiftedConvolutionCoeff_product_integral
    (S T : Finset ℕ) (m3 m4 D : ℕ) (a b : ℕ → ℝ → ℂ) (ρ : ℤ)
    (ha : ∀ k ∈ S, Integrable (a k)) (hb : ∀ k ∈ T, Integrable (b k)) :
    let f (z : ℝ × ℝ) := shiftedConvolutionCoeff S T m3 m4 D
      (fun k => a k z.1) (fun k => b k z.2) ρ
    Integrable f ∧
      shiftedConvolutionCoeff S T m3 m4 D (fun k => ∫ t, a k t) (fun k => ∫ t, b k t) ρ =
        ∫ z : ℝ × ℝ, f z := by
  intro f
  classical
  let P (k1 k2 : ℕ) : Prop := (m4 : ℤ)*k2-(m3 : ℤ)*k1 = ρ ∧
    (m3^2*k1 : ZMod D) = (m4^2*k2 : ZMod D)
  let u (k1 k2 : ℕ) (z : ℝ × ℝ) : ℂ := if P k1 k2 then a k1 z.1*b k2 z.2 else 0
  have hu (k1 : ℕ) (h1 : k1 ∈ S) (k2 : ℕ) (h2 : k2 ∈ T) : Integrable (u k1 k2) := by
    by_cases h : P k1 k2
    · simp only [u,h,ite_true,Measure.volume_eq_prod]
      exact (ha k1 h1).mul_prod (hb k2 h2)
    · simp [u,h]
  change Integrable (fun z : ℝ × ℝ => ∑ k1 ∈ S, ∑ k2 ∈ T, u k1 k2 z) ∧ _
  refine ⟨integrable_finsetSum S (fun k1 h1 =>
    integrable_finsetSum T (fun k2 h2 => hu k1 h1 k2 h2)), ?_⟩
  change (∑ k1 ∈ S, ∑ k2 ∈ T, if P k1 k2 then (∫ t, a k1 t)*(∫ t, b k2 t) else 0) =
    ∫ z : ℝ × ℝ, ∑ k1 ∈ S, ∑ k2 ∈ T, u k1 k2 z
  rw [integral_finsetSum S (fun k1 h1 => integrable_finsetSum T (fun k2 h2 => hu k1 h1 k2 h2))]
  apply Finset.sum_congr rfl
  intro k1 h1
  rw [integral_finsetSum T (fun k2 h2 => hu k1 h1 k2 h2)]
  apply Finset.sum_congr rfl
  intro k2 h2
  by_cases h : P k1 k2
  · simp only [u,h,ite_true,Measure.volume_eq_prod,integral_prod_mul]
  · simp [u,h]

/-- After log separation, the same original congruence coefficient has
no modulus dependence. -/
def shiftedABLMellinRhoCoefficient (χ : SevenEighths.HeckeFamily.Character)
    (D m3 m4 : ℕ) (d : ℕ × ℕ) (ρ : ℤ) (z : ℝ × ℝ) : ℂ :=
  shiftedConvolutionCoeff (shiftedABLDualWindow d.1) (shiftedABLDualWindow d.2) m3 m4 D
    (fun k => idealThetaCoeff χ k * shiftedABLMellinDualPhase d.1 k z.1)
    (fun k => idealThetaCoeff χ k * shiftedABLMellinDualPhase d.2 k z.2) ρ

/-- The two actual Schwartz kernels and their common modulus phases. -/
def shiftedABLMellinKernelFactor (Q q : ℝ) (b1 b2 : SchwartzMap ℝ ℂ)
    (z : ℝ × ℝ) : ℂ :=
  shiftedABLMellinCirclePhase Q z.1 q * shiftedABLMellinCirclePhase Q z.2 q *
    (b1 z.1*b2 z.2)

private theorem shiftedABLMellin_one_integrable
    (χ : SevenEighths.HeckeFamily.Character) (j k : ℕ) (Q q : ℝ) (b : SchwartzMap ℝ ℂ) :
    Integrable (fun t : ℝ => idealThetaCoeff χ k * shiftedABLMellinDualPhase j k t *
      shiftedABLMellinCirclePhase Q t q * b t) := by
  let C := ‖idealThetaCoeff χ k‖ * ‖(spectralDyadicBlock j k : ℂ)‖
  apply (b.integrable.norm.const_mul C).mono'
  · apply Continuous.aestronglyMeasurable
    unfold shiftedABLMellinDualPhase shiftedABLMellinCirclePhase FourierBridge.logPhase
    fun_prop
  · filter_upwards [] with t
    simp only [norm_mul,shiftedABLMellinDualPhase,shiftedABLMellinCirclePhase,
      norm_shifted_logPhase,mul_one,C]
    exact le_rfl

/-- Exact interchange at one modulus for the actual original coefficient,
with product-measure integrability derived from the two Schwartz kernels. -/
theorem shiftedABLThetaRhoCoefficient_eq_mellin
    (χ : SevenEighths.HeckeFamily.Character) (W1 W2 : SchwartzMap ℝ ℂ)
    (K1 K2 Q : ℝ) (D m3 m4 q : ℕ) (d : ℕ × ℕ) (ρ : ℤ)
    (b1 b2 : SchwartzMap ℝ ℂ)
    (h1 : ∀ k ∈ shiftedABLDualWindow d.1,
      (spectralDyadicBlock d.1 k : ℂ) *
        weightOneBesselTransform (fun x => W1 (x/K1)) ((k : ℝ)/(q : ℝ)^2) =
          ∫ t : ℝ, shiftedABLMellinDualPhase d.1 k t *
            shiftedABLMellinCirclePhase Q t q * b1 t)
    (h2 : ∀ k ∈ shiftedABLDualWindow d.2,
      (spectralDyadicBlock d.2 k : ℂ) *
        weightOneBesselTransform (fun x => W2 (x/K2)) ((k : ℝ)/(q : ℝ)^2) =
          ∫ t : ℝ, shiftedABLMellinDualPhase d.2 k t *
            shiftedABLMellinCirclePhase Q t q * b2 t) :
    Integrable (fun z : ℝ × ℝ => shiftedABLMellinRhoCoefficient χ D m3 m4 d ρ z *
      shiftedABLMellinKernelFactor Q q b1 b2 z) ∧
      shiftedABLThetaRhoCoefficient χ W1 W2 K1 K2 D m3 m4 q d ρ =
        ∫ z : ℝ × ℝ, shiftedABLMellinRhoCoefficient χ D m3 m4 d ρ z *
          shiftedABLMellinKernelFactor Q q b1 b2 z := by
  let S := shiftedABLDualWindow d.1
  let T := shiftedABLDualWindow d.2
  let a (k : ℕ) (t : ℝ) := idealThetaCoeff χ k * shiftedABLMellinDualPhase d.1 k t *
    shiftedABLMellinCirclePhase Q t q * b1 t
  let b (k : ℕ) (t : ℝ) := idealThetaCoeff χ k * shiftedABLMellinDualPhase d.2 k t *
    shiftedABLMellinCirclePhase Q t q * b2 t
  let f (z : ℝ × ℝ) := shiftedConvolutionCoeff S T m3 m4 D
    (fun k => a k z.1) (fun k => b k z.2) ρ
  obtain ⟨hf,heq⟩ := shiftedConvolutionCoeff_product_integral S T m3 m4 D a b ρ
    (fun k _ => shiftedABLMellin_one_integrable χ d.1 k Q q b1)
    (fun k _ => shiftedABLMellin_one_integrable χ d.2 k Q q b2)
  have hf_eq : f = (fun z => shiftedABLMellinRhoCoefficient χ D m3 m4 d ρ z *
      shiftedABLMellinKernelFactor Q q b1 b2 z) := by
    funext z
    unfold f shiftedABLMellinRhoCoefficient shiftedConvolutionCoeff
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k1 _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k2 _
    split_ifs <;> simp only [a,b,shiftedABLMellinKernelFactor,zero_mul] <;> ring
  refine ⟨hf_eq ▸ hf, ?_⟩
  rw [← hf_eq, ← heq]
  unfold shiftedABLThetaRhoCoefficient shiftedConvolutionCoeff
  apply Finset.sum_congr rfl
  intro k1 hk1
  apply Finset.sum_congr rfl
  intro k2 hk2
  have ha' : thetaBesselCoeff χ W1 K1 ((q : ℝ)^2) k1 * (spectralDyadicBlock d.1 k1 : ℂ) =
      ∫ t : ℝ, a k1 t := by
    calc
      _ = idealThetaCoeff χ k1 * ((spectralDyadicBlock d.1 k1 : ℂ) *
          weightOneBesselTransform (fun x => W1 (x/K1)) ((k1 : ℝ)/(q : ℝ)^2)) := by
        unfold thetaBesselCoeff
        ring
      _ = _ := by
        rw [h1 k1 hk1, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with t
        dsimp [a]
        ring
  have hb' : thetaBesselCoeff χ W2 K2 ((q : ℝ)^2) k2 * (spectralDyadicBlock d.2 k2 : ℂ) =
      ∫ t : ℝ, b k2 t := by
    calc
      _ = idealThetaCoeff χ k2 * ((spectralDyadicBlock d.2 k2 : ℂ) *
          weightOneBesselTransform (fun x => W2 (x/K2)) ((k2 : ℝ)/(q : ℝ)^2)) := by
        unfold thetaBesselCoeff
        ring
      _ = _ := by
        rw [h2 k2 hk2, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with t
        dsimp [b]
        ring
  simp only [ha', hb']

end ArtinMatthews
