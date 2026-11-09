module

public import ArtinMatthews.ShiftedABLMellinKernels
public import ArtinMatthews.CircleNormalizerSmooth


set_option backward.privateInPublic true
@[expose] public section

/-! The exact (q=Fc) reindex of the original circle family and its
real smooth profile, retaining the factor (Q/q). -/

noncomputable section
open Complex Set OAI
open scoped BigOperators

namespace ArtinMatthews

/-- The actual modulus indices after extracting the divisibility factor. -/
def shiftedABLMellinModuli (F r L : ℕ) : Finset ℕ :=
  (circleModuli F r L).image (fun q => q/F)

theorem shiftedABLMellinModuli_reindex (F r L : ℕ) (f : ℕ → ℂ) :
    (∑ q ∈ circleModuli F r L, f q) = ∑ c ∈ shiftedABLMellinModuli F r L, f (F*c) := by
  have hmul (q : ℕ) (hq : q ∈ circleModuli F r L) : F*(q/F) = q :=
    Nat.mul_div_cancel' (Finset.mem_filter.mp hq).2.1
  unfold shiftedABLMellinModuli
  rw [Finset.sum_image]
  · exact Finset.sum_congr rfl (fun q hq => by rw [hmul q hq])
  · intro q hq q' hq' heq
    calc
      q = F*(q/F) := (hmul q hq).symm
      _ = F*(q'/F) := congrArg (F*·) heq
      _ = q' := hmul q' hq'

theorem shiftedABLMellinModuli_bounds {F r L c : ℕ}
    (hF : 0 < F) (hc : c ∈ shiftedABLMellinModuli F r L) :
    3*(L : ℝ)/(F : ℝ) ≤ (c : ℝ) ∧
      (c : ℝ) ≤ 2*(3*(L : ℝ)/(F : ℝ)) ∧ c.Coprime r := by
  obtain ⟨q,hq,hqc⟩ := Finset.mem_image.mp hc
  obtain ⟨hband,hdvd,hcop⟩ := Finset.mem_filter.mp hq
  have hF' : (0 : ℝ) < F := by exact_mod_cast hF
  have hqeq : F*c = q := by rw [← hqc]; exact Nat.mul_div_cancel' hdvd
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hband
  have hdiv : c ∣ q := ⟨F, by rw [← hqeq]; ring⟩
  refine ⟨?_,?_,hcop.of_dvd_left hdiv⟩
  · apply (div_le_iff₀ hF').2
    have h := show 3*(L : ℝ) ≤ (q : ℝ) by exact_mod_cast hlo
    rw [← hqeq, Nat.cast_mul] at h
    linarith
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ hF').2
    have h := show (q : ℝ) ≤ 6*(L : ℝ) by exact_mod_cast hhi
    rw [← hqeq, Nat.cast_mul] at h
    linarith

/-- The actual smooth modulus profile before the `1/c` in the spectral
sum. Its reciprocal factor is the original `Q/q`. -/
def shiftedABLMellinModulusWeight (F L : ℕ) (z : ℝ × ℝ) (c : ℝ) : ℂ :=
  (circleSmoothScaled L ((F : ℝ)*c) : ℂ) *
    ((3*(L : ℝ)/((F : ℝ)*c) : ℝ) : ℂ) *
    shiftedABLMellinCirclePhase (3*(L : ℝ)) z.1 ((F : ℝ)*c) *
    shiftedABLMellinCirclePhase (3*(L : ℝ)) z.2 ((F : ℝ)*c)

theorem shiftedABLMellinModulusWeight_support {F L : ℕ}
    (hF : 0 < F) (hL : 0 < L) (z : ℝ × ℝ) :
    Function.support (shiftedABLMellinModulusWeight F L z) ⊆
      Icc (3*(L : ℝ)/(F : ℝ)) (2*(3*(L : ℝ)/(F : ℝ))) := by
  intro c hc
  have hF' : (0 : ℝ) < F := by exact_mod_cast hF
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hn : (F : ℝ)*c ∈ Function.support (circleSmoothScaled L) := by
    intro h
    apply hc
    simp [shiftedABLMellinModulusWeight,h]
  rw [circleSmoothScaled_support hL'] at hn
  constructor
  · apply (div_le_iff₀ hF').2
    linarith [hn.1]
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ hF').2
    linarith [hn.2]

end ArtinMatthews
