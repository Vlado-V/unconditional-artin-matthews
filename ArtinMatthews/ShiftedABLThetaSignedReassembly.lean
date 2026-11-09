module

public import ArtinMatthews.ShiftedABLDualFrequency
public import ArtinMatthews.ShiftedABLThetaCircleTail


set_option backward.privateInPublic true
@[expose] public section

/-! The finite actual source reassembly, retaining the smooth dual indices,
signed frequency blocks, character, and original circle normalizer. -/

noncomputable section
open Set OAI
open scoped ContDiff BigOperators

namespace ArtinMatthews

def shiftedABLSignedFrequencyIndices (m3 m4 : ℕ) (d : ℕ × ℕ) : Finset (ℕ × Bool) :=
  (shiftedABLDualFrequencies m3 m4 d).image shiftedABLSignedFrequencyIndex

/-- The literal normalized summand for one signed frequency at one modulus. -/
def shiftedABLThetaRhoNormalized
    (χ : SevenEighths.HeckeFamily.Character) (W1 W2 : SchwartzMap ℝ ℂ)
    (K1 K2 : ℝ) (D m3 m4 q : ℕ) (d : ℕ × ℕ) (ρ : ℤ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    (cubicThetaNebentypus (-((m3 : ℕ) : ℤ) * m4) / (q : ℂ)^2) *
      (shiftedABLThetaRhoCoefficient χ W1 W2 K1 K2 D m3 m4 q d ρ *
        shiftedABLThetaRhoKloosterman q m3 m4 ρ)

/-- The sharp signed radius restriction acts only on the frequency
coefficient. The original smooth modulus weight and totient normalizer
are unchanged. -/
def shiftedABLThetaSignedCircleBlock
    (χ : SevenEighths.HeckeFamily.Character) (W1 W2 : SchwartzMap ℝ ℂ)
    (K1 K2 : ℝ) (D m3 m4 F r L : ℕ) (d : ℕ × ℕ) (i : ℕ × Bool) : ℂ :=
  ∑ ρ ∈ (shiftedABLDualFrequencies m3 m4 d).filter (fun ρ => shiftedABLSignedFrequencyIndex ρ = i),
    (∑ q ∈ circleModuli F r L, (circleSmoothWeight L q : ℂ) *
      shiftedABLThetaRhoNormalized χ W1 W2 K1 K2 D m3 m4 q d ρ) /
        (circleNormalizer (circleModuli F r L) (circleSmoothWeight L) : ℂ)

private theorem shiftedABLThetaDyadicNormalized_eq_sum_rho
    (χ : SevenEighths.HeckeFamily.Character) (W1 W2 : SchwartzMap ℝ ℂ)
    (K1 K2 : ℝ) (D m3 m4 q : ℕ) (d : ℕ × ℕ) :
    thetaDualDyadicNormalized χ W1 W2 K1 K2 D m3 m4 q d =
      ∑ ρ ∈ shiftedABLDualFrequencies m3 m4 d,
        shiftedABLThetaRhoNormalized χ W1 W2 K1 K2 D m3 m4 q d ρ := by
  by_cases hq : q = 0
  · simp [thetaDualDyadicNormalized, shiftedABLThetaRhoNormalized, hq]
  · let : NeZero q := ⟨hq⟩
    rw [shiftedABLThetaDyadicNormalized_eq_rho]
    simp only [shiftedABLThetaRhoNormalized, dite_eq_right hq, Finset.mul_sum]

theorem shiftedABLThetaDyadicCircleBlock_eq_signed
    (χ : SevenEighths.HeckeFamily.Character) (W1 W2 : SchwartzMap ℝ ℂ)
    (K1 K2 : ℝ) (D m3 m4 F r L : ℕ) (d : ℕ × ℕ) :
    thetaDualDyadicCircleBlock χ W1 W2 K1 K2 D m3 m4 F r L d =
      ∑ i ∈ shiftedABLSignedFrequencyIndices m3 m4 d,
        shiftedABLThetaSignedCircleBlock χ W1 W2 K1 K2 D m3 m4 F r L d i := by
  unfold thetaDualDyadicCircleBlock shiftedABLThetaSignedCircleBlock
  simp_rw [shiftedABLThetaDyadicNormalized_eq_sum_rho, Finset.mul_sum]
  rw [Finset.sum_comm (s := circleModuli F r L), Finset.sum_div]
  exact (Finset.sum_fiberwise_of_maps_to
    (fun ρ hρ => Finset.mem_image_of_mem shiftedABLSignedFrequencyIndex hρ) _).symm

/-- Exact scale hypotheses for a kept dual block and any frequency of
one of its signed radius blocks. With the source cutoff chosen below,
both dual scales are at most `8 P^ε Q²/(MT)`. -/
theorem shiftedABLThetaSignedBlock_geometry {U : ℝ} {J m3 m4 : ℕ}
    {d : ℕ × ℕ} {ρ : ℤ} {i : ℕ × Bool} (hJU : (2 : ℝ)^J ≤ 2*U)
    (hd : d ∈ shiftedABLDualRectangle J)
    (hρ : ρ ∈ (shiftedABLDualFrequencies m3 m4 d).filter
      (fun ρ => shiftedABLSignedFrequencyIndex ρ = i)) :
    (2 : ℝ)^d.1 ≤ 2*U ∧ (2 : ℝ)^d.2 ≤ 2*U ∧
    (1 ≤ (2 : ℝ)^i.1 ∧ (2 : ℝ)^i.1 ≤ (ρ.natAbs : ℝ) ∧
      (ρ.natAbs : ℝ) < 2*(2 : ℝ)^i.1) ∧
    ∃ k1 k2 : ℕ, (k1 : ℝ) ≤ 2*(2 : ℝ)^d.1 ∧ (k2 : ℝ) ≤ 2*(2 : ℝ)^d.2 ∧
      shiftedABLDualFrequency m3 m4 k1 k2 = ρ := by
  obtain ⟨hd1,hd2⟩ := Finset.mem_product.mp hd
  have hj₁ : d.1 ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd1)
  have hj₂ : d.2 ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd2)
  obtain ⟨hρf,hi⟩ := Finset.mem_filter.mp hρ
  obtain ⟨hρ0,hw⟩ := shiftedABLDualFrequencies_witness hρf
  have hi' : i.1 = Nat.log 2 ρ.natAbs := (congrArg Prod.fst hi).symm
  obtain ⟨hl,hu⟩ := shiftedABLFrequency_dyadic hρ0
  refine ⟨(pow_le_pow_right₀ (by norm_num) hj₁).trans hJU,
    (pow_le_pow_right₀ (by norm_num) hj₂).trans hJU, ⟨one_le_pow₀ (by norm_num), ?_, ?_⟩, hw⟩
  · rw [hi']
    exact_mod_cast hl
  · rw [hi']
    rw [pow_succ, mul_comm] at hu
    exact_mod_cast hu

/-- The number of retained signed blocks has two dual dyadic factors and
one signed radius factor. -/
theorem shiftedABLThetaSignedBlock_count_le (J m3 m4 : ℕ) :
    (∑ d ∈ shiftedABLDualRectangle J, (shiftedABLSignedFrequencyIndices m3 m4 d).card) ≤
      (J+1)^2 * ((Nat.log 2 ((m3+m4)*(2*2^J))+1)*2) := by
  let B := (m3+m4)*(2*2^J)
  let S := (Finset.range (Nat.log 2 B+1)).product (Finset.univ : Finset Bool)
  have hS : S.card = (Nat.log 2 B+1)*2 := by simp [S]
  have hsub (d : ℕ × ℕ) (hd : d ∈ shiftedABLDualRectangle J) :
      shiftedABLSignedFrequencyIndices m3 m4 d ⊆ S := by
    intro i hi
    obtain ⟨ρ,hρ,hρi⟩ := Finset.mem_image.mp hi
    obtain ⟨_,k1,k2,hk1,hk2,heq⟩ := shiftedABLDualFrequencies_witness hρ
    obtain ⟨hd1,hd2⟩ := Finset.mem_product.mp hd
    have hd1' : d.1 ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd1)
    have hd2' : d.2 ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd2)
    have hk1' : k1 ≤ 2*2^d.1 := by exact_mod_cast hk1
    have hk2' : k2 ≤ 2*2^d.2 := by exact_mod_cast hk2
    have hb₁ : k1 ≤ 2*2^J := hk1'.trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by decide) hd1'))
    have hb₂ : k2 ≤ 2*2^J := hk2'.trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by decide) hd2'))
    have hB : ρ.natAbs ≤ B := by
      rw [← heq, shiftedABLDualFrequency]
      calc
        _ ≤ m4*k2+m3*k1 := by
          simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
            Int.natAbs_sub_le ((m4 : ℤ)*k2) ((m3 : ℤ)*k1)
        _ ≤ m4*(2*2^J)+m3*(2*2^J) :=
          add_le_add (Nat.mul_le_mul_left _ hb₂) (Nat.mul_le_mul_left _ hb₁)
        _ = B := by dsimp [B]; ring
    rw [← hρi]
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Nat.log_mono_right (b := 2) hB)), Finset.mem_univ _⟩
  calc
    _ ≤ ∑ _d ∈ shiftedABLDualRectangle J, S.card :=
      Finset.sum_le_sum (fun d hd => Finset.card_le_card (hsub d hd))
    _ = _ := by simp [shiftedABLDualRectangle, hS, B, pow_two]

/-- The original nonzero circle dual, with an arbitrarily small remainder,
as a finite sum of the actual signed blocks. -/
theorem shiftedABLThetaCircle_signed_dual_tail
    {A ε E : ℝ} (hA : 1 ≤ A) (hε : 0 < ε) (hE : 0 ≤ E)
    (Cg : ℕ → ℝ) (hCg : ∀ j, 0 ≤ Cg j) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (χ : SevenEighths.HeckeFamily.Character) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
        (M T m1 m2 : ℝ) (N D m3 m4 F r : ℕ) (_hM : 1 ≤ M) (hT : 1 ≤ T)
        (hgs : Function.support g ⊆ Icc T (2*T)),
        0 < N → M ≤ m1 → m1 ≤ 2*M → M ≤ m2 → m2 ≤ 2*M →
        (∀ j x, ‖iteratedDeriv j g x‖ ≤ Cg j/T^j) →
        let P := shiftedABLSourceParameter M T N
        let L := circlePowerScale P A
        let Q := circlePowerQ P A
        let U := shiftedABLThetaDualCutoff M T P Q ε
        let J := shiftedABLDualCutoffIndex U
        let W1 := shiftedABLThetaTestWeight g hg T m1 (zero_lt_one.trans_le hT) hgs
        let W2 := shiftedABLThetaMajorantWeight m2 T
        1 ≤ U ∧ U ≤ (2 : ℝ)^J ∧ (2 : ℝ)^J ≤ 2*U ∧
          ‖thetaDualNonzeroCircleAverage χ W1 W2 (m1*T) (m2*T) D m3 m4 F r L -
            ∑ d ∈ shiftedABLDualRectangle J,
              ∑ i ∈ shiftedABLSignedFrequencyIndices m3 m4 d,
                shiftedABLThetaSignedCircleBlock χ W1 W2 (m1*T) (m2*T) D m3 m4 F r L d i‖ ≤
            C*P^(-E) := by
  obtain ⟨C,hC,hbound⟩ := shiftedABLThetaCircle_dual_tail hA hε hE Cg hCg
  refine ⟨C,hC, ?_⟩
  intro χ g hg M T m1 m2 N D m3 m4 F r hM hT hgs hN hm1 hm1' hm2 hm2' hderiv
  simpa only [shiftedABLThetaDyadicCircleBlock_eq_signed] using
    hbound χ g hg M T m1 m2 N D m3 m4 F r hM hT hgs hN hm1 hm1' hm2 hm2' hderiv

end ArtinMatthews
