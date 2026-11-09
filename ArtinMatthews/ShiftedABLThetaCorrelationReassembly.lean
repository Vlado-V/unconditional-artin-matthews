module

public import ArtinMatthews.ShiftedABLThetaSignedReassembly
public import ArtinMatthews.CubicThetaOriginalReduction


set_option backward.privateInPublic true
@[expose] public section

/-! The original shifted correlation, with the circle and zero-frequency
errors retained and the nonzero dual replaced by its finite signed blocks. -/

noncomputable section
open UpperHalfPlane Set OAI
open scoped MatrixGroups ContDiff BigOperators

namespace ArtinMatthews

theorem shiftedABLThetaCorrelation_signed_dual_error
    {A ε E : ℝ} (hA : 1 ≤ A) (hε : 0 < ε) (hE : 0 ≤ E)
    (Cg : ℕ → ℝ) (hCg : ∀ j, 0 ≤ Cg j) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) [NeZero N], 3 ∣ N → ∀ (f : CuspForm (cubicThetaKernel N) 1)
        (χ : SevenEighths.HeckeFamily.Character),
        (∀ n, (qExpansion 1 f).coeff n = idealThetaCoeff χ n) →
        ∀ (m1 m2 : ℕ), m1 ≠ m2 → Squarefree m1 → Squarefree m2 →
        ∀ (M T : ℝ) (hM : 1 ≤ M) (hT : 1 ≤ T)
          (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hgs : Function.support g ⊆ Icc T (2*T)),
          M ≤ (m1 : ℝ) → (m1 : ℝ) ≤ 2*M → M ≤ (m2 : ℝ) → (m2 : ℝ) ≤ 2*M →
          (∀ j x, ‖iteratedDeriv j g x‖ ≤ Cg j/T^j) →
          let K1 := (m1 : ℝ)*T
          let K2 := (m2 : ℝ)*T
          let W1 := shiftedABLThetaTestWeight g hg T m1 (zero_lt_one.trans_le hT) hgs
          let W2 := shiftedABLThetaMajorantWeight m2 T
          let T1 := ⌈1+2*K1⌉₊
          let T2 := ⌈1+5*K2/2⌉₊
          let D := shiftedCommonPrimePart m1 m2
          let m3 := m1 / m1.gcd m2
          let m4 := m2 / m1.gcd m2
          let F := N*D^2
          let r := m3*m4
          let P := shiftedABLSourceParameter M T N
          let L := circlePowerScale P A
          let Q := circlePowerQ P A
          let U := shiftedABLThetaDualCutoff M T P Q ε
          let J := shiftedABLDualCutoffIndex U
          ‖thetaShiftedCorrelation χ m1 m2 g -
            ∑ d ∈ shiftedABLDualRectangle J,
              ∑ i ∈ shiftedABLSignedFrequencyIndices m3 m4 d,
                shiftedABLThetaSignedCircleBlock χ W1 W2 K1 K2 D m3 m4 F r L d i‖ ≤
            circleThetaSourceError χ m1 m2 T1 T2 (shiftedSourceTest g m1)
              (shiftedSourceMajorant m2 T) F r L +
            ‖thetaDualZeroCircleAverage χ W1 W2 K1 K2 D m3 m4 F r L‖ +
            C*P^(-E) := by
  obtain ⟨C,hC,hbound⟩ := shiftedABLThetaCircle_signed_dual_tail hA hε hE Cg hCg
  refine ⟨C,hC, ?_⟩
  intro N inst hN f χ hcoeff m1 m2 hne hsq1 hsq2 M T hM hT g hg hgs
    hm1 hm1' hm2 hm2' hderiv K1 K2 W1 W2 T1 T2 D m3 m4 F r P L Q U J
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hm10 : 0 < m1 := by exact_mod_cast zero_lt_one.trans_le (hM.trans hm1)
  have hm20 : 0 < m2 := by exact_mod_cast zero_lt_one.trans_le (hM.trans hm2)
  have hP0 : 0 < P := zero_lt_one.trans_le (shiftedABLSourceParameter_one_le hM hT hN0)
  have hL : 0 < L := circlePowerScale_pos hP0
  have horiginal := thetaShiftedCorrelation_nonzero_error N hN f χ hcoeff m1 m2 L hL
    hm10 hm20 hne hsq1 hsq2 T hT g hg hgs
  obtain ⟨_,_,_,hsmall⟩ := hbound χ g hg M T m1 m2 N D m3 m4 F r
    hM hT hgs hN0 hm1 hm1' hm2 hm2' hderiv
  let source := thetaShiftedCorrelation χ m1 m2 g
  let dual := thetaDualNonzeroCircleAverage χ W1 W2 K1 K2 D m3 m4 F r L
  let finite := ∑ d ∈ shiftedABLDualRectangle J, ∑ i ∈ shiftedABLSignedFrequencyIndices m3 m4 d,
    shiftedABLThetaSignedCircleBlock χ W1 W2 K1 K2 D m3 m4 F r L d i
  change ‖source-dual‖ ≤ _ at horiginal
  change ‖dual-finite‖ ≤ C*P^(-E) at hsmall
  change ‖source-finite‖ ≤ _
  have heq : source-finite = (source-dual)+(dual-finite) := by ring
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add horiginal hsmall)

end ArtinMatthews
