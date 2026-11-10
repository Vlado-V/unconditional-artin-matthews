module

public import ArtinMatthews.CubicThetaShiftedCorrelation
public import ArtinMatthews.ShiftedABLThetaSignedReassembly
public import ArtinMatthews.ShiftedABLDetectorError
public import ArtinMatthews.ShiftedABLThetaCorrelationReassembly
public import ArtinMatthews.ShiftedABLZeroError
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Recovery of the original physical correlation from its finite signed
blocks, with both the actual circle detector and zero frequency absorbed. -/

noncomputable section
open UpperHalfPlane Set OAI
open scoped MatrixGroups ContDiff BigOperators

namespace ArtinMatthews

/-- A fixed circle exponent chosen before every source parameter. -/
def shiftedABLRecoveryPower (E : ℝ) : ℝ := max 12 (2*(18+E))

theorem shiftedABLRecoveryPower_bounds (E : ℝ) :
    12 ≤ shiftedABLRecoveryPower E ∧ 2*(18+E) ≤ shiftedABLRecoveryPower E :=
  ⟨le_max_left _ _,le_max_right _ _⟩

theorem shiftedABLOriginal_correlation_recovery
    {A ε E : ℝ} (hA : 12 ≤ A) (hAE : 2*(18+E) ≤ A) (hε : 0 < ε) (hE : 0 ≤ E)
    (Cg : ℕ → ℝ) (hCg : ∀ j, 0 ≤ Cg j) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) [NeZero N], 3 ∣ N → ∀ (f : CuspForm (cubicThetaKernel N) 1)
        (χ : SevenEighths.HeckeFamily.Character),
        (∀ n, (qExpansion 1 f).coeff n = idealThetaCoeff χ n) →
        ∀ (m1 m2 : ℕ), m1 ≠ m2 → Squarefree m1 → Squarefree m2 → N.Coprime (m1*m2) →
        ∀ (M T : ℝ) (hM : 1 ≤ M) (hT : 1 ≤ T)
          (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hgs : Function.support g ⊆ Icc T (2*T)),
          M ≤ (m1 : ℝ) → (m1 : ℝ) ≤ 2*M → M ≤ (m2 : ℝ) → (m2 : ℝ) ≤ 2*M →
          (∀ j x, ‖iteratedDeriv j g x‖ ≤ Cg j/T^j) →
          let K1 := (m1 : ℝ)*T
          let K2 := (m2 : ℝ)*T
          let W1 := shiftedABLThetaTestWeight g hg T m1 (zero_lt_one.trans_le hT) hgs
          let W2 := shiftedABLThetaMajorantWeight m2 T
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
            C*P^(-E) := by
  obtain ⟨Cd,hCd,hd⟩ := shiftedABLOriginal_detector_error hA hAE (Cg 0) (hCg 0)
  obtain ⟨Cz,hCz,hz⟩ := shiftedABLOriginal_zero_error hA hAE Cg hCg
  obtain ⟨Ct,hCt,ht⟩ := shiftedABLThetaCorrelation_signed_dual_error
    (by linarith : 1 ≤ A) hε hE Cg hCg
  refine ⟨Cd+Cz+Ct,by positivity,?_⟩
  intro N inst hN f χ hcoeff m1 m2 hne hs1 hs2 hcop M T hM hT g hg hgs
    hm1 hm1' hm2 hm2' hderiv K1 K2 W1 W2 D m3 m4 F r P L Q U J
  have hN2 : 2 ≤ N := (by norm_num : 2 ≤ 3).trans (Nat.le_of_dvd (NeZero.pos N) hN)
  have hfirst := ht N hN f χ hcoeff m1 m2 hne hs1 hs2 M T hM hT g hg hgs
    hm1 hm1' hm2 hm2' hderiv
  have hsource : ∀ x : ℝ, ‖g x‖ ≤ Cg 0 := by
    intro x
    simpa only [iteratedDeriv_zero,pow_zero,div_one] using hderiv 0 x
  have hdetector := hd M T N m1 m2 hM hT hN2 hm1 hm1' hm2 hm2' hne hs1 hs2 hcop χ g hsource
  simp only [mul_assoc] at hdetector
  have hzero := hz M T N m1 m2 hM hT hN2 hm1 hm1' hm2 hm2' hne hs1 hs2 hcop χ g hg hgs hderiv
  refine hfirst.trans ?_
  calc
    _ ≤ Cd*P^(-E)+Cz*P^(-E)+Ct*P^(-E) := add_le_add
      (add_le_add hdetector hzero) le_rfl
    _ = (Cd+Cz+Ct)*P^(-E) := by ring

end ArtinMatthews
