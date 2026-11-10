module

public import ArtinMatthews.ShiftedABLCorrelationTarget
public import ArtinMatthews.CubicThetaActualCuspFormBase
public import ArtinMatthews.ShiftedABLSignedSpectralInput
public import ArtinMatthews.CubicThetaActualCuspFormConstructed
public import ArtinMatthews.ShiftedABLBlockCountBudget
public import ArtinMatthews.ShiftedABLDetectorRecovery
public import ArtinMatthews.ShiftedABLOriginalParameters
public import ArtinMatthews.ShiftedABLRetainedGeometry
public import ArtinMatthews.ShiftedABLRetainedSourceBlock
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

/-! The exact signed Mellin estimate implies the original smooth source
correlation bound after summing the retained blocks and restoring the
circle detector and zero frequency. -/

noncomputable section
open OAI Set UpperHalfPlane
open scoped ContDiff BigOperators MatrixGroups
namespace ArtinMatthews

theorem shiftedABL_correlationSource_of_signed_spectral
    (hspectral : ShiftedABLSignedSpectralInput)
    (N : ℕ) [NeZero N] (hN : 3 ∣ N)
    (f : CuspForm (cubicThetaKernel N) 1) (χ : SevenEighths.HeckeFamily.Character)
    (hcoeff : ∀ k, (qExpansion 1 f).coeff k = idealThetaCoeff χ k) :
    ShiftedABLCorrelationSource N χ := by
  intro ν hν Cg hCg
  let τ : ℝ := min (1/8) (ν/1000)
  have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ ≤ 1 := (min_le_left _ _).trans (by norm_num : (1/8 : ℝ) ≤ 1)
  have hτν : 218*τ ≤ ν := by
    have h : τ ≤ ν/1000 := min_le_right _ _
    linarith only [h,hν]
  have hA : (12 : ℝ) ≤ 40 := by norm_num
  have hAE : 2*(18+(1 : ℝ)) ≤ 40 := by norm_num
  have hN0 : 0 < N := NeZero.pos N
  have hN2 : 2 ≤ N := (by norm_num : 2 ≤ 3).trans (Nat.le_of_dvd hN0 hN)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  obtain ⟨Cb,hCb,hblock⟩ := shiftedABL_retained_source_block_bound
    hspectral N hN f χ hcoeff τ hτ hτ1 Cg hCg
  obtain ⟨Cc,hCc,hcount⟩ := shiftedABLThetaSignedBlock_count_power_budget
    (A := 40) (ε := τ) (ν := τ) (by norm_num) hτ.le hτ1 hτ
  obtain ⟨Ce,hCe,hrecover⟩ := shiftedABLOriginal_correlation_recovery
    hA hAE hτ (by norm_num : (0 : ℝ) ≤ 1) Cg hCg
  let C := Ce+Cb*Cc*(N : ℝ)^ν
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro m1 m2 hne hs1 hs2 hcop M T hM hT hm1 hm1' hm2 hm2' g hg hgs hderiv
  let H := M*T
  let P := shiftedABLSourceParameter M T N
  let L := circlePowerScale P 40
  let Q := circlePowerQ P 40
  let U := shiftedABLThetaDualCutoff M T P Q τ
  let J := shiftedABLDualCutoffIndex U
  let d₀ := m1.gcd m2
  let D := shiftedCommonPrimePart m1 m2
  let m3 := m1/d₀
  let m4 := m2/d₀
  let F := N*D^2
  let r := m3*m4
  let W1 := shiftedABLThetaTestWeight g hg T m1 (zero_lt_one.trans_le hT) hgs
  let W2 := shiftedABLThetaMajorantWeight m2 T
  let block (d : ℕ × ℕ) (i : ℕ × Bool) :=
    shiftedABLThetaSignedCircleBlock χ W1 W2 ((m1 : ℝ)*T) ((m2 : ℝ)*T) D m3 m4 F r L d i
  let S : ℂ := ∑ d ∈ shiftedABLDualRectangle J,
    ∑ i ∈ shiftedABLSignedFrequencyIndices m3 m4 d, block d i
  let K : ℕ := ∑ d ∈ shiftedABLDualRectangle J,
    (shiftedABLSignedFrequencyIndices m3 m4 d).card
  let W := Real.sqrt (H+1)*Real.sqrt M*(D : ℝ)/Real.sqrt d₀+
    (H+1)^(3/4 : ℝ)*(D : ℝ)^(1/4 : ℝ)/M^(1/4 : ℝ)
  have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le hM hT
  have hP2 := (shiftedABLOriginal_scale_bounds hM hT hN2 hm1 hm1' hm2 hm2'
    hne hs1 hs2 hcop).1
  change 2 ≤ P at hP2
  have hP1 : 1 ≤ P := by linarith only [hP2]
  have hP0 : 0 < P := zero_lt_one.trans_le hP1
  have hW : 1 ≤ W := by
    have hm10 : 0 < m1 := by exact_mod_cast (zero_lt_one.trans_le (hM.trans hm1))
    have hm20 : 0 < m2 := by exact_mod_cast (zero_lt_one.trans_le (hM.trans hm2))
    have hd₀ : 0 < d₀ := Nat.gcd_pos_of_pos_left _ hm10
    have hdR : (1 : ℝ) ≤ d₀ := by exact_mod_cast hd₀
    obtain ⟨u,_,hu,he,_,_,_,_⟩ := squarefree_commonPrimePart_factors hm10 hm20 hne hs1 hs2
    have hdD : (d₀ : ℝ) ≤ D := by
      have hnat : d₀ ≤ D := by
        calc
          d₀ = d₀*1 := (Nat.mul_one _).symm
          _ ≤ d₀*u := Nat.mul_le_mul_left _ (Nat.pos_of_ne_zero hu)
          _ = D := he.symm
      exact_mod_cast hnat
    have hds : Real.sqrt d₀ ≤ D := (Real.sqrt_le_self_iff.mpr (Or.inr hdR)).trans hdD
    have hfirst : 1 ≤ Real.sqrt (H+1)*Real.sqrt M*((D : ℝ)/Real.sqrt d₀) :=
      one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le
          (Real.one_le_sqrt.mpr (by linarith only [hH])) (Real.one_le_sqrt.mpr hM))
        ((one_le_div (Real.sqrt_pos.mpr (zero_lt_one.trans_le hdR))).mpr hds)
    exact (hfirst.trans_eq (mul_div_assoc _ _ _).symm).trans (le_add_of_nonneg_right (by positivity))
  have hterm (d : ℕ × ℕ) (hd : d ∈ shiftedABLDualRectangle J)
      (i : ℕ × Bool) (hi : i ∈ shiftedABLSignedFrequencyIndices m3 m4 d) :
      ‖block d i‖ ≤ Cb*P^(217*τ)*W := by
    obtain ⟨hK1,hK2,_,hR,_,hX,hV,hnX,hVs,hP₀⟩ :=
      shiftedABL_retained_block_parameter_bounds hA hτ.le hτ1 hM hT hN2
        hm1 hm1' hm2 hm2' hne hs1 hs2 hcop d hd i hi
    rw [show 3*(40 : ℝ)+6=126 by norm_num] at hP₀
    exact hblock m1 m2 hne hs1 hs2 hcop M T hM hT hm1 hm1' hm2 hm2' g hg hgs hderiv
      d i hK1 hK2 hR hX hV hnX hVs hP₀
  have hcount' : (K : ℝ) ≤ Cc*P^τ := hcount M T N m1 m2 hM hT hN2 hm1' hm2'
  have hjoin : P^τ*P^(217*τ)=P^(218*τ) := by
    rw [← Real.rpow_add hP0]
    congr 1
    ring
  have hS : ‖S‖ ≤ Cb*Cc*P^(218*τ)*W := by
    calc
      ‖S‖ ≤ ∑ d ∈ shiftedABLDualRectangle J,
          ∑ i ∈ shiftedABLSignedFrequencyIndices m3 m4 d, ‖block d i‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
      _ ≤ ∑ d ∈ shiftedABLDualRectangle J,
          ∑ _ ∈ shiftedABLSignedFrequencyIndices m3 m4 d, Cb*P^(217*τ)*W :=
        Finset.sum_le_sum fun d hd => Finset.sum_le_sum fun i hi => hterm d hd i hi
      _ = (K : ℝ)*(Cb*P^(217*τ)*W) := by
        simp only [K,Finset.sum_const,nsmul_eq_mul,Nat.cast_sum,Finset.sum_mul]
      _ ≤ Cc*P^τ*(Cb*P^(217*τ)*W) :=
        mul_le_mul_of_nonneg_right hcount' (by positivity)
      _ = Cb*Cc*(P^τ*P^(217*τ))*W := by ring
      _ = _ := by rw [hjoin]
  have hPν : P^(218*τ) ≤ (N : ℝ)^ν*H^ν := by
    have hPH : P=(N : ℝ)*H := by dsimp only [P,H,shiftedABLSourceParameter]; ring
    calc
      _ ≤ P^ν := Real.rpow_le_rpow_of_exponent_le hP1 hτν
      _ = _ := by rw [hPH,Real.mul_rpow hNR.le (zero_le_one.trans hH)]
  have herror : ‖thetaShiftedCorrelation χ m1 m2 g-S‖ ≤ Ce*P^(-1 : ℝ) :=
    hrecover N hN f χ hcoeff m1 m2 hne hs1 hs2 hcop M T hM hT g hg hgs
      hm1 hm1' hm2 hm2' hderiv
  have herror' : ‖thetaShiftedCorrelation χ m1 m2 g-S‖ ≤ Ce*H^ν*W := by
    have hsmall : P^(-1 : ℝ) ≤ 1 := by
      simpa only [Real.rpow_zero] using
        Real.rpow_le_rpow_of_exponent_le hP1 (by norm_num : (-1 : ℝ) ≤ 0)
    have hlarge : 1 ≤ H^ν*W := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hH hν.le) hW
    simpa only [mul_assoc] using herror.trans (mul_le_mul_of_nonneg_left (hsmall.trans hlarge) hCe.le)
  change ‖thetaShiftedCorrelation χ m1 m2 g‖ ≤ C*H^ν*W
  calc
    _ = ‖thetaShiftedCorrelation χ m1 m2 g-S+S‖ := by rw [sub_add_cancel]
    _ ≤ ‖thetaShiftedCorrelation χ m1 m2 g-S‖+‖S‖ := norm_add_le _ _
    _ ≤ Ce*H^ν*W+Cb*Cc*P^(218*τ)*W := add_le_add herror' hS
    _ ≤ Ce*H^ν*W+Cb*Cc*((N : ℝ)^ν*H^ν)*W := by gcongr
    _ = _ := by dsimp only [C]; ring

theorem cubicNumerator_shiftedABLCorrelationSource_of_signed_spectral
    (hspectral : ShiftedABLSignedSpectralInput)
    (a : ℤ) (ha : a ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3=(a : OAI.CubicFirstMoment.Eisenstein)) :
    ShiftedABLCorrelationSource (cubicNumeratorThetaLevel a)
      (cubicNumeratorHeckeCharacter a ha) := by
  letI : NeZero (cubicNumeratorThetaLevel a) := ⟨cubicNumeratorThetaLevel_ne_zero ha⟩
  exact shiftedABL_correlationSource_of_signed_spectral hspectral
    (cubicNumeratorThetaLevel a) (cubicNumeratorThetaLevel_three_dvd a)
    (actualCubicNumeratorHeckeThetaCuspForm a ha hnoncube) _
    (actualCubicNumeratorHeckeThetaCuspForm_qExpansion_coeff a ha hnoncube)

end ArtinMatthews
