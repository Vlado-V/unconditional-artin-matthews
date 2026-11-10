module

public import ArtinMatthews.ShiftedABLThetaSourceDecay
public import ArtinMatthews.CubicThetaDualZeroAverage
public import ArtinMatthews.ShiftedABLSourceParameters
public import ArtinMatthews.ShiftedCommonPrimePartSquarefree
public import ArtinMatthews.ShiftedABLOriginalParameters
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

/-! Uniform seminorms of the literal shifted source and plateau make the
normalized Ramanujan zero-frequency term a power-saving error. -/

noncomputable section
open Set OAI
open scoped BigOperators ContDiff

namespace ArtinMatthews

private theorem shiftedABL_source_seminorms (s : Finset (ℕ × ℕ))
    (Cg : ℕ → ℝ) (hCg : ∀ j, 0 ≤ Cg j) :
    ∃ B1 B2 : ℝ, 0 ≤ B1 ∧ 0 ≤ B2 ∧
      ∀ (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (T m1 m2 : ℝ)
        (hT : 0 < T) (hgs : Function.support g ⊆ Icc T (2*T)),
        1 ≤ m1*T → 1 ≤ m2*T →
        (∀ j x, ‖iteratedDeriv j g x‖ ≤ Cg j/T^j) →
        s.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          (shiftedABLThetaTestWeight g hg T m1 hT hgs) ≤ B1 ∧
        s.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          (shiftedABLThetaMajorantWeight m2 T) ≤ B2 := by
  classical
  let B1 : ℝ := ∑ p ∈ s, 3^p.1 * Cg p.2
  let B2 : ℝ := ∑ p ∈ s, (7/2 : ℝ)^p.1 *
    SchwartzMap.seminorm ℝ 0 p.2 sourcePlateauSchwartz
  have hB1 : 0 ≤ B1 := Finset.sum_nonneg (fun p _ => mul_nonneg (by positivity) (hCg p.2))
  have hB2 : 0 ≤ B2 := Finset.sum_nonneg (fun p _ => by positivity)
  refine ⟨B1,B2,hB1,hB2,?_⟩
  intro g hg T m1 m2 hT hgs hscale1 hscale2 hderiv
  constructor
  · apply Seminorm.finset_sup_apply_le hB1
    intro p hp
    change SchwartzMap.seminorm ℝ p.1 p.2 _ ≤ B1
    exact (shiftedSourceTest_normalized_seminorm g hg T m1 (Cg p.2) hT hgs
      hscale1 p.1 p.2 (hCg p.2) (hderiv p.2)).trans
      (Finset.single_le_sum (f := fun p : ℕ × ℕ => 3^p.1 * Cg p.2)
        (fun p _ => mul_nonneg (by positivity) (hCg p.2)) hp)
  · apply Seminorm.finset_sup_apply_le hB2
    intro p hp
    change SchwartzMap.seminorm ℝ p.1 p.2 _ ≤ B2
    have hs : Function.support sourcePlateauSchwartz ⊆ Icc (0 : ℝ) (5/2) := by
      intro x hx
      have h := shiftedSourcePlateau_support hx
      exact ⟨by linarith [h.1],h.2⟩
    have hδ : 1/(m2*T) ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one (zero_lt_one.trans_le hscale2)).mpr hscale2⟩
    have hb := shiftedSourceTranslate_seminorm sourcePlateauSchwartz (5/2)
      (1/(m2*T)) (by norm_num) hs hδ p.1 p.2
    have hb' : SchwartzMap.seminorm ℝ p.1 p.2
        (shiftedABLThetaMajorantWeight m2 T) ≤
        (7/2 : ℝ)^p.1 * SchwartzMap.seminorm ℝ 0 p.2 sourcePlateauSchwartz := by
      simpa only [shiftedABLThetaMajorantWeight, show (5/2 : ℝ)+1=7/2 by norm_num] using hb
    exact hb'.trans (Finset.single_le_sum
      (f := fun p : ℕ × ℕ => (7/2 : ℝ)^p.1 * SchwartzMap.seminorm ℝ 0 p.2 sourcePlateauSchwartz)
      (fun p _ => by positivity) hp)

theorem shiftedABLOriginal_zero_error
    {A E : ℝ} (hA : 12 ≤ A) (hAE : 2*(18+E) ≤ A)
    (Cg : ℕ → ℝ) (hCg : ∀ j, 0 ≤ Cg j) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M T : ℝ) (N m1 m2 : ℕ), 1 ≤ M → ∀ hT : 1 ≤ T, 2 ≤ N →
        M ≤ (m1 : ℝ) → (m1 : ℝ) ≤ 2*M → M ≤ (m2 : ℝ) → (m2 : ℝ) ≤ 2*M →
        m1 ≠ m2 → Squarefree m1 → Squarefree m2 → N.Coprime (m1*m2) →
        ∀ (χ : SevenEighths.HeckeFamily.Character) (g : ℝ → ℂ)
          (hg : ContDiff ℝ ∞ g) (hgs : Function.support g ⊆ Icc T (2*T)),
          (∀ j x, ‖iteratedDeriv j g x‖ ≤ Cg j/T^j) →
        let P := shiftedABLSourceParameter M T N
        let d := m1.gcd m2
        let D := shiftedCommonPrimePart m1 m2
        let F := N*D^2
        let r := (m1/d)*(m2/d)
        let L := circlePowerScale P A
        ‖thetaDualZeroCircleAverage χ
          (shiftedABLThetaTestWeight g hg T m1 (zero_lt_one.trans_le hT) hgs)
          (shiftedABLThetaMajorantWeight m2 T) ((m1 : ℝ)*T) ((m2 : ℝ)*T)
          D (m1/d) (m2/d) F r L‖ ≤ C*P^(-E) := by
  obtain ⟨s,C₀,hC₀,hzero⟩ := thetaDualZeroCircleAverage_bound
  obtain ⟨B1,B2,hB1,hB2,hbounds⟩ := shiftedABL_source_seminorms s Cg hCg
  let B := 8*C₀*(B1^2+B2^2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B+1,by positivity,?_⟩
  intro M T N m1 m2 hM hT hN hm1 hm1' hm2 hm2' hne hs1 hs2 hcop χ g hg hgs
    hderiv P d D F r L
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hm1p : 0 < m1 := by exact_mod_cast zero_lt_one.trans_le (hM.trans hm1)
  have hm2p : 0 < m2 := by exact_mod_cast zero_lt_one.trans_le (hM.trans hm2)
  obtain ⟨_,_,hm3,hm4,hneq,_,_,_,_,_,hF,hr,hFr⟩ := shiftedABLOriginal_cofactors
    (by omega : 0 < N) hm1p hm2p hne hs1 hs2 hcop
  obtain ⟨hP,hHP,_,_,_,_,_,hnup,hFup,hrup⟩ := shiftedABLOriginal_scale_bounds
    hM hT hN hm1 hm1' hm2 hm2' hne hs1 hs2 hcop
  have hP0 : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  have hL := shiftedABLOriginal_detector_threshold hM hT hN hA hm1 hm1' hm2 hm2'
    hne hs1 hs2 hcop
  have hscale1 : 1 ≤ (m1 : ℝ)*T := one_le_mul_of_one_le_of_one_le (hM.trans hm1) hT
  have hscale2 : 1 ≤ (m2 : ℝ)*T := one_le_mul_of_one_le_of_one_le (hM.trans hm2) hT
  obtain ⟨hW1,hW2⟩ := hbounds g hg T m1 m2 hT0 hgs hscale1 hscale2 hderiv
  have hsupport1 := shiftedSourceTest_normalized_support g hg T m1 hT0 hgs hscale1
  have hsupport2 := shiftedSourceMajorant_normalized_support m2 T hscale2
  have he := hzero χ _ _ 3 (7/2) (by norm_num) (by norm_num) hsupport1 hsupport2
    ((m1 : ℝ)*T) ((m2 : ℝ)*T) (by positivity) (by positivity)
    D (m1/d) (m2/d) hm3 hm4 hneq F r L hF hr hFr hL
  have hK1 : ((m1 : ℝ)*T)^(7/8 : ℝ) ≤ 2*P := by
    calc
      _ ≤ ((m1 : ℝ)*T)^(1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hscale1 (by norm_num)
      _ = (m1 : ℝ)*T := Real.rpow_one _
      _ ≤ 2*P := by nlinarith [mul_le_mul_of_nonneg_right hm1' hT0.le]
  have hK2 : ((m2 : ℝ)*T)^(7/8 : ℝ) ≤ 2*P := by
    calc
      _ ≤ ((m2 : ℝ)*T)^(1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hscale2 (by norm_num)
      _ = (m2 : ℝ)*T := Real.rpow_one _
      _ ≤ 2*P := by nlinarith [mul_le_mul_of_nonneg_right hm2' hT0.le]
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr5 : (r : ℝ)^(1/4 : ℝ) ≤ P^5 := by
    calc
      _ ≤ (r : ℝ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hr1 (by norm_num)
      _ = (r : ℝ) := Real.rpow_one _
      _ ≤ P^5 := by
        change (r : ℝ) ≤ P^(5 : ℝ) at hrup
        norm_num at hrup
        exact hrup
  have hF5 : (F : ℝ) ≤ P^5 := by
    change (F : ℝ) ≤ P^(5 : ℝ) at hFup
    norm_num at hFup
    exact hFup
  change (((((m1/d : ℕ) : ℤ)-(m2/d : ℕ)).natAbs) : ℝ) ≤ 2*P at hnup
  have h18 : P^(13 : ℝ) ≤ P^(18 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hP1 (by norm_num)
  calc
    _ ≤ C₀ * (((((m1/d : ℕ) : ℤ)-(m2/d : ℕ)).natAbs) : ℝ)^2 *
        (((m1 : ℝ)*T)^(7/8 : ℝ) *
          (s.sup (schwartzSeminormFamily ℝ ℝ ℂ)
            (shiftedABLThetaTestWeight g hg T m1 hT0 hgs))^2 +
        ((m2 : ℝ)*T)^(7/8 : ℝ) *
          (s.sup (schwartzSeminormFamily ℝ ℝ ℂ)
            (shiftedABLThetaMajorantWeight m2 T))^2) *
        (F : ℝ)*(r : ℝ)^(1/4 : ℝ)/Real.sqrt L := he
    _ ≤ C₀*(2*P)^2*((2*P)*B1^2+(2*P)*B2^2)*P^5*P^5/Real.sqrt L := by
      gcongr
    _ = B*(P^(13 : ℝ)/Real.sqrt L) := by
      dsimp [B]; norm_num [Real.rpow_natCast]; ring
    _ ≤ B*(P^(18 : ℝ)/Real.sqrt L) := by gcongr
    _ ≤ B*P^(-E) := mul_le_mul_of_nonneg_left (circlePowerScale_decay hP hAE) hB
    _ ≤ (B+1)*P^(-E) := by gcongr; linarith

end ArtinMatthews
