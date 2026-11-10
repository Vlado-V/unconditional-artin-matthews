module

public import ArtinMatthews.PrincipalDedekindAbsoluteContour
public import ArtinMatthews.SourceContinuedPoissonRowIntegral
public import ArtinMatthews.SourceProbeComparison
public import ArtinMatthews.SourceContinuedPoissonMagnitude
public import ArtinMatthews.SourceContinuedPoissonRowShifts
public import ArtinMatthews.SourceRowAnalyticBounds
public import ArtinMatthews.SourceRowEulerDyadic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The source06 row bounds on the actual low-w and far-z right lines.
The estimates start at the original (4,4,2) contour and use the exact
proved shifts. The frequency power is part of the amplitude throughout. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators MeasureTheory
open VaryingKummerAnalytic SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "I" => sourceContinuedPoissonRowIntegral F S₀ hζ η hJ
local notation "N" => ‖(1/(2*Real.pi) : ℂ)^3‖ * sourcePoissonInverseQuadraticMass

private theorem sourceRightRowPoint_mem (p : ProbeCoordinates) (hξ : 1 < p.1.re)
    (hw : 3/1000 ≤ p.2.1.re) (hz : 2/5 ≤ p.2.2.re) : p ∈ probeEulerDomain :=
  Or.inl ⟨by linarith, by linarith, by linarith⟩

theorem exists_sourceContinuedPoissonRow_low_w_dyadic_bound
    (hcut : principalAngularCutoff F J ⊆ S) (v : InfinitePlace F) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : {a : R // a ≠ 0}), (¬ ∃ x : F, x^6 = (u.val : F)) →
      ∀ U : ℝ, 0 < U → U ≤ sourcePoissonFrequencyNorm F S₀ u → sourcePoissonFrequencyNorm F S₀ u ≤ 2*U →
      ∀ Z : ℝ, 0 < Z →
        ‖I v u (Z^(9/10 : ℝ)) (Z^(133/1000 : ℝ)) Z 4 4 2‖ ≤
          C*Z^(sourceContourExponent principalProbeSigma (3/1000) (2/5))*U^(1/10+ε) := by
  obtain ⟨m, hm⟩ := exists_sourceRowEulerContinuation_dyadic_low_w_bound F hζ S₀ η hJ hcut (2/5) (by norm_num)
  obtain ⟨A, hA, hAmp⟩ := hm ε hε
  obtain ⟨D, hD, hW⟩ := exists_sourceProbeContourWeights_inverse_quadratic F S₀ hζ v (3/1000) (2/5) (by norm_num) m
  let B := sourceRayAbsoluteEulerBound F principalProbeSigma
  let G := Real.exp ((principalProbeSigma+(2/5 : ℝ)-1)^2)
  have hB : 0 < B := sourceRayAbsoluteEulerBound_pos F _
  have hG : 0 < G := Real.exp_pos _
  have hN : 0 ≤ N := mul_nonneg (norm_nonneg _) sourcePoissonInverseQuadraticMass_nonneg
  refine ⟨(N+1)*G*A*B*D, by positivity, ?_⟩
  intro u hu U hU hlo hhi Z hZ
  let X := Z^(9/10 : ℝ)
  let Y := Z^(133/1000 : ℝ)
  have hX : 0 < X := Real.rpow_pos_of_pos hZ _
  have hY : 0 < Y := Real.rpow_pos_of_pos hZ _
  have hσ : 1 < principalProbeSigma := by norm_num [principalProbeSigma]
  have hQ := sourcePoissonFrequencyNorm_eq_exterior F S₀ hζ u
  rw [hQ] at hlo hhi
  rw [sourceContinuedPoissonRowIntegral_low_w F S₀ hζ η hJ hcut v u hu hX hY hZ]
  have H := sourceContinuedPoissonRowIntegral_norm_le_of_amplitude F S₀ hζ η hJ hcut v u hu hX hY hZ
    principalProbeSigma (3/1000) (2/5) hσ le_rfl le_rfl m (A*U^(1/10+ε)*B) D (by positivity) hW (by
      intro p
      dsimp only
      let q : ProbeCoordinates := (sourcePoissonVertical principalProbeSigma p.2,
        sourcePoissonVertical (3/1000) p.1.1, sourcePoissonVertical (2/5) p.1.2)
      have hξ : q.1.re = principalProbeSigma := sourcePoissonVertical_re _ _
      have hw : q.2.1.re = 3/1000 := sourcePoissonVertical_re _ _
      have hz : q.2.2.re = 2/5 := sourcePoissonVertical_re _ _
      have hi := sourceRightRowPoint_mem q (by rw [hξ]; exact hσ) hw.ge hz.ge
      have h := hAmp u.val u.property hu U hU hlo hhi q hi hw.ge hz.ge
      rw [← Complex.ofReal_natCast, ← hQ, hz, show (1/2 : ℝ)-2/5+ε = 1/10+ε by ring] at h
      have hR := sourceRowTwistReciprocal_norm_le_right F hζ S₀ η hJ u.val u.property hσ hξ.ge
      have hwt := mul_le_mul_of_nonneg_left hR (show 0 ≤ A*U^(1/10+ε)*(|q.2.1.im|+2)^m by positivity)
      have hWim : q.2.1.im = p.1.1 := sourcePoissonVertical_im _ _
      exact (h.trans hwt).trans_eq (by rw [hWim]; dsimp only [B]; ring))
  have hh := sourcePoissonTripleScale_source_scales hZ principalProbeSigma (3/1000) (2/5)
  change sourcePoissonTripleScale X Y Z principalProbeSigma (3/1000) (2/5) = _ at hh
  rw [hh] at H
  calc
    _ ≤ _ := H
    _ = (N*G*A*B*D)*Z^(sourceContourExponent principalProbeSigma (3/1000) (2/5))*U^(1/10+ε) := by
      dsimp only [G]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hU.le _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ.le _)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right zero_le_one) hG.le) hA.le) hB.le) hD.le

theorem exists_sourceContinuedPoissonRow_far_z_dyadic_bound
    (hcut : principalAngularCutoff F J ⊆ S) (v : InfinitePlace F) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : {a : R // a ≠ 0}), (¬ ∃ x : F, x^6 = (u.val : F)) →
      ∀ U : ℝ, 0 < U → U ≤ sourcePoissonFrequencyNorm F S₀ u → sourcePoissonFrequencyNorm F S₀ u ≤ 2*U →
      ∀ Z : ℝ, 0 < Z →
        ‖I v u (Z^(9/10 : ℝ)) (Z^(133/1000 : ℝ)) Z 4 4 2‖ ≤
          C*Z^(sourceContourExponent 4 4 350000)*U^(ε-350000) := by
  obtain ⟨A, hA, hAmp⟩ := exists_sourceRowEulerContinuation_dyadic_right_bound F hζ S₀ η hJ hcut
    4 (2/5) (by norm_num) (by norm_num) ε hε
  obtain ⟨D, hD, hW⟩ := exists_sourceProbeContourWeights_inverse_quadratic F S₀ hζ v 4 350000 (by norm_num) 0
  let G := Real.exp ((4+(350000 : ℝ)-1)^2)
  have hG : 0 < G := Real.exp_pos _
  have hN : 0 ≤ N := mul_nonneg (norm_nonneg _) sourcePoissonInverseQuadraticMass_nonneg
  refine ⟨(N+1)*G*A*D, by positivity, ?_⟩
  intro u hu U hU hlo hhi Z hZ
  let X := Z^(9/10 : ℝ)
  let Y := Z^(133/1000 : ℝ)
  have hX : 0 < X := Real.rpow_pos_of_pos hZ _
  have hY : 0 < Y := Real.rpow_pos_of_pos hZ _
  have hQ := sourcePoissonFrequencyNorm_eq_exterior F S₀ hζ u
  rw [hQ] at hlo hhi
  rw [sourceContinuedPoissonRowIntegral_far_z F S₀ hζ η hJ hcut v u hu hX hY hZ]
  have H := sourceContinuedPoissonRowIntegral_norm_le_of_amplitude F S₀ hζ η hJ hcut v u hu hX hY hZ
    4 4 350000 (by norm_num) (by norm_num) (by norm_num) 0 (A*U^(ε-350000)) D (by positivity) hW (by
      intro p
      dsimp only
      let q : ProbeCoordinates := (sourcePoissonVertical 4 p.2,
        sourcePoissonVertical 4 p.1.1, sourcePoissonVertical 350000 p.1.2)
      have hξ : q.1.re = 4 := sourcePoissonVertical_re _ _
      have hw : q.2.1.re = 4 := sourcePoissonVertical_re _ _
      have hz : q.2.2.re = 350000 := sourcePoissonVertical_re _ _
      have hreg := sourceRightRowPoint_mem q (by rw [hξ]; norm_num) (by rw [hw]; norm_num) (by rw [hz]; norm_num)
      have h := hAmp u.val u.property U hU hlo hhi q hreg hξ.ge hw.ge (by rw [hz]; norm_num)
      rw [← Complex.ofReal_natCast, ← hQ, hz] at h
      simpa only [pow_zero,mul_one] using h)
  have hh := sourcePoissonTripleScale_source_scales hZ 4 4 350000
  change sourcePoissonTripleScale X Y Z 4 4 350000 = _ at hh
  rw [hh] at H
  calc
    _ ≤ _ := H
    _ = (N*G*A*D)*Z^(sourceContourExponent 4 4 350000)*U^(ε-350000) := by dsimp only [G]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hU.le _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ.le _)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hG.le) hA.le) hD.le

end
end ArtinMatthews.SourceEulerAssembly
