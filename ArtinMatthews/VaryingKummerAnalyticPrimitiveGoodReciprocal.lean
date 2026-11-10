module

public import ArtinMatthews.VaryingKummerAnalyticPrimitiveReciprocalDiskBounds
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveReciprocal
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import OAI.NumberTheory.DirichletL.LogarithmicControl


set_option backward.privateInPublic true
@[expose] public section

/-! Local subpower reciprocal control obtained from actual Euler logarithms
and actual conductor growth. Its rectangle condition will be discharged by
the complement of the proved primitive exceptional set. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Metric Set
open scoped NumberField nonZeroDivisors Classical
noncomputable section

theorem primitiveDiskComplexity_le_power {U r t : ℝ} (hU : 1 ≤ U)
    (hr0 : 0 ≤ r) (hr : r ≤ 1/10) (ht : |t| ≤ 2*U^r) :
    primitiveDiskComplexity U t ≤ 50*U^2 := by
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hone : 1 ≤ U^r := Real.one_le_rpow hU hr0
  have hbase : 3+|t| ≤ 5*U^r := by linarith
  have hsq : (U^r)^2 ≤ U := by
    rw [← Real.rpow_mul_natCast hU0.le]
    have H := Real.rpow_le_rpow_of_exponent_le hU (show r*(2 : ℝ) ≤ 1 by linarith)
    simpa using H
  have hh := (sq_le_sq₀ (by positivity) (by positivity)).mpr hbase
  dsimp [primitiveDiskComplexity]
  nlinarith [mul_le_mul_of_nonneg_left (show (3+|t|)^2 ≤ 25*U by nlinarith) hU0.le]

theorem exists_primitive_reciprocal_bound_on_zero_free_rectangle
    (K : Type*) [Field K] [NumberField K] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U r : ℝ), 1 ≤ U → 0 < r → r < 1/10 →
      ∀ {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
        (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
        (_hnp : ψ.IsNonprincipal), (Ideal.absNorm M : ℝ) ≤ U →
        (∀ z : ℂ, (249/250 : ℝ) ≤ z.re → |z.im| ≤ 4*U^r →
          ψ.primitiveContinued hM hprim z ≠ 0) →
        ∀ s : ℂ, (499/500 : ℝ) ≤ s.re → |s.im| ≤ 2*U^r →
          ‖(ψ.primitiveContinued hM hprim s)⁻¹‖ ≤ C*U^ε := by
  obtain ⟨A,hA,hInner⟩ := exists_primitive_eulerLog_inner_disk_bound K
  obtain ⟨p,hp,hPoly⟩ := exists_primitiveContinued_disk_power_bound K
  obtain ⟨D,hD,hControl⟩ := OAI.SevenEighths.LogarithmicControl.logarithmic_control
    (e := 1/4000) (A := A) (M := p) (ε := ε/2) (by norm_num) (by norm_num) hA hp (by positivity)
  let C := primitiveReciprocalBound K+D*50^(ε/2)
  have hC : 0 < C := by
    have hbase := primitiveReciprocalBound_pos K
    dsimp [C]
    positivity
  refine ⟨C,hC,?_⟩
  intro U r hU hr0 hr M ψ hM hprim hnp hMU hzero s hs hst
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hu : 1 ≤ U^r := Real.one_le_rpow hU hr0.le
  have hpow : 1 ≤ U^ε := Real.one_le_rpow hU hε.le
  by_cases hsright : (5/4 : ℝ) ≤ s.re
  · have H := ψ.primitiveReciprocal_norm_le hM hprim hnp hsright
    change ‖(ψ.primitiveContinued hM hprim s)⁻¹‖ ≤ primitiveReciprocalBound K at H
    apply H.trans
    have hbase := (primitiveReciprocalBound_pos K).le
    have hDpow : 0 ≤ D*50^(ε/2) := by positivity
    dsimp [C]
    nlinarith
  · let Q := primitiveDiskComplexity U s.im
    let c := primitiveDiskCenter s.im
    let L := ψ.primitiveContinued hM hprim
    let E := ψ.eulerLog
    have hQ : Real.exp 1 ≤ Q := primitiveDiskComplexity_ge_exp hU s.im
    have hLc : DifferentiableOn ℂ L (ball c (2-(249/250 : ℝ)-2*(1/4000))) :=
      (ψ.primitiveContinued_entire hM hprim).differentiableOn
    have hzfree (z : ℂ) (hz : z ∈ ball c (2-(249/250 : ℝ)-2*(1/4000))) : L z ≠ 0 := by
      have hz' : z ∈ closedBall (primitiveDiskCenter s.im) (2-(249/250 : ℝ)-2*(1/4000)) :=
        ball_subset_closedBall hz
      obtain ⟨hre,him⟩ := primitiveDiskCoordinateBounds s.im _ hz'
      have hre' := abs_le.mp hre
      have him' : |z.im| ≤ |z.im-s.im|+|s.im| := by
        simpa only [sub_add_cancel] using abs_add_le (z.im-s.im) s.im
      exact hzero z (by linarith) (by linarith)
    have hpol (z : ℂ) (hz : z ∈ ball c (2-(249/250 : ℝ)-3*(1/4000))) : ‖L z‖ ≤ Q^p := by
      apply hPoly U hU ψ hM hprim hnp hMU s.im z
      exact (closedBall_subset_closedBall (by norm_num : 2-(249/250 : ℝ)-3*(1/4000) ≤ 3/2))
        (ball_subset_closedBall hz)
    have hright (z : ℂ) (hz : z ∈ ball c (1/2)) : 1 < z.re := by
      obtain ⟨hre,_⟩ := primitiveDiskCoordinateBounds s.im (1/2) (ball_subset_closedBall hz)
      have H := abs_le.mp hre
      linarith
    have hEc : DifferentiableOn ℂ E (ball c (1/2)) :=
      ψ.eulerLog_differentiableOn.mono (fun z hz => hright z hz)
    have hEL : EqOn (Complex.exp ∘ E) L (ball c (1/2)) := by
      intro z hz
      change Complex.exp (ψ.eulerLog z) = ψ.primitiveContinued hM hprim z
      rw [ψ.primitiveContinued_eq_dirichlet hM hprim hnp (hright z hz)]
      exact ψ.exp_eulerLog_eq_dirichlet (hright z hz)
    have hEb (z : ℂ) (hz : z ∈ closedBall c (49/100)) : ‖E z‖ ≤ A :=
      hInner ψ s.im z ((closedBall_subset_closedBall (by norm_num : (49/100 : ℝ) ≤ 1/2)) hz)
    have H := (hControl (249/250) Q L E c (by norm_num) (by norm_num) hQ
      hLc hzfree hpol hEc hEL hEb).1
    have hsball : s ∈ closedBall c (2-(249/250 : ℝ)-6*(1/4000)) := by
      have he : s-c = ((s.re-2 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [c,primitiveDiskCenter]
      rw [mem_closedBall,dist_eq_norm,he,Complex.norm_real,Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith,by linarith [lt_of_not_ge hsright]⟩
    have hrec : ‖(L s)⁻¹‖ ≤ D*Q^(ε/2) := by
      have hh := H s hsball
      linarith [norm_nonneg (L s)]
    have hQbound := primitiveDiskComplexity_le_power hU hr0.le hr.le hst
    have he : (50*U^2)^(ε/2) = 50^(ε/2)*U^ε := by
      rw [Real.mul_rpow (by norm_num) (sq_nonneg U),← Real.rpow_natCast_mul hU0.le 2]
      congr 1
      ring_nf
    calc
      _ ≤ D*Q^(ε/2) := hrec
      _ ≤ D*(50*U^2)^(ε/2) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by dsimp [Q,primitiveDiskComplexity]; positivity) hQbound (by positivity)) hD.le
      _ ≤ _ := by
        rw [he]
        have hbase := (primitiveReciprocalBound_pos K).le
        have hUpow := Real.rpow_nonneg hU0.le ε
        dsimp [C]
        nlinarith

end
end ArtinMatthews.VaryingKummerAnalytic
