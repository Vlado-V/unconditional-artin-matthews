module

public import ArtinMatthews.VaryingKummerAnalyticPrimitiveReciprocal
public import ArtinMatthews.PrincipalAngularCorrection
public import OAI.NumberTheory.DirichletL.ContinuationInversion
public import ArtinMatthews.ProbeIdealSourceRegions
public import ArtinMatthews.VaryingKummerAnalyticHeckeFiniteEulerBounds
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import OAI.NumberTheory.DirichletL.ContinuationContour
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The source amplitude exp((s-5/6)^2) H_eta(s) / L^S(s,eta).
The finite Euler deletion is literal, and the right-line bounds apply
to every finite ideal-ray character, including the principal character. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set Filter Complex
open OAI.SevenEighths.Continuation
open scoped NumberField Classical Topology FourierTransform BigOperators
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {ζ : K} {M : Ideal (𝓞 K)}

def principalAngularRayEulerFactor (η : EvenIdealRayCharacter K M)
    (S : Finset (ArtinMatthews.ProbePrime K)) (s : ℂ) : ℂ :=
  ∏ P ∈ S, (1 - η.allCoefficient P.asIdeal * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))

theorem principalAngularRayEulerFactor_entire (η : EvenIdealRayCharacter K M)
    (S : Finset (ArtinMatthews.ProbePrime K)) :
    Differentiable ℂ (principalAngularRayEulerFactor η S) := by
  unfold principalAngularRayEulerFactor
  apply Differentiable.fun_finsetProd
  intro P _
  apply Differentiable.const_sub
  apply Differentiable.const_mul
  exact differentiable_id.neg.const_cpow (Or.inl (by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot))

theorem principalAngularRayEulerFactor_ne_zero (η : EvenIdealRayCharacter K M)
    (S : Finset (ArtinMatthews.ProbePrime K)) {s : ℂ} (hs : 0 < s.re) :
    principalAngularRayEulerFactor η S s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro P _
  have hQ := probeIdealPrime_norm_gt_one K P
  have hn : ‖η.allCoefficient P.asIdeal * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, ← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.neg_re]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) _)
      (η.allCoefficient_norm_le_one P.asIdeal)).trans_lt
        (Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith))
  intro he
  rw [← sub_eq_zero.mp he, norm_one] at hn
  exact (lt_irrefl _ hn)

theorem principalAngularRayEulerFactor_inv_norm_le (η : EvenIdealRayCharacter K M)
    (S : Finset (ArtinMatthews.ProbePrime K)) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖(principalAngularRayEulerFactor η S s)⁻¹‖ ≤ (4 : ℝ) ^ S.card := by
  rw [principalAngularRayEulerFactor, ← Finset.prod_inv_distrib, norm_prod]
  calc
    _ ≤ ∏ _P ∈ S, (4 : ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro P _
      have hn : 2 ≤ (Ideal.absNorm P.asIdeal : ℝ) := by
        have h : 1 < Ideal.absNorm P.asIdeal := by exact_mod_cast probeIdealPrime_norm_gt_one K P
        have h' : 2 ≤ Ideal.absNorm P.asIdeal := by omega
        exact_mod_cast h'
      exact (norm_one_sub_euler_ratio_bounds hn hs (η.allCoefficient_norm_le_one P.asIdeal)).2
    _ = _ := by simp

def principalAngularExteriorL (η : EvenIdealRayCharacter K M)
    (S : Finset (ArtinMatthews.ProbePrime K)) (s : ℂ) : ℂ :=
  η.dirichlet s * principalAngularRayEulerFactor η S s

theorem principalAngularExteriorL_differentiableOn (η : EvenIdealRayCharacter K M)
    (S : Finset (ArtinMatthews.ProbePrime K)) :
    DifferentiableOn ℂ (principalAngularExteriorL η S) {s : ℂ | 1 < s.re} :=
  η.dirichlet_differentiableOn.mul (principalAngularRayEulerFactor_entire η S).differentiableOn

theorem principalAngularExteriorL_ne_zero (η : EvenIdealRayCharacter K M)
    (S : Finset (ArtinMatthews.ProbePrime K)) {s : ℂ} (hs : 1 < s.re) :
    principalAngularExteriorL η S s ≠ 0 :=
  mul_ne_zero (η.dirichlet_ne_zero hs) (principalAngularRayEulerFactor_ne_zero η S (by linarith))

theorem principalAngularExteriorL_inv_norm_le (η : EvenIdealRayCharacter K M)
    (S : Finset (ArtinMatthews.ProbePrime K)) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖(principalAngularExteriorL η S s)⁻¹‖ ≤ primitiveReciprocalBound K * (4 : ℝ) ^ S.card := by
  rw [principalAngularExteriorL, mul_inv_rev, norm_mul]
  calc
    _ ≤ (4 : ℝ) ^ S.card * primitiveReciprocalBound K :=
      mul_le_mul (principalAngularRayEulerFactor_inv_norm_le η S (by linarith))
        (η.dirichlet_inv_norm_le (by linarith)) (norm_nonneg _) (by positivity)
    _ = _ := by ring

def principalAngularGaussianAmplitude (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K)) (s : ℂ) : ℂ :=
  Complex.exp ((s - 5 / 6) ^ 2) *
    (principalAngularCorrection hζ η S s * (principalAngularExteriorL η S s)⁻¹)

theorem principalAngularGaussianAmplitude_differentiableAt (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : principalAngularCutoff K M ⊆ S) {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (principalAngularGaussianAmplitude hζ η S) s := by
  have hr : 99799 / 100000 < s.re := by linarith
  have hL := (principalAngularExteriorL_differentiableOn η S s hs).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  exact (((differentiable_id.sub_const (5 / 6 : ℂ)).pow 2).cexp.differentiableAt).mul
    (((principalAngularCorrection_analyticOnNhd hζ η S hS) s hr).differentiableAt.mul
      (hL.inv (principalAngularExteriorL_ne_zero η S hs)))

theorem principalAngularGaussianAmplitude_continuous_line (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : principalAngularCutoff K M ⊆ S) (a : ℝ) (ha : 1 < a) :
    Continuous (fun y : ℝ => principalAngularGaussianAmplitude hζ η S ((a : ℂ) + y * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  exact (principalAngularGaussianAmplitude_differentiableAt hζ η S hS
    (s := (a : ℂ) + y * I) (by simpa using ha)).continuousAt.comp
      (f := fun v : ℝ => (a : ℂ) + v * I) (by fun_prop)

theorem principalAngularGaussianAmplitude_norm_bound (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : principalAngularCutoff K M ⊆ S) (a y : ℝ) (ha : 2 ≤ a) :
    ‖principalAngularGaussianAmplitude hζ η S ((a : ℂ) + y * I)‖ ≤
      (Real.exp ((a - 5 / 6) ^ 2) * probeGoodProductUniformBound K *
        primitiveReciprocalBound K * (4 : ℝ) ^ S.card) * Real.exp (-(y ^ 2)) := by
  let F := fun s => principalAngularCorrection hζ η S s * (principalAngularExteriorL η S s)⁻¹
  have hn := norm_gaussianContourIntegrand F 0 a y (Z := 1) zero_lt_one
  simp only [gaussianContourIntegrand, Complex.ofReal_one, Complex.ofReal_zero,
    add_zero, Complex.one_cpow, one_mul, Real.one_rpow] at hn
  change ‖principalAngularGaussianAmplitude hζ η S ((a : ℂ) + y * I)‖ = _ at hn
  rw [hn]
  have hF : ‖F ((a : ℂ) + y * I)‖ ≤
      probeGoodProductUniformBound K * (primitiveReciprocalBound K * (4 : ℝ) ^ S.card) := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul (principalAngularCorrection_norm_le hζ η S hS (by norm_num; linarith))
      (principalAngularExteriorL_inv_norm_le η S (by simpa using ha))
      (norm_nonneg _) (probeGoodProductUniformBound_pos K).le
  calc
    _ ≤ (Real.exp ((a - 5 / 6) ^ 2) *
        (probeGoodProductUniformBound K * (primitiveReciprocalBound K * (4 : ℝ) ^ S.card))) *
        Real.exp (-(y ^ 2)) := by gcongr
    _ = _ := by ring

theorem principalAngularGaussianAmplitude_integrable_line (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K))
    (hS : principalAngularCutoff K M ⊆ S) (a : ℝ) (ha : 2 ≤ a) :
    Integrable (fun y : ℝ => principalAngularGaussianAmplitude hζ η S ((a : ℂ) + y * I)) :=
  integrable_of_gaussian_bound _ _
    (principalAngularGaussianAmplitude_continuous_line hζ η S hS a (by linarith)).aestronglyMeasurable
    (fun y => principalAngularGaussianAmplitude_norm_bound hζ η S hS a y ha)

def principalAngularGaussianSignal (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K)) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-8 / 15 : ℂ) *
    mellinInv (-2) (fun s => principalAngularGaussianAmplitude hζ η S (-s)) x

theorem principalAngularGaussianSignal_normalized (hζ : IsPrimitiveRoot ζ 12)
    (η : EvenIdealRayCharacter K M) (S : Finset (ArtinMatthews.ProbePrime K))
    {x : ℝ} (hx : 0 < x) :
    normalizedSignal (principalAngularGaussianSignal hζ η S) (-8 / 15) x =
      mellinInv (-2) (fun s => principalAngularGaussianAmplitude hζ η S (-s)) x := by
  unfold normalizedSignal principalAngularGaussianSignal
  simp only [smul_eq_mul, ← mul_assoc]
  have hcast : ((-8 / 15 : ℝ) : ℂ) = (-8 / 15 : ℂ) := by norm_num
  simp only [hcast]
  rw [Complex.cpow_neg, inv_mul_cancel₀]
  · simp
  · exact (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [hx.ne'])

end
end ArtinMatthews.VaryingKummerAnalytic
