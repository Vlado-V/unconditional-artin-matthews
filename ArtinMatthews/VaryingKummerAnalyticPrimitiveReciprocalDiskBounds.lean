module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealLog
public import ArtinMatthews.VaryingKummerAnalyticRayIdealPrimitiveContinuation
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCriticalBound
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

/-! Genuine inputs to local logarithmic control: the actual primitive
function has a uniform polynomial bound on the relevant disks, and its
actual Euler logarithm is uniformly bounded on the inner disks. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Metric Set
open scoped NumberField nonZeroDivisors Classical
noncomputable section

def primitiveDiskCenter (t : ℝ) : ℂ := 2+(t : ℂ)*I
def primitiveDiskComplexity (U t : ℝ) : ℝ := 2*U*(3+|t|)^2

theorem primitiveDiskComplexity_ge_exp {U : ℝ} (hU : 1 ≤ U) (t : ℝ) :
    Real.exp 1 ≤ primitiveDiskComplexity U t :=
  OAI.SevenEighths.LogarithmicControl.conductor_height_scale_ge_exp U t hU

theorem primitiveDiskComplexity_bounds {U : ℝ} (hU : 1 ≤ U) (t : ℝ) :
    U ≤ primitiveDiskComplexity U t ∧ |t|+4 ≤ primitiveDiskComplexity U t := by
  have hx := abs_nonneg t
  have hsq : 1 ≤ 2*(3+|t|)^2 := by nlinarith
  have hsq' : |t|+4 ≤ 2*(3+|t|)^2 := by nlinarith
  constructor
  · dsimp [primitiveDiskComplexity]
    nlinarith [mul_le_mul_of_nonneg_left hsq (zero_le_one.trans hU)]
  · dsimp [primitiveDiskComplexity]
    have H := mul_le_mul_of_nonneg_right hU (show 0 ≤ 2*(3+|t|)^2 by positivity)
    nlinarith

theorem primitiveDiskCoordinateBounds (t R : ℝ) {z : ℂ}
    (hz : z ∈ closedBall (primitiveDiskCenter t) R) :
    |z.re-2| ≤ R ∧ |z.im-t| ≤ R := by
  have hn : ‖z-primitiveDiskCenter t‖ ≤ R := by simpa only [mem_closedBall,dist_eq_norm] using hz
  have hre := (Complex.abs_re_le_norm (z-primitiveDiskCenter t)).trans hn
  have him := (Complex.abs_im_le_norm (z-primitiveDiskCenter t)).trans hn
  constructor
  · simpa [primitiveDiskCenter] using hre
  · simpa [primitiveDiskCenter] using him

theorem exists_primitiveContinued_disk_power_bound
    (K : Type*) [Field K] [NumberField K] :
    ∃ p : ℝ, 1 ≤ p ∧ ∀ U : ℝ, 1 ≤ U →
      ∀ {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
        (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
        (_hnp : ψ.IsNonprincipal), (Ideal.absNorm M : ℝ) ≤ U →
        ∀ (t : ℝ) (z : ℂ), z ∈ closedBall (primitiveDiskCenter t) (3/2) →
          ‖ψ.primitiveContinued hM hprim z‖ ≤ (primitiveDiskComplexity U t)^p := by
  obtain ⟨C,m,hC,hbound⟩ := exists_primitiveContinued_halfplane_polynomial_bound K
  obtain ⟨p,hp,hpbound⟩ := OAI.SevenEighths.LogarithmicControl.absorb_polynomial_constant
    (K := C) (p := (3/8 : ℝ)+(m : ℝ)) (by positivity)
  refine ⟨p,hp,?_⟩
  intro U hU M ψ hM hprim hnp hMU t z hz
  obtain ⟨hre,him⟩ := primitiveDiskCoordinateBounds t (3/2) hz
  have hzre : (1/2 : ℝ) ≤ z.re := by have H := abs_le.mp hre; linarith
  have him' : |z.im|+2 ≤ |t|+4 := by
    have H : |z.im| ≤ |z.im-t|+|t| := by
      simpa only [sub_add_cancel] using abs_add_le (z.im-t) t
    linarith
  have hc := primitiveDiskComplexity_bounds hU t
  have hcpos : 0 < primitiveDiskComplexity U t := zero_lt_one.trans_le (hU.trans hc.1)
  have H := hbound ψ hM hprim hnp z hzre
  calc
    _ ≤ C*(primitiveDiskComplexity U t)^(3/8 : ℝ)*(primitiveDiskComplexity U t)^m := by
      apply H.trans
      gcongr
      · exact hMU.trans hc.1
      · exact him'.trans hc.2
    _ = C*(primitiveDiskComplexity U t)^((3/8 : ℝ)+(m : ℝ)) := by
      rw [mul_assoc,← Real.rpow_natCast,← Real.rpow_add hcpos]
    _ ≤ _ := hpbound _ (primitiveDiskComplexity_ge_exp hU t)

theorem exists_primitive_eulerLog_inner_disk_bound
    (K : Type*) [Field K] [NumberField K] :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M)
      (t : ℝ) (z : ℂ), z ∈ closedBall (primitiveDiskCenter t) (1/2) →
        ‖ψ.eulerLog z‖ ≤ A := by
  refine ⟨max 1 ((Module.finrank ℚ K : ℝ)*dedekindEulerLogConstant),le_max_left _ _,?_⟩
  intro M ψ t z hz
  obtain ⟨hre,_⟩ := primitiveDiskCoordinateBounds t (1/2) hz
  have hzre : (5/4 : ℝ) ≤ z.re := by have H := abs_le.mp hre; linarith
  exact (ψ.eulerLog_norm_le hzre).trans (le_max_right _ _)

end
end ArtinMatthews.VaryingKummerAnalytic
