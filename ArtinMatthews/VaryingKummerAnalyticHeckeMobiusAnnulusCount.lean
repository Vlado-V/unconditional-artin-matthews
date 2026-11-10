module

public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusClassPolynomial
public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusDensityExponent
public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusRectangleCount
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

/-! Exact norm-annulus conversion and its genuine U^(2/5) large-value
count over arbitrary finite primitive coefficient families. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal Complex Set
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem finiteNormAnnulus_normCutoff_eq {L R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B) (hRB : R ≤ B)
    (v : Ideal (𝓞 K) → ℂ) :
    finiteNormAnnulus (HeckeIdealMobius.normCutoff K B) (fun I => (Ideal.absNorm I : ℝ)) L R v =
      finiteNormAnnulus (HeckeIdealMobius.normCutoff K R) (fun I => (Ideal.absNorm I : ℝ)) L R v := by
  unfold finiteNormAnnulus
  apply Finset.sum_congr
  · ext I
    simp only [Finset.mem_filter,HeckeIdealMobius.mem_normCutoff K hR I,
      HeckeIdealMobius.mem_normCutoff K hB I]
    constructor
    · rintro ⟨_,hL,hI⟩
      exact ⟨hI,hL,hI⟩
    · rintro ⟨hI,hL,_⟩
      exact ⟨hI.trans hRB,hL,hI⟩
  · intro _ _
    rfl

namespace EvenIdealRayCharacter
variable {K} {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M)

theorem mobiusPowerAnnulus_eq_classPolynomial {U : ℝ} (hU : 1 ≤ U) (ρ : ℂ)
    {j : ℕ} (hj : j < 144) :
    ψ.mobiusPowerAnnulus U ρ j =
      coefficientClassDirichletPolynomial K ψ.coefficient
        (heckeClassNormAnnulus K (mobiusPowerBoundary U j) (mobiusPowerBoundary U (j+1)))
        (mobiusSmoothedClassWeight K (U^2) (U^10)) ρ.re ρ.im := by
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hR : 0 ≤ mobiusPowerBoundary U (j+1) := Real.rpow_nonneg hU0.le _
  have H := ψ.mobiusClassPolynomial_eq_finiteNormAnnulus (U^2) (U^10)
    (mobiusPowerBoundary U j) (mobiusPowerBoundary U (j+1)) ρ.re ρ.im hR
  rw [Complex.re_add_im] at H
  rw [mobiusPowerAnnulus,finiteNormAnnulus_normCutoff_eq K hR (pow_nonneg hU0.le _)
    (mobiusPowerBoundary_bounds hU hj).2.2]
  exact H.symm

end EvenIdealRayCharacter

theorem exists_actual_mobius_annulus_count :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U → ∀ r : ℝ, r ≤ 1/10 → ∀ j : ℕ, j < 144 →
      ∀ (T : Finset (IdealConductorModulus K))
        (A : ∀ M : IdealConductorModulus K, Finset (EvenIdealRayCharacter K M.val)),
        (∀ M ∈ T, (Ideal.absNorm M.val : ℝ) ≤ U) →
        (∀ M ∈ T, ∀ ψ ∈ A M, IsPrimitiveOnIdeals ψ.residue) →
        (∑ M ∈ T, (((A M).image (fun ψ => ψ.coefficient)).filter
          (fun a => ∃ σ t : ℝ, σ ∈ Icc (249/250) 1 ∧ |t| ≤ 4*U^r ∧
            1/1152 ≤ ‖coefficientClassDirichletPolynomial K a
              (heckeClassNormAnnulus K (mobiusPowerBoundary U j) (mobiusPowerBoundary U (j+1)))
              (mobiusSmoothedClassWeight K (U^2) (U^10)) σ t‖)).card : ℝ) ≤ C*U^(2/5 : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := exists_actual_mobius_smoothed_rectangle_count K (1/10000) (by norm_num)
  let A₀ : ℝ := C*(1+2*((1 : ℝ)-249/250))/(1/1152 : ℝ)^2
  have hA₀ : 0 < A₀ := by dsimp [A₀]; positivity
  refine ⟨A₀*(34*(1210001 : ℝ)^2),mul_pos hA₀ (by norm_num),?_⟩
  intro U hU r hr j hj T A hT hA
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hb := mobiusPowerBoundary_bounds hU hj
  have hX : 1 ≤ mobiusPowerBoundary U (j+1) := (one_le_pow₀ hU).trans (hb.1.trans hb.2.1)
  have hZ : 0 < mobiusPowerBoundary U j := Real.rpow_pos_of_pos hU0 _
  let B := heckeClassNormAnnulus K (mobiusPowerBoundary U j) (mobiusPowerBoundary U (j+1))
  have hupper (c) (J) (hJ : J ∈ B c) :
      (FractionalIdeal.absNorm J.val.val : ℝ) ≤ mobiusPowerBoundary U (j+1) :=
    (mem_heckeClassNormCutoff K (Real.rpow_nonneg hU0.le _) c J).mp (Finset.mem_filter.mp hJ).1
  have hlower (c) (J) (hJ : J ∈ B c) :
      mobiusPowerBoundary U j ≤ (FractionalIdeal.absNorm J.val.val : ℝ) :=
    (Finset.mem_filter.mp hJ).2.le
  have H := hbound (U^2) (U^10) (249/250) 1 (mobiusPowerBoundary U (j+1)) U
    (4*U^r) (mobiusPowerBoundary U j) (1/1152) (pow_pos hU0 _) (by norm_num) hX hU
    (by positivity) hZ (by norm_num) (by norm_num) T A B hT hA hlower hupper
  apply H.trans
  have Hcost := mul_le_mul_of_nonneg_left (mobius_norm_height_log_cost hU hr hj) hA₀.le
  convert Hcost using 1 <;> dsimp [A₀] <;> ring_nf

end
end ArtinMatthews.VaryingKummerAnalytic
