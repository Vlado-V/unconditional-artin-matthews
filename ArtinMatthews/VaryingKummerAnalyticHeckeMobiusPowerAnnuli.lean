module

public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusFiniteDetector
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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! A finite partition of the literal detector into narrow norm annuli.
The 144 annuli have successive endpoints U^(2+j/16). Their number is
independent of U, and their ratio is U^(1/16). -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section

def finiteNormAnnulus {ι : Type*} (S : Finset ι) (N : ι → ℝ) (a b : ℝ) (v : ι → ℂ) : ℂ :=
  ∑ i ∈ S.filter (fun i => a < N i ∧ N i ≤ b), v i

theorem finiteNormAnnulus_eq_sub {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (v : ι → ℂ) {a b : ℝ} (hab : a ≤ b) :
    finiteNormAnnulus S N a b v =
      (∑ i ∈ S.filter (fun i => N i ≤ b), v i) -
        ∑ i ∈ S.filter (fun i => N i ≤ a), v i := by
  unfold finiteNormAnnulus
  simp only [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases ha : N i ≤ a
  · have hb := ha.trans hab
    simp [ha,hb,not_lt.mpr ha]
  · by_cases hb : N i ≤ b
    · simp [ha,hb,lt_of_not_ge ha]
    · simp [ha,hb]

theorem finiteNormAnnulus_telescope {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (v : ι → ℂ) (b : ℕ → ℝ) (hb : Monotone b) (n : ℕ) :
    (∑ j ∈ Finset.range n, finiteNormAnnulus S N (b j) (b (j+1)) v) =
      finiteNormAnnulus S N (b 0) (b n) v := by
  let P (j : ℕ) := ∑ i ∈ S.filter (fun i => N i ≤ b j), v i
  calc
    _ = ∑ j ∈ Finset.range n, (P (j+1)-P j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact finiteNormAnnulus_eq_sub S N v (hb (Nat.le_succ j))
    _ = P n-P 0 := Finset.sum_range_sub P n
    _ = _ := (finiteNormAnnulus_eq_sub S N v (hb (Nat.zero_le n))).symm

def mobiusPowerBoundary (U : ℝ) (j : ℕ) : ℝ := U^(2+(j : ℝ)/16)

theorem mobiusPowerBoundary_monotone {U : ℝ} (hU : 1 ≤ U) : Monotone (mobiusPowerBoundary U) := by
  intro j k hjk
  change U^(2+(j : ℝ)/16) ≤ U^(2+(k : ℝ)/16)
  apply Real.rpow_le_rpow_of_exponent_le hU
  have hjk' : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
  linarith

theorem mobiusPowerBoundary_endpoints (U : ℝ) :
    mobiusPowerBoundary U 0 = U^2 ∧ mobiusPowerBoundary U 144 = U^11 := by
  norm_num [mobiusPowerBoundary,Real.rpow_natCast]

namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M)

def mobiusPowerAnnulus (U : ℝ) (ρ : ℂ) (j : ℕ) : ℂ :=
  finiteNormAnnulus (HeckeIdealMobius.normCutoff K (U^11))
    (fun I => (Ideal.absNorm I : ℝ)) (mobiusPowerBoundary U j) (mobiusPowerBoundary U (j+1))
    (fun I => ψ.mobiusConvolutionCoefficient (U^2) I*(Ideal.absNorm I : ℂ)^(-ρ)*
      Complex.exp (-(Ideal.absNorm I : ℂ)/((U^10 : ℝ) : ℂ)))

theorem mobiusSmoothedPolynomial_eq_powerAnnuli {U : ℝ} (hU : 1 ≤ U) (ρ : ℂ) :
    ψ.mobiusSmoothedPolynomial (U^2) ρ (U^10) (U^11) =
      ∑ j ∈ Finset.range 144, ψ.mobiusPowerAnnulus U ρ j := by
  simp_rw [mobiusPowerAnnulus]
  rw [finiteNormAnnulus_telescope _ _ _ _ (mobiusPowerBoundary_monotone hU)]
  rw [(mobiusPowerBoundary_endpoints U).1,(mobiusPowerBoundary_endpoints U).2]
  unfold mobiusSmoothedPolynomial finiteNormAnnulus
  apply Finset.sum_congr
  · ext I
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hI,hN⟩
      exact ⟨hI,hN,(HeckeIdealMobius.mem_normCutoff K (pow_nonneg (zero_le_one.trans hU) 11) I).mp hI⟩
    · rintro ⟨hI,hN,_⟩
      exact ⟨hI,hN⟩
  · intro _ _
    rfl

theorem exists_large_mobiusPowerAnnulus {U : ℝ} (hU : 1 ≤ U) (ρ : ℂ)
    (hlarge : 1/8 ≤ ‖ψ.mobiusSmoothedPolynomial (U^2) ρ (U^10) (U^11)‖) :
    ∃ j : ℕ, j < 144 ∧ 1/1152 ≤ ‖ψ.mobiusPowerAnnulus U ρ j‖ := by
  by_contra hn
  push Not at hn
  have hs : (∑ j ∈ Finset.range 144, ‖ψ.mobiusPowerAnnulus U ρ j‖) <
      ∑ _j ∈ Finset.range 144, (1/1152 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro j hj
      exact (hn j (Finset.mem_range.mp hj)).le
    · exact ⟨0,by simp,hn 0 (by norm_num)⟩
  norm_num at hs
  rw [ψ.mobiusSmoothedPolynomial_eq_powerAnnuli hU ρ] at hlarge
  have H := norm_sum_le (Finset.range 144) (fun j => ψ.mobiusPowerAnnulus U ρ j)
  linarith

end EvenIdealRayCharacter

end
end ArtinMatthews.VaryingKummerAnalytic
