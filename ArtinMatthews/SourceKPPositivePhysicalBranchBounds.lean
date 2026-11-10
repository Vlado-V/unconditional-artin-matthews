module

public import ArtinMatthews.SourceKPPhysicalBranch
public import ArtinMatthews.ReflectionCoefficientBeforeGaussian
public import ArtinMatthews.ReflectionCoefficientConvergence
public import ArtinMatthews.SourcePrimeNormSummability
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
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
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

/-! Uniform fixed-row bounds for the literal finite branch amplitude. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain QuadraticWeil VaryingKummerAnalytic AllowedGenerators
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "S" => sourceHilbertSet K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "PE" => SourceExteriorPrime K S₀
local notation "R[" P "]" => (𝓞 K) ⧸ HeightOneSpectrum.asIdeal (Subtype.val P)
local notation "C₀" => sourceReflectionTameFourierCoefficient K hζ S₀

private theorem residueCharacterPower_norm_le_one (P : PE) (j : Fin 6) (a : R[P]) :
    ‖(reflectionPrimeCharacters K hζ S₀ P ^ j.val : MulChar R[P] ℂ) a‖ ≤ 1 := by
  letI : P.val.asIdeal.IsMaximal := P.val.isMaximal
  letI : Field R[P] := Ideal.Quotient.field _
  letI : Finite R[P] := Ring.HasFiniteQuotients.finiteQuotient P.val.ne_bot
  letI : Fintype R[P] := Fintype.ofFinite _
  by_cases ha : a = 0
  · simp only [ha, MulChar.map_zero, norm_zero, zero_le_one]
  · exact le_of_eq (Complex.norm_eq_one_of_mem_rootsOfUnity
      ((reflectionPrimeCharacters K hζ S₀ P ^ j.val).apply_mem_rootsOfUnity (Units.mk0 a ha)))

private theorem tameFourierZero_norm_le_one (P : PE) (j : Fin 6) :
    ‖C₀ P j 0‖ ≤ 1 := by
  rw [sourceReflectionTameFourierCoefficient_zero]
  split_ifs
  · have hq : (1 : ℝ) ≤ (Ideal.absNorm P.val.asIdeal : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.val.ne_bot)
    have hq' : 0 ≤ (Ideal.absNorm P.val.asIdeal : ℝ)⁻¹ := inv_nonneg.mpr (zero_le_one.trans hq)
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr (inv_le_one_of_one_le₀ hq))]
    exact sub_le_self _ hq'
  · exact norm_zero.trans_le zero_le_one

theorem sourceReflectionPositiveTwistBranchFactor_norm_le (e : E) (active : Finset PE)
    (x : sourceRing K S₀) :
    ‖sourceReflectionPositiveTwistBranchFactor K hζ S₀ e active x‖ ≤ (2 : ℝ) ^ e.support.card := by
  unfold sourceReflectionPositiveTwistBranchFactor sourceReflectionPositiveTwistBranchFactorAt
  rw [norm_prod]
  calc
    _ ≤ ∏ _P : e.support, (2 : ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro P _
      dsimp only
      split_ifs
      · refine (norm_sub_le _ _).trans ?_
        calc
          _ ≤ 1 + 1 := add_le_add (residueCharacterPower_norm_le_one K hζ S₀ P.val _ _)
            (tameFourierZero_norm_le_one K hζ S₀ P.val _)
          _ = 2 := by norm_num
      · exact (tameFourierZero_norm_le_one K hζ S₀ P.val _).trans (by norm_num)
    _ = _ := by simp

variable [IsTotallyComplex K] {J : Ideal (𝓞 K)}
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (η : EvenIdealRayCharacter K J)
local notation "C" => ReflectionSquarefreeExponents K S₀
local notation "N" => sourcePrimeExponentNorm K S₀
local notation "A" => sourceKPPositivePhysicalBranchAmplitude K hζ S₀ hS η
local notation "r[" u "]" => sourceExteriorUnitToSourceRing K S₀ (sourceExteriorUnitSixthRepresentative S u)

include hS

theorem sourceKPPositivePhysicalBranchAmplitude_norm_le (e : E) (u : ExteriorUnitSixthClasses S)
    (active : Finset PE) (c : C) (n : E) : ‖A e u active c n‖ ≤ (2 : ℝ) ^ e.support.card := by
  let a := reflectionCoefficientBeforeGaussian K hζ S₀ hS η c n r[u]
  let g := sourceReflectionPositiveTwistBranchFactor K hζ S₀ e active
    (sourcePrimeExponentGenerator K hζ S₀ (c.val + 3 • n))
  have h : A e u active c n = a * g := by
    dsimp only [sourceKPPositivePhysicalBranchAmplitude, a, reflectionCoefficientBeforeGaussian, g]
    ac_rfl
  rw [h,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg g)
    (reflectionCoefficientBeforeGaussian_norm_le_one K hζ S₀ hS η c n r[u])).trans
    (sourceReflectionPositiveTwistBranchFactor_norm_le K hζ S₀ e active _)

theorem sourceKPPositivePhysicalBranchAmplitude_dirichlet_summable
    (e : E) (u : ExteriorUnitSixthClasses S) (active : Finset PE) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun i : C × E =>
      ‖A e u active i.1 i.2‖ * (N (i.1.val + 3 • i.2) : ℝ) ^ (-σ)) := by
  have hN := sourcePrimeExponentNorm_summable K S₀ hσ
  have hC : Summable (fun c : C => (N c.val : ℝ) ^ (-σ)) :=
    hN.subtype (fun c => ∀ P, c P ≤ 1)
  have hs : Summable (fun i : C × E => (N i.1.val : ℝ) ^ (-σ) * (N i.2 : ℝ) ^ (-σ)) :=
    summable_mul_of_summable_norm hC.norm hN.norm
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (hs.mul_left ((2 : ℝ) ^ e.support.card))
  intro i
  have hc : 0 < (N i.1.val : ℝ) := Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos K S₀ _)
  have hn : 0 < (N i.2 : ℝ) := Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos K S₀ _)
  have hA := Real.rpow_le_rpow_of_nonpos (mul_pos hc hn)
    (reflectionExponentNorm_cube_ge_product K S₀ i.1.val i.2) (show -σ ≤ 0 by linarith)
  rw [Real.mul_rpow hc.le hn.le] at hA
  exact mul_le_mul (sourceKPPositivePhysicalBranchAmplitude_norm_le K hζ S₀ hS η e u active i.1 i.2)
    hA (by positivity) (by positivity)

end
end ArtinMatthews
