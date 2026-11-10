module

public import ArtinMatthews.SpectralEisensteinCriticalEnergy
public import ArtinMatthews.SpectralEisensteinTruncatedPairFlux
public import ArtinMatthews.SpectralEisensteinMatchingModes
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
public import Mathlib.RingTheory.SimpleRing.Principal
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


set_option backward.privateInPublic true
@[expose] public section

/-! The literal high constant term of the compact critical combination.
The matched truncated part has zero mean and each upper cutoff contributes
only in its own actual cusp class. -/
noncomputable section
open Set Filter MeasureTheory Matrix
open scoped MatrixGroups
namespace ArtinMatthews

def gamma0EisensteinCriticalMean (N : ℕ) [NeZero N] (i : Gamma0EisensteinCuspClasses N) :
    Gamma0RegionL2 N →L[ℂ] CuspVerticalL2 (N:ℝ) (gamma0EisensteinMatchingHeight N) :=
  gamma0CuspConstantTerm N (gamma0EisensteinCuspClassRepresentative N i)
    (gamma0EisensteinMatchingHeight N) (gamma0EisensteinMatchingHeight_pos N)

def gamma0EisensteinCriticalUpperMode (N : ℕ) [NeZero N] (i : Gamma0EisensteinCuspClasses N) (q : ℂ) :
    CuspVerticalL2 (N:ℝ) (gamma0EisensteinMatchingHeight N) :=
  gamma0EisensteinCriticalMean N i (gamma0EnergyInclusion N (gamma0CuspUpperTruncatedEnergy N
    (gamma0EisensteinCuspClassRepresentative N i) q (gamma0EisensteinFluxScale N)
    (gamma0EisensteinFluxScale_pos N)))

theorem gamma0EisensteinMatchingHeight_width_le (N : ℕ) [NeZero N] (r : SL(2,ℤ)) :
    (gamma0CuspTrueWidth N r:ℝ)≤gamma0EisensteinMatchingHeight N := by
  have h := gamma0EisensteinMatchingHeight_high N r
  have hw : (0:ℝ)<gamma0CuspTrueWidth N r := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  linarith

theorem gamma0EisensteinCriticalMean_upper_diagonal (N : ℕ) [NeZero N]
    (i j : Gamma0EisensteinCuspClasses N) (q : ℂ) :
    gamma0EisensteinCriticalMean N i (gamma0EnergyInclusion N (gamma0CuspUpperTruncatedEnergy N
      (gamma0EisensteinCuspClassRepresentative N j) q (gamma0EisensteinFluxScale N)
      (gamma0EisensteinFluxScale_pos N)))=
      if i=j then gamma0EisensteinCriticalUpperMode N i q else 0 := by
  by_cases h : i=j
  · subst j
    rw [ite_eq_left rfl]
    rfl
  · rw [ite_eq_right h]
    let r := gamma0EisensteinCuspClassRepresentative N
    have hm := gamma0CuspUpperTruncatedEnergy_constant_mode N (r i) (r j) q
      (gamma0EisensteinFluxScale N) (gamma0EisensteinFluxScale_pos N)
      (gamma0EisensteinMatchingHeight N) (gamma0EisensteinMatchingHeight_pos N)
      (gamma0EisensteinMatchingHeight_width_le N (r i))
    have hI : gamma0CuspEisensteinIndicator N (r i) (r j)=0 := by
      rw [gamma0CuspEisensteinIndicator_eq_cuspClass]
      simp only [r,gamma0EisensteinCuspClassRepresentative_class,ite_eq_right h]
    simp only [hI,zero_mul] at hm
    apply Lp.ext
    exact hm.trans (Lp.coeFn_zero ℂ 2 _).symm

theorem gamma0EisensteinCriticalUpperMode_ae (N : ℕ) [NeZero N]
    (i : Gamma0EisensteinCuspClasses N) (q : ℂ) :
    gamma0EisensteinCriticalUpperMode N i q
      =ᵐ[(cuspHorizontalMeasure (N:ℝ) univ) • cuspVerticalMeasure (gamma0EisensteinMatchingHeight N)]
        fun y => eisensteinOutgoingApprox q (gamma0EisensteinFluxScale N)
          (y/(gamma0CuspTrueWidth N (gamma0EisensteinCuspClassRepresentative N i):ℝ)) := by
  let r := gamma0EisensteinCuspClassRepresentative N i
  have hm := gamma0CuspUpperTruncatedEnergy_constant_mode N r r q
    (gamma0EisensteinFluxScale N) (gamma0EisensteinFluxScale_pos N)
    (gamma0EisensteinMatchingHeight N) (gamma0EisensteinMatchingHeight_pos N)
    (gamma0EisensteinMatchingHeight_width_le N r)
  have hI : gamma0CuspEisensteinIndicator N r r=1 := by
    simp [gamma0CuspEisensteinIndicator_eq_cuspClass]
  change gamma0CuspConstantTerm N r (gamma0EisensteinMatchingHeight N)
    (gamma0EisensteinMatchingHeight_pos N) (gamma0EnergyInclusion N
      (gamma0CuspUpperTruncatedEnergy N r q (gamma0EisensteinFluxScale N)
        (gamma0EisensteinFluxScale_pos N))) =ᵐ[_] _
  simpa only [hI,one_mul] using hm

theorem gamma0EisensteinCriticalMean_upper_sum (N : ℕ) [NeZero N]
    (i : Gamma0EisensteinCuspClasses N) (q : ℂ) (c : Gamma0EisensteinCuspClasses N → ℂ) :
    gamma0EisensteinCriticalMean N i (gamma0EnergyInclusion N
      (∑ j,c j • gamma0CuspUpperTruncatedEnergy N (gamma0EisensteinCuspClassRepresentative N j)
        q (gamma0EisensteinFluxScale N) (gamma0EisensteinFluxScale_pos N)))=
        c i • gamma0EisensteinCriticalUpperMode N i q := by
  simp only [map_sum,map_smul,gamma0EisensteinCriticalMean_upper_diagonal]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ h
    rw [ite_eq_right h.symm,smul_zero]
  · simp

theorem gamma0EisensteinCriticalBaseEnergy_mean_zero (N : ℕ) [NeZero N] (s : ℂ)
    (c : Gamma0EisensteinCuspClasses N → ℂ) (i : Gamma0EisensteinCuspClasses N) :
    gamma0EisensteinCriticalMean N i (gamma0EnergyInclusion N (gamma0EisensteinCriticalBaseEnergy N s c))=0 := by
  have hm : gamma0EisensteinCriticalBaseEnergy N s c∈(gamma0EisensteinMatchingForm N).subspace :=
    (gamma0EisensteinMatchingForm N).subspace.sum_mem (fun j _ =>
      (gamma0EisensteinMatchingForm N).subspace.smul_mem _
        (gamma0CuspEisensteinMatchedTruncatedEnergy_mem N _ s))
  exact (gamma0EisensteinMatchingForm_mem_iff N _).mp hm i

theorem gamma0EisensteinCriticalTruncatedEnergy_mean_ae (N : ℕ) [NeZero N] (s : ℂ)
    (c : Gamma0EisensteinCuspClasses N → ℂ) (i : Gamma0EisensteinCuspClasses N) :
    gamma0EisensteinCriticalMean N i
      (gamma0EnergyInclusion N (gamma0EisensteinCriticalTruncatedEnergy N s c))
      =ᵐ[(cuspHorizontalMeasure (N:ℝ) univ) • cuspVerticalMeasure (gamma0EisensteinMatchingHeight N)]
        fun y => eisensteinCriticalTruncatedPair s (gamma0EisensteinFluxScale N) (c i)
          ((gamma0CuspScatteringMatrix N s).mulVec c i)
          (y/(gamma0CuspTrueWidth N (gamma0EisensteinCuspClassRepresentative N i):ℝ)) := by
  let u := gamma0EisensteinCriticalUpperMode N i s
  let v := gamma0EisensteinCriticalUpperMode N i (1-s)
  let b := (gamma0CuspScatteringMatrix N s).mulVec c
  rw [gamma0EisensteinCriticalTruncatedEnergy,map_add,map_add,map_add,map_add,
    gamma0EisensteinCriticalBaseEnergy_mean_zero,zero_add,
    gamma0EisensteinCriticalMean_upper_sum,gamma0EisensteinCriticalMean_upper_sum]
  filter_upwards [Lp.coeFn_add (c i • u) (b i • v),Lp.coeFn_smul (c i) u,Lp.coeFn_smul (b i) v,
    gamma0EisensteinCriticalUpperMode_ae N i s,gamma0EisensteinCriticalUpperMode_ae N i (1-s)]
      with y hAdd hu hv hU hV
  change (c i • u+b i • v) y=_
  rw [hAdd,Pi.add_apply,hu,hv,Pi.smul_apply,Pi.smul_apply,hU,hV]
  rfl

end ArtinMatthews
