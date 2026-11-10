module

public import ArtinMatthews.SourceThetaFiniteMellin
public import ArtinMatthews.StandardLocalBall
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Topology.Algebra.IsOpenUnits
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The retained positive cutoff is the literal principal-unit ball,
with its actual compact-open multiplicative Haar carrier. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain SourcePhysical SourceReflection Set Topology
open scoped NumberField SourcePhysical Classical

noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "B" => sourceLocalBall K P
local notation "ν" => sourceLocalValuation K P

private theorem valuation_one_of_small (n : ℤ) (hn : n < 0)
    (x : L) (hx : x-1 ∈ B n) : ν x = 1 := by
  have hlt : ν (x-1) < 1 := (show ν (x-1) ≤ WithZero.exp n from hx).trans_lt (by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr hn)
  calc
    _ = ν (1+(x-1)) := congrArg ν (by ring)
    _ = ν 1 := (ν).map_add_eq_of_lt_left (by simpa only [map_one] using hlt)
    _ = 1 := map_one _

def sourceKPRetainedCutoff (n : ℤ) (hn : n < 0) : SourceThetaFiniteCutoff K P where
  region := {t : Lˣ | (t:L)-1 ∈ B n}
  isCompact := by
    apply (IsOpenUnits.isOpenEmbedding_unitsVal (M := L)).isEmbedding.isCompact_iff.mpr
    have he : (Units.val : Lˣ → L) '' {t : Lˣ | (t:L)-1 ∈ B n} =
        (fun x : L => 1+x) '' B n := by
      ext x
      constructor
      · rintro ⟨t,ht,rfl⟩
        exact ⟨(t:L)-1,ht,by ring⟩
      · rintro ⟨y,hy,rfl⟩
        have hy' : (1+y)-1 ∈ B n := by simpa only [add_sub_cancel_left] using hy
        have hval := valuation_one_of_small K P n hn (1+y) hy'
        have hne : (1+y:L) ≠ 0 := by
          intro hz
          rw [hz,map_zero] at hval
          exact zero_ne_one hval
        exact ⟨Units.mk0 _ hne,hy',rfl⟩
    rw [he]
    exact (sourceLocalBall_isCompact K P n).image (continuous_const.add continuous_id)
  isOpen := (sourceLocalBall_isOpen K P n).preimage (Units.continuous_val.sub continuous_const)
  one_mem := by
    change (1:L)-1 ∈ B n
    rw [sub_self]
    exact (sourceLocalOpenBall K P n).zero_mem
  norm_eq_one t ht := Valued.toNormedField.norm_eq_one_iff.mpr
    (valuation_one_of_small K P n hn (t:L) ht)

theorem sourceKPRetainedCutoff_factor (n : ℤ) (hn : n < 0) (t : Lˣ) :
    (sourceKPRetainedCutoff K P n hn).factor t =
      if (t:L)-1 ∈ B n then 1 else 0 := by
  simp only [SourceThetaFiniteCutoff.factor, sourceKPRetainedCutoff, Set.indicator_apply, Set.mem_setOf_eq]

end
end ArtinMatthews
