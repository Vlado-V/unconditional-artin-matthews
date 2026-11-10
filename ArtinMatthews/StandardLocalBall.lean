module

public import ArtinMatthews.StandardLocalConductor
public import ArtinMatthews.IntegerOpenSubgroup
public import ArtinMatthews.StandardAdelicCharacterData
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


set_option backward.privateInPublic true
@[expose] public section

/-! Actual compact-open local balls of every integral valuation radius.
Their standard-character annihilator reverses the exponent and adds
the genuine different exponent. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain StandardAdelic QuadraticWeil
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (P : HeightOneSpectrum (𝓞 K))

scoped instance sourceLocalRelation : ValuativeRel (P.adicCompletion K) := adicRelation K P

scoped instance sourceLocalField : IsNonarchimedeanLocalField (P.adicCompletion K) := adicLocalField K P

theorem sourceLocalBall_zero : sourceLocalBall K P 0 = (P.adicCompletionIntegers K : Set _) := by
  ext x
  change sourceLocalValuation K P x ≤ WithZero.exp (0 : ℤ) ↔ sourceLocalValuation K P x ≤ 1
  rw [WithZero.exp_zero]

theorem sourceLocalBall_zero_eq_integerOpen : sourceLocalBall K P 0 =
    (integerOpenSubgroup (P.adicCompletion K) : Set _) := by
  rw [sourceLocalBall_zero]
  ext x
  exact (adic_mem_integer_iff K P x).symm

def sourceLocalBallScale (n : ℤ) : P.adicCompletion K := localPrime K P ^ (-n)

theorem sourceLocalBallScale_ne_zero (n : ℤ) : sourceLocalBallScale K P n ≠ 0 :=
  zpow_ne_zero _ (localPrime_ne_zero K P)

theorem sourceLocalBallScale_valuation (n : ℤ) :
    sourceLocalValuation K P (sourceLocalBallScale K P n) = WithZero.exp n := by
  rw [sourceLocalBallScale, map_zpow₀, localPrime_valuation, ← WithZero.exp_zsmul]
  simp

theorem sourceLocalBall_eq_scaled_zero (n : ℤ) : sourceLocalBall K P n =
    (fun x => sourceLocalBallScale K P n * x) '' sourceLocalBall K P 0 := by
  let v := sourceLocalValuation K P
  let c := sourceLocalBallScale K P n
  have hcv : v c = WithZero.exp n := sourceLocalBallScale_valuation K P n
  have hc : c ≠ 0 := sourceLocalBallScale_ne_zero K P n
  ext y
  constructor
  · intro hy
    refine ⟨y / c, ?_, ?_⟩
    · change v (y / c) ≤ WithZero.exp (0 : ℤ)
      rw [map_div₀, WithZero.exp_zero, hcv, div_le_one₀ (pos_iff_ne_zero.mpr WithZero.exp_ne_zero)]
      exact hy
    · change c * (y / c) = y
      field_simp [hc]
  · rintro ⟨x, hx, rfl⟩
    change v (c * x) ≤ WithZero.exp n
    rw [map_mul, hcv]
    have hx' : v x ≤ 1 := by simpa only [sourceLocalBall, Set.mem_ofPred_eq, WithZero.exp_zero] using hx
    exact (mul_le_mul' le_rfl hx').trans_eq (mul_one _)

theorem sourceLocalBall_isOpen (n : ℤ) : IsOpen (sourceLocalBall K P n) := by
  rw [sourceLocalBall_eq_scaled_zero, sourceLocalBall_zero_eq_integerOpen]
  exact (Homeomorph.mulLeft₀ _ (sourceLocalBallScale_ne_zero K P n)).isOpenMap _
    (integerOpenSubgroup (P.adicCompletion K)).isOpen

theorem sourceLocalBall_isCompact (n : ℤ) : IsCompact (sourceLocalBall K P n) := by
  rw [sourceLocalBall_eq_scaled_zero, sourceLocalBall_zero_eq_integerOpen]
  exact (integerOpenSubgroup_compact (P.adicCompletion K)).image (continuous_const.mul continuous_id)

def sourceLocalOpenBall (n : ℤ) : OpenAddSubgroup (P.adicCompletion K) where
  toAddSubgroup :=
    { carrier := sourceLocalBall K P n
      zero_mem' := by change sourceLocalValuation K P 0 ≤ WithZero.exp n; rw [map_zero]; exact zero_le
      add_mem' := fun hx hy => (sourceLocalValuation K P).map_add_le hx hy
      neg_mem' := by
        intro x hx
        change sourceLocalValuation K P (-x) ≤ WithZero.exp n
        rw [Valuation.map_neg]
        exact hx }
  isOpen' := sourceLocalBall_isOpen K P n

theorem sourceLocalBall_annihilator_iff (n : ℤ) (y : P.adicCompletion K) :
    (∀ x ∈ sourceLocalBall K P n, localFiniteCharacter K P (y * x) = 1) ↔
      y ∈ sourceLocalBall K P ((sourceDifferentExponent K P : ℤ) - n) := by
  let c := sourceLocalBallScale K P n
  have hL : (∀ x ∈ sourceLocalBall K P n, localFiniteCharacter K P (y * x) = 1) ↔
      ∀ x ∈ P.adicCompletionIntegers K, localFiniteCharacter K P ((y * c) * x) = 1 := by
    rw [sourceLocalBall_eq_scaled_zero, sourceLocalBall_zero]
    constructor
    · intro h x hx
      exact (congrArg (localFiniteCharacter K P) (mul_assoc y c x)).trans (h _ ⟨x, hx, rfl⟩)
    · rintro h x ⟨z, hz, rfl⟩
      exact (congrArg (localFiniteCharacter K P) (mul_assoc y c z)).symm.trans (h z hz)
  rw [hL, sourceLocalInteger_annihilator_iff K P (y * c)]
  change sourceLocalValuation K P (y * c) ≤ WithZero.exp (sourceDifferentExponent K P : ℤ) ↔
    sourceLocalValuation K P y ≤ WithZero.exp ((sourceDifferentExponent K P : ℤ) - n)
  rw [map_mul, show sourceLocalValuation K P c = WithZero.exp n from sourceLocalBallScale_valuation K P n,
    WithZero.exp_sub, le_div_iff₀ (pos_iff_ne_zero.mpr WithZero.exp_ne_zero)]

end
end ArtinMatthews.SourcePhysical
