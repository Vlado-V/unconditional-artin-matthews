module

public import ArtinMatthews.SpectralEisensteinCriticalPoleRemoval
public import ArtinMatthews.SpectralEisensteinRegularGerms
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

/-! The actual scattering functional equation from the same finite
matching system and the two reflected full weak defect equations. -/
noncomputable section
open Set Filter Topology Matrix
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

theorem eisensteinParameterReflect_involutive : Function.Involutive (fun s : ℂ => 1-s) := by
  intro s
  ring

theorem eisensteinParameterReflect_tendsto_punctured (s : ℂ) :
    Tendsto (fun w : ℂ => 1-w) (𝓝[≠] s) (𝓝[≠] (1-s)) := by
  have hc : Continuous (fun w : ℂ => 1-w) := continuous_const.sub continuous_id
  refine tendsto_nhdsWithin_iff.mpr ⟨hc.continuousAt.mono_left nhdsWithin_le_nhds,?_⟩
  filter_upwards [(self_mem_nhdsWithin : ({s}:Set ℂ)ᶜ∈𝓝[≠] s)] with w hw
  intro h
  exact hw (mem_singleton_iff.mpr (eisensteinParameterReflect_involutive.injective (mem_singleton_iff.mp h)))

theorem gamma0EisensteinMatchingRegular_reflected_eventually (N : ℕ) [NeZero N] (s : ℂ) :
    ∀ᶠ w in 𝓝[≠] s, gamma0EisensteinMatchingRegular N w ∧ gamma0EisensteinMatchingRegular N (1-w) :=
  (gamma0EisensteinMatchingRegular_eventually N s).and
    ((eisensteinParameterReflect_tendsto_punctured s).eventually
      (gamma0EisensteinMatchingRegular_eventually N (1-s)))

theorem gamma0EisensteinMatchedDefect_eq_zero_regular (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : gamma0EisensteinMatchingRegular N s) :
    gamma0EisensteinMatchedDefect N a s=0 := by
  have h := gamma0CuspEisensteinMatchedTruncatedEnergy_pencil_defect N a s
  rw [gamma0CuspEisensteinMatchedTruncatedEnergy_pencil_regular N a s hs,sub_self] at h
  exact neg_eq_zero.mp h.symm

theorem gamma0EisensteinMatchingMatrix_scattering_regular (N : ℕ) [NeZero N]
    (s : ℂ) (hs : gamma0EisensteinMatchingRegular N s) :
    gamma0EisensteinMatchingMatrix N s * gamma0CuspScatteringMatrix N s =
      -gamma0EisensteinMatchingMatrix N (1-s) := by
  ext i j
  let r := gamma0EisensteinCuspClassRepresentative N
  let L := innerSL ℂ (gamma0EisensteinOutgoingDefect N 2 i)
  have hd := congrArg L (gamma0EisensteinMatchedDefect_eq_zero_regular N (r j) s hs)
  simp only [gamma0EisensteinMatchedDefect,map_add,map_sum,map_smul,map_zero,smul_eq_mul] at hd
  have hq : (1:ℂ)-(1-s)=s := eisensteinParameterReflect_involutive s
  have hR : gamma0EisensteinMatchingMatrix N (1-s) i j =
      L (gamma0EisensteinMatchingDefect N (r j) s) := by
    change L (gamma0EisensteinMatchingDefect N (r j) (1-(1-s)))=_
    rw [hq]
  rw [Matrix.mul_apply,Matrix.neg_apply,hR]
  calc
    (∑ k,gamma0EisensteinMatchingMatrix N s i k*gamma0CuspScatteringMatrix N s k j) =
        ∑ k,gamma0EisensteinMatchedCoefficient N (r j) s k * L (gamma0EisensteinOutgoingDefect N s k) := by
      apply Finset.sum_congr rfl
      intro k _
      change L (gamma0EisensteinOutgoingDefect N s k)*gamma0EisensteinMatchedCoefficient N (r j) s k=_
      rw [mul_comm]
    _ = _ := eq_neg_of_add_eq_zero_right hd

theorem gamma0CuspScatteringMatrix_reflection_regular (N : ℕ) [NeZero N]
    (s : ℂ) (hs : gamma0EisensteinMatchingRegular N s) (hq : gamma0EisensteinMatchingRegular N (1-s)) :
    gamma0CuspScatteringMatrix N s * gamma0CuspScatteringMatrix N (1-s)=1 := by
  let A := gamma0EisensteinMatchingMatrix N s
  let B := gamma0EisensteinMatchingMatrix N (1-s)
  let M := gamma0CuspScatteringMatrix N s
  let P := gamma0CuspScatteringMatrix N (1-s)
  have hM : A*M = -B := gamma0EisensteinMatchingMatrix_scattering_regular N s hs
  have hP : B*P = -A := by
    simpa only [eisensteinParameterReflect_involutive s] using
      gamma0EisensteinMatchingMatrix_scattering_regular N (1-s) hq
  have hA : IsUnit A.det := isUnit_iff_ne_zero.mpr hs.2
  have h : A*(M*P)=A*1 := by
    rw [← Matrix.mul_assoc,hM,Matrix.neg_mul,hP,neg_neg,mul_one]
  have hi := congrArg (fun X => A⁻¹*X) h
  simpa only [Matrix.nonsing_inv_mul_cancel_left A _ hA] using hi

theorem gamma0CuspScatteringCanonical_reflection_germ (N : ℕ) [NeZero N] (s : ℂ) :
    ∀ᶠ w in 𝓝[≠] s,
      gamma0CuspScatteringCanonical N w * gamma0CuspScatteringCanonical N (1-w)=1 := by
  filter_upwards [gamma0EisensteinMatchingRegular_reflected_eventually N s] with w hw
  rw [gamma0CuspScatteringCanonical_eq_regular N w hw.1,
    gamma0CuspScatteringCanonical_eq_regular N (1-w) hw.2]
  exact gamma0CuspScatteringMatrix_reflection_regular N w hw.1 hw.2

end ArtinMatthews
