module

public import ArtinMatthews.SpectralPeterssonPoincare
public import ArtinMatthews.SpectralPeterssonCuspRowAction
public import ArtinMatthews.SpectralCuspEisensteinInfinity
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact sign removal and right-slash transport of the actual
holomorphic Poincare sum, including the true-width cusp expansion. -/

noncomputable section
open Matrix Set UpperHalfPlane
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0PeterssonRowPositive_neg_iff {N : ℕ} {b a : SL(2, ℤ)}
    (p : Gamma0PeterssonSignedRow N b a) :
    gamma0PeterssonRowPositive (gamma0PeterssonSignedRowNeg N b a p) ↔
      ¬ gamma0PeterssonRowPositive p := by
  have hn : p.val 0 ≠ 0 ∨ p.val 1 ≠ 0 := by
    by_contra! h
    apply gamma0PeterssonSignedRow_ne_zero N b a p
    funext i
    fin_cases i
    · exact h.1
    · exact h.2
  change (0 < -p.val 0 ∨ -p.val 0 = 0 ∧ 0 < -p.val 1) ↔
    ¬ (0 < p.val 0 ∨ p.val 0 = 0 ∧ 0 < p.val 1)
  omega

theorem gamma0PeterssonPoincareChart_signed_sum (N : ℕ) [NeZero N]
    (b a : SL(2, ℤ)) (k m : ℕ) (hk : 3 ≤ k) (hEven : Even k) (z : UpperHalfPlane) :
    gamma0PeterssonPoincareChart N b a k m z =
      (1/2 : ℂ)*(∑' p : Gamma0PeterssonSignedRow N b a, gamma0PeterssonSignedSummand N b a k m p z) := by
  classical
  let S : Set (Gamma0PeterssonSignedRow N b a) := {p | gamma0PeterssonRowPositive p}
  let f (p : Gamma0PeterssonSignedRow N b a) := gamma0PeterssonSignedSummand N b a k m p z
  let e : ↥S ≃ ↥(Sᶜ) := Equiv.subtypeEquiv (gamma0PeterssonSignedRowNeg N b a) (fun p => by
    change gamma0PeterssonRowPositive p ↔ ¬ gamma0PeterssonRowPositive (gamma0PeterssonSignedRowNeg N b a p)
    rw [gamma0PeterssonRowPositive_neg_iff,not_not])
  have hcomp : (∑' p : ↥(Sᶜ), f p.val) = ∑' p : S, f p.val := by
    calc
      _ = ∑' p : S, f (e p).val := (e.tsum_eq (fun p : ↥(Sᶜ) => f p.val)).symm
      _ = _ := tsum_congr (fun p =>
        congrFun (gamma0PeterssonSignedSummand_neg N b a k m hEven p.val) z)
  have hs : Summable f := (gamma0PeterssonSignedSummand_summable N b a k m hk z).of_norm
  have hsplit := hs.tsum_subtype_add_tsum_subtype_compl S
  change (∑' p : S, f p.val) = (1/2 : ℂ)*(∑' p, f p)
  rw [← hsplit,hcomp]
  ring

theorem gamma0PeterssonSignedSummand_rightChange (N : ℕ) [NeZero N]
    (b b' a : SL(2, ℤ)) (γ : CongruenceSubgroup.Gamma0 N) (k m : ℕ)
    (p : Gamma0PeterssonSignedRow N b a) :
    gamma0PeterssonSignedSummand N b' a k m (gamma0PeterssonSignedRowRightEquiv N b b' a γ p) =
      spectralHolomorphicSlash k ((gamma0TrueCuspScaling N b)⁻¹*atkinRealMap γ.val*
        gamma0TrueCuspScaling N b') (gamma0PeterssonSignedSummand N b a k m p) := by
  let M := gamma0PeterssonRowMatrix N b a p
  let R := gamma0PeterssonRightMatrix N b b' a γ M
  have he : gamma0PeterssonSignedRowRightEquiv N b b' a γ p = gamma0PeterssonRowOfMatrix N b' a R := by
    apply Subtype.ext
    change p.val ᵥ* (b*γ.val*(b')⁻¹ : SL(2, ℤ)).val =
      fun i => (gamma0PeterssonRightMatrix N b b' a γ M).val 1 i
    rw [gamma0PeterssonRightMatrix_row,gamma0PeterssonRowMatrix_row N b a p]
  rw [he,gamma0PeterssonSignedSummand_of_matrix]
  change gamma0PeterssonMatrixSeed N b' a k m (M.val*(b*γ.val*(b')⁻¹)) =
    spectralHolomorphicSlash k ((gamma0TrueCuspScaling N b)⁻¹*atkinRealMap γ.val*
      gamma0TrueCuspScaling N b') (gamma0PeterssonMatrixSeed N b a k m M.val)
  unfold gamma0PeterssonMatrixSeed
  rw [gamma0Petersson_normalized_rightChange,spectralHolomorphicSlash_mul]

theorem gamma0PeterssonPoincareChart_rightChange (N : ℕ) [NeZero N]
    (b b' a : SL(2, ℤ)) (γ : CongruenceSubgroup.Gamma0 N) (k m : ℕ) (hk : 3 ≤ k)
    (hEven : Even k) :
    gamma0PeterssonPoincareChart N b' a k m =
      spectralHolomorphicSlash k ((gamma0TrueCuspScaling N b)⁻¹*atkinRealMap γ.val*
        gamma0TrueCuspScaling N b') (gamma0PeterssonPoincareChart N b a k m) := by
  funext z
  let e := gamma0PeterssonSignedRowRightEquiv N b b' a γ
  let G := (gamma0TrueCuspScaling N b)⁻¹*atkinRealMap γ.val*gamma0TrueCuspScaling N b'
  change gamma0PeterssonPoincareChart N b' a k m z =
    spectralHolomorphicSlash k G (gamma0PeterssonPoincareChart N b a k m) z
  rw [gamma0PeterssonPoincareChart_signed_sum N b' a k m hk hEven,
    spectralHolomorphicSlash_apply, gamma0PeterssonPoincareChart_signed_sum N b a k m hk hEven]
  let D := (((G 1 0 : ℝ) : ℂ)*(z : ℂ)+((G 1 1 : ℝ) : ℂ))^k
  change (1/2 : ℂ)*(∑' p : Gamma0PeterssonSignedRow N b' a,
    gamma0PeterssonSignedSummand N b' a k m p z) =
      ((1/2 : ℂ)*(∑' p : Gamma0PeterssonSignedRow N b a,
        gamma0PeterssonSignedSummand N b a k m p (G • z)))/D
  calc
    _ = (1/2 : ℂ)*(∑' p : Gamma0PeterssonSignedRow N b a,
        gamma0PeterssonSignedSummand N b' a k m (e p) z) :=
      congrArg (fun c : ℂ => (1/2 : ℂ)*c)
        (e.tsum_eq (fun p => gamma0PeterssonSignedSummand N b' a k m p z)).symm
    _ = (1/2 : ℂ)*(∑' p : Gamma0PeterssonSignedRow N b a,
        gamma0PeterssonSignedSummand N b a k m p (G • z)/D) := by
      congr 1
      apply tsum_congr
      intro p
      have hp := congrFun (gamma0PeterssonSignedSummand_rightChange N b b' a γ k m p) z
      exact hp.trans (spectralHolomorphicSlash_apply k G _ z)
    _ = _ := by rw [tsum_div_const]; ring

theorem gamma0PeterssonPoincare_slash_cusp (N : ℕ) [NeZero N]
    (b a : SL(2, ℤ)) (k m : ℕ) (hk : 3 ≤ k) (hEven : Even k) :
    spectralHolomorphicSlash k (gamma0TrueCuspScaling N b) (gamma0PeterssonPoincare N a k m) =
      gamma0PeterssonPoincareChart N b a k m := by
  unfold gamma0PeterssonPoincare
  simpa only [gamma0TrueCuspScaling_identity,inv_one,Subgroup.coe_one,map_one,one_mul] using
    (gamma0PeterssonPoincareChart_rightChange N 1 b a 1 k m hk hEven).symm

theorem gamma0PeterssonPoincare_slash_gamma0 (N : ℕ) [NeZero N]
    (a : SL(2, ℤ)) (γ : CongruenceSubgroup.Gamma0 N)
    (k m : ℕ) (hk : 3 ≤ k) (hEven : Even k) :
    spectralHolomorphicSlash k (atkinRealMap γ.val) (gamma0PeterssonPoincare N a k m) =
      gamma0PeterssonPoincare N a k m := by
  unfold gamma0PeterssonPoincare
  simpa only [gamma0TrueCuspScaling_identity,inv_one,one_mul,mul_one] using
    (gamma0PeterssonPoincareChart_rightChange N 1 1 a γ k m hk hEven).symm

theorem gamma0PeterssonPoincareChart_slash_translation (N : ℕ) [NeZero N]
    (b a : SL(2, ℤ)) (k m : ℕ) (hk : 3 ≤ k) (hEven : Even k) (l : ℤ) :
    spectralHolomorphicSlash k (realTranslation (l : ℝ)) (gamma0PeterssonPoincareChart N b a k m) =
      gamma0PeterssonPoincareChart N b a k m := by
  obtain ⟨γ,hγ⟩ := gamma0TrueCuspScaling_integer_period N b l
  have hG : (gamma0TrueCuspScaling N b)⁻¹*atkinRealMap γ.val*gamma0TrueCuspScaling N b =
      realTranslation (l : ℝ) := by rw [hγ]; group
  simpa only [hG] using (gamma0PeterssonPoincareChart_rightChange N b b a γ k m hk hEven).symm

end ArtinMatthews
