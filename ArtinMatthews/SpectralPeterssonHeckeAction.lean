module

public import ArtinMatthews.SpectralPeterssonHeckeSeed
public import ArtinMatthews.SpectralPeterssonCuspRowAction
public import ArtinMatthews.SpectralCuspEisensteinInfinity
public import ArtinMatthews.SpectralPeterssonPoincareAction
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

/-! Exact right-slash transport of the absolutely convergent regulated
Poincare sum and its projective-row realization. -/

noncomputable section
open Matrix Set UpperHalfPlane
open scoped MatrixGroups

namespace ArtinMatthews

theorem spectralHolomorphicSlash_tsum_mul (k : ℕ) (G : SL(2, ℝ)) {ι : Type*} (c : ℂ)
    (F : ι → UpperHalfPlane → ℂ) :
    spectralHolomorphicSlash k G (fun z => c*(∑' p, F p z)) =
      fun z => c*(∑' p, spectralHolomorphicSlash k G (F p) z) := by
  funext z
  rw [spectralHolomorphicSlash_apply]
  simp_rw [spectralHolomorphicSlash_apply,tsum_div_const,mul_div_assoc]

theorem gamma0PeterssonHeckeSignedSummand_rightChange (N : ℕ) [NeZero N]
    (b b' a : SL(2, ℤ)) (γ : CongruenceSubgroup.Gamma0 N) (u : ℝ) (m : ℕ+)
    (p : Gamma0PeterssonSignedRow N b a) :
    gamma0PeterssonHeckeSignedSummand N b' a u m (gamma0PeterssonSignedRowRightEquiv N b b' a γ p) =
      spectralHolomorphicSlash 2 ((gamma0TrueCuspScaling N b)⁻¹*atkinRealMap γ.val*
        gamma0TrueCuspScaling N b') (gamma0PeterssonHeckeSignedSummand N b a u m p) := by
  let M := gamma0PeterssonRowMatrix N b a p
  let R := gamma0PeterssonRightMatrix N b b' a γ M
  have he : gamma0PeterssonSignedRowRightEquiv N b b' a γ p = gamma0PeterssonRowOfMatrix N b' a R := by
    apply Subtype.ext
    change p.val ᵥ* (b*γ.val*(b')⁻¹ : SL(2, ℤ)).val =
      fun i => (gamma0PeterssonRightMatrix N b b' a γ M).val 1 i
    rw [gamma0PeterssonRightMatrix_row,gamma0PeterssonRowMatrix_row N b a p]
  rw [he,gamma0PeterssonHeckeSignedSummand_of_matrix]
  change gamma0PeterssonHeckeMatrixSeed N b' a u m (M.val*(b*γ.val*(b')⁻¹)) =
    spectralHolomorphicSlash 2 ((gamma0TrueCuspScaling N b)⁻¹*atkinRealMap γ.val*
      gamma0TrueCuspScaling N b') (gamma0PeterssonHeckeMatrixSeed N b a u m M.val)
  unfold gamma0PeterssonHeckeMatrixSeed
  rw [gamma0Petersson_normalized_rightChange,spectralHolomorphicSlash_mul]

theorem gamma0PeterssonHeckeChart_rightChange (N : ℕ) [NeZero N]
    (b b' a : SL(2, ℤ)) (γ : CongruenceSubgroup.Gamma0 N) (u : ℝ) (m : ℕ+) :
    gamma0PeterssonHeckeChart N b' a u m =
      spectralHolomorphicSlash 2 ((gamma0TrueCuspScaling N b)⁻¹*atkinRealMap γ.val*
        gamma0TrueCuspScaling N b') (gamma0PeterssonHeckeChart N b a u m) := by
  let e := gamma0PeterssonSignedRowRightEquiv N b b' a γ
  unfold gamma0PeterssonHeckeChart
  rw [spectralHolomorphicSlash_tsum_mul]
  funext z
  congr 1
  calc
    _ = ∑' p : Gamma0PeterssonSignedRow N b a, gamma0PeterssonHeckeSignedSummand N b' a u m (e p) z :=
      (e.tsum_eq (fun p => gamma0PeterssonHeckeSignedSummand N b' a u m p z)).symm
    _ = _ := tsum_congr (fun p =>
      congrFun (gamma0PeterssonHeckeSignedSummand_rightChange N b b' a γ u m p) z)

theorem gamma0PeterssonHecke_slash_cusp (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (u : ℝ) (m : ℕ+) :
    spectralHolomorphicSlash 2 (gamma0TrueCuspScaling N b) (gamma0PeterssonHecke N a u m) =
      gamma0PeterssonHeckeChart N b a u m := by
  unfold gamma0PeterssonHecke
  simpa only [gamma0TrueCuspScaling_identity,inv_one,Subgroup.coe_one,map_one,one_mul] using
    (gamma0PeterssonHeckeChart_rightChange N 1 b a 1 u m).symm

theorem gamma0PeterssonHecke_slash_gamma0 (N : ℕ) [NeZero N]
    (a : SL(2, ℤ)) (γ : CongruenceSubgroup.Gamma0 N) (u : ℝ) (m : ℕ+) :
    spectralHolomorphicSlash 2 (atkinRealMap γ.val) (gamma0PeterssonHecke N a u m) =
      gamma0PeterssonHecke N a u m := by
  unfold gamma0PeterssonHecke
  simpa only [gamma0TrueCuspScaling_identity,inv_one,one_mul,mul_one] using
    (gamma0PeterssonHeckeChart_rightChange N 1 1 a γ u m).symm

theorem gamma0PeterssonHeckeSignedSummand_neg (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (u : ℝ) (m : ℕ+) (p : Gamma0PeterssonSignedRow N b a) :
    gamma0PeterssonHeckeSignedSummand N b a u m (gamma0PeterssonSignedRowNeg N b a p) =
      gamma0PeterssonHeckeSignedSummand N b a u m p := by
  let M := gamma0PeterssonRowMatrix N b a p
  let R := gamma0CuspCorrespondenceNeg N b a M
  have hp : gamma0PeterssonSignedRowNeg N b a p = gamma0PeterssonRowOfMatrix N b a R := by
    apply Subtype.ext
    funext i
    have hi := congrFun (gamma0PeterssonRowMatrix_row N b a p) i
    change -p.val i = ((-M.val : SL(2, ℤ)) 1 i)
    simp [M,hi]
  rw [hp,gamma0PeterssonHeckeSignedSummand_of_matrix]
  change gamma0PeterssonHeckeMatrixSeed N b a u m (-M.val) = gamma0PeterssonHeckeMatrixSeed N b a u m M.val
  unfold gamma0PeterssonHeckeMatrixSeed
  rw [gamma0Petersson_normalized_neg,spectralHolomorphicSlash_neg 2 (by decide)]

theorem gamma0PeterssonHeckeChart_eq_positive (N : ℕ) [NeZero N]
    (b a : SL(2, ℤ)) (u : ℝ) (hu : 0 < u) (m : ℕ+) (z : UpperHalfPlane) :
    gamma0PeterssonHeckeChart N b a u m z =
      ∑' p : Gamma0PeterssonPositiveRow N b a, gamma0PeterssonHeckeSignedSummand N b a u m p.val z := by
  classical
  let S : Set (Gamma0PeterssonSignedRow N b a) := {p | gamma0PeterssonRowPositive p}
  let f (p : Gamma0PeterssonSignedRow N b a) := gamma0PeterssonHeckeSignedSummand N b a u m p z
  let e : ↥S ≃ ↥(Sᶜ) := Equiv.subtypeEquiv (gamma0PeterssonSignedRowNeg N b a) (fun p => by
    change gamma0PeterssonRowPositive p ↔ ¬ gamma0PeterssonRowPositive (gamma0PeterssonSignedRowNeg N b a p)
    rw [gamma0PeterssonRowPositive_neg_iff,not_not])
  have hcomp : (∑' p : ↥(Sᶜ), f p.val) = ∑' p : S, f p.val := by
    calc
      _ = ∑' p : S, f (e p).val := (e.tsum_eq (fun p : ↥(Sᶜ) => f p.val)).symm
      _ = _ := tsum_congr (fun p => congrFun (gamma0PeterssonHeckeSignedSummand_neg N b a u m p.val) z)
  have hs : Summable f := (gamma0PeterssonHeckeSignedSummand_summable N b a u hu m z).of_norm
  change (1/2 : ℂ)*(∑' p, f p) = ∑' p : S, f p.val
  rw [← hs.tsum_subtype_add_tsum_subtype_compl S,hcomp]
  ring

end ArtinMatthews
