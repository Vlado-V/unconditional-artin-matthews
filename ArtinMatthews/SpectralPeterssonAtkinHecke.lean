module

public import ArtinMatthews.SpectralPeterssonAtkinRows
public import ArtinMatthews.SpectralPeterssonHeckeSeed
public import ArtinMatthews.SpectralFourierBruhatKernel
public import ArtinMatthews.SpectralPeterssonHeckeAction
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Transport of the literal weight-two Hecke-regulated series, including the cusp phase. -/

noncomputable section
open Matrix UpperHalfPlane
open scoped MatrixGroups

namespace ArtinMatthews

theorem spectralPeterssonHeckeSeed_slash_realTranslation (u : ℝ) (m : ℕ+) (t : ℝ) :
    spectralHolomorphicSlash 2 (realTranslation t) (spectralPeterssonHeckeSeed u m) =
      fun z => atkinPhase ((m : ℝ)*t) * spectralPeterssonHeckeSeed u m z := by
  funext z
  rw [spectralHolomorphicSlash_apply]
  have hdenom : (((realTranslation t 1 0 : ℝ) : ℂ)*(z : ℂ) +
      ((realTranslation t 1 1 : ℝ) : ℂ)) = 1 := by
    simp [realTranslation]
  rw [hdenom, one_pow, div_one]
  have hphase : spectralHolomorphicCuspSeed (m : ℕ) (realTranslation t • z) =
      atkinPhase ((m : ℝ)*t) * spectralHolomorphicCuspSeed (m : ℕ) z := by
    unfold spectralHolomorphicCuspSeed atkinPhase
    rw [realTranslation_coe_smul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold spectralPeterssonHeckeSeed
  rw [realTranslation_im_smul, hphase]
  ring

private theorem slash_mul_scalar (k : ℕ) (G : SL(2, ℝ)) (v : ℂ)
    (f : UpperHalfPlane → ℂ) :
    spectralHolomorphicSlash k G (fun z => v * f z) =
      fun z => v * spectralHolomorphicSlash k G f z := by
  funext z
  simp only [spectralHolomorphicSlash_apply, mul_div_assoc]

private theorem heckeSignedSummand_groupRow (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (u : ℝ) (m : ℕ+) (γ : CongruenceSubgroup.Gamma0 N) :
    gamma0PeterssonHeckeSignedSummand N 1 a u m (gamma0PeterssonGroupRow N a γ) =
      spectralHolomorphicSlash 2 (gamma0PeterssonGroupMatrix N a γ) (spectralPeterssonHeckeSeed u m) := by
  unfold gamma0PeterssonGroupRow
  rw [gamma0PeterssonHeckeSignedSummand_of_matrix, gamma0PeterssonHeckeMatrixSeed,
    gamma0PeterssonGroupMatrix_eq]

theorem gamma0PeterssonHeckeSignedSummand_atkinLehner (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (u : ℝ) (m : ℕ+) (p : Gamma0PeterssonSignedRow (r*s) 1 (gamma0CuspOneOver s)) :
    gamma0PeterssonHeckeSignedSummand (r*s) 1 (gamma0CuspOneOver s) u m p =
      fun z => atkinPhase ((m : ℝ)*((b : ℝ)/(r : ℝ))) *
        spectralHolomorphicSlash 2 (atkinScaling (NeZero.pos r) hab)⁻¹
          (gamma0PeterssonHeckeSignedSummand (r*s) 1 1 u m
            (gamma0PeterssonAtkinSignedRowEquiv r s hcop hab p)) z := by
  obtain ⟨γ,rfl⟩ := gamma0PeterssonGroupRow_surjective (r*s) (gamma0CuspOneOver s) p
  rw [gamma0PeterssonAtkinSignedRowEquiv_groupRow r s hcop hab,
    heckeSignedSummand_groupRow, heckeSignedSummand_groupRow,
    gamma0PeterssonAtkinGroupMatrix r s hcop hab, spectralHolomorphicSlash_mul,
    spectralHolomorphicSlash_mul, spectralPeterssonHeckeSeed_slash_realTranslation]
  simp only [slash_mul_scalar]

theorem gamma0PeterssonHecke_atkinLehner_transport (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (u : ℝ) (m : ℕ+) :
    gamma0PeterssonHecke (r*s) (gamma0CuspOneOver s) u m =
      fun z => atkinPhase ((m : ℝ)*((b : ℝ)/(r : ℝ))) *
        spectralHolomorphicSlash 2 (atkinScaling (NeZero.pos r) hab)⁻¹
          (gamma0PeterssonHecke (r*s) 1 u m) z := by
  let W := atkinScaling (NeZero.pos r) hab
  let v := atkinPhase ((m : ℝ)*((b : ℝ)/(r : ℝ)))
  let e := gamma0PeterssonAtkinSignedRowEquiv r s hcop hab
  funext z
  unfold gamma0PeterssonHecke gamma0PeterssonHeckeChart
  rw [spectralHolomorphicSlash_tsum_mul]
  let f (q : Gamma0PeterssonSignedRow (r*s) 1 1) :=
    spectralHolomorphicSlash 2 W⁻¹ (gamma0PeterssonHeckeSignedSummand (r*s) 1 1 u m q) z
  change (1/2 : ℂ)*(∑' p, gamma0PeterssonHeckeSignedSummand (r*s) 1 (gamma0CuspOneOver s) u m p z) =
    v*((1/2 : ℂ)*(∑' q, f q))
  calc
    _ = (1/2 : ℂ)*(∑' p, v*f (e p)) := by
      apply congrArg (fun x : ℂ => (1/2 : ℂ)*x)
      exact tsum_congr (fun p => congrFun (gamma0PeterssonHeckeSignedSummand_atkinLehner r s hcop hab u m p) z)
    _ = _ := by
      rw [tsum_mul_left, e.tsum_eq]
      ring

end ArtinMatthews
