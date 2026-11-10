module

public import ArtinMatthews.SpectralPeterssonSourceGram
public import ArtinMatthews.SpectralPeterssonCuspForm
public import ArtinMatthews.SpectralPeterssonQCoefficient
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

/-! The normalized source vectors as genuine cusp forms, with their exact
true-width reproducing coefficients at every even weight. -/

noncomputable section
open Matrix UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace ArtinMatthews

def gamma0PeterssonSourceInfinityForm (N k : ℕ) [NeZero N] (hk : 2 ≤ k) (hEven : Even k)
    (n : ℕ+) : CuspForm (gamma0PeterssonRealGroup N) (k : ℤ) :=
  if he : k = 2 then by
    subst k
    exact (spectralPeterssonNormalization 2 n : ℂ) • gamma0PeterssonWeightTwoInfinityCuspForm N n
  else (spectralPeterssonNormalization k n : ℂ) •
    gamma0PeterssonPoincareCuspForm N 1 k (by omega) hEven n

theorem gamma0PeterssonSourceInfinityForm_coe (N k : ℕ) [NeZero N] (hk : 2 ≤ k) (hEven : Even k)
    (n : ℕ+) : ⇑(gamma0PeterssonSourceInfinityForm N k hk hEven n) = gamma0PeterssonSourceInfinity N k n := by
  by_cases he : k = 2
  · subst k
    rfl
  · unfold gamma0PeterssonSourceInfinityForm gamma0PeterssonSourceInfinity
    rw [dite_eq_right he,ite_eq_right he]
    rfl

def gamma0PeterssonSourceAtkinForm (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (k : ℕ) (hk : 2 ≤ k) (hEven : Even k)
    (n : ℕ+) : CuspForm (gamma0PeterssonRealGroup (r*s)) (k : ℤ) :=
  if he : k = 2 then by
    subst k
    exact (spectralPeterssonNormalization 2 n : ℂ) • gamma0PeterssonWeightTwoAtkinCuspForm r s hcop hab n
  else (spectralPeterssonNormalization k n : ℂ) •
    gamma0PeterssonPoincareCuspForm (r*s) (gamma0CuspOneOver s) k (by omega) hEven n

theorem gamma0PeterssonSourceAtkinForm_coe (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (k : ℕ) (hk : 2 ≤ k) (hEven : Even k) (n : ℕ+) :
    ⇑(gamma0PeterssonSourceAtkinForm r s hcop hab k hk hEven n) = gamma0PeterssonSourceAtkin r s hab k n := by
  by_cases he : k = 2
  · subst k
    rfl
  · unfold gamma0PeterssonSourceAtkinForm gamma0PeterssonSourceAtkin
    rw [dite_eq_right he,ite_eq_right he]
    rfl

private theorem peterssonInner_normalized_reproducing (N k : ℕ) (hk : 2 ≤ k) (n : ℕ+)
    (P F : UpperHalfPlane → ℂ) (a : ℂ)
    (h : gamma0PeterssonInner N k P F = (spectralPeterssonReproducingMass k n : ℂ)*a) :
    gamma0PeterssonInner N k (fun z => (spectralPeterssonNormalization k n : ℂ)*P z) F =
      (Real.sqrt (spectralPeterssonReproducingMass k n) : ℂ)*a := by
  have hs := gamma0PeterssonInner_scale_real N k (spectralPeterssonNormalization k n) 1 P F
  simp only [Complex.ofReal_one,one_mul,mul_one] at hs
  let M := spectralPeterssonReproducingMass k n
  have hM : 0 < M := spectralPeterssonReproducingMass_pos k hk n
  have hr : spectralPeterssonNormalization k n*M = Real.sqrt M := by
    change (Real.sqrt M)⁻¹*M = Real.sqrt M
    calc
      _ = (Real.sqrt M)⁻¹*(Real.sqrt M)^2 := by rw [Real.sq_sqrt hM.le]
      _ = _ := by rw [pow_two,← mul_assoc,inv_mul_cancel₀ (Real.sqrt_pos.mpr hM).ne',one_mul]
  rw [hs,h,← mul_assoc,← Complex.ofReal_mul,hr]

theorem gamma0PeterssonSourceInfinity_reproduce (N k : ℕ) [NeZero N] (hk : 2 ≤ k) (hEven : Even k)
    (n : ℕ+) (F : CuspForm (gamma0PeterssonRealGroup N) (k : ℤ)) :
    gamma0PeterssonInner N k (gamma0PeterssonSourceInfinity N k n) F =
      (Real.sqrt (spectralPeterssonReproducingMass k n) : ℂ)*
        (UpperHalfPlane.qExpansion 1 (spectralHolomorphicSlash k (gamma0TrueCuspScaling N 1) F)).coeff (n : ℕ) := by
  by_cases he : k = 2
  · subst k
    exact peterssonInner_normalized_reproducing N 2 le_rfl n _ F _
      (gamma0PeterssonWeightTwoInfinity_reproduce_cuspForm N n F)
  · unfold gamma0PeterssonSourceInfinity
    rw [ite_eq_right he]
    exact peterssonInner_normalized_reproducing N k hk n _ F _
      (gamma0PeterssonInner_reproduce_cuspForm N k (by omega) hEven 1 n F)

theorem gamma0PeterssonSourceAtkin_reproduce (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (k : ℕ) (hk : 2 ≤ k) (hEven : Even k)
    (n : ℕ+) (F : CuspForm (gamma0PeterssonRealGroup (r*s)) (k : ℤ)) :
    gamma0PeterssonInner (r*s) k (gamma0PeterssonSourceAtkin r s hab k n) F =
      (Real.sqrt (spectralPeterssonReproducingMass k n) : ℂ)*
        (UpperHalfPlane.qExpansion 1 (spectralHolomorphicSlash k
          (gamma0TrueCuspScaling (r*s) (gamma0CuspOneOver s)) F)).coeff (n : ℕ) := by
  by_cases he : k = 2
  · subst k
    exact peterssonInner_normalized_reproducing (r*s) 2 le_rfl n _ F _
      (gamma0PeterssonWeightTwoAtkin_reproduce_cuspForm r s hcop hab n F)
  · unfold gamma0PeterssonSourceAtkin
    rw [ite_eq_right he]
    exact peterssonInner_normalized_reproducing (r*s) k hk n _ F _
      (gamma0PeterssonInner_reproduce_cuspForm (r*s) k (by omega) hEven (gamma0CuspOneOver s) n F)

end ArtinMatthews
