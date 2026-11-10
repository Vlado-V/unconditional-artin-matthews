module

public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.SpectralTrueWidthDoubleCosets
public import ArtinMatthews.SpectralTrueWidthNormalizedMatrices
public import ArtinMatthews.AtkinLehnerModuli
public import ArtinMatthews.SpectralMixedCuspNormalization
public import ArtinMatthews.SpectralMixedSameCuspReducedUnits
public import ArtinMatthews.SpectralMixedSameCuspShiftedDet
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

/-! The literal scaling and admissible positive moduli for the
exact-divisor cusp in the native ABL series. -/

noncomputable section
open Matrix Set
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0AtkinSameCusp_scaling (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1) :
    atkinScaling (NeZero.pos r) hab =
      gamma0TrueCuspScaling (r*s) (gamma0CuspOneOver s) * realTranslation ((b : ℝ)/(r : ℝ)) := by
  rw [gamma0MixedCusp_trueScaling r s hcop]
  exact atkinScaling_eq_lowerTri_translation (NeZero.pos r) hab

theorem gamma0AtkinSameCusp_normalized_conjugate (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (γ : CongruenceSubgroup.Gamma0 (r*s)) :
    let U := gamma0CuspOneOver s
    let T := realTranslation ((b : ℝ)/(r : ℝ))
    let W := atkinScaling (NeZero.pos r) hab
    gamma0TrueWidthMatrix (r*s) U U (U*γ.val*U⁻¹) =
      T*(W⁻¹*atkinRealMap γ.val*W)*T⁻¹ := by
  dsimp only
  rw [gamma0TrueWidthMatrix_correspondence, gamma0AtkinSameCusp_scaling r s hcop hab]
  group

theorem gamma0AtkinSameCusp_modulus (r s c : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) :
    gamma0TrueWidthModulus (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) (c : ℝ) =
      ((r*c : ℕ) : ℝ) := by
  unfold gamma0TrueWidthModulus
  rw [gamma0MixedCusp_trueWidth r s hcop, mul_assoc, ← sq, Real.sq_sqrt (Nat.cast_nonneg r)]
  push_cast
  ring

theorem gamma0AtkinSameCusp_admissible (r s c : ℕ) [NeZero r] [NeZero s] [NeZero c]
    (hcop : r.Coprime s) :
    Nonempty (gamma0TrueWidthReducedMatrix (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) c) ↔
      s ∣ c := by
  constructor
  · rintro ⟨R⟩
    exact gamma0MixedSameCuspReduced_lower_dvd r s c R
  · rintro ⟨d, rfl⟩
    have hd : d ≠ 0 := fun h => NeZero.ne (s*d) (by rw [h, Nat.mul_zero])
    let _ : NeZero d := ⟨hd⟩
    obtain ⟨a, b, hab⟩ := exists_atkin_bezout hcop
    exact ⟨(gamma0MixedSameCuspReducedUnitEquiv r s d hcop hab).symm 1⟩

def gamma0AtkinSameCuspIndex (s : ℕ) [NeZero s] : ℕ ↪ Ioi (0 : ℕ) where
  toFun k := ⟨s*(k+1), Nat.mul_pos (NeZero.pos s) (Nat.succ_pos k)⟩
  inj' := by
    intro i j h
    exact Nat.succ.inj (Nat.eq_of_mul_eq_mul_left (NeZero.pos s) (congrArg Subtype.val h))

theorem gamma0AtkinSameCuspIndex_range (s : ℕ) [NeZero s] (c : Ioi (0 : ℕ)) :
    c ∈ range (gamma0AtkinSameCuspIndex s) ↔ s ∣ c.val := by
  constructor
  · rintro ⟨k, rfl⟩
    exact dvd_mul_right _ _
  · rintro ⟨d, hd⟩
    have hpos : 0 < d := by
      by_contra! hd0
      have h := c.property
      rw [hd, Nat.eq_zero_of_le_zero hd0, Nat.mul_zero] at h
      exact (Nat.lt_irrefl 0) h
    refine ⟨d-1, Subtype.ext ?_⟩
    change s*(d-1+1) = c.val
    rw [Nat.sub_add_cancel hpos, hd]

end ArtinMatthews
