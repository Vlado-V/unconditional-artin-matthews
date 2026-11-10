module

public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.SpectralTrueWidthDoubleCosets
public import ArtinMatthews.SpectralTrueWidthNormalizedMatrices
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

/-! The actual ABL mixed cusp is the right chart `1/s` at level `r*s`.
Its true scaling is the literal lower-triangular source scaling, and
its normalized modulus is `s*sqrt(r)*c`, not the integral lower entry. -/

noncomputable section
open Matrix Set
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0MixedCusp_trueWidth (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) : gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) = r := by
  rw [gamma0CuspTrueWidth_oneOver,pow_two,Nat.gcd_mul_right,hcop.gcd_eq_one,one_mul,
    Nat.mul_div_cancel r (NeZero.pos s)]

set_option backward.isDefEq.respectTransparency false in
theorem gamma0MixedCusp_trueScaling (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) :
    gamma0TrueCuspScaling (r*s) (gamma0CuspOneOver s) = lowerTriScaling (NeZero.pos r) s := by
  unfold gamma0TrueCuspScaling
  simp only [gamma0MixedCusp_trueWidth r s hcop]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atkinRealMap,gamma0CuspOneOver,cuspWidthDilation,lowerTriScaling,
      Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,one_div]

theorem gamma0MixedCusp_trueModulus (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) (c : ℕ) :
    gamma0TrueWidthModulus (r*s) (gamma0CuspOneOver s) 1 (s*c : ℕ) =
      (s : ℝ)*Real.sqrt (r : ℝ)*(c : ℝ) := by
  unfold gamma0TrueWidthModulus
  simp only [gamma0MixedCusp_trueWidth r s hcop,gamma0CuspTrueWidth_identity,Nat.cast_one,Real.sqrt_one,
    mul_one,Nat.cast_mul]
  ring_nf

theorem gamma0MixedCusp_normalized_coset (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) (γ : CongruenceSubgroup.Gamma0 (r*s)) :
    gamma0TrueWidthMatrix (r*s) (gamma0CuspOneOver s) 1 (γ.val*(gamma0CuspOneOver s)⁻¹) =
      atkinRealMap γ.val*lowerTriScaling (NeZero.pos r) s := by
  have h := gamma0TrueWidthMatrix_correspondence (r*s) (gamma0CuspOneOver s) 1 γ
  simpa only [gamma0MixedCusp_trueScaling r s hcop,gamma0TrueCuspScaling_identity,
    one_mul,inv_one] using h

set_option backward.isDefEq.respectTransparency false in
theorem gamma0MixedCuspCorrespondence_iff (r s : ℕ) (M : SL(2, ℤ)) :
    M ∈ gamma0CuspCorrespondence (r*s) (gamma0CuspOneOver s) 1 ↔
      (r : ℤ)*(s : ℤ) ∣ M 1 0-(s : ℤ)*M 1 1 := by
  have hC : (M*gamma0CuspOneOver s) 1 0 = M 1 0-(s : ℤ)*M 1 1 := by
    simp [gamma0CuspOneOver,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
    ring_nf
  simp only [gamma0CuspCorrespondence,mem_ofPred_eq,inv_one,one_mul,CongruenceSubgroup.Gamma0_mem,
    hC,ZMod.intCast_zmod_eq_zero_iff_dvd,Nat.cast_mul]

theorem gamma0MixedReduced_lower_dvd (r s q : ℕ) [NeZero r] [NeZero s]
    (R : gamma0TrueWidthReducedMatrix (r*s) (gamma0CuspOneOver s) 1 q) : s ∣ q := by
  obtain ⟨k,hk⟩ := (gamma0MixedCuspCorrespondence_iff r s R.val).mp R.property.1
  rw [R.property.2.1] at hk
  have he : (s : ℤ) ∣ (q : ℤ) := by
    refine ⟨R.val 1 1+(r : ℤ)*k,?_⟩
    linear_combination hk
  exact_mod_cast he

theorem gamma0MixedReduced_lower_right_congruence (r s c : ℕ) [NeZero r] [NeZero s]
    (R : gamma0TrueWidthReducedMatrix (r*s) (gamma0CuspOneOver s) 1 (s*c)) :
    (r : ℤ) ∣ (c : ℤ)-R.val 1 1 := by
  obtain ⟨k,hk⟩ := (gamma0MixedCuspCorrespondence_iff r s R.val).mp R.property.1
  rw [R.property.2.1] at hk
  have hkc : (s : ℤ)*(c : ℤ)-(s : ℤ)*R.val 1 1 = (r : ℤ)*(s : ℤ)*k := by
    simpa only [Nat.cast_mul] using hk
  refine ⟨k,?_⟩
  apply mul_left_cancel₀ (show (s : ℤ) ≠ 0 by exact_mod_cast NeZero.ne s)
  linear_combination hkc

end ArtinMatthews
