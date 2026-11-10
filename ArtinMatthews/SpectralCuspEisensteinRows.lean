module

public import ArtinMatthews.SpectralCuspDoubleCosetPeriod
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

/-! The actual distinct bottom rows of `s Γ₀(N) r⁻¹`. The left cusp is
` s⁻¹∞`; the right cusp is `r⁻¹∞`. No spectral expansion is used. -/
noncomputable section
open Matrix Set
open scoped MatrixGroups
namespace ArtinMatthews

def gamma0CuspEisensteinRow (N : ℕ) (r s : SL(2, ℤ))
    (M : gamma0CuspCorrespondence N r s) : Fin 2 → ℤ := M.val 1

abbrev Gamma0CuspEisensteinRows (N : ℕ) (r s : SL(2, ℤ)) :=
  {v : Fin 2 → ℤ // v ∈ range (gamma0CuspEisensteinRow N r s)}

def gamma0CuspEisensteinRowRepresentative (N : ℕ) (r s : SL(2, ℤ))
    (v : Gamma0CuspEisensteinRows N r s) : gamma0CuspCorrespondence N r s :=
  v.property.choose

theorem gamma0CuspEisensteinRowRepresentative_spec (N : ℕ) (r s : SL(2, ℤ))
    (v : Gamma0CuspEisensteinRows N r s) :
    (gamma0CuspEisensteinRowRepresentative N r s v).val 1 = v.val := v.property.choose_spec

theorem gamma0CuspEisensteinRows_coprime (N : ℕ) (r s : SL(2, ℤ))
    (v : Gamma0CuspEisensteinRows N r s) : IsCoprime (v.val 0) (v.val 1) := by
  rw [← gamma0CuspEisensteinRowRepresentative_spec N r s v]
  exact SpecialLinearGroup.isCoprime_row _ 1

theorem gamma0CuspEisensteinRows_ne_zero (N : ℕ) (r s : SL(2, ℤ))
    (v : Gamma0CuspEisensteinRows N r s) : v.val ≠ 0 := by
  intro h
  have hc := gamma0CuspEisensteinRows_coprime N r s v
  simp only [h,Pi.zero_apply,isCoprime_zero_left,not_isUnit_zero] at hc

theorem gamma0CuspCorrespondence_neg (N : ℕ) (r s M : SL(2, ℤ))
    (hM : M ∈ gamma0CuspCorrespondence N r s) :
    -M ∈ gamma0CuspCorrespondence N r s := by
  change s⁻¹ * (-M) * r ∈ CongruenceSubgroup.Gamma0 N
  rw [mul_neg,neg_mul,CongruenceSubgroup.Gamma0_mem]
  simp only [SpecialLinearGroup.coe_neg,Matrix.neg_apply,Int.cast_neg]
  exact neg_eq_zero.mpr (CongruenceSubgroup.Gamma0_mem.mp hM)

def gamma0CuspEisensteinNegRow (N : ℕ) (r s : SL(2, ℤ))
    (v : Gamma0CuspEisensteinRows N r s) : Gamma0CuspEisensteinRows N r s :=
  ⟨-v.val, by
    let M := gamma0CuspEisensteinRowRepresentative N r s v
    refine ⟨⟨-M.val,gamma0CuspCorrespondence_neg N r s M.val M.property⟩,?_⟩
    change (-M.val) 1 = -v.val
    rw [SpecialLinearGroup.coe_neg]
    exact congrArg Neg.neg (gamma0CuspEisensteinRowRepresentative_spec N r s v)⟩

@[simp] theorem gamma0CuspEisensteinNegRow_involutive (N : ℕ) (r s : SL(2, ℤ))
    (v : Gamma0CuspEisensteinRows N r s) :
    gamma0CuspEisensteinNegRow N r s (gamma0CuspEisensteinNegRow N r s v) = v := by
  apply Subtype.ext
  exact neg_neg v.val

def gamma0CuspEisensteinRowReindex (N : ℕ) (r t s : SL(2, ℤ))
    (v : Gamma0CuspEisensteinRows N r s) : Gamma0CuspEisensteinRows N t s :=
  ⟨vecMul v.val ((r*t⁻¹ : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ),by
    let M := gamma0CuspEisensteinRowRepresentative N r s v
    have hm : M.val*r*t⁻¹ ∈ gamma0CuspCorrespondence N t s := by
      change s⁻¹*(M.val*r*t⁻¹)*t ∈ CongruenceSubgroup.Gamma0 N
      have h := M.property
      change s⁻¹*M.val*r ∈ CongruenceSubgroup.Gamma0 N at h
      convert h using 1; group
    refine ⟨⟨M.val*r*t⁻¹,hm⟩,?_⟩
    change (M.val*r*t⁻¹ : SL(2,ℤ)) 1 = vecMul v.val ((r*t⁻¹ : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
    have he : (M.val*r*t⁻¹ : SL(2,ℤ)) 1 =
        vecMul (M.val 1) ((r*t⁻¹ : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [mul_assoc]
      rfl
    exact he.trans (congrArg (fun v : Fin 2 → ℤ =>
      vecMul v ((r*t⁻¹ : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
        (gamma0CuspEisensteinRowRepresentative_spec N r s v))⟩

def gamma0CuspEisensteinRowReindexEquiv (N : ℕ) (r t s : SL(2, ℤ)) :
    Gamma0CuspEisensteinRows N r s ≃ Gamma0CuspEisensteinRows N t s where
  toFun := gamma0CuspEisensteinRowReindex N r t s
  invFun := gamma0CuspEisensteinRowReindex N t r s
  left_inv v := by
    apply Subtype.ext
    change vecMul (vecMul v.val ((r*t⁻¹ : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) (t*r⁻¹ : SL(2,ℤ)) = v.val
    rw [vecMul_vecMul]
    change vecMul v.val ((r*t⁻¹*(t*r⁻¹) : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = v.val
    rw [show r*t⁻¹*(t*r⁻¹)=1 by group]
    exact vecMul_one v.val
  right_inv v := by
    apply Subtype.ext
    change vecMul (vecMul v.val ((t*r⁻¹ : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) ((r*t⁻¹ : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = v.val
    rw [vecMul_vecMul]
    change vecMul v.val ((t*r⁻¹*(r*t⁻¹) : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = v.val
    rw [show t*r⁻¹*(r*t⁻¹)=1 by group]
    exact vecMul_one v.val

end ArtinMatthews
