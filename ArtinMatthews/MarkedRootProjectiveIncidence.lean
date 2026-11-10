module

public import ArtinMatthews.MarkedRootProjectiveUniform
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-! The root kernel projective line is exactly the actual prime divisibility
incidence of each primitive integer position vector. -/
namespace ArtinMatthews
open Matrix
open scoped LinearAlgebra.Projectivization

/-- The projective kernel-line test is precisely vanishing of the literal
first row applied to the position vector. -/
theorem markedMatrixKernelLine_incidence {F : Type*} [Field F]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) (hv : v ≠ 0) :
    g 0 0*v 0+g 0 1*v 1=0 ↔ Projectivization.mk F v hv=markedMatrixKernelLine g := by
  rw [markedMatrixKernelLine_eq_mk,Projectivization.mk_eq_mk_iff']
  constructor
  · intro hrow
    by_cases ha : g 0 0=0
    · have hb : g 0 1 ≠ 0 := by
        intro hb
        apply markedMatrixKernelVector_nonzero g
        ext i
        fin_cases i <;> simp [markedMatrixKernelVector,ha,hb]
      have hv₁ : v 1=0 := by
        rw [ha,zero_mul,zero_add] at hrow
        exact (mul_eq_zero.mp hrow).resolve_left hb
      refine ⟨-(v 0)/(g 0 1),?_⟩
      ext i
      fin_cases i
      · change (-(v 0)/(g 0 1))*(-g 0 1)=v 0
        field_simp
      · change (-(v 0)/(g 0 1))*(g 0 0)=v 1
        rw [ha,hv₁,mul_zero]
    · refine ⟨v 1/(g 0 0),?_⟩
      ext i
      fin_cases i
      · change (v 1/(g 0 0))*(-g 0 1)=v 0
        field_simp
        linear_combination -hrow
      · change (v 1/(g 0 0))*(g 0 0)=v 1
        field_simp
  · rintro ⟨a,ha⟩
    have h₀ := congrFun ha 0
    have h₁ := congrFun ha 1
    change a*(-g 0 1)=v 0 at h₀
    change a*(g 0 0)=v 1 at h₁
    rw [← h₀,← h₁]
    ring

/-- Actual primitive integer vectors remain nonzero in every prime residue field. -/
theorem markedPrimePosition_nonzero (p : ℕ) [Fact p.Prime] (z : ℤ × ℤ)
    (hz : IsCoprime z.1 z.2) : (![z.1,z.2] : Fin 2 → ZMod p) ≠ 0 := by
  intro h
  have h₀ := congrFun h 0
  have h₁ := congrFun h 1
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Pi.zero_apply] at h₀ h₁
  obtain ⟨a,b,hab⟩ := hz
  have hh := congrArg (Int.castRingHom (ZMod p)) hab
  simp only [map_add,map_mul,map_one] at hh
  change (a : ZMod p)*(z.1 : ZMod p)+(b : ZMod p)*(z.2 : ZMod p)=1 at hh
  rw [h₀,h₁,mul_zero,mul_zero,zero_add] at hh
  exact zero_ne_one hh

/-- The actual projective residue of a primitive integer position. -/
def markedPrimePositionLine (p : ℕ) [Fact p.Prime] (z : ℤ × ℤ)
    (hz : IsCoprime z.1 z.2) : ℙ (ZMod p) (Fin 2 → ZMod p) :=
  Projectivization.mk (ZMod p) ![z.1,z.2] (markedPrimePosition_nonzero p z hz)

/-- Literal prime hits of the first coordinate of g*z are precisely equality
with the actual kernel line used in the finite root average. -/
theorem markedIntegerRoot_prime_hit_iff (p : ℕ) [Fact p.Prime]
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) :
    (p : ℤ) ∣ g 0 0*z.1+g 0 1*z.2 ↔ markedPrimePositionLine p z hz=
      markedMatrixKernelLine (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p)) g) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  unfold markedPrimePositionLine
  rw [← markedMatrixKernelLine_incidence _ _ (markedPrimePosition_nonzero p z hz)]
  simp only [Int.cast_add,Int.cast_mul,Matrix.cons_val_zero,Matrix.cons_val_one]
  rfl

end ArtinMatthews
