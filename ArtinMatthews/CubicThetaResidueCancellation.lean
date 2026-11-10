module

public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.Basic.Complex.Basic
public import ArtinMatthews.CubicThetaNormCancellation
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
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

/-!
# Finite residue-character cancellation

The norm-fiber cancellation applies to multiplicative characters on a finite
commutative monoid, including every finite residue ring. Nonunits are included
in the sum. The translation is by an actual unit of norm one, constructed from
the nontrivial anticyclotomic cubic character.
-/
noncomputable section
open scoped BigOperators Classical

namespace ArtinMatthews

/-- A nontrivial anticyclotomic cubic residue character cancels against
every function of the involution norm, including the nonunit terms. -/
theorem anticyclotomic_cubic_mulChar_sum_norm_eq_zero {R : Type*}
    [CommMonoid R] [Fintype R] (χ : MulChar R ℂ) (σ : R ≃* R)
    (hσ : Function.Involutive σ)
    (hχσ : ∀ u : Rˣ, χ (σ u) = (χ u)⁻¹)
    (hcubic : ∀ u : Rˣ, χ u ^ 3 = 1) (hne : χ ≠ 1) (F : R → ℂ) :
    (∑ z : R, χ z * F (z * σ z)) = 0 := by
  let χu : Rˣ →* ℂ := χ.toMonoidHom.comp (Units.coeHom R)
  let σu : Rˣ ≃* Rˣ := Units.mapEquiv σ
  have hσu : Function.Involutive σu := by
    intro u
    apply Units.ext
    exact hσ u
  have hχu : χu ≠ 1 := by
    intro heq
    apply hne
    apply MulChar.ext
    intro u
    have hu := congrArg (fun f : Rˣ →* ℂ => f u) heq
    simpa [χu] using hu
  have hχσu (u : Rˣ) : χu (σu u) = (χu u)⁻¹ := hχσ u
  have hcubicu (u : Rˣ) : χu u ^ 3 = 1 := hcubic u
  obtain ⟨u, huN, huχ⟩ := anticyclotomic_cubic_nontrivial_on_norm_kernel
    χu σu (involutionNorm σu) (involutionNorm_map_involution σu hσu)
    hχσu hcubicu hχu
  have huNorm : (u : R) * σ (u : R) = 1 := by
    exact congrArg (fun v : Rˣ => (v : R)) huN
  have hnorm (z : R) : ((u : R) * z) * σ ((u : R) * z) = z * σ z := by
    rw [map_mul]
    calc
      _ = ((u : R) * σ (u : R)) * (z * σ z) := by ac_rfl
      _ = _ := by rw [huNorm, one_mul]
  have ht := u.mulLeft.bijective.sum_comp (fun z : R => χ z * F (z * σ z))
  change (∑ z : R, χ ((u : R) * z) * F (((u : R) * z) * σ ((u : R) * z))) = _ at ht
  simp_rw [hnorm] at ht
  simp only [map_mul, mul_assoc, ← Finset.mul_sum] at ht
  have hp : (χ (u : R) - 1) * (∑ z : R, χ z * F (z * σ z)) = 0 := by
    linear_combination ht
  exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr huχ)

end ArtinMatthews
