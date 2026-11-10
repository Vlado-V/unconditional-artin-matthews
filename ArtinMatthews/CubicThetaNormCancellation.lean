module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-!
# Cancellation of cubic characters on norm fibers

A nontrivial anticyclotomic cubic character is nontrivial on the norm kernel.
Consequently its sum against every function of the norm vanishes. This is the
finite algebraic cancellation needed when analyzing rational cusp constants;
applying it to the arithmetic residue rings and their cusp weights remains a
separate step.
-/
noncomputable section
open scoped BigOperators Classical

namespace ArtinMatthews

/-- Translation by an element of the norm kernel forces cancellation when
the character is nontrivial on that element. -/
theorem character_sum_norm_weight_eq_zero {G H : Type*} [Group G] [Fintype G]
    [Group H] (χ : G →* ℂ) (N : G →* H) (F : H → ℂ)
    (u : G) (hNu : N u = 1) (hχu : χ u ≠ 1) :
    (∑ g : G, χ g * F (N g)) = 0 := by
  have htrans := (Equiv.mulLeft u).bijective.sum_comp (fun g : G => χ g * F (N g))
  change (∑ g : G, χ (u * g) * F (N (u * g))) = _ at htrans
  simp only [map_mul, hNu, one_mul, mul_assoc, ← Finset.mul_sum] at htrans
  have hprod : (χ u - 1) * (∑ g : G, χ g * F (N g)) = 0 := by
    linear_combination htrans
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hχu)

/-- A cubic character reversed by an automorphism is nontrivial on the
kernel of every homomorphism preserved by that automorphism. -/
theorem anticyclotomic_cubic_nontrivial_on_norm_kernel {G H : Type*}
    [Group G] [Group H] (χ : G →* ℂ) (σ : G ≃* G) (N : G →* H)
    (hσN : ∀ g, N (σ g) = N g)
    (hχσ : ∀ g, χ (σ g) = (χ g)⁻¹)
    (hcubic : ∀ g, χ g ^ 3 = 1) (hne : χ ≠ 1) :
    ∃ u : G, N u = 1 ∧ χ u ≠ 1 := by
  obtain ⟨g, hg⟩ : ∃ g : G, χ g ≠ 1 := by
    by_contra h
    apply hne
    ext g
    change χ g = 1
    push Not at h
    exact h g
  refine ⟨g / σ g, ?_, ?_⟩
  · simp only [map_div, hσN, div_self']
  · rw [map_div, hχσ, div_eq_mul_inv, inv_inv]
    intro hu
    apply hg
    have h3 := hcubic g
    calc
      χ g = (χ g * χ g) * χ g := by rw [hu, one_mul]
      _ = 1 := by simpa only [pow_succ, pow_two, pow_zero, one_mul] using h3

/-- Exact cancellation for every function of the norm, derived from
nontrivial anticyclotomic cubic character hypotheses. -/
theorem anticyclotomic_cubic_sum_norm_weight_eq_zero {G H : Type*}
    [Group G] [Fintype G] [Group H] (χ : G →* ℂ) (σ : G ≃* G) (N : G →* H)
    (hσN : ∀ g, N (σ g) = N g)
    (hχσ : ∀ g, χ (σ g) = (χ g)⁻¹)
    (hcubic : ∀ g, χ g ^ 3 = 1) (hne : χ ≠ 1) (F : H → ℂ) :
    (∑ g : G, χ g * F (N g)) = 0 := by
  obtain ⟨u, huN, huχ⟩ :=
    anticyclotomic_cubic_nontrivial_on_norm_kernel χ σ N hσN hχσ hcubic hne
  exact character_sum_norm_weight_eq_zero χ N F u huN huχ

/-- In particular every individual finite norm fiber has character sum zero. -/
theorem anticyclotomic_cubic_sum_norm_fiber_eq_zero {G H : Type*}
    [Group G] [Fintype G] [Group H] (χ : G →* ℂ) (σ : G ≃* G) (N : G →* H)
    (hσN : ∀ g, N (σ g) = N g)
    (hχσ : ∀ g, χ (σ g) = (χ g)⁻¹)
    (hcubic : ∀ g, χ g ^ 3 = 1) (hne : χ ≠ 1) (h : H) :
    ∑ g ∈ Finset.univ.filter (fun g => N g = h), χ g = 0 := by
  classical
  have hz := anticyclotomic_cubic_sum_norm_weight_eq_zero χ σ N hσN hχσ hcubic hne
    (fun x => if x = h then 1 else 0)
  simpa only [Finset.sum_filter, mul_ite, mul_one, mul_zero] using hz

/-- The norm homomorphism attached to an automorphism of a commutative group. -/
def involutionNorm {G : Type*} [CommGroup G] (σ : G ≃* G) : G →* G :=
  MonoidHom.id G * σ.toMonoidHom

@[simp] theorem involutionNorm_apply {G : Type*} [CommGroup G]
    (σ : G ≃* G) (g : G) : involutionNorm σ g = g * σ g := rfl

/-- For an involution the norm is preserved by conjugation. -/
theorem involutionNorm_map_involution {G : Type*} [CommGroup G]
    (σ : G ≃* G) (hσ : Function.Involutive σ) (g : G) :
    involutionNorm σ (σ g) = involutionNorm σ g := by
  rw [involutionNorm_apply, hσ g, involutionNorm_apply, mul_comm]

/-- Cancellation applies directly to the algebraic norm `g * σ(g)` of an
involution, without requiring a separately postulated norm map. -/
theorem anticyclotomic_cubic_sum_involutionNorm_eq_zero {G : Type*}
    [CommGroup G] [Fintype G] (χ : G →* ℂ) (σ : G ≃* G)
    (hσ : Function.Involutive σ)
    (hχσ : ∀ g, χ (σ g) = (χ g)⁻¹)
    (hcubic : ∀ g, χ g ^ 3 = 1) (hne : χ ≠ 1) (F : G → ℂ) :
    (∑ g : G, χ g * F (g * σ g)) = 0 :=
  anticyclotomic_cubic_sum_norm_weight_eq_zero χ σ (involutionNorm σ)
    (involutionNorm_map_involution σ hσ) hχσ hcubic hne F

end ArtinMatthews
