module

public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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


set_option backward.privateInPublic true
@[expose] public section

/-! Exact fixed-unit-progression character expansion for Proposition 3.1.
The original residue indicator is retained on all integers, including the
nonunits where every character and the indicator vanish. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

def giantUnitResidueIndicator {M : ℕ} (U : Finset (ZMod M)ˣ) (z : ZMod M) : ℂ := by
  classical
  exact if z ∈ U.image (fun a : (ZMod M)ˣ => (a : ZMod M)) then 1 else 0

def giantResidueCharacterCoefficient {M : ℕ} (U : Finset (ZMod M)ˣ)
    (χ : DirichletCharacter ℂ M) : ℂ :=
  (M.totient : ℂ)⁻¹ * ∑ a ∈ U, χ ((a : ZMod M)⁻¹)

theorem giantUnitResidueIndicator_eq_sum {M : ℕ} (U : Finset (ZMod M)ˣ) (z : ZMod M) :
    giantUnitResidueIndicator U z = ∑ a ∈ U, if (a : ZMod M) = z then (1 : ℂ) else 0 := by
  classical
  unfold giantUnitResidueIndicator
  by_cases hz : z ∈ U.image (fun a : (ZMod M)ˣ => (a : ZMod M))
  · rw [ite_eq_left hz]
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    symm
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hba
      exact ite_eq_right (fun h => hba (Units.ext h))
    · intro h
      exact (h ha).elim
  · rw [ite_eq_right hz]
    symm
    apply Finset.sum_eq_zero
    intro a ha
    apply ite_eq_right
    intro h
    exact hz (Finset.mem_image.mpr ⟨a,ha,h⟩)

theorem giantUnitResidueIndicator_nonunit {M : ℕ} (U : Finset (ZMod M)ˣ)
    (z : ZMod M) (hz : ¬ IsUnit z) : giantUnitResidueIndicator U z = 0 := by
  classical
  unfold giantUnitResidueIndicator
  apply ite_eq_right
  rintro h
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp h
  exact hz a.isUnit

/-- The exact finite character formula (3.9), valid also on nonunits. -/
theorem giantUnitResidueIndicator_character_expansion {M : ℕ} [NeZero M]
    (U : Finset (ZMod M)ˣ) (z : ZMod M) :
    giantUnitResidueIndicator U z =
      ∑ χ : DirichletCharacter ℂ M, giantResidueCharacterCoefficient U χ * χ z := by
  classical
  have hφ : (M.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos M)).ne'
  symm
  calc
    _ = (M.totient : ℂ)⁻¹ *
        ∑ a ∈ U, ∑ χ : DirichletCharacter ℂ M, χ ((a : ZMod M)⁻¹) * χ z := by
      simp only [giantResidueCharacterCoefficient, mul_assoc, Finset.sum_mul]
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ = (M.totient : ℂ)⁻¹ * ∑ a ∈ U,
        if (a : ZMod M) = z then (M.totient : ℂ) else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      exact DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit z
    _ = ∑ a ∈ U, if (a : ZMod M) = z then (1 : ℂ) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp [hφ]
    _ = giantUnitResidueIndicator U z := (giantUnitResidueIndicator_eq_sum U z).symm

/-- The principal coefficient is precisely the original progression density. -/
theorem giantResidueCharacterCoefficient_principal {M : ℕ}
    (U : Finset (ZMod M)ˣ) :
    giantResidueCharacterCoefficient U 1 = (U.card : ℂ) / M.totient := by
  simp only [giantResidueCharacterCoefficient, ZMod.inv_coe_unit, MulChar.one_apply_coe,
    Finset.sum_const, nsmul_eq_mul, mul_one, div_eq_mul_inv, mul_comm]

/-- Fixed progression restriction is exactly a finite sum of the original
character-weighted sums, with no removal of exceptional integers. -/
theorem giantUnitResidueIndicator_weighted_sum {M : ℕ} [NeZero M]
    (U : Finset (ZMod M)ˣ) (S : Finset ℕ) (w : ℕ → ℂ) :
    (∑ n ∈ S, w n * giantUnitResidueIndicator U (n : ZMod M)) =
      ∑ χ : DirichletCharacter ℂ M, giantResidueCharacterCoefficient U χ *
        ∑ n ∈ S, w n * χ n := by
  classical
  simp_rw [giantUnitResidueIndicator_character_expansion, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  apply Finset.sum_congr rfl
  intro n _
  ring

end
end ArtinMatthews
