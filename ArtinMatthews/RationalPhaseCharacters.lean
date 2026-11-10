module

public import ArtinMatthews.DirichletUnitFourier
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open Finset
open scoped BigOperators
noncomputable section

variable (r : ℕ) [NeZero r]

def rationalPhaseCharacterCoefficient (u : ℤ) (χ : DirichletCharacter ℂ r) : ℂ :=
  dirichletUnitFourierCoefficient r
    (fun a => ZMod.stdAddChar ((u : ZMod r) * (a : ZMod r))) χ

theorem rationalPhaseCharacterCoefficient_eq_gaussSum (u : ℤ)
    (χ : DirichletCharacter ℂ r) :
    rationalPhaseCharacterCoefficient r u χ =
      (r.totient : ℂ)⁻¹ * gaussSum (star χ) (ZMod.stdAddChar.mulShift (u : ZMod r)) := by
  classical
  unfold rationalPhaseCharacterCoefficient dirichletUnitFourierCoefficient
  congr 1
  let e : (ZMod r)ˣ ↪ ZMod r := ⟨Units.val, Units.val_injective⟩
  have hsum := Finset.sum_subset (Finset.subset_univ (Finset.univ.map e))
    (f := fun a : ZMod r => (star χ) a * ZMod.stdAddChar ((u : ZMod r) * a))
    (fun a _ ha => ?_)
  · simpa only [Finset.sum_map, e, Function.Embedding.coeFn_mk,
      MulChar.star_apply, mul_comm, gaussSum, AddChar.mulShift_apply] using hsum
  · have hnunit : ¬ IsUnit a := by
      intro h
      apply ha
      exact Finset.mem_map.mpr ⟨h.unit, Finset.mem_univ _, h.unit_spec⟩
    rw [(star χ).map_nonunit hnunit, zero_mul]

theorem rationalPhaseCharacterCoefficient_l1_le (u : ℤ) :
    (∑ χ : DirichletCharacter ℂ r, ‖rationalPhaseCharacterCoefficient r u χ‖) ≤
      Real.sqrt (r.totient : ℝ) := by
  apply dirichletUnitFourier_l1_bound
  intro a
  rw [ZMod.stdAddChar_apply]
  simp

theorem rationalPhase_stdAddChar (u : ℤ) (n : ℕ) :
    ZMod.stdAddChar ((u : ZMod r) * (n : ZMod r)) =
      (Real.fourierChar ((u : ℝ) * (n : ℝ) / (r : ℝ)) : ℂ) := by
  rw [show (u : ZMod r) * (n : ZMod r) = ((u * (n : ℤ) : ℤ) : ZMod r) by
    push_cast
    rfl]
  rw [ZMod.stdAddChar_coe, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

theorem rationalPhase_eq_character_sum (u : ℤ) (n : ℕ) (hn : n.Coprime r) :
    (Real.fourierChar ((u : ℝ) * (n : ℝ) / (r : ℝ)) : ℂ) =
      ∑ χ : DirichletCharacter ℂ r,
        rationalPhaseCharacterCoefficient r u χ * χ (n : ZMod r) := by
  simpa only [rationalPhaseCharacterCoefficient, ZMod.coe_unitOfCoprime,
    rationalPhase_stdAddChar] using
    (dirichletUnitFourier_inversion r
      (fun a => ZMod.stdAddChar ((u : ZMod r) * (a : ZMod r)))
      (ZMod.unitOfCoprime n hn)).symm

theorem rationalPhase_bilinear_character_sum (u : ℤ) (n m : ℕ)
    (hn : n.Coprime r) (hm : m.Coprime r) :
    (Real.fourierChar ((u : ℝ) * (n : ℝ) * (m : ℝ) / (r : ℝ)) : ℂ) =
      ∑ χ : DirichletCharacter ℂ r,
        rationalPhaseCharacterCoefficient r u χ * χ (n : ZMod r) * χ (m : ZMod r) := by
  have h := rationalPhase_eq_character_sum r u (n * m) (hn.mul_left hm)
  simpa only [Nat.cast_mul, map_mul, mul_assoc] using h

end
end ArtinMatthews
