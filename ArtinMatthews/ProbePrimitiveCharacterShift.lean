module

public import OAI.NumberTheory.DirichletL.FiniteFourier
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! Primitive additive characters of a finite Frobenius ring differ by a
unit shift.  The multiplier is obtained from actual finite Fourier
inversion, not supplied as a comparison hypothesis. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open OAI.SevenEighths.FiniteFourier
open scoped BigOperators Classical
noncomputable section

variable {R : Type*} [CommRing R] [Fintype R]

theorem probe_addChar_exists_shift (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (φ : AddChar R ℂ) : ∃ a : R, ψ.mulShift a = φ := by
  have hi := transform_inversion ψ hψ (fun x => φ x) 0
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one] at hi
  have hs : (∑ a : R, transform ψ (fun x => φ x) a) ≠ 0 := by
    rw [hi]
    exact_mod_cast Fintype.card_ne_zero
  obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  have hprod : φ * ψ.mulShift a = 1 := by
    by_contra hn
    apply ha
    have hz := AddChar.sum_eq_zero_of_ne_one hn
    simpa only [transform, AddChar.mul_apply, AddChar.mulShift_apply] using hz
  have hφ : φ = (ψ.mulShift a)⁻¹ := by
    calc
      φ = (φ * ψ.mulShift a) * (ψ.mulShift a)⁻¹ := by group
      _ = (ψ.mulShift a)⁻¹ := by rw [hprod, one_mul]
  refine ⟨-a, ?_⟩
  rw [hφ]
  ext x
  simp only [AddChar.mulShift_apply, AddChar.inv_apply, mul_neg, neg_mul]

theorem probe_addChar_exists_unit_shift (ψ φ : AddChar R ℂ)
    (hψ : ψ.IsPrimitive) (hφ : φ.IsPrimitive) :
    ∃ u : Rˣ, ψ.mulShift (u : R) = φ := by
  obtain ⟨a, ha⟩ := probe_addChar_exists_shift ψ hψ φ
  have hu : IsUnit a := by
    by_contra hn
    obtain ⟨b, hb, hab⟩ := exists_nonzero_annihilator hn
    have he : φ.mulShift b = 1 := by
      rw [← ha, AddChar.mulShift_mulShift, hab, AddChar.mulShift_zero]
    exact hφ hb he
  exact ⟨hu.unit, by simpa only [hu.unit_spec] using ha⟩

omit [Fintype R] in
theorem probe_addChar_primitive_unit_shift (ψ : AddChar R ℂ)
    (hψ : ψ.IsPrimitive) (u : Rˣ) : (ψ.mulShift (u : R)).IsPrimitive := by
  intro a ha
  rw [AddChar.mulShift_mulShift]
  apply hψ
  intro he
  apply ha
  have h := congrArg (fun x : R => (↑u⁻¹ : R) * x) he
  simpa only [← mul_assoc, Units.inv_mul, one_mul, mul_zero] using h

end

end ArtinMatthews.VaryingKummerAnalytic
