module

public import ArtinMatthews.CubicSieveDivisorHyperbola
public import ArtinMatthews.CubicSieveDivisorProgression


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform floor error for the divisor hyperbola in an actual unit class.
The finite main term keeps the coprime harmonic sum and coprime count. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

def cubicSieveUnitRow (d a N : ℕ) (u : (ZMod d)ˣ) : ℝ :=
  ∑ b ∈ Icc 1 N, if ((a * b : ℕ) : ZMod d) = (u : ZMod d) then 1 else 0

def cubicSieveDivisorUnitCount (d X : ℕ) (u : (ZMod d)ˣ) : ℝ :=
  ∑ n ∈ Icc 1 X, (n.divisors.card : ℝ) *
    (if (n : ZMod d) = (u : ZMod d) then 1 else 0)

def cubicSieveDivisorUnitMain (d X : ℕ) : ℝ :=
  let C := (Icc 1 X.sqrt).filter (fun a => a.Coprime d)
  2 * ((X : ℝ) / d) * (∑ a ∈ C, (a : ℝ)⁻¹) - ((X.sqrt : ℝ) / d) * (C.card : ℝ)

theorem cubicSieve_unitRow_of_not_coprime {d a N : ℕ}
    (u : (ZMod d)ˣ) (ha : ¬a.Coprime d) :
    cubicSieveUnitRow d a N u = 0 := by
  unfold cubicSieveUnitRow
  apply sum_eq_zero
  intro b _
  apply ite_eq_right
  intro h
  rw [Nat.cast_mul] at h
  exact ha ((ZMod.isUnit_iff_coprime a d).mp
    (isUnit_of_mul_isUnit_left (h ▸ u.isUnit : IsUnit ((a : ZMod d) * b))))

theorem cubicSieve_unitRow_error (d a N : ℕ) (hd : 0 < d) (u : (ZMod d)ˣ) :
    |cubicSieveUnitRow d a N u - (if a.Coprime d then (N : ℝ) / d else 0)| ≤ 1 := by
  by_cases ha : a.Coprime d
  · let _ : NeZero d := ⟨hd.ne'⟩
    let v : (ZMod d)ˣ := (ZMod.unitOfCoprime a ha)⁻¹ * u
    have hclass (b : ℕ) : ((a * b : ℕ) : ZMod d) = (u : ZMod d) ↔
        Nat.ModEq d b (v : ZMod d).val :=
      (cubicSieve_unit_progression_quotient ha u b).trans (by
        simpa only [ZMod.natCast_zmod_val] using
          ZMod.natCast_eq_natCast_iff b (v : ZMod d).val d)
    have hI : Icc 1 N = Ioc 0 N := by
      ext b
      simp only [mem_Icc, mem_Ioc]
      omega
    have hrow : cubicSieveUnitRow d a N u =
        (((Ioc 0 N).filter fun b => Nat.ModEq d b (v : ZMod d).val).card : ℝ) := by
      unfold cubicSieveUnitRow
      simp_rw [hclass]
      rw [hI, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    rw [hrow, ite_eq_left ha]
    simpa only [Nat.cast_zero, sub_zero] using
      marked_interval_residue_error 0 N d (v : ZMod d).val (Nat.zero_le N) hd
  · rw [cubicSieve_unitRow_of_not_coprime u ha, ite_eq_right ha]
    norm_num

private theorem cubicSieve_cast_divided_floor_error (d a X : ℕ)
    (hd : 0 < d) (ha : 0 < a) :
    |(((X / a : ℕ) : ℝ) / d) - ((X : ℝ) / a / d)| ≤ 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hlow : ((X / a : ℕ) : ℝ) ≤ (X : ℝ) / a := Nat.cast_div_le
  have hhigh : (X : ℝ) / a ≤ ((X / a : ℕ) : ℝ) + 1 := by
    apply (div_le_iff₀ haR).mpr
    have h : X ≤ (X / a + 1) * a := by
      have hm := Nat.mod_lt X ha
      have hq := Nat.mod_add_div X a
      rw [Nat.add_mul, one_mul, Nat.mul_comm (X / a) a]
      omega
    exact_mod_cast h
  have hlow' := div_le_div_of_nonneg_right hlow hdR.le
  have hhigh' := div_le_div_of_nonneg_right hhigh hdR.le
  rw [add_div] at hhigh'
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hone := (div_le_one hdR).mpr hd1
  exact abs_le.mpr ⟨by linarith only [hhigh', hone], by linarith only [hlow']⟩

private theorem cubicSieve_unitRow_div_error (d a X : ℕ)
    (hd : 0 < d) (ha : 0 < a) (u : (ZMod d)ˣ) :
    |cubicSieveUnitRow d a (X / a) u -
      (if a.Coprime d then (X : ℝ) / a / d else 0)| ≤ 2 := by
  by_cases h : a.Coprime d
  · rw [ite_eq_left h]
    have h1 := cubicSieve_unitRow_error d a (X / a) hd u
    rw [ite_eq_left h] at h1
    exact (abs_sub_le _ (((X / a : ℕ) : ℝ) / d) _).trans
      (by linarith only [h1, cubicSieve_cast_divided_floor_error d a X hd ha])
  · rw [cubicSieve_unitRow_of_not_coprime u h, ite_eq_right h]
    norm_num

private theorem cubicSieve_sum_row_error {α : Type*} (s : Finset α) (f g : α → ℝ)
    (C : ℝ) (h : ∀ a ∈ s, |f a - g a| ≤ C) :
    |(∑ a ∈ s, f a) - (∑ a ∈ s, g a)| ≤ (s.card : ℝ) * C := by
  rw [← sum_sub_distrib]
  exact (abs_sum_le_sum_abs _ _).trans (by
    simpa only [sum_const, nsmul_eq_mul] using sum_le_sum h)

theorem cubicSieve_divisorUnitCount_error (d X : ℕ) (hd : 0 < d) (u : (ZMod d)ˣ) :
    |cubicSieveDivisorUnitCount d X u - cubicSieveDivisorUnitMain d X| ≤
      5 * (X.sqrt : ℝ) := by
  let m := X.sqrt
  let S := Icc 1 m
  let A := ∑ a ∈ S, cubicSieveUnitRow d a (X / a) u
  let B := ∑ a ∈ S, cubicSieveUnitRow d a m u
  let A₀ := ∑ a ∈ S, if a.Coprime d then (X : ℝ) / a / d else 0
  let B₀ := ∑ a ∈ S, if a.Coprime d then (m : ℝ) / d else 0
  have hS : S.card = m := by
    unfold S
    rw [Nat.card_Icc]
    omega
  have hA : |A - A₀| ≤ (m : ℝ) * 2 := by
    simpa only [hS] using cubicSieve_sum_row_error S
      (fun a => cubicSieveUnitRow d a (X / a) u)
      (fun a => if a.Coprime d then (X : ℝ) / a / d else 0) 2
      (fun a ha => cubicSieve_unitRow_div_error d a X hd (mem_Icc.mp ha).1 u)
  have hB : |B - B₀| ≤ (m : ℝ) * 1 := by
    simpa only [hS] using cubicSieve_sum_row_error S
      (fun a => cubicSieveUnitRow d a m u)
      (fun a => if a.Coprime d then (m : ℝ) / d else 0) 1
      (fun a _ => cubicSieve_unitRow_error d a m hd u)
  have hcount : cubicSieveDivisorUnitCount d X u = 2 * A - B :=
    cubicSieve_divisorCount_hyperbola X (fun n =>
      if (n : ZMod d) = (u : ZMod d) then 1 else 0)
  have hmain : cubicSieveDivisorUnitMain d X = 2 * A₀ - B₀ := by
    unfold cubicSieveDivisorUnitMain A₀ B₀
    change 2 * ((X : ℝ) / d) * (∑ a ∈ S.filter (fun a => a.Coprime d), (a : ℝ)⁻¹) -
      ((m : ℝ) / d) * ((S.filter (fun a => a.Coprime d)).card : ℝ) = _
    rw [← sum_filter, ← sum_filter, sum_const, nsmul_eq_mul, mul_comm ((m : ℝ) / d),
      mul_assoc, mul_sum]
    congr 1
    congr 1
    apply sum_congr rfl
    intro a _
    ring
  rw [hcount, hmain, show (2 * A - B) - (2 * A₀ - B₀) = 2 * (A - A₀) - (B - B₀) by ring]
  calc
    _ ≤ |2 * (A - A₀)| + |B - B₀| := abs_sub _ _
    _ ≤ 5 * (X.sqrt : ℝ) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      change 2 * |A - A₀| + |B - B₀| ≤ 5 * (m : ℝ)
      linarith only [hA, hB]

end ArtinMatthews
