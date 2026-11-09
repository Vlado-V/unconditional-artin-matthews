module

public import ArtinMatthews.CubicFrobeniusCondition
public import OAI.NumberTheory.DirichletL.Reciprocity.CubicJacobi


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Frobenius action on cubic radicals agrees with the cubic residue symbol. -/

namespace ArtinMatthews

theorem cube_roots_eq_of_reduction_eq {R : Type*} [CommRing R] [IsDomain R]
    (Q : Ideal R) [Q.IsPrime] (hthree : (3 : R) ∉ Q) {x y : R}
    (hy : y ∉ Q) (hpow : x ^ 3 = y ^ 3)
    (hred : Ideal.Quotient.mk Q x = Ideal.Quotient.mk Q y) : x = y := by
  by_contra hne
  have hprod : (x - y) * (x ^ 2 + x * y + y ^ 2) = 0 := by
    calc
      _ = x ^ 3 - y ^ 3 := by ring
      _ = 0 := sub_eq_zero.mpr hpow
  have hsum : x ^ 2 + x * y + y ^ 2 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)
  have hq := congrArg (Ideal.Quotient.mk Q) hsum
  have hzero : (3 : R ⧸ Q) * (Ideal.Quotient.mk Q y) ^ 2 = 0 := by
    calc
      _ = (Ideal.Quotient.mk Q y) ^ 2 + Ideal.Quotient.mk Q y * Ideal.Quotient.mk Q y +
          (Ideal.Quotient.mk Q y) ^ 2 := by ring
      _ = 0 := by simpa only [map_add, map_mul, map_pow, map_zero, hred] using hq
  rcases mul_eq_zero.mp hzero with h3 | hy0
  · exact hthree ((Ideal.Quotient.eq_zero_iff_mem (I := Q)).mp h3)
  · exact hy ((Ideal.Quotient.eq_zero_iff_mem (I := Q)).mp
      ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hy0))

open OAI OAI.ActualEisensteinCubic

section SymbolAction

variable {R G : Type*} [CommRing R] [IsDomain R]
    [Algebra OAI.ActualEisensteinCubic.O R] [Group G] [MulSemiringAction G R]
    [SMulCommClass G OAI.ActualEisensteinCubic.O R]

local notation "EO" => OAI.ActualEisensteinCubic.O

/-- This compares the genuine arithmetic Frobenius congruence with the
genuine finite-field cubic residue character; no reciprocity correspondence
is assumed as an input. -/
theorem arithFrob_cubic_symbol_action (P : Ideal EO) [P.IsMaximal]
    (Q : Ideal R) [Q.IsPrime] [Q.LiesOver P] (hg : lambda ∉ P)
    (σ : G) (hF : IsArithFrobAt EO σ Q) {a : EO} (ha : a ∉ P)
    {x : R} (hx : x ^ 3 = algebraMap EO R a) :
    σ • x = algebraMap EO R (cubicChar P hg (Ideal.Quotient.mk P a)) * x := by
  classical
  let c := cubicChar P hg (Ideal.Quotient.mk P a)
  let N := Nat.card (EO ⧸ P)
  let m := (N - 1) / 3
  have hcard : Nat.card (EO ⧸ Q.under EO) = N := by rw [← Ideal.over_def Q P]
  have haR : algebraMap EO R a ∉ Q := by
    intro h
    apply ha
    change a ∈ Q.under EO at h
    rwa [← Ideal.over_def Q P] at h
  have hxQ : x ∉ Q := by
    intro h
    apply haR
    rw [← hx]
    exact Q.pow_mem_of_mem h 3 (by decide)
  have hthreeP : (3 : EO) ∉ P := by
    intro h
    have hlam : lambda ^ 2 = (-3 : EO) * omega := by
      change (omega - 1) ^ 2 = (-3 : EO) * omega
      linear_combination omega_sq_for_norm
    have hsq : lambda ^ 2 ∈ P := by rw [hlam]; exact P.mul_mem_right _ (P.neg_mem h)
    exact hg ((Ideal.IsPrime.mem_of_pow_mem (inferInstance : P.IsPrime) 2 hsq))
  have hthreeQ : (3 : R) ∉ Q := by
    intro h
    apply hthreeP
    have hh : (3 : EO) ∈ Q.under EO := by change algebraMap EO R 3 ∈ Q; simpa only [map_ofNat] using h
    rwa [← Ideal.over_def Q P] at hh
  have hc3 : c ^ 3 = 1 := OAI.CubicRamified.cubicValue_cube P hg a ha
  have hpow : (σ • x) ^ 3 = (algebraMap EO R c * x) ^ 3 := by
    rw [mul_pow, ← map_pow, hc3, map_one, one_mul, hx]
    rw [← smul_pow', hx, smul_algebraMap]
  let j : EO ⧸ P →+* R ⧸ Q := algebraMap (EO ⧸ P) (R ⧸ Q)
  have hcReduce : Ideal.Quotient.mk Q (algebraMap EO R c) =
      (Ideal.Quotient.mk Q (algebraMap EO R a)) ^ m := by
    have h := congrArg j (cubicChar_reduce P hg (Ideal.Quotient.mk P a))
    simpa only [j, c, m, N, map_pow, Ideal.Quotient.algebraMap_mk_of_liesOver] using h
  have hNm : 3 * m + 1 = N := by
    have hdiv : 3 ∣ N - 1 := card_sub_one_div_three P hg
    have hpos : 0 < N := Nat.card_pos
    have hmul := Nat.div_mul_cancel hdiv
    dsimp [m]
    omega
  have hred : Ideal.Quotient.mk Q (σ • x) =
      Ideal.Quotient.mk Q (algebraMap EO R c * x) := by
    have h := hF.mk_apply x
    change Ideal.Quotient.mk Q (σ • x) = (Ideal.Quotient.mk Q x) ^ _ at h
    rw [hcard] at h
    rw [h, map_mul, hcReduce, ← hx, map_pow, ← pow_mul, ← hNm, pow_add, pow_one]
  apply cube_roots_eq_of_reduction_eq Q hthreeQ _ hpow hred
  intro h
  exact hxQ ((inferInstance : Q.IsPrime).mem_or_mem h |>.resolve_left (by
    intro hc
    have hc0 : Ideal.Quotient.mk Q (algebraMap EO R c) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem (I := Q)).mpr hc
    have hh := congrArg (fun t : R => Ideal.Quotient.mk Q t) (show (algebraMap EO R c) ^ 3 = 1 by
      rw [← map_pow, hc3, map_one])
    exact zero_ne_one (by
      simpa only [map_pow, map_one, hc0, zero_pow (by decide : (3 : ℕ) ≠ 0)] using hh)))

end SymbolAction

end ArtinMatthews
