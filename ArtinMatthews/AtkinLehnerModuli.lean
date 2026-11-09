module

public import ArtinMatthews.AtkinLehnerNormalizer


set_option backward.privateInPublic true
@[expose] public section

/-! The exact allowable moduli at the actual same Atkin-Lehner cusp. -/
namespace ArtinMatthews

open Matrix CongruenceSubgroup

theorem exists_atkin_bezout {r s : ℕ} (hrs : r.Coprime s) :
    ∃ a b : ℤ, (r : ℤ)*a-(s : ℤ)*b = 1 := by
  refine ⟨Nat.gcdA r s,-Nat.gcdB r s,?_⟩
  rw [mul_neg,sub_neg_eq_add,← Nat.gcd_eq_gcd_ab,hrs.gcd_eq_one]
  rfl

/-- The literal conjugated-group definition of an allowable positive modulus. -/
def atkinSameCuspAllowed {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (c : ℝ) : Prop :=
  0 < c ∧ ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Gamma0 (r*s) ∧
    ((atkinScaling hr hab)⁻¹ * atkinRealMap γ * atkinScaling hr hab) 1 0 = c

/-- All and only the positive integer multiples of the actual level occur as
lower-left entries of the same-cusp conjugated group. -/
theorem atkinSameCuspAllowed_iff {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (c : ℝ) :
    atkinSameCuspAllowed hr hab c ↔ 0 < c ∧ ∃ k : ℤ, c = ((r*s : ℕ) : ℝ)*(k : ℝ) := by
  constructor
  · rintro ⟨hc,γ,hγ,hentry⟩
    obtain ⟨δ,hδ,hconj⟩ := atkinScaling_normalizes_forward hr hab γ hγ
    have he := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) ℝ => g 1 0) hconj
    change _ = (δ 1 0 : ℝ) at he
    have hdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd (δ 1 0) (r*s)).mp (Gamma0_mem.mp hδ)
    obtain ⟨k,hk⟩ := hdiv
    refine ⟨hc,k,?_⟩
    calc
      c = (δ 1 0 : ℝ) := hentry.symm.trans he
      _ = ((r*s : ℕ) : ℝ)*(k : ℝ) := by rw [hk]; push_cast; rfl
  · rintro ⟨hc,k,hk⟩
    let δ := atkinGammaSL r s 1 0 k 1 (by ring)
    have hδ : δ ∈ Gamma0 (r*s) := atkinGammaSL_mem r s 1 0 k 1 (by ring)
    obtain ⟨γ,hγ,hback⟩ := atkinScaling_normalizes_backward hr hab δ hδ
    have hconj : (atkinScaling hr hab)⁻¹ * atkinRealMap γ * atkinScaling hr hab =
        atkinRealMap δ := by rw [← hback]; group
    refine ⟨hc,γ,hγ,?_⟩
    rw [hconj]
    change (((r : ℤ)*(s : ℤ)*k : ℤ) : ℝ) = c
    rw [hk]
    push_cast
    ring

theorem atkinSameCuspAllowed_nat_iff {r s c : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) :
    atkinSameCuspAllowed hr hab (c : ℝ) ↔ 0 < c ∧ r*s ∣ c := by
  rw [atkinSameCuspAllowed_iff]
  constructor
  · rintro ⟨hc,k,hk⟩
    have hd : ((r*s : ℕ) : ℤ) ∣ (c : ℤ) := ⟨k,by exact_mod_cast hk⟩
    exact ⟨by exact_mod_cast hc,Int.natCast_dvd_natCast.mp hd⟩
  · rintro ⟨hc,k,hk⟩
    exact ⟨by exact_mod_cast hc,(k : ℤ),by exact_mod_cast hk⟩

end ArtinMatthews
