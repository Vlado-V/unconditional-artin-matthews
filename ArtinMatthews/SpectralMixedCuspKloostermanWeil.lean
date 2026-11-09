module

public import ArtinMatthews.SpectralMixedCuspSourcePhase
public import ArtinMatthews.AtkinLehnerMixedWeight


set_option backward.privateInPublic true
@[expose] public section

/-! The actual ABL mixed sum has the same all-frequency Weil envelope as
the ordinary sum at modulus `s*c`. Only one frequency is multiplied by
a unit, and its full common gcd with the other frequency is preserved. -/

noncomputable section
open scoped MatrixGroups
open OAI.Erdos970.ErdosKloosterman

namespace ArtinMatthews

theorem spectral_frequencyGcd_mul_right_unit (q : ℕ) (u v m n : ℤ)
    (huv : (q : ℤ) ∣ u*v-1) :
    Nat.gcd q (Int.gcd (m*v) n) = Nat.gcd q (Int.gcd m n) := by
  change frequencyGcd q (m*v) n = frequencyGcd q m n
  apply Nat.dvd_antisymm
  · obtain ⟨hD,hm,hn⟩ := (dvd_frequencyGcd_iff _ _ _ _).mp (dvd_refl (frequencyGcd q (m*v) n))
    have hD' : (frequencyGcd q (m*v) n : ℤ) ∣ (q : ℤ) := by exact_mod_cast hD
    refine (dvd_frequencyGcd_iff _ _ _ _).mpr ⟨hD,?_,hn⟩
    have h := dvd_sub (dvd_mul_of_dvd_right hm u) (dvd_mul_of_dvd_left (hD'.trans huv) m)
    have he : u*(m*v)-(u*v-1)*m = m := by ring
    rwa [he] at h
  · obtain ⟨hD,hm,hn⟩ := (dvd_frequencyGcd_iff _ _ _ _).mp (dvd_refl (frequencyGcd q m n))
    exact (dvd_frequencyGcd_iff _ _ _ _).mpr ⟨hD,dvd_mul_of_dvd_left hm v,hn⟩

def spectral_inverseUnitRepresentative (r q : ℕ) [NeZero q] (hrq : r.Coprime q) : ℤ :=
  (((((ZMod.unitOfCoprime r hrq)⁻¹ : (ZMod q)ˣ) : ZMod q).val : ℕ) : ℤ)

theorem spectral_inverseUnitRepresentative_cast (r q : ℕ) [NeZero q] (hrq : r.Coprime q) :
    (spectral_inverseUnitRepresentative r q hrq : ZMod q) =
      (((ZMod.unitOfCoprime r hrq)⁻¹ : (ZMod q)ˣ) : ZMod q) := by
  simp only [spectral_inverseUnitRepresentative,Int.cast_natCast,ZMod.natCast_zmod_val]

theorem spectral_inverseUnitRepresentative_inverse (r q : ℕ) [NeZero q] (hrq : r.Coprime q) :
    (q : ℤ) ∣ (r : ℤ)*spectral_inverseUnitRepresentative r q hrq-1 := by
  let u := ZMod.unitOfCoprime r hrq
  have hu : (u : ZMod q) = (r : ZMod q) := ZMod.coe_unitOfCoprime r hrq
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  rw [Int.cast_sub,Int.cast_mul,Int.cast_natCast,Int.cast_one,
    spectral_inverseUnitRepresentative_cast,← hu]
  exact sub_eq_zero.mpr u.val_inv

theorem gamma0MixedKloosterman_eq_source_standard (r s c : ℕ) [NeZero r] [NeZero s] [NeZero c]
    (hcop : r.Coprime s) (hrc : r.Coprime c) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (m n : ℤ) :
    let hrq : r.Coprime (s*c) := Nat.coprime_mul_iff_right.mpr ⟨hcop,hrc⟩
    gamma0TrueWidthKloostermanSum (r*s) (gamma0CuspOneOver s) 1 (s*c) n m =
      atkinPhase (-(n : ℝ)*(b : ℝ)/(r : ℝ))*
        standardSum (s*c) (m*spectral_inverseUnitRepresentative r (s*c) hrq) n := by
  dsimp only
  rw [gamma0MixedKloosterman_eq_source_ordinary r s c hcop hrc hab,standardSum,
    Int.cast_mul,spectral_inverseUnitRepresentative_cast]

theorem gamma0MixedKloosterman_weil {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (r s q : ℕ) [NeZero r] [NeZero s] [NeZero q],
      r.Coprime s → ∀ m n : ℤ,
      ‖gamma0TrueWidthKloostermanSum (r*s) (gamma0CuspOneOver s) 1 q n m‖ ≤
        D*(q : ℝ)^((1/2 : ℝ)+ε)*((Nat.gcd q (Int.gcd m n) : ℕ) : ℝ)^(1/2 : ℝ) := by
  obtain ⟨D,hD,hW⟩ := standardKloosterman_weil_bound hε
  refine ⟨D,hD,?_⟩
  intro r s q _ _ _ hcop m n
  obtain ⟨a,b,hab⟩ := exists_atkin_bezout hcop
  by_cases hq : ∃ c : ℕ, 0 < c ∧ q = s*c ∧ r.Coprime c
  · obtain ⟨c,hc,rfl,hrc⟩ := hq
    let _ : NeZero c := ⟨hc.ne'⟩
    let hrq : r.Coprime (s*c) := Nat.coprime_mul_iff_right.mpr ⟨hcop,hrc⟩
    rw [gamma0MixedKloosterman_eq_source_standard r s c hcop hrc hab,norm_mul,atkinPhase_norm,one_mul]
    have hb := hW (s*c) (m*spectral_inverseUnitRepresentative r (s*c) hrq) n
    rw [spectral_frequencyGcd_mul_right_unit _ (r : ℤ) _ m n
      (spectral_inverseUnitRepresentative_inverse r (s*c) hrq)] at hb
    exact hb
  · rw [gamma0MixedKloosterman_zero_off_source_moduli r s q hcop hab m n hq,norm_zero]
    positivity

end ArtinMatthews
