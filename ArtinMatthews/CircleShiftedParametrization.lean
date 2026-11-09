module

public import ArtinMatthews.CircleShiftedFrequency


set_option backward.privateInPublic true
@[expose] public section

/-! Exact parametrization of the shifted equation and its d-congruence.
The coprimality hypotheses are the ones supplied by squarefree source integers. -/

noncomputable section
namespace ArtinMatthews

theorem circleShiftedFrequency_zero_iff (m3 m4 : ℕ) (k : ℕ×ℕ)
    (hk1 : 1≤k.1) (hk2 : 1≤k.2) :
    circleShiftedFrequency m3 m4 k=0 ↔ m4*(k.1-1)=m3*(k.2-1) := by
  simp only [circleShiftedFrequency,sub_eq_zero]
  have hc : ((m4*(k.1-1) : ℕ) : ℤ)=((m3*(k.2-1) : ℕ) : ℤ) ↔
      m4*(k.1-1)=m3*(k.2-1) := by norm_cast
  simpa only [Nat.cast_mul,Nat.cast_sub hk1,Nat.cast_sub hk2,Nat.cast_one] using hc

theorem circleShifted_parametrization (d m3 m4 : ℕ) (hm3 : 0 < m3)
    (h34 : m3.Coprime m4) (h3d : m3.Coprime d)
    (k : ℕ×ℕ) (hk1 : 1≤k.1) (hk2 : 1≤k.2) :
    (circleShiftedFrequency m3 m4 k=0 ∧ (d : ℤ)∣((k.1 : ℤ)-1)) ↔
      ∃ n : ℕ, k.1=d*m3*n+1 ∧ k.2=d*m4*n+1 := by
  have hsub : ((k.1-1 : ℕ) : ℤ)=(k.1 : ℤ)-1 := by
    simp only [Nat.cast_sub hk1,Nat.cast_one]
  rw [circleShiftedFrequency_zero_iff m3 m4 k hk1 hk2,← hsub]
  constructor
  · rintro ⟨heq,hd⟩
    have hd' : d∣k.1-1 := by exact_mod_cast hd
    have h3 : m3∣k.1-1 := h34.dvd_of_dvd_mul_left (heq ▸ dvd_mul_right m3 (k.2-1))
    obtain ⟨n,hn⟩ := h3d.symm.mul_dvd_of_dvd_of_dvd hd' h3
    refine ⟨n,?_,?_⟩
    · omega
    · have hmul : m3*(d*m4*n)=m3*(k.2-1) := by
        calc
          _ = m4*(d*m3*n) := by ring
          _ = m4*(k.1-1) := by rw [hn]
          _ = _ := heq
      have hh := Nat.eq_of_mul_eq_mul_left hm3 hmul
      omega
  · rintro ⟨n,h1,h2⟩
    rw [h1,h2]
    simp only [Nat.add_sub_cancel]
    constructor
    · ring
    · exact_mod_cast (show d∣d*m3*n from ⟨m3*n,by ring⟩)

end ArtinMatthews
