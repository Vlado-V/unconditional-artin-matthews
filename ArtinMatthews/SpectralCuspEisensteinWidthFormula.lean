module

public import ArtinMatthews.SpectralCuspEisensteinConstantTerm
public import Mathlib.Data.Nat.GCD.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Explicit true widths for every integral cusp chart, in particular the
chart `[[1,0],[-d,1]]` whose inverse has first column `(1,d)`. -/
noncomputable section
open Matrix
open scoped MatrixGroups
namespace ArtinMatthews

theorem nat_div_gcd_mul_dvd_iff (N b : ℕ) (hN : 0 < N) (j : ℕ) :
    N ∣ j*b ↔ N/Nat.gcd N b ∣ j := by
  have hg : 0 < Nat.gcd N b := Nat.gcd_pos_of_pos_left b hN
  have hc := Nat.coprime_div_gcd_div_gcd hg
  constructor
  · intro h
    apply hc.dvd_of_dvd_mul_right
    apply Nat.dvd_of_mul_dvd_mul_right hg
    rw [Nat.div_mul_cancel (Nat.gcd_dvd_left N b),mul_assoc,
      Nat.div_mul_cancel (Nat.gcd_dvd_right N b)]
    exact h
  · rintro ⟨k,rfl⟩
    refine ⟨k*(b/Nat.gcd N b),?_⟩
    calc
      (N/Nat.gcd N b*k)*b=(N/Nat.gcd N b)*(Nat.gcd N b*(b/Nat.gcd N b))*k := by
        rw [Nat.mul_div_cancel' (Nat.gcd_dvd_right N b)]
        ring
      _=((N/Nat.gcd N b)*Nat.gcd N b)*(k*(b/Nat.gcd N b)) := by ring
      _=N*(k*(b/Nat.gcd N b)) := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left N b)]

theorem gamma0CuspTrueWidth_formula (N : ℕ) [NeZero N] (r : SL(2,ℤ)) :
    gamma0CuspTrueWidth N r=N/Nat.gcd N ((r 1 0).natAbs^2) := by
  let b := (r 1 0).natAbs^2
  let L := N/Nat.gcd N b
  have he : (b:ℤ)=(r 1 0)^2 := by
    dsimp [b]
    rw [Int.natCast_natAbs,sq_abs]
  have hL : 0 < L := Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) (Nat.gcd_dvd_left N b))
    (Nat.gcd_pos_of_pos_left b (NeZero.pos N))
  have hpNat : N ∣ L*b := (nat_div_gcd_mul_dvd_iff N b (NeZero.pos N) L).mpr dvd_rfl
  have hp : (N:ℤ) ∣ (L:ℤ)*(r 1 0)^2 := by
    rw [← he]
    exact_mod_cast hpNat
  apply Nat.le_antisymm
  · exact gamma0CuspTrueWidth_minimal N r L hL hp
  · have hw := gamma0CuspTrueWidth_period N r
    rw [← he] at hw
    have hwNat : N ∣ gamma0CuspTrueWidth N r*b := by exact_mod_cast hw
    exact Nat.le_of_dvd (gamma0CuspTrueWidth_pos N r)
      ((nat_div_gcd_mul_dvd_iff N b (NeZero.pos N) _).mp hwNat)

def gamma0CuspOneOver (d : ℕ) : SL(2,ℤ) :=
  ⟨!![1,0;-(d:ℤ),1],by simp [Matrix.det_fin_two]⟩

theorem gamma0CuspOneOver_inverse_first_column (d : ℕ) :
    (gamma0CuspOneOver d)⁻¹ 0 0=1 ∧ (gamma0CuspOneOver d)⁻¹ 1 0=(d:ℤ) := by
  change (Matrix.adjugate (!![1,0;-(d:ℤ),1]:Matrix (Fin 2) (Fin 2) ℤ)) 0 0=1 ∧
    (Matrix.adjugate (!![1,0;-(d:ℤ),1]:Matrix (Fin 2) (Fin 2) ℤ)) 1 0=(d:ℤ)
  simp [Matrix.adjugate_fin_two]

theorem gamma0CuspTrueWidth_oneOver (N : ℕ) [NeZero N] (d : ℕ) :
    gamma0CuspTrueWidth N (gamma0CuspOneOver d)=N/Nat.gcd N (d^2) := by
  rw [gamma0CuspTrueWidth_formula]
  simp [gamma0CuspOneOver]

theorem gamma0CuspEisenstein_oneOver_constant_term (N : ℕ) [NeZero N]
    (d e : ℕ) (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0:ℝ)..1, gamma0CuspEisenstein N (gamma0CuspOneOver e) s
      (gamma0TrueCuspScaling N (gamma0CuspOneOver d) • gamma0EisensteinHorizontalPoint y hy x))=
      gamma0CuspEisensteinIndicator N (gamma0CuspOneOver d) (gamma0CuspOneOver e)*(y:ℂ)^s+
        (y:ℂ)^(1-s)*((N/Nat.gcd N (e^2):ℕ):ℂ)^(-s)*((N/Nat.gcd N (d^2):ℕ):ℂ)^(-s)*
          ((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s)*
            gamma0CuspScatteringDirichlet N (gamma0CuspOneOver d) (gamma0CuspOneOver e) s := by
  rw [gamma0CuspEisenstein_all_cusp_constant_term N _ _ s hs y hy]
  unfold gamma0CuspScattering
  rw [gamma0CuspTrueWidth_oneOver,gamma0CuspTrueWidth_oneOver]
  ring

end ArtinMatthews
