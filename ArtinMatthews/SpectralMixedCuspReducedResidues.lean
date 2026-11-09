module

public import ArtinMatthews.SpectralMixedCuspNormalization


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine true-width reduced mixed cusp matrices give the actual
ABL Atkin-Lehner residue pair, with the exact translated lower-right
coordinate and the resulting admissible moduli. -/

noncomputable section
open Matrix Set
open scoped MatrixGroups

namespace ArtinMatthews

def gamma0MixedReducedShiftedRight (r s c : ℕ) [NeZero r] [NeZero s] (b : ℤ)
    (R : gamma0TrueWidthReducedMatrix (r*s) (gamma0CuspOneOver s) 1 (s*c)) : ℤ :=
  (R.val 1 1+((s*c : ℕ) : ℤ)*b)/(r : ℤ)

theorem gamma0MixedReduced_shifted_right_eq (r s c : ℕ) [NeZero r] [NeZero s]
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (R : gamma0TrueWidthReducedMatrix (r*s) (gamma0CuspOneOver s) 1 (s*c)) :
    (r : ℤ)*gamma0MixedReducedShiftedRight r s c b R = R.val 1 1+((s*c : ℕ) : ℤ)*b := by
  obtain ⟨k,hk⟩ := gamma0MixedReduced_lower_right_congruence r s c R
  have hd : (r : ℤ) ∣ R.val 1 1+((s*c : ℕ) : ℤ)*b := by
    refine ⟨(c : ℤ)*a-k,?_⟩
    simp only [Nat.cast_mul]
    linear_combination -hk-(c : ℤ)*hab
  unfold gamma0MixedReducedShiftedRight
  rw [mul_comm]
  exact Int.ediv_mul_cancel hd

theorem gamma0MixedReduced_shifted_det (r s c : ℕ) [NeZero r] [NeZero s]
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (R : gamma0TrueWidthReducedMatrix (r*s) (gamma0CuspOneOver s) 1 (s*c)) :
    (r : ℤ)*R.val 0 0*gamma0MixedReducedShiftedRight r s c b R-
      (s : ℤ)*(c : ℤ)*(R.val 0 1+R.val 0 0*b) = 1 := by
  have hR := R.val.prop
  rw [Matrix.det_fin_two,R.property.2.1] at hR
  have hD := gamma0MixedReduced_shifted_right_eq r s c hab R
  simp only [Nat.cast_mul] at hR hD
  linear_combination R.val 0 0*hD+hR

theorem gamma0MixedReduced_parameter_coprime (r s c : ℕ) [NeZero r] [NeZero s]
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (R : gamma0TrueWidthReducedMatrix (r*s) (gamma0CuspOneOver s) 1 (s*c)) : r.Coprime c := by
  simpa only [Int.natAbs_natCast] using atkinMixed_constraint_coprime (gamma0MixedReduced_shifted_det r s c hab R)

theorem gamma0MixedReduced_modulus_shape (r s q : ℕ) [NeZero r] [NeZero s] [NeZero q]
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (R : gamma0TrueWidthReducedMatrix (r*s) (gamma0CuspOneOver s) 1 q) :
    ∃ c : ℕ, 0 < c ∧ q = s*c ∧ r.Coprime c := by
  obtain ⟨c,rfl⟩ := gamma0MixedReduced_lower_dvd r s q R
  exact ⟨c,Nat.pos_of_ne_zero (right_ne_zero_of_mul (NeZero.ne (s*c))),rfl,
    gamma0MixedReduced_parameter_coprime r s c hab R⟩

def gamma0MixedReducedResiduePair (r s c : ℕ) [NeZero r] [NeZero s] [NeZero c]
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (R : gamma0TrueWidthReducedMatrix (r*s) (gamma0CuspOneOver s) 1 (s*c)) :
    ↥(atkinMixedResiduePairs (NeZero.pos r) hab c) := by
  refine ⟨((R.val 0 0 : ZMod (s*c)),(gamma0MixedReducedShiftedRight r s c b R : ZMod (s*c))),
    (mem_atkinMixedResiduePairs_iff (NeZero.pos r) hab c _).mpr ?_⟩
  have h := congrArg (fun v : ℤ => (v : ZMod (s*c))) (gamma0MixedReduced_shifted_det r s c hab R)
  push_cast at h
  have hQ : (s : ZMod (s*c))*(c : ZMod (s*c)) = 0 := by rw [← Nat.cast_mul,ZMod.natCast_self]
  rw [hQ,zero_mul,sub_zero] at h
  exact h

theorem gamma0MixedReducedResiduePair_injective (r s c : ℕ) [NeZero r] [NeZero s] [NeZero c]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1) :
    Function.Injective (gamma0MixedReducedResiduePair r s c hab) := by
  intro R S h
  have hA : (R.val 0 0 : ZMod (s*c)) = (S.val 0 0 : ZMod (s*c)) :=
    congrArg (fun ad : ↥(atkinMixedResiduePairs (NeZero.pos r) hab c) => ad.val.1) h
  have hD : (gamma0MixedReducedShiftedRight r s c b R : ZMod (s*c)) =
      (gamma0MixedReducedShiftedRight r s c b S : ZMod (s*c)) :=
    congrArg (fun ad : ↥(atkinMixedResiduePairs (NeZero.pos r) hab c) => ad.val.2) h
  have hRa : R.val 0 0 < ((s*c : ℕ) : ℤ) := by
    simpa only [gamma0CuspTrueWidth_identity,Nat.cast_one,one_mul] using R.property.2.2.2.1
  have hSa : S.val 0 0 < ((s*c : ℕ) : ℤ) := by
    simpa only [gamma0CuspTrueWidth_identity,Nat.cast_one,one_mul] using S.property.2.2.2.1
  have hRd : R.val 1 1 < ((r*(s*c) : ℕ) : ℤ) := by
    simpa only [gamma0MixedCusp_trueWidth r s hcop,Nat.cast_mul] using R.property.2.2.2.2.2
  have hSd : S.val 1 1 < ((r*(s*c) : ℕ) : ℤ) := by
    simpa only [gamma0MixedCusp_trueWidth r s hcop,Nat.cast_mul] using S.property.2.2.2.2.2
  have hDmod : Int.ModEq ((r*(s*c) : ℕ) : ℤ) (R.val 1 1) (S.val 1 1) := by
    obtain ⟨k,hk⟩ := ((ZMod.intCast_eq_intCast_iff _ _ _).mp hD).dvd
    apply Int.modEq_iff_dvd.mpr
    refine ⟨k,?_⟩
    have hR := gamma0MixedReduced_shifted_right_eq r s c hab R
    have hS := gamma0MixedReduced_shifted_right_eq r s c hab S
    simp only [Nat.cast_mul] at hk hR hS ⊢
    linear_combination (r : ℤ)*hk-hS+hR
  apply Subtype.ext
  exact specialLinear_eq_of_diagonal_lower (by exact_mod_cast NeZero.ne (s*c)) R.val S.val
    R.property.2.1 S.property.2.1
    (spectral_intCast_injective_on_residues ⟨R.property.2.2.1,hRa⟩ ⟨S.property.2.2.1,hSa⟩ hA)
    (spectral_intCast_injective_on_residues ⟨R.property.2.2.2.2.1,hRd⟩ ⟨S.property.2.2.2.2.1,hSd⟩
      ((ZMod.intCast_eq_intCast_iff _ _ _).mpr hDmod))

end ArtinMatthews
