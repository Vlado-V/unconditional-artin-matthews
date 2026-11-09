module

public import ArtinMatthews.SpectralTrueWidthBesselPairing
public import ArtinMatthews.SpectralCuspEisensteinInfinity
public import ArtinMatthews.KloostermanWeakBound


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine infinity-cusp reduced matrices at an admissible modulus are
exactly the units modulo that modulus. The lower-right residue is the
unit and the upper-left residue is its inverse. -/

noncomputable section
open Matrix Set
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0TrueWidthReducedMatrix_identity_dvd (N : ℕ) [NeZero N] (c : ℕ)
    (R : gamma0TrueWidthReducedMatrix N 1 1 c) : N ∣ c := by
  have hR : R.val ∈ CongruenceSubgroup.Gamma0 N := by
    simpa only [gamma0CuspCorrespondence,mem_ofPred_eq,inv_one,one_mul,mul_one] using R.property.1
  rw [CongruenceSubgroup.Gamma0_mem,R.property.2.1] at hR
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (c : ℤ) N).mp hR

theorem gamma0TrueWidthReducedMatrix_identity_bounds (N : ℕ) [NeZero N] (c : ℕ)
    (R : gamma0TrueWidthReducedMatrix N 1 1 c) :
    (0 ≤ R.val 0 0 ∧ R.val 0 0 < (c : ℤ)) ∧ (0 ≤ R.val 1 1 ∧ R.val 1 1 < (c : ℤ)) := by
  obtain ⟨_,_,ha0,ha,hd0,hd⟩ := R.property
  simp only [gamma0CuspTrueWidth_identity,Nat.cast_one,one_mul] at ha hd
  exact ⟨⟨ha0,ha⟩,⟨hd0,hd⟩⟩

def gamma0InfinityReducedUnit (N : ℕ) [NeZero N] (c : ℕ) [NeZero c]
    (R : gamma0TrueWidthReducedMatrix N 1 1 c) : (ZMod c)ˣ := by
  have hdet : R.val 0 0*R.val 1 1-R.val 0 1*(c : ℤ) = 1 := by
    have h := R.val.prop
    rwa [Matrix.det_fin_two,R.property.2.1] at h
  have h := congrArg (fun z : ℤ => (z : ZMod c)) hdet
  push_cast at h
  simp only [ZMod.natCast_self,mul_zero,sub_zero] at h
  exact ⟨(R.val 1 1 : ZMod c),(R.val 0 0 : ZMod c),by simpa only [mul_comm] using h,h⟩

theorem gamma0InfinityReducedUnit_val (N : ℕ) [NeZero N] (c : ℕ) [NeZero c]
    (R : gamma0TrueWidthReducedMatrix N 1 1 c) :
    (gamma0InfinityReducedUnit N c R : ZMod c) = (R.val 1 1 : ZMod c) := rfl

theorem gamma0InfinityReducedUnit_inv_val (N : ℕ) [NeZero N] (c : ℕ) [NeZero c]
    (R : gamma0TrueWidthReducedMatrix N 1 1 c) :
    (((gamma0InfinityReducedUnit N c R)⁻¹ : (ZMod c)ˣ) : ZMod c) = (R.val 0 0 : ZMod c) := rfl

def gamma0InfinityUnitReducedMatrix (N : ℕ) [NeZero N] (c : ℕ) [NeZero c]
    (hNc : N ∣ c) (u : (ZMod c)ˣ) : gamma0TrueWidthReducedMatrix N 1 1 c := by
  let a : ℤ := ((u⁻¹ : (ZMod c)ˣ) : ZMod c).val
  let d : ℤ := (u : ZMod c).val
  have hprod : ((a*d-1 : ℤ) : ZMod c) = 0 := by
    simp only [a,d,Int.cast_sub,Int.cast_mul,Int.cast_natCast,ZMod.natCast_zmod_val,Int.cast_one,Units.inv_mul,sub_self]
  have hbex : (c : ℤ) ∣ a*d-1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ c).mp hprod
  let b := Classical.choose hbex
  have hb : a*d-1 = (c : ℤ)*b := Classical.choose_spec hbex
  let M : SL(2, ℤ) := ⟨!![a,b;(c : ℤ),d],by
    rw [Matrix.det_fin_two]
    change a*d-b*(c : ℤ) = 1
    linarith [hb]⟩
  have hM : M ∈ gamma0CuspCorrespondence N 1 1 := by
    have h : ((c : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr (by exact_mod_cast hNc)
    simp only [gamma0CuspCorrespondence,mem_ofPred_eq,inv_one,one_mul,mul_one,CongruenceSubgroup.Gamma0_mem]
    change ((c : ℤ) : ZMod N) = 0
    exact h
  refine ⟨M,hM,rfl,?_,?_,?_,?_⟩
  · change 0 ≤ a
    exact Int.natCast_nonneg _
  · simp only [gamma0CuspTrueWidth_identity,Nat.cast_one,one_mul]
    change a < (c : ℤ)
    dsimp only [a]
    exact_mod_cast ZMod.val_lt ((u⁻¹ : (ZMod c)ˣ) : ZMod c)
  · change 0 ≤ d
    exact Int.natCast_nonneg _
  · simp only [gamma0CuspTrueWidth_identity,Nat.cast_one,one_mul]
    change d < (c : ℤ)
    dsimp only [d]
    exact_mod_cast ZMod.val_lt (u : ZMod c)

theorem spectral_intCast_injective_on_residues {c : ℕ} {a b : ℤ}
    (ha : 0 ≤ a ∧ a < (c : ℤ)) (hb : 0 ≤ b ∧ b < (c : ℤ))
    (h : (a : ZMod c) = (b : ZMod c)) : a = b := by
  have he := (ZMod.intCast_eq_intCast_iff a b c).mp h
  change a % (c : ℤ) = b % (c : ℤ) at he
  rwa [Int.emod_eq_of_lt ha.1 ha.2,Int.emod_eq_of_lt hb.1 hb.2] at he

theorem gamma0InfinityReducedUnit_bijective (N : ℕ) [NeZero N] (c : ℕ) [NeZero c]
    (hNc : N ∣ c) : Function.Bijective (gamma0InfinityReducedUnit N c) := by
  constructor
  · intro R S h
    have hR := gamma0TrueWidthReducedMatrix_identity_bounds N c R
    have hS := gamma0TrueWidthReducedMatrix_identity_bounds N c S
    have ha : (R.val 0 0 : ZMod c) = (S.val 0 0 : ZMod c) :=
      congrArg (fun u : (ZMod c)ˣ => ((u⁻¹ : (ZMod c)ˣ) : ZMod c)) h
    have hd : (R.val 1 1 : ZMod c) = (S.val 1 1 : ZMod c) :=
      congrArg (fun u : (ZMod c)ˣ => (u : ZMod c)) h
    apply Subtype.ext
    exact specialLinear_eq_of_diagonal_lower (by exact_mod_cast NeZero.ne c) R.val S.val
      R.property.2.1 S.property.2.1 (spectral_intCast_injective_on_residues hR.1 hS.1 ha)
      (spectral_intCast_injective_on_residues hR.2 hS.2 hd)
  · intro u
    refine ⟨gamma0InfinityUnitReducedMatrix N c hNc u,?_⟩
    apply Units.ext
    change ((((u : ZMod c).val : ℤ) : ZMod c)) = (u : ZMod c)
    rw [Int.cast_natCast,ZMod.natCast_zmod_val]

def gamma0InfinityReducedUnitEquiv (N : ℕ) [NeZero N] (c : ℕ) [NeZero c]
    (hNc : N ∣ c) : gamma0TrueWidthReducedMatrix N 1 1 c ≃ (ZMod c)ˣ :=
  Equiv.ofBijective (gamma0InfinityReducedUnit N c) (gamma0InfinityReducedUnit_bijective N c hNc)

end ArtinMatthews
