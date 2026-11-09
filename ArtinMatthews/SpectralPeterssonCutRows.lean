module

public import ArtinMatthews.SpectralPeterssonParabolicUnfold
public import ArtinMatthews.SpectralPeterssonPoincare
public import ArtinMatthews.SpectralCuspHeightRowCount
public import ArtinMatthews.SpectralCuspEisensteinParabolic


set_option backward.privateInPublic true
@[expose] public section

/-! The literal sharp height cut has finitely many contributing parabolic
rows at every point, for every weight, including weight two. -/
noncomputable section
open Set Matrix UpperHalfPlane
open scoped MatrixGroups

namespace ArtinMatthews

def gamma0PeterssonEisensteinRow (N : ℕ) (a : SL(2, ℤ))
    (p : Gamma0PeterssonSignedRow N 1 a) : Gamma0CuspEisensteinRows N 1 a :=
  ⟨p.val,by
    obtain ⟨M,hM⟩ := p.property
    exact ⟨M,hM⟩⟩

theorem gamma0PeterssonEisensteinRow_injective (N : ℕ) (a : SL(2, ℤ)) :
    Function.Injective (gamma0PeterssonEisensteinRow N a) := by
  intro p q h
  exact Subtype.ext (congrArg Subtype.val h)

def gamma0PeterssonRowHeight (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (p : Gamma0PeterssonSignedRow N 1 a) (z : UpperHalfPlane) : ℝ :=
  ((gamma0TrueWidthMatrix N 1 a (gamma0PeterssonRowMatrix N 1 a p).val) • z).im

theorem gamma0PeterssonRowHeight_eq (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (p : Gamma0PeterssonSignedRow N 1 a) (z : UpperHalfPlane) :
    gamma0PeterssonRowHeight N a p z =
      cuspEisensteinRowHeight N 1 a (gamma0PeterssonEisensteinRow N a p) z /
        (gamma0CuspTrueWidth N a : ℝ) := by
  have hD : cuspWidthDilation (gamma0CuspTrueWidth N 1 : ℝ)
      (by exact_mod_cast gamma0CuspTrueWidth_pos N 1) = (1 : SL(2, ℝ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cuspWidthDilation,gamma0CuspTrueWidth_identity]
  unfold gamma0PeterssonRowHeight gamma0TrueWidthMatrix
  rw [hD,mul_one,mul_smul,atkinRealMap_smul,
    cuspWidthDilation_im_inv_smul]
  congr 1

def gamma0PeterssonCutRow (N : ℕ) [NeZero N] (a : SL(2, ℤ)) (k : ℕ)
    (n : ℕ+) (A : ℝ) (p : Gamma0PeterssonSignedRow N 1 a) (z : UpperHalfPlane) : ℂ :=
  if A < 4*Real.pi*(n : ℝ)*gamma0PeterssonRowHeight N a p z then
    gamma0PeterssonSignedSummand N 1 a k (n : ℕ) p z else 0

def gamma0PeterssonTruncatedPoincare (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (n : ℕ+) (A : ℝ) (z : UpperHalfPlane) : ℂ :=
  (1/2 : ℂ)*∑' p : Gamma0PeterssonSignedRow N 1 a, gamma0PeterssonCutRow N a k n A p z

theorem gamma0PeterssonCutRow_hasFiniteSupport (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (n : ℕ+) {A : ℝ} (hA : 0 < A) (z : UpperHalfPlane) :
    Function.HasFiniteSupport (fun p => gamma0PeterssonCutRow N a k n A p z) := by
  let w : ℝ := (gamma0CuspTrueWidth N a : ℝ)
  let rate : ℝ := 4*Real.pi*(n : ℝ)
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N a)
  have hr : 0 < rate := by dsimp [rate]; positivity
  have ht : 0 < w*(A/rate) := by positivity
  have hf := cuspEisensteinHeightRows_finite N a z ht
  have hpre : ((gamma0PeterssonEisensteinRow N a) ⁻¹'
      {v | w*(A/rate) ≤ cuspEisensteinRowHeight N 1 a v z}).Finite :=
    Set.Finite.preimage (gamma0PeterssonEisensteinRow_injective N a).injOn hf
  apply hpre.subset
  intro p hp
  have hcut : A < rate*gamma0PeterssonRowHeight N a p z := by
    by_contra h
    exact hp (by simpa only [gamma0PeterssonCutRow,rate,ite_eq_right h])
  rw [gamma0PeterssonRowHeight_eq] at hcut
  have h := (div_lt_iff₀ hr).mpr (by simpa only [mul_comm] using hcut)
  have h' := (lt_div_iff₀ hw).mp h
  simpa only [Set.mem_preimage,Set.mem_setOf_eq,mul_comm] using h'.le

end ArtinMatthews
