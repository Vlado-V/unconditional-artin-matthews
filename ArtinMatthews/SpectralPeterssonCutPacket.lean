module

public import ArtinMatthews.SpectralPeterssonCutPeriodization
public import ArtinMatthews.SpectralPeterssonMass


set_option backward.privateInPublic true
@[expose] public section

/-! Finite normalized holomorphic packets keep the same sharp scaled
height cut at every frequency. -/
noncomputable section
open Set Matrix UpperHalfPlane
open scoped MatrixGroups BigOperators

namespace ArtinMatthews

variable {ι : Type*}

def spectralPeterssonCutPacketSeed (k : ℕ) (t : Finset ι) (α : ι → ℂ)
    (n : ι → ℕ+) (A : ℝ) (z : UpperHalfPlane) : ℂ :=
  ∑ j ∈ t, α j*(spectralPeterssonNormalization k (n j) : ℂ)*spectralPeterssonHeightCutSeed (n j) A z

def gamma0PeterssonCutPacket (N : ℕ) [NeZero N] (a : SL(2, ℤ)) (k : ℕ)
    (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+) (A : ℝ) (z : UpperHalfPlane) : ℂ :=
  ∑ j ∈ t, α j*(spectralPeterssonNormalization k (n j) : ℂ)*gamma0PeterssonTruncatedPoincare N a k (n j) A z

def gamma0PeterssonCutPacketRow (N : ℕ) [NeZero N] (a : SL(2, ℤ)) (k : ℕ)
    (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+) (A : ℝ)
    (p : Gamma0PeterssonSignedRow N 1 a) (z : UpperHalfPlane) : ℂ :=
  ∑ j ∈ t, α j*(spectralPeterssonNormalization k (n j) : ℂ)*gamma0PeterssonCutRow N a k (n j) A p z

theorem gamma0PeterssonCutPacketRow_eq_slash (N : ℕ) [NeZero N] (a : SL(2, ℤ)) (k : ℕ)
    (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+) (A : ℝ)
    (p : Gamma0PeterssonSignedRow N 1 a) (z : UpperHalfPlane) :
    gamma0PeterssonCutPacketRow N a k t α n A p z =
      spectralHolomorphicSlash k (gamma0TrueWidthMatrix N 1 a (gamma0PeterssonRowMatrix N 1 a p).val)
        (spectralPeterssonCutPacketSeed k t α n A) z := by
  unfold gamma0PeterssonCutPacketRow spectralPeterssonCutPacketSeed
  simp_rw [gamma0PeterssonCutRow_eq_slash,spectralHolomorphicSlash_apply]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem gamma0PeterssonCutPacket_eq_rows (N : ℕ) [NeZero N] (a : SL(2, ℤ)) (k : ℕ)
    (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+) {A : ℝ} (hA : 0 < A) (z : UpperHalfPlane) :
    gamma0PeterssonCutPacket N a k t α n A z =
      (1/2 : ℂ)*∑' p : Gamma0PeterssonSignedRow N 1 a, gamma0PeterssonCutPacketRow N a k t α n A p z := by
  have hs (j : ι) : Summable (fun p =>
      (α j*(spectralPeterssonNormalization k (n j) : ℂ))*gamma0PeterssonCutRow N a k (n j) A p z) :=
    (summable_of_hasFiniteSupport (gamma0PeterssonCutRow_hasFiniteSupport N a k (n j) hA z)).mul_left _
  symm
  unfold gamma0PeterssonCutPacketRow gamma0PeterssonCutPacket gamma0PeterssonTruncatedPoincare
  rw [Summable.tsum_finsetSum (fun j _ => hs j),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [tsum_mul_left]
  ring

theorem spectralPeterssonCutPacketSeed_translate (k : ℕ) (t : Finset ι) (α : ι → ℂ)
    (n : ι → ℕ+) (A : ℝ) (l : ℤ) (z : UpperHalfPlane) :
    spectralPeterssonCutPacketSeed k t α n A (realTranslation (l : ℝ) • z) =
      spectralPeterssonCutPacketSeed k t α n A z := by
  simp only [spectralPeterssonCutPacketSeed,spectralPeterssonHeightCutSeed_translate]

theorem gamma0PeterssonCutPacketRow_height (N : ℕ) [NeZero N] (a : SL(2, ℤ)) (k : ℕ)
    (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+) (A B : ℝ) (hB : 0 < B)
    (hnB : ∀ j ∈ t, (n j : ℝ) ≤ B) (p : Gamma0PeterssonSignedRow N 1 a) (z : UpperHalfPlane)
    (hrow : gamma0PeterssonCutPacketRow N a k t α n A p z ≠ 0) :
    A/(4*Real.pi*B) < gamma0PeterssonRowHeight N a p z := by
  classical
  obtain ⟨j,hj,hjv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hrow
  have hcutrow : gamma0PeterssonCutRow N a k (n j) A p z ≠ 0 :=
    (mul_ne_zero_iff.mp hjv).2
  have hcut : A < 4*Real.pi*(n j : ℝ)*gamma0PeterssonRowHeight N a p z := by
    by_contra h
    exact hcutrow (by simp only [gamma0PeterssonCutRow,ite_eq_right h])
  have hh : 0 < gamma0PeterssonRowHeight N a p z := UpperHalfPlane.im_pos _
  apply (div_lt_iff₀ (by positivity : 0 < 4*Real.pi*B)).mpr
  have hle : 4*Real.pi*(n j : ℝ)*gamma0PeterssonRowHeight N a p z ≤
      4*Real.pi*B*gamma0PeterssonRowHeight N a p z := by gcongr; exact hnB j hj
  simpa only [mul_comm] using hcut.trans_le hle

end ArtinMatthews
