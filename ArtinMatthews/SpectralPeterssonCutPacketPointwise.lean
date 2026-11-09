module

public import ArtinMatthews.SpectralPeterssonCutPacket
public import ArtinMatthews.SpectralPeterssonCutRowCount


set_option backward.privateInPublic true
@[expose] public section

/-! Pointwise Cauchy--Schwarz on the actual finite set of sharp-cut
parabolic rows. The congruence-level overlap bound is uniform in weight. -/
noncomputable section
open Set UpperHalfPlane
open scoped MatrixGroups BigOperators

namespace ArtinMatthews

variable {ι : Type*}

theorem gamma0PeterssonCutPacketRow_hasFiniteSupport (N : ℕ) [NeZero N]
    (a : SL(2, ℤ)) (k : ℕ) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+)
    {A : ℝ} (hA : 0 < A) (z : UpperHalfPlane) :
    Function.HasFiniteSupport (fun p => gamma0PeterssonCutPacketRow N a k t α n A p z) := by
  have h (j : ι) : Function.HasFiniteSupport (fun p =>
      α j*(spectralPeterssonNormalization k (n j) : ℂ)*gamma0PeterssonCutRow N a k (n j) A p z) :=
    Function.HasFiniteSupport.mul_right _ (gamma0PeterssonCutRow_hasFiniteSupport N a k (n j) hA z)
  simpa only [gamma0PeterssonCutPacketRow] using Function.HasFiniteSupport.sum h t

private theorem half_sum_norm_sq_le {β : Type*} (s : Finset β) (F : β → ℂ) :
    ‖(1/2 : ℂ)*∑ p ∈ s, F p‖^2 ≤ (s.card : ℝ)/4*∑ p ∈ s, ‖F p‖^2 := by
  have hsum := norm_sum_le s F
  have hn : 0 ≤ ∑ p ∈ s, ‖F p‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hsq : ‖∑ p ∈ s, F p‖^2 ≤ (∑ p ∈ s, ‖F p‖)^2 :=
    (sq_le_sq₀ (norm_nonneg _) hn).mpr hsum
  have hcs : (∑ p ∈ s, ‖F p‖)^2 ≤ (s.card : ℝ)*∑ p ∈ s, ‖F p‖^2 := by
    simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] using
      (Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun p => ‖F p‖))
  have he : ‖(1/2 : ℂ)*∑ p ∈ s, F p‖^2 = (1/4 : ℝ)*‖∑ p ∈ s, F p‖^2 := by
    rw [norm_mul,mul_pow]
    norm_num
  rw [he]
  nlinarith

theorem gamma0PeterssonCutPacket_pointwise_of_count (N : ℕ) [NeZero N]
    (a : SL(2, ℤ)) (k : ℕ) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+)
    {A B M : ℝ} (hA : 0 < A) (hB : 0 < B) (z : UpperHalfPlane)
    (hnB : ∀ j ∈ t, (n j : ℝ) ≤ B)
    (hcount : ∀ T : Finset (Gamma0PeterssonSignedRow N 1 a),
      (∀ p ∈ T, A/(4*Real.pi*B) ≤ gamma0PeterssonRowHeight N a p z) → (T.card : ℝ) ≤ M) :
    ‖gamma0PeterssonCutPacket N a k t α n A z‖^2*z.im^k ≤
      (M/4)*(∑' p : Gamma0PeterssonSignedRow N 1 a,
        ‖gamma0PeterssonCutPacketRow N a k t α n A p z‖^2*z.im^k) := by
  classical
  let F := fun p => gamma0PeterssonCutPacketRow N a k t α n A p z
  have hfin := gamma0PeterssonCutPacketRow_hasFiniteSupport N a k t α n hA z
  let T := hfin.toFinset
  have hmem (p : Gamma0PeterssonSignedRow N 1 a) : p ∈ T ↔ F p ≠ 0 := by
    change p ∈ hfin.toFinset ↔ p ∈ Function.support _
    exact Set.Finite.mem_toFinset hfin
  have hzero (p : Gamma0PeterssonSignedRow N 1 a) (hp : p ∉ T) : F p = 0 :=
    not_ne_iff.mp (fun h => hp ((hmem p).mpr h))
  have hc : (T.card : ℝ) ≤ M := hcount T (fun p hp =>
    (gamma0PeterssonCutPacketRow_height N a k t α n A B hB hnB p z ((hmem p).mp hp)).le)
  have htsum : (∑' p, F p) = ∑ p ∈ T, F p := tsum_eq_sum hzero
  have hmass : (∑' p, ‖F p‖^2*z.im^k) = ∑ p ∈ T, ‖F p‖^2*z.im^k := by
    apply tsum_eq_sum
    intro p hp
    rw [hzero p hp,norm_zero,zero_pow (by omega : 2 ≠ 0),zero_mul]
  have hnorm := half_sum_norm_sq_le T F
  have hnonneg : 0 ≤ ∑ p ∈ T, ‖F p‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [gamma0PeterssonCutPacket_eq_rows N a k t α n hA z,htsum,hmass,← Finset.sum_mul]
  calc
    _ ≤ ((T.card : ℝ)/4*(∑ p ∈ T, ‖F p‖^2))*z.im^k :=
      mul_le_mul_of_nonneg_right hnorm (pow_nonneg z.im_pos.le _)
    _ ≤ ((M/4)*(∑ p ∈ T, ‖F p‖^2))*z.im^k :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hc (by norm_num)) hnonneg)
        (pow_nonneg z.im_pos.le _)
    _ = _ := by ring

theorem gamma0PeterssonCutPacket_infinity_pointwise (N : ℕ) [NeZero N]
    (k : ℕ) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hnB : ∀ j ∈ t, (n j : ℝ) ≤ B)
    (z : UpperHalfPlane) :
    ‖gamma0PeterssonCutPacket N 1 k t α n A z‖^2*z.im^k ≤
      (1+8*Real.pi*B/((N : ℝ)*A))*(∑' p : Gamma0PeterssonSignedRow N 1 1,
        ‖gamma0PeterssonCutPacketRow N 1 k t α n A p z‖^2*z.im^k) := by
  have ht : 0 < A/(4*Real.pi*B) := by positivity
  have h := gamma0PeterssonCutPacket_pointwise_of_count N 1 k t α n hA hB z hnB
    (fun T hT => gamma0PeterssonHeightRows_infinity_card N z _ ht T hT)
  have he : 4*(1+2/((N : ℝ)*(A/(4*Real.pi*B))))/4 = 1+8*Real.pi*B/((N : ℝ)*A) := by
    have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
    field_simp
    <;> ring
  rwa [he] at h

theorem gamma0PeterssonCutPacket_mixed_pointwise (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) (k : ℕ) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hnB : ∀ j ∈ t, (n j : ℝ) ≤ B)
    (z : UpperHalfPlane) :
    ‖gamma0PeterssonCutPacket (r*s) (gamma0CuspOneOver s) k t α n A z‖^2*z.im^k ≤
      (1+8*Real.pi*B/(((r*s : ℕ) : ℝ)*A))*(∑' p : Gamma0PeterssonSignedRow (r*s) 1 (gamma0CuspOneOver s),
        ‖gamma0PeterssonCutPacketRow (r*s) (gamma0CuspOneOver s) k t α n A p z‖^2*z.im^k) := by
  have ht : 0 < A/(4*Real.pi*B) := by positivity
  have h := gamma0PeterssonCutPacket_pointwise_of_count (r*s) (gamma0CuspOneOver s) k t α n hA hB z hnB
    (fun T hT => gamma0PeterssonHeightRows_mixed_card r s hcop z _ ht T hT)
  have he : 4*(1+2/(((r*s : ℕ) : ℝ)*(A/(4*Real.pi*B))))/4 = 1+8*Real.pi*B/(((r*s : ℕ) : ℝ)*A) := by
    have hN : ((r*s : ℕ) : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (r*s)
    field_simp
    <;> ring
  rwa [he] at h

end ArtinMatthews
