module

public import ArtinMatthews.SpectralPeterssonCutNormUnfold
public import ArtinMatthews.SpectralPeterssonCutPacketPointwise
public import ArtinMatthews.SpectralPeterssonCutMeasurable


set_option backward.privateInPublic true
@[expose] public section

/-! The actual normalized sharp-cut Poincare packet has a congruence-level
L2 bound, including weight two, before any holomorphic reproduction step. -/
noncomputable section
open Set MeasureTheory UpperHalfPlane
open scoped MatrixGroups BigOperators

namespace ArtinMatthews

variable {ι : Type*}

private theorem cutPacket_norm_of_pointwise (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (hk : 2 ≤ k) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+)
    {A : ℝ} (hA : 0 < A) (hn : Set.InjOn n (t : Set ι)) (C : ℝ)
    (hbound : ∀ z : UpperHalfPlane,
      ‖gamma0PeterssonCutPacket N a k t α n A z‖^2*z.im^k ≤
        C*(∑' p : Gamma0PeterssonSignedRow N 1 a,
          ‖gamma0PeterssonCutPacketRow N a k t α n A p z‖^2*z.im^k)) :
    IntegrableOn (fun z => ‖gamma0PeterssonCutPacket N a k t α n A z‖^2*z.im^k)
      (gamma0InteriorRegion N) ∧
    (∫ z in gamma0InteriorRegion N, ‖gamma0PeterssonCutPacket N a k t α n A z‖^2*z.im^k) ≤
      2*C*(spectralPeterssonGammaTailRatio k A*∑ j ∈ t, ‖α j‖^2) := by
  let R (z : UpperHalfPlane) := ∑' p : Gamma0PeterssonSignedRow N 1 a,
    ‖gamma0PeterssonCutPacketRow N a k t α n A p z‖^2*z.im^k
  have hR : IntegrableOn R (gamma0InteriorRegion N) :=
    gamma0PeterssonCutPacket_row_integrable N a k hk t α n A hA.le hn
  have hEnv := hR.const_mul C
  have hmeas : Measurable (fun z : UpperHalfPlane =>
      ‖gamma0PeterssonCutPacket N a k t α n A z‖^2*z.im^k) :=
    ((gamma0PeterssonCutPacket_measurable N a k t α n hA).norm.pow_const 2).mul
      (by fun_prop)
  have hInt : IntegrableOn (fun z : UpperHalfPlane =>
      ‖gamma0PeterssonCutPacket N a k t α n A z‖^2*z.im^k) (gamma0InteriorRegion N) := by
    apply hEnv.mono' hmeas.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg z.im_pos.le _))]
    exact hbound z
  refine ⟨hInt,?_⟩
  calc
    _ ≤ ∫ z in gamma0InteriorRegion N, C*R z :=
      integral_mono hInt hEnv (fun z => hbound z)
    _ = _ := by
      rw [integral_const_mul,gamma0PeterssonCutPacket_row_mass N a k hk t α n A hA.le hn]
      ring

theorem gamma0PeterssonCutPacket_infinity_norm (N : ℕ) [NeZero N]
    (k : ℕ) (hk : 2 ≤ k) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hn : Set.InjOn n (t : Set ι))
    (hnB : ∀ j ∈ t, (n j : ℝ) ≤ B) :
    IntegrableOn (fun z => ‖gamma0PeterssonCutPacket N 1 k t α n A z‖^2*z.im^k)
      (gamma0InteriorRegion N) ∧
    (∫ z in gamma0InteriorRegion N, ‖gamma0PeterssonCutPacket N 1 k t α n A z‖^2*z.im^k) ≤
      2*(1+8*Real.pi*B/((N : ℝ)*A))*(spectralPeterssonGammaTailRatio k A*∑ j ∈ t, ‖α j‖^2) :=
  cutPacket_norm_of_pointwise N 1 k hk t α n hA hn _
    (gamma0PeterssonCutPacket_infinity_pointwise N k t α n hA hB hnB)

theorem gamma0PeterssonCutPacket_mixed_norm (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) (k : ℕ) (hk : 2 ≤ k) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hn : Set.InjOn n (t : Set ι))
    (hnB : ∀ j ∈ t, (n j : ℝ) ≤ B) :
    IntegrableOn (fun z => ‖gamma0PeterssonCutPacket (r*s) (gamma0CuspOneOver s) k t α n A z‖^2*z.im^k)
      (gamma0InteriorRegion (r*s)) ∧
    (∫ z in gamma0InteriorRegion (r*s), ‖gamma0PeterssonCutPacket (r*s) (gamma0CuspOneOver s) k t α n A z‖^2*z.im^k) ≤
      2*(1+8*Real.pi*B/(((r*s : ℕ) : ℝ)*A))*(spectralPeterssonGammaTailRatio k A*∑ j ∈ t, ‖α j‖^2) :=
  cutPacket_norm_of_pointwise (r*s) (gamma0CuspOneOver s) k hk t α n hA hn _
    (gamma0PeterssonCutPacket_mixed_pointwise r s hcop k t α n hA hB hnB)

end ArtinMatthews
