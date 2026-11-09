module

public import ArtinMatthews.SpectralPeterssonCutPacketPairing
public import ArtinMatthews.SpectralPeterssonCutComparison


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform holomorphic packet density from the actual height-cut
Poincare vectors. The constants are independent of the even weight. -/
noncomputable section
open Set Matrix MeasureTheory UpperHalfPlane
open scoped MatrixGroups ModularForm BigOperators

namespace ArtinMatthews

variable {ι : Type*}

theorem gamma0PeterssonSourceInfinityPacket_density (N k : ℕ) [NeZero N]
    (hk : 2 ≤ k) (hEven : Even k) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hn : Set.InjOn n (t : Set ι))
    (hnB : ∀ j ∈ t, (n j : ℝ) ≤ B) :
    (∫ z in gamma0InteriorRegion N, ‖gamma0PeterssonSourceInfinityPacket N k t α n z‖^2*z.im^k) ≤
      2*Real.exp A*(1+8*Real.pi*B/((N : ℝ)*A))*(∑ j ∈ t, ‖α j‖^2) := by
  let F := gamma0PeterssonSourceInfinityPacketForm N k hk hEven t α n
  have hFeq : ⇑F = gamma0PeterssonSourceInfinityPacket N k t α n :=
    gamma0PeterssonSourceInfinityPacketForm_coe N k hk hEven t α n
  have hFLp : MemLp (spectralPeterssonHilbertProfile k (gamma0PeterssonSourceInfinityPacket N k t α n)) 2
      (volume.restrict (gamma0InteriorRegion N)) := by
    rw [← hFeq]
    exact gamma0PeterssonCuspPacket_memLp N k F
  have hcut := gamma0PeterssonCutPacket_infinity_norm N k hk t α n hA hB hn hnB
  have hPLp := spectralPeterssonHilbertProfile_memLp_of_integrable N k
    (gamma0PeterssonCutPacket N 1 k t α n A)
    (gamma0PeterssonCutPacket_measurable N 1 k t α n hA) hcut.1
  have hpair := gamma0PeterssonCutPacket_infinity_pairing N k hk hEven t α n A hA F
  rw [hFeq] at hpair
  exact gamma0Petersson_density_of_cut N k _ _ hFLp hPLp A (spectralPeterssonGammaTailRatio k A)
    (1+8*Real.pi*B/((N : ℝ)*A)) (∑ j ∈ t, ‖α j‖^2)
    ((Real.exp_pos (-A)).trans_le (spectralPeterssonGammaTailRatio_bounds k hk A hA.le).1)
    (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (spectralPeterssonGammaTailRatio_bounds k hk A hA.le).1 hpair hcut.2

theorem gamma0PeterssonSourceAtkinPacket_density (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1)
    (k : ℕ) (hk : 2 ≤ k) (hEven : Even k) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hn : Set.InjOn n (t : Set ι))
    (hnB : ∀ j ∈ t, (n j : ℝ) ≤ B) :
    (∫ z in gamma0InteriorRegion (r*s), ‖gamma0PeterssonSourceAtkinPacket r s hab k t α n z‖^2*z.im^k) ≤
      2*Real.exp A*(1+8*Real.pi*B/(((r*s : ℕ) : ℝ)*A))*(∑ j ∈ t, ‖α j‖^2) := by
  let F := gamma0PeterssonSourceAtkinPacketForm r s hcop hab k hk hEven t α n
  have hFeq : ⇑F = gamma0PeterssonSourceAtkinPacket r s hab k t α n :=
    gamma0PeterssonSourceAtkinPacketForm_coe r s hcop hab k hk hEven t α n
  have hFLp : MemLp (spectralPeterssonHilbertProfile k (gamma0PeterssonSourceAtkinPacket r s hab k t α n)) 2
      (volume.restrict (gamma0InteriorRegion (r*s))) := by
    rw [← hFeq]
    exact gamma0PeterssonCuspPacket_memLp (r*s) k F
  have hcut := gamma0PeterssonCutPacket_mixed_norm r s hcop k hk t α n hA hB hn hnB
  have hPLp := spectralPeterssonHilbertProfile_memLp_of_integrable (r*s) k
    (gamma0PeterssonCutPacket (r*s) (gamma0CuspOneOver s) k t α n A)
    (gamma0PeterssonCutPacket_measurable (r*s) (gamma0CuspOneOver s) k t α n hA) hcut.1
  have hpair := gamma0PeterssonCutPacket_mixed_pairing r s hcop hab k hk hEven t α n A hA F
  rw [hFeq] at hpair
  exact gamma0Petersson_density_of_cut (r*s) k _ _ hFLp hPLp A (spectralPeterssonGammaTailRatio k A)
    (1+8*Real.pi*B/(((r*s : ℕ) : ℝ)*A)) (∑ j ∈ t, ‖α j‖^2)
    ((Real.exp_pos (-A)).trans_le (spectralPeterssonGammaTailRatio_bounds k hk A hA.le).1)
    (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (spectralPeterssonGammaTailRatio_bounds k hk A hA.le).1 hpair hcut.2

def spectralPeterssonDensityConstant : ℝ :=
  2*Real.exp (1/4 : ℝ)*max 1 (32*Real.pi)

theorem spectralPeterssonDensityConstant_pos : 0 < spectralPeterssonDensityConstant := by
  unfold spectralPeterssonDensityConstant
  have h : (0 : ℝ) < max 1 (32*Real.pi) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  positivity

private theorem density_scale_le (N B S : ℝ) (hN : 0 < N) (hB : 0 ≤ B) (hS : 0 ≤ S) :
    2*Real.exp (1/4 : ℝ)*(1+8*Real.pi*B/(N*(1/4)))*S ≤
      spectralPeterssonDensityConstant*(1+B/N)*S := by
  let M : ℝ := max 1 (32*Real.pi)
  have h1 : 1 ≤ M := le_max_left _ _
  have h2 : 32*Real.pi ≤ M := le_max_right _ _
  have ht : 0 ≤ B/N := div_nonneg hB hN.le
  have hscale : 8*Real.pi*B/(N*(1/4)) = 32*Real.pi*(B/N) := by field_simp [hN.ne'] <;> ring
  have hlin : 1+32*Real.pi*(B/N) ≤ M*(1+B/N) := by
    have hm := mul_le_mul_of_nonneg_right h2 ht
    nlinarith
  rw [hscale]
  have h := mul_le_mul_of_nonneg_left hlin (by positivity : 0 ≤ 2*Real.exp (1/4 : ℝ))
  have hs := mul_le_mul_of_nonneg_right h hS
  simpa only [spectralPeterssonDensityConstant,M,mul_assoc] using hs

theorem gamma0PeterssonSourceInfinityPacket_uniform_density (N k : ℕ) [NeZero N]
    (hk : 2 ≤ k) (hEven : Even k) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+)
    {B : ℝ} (hB : 0 < B) (hn : Set.InjOn n (t : Set ι))
    (hnB : ∀ j ∈ t, (n j : ℝ) ≤ B) :
    (∫ z in gamma0InteriorRegion N, ‖gamma0PeterssonSourceInfinityPacket N k t α n z‖^2*z.im^k) ≤
      spectralPeterssonDensityConstant*(1+B/(N : ℝ))*(∑ j ∈ t, ‖α j‖^2) := by
  have h := gamma0PeterssonSourceInfinityPacket_density N k hk hEven t α n
    (A := 1/4) (by norm_num) hB hn hnB
  exact h.trans (density_scale_le (N : ℝ) B _ (by exact_mod_cast NeZero.pos N) hB.le
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))

theorem gamma0PeterssonSourceAtkinPacket_uniform_density (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1)
    (k : ℕ) (hk : 2 ≤ k) (hEven : Even k) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+)
    {B : ℝ} (hB : 0 < B) (hn : Set.InjOn n (t : Set ι))
    (hnB : ∀ j ∈ t, (n j : ℝ) ≤ B) :
    (∫ z in gamma0InteriorRegion (r*s), ‖gamma0PeterssonSourceAtkinPacket r s hab k t α n z‖^2*z.im^k) ≤
      spectralPeterssonDensityConstant*(1+B/((r*s : ℕ) : ℝ))*(∑ j ∈ t, ‖α j‖^2) := by
  have h := gamma0PeterssonSourceAtkinPacket_density r s hcop hab k hk hEven t α n
    (A := 1/4) (by norm_num) hB hn hnB
  exact h.trans (density_scale_le ((r*s : ℕ) : ℝ) B _ (by exact_mod_cast NeZero.pos (r*s)) hB.le
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))

theorem gamma0PeterssonSourceAtkin_uniform_density (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1)
    (k : ℕ) (hk : 2 ≤ k) (hEven : Even k) (n : ℕ+) :
    (∫ z in gamma0InteriorRegion (r*s), ‖gamma0PeterssonSourceAtkin r s hab k n z‖^2*z.im^k) ≤
      spectralPeterssonDensityConstant*(1+(n : ℝ)/((r*s : ℕ) : ℝ)) := by
  have hinj : Set.InjOn (fun _ : Unit => n) ((Finset.univ : Finset Unit) : Set Unit) :=
    fun _ _ _ _ _ => Subsingleton.elim _ _
  have h := gamma0PeterssonSourceAtkinPacket_uniform_density r s hcop hab k hk hEven
    (Finset.univ : Finset Unit) (fun _ => (1 : ℂ)) (fun _ => n)
    (by positivity : 0 < (n : ℝ)) hinj (fun _ _ => le_rfl)
  simpa [gamma0PeterssonSourceAtkinPacket] using h

end ArtinMatthews
