module

public import ArtinMatthews.MarkedMinorArcBanKernel
public import ArtinMatthews.MarkedMinorArcPositionOperator


set_option backward.privateInPublic true
@[expose] public section

/-! Exact circle detector and adjoint identities for the ban coefficient. -/
noncomputable section
namespace ArtinMatthews

open MeasureTheory
open scoped ComplexConjugate

local instance : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩

theorem markedBan_fourier_integral (k : ℤ) :
    (∫ θ : AddCircle (1:ℝ), fourier k θ ∂AddCircle.haarAddCircle) = if k=0 then 1 else 0 := by
  classical
  by_cases hk : k=0
  · simp [hk]
  · rw [ite_eq_right hk]
    exact integral_eq_zero_of_add_right_eq_neg (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index hk (by norm_num : (0:ℝ)<1))

theorem markedBan_minor_integral (Q Y : ℝ) (k : ℤ) :
    (∫ θ : AddCircle (1:ℝ) in (markedMinorCircleMajor Q Y)ᶜ,
      fourier k θ ∂AddCircle.haarAddCircle) =
      (if k=0 then 1 else 0)-markedBanMajorKernel Q Y k := by
  classical
  have hi : Integrable (fun θ : AddCircle (1:ℝ) => fourier k θ) AddCircle.haarAddCircle :=
    (fourier k).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hh := integral_add_compl (markedMinorCircleMajor_measurable Q Y) hi
  rw [markedBan_fourier_integral] at hh
  unfold markedBanMajorKernel
  linear_combination hh

theorem markedBan_edge_minor_identity (ψ : ℝ → ℂ) (Q Y : ℝ) (b a l : ℤ) :
    ψ ((l:ℝ)/Y)*(∫ θ : AddCircle (1:ℝ) in (markedMinorCircleMajor Q Y)ᶜ,
      fourier (l-b+a) θ ∂AddCircle.haarAddCircle) = markedBanEdgeKernel ψ Q Y b a l := by
  classical
  rw [markedBan_minor_integral]
  have he : l-b+a=0 ↔ l=b-a := by omega
  simp only [he,markedBanEdgeKernel]

theorem markedBanMajorKernel_neg (Q Y : ℝ) (k : ℤ) :
    markedBanMajorKernel Q Y (-k) = (starRingEnd ℂ) (markedBanMajorKernel Q Y k) := by
  unfold markedBanMajorKernel
  simp_rw [fourier_neg]
  exact integral_conj

def markedBanAdjointCutoff (ψ : ℝ → ℂ) (u : ℝ) : ℂ := (starRingEnd ℂ) (ψ (-u))

theorem markedBanEdgeKernel_adjoint (ψ : ℝ → ℂ) (Q Y : ℝ) (b a l : ℤ) :
    markedBanEdgeKernel (markedBanAdjointCutoff ψ) Q Y a b (-l) =
      (starRingEnd ℂ) (markedBanEdgeKernel ψ Q Y b a l) := by
  classical
  have he : -l-a+b = -(l-b+a) := by ring
  have hi : -l=a-b ↔ l=b-a := by omega
  unfold markedBanEdgeKernel markedBanAdjointCutoff
  rw [he,markedBanMajorKernel_neg]
  simp only [Int.cast_neg,neg_div,neg_neg,hi,map_mul,map_sub]
  split_ifs <;> simp

theorem markedBanAdjointCutoff_bounds (ψ : ℝ → ℂ) {A W : ℝ}
    (hψ : ∀ u, ‖ψ u‖ ≤ W) (hsupp : ∀ u, ψ u ≠ 0 → |u| ≤ A) :
    (∀ u, ‖markedBanAdjointCutoff ψ u‖ ≤ W) ∧
      (∀ u, markedBanAdjointCutoff ψ u ≠ 0 → |u| ≤ A) := by
  constructor
  · intro u
    simpa only [markedBanAdjointCutoff,RCLike.norm_conj] using hψ (-u)
  · intro u hu
    have hn : ψ (-u) ≠ 0 := fun hh => hu (by simp only [markedBanAdjointCutoff,hh,map_zero])
    simpa only [abs_neg] using hsupp (-u) hn

end ArtinMatthews
