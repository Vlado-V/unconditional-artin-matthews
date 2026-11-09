module

public import Mathlib


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite orbit multiplicities on a separated invariant slice. -/
namespace ArtinMatthews
open Set
open scoped ENNReal Pointwise Classical
noncomputable section

variable {Γ X : Type*} [Group Γ] [MulAction Γ X]

theorem sourceFiniteSlice_hit_iff (H : Subgroup Γ) (E : Set X)
    (hstable : ∀ h : H, ∀ x ∈ E, (h : Γ) • x ∈ E)
    (hsep : ∀ γ : Γ, ∀ x ∈ E, γ • x ∈ E → γ ∈ H)
    {x : X} (hx : x ∈ E) (γ : Γ) : γ • x ∈ E ↔ γ ∈ H := by
  exact ⟨hsep γ x hx, fun hγ => hstable ⟨γ, hγ⟩ x hx⟩

theorem sourceFiniteSlice_indicator_tsum (H : Subgroup Γ) [Finite H] (E : Set X)
    (hstable : ∀ h : H, ∀ x ∈ E, (h : Γ) • x ∈ E)
    (hsep : ∀ γ : Γ, ∀ x ∈ E, γ • x ∈ E → γ ∈ H) (x : X) :
    (∑' γ : Γ, E.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x)) =
      if (Quotient.mk (MulAction.orbitRel Γ X) x) ∈
        (Quotient.mk (MulAction.orbitRel Γ X) '' E) then (Nat.card H : ℝ≥0∞) else 0 := by
  classical
  by_cases hx : (Quotient.mk (MulAction.orbitRel Γ X) x) ∈
      (Quotient.mk (MulAction.orbitRel Γ X) '' E)
  · rw [ite_eq_left hx]
    obtain ⟨y, hy, hxy⟩ := hx
    obtain ⟨γ₀, hγ₀⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact hxy)
    have hhit : γ₀ • x ∈ E := by simpa only [hγ₀] using hy
    calc
      (∑' γ : Γ, E.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x)) =
          ∑' γ : Γ, E.indicator (fun _ => (1 : ℝ≥0∞)) ((γ * γ₀) • x) :=
        ((Equiv.mulRight γ₀).tsum_eq _).symm
      _ = ∑' γ : Γ, (H : Set Γ).indicator (fun _ => (1 : ℝ≥0∞)) γ := by
        apply tsum_congr
        intro γ
        rw [mul_smul]
        have hh := sourceFiniteSlice_hit_iff H E hstable hsep hhit γ
        change (if γ • (γ₀ • x) ∈ E then (1 : ℝ≥0∞) else 0) =
          if γ ∈ H then 1 else 0
        simp only [hh]
      _ = ∑' _ : H, (1 : ℝ≥0∞) := (tsum_subtype (H : Set Γ) _).symm
      _ = (Nat.card H : ℝ≥0∞) := by
        let : Fintype H := Fintype.ofFinite H
        simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          mul_one, Nat.card_eq_fintype_card]
  · rw [ite_eq_right hx]
    have hz (γ : Γ) : E.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) = 0 := by
      have hh : γ • x ∉ E := by
        intro hγ
        apply hx
        refine ⟨γ • x, hγ, ?_⟩
        apply Quotient.sound
        exact MulAction.mem_orbit_iff.mpr ⟨γ, rfl⟩
      exact Set.indicator_of_notMem hh _
    simp only [hz, tsum_zero]

end
end ArtinMatthews
