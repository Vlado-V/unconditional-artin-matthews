module

public import ArtinMatthews.GiantComparisonPositionCell


set_option backward.privateInPublic true
@[expose] public section

/-! A cell contributes the two true harmonic averages and a normalized
cutoff shift. The fixed Dirichlet character on the shift separates
between the two product variables. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators ComplexConjugate
noncomputable section

variable {I K J : Type*} [Fintype I] [Fintype K] [Fintype J] [DecidableEq I] [DecidableEq K]
  {k ell M : ℕ} {P : J → Finset ℕ} {C : J → Finset (Fin k)}

def giantComparisonWeightedCell (PA : I → Finset ℕ) (PB : K → Finset ℕ)
    (f : IdealSelectedLabels PA → ℂ) (g : IdealSelectedLabels PB → ℂ)
    (χ : DirichletCharacter ℂ M) (F G : ℕ → ℂ)
    (Ψ : ℝ → ℂ) (x q : ℝ) (N : ℕ)
    (s t : ((j : J) → Fin (ell+(C j).card) → ℕ) → ℂ) : ℂ :=
  let t_g (j : J) := ell+(C j).card
  ∑ u, (idealSelectedMass PA u:ℂ)*f u *
    ∑ v, (idealSelectedMass PB v:ℂ)*g v *
      ∑ w ∈ Ioc 0 N, giantComparisonPositionKernel x Ψ χ F G
        (idealSelectedProduct u*idealSelectedProduct v) w *
        sourceComparisonMarkWeight P t_g (fun _ => q) s w *
        sourceComparisonMarkWeight P t_g (fun _ => q) t (w+idealSelectedProduct u*idealSelectedProduct v)

theorem giantComparisonWeightedCell_eq_cutoff
    (PA : I → Finset ℕ) (PB : K → Finset ℕ)
    (f : IdealSelectedLabels PA → ℂ) (g : IdealSelectedLabels PB → ℂ)
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (hf : ∀ u, idealSelectedProduct u ∉ Ico A (A+4*A) → f u = 0)
    (hg : ∀ v, idealSelectedProduct v ∉ Ico B (B+4*B) → g v = 0)
    (χ : DirichletCharacter ℂ M) (F G : ℕ → ℂ) (hF : ∀ n, conj (F n) = F n)
    (Ψ ψL ψR : ℝ → ℂ) {a b x : ℝ} (ha : 0 < a)
    (hsupp : Function.support Ψ ⊆ Set.Icc a b)
    (hψL : ∀ t, conj (ψL t) = ψL t)
    (hψ : ∀ t ∈ Set.Icc a (25*(b+1)), ψL t = (t:ℂ)⁻¹ ∧ ψR t = 1)
    (hx : 1 ≤ x) {N : ℕ} (hN : (25*(b+1)+a/2)*(x*((A:ℝ)*(B:ℝ))) ≤ (N:ℝ)) (q : ℝ)
    (s t : ((j : J) → Fin (ell+(C j).card) → ℕ) → ℂ) :
    let Y := x*((A:ℝ)*(B:ℝ))
    let R := giantComparisonCutoffRows Y (a/2) (25*(b+1)+a/2)
    let t_g (j : J) := ell+(C j).card
    let U := giantComparisonWeightedEndpoint P t_g (fun _ => q) (fun l => conj (s l)) ψL F Y
    let V := giantComparisonWeightedEndpoint P t_g (fun _ => q) t ψR (fun n => χ n*G n) Y
    giantComparisonWeightedCell (P:=P) (C:=C) PA PB f g χ F G Ψ x q N s t =
      (Y:ℂ)⁻¹ * giantComparisonNatCutoffSum PA PB
        (fun u => f u*conj (χ (idealSelectedProduct u)))
        (fun v => g v*conj (χ (idealSelectedProduct v))) R R U V Ψ x := by
  intro Y R t_g U V
  let d (u : IdealSelectedLabels PA) (v : IdealSelectedLabels PB) :=
    idealSelectedProduct u*idealSelectedProduct v
  let H (u : IdealSelectedLabels PA) (v : IdealSelectedLabels PB) :=
    ∑ w ∈ R, ∑ z ∈ R, if z = w+d u v then
      conj (U w)*V z*Ψ ((w:ℝ)/(x*(d u v:ℝ))) else 0
  have hW : 0 < (A:ℝ)*(B:ℝ) := mul_pos (Nat.cast_pos.mpr hA) (Nat.cast_pos.mpr hB)
  calc
    _ = ∑ u, (idealSelectedMass PA u:ℂ)*f u *
        ∑ v, (idealSelectedMass PB v:ℂ)*g v * ((Y:ℂ)⁻¹*conj (χ (d u v))*H u v) := by
      unfold giantComparisonWeightedCell
      apply sum_congr rfl
      intro u _
      by_cases hu : idealSelectedProduct u ∈ Ico A (A+4*A)
      · congr 1
        apply sum_congr rfl
        intro v _
        by_cases hv : idealSelectedProduct v ∈ Ico B (B+4*B)
        · obtain ⟨hlo,hhi⟩ := giantComparisonProductCell_bounds hu hv
          rw [giantComparisonPositionKernel_cell_eq (P:=P) (C:=C) χ F G hF
            Ψ ψL ψR ha hsupp hψL hψ hx hW
            (show (A:ℝ)*(B:ℝ) ≤ (d u v:ℝ) by exact_mod_cast hlo)
            (show (d u v:ℝ) ≤ 25*((A:ℝ)*(B:ℝ)) by exact_mod_cast hhi)
            hN q s t]
        · simp [hg v hv]
      · simp [hf u hu]
    _ = _ := by
      simp only [giantComparisonNatCutoffSum, H, d, Nat.cast_mul, map_mul, mul_sum]
      apply sum_congr rfl
      intro u _
      apply sum_congr rfl
      intro v _
      apply sum_congr rfl
      intro w _
      apply sum_congr rfl
      intro z _
      split_ifs <;> ring

end
end ArtinMatthews
