module

public import ArtinMatthews.FixedURootMixedWeights


set_option backward.privateInPublic true
@[expose] public section

/-! Exact FTC in the third, canonical-completion coordinate. This retains
the original prescribed SL₂ class and the actual arithmetic root set. -/

noncomputable section
namespace ArtinMatthews
open OAI.Erdos970.ErdosHyperbolaError MeasureTheory
open scoped BigOperators

def fixedURootRatio (p : Σ _u : ℤ, ℤ × ℤ) : ℝ := (p.2.1 : ℝ)/(p.1 : ℝ)

theorem fixedURootMatrixBox_ratio_bounds {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    {A B α β C D : ℝ} (hA : 1 < A) (p : Σ _u : ℤ, ℤ × ℤ)
    (hp : p ∈ fixedURootMatrixBoxPoints g₀ A B α β C D true true true true true true) :
    fixedURootRatio p ∈ Set.Icc α β := by
  rcases p with ⟨u,c,v⟩
  have hu := (fixedURootMatrixBox_coordinate_bounds g₀ A B α β C D true true ⟨u,c,v⟩ hp).1
  have hup : 0 < (u : ℝ) := by linarith [hu.1]
  have hun : (u.natAbs : ℝ) = (u : ℝ) := by
    rw [← Int.cast_natCast,Int.natCast_natAbs,abs_of_pos]
    exact_mod_cast hup
  simp only [fixedURootMatrixBoxPoints,fixedURootBoxPoints,Finset.mem_sigma,
    fixedURootBoxIndices,fixedURootPairs,Finset.mem_filter,Finset.product_eq_sprod,
    Finset.mem_product,fixedURoot_mem_closed_interval] at hp
  rcases hp with ⟨_,⟨⟨hc,_⟩,_⟩⟩
  rw [hun] at hc
  exact ⟨(le_div_iff₀ hup).mpr (by linarith [hc.1]),
    (div_le_iff₀ hup).mpr (by linarith [hc.2])⟩

theorem fixedURootMatrixBox_filter_ratio {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    {A B α β C D s : ℝ} (hA : 1 < A) (hs : s ∈ Set.Icc α β) :
    (fixedURootMatrixBoxPoints g₀ A B α β C D true true true true true true).filter
      (fun p => s ≤ fixedURootRatio p) =
        fixedURootMatrixBoxPoints g₀ A B s β C D true true true true true true := by
  ext p
  rcases p with ⟨u,c,v⟩
  rw [Finset.mem_filter]
  by_cases hu : u ∈ realIntervalIntegers A B true true
  · have hur := (fixedURoot_mem_closed_interval A B u).mp hu
    have hup : 0 < (u : ℝ) := by linarith [hur.1]
    have hun : (u.natAbs : ℝ) = (u : ℝ) := by
      rw [← Int.cast_natCast,Int.natCast_natAbs,abs_of_pos]
      exact_mod_cast hup
    simp only [fixedURootMatrixBoxPoints,fixedURootBoxPoints,Finset.mem_sigma,
      fixedURootBoxIndices,fixedURootPairs,Finset.mem_filter,Finset.product_eq_sprod,
      Finset.mem_product,fixedURoot_mem_closed_interval,fixedURootRatio,hun]
    constructor
    · rintro ⟨⟨hu',⟨⟨hc,hv⟩,hm⟩⟩,hr⟩
      exact ⟨hu',⟨⟨⟨by simpa only [mul_comm] using (le_div_iff₀ hup).mp hr,hc.2⟩,hv⟩,hm⟩⟩
    · rintro ⟨hu',⟨⟨hc,hv⟩,hm⟩⟩
      have hlo : (u : ℝ)*α ≤ (c : ℝ) :=
        (mul_le_mul_of_nonneg_left hs.1 hup.le).trans hc.1
      exact ⟨⟨hu',⟨⟨⟨hlo,hc.2⟩,hv⟩,hm⟩⟩,(le_div_iff₀ hup).mpr (by nlinarith [hc.1])⟩
  · simp only [fixedURootMatrixBoxPoints,fixedURootBoxPoints,Finset.mem_sigma,
      fixedURootBoxIndices,Finset.mem_filter,hu,false_and]

def fixedURootRatioSum {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (A B α β C D : ℝ) (F : ℝ → ℝ → ℝ → ℂ) : ℂ :=
  ∑ p ∈ fixedURootMatrixBoxPoints g₀ A B α β C D true true true true true true,
    F (p.1 : ℝ) (p.2.2 : ℝ) (fixedURootRatio p)

theorem fixedURootRatioSum_abel {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (A B α β C D : ℝ) (F : ℝ → ℝ → ℝ → ℂ)
    (hA : 1 < A) (hαβ : α ≤ β)
    (hF : ∀ u v,Differentiable ℝ (F u v))
    (hD : ∀ u v,Continuous (deriv (F u v))) :
    fixedURootRatioSum g₀ A B α β C D F =
      fixedURootMixedSum g₀ A B α β C D true true (fun u v => F u v α) +
        ∫ s in α..β,fixedURootMixedSum g₀ A B s β C D true true
          (fun u v => deriv (F u v) s) := by
  let T := fixedURootMatrixBoxPoints g₀ A B α β C D true true true true true true
  have hh := root_weight_family_abel T fixedURootRatio (fun _ => (1 : ℂ))
    (fun p => F (p.1 : ℝ) (p.2.2 : ℝ)) hαβ
    (fun p hp => fixedURootMatrixBox_ratio_bounds g₀ hA p hp)
    (fun p => hF _ _) (fun p => hD _ _)
  simp only [one_mul] at hh
  rw [fixedURootRatioSum]
  refine hh.trans ?_
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Set.Icc α β := by simpa only [Set.uIcc_of_le hαβ] using hs
  dsimp only
  rw [← Finset.sum_filter]
  change (∑ p ∈ T.filter (fun p => s ≤ fixedURootRatio p),
    deriv (F (p.1 : ℝ) (p.2.2 : ℝ)) s) = _
  rw [show T.filter (fun p => s ≤ fixedURootRatio p) =
      fixedURootMatrixBoxPoints g₀ A B s β C D true true true true true true from
        fixedURootMatrixBox_filter_ratio g₀ hA hs']
  rfl

end ArtinMatthews
