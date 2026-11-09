module

public import ArtinMatthews.MarkedMajorArcShift
public import ArtinMatthews.MarkedMajorArcTails


set_option backward.privateInPublic true
@[expose] public section

/-! An actual, unconditional error estimate for the normalized twisted
Mangoldt Riesz sums, including the complete unbounded Perron tails. -/
namespace ArtinMatthews

open Complex Set Filter Erdos970
open scoped Topology BigOperators

noncomputable def markedMajorRieszSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, markedMajorMangoldt χ t n * markedMellinTriangle ((n:ℝ)/x)

noncomputable def markedMajorRieszError (K C L H x : ℝ) : ℝ :=
  (2*(C+L)*x^(1/L)/H +
    2*H*(K*L^2*x^(-L^(-(3/4:ℝ)))/(L^(-(3/4:ℝ))*(1-L^(-(3/4:ℝ))))) +
    2*(K*L^2*x^(1/L)/H^2)*(1/L+L^(-(3/4:ℝ))))/(2*Real.pi)

/-- The actual Riesz sum equals the same log-derivative residue for every
cutoff, up to an explicit error with power-saving left edge and controllable
horizontal and right-tail terms. Thus subsequent endpoint differences cancel
the residue exactly. -/
theorem marked_major_mangoldt_riesz_error (A b : ℝ) (hA : 0 ≤ A) (hb : 0 ≤ b) :
    ∃ K C T₀ : ℝ, 0 < K ∧ 0 ≤ C ∧ 0 < T₀ ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q], (q:ℝ) ≤ L^A →
      ∀ (χ : DirichletCharacter ℂ q) (x t H : ℝ),
      1 ≤ x → 0 < H → H ≤ |t|/2 → 2*T₀ ≤ |t| → 2*|t| ≤ Real.exp (b*L) →
      ‖markedMajorRieszSum χ t x -
        (-deriv (DirichletCharacter.LFunction χ) (1-(t:ℂ)*Complex.I) /
          DirichletCharacter.LFunction χ (1-(t:ℂ)*Complex.I))‖ ≤
        markedMajorRieszError K C L H x := by
  obtain ⟨K,T₀,hK,hT₀,hr⟩ := marked_major_mangoldt_uniform_rectangle A b hA hb
  obtain ⟨C,hC,htail⟩ := marked_major_mangoldt_right_tails
  refine ⟨K,C,T₀,hK,hC,hT₀,?_⟩
  filter_upwards [hr,eventually_gt_atTop (1:ℝ)] with L hL hL1
  intro q _ hq χ x t H hx hH hHt htlo hthi
  have hLp : 0 < L := by linarith
  have hx0 : 0 < x := by linarith
  have hδp : 0 < L^(-(3/4:ℝ)) := Real.rpow_pos_of_pos hLp _
  have hδ1 : L^(-(3/4:ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hL1 (by norm_num)
  have hσp : 0 < 1/L := one_div_pos.mpr hLp
  have hσ1 : 1/L ≤ 1 := (div_le_one hLp).mpr hL1.le
  obtain ⟨hres,hbound⟩ := hL q hq χ x t H hx0 hH hHt htlo hthi
  let F : ℂ → ℂ := fun s =>
    -deriv (DirichletCharacter.LFunction χ) (s+(1-(t:ℂ)*Complex.I)) /
      DirichletCharacter.LFunction χ (s+(1-(t:ℂ)*Complex.I))
  have hF0 : F 0 = -deriv (DirichletCharacter.LFunction χ) (1-(t:ℂ)*Complex.I) /
      DirichletCharacter.LFunction χ (1-(t:ℂ)*Complex.I) := by simp only [F,zero_add]
  have hres' : RectangleIntegral' (fun s => F s*markedPerronKernel x s)
      (((-L^(-(3/4:ℝ)):ℝ):ℂ)-Complex.I*(H:ℂ))
      (((1/L:ℝ):ℂ)+Complex.I*(H:ℂ)) = F 0 := by
    change RectangleIntegral' (markedMajorMangoldtIntegrand χ x t) _ _ = F 0
    rw [hF0]
    exact hres
  have hb' : ∀ s ∈ Rectangle
      (((-L^(-(3/4:ℝ)):ℝ):ℂ)-Complex.I*(H:ℂ))
      (((1/L:ℝ):ℂ)+Complex.I*(H:ℂ)), ‖F s‖ ≤ K*L^2 := by
    intro s hs
    simpa only [F,neg_div,norm_neg] using hbound s hs
  have hs := marked_perron_product_finite_shift_bound hx hδp hδ1 hσp hH
    (by positivity : 0 ≤ K*L^2) hres' hb'
  have htail' := htail q χ x (1/L) t H hx0 hσp hσ1 hH
  simp only [one_div_one_div] at htail'
  have hn : ‖1/(2*(Real.pi:ℂ)*Complex.I)‖ = 1/(2*Real.pi) := by
    simp [Complex.norm_real,Real.norm_eq_abs]
  have hper := marked_major_mangoldt_perron χ t hx0 hσp hσ1
  change VerticalIntegral' (markedMajorMangoldtIntegrand χ x t) (1/L) =
    markedMajorRieszSum χ t x at hper
  rw [← hper,← hF0]
  change ‖VerticalIntegral' (markedMajorMangoldtIntegrand χ x t) (1/L) - F 0‖ ≤ _
  let Z : ℂ := (1/(2*(Real.pi:ℂ)*Complex.I))*
    VIntegral (markedMajorMangoldtIntegrand χ x t) (1/L) (-H) H
  have he : VerticalIntegral' (markedMajorMangoldtIntegrand χ x t) (1/L) - F 0 =
      (VerticalIntegral' (markedMajorMangoldtIntegrand χ x t) (1/L)-Z)+(Z-F 0) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hnTail : ‖VerticalIntegral' (markedMajorMangoldtIntegrand χ x t) (1/L)-Z‖ ≤
      (2*(C+L)*x^(1/L)/H)/(2*Real.pi) := by
    change ‖(1/(2*(Real.pi:ℂ)*Complex.I))*
      VerticalIntegral (markedMajorMangoldtIntegrand χ x t) (1/L)-
      (1/(2*(Real.pi:ℂ)*Complex.I))*
      VIntegral (markedMajorMangoldtIntegrand χ x t) (1/L) (-H) H‖ ≤ _
    rw [← mul_sub,norm_mul,hn]
    exact (mul_le_mul_of_nonneg_left htail' (by positivity)).trans_eq (by ring)
  change ‖Z-F 0‖ ≤ _ at hs
  exact (add_le_add hnTail hs).trans_eq (by unfold markedMajorRieszError; ring)

end ArtinMatthews
