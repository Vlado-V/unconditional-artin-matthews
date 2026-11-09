module

public import ArtinMatthews.MarkedMinorArcBanNeighbors
public import ArtinMatthews.MarkedMajorArcProductPolynomial


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute multiplicity of the compact determinant band. The two
endpoint products are counted with their actual representation fibers.
This estimate includes determinant zero and shared marking primes. -/
namespace ArtinMatthews
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable

def MarkedTypeIIDeterminantBand (a b : ℕ) (Y R : ℝ) (u v : ℕ) : Prop :=
  |(b:ℝ)*u-(a:ℝ)*v| ≤ R*Y

theorem markedTypeIIDeterminantBand_swap (a b : ℕ) (Y R : ℝ) (u v : ℕ) :
    MarkedTypeIIDeterminantBand a b Y R u v ↔ MarkedTypeIIDeterminantBand b a Y R v u := by
  unfold MarkedTypeIIDeterminantBand
  rw [abs_sub_comm]

theorem markedTypeIIDeterminantBand_row_card (S : Finset ℕ) (a b u : ℕ)
    {Y R : ℝ} (hY : 0 < Y) (hR : 0 ≤ R) (ha : Y ≤ (a:ℝ)) :
    ((S.filter (MarkedTypeIIDeterminantBand a b Y R u)).card:ℝ) ≤ 2*R+1 := by
  classical
  have ha₀ : 0 < (a:ℝ) := hY.trans_le ha
  let c := -((b:ℝ)*u)/(a:ℝ)
  have hcard : (S.filter (MarkedTypeIIDeterminantBand a b Y R u)).card ≤
      (markedBanIntegerWindow c R).card := by
    apply card_le_card_of_injOn (fun v : ℕ => (v:ℤ))
    · intro v hv
      have hv' := (mem_filter.mp hv).2
      rw [MarkedTypeIIDeterminantBand, abs_le] at hv'
      apply mem_markedBanIntegerWindow.mpr
      push_cast
      rw [abs_le]
      dsimp only [c]
      rw [neg_div]
      have hYR := mul_le_mul_of_nonneg_left ha hR
      constructor
      · have h := (div_le_iff₀ ha₀).mpr (show (b:ℝ)*u ≤
              ((v:ℝ)+R)*(a:ℝ) by nlinarith [hv'.2])
        linarith
      · have h := (le_div_iff₀ ha₀).mpr (show ((v:ℝ)-R)*(a:ℝ) ≤
              (b:ℝ)*u by nlinarith [hv'.1])
        linarith
    · intro v _ w _ h
      change (v:ℤ)=(w:ℤ) at h
      exact_mod_cast h
  exact (Nat.cast_le.mpr hcard).trans (markedBanIntegerWindow_card_le c hR)

private theorem markedTypeIIDeterminantBand_one_square_sum (S T : Finset ℕ) (a b : ℕ)
    {Y R : ℝ} (hY : 0 < Y) (hR : 0 ≤ R) (ha : Y ≤ (a:ℝ)) (f : ℕ → ℝ) :
    (∑ u ∈ S, ∑ v ∈ T, if MarkedTypeIIDeterminantBand a b Y R u v then f u^2 else 0) ≤
      (2*R+1)*∑ u ∈ S, f u^2 := by
  classical
  rw [mul_sum]
  apply sum_le_sum
  intro u _
  rw [← sum_filter]
  simp only [sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right
    (markedTypeIIDeterminantBand_row_card T a b u hY hR ha) (sq_nonneg _)

theorem markedTypeIIDeterminantBand_weighted_le (S T : Finset ℕ) (a b : ℕ)
    {Y R : ℝ} (hY : 0 < Y) (hR : 0 ≤ R) (ha : Y ≤ (a:ℝ)) (hb : Y ≤ (b:ℝ))
    (f g : ℕ → ℝ) :
    (∑ u ∈ S, ∑ v ∈ T, if MarkedTypeIIDeterminantBand a b Y R u v then f u*g v else 0) ≤
      (2*R+1)/2*((∑ u ∈ S, f u^2)+(∑ v ∈ T, g v^2)) := by
  classical
  have h₁ := markedTypeIIDeterminantBand_one_square_sum S T a b hY hR ha f
  have h₂ :
      (∑ u ∈ S, ∑ v ∈ T, if MarkedTypeIIDeterminantBand a b Y R u v then g v^2 else 0) ≤
        (2*R+1)*∑ v ∈ T, g v^2 := by
    rw [sum_comm]
    simp_rw [markedTypeIIDeterminantBand_swap a b Y R]
    exact markedTypeIIDeterminantBand_one_square_sum T S b a hY hR hb g
  have h :
      (∑ u ∈ S, ∑ v ∈ T, if MarkedTypeIIDeterminantBand a b Y R u v then f u*g v else 0) ≤
        (∑ u ∈ S, ∑ v ∈ T,
          ((if MarkedTypeIIDeterminantBand a b Y R u v then f u^2 else 0)/2+
           (if MarkedTypeIIDeterminantBand a b Y R u v then g v^2 else 0)/2)) := by
    apply sum_le_sum
    intro u _
    apply sum_le_sum
    intro v _
    split_ifs
    · nlinarith [sq_nonneg (f u-g v)]
    · norm_num
  simp only [sum_add_distrib, ← sum_div] at h
  nlinarith

theorem markedTypeIIProductFiber_sum (S T : Finset ℕ) (N : ℕ)
    (hST : ∀ v ∈ S×ˢT, v.1*v.2 ∈ Icc 1 N) (f : ℕ → ℝ) :
    (∑ v ∈ S×ˢT, f (v.1*v.2)) =
      ∑ n ∈ Icc 1 N, ((markedProductFiber S T n).card:ℝ)*f n := by
  classical
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ v ∈ markedProductFiber S T n, f (v.1*v.2) :=
      (sum_fiberwise_of_maps_to hST (fun v => f (v.1*v.2))).symm
    _ = _ := by
      apply sum_congr rfl
      intro n _
      rw [← nsmul_eq_mul,← sum_const]
      apply sum_congr rfl
      intro v hv
      rw [(mem_filter.mp hv).2]

theorem markedTypeIIProductFiber_square_mass (S T : Finset ℕ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ((markedProductFiber S T n).card:ℝ)^2) ≤
      (N:ℝ)*(∑ d ∈ Icc 1 N, 1/(d:ℝ))^3 := by
  simpa [markedProductCoefficient] using
    markedProductCoefficient_square_mass S T (fun _ => (1:ℂ)) (fun _ => (1:ℂ)) N
      1 1 (by norm_num) (by norm_num) (fun _ _ => by simp) (fun _ _ => by simp)

theorem markedTypeIIEndpointDeterminantBand_count (S T U V : Finset ℕ) (N a b : ℕ)
    (hST : ∀ v ∈ S×ˢT, v.1*v.2 ∈ Icc 1 N)
    (hUV : ∀ v ∈ U×ˢV, v.1*v.2 ∈ Icc 1 N)
    {Y R : ℝ} (hY : 0 < Y) (hR : 0 ≤ R) (ha : Y ≤ (a:ℝ)) (hb : Y ≤ (b:ℝ)) :
    (∑ v ∈ S×ˢT, ∑ w ∈ U×ˢV,
      if MarkedTypeIIDeterminantBand a b Y R (v.1*v.2) (w.1*w.2) then (1:ℝ) else 0) ≤
      (2*R+1)*(N:ℝ)*(∑ d ∈ Icc 1 N, 1/(d:ℝ))^3 := by
  classical
  let f : ℕ → ℝ := fun n => (markedProductFiber S T n).card
  let g : ℕ → ℝ := fun n => (markedProductFiber U V n).card
  have h : (∑ v ∈ S×ˢT, ∑ w ∈ U×ˢV,
      if MarkedTypeIIDeterminantBand a b Y R (v.1*v.2) (w.1*w.2) then (1:ℝ) else 0) =
      ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
        if MarkedTypeIIDeterminantBand a b Y R u v then f u*g v else 0 := by
    rw [markedTypeIIProductFiber_sum S T N hST (fun u =>
      ∑ w ∈ U×ˢV, if MarkedTypeIIDeterminantBand a b Y R u (w.1*w.2) then (1:ℝ) else 0)]
    apply sum_congr rfl
    intro u _
    rw [markedTypeIIProductFiber_sum U V N hUV (fun v =>
      if MarkedTypeIIDeterminantBand a b Y R u v then (1:ℝ) else 0),mul_sum]
    apply sum_congr rfl
    intro v _
    change f u*(g v*(if _ then 1 else 0))=_
    split_ifs <;> simp
  rw [h]
  apply (markedTypeIIDeterminantBand_weighted_le (Icc 1 N) (Icc 1 N) a b hY hR ha hb f g).trans
  have h₁ := markedTypeIIProductFiber_square_mass S T N
  have h₂ := markedTypeIIProductFiber_square_mass U V N
  change (∑ n ∈ Icc 1 N,f n^2) ≤ _ at h₁
  change (∑ n ∈ Icc 1 N,g n^2) ≤ _ at h₂
  apply (mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by positivity : 0≤(2*R+1)/2)).trans_eq
  ring

end
end ArtinMatthews
