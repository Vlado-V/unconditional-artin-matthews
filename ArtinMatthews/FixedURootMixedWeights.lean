module

public import ArtinMatthews.FixedURootMixedAbel
public import ArtinMatthews.FixedURootWeightedBoxes


set_option backward.privateInPublic true
@[expose] public section

/-! Actual root replacement for mixed-C² weights and an exact interval mask
on the root ratio. The prescribed SL₂ class and arithmetic root set are
unchanged; the conclusion uses the proved root-count error. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators

def rootMixedWeightNorm (F : ℝ → ℝ → ℂ) (a b c d Cx Cy Cxy : ℝ) : ℝ :=
  ‖F a c‖+(b-a)*Cx+(d-c)*Cy+(b-a)*(d-c)*Cxy

def fixedURootMixedSum {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (A B α β C D : ℝ) (lcR rcR : Bool) (F : ℝ → ℝ → ℂ) : ℂ :=
  ∑ p ∈ fixedURootMatrixBoxPoints g₀ A B α β C D true true lcR rcR true true,
    F (p.1 : ℝ) (p.2.2 : ℝ)

def fixedURootMixedMain (S : ℕ) (A B α β C D : ℝ) (F : ℝ → ℝ → ℂ) : ℂ :=
  (((β-α)/((riemannZeta 2).re *
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) : ℝ) : ℂ) *
      (∫ t in A..B, ∫ s in C..D, F t s)

theorem fixedURoot_complex_tail_error {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (A B α β C D t s : ℝ) (lcR rcR : Bool)
    (ht : t ∈ Set.Icc A B) (hs : s ∈ Set.Icc C D) {E : ℝ}
    (he : |((fixedURootMatrixBoxPoints g₀ t B α β s D true true lcR rcR true true).card : ℝ) -
      ((B-t)*(β-α)*(D-s))/((riemannZeta 2).re *
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))| ≤ E) :
    ‖(∑ p ∈ fixedURootMatrixBoxPoints g₀ A B α β C D true true lcR rcR true true,
        if t ≤ (p.1 : ℝ) ∧ s ≤ (p.2.2 : ℝ) then (1 : ℂ) else 0) -
      ((((β-α)/((riemannZeta 2).re *
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) : ℝ) : ℂ)) *
        ((B-t : ℝ) : ℂ)*((D-s : ℝ) : ℂ)‖ ≤ E := by
  classical
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
    fixedURootMatrixBox_filter_tails g₀ A B α β C D t s lcR rcR ht hs]
  have heq :
      ((fixedURootMatrixBoxPoints g₀ t B α β s D true true lcR rcR true true).card : ℂ) -
        ((((β-α)/((riemannZeta 2).re *
          (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) : ℝ) : ℂ)) *
            ((B-t : ℝ) : ℂ)*((D-s : ℝ) : ℂ) =
      (((fixedURootMatrixBoxPoints g₀ t B α β s D true true lcR rcR true true).card : ℝ) -
        ((B-t)*(β-α)*(D-s))/((riemannZeta 2).re *
          (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) : ℝ) := by
    push_cast
    ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  exact he

theorem fixedURootMixedSum_error_of_counts {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (A B α β C D : ℝ) (lcR rcR : Bool) (F : ℝ → ℝ → ℂ)
    {E Cx Cy Cxy : ℝ} (hAB : A ≤ B) (hCD : C ≤ D) (hE : 0 ≤ E)
    (hF : Continuous F.uncurry)
    (hFx : ∀ s, Differentiable ℝ (fun t => F t s))
    (hDx : ∀ s, Continuous (deriv (fun t => F t s)))
    (hFy : ∀ t, Differentiable ℝ (F t))
    (hDy : Continuous (fun p : ℝ × ℝ => deriv (F p.1) p.2))
    (hFxy : ∀ s, Differentiable ℝ (fun t => deriv (F t) s))
    (hDxy : ∀ s, Continuous (deriv (fun t => deriv (F t) s)))
    (hCx : ∀ t ∈ Set.Icc A B, ‖deriv (fun z => F z C) t‖ ≤ Cx)
    (hCy : ∀ s ∈ Set.Icc C D, ‖deriv (F A) s‖ ≤ Cy)
    (hCxy : ∀ t ∈ Set.Icc A B, ∀ s ∈ Set.Icc C D,
      ‖deriv (fun z => deriv (F z) s) t‖ ≤ Cxy)
    (hcount : ∀ t ∈ Set.Icc A B, ∀ s ∈ Set.Icc C D,
      |((fixedURootMatrixBoxPoints g₀ t B α β s D true true lcR rcR true true).card : ℝ) -
        ((B-t)*(β-α)*(D-s))/((riemannZeta 2).re *
          (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))| ≤ E) :
    ‖fixedURootMixedSum g₀ A B α β C D lcR rcR F -
      fixedURootMixedMain S A B α β C D F‖ ≤ E*rootMixedWeightNorm F A B C D Cx Cy Cxy := by
  have hh := root_weight_mixed_rectangle_error
    (fixedURootMatrixBoxPoints g₀ A B α β C D true true lcR rcR true true)
    (fun p => (p.1 : ℝ)) (fun p => (p.2.2 : ℝ)) (fun _ => (1 : ℂ)) F
    ((((β-α)/((riemannZeta 2).re *
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) : ℝ) : ℂ)) hAB hCD hE
    (fun p hp => (fixedURootMatrixBox_coordinate_bounds g₀ A B α β C D lcR rcR p hp).1)
    (fun p hp => (fixedURootMatrixBox_coordinate_bounds g₀ A B α β C D lcR rcR p hp).2)
    hF hFx hDx hFy hDy hFxy hDxy hCx hCy hCxy
    (fun t ht s hs => fixedURoot_complex_tail_error g₀ A B α β C D t s lcR rcR ht hs (hcount t ht s hs))
  simpa only [fixedURootMixedSum, fixedURootMixedMain, rootMixedWeightNorm, one_mul] using hh

/-- Mixed-C² root replacement with the literal UV normalization. The
derivative bounds enter explicitly and no weighted discrepancy is assumed. -/
theorem fixedURootMixedSum_normalized_power_saving {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
        (U V A B α β C D Cx Cy Cxy : ℝ) (lcR rcR : Bool) (F : ℝ → ℝ → ℂ),
        x^δ ≤ U → x^δ ≤ V → Squarefree S →
        (S : ℝ) ≤ Real.exp (M*(Real.log x)^(49/50 : ℝ)) →
        U ≤ A → A ≤ B → B ≤ 16*U →
        0 ≤ α → α ≤ β → β ≤ 1 → V ≤ C → C ≤ D → D ≤ 2*V →
        Continuous F.uncurry →
        (∀ s, Differentiable ℝ (fun t => F t s)) →
        (∀ s, Continuous (deriv (fun t => F t s))) →
        (∀ t, Differentiable ℝ (F t)) →
        Continuous (fun p : ℝ × ℝ => deriv (F p.1) p.2) →
        (∀ s, Differentiable ℝ (fun t => deriv (F t) s)) →
        (∀ s, Continuous (deriv (fun t => deriv (F t) s))) →
        (∀ t ∈ Set.Icc A B, ‖deriv (fun z => F z C) t‖ ≤ Cx) →
        (∀ s ∈ Set.Icc C D, ‖deriv (F A) s‖ ≤ Cy) →
        (∀ t ∈ Set.Icc A B, ∀ s ∈ Set.Icc C D,
          ‖deriv (fun z => deriv (F z) s) t‖ ≤ Cxy) →
        ‖fixedURootMixedSum g₀ A B α β C D lcR rcR F -
          fixedURootMixedMain S A B α β C D F‖ / (U*V) ≤
          E*x^(-δ/1000)*rootMixedWeightNorm F A B C D Cx Cy Cxy := by
  obtain ⟨E,hE,hcount⟩ := fixedURootMatrixBox_uniform_power_saving hδ M
  refine ⟨E,hE,?_⟩
  filter_upwards [hcount, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  intro S g₀ U V A B α β C D Cx Cy Cxy lcR rcR F hU hV hS hSr hUA hAB hB
    hα hαβ hβ hVC hCD hD hF hFx hDx hFy hDy hFxy hDxy hCx hCy hCxy
  have hUp : 0 < U := (Real.rpow_pos_of_pos hx0 δ).trans_le hU
  have hVp : 0 < V := (Real.rpow_pos_of_pos hx0 δ).trans_le hV
  have hb := fixedURootMixedSum_error_of_counts g₀ A B α β C D lcR rcR F
    hAB hCD (show 0 ≤ E*U*V*x^(-δ/1000) by positivity)
    hF hFx hDx hFy hDy hFxy hDxy hCx hCy hCxy (fun t ht s hs =>
      hx S g₀ U V t B α β s D true true lcR rcR true true hU hV hS hSr
        (hUA.trans ht.1) ht.2 hB hα hαβ hβ (hVC.trans hs.1) hs.2 hD)
  apply (div_le_iff₀ (mul_pos hUp hVp)).mpr
  convert hb using 1
  ring

end ArtinMatthews
