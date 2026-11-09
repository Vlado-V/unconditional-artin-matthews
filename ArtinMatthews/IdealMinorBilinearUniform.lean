module

public import ArtinMatthews.IdealMinorCellBilinear
public import ArtinMatthews.IdealMinorSourceBudget
public import ArtinMatthews.IdealMinorSourceGeometry
public import ArtinMatthews.IdealCharacterTransposeUniform


set_option backward.privateInPublic true
@[expose] public section

/-! The large-denominator dyadic comparison uses the actual uniform
character kernel, harmonic atom losses and source-scale Gram bounds. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v

def idealMinorBilinearExponent (m : ℕ) (C₀ v₀ d E : ℝ) : ℝ :=
  idealMinorCutoffExponent (E+2) (idealGroupedBudgetExponent m C₀ v₀) d

theorem idealGroupedBudgetExponent_nonneg (m : ℕ) {C₀ v₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    0 ≤ idealGroupedBudgetExponent m C₀ v₀ := by
  unfold idealGroupedBudgetExponent
  apply mul_nonneg hC₀
  apply add_nonneg
  · exact Real.log_nonneg (by exact_mod_cast Nat.factorial_pos m)
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (le_max_left _ _))

theorem idealMinorCellBilinear_uniform (m : ℕ) (C₀ v₀ c d E X H : ℝ)
    (hC₀ : 0 ≤ C₀) (hv₀ : 0 < v₀) (hc : 0 < c) (hd : 0 ≤ d)
    (hE : 0 ≤ E) (hX : 0 ≤ X) (hH : 1 ≤ H) :
    ∀ᶠ L : ℝ in atTop, ∀ (A : Type u) (B : Type v)
      [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B],
      ∀ (P : A → Finset ℕ) (k : A → ℕ) (R : B → Finset ℕ) (l : B → ℕ),
      (∀ i p, p ∈ P i → p.Prime) → (∀ i p, p ∈ R i → p.Prime) →
      Pairwise (fun i j => Disjoint (P i) (P j)) → Pairwise (fun i j => Disjoint (R i) (R j)) →
      (∀ i, v₀ ≤ bandReciprocalMass (P i)) → (∀ i, v₀ ≤ bandReciprocalMass (R i)) →
      (∀ i, k i ≤ m) → (∀ i, l i ≤ m) →
      (Fintype.card A : ℝ) ≤ C₀*Real.log L → (Fintype.card B : ℝ) ≤ C₀*Real.log L →
      (∀ i p, p ∈ P i → Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
      (∀ i p, p ∈ R i → Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
      ∀ (i : Σ a, Fin (k a)) (j : Σ b, Fin (l b)), IdealPrimeInterval (P i.1) → IdealPrimeInterval (R j.1) →
      ∀ Q : ℕ, (Q : ℝ) ≤ L^(idealMinorBilinearExponent m C₀ v₀ d E) →
      ∀ U V r : ℕ, 0 < U → 0 < V → 0 < r →
      Real.exp (L^c)/4 ≤ (U : ℝ) → Real.exp (L^c)/4 ≤ (V : ℝ) →
      Real.log (U : ℝ) ≤ L^(d+2) → Real.log (V : ℝ) ≤ L^(d+2) →
      L^(idealMinorBilinearExponent m C₀ v₀ d E)/2 ≤ (r : ℝ) →
      (r : ℝ) ≤ 64*(U : ℝ)*(V : ℝ)/L^(idealMinorBilinearExponent m C₀ v₀ d E) →
      ∀ (ζ α : ℝ) (w : ℤ), IsCoprime w (r : ℤ) → |α-(w : ℝ)/r| ≤ 1/(r : ℝ)^2 →
      ∀ (f : IdealSelectedLabels (fun z : Σ i, Fin (k i) => P z.1) → ℂ)
        (g : IdealSelectedLabels (fun z : Σ i, Fin (l i) => R z.1) → ℂ),
      (∀ x, idealSelectedProduct x ∉ Finset.Ico (2*U) (4*U) → f x = 0) →
      (∀ y, idealSelectedProduct y ∉ Finset.Ico (2*V) (4*V) → g y = 0) →
      ‖∑ x, (idealSelectedMass (fun z : Σ i, Fin (k i) => P z.1) x : ℂ)*f x*
        ∑ y, (idealSelectedMass (fun z : Σ i, Fin (l i) => R z.1) y : ℂ)*g y*
          (idealProductPhase ζ α (idealSelectedProduct x) (idealSelectedProduct y) -
            idealFullCellPhaseAverage (fun z : Σ i, Fin (k i) => P z.1)
              (fun z : Σ i, Fin (l i) => R z.1) Q (L^(-H)) (L^(-X)) ζ α x y)‖^2 ≤
        L^(-2*E)*idealFrameEnergy (idealSelectedMass (fun z : Σ i, Fin (k i) => P z.1)) f*
          idealFrameEnergy (idealSelectedMass (fun z : Σ i, Fin (l i) => R z.1)) g := by
  let κ := idealGroupedBudgetExponent m C₀ v₀
  let a := idealMinorBilinearExponent m C₀ v₀ d E
  have hκ : 0 ≤ κ := idealGroupedBudgetExponent_nonneg m hC₀
  have ha : 0 ≤ a := by dsimp [a, idealMinorBilinearExponent, idealMinorCutoffExponent]; linarith
  filter_upwards [idealCharacterCellTranspose_uniform.{u} a c d X v₀ ha hc hd hX hv₀,
    idealCharacterCellTranspose_uniform.{v} a c d X v₀ ha hc hd hX hv₀,
    idealMinorGramBudget_source c d (E+2) κ hc hd, idealSource_gram_log_bound d hd,
    idealSource_log_width H hH, eventually_ge_atTop (34 : ℝ)] with L hnormP hnormR hgram hlog hwidth hL34
  have hL1 : 1 ≤ L := by linarith
  have hL : 0 < L := by linarith
  intro A B _ _ _ _ P k R l hP hR hdisP hdisR hVP hVR hk hl hcardP hcardR hbP hbR i j hi hj
    Q hQ U V r hU hV hr hUlarge hVlarge hUlog hVlog hrlo hrhi ζ α w hcop happrox f g hf hg
  have hvP : ∀ i, 0 < bandReciprocalMass (P i) := fun i => hv₀.trans_le (hVP i)
  have hvR : ∀ i, 0 < bandReciprocalMass (R i) := fun i => hv₀.trans_le (hVR i)
  have hnorm1 := hnormP (Σ a, Fin (k a)) Q hQ (fun z => P z.1)
    (fun z p hp => hP z.1 p hp) (fun z => hvP z.1) (fun z => hbP z.1) i hi (hVP i.1)
    (L^(-H)) hwidth.1
  have hnorm2 := hnormR (Σ b, Fin (l b)) Q hQ (fun z => R z.1)
    (fun z p hp => hR z.1 p hp) (fun z => hvR z.1) (fun z => hbR z.1) j hj (hVR j.1)
    (L^(-H)) hwidth.1
  have hraw := idealMinorCellBilinear_sq_le P k R l hP hR hdisP hdisR hvP hvR Q hwidth.1 hwidth.2
    hnorm1 hnorm2 U V hU hV f g hf hg ζ α w r hr hcop happrox
  have hbp := idealGroupedAtomBudget_power P k hv₀ hL1 hVP hk hcardP
  have hbr := idealGroupedAtomBudget_power R l hv₀ hL1 hVR hl hcardR
  have hS1 : 1 ≤ L^a := Real.one_le_rpow hL1 ha
  have hrwide : (r : ℝ) ≤ 64*(U : ℝ)*(V : ℝ) :=
    hrhi.trans (div_le_self (by positivity) hS1)
  have hlogr := hlog U V r hU hV hr hUlog hVlog hrwide
  have hrGram : (r : ℝ) ≤ (((8*U : ℕ) : ℝ)*((8*V : ℕ) : ℝ))/L^a := by
    apply hrhi.trans_eq
    push_cast
    ring
  have hUM : (U : ℝ) ≤ ((8*U : ℕ) : ℝ) := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ U by positivity]
  have hVM : (V : ℝ) ≤ ((8*V : ℕ) : ℝ) := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ V by positivity]
  have hg := hgram (8*U) (8*V) r (by omega) (by omega) hr
    (hUlarge.trans hUM) (hVlarge.trans hVM) hrlo
    hrGram hlogr
  have hG0 := markedMinorGramBudget_nonneg (8*U) (8*V) r hr
  have hprod : idealGroupedAtomBudget P k*idealGroupedAtomBudget R l ≤ L^(2*κ) := by
    calc
      _ ≤ L^κ*L^κ := mul_le_mul hbp hbr (idealGroupedAtomBudget_nonneg R l hvR)
        (Real.rpow_nonneg hL.le _)
      _ = _ := by rw [← Real.rpow_add hL]; congr 1; ring
  have hcoeff : 34*markedMinorGramBudget (8*U) (8*V) r*(idealGroupedAtomBudget P k/(U : ℝ))*
      (idealGroupedAtomBudget R l/(V : ℝ)) ≤ L^(-2*E) := by
    have hUr : 0 < (U : ℝ) := by exact_mod_cast hU
    have hVr : 0 < (V : ℝ) := by exact_mod_cast hV
    calc
      _ = 34*(64*(idealGroupedAtomBudget P k*idealGroupedAtomBudget R l)*
          (markedMinorGramBudget (8*U) (8*V) r/(((8*U : ℕ) : ℝ)*((8*V : ℕ) : ℝ)))) := by
        push_cast
        field_simp
        ring
      _ ≤ 34*(64*L^(2*κ)*(markedMinorGramBudget (8*U) (8*V) r/
          (((8*U : ℕ) : ℝ)*((8*V : ℕ) : ℝ)))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 34)
        apply mul_le_mul_of_nonneg_right _ (div_nonneg hG0 (by positivity))
        exact mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ ≤ 34*L^(-2*(E+2)) := mul_le_mul_of_nonneg_left hg (by norm_num)
      _ ≤ L*L^(-2*(E+2)) := mul_le_mul_of_nonneg_right hL34 (Real.rpow_nonneg hL.le _)
      _ = L^(-2*E-3) := by
        nth_rw 1 [← Real.rpow_one L]
        rw [← Real.rpow_add hL]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff
      (idealFrameEnergy_nonneg _ (idealSelectedMass_nonneg (fun z : Σ i, Fin (k i) => P z.1)
        (fun z => hvP z.1)) f))
    (idealFrameEnergy_nonneg _ (idealSelectedMass_nonneg (fun z : Σ i, Fin (l i) => R z.1)
      (fun z => hvR z.1)) g))

end
end ArtinMatthews
