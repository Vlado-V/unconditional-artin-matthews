module

public import ArtinMatthews.FixedURootWeightedAbel
public import ArtinMatthews.FixedURootWeightedGeometry


set_option backward.privateInPublic true
@[expose] public section

/-! Smooth weighted root counts for each literal special-linear residue.
The rectangle discrepancy used here is the proved fixed-root discrepancy;
the root-ratio interval and all arithmetic conditions remain in the set. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators

def fixedURootWeightedSum {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (A B α β C D : ℝ) (lcR rcR : Bool) (f g : ℝ → ℂ) : ℂ :=
  ∑ p ∈ fixedURootMatrixBoxPoints g₀ A B α β C D true true lcR rcR true true,
    f (p.1 : ℝ)*g (p.2.2 : ℝ)

def fixedURootWeightedMain (S : ℕ) (A B α β C D : ℝ) (f g : ℝ → ℂ) : ℂ :=
  (((β-α)/((riemannZeta 2).re *
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) : ℝ) : ℂ) *
      (∫ t in A..B, f t)*(∫ s in C..D, g s)

/-- Two-dimensional Abel assembly for the actual root set. This intermediate
form keeps a concrete family of rectangular cardinality errors explicit. -/
theorem fixedURootWeightedSum_error_of_counts {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (A B α β C D : ℝ) (lcR rcR : Bool) (f g : ℝ → ℂ)
    (hAB : A ≤ B) (hCD : C ≤ D) (hf : Differentiable ℝ f) (hdf : Continuous (deriv f))
    (hg : Differentiable ℝ g) (hdg : Continuous (deriv g)) {E : ℝ}
    (hcount : ∀ t ∈ Set.Icc A B, ∀ s ∈ Set.Icc C D,
      |((fixedURootMatrixBoxPoints g₀ t B α β s D true true lcR rcR true true).card : ℝ) -
        ((B-t)*(β-α)*(D-s))/((riemannZeta 2).re *
          (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))| ≤ E) :
    ‖fixedURootWeightedSum g₀ A B α β C D lcR rcR f g -
      fixedURootWeightedMain S A B α β C D f g‖ ≤
        E*rootWeightVariation f A B*rootWeightVariation g C D := by
  classical
  let Z := fixedURootMatrixBoxPoints g₀ A B α β C D true true lcR rcR true true
  have hx : ∀ p ∈ Z, (p.1 : ℝ) ∈ Set.Icc A B :=
    fun p hp => (fixedURootMatrixBox_coordinate_bounds g₀ A B α β C D lcR rcR p hp).1
  have hy : ∀ p ∈ Z, (p.2.2 : ℝ) ∈ Set.Icc C D :=
    fun p hp => (fixedURootMatrixBox_coordinate_bounds g₀ A B α β C D lcR rcR p hp).2
  have hh := root_weight_rectangle_error Z (fun p => (p.1 : ℝ)) (fun p => (p.2.2 : ℝ))
    (fun _ => (1 : ℂ)) f g
    ((((β-α)/((riemannZeta 2).re *
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) : ℝ) : ℂ))
    (E := E) hAB hCD hx hy hf hdf hg hdg (fun t ht s hs => ?_)
  · simpa only [fixedURootWeightedSum, fixedURootWeightedMain, one_mul, Z] using hh
  · rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
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
    change ‖_‖ ≤ E
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
    exact hcount t ht s hs

/-- Actual smooth weighted root equidistribution, uniformly over the
prescribed SL₂ class, ratio interval flags and both coordinate regimes. -/
theorem fixedURootWeightedSum_uniform_power_saving {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
        (U V A B α β C D : ℝ) (lcR rcR : Bool) (f g : ℝ → ℂ),
        x^δ ≤ U → x^δ ≤ V → Squarefree S →
        (S : ℝ) ≤ Real.exp (M*(Real.log x)^(49/50 : ℝ)) →
        U ≤ A → A ≤ B → B ≤ 16*U →
        0 ≤ α → α ≤ β → β ≤ 1 → V ≤ C → C ≤ D → D ≤ 2*V →
        Differentiable ℝ f → Continuous (deriv f) →
        Differentiable ℝ g → Continuous (deriv g) →
        ‖fixedURootWeightedSum g₀ A B α β C D lcR rcR f g -
          fixedURootWeightedMain S A B α β C D f g‖ ≤
          (E*U*V*x^(-δ/1000))*rootWeightVariation f A B*rootWeightVariation g C D := by
  obtain ⟨E,hE,hcount⟩ := fixedURootMatrixBox_uniform_power_saving hδ M
  refine ⟨E,hE,?_⟩
  filter_upwards [hcount] with x hx
  intro S g₀ U V A B α β C D lcR rcR f g hU hV hS hSr hUA hAB hB
    hα hαβ hβ hVC hCD hD hf hdf hg hdg
  apply fixedURootWeightedSum_error_of_counts g₀ A B α β C D lcR rcR f g hAB hCD hf hdf hg hdg
  intro t ht s hs
  exact hx S g₀ U V t B α β s D true true lcR rcR true true hU hV hS hSr
    (hUA.trans ht.1) ht.2 hB hα hαβ hβ (hVC.trans hs.1) hs.2 hD

/-- Finite interval masks may have arbitrary complex coefficients and
overlap. The total variation cost is the literal coefficient l1 mass. -/
theorem fixedURootWeightedIntervalSum_uniform_power_saving {δ : ℝ}
    (hδ : 0 < δ) (M : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} (I : Finset ι) (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
        (U V A B C D : ℝ) (α β : ι → ℝ) (lcR rcR : ι → Bool)
        (c : ι → ℂ) (f g : ι → ℝ → ℂ),
        x^δ ≤ U → x^δ ≤ V → Squarefree S →
        (S : ℝ) ≤ Real.exp (M*(Real.log x)^(49/50 : ℝ)) →
        U ≤ A → A ≤ B → B ≤ 16*U → V ≤ C → C ≤ D → D ≤ 2*V →
        (∀ i ∈ I, 0 ≤ α i ∧ α i ≤ β i ∧ β i ≤ 1) →
        (∀ i ∈ I, Differentiable ℝ (f i) ∧ Continuous (deriv (f i)) ∧
          Differentiable ℝ (g i) ∧ Continuous (deriv (g i))) →
        ‖(∑ i ∈ I, c i*fixedURootWeightedSum g₀ A B (α i) (β i) C D (lcR i) (rcR i) (f i) (g i)) -
          ∑ i ∈ I, c i*fixedURootWeightedMain S A B (α i) (β i) C D (f i) (g i)‖ / (U*V) ≤
          E*x^(-δ/1000) *
            ∑ i ∈ I, ‖c i‖*rootWeightVariation (f i) A B*rootWeightVariation (g i) C D := by
  obtain ⟨E,hE,hcount⟩ := fixedURootWeightedSum_uniform_power_saving hδ M
  refine ⟨E,hE,?_⟩
  filter_upwards [hcount, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  intro ι I S g₀ U V A B C D α β lcR rcR c f g hU hV hS hSr hUA hAB hB hVC hCD hD hα hfg
  have hUp : 0 < U := (Real.rpow_pos_of_pos hx0 δ).trans_le hU
  have hVp : 0 < V := (Real.rpow_pos_of_pos hx0 δ).trans_le hV
  have hterm (i : ι) (hi : i ∈ I) := hx S g₀ U V A B (α i) (β i) C D
    (lcR i) (rcR i) (f i) (g i) hU hV hS hSr hUA hAB hB
    (hα i hi).1 (hα i hi).2.1 (hα i hi).2.2 hVC hCD hD
    (hfg i hi).1 (hfg i hi).2.1 (hfg i hi).2.2.1 (hfg i hi).2.2.2
  apply (div_le_iff₀ (mul_pos hUp hVp)).mpr
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ I, ‖c i*(fixedURootWeightedSum g₀ A B (α i) (β i) C D
        (lcR i) (rcR i) (f i) (g i) - fixedURootWeightedMain S A B (α i) (β i) C D (f i) (g i))‖ := by
      simp_rw [← mul_sub]
      exact norm_sum_le _ _
    _ ≤ ∑ i ∈ I, ‖c i‖*((E*U*V*x^(-δ/1000))*
        rootWeightVariation (f i) A B*rootWeightVariation (g i) C D) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hterm i hi) (norm_nonneg _)
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

end ArtinMatthews
