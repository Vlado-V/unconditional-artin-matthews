module

public import ArtinMatthews.MarkedArrayEulerModel
public import ArtinMatthews.GiantFixedResiduePolynomial
public import ArtinMatthews.GiantMarkedResidual
public import ArtinMatthews.GiantFixedResidueInsertion
public import ArtinMatthews.MarkedProgressionCoprime
public import ArtinMatthews.MarkedProgressionFamily
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The exact fixed-unit progression for the represented marking choices.
Both absolute and reciprocal coefficient masses retain their original
normalization, with the fixed-modulus correction only in the density. -/
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators
noncomputable section

private theorem giantFixedResidue_selected_card_le {ι : Type*} [Fintype ι] {a : ι → ℕ}
    (t : (i : ι) → Fin (a i) → ℕ) : (representedArraySelected t).card ≤ ∑ i, a i := by
  classical
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro i _
  exact Finset.card_image_le.trans_eq (by simp)

private theorem giantFixedResidue_residual_uniform_bound (M r₀ : ℕ)
    (hM : 0 < M) (hr₀ : r₀.Coprime M) (G P S : Finset ℕ)
    (hcop : ∀ p∈P,p.Coprime M) (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (θ : ℕ → ℝ)
    (hθ : ∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) (m R s : ℕ) (hs : S.card ≤ s)
    (hG : ∀ ell ∈ G, ell=1 ∨ ell.Prime) (hGM : ∀ ell∈G,ell.Coprime M) (hdis : Disjoint G P)
    (hθG : ∀ ell ∈ G, 0 ≤ θ ell ∧ θ ell ≤ 1)
    {y V N : ℝ} (hy : 0 < y) (hmin : ∀ p ∈ P, y ≤ (p : ℝ))
    (hGmin : ∀ ell ∈ G, ell=1 ∨ y ≤ (ell : ℝ)) (hV : 0 ≤ V)
    (hmass : ∑ p ∈ P \ S, θ p / (p : ℝ) ≤ V)
    (hN : max 1 ((P \ S).card : ℝ) ≤ N)
    (Φ : ℝ → ℝ) {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ))
    (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t) :
    (∑ r ∈ Finset.Icc 1 R,
      |(∑ u ∈ giantFixedResidueSet M r₀ r (T*x),
        Φ ((u : ℝ) / x) * (giantWindowDivisorCount G u * markedWeightedResidual P S θ u)) -
        giantFixedResidueScale M r (x * ∫ t in Set.Ioc 0 T, Φ t) *
          ((∑ ell ∈ G, 1 / (ell : ℝ)) * markedWeightedModel P S θ)|) ≤
      ((R : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv Φ t|) *
        (((2 * m + 1 : ℕ) : ℝ) * N ^ (2 * m) + N ^ (2 * m + 1))) * G.card +
      ((((x * ∫ t in Set.Ioc 0 T, Φ t) * (harmonic R : ℝ)) *
        ((((s + 1 + 2 * m : ℕ) : ℝ) / y) * Real.exp V +
          2 * (V ^ (2 * m + 1) / (2 * m + 1).factorial))) *
        (∑ ell ∈ G, 1 / (ell : ℝ))) / (∏ p ∈ S, p : ℕ) := by
  have h := giantFixedResidue_window_residual M r₀ hM hr₀ G P S hcop hP hS θ hθ m R hG hdis hGM hθG
    hy hmin hGmin hV hmass Φ hx hT hΦ hderiv hΦT hΦ0
  have hI : 0 ≤ ∫ t in Set.Ioc 0 T, Φ t := integral_nonneg hΦ0
  have hJ : 0 ≤ ∫ t in Set.Ioc 0 T, |deriv Φ t| := integral_nonneg (fun _ => abs_nonneg _)
  have hH : 0 ≤ (harmonic R : ℝ) := by
    rw [← reciprocal_Icc_eq_harmonic]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hGmass : 0 ≤ ∑ ell ∈ G, 1 / (ell : ℝ) := Finset.sum_nonneg (fun _ _ => by positivity)
  have hN0 : 0 ≤ max 1 ((P \ S).card : ℝ) := le_trans (by norm_num) (le_max_left _ _)
  apply h.trans
  calc
    _ ≤ ((R : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv Φ t|) *
        (((2 * m + 1 : ℕ) : ℝ) * N ^ (2 * m) + N ^ (2 * m + 1))) * G.card +
      (((x * ∫ t in Set.Ioc 0 T, Φ t) * (harmonic R : ℝ)) *
        (1 / (∏ p ∈ S, p : ℕ)) *
        ((((s + 1 + 2 * m : ℕ) : ℝ) / y) * Real.exp V +
          2 * (V ^ (2 * m + 1) / (2 * m + 1).factorial))) *
        (∑ ell ∈ G, 1 / (ell : ℝ)) := by
      gcongr
    _ = _ := by ring

/-- The actual finite array estimate, with exact giant-window reciprocal
mass and cardinality. All analytic errors on the right have been proved. -/
theorem giantFixedResidue_array_progression_error {ι : Type*} [Fintype ι]
    (M r₀ : ℕ) (hM : 0 < M) (hr₀ : r₀.Coprime M)
    (G : Finset ℕ) (P : ι → Finset ℕ) (W : ι → ℝ) (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (hcop : ∀ i p, p∈P i → p.Coprime M) (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (hP : ∀ i p, p ∈ P i → p.Prime) (m R : ℕ)
    (hG : ∀ ell ∈ G, ell=1 ∨ ell.Prime) (hGM : ∀ ell∈G,ell.Coprime M) (hGP : Disjoint G (Finset.univ.biUnion P))
    {y V : ℝ} (hy : 0 < y) (hmin : ∀ i p, p ∈ P i → y ≤ (p : ℝ))
    (hGmin : ∀ ell ∈ G, ell=1 ∨ y ≤ (ell : ℝ))
    (hV : 0 ≤ V) (hmass : ∑ p ∈ Finset.univ.biUnion P, 1 / (p : ℝ) ≤ V)
    (Φ : ℝ → ℝ) {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t) :
    (∑ r ∈ Finset.Icc 1 R,
      |(∑ u ∈ giantFixedResidueSet M r₀ r (T*x),
          Φ ((u : ℝ) / x) * (giantWindowDivisorCount G u *
            ∏ i, (bandWeight (P i) (W i) u) ^ a i)) -
        giantFixedResidueScale M r (x * ∫ t in Set.Ioc 0 T, Φ t) *
          ((∑ ell ∈ G, 1 / (ell : ℝ)) * representedArrayEulerMean P W a)|) ≤
      (((R : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv Φ t|) *
        (((2 * m + 1 : ℕ) : ℝ) * (max 1 ((Finset.univ.biUnion P).card : ℝ)) ^ (2 * m) +
          (max 1 ((Finset.univ.biUnion P).card : ℝ)) ^ (2 * m + 1))) * G.card) *
        (∑ t ∈ representedArrayChoices P a, |representedArrayCoefficient W a t|) +
      ((((x * ∫ t in Set.Ioc 0 T, Φ t) * (harmonic R : ℝ)) *
        (((((∑ i, a i) + 1 + 2 * m : ℕ) : ℝ) / y) * Real.exp V +
          2 * (V ^ (2 * m + 1) / (2 * m + 1).factorial))) *
        (∑ ell ∈ G, 1 / (ell : ℝ))) *
        (∑ t ∈ representedArrayChoices P a,
          |representedArrayCoefficient W a t| / (∏ p ∈ representedArraySelected t, p : ℕ)) := by
  classical
  let Q := Finset.univ.biUnion P
  let θ := representedArrayDamping Finset.univ P a (1 / 2)
  have hQ : ∀ p ∈ Q, p.Prime := by
    intro p hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    exact hP i p hi
  have hQcop : ∀ p∈Q,p.Coprime M := by
    intro p hp
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
    exact hcop i p hi
  have hqmin : ∀ p ∈ Q, y ≤ (p : ℝ) := by
    intro p hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    exact hmin i p hi
  have hθ : ∀ p ∈ Q, 0 ≤ θ p ∧ θ p ≤ 1 := fun p hp =>
    representedArrayDamping_mem_unitInterval Finset.univ P a (by norm_num) (by norm_num)
      (fun i _ j _ hij => hdis hij) hp
  have hθG : ∀ ell ∈ G, 0 ≤ θ ell ∧ θ ell ≤ 1 := by
    intro ell hell
    have hzero : θ ell = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact ite_eq_right (fun hp => Finset.disjoint_left.mp hGP hell
        (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hp⟩))
    rw [hzero]
    norm_num
  have hsel (t) (ht : t ∈ representedArrayChoices P a) : representedArraySelected t ⊆ Q := by
    intro p hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
      representedChoiceSet_subset (Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp ht i)) hi⟩
  have hterm (t) (ht : t ∈ representedArrayChoices P a) :=
    giantFixedResidue_residual_uniform_bound M r₀ hM hr₀ G Q (representedArraySelected t) hQcop hQ (hsel t ht) θ hθ m R
      (∑ i, a i) (giantFixedResidue_selected_card_le t) hG hGM hGP hθG hy hqmin hGmin hV (by
        calc
          _ ≤ ∑ p ∈ Q \ representedArraySelected t, 1 / (p : ℝ) := by
            apply Finset.sum_le_sum
            intro p hp
            exact div_le_div_of_nonneg_right (hθ p (Finset.mem_sdiff.mp hp).1).2 (Nat.cast_nonneg _)
          _ ≤ ∑ p ∈ Q, 1 / (p : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg
            Finset.sdiff_subset (fun p _ _ => by positivity)
          _ ≤ V := hmass)
      (N := max 1 (Q.card : ℝ)) (by
        apply max_le_max_left
        exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := Q) (t := representedArraySelected t)))
      Φ hx hT hΦ hderiv hΦT hΦ0
  have hfam := marked_family_summed_error_of_bounds (Finset.Icc 1 R)
    (fun r => giantFixedResidueSet M r₀ r (T*x))
    (representedArrayChoices P a) (fun u => Φ ((u : ℝ) / x))
    (representedArrayCoefficient W a)
    (fun t => (∑ ell ∈ G, 1 / (ell : ℝ)) * markedWeightedModel Q (representedArraySelected t) θ)
    (fun t u => giantWindowDivisorCount G u * markedWeightedResidual Q (representedArraySelected t) θ u)
    (fun r => giantFixedResidueScale M r (x * ∫ t in Set.Ioc 0 T, Φ t))
    (fun t => (∏ p ∈ representedArraySelected t, p : ℕ)) _ _ hterm
  have hweight (u : ℕ) : (∑ t ∈ representedArrayChoices P a,
      representedArrayCoefficient W a t *
        (giantWindowDivisorCount G u * markedWeightedResidual Q (representedArraySelected t) θ u)) =
      giantWindowDivisorCount G u * ∏ i, (bandWeight (P i) (W i) u) ^ a i := by
    rw [bandWeight_product_powers_eq_normalized_residual_sum P W a ha hdis, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hmodel : (∑ t ∈ representedArrayChoices P a,
      representedArrayCoefficient W a t *
        ((∑ ell ∈ G, 1 / (ell : ℝ)) * markedWeightedModel Q (representedArraySelected t) θ)) =
      (∑ ell ∈ G, 1 / (ell : ℝ)) * representedArrayEulerMean P W a := by
    unfold representedArrayEulerMean
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  simp_rw [hweight, hmodel] at hfam
  exact hfam

end
end ArtinMatthews
