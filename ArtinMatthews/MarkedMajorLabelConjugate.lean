module

public import ArtinMatthews.MarkedMajorArcConjugate
public import ArtinMatthews.MarkedMajorLabelPolynomial
public import ArtinMatthews.MarkedSparsePhaseKernel
public import ArtinMatthews.MarkedMajorLabelCancellation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! The same full prime-label energy with the actual conjugated centered coefficient. -/
namespace ArtinMatthews
open Finset Filter MeasureTheory
open scoped Topology ContDiff

theorem marked_major_label_conjugate_cancellation
    (cutoff : ℝ → ℂ) (hcutoff : ContDiff ℝ ∞ cutoff) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) (hsupp : Function.support cutoff ⊆ Set.Icc lo hi)
    (c C₁ C₂ d a η τ C b K σ b₀ D P A₀ Kθ v₀ : ℝ)
    (hc : 0 < c) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hd : 0 < d)
    (ha : 0 ≤ a) (hη : 0 < η) (hτ : 0 < τ) (hC : 0 ≤ C)
    (hσ : 0 ≤ σ) (hb₀ : 0 ≤ b₀) (hD : 0 ≤ D) (hP : 0 ≤ P)
    (hA₀ : 0 ≤ A₀) (hKθ : 0 ≤ Kθ) (hv₀ : 0 < v₀) :
    ∀ᶠ L : ℝ in atTop,∀ {J : Type} [Fintype J] [DecidableEq J]
      (P₀ : Finset ℕ) (bands : J → Finset ℕ),
      (∀ p ∈ P₀,p.Prime) → (∀ j p,p ∈ bands j → p.Prime) →
      (∀ j,Disjoint P₀ (bands j)) → Pairwise (fun i j => Disjoint (bands i) (bands j)) →
      v₀ ≤ bandReciprocalMass P₀ → (∀ j,0 < bandReciprocalMass (bands j)) →
      (∀ p ∈ P₀,c*L^(1/(10:ℝ)) ≤ Real.log p) →
      (∀ p ∈ P₀,Real.log p ≤ C₁*L^(1/(5:ℝ))) →
      ∀ (Y θ T H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ),
      0 < Y → |θ| ≤ Kθ*L^A₀ → 1 < T → Real.log T ≤ C₂*L →
      T ≤ K*Real.exp L*L^b → Real.exp (τ*L) ≤ H → H ≤ u → u ≤ v →
      v ≤ 2*H → v ≤ Real.exp (η*L) → Real.exp (d*L) ≤ U →
      U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U → H*U ≤ Real.exp (σ*L) → T/(H*U) ≤ L^b₀ →
      (∀ n ∈ Icc l r,‖β n‖ ≤ L^D) →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (modulation : ℝ),
      (q:ℝ) ≤ L^a → |modulation| ≤ L^C →
      ∀ (k : ℕ) (χb : DirichletCharacter ℂ k),
      (∫ t in Set.Icc (-T) T,
        ‖markedMajorLabelPolynomial (fun j : Option J => j.elim P₀ bands) cutoff χb θ Y t*
          markedMajorConjugateCenteredSum χ (Real.exp (L^(6/25:ℝ))) modulation t H u v*
          markedDyadicPolynomial l r U β t‖^2) ≤ L^(-P) := by
  filter_upwards [marked_major_label_cancellation cutoff hcutoff hlo hhi hsupp
    c C₁ C₂ d a η τ C b K σ b₀ D P A₀ Kθ v₀
    hc hC₁ hC₂ hd ha hη hτ hC hσ hb₀ hD hP hA₀ hKθ hv₀] with L hL
  intro J _ _ P₀ bands hP₀ hbands hdis₀ hdis hV₀ hV hloP hhiP
    Y θ T H u v U l r β hY hθ hT hTlog hTupper hH hHu huv hvH hvhi hU hl hr hHU hratio hβ
    q _ χ modulation hq hmod k χb
  simp only [marked_conjugate_centered_sum_eq]
  exact hL P₀ bands hP₀ hbands hdis₀ hdis hV₀ hV hloP hhiP
    Y θ T H u v U l r β hY hθ hT hTlog hTupper hH hHu huv hvH hvhi hU hl hr hHU hratio hβ
    q χ (-modulation) hq (by simpa only [abs_neg] using hmod) k χb

end ArtinMatthews
