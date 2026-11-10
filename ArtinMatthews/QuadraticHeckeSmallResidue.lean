module

public import ArtinMatthews.QuadraticHeckeCutoffSplit
public import ArtinMatthews.QuadraticHeckeMainTermEuler
public import ArtinMatthews.QuadraticHeckeCutoffWeightBounds
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField VaryingKummerAnalytic UniqueFactorizationMonoid
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
open HeckeIdealMobius (primeSupport)

private theorem primeSupport_mul {a b : Ideal (𝓞 F)} (ha : a ≠ ⊥) (hb : b ≠ ⊥) :
    primeSupport F (a * b) = primeSupport F a ∪ primeSupport F b := by
  ext P
  simp only [primeSupport, normalizedFactors_mul ha hb, Multiset.mem_toFinset,
    Finset.mem_union, Multiset.mem_add]

private theorem primeSupport_disjoint {a b : Ideal (𝓞 F)} (hab : IsCoprime a b) :
    Disjoint (primeSupport F a) (primeSupport F b) := by
  apply Finset.disjoint_left.mpr
  intro P ha hb
  exact (HeckeIdealMobius.support_prime F ha).not_isUnit
    (hab.isUnit_of_dvd' (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp ha))
      (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hb)))

/-- The normalized coprime density factors on coprime nonzero ideal products. -/
theorem quadraticHeckeCoprimeDensity_mul {a b : Ideal (𝓞 F)}
    (ha : a ≠ ⊥) (hb : b ≠ ⊥) (hab : IsCoprime a b) :
    quadraticHeckeCoprimeDensity F (a * b) =
      quadraticHeckeCoprimeDensity F a * quadraticHeckeCoprimeDensity F b := by
  unfold quadraticHeckeCoprimeDensity
  rw [primeSupport_mul F ha hb, Finset.prod_union (primeSupport_disjoint F hab)]

/-- The finite real norm cutoff identifies the corresponding squarefree ideal tsum. -/
theorem quadraticHeckeSquarefreeCutoff_tsum (H : ℝ) (f : Ideal (𝓞 F) → ℂ) :
    (∑' a : {J : Ideal (𝓞 F) // Squarefree J},
      if (Ideal.absNorm a.val : ℝ) ≤ H then f a.val else 0) =
        ∑ a ∈ quadraticHeckeSquarefreeCutoff F H, f a := by
  let f₀ (J : Ideal (𝓞 F)) : ℂ :=
    if Squarefree J ∧ (Ideal.absNorm J : ℝ) ≤ H then f J else 0
  have hsupport : Function.support f₀ ⊆ {J : Ideal (𝓞 F) | Squarefree J} := by
    intro J hJ
    by_contra h
    change ¬ Squarefree J at h
    exact hJ (by simp only [f₀, h, false_and, ite_false])
  calc
    _ = ∑' a : {J : Ideal (𝓞 F) // Squarefree J}, f₀ a.val := by
      apply tsum_congr
      intro a
      simp only [f₀, a.property, true_and]
    _ = ∑' J : Ideal (𝓞 F), f₀ J := tsum_subtype_eq_of_support_subset hsupport
    _ = ∑ J ∈ quadraticHeckeSquarefreeCutoff F H, f₀ J := by
      apply tsum_eq_sum
      intro J hJ
      exact ite_eq_right (fun h => hJ ((mem_quadraticHeckeSquarefreeCutoff F).2 h))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro J hJ
      exact ite_eq_left ((mem_quadraticHeckeSquarefreeCutoff F).1 hJ)

/-- Both fixed and common-ideal masks remain in the finite squarefree cutoff. -/
theorem quadraticHeckeSquarefreeCutoff_masked_tsum (g m : Ideal (𝓞 F))
    (H : ℝ) (f : Ideal (𝓞 F) → ℂ) :
    (∑' a : {J : Ideal (𝓞 F) // Squarefree J},
      if IsCoprime a.val m ∧ IsCoprime a.val g ∧ (Ideal.absNorm a.val : ℝ) ≤ H then
        f a.val else 0) =
      ∑ a ∈ quadraticHeckeCoprimeCutoff F g H, if IsCoprime a m then f a else 0 := by
  calc
    _ = ∑' a : {J : Ideal (𝓞 F) // Squarefree J},
        if (Ideal.absNorm a.val : ℝ) ≤ H then
          (if IsCoprime a.val m ∧ IsCoprime a.val g then f a.val else 0) else 0 := by
      apply tsum_congr
      intro a
      by_cases hn : (Ideal.absNorm a.val : ℝ) ≤ H
      · simp only [hn, and_true, ite_true]
      · simp only [hn, and_false, ite_false]
    _ = ∑ a ∈ quadraticHeckeSquarefreeCutoff F H,
        if IsCoprime a m ∧ IsCoprime a g then f a else 0 :=
      quadraticHeckeSquarefreeCutoff_tsum F H
        (fun a : Ideal (𝓞 F) => if IsCoprime a m ∧ IsCoprime a g then f a else 0)
    _ = _ := by
      rw [quadraticHeckeCoprimeCutoff, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hg : IsCoprime a g
      · simp only [hg, and_true, ite_true]
      · simp only [hg, and_false, ite_false]

/-- At the actual square scale the residue coefficient is the half-norm coefficient. -/
theorem quadraticHeckeSmallResidue_term {N : Ideal (𝓞 F)}
    (ψ : EvenIdealRayCharacter F N) {M : ℝ} (hM : 0 ≤ M)
    (a : Ideal (𝓞 F)) (R T : ℂ) :
    ψ.allCoefficient a * (R * (Real.sqrt (M / (Ideal.absNorm a : ℝ)) : ℂ) * T) =
      (R * (Real.sqrt M : ℂ) * T) * quadraticHeckeHalfCoefficient F ψ a := by
  rw [quadraticHeckeHalfCoefficient_eq_div_sqrt, Real.sqrt_div hM]
  push_cast
  ring

/-- The literal small-squarefree residue sum has the finite masked half-coefficient form. -/
theorem quadraticHeckeSmallResidue_sum {N : Ideal (𝓞 F)}
    (ψ : EvenIdealRayCharacter F N) (g m : Ideal (𝓞 F)) {M : ℝ} (hM : 0 ≤ M)
    (H : ℝ) (R T : ℂ) :
    (∑' a : {J : Ideal (𝓞 F) // Squarefree J},
      if IsCoprime a.val m ∧ IsCoprime a.val g ∧ (Ideal.absNorm a.val : ℝ) ≤ H then
        ψ.allCoefficient a.val *
          (R * (Real.sqrt (M / (Ideal.absNorm a.val : ℝ)) : ℂ) * T) else 0) =
      (R * (Real.sqrt M : ℂ) * T) *
        ∑ a ∈ quadraticHeckeCoprimeCutoff F g H,
          if IsCoprime a m then quadraticHeckeHalfCoefficient F ψ a else 0 := by
  rw [quadraticHeckeSquarefreeCutoff_masked_tsum F g m H
    (fun a : Ideal (𝓞 F) => ψ.allCoefficient a *
      (R * (Real.sqrt (M / (Ideal.absNorm a : ℝ)) : ℂ) * T)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : IsCoprime a m
  · rw [ite_eq_left ha, ite_eq_left ha]
    exact quadraticHeckeSmallResidue_term F ψ hM a R T
  · rw [ite_eq_right ha, ite_eq_right ha, mul_zero]

end
end ArtinMatthews
