module

public import ArtinMatthews.VaryingKummerAnalyticHeckeGoodFamily
public import ArtinMatthews.VaryingKummerAnalyticHeckeFiniteEulerBounds
public import ArtinMatthews.VaryingKummerAnalyticHeckeFiniteEulerAlgebra
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine nonprincipal continuation of the old-modulus coprime Dirichlet series,
and its subpower reciprocal bound outside the actual exceptional family. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {f : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K f) (hf : f ≠ ⊥) (hprim : IsPrimitiveOnIdeals ψ.residue)

def idealCoprimeContinued (M : Ideal (𝓞 K)) (s : ℂ) : ℂ :=
  ψ.primitiveContinued hf hprim s*ψ.idealEulerDeletion M s

theorem idealCoprimeContinued_entire (M : Ideal (𝓞 K)) :
    Differentiable ℂ (ψ.idealCoprimeContinued hf hprim M) :=
  (ψ.primitiveContinued_entire hf hprim).mul (ψ.idealEulerDeletion_entire M)

theorem idealCoprimeContinued_eq_dirichlet (hnp : ψ.IsNonprincipal)
    (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) {s : ℂ} (hs : 1 < s.re) :
    ψ.idealCoprimeContinued hf hprim M s =
      ∑' I : Ideal (𝓞 K), if IsCoprime I M then
        ψ.allCoefficient I*(Ideal.absNorm I : ℂ)^(-s) else 0 :=
  (ψ.idealCoprimeDirichlet_primitive_hasSum hf hprim hnp M hM hs).tsum_eq.symm

theorem idealCoprimeContinued_zero_iff (M : Ideal (𝓞 K)) {s : ℂ} (hs : 0 < s.re) :
    ψ.idealCoprimeContinued hf hprim M s = 0 ↔ ψ.primitiveContinued hf hprim s = 0 := by
  rw [idealCoprimeContinued,mul_eq_zero]
  exact or_iff_left (ψ.idealEulerDeletion_ne_zero M hs)

theorem idealCoprimeContinued_inv_norm (M : Ideal (𝓞 K)) (s : ℂ) :
    ‖(ψ.idealCoprimeContinued hf hprim M s)⁻¹‖ =
      ‖(ψ.primitiveContinued hf hprim s)⁻¹‖ * ‖(ψ.idealEulerDeletion M s)⁻¹‖ := by
  rw [idealCoprimeContinued,mul_inv,norm_mul]

end EvenIdealRayCharacter

theorem exists_actual_primitive_good_family_with_deletions
    (K : Type*) [Field K] [NumberField K] :
    ∃ r C U₀ : ℝ, 0 < r ∧ r < 1/10 ∧ 0 < C ∧ 2 ≤ U₀ ∧
      (∀ U : ℝ, U₀ ≤ U →
        ∀ (T : Finset (IdealConductorModulus K))
          (A : ∀ f : IdealConductorModulus K, Finset (EvenIdealRayCharacter K f.val)),
          (∀ f ∈ T, (Ideal.absNorm f.val : ℝ) ≤ U) →
          (∀ f ∈ T, ∀ ψ ∈ A f, IsPrimitiveOnIdeals ψ.residue) →
          (∀ f ∈ T, ∀ ψ ∈ A f, ψ.IsNonprincipal) →
          (∑ f ∈ T, ((primitiveExceptionalCoefficients K f (A f) U r).card : ℝ)) ≤ C*U^(1/2 : ℝ)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 < B ∧
        ∀ U : ℝ, U₀ ≤ U →
        ∀ (T : Finset (IdealConductorModulus K))
          (A : ∀ f : IdealConductorModulus K, Finset (EvenIdealRayCharacter K f.val)),
          (∀ f ∈ T, (Ideal.absNorm f.val : ℝ) ≤ U) →
          (∀ f ∈ T, ∀ ψ ∈ A f, IsPrimitiveOnIdeals ψ.residue) →
          (∀ f ∈ T, ∀ ψ ∈ A f, ψ.IsNonprincipal) →
          ∀ f ∈ T, ∀ ψ ∈ A f, ∀ hprim : IsPrimitiveOnIdeals ψ.residue,
            ψ.coefficient ∉ primitiveExceptionalCoefficients K f (A f) U r →
            ∀ M : Ideal (𝓞 K), M ≠ ⊥ → (Ideal.absNorm M : ℝ) ≤ U →
            ∀ s : ℂ, (499/500 : ℝ) ≤ s.re → |s.im| ≤ 2*U^r →
              ‖(ψ.idealCoprimeContinued f.property hprim M s)⁻¹‖ ≤ B*U^ε) := by
  obtain ⟨r,C,U₀,hr,hr',hC,hU₀,hcount,hgood⟩ := exists_actual_primitive_good_family K
  refine ⟨r,C,U₀,hr,hr',hC,hU₀,hcount,?_⟩
  intro ε hε
  obtain ⟨B,hB,hrec⟩ := hgood (ε/2) (by positivity)
  obtain ⟨D,hD,hdel⟩ := exists_idealEulerDeletion_subpower_bound K (ε/2) (by positivity)
  refine ⟨B*D,mul_pos hB hD,?_⟩
  intro U hU T A hT hA hnp f hfT ψ hψ hprim hcomp M hM hMU s hs him
  have hU1 : 1 ≤ U := by linarith [hU₀.trans hU]
  have hU0 : 0 < U := zero_lt_one.trans_le hU1
  have H := hrec U hU T A hT hA hnp f hfT ψ hψ hprim hcomp s hs him
  have Hdel := hdel ψ M hM s (by linarith : (1/2 : ℝ) ≤ s.re)
  have hd : ‖(ψ.idealEulerDeletion M s)⁻¹‖ ≤ D*U^(ε/2) := by
    have h1 : ‖(ψ.idealEulerDeletion M s)⁻¹‖ ≤ D*(Ideal.absNorm M : ℝ)^(ε/2) := by
      linarith [norm_nonneg (ψ.idealEulerDeletion M s)]
    exact h1.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hMU (by positivity)) hD.le)
  rw [ψ.idealCoprimeContinued_inv_norm]
  calc
    _ ≤ (B*U^(ε/2))*(D*U^(ε/2)) :=
      mul_le_mul H hd (norm_nonneg _) (by positivity)
    _ = (B*D)*U^ε := by
      rw [mul_mul_mul_comm,← Real.rpow_add hU0]
      congr 1
      ring_nf

end
end ArtinMatthews.VaryingKummerAnalytic
