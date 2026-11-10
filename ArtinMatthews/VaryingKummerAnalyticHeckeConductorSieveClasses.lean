module

public import ArtinMatthews.VaryingKummerAnalyticHeckeConductorSieve
public import ArtinMatthews.VaryingKummerAnalyticRayClassSeries
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Finite ideal-class assembly of the actual Hecke conductor sieve.
The class representatives and every geometric constant depend only on the
field. The X + U² scale survives; multiplicities of residue fibers remain
explicit rather than being confused with distinct global characters. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def heckeConductorClassConstant : ℝ :=
  (Fintype.card (ClassGroup (𝓞 K)):ℝ) *
    ∑ c : ClassGroup (𝓞 K), idealModuleBalancedSieveConstant K
      (rayClassRepresentative K 1 c) (rayClassRepresentative_ne_bot K 1 c)

theorem heckeConductorClassConstant_pos : 0 < heckeConductorClassConstant K := by
  apply mul_pos (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (ClassGroup (𝓞 K))))
  exact Finset.sum_pos (fun c _ => idealModuleBalancedSieveConstant_pos K _ _)
    Finset.univ_nonempty

namespace EvenIdealRayCharacter
variable {K} {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M)

def classGroupHeckePolynomial
    (B : ∀ c : ClassGroup (𝓞 K), Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K), integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ) : ℂ :=
  ∑ c : ClassGroup (𝓞 K), ψ.idealClassHeckePolynomial (rayClassRepresentative K 1 c)
    (rayClassRepresentative_ne_bot K 1 c) (B c) (v c)

/-- This is a literal finite sum of genuine ideal coefficients over the
injective class-partition equivalence, not a substitute residue polynomial. -/
theorem classGroupHeckePolynomial_eq_ideal_sum
    (B : ∀ c : ClassGroup (𝓞 K), Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K), integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ) :
    ψ.classGroupHeckePolynomial B v =
      ∑ J ∈ (Finset.univ.sigma B).map (rayIdealClassPartitionEquiv K 1).toEmbedding,
        (let t := (rayIdealClassPartitionEquiv K 1).symm J; v t.1 t.2) * ψ.coefficient J := by
  rw [Finset.sum_map]
  rw [Finset.sum_sigma]
  unfold classGroupHeckePolynomial
  apply Finset.sum_congr rfl
  intro c _
  unfold idealClassHeckePolynomial
  apply Finset.sum_congr rfl
  intro J _
  change v c J * ψ.coefficient ⟨J.val,J.property.1⟩ =
    v ((rayIdealClassPartitionEquiv K 1).symm ((rayIdealClassPartitionEquiv K 1) ⟨c,J⟩)).1
      ((rayIdealClassPartitionEquiv K 1).symm ((rayIdealClassPartitionEquiv K 1) ⟨c,J⟩)).2 *
        ψ.coefficient ((rayIdealClassPartitionEquiv K 1) ⟨c,J⟩)
  rw [(rayIdealClassPartitionEquiv K 1).symm_apply_apply]
  rfl

theorem classGroupHeckePolynomial_sq_norm_le
    (B : ∀ c : ClassGroup (𝓞 K), Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K), integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ) :
    ‖ψ.classGroupHeckePolynomial B v‖^2 ≤
      (Fintype.card (ClassGroup (𝓞 K)):ℝ) *
        ∑ c : ClassGroup (𝓞 K), ‖ψ.idealClassHeckePolynomial (rayClassRepresentative K 1 c)
          (rayClassRepresentative_ne_bot K 1 c) (B c) (v c)‖^2 := by
  unfold classGroupHeckePolynomial
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans
    (by simpa only [Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun c : ClassGroup (𝓞 K) => ‖ψ.idealClassHeckePolynomial
          (rayClassRepresentative K 1 c) (rayClassRepresentative_ne_bot K 1 c) (B c) (v c)‖)))

end EvenIdealRayCharacter

theorem actualHecke_conductor_sieve_of_fiber_bound
    {U X : ℝ} (hU : 1 ≤ U) (hX : 1 ≤ X)
    (T : Finset (IdealConductorModulus K))
    (hT : ∀ M ∈ T, (Ideal.absNorm M.val:ℝ) ≤ U)
    (A : ∀ M : IdealConductorModulus K, Finset (EvenIdealRayCharacter K M.val))
    (hA : ∀ M ∈ T, ∀ ψ ∈ A M, IsPrimitiveOnIdeals ψ.residue)
    (r : ℕ) (hr : ∀ M ∈ T, ∀ χ ∈ (A M).image (fun ψ => ψ.residue),
      heckeResidueMultiplicity K (A M) χ ≤ r)
    (B : ∀ c : ClassGroup (𝓞 K), Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (hB : ∀ c, ∀ J ∈ B c, (FractionalIdeal.absNorm J.val.val:ℝ) ≤ X)
    (v : ∀ c : ClassGroup (𝓞 K), integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ) :
    (∑ M ∈ T, ∑ ψ ∈ A M, ‖ψ.classGroupHeckePolynomial B v‖^2) ≤
      ((r:ℝ) * heckeConductorClassConstant K * (X+U^2)) *
        ∑ c : ClassGroup (𝓞 K), ∑ J ∈ B c, ‖v c J‖^2 := by
  let n : ℝ := Fintype.card (ClassGroup (𝓞 K))
  let C := fun c : ClassGroup (𝓞 K) => idealModuleBalancedSieveConstant K
    (rayClassRepresentative K 1 c) (rayClassRepresentative_ne_bot K 1 c)
  let E := fun (M : IdealConductorModulus K) (ψ : EvenIdealRayCharacter K M.val)
      (c : ClassGroup (𝓞 K)) =>
    ‖ψ.idealClassHeckePolynomial (rayClassRepresentative K 1 c)
      (rayClassRepresentative_ne_bot K 1 c) (B c) (v c)‖^2
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hC : ∀ c, 0 ≤ C c := fun c => (idealModuleBalancedSieveConstant_pos K _ _).le
  have hCsum (c : ClassGroup (𝓞 K)) : C c ≤ ∑ d, C d :=
    Finset.single_le_sum (fun d _ => hC d) (Finset.mem_univ c)
  have hlocal (c : ClassGroup (𝓞 K)) :
      (∑ M ∈ T, ∑ ψ ∈ A M, E M ψ c) ≤
        ((r:ℝ)*C c*(X+U^2)) * ∑ J ∈ B c, ‖v c J‖^2 :=
    actualHeckeClass_conductor_sieve_of_fiber_bound K
      (rayClassRepresentative K 1 c) (rayClassRepresentative_ne_bot K 1 c)
      hU hX T hT A hA r hr (B c) (hB c) (v c)
  have hswap : (∑ M ∈ T, ∑ ψ ∈ A M, ∑ c, E M ψ c) =
      ∑ c, ∑ M ∈ T, ∑ ψ ∈ A M, E M ψ c := by
    calc
      _ = ∑ M ∈ T, ∑ c, ∑ ψ ∈ A M, E M ψ c := by
        apply Finset.sum_congr rfl
        intro M _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  calc
    _ ≤ ∑ M ∈ T, ∑ ψ ∈ A M, n * ∑ c, E M ψ c := by
      apply Finset.sum_le_sum
      intro M _
      exact Finset.sum_le_sum fun ψ _ => ψ.classGroupHeckePolynomial_sq_norm_le B v
    _ = n * ∑ M ∈ T, ∑ ψ ∈ A M, ∑ c, E M ψ c := by simp only [Finset.mul_sum]
    _ = n * ∑ c, ∑ M ∈ T, ∑ ψ ∈ A M, E M ψ c := congrArg (n * ·) hswap
    _ ≤ n * ∑ c, ((r:ℝ)*C c*(X+U^2)) * ∑ J ∈ B c, ‖v c J‖^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => hlocal c) hn
    _ ≤ n * ∑ c, ((r:ℝ)*(∑ d, C d)*(X+U^2)) * ∑ J ∈ B c, ‖v c J‖^2 := by
      apply mul_le_mul_of_nonneg_left _ hn
      apply Finset.sum_le_sum
      intro c _
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun J _ => sq_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (hCsum c) (Nat.cast_nonneg r)
    _ = _ := by
      rw [← Finset.mul_sum]
      dsimp [n,C,heckeConductorClassConstant]
      ring

theorem actualHecke_conductor_sieve
    {U X : ℝ} (hU : 1 ≤ U) (hX : 1 ≤ X)
    (T : Finset (IdealConductorModulus K))
    (hT : ∀ M ∈ T, (Ideal.absNorm M.val:ℝ) ≤ U)
    (A : ∀ M : IdealConductorModulus K, Finset (EvenIdealRayCharacter K M.val))
    (hA : ∀ M ∈ T, ∀ ψ ∈ A M, IsPrimitiveOnIdeals ψ.residue)
    (B : ∀ c : ClassGroup (𝓞 K), Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (hB : ∀ c, ∀ J ∈ B c, (FractionalIdeal.absNorm J.val.val:ℝ) ≤ X)
    (v : ∀ c : ClassGroup (𝓞 K), integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ) :
    (∑ M ∈ T, ∑ ψ ∈ A M, ‖ψ.classGroupHeckePolynomial B v‖^2) ≤
      ((heckeConductorMultiplicityBound K T A:ℝ) * heckeConductorClassConstant K * (X+U^2)) *
        ∑ c : ClassGroup (𝓞 K), ∑ J ∈ B c, ‖v c J‖^2 :=
  actualHecke_conductor_sieve_of_fiber_bound K hU hX T hT A hA
    (heckeConductorMultiplicityBound K T A) (heckeResidueMultiplicity_le_bound K T A) B hB v

end
end ArtinMatthews.VaryingKummerAnalytic
