module

public import ArtinMatthews.VaryingKummerAnalyticHeckeIdealMobius
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The actual truncated ideal Möbius coefficient is bounded by the number
of squarefree divisors. This is `O_{K,epsilon}(Norm(I)^epsilon)`, uniformly
in the truncation and the eventual Hecke character. -/
namespace ArtinMatthews.VaryingKummerAnalytic.HeckeIdealMobius
open NumberField UniqueFactorizationMonoid Filter
open scoped NumberField nonZeroDivisors Classical BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem squarefree_divisor_card_le (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ((divisors K I).filter Squarefree).card ≤ 2^(primeSupport K I).card := by
  rw [squarefree_divisors_eq_image K I hI]
  exact Finset.card_image_le.trans_eq (Finset.card_powerset _)

theorem prime_support_subsets_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal (𝓞 K), I ≠ ⊥ →
      (2 : ℝ)^(primeSupport K I).card ≤ C*(Ideal.absNorm I : ℝ)^ε := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)^ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2 : ℝ)))
  let small : Finset (Ideal (𝓞 K)) :=
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) N).toFinset
  refine ⟨(2 : ℝ)^small.card,by positivity,?_⟩
  intro I hI
  let S := primeSupport K I
  let A := S ∩ small
  let B := S \ small
  have hBS : B ⊆ primeSupport K I := Finset.sdiff_subset
  have hlarge (P : Ideal (𝓞 K)) (hP : P ∈ B) : (2 : ℝ) ≤ (Ideal.absNorm P : ℝ)^ε := by
    apply hN
    have hn : P ∉ small := (Finset.mem_sdiff.mp hP).2
    have hgt : N < Ideal.absNorm P := by
      apply Nat.lt_of_not_ge
      intro hp
      exact hn (by simpa [small] using hp)
    exact hgt.le
  have hpowB : (2 : ℝ)^B.card ≤ (Ideal.absNorm (∏ P ∈ B, P) : ℝ)^ε := by
    calc
      _ = ∏ _P ∈ B, (2 : ℝ) := by simp
      _ ≤ ∏ P ∈ B, (Ideal.absNorm P : ℝ)^ε :=
        Finset.prod_le_prod₀ (fun _ _ => by positivity) hlarge
      _ = (∏ P ∈ B, (Ideal.absNorm P : ℝ))^ε :=
        Real.finsetProd_rpow B (fun P => (Ideal.absNorm P : ℝ)) (fun _ _ => by positivity) ε
      _ = _ := by simp only [map_prod,Nat.cast_prod]
  have hNI : 0 < Ideal.absNorm I := Nat.pos_iff_ne_zero.mpr
    (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))
  have hnorm : Ideal.absNorm (∏ P ∈ B, P) ≤ Ideal.absNorm I :=
    Nat.le_of_dvd hNI (map_dvd Ideal.absNorm (support_product_dvd K hI hBS))
  have hpowBI : (2 : ℝ)^B.card ≤ (Ideal.absNorm I : ℝ)^ε :=
    hpowB.trans (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnorm) hε.le)
  have hAc : A.card ≤ small.card := Finset.card_le_card Finset.inter_subset_right
  have hcard : S.card = A.card+B.card := by simp [A,B]
  change (2 : ℝ)^S.card ≤ _
  rw [hcard,pow_add]
  exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hAc) hpowBI (by positivity) (by positivity)

theorem squarefree_divisor_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal (𝓞 K), I ≠ ⊥ →
      (((divisors K I).filter Squarefree).card : ℝ) ≤ C*(Ideal.absNorm I : ℝ)^ε := by
  obtain ⟨C,hC,h⟩ := prime_support_subsets_bound K ε hε
  refine ⟨C,hC,fun I hI => ?_⟩
  have hc : (((divisors K I).filter Squarefree).card : ℝ) ≤ (2 : ℝ)^(primeSupport K I).card := by
    exact_mod_cast squarefree_divisor_card_le K I hI
  exact hc.trans (h I hI)

theorem truncated_norm_le_squarefree_divisors (D : ℝ) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ‖truncated K D I‖ ≤ (((divisors K I).filter Squarefree).card : ℝ) := by
  change I ≠ 0 at hI
  let S := (divisors K I).filter (fun J => (Ideal.absNorm J : ℝ) ≤ D)
  have he : (∑ J ∈ S, (moebius J : ℂ)) = ∑ J ∈ S.filter Squarefree, (moebius J : ℂ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro J hJ hn
    have hns : ¬ Squarefree J := by simpa [hJ] using hn
    rw [moebius_of_not_squarefree hns,Int.cast_zero]
  have hsub : S.filter Squarefree ⊆ (divisors K I).filter Squarefree := by
    intro J hJ
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hJ).1).1,
      (Finset.mem_filter.mp hJ).2⟩
  rw [truncated,ite_eq_right hI]
  change ‖∑ J ∈ S, (moebius J : ℂ)‖ ≤ _
  rw [he]
  calc
    _ ≤ ∑ J ∈ S.filter Squarefree, ‖(moebius J : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _J ∈ S.filter Squarefree, (1 : ℝ) :=
      Finset.sum_le_sum (fun J _ => norm_moebius_le_one K J)
    _ = ((S.filter Squarefree).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub

theorem truncated_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : ℝ) (I : Ideal (𝓞 K)), I ≠ ⊥ →
      ‖truncated K D I‖ ≤ C*(Ideal.absNorm I : ℝ)^ε := by
  obtain ⟨C,hC,h⟩ := squarefree_divisor_small_power K ε hε
  exact ⟨C,hC,fun D I hI => (truncated_norm_le_squarefree_divisors K D I hI).trans (h I hI)⟩

end
end ArtinMatthews.VaryingKummerAnalytic.HeckeIdealMobius
