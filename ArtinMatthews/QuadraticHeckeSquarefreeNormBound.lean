module

public import ArtinMatthews.QuadraticHeckeSquarefreeNorm
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.Topology.Sheaves.Presheaf


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Set SourceEulerAssembly
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
local notation "NZ" => {J : Ideal (𝓞 F) // J ≠ ⊥}

/-- The norm of the unique squarefree part cannot exceed the full ideal norm. -/
theorem quadraticHeckeSquarefreeNorm_le_absNorm (J : NZ) :
    quadraticHeckeSquarefreeNorm F J ≤ Ideal.absNorm J.val := by
  have hnorm := congrArg (fun I : Ideal (𝓞 F) => Ideal.absNorm I)
    (sourceQuadraticIdealSquareParts_val F J)
  simp only [map_mul, map_pow] at hnorm
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr J.property))
  exact ⟨Ideal.absNorm (sourceQuadraticIdealSquareParts F J).2.val ^ 2, hnorm.symm⟩

theorem quadraticHeckeSquarefreeNorm_cast_le_absNorm (J : NZ) :
    (quadraticHeckeSquarefreeNorm F J : ℝ) ≤ (Ideal.absNorm J.val : ℝ) := by
  exact_mod_cast quadraticHeckeSquarefreeNorm_le_absNorm F J

theorem quadraticHeckeSquarefreeNorm_tail_subset (U : ℝ) :
    {J : NZ | U < (quadraticHeckeSquarefreeNorm F J : ℝ)} ⊆
      {J : NZ | U < (Ideal.absNorm J.val : ℝ)} := by
  intro J hJ
  exact hJ.trans_le (quadraticHeckeSquarefreeNorm_cast_le_absNorm F J)

/-- Every nonnegative squarefree-part tail is dominated by the full-norm tail. -/
theorem quadraticHeckeSquarefreeNorm_absolute_tail_le (f : NZ → ℝ)
    (hf : ∀ J, 0 ≤ f J) (hs : Summable f) (U : ℝ) :
    (∑' J : NZ, if U < (quadraticHeckeSquarefreeNorm F J : ℝ) then f J else 0) ≤
      ∑' J : {J : NZ // U < (Ideal.absNorm J.val : ℝ)}, f J.val := by
  have hsum : (∑' J : {J : NZ // U < (Ideal.absNorm J.val : ℝ)}, f J.val) =
      ∑' J : NZ, if U < (Ideal.absNorm J.val : ℝ) then f J else 0 := by
    simpa only [Set.coe_ofPred, Set.indicator_apply, Set.mem_ofPred_eq] using
      (tsum_subtype {J : NZ | U < (Ideal.absNorm J.val : ℝ)} f)
  rw [hsum]
  have hsmall : Summable (fun J : NZ =>
      if U < (quadraticHeckeSquarefreeNorm F J : ℝ) then f J else 0) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hs
    · intro J
      split_ifs
      · exact hf J
      · exact le_rfl
    · intro J
      split_ifs
      · exact le_rfl
      · exact hf J
  have hlarge : Summable (fun J : NZ =>
      if U < (Ideal.absNorm J.val : ℝ) then f J else 0) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hs
    · intro J
      split_ifs
      · exact hf J
      · exact le_rfl
    · intro J
      split_ifs
      · exact le_rfl
      · exact hf J
  apply hsmall.tsum_le_tsum _ hlarge
  intro J
  by_cases hJ : U < (quadraticHeckeSquarefreeNorm F J : ℝ)
  · have hnorm : U < (Ideal.absNorm J.val : ℝ) :=
      hJ.trans_le (quadraticHeckeSquarefreeNorm_cast_le_absNorm F J)
    simp only [hJ, hnorm, ite_true, le_refl]
  · simp only [hJ, ite_false]
    split_ifs <;> first | exact hf J | exact le_rfl

/-- Taking the norm of a masked complex tail preserves the same domination. -/
theorem quadraticHeckeSquarefreeNorm_tail_norm_le (f : NZ → ℂ)
    (hs : Summable (fun J => ‖f J‖)) (U : ℝ) :
    ‖∑' J : NZ, if U < (quadraticHeckeSquarefreeNorm F J : ℝ) then f J else 0‖ ≤
      ∑' J : {J : NZ // U < (Ideal.absNorm J.val : ℝ)}, ‖f J.val‖ := by
  have hmasked : Summable (fun J : NZ =>
      ‖if U < (quadraticHeckeSquarefreeNorm F J : ℝ) then f J else 0‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hs
    intro J
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg (f J)
  calc
    _ ≤ ∑' J : NZ, ‖if U < (quadraticHeckeSquarefreeNorm F J : ℝ) then f J else 0‖ :=
      norm_tsum_le_tsum_norm hmasked
    _ = ∑' J : NZ, if U < (quadraticHeckeSquarefreeNorm F J : ℝ) then ‖f J‖ else 0 := by
      apply tsum_congr
      intro J
      split_ifs <;> simp
    _ ≤ _ := quadraticHeckeSquarefreeNorm_absolute_tail_le F
      (fun J => ‖f J‖) (fun _ => norm_nonneg _) hs U

end
end ArtinMatthews
