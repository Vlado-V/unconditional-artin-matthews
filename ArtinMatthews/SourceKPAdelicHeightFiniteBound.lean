module

public import ArtinMatthews.SourceKPAdelicHighHeightFinite
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
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

/-! A bounded literal height constant gives one finite rational
superlevel set, before choosing a compact parameter neighborhood. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicRationalHeight_finite_of_bound (B : ℝ) {a : ℝ} (ha : 0 < a) :
    ∃ I : Set (SourceKPRationalBorelCoset K), I.Finite ∧
      ∀ g : GL (Fin 2) 𝔸[K], sourceKPAdelicHeightConstant K hζ g ≤ B →
      ∀ q : SourceKPAdelicProjective K hζ,
        sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g →
        ∀ c, a < sourceKPAdelicRationalHeight K hζ q c → c ∈ I := by
  let I : Set (SourceKPRationalBorelCoset K) := sourceKPRationalBorelCosetEquiv K ''
    insert none (some '' {x : K | Height.mulHeight₁ x ≤ B/a})
  have hI : I.Finite :=
    (((NumberField.finite_setOfPred_mulHeight₁_le K (B/a)).image some).insert none).image _
  refine ⟨I,hI,?_⟩
  intro g hg q hq c hc
  obtain ⟨i,rfl⟩ := (sourceKPRationalBorelCosetEquiv K).surjective c
  refine ⟨i,?_,rfl⟩
  cases i with
  | none => exact Set.mem_insert none _
  | some x =>
    apply Set.mem_insert_of_mem
    refine ⟨x,?_,rfl⟩
    rw [sourceKPAdelicRationalHeight_openCell K hζ q g hq x] at hc
    have hx : a < B*(Height.mulHeight₁ x)⁻¹^2 := hc.trans_le
      ((sourceKPAdelicHeight_translate K hζ g x).trans
        (mul_le_mul_of_nonneg_right hg (sq_nonneg _)))
    have hp := Height.mulHeight₁_pos x
    have hsq : a*(Height.mulHeight₁ x)^2 < B := by
      apply (lt_div_iff₀ (sq_pos_of_pos hp)).mp
      simpa only [div_eq_mul_inv,inv_pow] using hx
    have hlarge : Height.mulHeight₁ x ≤ (Height.mulHeight₁ x)^2 := by
      nlinarith [Height.one_le_mulHeight₁ x]
    apply (le_div_iff₀ ha).mpr
    simpa only [mul_comm] using (mul_le_mul_of_nonneg_left hlarge ha.le).trans hsq.le

end
end ArtinMatthews
