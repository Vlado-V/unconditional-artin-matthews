module

public import ArtinMatthews.FixedURootFirstColumns
public import ArtinMatthews.FixedURootFullPowerSaving
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

/-!
# Uniform root residues

The primitive first-column count in PD (det:root-residue-count), for both
coordinate regimes and every prescribed special-linear residue. The explicit
saving is δ/1000. All interval endpoint choices are retained uniformly.
-/
namespace ArtinMatthews
open Filter
open scoped Topology

/-- Uniform residues of actual primitive roots, with their canonical
completions, at every squarefree subpower modulus. -/
theorem fixedURoot_residue_count {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
        (U V A B α β C D : ℝ) (lcU rcU lcC rcC lcV rcV : Bool),
        x^δ ≤ U → x^δ ≤ V → Squarefree S →
        (S : ℝ) ≤ Real.exp (M*(Real.log x)^(49/50 : ℝ)) →
        U ≤ A → A ≤ B → B ≤ 16*U →
        0 ≤ α → α ≤ β → β ≤ 1 → V ≤ C → C ≤ D → D ≤ 2*V →
        |((fixedURootMatrixFirstColumns g₀ A B α β C D
            lcU rcU lcC rcC lcV rcV).card : ℝ) -
          ((B-A)*(β-α)*(D-C)) /
            ((riemannZeta 2).re *
              (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))| ≤
          E*U*V*x^(-δ/1000) := by
  obtain ⟨E,hE,hcount⟩ := fixedURootMatrixBox_uniform_power_saving hδ M
  refine ⟨E,hE,?_⟩
  filter_upwards [hcount,eventually_gt_atTop (1:ℝ)] with x hx hx1
  intro S g₀ U V A B α β C D lcU rcU lcC rcC lcV rcV
    hU hV hS hSrange hUA hAB hB hα hαβ hβ hVC hCD hD
  have hA : 1 < A := ((Real.one_lt_rpow hx1 hδ).trans_le hU).trans_le hUA
  have hC : 1 < C := ((Real.one_lt_rpow hx1 hδ).trans_le hV).trans_le hVC
  rw [fixedURootMatrixFirstColumns_card g₀ hA hC hα hβ]
  exact hx S g₀ U V A B α β C D lcU rcU lcC rcC lcV rcV
    hU hV hS hSrange hUA hAB hB hα hαβ hβ hVC hCD hD

end ArtinMatthews
