module

public import ArtinMatthews.FixedURootPrescribedMatrix
public import ArtinMatthews.FixedURootPowerSaving
public import ArtinMatthews.FixedURootReciprocalPowerSaving
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
# The complete root-residue rectangle theorem

Both coordinate regimes have now been proved for the actual finite root set.
The modulus and all endpoint flags remain uniform; the prescribed determinant-
one matrix supplies its integer residue data automatically.
-/
namespace ArtinMatthews
open Filter
open scoped Topology

/-- Both coordinate regimes of the actual root-residue estimate. -/
theorem fixedURootBox_uniform_power_saving {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (S : ℕ) (u₀ c₀ v₀ d₀ : ℤ) (U V A B α β C D : ℝ)
        (lcU rcU lcC rcC lcV rcV : Bool),
        x^δ ≤ U → x^δ ≤ V → Squarefree S →
        (S : ℝ) ≤ Real.exp (M*(Real.log x)^(49/50 : ℝ)) →
        Int.ModEq (S : ℤ) (u₀*d₀-c₀*v₀) 1 →
        U ≤ A → A ≤ B → B ≤ 16*U →
        0 ≤ α → α ≤ β → β ≤ 1 → V ≤ C → C ≤ D → D ≤ 2*V →
        |((fixedURootBoxPoints S u₀ c₀ v₀ d₀ A B α β C D
            lcU rcU lcC rcC lcV rcV).card : ℝ) -
          ((B-A)*(β-α)*(D-C)) /
            ((riemannZeta 2).re *
              (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))| ≤
          E*U*V*x^(-δ/1000) := by
  obtain ⟨E₁,hE₁,hfirst⟩ := fixedURootBox_power_saving hδ M
  obtain ⟨E₂,hE₂,hsecond⟩ := fixedURootBox_reciprocal_power_saving hδ M
  refine ⟨E₁+E₂,add_pos hE₁ hE₂,?_⟩
  filter_upwards [hfirst,hsecond,eventually_gt_atTop (1:ℝ)] with x hx₁ hx₂ hx1
  intro S u₀ c₀ v₀ d₀ U V A B α β C D lcU rcU lcC rcC lcV rcV
    hU hV hS hSrange hdet hUA hAB hB hα hαβ hβ hVC hCD hD
  have hxpos : 0 < x := by linarith
  have hUpos : 0 < U := (Real.rpow_pos_of_pos hxpos δ).trans_le hU
  have hVpos : 0 < V := (Real.rpow_pos_of_pos hxpos δ).trans_le hV
  have hY : D-C ≤ V := by linarith
  have hdom (e : ℝ) (he : e ≤ E₁+E₂) :
      e*U*V*x^(-δ/1000) ≤ (E₁+E₂)*U*V*x^(-δ/1000) := by
    calc
      _ = e*(U*V*x^(-δ/1000)) := by ring
      _ ≤ (E₁+E₂)*(U*V*x^(-δ/1000)) := mul_le_mul_of_nonneg_right he (by positivity)
      _ = _ := by ring
  rcases le_total U V with hUV | hVU
  · exact (hx₁ S u₀ c₀ v₀ d₀ U V A B α β C D lcU rcU lcC rcC lcV rcV
      hU hUV hS hSrange hdet hUA hAB hB hα hαβ hβ hCD hY).trans
        (hdom E₁ (by linarith))
  · exact (hx₂ S u₀ c₀ v₀ d₀ U V A B α β C D lcU rcU lcC rcC lcV rcV
      hV hVU hS hSrange hdet hUA hAB hB hα hαβ hβ hVC hCD (by linarith) hY).trans
        (hdom E₂ (by linarith))

/-- The root-residue lemma, literally uniform over each prescribed
`g₀∈SL₂(ℤ/Sℤ)`, all source rectangles and both coordinate scale regimes. -/
theorem fixedURootMatrixBox_uniform_power_saving {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
        (U V A B α β C D : ℝ) (lcU rcU lcC rcC lcV rcV : Bool),
        x^δ ≤ U → x^δ ≤ V → Squarefree S →
        (S : ℝ) ≤ Real.exp (M*(Real.log x)^(49/50 : ℝ)) →
        U ≤ A → A ≤ B → B ≤ 16*U →
        0 ≤ α → α ≤ β → β ≤ 1 → V ≤ C → C ≤ D → D ≤ 2*V →
        |((fixedURootMatrixBoxPoints g₀ A B α β C D
            lcU rcU lcC rcC lcV rcV).card : ℝ) -
          ((B-A)*(β-α)*(D-C)) /
            ((riemannZeta 2).re *
              (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))| ≤
          E*U*V*x^(-δ/1000) := by
  obtain ⟨E,hE,hcount⟩ := fixedURootBox_uniform_power_saving hδ M
  refine ⟨E,hE,?_⟩
  filter_upwards [hcount] with x hx
  intro S g₀ U V A B α β C D lcU rcU lcC rcC lcV rcV
    hU hV hS hSrange hUA hAB hB hα hαβ hβ hVC hCD hD
  let : NeZero S := ⟨hS.ne_zero⟩
  exact hx S (fixedURootMatrixEntry g₀ 0 0) (fixedURootMatrixEntry g₀ 0 1)
    (fixedURootMatrixEntry g₀ 1 0) (fixedURootMatrixEntry g₀ 1 1)
    U V A B α β C D lcU rcU lcC rcC lcV rcV hU hV hS hSrange
    (fixedURootMatrixEntry_det g₀) hUA hAB hB hα hαβ hβ hVC hCD hD

end ArtinMatthews
