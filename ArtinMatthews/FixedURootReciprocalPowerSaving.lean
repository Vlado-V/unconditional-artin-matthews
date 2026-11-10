module

public import ArtinMatthews.FixedURootBoxes
public import ArtinMatthews.FixedURootMassShift
public import ArtinMatthews.FixedURootPowerSaving
public import ArtinMatthews.FixedURootPowerScale
public import ArtinMatthews.FixedURootReciprocalBoxes
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

/-! The reciprocal coordinate regime of the actual root-residue estimate. -/
namespace ArtinMatthews

open Filter
open scoped Topology

/-- The actual `V≤U` count follows from the proved smaller-first-coordinate
estimate by the literal reciprocal involution and its finite count sandwich.
The first-coordinate interval may have the full source width `15U`. -/
theorem fixedURootBox_reciprocal_power_saving {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (S : ℕ) (u₀ c₀ v₀ d₀ : ℤ) (U V A B α β C D : ℝ)
        (lcU rcU lcC rcC lcV rcV : Bool),
        x^δ ≤ V → V ≤ U → Squarefree S →
        (S : ℝ) ≤ Real.exp (M*(Real.log x)^(49/50 : ℝ)) →
        Int.ModEq (S : ℤ) (u₀*d₀-c₀*v₀) 1 →
        U ≤ A → A ≤ B → B ≤ 16*U →
        0 ≤ α → α ≤ β → β ≤ 1 →
        V ≤ C → C ≤ D → D ≤ 16*V → D-C ≤ V →
        |((fixedURootBoxPoints S u₀ c₀ v₀ d₀ A B α β C D
            lcU rcU lcC rcC lcV rcV).card : ℝ) -
          ((B-A)*(β-α)*(D-C)) /
            ((riemannZeta 2).re *
              (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))| ≤
          E*U*V*x^(-δ/1000) := by
  obtain ⟨E,hE,hbound⟩ := fixedURootBox_power_saving hδ M
  refine ⟨16*E+16,by positivity,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (1 : ℝ)] with x hx hx1
  intro S u₀ c₀ v₀ d₀ U V A B α β C D lcU rcU lcC rcC lcV rcV
    hV hVU hS hSrange hdet hUA hAB hB hα hαβ hβ hVC hCD hD hYV
  have hV1 : 1 < V := (Real.one_lt_rpow hx1 hδ).trans_le hV
  have hUpos : 0 < U := (by linarith : 0 < V).trans_le hVU
  have hA1 : 1 < A := hV1.trans_le (hVU.trans hUA)
  have hC1 : 1 < C := hV1.trans_le hVC
  have hApos : 0 < A := by linarith
  have hCpos : 0 < C := by linarith
  let ε : ℝ := 1/(A*C)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  let wi := fixedURootReciprocalInnerWidth α β ε
  let wo := fixedURootReciprocalOuterWidth α β ε
  let w := β-α
  let area := (B-A)*(D-C)
  let q := (riemannZeta 2).re *
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)
  obtain ⟨_hwi0,hwiw,hwwo,_hwo1,hwiε,hwoε⟩ :=
    fixedURoot_reciprocal_width_bounds hα hαβ hβ hε
  have hdet' := fixedURootReciprocal_residue_det hdet
  have hγo : max 0 (1-β-ε) ≤ 1-α := max_le (by linarith) (by linarith)
  have hηi : max (1-β) (1-α-ε) ≤ 1 := max_le (by linarith) (by linarith)
  have hwidth : B-A ≤ 16*U := by linarith
  have ho := hx S v₀ (v₀-d₀) u₀ (u₀-c₀) V (16*U)
    C D (max 0 (1-β-ε)) (1-α) A B lcV rcV true true lcU rcU
    hV (by linarith) hS hSrange hdet' hVC hCD hD (le_max_left _ _)
    hγo (by linarith) hAB hwidth
  have hi := hx S v₀ (v₀-d₀) u₀ (u₀-c₀) V (16*U)
    C D (1-β) (max (1-β) (1-α-ε)) A B lcV rcV false false lcU rcU
    hV (by linarith) hS hSrange hdet' hVC hCD hD (by linarith)
    (le_max_left _ _) hηi hAB hwidth
  have hmo : ((D-C)*((1-α)-max 0 (1-β-ε))*(B-A))/q = area*wo/q := by
    dsimp [area,wo,fixedURootReciprocalOuterWidth]
    ring
  have hmi : ((D-C)*(max (1-β) (1-α-ε)-(1-β))*(B-A))/q = area*wi/q := by
    dsimp [area,wi,fixedURootReciprocalInnerWidth]
    ring
  have herr : E*V*(16*U)*x^(-δ/1000) = 16*E*U*V*x^(-δ/1000) := by ring
  change |((fixedURootBoxPoints S v₀ (v₀-d₀) u₀ (u₀-c₀)
      C D (max 0 (1-β-ε)) (1-α) A B lcV rcV true true lcU rcU).card : ℝ) -
    ((D-C)*((1-α)-max 0 (1-β-ε))*(B-A))/q| ≤ E*V*(16*U)*x^(-δ/1000) at ho
  change |((fixedURootBoxPoints S v₀ (v₀-d₀) u₀ (u₀-c₀)
      C D (1-β) (max (1-β) (1-α-ε)) A B lcV rcV false false lcU rcU).card : ℝ) -
    ((D-C)*(max (1-β) (1-α-ε)-(1-β))*(B-A))/q| ≤ E*V*(16*U)*x^(-δ/1000) at hi
  rw [hmo,herr] at ho
  rw [hmi,herr] at hi
  have hB16A : B ≤ 16*A := by linarith
  have hYC : D-C ≤ C := hYV.trans hVC
  have hwo : |wo-w| ≤ 1/(A*C) := by
    rw [abs_of_nonneg (sub_nonneg.mpr hwwo)]
    exact hwoε
  have hwi : |wi-w| ≤ 1/(A*C) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hwiw)]
    change -(wi-w) ≤ ε
    linarith
  have hmassO := fixedURoot_reciprocal_mass_shift_le hS hApos hCpos hAB hB16A hCD hYC hwo
  have hmassI := fixedURoot_reciprocal_mass_shift_le hS hApos hCpos hAB hB16A hCD hYC hwi
  change |area*wo/q-area*w/q| ≤ 16 at hmassO
  change |area*wi/q-area*w/q| ≤ 16 at hmassI
  obtain ⟨hsI,hsO⟩ := fixedURootReciprocal_card_sandwich
    (S := S) (u₀ := u₀) (c₀ := c₀) (v₀ := v₀) (d₀ := d₀)
    (B := B) (D := D) (lcU := lcU) (rcU := rcU) (lcC := lcC) (rcC := rcC)
    (lcV := lcV) (rcV := rcV) hA1 hC1 hα hαβ hβ
  have hsIR : ((fixedURootBoxPoints S v₀ (v₀-d₀) u₀ (u₀-c₀)
      C D (1-β) (max (1-β) (1-α-ε)) A B lcV rcV false false lcU rcU).card : ℝ) ≤
      ((fixedURootBoxPoints S u₀ c₀ v₀ d₀ A B α β C D lcU rcU lcC rcC lcV rcV).card : ℝ) := by
    exact_mod_cast hsI
  have hsOR : ((fixedURootBoxPoints S u₀ c₀ v₀ d₀ A B α β C D lcU rcU lcC rcC lcV rcV).card : ℝ) ≤
      ((fixedURootBoxPoints S v₀ (v₀-d₀) u₀ (u₀-c₀)
        C D (max 0 (1-β-ε)) (1-α) A B lcV rcV true true lcU rcU).card : ℝ) := by
    exact_mod_cast hsO
  have htotal : |((fixedURootBoxPoints S u₀ c₀ v₀ d₀ A B α β C D
      lcU rcU lcC rcC lcV rcV).card : ℝ)-area*w/q| ≤ 16*E*U*V*x^(-δ/1000)+16 := by
    obtain ⟨hiL,_hiR⟩ := abs_le.mp hi
    obtain ⟨_hoL,hoR⟩ := abs_le.mp ho
    obtain ⟨hmiL,_hmiR⟩ := abs_le.mp hmassI
    obtain ⟨_hmoL,hmoR⟩ := abs_le.mp hmassO
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hmain : ((B-A)*(β-α)*(D-C))/q = area*w/q := by dsimp [area,w]; ring
  change |((fixedURootBoxPoints S u₀ c₀ v₀ d₀ A B α β C D
      lcU rcU lcC rcC lcV rcV).card : ℝ)-((B-A)*(β-α)*(D-C))/q| ≤ _
  rw [hmain]
  refine htotal.trans ?_
  have hscale := fixedURoot_reciprocal_error_scale_one_le hδ hx1 hV hVU
  nlinarith

end ArtinMatthews
