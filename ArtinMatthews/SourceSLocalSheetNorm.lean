module

public import ArtinMatthews.SLocalNormOneGroup
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Split off the chosen infinite place in the literal S-local product
and solve its normalized complex norm from the other coordinates. -/

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)

abbrev SNormOneOtherUnits :=
  (∀ w : {w : InfinitePlace K // w ≠ v}, w.val.Completionˣ) ×
    (∀ p : S, (p.val.adicCompletion K)ˣ)

/-- Delete the chosen infinite coordinate. The finite coordinates are unchanged. -/
def sourceSheetOther (x : SWholeUnits K S) : SNormOneOtherUnits S v :=
  (fun w => x.1 w.val, x.2)

theorem sourceSheetOther_mul (x y : SWholeUnits K S) :
    sourceSheetOther S v (x*y) = sourceSheetOther S v x * sourceSheetOther S v y := rfl

/-- Fill the chosen coordinate in the actual dependent product. -/
def sourceSheetFill (u : v.Completionˣ) (y : SNormOneOtherUnits S v) : SWholeUnits K S :=
  (fun w => if h : w = v then
    cast (congrArg (fun p : InfinitePlace K => p.Completionˣ) h.symm) u
    else y.1 ⟨w,h⟩, y.2)

@[simp] theorem sourceSheetFill_chosen (u : v.Completionˣ) (y : SNormOneOtherUnits S v) :
    (sourceSheetFill S v u y).1 v = u := by
  simp [sourceSheetFill]

@[simp] theorem sourceSheetFill_other (u : v.Completionˣ) (y : SNormOneOtherUnits S v)
    (w : {w : InfinitePlace K // w ≠ v}) :
    (sourceSheetFill S v u y).1 w.val = y.1 w := by
  simp [sourceSheetFill, w.property]

@[simp] theorem sourceSheetFill_finite (u : v.Completionˣ) (y : SNormOneOtherUnits S v) :
    (sourceSheetFill S v u y).2 = y.2 := rfl

@[simp] theorem sourceSheetOther_fill (u : v.Completionˣ) (y : SNormOneOtherUnits S v) :
    sourceSheetOther S v (sourceSheetFill S v u y) = y := by
  apply Prod.ext
  · funext w
    exact sourceSheetFill_other S v u y w
  · rfl

theorem sourceSheetFill_reconstruct (x : SWholeUnits K S) :
    sourceSheetFill S v (x.1 v) (sourceSheetOther S v x) = x := by
  apply Prod.ext
  · funext w
    by_cases hw : w = v
    · subst w
      exact sourceSheetFill_chosen S v _ _
    · exact sourceSheetFill_other S v _ _ ⟨w,hw⟩
  · rfl

/-- The precise normalized product over all coordinates except the chosen place. -/
def sourceSheetOtherNorm (y : SNormOneOtherUnits S v) : ℝ :=
  (∏ w : {w : InfinitePlace K // w ≠ v}, ‖(y.1 w : w.val.Completion)‖ ^ w.val.mult) *
    ∏ p : S, ‖(y.2 p : p.val.adicCompletion K)‖

theorem sourceSheetOtherNorm_pos (y : SNormOneOtherUnits S v) :
    0 < sourceSheetOtherNorm S v y :=
  mul_pos (Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.mpr (y.1 w).ne_zero) _)
    (Finset.prod_pos fun p _ => norm_pos_iff.mpr (y.2 p).ne_zero)

theorem sourceSheetWholeNorm_split (x : SWholeUnits K S) :
    sLocalNorm K S x = ‖(x.1 v : v.Completion)‖ ^ v.mult *
      sourceSheetOtherNorm S v (sourceSheetOther S v x) := by
  rw [sLocalNorm_eq_prod]
  let F (w : InfinitePlace K) := ‖(x.1 w : w.Completion)‖ ^ w.mult
  have h : (∏ w ∈ Finset.univ.erase v,F w) =
      ∏ w : {w : InfinitePlace K // w ≠ v},F w.val :=
    Finset.prod_subtype (Finset.univ.erase v) (fun w => by simp) F
  change (∏ w,F w) * (∏ p : S, ‖(x.2 p : p.val.adicCompletion K)‖) =
    F v * ((∏ w : {w : InfinitePlace K // w ≠ v},F w.val) *
      (∏ p : S, ‖(x.2 p : p.val.adicCompletion K)‖))
  rw [← h, ← mul_assoc, Finset.mul_prod_erase Finset.univ F (Finset.mem_univ v)]

theorem sourceSheetNormOne_chosen_sq (hv : IsComplex v) (x : SNormOne K S) :
    ‖(x.val.1 v : v.Completion)‖ ^ 2 =
      (sourceSheetOtherNorm S v (sourceSheetOther S v x.val))⁻¹ := by
  have hx : sLocalNorm K S x.val = 1 := x.property
  rw [sourceSheetWholeNorm_split S v, hv.mult_eq_two] at hx
  let M := sourceSheetOtherNorm S v (sourceSheetOther S v x.val)
  have hM : M ≠ 0 := (sourceSheetOtherNorm_pos S v _).ne'
  calc
    _ = ‖(x.val.1 v : v.Completion)‖ ^ 2 * (M*M⁻¹) := by rw [mul_inv_cancel₀ hM, mul_one]
    _ = M⁻¹ := by rw [← mul_assoc, hx, one_mul]

/-- The positive modulus forced at the chosen complex place. -/
def sourceSheetRadius (y : SNormOneOtherUnits S v) : ℝ :=
  Real.sqrt (sourceSheetOtherNorm S v y)⁻¹

theorem sourceSheetRadius_pos (y : SNormOneOtherUnits S v) :
    0 < sourceSheetRadius S v y :=
  Real.sqrt_pos.mpr (inv_pos.mpr (sourceSheetOtherNorm_pos S v y))

@[simp] theorem sourceSheetRadius_sq (y : SNormOneOtherUnits S v) :
    sourceSheetRadius S v y ^ 2 = (sourceSheetOtherNorm S v y)⁻¹ :=
  Real.sq_sqrt (inv_nonneg.mpr (sourceSheetOtherNorm_pos S v y).le)

theorem sourceSheetRadius_normOne (hv : IsComplex v) (x : SNormOne K S) :
    sourceSheetRadius S v (sourceSheetOther S v x.val) = ‖(x.val.1 v : v.Completion)‖ := by
  rw [sourceSheetRadius, ← sourceSheetNormOne_chosen_sq S v hv x, Real.sqrt_sq (norm_nonneg _)]

end
end ArtinMatthews.SourcePhysical
