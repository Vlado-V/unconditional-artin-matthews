module

public import ArtinMatthews.GiantSignedTraceSum
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal


set_option backward.privateInPublic true
@[expose] public section

/-! Conditional absolute row costs multiply along the same dependent
trace, with the retained memo updated at every actual move. -/
namespace ArtinMatthews
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

universe u v w
variable {X : Type u} {M : Type w}

structure GiantSignedTraceMemoRule (M : Type w) (r : GiantSignedTraceRow.{u,v} X) where
  update : M → (x : X) → r.Move x → M
  accept : M → (x : X) → r.Move x → Prop
  cost : ℝ≥0∞

def GiantSignedTraceMemoRules (M : Type w) : List (GiantSignedTraceRow.{u,v} X) → Type (max u v w)
  | [] => PUnit
  | r :: rs => GiantSignedTraceMemoRule M r × GiantSignedTraceMemoRules M rs

def GiantSignedTraceMemoAccept :
    (rs : List (GiantSignedTraceRow.{u,v} X)) → GiantSignedTraceMemoRules M rs →
      M → (x : X) → GiantSignedTrace rs x → Prop
  | [], _, _, _, _ => True
  | r :: rs, c, m, x, ⟨a,t⟩ =>
      c.1.accept m x a ∧ GiantSignedTraceMemoAccept rs c.2 (c.1.update m x a) (r.target x a) t

def giantSignedTraceMemoCost :
    (rs : List (GiantSignedTraceRow.{u,v} X)) → GiantSignedTraceMemoRules M rs → ℝ≥0∞
  | [], _ => 1
  | _ :: rs, c => c.1.cost * giantSignedTraceMemoCost rs c.2

def GiantSignedTraceMemoAbsolute (gauge : X → ℝ≥0∞) :
    (rs : List (GiantSignedTraceRow.{u,v} X)) → GiantSignedTraceMemoRules M rs → Prop
  | [], _ => True
  | r :: rs, c =>
      (∀ m x, (∑' a : r.Move x, if c.1.accept m x a then
        ENNReal.ofReal ‖r.coefficient x a‖ * gauge (r.target x a) else 0) ≤ c.1.cost * gauge x) ∧
      GiantSignedTraceMemoAbsolute gauge rs c.2

def giantSignedTraceMemoMass (f : X → ℂ) (rs : List (GiantSignedTraceRow.{u,v} X))
    (c : GiantSignedTraceMemoRules M rs) (m : M) (x : X) : ℝ≥0∞ :=
  ∑' t : GiantSignedTrace rs x, if GiantSignedTraceMemoAccept rs c m x t then
    ENNReal.ofReal ‖giantSignedTraceWeight f rs x t‖ else 0

theorem giantSignedTraceMemoMass_le (f : X → ℂ) (gauge : X → ℝ≥0∞)
    (hf : ∀ x, ENNReal.ofReal ‖f x‖ ≤ gauge x)
    (rs : List (GiantSignedTraceRow.{u,v} X))
    (c : GiantSignedTraceMemoRules M rs) (h : GiantSignedTraceMemoAbsolute gauge rs c)
    (m : M) (x : X) :
    giantSignedTraceMemoMass f rs c m x ≤ giantSignedTraceMemoCost rs c * gauge x := by
  induction rs generalizing m x with
  | nil =>
      change (∑' _ : PUnit.{v+1}, @ite ℝ≥0∞ True (Classical.propDecidable True)
        (ENNReal.ofReal ‖f x‖) 0) ≤ 1 * gauge x
      rw [ite_eq_left trivial, tsum_fintype, Fintype.sum_unique, one_mul]
      exact hf x
  | cons r rs ih =>
      let y := r.target x
      let next := c.1.update m x
      let a (z : r.Move x) := ENNReal.ofReal ‖r.coefficient x z‖
      let b := giantSignedTraceMemoCost rs c.2
      have he :
          giantSignedTraceMemoMass f (r::rs) c m x =
            ∑' z : r.Move x, if c.1.accept m x z then
              a z * giantSignedTraceMemoMass f rs c.2 (next z) (y z) else 0 := by
        unfold giantSignedTraceMemoMass
        change (∑' z : Σ z : r.Move x, GiantSignedTrace rs (y z),
          if GiantSignedTraceMemoAccept (r::rs) c m x z then
            ENNReal.ofReal ‖giantSignedTraceWeight f (r::rs) x z‖ else 0) = _
        rw [ENNReal.tsum_sigma']
        apply tsum_congr
        intro z
        by_cases hz : c.1.accept m x z
        · rw [ite_eq_left hz, ← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro t
          change (@ite ℝ≥0∞ (c.1.accept m x z ∧ GiantSignedTraceMemoAccept rs c.2 (next z) (y z) t)
            (Classical.propDecidable _)
            (ENNReal.ofReal ‖r.coefficient x z * giantSignedTraceWeight f rs (y z) t‖) 0) =
            a z * (if GiantSignedTraceMemoAccept rs c.2 (next z) (y z) t then
              ENNReal.ofReal ‖giantSignedTraceWeight f rs (y z) t‖ else 0)
          simp only [hz, true_and, norm_mul, ENNReal.ofReal_mul (norm_nonneg (r.coefficient x z)),
            a, mul_ite, mul_zero]
        · simp only [giantSignedTraceMemoMass, GiantSignedTraceMemoAccept, hz, false_and,
            ite_false, tsum_zero]
      rw [he]
      calc
        _ ≤ ∑' z : r.Move x, if c.1.accept m x z then a z * (b * gauge (y z)) else 0 := by
          apply ENNReal.tsum_le_tsum
          intro z
          by_cases hz : c.1.accept m x z
          · simp only [hz, ite_true]
            exact mul_le_mul_right (ih c.2 h.2 (next z) (y z)) _
          · simp only [hz, ite_false, le_refl]
        _ = b * ∑' z : r.Move x, if c.1.accept m x z then a z * gauge (y z) else 0 := by
          rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro z
          by_cases hz : c.1.accept m x z
          · simp only [hz, ite_true]
            ac_rfl
          · simp only [hz, ite_false, mul_zero]
        _ ≤ b * (c.1.cost * gauge x) := mul_le_mul_right (h.1 m x) _
        _ = _ := by
          change b * (c.1.cost * gauge x) = (c.1.cost * b) * gauge x
          ac_rfl

end
end ArtinMatthews
