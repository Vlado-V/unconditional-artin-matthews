module

public import ArtinMatthews.MarkedPhysicalMomentTube
public import ArtinMatthews.MarkedPhysicalPathCoordinateTerm
public import ArtinMatthews.MarkedFiniteCoordinateSums
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

/-! The root-dependent image of the physical box can be replaced by the
fixed finite tube for the genuine original even-moment weight. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
  (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)

theorem markedPhysicalMomentCoordinateTerm_ne_zero_tube
    (G : MarkedPhysicalState P (pads+1) Z → Prop) (R : ℕ)
    (a : MarkedPhysicalLabelPath P (pads+1) (2*R))
    (K : ℝ) (hd₀ : 0<d₀) (hY : 0<Y) (hK : 0≤K)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K)
    {S : ℕ} [NeZero S] {U W : ℝ} (hU : 1<U) (hW : 1<W)
    (hbox : Z⊆markedPhysicalPrimitiveBox U (16*U) W (2*W))
    (r : MarkedPhysicalCanonicalRoot S U (16*U) W (2*W)) (tail : Fin (2*R) → ℤ × ℤ)
    (h : markedPhysicalPathCoordinateTerm
      (markedPhysicalMomentPathTerm P hP V pads Z hZ ψ η d₀ Y Q q G R) a r tail≠0)
    (v : Fin (2*R)) :
    tail v∈markedPrimitiveCoordinateTube (markedPhysicalMomentTubeRadius (2*R) K (d₀*Y)) := by
  unfold markedPhysicalPathCoordinateTerm markedPhysicalPositionPathExtend at h
  split_ifs at h with hp
  · let pos : MarkedPhysicalPositionPath Z (2*R) := fun k => ⟨_,hp k⟩
    change markedPhysicalPathArrayExtend
      (markedPhysicalMomentPathTerm P hP V pads Z hZ ψ η d₀ Y Q q G R) pos a≠0 at h
    unfold markedPhysicalPathArrayExtend at h
    split_ifs at h with ha
    · let p := markedPhysicalPathOfArrays pos a ha
      have hn : markedPhysicalMomentPathTerm P hP V pads Z hZ ψ η d₀ Y Q q G R p≠0 := h
      have ht := markedPhysicalMomentPathTerm_coordinate_tube P hP V pads Z hZ ψ η d₀ Y Q q
        G R p hn K hd₀ hY hK hψ hU hW hbox r rfl v.succ
      change markedPhysicalRootCoordinates (markedPhysicalCanonicalRootPosition r)
        (markedPhysicalCanonicalCompletion r)
        (markedPhysicalRootLift (markedPhysicalCanonicalRootPosition r)
          (markedPhysicalCanonicalCompletion r) (tail v))∈_ at ht
      rw [markedPhysicalRootCoordinates_lift _ _ _ (markedPhysicalCanonicalCompletion_det hU hW r)] at ht
      exact ht
    · exact False.elim (h rfl)
  · exact False.elim (h rfl)

theorem markedPhysicalMomentCoordinateTube_sum
    (G : MarkedPhysicalState P (pads+1) Z → Prop) (R : ℕ)
    (a : MarkedPhysicalLabelPath P (pads+1) (2*R))
    (K : ℝ) (hd₀ : 0<d₀) (hY : 0<Y) (hK : 0≤K)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K)
    {S : ℕ} [NeZero S] {U W : ℝ} (hU : 1<U) (hW : 1<W)
    (hbox : Z⊆markedPhysicalPrimitiveBox U (16*U) W (2*W))
    (r : MarkedPhysicalCanonicalRoot S U (16*U) W (2*W)) :
    (∑ tail : Fin (2*R) → ↥(markedPhysicalCanonicalTargets hU hW r Z),
      markedPhysicalPathCoordinateTerm
        (markedPhysicalMomentPathTerm P hP V pads Z hZ ψ η d₀ Y Q q G R) a r (fun v => (tail v).1)) =
    ∑ tail : Fin (2*R) → ↥(markedPrimitiveCoordinateTube (markedPhysicalMomentTubeRadius (2*R) K (d₀*Y))),
      markedPhysicalPathCoordinateTerm
        (markedPhysicalMomentPathTerm P hP V pads Z hZ ψ η d₀ Y Q q G R) a r (fun v => (tail v).1) := by
  let f : (Fin (2*R) → ℤ × ℤ) → ℂ := markedPhysicalPathCoordinateTerm
    (markedPhysicalMomentPathTerm P hP V pads Z hZ ψ η d₀ Y Q q G R) a r
  have h₁ : ∀ tail,f tail≠0 → ∀ v,tail v∈markedPhysicalCanonicalTargets hU hW r Z :=
    fun tail ht v => markedPhysicalPathCoordinateTerm_ne_zero_image_mem _ a hU hW r tail ht v
  have h₂ : ∀ tail,f tail≠0 → ∀ v,
      tail v∈markedPrimitiveCoordinateTube (markedPhysicalMomentTubeRadius (2*R) K (d₀*Y)) :=
    fun tail ht v => markedPhysicalMomentCoordinateTerm_ne_zero_tube P hP V pads Z hZ ψ η d₀ Y Q q
      G R a K hd₀ hY hK hψ hU hW hbox r tail ht v
  have he := markedFiniteCoordinateSum_eq (markedPhysicalCanonicalTargets hU hW r Z)
    (markedPrimitiveCoordinateTube (markedPhysicalMomentTubeRadius (2*R) K (d₀*Y))) f h₁ h₂
  simpa only [f] using he

end
end ArtinMatthews
