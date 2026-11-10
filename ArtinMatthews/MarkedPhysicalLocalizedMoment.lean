module

public import ArtinMatthews.MarkedPhysicalHilbertMatrix
public import ArtinMatthews.MarkedFinitePositionCompression
public import ArtinMatthews.MarkedPositionLocalizedMoment
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
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

/-! The literal physical matrix and its unnormalized position moments
satisfy the source localization estimate, with the actual box constant. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical ComplexOrder
noncomputable section

@[instance_reducible] def markedPhysicalMomentFintype {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) :
    Fintype (MarkedPhysicalState P M Z) := by
  classical
  exact inferInstance

@[instance_reducible] def markedPhysicalMomentDecidableEq {J : Type*}
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) :
    DecidableEq (MarkedPhysicalState P M Z) := Classical.typeDecidableEq _

attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

theorem markedPhysicalSlopeCell_subtype_card (Z : Finset (ℤ × ℤ))
    (hprim : ∀ z∈Z,IsCoprime z.1 z.2) (U H : ℝ) (hU : 0<U) (hH : 0<H)
    (hfirst : ∀ z∈Z,U≤(z.1:ℝ) ∧ (z.1:ℝ)≤16*U) (j : ℤ) :
    ((Finset.univ.filter (fun z : Z => markedPhysicalSlopeCell (H/U^2) z.1=j)).card : ℝ) ≤
      256*H+1 := by
  let T := Finset.univ.filter (fun z : Z => markedPhysicalSlopeCell (H/U^2) z.1=j)
  have he : T.image Subtype.val=Z.filter (fun z => markedPhysicalSlopeCell (H/U^2) z=j) := by
    ext z
    constructor
    · intro hz
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_filter.mpr ⟨x.2,(Finset.mem_filter.mp hx).2⟩
    · intro hz
      obtain ⟨hz,hc⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_image.mpr ⟨⟨z,hz⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩,rfl⟩
  have hc : T.card=(Z.filter (fun z => markedPhysicalSlopeCell (H/U^2) z=j)).card := by
    rw [← he,Finset.card_image_of_injective T Subtype.val_injective]
  rw [show (Finset.univ.filter (fun z : Z => markedPhysicalSlopeCell (H/U^2) z.1=j)).card=T.card from rfl,hc]
  exact markedPhysicalSlopeCell_sixteen_card Z hprim U H hU hH hfirst j

def markedPhysicalPositionMoment {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (V : J → ℝ)
    (A : Matrix (MarkedPhysicalState P M Z) (MarkedPhysicalState P M Z) ℂ) (r : ℕ) : ℝ := by
  classical
  exact ∑ z : Z, markedQuadraticForm
    ((A*Aᴴ)^r : Matrix (MarkedPhysicalState P M Z) (MarkedPhysicalState P M Z) ℂ)
    (markedPositionVector (fun s : MarkedPhysicalState P M Z => s.1.1) (markedPhysicalMass V M) z)

theorem markedPhysicalPositionMoment_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (V : J → ℝ)
    (A : Matrix (MarkedPhysicalState P M Z) (MarkedPhysicalState P M Z) ℂ) (r : ℕ) :
    0 ≤ markedPhysicalPositionMoment P M Z V A r := by
  classical
  exact Finset.sum_nonneg (fun _ _ => ((Matrix.posSemidef_self_mul_conjTranspose A).pow r).re_dotProduct_nonneg _)

theorem markedPhysicalRestrictedMatrix_localized_moment
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q K U : ℝ)
    (G : MarkedPhysicalState P (pads+1) Z → Prop)
    (hd₀ : 0<d₀) (hY : 0<Y) (hK : 0≤K) (hU : 0<U)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K)
    (hfirst : ∀ z∈Z,U≤(z.1:ℝ) ∧ (z.1:ℝ)≤16*U)
    (a : Z → ℂ) (g : MarkedPhysicalState P (pads+1) Z → ℂ)
    (M : ℝ) (hM : 0≤M) (ha : ∀ z,‖a z‖^2≤M) (k : ℕ) :
    let A := markedPhysicalRestrictedMatrix P hP V pads Z hZ ψ η d₀ Y Q q G
    let f := markedPositionLift (fun s : MarkedPhysicalState P (pads+1) Z => s.1.1)
      (markedPhysicalMass V (pads+1)) a
    ‖markedMatrixPairing A f g‖^(2*(k+1)) ≤
      (2*(⌈2*K+1⌉₊:ℝ)+1)^(k+1) * (∑ s,‖g s‖^2)^(k+1) *
        (∑ s,‖f s‖^2)^k * ((256*(d₀*Y)+1)*M) *
          markedPhysicalPositionMoment P (pads+1) Z V A (k+1) := by
  classical
  dsimp only
  let p := fun s : MarkedPhysicalState P (pads+1) Z => s.1.1
  let c := fun z : Z => markedPhysicalSlopeCell ((d₀*Y)/U^2) z.1
  exact markedPositionPairing_localized_moment
    (markedPhysicalRestrictedMatrix P hP V pads Z hZ ψ η d₀ Y Q q G) p c (⌈2*K+1⌉₊:ℤ)
    (Int.natCast_nonneg _)
    (markedPhysicalRestrictedMatrix_cell_shift P hP V pads Z hZ ψ η d₀ Y Q q K U G
      hd₀ hY hK hU hψ (fun z hz => (hfirst z hz).1))
    (markedPhysicalMass V (pads+1)) a g (256*(d₀*Y)+1) M (by positivity) hM
    (markedPhysicalSlopeCell_subtype_card Z hZ U (d₀*Y) hU (mul_pos hd₀ hY) hfirst) ha k

end
end ArtinMatthews
