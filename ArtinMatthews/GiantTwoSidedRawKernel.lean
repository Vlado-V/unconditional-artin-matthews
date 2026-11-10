module

public import ArtinMatthews.GiantTwoSidedRawEdgeCoordinates
public import ArtinMatthews.MarkedPhysicalPadCollisionMass
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import ArtinMatthews.GiantCharacterGraph
public import ArtinMatthews.GiantTwoSidedRawEdgeEquiv
public import ArtinMatthews.GiantTwoSidedSharedLists
public import ArtinMatthews.MarkedPhysicalEndpointArithmetic
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


set_option backward.privateInPublic true
@[expose] public section

/-! Raw physical coefficients use both original half-dampings at each
endpoint. The shared-product change of variables removes the shared
character phase and turns its reciprocal into the actual harmonic law. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable

def giantTwoSidedRawPhysicalTerm {J : Type*} [Fintype J] {P : J → Finset ℕ}
    {k m : ℕ} {Z Z' : Finset ℕ} (x q : ℝ) (Ψ : ℝ → ℂ)
    (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ) (e : GiantTwoSidedRawPhysicalEdge P k Z Z') : ℂ :=
  let s := e.1.1
  let t := e.1.2
  let n := s.1.1.val
  let n' := t.1.1.val
  let D := markedPhysicalMarkingProduct (markedPhysicalMarkingSplit k s.1.2).1
  let V (j : J) := bandReciprocalMass (P j)
  let B := ∏ j,(V j)⁻¹
  (markedPhysicalMass V (k+1)*B:ℝ) *
    (Ψ ((n:ℝ)/(x*(D:ℝ)))/(n:ℂ)) *
    F n * (conj (χ (n'-n:ℕ))*χ n') * G n' *
    ((giantTwoSidedEndpointDamping P (k+1) q n)^2:ℝ) *
    ((giantTwoSidedEndpointDamping P (k+1) q n')^2:ℝ)

def giantTwoSidedRawSharedTerm {J : Type*} [Fintype J] {P : J → Finset ℕ}
    {k m N : ℕ} {Z Z' : Finset ℕ} (x q : ℝ) (Ψ : ℝ → ℂ)
    (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ) (a : GiantTwoSidedRawSharedEdge P k N Z Z') : ℂ :=
  let c := a.1.1
  let w := a.1.2.1.val
  let D := markedPhysicalMarkingProduct c
  let B := ∏ j,(bandReciprocalMass (P j))⁻¹
  (markedPhysicalPadHarmonicMass P k c*B^2:ℝ) *
    (Ψ ((w:ℝ)/x)/(w:ℂ)) *
    F w * χ (w+1:ℕ) * G (w+1) *
    ((giantTwoSidedEndpointDamping P (k+1) q (D*w))^2:ℝ) *
    ((giantTwoSidedEndpointDamping P (k+1) q (D*(w+1)))^2:ℝ)

theorem giantTwoSidedRawPhysicalTerm_eq_shared {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime) {k m N : ℕ}
    {Z Z' : Finset ℕ} {x : ℝ} (hx : 0 < x) (q : ℝ) (Ψ : ℝ → ℂ)
    (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ) (a : GiantTwoSidedRawSharedEdge P k N Z Z')
    (hF : F (markedPhysicalMarkingProduct a.1.1*a.1.2.1.val)=F a.1.2.1.val)
    (hG : G (markedPhysicalMarkingProduct a.1.1*(a.1.2.1.val+1))=G (a.1.2.1.val+1))
    (hc : (markedPhysicalMarkingProduct a.1.1).Coprime m) :
    giantTwoSidedRawPhysicalTerm x q Ψ χ F G (giantTwoSidedRawShared_to_physical a) =
      giantTwoSidedRawSharedTerm x q Ψ χ F G a := by
  let c := a.1.1
  let w := a.1.2.1.val
  let D := markedPhysicalMarkingProduct c
  let V (j : J) := bandReciprocalMass (P j)
  let B := ∏ j,(V j)⁻¹
  let μ := markedPhysicalPadHarmonicMass P k c
  let σ := markedPhysicalMass V (k+1)
  have hD : (D:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (markedPhysicalMarkingProduct_pos hP c).ne'
  have harg : ((D*w:ℕ):ℝ)/(x*(D:ℝ)) = (w:ℝ)/x := by
    push_cast
    field_simp [hD,hx.ne']
  have hd : D*(w+1)-D*w = D := by rw [Nat.mul_add,Nat.mul_one,Nat.add_sub_cancel_left]
  have hχ : conj (χ D)*χ (D*(w+1):ℕ) = χ (w+1:ℕ) := by
    simpa only [mul_one,Nat.cast_one,map_one,one_mul,Nat.cast_mul] using
      giant_character_shared_factor χ D 1 (w+1) hc
  have hmass : (((σ*B:ℝ):ℂ)/(D:ℂ)) = ((μ*B^2:ℝ):ℂ) := by
    rw [← Complex.ofReal_natCast,← Complex.ofReal_div]
    exact congrArg (fun y : ℝ => (y:ℂ)) (giantTwoSidedShared_mass_factor P k c)
  have hscale :
      ((σ*B:ℝ):ℂ)*(Ψ ((w:ℝ)/x)/((D*w:ℕ):ℂ)) = ((μ*B^2:ℝ):ℂ)*(Ψ ((w:ℝ)/x)/(w:ℂ)) := by
    calc
      _ = (((σ*B:ℝ):ℂ)/(D:ℂ))*(Ψ ((w:ℝ)/x)/(w:ℂ)) := by
        rw [Nat.cast_mul,div_mul_eq_div_div]
        ring
      _ = _ := by rw [hmass]
  simp only [giantTwoSidedRawPhysicalTerm,giantTwoSidedRawSharedTerm,
    giantTwoSidedRawShared_to_physical,Equiv.apply_symm_apply]
  change ((σ*B:ℝ):ℂ)*(Ψ (((D*w:ℕ):ℝ)/(x*(D:ℝ)))/((D*w:ℕ):ℂ)) *
    F (D*w) * (conj (χ (D*(w+1)-D*w:ℕ))*χ (D*(w+1):ℕ)) * G (D*(w+1)) *
      ((giantTwoSidedEndpointDamping P (k+1) q (D*w))^2:ℝ) *
      ((giantTwoSidedEndpointDamping P (k+1) q (D*(w+1)))^2:ℝ) =
    ((μ*B^2:ℝ):ℂ)*(Ψ ((w:ℝ)/x)/(w:ℂ))*F w*χ (w+1:ℕ)*G (w+1) *
      ((giantTwoSidedEndpointDamping P (k+1) q (D*w))^2:ℝ) *
      ((giantTwoSidedEndpointDamping P (k+1) q (D*(w+1)))^2:ℝ)
  change F (D*w)=F w at hF
  change G (D*(w+1))=G (w+1) at hG
  rw [harg,hd,hF,hG,hχ,hscale]

theorem giantTwoSidedRawPhysical_sum_eq_shared {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) {k m N : ℕ}
    {Z Z' : Finset ℕ} (hZ : Z ⊆ Ioc 0 N) {x : ℝ} (hx : 0 < x) (q : ℝ) (Ψ : ℝ → ℂ)
    (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ)
    (hF : ∀ c : MarkedPhysicalMarking P k,∀ w : ℕ,0 < w → F (markedPhysicalMarkingProduct c*w)=F w)
    (hG : ∀ c : MarkedPhysicalMarking P k,∀ w : ℕ,0 < w → G (markedPhysicalMarkingProduct c*w)=G w)
    (hc : ∀ c : MarkedPhysicalMarking P k,(markedPhysicalMarkingProduct c).Coprime m) :
    (∑ e : GiantTwoSidedRawPhysicalEdge P k Z Z',giantTwoSidedRawPhysicalTerm x q Ψ χ F G e) =
      ∑ a : GiantTwoSidedRawSharedEdge P k N Z Z',giantTwoSidedRawSharedTerm x q Ψ χ F G a := by
  classical
  rw [← (giantTwoSidedRawSharedEquiv hP hdis (Z':=Z') hZ).symm.sum_comp
    (giantTwoSidedRawPhysicalTerm x q Ψ χ F G)]
  apply sum_congr rfl
  intro a _
  exact giantTwoSidedRawPhysicalTerm_eq_shared hP hx q Ψ χ F G a
    (hF a.1.1 _ (mem_Ioc.mp a.1.2.1.property).1)
    (hG a.1.1 _ (Nat.succ_pos _)) (hc a.1.1)

end
end ArtinMatthews
