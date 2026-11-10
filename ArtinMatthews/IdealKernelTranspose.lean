module

public import ArtinMatthews.IdealCharacterCellApply
public import ArtinMatthews.IdealCharacterCellActual
public import ArtinMatthews.IdealCharacterCellRows
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Exact weighted transpose identities retain the original test
orientation and preserve the energy bound of a Hermitian kernel. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

def idealWeightedKernelApply {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (K : Ω → Ω → ℂ) (f : Ω → ℂ) (x : Ω) : ℂ :=
  ∑ d,(μ d:ℂ)*K d x*f d

def idealWeightedKernelTranspose {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (K : Ω → Ω → ℂ) (f : Ω → ℂ) (d : Ω) : ℂ :=
  ∑ x,(μ x:ℂ)*K d x*f x

theorem idealFrameEnergy_star {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (f : Ω → ℂ) :
    idealFrameEnergy μ (fun x => star (f x))=idealFrameEnergy μ f := by
  simp only [idealFrameEnergy,norm_star]

theorem idealKernelTranspose_conjugate {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (K : Ω → Ω → ℂ)
    (hK : ∀ d x,star (K d x)=K x d) (f : Ω → ℂ) (d : Ω) :
    idealWeightedKernelTranspose μ K f d=
      star (idealWeightedKernelApply μ K (fun x => star (f x)) d) := by
  unfold idealWeightedKernelTranspose idealWeightedKernelApply
  rw [star_sum]
  apply sum_congr rfl
  intro x _
  have hm : star (μ x:ℂ)=(μ x:ℂ) := Complex.conj_ofReal (μ x)
  rw [star_mul,star_mul,star_star,hK,hm]
  ring

theorem idealKernelTranspose_pairing {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (K : Ω → Ω → ℂ) (f g : Ω → ℂ) :
    (∑ d,(μ d:ℂ)*f d*idealWeightedKernelTranspose μ K g d)=
      ∑ x,(μ x:ℂ)*idealWeightedKernelApply μ K f x*g x := by
  unfold idealWeightedKernelTranspose idealWeightedKernelApply
  simp only [mul_sum,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro d _
  ring

theorem idealKernelTranspose_energy {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (K : Ω → Ω → ℂ)
    (hK : ∀ d x,star (K d x)=K x d) {B : ℝ}
    (hB : ∀ f : Ω → ℂ,idealFrameEnergy μ (idealWeightedKernelApply μ K f) ≤ B*idealFrameEnergy μ f)
    (f : Ω → ℂ) :
    idealFrameEnergy μ (idealWeightedKernelTranspose μ K f) ≤ B*idealFrameEnergy μ f := by
  have he : idealFrameEnergy μ (idealWeightedKernelTranspose μ K f)=
      idealFrameEnergy μ (idealWeightedKernelApply μ K (fun x => star (f x))) := by
    unfold idealFrameEnergy
    apply sum_congr rfl
    intro d _
    rw [idealKernelTranspose_conjugate μ K hK,norm_star]
  rw [he]
  simpa only [idealFrameEnergy_star] using hB (fun x => star (f x))

def idealCharacterCellTranspose {I : Type*} [Fintype I] [DecidableEq I]
    (P : I → Finset ℕ) (Q : ℕ) (h ξ : ℝ) (f : IdealSelectedLabels P → ℂ) :
    IdealSelectedLabels P → ℂ :=
  idealWeightedKernelTranspose (idealSelectedMass P) (idealCharacterCellKernel P Q h ξ) f

theorem idealCharacterCellTranspose_eq {I : Type*} [Fintype I] [DecidableEq I]
    (P : I → Finset ℕ) (Q : ℕ) (h ξ : ℝ)
    (f : IdealSelectedLabels P → ℂ) (d : IdealSelectedLabels P) :
    idealCharacterCellTranspose P Q h ξ f d=
      star (idealCharacterCellApply P Q h ξ (fun x => star (f x)) d) :=
  idealKernelTranspose_conjugate (idealSelectedMass P) (idealCharacterCellKernel P Q h ξ)
    (idealCharacterCellKernel_star P Q h ξ) f d

theorem idealCharacterCellTranspose_energy {I : Type*} [Fintype I] [DecidableEq I]
    (P : I → Finset ℕ) (Q : ℕ) (h ξ : ℝ) {B : ℝ}
    (hB : ∀ f : IdealSelectedLabels P → ℂ,
      idealFrameEnergy (idealSelectedMass P) (idealCharacterCellApply P Q h ξ f) ≤
        B*idealFrameEnergy (idealSelectedMass P) f)
    (f : IdealSelectedLabels P → ℂ) :
    idealFrameEnergy (idealSelectedMass P) (idealCharacterCellTranspose P Q h ξ f) ≤
      B*idealFrameEnergy (idealSelectedMass P) f :=
  idealKernelTranspose_energy (idealSelectedMass P) (idealCharacterCellKernel P Q h ξ)
    (idealCharacterCellKernel_star P Q h ξ) hB f

theorem idealCharacterCellTranspose_actual {I : Type*} [Fintype I] [DecidableEq I]
    (a c d X v₀ : ℝ) (ha : 0 ≤ a) (hc : 0 < c) (hd : 0 ≤ d) (hX : 0 ≤ X) (hv₀ : 0 < v₀) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (Q : ℕ), (Q:ℝ) ≤ L^a →
        ∀ (P : I → Finset ℕ), (∀ i p,p∈P i → p.Prime) →
        (∀ i,0 < bandReciprocalMass (P i)) →
        (∀ i p,p∈P i → Real.exp (L^c) ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp (L^d)) →
        ∀ i : I,IdealPrimeInterval (P i) → v₀ ≤ bandReciprocalMass (P i) →
        ∀ (h : ℝ),0 < h → ∀ f : IdealSelectedLabels P → ℂ,
          idealFrameEnergy (idealSelectedMass P) (idealCharacterCellTranspose P Q h (L^(-X)) f) ≤
            4*idealFrameEnergy (idealSelectedMass P) f := by
  filter_upwards [idealCharacterCellApply_actual (I:=I) a c d X v₀ ha hc hd hX hv₀] with L hL
  intro Q hQ P hP hV hbounds i hinterval hVlo h hh f
  exact idealCharacterCellTranspose_energy P Q h (L^(-X))
    (hL Q hQ P hP hV hbounds i hinterval hVlo h hh) f

end
end ArtinMatthews
