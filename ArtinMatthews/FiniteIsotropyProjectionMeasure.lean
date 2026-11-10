module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import ArtinMatthews.FiniteIsotropyQuotientMeasure
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! A measure-preserving equivariant projection retains the exact chart multiplicity. -/
namespace ArtinMatthews
open Set MeasureTheory
open scoped ENNReal Pointwise Classical
noncomputable section

variable {Γ G X : Type*} [Group Γ] [Countable Γ]
    [MulAction Γ G] [MulAction Γ X]
    [MeasurableSpace G] [MeasurableSpace X] [MeasurableConstSMul Γ G]
    (μ : Measure G) [SMulInvariantMeasure Γ G μ]
    (ν : Measure (Quotient (MulAction.orbitRel Γ G)))
    [QuotientMeasureEqMeasurePreimage (G := Γ) μ ν]
    (ξ : Measure X) (π : G → X) (hπ : MeasurePreserving π μ ξ)
    (hπγ : ∀ (γ : Γ) (g : G), π (γ • g) = γ • π g)
    (r : Quotient (MulAction.orbitRel Γ G) → Quotient (MulAction.orbitRel Γ X))
    (hr : Measurable r)
    (hrπ : ∀ g : G, r (Quotient.mk (MulAction.orbitRel Γ G) g) =
      Quotient.mk (MulAction.orbitRel Γ X) (π g))

include hπ hπγ hr hrπ

theorem sourceFiniteSlice_projection_measure (H : Subgroup Γ) [Finite H]
    {F : Set G} (hF : IsFundamentalDomain Γ F μ)
    (U : Set X) (hU : MeasurableSet U)
    (himage : MeasurableSet (Quotient.mk (MulAction.orbitRel Γ X) '' U))
    (hstable : ∀ h : H, ∀ x ∈ U, (h : Γ) • x ∈ U)
    (hsep : ∀ γ : Γ, ∀ x ∈ U, γ • x ∈ U → γ ∈ H) :
    (ν.map r).restrict (Quotient.mk (MulAction.orbitRel Γ X) '' U) =
      (Nat.card H : ℝ≥0∞)⁻¹ •
        (ξ.restrict U).map (Quotient.mk (MulAction.orbitRel Γ X)) := by
  classical
  let qG := Quotient.mk (MulAction.orbitRel Γ G)
  let qX := Quotient.mk (MulAction.orbitRel Γ X)
  have hq : Measurable qX := measurable_quotient_mk' (s := MulAction.orbitRel Γ X)
  have hqγ (γ : Γ) (x : X) : qX (γ • x) = qX x :=
    Quotient.sound (MulAction.mem_orbit_iff.mpr ⟨γ, rfl⟩)
  apply Measure.ext
  intro A hA
  let B := qX ⁻¹' A ∩ U
  let E := π ⁻¹' B
  have hB : MeasurableSet B := (hq hA).inter hU
  have hE : MeasurableSet E := hπ.measurable hB
  have hEimage : qG '' E = r ⁻¹' (A ∩ qX '' U) := by
    ext q
    induction q using Quotient.inductionOn with
    | _ g =>
      constructor
      · rintro ⟨g', hg', heq⟩
        have he : qX (π g') = qX (π g) := by
          have he' := congrArg r heq
          change r (Quotient.mk (MulAction.orbitRel Γ G) g') =
            r (Quotient.mk (MulAction.orbitRel Γ G) g) at he'
          rw [hrπ, hrπ] at he'
          exact he' 
        change qX (π g') ∈ A ∧ π g' ∈ U at hg'
        change r (qG g) ∈ A ∩ qX '' U
        rw [hrπ]
        exact ⟨by simpa only [he] using hg'.1, ⟨π g', hg'.2, he⟩⟩
      · intro hg
        change r (qG g) ∈ A ∩ qX '' U at hg
        rw [hrπ] at hg
        obtain ⟨u, hu, he⟩ := hg.2
        obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact he)
        refine ⟨γ • g, ?_, ?_⟩
        · change qX (π (γ • g)) ∈ A ∧ π (γ • g) ∈ U
          simp only [hπγ, hqγ]
          exact ⟨hg.1, hγ.symm ▸ hu⟩
        · exact Quotient.sound (MulAction.mem_orbit_iff.mpr ⟨γ, rfl⟩)
  have hEimage_meas : MeasurableSet (qG '' E) := by
    rw [hEimage]
    exact hr (hA.inter himage)
  have hEstable : ∀ h : H, ∀ g ∈ E, (h : Γ) • g ∈ E := by
    intro h g hg
    change qX (π g) ∈ A ∧ π g ∈ U at hg
    change qX (π ((h : Γ) • g)) ∈ A ∧ π ((h : Γ) • g) ∈ U
    simp only [hπγ, hqγ]
    exact ⟨hg.1, hstable h (π g) hg.2⟩
  have hEsep : ∀ γ : Γ, ∀ g ∈ E, γ • g ∈ E → γ ∈ H := by
    intro γ g hg hγg
    change qX (π g) ∈ A ∧ π g ∈ U at hg
    change qX (π (γ • g)) ∈ A ∧ π (γ • g) ∈ U at hγg
    exact hsep γ (π g) hg.2 ((hπγ γ g) ▸ hγg.2)
  rw [Measure.restrict_apply hA, Measure.map_apply hr (hA.inter himage),
    Measure.smul_apply, Measure.map_apply hq hA, Measure.restrict_apply (hq hA)]
  change ν (r ⁻¹' (A ∩ qX '' U)) = (Nat.card H : ℝ≥0∞)⁻¹ * ξ B
  rw [← hEimage, sourceFiniteSlice_quotient_measure μ ν H hF E hE hEimage_meas hEstable hEsep]
  exact congrArg ((Nat.card H : ℝ≥0∞)⁻¹ * ·) (hπ.measure_preimage hB.nullMeasurableSet)

end
end ArtinMatthews
