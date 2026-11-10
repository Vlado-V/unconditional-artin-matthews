module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.CompactCharacter
public import OAI.RepresentationTheory.Weil.Local.OscillatorProjection
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
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import OAI.RepresentationTheory.Weil.Local.AnnihilatorDuality
public import OAI.RepresentationTheory.Weil.Local.FourierTools


set_option backward.privateInPublic true
@[expose] public section

/-! # Schur Indicators -/

namespace OAI.RepresentationTheory.Weil.Local.SchurIndicators.Construction

noncomputable section

/-! Compact-open indicator eigenspaces for the nonarchimedean oscillator kernel. -/

open _root_.MeasureTheory
open scoped Classical

theorem heisenberg_pure_translation
    {k : Type} [Field k] {n : ℕ} (ψ : AddChar k ℂ)
    (t : FunctionsMetaplectic.Construction.Position k n) (f : FunctionsMetaplectic.Construction.Position k n → ℂ) :
    FunctionsMetaplectic.Construction.heisenbergFunction ψ (Sum.elim (-t) 0) f = fun x => f (x + t) := by
  funext x
  simp [FunctionsMetaplectic.Construction.heisenbergFunction, Pi.add_def]

theorem heisenberg_pure_modulation
    {k : Type} [Field k] {n : ℕ} (ψ : AddChar k ℂ)
    (t : FunctionsMetaplectic.Construction.Position k n) (f : FunctionsMetaplectic.Construction.Position k n → ℂ) :
    FunctionsMetaplectic.Construction.heisenbergFunction ψ (Sum.elim 0 t) f = fun x => ψ (FunctionsMetaplectic.Construction.dot t x) * f x := by
  funext x
  simp [FunctionsMetaplectic.Construction.heisenbergFunction, FunctionsMetaplectic.Construction.dot]

theorem oscillator_kernel_heisenberg
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k]
    [MeasurableSpace k] [BorelSpace k] {n : ℕ}
    (ψ : AddChar k ℂ)
    (g : FunctionsMetaplectic.Construction.Oscillator k n ψ) (hg : OscillatorProjection.Construction.oscillatorProjection k n ψ g = 1)
    (v : FunctionsMetaplectic.Construction.PhaseSpace k n) (f h : FunctionsMetaplectic.Construction.schwartzBruhat k n)
    (hh : h.val = FunctionsMetaplectic.Construction.heisenbergFunction ψ v f.val) :
    (g.val.2 h).val = FunctionsMetaplectic.Construction.heisenbergFunction ψ v (g.val.2 f).val := by
  have hgraph := (g.property.2 v f h).mp hh
  have hproj : g.val.1 = 1 := hg
  rw [hproj, FunctionsMetaplectic.Construction.symplecticAction_one] at hgraph
  exact hgraph

theorem oscillator_kernel_indicator_eigenvector
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (g : FunctionsMetaplectic.Construction.Oscillator k n ψ) (hg : OscillatorProjection.Construction.oscillatorProjection k n ψ g = 1)
    (U : OpenAddSubgroup (FunctionsMetaplectic.Construction.Position k n)) (hU : IsCompact (U : Set (FunctionsMetaplectic.Construction.Position k n))) :
    let f : FunctionsMetaplectic.Construction.schwartzBruhat k n := ⟨(U : Set (FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => 1),
      FunctionsMetaplectic.Construction.compact_locallyConstant_mem (CompactCharacter.Construction.subgroup_indicator_locallyConstant U)
        (CompactCharacter.Construction.subgroup_indicator_compactSupport U hU)⟩
    ∀ x, (g.val.2 f).val x = (g.val.2 f).val 0 * f.val x := by
  intro f x
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  have htranslation (t : FunctionsMetaplectic.Construction.Position k n) (ht : t ∈ U) :
      ∀ y, (g.val.2 f).val (y + t) = (g.val.2 f).val y := by
    have hh : f.val = FunctionsMetaplectic.Construction.heisenbergFunction ψ (Sum.elim (-t) 0) f.val := by
      rw [heisenberg_pure_translation]
      funext y
      have hmem : y + t ∈ U ↔ y ∈ U := U.add_mem_cancel_right ht
      by_cases hy : y ∈ U
      · simp [f, hy, hmem.mpr hy]
      · have hyt : y + t ∉ U := fun h => hy (hmem.mp h)
        simp [f, hy, hyt]
    have h := oscillator_kernel_heisenberg ψ g hg (Sum.elim (-t) 0) f f hh
    rw [heisenberg_pure_translation] at h
    exact fun y => (congrFun h y).symm
  have hmodulation (p : FunctionsMetaplectic.Construction.Position k n) (hp : p ∈ CompactCharacter.Construction.additiveAnnihilator ψ U.toAddSubgroup) :
      ∀ y, (g.val.2 f).val y = ψ (FunctionsMetaplectic.Construction.dot p y) * (g.val.2 f).val y := by
    have hh : f.val = FunctionsMetaplectic.Construction.heisenbergFunction ψ (Sum.elim 0 p) f.val := by
      rw [heisenberg_pure_modulation]
      funext y
      by_cases hy : y ∈ U
      · simp [f, hy, hp y hy]
      · simp [f, hy]
    have h := oscillator_kernel_heisenberg ψ g hg (Sum.elim 0 p) f f hh
    rw [heisenberg_pure_modulation] at h
    exact fun y => congrFun h y
  by_cases hx : x ∈ U
  · have h := htranslation x hx 0
    simpa [f, hx] using h
  · have hzero : (g.val.2 f).val x = 0 := by
      by_contra hz
      have hdouble : x ∈ CompactCharacter.Construction.additiveAnnihilator ψ (CompactCharacter.Construction.additiveAnnihilator ψ U.toAddSubgroup) := by
        intro p hp
        rw [FourierTools.Construction.dot_comm]
        apply mul_right_cancel₀ hz
        simpa only [one_mul] using (hmodulation p hp x).symm
      let μ : Measure (FunctionsMetaplectic.Construction.Position k n) := Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k))
      let : μ.IsAddHaarMeasure := by dsimp [μ]; infer_instance
      obtain ⟨_, _, hduality⟩ := AnnihilatorDuality.Construction.nonarchimedean_annihilator_duality_and_scale hNondiscrete n ψ hu hc hn μ
      rw [(hduality U hU).1] at hdouble
      exact hx hdouble
    simp [f, hx, hzero]

end

end OAI.RepresentationTheory.Weil.Local.SchurIndicators.Construction
